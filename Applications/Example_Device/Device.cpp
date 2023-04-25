/**
* @file Device.cpp
* @author Delia Rico (deliarico@uma.es)
* @brief Example device using MTIP with two sublinks
* @version 1.0
* @date 2023-01-31
*
* @copyright Copyright (c) 2023
*
*/
#include <QCoreApplication>
#include <QDateTime>
#include <QHostAddress>
#include <QString>
#include <QNetworkInterface>
#include <iostream>
#include <thread>
#include <dlfcn.h>
#include <stdio.h>
#include <math.h>
#include <inttypes.h>
#include <sys/time.h>
#include "../MTIP/MTIP.h"

/** Buffer size **/
#define PREF_SIZE 260

/** Number of messages to be sent */
#define NUM_OF_MESSAGES 10000

/** IP and ports */
#define IP_1 "10.0.0.1"
#define IP_2 "11.0.0.1"
#define PORT 1111

/** Connection */
void reception_callback(char *order, double time);
void finished_callback();
void get_my_ip(char **theIP);
int g_socket_descriptor;

/** Message */
int g_signal_created[NUM_OF_MESSAGES];
double g_times[NUM_OF_MESSAGES];

using namespace std;

int main(int argc, char *argv[]) {

    QCoreApplication app(argc, argv);
    char *my_ip;

    /* Extract API from a dynamic library */
    void* handle = dlopen("libMTIP.so", RTLD_LAZY);

    int (*mtip_socket)(int);
    int (*mtip_bind)(int, char *, int);
    int (*mtip_link)(int, uint8_t, char *, int);
    int (*mtip_preferences)(int, char *);
    int (*mtip_receive)(int, void (*)(char *, double));
    int (*mtip_finished)(int, void (*)());
    mtip_socket = (int (*)(int)) dlsym(handle, "mtip_socket");
    mtip_bind = (int (*)(int, char *, int)) dlsym(handle, "mtip_bind");
    mtip_link = (int (*)(int, uint8_t, char *, int)) dlsym(handle, "mtip_link");
    mtip_preferences = (int (*)(int, char *)) dlsym(handle, "mtip_preferences");
    mtip_receive = (int (*)(int, void (*)(char *, double))) dlsym(handle, "mtip_receive");
    mtip_finished = (int (*)(int, void (*)())) dlsym(handle, "mtip_finished");

    get_my_ip(&my_ip);
    g_socket_descriptor = mtip_socket(OPT_NOT_FULLMESH | OPT_FULL_DEBUG);

    if (g_socket_descriptor == -1) {
        perror("Error opening socket");
        exit(1);
    }

    if (mtip_bind(g_socket_descriptor,IP_1,PORT) == -1) {
        perror("Error binding socket");
        exit(1);
    }

    if (mtip_bind(g_socket_descriptor,IP_2,PORT) == -1) {
        perror("Error binding socket");
        exit(1);
    }

    free(my_ip);

    char preferences_json[PREF_SIZE] = " {\n "
                                       " \" latency \": 1e+7 ,\n "
                                       " \" duplicateThreshold \": 20 ,\n "
                                       " \" losslateThreshold \": 5 ,\n "
                                       " \" latWeight \": 50"
                                       " } " ;

    if (mtip_preferences(g_socket_descriptor, preferences_json) == -1) {
        perror("Error adding preferences to the socket");
        exit(1);
    }

    if (mtip_receive(g_socket_descriptor, reception_callback) == -1) {
        perror("Error adding reception callback");
        exit(1);
    }

    if (mtip_finished(g_socket_descriptor, finished_callback) == -1) {
        perror("Error adding finished callback");
        exit(1);
    }

    if (mtip_link(g_socket_descriptor, MTIP::Mode::DEVICE, NULL, 0) == -1) {
        perror("Error opening link in listen mode");
        exit(1);
    }
    
    return app.exec();
}

void reception_callback(char *order, double time) {

    printf("-------------------------------\n");
    printf("Received in APP: %s\n", order);
    printf("-------------------------------\n");
    g_times[atoi(order)] = time;
    g_signal_created[atoi(order)] = atoi(order);

}

void finished_callback() {

    printf("Time, Amplitude\n");
    for (int i = 1; i < NUM_OF_MESSAGES; ++i) {
        printf("%.0lf,%d\n", g_times[i], g_signal_created[i]);
    }
    fflush(stdout);
}

void get_my_ip(char **the_ip) {
    const QHostAddress &localhost = QHostAddress(QHostAddress::LocalHost);

    for (const QHostAddress &address: QNetworkInterface::allAddresses()) {
        if (address.protocol() == QAbstractSocket::IPv4Protocol && address != localhost) {
            qDebug() << address.toString();
            *the_ip = (char *) malloc((address.toString().size()) * sizeof(char));
            strcpy(*the_ip, address.toString().toLocal8Bit().data());
        }
    }
}

