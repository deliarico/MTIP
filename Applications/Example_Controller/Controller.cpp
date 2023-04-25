/**
* @file Controller.cpp
* @author Delia Rico (deliarico@uma.es)
* @brief Simple controller using MTIP with two sublinks
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
#include <unistd.h>
#include <stdio.h>
#include <sys/time.h>
#include <signal.h>
#include "../MTIP/MTIP.h"

/** Buffer size **/
#define PREF_SIZE 260

/** Number of messages to be sent */
#define NUM_OF_MESSAGES 10000
#define MAX_SIZE 15

/** Time interval for messages (ms) */
#define TIME_INTERVAL 10

/** IP and ports */
#define IP_1 "10.0.0.2"
#define IP_2 "11.0.0.2"
#define IP_REMOTE "10.0.0.1"
#define PORT 5555
#define PORT_REMOTE 1111

/** Connection */
void reception_callback(char *order, double time);
void send_message(int signum);
int (*mtip_send)(int, char *, int);
int (*mtip_feedback)(int, char *&, int);
void get_my_ip(char **the_ip);
int g_socket_descriptor;
bool g_is_sending;

/** Timer */
int set_ticker(long n_msecs);
int stop_ticker();

/** Message */
int g_signal_amplitude = 0;
int g_signal_created[NUM_OF_MESSAGES];
struct timespec g_times[NUM_OF_MESSAGES];
int get_amplitude();

using namespace std;

int main(int argc, char *argv[]) {

    QCoreApplication app(argc, argv);
    char *my_ip, *feedback;
    int link_opened = -1;

    /* Extract API from a dynamic library */
    void* handle = dlopen("libMTIP.so", RTLD_LAZY);

    int (*mtip_socket)(int);
    int (*mtip_bind)(int, char *, int);
    int (*mtip_link)(int, uint8_t, char *, int);
    int (*mtip_preferences)(int, char *);
    int (*mtip_receive)(int, void (*)(char *, double time));
    int (*mtip_close)(int);
    mtip_socket = (int (*)(int)) dlsym(handle, "mtip_socket");
    mtip_bind = (int (*)(int, char *, int)) dlsym(handle, "mtip_bind");
    mtip_link = (int (*)(int, uint8_t, char *, int)) dlsym(handle, "mtip_link");
    mtip_send = (int (*)(int, char *, int)) dlsym(handle, "mtip_send");
    mtip_preferences = (int (*)(int, char *)) dlsym(handle, "mtip_preferences");
    mtip_feedback = (int (*)(int, char *&, int)) dlsym(handle, "mtip_feedback");
    mtip_receive = (int (*)(int, void (*)(char *, double))) dlsym(handle, "mtip_receive");
    mtip_close = (int (*)(int)) dlsym(handle, "mtip_close");

    get_my_ip(&my_ip);
    g_socket_descriptor = mtip_socket(OPT_NOT_FULLMESH | OPT_FULL_DEBUG );

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

    while (link_opened < 0) {
        link_opened = mtip_link(g_socket_descriptor,MTIP::Mode::CONTROLLER, IP_REMOTE, PORT_REMOTE);
    }

    free(my_ip);

    signal(SIGALRM, send_message);
    if (set_ticker(TIME_INTERVAL) == -1) {
        perror("set_ticker");
    } else {
        g_is_sending = true;
        while (g_is_sending) {
            pause();
        }
    }

    printf("-------------------------------\n");
    printf("FINISHED.\n");
    printf("-------------------------------\n");

    sleep(3);

    if (mtip_feedback(g_socket_descriptor, feedback, MTIP::GENERAL) == -1) {
        perror("Error getting feedback");
        exit(1);
    }

    fprintf(stdout, "Feedback: %s", feedback);
    free(feedback);
    sleep(1);

    if (mtip_close(g_socket_descriptor) == -1) {
        perror("Error closing");
        exit(1);
    }

    return app.exec();
}

void reception_callback(char *order, double time) {

    printf("-------------------------------\n");
    printf("Received in APP: %s\n", order);
    printf("-------------------------------\n");

}

void send_message(int signum) {

    if (g_signal_amplitude >= (NUM_OF_MESSAGES - 1)) {

        stop_ticker();

        if (g_is_sending) {
            g_is_sending = false;
            for (int i = 1; i < NUM_OF_MESSAGES; ++i) {
                printf("%lld.%.9ld,%d\n", (long long) g_times[i].tv_sec, g_times[i].tv_nsec, g_signal_created[i]);
                fflush(stdout);
            }
        }

    } else {

        g_signal_amplitude++;
        char *msg = (char *) malloc(sizeof(char) * MAX_SIZE); /* deleted after sending */
        sprintf(msg, "%d", g_signal_amplitude);
        timespec_get(&g_times[g_signal_amplitude], TIME_UTC);
        g_signal_created[g_signal_amplitude] = g_signal_amplitude;
        mtip_send(g_socket_descriptor, msg, 0);

    }


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

/**
 * Valid for less than 1 sec
 */
int set_ticker(long n_msecs) {

    struct itimerval new_timeset;
    long n_sec, n_usecs;

    n_sec = 0;                      /* n_sec = n_msecs / 1000 ; int part */
    n_usecs = n_msecs * 1000L;      /* n_usecs = ( n_msecs % 1000 ) * 1000L remainder */

    new_timeset.it_interval.tv_sec = n_sec;
    new_timeset.it_interval.tv_usec = n_usecs;
    new_timeset.it_value.tv_sec = n_sec;
    new_timeset.it_value.tv_usec = n_usecs;

    return setitimer(ITIMER_REAL, &new_timeset, NULL);
}

int stop_ticker() {

    struct itimerval new_timeset;

    new_timeset.it_interval.tv_sec = 0;
    new_timeset.it_interval.tv_usec = 0;
    new_timeset.it_value.tv_sec = 0;
    new_timeset.it_value.tv_usec = 0;

    return setitimer(ITIMER_REAL, &new_timeset, NULL);
}


