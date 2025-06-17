# The Multi-connection Tactile Internet Protocol (MTIP)

The Multi-connection Tactile Internet Protocol (MTIP) is a transport protocol for the remote control of Tactile Internet applications. 
This repository presents models, applications and evaluation results of the protocol. Each folder has its own README.md with additional information.
Below, we give an overview of the protocol and API documentation.



## Overview

MTIP creates a link between two endpoints (typically a remote device and a controller) that consists of several sublinks. Current implementation of MTIP offers a C/C++ API described as follows.

## API

This section presents the API functions  in a typical order of usage.

### Create a new socket

`int mtip_socket(int options)`

* @param options: OPT_NOT_FULLMESH (Disable connection fullmesh), OPT_NOT_MONITOR (Disable MTICP), OPT_FULL_DEBUG (Disable debug information).

### Bind sublinks (IP and port) 

``int mtip_bind(int sd, char *addr, int port)``

### Create a link
``int mtip_link(int sd, uint8_t mode, char *addr, int port)``

* @param mode: Controller (to connect), Device (to listen).

### Set preferences

``int mtip_preferences(int sd, char *prefs)``

* @param prefs: [Go to Context Information section](#context).

### Receive (set a callback for the reception of data)

``mtip_receive(int sd, void (*callback)(char *, double))``

* @param char *: message data.
* @param double: timestamp information.

### Set a callback for when the connection finishes

``int mtip_finished(int sd, void (*callback)())``

### Send
``int mtip_send(int sd, char *message, int flag) ``

* @param flag: FLAG_DATAPRIO (Data with priority), 0 (Normal data).

### Get feedback

``int mtip_feedback(int sd, char *&feedback,  int type)``

* @param feedback:  [Go to Context Information section](#context).
* @param type: GENERAL (Characterization of each sublink).

### Close Socket

``int mtip_close(int sd)``

## Context Information

Context information refers to the communication preferences that can be set in ``mtip_preferences`` and the feedback information that can be retrieved from ``mtip_feedback``.

### Communication preferences

The application can set the following communication preferences:


|Communication preference|Description|Accepted values in current implementation|Default value in current implementation|     
|---|---|---|---| 
|Algorithm mode (AM)  |It selects the algorithm that  is going to be used for the selection of sublinks. The  sublinks might be selected by the application (fixed  selection) or dynamically  by the protocol.|0: Use all sublinks   (fixed selection) 1: Use one sublink   (fixed selection) 2: Use best (N) sublinks   (dynamic selection) 3: Use the MTIP Algorithm   (dynamic selection)|  0 | 
|Number of sublinks (N)|It selects the sublink that  is in use  (in the case of  AM 1) or the number of  sublinks that should be in  use (in the case of AM 2).|0 to the maximum number  of sublinks available|   0
|Maximum latency (deadline) |It defines the maximum  end-to-end latency of the  packets, namely the  deadline|  0 to 1e9 nanoseconds    |    1e7 nanoseconds 
|Duplicate threshold (DT)   |It defines the maximum  percentage of duplicate  packets that the MTIP  algorithm considers  reasonable (only used in AM 3).| 0 to 100 \%  | 50       
|Loss-late threshold (LT)  |It defines the maximum  percentage of loss or late  packets that the MTIP  algorithm considers  reasonable(only used in  AM 3).|0 to 100  \%   |    10 
|Latency weight (LW) |It defines how the sublink  ranking must be calculated, using just reliability  measurements (LW 0),  using only latency  measurements (LW 100),  or using a weighted mean  of both measurements  (LW from 0 to 100).|0 to 100  \%   |    100  

### Feedback information 

The application can obtain the following feedback information:




|Feedback|Description|Values in current implementation|
|---|---|---|
|Sublink| It indicates the network information on the available sublinks.|   Sublink ID, IP addresses and ports
|Latency (ingress) |   It indicates the measured latency (ingress) in each sublink.|      Latency in nanoseconds    
|Latency (egress) | It indicates the measured latency (egress) in each sublink.|       Latency in nanoseconds               
|Reliability (ingress) | It indicates the measured reliability (ingress) in each sublink|    Reliability in the percentage  of packets sucessfully forwarded to the application| 
|Reliability (egress) | It indicates the measured reliability  (ingress) in each sublink|  Reliability in the percentage  of packets sucessfully forwarded to the application| 



## Example 

To showcase an example of the use of MTIP API, ``Applications/`` presents a remote control application and a controlled device application.


