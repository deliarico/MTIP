# The Multi-connection Tactile Internet Protocol (MTIP)

## Application examples

To showcase an example of the usage of MTIP API, ``Applications/Example_Controller/`` presents a remote control application and (``Applications/Example_Device/``) a controlled device application.

### Usage

#### Prequisites

* Linux OS
* QT 5.0 or higher

#### Preparation

1. Download ``Application/`` folder.
2. Copy libMTIP.so (\*) and MTIP headers (\*) to ``Applications/MTIP/`` folder. Create folder if necessary.
3. Change IP and ports in ``Applications/Example_Device/Device.cpp`` and ``Applications/Example_Controller/Controller.cpp`` if there was any conflict.

(*) Regrettably, the access to these files is currently unavailable due to licensing restrictions. The files will be made available as soon as circumstances allow.

#### Execution

1. Run ``Device.cpp``.
2. Run ``Controller.cpp``.


