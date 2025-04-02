# Evaluation of MTIP and other Multipath Protocols for Time-Sensitive Applications

This folder contains the results of the evaluation of MTIP, MPTCP and MPQUIC for the Time Sensitive Application of the remote control of the quadruped robot Ghost Vision 60.

Each folder (MTIP, MPTCP and MPQUIC) contains the logs for the execution of the tests and a folder <em>/results</em> with the logs processed and figures to illustrate each protocol behavior.

The nomenclature in the files is the following:

* **Protocol**: MPTCP (mptcp-1), MPQUIC (mpquic-1), MTIP (mtip-a: use of all paths, mtip-b: use of MTIP's path algorithm selection).
* **Scenario**: two regular 5G-SA paths (Filter-False), one link failure in one of the 5G-SA paths (Filter-True), additional impairments to the paths as described in folder <em>/impairments</em> (Filter-Special) and background video traffic (Filter-background) as described in compressed files <em>Background-Traffic_*timestamp*.zip</em>.
* **Endpoint**: Controller (server_stderr_log & server_stdout_log) and Robot (client_stderr_log, client_stdout_log, robot_stderr_log & robot_stdout_log).
* **Timestamp**: date of the test.

Folder <em>/Wireshark-Examples</em> contains examples of each protocol.



