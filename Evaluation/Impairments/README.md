# The Multi-connection Tactile Internet Protocol (MTIP)

## Impairments

This folder describes the impairments included in scenarios Filter-Special (dditional latency impairments to the paths) and Filter-Congestion (additional congestion impairments). 

* Folder ``Filter-Special`` includes two files with the numeric values of the latency added to the paths (.csv) and a image to illustrate it. 
* Folder ``Filter-Congestion`` includes a file with the numeric values of the congestion added to the scenario: losses (.csv) and RTP video feedback sent concurrently (.zip). The losses follow a typical congestion pattern extracted from a 5G Network with a base packet loss, a gradual ramp-up, peak congestion and a ramp-down. This folder also contains logs and a figure illustrating the execution of two iperf TCP tests (with and without the losses), intended solely to demonstrate that the induced losses cause congestion.



