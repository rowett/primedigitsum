# ds(n)
Let ds(n) be the smallest prime number where the digit sums of it when written in bases 2 to n+1 are all prime.

This software searches for ds(n) prime numbers. The search can be parallelized across multiple cores.
The search space is split into blocks of 1e12 numbers and distributed for processing amongst available cores.
As each block is processed the results for that block are saved as text files in a "blocks" directory and a new block is allocated to the core.

## Requirements
Linux, gcc, make, modern x64 CPU supporting POPCNT instruction.


## Files
* **Makefile** - to build the search application
* **ds.c**     - the source code for the search application
* **ds**       - the search application (once built)
* **pards**    - a shell script that runs 'ds' in parallel across multiple cores each with a block of numbers to search
* **blocks/**  - the folder containing the results from searching each number block
* **results**  - a shell script that displays a list of each ds(n) found
* **tidy**     - a shell script that removes any unfinished blocks (this is also done automatically when you run **pards**)
* **times**    - a shell script that displays the processing time for each completed block in seconds


## Building
* Ensure you have "make" installed: 
  * **% sudo apt get make**

* Ensure you have "gcc" installed:
  * **% sudo apt get gcc**

* Change directory to the folder containing both **Makefile** and **ds.c**.

* Build the application:
  * **% make**


## Running
* Create a folder for the results. The default folder name is **blocks**. If you want a different folder name then you need to pass **-d <folder>** to the scripts.
  * **% mkdir blocks**

* Run **pards** to search using all CPU cores or **pards -c <number>** to specify number of cores:
  * **% ./pards -c 4**

* **pards** will show you which blocks are running on which core and then as they complete will show you how long the block took to process.


## Display results
* To output current results:
  * **% ./results**

* To monitor the results every 30 seconds:
  * **% ./results 30**

* To display a list of processing time (in seconds) for each completed block:
  * **% ./times**


* To remove any unfinished blocks (typically caused when you interrupt pards):
  * **% ./tidy**
  * Note: blocks are automatically tidied each time pards starts.

