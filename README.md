# ds(n)
Let *ds(n)* be the smallest prime number where the digit sums of it when written in bases 2 to n+1 are all prime.

This software searches for *ds(n)* prime numbers. The search can be parallelized across multiple cores.
The search space is split into blocks of 1E12 numbers and distributed for processing amongst available cores.
As each block is processed the result for that block is saved as text file in a **blocks/** directory and a new block is allocated to the core.

There is also a benchmark which tests how searching scales across threads on your CPU.


## Requirements
Linux, **gcc**, **make**, and a modern x64 CPU that supports the POPCNT instruction.


## Files
* **Makefile** - to build the search application.
* **ds.c**     - the source code for the search application.
* **ds**       - the search application (once built).
* **pards**    - a shell script that runs **ds** in parallel across multiple cores each with a block of numbers to search.
* **blocks/**  - the folder containing the results from searching each number block.
* **results**  - a shell script that displays a list of each *ds(n)* found.
* **tidy**     - a shell script that removes any unfinished blocks (this is also done automatically when you run **pards**).


## Building
* Ensure you have **make** installed: 
  * **% sudo apt install make**

* Ensure you have **gcc** installed:
  * **% sudo apt install gcc**

* Change directory to the folder containing both **Makefile** and **ds.c**.

* Build the application:
  * **% make**

* If the build fails it may be because your CPU does not support the required POPCNT instruction.


## Running
* Create a folder for the results. The default folder name is **blocks**. If you want a different folder name then you need to pass **-d _folder_** to the scripts.
  * **% mkdir blocks**

* Run **pards** to search using all CPU cores or **pards -c _number_** to specify number of cores:
  * **% ./pards -c 4**

* **pards** will show you which blocks are running on which core and then as they complete will show you how long the block took to process.

* When **pards** is first run it will start at block 0. If you stop it and then run it again it will skip any completed blocks and continue.


## Displaying results
* To output current results:
  * **% ./results**

* To monitor the results every 60 seconds:
  * **% ./results 60**

* To remove any unfinished blocks (typically caused when you interrupt **pards**):
  * **% ./tidy**
  * Note: blocks are automatically tidied each time **pards** starts.


## A note on performance
On an AMD3950 **ds** can search a block of 1E12 numbers in around 5 minutes on a single CPU core. Multiple blocks can be searched in parallel using the **pards** script.

* *ds(22)* can be found in about 12 seconds on a single core.
  * **% ./ds 0 100000000000 2 23**

* *ds(31)* can be found in about 3 days on a single core, or in about 2 hours and 30 minutes using 30 cores.
  * **% ./pards -c 30**


## Benchmark
* To run the benchmark:
  * **% ./startbench**

The output will be in a text file called *timing<date-stamp>.txt*.

* To run the benchmark on a just 8 threads:
  * **% ./startbench -c 8**

