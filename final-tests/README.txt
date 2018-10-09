TESTING LOGS
=====

This directory contains the logs from the random
testing process described in the testing section of the paper.
Each log file contains the log for one testing process,
which ran forever until the process was killed.

logs with the prefix `agda` contain the adga/redex tests.
logs with the prefix `external` contain tests that compared the calculus, the COS, Esterel V5, and HipHop.
logs with the prefix `internal` contain tests that compared the calculus and the COS.

Some of the `external` tests note differences between Esterel V5, Hiphop, and the COS. We have manually inspecte these,
and they are all the known bugs listed in the paper.
