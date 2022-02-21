What's in the repo
==================

This repo contains the raw materials used to for the experiments
described in "How to Specify it!":

     Hughes, John. "How to Specify it!."
     In International Symposium on Trends in Functional
     Programming, pp. 58-83. Springer, Cham, 2019.

If you would like to use them for further experiments, you're welcome
to do so.

They consist of:

-- a simple, but non-trivial example of code to test, an
   implementation of a finite map as a binary search tree (BST.hs, 66
   non-comment non-blank lines of source code)

-- a collection of QuickCheck properties for testing the code
   (BSTSpec.hs). There are:

   -- 48 properties designed using the principles explained in the
      paper, of which two are duplicates (the same property motivated
      in different ways).

   -- 31 properties discovered automatically by QuickSpec
      (https://hackage.haskell.org/package/quickspec), of which 11
      duplicate hand-written properties from the paper. (This goes
      beyond what the paper describes).

-- Eight buggy versions of the implementation (BST1..BST8.hs), with
   bugs ranging from the blatant to the somewhat-more-subtle.

-- Benchmarking code (also in BSTSpec.hs) for measuring the
   mean-tests-to-failure for each property and bug. Compile BSTSpec
   and run measureTests to perform a benchmarking run.

-- The results of running the benchmarks, in 'Mean time to failure for
   all properties and variants.xlsx'. Some properties never fail:
   these are coloured orange in the spreadsheet. A 0,0 in the table
   represents a property that does not fail for the variant in
   question.


How to run the benchmarks
=========================

Generating the benchmark results is not completely automated. One run
of measureTests benchmarks all the properties for ONE variant--which
one is determined by the

  import BST

at the top of BSTSpec.hs. Replace BST by one of BST1..BST8 to
benchmark a buggy version.

I recommend compiling BSTSpec with -O2; the benchmarks will very slow
if run as interpreted code. Some properties require almost 2,000
random tests to falsify them for some variants, and the benchmarks
test each failing property 1,000 times, so the benchmarks do run
millions of tests.

The output of the benchmarks is written to mttfs.csv, from which it
can be copied and pasted into another spreadsheet to gather a complete
set of results. Beware that the csv file is in SWEDISH, which uses a
decimal comma rather than a decimal point, and consequently a
semicolon as the separator in a csv file, rather than a comma. (Be
grateful it's not called an ssv file). This makes it easy to open in a
Swedish version of Excel; if you want to generate data for an English
version, then you will need to adapt the code at lines 496--498 of
BSTSpec.hs.
