# mrv-sign

 This is new implementation of Maxima function mrv-sign. This code is used by the Gruntz method for computing limits. The hope is that this implementation will fix some bugs and will extend the set of cases the limit can handle. There are no user-level functions in this code.

 The tests in rtest_gruntz are translationed from the SymPY tests. For the 
 copyright and license for these tests see the LICENSE. I thank the SymPY developers for making this resource available. 

 To run the testsuite without stopping, I had to insert a call to assume to one test in `rtest_limit` to avoid an asksign. The modified test is

 ~~~
/* 1-arg limit: limit(a*inf-inf) => minf - ID: 1385306 
This is a long-standing bug--the kill(a) is needed. */
block([L1,L2,L3,L4,L5,L6], 
   kill(a),
   assume(a > 0), /* added */
   L1 :limit(a*inf-inf),
   L2 : limit((a-1)*inf),
   forget(a > 1),
   assume(a<1), 
   L3 : limit(a*inf-inf),
   L4 : limit((a-1)*inf),
   forget(a < 1),
   assume(a > 1),
   L5 : limit(a*inf-inf),
   L6 : limit((a-1)*inf),
   [L1,L2,L3,L4,L5,L6]);
 ~~~


