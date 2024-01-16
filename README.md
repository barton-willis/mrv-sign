# mrv-sign

 This is new implementation of Maxima function mrv-sign that is used by the Gruntz method for computing limits. The hope is that this implementation will fix some bugs
 and will extend the set of programs that limit can handle.

 There are no user-level functions in this code.

 To run the testsuite with this code, I had to change one test in `rtest_limit` to avoid an asksign. In the following, `assume(a > 0)` is needed to prevent the asksign.

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


