#import "rules/base.typ": *
#import "rules/relations.typ": *
#import "rules/unification.typ": *
#import "rules/statements.typ": *
#import "../vars.typ": *

#pagebreak()
== While Loops
The process of typing a while statement from a context $Delta$ involves unifying $Delta$ with the resulting context after executing the body of the while loop. This unification is repeated with the context obtained until a fixed point is reached.

=== First approach

Given a statement $s$, we can define a funtion $u_s : Delta -> Delta$ as follows:

#display-rules(
  U-Fun, ""
)

Then we can define the following sequence:
$ Delta, u_s (Delta), u_s (u_s (Delta)), ..., u_s^n (Delta), ... $

After defining an ordering ($subset.eq.sq$) between contexts it will be possible to show that this sequence is an ascending chain i.e.

$ Delta subset.eq.sq u_s (Delta) subset.eq.sq u_s (u_s (Delta)) subset.eq.sq ... subset.eq.sq u_s^n (Delta) subset.eq.sq ... $

Moreover it will be possible to show that chain at some point will reach a fixed-point:

$ forall Delta . forall s . exists n . space u_s^n (Delta) = u_s^(n + 1) (Delta) = u_s^* (Delta) $

And so now it is possible to define the typing rule for while loops as follows:

#display-rules(
  While, ""
)

=== Alternative approach
Simpler approach with no guarantees on the termination of the typing algorithm

#display-rules(
  While-Base, While-Rec,
)