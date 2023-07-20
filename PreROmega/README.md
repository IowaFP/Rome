An intrinsically typed formalization of Rω with pre-terms and
pre-types. Archived for now, in favor of a formalization *without*
pre-terms and pre-types (See ../ROmega).


### What is the difference?

In this approach, pre-types are types before kinding judgments. Similarly,
pre-terms are terms before typing judgements. So, the inductive data types are
kept separate.

In contrast, one can skip defining terms and types altogether, and instead
*only* declare kinding & typing judgments. This is actually a nicer route. 

The only downside (in some scenarios) of the latter approach is that you may not
represent ill-typed or kinded data. So, parsing becomes a de facto type checking
decider. If we were to write a proper parser and surface level language for Rω
itself, one would want to keep things and pre-things separate. So, I will keep
this development for storage. (There is an argument that this will never happen,
though -- rather, one would build a simpler language which compiles to Rω).


