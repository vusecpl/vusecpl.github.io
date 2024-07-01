---
layout: post
title: Refinement Type Refutations
subtitle: How to show that a program doesn't type check?
tags: [liquid-types, counterexamples]
comments: true
mathjax: true
author: Klaus v. Gleissenthall
---

### Refinement Typing

Refinement types are a great way to statically verify properties of programs. 

With refinement types, we can annotate a base-type (like `Int` or `Bool`) with a
logical predicate that restrict the possible values inhabitants of the type may
take. For example, in [Liquid
Haskell](https://ucsd-progsys.github.io/liquidhaskell/) we can define the
following type for non-zero integers.

```haskell
type NonZero = Int{v:v /= 0}
```

We can then use this type in function definitions. For example, we can specify
`div` as a function that takes a non-zero integer, and returns its first input
`x` divided by its second one, `y`.

```haskell
div :: x:Int -> y:NonZero -> Int{v:v == x / y}
```

The type system then proves at compile-time, that whenever we call `div` at
runtime, its second argument must indeed be non-zero. Great!

### Modularity For the Win

What makes refinement types so powerful is their *modularity*. To check if a
program respects all the restrictions posed by the types -- and their
refinements -- the checker only needs to look at "what's written on the tin".
That is, the type-checker only works with what we explicitly know from the
types, and doesn't need to perform any additional costly analysis, say, by
enumerating program traces. 

It's exactly this modularity that allows refinement types to scale to more
advanced features like higher-order functions, datatypes and polymorphism. For
example, if we define the type `Nat` to represent the natural numbers

```haskell
type Nat = Int{v:0 <= v}
```
and function `max` that returns the larger of two integers

```haskell
max :: Ord a => a -> a -> a
max x y = if x > y then x else y
```

we can use the polymorphic function
[`foldr1`](https://hackage.haskell.org/package/base-4.20.0.1/docs/Prelude.html#v:foldr1)
to compute the maximum of a (non-empty) list, and the type-checker will
automatically verify that the result is indeed a natural number.

```haskell
foldr1 :: (a -> a -> a) -> [a] -> a
foldr1 = ...

test1 :: Nat
test1 = foldr1 max [4, 3, 2, 1]
```
It's worth noting that Liquid Haskell manages to verify this example without
further annotations, for example, on the type of `foldr1` at this particular
call site. This is due to *refinement inference* which automatically computes
solutions for missing refinements.

{: .box-note} 
**Summary:** Refinement types are a great, and lightweight way to
statically check program properties.

### When Typing Goes Wrong

But what if we write a function that *doesn't* type check? Usually, when we
build verification methods, we focus on the case where verification succeeds.

As anyone knows who ever tried to verify a program: success is not the common
case! Usually, things go wrong.

Say, we define type `Even` to represent the even numbers.

```haskell
type Even = Int{v:v `mod` 2 = 0}
```

We may now want to repeat our earlier verification success from before, by
trying to prove that the maximum of list `[4, 3, 2, 1]` is even.

```haskell
test2 :: Even
test2 = foldr1 max [4, 3, 2, 1]
```

Clearly, this program is correct as the largest number in the list is `4`, which
is even. Yet, the program fails to verify with the following cryptic error
message from Liquid Haskell. Something is up, but it's hard to tell what from
Liquid Haskell's error message.

![LHError](/assets/img/lh-error.png)

{: .box-note} 
**Summary:** When refinement typing goes wrong, existing type-checkers offer little help.

## Haystack 

To make it easier to debug these and other verification failures, we built a new
tool called Haystack, which makes it easier for users to debug verification
failures. We describe Haystack and the theory behind it in a [new
paper](https://gleissen.github.io/papers/refinement-refutations.pdf) which was
recently accepted at
[OOPSLA'24](https://2024.splashcon.org/track/splash-2024-oopsla).

Haystack comes with a graphical user interface called Explorer, that lets the
user interactively inspect typing violation. For our example, Explorer's root
screen displays the following.

![LHError](/assets/img/root.png)

Indeed, the crucial piece of information comes from the requirement $$3 \not \in int\{v : v \; mod \; 2 == 0  \}$$.
The type signature of `foldr1` requires the output type to be equal to the type of the list. 

```haskell
foldr1 :: (a -> a -> a) -> [a] -> a
foldr1 = ...
```

Since the output must be even, this means that every element in the list must be even. But that's not true for $$3$$, hence the type error. 

Interestingly, the same thing that makes refinement typing so great -- its
modularity -- is what makes it so hard to debug verifications failures. In fact,
there is no program trace which could justify verification failure. The program
is correct yet the failure is caused by the modular abstractions that come from
the type system.

### What even is a counterexample?

But that raises the following question. What even is a counterexample to a
failed typing derivation? That is, which mathematical object should we use to
represent a failed typing derivation?

We answer this question in our paper with the notion of a *refinement type
refutation*.  We start from the bidirectional type system defined in [this
paper](https://arxiv.org/abs/2010.07763).

 This type system defines two
judgements. 
The first judgement $$\Gamma \vdash e \Leftarrow t$$ says, under
typing environment $$\Gamma$$ expression e can be *checked* to have type $$t$$.
The second judgement $$\Gamma \vdash e \Rightarrow t$$ says that under typing
environment $$\Gamma$$, we can *synthesize* a type $$t$$ for expression e.

The difference between checking and synthesis comes from how we can use thost
judgements. For checking, $$t$$ is an *input* to the typing rule, that is, we
have to a supply a candidate $$t$$ and the rule will check if, under a given
typing environment $$\Gamma$$ the expression can be typed against it. For
synthesis, we only supply $$\Gamma$$ and $$e$$, and the rule produces a type as
an output.

To define a notion of a failed typing derivation that matches the modularity of
type-checking we now define two analoguous non-typing judgements. Judgement
$$\Gamma \vdash e \not\Leftarrow t$$ signifies a type-checking failure. The
judgement says that we cannot check $$e$$ to have type $$t$$ under $$\Gamma$$.
Similarly, $$\Gamma \vdash e \not\Rightarrow \; !$$ signifies a type synthesis
failure. The judgement says that *no possible type* can be synthesized for $$e$$
under $$\Gamma$$.

Intuitively, a typing refutation contains two pieces of information. (1) a path
towards a sub-expression with a failing subtyping check and (2) a concrete
variable instances that violate the constraint.

Refinement type refutations allow us to give a precise meaning to what it means
to refute a type check. They form the theoretical underpinning for Haystack and
are what we use to represent counterexamples. Indeed, our graphical tool
Explorer lets the user browse exactly the refutation to the failed typing
judgement.

{: .box-note} 
**Summary:** Type refutations formalize the idea of a counterexample to a typing refutation. Haystack presents a graphical, interactive view of the type-refutation to the user.

### Must Instantiations

An interesting complication for finding type-refutations comes from another
strength of refinement type checking: refinement type inference, which allows
for considerable automation.

Remember how we didn't have to provide a type annotation for the refinement of `foldr1`? 

Internally Liquid Haskell achieves this by assigning an *unknown* refinement to
type variable `a`, and using a Horn constraint solver to automatically generate
a solution.

While unknown refinements are convenient for the user, they also make finding
counterexamples hard. We now have to show that *any* possible solution for the
unknown refinement will lead to a typing failure.

Haystack solves this problem via a new notion called *must-instantiation*. For
example, in our example function `test1`, we know that *any* solution to the
unknown refinement *must* at least contain inhabitant $3$, as it is contained in
the list `[4, 3, 2, 1]`. Since we also know that the unknown refinement must
imply that all values are even, this alone is enough to ensure that any possible
solution to the constraints must fail.

{: .box-note} 

**Summary:** Must instantiations allow Haystack to refute typing judgement in
the presence of refinement inference, which allows the user to omit intermediate
type annotations. For this, must-instantiations specify values which must be part of any solution to the unknown refinements, yet violate a subtyping constraint.

### Using Haystack

But does all of this really make proving programs correct easier? 

