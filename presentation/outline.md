# Outline of Defense 

## Outline

- Point at the problem, explain why it’s important (standing in the way of verification reaching its promise, no-one seems to be tackling it or even systematically investigating it).  Note that I won’t be solving this problem.
- Share the projects I’ve done in my PhD, how this issue has shown up in them, what I’ve learnt about this problem from them
- Share what I've learnt about the landscape of this problem
- Explain why the folklore solutions won't cut it
- Point to the two angles of attack I see available to us as a field

## The Problem

### Why Verfication?
- Bugs bad.
- Verification fix. (Note that I'm talking about ITPs; human help is important for difficult problems)

### What Done?
- CompCert, seL4, CertiKOS, Fiat-Crypto
- scale of these projects vs scale of industry

### What Problem?
- The problem is asymptotic performance.
- IMPORTANT: I don't see us closing this gap with the research we're currently doing!
- I've spent 8 years working in verification, become something of an expert at making verification automation work.
- More people like me spending more time won't get us there.

### Why do I think this?
- Slide with allocation of PhD time
- The performance problems are fundamentally different from those found in most of industry.
- The performance challenges scale *super-linearly* with the size and complexity of the programs being verified.
- The problem is asymptotic performance.
- Somehow (how?) foreshadow discussion of reflection and dropping proof terms (or the myths more generally)

## My Projects:

### What's Next:
- I'll be going through my projects, sharing what I did and what I learnt about the asymptotic performance problem from each of them
- Name the four axes that I've found almost all performance issues have on the independent axis:
  + The Size of the Type
  + The Size of the Term
  + The Number of Binders
  + The Number of Nested Abstraction Barriers
- (note that there are others, but these are the major ones of my experience, and I believe they generalize well)

-----

Andres suggests:
for each project:
- a description of the overall goal of the project
- state key performance bottleneck
- relate it to project goals
- go over methods tried and how they went
- highlight (verbally and on slides) key takeaways you will refer back to in the end when you make recommendations

-----

### Category Theory Library:
- Explain CT library very briefly
- I learnt a number of things about performance, the one I want to focus on here is what I'm going to call abstraction barriers.
- Explain type-size dependence briefly
- Coq easily and excessively inlines and unfolds definitions; the best strategy I've found for avoiding this problem is to have a clear distinction between which proofs are allowed to unfold a given definition, and which proofs are not; I call this an abstraction barrier
- This segues nicely into the next project I worked on

### Parsers:
- Explain parser synthsis
- Successfully synthesized a parser for the JSON grammar
- Ran into insurmountable performance issues with full JS 1.4 grammar (1999)
  + has 128 non-terminals (https://www-archive.mozilla.org/js/language/grammar14.html)
  + JSON has only 22 (https://www.json.org/json-en.html)
- The issue is that if you dump the grammar all at once and try to synthesize a parser for it, it's already too big, you're already sunk
- Tie into size of type and size of term
- Here again abstraction barriers could be a solution
- Why is performance important here?  Both the compile-edit-debug loop is important, but even if I could magically write down the correct solution, the first time, performance sometimes still isn't good enough.  Segue into fiat-crypto.
- ??? takeaway

### Fiat-Crypto:
- Explain fiat-crypto briefly
- Talk about fesub wbw-montgomery taking estimated 4,000+ millennia due to unfolding order issues
- Now here we get to the next axis, the number of binders.  Talk about binders = variables in the same function = hypotheses in the context
- Performance of rewrite
- Talk about proof by reflection, reflective rewriter+partial evaluator
(I'm losing track of things here...)

## Concluding

### Problem, Take 2:
- Performance of ITPs is super-linear in the complexity and scale of the software being verified.
- This is important both because having to wait minutes or hours rather than fractions of a second to try out a change severely impacts development time, and because at some point, you just can't get the computer to check the proof (4,000+ millennia)
- I don't see a path to verification fully realizing its promise without solving this problem

### Problem Details:
- Often performance issues factor through term size, type size, number of binders, or the number of nested abstraction layers, though there can be others.
  + (is there time to give short examples of each of these?)

### Myths:
- ITP performance is slow due to brute force search
- Coq is just bad by accident
- Throwing away proof terms will solve everything
- Reflection will solve everything

### Myth-Dispelling Example: Rewriting
- Coq's setoid_rewrite tactic is cubic in the number of binders
  + Even when there are no occurences!
  + Talk about evar maps
  + Inefficiency here is baked into the locally-nameless representation of evars + use of general evars for rewrite unification (but this is not unreasonable)
- There are only linearly many places to "search", so it's not really a search-space explosion.
  + In general brute-force search can be keyed to patterns, so I haven't really encountered unsurmountable issues of brute-force search being too slow
- Lean seems to have the same perf as Coq.
- Moreoever, writing a rewrite tactic which incurs only linear overhead is highly-non-trivial
  + show obvious rewrite tactic
  + it's at least quadratic
  + throwing away the proof term buys us nothing asymptotically as long as we still need to track the theorem statement and have each recursive call be considered to be "proving something"
    . anecdotally CakeML bootstrapping in HOL might be hitting similar bottlenecks
- Reflection solves things here because reflection is not proving something at every step.  Reflection is computing the new goal, does not track nor store the old goal, and so isn't really a "proof engine"
  + reflection success stories are almost all specialized
  + augmenting reflection to be a proof engine would bring in all the same issues of the proof engine; reflection doesn't magically fix things

### Where does this leave us?
- As I see it, we could cut industrial software into neatly packaged units which are sufficiently small that we can handle them with current methods.
  + Seems improbable, I'm told that systems code like drivers, and also symmetric crypto, are developed adversarially/empirically and don't really admit clean factorings.
- We can try to build reflective automation for all the domains we care about, from scratch each time.
  + This is hard to scale, and proving the reflective automation itself is subject to all the same scaling issues when it gets big enough.  (The reflective rewriter/partial evaluator/term transformer for fiat-crypto is big enough to hit this, but it was surmountable.)
- We can tackle this problem head-on, develop a theory of what asymptotic behavior makes for a proof engine that's adequate at scale, and build adequate tools, and live up to the promise of formal verification.
  + (I of course advocate this last one)

### Q & A Slide



----------------------


TODO:
- talk about performance issues as duplicative/needless bookkeeping
- performance issues are not just for verification, also show up in math





----------------------------

look into https://thenounproject.com/
