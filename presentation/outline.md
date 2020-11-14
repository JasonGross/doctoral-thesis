# Outline of Defense

## Outline

- Point at the problem, explain why it’s important (standing in the way of verification reaching its promise)
  + Note, perhaps, that no-one seems to be tackling it or even systematically investigating it --- I have more to say about this, but only have time to hint at this in the defense
- Describe what current research progress towards this big problem looks like, using the particular example of the progress I've made towards it (fiat-crypto) with my colleagues during my PhD
- Share what I've learnt about how this problem can currently be chipped away at with current techniques
- Share what I've learnt about how the larger problem might need very different research that no-one seems to currently be doing

## The Problem

### Why Verification?
- Bugs bad.
- Verification fix. (Note that I'm talking about ITPs; human help is important for difficult problems)

### What Done?
- CompCert, seL4, CertiKOS (point out Fiat-Crypto as the new project I enabled)
- scale of these projects vs scale of industry

### What Problem?
- There's a gap between what academia and industry
- The bigger problem is asymptotic performance; I'll come back to this in a moment
- Currently we academics carve off a small chunk of the gap and spend a lot of time verifying it
  + I'll be talking about the small chunk that I helped carve off

TODO: maybe reorganize this next bit?
- More broadly, though I don't see us closing this gap with the research we're currently doing; let me share a bit of what I mean by this, before coming back to why I think we need a more systematic study at the end of the defense.
- Slide with allocation of PhD time
- The performance challenges scale *super-linearly* with the size and complexity of the programs being verified.
- The problem is asymptotic performance.

## Fiat-Crypto

- Carving off another chunk

### Which Goal?

- Low-level cryptographic primitives
- Desiderata:
  + the code we verify must be fast and constant time
    - Justification: server load, security
  + it should not take too much effort to add & prove a new algorithm, prime, architecture, etc
    - Justification: scalability of human effort, edit-compile-debug loops are important here
  + is should not take too much time for Coq to run the verification (asymptotics are important here)
    - Justification: Needs to be checkable in time for industry deadlines, in time to be usable
- Our output artifact is actually pretty cool, and can automatically generate basically verified code on the command line, in seconds (not hours or days or weeks), for given just the prime, the bitwidth, and the name of the high-level algorithm

### Methodology
- Carve up the low-level code into neatly-separated conceptually distinct units that are small enough to not hit asymptotic issues during interactive verification
  + My colleagues did most of this, though I helped them see how factoring and abstraction impact performance of verification effort

TODO: describe abstraction in terms of excessive unfolding, either here or elsewhere

- The remaining chunk is *partial evaluation*
  + Describe it
  + Note that it's too big to handle interactively with reasonable performance (include perf plots of rewrite)
  + The underlying reason for this chunk being hard is that all of the abstraction barriers that we introduced to carve the problem up into manageable chunks are broken here, so that we get fast low-level code out (this is a general pattern around performant code)
  + A large chunk of my PhD work was making this possible in a way that scales

### Partial Evaluation and Rewriting
- Requirements:
  - β-reduction (eliminating function call overhead)
  - ιδ-reduction + rewrites (inlining definitions to eliminate function call overhead, also arithmetic simplification)
    - Note that without this we get quartic asymptotics of the # lines of code rather than merely quadratic, so it's not really acceptable to save for a later stage
  - Code sharing preservation (to avoid exponential blowup in code size)
- Obvious Requirements:
  - Verified (and not extending the TCB)
  - Performant (should not introduce extra super-linear factors --- note that we don't quite manage this one, but we do a lot better than the interactive solutions)
- Implementation:
  - Reflective so as to not extend the TCB and to perform fast enough
    - Side benefit: we can extract it to OCaml to run as a nifty command-line utility
  - NbE (for β) + let-lifting (code-sharing) + rewriting (ιδ+rewrite)
    - Note that we use some tricks for speeding up rewriting such as pattern-matching compilation, on-the-fly emitting identifier codes so that we can use Coq's/OCaml's pattern matching compiler, pre-evaluating the rewriter itself
    - TODO: Spend some slides talking about these
- Evaluation:
  - It works!
  - It's performant!
  - It seems like it would also solve one of the two performance issues that killed the parser-synthesizer I worked on for my masters.

## Takeaways
- Asymptotic scaling of interactive proof assistant response is a real problem!
- Current method---of working around it by breaking the problem into small enough chunks and solving remaining chunks with specialized reflective solutions---does seem to work.
  - I'm not optimistic about being able to break things down enough to handle them all interactively; even in very abstract math (category theory), I ran into issues where the way mathematicians did it was not sufficient.  Furthermore basically all code that needs to be fast, and a great deal of systems code, inlines definitions in a way that causes performance issues.
  - And reflective automation requires enormous investment of effort for each new problem.
  - Because reflection is not a proof engine made of small pieces that can each be said to make progress towards proving a goal, it's not easy to mix-and-match.
  - I needed let-lifting; prior work had already done NbE and reflective rewriting, but fusing them with let-lifting in a performant way seems to have required re-engineering them almost from scratch.
- Does it have to be this way?
  - No! (I hope)
  - No one seems to be studying why proof engines are asymptotically slow!
  - It's not just accident; there are good reasons that obvious solutions have the wrong asymptotics, and there's so much going on that it's not even clear yet what the specification of "adequate performance" is.
  - I think solving this problem---getting the basics right, asymptotically---will drastically accelerate the scale of what we as a field can handle, and bring verification closer to it's promise and potential.

### Q & A Slide



----------------------


TODO:
- talk about performance issues as duplicative/needless bookkeeping
- moving the proof engine to be reflective won't solve things; where to put this?
- talk about recursive problem
----------------------------

look into https://thenounproject.com/
