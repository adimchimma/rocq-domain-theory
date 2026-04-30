# NOTE on AI Use

## 1: Planning

### Fromalization

Given my lack of familiarity with developing large-scale `Rocq` formalisations, I elected to converse with `Claude` about Project Structure and 
Architecture. I already knew that the project would entail modernising **BKV** with `HB`, as that is in the Thesis Proposal, but I didn't want to fall into 
common pitfalls or make use of design patterns that are nonstandard in the `Rocq` community.

Actually, it didn't help as much as one might think -- though I guess that might have been a function of the model when I started the project. If you look 
far enough in the git history, you'll find that the project had an entirely different architecture that ended up not being viable.

Additionally, gaining an understanding of what I should focus my energy on learning and quirks of `Rocq` that I might encounter came as a direct result of 
asking LLMs questions, as well as reading docs, reports, other libraries, and the relevant textbooks/papers, of course. The best example of this was the 
definition of the `var_case` combinator. I can't seem to find the relevant prompts, but the current definition came at the heels of a long, detailed 
conversation about acceptable axioms to import.

### Thesis Writing

Similarly, AI found its use in helping organise the thesis itself. I didn't have guidance or some sort of template to work from, so I worked with Claude to 
help make some decisions. It was not my only reference, however, as I also heavily refered to [Analyzing Sheaves on Graphs](https://drive.google.com/file/d/1cPSvZZSqKs61v2ItzALuFXJCGpH_mcJW/view) (the undergraduate thesis by Godknows Awuku at the University of Ghana) and [Partial State in Dataflow-Based Materialized Views](https://jon.thesquareplanet.com/papers/phd-thesis.pdf) (the PhD thesis of Jon Gjengset at MIT). 
Notably, the decision to use “we” in the thesis came out of some tips it gave me on the typical vernacular of a "formal" thesis.

## 2: Cleanup

### Proof cleanup

This is a more mundane use case; however, I believe it's important to note it. One executive decision I made early on was to use as little proof automation 
as possible for several reasons I'll indicate later. A consequence of this is that proofs could become particularly verbose. I would often write the proofs 
explicitly, and then do a second pass to shrink cases that might be trivial, or apply the tactic sequencing operator `;` where it makes sense, etc.
However, in the cases where a proof might still look particularly unwieldy, I would use `Claude` to help simplify/shorten the proofs, making sure not much information about the mechanics of the underlying proof is lost. 

A typical prompt might be: 
```txt
Could you help me clean up this proof if possible. I feel that it is unnecessarily verbose and can possibly be shortened in
a way that preserves as much information from stepping as possible.
```

#### Reasoning for sparing use of proof automation
- I wanted to familiarise myself with low-level tactics (That is part of the point of the thesis)
- I wanted to have as little computational expense as possible
- Given that I'm also a mathematician, I wanted to make sure that I fully understand the translation from pen & paper proofs to `Rocq` formalisation


### Notes -> Inline Docs

It would also help write documentation in a more comprehensible way. I like to keep notes for myself to better understand where I am in the implementation 
process. By this, I don't necessarily just mean things that might be considered documentation already; it would often entail my thought process at the present moment (often including profanity), as well as relevant links to ncatlab, Wikipedia, and whatever conglomeration of tabs I had open at the time. 
When I was finished, I would often ask `Claude` to help parse out the unnecessary and confusing materials and turn what was left into documentation.

## 3: Critique
Finally, I would have `Claude` provide detailed critiques of my work so I could better understand the reasoning behind best practices, as well as develop a 
strict formal understanding of the structures I'm working with.

## Other

It also provided templates for the `design-decisions.md`, `migration-notes.md` and `project-structure.md` files
