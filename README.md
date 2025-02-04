# HoTT_Model

This repository aims to formalize [the simplicial model of HoTT](https://arxiv.org/abs/1211.2851). All the indexes below refer to this paper.

## On the semantic side:

### Contextual Category
- [x] Contextual category (1.2.1)
- [x] Logical structures on a contextual category (Appendix B)

### Universe
- [x] Universe in a category, i.e., a morphism with chosen pullbacks (1.3)
- [x] Universe induces a contextual category (1.3.2, 1.3.3)
- Logical structures on a universe in a locally closed cartesian category (1.4)
- If the universe has a certain logical structures, so does the contextual category it induces (1.4.15)
- [x] $\Pi$-type has been completely formalized for the last two points.

### The simplicial model
1. Construction
- [x] $\alpha$-small well-ordered morphisms of simplicial sets (2.1.1, 2.1.3)
- [x] The isomorphism classes form a set, or is `Small` in Lean. (Footnote 9)
- [x] The isomorphism classes form a functor $\mathbf W_{\alpha}$ from simplicial sets to sets, and the functor preserves limits (2.1.4)
- [x] The functor is represented by $W_\alpha$ (2.1.5)
- [x] The canonical map $\tilde W_\alpha \to W_\alpha$ is strictly universal with respect to all the $\alpha$-small well-ordered morphisms
- [x] The subobject $U_\alpha$ corresponding to all the $\alpha$-small well-ordered Kan fibrations and a map $\tilde U_\alpha \to U_\alpha$ (2.1.9)
- [x] $\tilde U_\alpha \to U_\alpha$ is a Kan fibration (2.1.10)
- [x] $\tilde U_\alpha \to U_\alpha$ is strictly universal with respect to all the $\alpha$-small well-ordered Kan fibrations (2.1.12)
- [x] $\tilde U_\alpha \to U_\alpha$ forms a universe
- [x] Dependent products of a small morphism along a small morphism is again small.

2. Property
- The universe given by $\tilde U_\alpha \to U_\alpha$ has the logical structures
- [x] Proved $\Pi$-type
- The contextual category satisfies univalence

### Locally cartesian closedness
- [x] Definition of locally cartesian closed categories ([Reference](https://github.com/sinhp/Poly))
- [x] Every presheaf category is locally cartesian closed categories. Here by presheaf category we mean`Cᵒᵖ ⥤ Type max v w`, where the type of morphisms of `C` lies in `Type v`, hence not necessarily `Cᵒᵖ ⥤ Type v`. In particular `SSet.{u}` is locally cartesian closed for any `u`.
- [x] A not so trivial lemma: dependent products of a pullback along a pullback is a pullback.

## On the syntactic side
- Aim to formalize a type theory. Since formalizing the whole Martin-Löf type theory would be too much work, only
	trying [pure type system](https://ncatlab.org/nlab/show/pure+type+system) now
- [x] Define the syntactic category of PTS. Prove that it is contextual.
- Aim to define an interpretation function to connect the syntactics and semantics.
