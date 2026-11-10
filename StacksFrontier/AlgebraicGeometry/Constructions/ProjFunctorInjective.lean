module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleColimitCone
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleMorphismConverse

/-!
# The comparison `F(Y) ⟶ Mor(Y, Proj(A))` is injective

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)` and `Y` a scheme. Section 27.12 forms the
functor `F` by taking, at a quasi-compact `Y`, the union `F(Y) = ⋃_{d ≥ 1} F_d(Y)` of the sets of
strict equivalence classes of triples of weight `d` along the weight transitions
`F_d ⟶ F_{d'}`, `d ∣ d'`, of `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.veronese` — that
is, `F(Y)` is the colimit of the `F_d(Y)` over divisibility — and extending to a general `Y` by
`F(Y) = lim_{V ⊆ Y quasi-compact open} F(V)`. [Stacks, Tag 01NC] asserts that `F` is representable
by `X`, the comparison being
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.classifyingMorphism`, the map `F_d(Y) ⟶
Mor(Y, X)` of [Stacks, Tag 01N8] on classes, which is constant along the weight transitions
(`Fd.classifyingMorphism_veronese`) and so is a map out of the colimit.

**This file proves that comparison injective**, for every scheme `Y`:

* at a fixed weight, `Fd.classifyingMorphism` is injective;
* across two weights `d` and `d'`, two classes which classify the same morphism have the same
  image in `F_{d d'}(Y)` under the weight transitions, which is what "they are identified in the
  colimit `F(Y)`" says.

Surjectivity is proved in the sibling
`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorSurjective.lean`; see the implementation
notes for what the two files together do and do not cover, and the module docstrings of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorQuasiCompact.lean` and
`StacksFrontier/AlgebraicGeometry/OrderedOpenCover.lean` for the two reductions of the source's
proof that the argument uses.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.weightCongr`: the set `F_d(Y)` read at a
  weight equal to `d`, the bookkeeping that lets the images of `F_d(Y)` and `F_{d'}(Y)` in
  `F_{d d'}(Y)` and `F_{d' d}(Y)` be compared.

## Main results

* `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.classifyingMorphism_injective`: **at a
  fixed weight the comparison is injective**: two classes of weight-`d` triples which classify the
  same morphism `Y ⟶ Proj(A)` are equal.
* `Fd.veronese_eq_weightCongr_veronese_of_classifyingMorphism_eq`: **the comparison out of the
  colimit is injective**: classes of weights `d` and `d'` which classify the same morphism agree
  at the common weight `d d'`.

## Implementation notes

**Where injectivity comes from.** At a fixed weight it is the uniqueness half of [Stacks, Tag
01N9]: `Stacks.AlgebraicGeometry.ProjTripleMorphismConverse.sectionsEquiv_of_sameMorphism` says
that two weight-`d` graded maps whose classified morphisms agree are strictly equivalent, which on
the quotient `F_d(Y)` is injectivity. Across two weights the weight transitions are used to reduce
to one weight: by `Fd.classifyingMorphism_veronese` the transition does not change the classified
morphism, so the two images in `F_{d d'}(Y)` classify the same morphism and the fixed-weight case
applies. In the vocabulary of bundled triples the same content is
`Stacks.AlgebraicGeometry.ProjTripleMorphismConverse.agreeAtLcm_of_sameMorphism`, clause (4) ⇒ (1)
of [Stacks, Tag 01NB], stated at the least common multiple rather than at the product and before
passing to classes.

**Why `Fd.weightCongr` is needed.** The transition out of `F_d(Y)` at the multiplier `d'` lands in
`F_{d' d}(Y)` and the transition out of `F_{d'}(Y)` at the multiplier `d` lands in `F_{d d'}(Y)`.
The two weights are equal but not syntactically identical, and the weight is a parameter of the
type, so one of the two must be transported. The transport is along an equality of natural numbers
only; `Fd.classifyingMorphism_weightCongr` says it does not change the classified morphism, and
its proof is `subst`.

**Where surjectivity is.** Not here:
`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorSurjective.lean` proves that a morphism
from a quasi-compact scheme into `X` is classified by a triple, namely by the pullback of the
universal family `(d, 𝒪_{U_d}(d), ψ^d)` of [Stacks, Tag 01N9] along the factorization through a
single `U_d`. What that file supplies, and what was missing here, are the two statements about
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.IsCompatible` the argument runs on: that the
universal family is compatible with the identity of `U_d`
(`StacksFrontier/AlgebraicGeometry/Constructions/ProjUniversalCompatible.lean`), and that
compatibility is stable under pullback, which is the naturality in `Y` of the classification of
[Stacks, Tag 01N8].

**Where the functor `F` and the bijection are.** This file states injectivity as a statement about
the weight transitions, and so needs no functor. The functor itself —
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fcolim`, the colimit of the `F_d` along
divisibility, in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorColimit.lean`, and its extension
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.F` to a non-quasi-compact `Y`, in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorRepresentable.lean` — consumes the
theorem below, as `Fcolim.classifyingMorphism_injective`, to obtain the bijection
`F(Y) ≃ Mor(Y, X)` of [Stacks, Tag 01NC] as a single `Equiv` and the
`CategoryTheory.Functor.RepresentableBy` datum `F.representableBy`.

## References

* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
* [Stacks Project, Tag 01NB](https://stacks.math.columbia.edu/tag/01NB)
* [Stacks Project, Tag 01N9](https://stacks.math.columbia.edu/tag/01N9)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u w

namespace Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {Y : Scheme.{u}} {d d' : ℕ}

/-! ### Injectivity at a fixed weight -/

/-- **At a fixed weight the comparison `F_d(Y) ⟶ Mor(Y, Proj(A))` is injective**: two strict
equivalence classes of weight-`d` triples over `Y` which classify the same morphism are equal.

This is the uniqueness half of [Stacks, Tag 01N9] read on the classes. On representatives it is
`Stacks.AlgebraicGeometry.ProjTripleMorphismConverse.sectionsEquiv_of_sameMorphism`: the two
graded maps are strictly equivalent, which is exactly having the same class by
`Fd.mk_eq_mk_iff`. -/
theorem Fd.classifyingMorphism_injective (hd : 0 < d) :
    Function.Injective (Fd.classifyingMorphism 𝒜 hd (Y := Y)) := by
  intro ξ ξ'
  induction ξ using Quotient.ind with
  | _ t =>
    induction ξ' using Quotient.ind with
    | _ t' =>
      intro h
      have := t.isInvertible
      have := t'.isInvertible
      exact (Fd.mk_eq_mk_iff 𝒜 t t').mpr
        (ProjTripleMorphismConverse.sectionsEquiv_of_sameMorphism 𝒜 hd t.generated t'.generated h)

/-! ### Comparing two weights -/

/-- **The set `F_d(Y)` read at a weight equal to `d`.** The weight is a parameter of the type, so
the images of `F_d(Y)` and `F_{d'}(Y)` under the weight transitions of Section 27.12 land in
`F_{d' d}(Y)` and `F_{d d'}(Y)`, whose weights are equal without being syntactically identical;
this transports the second to the first. -/
def Fd.weightCongr (h : d = d') (ξ : Fd 𝒜 d Y) : Fd 𝒜 d' Y := h ▸ ξ

/-- **Reading a class at an equal weight does not change the morphism it classifies.** The
transport is along an equality of natural numbers and the two positivity hypotheses are
propositions. -/
theorem Fd.classifyingMorphism_weightCongr (h : d = d') (hd : 0 < d) (hd' : 0 < d')
    (ξ : Fd 𝒜 d Y) :
    Fd.classifyingMorphism 𝒜 hd' (Fd.weightCongr 𝒜 h ξ) = Fd.classifyingMorphism 𝒜 hd ξ := by
  subst h
  rfl

/-- **Stacks Tag 01NC: the comparison out of the colimit `F(Y)` is injective.** Let `A` be a
graded ring, `X = Proj(A)` and `Y` a scheme, and let `ξ ∈ F_d(Y)` and `ξ' ∈ F_{d'}(Y)` be strict
equivalence classes of triples, of weights `d, d' ≥ 1`, which classify **the same** morphism
`Y ⟶ X` by [Stacks, Tag 01N8]. Then `ξ` and `ξ'` have the same image in `F_{d d'}(Y)` under the
weight transitions `F_d ⟶ F_{d' d}` and `F_{d'} ⟶ F_{d d'}` of Section 27.12.

Since `F(Y)` is the colimit of the `F_d(Y)` over divisibility, this says precisely that the
comparison `F(Y) ⟶ Mor(Y, X)` is injective: two elements with the same image are identified at a
common weight.

The weight transition does not change the classified morphism
(`Fd.classifyingMorphism_veronese`), so both images classify the same morphism at the single
weight `d' d`, where `Fd.classifyingMorphism_injective` applies. -/
theorem Fd.veronese_eq_weightCongr_veronese_of_classifyingMorphism_eq (hd : 0 < d) (hd' : 0 < d')
    (ξ : Fd 𝒜 d Y) (ξ' : Fd 𝒜 d' Y)
    (h : Fd.classifyingMorphism 𝒜 hd ξ = Fd.classifyingMorphism 𝒜 hd' ξ') :
    Fd.veronese 𝒜 d' ξ
      = Fd.weightCongr 𝒜 (Nat.mul_comm d d') (Fd.veronese 𝒜 d ξ') := by
  refine Fd.classifyingMorphism_injective 𝒜 (Nat.mul_pos hd' hd) ?_
  refine (Fd.classifyingMorphism_veronese 𝒜 hd hd' ξ).trans (h.trans ?_)
  exact (Fd.classifyingMorphism_veronese 𝒜 hd' hd ξ').symm.trans
    (Fd.classifyingMorphism_weightCongr 𝒜 (Nat.mul_comm d d') (Nat.mul_pos hd hd')
      (Nat.mul_pos hd' hd) (Fd.veronese 𝒜 d ξ')).symm

end Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor

end
