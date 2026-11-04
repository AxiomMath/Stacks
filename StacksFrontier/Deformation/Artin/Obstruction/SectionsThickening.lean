module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.NilIdeal
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsFunctor

/-!
# The base-change immersion of a thickening, and the cohomology it does not change

Let `q : W → S` be a morphism of schemes and let `T' → T` be a morphism of schemes over `S`.
Base change along `q` gives a morphism `i : W_{T'} → W_T` of the fibre products, and the square
```
W_{T'} ⟶ W_T
  ↓        ↓
  T'   ⟶  T
```
is a pullback square. So if `T' → T` is a thickening — a closed immersion that is surjective on
points, which is what `Spec A → Spec A'` is for a surjection `A' → A` with nilpotent kernel —
then so is `i`, and the cohomology of a sheaf of modules on `W_{T'}` agrees with the cohomology
on `W_T` of its pushforward.

## Main definitions

* `Deformation.Artin.SectionsSheaf.baseChangeMap` — the morphism `W_{T'} → W_T`.

## Main results

* `Deformation.Artin.SectionsSheaf.isPullback_baseChangeMap` — the square above is a pullback.
* `Deformation.Artin.SectionsSheaf.isThickening_baseChangeMap` — a base change of a thickening
  is a thickening, at this square; `isClosedImmersion_baseChangeMap` is its closed-immersion
  half, and `isThickening_baseChangeMap_quotient` is the case of `Spec` of the quotient by
  an ideal of nilpotents.
* `Deformation.Artin.SectionsSheaf.baseChangeCohomologyIso` and
  `Deformation.Artin.SectionsSheaf.baseChangeCohomologyObjIso` — the comparison
  `Hⁿ(W_T, i_* G) ≅ Hⁿ(W_{T'}, G)`, naturally in `G` and at a fixed `G`.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Cohomology.AffineBase

universe u

namespace Deformation.Artin.SectionsSheaf

variable {S W : Scheme.{u}} (q : W ⟶ S)

/-- The morphism `W_{T'} → W_T` obtained by base change along `q` from a morphism `T' → T`
of schemes over `S`. It is the morphism underlying the value of
`Deformation.Artin.SectionsSheaf.baseChangeOver` on `T' → T`. -/
abbrev baseChangeMap {T T' : Over S} (α : T' ⟶ T) :
    pullback T'.hom q ⟶ pullback T.hom q :=
  ((baseChangeOver q).map α).left

/-- `W_{T'} → W_T` is compatible with the projections to `T'` and `T`. -/
theorem baseChangeMap_comp_fst {T T' : Over S} (α : T' ⟶ T) :
    baseChangeMap q α ≫ pullback.fst T.hom q = pullback.fst T'.hom q ≫ α.left :=
  pullback.lift_fst _ _ _

/-- `W_{T'} → W_T` is compatible with the projections to `W`. -/
theorem baseChangeMap_comp_snd {T T' : Over S} (α : T' ⟶ T) :
    baseChangeMap q α ≫ pullback.snd T.hom q = pullback.snd T'.hom q :=
  pullback.lift_snd _ _ _

/-- The base-change square is a pullback square: `W_{T'}` is the fibre product of `T'` and `W_T`
over `T`. -/
theorem isPullback_baseChangeMap {T T' : Over S} (α : T' ⟶ T) :
    IsPullback (baseChangeMap q α) (pullback.fst T'.hom q) (pullback.fst T.hom q) α.left := by
  refine IsPullback.of_right ?_ (baseChangeMap_comp_fst q α)
    (IsPullback.of_hasPullback T.hom q).flip
  rw [baseChangeMap_comp_snd q α, Over.w α]
  exact (IsPullback.of_hasPullback T'.hom q).flip

/-- A base change of a thickening is a thickening, at the base-change square: if `T' → T` is a
closed immersion surjective on points then so is `W_{T'} → W_T`, so the two have the same
underlying topological space. -/
theorem isThickening_baseChangeMap {T T' : Over S} (α : T' ⟶ T)
    (hα : Stacks.Thickenings.IsThickening α.left) :
    Stacks.Thickenings.IsThickening (baseChangeMap q α) :=
  Stacks.Thickenings.isThickening_of_isPullback (isPullback_baseChangeMap q α) hα

/-- The base change of a thickening is in particular a closed immersion. -/
theorem isClosedImmersion_baseChangeMap {T T' : Over S} (α : T' ⟶ T)
    (hα : Stacks.Thickenings.IsThickening α.left) :
    IsClosedImmersion (baseChangeMap q α) :=
  (isThickening_baseChangeMap q α hα).1

/-- For an ideal `I` all of whose elements are nilpotent, the morphism `W_{A/I} → W_A` obtained
by base change from `Spec(A/I) → Spec A` is a thickening: a closed immersion surjective on
points, so the two have the same underlying topological space. -/
theorem isThickening_baseChangeMap_quotient {A : Type u} [CommRing A] (I : Ideal A)
    (hI : ∀ x ∈ I, IsNilpotent x) (t : Spec (CommRingCat.of A) ⟶ S) :
    Stacks.Thickenings.IsThickening (baseChangeMap q
      (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) rfl :
        Over.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ t) ⟶ Over.mk t)) :=
  isThickening_baseChangeMap q _ (Stacks.Thickenings.isThickening_specMap_quotientMk I hI)

section Cohomology

attribute [local instance] HasDerivedCategory.standard

variable {T T' : Over S} (α : T' ⟶ T) (hα : IsClosedImmersion (baseChangeMap q α))

/-- For `W_{T'} → W_T` a closed immersion, the `n`-th cohomology on `W_{T'}` of a sheaf of
modules, with scalars restricted to the global functions on `W_T`, is the `n`-th cohomology on
`W_T` of its pushforward, naturally in the module. -/
def baseChangeCohomologyIso (n : ℕ) :
    letI := hα
    (moduleGlobalSections (pullback T'.hom q)).rightDerived n ⋙
        ModuleCat.restrictScalars (baseChangeMap q α).appTop.hom ≅
      AlgebraicGeometry.Scheme.Modules.pushforward (baseChangeMap q α) ⋙
        (moduleGlobalSections (pullback T.hom q)).rightDerived n :=
  letI := hα
  Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso (baseChangeMap q α) n

/-- For `i : W_{T'} → W_T` a closed immersion and a fixed sheaf of modules `G` on `W_{T'}`,
`Hⁿ(W_T, i_* G) ≅ Hⁿ(W_{T'}, G)`. -/
def baseChangeCohomologyObjIso (G : (pullback T'.hom q).Modules) (n : ℕ) :
    letI := hα
    ((moduleGlobalSections (pullback T.hom q)).rightDerived n).obj
        ((AlgebraicGeometry.Scheme.Modules.pushforward (baseChangeMap q α)).obj G) ≅
      (ModuleCat.restrictScalars (baseChangeMap q α).appTop.hom).obj
        (((moduleGlobalSections (pullback T'.hom q)).rightDerived n).obj G) :=
  letI := hα
  Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward (baseChangeMap q α) G n

end Cohomology

end Deformation.Artin.SectionsSheaf

end
