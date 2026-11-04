module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.StructureSheafPerfect
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalRepresentationOfADerivedMap

/-!
# The coevaluation of a pairing in `D(O)`, read as a map of complexes

Let `(C, O)` be a ringed site, let `ℳ` and `𝒩` be K-flat complexes of `O`-modules, and let

`η : 𝟙 ⟶ Q(ℳ) ⊗^L Q(𝒩)`

be a morphism out of the monoidal unit of `D(O)` — for instance the coevaluation of an exact
pairing. Then `η` is, after the two comparisons of Stacks 0FPT, a morphism

`Q(O[0]) ⟶ Q(Tot(ℳ ⊗ 𝒩))`

between the images of two complexes, and along the arrows of a covering sieve of every object of
`C` that morphism is the image of a genuine map of complexes.

This is the step the source of the first assertion of Stacks 0FPV opens the direct-summand
argument with: "consider the map `η : O ⟶ Tot(ℳ ⊗ 𝒩)`. After replacing `X` by the members of a
covering, we can find an integer `N` and … sections `fᵢ` and `gᵢ` … such that
`η(1) = ∑ᵢ fᵢ ⊗ gᵢ`." The first sentence is what this file supplies; the decomposition of the
section is `AlgebraicGeometry.RingedSite.exists_sieve_sum_tensorTotalSection`.

## Main results

* `AlgebraicGeometry.RingedSite.coevaluationUnitHom`: `η`, read as a morphism
  `Q(O[0]) ⟶ Q(Tot(ℳ ⊗ 𝒩))`.
* `AlgebraicGeometry.RingedSite.unitIso_hom_comp_coevaluationUnitHom`: that morphism is pinned
  down by `η`.
* `AlgebraicGeometry.RingedSite.coevaluationUnitHomRestrict`: its restriction to the slice over
  an object, which is the morphism Stacks 08FR (1) is applied to.

## Implementation notes

The monoidal unit of `D(O)` is the structure sheaf in degree zero, and `UnitIso` of
`Stacks.SheafOfModules.DerivedMonoidal.SymmetricMonoidalDerived` says so with the complex spelled
`(CochainComplex.singleFunctor _ 0).obj (SheafOfModules.unit _)`, while
`AlgebraicGeometry.RingedSite.structureSheafComplex` spells it
`(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _)`. Mathlib's
`CochainComplex.singleFunctor` is *definitionally* the functor
`HomologicalComplex.single _ (ComplexShape.up ℤ)`, so the two are the same complex and no
comparison isomorphism is introduced; the development's spelling is the one used below, so that
the strict perfection already proved for it applies.

The localization is Stacks 08FR (1),
`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap`, applied to
`coevaluationUnitHomRestrict`: it asks that the source be strictly perfect *over the slice*, and
that is `AlgebraicGeometry.RingedSite.isStrictlyPerfect_restrictComplex_structureSheafComplex`.
Getting the morphism into `D(O|_U)` in the first place is the bookkeeping done here: restriction
to the slice is an exact functor, so `CategoryTheory.Functor.mapDerivedCategoryFactors`
identifies its action on the image of a complex with the image of the restricted complex, and
`AlgebraicGeometry.RingedSite.restrictComplex` *is* that restriction applied degreewise, so the
identification needs no further comparison.

**Why the application of 08FR (1) is left to the consumer rather than stated here.** Its
conclusion existentially quantifies five instances — the two slice sheafification hypotheses and
the additivity and finite (co)limit preservation of restriction along an arrow — and the chain map
`β` and its defining equation have types depending on them. Those existentials cannot be
discharged against the ambient instances: `HasSheafify` and `WEqualsLocallyBijective` are
propositions, so proof irrelevance settles them, but `CategoryTheory.Limits.PreservesFiniteLimits`
carries the preservation data, so the instance 08FR (1) chose and the one in scope here are not
the same term and the equation is not the same equation. A statement here could therefore only
repeat 08FR (1)'s conclusion verbatim at this `α`, which is what applying the lemma already says.

Nothing here is a clause of a tag — it is a step of the proof of Stacks 0FPV's first assertion,
and of Stacks 0FPD's — so no `@[stacks …]` attribute is attached. In particular `η` is taken as
an arbitrary morphism out of the unit rather than as the coevaluation of a pairing: the pairing
is nowhere used, and the consumer supplies `η_ M N` composed with the identifications of the two
representatives.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u d

namespace AlgebraicGeometry.RingedSite

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction along an arrow of the site preserves finite limits; it is exact. -/
local instance overMapPreservesFiniteLimits {U V : X.C} (g : V ⟶ U) :
    PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction along an arrow of the site preserves finite colimits; it is exact. -/
local instance overMapPreservesFiniteColimits {U V : X.C} (g : V ⟶ U) :
    PreservesFiniteColimits
      (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

section AnyDerivedCategory

variable [HasDerivedCategory.{d}
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **A morphism of `D(O)` out of the monoidal unit, read as a morphism between the images of two
complexes.** For K-flat `ℳ` and `𝒩`, the two comparisons of Stacks 0FPT — the identification of
the monoidal unit of `D(O)` with `Q(O[0])` and the identification of `Q(ℳ) ⊗^L Q(𝒩)` with
`Q(Tot(ℳ ⊗ 𝒩))` — turn `η : 𝟙 ⟶ Q(ℳ) ⊗^L Q(𝒩)` into a morphism
`Q(O[0]) ⟶ Q(Tot(ℳ ⊗ 𝒩))`. K-flatness is used exactly once, in the second comparison. -/
def coevaluationUnitHom
    (Mc Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)
    (hM : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Mc)
    (hN : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Nc)
    (η : letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
      𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O) ⟶
        DerivedCategory.Q.obj Mc ⊗ DerivedCategory.Q.obj Nc) :
    DerivedCategory.Q.obj (structureSheafComplex X) ⟶
      DerivedCategory.Q.obj
        ((Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)) :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  (Stacks.SheafOfModules.DerivedMonoidal.symmetricMonoidalDerived X.O).unitIso.inv ≫ η ≫
    ((Stacks.SheafOfModules.DerivedMonoidal.symmetricMonoidalDerived X.O).comparison
      Mc Nc hM hN).hom

end AnyDerivedCategory

attribute [local instance] HasDerivedCategory.standard

/-- **The coevaluation, restricted to a slice of the site.** Restriction to the slice over `U` is
an exact functor, so `CategoryTheory.Functor.mapDerivedCategoryFactors` identifies its action on
the image of a complex with the image of the restricted complex, and
`AlgebraicGeometry.RingedSite.coevaluationUnitHom` becomes a morphism
`Q(O[0]|_U) ⟶ Q(Tot(ℳ ⊗ 𝒩)|_U)` of `D(O|_U)`. This is the morphism Stacks 08FR (1) is applied
to. -/
def coevaluationUnitHomRestrict
    (Mc Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)
    (hM : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Mc)
    (hN : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Nc)
    (η : letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
      𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O) ⟶
        DerivedCategory.Q.obj Mc ⊗ DerivedCategory.Q.obj Nc) (U : X.C) :
    DerivedCategory.Q.obj (X.restrictComplex (structureSheafComplex X) U) ⟶
      DerivedCategory.Q.obj (X.restrictComplex
        (Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O) U) :=
  inv ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategoryFactors.hom.app (structureSheafComplex X)) ≫
    (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.map (coevaluationUnitHom X Mc Nc hM hN η) ≫
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategoryFactors.hom.app
        (Mc ⊗ Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **`coevaluationUnitHom` is pinned down by `η`.** Composing it with the identification of the
monoidal unit with `Q(O[0])` recovers `η` followed by the comparison of Stacks 0FPT: the
definition is not an unconstrained morphism of its type, and since both identifications are
isomorphisms it is zero only if `η` is. -/
theorem unitIso_hom_comp_coevaluationUnitHom
    (Mc Nc : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)
    (hM : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Mc)
    (hN : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Nc)
    (η : letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
      𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O) ⟶
        DerivedCategory.Q.obj Mc ⊗ DerivedCategory.Q.obj Nc) :
    (Stacks.SheafOfModules.DerivedMonoidal.symmetricMonoidalDerived X.O).unitIso.hom ≫
        coevaluationUnitHom X Mc Nc hM hN η =
      η ≫ ((Stacks.SheafOfModules.DerivedMonoidal.symmetricMonoidalDerived X.O).comparison
        Mc Nc hM hN).hom := by
  rw [coevaluationUnitHom, Iso.hom_inv_id_assoc]
  rfl

end AlgebraicGeometry.RingedSite

end
