module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.ClosedSupportPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction
public import StacksFrontier.CategoryTheory.Triangulated.LocalizingAdmissible

/-!
# Support of the twisted inverse image and the comparison of Tag 0A9L

Let `f : X ⟶ Y` be a morphism of schemes, let `j : V ⟶ Y` be an open immersion and let

```
U --j'--> X
|         |
f'        f
v         v
V --j---> Y
```

be the base change of `j` along `f`, so that `U = f^{-1}(V)`. Write `a` and `a'` for the twisted
inverse images of [Stacks, Tag 0A9E] along `f` and `f'` and write

`(0A9L) : (j')^* ∘ a ⟶ a' ∘ j^*`

for the comparison of [Stacks, Tag 0A9L], which is
`Stacks.Duality.OpenImmersion.twistedInverseImageRestrictionMap`.

[Stacks, Tag 0A9N] relates the support of the values of `a` to invertibility of (0A9L). Its
part (2) is proved here: *for every `Q` in `D_QCoh(𝒪_Y)` supported on `Y ∖ V` the image `a(Q)` is
supported on `X ∖ U` if and only if (0A9L) is an isomorphism on all `K` in `D_QCoh(𝒪_Y)`.*

The argument is the source's, read through two elementary reductions.

*Support off an open is vanishing of the restriction.* Restriction along an open immersion is
exact, so it commutes with the cohomology sheaves, and the stalk of a restricted module at a
point of the open is the stalk of the module at its image. Hence the cohomology of `E` is
supported in the complement of the image of `j` exactly when `j^*E` is a zero object —
`cohomologySupportedOn_compl_range_iff_isZero_derivedRestrict`.

*The comparison is the restricted unit, up to two invertible arrows.* The composite defining
(0A9L) is `(j')^*` of `a` of the unit of `j^* ⊣ Rj_*`, then `(j')^*` of the inverse of `ξ`, then
the counit of `(j')^* ⊣ Rj'_*`; the last two are invertible, the second by the instance argument
carried by Tag 0A9L and the third because `j'` is an open immersion. So (0A9L) is invertible on
`K` precisely when `a(K)|_U ⟶ a(Rj_*(K|_V))|_U` is — this is the "in particular" that follows the
source's displayed formula — which is `isIso_twistedInverseImageRestrictionMap_app_iff`.

With these in hand the source's proof is short. Given the support condition and `K`, complete the
unit `K ⟶ Rj_*(K|_V)` to a distinguished triangle with third vertex `Q`. Applying `j^*` to it and
using that `j^*` of the unit is invertible — the counit of `j^* ⊣ Rj_*` being invertible — gives
`j^*Q = 0`, that is, `Q` is supported on `Y ∖ V`. So `a(Q)` is supported on `X ∖ U`, i.e.
`(j')^*a(Q) = 0`; applying the triangulated functor `a ⋙ (j')^*` to the triangle, a distinguished
triangle with vanishing third vertex has invertible first map, which is the reduced form of
(0A9L) on `K`. Conversely, if `Q` is supported on `Y ∖ V` then `j^*Q = 0`, hence `a'(j^*Q) = 0`,
and invertibility of (0A9L) on `Q` transports that vanishing to `(j')^*a(Q)`.

## Main results

All in the namespace `Stacks.Duality.OpenImmersion`.

* `cohomologySupportedOn_compl_range_iff_isZero_derivedRestrict` and its subcategory form
  `cohomologySupportedOn_compl_range_iff_isZero_quasiCoherentDerivedRestrict`.
* `isIso_liftDerivedRestrictPushforwardAdjunction_counit_app_iff` — the subcategory lift costs
  nothing for the counit, the companion of
  `Stacks.Duality.OpenImmersion.isIso_liftDerivedRestrictPushforwardAdjunction_unit_app_iff`.
* `twistedInverseImageRestrictionMap_app_eq` and
  `isIso_twistedInverseImageRestrictionMap_app_iff` — the comparison of Tag 0A9L read on an
  object.
* `twistedInverseImage_cohomologySupportedOn_iff_isIso_restrictionMap` — **[Stacks, Tag 0A9N],
  part (2)**.

## Implementation notes

*Which support predicate.* `AlgebraicGeometry.CohomologySupportedOn` is stated at
`CategoryTheory.HasDerivedCategory.standard` and is therefore a statement about a different
derived category; the predicate used here is the model-free
`Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn` of
`StacksFrontier/Topology/Sheaves/Cohomology/SupportedComplexes/PushforwardAndRestriction.lean`. It
is always written out qualified: both names are in scope under `open AlgebraicGeometry` and the
ambiguity is compile-blocking. For the same reason the statements of
`Stacks.DerivedQCoh.isZero_derivedRestrict_of_supported` and
`Stacks.DerivedQCoh.cohomologySupportedOn_compl_of_isZero_derivedRestrict`, which are this file's
two implications at the standard model, are not the ones needed here.

*The model.* Everything is at the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, as Tag 0A9L is: that is the model at
which `D_QCoh(𝒪_X)` has the direct sums Brown representability needs, so it is the only one at
which the right adjoint `a` of [Stacks, Tag 0A9E] exists.

*What is assumed, and why it is not a weakening.* The hypotheses are exactly those of Tag 0A9L,
which the statement mentions and so cannot avoid: preservation of quasi-coherent cohomology by
the four derived direct images and by the two restrictions (the open-immersion case of
[Stacks, Tag 08D5] and the first half of [Stacks, Tag 0A9E]); the two `IsLeftAdjoint` instances,
which are the second half of Tag 0A9E and are what gives `a` and `a'` their meaning; and
invertibility of `ξ`, which is [Stacks, Tag 0A9K] and without which the composite defining
(0A9L) — it contains `ξ⁻¹` literally — does not exist. Quasi-compactness and
quasi-separatedness of the four schemes, which the source assumes, are *not* needed for part (2)
and are not assumed: the statement here is more general.

Part (2) is registered, at the source's hypotheses, on
`Stacks.Duality.OpenImmersion.qcqs_cohomologySupportedOn_iff_isIso_restrictionMap`.

## References

* [Stacks Project, Tag 0A9N](https://stacks.math.columbia.edu/tag/0A9N)
* [Stacks Project, Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.PushforwardRestriction (isZero_derived_of_homology_isZero
  isZero_sheafOfModules_of_stalk_isZero)

universe u

namespace Stacks.Duality.OpenImmersion

/-! ### Support off the image of an open immersion -/

section Support

variable {V Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j]

/-- **The stalks of a cohomology sheaf of a restriction.** At a point `v` of `V`, the stalk of
the `n`-th cohomology sheaf of `j^*E` is the stalk at `j(v)` of the `n`-th cohomology sheaf
of `E`.

Restriction along an open immersion is exact, so it commutes with the cohomology sheaves
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`), and restricting a sheaf of modules does
not change its stalks at points of the open
(`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`). -/
def stalkRestrictHomologyIso (n : ℤ) (E : DerivedCategory Y.Modules) (v : V) :
    TopCat.Presheaf.stalk (X := V)
        (((DerivedCategory.homologyFunctor V.Modules n).obj
          ((derivedRestrict j).obj E)).val.presheaf) v ≅
      TopCat.Presheaf.stalk (X := Y)
        (((DerivedCategory.homologyFunctor Y.Modules n).obj E).val.presheaf) (j.base v) :=
  Functor.mapIso (Scheme.Modules.toPresheaf V ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} v)
      (((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso n).app E) ≪≫
    (Scheme.Modules.restrictStalkNatIso j v).app
      ((DerivedCategory.homologyFunctor Y.Modules n).obj E)

/-- **Cohomological support in the complement of the image of an open immersion is the vanishing
of the restriction.** This is the form in which the condition of [Stacks, Tag 08DA] is used
below: `E` has all its cohomology supported on `Y ∖ V` if and only if `j^*E = 0`. -/
theorem cohomologySupportedOn_compl_range_iff_isZero_derivedRestrict
    (E : DerivedCategory Y.Modules) :
    Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
        Y.ringCatSheaf (Set.range j.base)ᶜ E ↔
      IsZero ((derivedRestrict j).obj E) := by
  constructor
  · intro hE
    refine isZero_derived_of_homology_isZero _ fun n => ?_
    refine isZero_sheafOfModules_of_stalk_isZero _ _ fun v => ?_
    exact (hE n (j.base v) (by simp)).of_iso (stalkRestrictHomologyIso j n E v)
  · intro hE n y hy
    obtain ⟨v, rfl⟩ : y ∈ Set.range j.base := by simpa using hy
    exact IsZero.of_iso
      (Functor.map_isZero
        (Scheme.Modules.toPresheaf V ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} v)
        (Functor.map_isZero (DerivedCategory.homologyFunctor V.Modules n) hE))
      (stalkRestrictHomologyIso j n E v).symm

end Support

/-! ### Restriction on the quasi-coherent derived categories is triangulated -/

section Lift

variable {V Y : Scheme.{u}} (j : V ⟶ Y) [IsOpenImmersion j]
  (hresj : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor V.Modules i).obj
      ((derivedRestrict j).obj K.obj)).IsQuasicoherent)
  (hpushj : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward j).obj K.obj)).IsQuasicoherent)

/-- **`j^*` on the quasi-coherent derived categories commutes with the shift.** It is the lift of
`D_QCoh(𝒪_Y) ⊆ D(𝒪_Y) --j^*--> D(𝒪_V)` through the inclusion of `D_QCoh(𝒪_V)`, so this is
`CategoryTheory.Functor.CommShift.ofComp` for that lift; it is stated rather than inferred
because the quasi-coherence hypothesis is not in the shape `∀ X, P (F.obj X)` that instance
search matches. -/
@[instance_reducible]
def quasiCoherentDerivedRestrictCommShift :
    (quasiCoherentDerivedRestrict j hresj).CommShift ℤ :=
  Functor.CommShift.ofComp
    (ObjectProperty.liftCompιIso _
      ((ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (A := Y.Modules) (SheafOfModules.isQuasicoherent Y.ringCatSheaf))) ⋙
        derivedRestrict j) hresj) ℤ

attribute [local instance] quasiCoherentDerivedRestrictCommShift

/-- **`j^*` on the quasi-coherent derived categories is exact.** Restriction along an open
immersion is exact on `D(𝒪_Y)` and the inclusion of `D_QCoh(𝒪_V)` is fully faithful and
triangulated, so the lift is triangulated as well. -/
theorem quasiCoherentDerivedRestrict_isTriangulated :
    (quasiCoherentDerivedRestrict j hresj).IsTriangulated := by
  let : NatTrans.CommShift (ObjectProperty.liftCompιIso
      (DerivedCategoryB.derivedCategoryB
        (A := V.Modules) (SheafOfModules.isQuasicoherent V.ringCatSheaf))
      ((ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
        (A := Y.Modules) (SheafOfModules.isQuasicoherent Y.ringCatSheaf))) ⋙
        derivedRestrict j) hresj).hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  exact (Functor.isTriangulated_iff_comp_right (ObjectProperty.liftCompιIso _ _ hresj)).2
    inferInstance

/-- **The subcategory lift costs nothing.** For strictly full subcategories `A ⊆ D(𝒪_Y)` and
`B ⊆ D(𝒪_V)` preserved by `j^*` and `Rj_*`, the counit of the restricted adjunction is invertible
at an object of `B` exactly when the counit of `j^* ⊣ Rj_*` is invertible at the underlying
object: the inclusion `B.ι` carries one to the other, and a fully faithful functor reflects
isomorphisms. This is the counit companion of
`Stacks.Duality.OpenImmersion.isIso_liftDerivedRestrictPushforwardAdjunction_unit_app_iff`. -/
theorem isIso_liftDerivedRestrictPushforwardAdjunction_counit_app_iff
    (A : ObjectProperty (DerivedCategory Y.Modules))
    (B : ObjectProperty (DerivedCategory V.Modules))
    (hres : ∀ K : A.FullSubcategory, B ((derivedRestrict j).obj K.obj))
    (hpush : ∀ L : B.FullSubcategory,
      A ((Stacks.Duality.derivedPushforward j).obj L.obj))
    (E : B.FullSubcategory) :
    IsIso ((liftDerivedRestrictPushforwardAdjunction j A B hres hpush).counit.app E) ↔
      IsIso ((derivedRestrictPushforwardAdjunction j).counit.app E.obj) := by
  have h : B.ι.map ((liftDerivedRestrictPushforwardAdjunction j A B hres hpush).counit.app E) =
      (derivedRestrictPushforwardAdjunction j).counit.app E.obj := by
    unfold liftDerivedRestrictPushforwardAdjunction
    rw [Adjunction.map_restrictFullyFaithful_counit_app]
    simp [ObjectProperty.liftCompιIso]
  rw [← h]
  exact (isIso_iff_of_reflects_iso _ B.ι).symm

/-- **The counit of `j^* ⊣ Rj_*` on the quasi-coherent derived categories is invertible**, `j`
being an open immersion. -/
instance isIso_quasiCoherentDerivedRestrictAdjunction_counit_app
    (E : quasiCoherentDerivedCategory V) :
    IsIso ((quasiCoherentDerivedRestrictAdjunction j hresj hpushj).counit.app E) :=
  (isIso_liftDerivedRestrictPushforwardAdjunction_counit_app_iff j _ _ hresj hpushj E).2
    inferInstance

/-- The support condition of [Stacks, Tag 08DA] on an object of `D_QCoh(𝒪_Y)`, read as the
vanishing of its restriction inside `D_QCoh(𝒪_V)`. -/
theorem cohomologySupportedOn_compl_range_iff_isZero_quasiCoherentDerivedRestrict
    (Q : quasiCoherentDerivedCategory Y) :
    Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn
        Y.ringCatSheaf (Set.range j.base)ᶜ Q.obj ↔
      IsZero ((quasiCoherentDerivedRestrict j hresj).obj Q) := by
  rw [cohomologySupportedOn_compl_range_iff_isZero_derivedRestrict]
  exact ⟨fun h => ObjectProperty.isZero_fullSubcategory_of_isZero_obj h,
    Functor.map_isZero (ObjectProperty.ι _)⟩

end Lift

/-! ### The comparison of Tag 0A9L on an object -/

section Comparison

variable {U X V Y : Scheme.{u}} (j' : U ⟶ X) (f' : U ⟶ V) (f : X ⟶ Y) (j : V ⟶ Y)
  [IsOpenImmersion j'] [IsOpenImmersion j]
  (hpushj' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((Stacks.Duality.derivedPushforward j').obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory U) (i : ℤ),
    ((DerivedCategory.homologyFunctor V.Modules i).obj
      ((Stacks.Duality.derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushj : ∀ (K : quasiCoherentDerivedCategory V) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward j).obj K.obj)).IsQuasicoherent)
  (hresj : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor V.Modules i).obj
      ((derivedRestrict j).obj K.obj)).IsQuasicoherent)
  (hresj' : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor U.Modules i).obj
      ((derivedRestrict j').obj K.obj)).IsQuasicoherent)
  [(Stacks.Duality.quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(Stacks.Duality.quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]
  (sq : IsPullback j' f' f j)
  [IsIso (Stacks.Duality.twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf
    hpushf' hpushj sq)]

/-- **The comparison of [Stacks, Tag 0A9L], read on an object.** On `K` it is `(j')^*` of `a` of
the unit of `j^* ⊣ Rj_*`, then `(j')^*` of `ξ⁻¹`, then the counit of `(j')^* ⊣ Rj'_*`: the
unitors and associators in the definition are identities on components. -/
theorem twistedInverseImageRestrictionMap_app_eq (K : quasiCoherentDerivedCategory Y) :
    (twistedInverseImageRestrictionMap j' f' f j hpushj' hpushf hpushf' hpushj hresj hresj'
        sq).app K =
      (quasiCoherentDerivedRestrict j' hresj').map
          ((Stacks.Duality.twistedInverseImage f hpushf).map
            ((quasiCoherentDerivedRestrictAdjunction j hresj hpushj).unit.app K)) ≫
        (quasiCoherentDerivedRestrict j' hresj').map
          ((inv (Stacks.Duality.twistedInverseImagePushforwardBaseChange j' f' f j hpushj' hpushf
            hpushf' hpushj sq)).app ((quasiCoherentDerivedRestrict j hresj).obj K)) ≫
        (quasiCoherentDerivedRestrictAdjunction j' hresj' hpushj').counit.app
          ((Stacks.Duality.twistedInverseImage f' hpushf').obj
            ((quasiCoherentDerivedRestrict j hresj).obj K)) := by
  simp [twistedInverseImageRestrictionMap]

/-- **The comparison of [Stacks, Tag 0A9L] is invertible on `K` exactly when
`a(K)|_U ⟶ a(Rj_*(K|_V))|_U` is.** This is the "in particular" that follows the source's
displayed formula: of the three arrows making up the comparison, the second is invertible by the
instance argument of Tag 0A9L — that is [Stacks, Tag 0A9K] — and the third is the counit of
`(j')^* ⊣ Rj'_*`, invertible because `j'` is an open immersion. -/
theorem isIso_twistedInverseImageRestrictionMap_app_iff (K : quasiCoherentDerivedCategory Y) :
    IsIso ((twistedInverseImageRestrictionMap j' f' f j hpushj' hpushf hpushf' hpushj hresj
        hresj' sq).app K) ↔
      IsIso ((quasiCoherentDerivedRestrict j' hresj').map
        ((Stacks.Duality.twistedInverseImage f hpushf).map
          ((quasiCoherentDerivedRestrictAdjunction j hresj hpushj).unit.app K))) := by
  rw [twistedInverseImageRestrictionMap_app_eq]
  have : IsIso ((inv (Stacks.Duality.twistedInverseImagePushforwardBaseChange j' f' f j hpushj'
      hpushf hpushf' hpushj sq)).app ((quasiCoherentDerivedRestrict j hresj).obj K)) :=
    NatIso.isIso_app_of_isIso _ _
  exact isIso_comp_right_iff _ _

/-! ### Tag 0A9N, part (2) -/

/-- **[Stacks, Tag 0A9N], part (2).** Let `f : X ⟶ Y` be a morphism of schemes, let `j : V ⟶ Y` be
an open immersion and let `j' : U ⟶ X` be its base change along `f`, so that `U = f^{-1}(V)`. Let
`a` be the twisted inverse image of `f`. Then every `Q` in `D_QCoh(𝒪_Y)` whose cohomology is
supported on `Y ∖ V` has `a(Q)` with cohomology supported on `X ∖ U` if and only if the
comparison of [Stacks, Tag 0A9L] is an isomorphism on every `K` in `D_QCoh(𝒪_Y)`.

For the hypotheses — all of them Tag 0A9L's own, and none of them a restriction of the source's
statement — and for why only part (2) is proved, see the module documentation.

This form takes the inputs of [Stacks, Tag 0A9L] as arguments, so it is not registered; part (2)
of [Stacks, Tag 0A9N] at the source's hypotheses, with every input discharged, is registered on
`Stacks.Duality.OpenImmersion.qcqs_cohomologySupportedOn_iff_isIso_restrictionMap`.
-/
theorem twistedInverseImage_cohomologySupportedOn_iff_isIso_restrictionMap :
    (∀ Q : quasiCoherentDerivedCategory Y,
        Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn Y.ringCatSheaf
            (Set.range j.base)ᶜ Q.obj →
          Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf
            (Set.range j'.base)ᶜ ((Stacks.Duality.twistedInverseImage f hpushf).obj Q).obj) ↔
      (∀ K : quasiCoherentDerivedCategory Y,
        IsIso ((twistedInverseImageRestrictionMap j' f' f j hpushj' hpushf hpushf' hpushj hresj
          hresj' sq).app K)) := by
  let := quasiCoherentDerivedRestrictCommShift j hresj
  let := quasiCoherentDerivedRestrictCommShift j' hresj'
  let := quasiCoherentDerivedRestrict_isTriangulated j hresj
  let := quasiCoherentDerivedRestrict_isTriangulated j' hresj'
  let := (Stacks.Duality.twistedInverseImageAdjunction f hpushf).rightAdjointCommShift ℤ
  let := (Stacks.Duality.twistedInverseImageAdjunction f hpushf).commShift_of_leftAdjoint ℤ
  let : (Stacks.Duality.twistedInverseImage f hpushf).IsTriangulated :=
    (Stacks.Duality.twistedInverseImageAdjunction f hpushf).isTriangulated_rightAdjoint
  have := (Stacks.Duality.twistedInverseImageAdjunction f' hpushf').isRightAdjoint
  constructor
  · intro hSupp K
    rw [isIso_twistedInverseImageRestrictionMap_app_iff]
    obtain ⟨Q, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle
      ((quasiCoherentDerivedRestrictAdjunction j hresj hpushj).unit.app K)
    have hLunit : IsIso ((quasiCoherentDerivedRestrict j hresj).map
        ((quasiCoherentDerivedRestrictAdjunction j hresj hpushj).unit.app K)) := by
      rw [← isIso_comp_right_iff _ ((quasiCoherentDerivedRestrictAdjunction j hresj
        hpushj).counit.app ((quasiCoherentDerivedRestrict j hresj).obj K)),
        (quasiCoherentDerivedRestrictAdjunction j hresj hpushj).left_triangle_components K]
      exact IsIso.id _
    have hLQ : IsZero ((quasiCoherentDerivedRestrict j hresj).obj Q) :=
      Pretriangulated.Triangle.isZero₃_of_isIso₁ _
        (Functor.map_distinguished (quasiCoherentDerivedRestrict j hresj) _ hT) hLunit
    have hL'aQ : IsZero ((quasiCoherentDerivedRestrict j' hresj').obj
        ((Stacks.Duality.twistedInverseImage f hpushf).obj Q)) :=
      (cohomologySupportedOn_compl_range_iff_isZero_quasiCoherentDerivedRestrict j' hresj' _).1
        (hSupp Q
          ((cohomologySupportedOn_compl_range_iff_isZero_quasiCoherentDerivedRestrict j hresj
            Q).2 hLQ))
    exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      (Functor.map_distinguished (Stacks.Duality.twistedInverseImage f hpushf ⋙
        quasiCoherentDerivedRestrict j' hresj') _ hT)).1 hL'aQ
  · intro hIso Q hQsupp
    have := hIso Q
    exact (cohomologySupportedOn_compl_range_iff_isZero_quasiCoherentDerivedRestrict j' hresj'
      _).2 ((Functor.map_isZero (Stacks.Duality.twistedInverseImage f' hpushf')
        ((cohomologySupportedOn_compl_range_iff_isZero_quasiCoherentDerivedRestrict j hresj
          Q).1 hQsupp)).of_iso (asIso ((twistedInverseImageRestrictionMap j' f' f j
            hpushj' hpushf hpushf' hpushj hresj hresj' sq).app Q)))

end Comparison

end Stacks.Duality.OpenImmersion

end
