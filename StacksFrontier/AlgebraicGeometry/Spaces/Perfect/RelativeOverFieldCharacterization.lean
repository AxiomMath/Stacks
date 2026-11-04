module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomologyEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0DKP: the objects perfect relative to a field are the bounded coherent ones

Let `k` be a field and let `X` be an algebraic space of finite presentation over `k`. Stacks 0DKP
says that `X` is quasi-compact, and that an object `E` of `D(𝒪_X)` is `k`-perfect in the sense of
Stacks 0DKN if and only if it is bounded and pseudo-coherent, that is, if and only if it lies in
`D^b_Coh(X)`.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFinitePresentation_fieldSpace`: an algebraic
  space of finite presentation over a field is quasi-compact.
* `AlgebraicGeometry.Space.isRelativelyPerfect_iff_isBounded_and_isPseudoCoherent`: an object of
  `D(𝒪_X)` is `k`-perfect (`AlgebraicGeometry.Space.IsRelativelyPerfect`, Stacks 0DKN) if and
  only if it is bounded and pseudo-coherent.
* `AlgebraicGeometry.Space.isBounded_and_isPseudoCoherent_iff_derivedCategoryBBounded`: on a
  locally Noetherian algebraic space the bounded pseudo-coherent objects of `D(𝒪_X)` are the
  objects of `D^b_Coh(𝒪_X)`.
* `AlgebraicGeometry.Space.isRelativelyPerfect_iff_derivedCategoryBBounded`: the example in one
  statement, the `k`-perfect objects of `D(𝒪_X)` are exactly the objects of `D^b_Coh(𝒪_X)`.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_fieldSpace`: an algebraic
  space locally of finite presentation over a field is locally Noetherian.
* `AlgebraicGeometry.Space.isRelativelyPerfect_of_isBounded_of_isPseudoCoherent`: a bounded
  pseudo-coherent object is `k`-perfect as soon as `X` is locally of finite presentation over `k`.
* `AlgebraicGeometry.Space.isPerfectRelativeTo_iff_isBounded_and_isPseudoCoherent` and
  `AlgebraicGeometry.Space.isPerfectRelativeTo_iff_derivedCategoryBBounded`: the same two
  equivalences for `AlgebraicGeometry.Space.IsPerfectRelativeTo` measured against an arbitrary
  family of derived tensor products on the slices, and
  `AlgebraicGeometry.Space.isPerfectRelativeTo_canonical_iff_isBounded_and_isPseudoCoherent`,
  `AlgebraicGeometry.Space.isPerfectRelativeTo_canonical_iff_derivedCategoryBBounded` at the
  derived tensor product of Stacks 06YU.

The closing sentence of the example, that relative perfectness is not perfectness on the fibres,
is `AlgebraicGeometry.Space.isRelativelyPerfect_dualNumberResidueComplex_and_not_isPerfect` in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectNotFibrewise`.

## Implementation notes

`k`-perfectness is `AlgebraicGeometry.Space.IsRelativelyPerfect` of Stacks 0DKN, which measures
Tor dimension on each slice of the inverse-image ringed site against the derived tensor product
of Stacks 06YU on that slice. Flatness of `X ⟶ Spec k`, which the definition of relative
perfectness carries, is `AlgebraicGeometry.Space.isFlat_toFieldSpace`.

The identification with `D^b_Coh(𝒪_X)` is Stacks 08IK on a locally Noetherian algebraic space,
quasi-coherence of the cohomology sheaves being Stacks 08JL; an algebraic space locally of finite
presentation over `k` is locally Noetherian by Stacks 0464 and 04ZK. The statements hold at any
`HasDerivedCategory` instance.

## References

* [Stacks Project, Tag 0DKP](https://stacks.math.columbia.edu/tag/0DKP)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 08IK](https://stacks.math.columbia.edu/tag/08IK)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d e

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Bounded pseudo-coherent objects on a locally Noetherian algebraic space -/

section Coherent

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (hN : HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))

include hN

section Complexes

attribute [local instance] HasDerivedCategory.standard

/-- **A pseudo-coherent complex on a locally Noetherian algebraic space has coherent
cohomology.** This is Stacks 08IK, the direction (2) ⇒ (1). -/
theorem isCoherentOnSite_homology_of_isPseudoCoherentComplex
    (K : CochainComplex (Modules.{u, u} B S hS F hF) ℤ)
    (hK : (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentComplex K) (i : ℤ) :
    SheafOfModules.IsCoherentOnSite (K.homology i) :=
  Stacks.SheafOfModules.isCoherentOnSite_of_iso
    ((DerivedCategory.homologyFunctorFactors _ i).app K)
    (isCoherentOnSite_homology_of_isPseudoCoherentFrom B S hS F hF hN
      (DerivedCategory.Q.obj K) i i ⟨K, hK i, ⟨Iso.refl _⟩⟩ le_rfl
      (derivedCategoryB_of_isPseudoCoherent_unconditional B S hS F hF _
        ⟨K, hK, ⟨Iso.refl _⟩⟩ i))

/-- **A complex on a locally Noetherian algebraic space with coherent cohomology vanishing in
large degrees is pseudo-coherent.** This is Stacks 08IK, the direction (1) ⇒ (2) in every
degree. -/
theorem isPseudoCoherentComplex_of_isCoherentOnSite_homology
    (K : CochainComplex (Modules.{u, u} B S hS F hF) ℤ)
    (hb : ∃ b : ℤ, ∀ i, b < i → IsZero (K.homology i))
    (hc : ∀ i, SheafOfModules.IsCoherentOnSite (K.homology i)) :
    (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentComplex K := by
  obtain ⟨b, hb⟩ := hb
  intro m
  refine RingedSite.isPseudoCoherentComplexFrom_of_iso_general _ (DerivedCategory.Q.obj K) m
    ?_ K (Iso.refl _)
  exact isPseudoCoherentFrom_of_isCoherentOnSite_homology_of_isBoundedAbove B S hS F hF hN _ m
    (fun i _ => Stacks.SheafOfModules.isCoherentOnSite_of_iso
      ((DerivedCategory.homologyFunctorFactors _ i).app K).symm (hc i))
    ⟨b, fun i hi => (hb i hi).of_iso ((DerivedCategory.homologyFunctorFactors _ i).app K)⟩

end Complexes

variable [HasDerivedCategory.{d} (Modules.{u, u} B S hS F hF)]

/-- A complex isomorphic in the derived category to `E` has homology isomorphic to that of `E`. -/
private noncomputable def homologyIsoOfIso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {K : CochainComplex C ℤ} {E : DerivedCategory C}
    (e : DerivedCategory.Q.obj K ≅ E) (i : ℤ) :
    K.homology i ≅ (DerivedCategory.homologyFunctor _ i).obj E :=
  ((DerivedCategory.homologyFunctorFactors _ i).app K).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso e

/-- **On a locally Noetherian algebraic space the bounded pseudo-coherent objects of `D(𝒪_X)`
are the objects of `D^b_Coh(𝒪_X)`**: an object of `D(𝒪_X)` is bounded and pseudo-coherent if
and only if it is bounded with coherent cohomology sheaves.

This is the bounded case of the final statement of Stacks 08IK, which identifies the
pseudo-coherent objects with `D⁻_Coh(𝒪_X)`; quasi-coherence of the cohomology sheaves holds on
both sides, on the left by Stacks 08JL. -/
@[stacks 0DKP "bounded pseudo-coherent objects are the objects of `D^b_Coh(X)`, by Stacks 08IK"]
theorem isBounded_and_isPseudoCoherent_iff_derivedCategoryBBounded
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) :
    (DerivedCategoryB.IsBounded E ∧ (smallEtaleRingedSite B S hS F hF).IsPseudoCoherent E) ↔
      DerivedCategoryB.derivedCategoryBBounded
        (fun M : Modules.{u, u} B S hS F hF => M.IsCoherentOnSite) E := by
  constructor
  · rintro ⟨hb, K, hK, ⟨e⟩⟩
    exact ⟨hb, fun i => Stacks.SheafOfModules.isCoherentOnSite_of_iso (homologyIsoOfIso e i)
      (isCoherentOnSite_homology_of_isPseudoCoherentComplex B S hS F hF hN K hK i)⟩
  · rintro ⟨hb, hc⟩
    obtain ⟨b, hb'⟩ := hb.2
    exact ⟨hb, _, isPseudoCoherentComplex_of_isCoherentOnSite_homology B S hS F hF hN _
      ⟨b, fun i hi =>
        (hb' i hi).of_iso (homologyIsoOfIso (DerivedCategory.Q.objObjPreimageIso E) i)⟩
      (fun i => Stacks.SheafOfModules.isCoherentOnSite_of_iso
        (homologyIsoOfIso (DerivedCategory.Q.objObjPreimageIso E) i).symm (hc i)),
      ⟨DerivedCategory.Q.objObjPreimageIso E⟩⟩

end Coherent

/-! ### Algebraic spaces over a field -/

variable {X : AlgebraicSpaces B S hS} (k : Type u) [Field k]
  (hk : B.Contains (Spec (.of k))) (b : Spec (.of k) ⟶ S) (f : X ⟶ fieldSpace B hS hk b)

/-- **An algebraic space of finite presentation over a field is quasi-compact.** -/
@[stacks 0DKP "in particular, an algebraic space of finite presentation over a field is \
quasi-compact"]
theorem isQuasiCompactSpace_of_isFinitePresentation_fieldSpace
    (hfp : IsFinitePresentation B S hS f.hom) : IsQuasiCompactSpace B S hS X.1 :=
  isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS f.hom
    (isAffineSpace_yoneda B S hS _ (by change IsAffine (Spec (.of k)); infer_instance)) hfp.2.1

/-- **An algebraic space locally of finite presentation over a field is locally Noetherian**, by
Stacks 0464 and 04ZK, the spectrum of a field being Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_fieldSpace
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) :
    HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B S hS X.2 (fieldSpace B hS hk b).2 f.hom
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hlfp)
    (hasEtaleLocalProperty_of_representable B S hS _ _ _ (Iso.refl _)
      (by change IsLocallyNoetherian (Spec (.of k)); infer_instance))

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

/-- The modules over the inverse image of the structure sheaf of `Spec k` form an abelian
category. -/
noncomputable local instance (priority := high) inverseImageModules_abelian :
    Abelian (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f)) :=
  SheafOfModules.instAbelian _

/-- The modules on a slice of the inverse-image ringed site form an abelian category. -/
noncomputable local instance (priority := high) inverseImageModulesOver_abelian
    (U : (inverseImageRingedSite B S hS f).C) :
    Abelian (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) :=
  SheafOfModules.instAbelian _

/-- The modules on a slice of the inverse-image ringed site have binary biproducts, read off
the abelian structure `inverseImageModulesOver_abelian`. -/
local instance inverseImageModulesOver_hasBinaryBiproducts
    (U : (inverseImageRingedSite B S hS f).C) :
    HasBinaryBiproducts
      (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) :=
  @hasBinaryBiproducts_of_finite_biproducts _ _ _
    (@Abelian.hasFiniteBiproducts _ _ (inverseImageModulesOver_abelian B S hS k hk b f U))

/-- The tensor product of modules on a slice of the inverse-image ringed site is additive in its
first variable. -/
local instance inverseImageOverSheafTensor_additive (U : (inverseImageRingedSite B S hS f).C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((inverseImageRingedSite B S hS f).over U).O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u + 1, u, u, u, u} _

/-- The tensor product of modules on a slice of the inverse-image ringed site is additive in its
second variable. -/
local instance inverseImageOverSheafTensor_obj_additive (U : (inverseImageRingedSite B S hS f).C)
    (M : RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((inverseImageRingedSite B S hS f).over U).O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u + 1, u, u, u, u} _ M

/-- Total tensor complexes of complexes of modules on a slice of the inverse-image ringed site
exist. -/
local instance inverseImageOverSheafTensor_hasMapBifunctor
    (U : (inverseImageRingedSite B S hS f).C)
    (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u + 1, u, u, u, u} _ K L

variable [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]
    [∀ U : (inverseImageRingedSite B S hS f).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

/-- **Stacks 0DKP, first equivalence, for every derived tensor product.** Let `k` be a field and
let `X` be an algebraic space of finite presentation over `k`. For every family `T` of derived
tensor products on the slices of the inverse-image ringed site, an object `E` of `D(𝒪_X)` is
perfect relative to `Spec k` if and only if it is bounded and pseudo-coherent. -/
theorem isPerfectRelativeTo_iff_isBounded_and_isPseudoCoherent
    (hfp : IsFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    IsPerfectRelativeTo B S hS f (isFlat_toFieldSpace B S hS k hk b f) hfp.1 T E ↔
      (DerivedCategoryB.IsBounded E ∧ (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) :=
  ⟨fun h => ⟨isBounded_of_isPerfectRelativeTo B S hS f
      (isQuasiCompactSpace_of_isFinitePresentation_fieldSpace B S hS k hk b f hfp) _ _ T E h,
      h.1⟩,
    fun h => isPerfectRelativeTo_of_isBounded_of_isPseudoCoherent B S hS k hk b f hfp.1 T E
      h.2 h.1⟩

/-- **Stacks 0DKP, first equivalence, at the derived tensor product of Stacks 06YU.** Let `k` be
a field and let `X` be an algebraic space of finite presentation over `k`. An object `E` of
`D(𝒪_X)` is perfect relative to `Spec k` — Tor dimension being measured on each slice of the
inverse-image ringed site against the derived tensor product of Stacks 06YU on that slice — if
and only if it is bounded and pseudo-coherent. -/
theorem isPerfectRelativeTo_canonical_iff_isBounded_and_isPseudoCoherent
    (hfp : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    IsPerfectRelativeTo B S hS f (isFlat_toFieldSpace B S hS k hk b f) hfp.1
        (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct
          ((inverseImageRingedSite B S hS f).over U)) E ↔
      (DerivedCategoryB.IsBounded E ∧ (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) :=
  isPerfectRelativeTo_iff_isBounded_and_isPseudoCoherent B S hS k hk b f hfp _ E

/-- **Stacks 0DKP, for every derived tensor product.** Let `k` be a field and let `X` be an
algebraic space of finite presentation over `k`. For every family `T` of derived tensor products
on the slices of the inverse-image ringed site, an object `E` of `D(𝒪_X)` is perfect relative to
`Spec k` if and only if it lies in `D^b_Coh(𝒪_X)`. -/
theorem isPerfectRelativeTo_iff_derivedCategoryBBounded
    (hfp : IsFinitePresentation B S hS f.hom)
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    IsPerfectRelativeTo B S hS f (isFlat_toFieldSpace B S hS k hk b f) hfp.1 T E ↔
      DerivedCategoryB.derivedCategoryBBounded
        (fun M : Modules.{u, u} B S hS X.1 X.2 => M.IsCoherentOnSite) E :=
  (isPerfectRelativeTo_iff_isBounded_and_isPseudoCoherent B S hS k hk b f hfp T E).trans
    (isBounded_and_isPseudoCoherent_iff_derivedCategoryBBounded B S hS X.1 X.2
      (hasEtaleLocalProperty_isLocallyNoetherian_of_fieldSpace B S hS k hk b f hfp.1) E)

/-- **Stacks 0DKP.** Let `k` be a field and let `X` be an algebraic space of finite presentation
over `k`. An object `E` of `D(𝒪_X)` is `k`-perfect if and only if it lies in `D^b_Coh(𝒪_X)`,
that is, if and only if it is bounded with coherent cohomology sheaves.

Relative perfectness is read at the derived tensor product of Stacks 06YU on each slice of the
inverse-image ringed site. -/
theorem isPerfectRelativeTo_canonical_iff_derivedCategoryBBounded
    (hfp : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    IsPerfectRelativeTo B S hS f (isFlat_toFieldSpace B S hS k hk b f) hfp.1
        (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct
          ((inverseImageRingedSite B S hS f).over U)) E ↔
      DerivedCategoryB.derivedCategoryBBounded
        (fun M : Modules.{u, u} B S hS X.1 X.2 => M.IsCoherentOnSite) E :=
  isPerfectRelativeTo_iff_derivedCategoryBBounded B S hS k hk b f hfp _ E

/-- **A bounded pseudo-coherent object is `k`-perfect**, on an algebraic space which is only
assumed locally of finite presentation over the field `k`. This is the half of the first
equivalence of Stacks 0DKP that needs neither quasi-compactness nor quasi-separatedness. -/
theorem isRelativelyPerfect_of_isBounded_of_isPseudoCoherent
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hpc : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E)
    (hbdd : DerivedCategoryB.IsBounded E) :
    IsRelativelyPerfect B S hS f (isFlat_toFieldSpace B S hS k hk b f) hlfp E :=
  (isRelativelyPerfect_iff_isPerfectRelativeTo B S hS f _ hlfp
    (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct
      ((inverseImageRingedSite B S hS f).over U)) E).2
    (isPerfectRelativeTo_of_isBounded_of_isPseudoCoherent B S hS k hk b f hlfp _ E hpc hbdd)

/-- **Stacks 0DKP, first equivalence.** Let `k` be a field and let `X` be an algebraic space of
finite presentation over `k`. An object `E` of `D(𝒪_X)` is `k`-perfect (Stacks 0DKN) if and only
if it is bounded and pseudo-coherent. -/
@[stacks 0DKP "`k`-perfect objects are the bounded pseudo-coherent ones"]
theorem isRelativelyPerfect_iff_isBounded_and_isPseudoCoherent
    (hfp : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    IsRelativelyPerfect B S hS f (isFlat_toFieldSpace B S hS k hk b f) hfp.1 E ↔
      (DerivedCategoryB.IsBounded E ∧ (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) :=
  (isRelativelyPerfect_iff_isPerfectRelativeTo B S hS f _ _ _ E).trans
    (isPerfectRelativeTo_canonical_iff_isBounded_and_isPseudoCoherent B S hS k hk b f hfp E)

/-- **Stacks 0DKP.** Let `k` be a field and let `X` be an algebraic space of finite presentation
over `k`. An object `E` of `D(𝒪_X)` is `k`-perfect (Stacks 0DKN) if and only if it lies in
`D^b_Coh(𝒪_X)`, that is, if and only if it is bounded with coherent cohomology sheaves. -/
@[stacks 0DKP "the `k`-perfect objects are exactly the objects of `D^b_Coh(X)`"]
theorem isRelativelyPerfect_iff_derivedCategoryBBounded
    (hfp : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    IsRelativelyPerfect B S hS f (isFlat_toFieldSpace B S hS k hk b f) hfp.1 E ↔
      DerivedCategoryB.derivedCategoryBBounded
        (fun M : Modules.{u, u} B S hS X.1 X.2 => M.IsCoherentOnSite) E :=
  (isRelativelyPerfect_iff_isPerfectRelativeTo B S hS f _ _ _ E).trans
    (isPerfectRelativeTo_canonical_iff_derivedCategoryBBounded B S hS k hk b f hfp E)

end AlgebraicGeometry.Space

end
