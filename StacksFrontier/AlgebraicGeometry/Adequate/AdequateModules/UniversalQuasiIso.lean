module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedLocalization
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Abelian
public import StacksFrontier.Homology.FilteredDerivedCategory.Basic

/-!
# The universal quasi-isomorphisms form a multiplicative system

The proof of [Stacks, Tag 06ZR] opens by observing that the universal quasi-isomorphisms `S` of
`K⁺(QCoh(𝒪_U))` are "a saturated multiplicative system compatible with the triangulated
structure", so that the localization `S⁻¹K⁺(QCoh(𝒪_U))` exists. The source reads this off the
identification of `S` with the class of morphisms `φ` for which `uφ` is a quasi-isomorphism,
together with Derived Categories, Lemma [Stacks, Tag 05R4].

This file proves those closure properties of `Stacks.Adequate.universalQuasiIso` directly from
its definition, so that none of them is conditional: a universal quasi-isomorphism is one whose
pullback along every morphism of schemes is a quasi-isomorphism, and each property is inherited,
pullback by pullback, from the corresponding property of the quasi-isomorphisms of `K⁺`. In
particular this needs neither the identification with the inverse image of the
quasi-isomorphisms under `u` — the hypothesis `huniv` of
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq` — nor any
part of the adequacy theory.

The opening step also asserts that the localization `S⁻¹K⁺(QCoh(𝒪_U))` *exists as a triangulated
category*. That too is proved here, and unconditionally: the universal quasi-isomorphisms are the
class of morphisms whose cone is **universally acyclic**, and the universally acyclic complexes
are an intersection of triangulated subcategories, hence a triangulated subcategory. Everything
the localization needs — a left and a right calculus of fractions, and compatibility with the
triangulation — is then Mathlib's theory of the multiplicative system `P.trW` of a triangulated
subcategory `P`.

## Main definitions

* `Stacks.Adequate.universallyAcyclic` — the bounded below complexes of quasi-coherent
  `𝒪_S`-modules whose pullback along every morphism of schemes `T ⟶ S` is acyclic.

## Main results

* `Stacks.Adequate.universalQuasiIso_eq_iInf` — the universal quasi-isomorphisms are the
  intersection, over every morphism of schemes `f : T ⟶ S`, of the inverse images of the
  quasi-isomorphisms of `K⁺(Mod(𝒪_T))` along pullback by `f`.
* `Stacks.Adequate.universalQuasiIso` contains the identities, is stable under composition, is
  multiplicative, and respects isomorphisms.
* `Stacks.Adequate.universalQuasiIso_eq_trW` — a morphism is a universal quasi-isomorphism
  exactly when its cone is universally acyclic.
* `Stacks.Adequate.universalQuasiIso` has a left and a right calculus of fractions and is
  compatible with the triangulation, so Mathlib's instances make the localization
  `S⁻¹K⁺(QCoh(𝒪_S))` a triangulated category. Together these are the conclusion of the
  opening step of [Stacks, Tag 06ZR].
* `Stacks.Adequate.universalQuasiIso_eq_inverseImage_of_universallyAcyclic_eq` — the hypothesis
  `huniv` of `Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq`
  reduced to a statement about objects: it is enough that a complex be universally acyclic
  exactly when its image is acyclic.

## Implementation notes

The closure properties of the class go through `Stacks.Adequate.universalQuasiIso_eq_iInf` and
then Mathlib's stability of these properties under `MorphismProperty.inverseImage` and under
`iInf`. Nothing reduces the pullback functor or the quasi-coherent subcategory: the arguments
are those of an intersection of inverse images, and are carried out at that level of generality,
which is what keeps them cheap.

The triangulated half is stated with the library's own abelian structure on `QCoh(𝒪_S)`,
`AlgebraicGeometry.quasicoherentModules_abelian`, rather than with an assumed one. It has to be:
the pretriangulated structure of `K⁺(QCoh(𝒪_S))` is built from the preadditive structure that a
full subcategory inherits from its ambient category, so an abstract `Preadditive` hypothesis on
`QCoh(𝒪_S)` leaves `Pretriangulated (HomotopyCategory (QCoh 𝒪_S) (.up ℤ))` unsynthesizable. The
library's abelian structure is the inherited one on the nose
(`AlgebraicGeometry.quasicoherentModules_abelian_toPreadditive` is `rfl`), so nothing is lost and
no instance diamond is created.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
* [Stacks Project, Tag 05R4](https://stacks.math.columbia.edu/tag/05R4)
* [Stacks Project, Tag 05RL](https://stacks.math.columbia.edu/tag/05RL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated

universe u w v' u'

namespace Stacks.Adequate

section UniversalQuasiIso

variable {S : Scheme.{u}}
  [Preadditive (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory]
  [(SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.Additive]

/-- A morphism of `K⁺(QCoh(𝒪_S))` is a universal quasi-isomorphism exactly when each of its
pullbacks is a quasi-isomorphism: the defining property, as an `Iff`. -/
public theorem universalQuasiIso_iff
    {K L : HomotopyCategory.Plus
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory} (φ : K ⟶ L) :
    universalQuasiIso S φ ↔ ∀ (T : Scheme.{u}) (f : T ⟶ S),
      HomotopyCategory.Plus.quasiIso T.Modules
        ((qcohPullback f).mapHomotopyCategoryPlus.map φ) :=
  Iff.rfl

variable (S) in
/-- The universal quasi-isomorphisms are the intersection, over every morphism of schemes
`f : T ⟶ S`, of the inverse images of the quasi-isomorphisms of `K⁺(Mod(𝒪_T))` along the
pullback by `f`. -/
public theorem universalQuasiIso_eq_iInf :
    universalQuasiIso S = ⨅ (T : Scheme.{u}), ⨅ (f : T ⟶ S),
      (HomotopyCategory.Plus.quasiIso T.Modules).inverseImage
        (qcohPullback f).mapHomotopyCategoryPlus := by
  ext K L φ
  simp only [MorphismProperty.iInf_iff, MorphismProperty.inverseImage_iff]
  exact universalQuasiIso_iff φ

/-- The identity of a bounded below complex of quasi-coherent `𝒪_S`-modules is a universal
quasi-isomorphism. -/
public instance universalQuasiIso_containsIdentities :
    (universalQuasiIso S).ContainsIdentities := by
  rw [universalQuasiIso_eq_iInf]
  infer_instance

/-- A composition of universal quasi-isomorphisms is a universal quasi-isomorphism. -/
public instance universalQuasiIso_isStableUnderComposition :
    (universalQuasiIso S).IsStableUnderComposition := by
  rw [universalQuasiIso_eq_iInf]
  infer_instance

/-- The universal quasi-isomorphisms are a multiplicative system: they contain the identities
and are stable under composition. This is the first assertion of the opening step of
[Stacks, Tag 06ZR]. -/
public instance universalQuasiIso_isMultiplicative :
    (universalQuasiIso S).IsMultiplicative where

/-- The universal quasi-isomorphisms are stable under pre- and post-composition with
isomorphisms. -/
public instance universalQuasiIso_respectsIso : (universalQuasiIso S).RespectsIso := by
  rw [universalQuasiIso_eq_iInf]
  infer_instance

/-- The universal quasi-isomorphisms are unchanged by the shift of `K⁺(QCoh(𝒪_S))`: the shift
half of the assertion of the opening step of [Stacks, Tag 06ZR] that the system is compatible
with the triangulated structure, the other half being
`Stacks.Adequate.universalQuasiIso_isCompatibleWithTriangulation`. Each pullback commutes with
the shift, so the condition is inherited from the corresponding compatibility of the
quasi-isomorphisms of `K⁺(Mod(𝒪_T))`. -/
public instance universalQuasiIso_isCompatibleWithShift :
    (universalQuasiIso S).IsCompatibleWithShift ℤ where
  condition a := by
    ext K L φ
    simp only [MorphismProperty.inverseImage_iff]
    rw [universalQuasiIso_iff, universalQuasiIso_iff]
    refine forall_congr' fun T ↦ forall_congr' fun f ↦ ?_
    rw [← MorphismProperty.IsCompatibleWithShift.iff
      (HomotopyCategory.Plus.quasiIso T.Modules)
      ((qcohPullback f).mapHomotopyCategoryPlus.map φ) a]
    exact (HomotopyCategory.Plus.quasiIso T.Modules).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((qcohPullback f).mapHomotopyCategoryPlus.commShiftIso a) (Arrow.mk φ))

end UniversalQuasiIso

/-! ### The universally acyclic complexes and the triangulated localization -/

section UniversallyAcyclic

variable {S : Scheme.{u}}

variable (S) in
/-- A bounded below complex of quasi-coherent `𝒪_S`-modules is **universally acyclic** when its
pullback along every morphism of schemes `T ⟶ S` is acyclic: the objects of `K⁺(QCoh(𝒪_S))` cut
out by the universal quasi-isomorphisms. -/
public noncomputable def universallyAcyclic :
    ObjectProperty (HomotopyCategory.Plus
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :=
  ⨅ (T : Scheme.{u}), ⨅ (f : T ⟶ S),
    (HomotopyCategory.Plus.subcategoryAcyclic T.Modules).inverseImage
      (qcohPullback f).mapHomotopyCategoryPlus

/-- A complex is universally acyclic exactly when each of its pullbacks is acyclic: the
defining property, as an `Iff`. -/
public theorem universallyAcyclic_iff
    (K : HomotopyCategory.Plus
      (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    universallyAcyclic S K ↔ ∀ (T : Scheme.{u}) (f : T ⟶ S),
      HomotopyCategory.Plus.subcategoryAcyclic T.Modules
        ((qcohPullback f).mapHomotopyCategoryPlus.obj K) := by
  simp [universallyAcyclic]

/-- The universally acyclic complexes are stable under isomorphism, each acyclicity condition
being so. -/
public instance universallyAcyclic_isClosedUnderIsomorphisms :
    (universallyAcyclic S).IsClosedUnderIsomorphisms := by
  dsimp only [universallyAcyclic]
  infer_instance

/-- The universally acyclic complexes are a triangulated subcategory of `K⁺(QCoh(𝒪_S))`, being
an intersection of inverse images of the acyclic complexes along triangulated functors. -/
public instance universallyAcyclic_isTriangulated :
    (universallyAcyclic S).IsTriangulated := by
  have (T : Scheme.{u}) :
      (⨅ (f : T ⟶ S), (HomotopyCategory.Plus.subcategoryAcyclic T.Modules).inverseImage
        (qcohPullback f).mapHomotopyCategoryPlus).IsTriangulated :=
    ObjectProperty.isTriangulated_iInf _
  dsimp only [universallyAcyclic]
  exact ObjectProperty.isTriangulated_iInf _

variable (S) in
/-- A morphism of `K⁺(QCoh(𝒪_S))` is a universal quasi-isomorphism exactly when its cone is
universally acyclic: the universal quasi-isomorphisms are the multiplicative system attached to
the triangulated subcategory of universally acyclic complexes, which is [Stacks, Tag 05RL] for
that subcategory. -/
public theorem universalQuasiIso_eq_trW :
    universalQuasiIso S = (universallyAcyclic S).trW := by
  ext K L φ
  obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle φ
  refine Iff.trans ?_ ((universallyAcyclic S).trW_iff_of_distinguished _ hT).symm
  rw [universalQuasiIso_iff, universallyAcyclic_iff]
  refine forall_congr' fun T ↦ forall_congr' fun f ↦ ?_
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
  exact (HomotopyCategory.Plus.subcategoryAcyclic T.Modules).trW_iff_of_distinguished _
    ((qcohPullback f).mapHomotopyCategoryPlus.map_distinguished _ hT)

/-- The universal quasi-isomorphisms admit a left calculus of fractions. -/
public instance universalQuasiIso_hasLeftCalculusOfFractions :
    (universalQuasiIso S).HasLeftCalculusOfFractions := by
  rw [universalQuasiIso_eq_trW]
  infer_instance

/-- The universal quasi-isomorphisms admit a right calculus of fractions. -/
public instance universalQuasiIso_hasRightCalculusOfFractions :
    (universalQuasiIso S).HasRightCalculusOfFractions := by
  rw [universalQuasiIso_eq_trW]
  infer_instance

/-- The universal quasi-isomorphisms are compatible with the triangulation of `K⁺(QCoh(𝒪_S))`:
a morphism of distinguished triangles whose first two components are universal
quasi-isomorphisms can be completed by a third one. This is the remaining assertion of the
opening step of [Stacks, Tag 06ZR]. -/
public instance universalQuasiIso_isCompatibleWithTriangulation :
    (universalQuasiIso S).IsCompatibleWithTriangulation := by
  rw [universalQuasiIso_eq_trW]
  infer_instance

/-- **The hypothesis `huniv` reduced to objects.** For an additive functor `F` out of
`QCoh(𝒪_S)` into an abelian category, if a bounded below complex is universally acyclic exactly
when its image under `F` is acyclic, then a morphism is a universal quasi-isomorphism exactly
when its image under `F` is a quasi-isomorphism. This is the hypothesis `huniv` of
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq`, and it is
enough to supply the statement about objects. -/
public theorem universalQuasiIso_eq_inverseImage_of_universallyAcyclic_eq
    {A : Type u'} [Category.{v'} A] [Abelian A]
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤ A) [F.Additive]
    (hF : universallyAcyclic S =
      (HomotopyCategory.Plus.subcategoryAcyclic A).inverseImage F.mapHomotopyCategoryPlus) :
    universalQuasiIso S =
      (HomotopyCategory.Plus.quasiIso A).inverseImage F.mapHomotopyCategoryPlus := by
  rw [universalQuasiIso_eq_trW, hF]
  ext K L φ
  rw [MorphismProperty.inverseImage_iff,
    HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW,
    ObjectProperty.inverseImage_trW_iff]

end UniversallyAcyclic

end Stacks.Adequate

end
