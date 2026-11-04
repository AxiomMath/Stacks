module

public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Homology.Tor.FlatDerivedExtensionScalars
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedHomologyComposition
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Naturality of the derived base-change comparison in localizations of the square

Tag 065Z attaches to a commutative square of commutative rings `R → A`, `R → R'`, `A → D`,
`R' → D` a comparison `K ⊗ᴸ_R R' ⟶ (K ⊗ᴸ_A D)|_{R'}`, natural in `K ∈ D(A)`:
`RingTheory.TorIndependence.derivedBaseChangeComparison`. Nothing was recorded about its
behaviour under a change of the SQUARE. This file supplies that naturality for the
localizations of a square which the affine reduction of Tag 0DJ8 needs, and the idempotence of
derived extension of scalars along a localization that the comparison rests on.

## Main definitions

* `RingTheory.TorIndependence.restrictExtendScalarsIso`: for `A₂` a localization of `A`, the
  underived isomorphism `A₂ ⊗_A N ≅ N` of `A₂`-modules, natural in `N`. It is the counit of the
  extension-restriction adjunction, invertible because restriction of scalars along a
  localization is full.
* `RingTheory.TorIndependence.restrictExtendScalarsComplexIso`: the same read degreewise on
  cochain complexes.
* `RingTheory.TorIndependence.restrictScalarsDerivedExtendIso`: the derived form,
  `(-|_A) ⊗ᴸ_A A₂ ≅ -` on `D(A₂)`.

## Main results

* `RingTheory.TorIndependence.full_restrictScalars_of_isLocalization`: restriction of scalars
  along a localization is full.
* `RingTheory.TorIndependence.restrictScalarsDerivedExtendIso_hom_app_Q`: the characterizing
  compatibility of the derived isomorphism with the comparison of derived and degreewise
  extension of scalars, at a cochain complex. This is the equation every diagram chase with the
  isomorphism goes through.

## Implementation notes

The derived isomorphism is built by descending its restriction along the localization functor
`Q : C(Mod A₂) ⥤ D(Mod A₂)`, which is where the characterizing equation comes from: the
restriction is assembled from `RingTheory.TorIndependence.flatDerivedExtensionScalarsIso` — a
localization is flat, so derived extension of scalars along it is the degreewise functor — the
two factorizations of `Functor.mapDerivedCategory` through complexes, and the degreewise
underived isomorphism; and `CategoryTheory.Localization.liftNatTrans_app` reads off its value on
the image of `Q`. The passage from `flatDerivedExtensionScalarsIso` to the comparison of
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` is
`RingTheory.TorIndependence.totalDerivedExtensionScalarsIsoMapDerivedCategory_app_comp_factors`.

The model of the derived category is a binder `[HasDerivedCategory.{w} (ModuleCat.{u} ·)]` for
each ring, not `HasDerivedCategory.standard`: a statement proved at one model says nothing about
another, and the consumers of Tag 0DJ8 work at a locally small model.

## References

* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [The Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open scoped TensorProduct ChangeOfRings

universe u w

namespace RingTheory.TorIndependence

section Localization

variable {A A₂ : Type u} [CommRing A] [CommRing A₂] [Algebra A A₂]
  (S : Submonoid A) [IsLocalization S A₂]

include S in
/-- **Restriction of scalars along a localization is full.** An `A`-linear map between two
`A₂`-modules is `A₂`-linear, by `LinearMap.extendScalarsOfIsLocalization`. -/
theorem full_restrictScalars_of_isLocalization :
    (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).Full where
  map_surjective {M N} φ := by
    let : Module A (M : Type u) := Module.compHom _ (algebraMap A A₂)
    let : Module A (N : Type u) := Module.compHom _ (algebraMap A A₂)
    let : IsScalarTower A A₂ (M : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let : IsScalarTower A A₂ (N : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    refine ⟨ModuleCat.ofHom (LinearMap.extendScalarsOfIsLocalization S A₂
      (M := (M : Type u)) (N := (N : Type u)) φ.hom), ?_⟩
    ext x
    rfl

include S in
/-- **Localization is idempotent for extension of scalars, underived.** For `A₂` a localization
of `A` and `N` an `A₂`-module the canonical map `A₂ ⊗_A N → N`, `a ⊗ n ↦ a • n`, is bijective;
naturally in `N`, this is the counit of the extension-restriction adjunction. -/
def restrictExtendScalarsIso :
    ModuleCat.restrictScalars.{u} (algebraMap A A₂) ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂) ≅ 𝟭 (ModuleCat.{u} A₂) :=
  haveI := full_restrictScalars_of_isLocalization S (A₂ := A₂)
  asIso (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A A₂)).counit

include S in
/-- The underived comparison is the counit of the extension-restriction adjunction. -/
theorem restrictExtendScalarsIso_hom :
    (restrictExtendScalarsIso S (A₂ := A₂)).hom =
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} (algebraMap A A₂)).counit :=
  rfl

include S in
/-- The underived comparison carries `1 ⊗ n` to `n`. -/
theorem restrictExtendScalarsIso_hom_app_one_tmul (N : ModuleCat.{u} A₂)
    (n : (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).obj N) :
    (restrictExtendScalarsIso S (A₂ := A₂)).hom.app N
        ((1 : A₂) ⊗ₜ[A, algebraMap A A₂] n) = n := by
  rw [restrictExtendScalarsIso_hom]
  exact one_smul A₂ n

include S in
/-- **The flatness of a localization.** -/
theorem flat_algebraMap_of_isLocalization : (algebraMap A A₂).Flat :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A₂ S)

include S in
/-- **Localization is idempotent for degreewise extension of scalars.** The underived
comparison read degreewise on cochain complexes. -/
def restrictExtendScalarsComplexIso :
    (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      𝟭 (CochainComplex (ModuleCat.{u} A₂) ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
    NatIso.mapHomologicalComplex (restrictExtendScalarsIso S (A₂ := A₂)) (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat.{u} A₂) (ComplexShape.up ℤ)

section Derived

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} A₂)]

open CochainComplex.DerivedExtensionScalars

include S in
/-- The comparison of Group 0 before descent along the localization functor. -/
def restrictExtendScalarsDerivedQIso :
    DerivedCategory.Q ⋙ ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor) ≅
      DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (ModuleCat.{u} A₂)) :=
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (flat_algebraMap_of_isLocalization S (A₂ := A₂))
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (flatDerivedExtensionScalarsIso.{u, w} (algebraMap A A₂)
        (flat_algebraMap_of_isLocalization S (A₂ := A₂)))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategoryFactors
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictExtendScalarsComplexIso S (A₂ := A₂)) DerivedCategory.Q ≪≫
    Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm

include S in
/-- **Localization is idempotent for derived extension of scalars.** -/
def restrictScalarsDerivedExtendIso :
    (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A₂)) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A₂) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor))
    (DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (ModuleCat.{u} A₂)))
    _ _ (restrictExtendScalarsDerivedQIso.{u, w} S (A₂ := A₂))

include S in
/-- The value of the Q-level comparison at a cochain complex: derived extension of scalars
applied to the factorization of restriction of scalars, the comparison of derived with
degreewise extension of scalars, and the degreewise underived comparison. -/
private lemma restrictExtendScalarsDerivedQIso_hom_app
    (P : CochainComplex (ModuleCat.{u} A₂) ℤ) :
    (restrictExtendScalarsDerivedQIso.{u, w} S (A₂ := A₂)).hom.app P =
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.map
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app
            P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).comparison.app
          (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((restrictExtendScalarsComplexIso S (A₂ := A₂)).hom.app P) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (flat_algebraMap_of_isLocalization S (A₂ := A₂))
  have hid : (mapHomologicalComplexIsoOfExtendScalars (algebraMap A A₂)
        (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)) (Iso.refl _)).hom.app
      (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) = CategoryStruct.id _ :=
    CategoryTheory.Functor.map_id _ _
  have hfac : (flatDerivedExtensionScalarsIso.{u, w} (algebraMap A A₂)
            (flat_algebraMap_of_isLocalization S (A₂ := A₂))).hom.app
          (DerivedCategory.Q.obj
            (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) ≫
        (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) =
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).comparison.app
        (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) := by
    refine (totalDerivedExtensionScalarsIsoMapDerivedCategory_app_comp_factors
      (algebraMap A A₂) (ModuleCat.extendScalars.{u, u, u} (algebraMap A A₂)) (Iso.refl _)
      _).trans ?_
    exact (congrArg (fun z => (totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A A₂)).comparison.app
      (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ≫ z) hid).trans (Category.comp_id _)
  have hnat := (flatDerivedExtensionScalarsIso.{u, w} (algebraMap A A₂)
      (flat_algebraMap_of_isLocalization S (A₂ := A₂))).hom.naturality
    ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app P)
  simp only [Functor.comp_obj] at hnat
  simp only [restrictExtendScalarsDerivedQIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.id_obj,
    Functor.comp_obj, Category.id_comp, Category.comp_id]
  rw [← reassoc_of% hnat, reassoc_of% hfac]
  rfl

include S in
/-- **The characterizing compatibility of the derived comparison.** At a cochain complex of
`A₂`-modules the comparison is derived extension of scalars applied to the factorization of
restriction of scalars, followed by the comparison of derived with degreewise extension of
scalars, followed by the degreewise underived comparison. -/
theorem restrictScalarsDerivedExtendIso_hom_app_Q
    (P : CochainComplex (ModuleCat.{u} A₂) ℤ) :
    (restrictScalarsDerivedExtendIso.{u, w} S (A₂ := A₂)).hom.app (DerivedCategory.Q.obj P) =
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.map
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategoryFactors.hom.app
            P) ≫
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).comparison.app
          (((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((restrictExtendScalarsComplexIso S (A₂ := A₂)).hom.app P) := by
  refine Eq.trans ?_ (restrictExtendScalarsDerivedQIso_hom_app S P)
  simp only [restrictScalarsDerivedExtendIso, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app, Localization.Lifting.compLeft_iso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id]

end Derived

end Localization

end RingTheory.TorIndependence

end
