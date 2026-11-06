module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayPullbackComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The derived base change map and the units of the derived adjunctions

Consider four adjunctions `g^* ⊣ g_*`, `f^* ⊣ f_*`, `e^* ⊣ e_*`, `h^* ⊣ h_*` between abelian
categories, the left adjoints exact, arranged around a square

```
𝒴 ←-h^*- 𝒳
↑e^*     ↑f^*
𝒯 ←-g^*- 𝒮
```

together with a comparison `σ : e_* ⋙ g_* ≅ h_* ⋙ f_*` of the two composite right adjoints. The
mate of `σ` is the underived base change map `g_* ⋙ f^* ⟶ e^* ⋙ h_*`, and
`Stacks.Cohomology.BaseChange.derived` descends it to the bounded below derived categories, giving
the derived base change map `β : Rg_* ⋙ f^* ⟶ e^* ⋙ Rh_*`. This is how the base change map of
abelian sheaves on small étale sites is built
(`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`).

This file proves that `β` is compatible with the units of the derived adjunctions
`Adjunction.rightDerivedFunctorPlus`: for every `M` in `D⁺(𝒮)`,

`f^*(η^g_M) ≫ β_{g^*M} = η^h_{f^*M} ≫ Rh_*(θ_M)`,

where `θ : f^* ⋙ h^* ≅ g^* ⋙ e^*` is the derived comparison of the two composite left adjoints
attached to `σ`. Read through the adjunctions, this says that for `φ : g^*M ⟶ N` the transpose of
`θ_M ≫ e^*φ` across `h^* ⊣ Rh_*` is `f^*` of the transpose of `φ` across `g^* ⊣ Rg_*`, followed by
`β_N`. In the étale situation, with `M` a coefficient object on the base, this is the statement
that the base change map computes the pullback map on cohomology.

## Main results

* `CategoryTheory.Adjunction.rightDerivedFunctorPlus_unit_app_Qh` — the unit of the derived
  adjunction of an adjunction with homology-preserving left adjoint, at the image of a complex.
* `Stacks.Cohomology.BaseChange.map_unit_comp_mate_app` — the underived compatibility of the mate
  with the units.
* `Stacks.Cohomology.BaseChange.map_derivedUnit_comp_derivedMate_app` — **the derived
  compatibility**.
* `Stacks.Cohomology.BaseChange.homEquiv_derivedSquareLeftIso_comp_map` — the same, read through
  the derived adjunctions.
* `Stacks.Cohomology.BaseChange.bijective_map_of_isIso_derivedMate_app` — if `β_N` is invertible
  and `f^*` is bijective on `Hom(M, Rg_*N)`, then `e^*` is bijective on `Hom(g^*M, N)`.

## Implementation notes

The derived compatibility is an identity of transformations out of the derived functor of the
exact `f^*`, so it is checked on objects `Qh(K)` (`Localization.natTrans_ext`). There every unit of
right derivation of an exact functor is invertible, the derived adjunction units are read off by
`rightDerivedFunctorPlus_unit_app_Qh`, `β` by `Stacks.Cohomology.BaseChange.derived_fac` and `θ`
by `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact_fac`; what is left is the
underived compatibility applied degreewise, which is `map_unit_comp_mate_app` through
`Stacks.Cohomology.BaseChange.mapPlus`.

The descent `Stacks.Cohomology.BaseChange.derived` is built under the standard model of the
derived category, which therefore fixes the model in the second half of the file.

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {A : Type*} [Category* A] [Abelian A]
  {B : Type*} [Category* B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A] [EnoughInjectives B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] (adj : L ⊣ R) [L.PreservesHomology]

/-- **The unit of the derived adjunction at the image of a complex.** For `adj : L ⊣ R` with `L`
preserving homology, the unit of `Adjunction.rightDerivedFunctorPlus adj` at `Qh(K)` is the
degreewise unit, followed by the unit of right derivation of `R` and by `RR` of the (invertible)
unit of right derivation of `L`. -/
theorem rightDerivedFunctorPlus_unit_app_Qh (K : HomotopyCategory.Plus A) :
    letI := L.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
    adj.rightDerivedFunctorPlus.unit.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
        R.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj K) ≫
          R.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlusUnith.app K) := by
  have := L.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hαR : (L.rightDerivedFunctorPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (asIso L.rightDerivedFunctorPlusUnith).inv R.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso L.rightDerivedFunctorPlusUnith).symm _)
  have h := adj.mapHomotopyCategoryPlus.derivedη_fac_app
    (HomotopyCategory.Plus.quasiIso A) (asIso L.rightDerivedFunctorPlusUnith).inv
    R.rightDerivedFunctorPlusUnith K
  have e : adj.rightDerivedFunctorPlus.unit = adj.mapHomotopyCategoryPlus.derivedη
    (HomotopyCategory.Plus.quasiIso A) (asIso L.rightDerivedFunctorPlusUnith).inv
    R.rightDerivedFunctorPlusUnith := rfl
  rw [e, ← cancel_mono (R.rightDerivedFunctorPlus.map
    ((asIso L.rightDerivedFunctorPlusUnith).inv.app K)), h, Category.assoc, Category.assoc,
    ← Functor.map_comp]
  simp

end CategoryTheory.Adjunction

namespace Stacks.Cohomology.BaseChange

section Underived

variable {𝒮 𝒯 𝒳 𝒴 : Type*} [Category* 𝒮] [Category* 𝒯] [Category* 𝒳] [Category* 𝒴]
  {Lg : 𝒮 ⥤ 𝒯} {Pg : 𝒯 ⥤ 𝒮} (adjg : Lg ⊣ Pg)
  {Lf : 𝒮 ⥤ 𝒳} {Pf : 𝒳 ⥤ 𝒮} (adjf : Lf ⊣ Pf)
  {Le : 𝒯 ⥤ 𝒴} {Pe : 𝒴 ⥤ 𝒯} (adje : Le ⊣ Pe)
  {Lh : 𝒳 ⥤ 𝒴} {Ph : 𝒴 ⥤ 𝒳} (adjh : Lh ⊣ Ph)
  (σ : Pe ⋙ Pg ≅ Ph ⋙ Pf)

/-- The comparison `f^* ⋙ h^* ≅ g^* ⋙ e^*` of the two composite left adjoints of the square, the
conjugate of the comparison `σ : e_* ⋙ g_* ≅ h_* ⋙ f_*` of the composite right adjoints. -/
abbrev squareLeftIso : Lf ⋙ Lh ≅ Lg ⋙ Le :=
  (conjugateIsoEquiv (adjg.comp adje) (adjf.comp adjh)).symm σ

/-- **The mate of `σ` and the units.** `f^*` of the unit of `g^* ⊣ g_*`, followed by the mate of
`σ`, is the unit of `h^* ⊣ h_*` followed by `h_*` of the comparison of the composite left
adjoints. Both are transposed across `f^* ⊣ f_*`, where they become the defining identities of
the mate (`Stacks.Cohomology.BaseChange.unit_comp_map_mate`) and of the conjugate
(`CategoryTheory.unit_conjugateEquiv_symm`). -/
theorem map_unit_comp_mate_app (x : 𝒮) :
    Lf.map (adjg.unit.app x) ≫ (mate adjf adje Pg Ph σ).app (Lg.obj x) =
      adjh.unit.app (Lf.obj x) ≫ Ph.map ((squareLeftIso adjg adjf adje adjh σ).hom.app x) := by
  apply (adjf.homEquiv _ _).injective
  have h1 := unit_comp_map_mate adjf adje Pg Ph σ (Lg.obj x)
  have h2 := unit_conjugateEquiv_symm (adjg.comp adje) (adjf.comp adjh) σ.hom x
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] at h2
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  dsimp only [Functor.id_obj]
  rw [adjf.unit_naturality_assoc]
  exact (adjg.unit.app x ≫= h1).trans h2

end Underived

section Derived

-- `Stacks.Cohomology.BaseChange.derived` (`StacksFrontier/Topology/Sheaves/Cohomology/
-- StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/AbelianBaseChangeMap.lean:204`) is built under the standard model.
attribute [local instance] HasDerivedCategory.standard

variable {𝒮 𝒯 𝒳 𝒴 : Type*} [Category* 𝒮] [Category* 𝒯] [Category* 𝒳] [Category* 𝒴]
  [Abelian 𝒮] [Abelian 𝒯] [Abelian 𝒳] [Abelian 𝒴]
  [EnoughInjectives 𝒮] [EnoughInjectives 𝒯] [EnoughInjectives 𝒳] [EnoughInjectives 𝒴]
  {Lg : 𝒮 ⥤ 𝒯} {Pg : 𝒯 ⥤ 𝒮} (adjg : Lg ⊣ Pg)
  {Lf : 𝒮 ⥤ 𝒳} {Pf : 𝒳 ⥤ 𝒮} (adjf : Lf ⊣ Pf)
  {Le : 𝒯 ⥤ 𝒴} {Pe : 𝒴 ⥤ 𝒯} (adje : Le ⊣ Pe)
  {Lh : 𝒳 ⥤ 𝒴} {Ph : 𝒴 ⥤ 𝒳} (adjh : Lh ⊣ Ph)
  [Lg.Additive] [Pg.Additive] [Lf.Additive] [Le.Additive] [Lh.Additive] [Ph.Additive]
  [PreservesFiniteLimits Lg] [PreservesFiniteColimits Lg]
  [PreservesFiniteLimits Lf] [PreservesFiniteColimits Lf]
  [PreservesFiniteLimits Le] [PreservesFiniteColimits Le]
  [PreservesFiniteLimits Lh] [PreservesFiniteColimits Lh]
  (σ : Pe ⋙ Pg ≅ Ph ⋙ Pf)

/-- The derived comparison `Rf^* ⋙ Rh^* ≅ Rg^* ⋙ Re^*` of the two composite left adjoints, the
derived functor of `Stacks.Cohomology.BaseChange.squareLeftIso` read through the composition
isomorphisms of right derived functors of exact functors. -/
def derivedSquareLeftIso :
    Lf.rightDerivedFunctorPlus ⋙ Lh.rightDerivedFunctorPlus ≅
      Lg.rightDerivedFunctorPlus ⋙ Le.rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusCompIsoOfExact Lf Lh (Lg ⋙ Le)
      (squareLeftIso adjg adjf adje adjh σ) ≪≫
    (Functor.rightDerivedFunctorPlusCompIsoOfExact Lg Le (Lg ⋙ Le) (Iso.refl _)).symm

/-- The unit of right derivation of the exact `f^*` is invertible. -/
instance isIso_rightDerivedFunctorPlusUnit_exactPullback : IsIso Lf.rightDerivedFunctorPlusUnith :=
  exactUnit_isIso Lf

/-- The derived base change map `Rg_* ⋙ Rf^* ⟶ Re^* ⋙ Rh_*`: the descent, by
`Stacks.Cohomology.BaseChange.derived`, of the mate of `σ`. -/
abbrev derivedMate :
    Pg.rightDerivedFunctorPlus ⋙ Lf.rightDerivedFunctorPlus ⟶
      Le.rightDerivedFunctorPlus ⋙ Ph.rightDerivedFunctorPlus :=
  derived Pg Ph Lf Le (mate adjf adje Pg Ph σ) (asIso Lf.rightDerivedFunctorPlusUnith)

omit [EnoughInjectives 𝒴] [Pg.Additive] [Ph.Additive]
  [PreservesFiniteLimits Lg] [PreservesFiniteColimits Lg] [PreservesFiniteLimits Lf]
  [PreservesFiniteColimits Lf] in
/-- **The characterizing factorization of `derivedSquareLeftIso`** on the image of a complex: it is
the degreewise comparison of the composite left adjoints, read through the units of right
derivation. -/
theorem derivedSquareLeftIso_fac (K : HomotopyCategory.Plus 𝒮) :
    Lh.rightDerivedFunctorPlusUnith.app (Lf.mapHomotopyCategoryPlus.obj K) ≫
      Lh.rightDerivedFunctorPlus.map (Lf.rightDerivedFunctorPlusUnith.app K) ≫
        (derivedSquareLeftIso adjg adjf adje adjh σ).hom.app (DerivedCategory.Plus.Qh.obj K) =
    DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (squareLeftIso adjg adjf adje adjh σ)).hom.app K ≫
          (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (Lg ⋙ Le))).inv.app K) ≫
      Le.rightDerivedFunctorPlusUnith.app (Lg.mapHomotopyCategoryPlus.obj K) ≫
        Le.rightDerivedFunctorPlus.map (Lg.rightDerivedFunctorPlusUnith.app K) := by
  have h1 := Functor.rightDerivedFunctorPlusCompIsoOfExact_fac Lf Lh (Lg ⋙ Le)
    (squareLeftIso adjg adjf adje adjh σ) K
  have h2 := Functor.rightDerivedFunctorPlusCompIsoOfExact_fac Lg Le (Lg ⋙ Le) (Iso.refl _) K
  simp only [derivedSquareLeftIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [reassoc_of% h1, Functor.map_comp, Category.assoc]
  congr 1
  rw [← Iso.app_inv, Iso.comp_inv_eq, Iso.app_hom, Category.assoc, Category.assoc, h2,
    ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- `map_derivedUnit_comp_derivedMate_app` at the image of a complex. -/
theorem map_derivedUnit_comp_derivedMate_app_Qh (K : HomotopyCategory.Plus 𝒮) :
    Lf.rightDerivedFunctorPlus.map
        (adjg.rightDerivedFunctorPlus.unit.app (DerivedCategory.Plus.Qh.obj K)) ≫
      (derivedMate adjf adje σ).app
        (Lg.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) =
    adjh.rightDerivedFunctorPlus.unit.app
        (Lf.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      Ph.rightDerivedFunctorPlus.map
        ((derivedSquareLeftIso adjg adjf adje adjh σ).hom.app (DerivedCategory.Plus.Qh.obj K)) := by
  have hnat := (derivedMate adjf adje σ).naturality (Lg.rightDerivedFunctorPlusUnith.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hnat
  have hfac := congrArg (fun t => t.app (Lg.mapHomotopyCategoryPlus.obj K))
    (derived_fac Pg Ph Lf Le (mate adjf adje Pg Ph σ) (asIso Lf.rightDerivedFunctorPlusUnith))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp] at hfac
  rw [Adjunction.rightDerivedFunctorPlus_unit_app_Qh adjg K, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, hnat, reassoc_of% hfac]
  simp only [onHomotopy, NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Category.id_comp, Category.assoc]
  have h5 := (asIso Lf.rightDerivedFunctorPlusUnith).inv.naturality
    (adjg.mapHomotopyCategoryPlus.unit.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at h5
  rw [reassoc_of% h5, ← cancel_epi ((asIso Lf.rightDerivedFunctorPlusUnith).hom.app K),
    Iso.hom_inv_id_app_assoc]
  have h6 := adjh.rightDerivedFunctorPlus.unit.naturality (Lf.rightDerivedFunctorPlusUnith.app K)
  simp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h6
  simp only [asIso_hom]
  rw [reassoc_of% h6, Adjunction.rightDerivedFunctorPlus_unit_app_Qh adjh
    (Lf.mapHomotopyCategoryPlus.obj K)]
  have hR : Ph.rightDerivedFunctorPlus.map
        (Lh.rightDerivedFunctorPlusUnith.app (Lf.mapHomotopyCategoryPlus.obj K)) ≫
      Ph.rightDerivedFunctorPlus.map
        (Lh.rightDerivedFunctorPlus.map (Lf.rightDerivedFunctorPlusUnith.app K)) ≫
      Ph.rightDerivedFunctorPlus.map
        ((derivedSquareLeftIso adjg adjf adje adjh σ).hom.app (DerivedCategory.Plus.Qh.obj K)) =
      Ph.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (squareLeftIso adjg adjf adje adjh σ)).hom.app K ≫
          (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (Lg ⋙ Le))).inv.app K)) ≫
      Ph.rightDerivedFunctorPlus.map
        (Le.rightDerivedFunctorPlusUnith.app (Lg.mapHomotopyCategoryPlus.obj K)) ≫
      Ph.rightDerivedFunctorPlus.map
        (Le.rightDerivedFunctorPlus.map (Lg.rightDerivedFunctorPlusUnith.app K)) := by
    simp only [← Functor.map_comp]
    rw [derivedSquareLeftIso_fac]
  simp only [Category.assoc]
  rw [hR]
  have h9 := Ph.rightDerivedFunctorPlusUnith.naturality
    ((Functor.mapHomotopyCategoryPlusCompIso (squareLeftIso adjg adjf adje adjh σ)).hom.app K ≫
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (Lg ⋙ Le))).inv.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at h9
  rw [← reassoc_of% h9, ← DerivedCategory.Plus.Qh.map_comp_assoc,
    ← DerivedCategory.Plus.Qh.map_comp_assoc]
  congr 2
  have key : Functor.whiskerRight adjg.unit Lf ≫ Functor.whiskerLeft Lg (mate adjf adje Pg Ph σ) =
      Functor.whiskerLeft Lf adjh.unit ≫
        Functor.whiskerRight (squareLeftIso adjg adjf adje adjh σ).hom Ph := by
    ext x
    simpa using map_unit_comp_mate_app adjg adjf adje adjh σ x
  have h10 := congrArg (fun t => (mapPlus t).app K) key
  simp only [mapPlus_comp, NatTrans.comp_app] at h10
  rw [mapHomotopyCategoryPlusCompIso_refl_hom_comp, mapHomotopyCategoryPlusCompIso_refl_comp_inv,
    mapHomotopyCategoryPlusCompIso_refl_comp_inv,
    Stacks.LerayPullbackComparison.mapHomotopyCategoryPlus_unit_app adjg K,
    Stacks.LerayPullbackComparison.mapHomotopyCategoryPlus_unit_app adjh]
  rw [mapPlus_whiskerRight_app, mapPlus_whiskerLeft_app, mapPlus_whiskerLeft_app,
    mapPlus_whiskerRight_app] at h10
  exact h10

/-- **The derived base change map and the units of the derived adjunctions.** For every `M` in
`D⁺(𝒮)`, `Rf^*` of the unit of `Rg^* ⊣ Rg_*` at `M`, followed by the derived base change map at
`Rg^*M`, is the unit of `Rh^* ⊣ Rh_*` at `Rf^*M` followed by `Rh_*` of the derived comparison of
the composite left adjoints. -/
theorem map_derivedUnit_comp_derivedMate_app (M : DerivedCategory.Plus 𝒮) :
    Lf.rightDerivedFunctorPlus.map (adjg.rightDerivedFunctorPlus.unit.app M) ≫
      (derivedMate adjf adje σ).app (Lg.rightDerivedFunctorPlus.obj M) =
    adjh.rightDerivedFunctorPlus.unit.app (Lf.rightDerivedFunctorPlus.obj M) ≫
      Ph.rightDerivedFunctorPlus.map ((derivedSquareLeftIso adjg adjf adje adjh σ).hom.app M) := by
  have key : Functor.whiskerRight adjg.rightDerivedFunctorPlus.unit Lf.rightDerivedFunctorPlus ≫
      Functor.whiskerLeft Lg.rightDerivedFunctorPlus (derivedMate adjf adje σ) =
    Functor.whiskerLeft Lf.rightDerivedFunctorPlus adjh.rightDerivedFunctorPlus.unit ≫
      Functor.whiskerRight (derivedSquareLeftIso adjg adjf adje adjh σ).hom
        Ph.rightDerivedFunctorPlus := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso 𝒮)
    intro K
    simpa using map_derivedUnit_comp_derivedMate_app_Qh adjg adjf adje adjh σ K
  simpa using congrArg (fun t => t.app M) key

/-- **The derived base change map computes the pullback on morphisms out of a pullback.** For
`φ : Rg^*M ⟶ N`, the transpose across `Rh^* ⊣ Rh_*` of `θ_M ≫ Re^*φ` is `Rf^*` of the transpose
of `φ` across `Rg^* ⊣ Rg_*`, followed by the derived base change map at `N`. -/
theorem homEquiv_derivedSquareLeftIso_comp_map (M : DerivedCategory.Plus 𝒮)
    {N : DerivedCategory.Plus 𝒯} (φ : Lg.rightDerivedFunctorPlus.obj M ⟶ N) :
    adjh.rightDerivedFunctorPlus.homEquiv _ _
        ((derivedSquareLeftIso adjg adjf adje adjh σ).hom.app M ≫
          Le.rightDerivedFunctorPlus.map φ) =
      Lf.rightDerivedFunctorPlus.map (adjg.rightDerivedFunctorPlus.homEquiv _ _ φ) ≫
        (derivedMate adjf adje σ).app N := by
  have hn := (derivedMate adjf adje σ).naturality φ
  simp only [Functor.comp_map] at hn
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc, hn]
  rw [reassoc_of% (map_derivedUnit_comp_derivedMate_app adjg adjf adje adjh σ M)]

include adjg adjh in
/-- **Bijectivity of the pullback on morphisms out of a pullback.** If the derived base change map
is invertible at `N` and `Rf^*` is bijective on `Hom(M, Rg_*N)`, then `Re^*` is bijective on
`Hom(Rg^*M, N)`. -/
theorem bijective_map_of_isIso_derivedMate_app (M : DerivedCategory.Plus 𝒮)
    (N : DerivedCategory.Plus 𝒯) (hN : IsIso ((derivedMate adjf adje σ).app N))
    (hM : Function.Bijective (fun ψ : M ⟶ Pg.rightDerivedFunctorPlus.obj N ↦
      Lf.rightDerivedFunctorPlus.map ψ)) :
    Function.Bijective (fun φ : Lg.rightDerivedFunctorPlus.obj M ⟶ N ↦
      Le.rightDerivedFunctorPlus.map φ) := by
  have e : (fun φ : Lg.rightDerivedFunctorPlus.obj M ⟶ N ↦
      (derivedSquareLeftIso adjg adjf adje adjh σ).hom.app M ≫
        Le.rightDerivedFunctorPlus.map φ) =
      (adjh.rightDerivedFunctorPlus.homEquiv _ _).symm ∘
        (fun ψ ↦ ψ ≫ (derivedMate adjf adje σ).app N) ∘
          (fun ψ : M ⟶ Pg.rightDerivedFunctorPlus.obj N ↦ Lf.rightDerivedFunctorPlus.map ψ) ∘
            (adjg.rightDerivedFunctorPlus.homEquiv _ _) := by
    funext φ
    simp only [Function.comp_apply]
    rw [← homEquiv_derivedSquareLeftIso_comp_map adjg adjf adje adjh σ, Equiv.symm_apply_apply]
  have hb : Function.Bijective (fun φ : Lg.rightDerivedFunctorPlus.obj M ⟶ N ↦
      (derivedSquareLeftIso adjg adjf adje adjh σ).hom.app M ≫
        Le.rightDerivedFunctorPlus.map φ) := by
    rw [e]
    refine (Equiv.bijective _).comp ((?_ : Function.Bijective _).comp
      (hM.comp (Equiv.bijective _)))
    exact ((asIso ((derivedMate adjf adje σ).app N)).homToEquiv).bijective
  have e' : (fun φ : Lg.rightDerivedFunctorPlus.obj M ⟶ N ↦ Le.rightDerivedFunctorPlus.map φ) =
      ((derivedSquareLeftIso adjg adjf adje adjh σ).app M).homFromEquiv ∘
        (fun φ : Lg.rightDerivedFunctorPlus.obj M ⟶ N ↦
          (derivedSquareLeftIso adjg adjf adje adjh σ).hom.app M ≫
            Le.rightDerivedFunctorPlus.map φ) := by
    funext φ
    simp [Iso.homFromEquiv]
  rw [e']
  exact (Equiv.bijective _).comp hb

end Derived

end Stacks.Cohomology.BaseChange
