module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportFunctoriality.BoundedBelowToDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Refinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.UnboundedCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageCompositionUnbounded
import StacksCore.Tactic.StacksAttribute

/-!
# The map `Rf_! ⟶ Rf_*` on `D(X_étale, Λ)`

Let `f : X ⟶ Y` be a finite type separated morphism of schemes, `j : X ⟶ X̄` a compactification
of `X` over `Y` with structure morphism `f̄ : X̄ ⟶ Y`, and `Λ` a ring. [Stacks, Tag 0H6X]
constructs a map `Rf_! K ⟶ Rf_* K`, functorial in `K` in `D(X_étale, Λ)` when `Λ` is torsion
(the functor `Rf_!` of [Stacks, Tag 0F7H] being defined there for such `Λ`): since
`Rf_! = Rf̄_* ∘ Rj_!` and `Rf_* = Rf̄_* ∘ Rj_*` it is `Rf̄_*` applied to the map `Rj_! ⟶ Rj_*`
induced by the canonical transformation `j_! ⟶ j_*` of [Stacks, Tag 0F4L], followed by the
composition isomorphism `Rf̄_* ∘ Rj_* ≅ Rf_*` (Leray). The construction uses no hypothesis on
`Λ`; the bounded below case is `Stacks.EtaleCohomology.derivedLowerShriekToDirectImage`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroToDirectImageUnbounded`: `Rj_! ⟶ Rj_*`
  on unbounded derived categories, the right derived transformation of `j_! ⟶ j_*`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedToDirectImage`: **the map `Rf_! ⟶ Rf_*` of
  [Stacks, Tag 0H6X]** on `D(X_étale, Λ)`.

## References

* [Stacks Project, Tag 0H6X](https://stacks.math.columbia.edu/tag/0H6X)
* [Stacks Project, Tag 0F4L](https://stacks.math.columbia.edu/tag/0F4L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ]

/-- **The map `Rj_! ⟶ Rj_*` on unbounded derived categories** for an open immersion `j`: the
right derived transformation of the canonical map `j_! ⟶ j_*` of [Stacks, Tag 0F4L]
(`Stacks.EtaleCohomology.etaleModuleExtensionByZeroToDirectImage`), applied degreewise. -/
def etaleModuleDerivedExtensionByZeroToDirectImageUnbounded {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j ⟶
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j :=
  Functor.rightDerivedNatTrans _ _ (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ j)
    (HomologicalComplex.quasiIso (EtaleModules.{u, r} Λ U) (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j) (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- The defining property of `etaleModuleDerivedExtensionByZeroToDirectImageUnbounded`: at a
complex `K`, after the derivation unit of `Rj_!`, it is the degreewise map `j_! K ⟶ j_* K`
followed by the derivation unit of `Rj_*`. -/
theorem etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : CochainComplex (EtaleModules.{u, r} Λ U) ℤ) :
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j).app K ≫
        (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j).app
          (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j) (ComplexShape.up ℤ)).app K) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ j).app K :=
  Functor.rightDerivedNatTrans_app _ _ _ _ _ _ K

/-- The map `Rj_! ⟶ Rj_*` read through `Rj_! ≅ j_!` on derived categories
(`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroUnboundedIso`): at a complex `K` it is
the degreewise map `j_! K ⟶ j_* K` followed by the derivation unit of `Rj_*`. -/
theorem etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app_factors {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : CochainComplex (EtaleModules.{u, r} Λ U) ℤ) :
    (etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategoryFactors.inv.app K ≫
        (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).inv.app
          (DerivedCategory.Q.obj K) ≫
        (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j).app
          (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j) (ComplexShape.up ℤ)).app K) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ j).app K := by
  have h : (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ j).app K ≫
      (etaleModuleDerivedExtensionByZeroUnboundedIso.{u, r} Λ j).hom.app
        (DerivedCategory.Q.obj K) =
      (etaleModuleExtensionByZero.{u, r} Λ j).mapDerivedCategoryFactors.inv.app K := by
    rw [etaleModuleDerivedExtensionByZeroUnboundedIso,
      Stacks.Injectives.KInjectiveResolution.isoMapDerivedCategoryOfIsRightDerivedFunctor,
      Functor.rightDerivedNatIso_hom, Functor.rightDerivedNatTrans_app]
    simp
  rw [← h, Category.assoc, Iso.hom_inv_id_app_assoc,
    etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app]

/-- **The map `Rf_! ⟶ Rf_*` of [Stacks, Tag 0H6X]** on `D(X_étale, Λ)`. For a finite type
separated morphism `f : X ⟶ Y` and a compactification `j : X ⟶ X̄`, `f̄ : X̄ ⟶ Y` of `X` over `Y`
it is
```
Rf_! = Rf̄_* ∘ Rj_! ⟶ Rf̄_* ∘ Rj_* ≅ R(j ≫ f̄)_* = Rf_*,
```
`Rf̄_*` of the map `Rj_! ⟶ Rj_*` induced by the canonical transformation `j_! ⟶ j_*` of
[Stacks, Tag 0F4L], followed by the inverse of the Leray isomorphism of unbounded derived direct
images. It is natural in `K`. -/
@[stacks 0H6X "the map Rf_! ⟶ Rf_*, functorial in K, on D(X_étale, Λ)"]
def derivedLowerShriekUnboundedToDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) :
    derivedLowerShriekUnbounded.{u, r} f j Λ ⟶ etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f :=
  Functor.whiskerRight
      (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j.immersion)
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j.toBase) ≫
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ j.immersion j.toBase f
      (CompactificationOf.immersion_toBase j).symm).inv

/-! ### Associativity of the unbounded Leray isomorphisms -/

section Leray

/-- **The unbounded Leray isomorphism is the composition comparison** of [Stacks, Tag 05T2]
attached to the composition isomorphism `f_* ⋙ g_* ≅ (g ∘ f)_*` of sheaves. -/
theorem etaleModuleDerivedDirectImageUnboundedLerayIso_hom_eq_compComparison {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f g fg hfg).hom =
      Stacks.DerivedBaseChange.compComparison (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g)
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ fg)
        (Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, r} Λ f g fg hfg)
          (ComplexShape.up ℤ)) := by
  refine Functor.rightDerived_ext _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ fg)
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Stacks.DerivedBaseChange.compComparison_fac_app,
    etaleModuleDerivedDirectImageUnboundedLerayIso, Functor.rightDerivedNatIso_hom,
    Functor.rightDerivedNatTrans_app]
  simp [etaleModuleDerivedDirectImageUnboundedLerayUnit]

/-- The defining property of the unbounded Leray isomorphism: at a complex `K`, after the
derivation unit of `R(g ∘ f)_*`, it is the composition isomorphism of sheaves followed by the
derivation units of `Rg_*` and `Rf_*`. -/
@[reassoc]
theorem etaleModuleDerivedDirectImageUnboundedLerayIso_hom_fac {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) (K : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ fg).app K ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f g fg hfg).hom.app
          (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (etaleModuleDirectImageComp.{u, r} Λ f g fg hfg) (ComplexShape.up ℤ)).inv.app K) ≫
        (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g).app
          (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).map
          ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app K) := by
  rw [etaleModuleDerivedDirectImageUnboundedLerayIso_hom_eq_compComparison]
  exact Stacks.DerivedBaseChange.compComparison_fac_app _ _ _ _ _ K

/-- **The unbounded Leray isomorphisms are associative**: along `T ⟶ X ⟶ Y ⟶ Z`, taking
`R(fgh)_*` apart through `R(fg)_* ⋙ Rh_*` or through `Rf_* ⋙ R(gh)_*` gives the same isomorphism
with `Rf_* ⋙ Rg_* ⋙ Rh_*`, on `D(T_étale, Λ)`. -/
theorem etaleModuleDerivedDirectImageUnboundedLerayIso_assoc {T X Y Z : Scheme.{u}} (f : T ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) :
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ fg h fgh h₁).hom ≫
        Functor.whiskerRight
          (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f g fg hfg).hom
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h) =
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f gh fgh h₂).hom ≫
        Functor.whiskerLeft (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f)
          (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ g h gh hgh).hom := by
  simp only [etaleModuleDerivedDirectImageUnboundedLerayIso_hom_eq_compComparison]
  refine Stacks.DerivedBaseChange.compComparison_paste
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ _ _ _ _ _ _ _ fun K => ?_
  ext n : 1
  have hc := smallEtalePushforwardComp'_inv_app_cocycle f g h fg hfg gh hgh fgh h₁ h₂
    (ModuleCat.{max (u + 1) r} Λ) (K.X n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f]
  let A := etaleModuleDirectImageComp.{u, r} Λ fg h fgh h₁
  let B := etaleModuleDirectImageComp.{u, r} Λ f g fg hfg
  let C := etaleModuleDirectImageComp.{u, r} Λ f gh fgh h₂
  let D := etaleModuleDirectImageComp.{u, r} Λ g h gh hgh
  have hc' : ((A.app (K.X n)).symm ≪≫
      (etaleModuleDirectImage.{u, r} Λ h).mapIso (B.app (K.X n)).symm) =
      (C.app (K.X n)).symm ≪≫
        (D.app ((etaleModuleDirectImage.{u, r} Λ f).obj (K.X n))).symm := Iso.ext hc
  simpa [A, B, C, D] using congrArg (fun e => e.symm.hom) hc'

/-- `etaleModuleDerivedDirectImageUnboundedLerayIso_assoc` read at an object. -/
theorem etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app {T X Y Z : Scheme.{u}}
    (f : T ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z)
    (hgh : gh = g ≫ h) (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh)
    (K : DerivedCategory (EtaleModules.{u, r} Λ T)) :
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ fg h fgh h₁).hom.app K ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ h).map
          ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f g fg hfg).hom.app K) =
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ f gh fgh h₂).hom.app K ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ g h gh hgh).hom.app
          ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj K) :=
  NatTrans.congr_app
    (etaleModuleDerivedDirectImageUnboundedLerayIso_assoc Λ f g h fg hfg gh hgh fgh h₁ h₂) K

end Leray

/-! ### Independence of the compactification -/

section Independence

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k)

/-- The composition comparison `R(j̄)_* ⟶ Rḡ_* ⋙ R(k̄)_*` of unbounded derived direct images
attached to a morphism of compactifications is the Leray isomorphism. -/
theorem derivedBaseComparisonUnboundedUniv_eq_lerayIso_hom :
    derivedBaseComparisonUnboundedUniv.{u, r} Λ g =
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ (CompactificationOf.Hom.map g)
        k.toBase j.toBase (CompactificationOf.map_comp_toBase g).symm).hom :=
  (etaleModuleDerivedDirectImageUnboundedLerayIso_hom_eq_compComparison Λ _ _ _ _).symm

/-- **The map `Rk_! ⟶ Rḡ_* ∘ Rj_!` of [Stacks, Tag 0F7G] is compatible with the maps
`Rj_! ⟶ Rj_*`**, on unbounded derived categories: followed by `Rḡ_*` of `Rj_! ⟶ Rj_*` it is
`Rk_! ⟶ Rk_*` followed by the Leray isomorphism `Rk_* ≅ Rḡ_* ∘ Rj_*`. -/
theorem derivedRefinementComparisonUnboundedUniv_comp_toDirectImage :
    derivedRefinementComparisonUnboundedUniv.{u, r} Λ g ≫
        Functor.whiskerRight
          (etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j.immersion)
          (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ (CompactificationOf.Hom.map g)) =
      etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ k.immersion ≫
        (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ j.immersion
          (CompactificationOf.Hom.map g) k.immersion
          (CompactificationOf.immersion_comp_map g).symm).hom := by
  refine Functor.rightDerived_ext _
    (etaleModuleDerivedExtensionByZeroUnboundedUnit.{u, r} Λ k.immersion)
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hdeg : (Functor.mapHomologicalComplexCompIso (refinementIsoUniv.{u, r} Λ g).symm
        (ComplexShape.up ℤ)).inv.app K ≫
      ((etaleModuleDirectImage.{u, r} Λ (CompactificationOf.Hom.map g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex
          (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j.immersion)
          (ComplexShape.up ℤ)).app K) =
      (NatTrans.mapHomologicalComplex (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ k.immersion)
          (ComplexShape.up ℤ)).app K ≫
        (Functor.mapHomologicalComplexCompIso (etaleModuleDirectImageComp.{u, r} Λ j.immersion
          (CompactificationOf.Hom.map g) k.immersion
          (CompactificationOf.immersion_comp_map g).symm) (ComplexShape.up ℤ)).inv.app K := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
      Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f, Iso.symm_inv]
    exact etaleModuleRefinementComparison_comp_map Λ (CompactificationOf.immersion_comp_map g) _
  have nu :=
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ (CompactificationOf.Hom.map g)).naturality
      ((NatTrans.mapHomologicalComplex
        (etaleModuleExtensionByZeroToDirectImage.{u, r} Λ j.immersion) (ComplexShape.up ℤ)).app K)
  simp only [Functor.comp_map] at nu
  rw [derivedRefinementComparisonUnboundedUniv,
    Stacks.DerivedBaseChange.compComparison_fac_app_assoc, ← Functor.map_comp,
    etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app, Functor.map_comp,
    reassoc_of% etaleModuleDerivedExtensionByZeroToDirectImageUnbounded_app,
    etaleModuleDerivedDirectImageUnboundedLerayIso, Functor.rightDerivedNatIso_hom,
    Functor.rightDerivedNatTrans_app]
  simp only [etaleModuleDerivedDirectImageUnboundedLerayUnit, NatTrans.comp_app, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom]
  rw [← reassoc_of% nu]
  exact (Functor.map_comp_assoc _ _ _ _).symm.trans ((eq_whisker
    (congrArg DerivedCategory.Q.map hdeg) _).trans (Functor.map_comp_assoc _ _ _ _))

/-- **The map `Rf_! ⟶ Rf_*` is carried to itself by a morphism of compactifications**, on
`D(X_étale, Λ)`: for `g : j ⟶ k`, the comparison `Rf_!^k ⟶ Rf_!^j` followed by the map
`Rf_!^j ⟶ Rf_*` is the map `Rf_!^k ⟶ Rf_*`. -/
theorem derivedLowerShriekUnboundedHomUniv_comp_toDirectImage :
    derivedLowerShriekUnboundedHomUniv.{u, r} Λ g ≫
        derivedLowerShriekUnboundedToDirectImage.{u, r} Λ f j =
      derivedLowerShriekUnboundedToDirectImage.{u, r} Λ f k := by
  refine NatTrans.ext (funext fun K => ?_)
  have hA := NatTrans.congr_app (derivedRefinementComparisonUnboundedUniv_comp_toDirectImage Λ g) K
  have hB := etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ j.immersion
    (CompactificationOf.Hom.map g) k.toBase k.immersion
    (CompactificationOf.immersion_comp_map g).symm j.toBase
    (CompactificationOf.map_comp_toBase g).symm f (CompactificationOf.immersion_toBase k).symm
    (CompactificationOf.immersion_toBase j).symm K
  have hinv : inv (derivedBaseComparisonUnboundedUniv.{u, r} Λ g) =
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ (CompactificationOf.Hom.map g)
        k.toBase j.toBase (CompactificationOf.map_comp_toBase g).symm).inv :=
    IsIso.inv_eq_of_hom_inv_id (by rw [derivedBaseComparisonUnboundedUniv_eq_lerayIso_hom,
      Iso.hom_inv_id])
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hA
  have nb := (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ
    (CompactificationOf.Hom.map g) k.toBase j.toBase
      (CompactificationOf.map_comp_toBase g).symm).inv.naturality
      ((etaleModuleDerivedExtensionByZeroToDirectImageUnbounded.{u, r} Λ j.immersion).app K)
  simp only [Functor.comp_map] at nb
  simp only [NatTrans.comp_app, derivedLowerShriekUnboundedHomUniv_app, hinv,
    derivedLowerShriekUnboundedToDirectImage, Functor.whiskerRight_app, Category.assoc]
  rw [← reassoc_of% nb, ← Functor.map_comp_assoc, hA, Functor.map_comp_assoc]
  congr 1
  rw [← cancel_epi ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, r} Λ k.immersion k.toBase
    f (CompactificationOf.immersion_toBase k).symm).hom.app K), reassoc_of% hB]
  simp

end Independence

/-- **[Stacks, Tag 0H6X]: the map `Rf_! ⟶ Rf_*` does not depend on the compactification**, on
`D(X_étale, Λ)` for a torsion ring `Λ`: for any two compactifications `j₁`, `j₂` of `X` over
`Y`, the canonical isomorphism `Rf_!^{j₁} ≅ Rf_!^{j₂}` of [Stacks, Tag 0F7I], computed through a
compactification dominating both, followed by the map `Rf_!^{j₂} ⟶ Rf_*` is the map
`Rf_!^{j₁} ⟶ Rf_*`. -/
@[stacks 0H6X "independence of the compactification, on D(X_étale, Λ), Λ torsion"]
theorem derivedLowerShriekUnboundedCompactificationIsoUniv_hom_comp_toDirectImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (j₁ j₂ : CompactificationOf (Over.mk f))
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    (derivedLowerShriekUnboundedCompactificationIsoUniv f j₁ j₂ Λ hΛ).hom ≫
        derivedLowerShriekUnboundedToDirectImage.{u, r} Λ f j₂ =
      derivedLowerShriekUnboundedToDirectImage.{u, r} Λ f j₁ :=
  IsCofiltered.isoSystemComparison_hom_comp _
    (fun j => derivedLowerShriekUnboundedToDirectImage.{u, r} Λ f j)
    (fun g => derivedLowerShriekUnboundedHomUniv_comp_toDirectImage Λ g) j₁ j₂

end Stacks.EtaleCohomology

end
