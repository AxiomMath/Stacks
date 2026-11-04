module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineSpecBaseChange
public import StacksFrontier.Homology.KFlat.RestrictScalarsTensor
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsModelComp

/-!
# The base-change composition at a degreewise pullback, over an affine morphism

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` affine, and let `C` be a complex of quasi-coherent
`𝒪_X`-modules. The composition `Lg^*Rf_*C ⟶ Rf'_*L(g')^*C ⟶ Rf'_*(g')^*C` of the derived
base-change map with the derived direct image of the comparison `L(g')^*C ⟶ (g')^*C` is an
isomorphism as soon as `Lg^*(f_*C) ⟶ g^*(f_*C)` is: both direct images are computed degreewise
and the degreewise base-change map is invertible.

Over the square of spectra of a pushout square of rings `R → A`, `R → R'`, `A → A'`, `R' → A'`
and at `C = T̃` for a complex `T` of `A`-modules, the hypothesis holds as soon as `T` is K-flat as
a complex of `R`-modules.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_comp_comparison_of_isAffineHom`
* `Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_comp_comparison_specMap`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The base-change composition at a degreewise pullback, over an affine morphism.** For a
cartesian square with `f` affine and a complex `C` of quasi-coherent modules, the composition
`Lg^*Rf_*C ⟶ Rf'_*L(g')^*C ⟶ Rf'_*(g')^*C` is invertible as soon as the comparison
`Lg^*(f_*C) ⟶ g^*(f_*C)` is. -/
theorem isIso_derivedBaseChangeMap_comp_comparison_of_isAffineHom (sq : IsPullback g' f' f g)
    [IsAffineHom f]
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (hC : ∀ n, (C.X n).IsQuasicoherent)
    (h₃ : IsIso ((derivedPullbackComparison g.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)))) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) ≫
      (derivedPushforward f'.toLRSHom.toShHom).map
        ((derivedPullbackComparison g'.toLRSHom.toShHom).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C))) := by
  have hf' : IsAffineHom f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
    inferInstance
  have hG := derivedBaseChangeMap_Qh_comparison g'.toLRSHom.toShHom f'.toLRSHom.toShHom
    f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm sq.w)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)
  have h₁ : IsIso ((derivedPushforwardUnit f.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) :=
    isIso_derivedPushforwardUnit_app_of_isAffineHom f C hC
  have h₄ := isIso_underivedBaseChangeSquare_app_quotient sq C hC
  have h₅ : IsIso ((derivedPushforwardUnit f'.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((modulePullback g'.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C))) :=
    isIso_derivedPushforwardUnit_app_of_isAffineHom f' _ fun n =>
      @Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _ g' (C.X n) (hC n)
  have hR : IsIso ((derivedPullbackComparison g.toLRSHom.toShHom).app
        (((modulePushforward f.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) ≫
      DerivedCategory.Qh.map ((underivedBaseChangeSquare g'.toLRSHom.toShHom
        f'.toLRSHom.toShHom f.toLRSHom.toShHom g.toLRSHom.toShHom
        (comp_toShHom_of_comm sq.w)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C)) ≫
      (derivedPushforwardUnit f'.toLRSHom.toShHom).app
        (((modulePullback g'.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C))) :=
    @IsIso.comp_isIso _ _ _ _ _ _ _ h₃ (@IsIso.comp_isIso _ _ _ _ _ _ _
      (Functor.map_isIso DerivedCategory.Qh _) h₅)
  rw [← hG] at hR
  have hA : IsIso ((derivedPullback g.toLRSHom.toShHom).map
      ((derivedPushforwardUnit f.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C))) := Functor.map_isIso _ _
  exact IsIso.of_isIso_comp_left ((derivedPullback g.toLRSHom.toShHom).map
      ((derivedPushforwardUnit f.toLRSHom.toShHom).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C))) _

/-- At a complex of modules which is K-flat over the ring, derived extension of scalars is computed
degreewise. -/
theorem isIso_totalDerivedExtensionScalars_comparison_app_of_kFlat {R R' : Type u} [CommRing R]
    [CommRing R'] (φ : R →+* R') (T : CochainComplex (ModuleCat.{u} R) ℤ) (hT : T.KFlat) :
    IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      φ).comparison.app T) :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    φ).comparison_isIso_of_kFlat T hT

/-- **The base-change composition at `T̃` over a pushout square of rings.** If `T` is a complex
of `A`-modules which is K-flat as a complex of `R`-modules, the composition
`Lg^*Rf_*T̃ ⟶ Rf'_*(g')^*T̃` over the square of spectra is invertible. -/
theorem isIso_derivedBaseChangeMap_comp_comparison_specMap {R A R' A' : CommRingCat.{u}}
    {a : R ⟶ A} {b : R ⟶ R'} {c : A ⟶ A'} {d : R' ⟶ A'} (h : IsPushout a b c d)
    (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (hT : CochainComplex.KFlat.{u, u} (((ModuleCat.restrictScalars a.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj T)) :
    IsIso (derivedBaseChangeMap (Spec.map c).toLRSHom.toShHom (Spec.map d).toLRSHom.toShHom
        (Spec.map a).toLRSHom.toShHom (Spec.map b).toLRSHom.toShHom
        (comp_toShHom_of_comm (isPullback_specMap h).w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj T))) ≫
      (derivedPushforward (Spec.map d).toLRSHom.toShHom).map
        ((derivedPullbackComparison (Spec.map c).toLRSHom.toShHom).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj T)))) := by
  have e := (NatIso.mapHomologicalComplex (asIso (pushforwardTildeNatTrans R A a))
    (ComplexShape.up ℤ)).app T
  have hcmp := isIso_totalDerivedExtensionScalars_comparison_app_of_kFlat b.hom _ hT
  have h₀ := isIso_derivedPullbackComparison_tilde b _ hcmp
  have h₃ := (NatTrans.isIso_app_iff_of_iso
    (derivedPullbackComparison (Spec.map b).toLRSHom.toShHom)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso e)).1 h₀
  exact isIso_derivedBaseChangeMap_comp_comparison_of_isAffineHom (isPullback_specMap h) _
    (fun n => (inferInstance : ((tilde.functor A).obj (T.X n)).IsQuasicoherent)) h₃

end Stacks.Cohomology.DerivedBaseChange
