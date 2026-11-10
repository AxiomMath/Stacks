module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensorIso

/-!
# The derived direct image to an affine source reflects isomorphisms of `D_QCoh`

Let `g : Y' ⟶ Y` be a morphism of algebraic spaces with `Y'` affine.  The derived direct image
`Rg_*` reflects isomorphisms between objects of `D_QCoh(𝒪_{Y'})`: the cone `C` of a morphism
inverted by `Rg_*` has `Rg_*C = 0`, so `Hom(𝒪_{Y'}[n], C) = Hom(Lg^*𝒪_Y[n], C) = Hom(𝒪_Y[n], Rg_*C)`
vanishes for every `n`, and `𝒪_{Y'}` is a weak generator of `D_QCoh(𝒪_{Y'})`.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_derivedModulePushforward_map`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y Y' : AlgebraicSpaces B S hS}

/-- **`Rg_*` reflects isomorphisms of `D_QCoh` out of an affine algebraic space.**  For
`g : Y' ⟶ Y` with `Y'` affine, a morphism `φ` of `D_QCoh(𝒪_{Y'})` is an isomorphism as soon as
`Rg_*φ` is. -/
theorem isIso_of_isIso_derivedModulePushforward_map (g : Y' ⟶ Y)
    (hY' : IsAffineSpace B S hS Y'.1)
    {M N : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y'))}
    (hM : QcohDerived B S hS Y' M) (hN : QcohDerived B S hS Y' N) (φ : M ⟶ N)
    (h : IsIso ((derivedModulePushforward B S hS g).map φ)) : IsIso φ := by
  let R := derivedModulePushforward B S hS g
  let : R.CommShift ℤ := derivedModulePushforward_commShift B S hS g
  let : R.IsTriangulated := derivedModulePushforward_isTriangulated B S hS g
  obtain ⟨Z, a, b, hT⟩ := distinguished_cocone_triangle φ
  have hZ : QcohDerived B S hS Y' Z :=
    (QcohDerived B S hS Y').ext_of_isTriangulatedClosed₃ _ hT hM hN
  have hRT := R.map_distinguished _ hT
  have hRZ : IsZero (R.obj Z) :=
    (Triangle.isZero₃_iff_isIso₁ _ hRT).2 h
  have hzero : ∀ (q : ℤ) (k : structureDerived Y' ⟶ Z⟦q⟧), k = 0 := fun q k => by
    let adj := smallEtaleDerivedModuleAdjunction B S hS g
    let e : (smallEtaleDerivedModulePullback B S hS g).obj (structureDerived Y) ≅
        structureDerived Y' :=
      (smallEtaleDerivedModulePullback B S hS g).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _) ≪≫
        Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackSingleUnitIso
          (smallEtaleRingedToposHom B S hS g) 0 ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm
    have hz : IsZero (R.obj (Z⟦q⟧)) :=
      IsZero.of_iso (Functor.map_isZero (shiftFunctor _ q) hRZ) ((R.commShiftIso q).app Z)
    have hk : e.hom ≫ k = e.hom ≫ 0 :=
      (adj.homEquiv _ _).injective (hz.eq_of_tgt _ _)
    exact (cancel_epi e.hom).1 hk
  obtain ⟨T₀, hT₀, ⟨i⟩⟩ := hY'
  have hTt := isTerminalChartOfIso T₀ i
  have hTa : IsAffineChart B S hS Y'.1 (chartOfIso B S hS T₀ i) := hT₀
  have hZ0 : IsZero Z :=
    isZero_of_forall_homFromUnit_eq_zero (X := Y'.1) (hX := Y'.2) _ hTt hTa Z hZ
      fun q k => hzero q k
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hZ0

end AlgebraicGeometry.Space

end
