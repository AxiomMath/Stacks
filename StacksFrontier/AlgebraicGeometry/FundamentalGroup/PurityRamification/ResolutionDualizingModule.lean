module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.FlatBaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompositionProper
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.UpperShriekStructureSheafTrivial
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.MinimalResolution

/-!
# The dualizing module of the resolution, by base change from a model

This is the third paragraph of the proof of [Stacks, Tag 0EA3]: "since `ω_{X/Y} = 𝒪_X` we see
that `ω_{X'/Y} = b^! f^! 𝒪_Y = b^! 𝒪_X`; returning to `W ⟶ Spec(𝒪_{X, x})` we see that
`ω_W = 𝒪_W(E|_W)`". Here the identification of `ω_W` is made with the pullback of
`ω_{X'/Y} = H⁰((b ≫ h)^!𝒪)`:

  `ω_W = H^{-2}(g^×(𝒪_B[2])) ≅ H⁰(g^×𝒪_B) ≅ H⁰(L(π')^* b^×𝒪_U) ≅ (π')^* H⁰(b^×(h^!𝒪))`
  `   ≅ (π')^* H⁰((b ≫ h)^!𝒪)`,

using flat base change along `π : Spec B ⟶ U` ([Stacks, Tag 0E9U], `Stacks.Duality.
isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat_right`), `h^!𝒪 ≅ 𝒪_U`
(`Stacks.PurityRamification.nonempty_upperShriek_derivedStructureSheaf_iso`), the composition
`(b ≫ h)^! = b^× ∘ h^!` for `b` proper ([Stacks, Tag 0ATX],
`Stacks.Duality.CompCompactification.upperShriekCompProperTwistedObjIso`) and the exactness of
flat pullback. The dualizing module of `B` is `B` itself, `B` being Gorenstein.

## Main results

* `Stacks.PurityRamification.nonempty_relativeDualizingModule_iso_pullback_upperShriekHomology`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits DerivedCategory Stacks.Duality
open AlgebraicGeometry.DualizingDivisor

universe u

namespace Stacks.PurityRamification

/-- **`ω_W ≅ (π')^* H⁰((b ≫ h)^!𝒪_{Spec A})`.** Let `A` be a regular local ring, `h : U ⟶ Spec A`
locally of finite type with `U` affine and Cohen–Macaulay and `h` étale at the points of
dimension at most one, `π : Spec B ⟶ U` flat with `B` local Noetherian, `b : X' ⟶ U` proper, and
`g : W ⟶ Spec B` the base change of `b` along `π`, with `W` of dimension two. Then the relative
dualizing module `ω_W = H^{-2}(g^×(B[2]))` of `g` is the pullback along `π' : W ⟶ X'` of
`H⁰((b ≫ h)^!𝒪)`, for any compactification of `b ≫ h`. -/
theorem nonempty_relativeDualizingModule_iso_pullback_upperShriekHomology {A : Type u}
    [CommRing A] [IsRegularLocalRing A] {U : Scheme.{u}} [IsAffine U] (h : U ⟶ Spec (.of A))
    [LocallyOfFiniteType h] (hCM : AlgebraicGeometry.IsCohenMacaulay U)
    (het : ∀ z : U, ringKrullDim (U.presheaf.stalk z) ≤ 1 → EtaleAt h z)
    {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (π : Spec (.of B) ⟶ U)
    [Flat π] {X' : Scheme.{u}} (b : X' ⟶ U) [IsProper b] {W : Scheme.{u}}
    (g : W ⟶ Spec (.of B)) (π' : W ⟶ X') (sq : IsPullback π' g b π)
    (hdimW : topologicalKrullDim W = 2) (c : CompactificationOf (Over.mk (b ≫ h))) :
    haveI : IsProper g := MorphismProperty.of_isPullback sq inferInstance
    haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace g
    haveI : QuasiSeparatedSpace W := quasiSeparatedSpace_of_quasiSeparated g
    Nonempty (relativeDualizingModule g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
        ((derivedTilde (CommRingCat.of B)).obj
          ((singleFunctor (ModuleCat.{u} B) (-2)).obj (ModuleCat.of B B))) ≅
      (Scheme.Modules.pullback π').obj
        (ClosedOpenProperFactorization.upperShriekHomology (ftsHomToBase (b ≫ h)) c 0)) := by
  have : IsProper g := MorphismProperty.of_isPullback sq inferInstance
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace W := quasiSeparatedSpace_of_quasiSeparated g
  have : Flat π' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian h
  have : IsNoetherian U := ⟨⟩
  have : IsNoetherian (Spec (.of B)) := ⟨⟩
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace b
  have : QuasiSeparatedSpace X' := quasiSeparatedSpace_of_quasiSeparated b
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward g
  let := isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward b
  -- `h^!𝒪 ≅ 𝒪_U`
  obtain ⟨cU, -⟩ := exists_quasiCompact_compactificationOf_of_isQuasiAffine h
  obtain ⟨eU⟩ := nonempty_upperShriek_derivedStructureSheaf_iso h hCM het cU
  -- the composite `b ≫ h` as a morphism of `FTS (Spec A)`
  let F := ftsHomToBase h
  let bF : FTS.mk (b ≫ h) ⟶ FTS.mk h := MorphismProperty.Over.homMk b rfl
  have : IsProper bF.left := ‹IsProper b›
  have hO : DerivedCategoryB.IsBoundedBelow
      (DerivedPushforward.derivedStructureSheaf (Spec (.of A))).obj :=
    isBoundedBelow_unitQC _
  let Kb := (twistedInverseImage b (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).obj
    (unitQC U)
  let e₂ : (upperShriek (bF ≫ F) c).obj
      (DerivedPushforward.derivedStructureSheaf (Spec (.of A))) ≅ Kb :=
    CompCompactification.upperShriekCompProperTwistedObjIso bF F cU c _ hO ≪≫
      (twistedInverseImage b _).mapIso (eU ≪≫ ObjectProperty.isoMk _ (Iso.refl _))
  -- flat base change along `π`
  have fB := isIso_twistedInverseImageBaseChangeMap_app_of_isProper_of_flat_right sq (unitQC U)
    (isBoundedBelow_unitQC _)
  let Kg := (twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
    (unitQC (Spec (.of B)))
  let e₃ : (quasiCoherentDerivedPullback' π').obj Kb ≅ Kg :=
    @asIso _ _ _ _ _ fB ≪≫ (twistedInverseImage g _).mapIso (quasiCoherentDerivedPullbackUnitIso π)
  -- `ω_W ≅ H⁰(g^×𝒪_B)`, as in `AlgebraicGeometry.DualizingDivisor`
  have hidx : (-(ENat.toNat ((topologicalKrullDim W).getD 0) : ℤ)) = -2 := by
    rw [hdimW]
    rfl
  let := (twistedInverseImageAdjunction g
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).rightAdjointCommShift ℤ
  let eΩ : (derivedTilde (CommRingCat.of B)).obj
      ((singleFunctor (ModuleCat.{u} B) (-2)).obj (ModuleCat.of B B)) ≅
      (unitQC (Spec (.of B)))⟦(2 : ℤ)⟧ :=
    (unitQCShiftIso B 2).symm
  let eH : relativeDualizingModule g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
      ((derivedTilde (CommRingCat.of B)).obj
        ((singleFunctor (ModuleCat.{u} B) (-2)).obj (ModuleCat.of B B))) ≅
      (homologyFunctor W.Modules 0).obj Kg.obj :=
    eqToIso (by rw [relativeDualizingModule, hidx]; rfl) ≪≫
      (homologyFunctor W.Modules (-2)).mapIso ((ObjectProperty.ι _).mapIso
        ((twistedInverseImage g _).mapIso eΩ ≪≫
          ((twistedInverseImage g _).commShiftIso (2 : ℤ)).app _) ≪≫
        ((ObjectProperty.ι _).commShiftIso (2 : ℤ)).app Kg) ≪≫
      (derivedCategoryHomologyShiftNatIso W.Modules 2 (-2) 0 (by norm_num)).app Kg.obj
  exact ⟨eH ≪≫ (homologyFunctor W.Modules 0).mapIso ((ObjectProperty.ι _).mapIso e₃.symm) ≪≫
    homologyQuasiCoherentDerivedPullbackIso π' Kb 0 ≪≫
    (Scheme.Modules.pullback π').mapIso
      ((homologyFunctor X'.Modules 0).mapIso ((ObjectProperty.ι _).mapIso e₂.symm))⟩

end Stacks.PurityRamification

end
