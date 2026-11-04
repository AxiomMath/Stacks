module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FibreProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle
public import StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceZeroHodge

/-!
# The projective bundle over an open where the module is free

Let `ℰ` be a module on a scheme `X`, finite locally free of constant rank `r + 1`, and
`p : P = 𝐏(ℰ) ⟶ X` its projective bundle (`Stacks.Chow.bundle`), with twist `𝒪_P(1)`
(`Stacks.Chow.bundleTwist`). Let `s : X ⟶ Spec k` be a morphism to the spectrum of a ring. If
`ℰ` is free on an open `U ⊆ X` and `V ⊆ U` is open, then `p⁻¹V = ℙʳ_k ×_{Spec k} V`, by a
cartesian square along which `𝒪(1)` on `ℙʳ_k = Proj k[T₀, …, T_r]` pulls back to the
restriction of `𝒪_P(1)` to `p⁻¹V`.

The affine opens contained in an open on which `ℰ` is free form a basis of the topology of `X`.

## Main results

* `Stacks.HodgeWeil.exists_isPullback_freeProjectiveBundle`: `𝐏(𝒪_V^{r+1}) = ℙʳ_k ×_k V` for
  any `V ⟶ Spec k`, with `𝒪(1)` pulling back to the tautological twist.
* `Stacks.HodgeWeil.exists_isPullback_bundleProj_restrict`: `p⁻¹V = ℙʳ_k ×_k V` for `V` inside
  an open on which `ℰ` is free, with `𝒪(1)` pulling back to `𝒪_P(1)|_{p⁻¹V}` in `Pic(p⁻¹V)`.
* `Stacks.HodgeWeil.isBasis_affine_le_restrict_free`: the affine opens contained in an open on
  which `ℰ` is free form a basis of the topology of `X`.

## References

* [Stacks Project, Tag 0FMT](https://stacks.math.columbia.edu/tag/0FMT)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RelativeProj (projectiveBundle projectiveBundleToBase tautologicalDatumTwist
  isInvertible_tautologicalDatumTwist)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.HodgeWeil

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff polyGrading)
open Stacks.AlgebraicGeometry.ProjectiveSpaceHodge (projectiveSpace)
open Stacks.SheafOfModules (pullbackPicardHom)

/-! ### The projective bundle of a free module -/

section FreeModel

variable (k : Type u) [CommRing k] {V : Scheme.{u}} (t : V ⟶ Spec (CommRingCat.of k)) (r : ℕ)

/-- **The projective bundle of `𝒪_V^{r+1}` is `ℙʳ_k ×_{Spec k} V`** for any morphism
`t : V ⟶ Spec k`, with `𝒪(1)` on `ℙʳ_k` pulling back to the tautological twist. -/
theorem exists_isPullback_freeProjectiveBundle :
    ∃ pr : (Stacks.SymGraded.freeProjectiveBundle (X := V) r).scheme ⟶ projectiveSpace k r,
      IsPullback pr (Stacks.SymGraded.freeProjectiveBundle (X := V) r).toBase
          (projToSpecCoeff k r) t ∧
        Nonempty ((Scheme.Modules.pullback pr).obj
            (Stacks.ProjectiveBundleDeRham.projectiveTwistOne k r) ≅
          Stacks.ProjectiveBundleSplitting.tautologicalTwist
            (Stacks.SymGraded.freeModule (X := V) (Stacks.SymGraded.coordIndex.{u} r))
            (Stacks.SymGraded.isQuasicoherentPieces_free (X := V)
              (Stacks.SymGraded.coordIndex.{u} r))) := by
  have sqA := Stacks.ProjectiveCohomology.isPullback_terminal_from_projModel k r
  let pr := sqA.lift ((Stacks.SymGraded.freeProjectiveBundle (X := V) r).toBase ≫ t)
    (Stacks.SymGraded.projectiveBundleToIntegralModel (X := V) r) (terminal.hom_ext _ _)
  have hfst : pr ≫ Stacks.ProjectiveCohomology.projModelToSpec k r =
      (Stacks.SymGraded.freeProjectiveBundle (X := V) r).toBase ≫ t := sqA.lift_fst _ _ _
  have hsnd : pr ≫ Stacks.ProjectiveCohomology.projModelMap r
      (Stacks.ProjectiveCohomology.fromULiftInt k) =
      Stacks.SymGraded.projectiveBundleToIntegralModel (X := V) r := sqA.lift_snd _ _ _
  have hcoeff := Stacks.ProjectiveBundleFibre.projToSpecCoeff_eq_projModelToSpec k r
  refine ⟨pr, ?_, ?_⟩
  · refine IsPullback.of_right (h₁₂ := Stacks.ProjectiveCohomology.projModelMap r
      (Stacks.ProjectiveCohomology.fromULiftInt k))
      (v₁₃ := terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} r))
      (h₂₂ := terminal.from (Spec (CommRingCat.of k))) ?_ ?_ ?_
    · rw [hsnd, show t ≫ terminal.from (Spec (CommRingCat.of k)) = terminal.from V from
        terminal.hom_ext _ _]
      exact Stacks.Chow.FreeTower.isPullback_projectiveBundleToIntegralModel V r
    · rw [hcoeff, hfst]
    · rw [hcoeff]
      exact sqA.flip
  · obtain ⟨β, -⟩ := Stacks.Chow.FreeTower.exists_tautologicalTwist_iso_pullback V r
    obtain ⟨γ⟩ := Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport k r 1
    exact ⟨(Scheme.Modules.pullback pr).mapIso γ.symm ≪≫
      (Scheme.Modules.pullbackComp pr _).app _ ≪≫ (Scheme.Modules.pullbackCongr hsnd).app _ ≪≫
      β.symm⟩

end FreeModel

/-! ### Comparing the two presentations of the projective bundle -/

section TwistComparison

/-- Pulling back the class of `L` along `f` gives the class of any module isomorphic to the
pullback of `L`. -/
private theorem pullbackPicardHom_picardClassOf_eq_of_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    {L : Y.Modules} {L' : X.Modules}
    {hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L}
    {hL' : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'}
    (e : (Scheme.Modules.pullback f).obj L ≅ L') :
    pullbackPicardHom f (Stacks.WeilCohomology.picardClassOf Y L hL) =
      Stacks.WeilCohomology.picardClassOf X L' hL' :=
  (Stacks.ProjectiveBundleFibre.pullbackPicardHom_picardClassOf f L hL).trans
    (Stacks.WeilCohomology.picardClassOf_eq_of_iso _ _ _ _ _ e)

/-- A morphism `a` into `Stacks.RelativeProj.projectiveBundle X E'` lying over a morphism `b` into
`𝐏(E)` through the base-change morphism pulls the tautological twist of `E'` back to the class
that `b` pulls `𝒪_{𝐏(E)}(1)` back to. -/
private theorem pullbackPicardHom_tautologicalDatumTwist_eq_of_comp_eq {X Y W : Scheme.{u}}
    (g : X ⟶ Y) (E : Y.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [E.IsQuasicoherent] (E' : X.Modules) [E'.IsQuasicoherent]
    (hE : E' ≅ (Scheme.Modules.pullback g).obj E) (a : W ⟶ projectiveBundle X E')
    (b : W ⟶ Stacks.Chow.bundle E)
    (h : a ≫ Stacks.RelativeProj.projectiveBundleBaseChange g E E' hE =
      b ≫ (Stacks.RelativeProj.bundlePresentationIso E).hom) :
    pullbackPicardHom a (Stacks.WeilCohomology.picardClassOf _ (tautologicalDatumTwist E')
        (isInvertible_tautologicalDatumTwist E')) =
      pullbackPicardHom b (Stacks.WeilCohomology.picardClassOf _ (Stacks.Chow.bundleTwist E)
        (Stacks.Chow.isInvertible_bundleTwist E)) := by
  rw [← pullbackPicardHom_picardClassOf_eq_of_iso _
      (hL := isInvertible_tautologicalDatumTwist E)
      (Stacks.RelativeProj.tautologicalDatumTwistBaseChangeIso g E E' hE),
    ← Stacks.SheafOfModules.pullbackPicardHom_comp_apply, h]
  exact (Stacks.SheafOfModules.pullbackPicardHom_comp_apply _ _ _).trans
    (congrArg (pullbackPicardHom b) (pullbackPicardHom_picardClassOf_eq_of_iso
    (Stacks.RelativeProj.bundlePresentationIso E).hom (L := tautologicalDatumTwist E)
    ((Scheme.Modules.pullbackComp (Stacks.RelativeProj.bundlePresentationIso E).hom
      (Stacks.RelativeProj.bundlePresentationIso E).inv).app _ ≪≫
      (Scheme.Modules.pullbackCongr
        (Stacks.RelativeProj.bundlePresentationIso E).hom_inv_id).app _ ≪≫
      (Scheme.Modules.pullbackId _).app _)))

/-- Over an open `V ⊆ X`, the restriction of `p : 𝐏(ℰ) ⟶ X` to `p⁻¹V` is the base change of
`Stacks.RelativeProj.projectiveBundleToBase` along `V ⟶ X`, through the presentation
comparison. -/
private theorem isPullback_bundleProj_restrict_projectiveBundleToBase {X : Scheme.{u}}
    (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] [E.IsQuasicoherent]
    (V : X.Opens) :
    IsPullback (Stacks.Chow.bundleProj E ∣_ V)
      ((Stacks.Chow.bundleProj E ⁻¹ᵁ V).ι ≫ (Stacks.RelativeProj.bundlePresentationIso E).hom)
      V.ι (projectiveBundleToBase X E) :=
  (isPullback_morphismRestrict (Stacks.Chow.bundleProj E) V).of_iso (Iso.refl _) (Iso.refl _)
    (Stacks.RelativeProj.bundlePresentationIso E) (Iso.refl _) (by simp) (by simp) (by simp)
    (by
      rw [Iso.refl_hom, Category.comp_id]
      exact (Stacks.RelativeProj.bundlePresentationIso_hom_comp_toBase E).symm)

end TwistComparison

/-! ### The projective bundle over an open where the module is free -/

section Restrict

variable {k : Type u} [CommRing k] {X : Scheme.{u}} (s : X ⟶ Spec (CommRingCat.of k))
  (E : X.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)]

/-- **Over an open inside an open where `ℰ` is free, the projective bundle is projective space
over the open, with its twist.** For `ℰ` finite locally free of rank `r + 1`, free on `U`, and
an open `V ⊆ U`, there is a cartesian square `p⁻¹V ⟶ ℙʳ_k` over `V ⟶ X ⟶ Spec k` along which
`𝒪(1)` pulls back to the restriction of `𝒪_P(1)` to `p⁻¹V` in the Picard group. -/
theorem exists_isPullback_bundleProj_restrict (U : X.Opens)
    (hU : Nonempty (E.restrict U.ι ≅
      SheafOfModules.free.{u} (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1)))))
    (V : X.Opens) (hVU : V ≤ U) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (r + 1)
    ∃ pr₁ : (Stacks.Chow.bundleProj E ⁻¹ᵁ V).toScheme ⟶ projectiveSpace k r,
      IsPullback pr₁ (Stacks.Chow.bundleProj E ∣_ V) (projToSpecCoeff k r) (V.ι ≫ s) ∧
        pullbackPicardHom pr₁ (Stacks.WeilCohomology.picardClassOf _
            (Stacks.ProjectiveBundleDeRham.projectiveTwistOne k r)
            (Stacks.ProjectiveBundleDeRham.isInvertible_projectiveTwistOne k r)) =
          pullbackPicardHom (Stacks.Chow.bundleProj E ⁻¹ᵁ V).ι
            (Stacks.WeilCohomology.picardClassOf _ (Stacks.Chow.bundleTwist E)
              (Stacks.Chow.isInvertible_bundleTwist E)) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (r + 1)
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let hF := (Stacks.ProjectiveBundleFibre.nonempty_iso_pullback_of_restrict_free E _ U hU.some
    V.ι (by rwa [V.range_ι])).some
  let F := SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin (r + 1)))
  have : F.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free _
  have sqBC := Stacks.RelativeProj.isPullback_projectiveBundleToBase_baseChange V.ι E F hF
  have sqR := isPullback_bundleProj_restrict_projectiveBundleToBase E V
  let Φ := sqR.isoIsPullback _ _ sqBC
  have hΦsnd : Φ.hom ≫ Stacks.RelativeProj.projectiveBundleBaseChange V.ι E F hF =
      (Stacks.Chow.bundleProj E ⁻¹ᵁ V).ι ≫ (Stacks.RelativeProj.bundlePresentationIso E).hom :=
    sqR.isoIsPullback_hom_snd _ _ sqBC
  have hfree := exists_isPullback_freeProjectiveBundle k (V.ι ≫ s) r
  let pr := hfree.choose
  have hpr : IsPullback pr (Stacks.SymGraded.freeProjectiveBundle (X := V.toScheme) r).toBase
      (projToSpecCoeff k r) (V.ι ≫ s) := hfree.choose_spec.1
  let τ := hfree.choose_spec.2.some
  let ψ : (Stacks.Chow.bundleProj E ⁻¹ᵁ V).toScheme ≅
      (Stacks.SymGraded.freeProjectiveBundle (X := V.toScheme) r).scheme :=
    Φ ≪≫ (Stacks.RelativeProj.bundlePresentationIso F).symm
  have hψ : ψ.hom ≫ (Stacks.SymGraded.freeProjectiveBundle (X := V.toScheme) r).toBase =
      Stacks.Chow.bundleProj E ∣_ V :=
    (Category.assoc _ _ _).trans ((congrArg (fun g => Φ.hom ≫ g)
      (Stacks.RelativeProj.bundlePresentationIso_inv_comp_toBase F)).trans
        (sqR.isoIsPullback_hom_fst _ _ sqBC))
  refine ⟨ψ.hom ≫ pr, ?_, ?_⟩
  · exact hpr.of_iso ψ.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
      (by simp [← hψ]) (by simp) (by simp)
  · calc pullbackPicardHom (ψ.hom ≫ pr) (Stacks.WeilCohomology.picardClassOf _
            (Stacks.ProjectiveBundleDeRham.projectiveTwistOne k r)
            (Stacks.ProjectiveBundleDeRham.isInvertible_projectiveTwistOne k r))
        = pullbackPicardHom Φ.hom (Stacks.WeilCohomology.picardClassOf _
            (tautologicalDatumTwist F) (isInvertible_tautologicalDatumTwist F)) := by
          rw [show ψ.hom ≫ pr = Φ.hom ≫ _ ≫ pr from Category.assoc _ _ _,
            Stacks.SheafOfModules.pullbackPicardHom_comp_apply]
          exact congrArg _
            (pullbackPicardHom_picardClassOf_eq_of_iso _
              (((Scheme.Modules.pullbackComp _ pr).app _).symm ≪≫
                (Scheme.Modules.pullback (Stacks.RelativeProj.bundlePresentationIso F).inv).mapIso
                  τ))
      _ = _ := pullbackPicardHom_tautologicalDatumTwist_eq_of_comp_eq V.ι E F hF Φ.hom _ hΦsnd

end Restrict

/-! ### Opens on which the module is free -/

section Basis

variable {X : Scheme.{u}} (E : X.Modules)

/-- **The affine opens contained in an open on which `ℰ` is free form a basis of the topology
of `X`**, for `ℰ` finite locally free of rank `r`. -/
theorem isBasis_affine_le_restrict_free (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    Opens.IsBasis {V : X.Opens | IsAffineOpen V ∧ ∃ U : X.Opens, V ≤ U ∧
      Nonempty (E.restrict U.ι ≅
        SheafOfModules.free.{u} (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))} := by
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨U, hxU, hU⟩ := Stacks.ProjectiveBundle.exists_restrict_free E r x
  obtain ⟨V, hV, hxV, hVW⟩ := Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens X)
    (show x ∈ W ⊓ U from ⟨hx, hxU⟩)
  exact ⟨V, ⟨hV, U, hVW.trans inf_le_right, hU⟩, hxV, hVW.trans inf_le_left⟩

end Basis

end Stacks.HodgeWeil
