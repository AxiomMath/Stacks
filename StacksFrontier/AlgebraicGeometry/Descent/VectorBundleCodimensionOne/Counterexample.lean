module

public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.PicardChart.Basic
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.Topology.OpensMapFinal

/-!
# The statement of Tag 0EXG as written is false

[Stacks, Tag 0EXG] asserts: let `f : X ⟶ S` be flat and proper with `𝒪_S = f_*𝒪_X`, let `S` be a
normal Noetherian scheme, and let `ℰ` be a finite locally free `𝒪_X`-module whose pullback to
`X ×_S Spec 𝒪_{S,s}` is free for every point `s ∈ S` of codimension one; then `ℰ` is the pullback
of a finite locally free `𝒪_S`-module. This file proves that statement false. Over a field `k`
the projective line `ℙ¹_k ⟶ Spec k` is flat and proper with `Γ(ℙ¹_k, 𝒪) = k`, the base is
normal and Noetherian and has no point of codimension one, and `𝒪(1)` is not pulled back from
`Spec k`. The corrected statement, which also asks for freeness at the generic points of the
irreducible components of `S` with no point of codimension one, is
`AlgebraicGeometry.VectorBundleCodimensionOne.exists_isFiniteLocallyFree_pullback_iso`.

## Main results

* `AlgebraicGeometry.VectorBundleCodimensionOne.isIso_c_projToSpecCoeff_one`: `𝒪_S = f_*𝒪_X`
  for `f : ℙ¹_k ⟶ Spec k`, from `Γ(ℙ¹_k, 𝒪) = k` (Tag 01XT).
* `AlgebraicGeometry.VectorBundleCodimensionOne.not_exists_pullback_iso_twistingSheaf_one`:
  `𝒪(1)` on `ℙ¹_k` is not the pullback of an `𝒪_{Spec k}`-module.
* `not_forall_exists_isFiniteLocallyFree_pullback_iso_of_codimOne` (same namespace): the
  negation of Tag 0EXG under exactly the source's hypotheses.

## References

* [Stacks Project, Tag 0EXG](https://stacks.math.columbia.edu/tag/0EXG)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
* [Stacks Project, Tag 0BXJ](https://stacks.math.columbia.edu/tag/0BXJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry.VectorBundleCodimensionOne

variable (k : Type u) [Field k]

/-- The spectrum of a field has a single point. -/
theorem subsingleton_spec_field : Subsingleton (Spec (CommRingCat.of k)) :=
  ⟨fun x y => PrimeSpectrum.ext ((@Ideal.eq_bot_of_prime _ _ x.asIdeal x.isPrime).trans
    (@Ideal.eq_bot_of_prime _ _ y.asIdeal y.isPrime).symm)⟩

/-- Every local ring of the spectrum of a field has Krull dimension zero. -/
theorem ringKrullDim_stalk_spec_field (s : Spec (CommRingCat.of k)) :
    ringKrullDim ((Spec (CommRingCat.of k)).presheaf.stalk s) = 0 := by
  have := subsingleton_spec_field k
  rw [ringKrullDim_stalk_eq_coheight]
  have h : Order.coheight s = 0 :=
    Order.coheight_eq_zero.mpr fun t _ => (Subsingleton.elim t s) ▸ le_rfl
  simp [h]

/-- **`𝒪_S = f_*𝒪_X` for the projective line over a field.** -/
theorem isIso_c_projToSpecCoeff_one :
    IsIso (projToSpecCoeff k 1).toLRSHom.toHom.c := by
  have hsub := subsingleton_spec_field k
  suffices h : ∀ V : (Spec (CommRingCat.of k)).Opens, IsIso ((projToSpecCoeff k 1).app V) by
    have : ∀ V, IsIso ((projToSpecCoeff k 1).toLRSHom.toHom.c.app V) := fun V => h V.unop
    exact NatIso.isIso_of_isIso_app _
  intro V
  by_cases hV : V = ⊤
  · subst hV
    have hb := Stacks.ProjectiveSpace.Cohomology.bijective_coeffToGlobalSections k 1
    have : IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (projToSpecCoeff k 1).app ⊤) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hb
    exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of k)).inv _
  · have hV' : V = ⊥ :=
      eq_bot_iff.mpr fun x hx => hV (eq_top_iff.mpr fun y _ => (Subsingleton.elim x y) ▸ hx)
    subst hV'
    have h1 : Subsingleton Γ(Spec (CommRingCat.of k), ⊥) := inferInstance
    have hpre : (projToSpecCoeff k 1) ⁻¹ᵁ (⊥ : (Spec (CommRingCat.of k)).Opens) = ⊥ := by simp
    have h2 : Subsingleton Γ(Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1),
        (projToSpecCoeff k 1) ⁻¹ᵁ ⊥) := by
      rw [hpre]
      infer_instance
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩

/-- `𝒪(1)` on the projective line over a field is finite locally free, being invertible. -/
theorem isFiniteLocallyFree_twistingSheaf_one :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (twistingSheaf (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1) 1 :
        (Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1)).Modules) := by
  have h := Stacks.PicardUFD.isInvertible_twistingSheaf k 1 1
  have h1 := (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one
    (Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1))
    (twistingSheaf (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1) 1)).mp h
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree (hM := h1) _ 1

/-- **`𝒪(1)` on the projective line over a field is not pulled back from the base**: there is
no `𝒪_{Spec k}`-module `M` with `f^*M ≅ 𝒪(1)`. -/
theorem not_exists_pullback_iso_twistingSheaf_one :
    ¬ ∃ M : (Spec (CommRingCat.of k)).Modules,
      Nonempty ((Scheme.Modules.pullback (projToSpecCoeff k 1)).obj M ≅
        twistingSheaf (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1) 1) := by
  rintro ⟨M, ⟨e⟩⟩
  let P := Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1)
  let S := Spec (CommRingCat.of k)
  let f := projToSpecCoeff k 1
  let L : P.Modules := twistingSheaf (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1) 1
  have hL : Stacks.Ample.IsInvertibleModule P L := Stacks.PicardUFD.isInvertible_twistingSheaf k 1 1
  have hfM : Stacks.Ample.IsInvertibleModule P ((Scheme.Modules.pullback f).obj M) :=
    Stacks.SheafOfModules.isInvertible_of_iso _ _ e.symm
  let p := Stacks.FiniteMorphismProjective.chartImmersion k k 1 (fun _ => 0)
  have hpf : p ≫ f = 𝟙 S := by
    rw [Stacks.FiniteMorphismProjective.chartImmersion_projToSpecCoeff, Algebra.algebraMap_self,
      CommRingCat.ofHom_id]
    exact Spec.map_id _
  let eM : (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback f).obj M) ≅ M :=
    (Scheme.Modules.pullbackComp p f).app M ≪≫ (Scheme.Modules.pullbackCongr hpf).app M ≪≫
      (Scheme.Modules.pullbackId S).app M
  have hM : Stacks.Ample.IsInvertibleModule S M := Stacks.SheafOfModules.isInvertible_of_iso _ _ eM
  have hPic := Stacks.ProjectiveSpace.PicardChart.subsingleton_picardGroup_spectrum k
  obtain ⟨eU⟩ := (S.picardClass_eq_iff M (Stacks.Ample.unitModule S) hM
    (Stacks.Ample.isInvertibleModule_unit S)).mp (Subsingleton.elim _ _)
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have : (Opens.map f.base).Final := Stacks.Topology.final_opensMap _
  let q : (Scheme.Modules.pullback f).obj (Stacks.Ample.unitModule S) ≅
      SheafOfModules.unit P.ringCatSheaf :=
    @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
      (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _)
  have htriv : P.picardClass L hL = 0 :=
    (P.picardClass_eq_zero_iff L hL).mpr ⟨e.symm ≪≫ (Scheme.Modules.pullback f).mapIso eU ≪≫ q⟩
  have h0 : Stacks.PicardUFD.twistPicardHom k 1 1 = Stacks.PicardUFD.twistPicardHom k 1 0 := by
    rwa [map_zero, Stacks.PicardUFD.twistPicardHom_apply]
  exact one_ne_zero (Stacks.PicardUFD.twistPicardHom_injective k 1 Nat.one_pos h0)

/-- **Tag 0EXG as written is false.** The statement of Tag 0EXG under exactly the source's
hypotheses — `f : X ⟶ S` flat and proper with `𝒪_S = f_*𝒪_X`, `S` normal and Noetherian, `ℰ`
finite locally free with free pullback to `X ×_S Spec 𝒪_{S,s}` at every point `s` of codimension
one — does not hold. The corrected statement is
`AlgebraicGeometry.VectorBundleCodimensionOne.exists_isFiniteLocallyFree_pullback_iso`. -/
theorem not_forall_exists_isFiniteLocallyFree_pullback_iso_of_codimOne :
    ¬ (∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f] [IsNoetherian S] [IsNormal S]
      (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
      (_hO : IsIso f.toLRSHom.toHom.c)
      (_hfree : ∀ s : S, ringKrullDim (S.presheaf.stalk s) = 1 →
        ∃ I : Type u, Nonempty
          ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecStalk s))).obj E ≅
            SheafOfModules.free I)),
      ∃ M : S.Modules, SheafOfModules.IsFiniteLocallyFree.{u, u, u} M ∧
        Nonempty ((Scheme.Modules.pullback f).obj M ≅ E)) := by
  intro h
  let k := ULift.{u} ℚ
  have : Flat (projToSpecCoeff k 1) := by
    have := Stacks.AlgebraicGeometry.ProjPolyChart.smooth_projToSpecCoeff k 1
    infer_instance
  have : IsProper (projToSpecCoeff k 1) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k 1
  have : IsNormal (Spec (CommRingCat.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  obtain ⟨M, -, e⟩ := @h _ _ (projToSpecCoeff k 1) _ _ _ _
    (twistingSheaf (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading k 1) 1)
    (isFiniteLocallyFree_twistingSheaf_one k)
    (isIso_c_projToSpecCoeff_one k) fun s hs =>
      absurd ((ringKrullDim_stalk_spec_field k s).symm.trans hs) zero_ne_one
  exact not_exists_pullback_iso_twistingSheaf_one k ⟨M, e⟩

end AlgebraicGeometry.VectorBundleCodimensionOne

end
