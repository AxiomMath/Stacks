module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.ChowRetract
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowLemmaGeneral
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.CoefficientBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeAffineBase
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.SmoothTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Comparison
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.QcqsSummandOfRestriction
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange

/-!
# The graph datum of the proof of [Stacks, Tag 0FYD]

Two inputs of the proof of the implication (2) ⇒ (1) of [Stacks, Tag 0FYD], both about the
Chow datum of [Stacks, Tag 0CSJ].

* `AlgebraicGeometry.CoherentConverse.exists_chowGraphDatum`: for `X` separated of finite type
  over a field `k` and `x ∈ X`, a Chow datum on `T = X ×_k ℙᵐ_k` read with the polynomial model
  `ℙᵐ_k = Proj k[T₀, …, Tₘ]` — the model on which the exceptional sequence of
  `ProjectiveSpacePerfect` lives. It is the Noetherian case of [Stacks, Tag 0CSJ]
  (`exists_chowDatum_isPseudoCoherent_of_isNoetherian`), carried along the comparison
  `Stacks.ProjectiveCohomology.projModelIso` of the two models of projective space.
* `AlgebraicGeometry.CoherentConverse.exists_isPerfect_retract_chowDatum`: if the first projection
  `p : T ⟶ X` is smooth, then `Ri_*𝒪_W` is a retract of `Lj^*E'` for some perfect `E'` on `T`.
  Here `i : W ⟶ q ⁻¹ᵁ V` is a perfect closed immersion by [Stacks, Tag 068D], `W ≅ U` being open
  in `X` and `q ⁻¹ᵁ V ⟶ X` smooth; so `Ri_*𝒪_W` is perfect by [Stacks, Tag 0G2E]; and
  [Stacks, Tag 09IQ] extends it, up to a direct summand, to a perfect complex on `T`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.CoherentConverse

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] MvPolynomial.gradedAlgebra

open DerivedChow Stacks.AlgebraicGeometry.ProjPolyChart

section Datum

variable {k : Type u} [Field k]

/-- The structure morphism of the polynomial model of projective space is that of the library's
model, read through `Stacks.ProjectiveCohomology.projModelIso`. -/
theorem projModelIso_hom_comp_over (m : ℕ) :
    (Stacks.ProjectiveCohomology.projModelIso k m).hom ≫
        (projectiveSpaceOver m (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
      projToSpecCoeff k m :=
  (Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism k m).trans
    (Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.projToSpecCoeff_eq_projModelToSpec
      k m).symm

/-- **The Chow datum of [Stacks, Tag 0CSJ] on `X ×_k Proj k[T₀, …, Tₘ]`.** For `f : X ⟶ Spec k`
separated and of finite type and `x ∈ X` there are an open `U ∋ x`, an `m`, an open `V` of
`Proj k[T₀, …, Tₘ]` and a closed subscheme `iZ : Z ⟶ X ×_k Proj k[T₀, …, Tₘ]` such that, with
`b`, `c` the two projections of `Z`, `b` is an isomorphism over `U`, `c` is a closed immersion
over `V`, and `b ⁻¹ᵁ U = c ⁻¹ᵁ V`. -/
theorem exists_chowGraphDatum {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (x : X) :
    ∃ (U : X.Opens) (m : ℕ) (V : (Proj (polyGrading k m)).Opens) (Z : Scheme.{u})
      (iZ : Z ⟶ pullback f (projToSpecCoeff k m)),
      x ∈ U ∧ IsClosedImmersion iZ ∧
        IsIso ((iZ ≫ pullback.fst f (projToSpecCoeff k m)) ∣_ U) ∧
        IsClosedImmersion ((iZ ≫ pullback.snd f (projToSpecCoeff k m)) ∣_ V) ∧
        (iZ ≫ pullback.fst f (projToSpecCoeff k m)) ⁻¹ᵁ U =
          (iZ ≫ pullback.snd f (projToSpecCoeff k m)) ⁻¹ᵁ V := by
  obtain ⟨U, m, V, Z, iZ, -, -, hxU, hiZ, -, hU, -, hV, hpre, -⟩ :=
    exists_chowDatum_isPseudoCoherent_of_isNoetherian f x
  let Θ := Stacks.ProjectiveCohomology.projModelIso k m
  let π₀ := projectiveSpaceOver m (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)
  let φ : pullback f (projToSpecCoeff k m) ⟶ pullback f π₀ :=
    pullback.map _ _ _ _ (𝟙 _) Θ.hom (𝟙 _) (by simp) (by simp [Θ, π₀, projModelIso_hom_comp_over])
  have h1 : inv φ ≫ pullback.fst f (projToSpecCoeff k m) = pullback.fst f π₀ := by
    rw [IsIso.inv_comp_eq]; exact ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm
  have h2 : inv φ ≫ pullback.snd f (projToSpecCoeff k m) ≫ Θ.hom = pullback.snd f π₀ := by
    rw [IsIso.inv_comp_eq]; exact (pullback.lift_snd _ _ _).symm
  have hc : (iZ ≫ inv φ ≫ pullback.snd f (projToSpecCoeff k m)) ≫ Θ.hom =
      iZ ≫ pullback.snd f π₀ := by
    rw [Category.assoc, Category.assoc, h2]
  have sq : IsPullback (𝟙 Z) (iZ ≫ inv φ ≫ pullback.snd f (projToSpecCoeff k m))
      (iZ ≫ pullback.snd f π₀) Θ.hom :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hc]⟩
  refine ⟨U, m, Θ.hom ⁻¹ᵁ V, Z, iZ ≫ inv φ, hxU, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, h1]; exact hU
  · rw [Category.assoc]
    exact of_isPullback_morphismRestrict (@IsClosedImmersion) sq V hV
  · rw [← Scheme.Hom.comp_preimage]
    simp only [Category.assoc]
    rw [h2, h1]
    exact hpre

end Datum

section Retract

variable {X P T Z : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ P) (iZ : Z ⟶ T) (U : X.Opens) (V : P.Opens)
  (hb : IsIso ((iZ ≫ p) ∣_ U)) (hW : (iZ ≫ p) ⁻¹ᵁ U = (iZ ≫ q) ⁻¹ᵁ V)

/-- `Ri_*𝒪_W` is perfect for a perfect closed immersion `i`, in the spelling of
[Stacks, Tag 0CSK]. -/
theorem isPerfect_derivedPushforward_structureSheafSingle {W Y : Scheme.{u}} (i : W ⟶ Y)
    [IsClosedImmersion i] [Perfect i] :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      ((derivedPushforward (ofScheme i)).obj (structureSheafSingle W)) := by
  have hP0 : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit W.ringCatSheaf))) :=
    isPerfect_pushforward_structureSheaf i
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (derivedPushforwardSingleIsoOfIsAffineHom i (SheafOfModules.unit W.ringCatSheaf)).symm hP0

include U hb hW in
/-- **`Ri_*𝒪_W` extends to a perfect complex on `T` up to a direct summand.** In a Chow datum
whose first projection `p : T ⟶ X` is smooth, with `T` quasi-compact and quasi-separated and
`q ⁻¹ᵁ V` quasi-compact, there is a perfect `E'` on `T` with `Ri_*𝒪_W` a retract of `Lj^*E'`,
`j : q ⁻¹ᵁ V ⟶ T` the inclusion. -/
theorem exists_isPerfect_retract_chowDatum [IsClosedImmersion iZ] [Smooth p] [CompactSpace T]
    [QuasiSeparatedSpace T] (hV : IsCompact (q ⁻¹ᵁ V : Set T)) :
    ∃ E' : DerivedCategory T.Modules,
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := T.toRingedSpace) E' ∧
      Nonempty (Retract ((derivedPushforward (ofScheme (iZ ∣_ (q ⁻¹ᵁ V)))).obj
          (structureSheafSingle (iZ ⁻¹ᵁ (q ⁻¹ᵁ V)).toScheme))
        ((derivedPullback (ofScheme (q ⁻¹ᵁ V).ι)).obj E')) := by
  have : IsClosedImmersion (iZ ∣_ (q ⁻¹ᵁ V)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have := isIso_chowDatumGraphIso p q iZ U V hb hW
  have : Perfect U.ι := inferInstance
  have : Perfect (chowDatumGraphIso p q iZ U V hW) := inferInstance
  have : Perfect (chowDatumGraphIso p q iZ U V hW ≫ U.ι) := perfect_comp _ _
  have : Smooth ((q ⁻¹ᵁ V).ι ≫ p) := inferInstance
  have : Perfect (iZ ∣_ (q ⁻¹ᵁ V)) :=
    perfect_of_comp_eq_of_smooth (iZ ∣_ (q ⁻¹ᵁ V)) ((q ⁻¹ᵁ V).ι ≫ p)
      (p := chowDatumGraphIso p q iZ U V hW ≫ U.ι) (chowDatumGraphIso_comp_ι p q iZ U V hW).symm
  have hP := isPerfect_derivedPushforward_structureSheafSingle (iZ ∣_ (q ⁻¹ᵁ V))
  obtain ⟨R, hR, ⟨ρ⟩⟩ := Stacks.DerivedQCoh.OpenLift.exists_isPerfect_retract_derivedRestrict T
    (q ⁻¹ᵁ V) hV (hU' := HasDerivedCategory.standard _) (hX := HasDerivedCategory.standard _) _ hP
  exact ⟨R, hR, ⟨ρ.trans (Retract.ofIso
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback (q ⁻¹ᵁ V).ι).app R))⟩⟩

end Retract

end AlgebraicGeometry.CoherentConverse

end
