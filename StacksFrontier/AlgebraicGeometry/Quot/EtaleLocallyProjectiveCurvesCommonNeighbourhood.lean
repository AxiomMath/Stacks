module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocallyProjectiveCurvesCartierSubspace

/-!
# A common étale neighbourhood through a residue-field point

Let `S₀` be a scheme of the big fppf site and `s ∈ S₀`. An étale morphism `φ : U ⟶ S₀` of the
site with a point `u` over `s` at which the residue field map is an isomorphism (an elementary
étale neighbourhood, Stacks 02LE) carries a lift `Spec κ(s) ⟶ U` of the residue-field point of
`S₀` through `u`. Finitely many such lifts are lifts of one étale neighbourhood: the fibre product
over `S₀` of the neighbourhoods, through the induced morphism from `Spec κ(s)`.

This is the step of the proof that families of curves are étale locally schemes (Stacks 0E6F)
that puts the finitely many local divisors, each produced over its own elementary étale
neighbourhood, over one étale neighbourhood, and presents the fibre of the family there over
`Spec κ(s)` itself.

## Main results

* `AlgebraicGeometry.Space.exists_lift_residueFieldMap_of_isIso_residueFieldMap`: the lift
  `Spec κ(s) ⟶ U` through an elementary étale neighbourhood.
* `AlgebraicGeometry.Space.exists_etale_common_lift`: finitely many lifts factor through one
  étale neighbourhood.

## References

* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- **The residue-field point through an elementary étale neighbourhood.** If `φ : U ⟶ S₀` maps
`u` to `s` and induces an isomorphism of residue fields at `u`, the residue-field point
`Spec κ(s) ⟶ S₀` lifts through `φ` to a morphism `Spec κ(s) ⟶ U` of the site whose image is
`u`. -/
theorem exists_lift_residueFieldMap_of_isIso_residueFieldMap {U S₀ : BigFppfOver B S hS}
    (φ : U ⟶ S₀) (u : (𝒯).obj U) (s : (𝒯).obj S₀) (hu : (𝒯).map φ u = s)
    (hres : IsIso (((𝒯).map φ).residueFieldMap u)) :
    ∃ σ : residueFieldObject B S hS S₀ s (B.residueField_spec_contains S₀.left.property s) ⟶ U,
      σ ≫ φ = residueFieldMap B S hS S₀ s (B.residueField_spec_contains S₀.left.property s) ∧
      ∀ y, (𝒯).map σ y = u := by
  subst hu
  have : IsIso (φ.left.1.residueFieldMap u) := hres
  have := isIso_residueFieldObjectMap B S hS U S₀ φ u
  refine ⟨inv (residueFieldObjectMap B S hS U S₀ φ u) ≫
    residueFieldMap B S hS U u (B.residueField_spec_contains U.left.property u), ?_, ?_⟩
  · rw [Category.assoc, ← residueFieldObjectMap_comp, IsIso.inv_hom_id_assoc]
    rfl
  · intro y
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _

/-- **Finitely many lifts of a morphism factor through one étale neighbourhood.** Let
`r₀ : F ⟶ S₀` be a morphism of the site and, for `i` in a finite set `I`, let `φ i : U i ⟶ S₀`
be étale with a lift `σ i : F ⟶ U i` of `r₀`. Then there are an étale `φT : T ⟶ S₀` with a lift
`σT : F ⟶ T` of `r₀` and, for each `i ∈ I`, an étale `ψ : T ⟶ U i` over `S₀` with
`σT ≫ ψ = σ i`. -/
theorem exists_etale_common_lift {ι : Type*} {S₀ F : BigFppfOver B S hS}
    (r₀ : F ⟶ S₀) (U : ι → BigFppfOver B S hS) (φ : ∀ i, U i ⟶ S₀)
    (hφ : ∀ i, Etale ((𝒯).map (φ i))) (σ : ∀ i, F ⟶ U i) (hσ : ∀ i, σ i ≫ φ i = r₀)
    (I : Finset ι) :
    ∃ (T : BigFppfOver B S hS) (φT : T ⟶ S₀) (σT : F ⟶ T),
      Etale ((𝒯).map φT) ∧ σT ≫ φT = r₀ ∧
      ∀ i ∈ I, ∃ ψ : T ⟶ U i, Etale ((𝒯).map ψ) ∧ ψ ≫ φ i = φT ∧ σT ≫ ψ = σ i := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨S₀, 𝟙 S₀, r₀, ?_, Category.comp_id _, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  | insert a I ha ih =>
    obtain ⟨T, φT, σT, hφT, hσT, hψ⟩ := ih
    have sq := (IsPullback.of_hasPullback φT (φ a)).map (𝒯)
    have hfst : Etale ((𝒯).map (pullback.fst φT (φ a))) :=
      MorphismProperty.of_isPullback sq.flip (hφ a)
    have hsnd : Etale ((𝒯).map (pullback.snd φT (φ a))) :=
      MorphismProperty.of_isPullback sq hφT
    refine ⟨pullback φT (φ a), pullback.fst φT (φ a) ≫ φT,
      pullback.lift σT (σ a) (by rw [hσT, hσ a]), ?_, ?_, ?_⟩
    · rw [Functor.map_comp]
      infer_instance
    · rw [pullback.lift_fst_assoc, hσT]
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact ⟨pullback.snd φT (φ i), hsnd, pullback.condition.symm, pullback.lift_snd _ _ _⟩
      · obtain ⟨ψ, hψe, hψφ, hψσ⟩ := hψ i hi
        refine ⟨pullback.fst φT (φ a) ≫ ψ, ?_, ?_, ?_⟩
        · rw [Functor.map_comp]
          infer_instance
        · rw [Category.assoc, hψφ]
        · rw [pullback.lift_fst_assoc, hψσ]

end AlgebraicGeometry.Space

end
