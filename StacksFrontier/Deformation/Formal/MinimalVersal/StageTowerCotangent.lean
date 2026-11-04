module

public import StacksFrontier.Deformation.Formal.MinimalVersal.StageTowerBase

/-!
# Boundedness of the cotangent spaces of the stage tower

For a versal formal object the arrows into the minimal stages are surjective on bases, so the
cotangent spaces of the stage tower have dimension bounded by that of the base of the zeroth
level. By the criterion for an inverse limit of a tower of Artinian local algebras, the inverse
limit of the tower is then a Noetherian complete local ring with residue field `k`.

## Main definitions

* `Deformation.versalStageFormalizationMaps`: for a versal formal object, a compatible family of
  arrows from it into the minimal stages.

## Main results

* `Deformation.stageBaseTowerTransition_surjective`: the transition maps of `stageBaseTower` are
  surjective.
* `Deformation.versalLiftAlongStageTransition`: for a versal formal object, every arrow from it
  into the `n`-th minimal stage lifts along the transition morphism of the stages.
* `Deformation.versal_minimalStage_map_surjective`: for a versal formal object, the chosen arrow
  into each minimal stage is surjective on bases.
* `Deformation.cotangent_finrank_le_of_surjective_local`: a surjection of local Noetherian rings
  does not increase the dimension of the cotangent space.
* `Deformation.stageBaseTower_cotangent_bounded_of_versal`: for a versal formal object the
  cotangent spaces of `stageBaseTower` have bounded dimension, bounded by the cotangent space of
  the base of the zeroth level.
* `Deformation.stageBaseTower_cotangent_bounded`: under a bound on the cotangent dimensions, the
  inverse limit of `stageBaseTower` is a Noetherian complete local ring with residue field `k`.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}


section
variable [IsNoetherianRing Λ] [Module.Finite Λ k]
/-- The transition maps of `stageBaseTower` are surjective. -/
theorem stageBaseTowerTransition_surjective
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (n : ℕ) :
    Function.Surjective (stageBaseTowerTransition hp hS1 ξ n).hom :=
  stageBaseTransition_surjective hp hS1 ξ n

/-- For a versal formal object, every arrow from it into the `n`-th minimal stage lifts along the
transition morphism of the stages. -/
theorem versalLiftAlongStageTransition
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (hξ : IsVersal hp ξ) (n : ℕ)
    (a : ξ ⟶ artinianFormalization hp
      (minimalStages hp hS1 ξ n).obj.left) :
    ∃ b : ξ ⟶ artinianFormalization hp
        (minimalStages hp hS1 ξ (n + 1)).obj.left,
      b ≫ artinianFormalizationMap hp (stageObjectTransition hp hS1 ξ n) = a :=
  (isVersal_iff_lifts_artinian hp ξ).mp hξ _ (stageBaseTowerTransition_surjective hp hS1 ξ n) _
    (IsHomLift.of_fac' _ _ _ rfl rfl rfl) a

/-- For a versal formal object, a compatible family of arrows from it into the minimal stages. -/
noncomputable def versalStageFormalizationMaps
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (hξ : IsVersal hp ξ)
    (a₀ : ξ ⟶ artinianFormalization hp
      (minimalStages hp hS1 ξ 0).obj.left) :
    ∀ n, ξ ⟶ artinianFormalization hp (minimalStages hp hS1 ξ n).obj.left :=
  Nat.rec a₀ (fun n a => Classical.choose
    (versalLiftAlongStageTransition hp hS1 ξ hξ n a))


/-- For a versal formal object, the chosen arrow into each minimal stage is surjective on bases. -/
theorem versal_minimalStage_map_surjective
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (hξ : IsVersal hp ξ) (n : ℕ) :
    ∃ f : ξ.level n ⟶ (minimalStages hp hS1 ξ n).obj.left,
      Function.Surjective (p.map f).hom := by
  let a₀ := versalInitialFormalizationMap hp ξ
  let h := versalStageFormalizationMaps hp hS1 ξ hξ a₀
  let eIso := artinianFormalizationInclusion_isIso_at_stage hp hS1 ξ n
  let eInv := Classical.choose eIso.out
  let f : ξ.level n ⟶ (minimalStages hp hS1 ξ n).obj.left := (h n).app n ≫ eInv
  refine ⟨f, ?_⟩
  exact minimalDescent_map_surjective hp (minimalStages hp hS1 ξ n)
    ((minimalStages_spec hp hS1 ξ).1 n) f

/-- A surjection of local Noetherian rings does not increase the dimension of the cotangent
space. -/
theorem cotangent_finrank_le_of_surjective_local
    {A B : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (g : A →+* B) (hg : Function.Surjective g) :
    Module.finrank (ResidueField B) (CotangentSpace B) ≤
      Module.finrank (ResidueField A) (CotangentSpace A) := by
  classical
  rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    ← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  obtain ⟨t, htcard, htspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (maximalIdeal A).fg_of_isNoetherianRing
  have hmB : maximalIdeal B = Ideal.span (g '' (↑t : Set A)) := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective g hg, ← htspan, Ideal.map_span]
  rw [hmB]
  calc
    (Ideal.span (g '' (↑t : Set A))).spanFinrank ≤
        (g '' (↑t : Set A)).ncard :=
      Submodule.spanFinrank_span_le_ncard_of_finite (t.finite_toSet.image _)
    _ ≤ (↑t : Set A).ncard := Set.ncard_image_le t.finite_toSet
    _ = t.card := Set.ncard_coe_finset _
    _ = (maximalIdeal A).spanFinrank := htcard

/-- For a versal formal object the cotangent spaces of `stageBaseTower` have bounded dimension,
bounded by the cotangent space of the base of the zeroth level. -/
theorem stageBaseTower_cotangent_bounded_of_versal
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p) (hξ : IsVersal hp ξ) :
    ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d := by
  refine ⟨Module.finrank (ResidueField ξ.base) (CotangentSpace ξ.base), fun n => ?_⟩
  obtain ⟨f, hf⟩ := versal_minimalStage_map_surjective hp hS1 ξ hξ n
  calc
    Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) =
      Module.finrank (ResidueField (p.obj (minimalStages hp hS1 ξ n).obj.left))
        (CotangentSpace (p.obj (minimalStages hp hS1 ξ n).obj.left)) := rfl
    _ ≤ Module.finrank (ResidueField (p.obj (ξ.level n)))
        (CotangentSpace (p.obj (ξ.level n))) :=
      cotangent_finrank_le_of_surjective_local (p.map f).hom.toRingHom hf
    _ ≤ Module.finrank (ResidueField ξ.base) (CotangentSpace ξ.base) :=
      cotangent_finrank_le_of_surjective_local
        ((eqToHom (ξ.level_eq n).symm).hom.toRingHom.comp
          (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n)))
        ((artinianHom_surjective_of_isIso (eqToHom (ξ.level_eq n).symm)).comp
          Ideal.Quotient.mk_surjective)

/-- Under a bound on the cotangent dimensions, the inverse limit of `stageBaseTower` is a
Noetherian complete local ring with residue field `k`. -/
theorem stageBaseTower_cotangent_bounded
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d) :
    ∃ h : IsNoetherianCompleteLocalRing
        (inverseLimit (stageBaseTower hp hS1 ξ)
          (stageBaseTowerTransition hp hS1 ξ)),
      letI : IsLocalRing (inverseLimit (stageBaseTower hp hS1 ξ)
        (stageBaseTowerTransition hp hS1 ξ)) := h.isLocal
      Nonempty (ResidueField (inverseLimit (stageBaseTower hp hS1 ξ)
        (stageBaseTowerTransition hp hS1 ξ)) ≃ₐ[Λ] k) := by
  apply inverseLimit_isObjectOfCompleteLocalAlgCat
    (stageBaseTower hp hS1 ξ) (stageBaseTowerTransition hp hS1 ξ)
    (fun n => stageBaseTowerTransition_surjective hp hS1 ξ n) hbound

end

end Deformation

end
