module

public import StacksFrontier.Deformation.Formal.MinimalVersal.FilteredFormalObject

/-!
# The descended formal object and the arrows into the original levels

Pushing the minimal stages forward onto the adic truncations of the stage tower limit gives a
formal object over that limit. Its levels receive arrows from the filtered levels, and these
arrows map to the levels of the original formal object compatibly with all transition morphisms.

## Main definitions

* `Deformation.stageBaseTowerFormalObject`: the formal object over `stageBaseTowerCompleteLocal`
  obtained by pushing the minimal stages forward onto the adic truncations of that base.
* `Deformation.stageFilteredLevelMapBaseAtStage`: the base map of `stageFilteredLevelMapAtStage`:
  the identification of the base of the filtered level with a term of the tower, followed by its
  inclusion.
* `Deformation.stageFilteredLevelMapAtStage`: the chosen arrow from the filtered level at index
  `b` into the `b`-th level of the formal object.

## Main results

* `Deformation.stageFilteredLevelMapBaseAtStage_fac`: `stageFilteredLevelMapBaseAtStage` factors
  through `stageBaseTowerQuotientIso` and the inclusion of the tower.
* `Deformation.stageFilteredLevelMapAtStage_exists`: there is an arrow from the filtered level at
  index `b` into the `b`-th level of the formal object lying over
  `stageFilteredLevelMapBaseAtStage`.
* `Deformation.stageFilteredLevelMapAtStage_fac`: `stageFilteredLevelMapAtStage` is compatible
  with the pushforward arrow of the minimal stage at the same index.
* `Deformation.stageFilteredLevelMapAtStage_map`: `stageFilteredLevelMapAtStage` lies over
  `stageFilteredLevelMapBaseAtStage`.
* `Deformation.stageFilteredLevelMapAtStage_naturality`: the arrows `stageFilteredLevelMapAtStage`
  commute with the transition morphisms on both sides.

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
/-- The formal object over `stageBaseTowerCompleteLocal` obtained by pushing the minimal stages
forward onto the adic truncations of that base. -/
noncomputable def stageBaseTowerFormalObject
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d) :
    FormalObject p := by
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let R := stageBaseTowerCompleteLocal hp hS1 ξ hbound
  let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
  let b := toAdicIndex I
  let q (n : ℕ) := stageFormalQuotientToAdic hp hS1 ξ hbound n
  let level (n : ℕ) := cofiberedPushforwardObj hp (q n) (X.level (b n))
    (X.level_eq (b n))
  let inclusion (n : ℕ) := cofiberedPushforwardMap hp (q n) (X.level (b n))
    (X.level_eq (b n))
  let transition (n : ℕ) := cofiberedPushforwardDesc hp (q (n + 1))
    (AdicTruncation.transition R n) (X.level (b (n + 1))) (level n)
    (X.level_eq (b (n + 1)))
    (filteredObjectPath I X (toAdicIndex_mono I (Nat.le_succ n)) ≫ inclusion n)
    (stageFormalPsi_lift hp hS1 ξ hbound X n)
  have hlevel (n : ℕ) : p.obj (level n) = AdicTruncation.obj R n :=
    cofiberedPushforwardObj_eq hp (q n) (X.level (b n)) (X.level_eq (b n))
  exact
    { base := R
      level := level
      level_eq := hlevel
      transition := transition
      transition_lift := fun n => cofiberedPushforwardDesc_lift hp (q (n + 1))
        (AdicTruncation.transition R n) (X.level (b (n + 1))) (level n)
        (X.level_eq (b (n + 1)))
        (filteredObjectPath I X (toAdicIndex_mono I (Nat.le_succ n)) ≫ inclusion n)
        (stageFormalPsi_lift hp hS1 ξ hbound X n) }


/-- The base map of `stageFilteredLevelMapAtStage`: the identification of the base of the filtered
level with a term of the tower, followed by its inclusion. -/
noncomputable def stageFilteredLevelMapBaseAtStage
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (b : ℕ) :
    let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
    p.obj (X.level b) ⟶ p.obj (ξ.level b) := by
  classical
  let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
  let M := minimalStages hp hS1 ξ b
  let e := stageBaseTowerQuotientIso hp hS1 ξ hbound b
  have hM : p.obj M.obj.left = stageBaseTower hp hS1 ξ b := rfl
  have hobj : cofiberedPushforwardObj hp e.inv M.obj.left hM = X.level b := by
    dsimp [X, minimalStagesFilteredFormalObject]
  have hobjBase := congrArg p.obj hobj
  let α := eqToHom hobjBase ≫ eqToHom (X.level_eq b) ≫ e.hom ≫
    stageBaseTowerInclusion hp hS1 ξ b
  exact eqToHom hobjBase.symm ≫ α

/-- `stageFilteredLevelMapBaseAtStage` factors through `stageBaseTowerQuotientIso` and the
inclusion of the tower. -/
theorem stageFilteredLevelMapBaseAtStage_fac
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (b : ℕ) :
    let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
    stageFilteredLevelMapBaseAtStage hp hS1 ξ hbound b =
      eqToHom (X.level_eq b) ≫
        (stageBaseTowerQuotientIso hp hS1 ξ hbound b).hom ≫
        stageBaseTowerInclusion hp hS1 ξ b := by
  classical
  dsimp only
  simp [stageFilteredLevelMapBaseAtStage, stageBaseTowerInclusion]

/-- There is an arrow from the filtered level at index `b` into the `b`-th level of the formal
object lying over `stageFilteredLevelMapBaseAtStage`. -/
theorem stageFilteredLevelMapAtStage_exists
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (b : ℕ) :
    let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
    let M := minimalStages hp hS1 ξ b
    ∃ u : X.level b ⟶ ξ.level b,
      p.map u = stageFilteredLevelMapBaseAtStage hp hS1 ξ hbound b ∧
      cofiberedPushforwardMap hp
        (stageBaseTowerQuotientIso hp hS1 ξ hbound b).inv M.obj.left
        (show p.obj M.obj.left = stageBaseTower hp hS1 ξ b from by
          simp [stageBaseTower, M]) ≫
        eqToHom (show cofiberedPushforwardObj hp
          (stageBaseTowerQuotientIso hp hS1 ξ hbound b).inv M.obj.left
          (show p.obj M.obj.left = stageBaseTower hp hS1 ξ b from by
            simp [stageBaseTower, M]) = X.level b
          from by dsimp [X, minimalStagesFilteredFormalObject]) ≫ u = M.obj.hom := by
  classical
  dsimp only
  let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
  let M := minimalStages hp hS1 ξ b
  let e := stageBaseTowerQuotientIso hp hS1 ξ hbound b
  have hM : p.obj M.obj.left = stageBaseTower hp hS1 ξ b := by
    simp [stageBaseTower, M]
  have hobj : cofiberedPushforwardObj hp e.inv M.obj.left hM = X.level b := by
    dsimp [X, minimalStagesFilteredFormalObject]
  have hobjBase := congrArg p.obj hobj
  let i := cofiberedPushforwardMap hp e.inv M.obj.left hM
  let α := eqToHom hobjBase ≫ eqToHom (X.level_eq b) ≫ e.hom ≫
    eqToHom hM.symm ≫ p.map M.obj.hom
  have hfac : p.map i ≫ eqToHom hobjBase ≫ eqToHom (X.level_eq b) =
      eqToHom hM ≫ e.inv := by
    let := cofiberedPushforwardMap_lift hp e.inv M.obj.left hM
    rw [IsHomLift.fac' p e.inv i]
    simp
  have hbase : p.map i ≫ α = p.map M.obj.hom := by
    calc
      p.map i ≫ α =
          (p.map i ≫ eqToHom hobjBase ≫ eqToHom (X.level_eq b)) ≫ e.hom ≫
            eqToHom hM.symm ≫ p.map M.obj.hom := by simp [α, Category.assoc]
      _ = (eqToHom hM ≫ e.inv) ≫ e.hom ≫
            eqToHom hM.symm ≫ p.map M.obj.hom := by rw [hfac]
      _ = p.map M.obj.hom := by simp [Category.assoc]
  let H := existsUnique_factor_of_isHomLift hp i M.obj.hom α hbase
  obtain ⟨u, ⟨hu, hcomp⟩⟩ := H.exists
  refine ⟨eqToHom hobj.symm ≫ u, ?_, ?_⟩
  · change p.map (eqToHom hobj.symm ≫ u) = eqToHom hobjBase.symm ≫ α
    rw [Functor.map_comp, hu]
    rw [eqToHom_map]
  · change i ≫ eqToHom hobj ≫ (eqToHom hobj.symm ≫ u) = M.obj.hom
    simp [hcomp]

/-- The chosen arrow from the filtered level at index `b` into the `b`-th level of the formal
object. -/
noncomputable def stageFilteredLevelMapAtStage
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (b : ℕ) :
    (minimalStagesFilteredFormalObject hp hS1 ξ hbound).level b ⟶ ξ.level b :=
  Classical.choose (stageFilteredLevelMapAtStage_exists hp hS1 ξ hbound b)

/-- `stageFilteredLevelMapAtStage` is compatible with the pushforward arrow of the minimal stage at
the same index. -/
theorem stageFilteredLevelMapAtStage_fac
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (b : ℕ) :
    let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
    let M := minimalStages hp hS1 ξ b
    cofiberedPushforwardMap hp
      (stageBaseTowerQuotientIso hp hS1 ξ hbound b).inv M.obj.left
      (show p.obj M.obj.left = stageBaseTower hp hS1 ξ b from by
        simp [stageBaseTower, M]) ≫
      eqToHom (show cofiberedPushforwardObj hp
        (stageBaseTowerQuotientIso hp hS1 ξ hbound b).inv M.obj.left
        (show p.obj M.obj.left = stageBaseTower hp hS1 ξ b from by
          simp [stageBaseTower, M]) =
        X.level b from by dsimp [X, minimalStagesFilteredFormalObject]) ≫
      stageFilteredLevelMapAtStage hp hS1 ξ hbound b = M.obj.hom :=
  (stageFilteredLevelMapAtStage_exists hp hS1 ξ hbound b).choose_spec.2

/-- `stageFilteredLevelMapAtStage` lies over `stageFilteredLevelMapBaseAtStage`. -/
theorem stageFilteredLevelMapAtStage_map
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (b : ℕ) :
    p.map (stageFilteredLevelMapAtStage hp hS1 ξ hbound b) =
      stageFilteredLevelMapBaseAtStage hp hS1 ξ hbound b :=
  (stageFilteredLevelMapAtStage_exists hp hS1 ξ hbound b).choose_spec.1

/-- The arrows `stageFilteredLevelMapAtStage` commute with the transition morphisms on both sides.
-/
theorem stageFilteredLevelMapAtStage_naturality
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (b : ℕ) :
    let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
    X.transition b ≫ stageFilteredLevelMapAtStage hp hS1 ξ hbound b =
      stageFilteredLevelMapAtStage hp hS1 ξ hbound (b + 1) ≫ ξ.transition b := by
  classical
  let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
  let M := minimalStages hp hS1 ξ
  let e (n : ℕ) := stageBaseTowerQuotientIso hp hS1 ξ hbound n
  let rawi (n : ℕ) := cofiberedPushforwardMap hp (e n).inv (M n).obj.left
    (show p.obj (M n).obj.left = stageBaseTower hp hS1 ξ n from by
      simp [stageBaseTower, M])
  let i (n : ℕ) := rawi n ≫ eqToHom (show
    cofiberedPushforwardObj hp (e n).inv (M n).obj.left
      (show p.obj (M n).obj.left = stageBaseTower hp hS1 ξ n from by
        simp [stageBaseTower, M]) = X.level n
      from by dsimp [X, minimalStagesFilteredFormalObject])
  have hiCart (n : ℕ) : p.IsStronglyCocartesian ((e n).inv) (i n) := by
    have hM : p.obj (M n).obj.left = stageBaseTower hp hS1 ξ n := by simp [stageBaseTower, M]
    have : p.IsStronglyCocartesian ((e n).inv) (rawi n) :=
      cofibered_pushforward_isCocartesian hp (e n).inv (M n).obj.left hM
    have hobj : cofiberedPushforwardObj hp (e n).inv (M n).obj.left hM = X.level n := by
      dsimp [X, minimalStagesFilteredFormalObject]
    have : p.IsHomLift (𝟙 ((stageBaseTowerIdealFiltration hp hS1 ξ hbound).quotient n))
        (asIso (eqToHom hobj)).hom :=
      IsHomLift.of_fac p _ _ (cofiberedPushforwardObj_eq hp (e n).inv (M n).obj.left hM)
        (X.level_eq n) (by simp [eqToHom_map])
    exact stronglyCocartesian_postcomp_iso p (e n).inv (rawi n) (asIso (eqToHom hobj))
  have hi : IsIso (i (b + 1)) :=
    have := hiCart (b + 1)
    Functor.IsStronglyCocartesian.isIso_of_base_isIso p (e (b + 1)).inv (i (b + 1))
  let τ := (stageBaseTowerIdealFiltration hp hS1 ξ hbound).transition b
  have htransition : i (b + 1) ≫ X.transition b =
      stageObjectTransition hp hS1 ξ b ≫ i b := by
    dsimp [X, minimalStagesFilteredFormalObject, i, rawi, e, M]
    simpa [Category.id_comp, Category.comp_id] using cofiberedPushforwardDesc_fac hp
      (stageBaseTowerQuotientIso hp hS1 ξ hbound (b + 1)).inv
      τ
      (minimalStages hp hS1 ξ (b + 1)).obj.left
      (cofiberedPushforwardObj hp
        (stageBaseTowerQuotientIso hp hS1 ξ hbound b).inv
        (minimalStages hp hS1 ξ b).obj.left (by rfl))
      (by rfl)
      (stageObjectTransition hp hS1 ξ b ≫
        cofiberedPushforwardMap hp
          (stageBaseTowerQuotientIso hp hS1 ξ hbound b).inv
          (minimalStages hp hS1 ξ b).obj.left (by rfl))
      (by
        have hmap : p.map (stageObjectTransition hp hS1 ξ b) =
            stageBaseTowerTransition hp hS1 ξ b := stageObjectTransition_map hp hS1 ξ b
        let : p.IsHomLift (stageBaseTowerTransition hp hS1 ξ b)
            (stageObjectTransition hp hS1 ξ b) :=
          hmap.symm ▸ IsHomLift.map (p := p) (stageObjectTransition hp hS1 ξ b)
        let := cofiberedPushforwardMap_lift hp
          (stageBaseTowerQuotientIso hp hS1 ξ hbound b).inv
          (minimalStages hp hS1 ξ b).obj.left (by rfl)
        have hcomp : p.IsHomLift
            (stageBaseTowerTransition hp hS1 ξ b ≫
              (stageBaseTowerQuotientIso hp hS1 ξ hbound b).inv)
            (stageObjectTransition hp hS1 ξ b ≫
              cofiberedPushforwardMap hp
                (stageBaseTowerQuotientIso hp hS1 ξ hbound b).inv
                (minimalStages hp hS1 ξ b).obj.left (by rfl)) := inferInstance
        exact (stageBaseTowerQuotientIso_inv_transition_fac hp hS1 ξ hbound b).symm ▸ hcomp)
  have hfac (n : ℕ) : i n ≫ stageFilteredLevelMapAtStage hp hS1 ξ hbound n =
      (M n).obj.hom := by
    simpa only [i, rawi, e, M, Category.assoc] using
      stageFilteredLevelMapAtStage_fac hp hS1 ξ hbound n
  have hcore : i (b + 1) ≫ X.transition b ≫
        stageFilteredLevelMapAtStage hp hS1 ξ hbound b =
      i (b + 1) ≫ stageFilteredLevelMapAtStage hp hS1 ξ hbound (b + 1) ≫
        ξ.transition b := by
    calc
      i (b + 1) ≫ X.transition b ≫
          stageFilteredLevelMapAtStage hp hS1 ξ hbound b =
        stageObjectTransition hp hS1 ξ b ≫ i b ≫
          stageFilteredLevelMapAtStage hp hS1 ξ hbound b := by
            rw [← Category.assoc, htransition, Category.assoc]
      _ = stageObjectTransition hp hS1 ξ b ≫
          (minimalStages hp hS1 ξ b).obj.hom := by rw [hfac b]
      _ = (minimalStages hp hS1 ξ (b + 1)).obj.hom ≫ ξ.transition b :=
        stageObjectTransition_fac hp hS1 ξ b
      _ = i (b + 1) ≫ stageFilteredLevelMapAtStage hp hS1 ξ hbound (b + 1) ≫
          ξ.transition b := by
            simpa [Category.assoc] using
              congrArg (fun t => t ≫ ξ.transition b) (hfac (b + 1)).symm
  exact (cancel_epi (i (b + 1))).1 hcore

end

end Deformation

end
