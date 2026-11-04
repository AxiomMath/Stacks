module

public import StacksFrontier.Deformation.Formal.MinimalVersal.LevelMapPaths

/-!
# The morphism from the descended formal object

The arrows from the filtered levels into the levels of the original formal object descend to the
levels of the pushed-forward formal object and assemble into a morphism of formal objects lying
over the inclusion of the stage tower limit into the original base.

## Main definitions

* `Deformation.stageBaseTowerFormalObjectApp`: the component at level `n` of the morphism from
  `stageBaseTowerFormalObject` to the given formal object.
* `Deformation.stageBaseTowerFormalObjectHom`: the morphism of formal objects from
  `stageBaseTowerFormalObject` to the given formal object.

## Main results

* `Deformation.stageBaseTowerFormalObjectApp_lift`: the components of the morphism out of
  `stageBaseTowerFormalObject` lie over the adic truncations of `stageBaseTowerBaseHom`.
* `Deformation.stageBaseTowerFormalObjectApp_fac`: the components of the morphism out of
  `stageBaseTowerFormalObject` are compatible with the pushforward arrows defining its levels.
* `Deformation.stageBaseTowerFormalObjectApp_naturality`: the components of the morphism out of
  `stageBaseTowerFormalObject` commute with the transition morphisms on both sides.

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
/-- The component at level `n` of the morphism from `stageBaseTowerFormalObject` to the given
formal object. -/
noncomputable def stageBaseTowerFormalObjectApp
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    (stageBaseTowerFormalObject hp hS1 ξ hbound).level n ⟶ ξ.level n := by
  let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
  let b := toAdicIndex (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n
  let q := stageFormalQuotientToAdic hp hS1 ξ hbound n
  let β := (AdicTruncation.functor n).map (stageBaseTowerBaseHom hp hS1 ξ hbound)
  let g := β ≫ eqToHom (ξ.level_eq n).symm
  let ψ := stageFilteredLevelToOriginal hp hS1 ξ hbound n
  have hψ : p.IsHomLift (q ≫ g) ψ := by
    have h : p.map ψ ≫ eqToHom (ξ.level_eq n) =
        eqToHom (X.level_eq b) ≫ q ≫ β := by
      simpa [ψ, stageFilteredLevelToOriginal, q, β, X, b] using
        stageFilteredLevelMapAtStage_path_lift hp hS1 ξ hbound n
    exact IsHomLift.of_fac' p (q ≫ g) ψ (X.level_eq b) rfl (by
      simpa [g] using (comp_eqToHom_iff _ _ _).1 h)
  exact cofiberedPushforwardDesc hp q g (X.level b) (ξ.level n)
    (X.level_eq b) ψ hψ

/-- The components of the morphism out of `stageBaseTowerFormalObject` lie over the adic
truncations of `stageBaseTowerBaseHom`. -/
theorem stageBaseTowerFormalObjectApp_lift
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    p.IsHomLift ((AdicTruncation.functor n).map
        (stageBaseTowerBaseHom hp hS1 ξ hbound))
      (stageBaseTowerFormalObjectApp hp hS1 ξ hbound n) :=
  (IsHomLift.lift_comp_eqToHom_iff p _ _ _).1 (cofiberedPushforwardDesc_lift hp _ _ _ _ _ _ _)

/-- The components of the morphism out of `stageBaseTowerFormalObject` are compatible with the
pushforward arrows defining its levels. -/
theorem stageBaseTowerFormalObjectApp_fac
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    cofiberedPushforwardMap hp
        (stageFormalQuotientToAdic hp hS1 ξ hbound n)
        ((minimalStagesFilteredFormalObject hp hS1 ξ hbound).level
          (toAdicIndex (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n))
        ((minimalStagesFilteredFormalObject hp hS1 ξ hbound).level_eq
          (toAdicIndex (stageBaseTowerIdealFiltration hp hS1 ξ hbound) n)) ≫
      stageBaseTowerFormalObjectApp hp hS1 ξ hbound n =
        stageFilteredLevelToOriginal hp hS1 ξ hbound n :=
  cofiberedPushforwardDesc_fac hp _ _ _ _ _ _ _

/-- The components of the morphism out of `stageBaseTowerFormalObject` commute with the transition
morphisms on both sides. -/
theorem stageBaseTowerFormalObjectApp_naturality
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d)
    (n : ℕ) :
    (stageBaseTowerFormalObject hp hS1 ξ hbound).transition n ≫
        stageBaseTowerFormalObjectApp hp hS1 ξ hbound n =
      stageBaseTowerFormalObjectApp hp hS1 ξ hbound (n + 1) ≫ ξ.transition n := by
  let F := stageBaseTowerFormalObject hp hS1 ξ hbound
  let I := stageBaseTowerIdealFiltration hp hS1 ξ hbound
  let X := minimalStagesFilteredFormalObject hp hS1 ξ hbound
  let q (j : ℕ) := stageFormalQuotientToAdic hp hS1 ξ hbound j
  let incl (j : ℕ) := cofiberedPushforwardMap hp (q j) (X.level (toAdicIndex I j))
    (X.level_eq (toAdicIndex I j))
  let left := F.transition n ≫ stageBaseTowerFormalObjectApp hp hS1 ξ hbound n
  let right := stageBaseTowerFormalObjectApp hp hS1 ξ hbound (n + 1) ≫ ξ.transition n
  have hψ : p.IsHomLift
      (stageFormalQuotientToAdic hp hS1 ξ hbound (n + 1) ≫
        AdicTruncation.transition (stageBaseTowerCompleteLocal hp hS1 ξ hbound) n)
      (filteredObjectPath I X (toAdicIndex_mono I (Nat.le_succ n)) ≫ incl n) := by
    simpa [incl, q] using stageFormalPsi_lift hp hS1 ξ hbound X n
  have htransfac : incl (n + 1) ≫ F.transition n =
      filteredObjectPath I X (toAdicIndex_mono I (Nat.le_succ n)) ≫ incl n := by
    dsimp [F, stageBaseTowerFormalObject, incl, q, X, minimalStagesFilteredFormalObject]
    exact cofiberedPushforwardDesc_fac hp _ _ _ _ _ _ hψ
  have happfac (j : ℕ) : incl j ≫
      stageBaseTowerFormalObjectApp hp hS1 ξ hbound j =
        stageFilteredLevelToOriginal hp hS1 ξ hbound j := by
    simpa [incl, q, X] using stageBaseTowerFormalObjectApp_fac hp hS1 ξ hbound j
  have hcomp : incl (n + 1) ≫ left = incl (n + 1) ≫ right := by
    calc
      incl (n + 1) ≫ left =
          (incl (n + 1) ≫ F.transition n) ≫
            stageBaseTowerFormalObjectApp hp hS1 ξ hbound n := by
              dsimp [left]
              exact (Category.assoc _ _ _).symm
      _ = (filteredObjectPath I X
            (toAdicIndex_mono I (Nat.le_succ n)) ≫ incl n) ≫
            stageBaseTowerFormalObjectApp hp hS1 ξ hbound n :=
              congrArg (fun t => t ≫ stageBaseTowerFormalObjectApp hp hS1 ξ hbound n) htransfac
      _ = filteredObjectPath I X
            (toAdicIndex_mono I (Nat.le_succ n)) ≫
            (incl n ≫ stageBaseTowerFormalObjectApp hp hS1 ξ hbound n) :=
              Category.assoc _ _ _
      _ = filteredObjectPath I X
            (toAdicIndex_mono I (Nat.le_succ n)) ≫
            stageFilteredLevelToOriginal hp hS1 ξ hbound n := by rw [happfac n]
      _ = stageFilteredLevelToOriginal hp hS1 ξ hbound (n + 1) ≫ ξ.transition n :=
        stageFilteredLevelToOriginal_naturality hp hS1 ξ hbound n
      _ = (incl (n + 1) ≫
            stageBaseTowerFormalObjectApp hp hS1 ξ hbound (n + 1)) ≫ ξ.transition n := by
              rw [happfac (n + 1)]
      _ = incl (n + 1) ≫ right := by
            dsimp [right]
            exact Category.assoc _ _ _
  let βn := (AdicTruncation.functor n).map
    (stageBaseTowerBaseHom hp hS1 ξ hbound)
  let βnext := (AdicTruncation.functor (n + 1)).map
    (stageBaseTowerBaseHom hp hS1 ξ hbound)
  let τR := (AdicTruncation.transitionNat n).app F.base
  let τξ := (AdicTruncation.transitionNat n).app ξ.base
  have hl : p.IsHomLift (τR ≫ βn) left :=
    @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ τR βn
      (F.transition n) (stageBaseTowerFormalObjectApp hp hS1 ξ hbound n) (F.transition_lift n)
      (stageBaseTowerFormalObjectApp_lift hp hS1 ξ hbound n)
  have hr₀ : p.IsHomLift (βnext ≫ τξ) right :=
    @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ βnext τξ
      (stageBaseTowerFormalObjectApp hp hS1 ξ hbound (n + 1))
      (ξ.transition n) (stageBaseTowerFormalObjectApp_lift hp hS1 ξ hbound (n + 1))
      (ξ.transition_lift n)
  have hβ : βnext ≫ τξ = τR ≫ βn := by
    dsimp [βnext, βn, τξ, τR, F]
    exact (AdicTruncation.transitionNat n).naturality
      (stageBaseTowerBaseHom hp hS1 ξ hbound)
  have hr : p.IsHomLift (τR ≫ βn) right := hβ.symm ▸ hr₀
  let qnext := q (n + 1)
  let : p.IsStronglyCocartesian qnext (incl (n + 1)) :=
    cofibered_pushforward_isCocartesian hp qnext _ _
  exact @Functor.IsStronglyCocartesian.ext _ _ _ _ p _ _ _ _
    qnext (incl (n + 1)) inferInstance _ _ (τR ≫ βn) _ _ hl hr hcomp

end

/-- The morphism of formal objects from `stageBaseTowerFormalObject` to the given formal object. -/
noncomputable def stageBaseTowerFormalObjectHom
    [IsNoetherianRing Λ] [Module.Finite Λ k]
    (hp : IsCofiberedInGroupoids p)
    (hS1 : SchlessingerConditionS1 p)
    (ξ : FormalObject p)
    (hbound : ∃ d : ℕ, ∀ n,
      Module.finrank (ResidueField (stageBaseTower hp hS1 ξ n))
        (CotangentSpace (stageBaseTower hp hS1 ξ n)) ≤ d) :
    stageBaseTowerFormalObject hp hS1 ξ hbound ⟶ ξ :=
  { base := stageBaseTowerBaseHom hp hS1 ξ hbound
    app := stageBaseTowerFormalObjectApp hp hS1 ξ hbound
    app_lift := stageBaseTowerFormalObjectApp_lift hp hS1 ξ hbound
    naturality := stageBaseTowerFormalObjectApp_naturality hp hS1 ξ hbound }

end Deformation

end
