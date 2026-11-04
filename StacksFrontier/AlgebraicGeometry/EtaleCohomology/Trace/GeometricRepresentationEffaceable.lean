module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafDegreeTwo
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricCyclicCharacter

/-!
# `ρ ↦ H^i(X_{k̄}, ℱ_ρ)` is elementwise effaceable

Let `X` be a quasi-compact quasi-separated connected curve over `k`, `K` an algebraic closure of
`k` with `X_K` connected, `Λ` a finite ring with `#Λ` invertible in `K`. The δ-functor
`ρ ↦ H^i(X_K, ℱ_ρ)` on finite `Λ`-modules with continuous `π₁(X)`-action is elementwise
effaceable, provided either `X_K` is affine, or `X_K` is a smooth proper curve of genus `≥ 1`:

* degree one: classes die on finite étale covers of `X` (torsors,
  `AlgebraicGeometry.exists_unit_map_eq_zero_of_eq_one`);
* degree two: zero if `X_K` is affine (Tag 0A54); if `X_K` is projective of genus `≥ 1`, the trace
  argument with the cyclic quotients of `π₁(X_K)`
  (`AlgebraicGeometry.exists_unit_map_eq_zero_of_eq_two`,
  `AlgebraicGeometry.exists_surjective_geometricFundamentalGroup_zmod`);
* degree `≥ 3`: zero (Tag 0A53, `AlgebraicGeometry.exists_unit_map_eq_zero_of_two_lt`).

This is the étale half of the proof of Tag 03VM ("both sides are universal δ-functors").

## Main results

* `AlgebraicGeometry.elementwiseEffaceable_geometricRepresentationCohomology_of_genus`
* `AlgebraicGeometry.elementwiseEffaceable_geometricRepresentationCohomology_of_isAffine`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.EtaleCohomology Stacks.GroupCohomology

universe u

namespace AlgebraicGeometry

/-- Sheafification of presheaves of `Λ`-modules on Mathlib's small étale site, pinned at
`u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_objectUniverse_effaceable (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

/-- Enough injectives for sheaves of `Λ`-modules on Mathlib's small étale site, pinned at
`u + 1`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_objectUniverse_effaceable
    (Λ : Type) [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) (K : Type u)
  [Field K] [Algebra k K]

/-- **The effacement hypothesis on an affine curve**: in degree two `H²(X_K, ℱ_ρ) = 0`. -/
theorem exists_unit_map_eq_zero_of_eq_two_of_isAffine (hcurve : IsCurve k f) [IsAlgClosed K]
    [IsAffine (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x))
    (ξ : ((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (1 + 1)).obj
          ((geometricRepresentationSheaf B X x Λ f K).obj M)) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ X.1) (_ : IsFinite π) (_ : Etale π) (_ : Surjective π),
      ((etaleModuleGlobalSections.{u, 0} Λ
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived (1 + 1)).map
        ((etaleModuleInverseImage.{u, 0} Λ
          (pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))).map
          ((etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app
            ((representationSheaf.{u, 0} B X x Λ).obj M))) ξ = 0 := by
  have hz := isZero_rightDerived_fieldBaseChange_of_isAffine Λ f K hcurve
    ((geometricRepresentationSheaf B X x Λ f K).obj M) (q := 1 + 1) (by omega)
  rw [ModuleCat.isZero_iff_subsingleton] at hz
  refine ⟨X.1, 𝟙 _, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Subsingleton.elim ξ 0]
  exact map_zero _

/-- **`ρ ↦ H^i(X_K, ℱ_ρ)` is elementwise effaceable for `X_K` affine.** -/
theorem elementwiseEffaceable_geometricRepresentationCohomology_of_isAffine [CompactSpace X.1]
    [QuasiSeparatedSpace X.1] (hcurve : IsCurve k f) [Algebra.IsAlgebraic k K] [IsAlgClosed K]
    [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
    [IsAffine (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)] :
    (geometricRepresentationCohomology.{u, 0} B X x Λ f K).ElementwiseEffaceable := by
  refine elementwiseEffaceable_geometricRepresentationCohomology_of_forall_exists_unit B X x Λ f K
    fun M n ξ => ?_
  match n with
  | 0 => exact exists_unit_map_eq_zero_of_eq_one B X x Λ f K M ξ
  | 1 => exact exists_unit_map_eq_zero_of_eq_two_of_isAffine B X x Λ f K hcurve M ξ
  | n + 2 => exact exists_unit_map_eq_zero_of_two_lt B X x Λ f K hcurve M (by omega) ξ

/-- **`ρ ↦ H^i(X_K, ℱ_ρ)` is elementwise effaceable for `X_K` a smooth proper curve of genus
`≥ 1`**, `K` an algebraic closure of `k` and `#Λ` invertible in `K`. -/
theorem elementwiseEffaceable_geometricRepresentationCohomology_of_genus [CompactSpace X.1]
    [QuasiSeparatedSpace X.1] (hcurve : IsCurve k f) [IsAlgClosure k K]
    [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
    (hK : B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
    [IsCurve K (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
    [Smooth (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
    [IsProper (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
    (hg : 1 ≤ genus (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)))
    (hΛ : IsUnit ((Nat.card Λ : ℕ) : K)) :
    (geometricRepresentationCohomology.{u, 0} B X x Λ f K).ElementwiseEffaceable := by
  have : Algebra.IsAlgebraic k K := IsAlgClosure.isAlgebraic
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have : NeZero (Nat.card Λ) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨z₀⟩ : Nonempty (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) :=
    ConnectedSpace.toNonempty
  let z := GeometricPoint.ofPoint _ z₀
  have hχ : ∀ e : ℕ,
      ∃ χ : EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) z →*
          Multiplicative (ZMod (Nat.card Λ ^ (e + 1))),
        IsOpen (χ.ker : Set (EtaleFundamentalGroup _ z)) ∧ Function.Surjective χ := fun e =>
    exists_surjective_geometricFundamentalGroup_zmod B X f K hK z hg (Nat.card Λ) (e + 1) hΛ
  refine elementwiseEffaceable_geometricRepresentationCohomology_of_forall_exists_unit B X x Λ f K
    fun M n ξ => ?_
  match n with
  | 0 => exact exists_unit_map_eq_zero_of_eq_one B X x Λ f K M ξ
  | 1 => exact exists_unit_map_eq_zero_of_eq_two B X x Λ f K z hχ hΛ M ξ
  | n + 2 => exact exists_unit_map_eq_zero_of_two_lt B X x Λ f K hcurve M (by omega) ξ

end AlgebraicGeometry

end
