module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.ThickeningTower
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedChartEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesOnAffineSite
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianModulesSmallSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.AdditiveGroupSheafCohomology
public import StacksFrontier.Topology.Algebra.DiscreteRingSheaf
public import StacksFrontier.Topology.Algebra.RingLimits

/-!
# The sheaf `W ↦ lim Γ(Wₙ, 𝒪)` on the affine étale site of a thickened algebraic space

Let `F` be a presheaf on the big fppf site of `S` identified, by `e : F ≅ yoneda.obj V`, with
the presheaf represented by an object `V` of the site, and let `V ⟶ X₀ ⟶ X₁ ⟶ ⋯` be a tower of
thickenings of the scheme underlying `V`. Every affine étale chart `W` of `F` is a scheme étale
over `V`, so it has an étale lift `Wₙ` to every stage `Xₙ` (Stacks 04DZ), and the lifts form a
sequence of closed immersions `W₀ ⟶ W₁ ⟶ ⋯`. This file constructs the presheaves
`W ↦ Γ(Wₙ, 𝒪)` on the affine étale site of `F`, their transition maps, and their limit
`W ↦ lim Γ(Wₙ, 𝒪)`, with the inverse-limit topology of the discrete rings `Γ(Wₙ, 𝒪)`.

When `F` is the reduction of a countably indexed affine formal algebraic space
`X = colim Xₙ`, the lift `Wₙ` of an affine étale chart `W = U_red` is the stage `U ×_X Xₙ` of the
corresponding affine formal algebraic space `U` étale over `X`, so the limit is the structure
sheaf of Stacks 0DEJ: `𝒪_X(U_red) = lim Γ(U ×_X Xₙ, 𝒪)`.

## Main definitions

* `AlgebraicGeometry.Space.towerLift`: the functor `W ↦ Wₙ` from affine étale charts to the
  small étale site of `Xₙ`.
* `AlgebraicGeometry.Space.towerRings` and `AlgebraicGeometry.Space.towerRingsTransition`: the
  presheaves `W ↦ Γ(Wₙ, 𝒪)` and the restrictions `Γ(Wₙ₊₁, 𝒪) ⟶ Γ(Wₙ, 𝒪)`.
* `AlgebraicGeometry.Space.towerRingsSystem`: the inverse system they form.
* `AlgebraicGeometry.Space.towerSections`: the presheaf of abelian groups `W ↦ Γ(Wₙ, 𝒪)`, with its
  sections raised one universe.

## Main results

* `AlgebraicGeometry.Space.surjective_towerRingsTransition`: the transition maps are surjective,
  `Wₙ ⟶ Wₙ₊₁` being a closed immersion of affine schemes.
* `AlgebraicGeometry.Space.isSheaf_towerRings_forget`: each `W ↦ Γ(Wₙ, 𝒪)` is a sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS} (e : F ≅ yoneda.obj V)
  (T : ThickeningTower ((BigFppfOver.toScheme B S hS).obj V))

/-! ### The lifts and their rings of functions -/

/-- The lift `W ↦ Wₙ` of the affine étale charts of `F` to the stage `Xₙ` of the tower. -/
noncomputable def towerLift (n : ℕ) : AffineEtale B S hS F ⥤ (T.stage.obj n).Etale :=
  representedAffineChartEtale e ⋙ T.lift n

/-- The lift `W ↦ Wₙ` preserves fibre products. -/
instance towerLift_preservesPullbacks (n : ℕ) :
    PreservesLimitsOfShape WalkingCospan (towerLift e T n) := by
  unfold towerLift
  infer_instance

/-- The lift of an affine chart is affine. -/
instance isAffine_towerLift_obj_left (n : ℕ) (W : AffineEtale B S hS F) :
    IsAffine ((towerLift e T n).obj W).left :=
  T.isAffine_lift_obj_left n _

/-- The scheme `Wₙ` underlying the lift of an affine chart, as a functor to schemes. -/
noncomputable abbrev towerScheme (n : ℕ) : AffineEtale B S hS F ⥤ Scheme.{u} :=
  towerLift e T n ⋙ Scheme.Etale.forget _ ⋙ Over.forget _

/-- The scheme `Wₙ` is affine. -/
instance isAffine_towerScheme_obj (n : ℕ) (W : AffineEtale B S hS F) :
    IsAffine ((towerScheme e T n).obj W) :=
  isAffine_towerLift_obj_left e T n W

/-- The functor `W ↦ Wₙ` to schemes preserves fibre products. -/
instance towerScheme_preservesPullbacks (n : ℕ) :
    PreservesLimitsOfShape WalkingCospan (towerScheme e T n) := by
  unfold towerScheme
  infer_instance

/-- The presheaf of rings `W ↦ Γ(Wₙ, 𝒪)` on the affine étale site of `F`. -/
noncomputable def towerRings (n : ℕ) : (AffineEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u} :=
  (towerScheme e T n).op ⋙ Scheme.Γ

/-- The restriction `Γ(Wₙ₊₁, 𝒪) ⟶ Γ(Wₙ, 𝒪)` along the closed immersion `Wₙ ⟶ Wₙ₊₁`. -/
noncomputable def towerRingsTransition (n : ℕ) : towerRings e T (n + 1) ⟶ towerRings e T n where
  app W := Scheme.Γ.map (T.transition n ((representedAffineChartEtale e).obj W.unop)).op
  naturality {W W'} g := by
    change Scheme.Γ.map
          (((T.lift (n + 1)).map ((representedAffineChartEtale e).map g.unop)).left.op)
        ≫ Scheme.Γ.map (T.transition n ((representedAffineChartEtale e).obj W'.unop)).op =
      Scheme.Γ.map (T.transition n ((representedAffineChartEtale e).obj W.unop)).op ≫
        Scheme.Γ.map (((T.lift n).map ((representedAffineChartEtale e).map g.unop)).left.op)
    rw [← Scheme.Γ.map_comp, ← Scheme.Γ.map_comp, ← op_comp, ← op_comp,
      T.transition_naturality]

/-- The restriction `Γ(Wₙ₊₁, 𝒪) ⟶ Γ(Wₙ, 𝒪)` is surjective. -/
theorem surjective_towerRingsTransition (n : ℕ) (W : (AffineEtale B S hS F)ᵒᵖ) :
    Function.Surjective ((towerRingsTransition e T n).app W) := by
  have : IsAffine ((T.lift (n + 1)).obj ((representedAffineChartEtale e).obj W.unop)).left :=
    T.isAffine_lift_obj_left (n + 1) _
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine
    (T.transition n ((representedAffineChartEtale e).obj W.unop))).2

/-- The inverse system `n ↦ (W ↦ Γ(Wₙ, 𝒪))` of presheaves of rings. -/
noncomputable def towerRingsSystem : ℕᵒᵖ ⥤ ((AffineEtale B S hS F)ᵒᵖ ⥤ CommRingCat.{u}) :=
  Functor.ofOpSequence (towerRingsTransition e T)

/-- The `n`-th term of the inverse system is the presheaf `W ↦ Γ(Wₙ, 𝒪)`. -/
@[simp]
theorem towerRingsSystem_obj (n : ℕ) : (towerRingsSystem e T).obj (op n) = towerRings e T n :=
  rfl

/-- The map from the `(n + 1)`-st to the `n`-th term of the inverse system is the restriction
`Γ(Wₙ₊₁, 𝒪) ⟶ Γ(Wₙ, 𝒪)`. -/
@[simp]
theorem towerRingsSystem_map_succ (n : ℕ) :
    (towerRingsSystem e T).map (homOfLE (Nat.le_succ n)).op = towerRingsTransition e T n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-! ### Covering families -/

/-- For a covering family `Eᵢ ⟶ W` of affine charts, the lifts `(Eᵢ)ₙ ⟶ Wₙ` are jointly
surjective. -/
theorem jointlySurjective_towerScheme_of_isCovering (n : ℕ) {W : AffineEtale B S hS F}
    (E : PreZeroHypercover.{u + 1} W) (hE : AffineEtale.IsCovering B S hS F ⟨W, E⟩) :
    ∀ x : (towerScheme e T n).obj W, ∃ i, ∃ y : (towerScheme e T n).obj (E.X i),
      (towerScheme e T n).map (E.f i) y = x := by
  have hcov := (Scheme.presieve₀_mem_precoverage_iff
    ((E.map (AffineEtale.toSchemes B S hS F)).map B.inclusion)).mp hE.1.2
  refine T.lift_jointlySurjective n (fun i ↦ (representedAffineChartEtale e).map (E.f i))
    fun x ↦ ?_
  obtain ⟨i, y, hy⟩ := hcov.1 x
  exact ⟨i, y, hy⟩

/-- The lift `Wₙ ⟶ W'ₙ` of a morphism of affine charts `W ⟶ W'` is étale. -/
instance etale_towerScheme_map (n : ℕ) {W W' : AffineEtale B S hS F} (g : W ⟶ W') :
    Etale ((towerScheme e T n).map g) :=
  inferInstanceAs (Etale ((towerLift e T n).map g).left)

/-! ### The sheaf condition -/

/-- The presheaf `W ↦ Γ(Wₙ, 𝒪)` is a sheaf of sets on the affine étale site of `F`. -/
theorem isSheaf_towerRings_forget (n : ℕ) :
    Presieve.IsSheaf (AffineEtale.topology B S hS F)
      (towerRings e T n ⋙ CategoryTheory.forget CommRingCat.{u}) := by
  have hM :=
    Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_covers'.{u, u + 1, u, u + 1, u, u + 1}
      (towerScheme e T n) (towerRings e T n)
      (fun {U} E hfin hE ↦ by
        have _ := hfin
        obtain ⟨hcov, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff
          (E.map (towerScheme e T n))).mp hE
        have _ : ∀ i, Flat ((towerScheme e T n).map (E.f i)) := hfl
        exact Scheme.faithfullyFlat_pi_appTop (fun i ↦ (towerScheme e T n).obj (E.X i))
          (fun i ↦ (towerScheme e T n).map (E.f i)) (fun x ↦ by
            obtain ⟨i, y, hy⟩ := hcov x
            exact ⟨i, y, hy⟩))
      (fun {X Y Z P fst snd a b} h ↦ by
        have (W : AffineEtale B S hS F) : IsAffine (unop ((towerScheme e T n).op.obj (op W))) :=
          isAffine_towerScheme_obj e T n W
        exact isPushout_appTop_of_isPullback (Functor.map_isPullback (towerScheme e T n) h))
      (Stacks.PresheafOfModules.largeUnit.{u + 1, u, u, u + 1} (towerRings e T n))
      (fun f ↦ Stacks.PresheafOfModules.isIso_restrictionBaseChange_largeUnit _ f)
      (AffineEtale.precoverage B S hS F)
      (fun {U P} hP ↦ by
        obtain ⟨E, rfl, hE⟩ := (AffineEtale.mem_precoverage_iff B S hS F).mp hP
        refine ⟨E, rfl, hE.2, (Scheme.presieve₀_mem_precoverage_iff _).mpr
          ⟨fun x ↦ ?_, fun i ↦ (inferInstance : Flat ((towerScheme e T n).map (E.f i)))⟩⟩
        obtain ⟨i, y, hy⟩ := jointlySurjective_towerScheme_of_isCovering e T n E hE x
        exact ⟨i, y, hy⟩)
  have h₁ : Presieve.IsSheaf (AffineEtale.topology B S hS F)
      ((Stacks.PresheafOfModules.largeUnit.{u + 1, u, u, u + 1} (towerRings e T n)).presheaf ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      (GrothendieckTopology.HasSheafCompose.isSheaf _ hM)
  exact (Presieve.isSheaf_comp_uliftFunctor_iff (AffineEtale.topology B S hS F)).1 h₁

end AlgebraicGeometry.Space

end
