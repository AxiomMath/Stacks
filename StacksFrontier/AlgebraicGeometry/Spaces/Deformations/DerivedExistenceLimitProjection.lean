module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceDerivedLimit

/-!
# The projections of the derived limit of Situation 0DIK and their adjoints

In Situation [Stacks, Tag 0DIK], with `K = DQ_X(R lim_{D(𝒪_X)} Kₙ)` as in [Stacks, Tag 0DIL],
we construct the projections `K ⟶ Rjₙ,* Kₙ` and their adjoints `τₙ : Ljₙ^* K ⟶ Kₙ`.

All names below are in the namespace `AlgebraicGeometry.Space.DerivedExistenceSystem`.

## Main definitions

* `stageAdjunction`: `Ljₙ^* ⊣ Rjₙ,*` with `Rjₙ,*` the exact direct image `stagePushforward` along
  the closed immersion `jₙ : Xₙ ⟶ X`.
* `derivedLimit`, `derivedLimitProjection`: a chosen `R lim_{D(𝒪_X)} Kₙ` and its projections to
  the terms of the tower.
* `coheratorLimit`: `K = DQ_X(R lim Kₙ)`, for a coherator `DQ_X` (a right adjoint of
  `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`); `coheratorLimitProjection n : K ⟶ Rjₙ,* Kₙ`, the counit followed by the
  projection; and `coheratorLimitPullbackMap n : Ljₙ^* K ⟶ Kₙ`, its adjoint `τₙ`.
* `stageAdjoint`: the adjoint `Ljₙ^* E ⟶ Kₙ` of any `E ⟶ Rjₙ,* Kₙ`.

## Main results

* `isDerivedLimit_derivedLimit`: `derivedLimit` is a derived limit of the tower `(Rjₙ,* Kₙ)`.
* `coheratorLimitProjection_comp_map`: the projections `K ⟶ Rjₙ,* Kₙ` are compatible with the
  transition maps of the tower.

## Implementation notes

`stageAdjunction` is the ringed-topos adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6] with its right
adjoint identified with the exact direct image through `rightDerivedIsoOfFactors`.

## References

* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace DerivedExistenceSystem

variable (D : DerivedExistenceSystem.{u})

/-- The derived pullback `Ljₙ^* : D(𝒪_X) ⥤ D(𝒪_{Xₙ})` along `jₙ : Xₙ ⟶ X`. -/
abbrev stageDerivedPullback (n : ℕ) :
    D.limitDerivedCategory ⥤
      derivedCategoryAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n :=
  smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)

/-- The ringed-topos derived pushforward `Rjₙ,*` of Stacks 07A5. -/
abbrev stageToposDerivedPushforward (n : ℕ) :
    derivedCategoryAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n ⥤
      D.limitDerivedCategory :=
  haveI : IsGrothendieckAbelian.{u} (D.toposModules (D.stage n)) :=
    isGrothendieckAbelian_modules D.B (limitBase D.system) D.containsLimitBase _ (D.stage n).2
  Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))

/-- `Ljₙ^* ⊣ Rjₙ,*`, ringed-topos form. -/
def stageToposDerivedAdjunction (n : ℕ) :
    D.stageDerivedPullback n ⊣ D.stageToposDerivedPushforward n :=
  haveI : IsGrothendieckAbelian.{u} (D.toposModules (D.stage n)) :=
    isGrothendieckAbelian_modules D.B (limitBase D.system) D.containsLimitBase _ (D.stage n).2
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
    (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))

/-- Degreewise direct image along `jₙ` followed by localization. -/
abbrev stageHomotopyPushforward (n : ℕ) :
    HomotopyCategory (D.toposModules (D.stage n)) (ComplexShape.up ℤ) ⥤ D.limitDerivedCategory :=
  Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))

/-- The derivation unit of the ringed-topos `Rjₙ,*`. -/
def stageToposUnit (n : ℕ) :
    D.stageHomotopyPushforward n ⟶ D.stageQh n ⋙ D.stageToposDerivedPushforward n :=
  letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
  letI := HasDerivedCategory.standard (D.toposModules D.X.left)
  haveI : IsGrothendieckAbelian.{u} (D.toposModules (D.stage n)) :=
    isGrothendieckAbelian_modules D.B (limitBase D.system) D.containsLimitBase _ (D.stage n).2
  (Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy
    (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt
        D.X n))).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ))

/-- The ringed-topos `Rjₙ,*` is a right derived functor of degreewise direct image along `jₙ`,
with unit `stageToposUnit n`. -/
instance isRightDerivedFunctor_stageToposUnit (n : ℕ) :
    (D.stageToposDerivedPushforward n).IsRightDerivedFunctor (D.stageToposUnit n)
      (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) := by
  let := HasDerivedCategory.standard (D.toposModules (D.stage n))
  let := HasDerivedCategory.standard (D.toposModules D.X.left)
  have : IsGrothendieckAbelian.{u} (D.toposModules (D.stage n)) :=
    isGrothendieckAbelian_modules D.B (limitBase D.system) D.containsLimitBase _ (D.stage n).2
  have := Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy_hasRightDerivedFunctor
    (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
  have : (Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy
      (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt
          D.X n))).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) :=
    Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _
  unfold stageToposUnit
  infer_instance

/-- The defining isomorphism of the exact direct image `Rjₙ,*` on the homotopy category. -/
def stagePushforwardFactorsh (n : ℕ) :
    D.stageQh n ⋙ D.stagePushforward n ≅ D.stageHomotopyPushforward n :=
  letI := HasDerivedCategory.standard (D.toposModules (D.stage n))
  letI := HasDerivedCategory.standard (D.toposModules D.X.left)
  haveI := D.additive_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteLimits_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  haveI := D.preservesFiniteColimits_toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (D.toDerivedExistenceSituation.closedSpaceProjection n)
  Functor.mapDerivedCategoryFactorsh (D.toposPushforward
    (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))

/-- **The ringed-topos `Rjₙ,*` is the exact direct image along `jₙ`.** -/
def stageToposDerivedPushforwardIso (n : ℕ) :
    D.stageToposDerivedPushforward n ≅ D.stagePushforward n :=
  rightDerivedIsoOfFactors (D.stageQh n)
    (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) _ _
    (D.stageToposUnit n) (D.stagePushforwardFactorsh n)

/-- **`Ljₙ^* ⊣ Rjₙ,*`** with `Rjₙ,*` the exact direct image (Stacks 07A6). -/
def stageAdjunction (n : ℕ) : D.stageDerivedPullback n ⊣ D.stagePushforward n :=
  (D.stageToposDerivedAdjunction n).ofNatIsoRight (D.stageToposDerivedPushforwardIso n)

/-- The adjoint `Ljₙ^* E ⟶ Kₙ` of a morphism `E ⟶ Rjₙ,* Kₙ`. -/
def stageAdjoint (n : ℕ) {E : D.limitDerivedCategory} (f : E ⟶ D.towerObj n) :
    (D.stageDerivedPullback n).obj E ⟶ D.K n :=
  ((D.stageAdjunction n).homEquiv _ _).symm f

/-- The adjunction `Ljₙ^* ⊣ Rjₙ,*` sends `stageAdjoint n f` back to `f`. -/
lemma stageAdjunction_homEquiv_stageAdjoint (n : ℕ) {E : D.limitDerivedCategory}
    (f : E ⟶ D.towerObj n) : (D.stageAdjunction n).homEquiv _ _ (D.stageAdjoint n f) = f :=
  Equiv.apply_symm_apply _ _

/-! ### The derived limit and its projections -/

/-- A chosen derived limit `R lim_{D(𝒪_X)} Kₙ` of the tower `(Rjₙ,* Kₙ)`. -/
def derivedLimit : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left :=
  D.exists_isDerivedLimit_spaceTower.choose

/-- `derivedLimit` is a derived limit of the tower `(Rjₙ,* Kₙ)`. -/
theorem isDerivedLimit_derivedLimit : IsDerivedLimit D.spaceTower D.derivedLimit :=
  D.exists_isDerivedLimit_spaceTower.choose_spec

/-- The map `R lim Kₙ ⟶ ∏ Rjₙ,* Kₙ` of the chosen derived limit triangle. -/
def derivedLimitToProduct : D.derivedLimit ⟶ ∏ᶜ fun n : ℕ => D.spaceTower.obj ⟨n⟩ :=
  D.isDerivedLimit_derivedLimit.choose

/-- `derivedLimitToProduct` is the first map of a distinguished triangle
`R lim Kₙ ⟶ ∏ Rjₙ,* Kₙ ⟶ ∏ Rjₙ,* Kₙ ⟶ R lim Kₙ[1]` whose second map has components
`pₙ - pₙ₊₁ ≫ tₙ`, with `pₙ` the product projections and `tₙ` the transition maps of the tower. -/
theorem exists_distTriang_derivedLimitToProduct :
    ∃ δ : (∏ᶜ fun n : ℕ => D.spaceTower.obj ⟨n⟩) ⟶ D.derivedLimit⟦(1 : ℤ)⟧,
      Triangle.mk D.derivedLimitToProduct (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => D.spaceTower.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => D.spaceTower.obj ⟨n⟩) (n + 1) ≫
            D.spaceTower.map (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang _ :=
  D.isDerivedLimit_derivedLimit.choose_spec

/-- **The projection `R lim Kₙ ⟶ Rjₙ,* Kₙ`.** -/
def derivedLimitProjection (n : ℕ) : D.derivedLimit ⟶ D.spaceTower.obj ⟨n⟩ :=
  D.derivedLimitToProduct ≫ Pi.π _ n

/-- The projections are compatible with the transition maps of the tower. -/
theorem derivedLimitProjection_comp_map (n : ℕ) :
    D.derivedLimitProjection (n + 1) ≫ D.spaceTower.map (homOfLE (Nat.le_succ n)).op =
      D.derivedLimitProjection n := by
  obtain ⟨δ, hT⟩ := D.exists_distTriang_derivedLimitToProduct
  have h := comp_distTriang_mor_zero₁₂ _ hT
  have h' := congrArg (· ≫ Pi.π (fun n : ℕ => D.spaceTower.obj ⟨n⟩) n) h
  simp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_mor₁, Triangle.mk_mor₂,
    Category.assoc, Pi.lift_comp_π, zero_comp, Preadditive.comp_sub] at h'
  simp only [derivedLimitProjection, Category.assoc]
  exact (sub_eq_zero.1 h').symm

/-! ### `K = DQ_X(R lim Kₙ)` and `τₙ` -/

section Coherator

variable (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).FullSubcategory)
  (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)

/-- **`K = DQ_X(R lim_{D(𝒪_X)} Kₙ)`**, the object of Stacks 0DIL, for a coherator `DQ_X`. -/
def coheratorLimit :
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
      D.X.left).FullSubcategory :=
  DQ.obj D.derivedLimit

/-- **The projection `K ⟶ Rjₙ,* Kₙ`**: the counit `K ⟶ R lim Kₙ` followed by the projection. -/
def coheratorLimitProjection (n : ℕ) :
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
      (D.coheratorLimit DQ) ⟶ D.spaceTower.obj ⟨n⟩ :=
  adj.counit.app D.derivedLimit ≫ D.derivedLimitProjection n

/-- **`τₙ : Ljₙ^* K ⟶ Kₙ`**, the adjoint of the projection `K ⟶ Rjₙ,* Kₙ`. -/
def coheratorLimitPullbackMap (n : ℕ) :
    (D.stageDerivedPullback n).obj
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
        (D.coheratorLimit DQ)) ⟶ D.K n :=
  D.stageAdjoint n (D.coheratorLimitProjection DQ adj n)

/-- The projections `K ⟶ Rjₙ,* Kₙ` are compatible with the transition maps of the tower. -/
theorem coheratorLimitProjection_comp_map (n : ℕ) :
    D.coheratorLimitProjection DQ adj (n + 1) ≫ D.spaceTower.map (homOfLE (Nat.le_succ n)).op =
      D.coheratorLimitProjection DQ adj n := by
  have h := D.derivedLimitProjection_comp_map n
  unfold coheratorLimitProjection
  rw [← h]
  exact Category.assoc _ _ _

end Coherator

end DerivedExistenceSystem

end AlgebraicGeometry.Space
