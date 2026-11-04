module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfDescent
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Coskeletal

/-!
# Local lifts along an fppf hypercovering

Let `a : U → X` be an fppf hypercovering of an algebraic space (Section 0DH4 of the Stacks
project). This file reads off the two consequences of the first three conditions which descent
along `a` uses: two morphisms `Y ⟶ U_0` agreeing over `X` are, after a flat, locally finitely
presented, surjective base change of `Y`, the two vertices of a morphism to `U_1`; and three
morphisms `Y ⟶ U_1` bounding a triangle are, after such a base change, the three edges of a
morphism to `U_2`. The second is surjectivity of the matching morphism
`U_2 → (cosk_1 sk_1 U)_2`, read through the limit description of the coskeleton.

## Main results

* `AlgebraicGeometry.Space.IsFppfHypercovering.exists_edge`: local lifts of pairs of vertices.
* `AlgebraicGeometry.Space.IsFppfHypercovering.exists_triangle`: local lifts of triangles.

## References

* [Stacks Project, Tag 0DH4](https://stacks.math.columbia.edu/tag/0DH4)
* [Stacks Project, Tag 0DER](https://stacks.math.columbia.edu/tag/0DER)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject.Truncated

universe u

namespace AlgebraicGeometry.Space.IsFppfHypercovering

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)} (hyp : IsFppfHypercovering A)
include hyp

/-- **Edges of an fppf hypercovering.** Two morphisms `Y ⟶ U_0` with the same composite to `X`
are, after a flat, locally finitely presented, surjective base change of `Y`, the two vertices
of a morphism to `U_1`. -/
theorem exists_edge {Y : AlgebraicSpaces B S hS} (y₁ y₂ : Y ⟶ A.left.obj (op ⦋0⦌))
    (w : y₁ ≫ A.hom.app (op ⦋0⦌) = y₂ ≫ A.hom.app (op ⦋0⦌)) :
    ∃ (Y' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (t : Y' ⟶ A.left.obj (op ⦋1⦌)),
      fppfSurjective B S hS g ∧ t ≫ A.left.δ 1 = g ≫ y₁ ∧ t ≫ A.left.δ 0 = g ≫ y₂ := by
  let ℓ : Y ⟶ pullback (A.hom.app (op ⦋0⦌)) (A.hom.app (op ⦋0⦌)) := pullback.lift y₁ y₂ w
  have sq := IsPullback.of_hasPullback (SimplicialObject.Augmented.firstMatchingArrow A).hom ℓ
  refine ⟨_, pullback.snd _ _, pullback.fst _ _, fppfSurjective_of_isPullback sq hyp.map_one,
    ?_, ?_⟩
  · rw [← SimplicialObject.Augmented.firstMatchingArrow_hom_fst, ← Category.assoc,
      pullback.condition, Category.assoc, pullback.lift_fst]
  · rw [← SimplicialObject.Augmented.firstMatchingArrow_hom_snd, ← Category.assoc,
      pullback.condition, Category.assoc, pullback.lift_snd]

/-- **Triangles of an fppf hypercovering.** Three morphisms `Y ⟶ U_1` bounding a triangle are,
after a flat, locally finitely presented, surjective base change of `Y`, the three edges of a
morphism to `U_2`. -/
theorem exists_triangle {Y : AlgebraicSpaces B S hS} (e₀₁ e₀₂ e₁₂ : Y ⟶ A.left.obj (op ⦋1⦌))
    (h₁ : e₀₁ ≫ A.left.δ 1 = e₀₂ ≫ A.left.δ 1) (h₂ : e₀₁ ≫ A.left.δ 0 = e₁₂ ≫ A.left.δ 1)
    (h₃ : e₀₂ ≫ A.left.δ 0 = e₁₂ ≫ A.left.δ 0) :
    ∃ (Y' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (σ : Y' ⟶ A.left.obj (op ⦋2⦌)),
      fppfSurjective B S hS g ∧ σ ≫ A.left.δ 2 = g ≫ e₀₁ ∧ σ ≫ A.left.δ 1 = g ≫ e₀₂ ∧
        σ ≫ A.left.δ 0 = g ≫ e₁₂ := by
  let : HasFiniteLimits (Over A.right) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : ∀ F : SimplicialObject.Truncated (Over A.right) 1,
      (SimplexCategory.Truncated.inclusion 1).op.HasPointwiseRightKanExtension F := fun F =>
    (hasPointwiseRightKanExtension_of_hasBinaryProducts_or_hasFiniteConnectedLimits
        (C := Over A.right)).2 (fun _ ↦ inferInstance) (0 + 1) (by omega) F
  let L := (SimplexCategory.Truncated.inclusion 1).op
  let Ut := (SimplicialObject.truncation 1).obj (SimplicialObject.Augmented.over A)
  let η := ((SimplicialObject.coskAdj 1).unit.app (SimplicialObject.Augmented.over A)).app
    (op ⦋2⦌)
  have leg : ∀ f : StructuredArrow (op ⦋2⦌) L,
      η ≫ ((Functor.RightExtension.mk _ (L.ranCounit.app Ut)).coneAt (op ⦋2⦌)).π.app f =
        (SimplicialObject.Augmented.over A).map f.hom := by
    intro f
    have k₁ := ((SimplicialObject.coskAdj 1).unit.app
      (SimplicialObject.Augmented.over A)).naturality f.hom
    have k₂ := L.ranCounit_app_app_ranAdjunction_unit_app_app (H := Over A.right)
      (SimplicialObject.Augmented.over A) f.right
    have k₃ := congrArg (fun g => g ≫ (L.ranCounit.app Ut).app f.right) k₁
    exact ((Category.assoc _ _ _).symm.trans k₃.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => (SimplicialObject.Augmented.over A).map f.hom ≫ g) k₂).trans
          (Category.comp_id _)))
  have hδ : ∀ j : Fin 2, A.left.δ j ≫ A.hom.app (op ⦋0⦌) = A.hom.app (op ⦋1⦌) :=
    fun j => EtaleComponent.hom_app_comp (A := A) (SimplexCategory.δ j)
  let T : Over A.right := Over.mk (e₀₁ ≫ A.hom.app (op ⦋1⦌))
  let fe : ∀ e : Y ⟶ A.left.obj (op ⦋1⦌), e ≫ A.hom.app (op ⦋1⦌) = e₀₁ ≫ A.hom.app (op ⦋1⦌) →
      (T ⟶ Ut.obj (op ⟨⦋1⦌, le_rfl⟩)) := fun e he => Over.homMk e he
  have he₀₂ : e₀₂ ≫ A.hom.app (op ⦋1⦌) = e₀₁ ≫ A.hom.app (op ⦋1⦌) := by
    rw [← hδ 1, ← Category.assoc, ← h₁, Category.assoc]
  have he₁₂ : e₁₂ ≫ A.hom.app (op ⦋1⦌) = e₀₁ ≫ A.hom.app (op ⦋1⦌) := by
    simpa only [Category.assoc, hδ] using (congrArg (· ≫ A.hom.app (op ⦋0⦌)) h₂).symm
  let f : Fin 3 → (T ⟶ Ut.obj (op ⟨⦋1⦌, le_rfl⟩)) :=
    ![fe e₁₂ he₁₂, fe e₀₂ he₀₂, fe e₀₁ rfl]
  have hf : ∀ i j : Fin 2, i ≤ j →
      f i.castSucc ≫ Ut.map (SimplexCategory.Truncated.δ 1 j (Nat.le_succ 0) le_rfl).op =
        f j.succ ≫ Ut.map (SimplexCategory.Truncated.δ 1 i (Nat.le_succ 0) le_rfl).op := by
    intro i j hij
    apply Over.OverMorphism.ext
    fin_cases i <;> fin_cases j
    exacts [h₃.symm, h₂.symm, absurd hij (by decide), h₁.symm]
  obtain ⟨π, hπ, -⟩ := (SimplicialObject.Truncated.existsUnique_cone_app_δ_eq_iff Ut T f).2 hf
  let hlim := L.isPointwiseRightKanExtensionRanCounit Ut (op ⦋2⦌)
  let ℓ := hlim.lift ⟨T, π⟩
  have sq := IsPullback.of_hasPullback ((Over.forget A.right).map η) ℓ.left
  have key : ∀ i : Fin 3, pullback.fst ((Over.forget A.right).map η) ℓ.left ≫ A.left.δ i =
      pullback.snd ((Over.forget A.right).map η) ℓ.left ≫ (f i).left := by
    intro i
    let gi := StructuredArrow.mk (Y := op (⟨⦋1⦌, le_rfl⟩ : SimplexCategory.Truncated 1))
      (T := L) (SimplexCategory.δ i).op
    have e₁ : η.left ≫
        (((Functor.RightExtension.mk _ (L.ranCounit.app Ut)).coneAt (op ⦋2⦌)).π.app gi).left =
        A.left.δ i := congrArg Over.Hom.left (leg gi)
    have e₂ : ℓ.left ≫
        (((Functor.RightExtension.mk _ (L.ranCounit.app Ut)).coneAt (op ⦋2⦌)).π.app gi).left =
        (f i).left := congrArg Over.Hom.left ((hlim.fac ⟨T, π⟩ gi).trans (hπ i))
    have e₄ := pullback.condition (f := (Over.forget A.right).map η) (g := ℓ.left)
    exact ((congrArg (_ ≫ ·) e₁).symm.trans (Category.assoc _ _ _).symm).trans
      ((congrArg (· ≫ _) e₄).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) e₂)))
  exact ⟨_, pullback.snd _ _, pullback.fst _ _,
    fppfSurjective_of_isPullback sq (hyp.matching 1 le_rfl), key 2, key 1, key 0⟩

end AlgebraicGeometry.Space.IsFppfHypercovering
