module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FiniteLevelStalk
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Surjectivity on ℓ-adic stalks from surjectivity on the finite levels

Let `φ : F ⟶ G` be a morphism of ℓ-adic sheaves and `x̄` a geometric point. The ℓ-adic stalk
`F_x̄ = lim_n F_{n, x̄}` is an inverse limit of finite modules
(`Stacks.EtaleCohomology.finite_finiteLevelStalk`). If every finite-level map
`F_{n, x̄} ⟶ G_{n, x̄}` is surjective, then so is the map of ℓ-adic stalks: the fibres over a
compatible family of `G` form an inverse system of finite nonempty sets, which has a compatible
family of points (König's lemma, `nonempty_sections_of_finite_inverse_system`). Extending
scalars to `ℚ_ℓ`, the map of rational stalks is surjective as well.

## Main results

* `LAdicSheaf.surjective_stalkMap_of_surjective_finiteLevelStalkMap`: a morphism surjective on
  every finite-level stalk is surjective on the ℓ-adic stalk.
* `LAdicSheaf.surjective_rationalStalkMap_of_surjective_finiteLevelStalkMap`: a morphism
  surjective on every finite-level stalk is surjective on the rational stalk.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ}
variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

namespace LAdicSheaf

variable {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (s : GeometricPoint X.1)

/-- The fibre of the level-`n` stalk map over the level-`n` component of a compatible family. -/
abbrev stalkMapFibre (w : LAdicSheaf.stalk B X ℓ G s) (n : ℕ) : Type (u + 1) :=
  {v : finiteLevelStalk B X ℓ F s n // (finiteLevelStalkMap φ s n).hom v = w.1 n}

/-- The transition between the fibres of consecutive levels. -/
def stalkMapFibreTransition (w : LAdicSheaf.stalk B X ℓ G s) (n : ℕ) :
    stalkMapFibre φ s w (n + 1) → stalkMapFibre φ s w n := fun v =>
  ⟨LAdicSheaf.stalkTransition B X ℓ F s n v.1, by
    have h := congrArg (fun g => g.hom v.1) (finiteLevelStalkMap_transition φ s n)
    change LAdicSheaf.stalkTransition B X ℓ G s n _ =
      (finiteLevelStalkMap φ s n).hom (LAdicSheaf.stalkTransition B X ℓ F s n v.1) at h
    rw [← h]
    exact (congrArg (LAdicSheaf.stalkTransition B X ℓ G s n) v.2).trans (w.2 n)⟩

/-- The inverse system of the fibres of the finite-level stalk maps over a compatible family. -/
def stalkMapFibreSystem (w : LAdicSheaf.stalk B X ℓ G s) : ℕᵒᵖ ⥤ Type (u + 1) :=
  Functor.ofOpSequence (X := stalkMapFibre φ s w)
    (fun n => TypeCat.ofHom (stalkMapFibreTransition φ s w n))

/-- **A morphism of ℓ-adic sheaves surjective on every finite-level stalk is surjective on the
ℓ-adic stalk.** -/
theorem surjective_stalkMap_of_surjective_finiteLevelStalkMap
    (h : ∀ n, Function.Surjective (finiteLevelStalkMap φ s n).hom) :
    Function.Surjective (LAdicSheaf.stalkMap φ s) := by
  intro w
  have : ∀ j : ℕᵒᵖ, Finite ((stalkMapFibreSystem φ s w).obj j) := fun j => by
    have := finite_finiteLevelStalk B X ℓ F s j.unop
    exact Subtype.finite
  have : ∀ j : ℕᵒᵖ, Nonempty ((stalkMapFibreSystem φ s w).obj j) := fun j =>
    nonempty_subtype.mpr (h j.unop (w.1 j.unop))
  obtain ⟨σ, hσ⟩ := nonempty_sections_of_finite_inverse_system (stalkMapFibreSystem φ s w)
  refine ⟨⟨fun n => (σ (op n)).1, fun n => ?_⟩, ?_⟩
  · have h1 := hσ (homOfLE (Nat.le_succ n)).op
    rw [show (stalkMapFibreSystem φ s w).map (homOfLE (Nat.le_succ n)).op =
      TypeCat.ofHom (stalkMapFibreTransition φ s w n) from
        Functor.ofOpSequence_map_homOfLE_succ _ n] at h1
    exact congrArg Subtype.val h1
  · exact Subtype.ext (funext fun n => (σ (op n)).2)

/-- **A morphism of ℓ-adic sheaves surjective on every finite-level stalk is surjective on the
rational stalk.** -/
theorem surjective_rationalStalkMap_of_surjective_finiteLevelStalkMap
    (h : ∀ n, Function.Surjective (finiteLevelStalkMap φ s n).hom) :
    Function.Surjective (LAdicSheaf.rationalStalkMap φ s) :=
  LinearMap.baseChange_surjective _ (surjective_stalkMap_of_surjective_finiteLevelStalkMap φ s h)

end LAdicSheaf

end Stacks.EtaleCohomology

end
