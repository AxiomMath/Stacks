module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible

/-!
# Finite type locally constant module sheaves: zero object and isomorphisms

Let `J` be a Grothendieck topology on `C` and `Λ` a ring. The property of a sheaf of `Λ`-modules of
being finite type locally constant contains the zero sheaf and is closed under isomorphisms.

## Main results

* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr`: a sheaf of modules isomorphic to a
  finite type locally constant one is finite type locally constant.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_zero`: the zero sheaf of modules is finite type
  locally constant.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_isClosedUnderIsomorphisms` and
  `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_containsZero`: the same two facts as
  `ObjectProperty` instances.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u w r

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type r) [Ring Λ]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

/-- A sheaf of modules isomorphic to a finite type locally constant one is finite type locally
constant. -/
public theorem isFiniteTypeLocallyConstant_congr {F G : Sheaf J (ModuleCat.{w} Λ)} (e : F ≅ G)
    (hF : IsFiniteTypeLocallyConstant Λ J F) : IsFiniteTypeLocallyConstant Λ J G := by
  intro U
  obtain ⟨I, V, f, hf, h⟩ := hF U
  refine ⟨I, V, f, hf, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨c⟩⟩ := h i
  exact ⟨E, hE, ⟨c ≪≫ (J.overPullback (ModuleCat.{w} Λ) (V i)).mapIso e⟩⟩

/-- Being a finite type locally constant sheaf of modules is closed under isomorphisms. -/
public instance isFiniteTypeLocallyConstant_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun F : Sheaf J (ModuleCat.{w} Λ) => IsFiniteTypeLocallyConstant Λ J F) where
  of_iso e hF := isFiniteTypeLocallyConstant_congr J Λ e hF

section Zero

variable [HasSheafify J (ModuleCat.{w} Λ)]

/-- The zero sheaf of modules is finite type locally constant. -/
public theorem isFiniteTypeLocallyConstant_zero :
    IsFiniteTypeLocallyConstant Λ J (0 : Sheaf J (ModuleCat.{w} Λ)) := by
  intro U
  refine ⟨PUnit, fun _ => U, fun _ => 𝟙 _, ?_, fun _ => ?_⟩
  · apply J.superset_covering _ (J.top_mem _)
    intro W k _
    exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨PUnit.unit, k, by simp⟩
  · refine ⟨ModuleCat.of Λ PUnit.{w + 1}, ?_, ⟨?_⟩⟩
    · rw [ModuleCat.isFG_iff]
      infer_instance
    · have hone : IsZero ((constantSheaf (J.over U) (ModuleCat.{w} Λ)).obj
          (ModuleCat.of Λ PUnit.{w + 1})) :=
        Functor.map_isZero
          (Functor.const (Over U)ᵒᵖ ⋙ presheafToSheaf (J.over U) (ModuleCat.{w} Λ))
          (ModuleCat.isZero_of_subsingleton _)
      have htwo : IsZero ((J.overPullback (ModuleCat.{w} Λ) U).obj
          (0 : Sheaf J (ModuleCat.{w} Λ))) := by
        have : (J.overPullback (ModuleCat.{w} Λ) U).Additive := ⟨by intros; ext; rfl⟩
        exact Functor.map_isZero _ (isZero_zero _)
      exact hone.iso htwo

/-- The finite type locally constant sheaves of modules contain a zero object. -/
public instance isFiniteTypeLocallyConstant_containsZero :
    ObjectProperty.ContainsZero
      (fun F : Sheaf J (ModuleCat.{w} Λ) => IsFiniteTypeLocallyConstant Λ J F) where
  exists_zero := ⟨0, isZero_zero _, isFiniteTypeLocallyConstant_zero J Λ⟩

end Zero

end Stacks.ConstantSheaf

end
