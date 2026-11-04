module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationTriangle
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite type locally constant sheaves of modules

On a site `(C, J)` and for a ring `Λ`, a sheaf of `Λ`-modules is *locally constant of finite
type* when every object of the site is covered by objects on which the sheaf becomes the constant
sheaf attached to a finitely generated `Λ`-module. This file states that condition at the module
universe `max u v w`.

## Main definitions

* `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf`: the condition above.

## Main results

* `Stacks.ConstantSheaf.isClosedUnderIsomorphisms_isFiniteTypeLocallyConstantModuleSheaf`:
  the condition is invariant under isomorphism.
* `Stacks.ConstantSheaf.overPullback_eq_comp`: the slice-of-slice comparison
  `j_V^{-1} = j^{-1} ∘ j_U^{-1}`, restriction to `C/V` being restriction to `C/U` followed by
  relocalization along `V/U`.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
-/

@[expose] public section

open CategoryTheory Limits

namespace Stacks.ConstantSheaf

universe v u w r

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type r) [Ring Λ]

/-- A sheaf of `Λ`-modules `F` is locally constant of finite type when every object `U` of the
site has a covering family `V i ⟶ U` such that the restriction of `F` to each `C/V i` is
isomorphic to the constant sheaf attached to a finitely generated `Λ`-module. -/
@[sga "4 IX 2.0"]
def IsFiniteTypeLocallyConstantModuleSheaf (F : Sheaf J (ModuleCat.{max u v w} Λ)) : Prop :=
  ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ J U ∧ ∀ i,
      ∃ E : ModuleCat.{max u v w} Λ, ModuleCat.isFG Λ E ∧
        Nonempty ((constantSheaf (J.over (V i)) (ModuleCat.{max u v w} Λ)).obj E ≅
          (J.overPullback (ModuleCat.{max u v w} Λ) (V i)).obj F)

/-- Being locally constant of finite type is invariant under isomorphism. -/
instance isClosedUnderIsomorphisms_isFiniteTypeLocallyConstantModuleSheaf :
    ObjectProperty.IsClosedUnderIsomorphisms
      (IsFiniteTypeLocallyConstantModuleSheaf.{v, u, w} J Λ) where
  of_iso {F F'} e hF U := by
    obtain ⟨I, V, f, hcov, h⟩ := hF U
    exact ⟨I, V, f, hcov, fun i ↦ (h i).imp fun _ ⟨hE, ⟨φ⟩⟩ ↦
      ⟨hE, ⟨φ ≪≫ (J.overPullback (ModuleCat.{max u v w} Λ) (V i)).mapIso e⟩⟩⟩

/-- Restriction to `C/V` is restriction to `C/U` followed by relocalization along `V/U`, as a
strict equality of functors, for sheaves with values in any category. -/
theorem overPullback_eq_comp (A : Type*) [Category A] {U V : C} (f : V ⟶ U) :
    J.overPullback A V = J.overPullback A U ⋙ J.overMapPullback A f :=
  _root_.inverseImage_eq J f A

end Stacks.ConstantSheaf

end
