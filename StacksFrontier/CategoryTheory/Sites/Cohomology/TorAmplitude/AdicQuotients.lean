module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TowerOfShortExactSequences
public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientModuleTower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru

/-!
# Derived tensor products with the quotients of the structure sheaf by the powers of an ideal

Let `(C, O)` be a ringed site, `I ⊆ O` a sheaf of ideals and `K` an object of `D(O)`. The
quotients `O/Iⁿ` form a tower of short exact sequences `0 → Iⁿ/Iⁿ⁺¹ → O/Iⁿ⁺¹ → O/Iⁿ → 0`
beginning at `O/I⁰ = 0`, so an upper cohomological bound shared by all the derived tensor
products `K ⊗^L_O Iⁿ/Iⁿ⁺¹` bounds the whole family `K ⊗^L_O O/Iⁿ` uniformly.

## Main results

* `Stacks.SheafOfModules.isSplitEpi_ι_top`: the inclusion of the largest submodule of a sheaf of
  modules is a split epimorphism.
* `Stacks.Sites.isZero_adicQuotientModule_zero`: `O/I⁰` is the zero sheaf of modules.
* `Stacks.Sites.isUniformlyBoundedAbove_tensor_adicQuotientModule`: one upper bound for the
  derived tensor products of `K` with the graded pieces of the filtration by the powers of a
  sheaf of ideals is a uniform upper bound for the derived tensor products of `K` with the
  quotients `O/Iⁿ`.

## Implementation notes

The zeroth stage of the tower is zero because the zeroth power of a sheaf of ideals is the whole
structure sheaf, whose inclusion is split by the factorization of the identity through it; the
derived tensor product with a zero module vanishes, which is the base case of the induction along
the tower.

The graded piece `Iⁿ/Iⁿ⁺¹` is the left-hand term of the `n`-th stage of the tower on the nose, so
the hypothesis is stated for the graded pieces and transported along
`Stacks.Sites.adicQuotientShortComplexX₁Iso`.

Sheaves of ideals on a ringed site are the submodules of its free rank-one sheaf of modules, so
naming their type requires the structure sheaf to be readable as a sheaf of not necessarily
commutative rings. That holds for every ringed site and is supplied here as a section-local
instance; it is needed only to write the type of a sheaf of ideals down.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d u₁ v₁

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {M : _root_.SheafOfModules.{v} R}

/-- **The inclusion of the largest submodule of a sheaf of modules is a split epimorphism.**
Every section of the sheaf is a section of that submodule, so the identity factors through the
inclusion. -/
lemma isSplitEpi_ι_top : IsSplitEpi (⊤ : M.Submodule).ι :=
  IsSplitEpi.mk'
    ⟨(⊤ : M.Submodule).factorThru (𝟙 M) (fun _ _ => by simp [toSubmodule_top]),
      _root_.SheafOfModules.Submodule.factorThru_ι _ _ _⟩

/-- The inclusion of the largest submodule of a sheaf of modules is an epimorphism. -/
lemma epi_ι_top : Epi (⊤ : M.Submodule).ι :=
  let := isSplitEpi_ι_top (M := M)
  inferInstance

end Stacks.SheafOfModules

namespace Stacks.Sites

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (I : IdealSubsheaf.{v, u, w} X.O)

/-- **The quotient of the structure sheaf by the zeroth power of a sheaf of ideals is zero**: the
zeroth power is the whole structure sheaf. -/
lemma isZero_adicQuotientModule_zero : IsZero (adicQuotientModule I 0) := by
  have key : ∀ N : IdealSubsheaf.{v, u, w} X.O, N = ⊤ → IsZero (cokernel N.ι) := by
    rintro N rfl
    have : Epi (⊤ : IdealSubsheaf.{v, u, w} X.O).ι := Stacks.SheafOfModules.epi_ι_top
    exact isZero_cokernel_of_epi _
  exact key _ (idealPow_zero I)

section Derived

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, v, w, d} X)
  (K : RingedSite.DerivedModules.{u, v, w, d} X)

/-- The derived tensor product of an object of `D(O)` with `O/I⁰` vanishes, so it is bounded
above by every integer. -/
lemma isBoundedAboveBy_tensor_adicQuotientModule_zero (b : ℤ) :
    Stacks.DerivedCategory.IsBoundedAboveBy
      ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj
          (adicQuotientModule I 0))) b :=
  fun _ _ => Functor.map_isZero _ (Functor.map_isZero _
    (Functor.map_isZero _ (isZero_adicQuotientModule_zero I)))

/-- **A uniform upper bound for the derived tensor products with the quotients by the powers of a
sheaf of ideals.** If `K ⊗^L_O Iⁿ/Iⁿ⁺¹` is bounded above by `b` for every `n`, then the family
`K ⊗^L_O O/Iⁿ` is uniformly bounded above. -/
theorem isUniformlyBoundedAbove_tensor_adicQuotientModule (b : ℤ)
    (h : ∀ n : ℕ, Stacks.DerivedCategory.IsBoundedAboveBy
      ((T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj
          (adicGradedPiece I n))) b) :
    Stacks.DerivedCategory.IsUniformlyBoundedAbove
      (fun n : ℕ => (T.tensor.obj K).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj
          (adicQuotientModule I n))) :=
  Stacks.SheafOfModules.DerivedTensorProduct.isUniformlyBoundedAbove_tensor_of_tower T K
    (adicQuotientModule I) b (adicQuotientShortComplex I) (adicQuotientShortComplex_shortExact I)
    (adicQuotientShortComplexX₂Iso I) (adicQuotientShortComplexX₃Iso I)
    (isBoundedAboveBy_tensor_adicQuotientModule_zero I T K b)
    (fun n => (h n).of_iso ((T.tensor.obj K).mapIso
      ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).mapIso
        (adicQuotientShortComplexX₁Iso I n).symm)))

end Derived

end Stacks.Sites

end
