module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveEquivalenceOver
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence


/-!
# The terms of the relative Čech nerve of a 1-morphism of algebraic stacks are algebraic stacks

For a 1-morphism `c : 𝒰 ⟶ 𝒳` of algebraic stacks over `S`, every term `𝒰ₙ` of the relative Čech
nerve of `c` — the category `Stacks.RelativeCech.Tuple` of `n + 1` objects of `𝒰` over a common
object of `𝒳`, over the base through its projection to `𝒳` — is an algebraic stack, and the
projection `𝒰ₙ ⟶ 𝒳` is a 1-morphism of algebraic stacks. This is what lets statements about
1-morphisms of algebraic stacks be applied to the terms of the relative Čech spectral sequence of
Stacks 072G, whose first page is indexed by them.

## Main definitions

* `AlgebraicGeometry.Stack.cechNerveStack`: the degree `n` term, as an algebraic stack.
* `AlgebraicGeometry.Stack.cechNerveStackProjection`: its projection to `𝒳`, whose functor is
  `Stacks.RelativeCech.Tuple.projection` on the nose.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_tuple`: the terms are algebraic stacks, by induction
  on the degree from `𝒰₀ ≃ 𝒰` and `𝒰_{n + 1} ≃ 𝒰 ×_𝒳 𝒰ₙ` over the base (Stacks 06X3), Stacks 04TF
  and Stacks 03YQ.

## References

* [Stacks Project, Tag 06X3](https://stacks.math.columbia.edu/tag/06X3)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (c : 𝒰 ⟶ 𝒳)

local notation "Tp" => Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
  (CatFiberedInGroupoids.homFunctor c.hom)

/-- The source of a 1-morphism of algebraic stacks, presented by the composite of the
morphism's functor with the structure functor of the target, is an algebraic stack. -/
theorem isAlgebraicStack_ofFunctor_homFunctor_comp :
    IsAlgebraicStack.{u, w} B S hS
      (BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor c.hom ⋙ 𝒳.val.val.p)) := by
  have h : BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor c.hom ⋙ 𝒳.val.val.p) =
      𝒰.val.val := by
    rw [CatFiberedInGroupoids.homFunctor_comp_p]
    rfl
  rw [h]
  exact 𝒰.property

/-- Being an algebraic stack transfers along an equivalence over the big fppf site of the
structure functors. -/
private theorem isAlgebraicStack_ofFunctor_of_equivalenceOver
    {D₁ D₂ : Type (u + 1)} [Category.{u} D₁] [Category.{u} D₂]
    {p₁ : D₁ ⥤ BigFppfOver B S hS} {p₂ : D₂ ⥤ BigFppfOver B S hS}
    (e : StacksRepresentableCFG.EquivalenceOver p₁ p₂)
    (h : IsAlgebraicStack.{u, w} B S hS (BasedCategory.ofFunctor p₁)) :
    IsAlgebraicStack.{u, w} B S hS (BasedCategory.ofFunctor p₂) :=
  (isAlgebraicStack_iff_of_equivalence B S hS
    (StacksRepresentableCFG.EquivalenceOver.toBasedEquivalence
      (𝒳 := BasedCategory.ofFunctor p₁) (𝒴 := BasedCategory.ofFunctor p₂) e)).1 h

/-- **Every term of the relative Čech nerve of a 1-morphism of algebraic stacks is an algebraic
stack.** The degree `0` term is the source and the degree `n + 1` term is the 2-fibre product of
the source with the degree `n` term over the target (Stacks 06X3), and 2-fibre products of
algebraic stacks are algebraic stacks (Stacks 04TF); being an algebraic stack is invariant under
equivalence over the base (Stacks 03YQ). -/
theorem isAlgebraicStack_tuple (n : ℕ) :
    IsAlgebraicStack.{u, w} B S hS (BasedCategory.ofFunctor (Tp n ⋙ 𝒳.val.val.p)) := by
  induction n with
  | zero =>
    exact isAlgebraicStack_ofFunctor_of_equivalenceOver B S hS
      (Stacks.RelativeCech.tupleZeroEquivalenceOver 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor c.hom))
      (isAlgebraicStack_ofFunctor_homFunctor_comp B S hS c)
  | succ n ih =>
    obtain ⟨_, h𝒳stack, h𝒳diag, -⟩ := 𝒳.property
    exact isAlgebraicStack_ofFunctor_of_equivalenceOver B S hS
      (Stacks.RelativeCech.tupleSuccEquivalenceOver 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor c.hom) n)
      (isAlgebraicStack_twoFibreProduct B S hS
        (BasedCategory.ofFunctor (CatFiberedInGroupoids.homFunctor c.hom ⋙ 𝒳.val.val.p))
        (BasedCategory.ofFunctor (Tp n ⋙ 𝒳.val.val.p)) 𝒳.val.val
        ⟨CatFiberedInGroupoids.homFunctor c.hom, rfl⟩ ⟨Tp n, rfl⟩ h𝒳stack h𝒳diag
        (isAlgebraicStack_ofFunctor_homFunctor_comp B S hS c) ih)

/-- **The degree `n` term of the relative Čech nerve of a 1-morphism `c : 𝒰 ⟶ 𝒳` of algebraic
stacks, as an algebraic stack.** Its underlying category is the category
`Stacks.RelativeCech.Tuple` of `n + 1` objects of `𝒰` over a common object of `𝒳`, and its
structure functor is the projection to `𝒳` followed by the structure functor of `𝒳`; it is the
`(n + 1)`-fold 2-fibre product `𝒰 ×_𝒳 ⋯ ×_𝒳 𝒰`. -/
def cechNerveStack (n : ℕ) : AlgebraicStacks.{u, w} B S hS :=
  ⟨⟨BasedCategory.ofFunctor (Tp n ⋙ 𝒳.val.val.p),
    (isAlgebraicStack_tuple B S hS c n).elim fun h _ => h⟩, isAlgebraicStack_tuple B S hS c n⟩

/-- The projection of the degree `n` term of the relative Čech nerve of `c : 𝒰 ⟶ 𝒳` to `𝒳`, as
a 1-morphism of algebraic stacks. Its functor is `Stacks.RelativeCech.Tuple.projection`. -/
def cechNerveStackProjection (n : ℕ) : cechNerveStack B S hS c n ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom ⟨Tp n, rfl⟩)

/-- The functor of the projection of the relative Čech nerve is the projection of tuples. -/
@[simp]
theorem homFunctor_cechNerveStackProjection (n : ℕ) :
    CatFiberedInGroupoids.homFunctor (cechNerveStackProjection B S hS c n).hom = Tp n := rfl

end AlgebraicGeometry.Stack
