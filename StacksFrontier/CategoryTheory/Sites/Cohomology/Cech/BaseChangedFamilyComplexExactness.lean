module

public import StacksFrontier.AlgebraicGeometry.CechSiteChange.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SplitFamilyComplexExactness

/-!
# The Čech complex of a base-changed family is exact in positive degrees

Let `{U_i → X}` be a family of morphisms with fixed target and let `g : W ⟶ X` be a morphism
that *factors* through one of its members, say `g = h ≫ (U_{i₀} → X)`.  Then the base-changed
family `{U_i ×_X W → W}` is **split**: the morphism `h` and the identity of `W` together lift
to a section `W ⟶ U_{i₀} ×_X W` of its `i₀`-th member — the diagonal of `h`.  By
`Stacks.CechSite.exactAt_cechComplex_of_section` the Čech complex of the base-changed family is
therefore exact in every positive degree, at every presheaf.

No comparison of complexes is involved: the base change of a family is Mathlib's
`CategoryTheory.PreZeroHypercover.pullback₁`, and the split-family theorem is applied to it
directly.

When `X` is a terminal object of the site the factorization hypothesis is automatic: any
morphism `W ⟶ U_{i₀}` factors `g` because both `g` and the composite are morphisms into a
terminal object.  That is the case recorded in
`Stacks.CechSite.exactAt_cechComplex_pullback₁_of_isTerminal`.

## Main definitions

* `Stacks.CechSite.pullback₁Section`: the diagonal section of the `i₀`-th member of the
  base-changed family.

## Main results

* `Stacks.CechSite.pullback₁Section_comp_f`: it is a section.
* `Stacks.CechSite.exactAt_cechComplex_pullback₁_of_factorsThrough`: the Čech complex of the
  base-changed family is exact in every positive degree.
* `Stacks.CechSite.exactAt_cechComplex_pullback₁_of_isTerminal`: the same with the
  factorization supplied by terminality of the target.
* `Stacks.CechObjectFamily.exactAt_cechComplexFunctor_of_sectionFromTerminal`: the split-family
  statement for a family of objects.
* `Stacks.CechObjectFamily.exactAt_cechComplexFunctor_prodRestriction_of_hom`: for a family of
  *objects* `U : ι → C` and an object `W` with a morphism `W ⟶ U i₀`, the Čech complex of `U` at
  the presheaf `V ↦ P(W ⨯ V)` is exact in every positive degree.

## Implementation notes

For a family of objects the base change is carried out on the coefficients rather than on the
family: the Čech complex of `{W ⨯ U_i → W}` in the slice over `W` is the Čech complex of `U` at
`V ↦ P(W ⨯ V)`, by `Stacks.CechSiteChange.cechComplexFunctorSiteIso` and the fact that
`CategoryTheory.Over.star` preserves finite products.

## References

* [Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u'

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C]

section MorphismFamily

variable {X W : C} (E : PreZeroHypercover.{w} X) (g : W ⟶ X)
  [∀ i : E.I₀, HasPullback g (E.f i)]

/-- **The diagonal section of a base-changed family.**  If `g : W ⟶ X` factors as
`h ≫ E.f i₀`, then `W ⟶ U_{i₀} ×_X W` is cut out by the identity of `W` and by `h`; it is a
section of the `i₀`-th member of `CategoryTheory.PreZeroHypercover.pullback₁`. -/
noncomputable def pullback₁Section {i₀ : E.I₀} (h : W ⟶ E.X i₀) (hh : h ≫ E.f i₀ = g) :
    W ⟶ (E.pullback₁ g).X i₀ :=
  pullback.lift (𝟙 W) h ((Category.id_comp g).trans hh.symm)

/-- `Stacks.CechSite.pullback₁Section` is a section of the `i₀`-th member of the base-changed
family. -/
@[simp]
theorem pullback₁Section_comp_f {i₀ : E.I₀} (h : W ⟶ E.X i₀) (hh : h ≫ E.f i₀ = g) :
    pullback₁Section E g h hh ≫ (E.pullback₁ g).f i₀ = 𝟙 W :=
  pullback.lift_fst _ _ _

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Abelian A]
  [HasFiniteProducts C] [HasFiniteProducts (Over W)]

/-- **The Čech complex of a base-changed family is exact in positive degrees**, provided the
morphism `g : W ⟶ X` one base-changes along lifts, as `h` with `h ≫ E.f i₀ = g`, to the `i₀`-th
member of the family. -/
theorem exactAt_cechComplex_pullback₁_of_factorsThrough (P : Cᵒᵖ ⥤ A) {i₀ : E.I₀}
    (h : W ⟶ E.X i₀) (hh : h ≫ E.f i₀ = g) (n : ℕ) (hn : 0 < n) :
    (cechComplex (E.pullback₁ g) P).ExactAt n :=
  exactAt_cechComplex_of_section (E.pullback₁ g) P (pullback₁Section E g h hh)
    (pullback₁Section_comp_f E g h hh) n hn

/-- **The Čech complex of a family base-changed to an object over one of its members is exact
in positive degrees**, when the target of the family is a terminal object: any morphism
`h : W ⟶ U_{i₀}` suffices. -/
theorem exactAt_cechComplex_pullback₁_of_isTerminal (hX : IsTerminal X) (P : Cᵒᵖ ⥤ A)
    {i₀ : E.I₀} (h : W ⟶ E.X i₀) (n : ℕ) (hn : 0 < n) :
    (cechComplex (E.pullback₁ g) P).ExactAt n :=
  exactAt_cechComplex_pullback₁_of_factorsThrough E g P h (hX.hom_ext _ _) n hn

end MorphismFamily

end Stacks.CechSite

namespace Stacks.CechObjectFamily

/-! ### Base change of the coefficients, for a family of objects

For Mathlib's `CategoryTheory.cechComplexFunctor`, attached to a family of objects `U : ι → C` of
a category with finite products, the base change to an object `W` is carried out on the
coefficients: the Čech complex of `U` at the presheaf `V ↦ P(W ⨯ V)`. -/

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Abelian A]
  {ι : Type w} (U : ι → C)

/-- Restricting to the slice over `W` and forgetting again is multiplication by `W`. -/
theorem starForget_obj (W V : C) : (Over.star W ⋙ Over.forget W).obj V = (W ⨯ V) := rfl

/-- **The Čech complex of a split family of objects is exact in positive degrees.**  This is
`Stacks.CechSite.exactAt_cochainComplexFunctor_of_sectionFromTerminal` for Mathlib's
`CategoryTheory.cechComplexFunctor`, whose family is a family of objects rather than a formal
coproduct. -/
theorem exactAt_cechComplexFunctor_of_sectionFromTerminal (P : Cᵒᵖ ⥤ A) {T : C}
    (hT : IsTerminal T) {i₀ : ι} (d : T ⟶ U i₀) (n : ℕ) (hn : 0 < n) :
    ((cechComplexFunctor U).obj P).ExactAt n :=
  Stacks.CechSite.exactAt_cochainComplexFunctor_of_sectionFromTerminal
    (FormalCoproduct.mk ι U) P hT d n hn

/-- **The Čech complex of a family of objects, with coefficients base-changed to an object
mapping into a member of the family, is exact in every positive degree.**

Precisely: let `U : ι → C` be a family of objects, let `W` be an object admitting a morphism
`q : W ⟶ U i₀` to one of them, and let `P` be a presheaf with values in an abelian category with
products.  Then the Čech complex of `U` at the presheaf `V ↦ P(W ⨯ V)` is exact in every degree
`n > 0`. -/
theorem exactAt_cechComplexFunctor_prodRestriction_of_hom (W : C) [HasFiniteProducts (Over W)]
    (P : Cᵒᵖ ⥤ A) {i₀ : ι} (q : W ⟶ U i₀) (n : ℕ) (hn : 0 < n) :
    ((cechComplexFunctor U).obj ((Over.star W ⋙ Over.forget W).op ⋙ P)).ExactAt n := by
  have : PreservesLimits (Over.star W) :=
    (Over.forgetAdjStar W).rightAdjoint_preservesLimits
  exact (exactAt_cechComplexFunctor_of_sectionFromTerminal
      (fun i ↦ (Over.star W).obj (U i)) ((Over.forget W).op ⋙ P) Over.mkIdTerminal
      (((Over.forgetAdjStar W).homEquiv (Over.mk (𝟙 W)) (U i₀)) q) n hn).of_iso
    ((Stacks.CechSiteChange.cechComplexFunctorSiteIso (A := A) (Over.star W) U).app
      ((Over.forget W).op ⋙ P))

end Stacks.CechObjectFamily

end
