module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentHasSeparator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSheafFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SubcategoryCoherator

/-!
# The coherator of an algebraic stack on `LQCoh^fbc` (Stacks 0778)

Let `𝒳` be an algebraic stack and let `LQCoh^fbc(𝒪_𝒳)` be the category of locally quasi-coherent
modules with the flat base change property (Stacks, Section 0GQG).  **Stacks 0778** says that the
inclusion `i : QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳)` has a right adjoint `Q` with `Q ∘ i` the identity.

Here `LQCoh^fbc(𝒪_𝒳)` is `AlgebraicGeometry.Stack.lqcohSheafFbcFppfModules`, the full subcategory
of `Mod(𝒪_𝒳)` cut out by local quasi-coherence (**Stacks 06WJ**) and the flat base change property
of **Stacks 0762**, read with the inverse image of étale sheaves.

## The construction

The source builds `Q` from a presentation `𝒳 = [U/R]` and the equivalence of **Stacks 06WT**.  Here
`Q` is the restriction to `LQCoh^fbc(𝒪_𝒳)` of the coherator `Mod(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of **Stacks
0781** part (2) (`AlgebraicGeometry.Stack.AlgebraicStacks.coheratorOfSeparator`), whose inputs are
all proved: closure of quasi-coherence under colimits, local smallness, well-copoweredness, and a
separator (`AlgebraicGeometry.Stack.hasSeparator_quasicoherentModules`).  The right adjoint of an
inclusion of full subcategories `QCoh ⊆ LQCoh^fbc ⊆ Mod` is the restriction of the right adjoint of
the composite inclusion
(`AlgebraicGeometry.Stack.AlgebraicStacks.subcategoryCoheratorAdjunctionOfSeparator`), which
needs only the containment `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)`:
`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohSheafFbcFppfModules_quasicoherentInclusion`.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentToLqcohFbc`: the inclusion `i`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoherator`: the right adjoint `Q`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoheratorAdjunction`: `i ⊣ Q`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoheratorCompIso`: `i ⋙ Q ≅ 𝟭`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcCoheratorAdjunctionAndCompIso`: both
  together, the whole statement of **Stacks 0778**.

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
* [Stacks Project, Tag 0GQG](https://stacks.math.columbia.edu/tag/0GQG)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- The inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` of **Stacks 0778**. -/
abbrev quasicoherentToLqcohFbc :
    quasicoherentModules B S hS 𝒳 ⥤
      (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory :=
  quasicoherentToSubcategory B S hS 𝒳 _
    (lqcohSheafFbcFppfModules_quasicoherentInclusion B E h S hS 𝒳)

/-- **Stacks 0778: the right adjoint `Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)`.** -/
@[stacks 0778 "the right adjoint Q : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳) of the inclusion"]
abbrev lqcohFbcCoherator :
    (lqcohSheafFbcFppfModules.{u, w, u} B E h S hS 𝒳).FullSubcategory ⥤
      quasicoherentModules B S hS 𝒳 :=
  subcategoryCoheratorOfSeparator B S hS 𝒳 _ (hasSeparator_quasicoherentModules B S hS 𝒳)

/-- **Stacks 0778: `Q` is right adjoint to the inclusion `i`.** -/
@[stacks 0778 "the inclusion QCoh(𝒪_𝒳) → LQCoh^fbc(𝒪_𝒳) is left adjoint to Q"]
def lqcohFbcCoheratorAdjunction :
    quasicoherentToLqcohFbc B E h S hS 𝒳 ⊣ lqcohFbcCoherator B E h S hS 𝒳 :=
  subcategoryCoheratorAdjunctionOfSeparator B S hS 𝒳 _ _ _

/-- **Stacks 0778: `Q ∘ i` is the identity functor of `QCoh(𝒪_𝒳)`.** -/
@[stacks 0778 "Q ∘ i is the identity functor"]
def lqcohFbcCoheratorCompIso :
    quasicoherentToLqcohFbc B E h S hS 𝒳 ⋙ lqcohFbcCoherator B E h S hS 𝒳 ≅
      𝟭 (quasicoherentModules B S hS 𝒳) :=
  subcategoryCoheratorCompIsoOfSeparator B S hS 𝒳 _ _ _

/-- **Stacks 0778, the whole statement.**  For an algebraic stack `𝒳`, the inclusion
`i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` has the right adjoint `Q`, and `Q ∘ i` is the identity functor
of `QCoh(𝒪_𝒳)`. -/
@[stacks 0778 "the whole statement: i has a right adjoint Q, and Q ∘ i is the identity"]
def lqcohFbcCoheratorAdjunctionAndCompIso :
    (quasicoherentToLqcohFbc B E h S hS 𝒳 ⊣ lqcohFbcCoherator B E h S hS 𝒳) ×
      (quasicoherentToLqcohFbc B E h S hS 𝒳 ⋙ lqcohFbcCoherator B E h S hS 𝒳 ≅
        𝟭 (quasicoherentModules B S hS 𝒳)) :=
  ⟨lqcohFbcCoheratorAdjunction B E h S hS 𝒳, lqcohFbcCoheratorCompIso B E h S hS 𝒳⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
