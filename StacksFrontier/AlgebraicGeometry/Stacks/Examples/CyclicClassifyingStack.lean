module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ConstantGroupSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.ClassifyingStackHom
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleChartOpenSubspaceSiteObject
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties

/-!
# The classifying stack of `ℤ/pℤ` over `Spec k[x]`

Let `k` be a field, `S = Spec k[x]` and `G = ℤ/pℤ`, regarded as the constant group algebraic
space `G_S` over `S` (**Stacks 043O**). The classifying stack `𝒳 = [S/G]`, the quotient stack of
the trivial action of `G` on `S`, is an algebraic stack because `G_S ⟶ S` is smooth
(**Stacks 04TK**), and its structure morphism `f : 𝒳 ⟶ S` is quasi-compact and
quasi-separated. This is the morphism of the discussion of **Stacks 07DC**, the witness for
**Stacks 07DD**.

## Main definitions

* `Stacks.Examples.UnboundedDerivedPushforward.cyclicClassifyingStack`: `𝒳 = [S/G]`.
* `Stacks.Examples.UnboundedDerivedPushforward.baseStack`: `S`, as an algebraic stack.
* `Stacks.Examples.UnboundedDerivedPushforward.cyclicStructureMorphism`: `f : 𝒳 ⟶ S`.
* `Stacks.Examples.UnboundedDerivedPushforward.cyclicAtlas`: the atlas `S ⟶ 𝒳` given by the
  trivial torsor.

## Main results

* `Stacks.Examples.UnboundedDerivedPushforward.isQuasiCompactMorphism_cyclicStructureMorphism`
  and `Stacks.Examples.UnboundedDerivedPushforward.isQuasiSeparated_cyclicStructureMorphism`:
  `f` is quasi-compact and quasi-separated.

## Implementation notes

`𝒳` is the packaged model `AlgebraicGeometry.Stack.classifyingAlgebraicStack` of the quotient
stack, which lies in the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks`; quasi-compactness
of `𝒳` is that of the affine scheme `S` surjecting onto it, and quasi-separatedness of `f` comes
from separatedness of a classifying stack of a proper, flat, finitely presented group.

## References

* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 043O](https://stacks.math.columbia.edu/tag/043O)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w

namespace Stacks.Examples.UnboundedDerivedPushforward

variable (p : ℕ) [NeZero p] {k : Type u} [Field k] (𝒞 : BigFppfSite.{u})
  (hS : 𝒞.Contains (Spec (.of (Polynomial k))))

/-- The cyclic group `ℤ/pℤ`, written multiplicatively. -/
abbrev CyclicGroup := Multiplicative (ZMod p)

include hS in
/-- The big fppf site contains the constant group scheme `(ℤ/pℤ)_S` over `S = Spec k[x]`. -/
theorem contains_cyclicGroupScheme :
    𝒞.Contains (constantGroupScheme.{u} (CyclicGroup p) (Spec (.of (Polynomial k)))).X.left :=
  Space.contains_constantGroupScheme.{u} (CyclicGroup p) hS

/-- The constant group algebraic space `(ℤ/pℤ)_S` over the final algebraic space of the big fppf
site of `S = Spec k[x]`. -/
abbrev cyclicGroupSpace :
    Space.GroupAlgebraicSpace 𝒞 (Spec (.of (Polynomial k))) hS
      (Space.terminalSpace 𝒞 _ hS).obj (Space.terminalSpace 𝒞 _ hS).property :=
  Space.constantGroupSpace 𝒞 _ hS (CyclicGroup p) (Space.terminalSpace 𝒞 _ hS).obj
    (Space.terminalSpace 𝒞 _ hS).property (contains_cyclicGroupScheme p 𝒞 hS)

/-- `(ℤ/pℤ)_S ⟶ S` is smooth. -/
theorem isSmooth_cyclicGroupSpace :
    Space.IsSmooth 𝒞 _ hS (cyclicGroupSpace p 𝒞 hS).obj.X.hom :=
  Space.isSmooth_constantGroupSpace_terminal _ hS _

/-- **The classifying stack `𝒳 = [S/(ℤ/pℤ)]` over `S = Spec k[x]`**, the quotient stack of the
trivial action of the constant group `(ℤ/pℤ)_S` on `S`, as an algebraic stack. -/
abbrev cyclicClassifyingStack : Stack.AlgebraicStacks.{u, w} 𝒞 (Spec (.of (Polynomial k))) hS :=
  Stack.classifyingAlgebraicStack.{u, w} (cyclicGroupSpace p 𝒞 hS)
    (isSmooth_cyclicGroupSpace p 𝒞 hS)

/-- The base `S = Spec k[x]`, as an algebraic stack over itself. -/
abbrev baseStack : Stack.AlgebraicStacks.{u, w} 𝒞 (Spec (.of (Polynomial k))) hS :=
  Stack.schemeStack.{u, w} 𝒞 _ hS (Over.mk (𝟙 (𝒞.obj hS)))

/-- **The structure morphism `f : [S/(ℤ/pℤ)] ⟶ S`.** -/
abbrev cyclicStructureMorphism : cyclicClassifyingStack.{u, w} p 𝒞 hS ⟶ baseStack.{u, w} 𝒞 hS :=
  Stack.structureMorphism.{u, w} 𝒞 _ hS (cyclicClassifyingStack.{u, w} p 𝒞 hS)

/-- The atlas `S ⟶ [S/(ℤ/pℤ)]`, the trivial torsor. -/
abbrev cyclicAtlas :
    Stack.schemeStack.{u, w} 𝒞 _ hS (Space.baseTerminal 𝒞 _ hS) ⟶
      cyclicClassifyingStack.{u, w} p 𝒞 hS :=
  Stack.siteObjectAlgebraicSpaceStackMap.{u, w} 𝒞 _ hS
      (Space.terminalSpace 𝒞 _ hS).property (Iso.refl _) ≫
    Stack.classifyingAtlas.{u, w} (cyclicGroupSpace p 𝒞 hS) (isSmooth_cyclicGroupSpace p 𝒞 hS)

/-- The atlas `S ⟶ [S/(ℤ/pℤ)]` is surjective. -/
theorem isSurjective_cyclicAtlas : Stack.IsSurjective 𝒞 _ hS (cyclicAtlas.{u, w} p 𝒞 hS) := by
  change Function.Surjective (Stack.AlgebraicStacks.pointsMap 𝒞 _ hS _)
  rw [Stack.AlgebraicStacks.pointsMap_comp]
  exact (Stack.classifyingAtlas_fppf.{u, w} _ _).2.1.comp
    (Stack.pointsMap_surjective_siteObjectAlgebraicSpaceStackMap.{u, w} 𝒞 _ hS _ _)

/-- `[S/(ℤ/pℤ)]` is quasi-compact: the affine scheme `S` surjects onto it. -/
theorem isQuasiCompactStack_cyclicClassifyingStack :
    Stack.IsQuasiCompactStack.{u, w} 𝒞 _ hS (cyclicClassifyingStack.{u, w} p 𝒞 hS).val
      (cyclicClassifyingStack.{u, w} p 𝒞 hS).property :=
  Stack.isQuasiCompactStack_of_isSurjective.{u, w} 𝒞 _ hS (cyclicAtlas.{u, w} p 𝒞 hS)
    (Stack.isQuasiCompactStack_schemeStack_of_isAffine.{u, w} 𝒞 _ hS _
      (by change IsAffine (Spec (.of (Polynomial k))); infer_instance))
    (isSurjective_cyclicAtlas.{u, w} p 𝒞 hS)

/-- **`f : [S/(ℤ/pℤ)] ⟶ S` is quasi-compact.** -/
theorem isQuasiCompactMorphism_cyclicStructureMorphism :
    Stack.IsQuasiCompactMorphism.{u, w} 𝒞 _ hS (cyclicStructureMorphism.{u, w} p 𝒞 hS) :=
  Stack.isQuasiCompactMorphism_structureMorphism.{u, w} 𝒞 _ hS inferInstance _
    (isQuasiCompactStack_cyclicClassifyingStack.{u, w} p 𝒞 hS)

/-- **`f : [S/(ℤ/pℤ)] ⟶ S` is quasi-separated**: the classifying stack of a proper, flat and
finitely presented group is separated over the base. -/
theorem isQuasiSeparated_cyclicStructureMorphism :
    Stack.AlgebraicStacks.IsQuasiSeparated.{u, w} 𝒞 _ hS
      (cyclicStructureMorphism.{u, w} p 𝒞 hS) :=
  have hsm := isSmooth_cyclicGroupSpace p 𝒞 hS
  Stack.AlgebraicStacks.isQuasiSeparated_of_isSeparated 𝒞 _ hS
    (Stack.isSeparatedOver_classifyingAlgebraicStack.{u, w} _ _
      (Space.isProper_constantGroupSpace_terminal _ hS _)
      (Space.isFlat_of_isSmooth 𝒞 _ hS _ hsm)
      (Space.isLocallyOfFinitePresentation_of_isSmooth 𝒞 _ hS hsm))

end Stacks.Examples.UnboundedDerivedPushforward
