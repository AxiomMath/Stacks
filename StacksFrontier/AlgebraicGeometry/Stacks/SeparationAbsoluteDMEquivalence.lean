module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBaseSource
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSmallerBaseDMAndSeparated
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications

/-!
# Being DM is the same as being DM over the base scheme (Stacks 050N, parts (1) and (2))

Let `S` be a scheme contained in a big fppf site `B` and let `𝒳` be an algebraic stack over `S`.
**Stacks 050D** calls `𝒳` *DM over `S`* when its structure 1-morphism `𝒳 ⟶ S` is DM (part (1))
and *DM* when `𝒳`, viewed over the terminal scheme `Spec ℤ` by Construction A of **Stacks 04X5**,
is DM over `Spec ℤ` (part (5)). **Stacks 050N** part (1) says the two agree, and part (2) says
the same for quasi-DM. This module proves both biconditionals.

The forward implications are
`AlgebraicGeometry.Stack.AlgebraicStacks.isDMOver_of_isAbsolutelyDM` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDMOver_of_isAbsolutelyQuasiDM`, which change the
base along `S ⟶ Spec ℤ`. The converses do **not** go that way: the inclusion of the self-product
over `S` into the self-product over `Spec ℤ` is fully faithful and not essentially surjective, so
the change-of-base equivalence is unavailable in that direction. They are obtained instead from
**Stacks 050L** part (5): a 1-morphism which is DM into a target which is DM has DM source, and
the structure 1-morphism of `𝒳` is a 1-morphism into the algebraic stack of `S` itself. So the
whole content of the converse is that *the algebraic stack of the base scheme is DM*, and that
holds because it is representable by an algebraic space after Construction A, whence its
structure 1-morphism over `Spec ℤ` is representable by algebraic spaces and therefore DM.

That last step is the one piece of infrastructure the module adds: Construction A of the algebraic
stack of a scheme over `S` is the algebraic stack of that scheme viewed over `S'`, up to an
equivalence over the site which `AlgebraicGeometry.Stack.factorSliceInverse` already supplies, so
representability by an algebraic space travels across it.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_changeBase_scheme`: Construction A of
  the category fibred in groupoids represented by a scheme over `S` is represented by an
  algebraic space over `S'`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_schemeStack_id`: the algebraic stack of
  the base scheme is DM.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_iff_isDMOver`: **Stacks 050N**,
  part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiDM_iff_isQuasiDMOver`:
  **Stacks 050N**, part (2).

## Implementation notes

`AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers` is the first component of the object
bijection of Stacks 04X5, and it is `AlgebraicGeometry.Stack.changeBaseAlgebraicStack` along
`terminal.from S` on the nose; so no transport of the view is written anywhere below, and the
only comparison used is the slice identification of Construction A.

The quasi-DM half is not proved independently: a DM 1-morphism is quasi-DM
(`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_of_isDM`, **Stacks 050E**), so the algebraic
stack of the base scheme being DM gives it quasi-DM as well, and Stacks 050L part (6) then runs
the same argument.

## References

* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **Construction A of the category fibred in groupoids represented by a scheme over `S` is
represented by an algebraic space over `S'`.**

Construction A of the slice over `V` is identified with the slice over the relocalization of `V`
by `AlgebraicGeometry.Stack.factorSliceInverse`, which is an equivalence over the big fppf site
of `S'`; and the slice over a scheme over `S'` is represented by an algebraic space by
Stacks 04SV. Representability by an algebraic space travels across an equivalence over the
site. -/
theorem isRepresentableByAlgebraicSpace_changeBase_scheme (V : BigFppfOver B S hS) :
    IsRepresentableByAlgebraicSpace B S' hS'
      (changeBaseFiberedInGroupoids B S S' hS hS' g (schemeFibredCategory B S hS V)) := by
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (schemeFibredCategory B S' hS' ((Over.map g).obj V)).isFiberedInGroupoids
    (changeBaseFiberedInGroupoids B S S' hS hS' g
      (schemeFibredCategory B S hS V)).isFiberedInGroupoids
    (factorSliceInverse B S S' hS hS' g V).toFunctor
    (factorSliceInverse B S S' hS hS' g V).w
    (isEquivalence_factorSliceInverse B S S' hS hS' g V)
  exact isRepresentableByAlgebraicSpace_of_equivalenceOver k.symm
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S' hS' ((Over.map g).obj V))

namespace AlgebraicStacks

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **The algebraic stack of the base scheme is Deligne–Mumford**, in the absolute sense of
Stacks 050D part (5).

Its view over the terminal scheme is Construction A of a scheme stack, hence representable by an
algebraic space; a 1-morphism out of something representable by an algebraic space into an
algebraic stack is representable by algebraic spaces (Stacks 02ZZ, through Stacks 045G); and a
1-morphism representable by algebraic spaces is DM, its relative diagonal being a monomorphism
locally of finite type and so unramified by Stacks 05W6. -/
theorem isAbsolutelyDM_schemeStack_id :
    IsAbsolutelyDM.{u, w} B S hS hZ (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))) :=
  isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces.{u, w} B (⊤_ Scheme.{u}) hZ
    (Stack.structureMorphism B (⊤_ Scheme.{u}) hZ
      (viewOverIntegers.{u, w} B S hS hZ
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS))))))
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B (⊤_ Scheme.{u}) hZ
      (schemeStack.{u, w} B (⊤_ Scheme.{u}) hZ (Over.mk (𝟙 (B.obj hZ)))).property
      (isRepresentableByAlgebraicSpace_changeBase_scheme B S (⊤_ Scheme.{u}) hS hZ
        (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) (Over.mk (𝟙 (B.obj hS))))
      (Stack.structureMorphism B (⊤_ Scheme.{u}) hZ
        (viewOverIntegers.{u, w} B S hS hZ
          (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))))).hom)

/-- **The algebraic stack of the base scheme is quasi-DM**, in the absolute sense of Stacks 050D
part (6): it is DM, and a DM 1-morphism is quasi-DM by Stacks 050E. -/
theorem isAbsolutelyQuasiDM_schemeStack_id :
    IsAbsolutelyQuasiDM.{u, w} B S hS hZ (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))) :=
  isQuasiDM_of_isDM B (⊤_ Scheme.{u}) hZ (isAbsolutelyDM_schemeStack_id.{u, w} B S hS hZ)

/-- **An algebraic stack Deligne–Mumford over its base scheme is Deligne–Mumford**, the converse
of `AlgebraicGeometry.Stack.AlgebraicStacks.isDMOver_of_isAbsolutelyDM` and the backward
implication of Stacks 050N part (1).

The structure 1-morphism `𝒳 ⟶ S` is DM exactly by hypothesis, the algebraic stack of `S` is DM,
and Stacks 050L part (5) composes them. -/
theorem isAbsolutelyDM_of_isDMOver (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : Stack.IsDMOver B S hS 𝒳) :
    IsAbsolutelyDM.{u, w} B S hS hZ 𝒳 :=
  isAbsolutelyDM_of_isDM.{u, w} B S hS hZ (Stack.structureMorphism B S hS 𝒳)
    (isAbsolutelyDM_schemeStack_id.{u, w} B S hS hZ) h𝒳

/-- **An algebraic stack quasi-DM over its base scheme is quasi-DM**, the converse of
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDMOver_of_isAbsolutelyQuasiDM` and the backward
implication of Stacks 050N part (2). This is Stacks 050L part (6) at the structure
1-morphism. -/
theorem isAbsolutelyQuasiDM_of_isQuasiDMOver (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : Stack.IsQuasiDMOver B S hS 𝒳) :
    IsAbsolutelyQuasiDM.{u, w} B S hS hZ 𝒳 :=
  isAbsolutelyQuasiDM_of_isQuasiDM.{u, w} B S hS hZ (Stack.structureMorphism B S hS 𝒳)
    (isAbsolutelyQuasiDM_schemeStack_id.{u, w} B S hS hZ) h𝒳

/-- **Stacks 050N, part (1).** An algebraic stack over `S` is Deligne–Mumford exactly when it is
Deligne–Mumford over `S`. -/
@[stacks 050N "dm_equiv"]
theorem isAbsolutelyDM_iff_isDMOver (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    IsAbsolutelyDM.{u, w} B S hS hZ 𝒳 ↔ Stack.IsDMOver B S hS 𝒳 :=
  ⟨isDMOver_of_isAbsolutelyDM.{u, w} B S hS hZ 𝒳,
    isAbsolutelyDM_of_isDMOver.{u, w} B S hS hZ 𝒳⟩

/-- **Stacks 050N, part (2).** An algebraic stack over `S` is quasi-DM exactly when it is
quasi-DM over `S`. -/
@[stacks 050N "quasi_dm_equiv"]
theorem isAbsolutelyQuasiDM_iff_isQuasiDMOver (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    IsAbsolutelyQuasiDM.{u, w} B S hS hZ 𝒳 ↔ Stack.IsQuasiDMOver B S hS 𝒳 :=
  ⟨isQuasiDMOver_of_isAbsolutelyQuasiDM.{u, w} B S hS hZ 𝒳,
    isAbsolutelyQuasiDM_of_isQuasiDMOver.{u, w} B S hS hZ 𝒳⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
