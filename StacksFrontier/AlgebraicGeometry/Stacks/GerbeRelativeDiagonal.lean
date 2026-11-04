module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatness
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeRelativeDiagonalSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedIsomPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative

/-!
# The relative diagonal and the relative inertia of a gerbe (Stacks 0CPR)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which makes `𝒳` a gerbe over `𝒴`
(**Stacks 06QC**). **Stacks 0CPR** asserts:

1. the forgetful 1-morphism `I_{𝒳/𝒴} ⟶ 𝒳` of the relative inertia is flat and locally of finite
   presentation;
2. the relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is surjective, flat and locally of finite
   presentation;
3. for algebraic spaces `T₁`, `T₂` with 1-morphisms `x_i : T_i ⟶ 𝒳` and `y_i = x_i ≫ f`, the
   comparison `T₁ ×_{x₁, 𝒳, x₂} T₂ ⟶ T₁ ×_{y₁, 𝒴, y₂} T₂` is surjective, flat and locally of
   finite presentation;
4. for an algebraic space `T` with two 1-morphisms `x_i : T ⟶ 𝒳`, the induced morphism
   `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(y₁, y₂)` is surjective, flat and locally of finite presentation.

All four parts are proved here, each at exactly these hypotheses.

## The shape of the proofs

Everything rests on part (2), as in the source. In the namespace
`AlgebraicGeometry.Stack.AlgebraicStacks`, its surjectivity clause is
`isSurjective_relativeDiagonal_of_isGerbeOver`, and its flatness and local finite presentation are
`isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal`: `Δ_f` is a section of the second
projection `𝒳 ×_𝒴 𝒳 ⟶ 𝒳`, which is a gerbe by **Stacks 06QE**, and a section of a gerbe is flat
and locally of finite presentation.

* Part (1): the relative inertia is equivalent over the site to `𝒳 ×_{Δ_f, 𝒳 ×_𝒴 𝒳, Δ_f} 𝒳` in
  such a way that its forgetful 1-morphism becomes the first projection, a base change of `Δ_f`;
  the two properties base change by **Stacks 06PY** and **Stacks 06Q4** and are unchanged by the
  comparison.
* Part (3): by **Stacks 04Z1** the comparison of two fibre products is a base change of `Δ_f`,
  and the three properties base change by **Stacks 04ZU**, **Stacks 06PY** and **Stacks 06Q4**.
* Part (4): `Isom_𝒳(x₁, x₂)` sits in a 2-cartesian square over the comparison
  `T ×_{x₁, 𝒳, x₂} T ⟶ T ×_{y₁, 𝒴, y₂} T` of part (3)
  (`AlgebraicGeometry.Stack.HigherDiagonal.isTwoFibreProduct_isomSquare`), that comparison sits in
  a 2-cartesian square over `Δ_f` (**Stacks 050H**), and the morphism of part (4) is therefore a
  base change of `Δ_f`. As `Δ_f` is representable by algebraic spaces, its three properties in
  the sense of **Stacks 06FM** and **Stacks 04ZS** are those of the morphisms of algebraic spaces
  obtained by base change to schemes (**Stacks 06FM**, the assertion for representable
  morphisms, and **Stacks 04XI**), which is the form in which they pass along base change.

## Main results

All of these live in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`.

* `isFlat_and_isLocallyOfFinitePresentation_relativeInertiaProjection_of_isGerbeOver`:
  **Stacks 0CPR, part (1)**.
* `isSurjective_and_isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal_of_isGerbeOver`:
  **Stacks 0CPR, part (2)**.
* `isSurjective_and_isFlat_and_isLocallyOfFinitePresentation_comparison_of_isGerbeOver`:
  **Stacks 0CPR, part (3)**.
* `isomMap_isSurjective_and_isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver`:
  **Stacks 0CPR, part (4)**.

## Implementation notes

In part (4) the object `Isom_𝒳(x₁, x₂)` is `AlgebraicGeometry.Stack.HigherDiagonal.isomStack`,
the category fibred in groupoids of the vertical isomorphisms `x₁(t) ≅ x₂(t)` at a single point
`t` of `T` (the category fibred in setoids attached to the sheaf `Isom_𝒳(x₁, x₂)` of
**Stacks 06PP**), and the morphism is `AlgebraicGeometry.Stack.HigherDiagonal.isomMap`, which
applies `f` to such an isomorphism. The conclusion says that this morphism is representable by
algebraic spaces and that for every scheme `U` over `S` and every object of `Isom_𝒴(y₁, y₂)`
over `U`, the algebraic space representing the base change is surjective, flat and locally of
finite presentation over `U`: these are the three properties of a morphism representable by
algebraic spaces in the sense of **Stacks 04XB**, written out as they are in the library's
statement of **Stacks 0CPL**, part (2), for the same morphism.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04Z1](https://stacks.math.columbia.edu/tag/04Z1)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 04ZU](https://stacks.math.columbia.edu/tag/04ZU)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 06Q4](https://stacks.math.columbia.edu/tag/06Q4)
* [Stacks Project, Tag 06QC](https://stacks.math.columbia.edu/tag/06QC)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 0CPL](https://stacks.math.columbia.edu/tag/0CPL)
* [Stacks Project, Tag 0CPR](https://stacks.math.columbia.edu/tag/0CPR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CPR, part (2).** If a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` makes
`𝒳` a gerbe over `𝒴`, then its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is surjective, flat and
locally of finite presentation.

Surjectivity is Stacks 06P1 (2)(b) read at a field-valued point
(`AlgebraicGeometry.Stack.AlgebraicStacks.isSurjective_relativeDiagonal_of_isGerbeOver`);
flatness and local finite presentation hold because `Δ_f` is a section of the gerbe
`𝒳 ×_𝒴 𝒳 ⟶ 𝒳`
(`isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal`).
-/
@[stacks 0CPR "part (2): the relative diagonal is surjective, flat and locally of finite \
presentation"]
theorem isSurjective_and_isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal_of_isGerbeOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    Stack.IsSurjective B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) ∧
      IsFlat B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) ∧
      IsLocallyOfFinitePresentation B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f) :=
  ⟨isSurjective_relativeDiagonal_of_isGerbeOver B S hS f hf,
    isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf⟩

/-- **Stacks 0CPR, part (1).** If a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` makes
`𝒳` a gerbe over `𝒴`, then the forgetful 1-morphism `I_{𝒳/𝒴} ⟶ 𝒳` of the relative inertia is
flat and locally of finite presentation.

The relative inertia is equivalent over the site to `𝒳 ×_{Δ_f, 𝒳 ×_𝒴 𝒳, Δ_f} 𝒳` in such a way
that the forgetful 1-morphism becomes the first projection
(`AlgebraicGeometry.Stack.AlgebraicStacks.relativeInertiaProjection_eq_comp_fst`), which is a base
change of `Δ_f`; so part (2) together with **Stacks 06PY** and **Stacks 06Q4** gives the two
properties for the projection, and they are unchanged by the comparison. -/
@[stacks 0CPR "part (1): the relative inertia is flat and locally of finite presentation over \
the source"]
theorem isFlat_and_isLocallyOfFinitePresentation_relativeInertiaProjection_of_isGerbeOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    IsFlat B S hS (Stack.relativeInertiaProjection B S hS f) ∧
      IsLocallyOfFinitePresentation B S hS (Stack.relativeInertiaProjection B S hS f) := by
  obtain ⟨hΔflat, hΔlfp⟩ := isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal B S hS f hf
  have hequiv : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor
      (Bicategory.InducedBicategory.mkHom
        (Stack.relativeInertiaToSecondRelativeDiagonal B S hS f.hom) :
      Stack.relativeInertiaStack B S hS f ⟶
        Stack.twoFibreProductAlgebraicStack B S hS
          (Stack.relativeDiagonalAlgebraicStacks B S hS f)
          (Stack.relativeDiagonalAlgebraicStacks B S hS f)).hom) :=
    Stack.isEquivalence_relativeInertiaToSecondRelativeDiagonal B S hS f.hom
  rw [relativeInertiaProjection_eq_comp_fst]
  refine ⟨isFlat_comp_of_isEquivalence B S hS _ _ hequiv
      (isFlat_baseChange B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f)
        (Stack.relativeDiagonalAlgebraicStacks B S hS f) _
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _) hΔflat),
    isLocallyOfFinitePresentation_comp_of_isEquivalence B S hS _ _ hequiv
      (isLocallyOfFinitePresentation_baseChange B S hS
        (Stack.relativeDiagonalAlgebraicStacks B S hS f)
        (Stack.relativeDiagonalAlgebraicStacks B S hS f) _
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _) hΔlfp)⟩

/-- **Stacks 0CPR, part (3).** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`
making `𝒳` a gerbe over `𝒴`, let `T₁` and `T₂` be algebraic spaces over `S` and let
`x_i : T_i ⟶ 𝒳` be 1-morphisms, with `y_i = x_i ≫ f`. Then the comparison 1-morphism

    T₁ ×_{x₁, 𝒳, x₂} T₂ ⟶ T₁ ×_{y₁, 𝒴, y₂} T₂

is surjective, flat and locally of finite presentation.

By **Stacks 04Z1** that comparison is a base change of the relative diagonal `Δ_f`, which has the
three properties by part (2), and they base change by **Stacks 04ZU**, **Stacks 06PY** and
**Stacks 06Q4**. -/
@[stacks 0CPR "part (3): the comparison of the two fibre products of a pair of algebraic spaces \
over the stacks is surjective, flat and locally of finite presentation"]
theorem isSurjective_and_isFlat_and_isLocallyOfFinitePresentation_comparison_of_isGerbeOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsGerbeOver B S hS f) (T₁ T₂ : AlgebraicSpaces B S hS)
    (x₁ : ofAlgebraicSpace.{u, w} B S hS T₁ ⟶ 𝒳)
    (x₂ : ofAlgebraicSpace.{u, w} B S hS T₂ ⟶ 𝒳) :
    Stack.IsSurjective B S hS (Stack.comparison B S hS x₁ x₂ f) ∧
      IsFlat B S hS (Stack.comparison B S hS x₁ x₂ f) ∧
      IsLocallyOfFinitePresentation B S hS (Stack.comparison B S hS x₁ x₂ f) := by
  obtain ⟨hΔsurj, hΔflat, hΔlfp⟩ :=
    isSurjective_and_isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal_of_isGerbeOver
      B S hS f hf
  exact ⟨Stack.isSurjective_of_isTwoFibreProduct B S hS
      (comparisonSquareAlgebraicStacks B S hS x₁ x₂ f).swap
      (Bicategory.isTwoFibreProduct_swap
        (isTwoFibreProduct_comparisonSquareAlgebraicStacks B S hS x₁ x₂ f)) hΔsurj,
    isFlat_baseChange B S hS (Stack.relativeDiagonalAlgebraicStacks B S hS f)
      (Stack.comparisonCospanRight B S hS x₁ x₂ f)
      (comparisonSquareAlgebraicStacks B S hS x₁ x₂ f)
      (isTwoFibreProduct_comparisonSquareAlgebraicStacks B S hS x₁ x₂ f) hΔflat,
    isLocallyOfFinitePresentation_baseChange B S hS
      (Stack.relativeDiagonalAlgebraicStacks B S hS f)
      (Stack.comparisonCospanRight B S hS x₁ x₂ f)
      (comparisonSquareAlgebraicStacks B S hS x₁ x₂ f)
      (isTwoFibreProduct_comparisonSquareAlgebraicStacks B S hS x₁ x₂ f) hΔlfp⟩

/-- **Stacks 0CPR, part (4).** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`
making `𝒳` a gerbe over `𝒴`, let `T` be an algebraic space over `S` and let `x₁, x₂ : T ⟶ 𝒳` be
1-morphisms, with `y_i = x_i ≫ f`. Then the morphism

    Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(y₁, y₂)

which applies `f` to an isomorphism `x₁(t) ≅ x₂(t)` is representable by algebraic spaces, and
it is surjective, flat and locally of finite presentation: for every scheme `U` over `S` and
every object of `Isom_𝒴(y₁, y₂)` over `U`, the morphism to `U` from the algebraic space
representing the base change is surjective, flat and locally of finite presentation
(**Stacks 04XB**).

As in the source, `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(y₁, y₂)` is a base change of the comparison
`T ×_{x₁, 𝒳, x₂} T ⟶ T ×_{y₁, 𝒴, y₂} T` of part (3)
(`AlgebraicGeometry.Stack.HigherDiagonal.isTwoFibreProduct_isomSquare`), which is a base change of
`Δ_f` (**Stacks 050H**). The relative diagonal is representable by algebraic spaces, so its three
properties of part (2) are its relative properties in the sense of Stacks 04XB, by **Stacks 04XI**
for surjectivity and by **Stacks 06FM**, the assertion for representable morphisms, for flatness
and local finite presentation; and these pass along the two base changes. -/
@[stacks 0CPR "part (4): the morphism of isomorphism spaces is surjective, flat and locally of \
finite presentation"]
theorem isomMap_isSurjective_and_isFlat_and_isLocallyOfFinitePresentation_of_isGerbeOver
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f)
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳) :
    IsRepresentableByAlgebraicSpaces B S hS (HigherDiagonal.isomMap B S hS f T hT x₁ x₂).hom ∧
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (HigherDiagonal.isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f)).val.obj)
      (_hz : z ⋙ (HigherDiagonal.isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f)).val.p =
        Over.map U.hom)
      (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (HigherDiagonal.isomStack B S hS T hT x₁ x₂).val.p
            (HigherDiagonal.isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f)).val.p z
            (CatFiberedInGroupoids.homFunctor (HigherDiagonal.isomMap B S hS f T hT x₁ x₂)))
          (presheafOfCategories (G ⋙ typeToCat)).p) →
        Space.IsSurjective B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)).hom ∧
          Space.IsFlat B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)).hom ∧
          Space.IsLocallyOfFinitePresentation B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)).hom := by
  obtain ⟨hΔsurj, hΔflat, hΔlfp⟩ :=
    isSurjective_and_isFlat_and_isLocallyOfFinitePresentation_relativeDiagonal_of_isGerbeOver
      B S hS f hf
  have hΔrep : IsRepresentableByAlgebraicSpaces B S hS
      (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom.hom :=
    isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f
  have hflatBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hflatLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  have hlfpBC : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsStableUnderBaseChange :=
    Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have hlfpLT : (spaceProperty B S hS
      (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf B S hS
  have hsurjRel := (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS
    (Stack.relativeDiagonalAlgebraicStacks B S hS f) hΔrep).1 hΔsurj
  have hflatRel := (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) 𝒳.property
    (Stack.twoFibreProductAlgebraicStack B S hS f f).property
    (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom hΔrep).1 hΔflat
  have hlfpRel := (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) 𝒳.property
    (Stack.twoFibreProductAlgebraicStack B S hS f f).property
    (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom hΔrep).1
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
        𝒳.property (Stack.twoFibreProductAlgebraicStack B S hS f f).property
        (Stack.relativeDiagonalAlgebraicStacks B S hS f).hom).1 hΔlfp)
  have hmapRep : IsRepresentableByAlgebraicSpaces B S hS (mapBase B S hS x₁ x₂ f).hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒳.val
      (twoFibreProduct B S hS f f).val (twoFibreProduct B S hS (x₁ ≫ f) (x₂ ≫ f)).val
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
      (mapCospan B S hS x₁ x₂ f).hom
      (mapBaseSquare B S hS x₁ x₂ f) (isTwoFibreProduct_mapBaseSquare B S hS x₁ x₂ f) hΔrep
  refine ⟨isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (twoFibreProduct B S hS x₁ x₂).val (twoFibreProduct B S hS (x₁ ≫ f) (x₂ ≫ f)).val
      (HigherDiagonal.isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f))
      (mapBase B S hS x₁ x₂ f).hom (HigherDiagonal.isomInclusion B S hS T hT (x₁ ≫ f) (x₂ ≫ f))
      (HigherDiagonal.isomSquare B S hS f T hT x₁ x₂)
      (HigherDiagonal.isTwoFibreProduct_isomSquare B S hS f T hT x₁ x₂) hmapRep, ?_⟩
  let P : MorphismProperty (AlgebraicSpaces B S hS) := fun _ _ m =>
    Space.IsSurjective B S hS m.hom ∧ Space.IsFlat B S hS m.hom ∧
      Space.IsLocallyOfFinitePresentation B S hS m.hom
  exact HigherDiagonal.prop_isomMap_of_prop_mapBase B S hS f T hT x₁ x₂ P
    (prop_mapBase_of_prop_relativeDiagonal B S hS x₁ x₂ f P
      (fun U y hy F hF he => ⟨hsurjRel U y hy F hF he, hflatRel U y hy F hF he,
        hlfpRel U y hy F hF he⟩))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
