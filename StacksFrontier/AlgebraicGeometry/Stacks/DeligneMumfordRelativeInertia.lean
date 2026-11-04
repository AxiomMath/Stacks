module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalSeparatednessRelativeInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

/-!
# Stacks 0CL0, parts (4) and (5): the relative inertia detects DM and quasi-DM

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. Parts (4) and (5) of
**Stacks 0CL0** assert

* **(4)** `π : I_{𝒳/𝒴} ⟶ 𝒳` is unramified `↔` `f` is DM;
* **(5)** `π : I_{𝒳/𝒴} ⟶ 𝒳` is locally quasi-finite `↔` `f` is quasi-DM,

both conditions on `π` in the relative sense of Properties of Stacks, Section 04XB. Part (3) of
the same lemma, on local separatedness, is
`StacksFrontier/AlgebraicGeometry/Stacks/LocalSeparatednessRelativeInertia.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/SecondRelativeDiagonalInertia.lean`; nothing there is
changed by this file, which only adds the two further parts alongside.

## What is proved and what is carried

The direction **(b) ⇒ (a)** is proved outright, for both parts, and with no hypothesis on the
property tested. The reason is the one the part-(3) file already exploits: `π` is, up to an
equivalence over `𝒳`, the first projection `pr₁` of the 2-fibre product of `Δ_f` with itself,
and `pr₁` is a base change of `Δ_f`. Transport along the equivalence is **Stacks 0457** in the
hypothesis-free form `AlgebraicGeometry.Stack.relativeProperty_of_equivalences`, and the base
change is **Stacks 045C** in the form `AlgebraicGeometry.Stack.relativeProperty_baseChange`;
both are stated over an arbitrary `CategoryTheory.MorphismProperty`, so they apply verbatim at
unramifiedness and at local quasi-finiteness.

The direction **(a) ⇒ (b)** is not proved here; it is stated, as
`AlgebraicGeometry.Stack.IsDMOfIsRelativelyUnramifiedRelativeInertiaProjection` and
`AlgebraicGeometry.Stack.IsQuasiDMOfIsLocallyQuasiFiniteRelativeInertiaProjection`. Both parts,
in both directions, are
`Stack.isRelativelyUnramified_relativeInertiaProjection_iff_isDM_unconditional` and
`Stack.isLocallyQuasiFinite_relativeInertiaProjection_iff_isQuasiDM_unconditional` in
`StacksFrontier/AlgebraicGeometry/Stacks/DeligneMumfordRelativeInertiaConverse.lean`. For part (3)
that direction is the section argument: `Δ_{f,2}` is a section of `pr₁`, and a section of a
locally separated 1-morphism is an immersion. **That argument gives nothing here.**
Unramifiedness and local quasi-finiteness are cancellable in the first factor
(`AlgebraicGeometry.Space.isUnramified_of_comp`, **Stacks 06G6**, and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_comp`, **Stacks 03XN**), so *every* section is
automatically unramified and locally quasi-finite and the hypothesis is never used. The source
instead goes through the group structure on `I_{𝒳/𝒴}` and Groupoids in Spaces, Lemma **06P6**;
the composition law is `CategoryTheory.RelativeInertia.composition` (**Stacks 050R**) but the
group-object axioms for it are not proved in this library, so that route is not yet open.

## Main definitions

* `AlgebraicGeometry.Stack.IsRelativelyUnramified`: the notion of Section 04XB for
  `AlgebraicGeometry.Space.IsUnramified`, i.e. condition (a) of part (4). This is the sibling of
  `AlgebraicGeometry.Stack.IsLocallyQuasiFinite` and
  `AlgebraicGeometry.Stack.IsLocallySeparated`; the unqualified name
  `AlgebraicGeometry.Stack.IsUnramified` is already **Stacks 0CIT**, a different condition.

## Main results

* `AlgebraicGeometry.Stack.isRelativelyUnramified_relativeInertiaProjection_of_isDM` and
  `AlgebraicGeometry.Stack.isLocallyQuasiFinite_relativeInertiaProjection_of_isQuasiDM`: the
  (b) ⇒ (a) halves of parts (4) and (5), unconditionally.

## Implementation notes

`AlgebraicGeometry.Stack.IsDM` bundles the representability of `Δ_f` by algebraic spaces as an
existential witness alongside the relative unramifiedness. For algebraic stacks that witness is
a theorem,
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks`
(**Stacks 04XS**, part (1)), so it is supplied rather than assumed wherever `IsDM` has to be
produced.

The two packaged morphism properties used below are the public
`AlgebraicGeometry.Space.unramifiedMorphismProperty` and
`AlgebraicGeometry.Space.locallyQuasiFiniteProperty`, imported from
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleChartTargetDescent.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/QuasiFiniteMorphismProperty.lean`; only the packaging is
used here, never a hypothesis on it.

## References

* [Stacks Project, Tag 03XN](https://stacks.math.columbia.edu/tag/03XN)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 050R](https://stacks.math.columbia.edu/tag/050R)
* [Stacks Project, Tag 06G6](https://stacks.math.columbia.edu/tag/06G6)
* [Stacks Project, Tag 06P6](https://stacks.math.columbia.edu/tag/06P6)
* [Stacks Project, Tag 0CL0](https://stacks.math.columbia.edu/tag/0CL0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

section Defn

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is unramified* when every algebraic space representing its
base change along a scheme-valued point of the target has unramified structural morphism, read
as a morphism of algebraic spaces over `S`. This is the notion of Stacks 04XB for
`AlgebraicGeometry.Space.IsUnramified` (**Stacks 03ZH**, part (1)), and it is condition (a) of
part (4) of **Stacks 0CL0**.

The name carries `Relatively` because `AlgebraicGeometry.Stack.IsUnramified` is already taken by
**Stacks 0CIT**, the condition on a 1-morphism of algebraic stacks that it be DM with unramified
étale-smooth diagrams; the convention is that of
`AlgebraicGeometry.Stack.IsRelativelyEtale` and `AlgebraicGeometry.Stack.IsRelativelySmooth`. -/
abbrev IsRelativelyUnramified (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsUnramified B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

end Defn

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Inertia

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 0CL0, part (4), the direction (b) ⇒ (a).** If `f` is DM then its relative inertia
projection `π : I_{𝒳/𝒴} ⟶ 𝒳` is unramified in the sense of Section 04XB.

`π` is carried onto the first projection `pr₁` of the 2-fibre product of `Δ_f` with itself by
the equivalence `AlgebraicGeometry.Stack.relativeInertiaToSecondRelativeDiagonal`, and `pr₁` is
a base change of `Δ_f`. Neither transport needs a hypothesis on the property. -/
theorem isRelativelyUnramified_relativeInertiaProjection_of_isDM (f : 𝒳 ⟶ 𝒴)
    (h : IsDM B S hS f) :
    IsRelativelyUnramified B S hS (relativeInertiaProjection B S hS f).hom :=
  @relativeProperty_of_equivalences B S hS _ _ _ _ (Space.unramifiedMorphismProperty B S hS)
    (relativeInertiaProjection B S hS f).hom.hom
    (twoFibreProductSquareAlgebraicStacks B S hS
      (relativeDiagonalAlgebraicStacks B S hS f)
      (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom.hom
    (relativeInertiaToSecondRelativeDiagonal B S hS f.hom).hom
    (BasedFunctor.id 𝒳.val.val) (eqToIso rfl)
    (isEquivalence_relativeInertiaToSecondRelativeDiagonal B S hS f.hom)
    (isEquivalence_basedFunctorId B S hS 𝒳.val)
    (relativeProperty_baseChange.{u, u, u + 1} B S hS (Space.unramifiedMorphismProperty B S hS)
      𝒳.val (twoFibreProductAlgebraicStack B S hS f f).val 𝒳.val
      (relativeDiagonalAlgebraicStacks B S hS f).hom
      (relativeDiagonalAlgebraicStacks B S hS f).hom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (relativeDiagonalAlgebraicStacks B S hS f).hom
        (relativeDiagonalAlgebraicStacks B S hS f).hom)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (relativeDiagonalAlgebraicStacks B S hS f).hom
        (relativeDiagonalAlgebraicStacks B S hS f).hom)
      h.choose_spec)

/-- **Stacks 0CL0, part (5), the direction (b) ⇒ (a).** If `f` is quasi-DM then its relative
inertia projection `π : I_{𝒳/𝒴} ⟶ 𝒳` is locally quasi-finite in the sense of Section 04XB. The
proof is that of
`AlgebraicGeometry.Stack.isRelativelyUnramified_relativeInertiaProjection_of_isDM` at the
packaged property of local quasi-finiteness. -/
theorem isLocallyQuasiFinite_relativeInertiaProjection_of_isQuasiDM (f : 𝒳 ⟶ 𝒴)
    (h : AlgebraicStacks.IsQuasiDM B S hS f) :
    IsLocallyQuasiFinite B S hS (relativeInertiaProjection B S hS f).hom :=
  @relativeProperty_of_equivalences B S hS _ _ _ _ (Space.locallyQuasiFiniteProperty B S hS)
    (relativeInertiaProjection B S hS f).hom.hom
    (twoFibreProductSquareAlgebraicStacks B S hS
      (relativeDiagonalAlgebraicStacks B S hS f)
      (relativeDiagonalAlgebraicStacks B S hS f)).fst.hom.hom
    (relativeInertiaToSecondRelativeDiagonal B S hS f.hom).hom
    (BasedFunctor.id 𝒳.val.val) (eqToIso rfl)
    (isEquivalence_relativeInertiaToSecondRelativeDiagonal B S hS f.hom)
    (isEquivalence_basedFunctorId B S hS 𝒳.val)
    (relativeProperty_baseChange.{u, u, u + 1} B S hS (Space.locallyQuasiFiniteProperty B S hS)
      𝒳.val (twoFibreProductAlgebraicStack B S hS f f).val 𝒳.val
      (relativeDiagonalAlgebraicStacks B S hS f).hom
      (relativeDiagonalAlgebraicStacks B S hS f).hom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (relativeDiagonalAlgebraicStacks B S hS f).hom
        (relativeDiagonalAlgebraicStacks B S hS f).hom)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (relativeDiagonalAlgebraicStacks B S hS f).hom
        (relativeDiagonalAlgebraicStacks B S hS f).hom)
      h)

/-- **The direction (a) ⇒ (b) of part (4) of Stacks 0CL0, carried.** That an unramified relative
inertia projection forces `f` to be DM.

The source deduces this from the group structure on `I_{𝒳/𝒴}` through Groupoids in Spaces,
Lemma **06P6**; the composition law `CategoryTheory.RelativeInertia.composition` (**Stacks
050R**) is in the library but its group-object axioms are not, so the deduction is not available.
The section argument that settles the corresponding direction of part (3) cannot replace it:
unramifiedness is cancellable in the first factor (**Stacks 06G6**), so every section is
unramified and the hypothesis would go unused. -/
abbrev IsDMOfIsRelativelyUnramifiedRelativeInertiaProjection : Prop :=
  ∀ (𝒰 𝒱 : AlgebraicStacks.{u, w} B S hS) (g : 𝒰 ⟶ 𝒱),
    IsRelativelyUnramified B S hS (relativeInertiaProjection B S hS g).hom → IsDM B S hS g

/-- **The direction (a) ⇒ (b) of part (5) of Stacks 0CL0, carried.** The quasi-DM twin of
`AlgebraicGeometry.Stack.IsDMOfIsRelativelyUnramifiedRelativeInertiaProjection`; the source
obtains it the same way, and local quasi-finiteness is cancellable in the first factor by
**Stacks 03XN**, so the section argument is equally unavailable. -/
abbrev IsQuasiDMOfIsLocallyQuasiFiniteRelativeInertiaProjection : Prop :=
  ∀ (𝒰 𝒱 : AlgebraicStacks.{u, w} B S hS) (g : 𝒰 ⟶ 𝒱),
    IsLocallyQuasiFinite B S hS (relativeInertiaProjection B S hS g).hom →
      AlgebraicStacks.IsQuasiDM B S hS g

end Inertia

end AlgebraicGeometry.Stack

end
