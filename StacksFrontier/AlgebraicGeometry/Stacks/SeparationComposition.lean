module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalFunctoriality
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# The separation axioms and composition (Stacks 050K)

Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over a scheme `S` contained
in a big fppf site `B`. **Stacks 050K** says that each of the four separation axioms of
**Stacks 04YW** — DM, quasi-DM, separated, quasi-separated — holds for `f ≫ g` as soon as it
holds for `f` and for `g`.

The proof is the source's. The relative diagonal of the composite factors as

```text
  Δ_{f ≫ g} : 𝒳 --Δ_f--> 𝒳 ×_𝒴 𝒳 --i--> 𝒳 ×_𝒵 𝒳,
```

with `i = AlgebraicGeometry.Stack.AlgebraicStacks.mapBase` the comparison 1-morphism, which is a
base change of `Δ_g` (**Stacks 050H**). So each axiom for `f ≫ g` is the composition of its
condition of Properties of Stacks, Section 04XB, for `Δ_f` — the axiom for `f` — with the same
condition for `i`, which the corresponding clause of Stacks 050H supplies from the axiom for `g`;
and composition of a condition of Stacks 04XB is **Stacks 045B**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal_comp`: the factorization
  `Δ_{f ≫ g} = Δ_f ≫ i`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableByAlgebraicSpaces_mapBase`: the
  comparison 1-morphism is representable by algebraic spaces, being a base change of `Δ_g`
  (**Stacks 0302**).
* `AlgebraicGeometry.Stack.AlgebraicStacks.prop_relativeDiagonal_comp`: the argument above,
  uniformly in the property `P`. This is the whole content of Stacks 050K, and the four clauses
  are its four specialisations.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_comp`: **Stacks 050K**, DM.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_comp`: **Stacks 050K**, quasi-DM.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_comp`: **Stacks 050K**, separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_comp`: **Stacks 050K**,
  quasi-separated, both halves of the conjunction.

## Implementation notes

The composition step is `AlgebraicGeometry.Stack.prop_comp_of_atlasDescent`, the form of Stacks
045B whose conclusion is the condition of Stacks 04XB written out longhand and whose locality
hypothesis is descent along a surjective étale scheme chart of the target. That is the hypothesis
`prop_relativeDiagonal_comp` carries, rather than the
`CategoryTheory.MorphismProperty.IsLocalAtTarget` instance for the fppf precoverage that the
instance form `AlgebraicGeometry.Stack.hasRelativeProperty_comp` demands, because chart descent
is strictly weaker and is what the four clauses can supply unconditionally:

* unramifiedness, by `AlgebraicGeometry.Space.unramifiedMorphismProperty_of_pullbackSnd_atlas`;
* local quasi-finiteness, quasi-compactness and quasi-separatedness, from their locality at the
  fpqc precoverage (**Stacks 0427**, **Stacks 041L**, **Stacks 041N**) through
  `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le` at
  `AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage` and then
  `AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas`. The transport is written out at each use
  site rather than registered globally, which is the decision recorded in the implementation
  notes of `StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison`;
* properness, by `AlgebraicGeometry.Space.properMorphismProperty_of_pullbackSnd_atlas`.

The last of these is why the separated clause needs no fpqc locality statement for properness,
i.e. neither Stacks 0422 nor, through it, Gabber's Stacks 0APL: only the three conjuncts of
properness have to descend along one étale chart, and each of them does — see that declaration.

Quasi-separatedness of Stacks 04YW is a conjunction of two conditions of Stacks 04XB, so its
clause runs the same argument twice, once at each property, and states both halves in the one
declaration that carries the tag.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **The relative diagonal of a composite factors through the comparison 1-morphism.** For
1-morphisms `f : 𝒳 ⟶ 𝒴` and `g : 𝒴 ⟶ 𝒵` of algebraic stacks over `S`,
`Δ_{f ≫ g} = Δ_f ≫ i` with `i : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳` the comparison 1-morphism of
`AlgebraicGeometry.Stack.AlgebraicStacks.mapBase`. -/
theorem relativeDiagonal_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    relativeDiagonal B S hS (f ≫ g) =
      relativeDiagonal B S hS f ≫ mapBase B S hS f f g := by
  apply Bicategory.InducedBicategory.hom_ext
  apply Bicategory.InducedBicategory.hom_ext
  apply BasedCategory.BasedFunctor.ext'
  exact (TwoFibreProductOver.diagonal_comp_mapBase
    (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p (f ≫ g).hom)).symm

/-- **The comparison 1-morphism is representable by algebraic spaces.** It is a base change of the
relative diagonal `Δ_{𝒵/𝒯}` (`AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseSquare`), which is
representable by algebraic spaces by **Stacks 04XS**, part (1); representability by algebraic
spaces is stable under base change by **Stacks 0302**. -/
theorem isRepresentableByAlgebraicSpaces_mapBase {𝒯 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯) :
    IsRepresentableByAlgebraicSpaces B S hS (mapBase B S hS f g h).hom.hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, u, u} B S hS 𝒵.val
    (twoFibreProduct B S hS h h).val (twoFibreProduct B S hS (f ≫ h) (g ≫ h)).val
    (_root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val h.hom)
    (mapCospan B S hS f g h).hom
    (mapBaseSquare B S hS f g h) (isTwoFibreProduct_mapBaseSquare B S hS f g h)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS h)

/-- The underlying functor of `Δ_{f ≫ g}` is that of `Δ_f` followed by that of `i`. -/
private theorem relativeDiagonal_comp_hom (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) :
    _root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒵.val
        (f ≫ g).hom =
      (relativeDiagonal B S hS f).hom ≫ (mapBase B S hS f f g).hom := by
  rw [← Bicategory.InducedBicategory.bicategory_comp_hom]
  exact congrArg (fun q => q.hom) (relativeDiagonal_comp B S hS f g)

/-- **Stacks 050K, DM.** The composite of two Deligne–Mumford 1-morphisms of algebraic stacks over
`S` is Deligne–Mumford: its relative diagonal is `Δ_f` followed by the comparison 1-morphism `i`,
`Δ_f` is unramified in the sense of Stacks 04XB because `f` is DM, `i` is unramified because `g`
is DM (**Stacks 050H**, part (4)), and a condition of Stacks 04XB at a property stable under
composition which descends along a surjective étale scheme chart of the target is stable under
composition (**Stacks 045B**). -/
@[stacks 050K "dm"]
theorem isDM_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hf : Stack.IsDM B S hS f)
    (hg : Stack.IsDM B S hS g) : Stack.IsDM B S hS (f ≫ g) := by
  refine ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS (f ≫ g), ?_⟩
  rw [relativeDiagonal_comp_hom]
  exact prop_comp_of_atlasDescent B S hS (Space.unramifiedMorphismProperty B S hS)
    (fun {_X _Y} k {_T} {_a} hsurj hetale hk =>
      Space.unramifiedMorphismProperty_of_pullbackSnd_atlas B S hS k hsurj hetale hk)
    (relativeDiagonal B S hS f).hom (mapBase B S hS f f g).hom
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
    (isRepresentableByAlgebraicSpaces_mapBase B S hS f f g) hf.2
    (isUnramified_mapBase_of_isDM B S hS f f g hg)

/-- **The separation axioms of Stacks 04YW compose, uniformly in the property `P`.**

Let `P` be a property of morphisms of algebraic spaces over `S` which respects isomorphisms, is
stable under composition, and may be tested on the base change of a morphism to a surjective
étale scheme chart of its target. If the relative diagonal `Δ_f` of `f : 𝒳 ⟶ 𝒴` satisfies the
condition of Stacks 04XB for `P`, and so does the comparison 1-morphism
`i : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳`, then so does the relative diagonal `Δ_{f ≫ g}` of the composite.

This is the whole content of **Stacks 050K**: each of the four separation axioms of Stacks 04YW
is "`Δ_f` satisfies the condition of Stacks 04XB for `P`" at one such `P`, the hypothesis on `i`
is supplied from the axiom for `g` by the corresponding clause of **Stacks 050H**, and the four
clauses of Stacks 050K are the four specialisations of this one statement. The factorization
`Δ_{f ≫ g} = Δ_f ≫ i` is
`AlgebraicGeometry.Stack.AlgebraicStacks.relativeDiagonal_comp`, and the composition step is
`AlgebraicGeometry.Stack.prop_comp_of_atlasDescent`, the form of **Stacks 045B** whose locality
hypothesis is descent along a surjective étale scheme chart. -/
theorem prop_relativeDiagonal_comp
    (P : CategoryTheory.MorphismProperty (AlgebraicSpaces B S hS))
    [P.RespectsIso] [P.IsStableUnderComposition]
    (hatlas : ∀ {X Y : AlgebraicSpaces B S hS} (k : X ⟶ Y) {T : BigFppfOver B S hS}
      {a : yoneda.obj T ⟶ Y.obj},
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a →
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a →
      P (Limits.pullback.snd k (ObjectProperty.homMk a :
        (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ Y)) → P k)
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hPf : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ (twoFibreProduct B S hS f f).val.val.obj)
      (_hy : y ⋙ (twoFibreProduct B S hS f f).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (twoFibreProduct B S hS f f).val.val.p y
            (CatFiberedInGroupoids.homFunctor
              (_root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
                𝒴.val f.hom)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)))
    (hPi : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.obj)
      (_hz : z ⋙ (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (twoFibreProduct B S hS f f).val.val.p
            (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.p z
            (CatFiberedInGroupoids.homFunctor (mapBase B S hS f f g).hom))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.obj)
      (_hz : z ⋙ (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (twoFibreProduct B S hS (f ≫ g) (f ≫ g)).val.val.p z
            (CatFiberedInGroupoids.homFunctor
              (_root_.AlgebraicGeometry.Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
                𝒵.val (f ≫ g).hom)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  rw [relativeDiagonal_comp_hom]
  exact prop_comp_of_atlasDescent B S hS P hatlas
    (AlgebraicStacks.relativeDiagonal B S hS f).hom (mapBase B S hS f f g).hom
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
    (isRepresentableByAlgebraicSpaces_mapBase B S hS f f g) hPf hPi

/-- **Stacks 050K, quasi-DM.** The composite of two quasi-DM 1-morphisms of algebraic stacks over
`S` is quasi-DM: `Δ_{f ≫ g}` is `Δ_f` followed by the comparison 1-morphism `i`, `Δ_f` is locally
quasi-finite in the sense of Stacks 04XB because `f` is quasi-DM, `i` is locally quasi-finite
because `g` is quasi-DM (**Stacks 050H**, part (5)), and local quasi-finiteness of morphisms of
algebraic spaces over `S` composes (**Stacks 03XK**) and is fpqc local on the base
(**Stacks 0427**). -/
@[stacks 050K "quasi-DM"]
theorem isQuasiDM_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hf : IsQuasiDM B S hS f)
    (hg : IsQuasiDM B S hS g) : IsQuasiDM B S hS (f ≫ g) := by
  have : (Space.locallyQuasiFiniteProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact prop_relativeDiagonal_comp B S hS (Space.locallyQuasiFiniteProperty B S hS)
    (fun {_X _Y} k {_T} {_a} hsurj hetale hk =>
      (Space.prop_iff_pullbackSnd_atlas.{u, u} B S hS _ k hsurj hetale).2 hk)
    f g hf (isLocallyQuasiFinite_mapBase_of_isQuasiDM B S hS f f g hg)

/-- **Stacks 050K, separated.** The composite of two separated 1-morphisms of algebraic stacks
over `S` is separated: `Δ_{f ≫ g}` is `Δ_f` followed by the comparison 1-morphism `i`, `Δ_f` is
proper in the sense of Stacks 04XB because `f` is separated, `i` is proper because `g` is
separated (**Stacks 050H**, part (6)), and properness of morphisms of algebraic spaces over `S`
composes (**Stacks 04XY**) and descends along a surjective étale scheme chart of the target
(`AlgebraicGeometry.Space.properMorphismProperty_of_pullbackSnd_atlas`). -/
@[stacks 050K "separated"]
theorem isSeparated_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hf : IsSeparated B S hS f)
    (hg : IsSeparated B S hS g) : IsSeparated B S hS (f ≫ g) :=
  prop_relativeDiagonal_comp B S hS (Space.properProperty B S hS)
    (fun {_X _Y} k {_T} {_a} hsurj hetale hk =>
      Space.properMorphismProperty_of_pullbackSnd_atlas B S hS k hsurj hetale hk)
    f g hf (isProper_mapBase_of_isSeparated B S hS f f g hg)

/-- **Stacks 050K, quasi-separated.** The composite of two quasi-separated 1-morphisms of
algebraic stacks over `S` is quasi-separated. Quasi-separatedness of Stacks 04YW is the
conjunction of two conditions of Stacks 04XB on `Δ_f` — quasi-compactness and
quasi-separatedness — and each half is the same composition argument at its own property:
`Δ_{f ≫ g} = Δ_f ≫ i`, the half for `Δ_f` is the axiom for `f`, the half for `i` comes from the
axiom for `g` by **Stacks 050H**, part (7), and quasi-compactness and quasi-separatedness of
morphisms of algebraic spaces over `S` compose (**Stacks 03HG**, **Stacks 03KQ**) and are fpqc
local on the base (**Stacks 041L**, **Stacks 041N**). -/
@[stacks 050K "quasi-separated"]
theorem isQuasiSeparated_comp (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵) (hf : IsQuasiSeparated B S hS f)
    (hg : IsQuasiSeparated B S hS g) : IsQuasiSeparated B S hS (f ≫ g) := by
  have : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  have : (Space.quasiSeparatedProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u} B S hS)
  exact ⟨prop_relativeDiagonal_comp B S hS (Space.quasiCompactProperty B S hS)
      (fun {_X _Y} k {_T} {_a} hsurj hetale hk =>
        (Space.prop_iff_pullbackSnd_atlas.{u, u} B S hS _ k hsurj hetale).2 hk)
      f g hf.1 (isQuasiCompactAndQuasiSeparated_mapBase B S hS f f g hg).1,
    prop_relativeDiagonal_comp B S hS (Space.quasiSeparatedProperty B S hS)
      (fun {_X _Y} k {_T} {_a} hsurj hetale hk =>
        (Space.prop_iff_pullbackSnd_atlas.{u, u} B S hS _ k hsurj hetale).2 hk)
      f g hf.2 (isQuasiCompactAndQuasiSeparated_mapBase B S hS f f g hg).2⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
