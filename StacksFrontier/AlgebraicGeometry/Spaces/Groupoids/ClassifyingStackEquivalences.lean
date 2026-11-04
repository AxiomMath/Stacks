module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.FppfTorsorsPrincipalComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorComparisonUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackTorsorEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare

/-!
# The classifying stack of a group algebraic space (Stacks 0CQJ)

Let `S` be a scheme, `B` an algebraic space over `S` and `G` a group algebraic space over `B`.
**Stacks 0CQJ** says that the four stacks in groupoids over `(Sch/S)_fppf`
`[B/G]`, `[[B/G]]`, `G-Torsors` and `𝒢/ℬ-Torsors` are canonically equivalent, and that when
`G ⟶ B` is flat and locally of finite presentation they are also equivalent to `G-Principal`.

Every equivalence here is an equivalence *over the big fppf site of `S`*, in the sense of
`StacksRepresentableCFG.EquivalenceOver`: 1-morphisms over the site in both directions, with unit
and counit whose components lie over identities.

## Main definitions

* `AlgebraicGeometry.Space.classifyingQuotientStackEquivalence`: **Stacks 0CQJ**, the leg
  `[B/G] ≌ [[B/G]]`; this is Stacks 04WM at `X = B` with the trivial action.
* `AlgebraicGeometry.Space.classifyingStackTorsorsEquivalenceOver`: `[[B/G]] ≌ G-Torsors` over
  the site, the equivalence `AlgebraicGeometry.Space.torsorWithMapEquivTorsorObj` (forget the
  equivariant map to `B`) followed by the identification of the library's two renderings of
  `G-Torsors`.
* `AlgebraicGeometry.Space.classifyingStackEquivalences`: **Stacks 0CQJ** in full — the chain
  `[B/G] ≌ [[B/G]] ≌ G-Torsors ≌ 𝒢/ℬ-Torsors`, and `G-Torsors ≌ G-Principal` when `G ⟶ B` is
  flat and locally of finite presentation, each with its canonical forward functor.

## Implementation notes

The proof is the source's: `[B/G] ≌ [[B/G]]` is Stacks 04WM
(`AlgebraicGeometry.Space.quotientStackTorsorEquivalence`) at `X = B`; `[[B/G]] = G-Torsors`
is the unwinding of the definition (Section 04UV), which is
`AlgebraicGeometry.Space.torsorWithMapEquivTorsorObj`; `G-Torsors ≌ 𝒢/ℬ-Torsors` is Stacks 04UT
(`AlgebraicGeometry.Space.FppfTorsors.nonempty_isEquivalenceOver_comparison`); and
`G-Torsors ≌ G-Principal` is `AlgebraicGeometry.Space.FppfTorsors.isEquivalenceOverPrincipal`.
Nothing is carried.

The library has two renderings of `G-Torsors`: `AlgebraicGeometry.Space.TorsorObj`, the one
`[[X/G]]` is built on, and `AlgebraicGeometry.Space.FppfTorsors`, the one the comparisons with
`𝒢/ℬ-Torsors` and `G-Principal` are built on.  They are field-for-field the same data,
identified by `AlgebraicGeometry.Space.torsorObjComparison` and its inverse, whose composites
are the identity on the nose.  The chain below passes through `FppfTorsors`.

Stacks 04UT is available only as the existence of an equivalence over the site with the
comparison functor as forward 1-morphism (its quasi-inverse is a choice); the chain therefore
fixes the forward functor of that leg to be `AlgebraicGeometry.Space.FppfTorsors.comparison` and
records that, so that the canonical functor, not merely some functor, is the equivalence.

## References

* [Stacks Project, Tag 0CQJ](https://stacks.math.columbia.edu/tag/0CQJ)
* [Stacks Project, Tag 04WM](https://stacks.math.columbia.edu/tag/04WM)
* [Stacks Project, Tag 04UT](https://stacks.math.columbia.edu/tag/04UT)
* [Stacks Project, Section 04UV](https://stacks.math.columbia.edu/tag/04UV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (hB : IsAlgebraicSpace 𝒞 S hS B)
  (G : GroupAlgebraicSpace 𝒞 S hS B hB)

/-- **Stacks 0CQJ**, the leg `[B/G] ≌ [[B/G]]`.  The quotient stack `[B/G]` of the trivial
action of `G` on `B` (Stacks 044Q part (2), the quotient stack of the action groupoid of
Stacks 0444) is equivalent over the big fppf site of `S` to `[[B/G]]`, the stack of fppf
`G`-torsors with an equivariant morphism to `B`.  This is Stacks 04WM at `X = B`. -/
@[stacks 0CQJ "the leg [B/G] ≌ [[B/G]] over the big fppf site, Stacks 04WM at X = B"]
def classifyingQuotientStackEquivalence :
    StacksRepresentableCFG.EquivalenceOver
      (Stack.quotientStackOfAction ⟨B, hB⟩ G.obj.X (𝟙_ (Over B)) G.property hB).p
      (TorsorWithMap.projection hB G (𝟙_ (Over B))) :=
  (quotientStackTorsorEquivalence hB G (𝟙_ (Over B)) hB).1

/-- `[[B/G]] ≌ G-Torsors` over the big fppf site of `S`: forget the equivariant morphism to `B`
(`AlgebraicGeometry.Space.torsorWithMapEquivTorsorObj`), then read the torsor in the rendering
`AlgebraicGeometry.Space.FppfTorsors`. -/
def classifyingStackTorsorsEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (TorsorWithMap.projection hB G (𝟙_ (Over B)))
      (FppfTorsors.projection hB G) where
  hom := ⟨TorsorWithMap.forget hB G (𝟙_ (Over B)) ⋙ torsorObjComparisonInverse hB G, rfl⟩
  inv := ⟨torsorObjComparison hB G ⋙ torsorObjToTorsorWithMap hB G, rfl⟩
  unitIso := torsorWithMapUnitIso hB G
  counitIso := Iso.refl _
  unit_over := by
    apply StacksRepresentableCFG.whiskerRight_eq_eqToHom
    intro A
    refine IsHomLift.of_fac _ _ _ rfl rfl ?_
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  counit_over := by
    apply StacksRepresentableCFG.whiskerRight_eq_eqToHom
    intro T
    exact (IsHomLift.id rfl : (FppfTorsors.projection hB G).IsHomLift (𝟙 T.base) (𝟙 T))

/-- The forward functor of `[[B/G]] ≌ G-Torsors` forgets the equivariant morphism to `B`. -/
theorem classifyingStackTorsorsEquivalenceOver_hom_functor :
    (classifyingStackTorsorsEquivalenceOver hB G).hom.functor =
      TorsorWithMap.forget hB G (𝟙_ (Over B)) ⋙ torsorObjComparisonInverse hB G :=
  rfl

/-- `G-Torsors ≌ 𝒢/ℬ-Torsors` over the big fppf site of `S` (Stacks 04UT), with forward functor
the comparison functor `AlgebraicGeometry.Space.FppfTorsors.comparison`. -/
def torsorsSheafTorsorsEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (FppfTorsors.projection hB G)
      (SheafTorsors.projection G.obj) :=
  StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (FppfTorsors.comparison_comp_projection hB G)
    (FppfTorsors.nonempty_isEquivalenceOver_comparison hB G).some

/-- `G-Torsors ≌ G-Principal` over the big fppf site of `S`, for `G ⟶ B` flat and locally of
finite presentation, with forward functor the canonical
`AlgebraicGeometry.Space.FppfTorsors.toPrincipal`. -/
def torsorsPrincipalEquivalenceOver (hflat : IsFlat 𝒞 S hS G.obj.X.hom)
    (hlfp : IsLocallyOfFinitePresentation 𝒞 S hS G.obj.X.hom) :
    StacksRepresentableCFG.EquivalenceOver (FppfTorsors.projection hB G)
      (PrincipalHomogeneousSpaces.projection hB G) :=
  StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (FppfTorsors.toPrincipal_comp_projection hB G)
    (FppfTorsors.isEquivalenceOverPrincipal hB G hflat hlfp)

/-- **Stacks 0CQJ.** Let `S` be a scheme, `B` an algebraic space over `S` and `G` a group
algebraic space over `B`.  Then the stacks in groupoids over `(Sch/S)_fppf`
`[B/G]`, `[[B/G]]`, `G-Torsors` and `𝒢/ℬ-Torsors` are all canonically equivalent: this gives
equivalences over the site
`[B/G] ≌ [[B/G]]`, `[[B/G]] ≌ G-Torsors` and `G-Torsors ≌ 𝒢/ℬ-Torsors`, and, if `G ⟶ B` is flat
and locally of finite presentation, `G-Torsors ≌ G-Principal`.

Each is the canonical one:
* the forward functor of `[B/G] ≌ [[B/G]]` extends the pointwise comparison `F_p`
  (`AlgebraicGeometry.Space.actionPointwiseComparison`) sending a point `b : U ⟶ B` to the
  trivial torsor, by a natural isomorphism lying over identities (Stacks 04WM at `X = B`);
* the forward functor of `[[B/G]] ≌ G-Torsors` forgets the equivariant map to `B`;
* the forward functor of `G-Torsors ≌ 𝒢/ℬ-Torsors` is the comparison functor of Stacks 04UT;
* the forward functor of `G-Torsors ≌ G-Principal` is the canonical inclusion
  `AlgebraicGeometry.Space.FppfTorsors.toPrincipal`. -/
@[stacks 0CQJ "the whole lemma: [B/G] ≌ [[B/G]] ≌ G-Torsors ≌ 𝒢/ℬ-Torsors over the big fppf \
site, and G-Torsors ≌ G-Principal for G ⟶ B flat and locally of finite presentation, each with \
its canonical forward functor"]
def classifyingStackEquivalences :
    { c : StacksRepresentableCFG.EquivalenceOver
          (Stack.quotientStackOfAction ⟨B, hB⟩ G.obj.X (𝟙_ (Over B)) G.property hB).p
          (TorsorWithMap.projection hB G (𝟙_ (Over B))) ×
        StacksRepresentableCFG.EquivalenceOver (TorsorWithMap.projection hB G (𝟙_ (Over B)))
          (FppfTorsors.projection hB G) ×
        StacksRepresentableCFG.EquivalenceOver (FppfTorsors.projection hB G)
          (SheafTorsors.projection G.obj) ×
        (IsFlat 𝒞 S hS G.obj.X.hom → IsLocallyOfFinitePresentation 𝒞 S hS G.obj.X.hom →
          StacksRepresentableCFG.EquivalenceOver (FppfTorsors.projection hB G)
            (PrincipalHomogeneousSpaces.projection hB G)) //
      (∃ α : Stack.pointwiseToQuotientStack
            (groupoidOfAction ⟨B, hB⟩ G.obj.X (𝟙_ (Over B)) G.property hB).groupoid ⋙
              c.1.hom.functor ≅
            actionPointwiseComparison hB G (𝟙_ (Over B)) hB,
          ∀ A : (actionPointwiseCategory hB G (𝟙_ (Over B)) hB).obj,
            (TorsorWithMap.projection hB G (𝟙_ (Over B))).IsHomLift (𝟙 A.base) (α.hom.app A)) ∧
        c.2.1.hom.functor =
          TorsorWithMap.forget hB G (𝟙_ (Over B)) ⋙ torsorObjComparisonInverse hB G ∧
        c.2.2.1.hom.functor = FppfTorsors.comparison hB G ∧
        ∀ hflat hlfp, (c.2.2.2 hflat hlfp).hom.functor = FppfTorsors.toPrincipal hB G } :=
  ⟨(classifyingQuotientStackEquivalence hB G, classifyingStackTorsorsEquivalenceOver hB G,
      torsorsSheafTorsorsEquivalenceOver hB G, torsorsPrincipalEquivalenceOver hB G),
    (quotientStackTorsorEquivalence hB G (𝟙_ (Over B)) hB).2, rfl, rfl, fun _ _ => rfl⟩

end AlgebraicGeometry.Space

end
