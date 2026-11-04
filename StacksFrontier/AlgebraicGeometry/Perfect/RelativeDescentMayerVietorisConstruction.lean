module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentMayerVietoris

/-!
# The restriction and difference maps of the Mayer--Vietoris union step of Tag 0DI7

`AlgebraicGeometry.RelativeDescentSituation.MayerVietorisHomSequence` of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentMayerVietoris.lean` packages the
Mayer--Vietoris sequence of Stacks 08BW read on the four systems of derived morphism sets of a
relative descent situation restricted to `U₀`, `V₀`, `U₀ ∩ V₀` and `U₀ ∪ V₀`: its six maps at
the stages and at the limit, their naturality, and exactness at all three kinds of spot.

Four of those six maps are not Mayer--Vietoris at all. The restriction map and the difference
map, at a stage and at the limit, are built out of restriction along an inclusion of
quasi-compact opens of `X₀`, which the relative descent situation already carries as
`AlgebraicGeometry.RelativeDescentSituation.homRestrictToSmaller` and
`homRestrictToSmallerLimit`. This file makes those restrictions group homomorphisms, assembles
the four maps out of them, proves their naturality in the stage and their compatibility with
the comparison maps to the limit, and records the result as a constructor for
`MayerVietorisHomSequence` whose remaining data are the two connecting homomorphisms, their
naturality, and the six exactness statements.

## Main definitions

* `Stacks.DerivedPullback.schemeFactorTowerAddHom`: the map on derived morphism sets attached to
  a commutative square of morphisms of schemes with factored horizontal edges, as a group
  homomorphism.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomSmaller` and
  `restrictHomSmallerLimit`: restriction from `U₀` to a smaller quasi-compact open `V₀` on the
  derived morphism sets of the restricted situations, at a stage and at the limit, as group
  homomorphisms.
* `AlgebraicGeometry.RelativeDescentSituation.mayerVietorisStageRestriction`,
  `mayerVietorisStageDifference`, `mayerVietorisLimitRestriction` and
  `mayerVietorisLimitDifference`: the restriction and difference maps of the Mayer--Vietoris
  sequence on those systems, at a stage and at the limit.
* `AlgebraicGeometry.RelativeDescentSituation.restrictRangeToFixedStage`: the inclusion of the
  open range of `Vᵢ ⟶ Uᵢ`, followed by the map of `Uᵢ` to `U₀`; the edge along which the
  Mayer--Vietoris Ext sequence of Stacks 08BW restricts.
* `AlgebraicGeometry.RelativeDescentSituation.mayerVietorisHomSequenceOfBoundary`: **the
  Mayer--Vietoris sequence of the union step from its connecting homomorphisms alone.** The four
  restriction and difference maps and their four naturality and comparison statements are
  supplied; what is left to provide is the two connecting homomorphisms, the naturality of the
  stage one, the compatibility of the limit one with the comparison maps, and the six exactness
  statements.

## Main results

* `Stacks.DerivedPullback.schemeFactorTowerHom_add`: the map attached to such a square is
  additive, derived pullback being a triangulated functor and hence additive.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomTransition_restrictHomSmaller` and
  `restrictHomComparison_restrictHomSmaller`: restriction to a smaller quasi-compact open
  commutes with the transition maps and with the comparison maps of the systems.
* `AlgebraicGeometry.RelativeDescentSituation.mayerVietorisStageRestriction_transition`,
  `mayerVietorisStageDifference_transition`,
  `mayerVietorisLimitRestriction_comparison` and `mayerVietorisLimitDifference_comparison`: the
  four naturality and comparison statements of `MayerVietorisHomSequence` that concern the
  restriction and difference maps.
* In `AlgebraicGeometry.RelativeDescentSituation`,
  `opensRange_restrictToLarger_sup_opensRange_restrictToLarger` and
  `opensRange_restrictToLargerLimit_sup_opensRange_restrictToLargerLimit`: **the preimages of
  `U₀` and of `V₀` cover the restriction to `U₀ ∪ V₀`**, at a stage and at the limit. This is the
  hypothesis `U ⊔ V = ⊤` under which the Mayer--Vietoris sequence of Stacks 08BW is available.
* `Stacks.DerivedPullback.bijective_factorTowerHom` and `bijective_schemeFactorTowerHom`: the map
  attached to such a square whose vertical edge is an isomorphism is bijective.
* In `AlgebraicGeometry.RelativeDescentSituation`,
  `homRestrictToSmaller_eq_schemeFactorTowerHom_isoOpensRange` and
  `bijective_schemeFactorTowerHom_isoOpensRange`: **restriction from `U₀` to `V₀` is
  restriction along the inclusion of an open subscheme, followed by a bijection.** The first step
  restricts to the open range of `Vᵢ ⟶ Uᵢ`, which is the shape Stacks 08BW is stated in; the
  second transports along the canonical isomorphism of `Vᵢ` with that open range, and is
  bijective, so exactness transports across it.

## Implementation notes

The difference map carries the Mayer--Vietoris sign as an honest subtraction of the two
restrictions to `U₀ ∩ V₀` rather than as a sum against a negated inclusion, which is what makes
its naturality the group-homomorphism identity `map_sub` applied to the transition map together
with the naturality of restriction.

Additivity of restriction to a smaller open is additivity of
`Stacks.DerivedPullback.schemeFactorTowerHom`, which is built from `Iso.homCongr` of the derived
pullback along the vertical edge of the square; conjugation by isomorphisms is additive in a
preadditive category, and the derived pullback is additive because it is triangulated.

The two connecting homomorphisms are left as data. They are not restriction along an inclusion
of opens: producing them is Stacks 08BW proper, the long exact sequence of the Mayer--Vietoris
distinguished triangle of Stacks 08BU. The named, non-existential form of that sequence has terms
that are morphism groups out of the extensions by zero on one fixed ringed space; the existential
form in `StacksFrontier/Topology/Sheaves/Cohomology/MayerVietoris/ExtSequence.lean` cannot serve here,
because the connecting homomorphism it produces carries no naturality clause, while
`MayerVietorisHomSequence` asks for naturality of its connecting homomorphism in the stage.

The two cover lemmas and the two bijectivity results above are the geometric and transport
halves of that identification: they put the stage of the restriction to `U₀ ∪ V₀` in the shape
08BW consumes — a ringed space with two opens covering it — and they identify restriction along
`restrictToLarger` with restriction along an open-subscheme inclusion, up to a bijection of
groups.

The union step of Stacks 0DI7 itself is run through the triangle of Stacks 08BU in the first
argument, in `StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentHomDescentUnion.lean`, where
every map of the long exact sequences is precomposition with the derived pullback of a fixed
morphism over `U₀ ∪ V₀`.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.DerivedPullback

/-! ### Additivity of the map attached to a square with factored horizontal edges -/

variable {A B Y Y' Z : Scheme.{u}}

/-- **The map on derived morphism sets attached to a commutative square with factored horizontal
edges is additive.** It is the derived pullback along the vertical edge of the square, conjugated
by the comparison isomorphisms of Tag 0D5S; conjugation by an isomorphism is additive and the
derived pullback is a triangulated functor, hence additive. -/
theorem schemeFactorTowerHom_add (r : A ⟶ B) (g : B ⟶ Y) (p : Y ⟶ Z) (e : A ⟶ Y') (q : Y' ⟶ Z)
    (h : r ≫ g ≫ p = e ≫ q)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ φ' : (derivedPullback g.toLRSHom.toShHom).obj
          ((derivedPullback p.toLRSHom.toShHom).obj K) ⟶
        (derivedPullback g.toLRSHom.toShHom).obj ((derivedPullback p.toLRSHom.toShHom).obj L)) :
    schemeFactorTowerHom r g p e q h K L (φ + φ') =
      schemeFactorTowerHom r g p e q h K L φ + schemeFactorTowerHom r g p e q h K L φ' := by
  simp only [schemeFactorTowerHom, factorTowerHom, factorEquiv, factorHom, Iso.homCongr_symm,
    Iso.homCongr_apply, Iso.symm_hom, Iso.symm_inv, Functor.map_add, Preadditive.comp_add,
    Preadditive.add_comp]

/-- The map on derived morphism sets attached to a commutative square of morphisms of schemes
with factored horizontal edges, as a group homomorphism. -/
def schemeFactorTowerAddHom (r : A ⟶ B) (g : B ⟶ Y) (p : Y ⟶ Z) (e : A ⟶ Y') (q : Y' ⟶ Z)
    (h : r ≫ g ≫ p = e ≫ q)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    ((derivedPullback g.toLRSHom.toShHom).obj ((derivedPullback p.toLRSHom.toShHom).obj K) ⟶
        (derivedPullback g.toLRSHom.toShHom).obj
          ((derivedPullback p.toLRSHom.toShHom).obj L)) →+
      ((derivedPullback e.toLRSHom.toShHom).obj ((derivedPullback q.toLRSHom.toShHom).obj K) ⟶
        (derivedPullback e.toLRSHom.toShHom).obj
          ((derivedPullback q.toLRSHom.toShHom).obj L)) :=
  AddMonoidHom.mk' (schemeFactorTowerHom r g p e q h K L)
    (schemeFactorTowerHom_add r g p e q h K L)

/-! ### Bijectivity when the vertical edge is an isomorphism -/

section Iso

/-- **The map on derived morphism sets attached to a square of ringed spaces with factored
horizontal edges whose vertical edge is an isomorphism is bijective.** The map is the derived
pullback along that edge composed with three comparison bijections, and derived pullback along
an isomorphism is an equivalence. -/
theorem bijective_factorTowerHom {A B Y Y' Z : RingedSpace.{u, u}} (r : A ⟶ B) (g : B ⟶ Y)
    (p : Y ⟶ Z) (e : A ⟶ Y') (q : Y' ⟶ Z) (h : r ≫ g ≫ p = e ≫ q) (r' : B ⟶ A)
    (hrr' : r ≫ r' = 𝟙 A) (hr'r : r' ≫ r = 𝟙 B)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    Function.Bijective (factorTowerHom r g p e q h K L) := by
  have key : factorTowerHom r g p e q h K L =
      (factorEquiv e q (e ≫ q) rfl K L).symm ∘ (factorEquiv r (g ≫ p) (e ≫ q) h K L) ∘
        (derivedPullback r).map ∘ (factorEquiv g p (g ≫ p) rfl K L) := by
    funext φ
    exact congrArg (factorEquiv e q (e ≫ q) rfl K L).symm
      (factorHom_eq_factorEquiv r (g ≫ p) (e ≫ q) h K L _)
  rw [key]
  exact (factorEquiv e q (e ≫ q) rfl K L).symm.bijective.comp
    ((factorEquiv r (g ≫ p) (e ≫ q) h K L).bijective.comp
      ((bijective_derivedPullback_map r r' hrr' hr'r _ _).comp
        (factorEquiv g p (g ≫ p) rfl K L).bijective))

/-- **The map on derived morphism sets attached to a square of morphisms of schemes with
factored horizontal edges whose vertical edge is an isomorphism is bijective.** Applied at
`Scheme.Hom.isoOpensRange` this is what identifies restriction along an open immersion with
restriction along the inclusion of its open range, the form the Mayer--Vietoris Ext sequence of
Stacks 08BW is stated in. -/
theorem bijective_schemeFactorTowerHom (r : A ⟶ B) (g : B ⟶ Y) (p : Y ⟶ Z) (e : A ⟶ Y')
    (q : Y' ⟶ Z) (h : r ≫ g ≫ p = e ≫ q) (r' : B ⟶ A) (hrr' : r ≫ r' = 𝟙 A)
    (hr'r : r' ≫ r = 𝟙 B)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    Function.Bijective (schemeFactorTowerHom r g p e q h K L) :=
  bijective_factorTowerHom r.toLRSHom.toShHom g.toLRSHom.toShHom p.toLRSHom.toShHom
    e.toLRSHom.toShHom q.toLRSHom.toShHom
    (congrArg (fun m : A ⟶ Z ↦ m.toLRSHom.toShHom) h) r'.toLRSHom.toShHom
    (congrArg (fun m : A ⟶ A ↦ m.toLRSHom.toShHom) hrr')
    (congrArg (fun m : B ⟶ B ↦ m.toLRSHom.toShHom) hr'r) K L

end Iso

end Stacks.DerivedPullback

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

attribute [local implicit_reducible] restrict

variable (K₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-! ### Restriction to a smaller quasi-compact open as a group homomorphism -/

section Smaller

variable (L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))
  (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
  (V₀ : D.X₀.left.Opens) (hV₀ : IsCompact (V₀ : Set D.X₀.left)) (hVU : V₀ ≤ U₀)

/-- Restriction from `U₀` to a smaller quasi-compact open `V₀` on the derived morphism sets of
the restricted situations at a stage, as a group homomorphism. -/
def restrictHomSmaller (i : D.LaterIndex) :
    D.restrictHomStage K₀ U₀ hU₀ L₀ i →+ D.restrictHomStage K₀ V₀ hV₀ L₀ i :=
  Stacks.DerivedPullback.schemeFactorTowerAddHom (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i)
    ((D.restrict U₀ hU₀).toFixedStage i) U₀.ι ((D.restrict V₀ hV₀).toFixedStage i) V₀.ι
    (D.restrictToLarger_comp_toFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i) K₀ L₀

/-- Restriction from `U₀` to a smaller quasi-compact open `V₀` on the derived morphism sets of
the restricted situations at the limit, as a group homomorphism. -/
def restrictHomSmallerLimit :
    D.restrictHomLimit K₀ U₀ hU₀ L₀ →+ D.restrictHomLimit K₀ V₀ hV₀ L₀ :=
  Stacks.DerivedPullback.schemeFactorTowerAddHom (D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU)
    (D.restrict U₀ hU₀).limitToFixedStage U₀.ι (D.restrict V₀ hV₀).limitToFixedStage V₀.ι
    (D.restrictToLargerLimit_comp_limitToFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU) K₀ L₀

/-- Restriction to a smaller quasi-compact open is the map of derived morphism sets
`homRestrictToSmaller`. -/
theorem restrictHomSmaller_apply (i : D.LaterIndex) (x : D.restrictHomStage K₀ U₀ hU₀ L₀ i) :
    D.restrictHomSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU i x =
      D.homRestrictToSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU i x :=
  rfl

/-- Restriction to a smaller quasi-compact open at the limit is the map of derived morphism sets
`homRestrictToSmallerLimit`. -/
theorem restrictHomSmallerLimit_apply (x : D.restrictHomLimit K₀ U₀ hU₀ L₀) :
    D.restrictHomSmallerLimit K₀ L₀ U₀ hU₀ V₀ hV₀ hVU x =
      D.homRestrictToSmallerLimit K₀ L₀ U₀ hU₀ V₀ hV₀ hVU x :=
  rfl

/-- **Restriction to a smaller quasi-compact open is natural in the stage.** -/
theorem restrictHomTransition_restrictHomSmaller (i j : D.LaterIndex) (h : i ≤ j)
    (x : D.restrictHomStage K₀ U₀ hU₀ L₀ i) :
    D.restrictHomTransition K₀ V₀ hV₀ L₀ i j h
        (D.restrictHomSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU i x) =
      D.restrictHomSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU j
        (D.restrictHomTransition K₀ U₀ hU₀ L₀ i j h x) :=
  D.homTransition_homRestrictToSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU h x

/-- **Restriction to a smaller quasi-compact open commutes with the comparison maps to the
limits.** -/
theorem restrictHomComparison_restrictHomSmaller (i : D.LaterIndex)
    (x : D.restrictHomStage K₀ U₀ hU₀ L₀ i) :
    D.restrictHomComparison K₀ V₀ hV₀ L₀ i
        (D.restrictHomSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU i x) =
      D.restrictHomSmallerLimit K₀ L₀ U₀ hU₀ V₀ hV₀ hVU
        (D.restrictHomComparison K₀ U₀ hU₀ L₀ i x) :=
  D.homComparison_homRestrictToSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU i x

/-! ### Restriction along the inclusion of the open range -/

/-- The inclusion of the open range of `Vᵢ ⟶ Uᵢ`, followed by the map of `Uᵢ` to `U₀`. This is
the edge along which the Mayer--Vietoris Ext sequence of Stacks 08BW restricts, `U₀` being the
base over which the derived morphism sets are taken. -/
abbrev restrictRangeToFixedStage (i : D.LaterIndex) :
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).opensRange.toScheme ⟶ U₀.toScheme :=
  (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).opensRange.ι ≫ (D.restrict U₀ hU₀).toFixedStage i

/-- The inclusion of the open range of `Vᵢ ⟶ Uᵢ` lies over `X₀`, trivially: the two ways of
bracketing the composite down to `X₀` agree. -/
theorem opensRange_ι_comp_restrictRangeToFixedStage_comp_ι (i : D.LaterIndex) :
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).opensRange.ι ≫
        (D.restrict U₀ hU₀).toFixedStage i ≫ U₀.ι =
      D.restrictRangeToFixedStage U₀ hU₀ V₀ hV₀ hVU i ≫ U₀.ι :=
  (Category.assoc _ _ _).symm

/-- **`Vᵢ` is the open subscheme of `Uᵢ` cut out by the range of `Vᵢ ⟶ Uᵢ`, over `X₀`.** The
canonical isomorphism onto that open range is a morphism of the two towers down to `X₀`. -/
theorem isoOpensRange_hom_comp_restrictRangeToFixedStage_comp_ι (i : D.LaterIndex) :
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).isoOpensRange.hom ≫
        D.restrictRangeToFixedStage U₀ hU₀ V₀ hV₀ hVU i ≫ U₀.ι =
      (D.restrict V₀ hV₀).toFixedStage i ≫ V₀.ι := by
  simp only [restrictRangeToFixedStage, Category.assoc]
  rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
  exact D.restrictToLarger_comp_toFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i

/-- **Restriction from `U₀` to a smaller quasi-compact open `V₀` is restriction along the
inclusion of an open subscheme, followed by a bijection.** The first step restricts to the open
range of `Vᵢ ⟶ Uᵢ`, which is the form Stacks 08BW is stated in; the second transports along the
canonical isomorphism of `Vᵢ` with that open range. -/
theorem homRestrictToSmaller_eq_schemeFactorTowerHom_isoOpensRange (i : D.LaterIndex)
    (φ : (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀) ⟶
        (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀)) :
    D.homRestrictToSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU i φ =
      Stacks.DerivedPullback.schemeFactorTowerHom
        (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).isoOpensRange.hom
        (D.restrictRangeToFixedStage U₀ hU₀ V₀ hV₀ hVU i) U₀.ι
        ((D.restrict V₀ hV₀).toFixedStage i) V₀.ι
        (D.isoOpensRange_hom_comp_restrictRangeToFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i) K₀ L₀
        (Stacks.DerivedPullback.schemeFactorTowerHom
          (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).opensRange.ι
          ((D.restrict U₀ hU₀).toFixedStage i) U₀.ι
          (D.restrictRangeToFixedStage U₀ hU₀ V₀ hV₀ hVU i) U₀.ι
          (D.opensRange_ι_comp_restrictRangeToFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i) K₀ L₀ φ) :=
  (Stacks.DerivedPullback.schemeFactorTowerHom_comp
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).opensRange.ι
    ((D.restrict U₀ hU₀).toFixedStage i) U₀.ι
    (D.restrictRangeToFixedStage U₀ hU₀ V₀ hV₀ hVU i) U₀.ι
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).isoOpensRange.hom
    ((D.restrict V₀ hV₀).toFixedStage i) V₀.ι (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i)
    (D.opensRange_ι_comp_restrictRangeToFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i)
    (D.isoOpensRange_hom_comp_restrictRangeToFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i)
    (D.restrictToLarger_comp_toFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i)
    (Scheme.Hom.isoOpensRange_hom_ι _) K₀ L₀ φ).symm

/-- **The transport from the open range of `Vᵢ ⟶ Uᵢ` back to `Vᵢ` is bijective.** With
`homRestrictToSmaller_eq_schemeFactorTowerHom_isoOpensRange` this says that the restriction map
of the system of derived morphism sets and the restriction map of Stacks 08BW differ by a
bijection of groups, so exactness transports between them. -/
theorem bijective_schemeFactorTowerHom_isoOpensRange (i : D.LaterIndex) :
    Function.Bijective (Stacks.DerivedPullback.schemeFactorTowerHom
      (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).isoOpensRange.hom
      (D.restrictRangeToFixedStage U₀ hU₀ V₀ hV₀ hVU i) U₀.ι
      ((D.restrict V₀ hV₀).toFixedStage i) V₀.ι
      (D.isoOpensRange_hom_comp_restrictRangeToFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i) K₀ L₀) :=
  Stacks.DerivedPullback.bijective_schemeFactorTowerHom _ _ _ _ _ _
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).isoOpensRange.inv
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).isoOpensRange.hom_inv_id
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).isoOpensRange.inv_hom_id K₀ L₀

end Smaller

/-! ### The two restricted opens cover the restriction to the union -/

section Cover

/-- Pulling back `U` and `V` along the inclusion of `U ⊔ V` and then along any morphism gives two
opens that cover the source. -/
private theorem preimage_sup_ι_preimage_eq_top {X Y : Scheme.{u}} (U V : Y.Opens)
    (f : X ⟶ (U ⊔ V).toScheme) :
    f ⁻¹ᵁ (U ⊔ V).ι ⁻¹ᵁ U ⊔ f ⁻¹ᵁ (U ⊔ V).ι ⁻¹ᵁ V = ⊤ :=
  (congrArg (f ⁻¹ᵁ ·) (U ⊔ V).ι_preimage_self).trans (Scheme.Hom.preimage_top _)

variable (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
  (hV₀ : IsCompact (V₀ : Set D.X₀.left))
  (hsup : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left))

/-- **The preimages of `U₀` and of `V₀` cover the stage of the situation restricted to
`U₀ ∪ V₀`.** This is the hypothesis `U ⊔ V = ⊤` under which the Mayer--Vietoris sequence of
Stacks 08BW is available, for the two opens of `(U₀ ∪ V₀)ᵢ` cut out by `U₀` and by `V₀`. -/
theorem opensRange_restrictToLarger_sup_opensRange_restrictToLarger (i : D.LaterIndex) :
    (D.restrictToLarger (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left i).opensRange ⊔
        (D.restrictToLarger (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right i).opensRange = ⊤ := by
  rw [D.opensRange_restrictToLarger (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left i,
    D.opensRange_restrictToLarger (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right i]
  exact preimage_sup_ι_preimage_eq_top _ _ _

/-- **The preimages of `U₀` and of `V₀` cover the limit of the situation restricted to
`U₀ ∪ V₀`.** -/
theorem opensRange_restrictToLargerLimit_sup_opensRange_restrictToLargerLimit :
    (D.restrictToLargerLimit (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left).opensRange ⊔
        (D.restrictToLargerLimit (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right).opensRange = ⊤ := by
  rw [D.opensRange_restrictToLargerLimit (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left,
    D.opensRange_restrictToLargerLimit (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right]
  exact preimage_sup_ι_preimage_eq_top _ _ _

end Cover

/-! ### The restriction and difference maps of the Mayer--Vietoris sequence -/

section Sup

variable (L : ℤ → DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))
  (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
  (hV₀ : IsCompact (V₀ : Set D.X₀.left))
  (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
  (hsup : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left))

/-- The restriction map of the Mayer--Vietoris sequence at a stage: the pair of the restrictions
from `U₀ ∪ V₀` to `U₀` and to `V₀`. -/
def mayerVietorisStageRestriction (n : ℤ) (i : D.LaterIndex) :
    D.restrictHomStage K₀ (U₀ ⊔ V₀) hsup (L n) i →+
      D.restrictHomStage K₀ U₀ hU₀ (L n) i × D.restrictHomStage K₀ V₀ hV₀ (L n) i :=
  (D.restrictHomSmaller K₀ (L n) (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left i).prod
    (D.restrictHomSmaller K₀ (L n) (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right i)

/-- The restriction map of the Mayer--Vietoris sequence at a stage sends a morphism to the pair
of its two restrictions. -/
theorem mayerVietorisStageRestriction_apply (n : ℤ) (i : D.LaterIndex)
    (x : D.restrictHomStage K₀ (U₀ ⊔ V₀) hsup (L n) i) :
    D.mayerVietorisStageRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n i x =
      (D.restrictHomSmaller K₀ (L n) (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left i x,
        D.restrictHomSmaller K₀ (L n) (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right i x) :=
  rfl

/-- The difference map of the Mayer--Vietoris sequence at a stage: the difference of the two
restrictions to `U₀ ∩ V₀`. -/
def mayerVietorisStageDifference (n : ℤ) (i : D.LaterIndex) :
    (D.restrictHomStage K₀ U₀ hU₀ (L n) i × D.restrictHomStage K₀ V₀ hV₀ (L n) i) →+
      D.restrictHomStage K₀ (U₀ ⊓ V₀) hinf (L n) i :=
  AddMonoidHom.mk'
    (fun y => D.restrictHomSmaller K₀ (L n) U₀ hU₀ (U₀ ⊓ V₀) hinf inf_le_left i y.1 -
      D.restrictHomSmaller K₀ (L n) V₀ hV₀ (U₀ ⊓ V₀) hinf inf_le_right i y.2)
    fun y y' => by
      simp only [Prod.fst_add, Prod.snd_add, map_add]
      abel

/-- The difference map of the Mayer--Vietoris sequence at a stage sends a pair of morphisms to
the difference of their restrictions to `U₀ ∩ V₀`. -/
theorem mayerVietorisStageDifference_apply (n : ℤ) (i : D.LaterIndex)
    (y : D.restrictHomStage K₀ U₀ hU₀ (L n) i × D.restrictHomStage K₀ V₀ hV₀ (L n) i) :
    D.mayerVietorisStageDifference K₀ L U₀ V₀ hU₀ hV₀ hinf n i y =
      D.restrictHomSmaller K₀ (L n) U₀ hU₀ (U₀ ⊓ V₀) hinf inf_le_left i y.1 -
        D.restrictHomSmaller K₀ (L n) V₀ hV₀ (U₀ ⊓ V₀) hinf inf_le_right i y.2 :=
  rfl

/-- The restriction map of the Mayer--Vietoris sequence at the limit. -/
def mayerVietorisLimitRestriction (n : ℤ) :
    D.restrictHomLimit K₀ (U₀ ⊔ V₀) hsup (L n) →+
      D.restrictHomLimit K₀ U₀ hU₀ (L n) × D.restrictHomLimit K₀ V₀ hV₀ (L n) :=
  (D.restrictHomSmallerLimit K₀ (L n) (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left).prod
    (D.restrictHomSmallerLimit K₀ (L n) (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right)

/-- The restriction map of the Mayer--Vietoris sequence at the limit sends a morphism to the pair
of its two restrictions. -/
theorem mayerVietorisLimitRestriction_apply (n : ℤ)
    (x : D.restrictHomLimit K₀ (U₀ ⊔ V₀) hsup (L n)) :
    D.mayerVietorisLimitRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n x =
      (D.restrictHomSmallerLimit K₀ (L n) (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left x,
        D.restrictHomSmallerLimit K₀ (L n) (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right x) :=
  rfl

/-- The difference map of the Mayer--Vietoris sequence at the limit. -/
def mayerVietorisLimitDifference (n : ℤ) :
    (D.restrictHomLimit K₀ U₀ hU₀ (L n) × D.restrictHomLimit K₀ V₀ hV₀ (L n)) →+
      D.restrictHomLimit K₀ (U₀ ⊓ V₀) hinf (L n) :=
  AddMonoidHom.mk'
    (fun y => D.restrictHomSmallerLimit K₀ (L n) U₀ hU₀ (U₀ ⊓ V₀) hinf inf_le_left y.1 -
      D.restrictHomSmallerLimit K₀ (L n) V₀ hV₀ (U₀ ⊓ V₀) hinf inf_le_right y.2)
    fun y y' => by
      simp only [Prod.fst_add, Prod.snd_add, map_add]
      abel

/-- The difference map of the Mayer--Vietoris sequence at the limit sends a pair of morphisms to
the difference of their restrictions to `U₀ ∩ V₀`. -/
theorem mayerVietorisLimitDifference_apply (n : ℤ)
    (y : D.restrictHomLimit K₀ U₀ hU₀ (L n) × D.restrictHomLimit K₀ V₀ hV₀ (L n)) :
    D.mayerVietorisLimitDifference K₀ L U₀ V₀ hU₀ hV₀ hinf n y =
      D.restrictHomSmallerLimit K₀ (L n) U₀ hU₀ (U₀ ⊓ V₀) hinf inf_le_left y.1 -
        D.restrictHomSmallerLimit K₀ (L n) V₀ hV₀ (U₀ ⊓ V₀) hinf inf_le_right y.2 :=
  rfl

/-- **The restriction map of the Mayer--Vietoris sequence is natural in the stage.** -/
theorem mayerVietorisStageRestriction_transition (n : ℤ) (i j : D.LaterIndex) (h : i ≤ j)
    (x : D.restrictHomStage K₀ (U₀ ⊔ V₀) hsup (L n) i) :
    D.mayerVietorisStageRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n j
        (D.restrictHomTransition K₀ (U₀ ⊔ V₀) hsup (L n) i j h x) =
      (D.restrictHomTransition K₀ U₀ hU₀ (L n) i j h
          (D.mayerVietorisStageRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n i x).1,
        D.restrictHomTransition K₀ V₀ hV₀ (L n) i j h
          (D.mayerVietorisStageRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n i x).2) :=
  Prod.ext
    (D.restrictHomTransition_restrictHomSmaller K₀ (L n) (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left
      i j h x).symm
    (D.restrictHomTransition_restrictHomSmaller K₀ (L n) (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right
      i j h x).symm

/-- **The difference map of the Mayer--Vietoris sequence is natural in the stage.** -/
theorem mayerVietorisStageDifference_transition (n : ℤ) (i j : D.LaterIndex) (h : i ≤ j)
    (y : D.restrictHomStage K₀ U₀ hU₀ (L n) i × D.restrictHomStage K₀ V₀ hV₀ (L n) i) :
    D.mayerVietorisStageDifference K₀ L U₀ V₀ hU₀ hV₀ hinf n j
        (D.restrictHomTransition K₀ U₀ hU₀ (L n) i j h y.1,
          D.restrictHomTransition K₀ V₀ hV₀ (L n) i j h y.2) =
      D.restrictHomTransition K₀ (U₀ ⊓ V₀) hinf (L n) i j h
        (D.mayerVietorisStageDifference K₀ L U₀ V₀ hU₀ hV₀ hinf n i y) :=
  Eq.symm
    ((map_sub (D.restrictHomTransition K₀ (U₀ ⊓ V₀) hinf (L n) i j h) _ _).trans
      (congrArg₂ (· - ·)
        (D.restrictHomTransition_restrictHomSmaller K₀ (L n) U₀ hU₀ (U₀ ⊓ V₀) hinf inf_le_left
          i j h y.1)
        (D.restrictHomTransition_restrictHomSmaller K₀ (L n) V₀ hV₀ (U₀ ⊓ V₀) hinf inf_le_right
          i j h y.2)))

/-- **The comparison maps commute with the restriction maps of the Mayer--Vietoris
sequence.** -/
theorem mayerVietorisLimitRestriction_comparison (n : ℤ) (i : D.LaterIndex)
    (x : D.restrictHomStage K₀ (U₀ ⊔ V₀) hsup (L n) i) :
    (D.restrictHomComparison K₀ U₀ hU₀ (L n) i
          (D.mayerVietorisStageRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n i x).1,
        D.restrictHomComparison K₀ V₀ hV₀ (L n) i
          (D.mayerVietorisStageRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n i x).2) =
      D.mayerVietorisLimitRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n
        (D.restrictHomComparison K₀ (U₀ ⊔ V₀) hsup (L n) i x) :=
  Prod.ext
    (D.restrictHomComparison_restrictHomSmaller K₀ (L n) (U₀ ⊔ V₀) hsup U₀ hU₀ le_sup_left i x)
    (D.restrictHomComparison_restrictHomSmaller K₀ (L n) (U₀ ⊔ V₀) hsup V₀ hV₀ le_sup_right i x)

/-- **The comparison maps commute with the difference maps of the Mayer--Vietoris sequence.** -/
theorem mayerVietorisLimitDifference_comparison (n : ℤ) (i : D.LaterIndex)
    (y : D.restrictHomStage K₀ U₀ hU₀ (L n) i × D.restrictHomStage K₀ V₀ hV₀ (L n) i) :
    D.restrictHomComparison K₀ (U₀ ⊓ V₀) hinf (L n) i
        (D.mayerVietorisStageDifference K₀ L U₀ V₀ hU₀ hV₀ hinf n i y) =
      D.mayerVietorisLimitDifference K₀ L U₀ V₀ hU₀ hV₀ hinf n
        (D.restrictHomComparison K₀ U₀ hU₀ (L n) i y.1,
          D.restrictHomComparison K₀ V₀ hV₀ (L n) i y.2) :=
  (map_sub (D.restrictHomComparison K₀ (U₀ ⊓ V₀) hinf (L n) i) _ _).trans
    (congrArg₂ (· - ·)
      (D.restrictHomComparison_restrictHomSmaller K₀ (L n) U₀ hU₀ (U₀ ⊓ V₀) hinf inf_le_left
        i y.1)
      (D.restrictHomComparison_restrictHomSmaller K₀ (L n) V₀ hV₀ (U₀ ⊓ V₀) hinf inf_le_right
        i y.2))

/-! ### The Mayer--Vietoris sequence from its connecting homomorphisms -/

/-- **The Mayer--Vietoris sequence of the union step of Tag 0DI7 from its connecting
homomorphisms.** The restriction and difference maps of the sequence, at a stage and at the
limit, are restriction along the inclusions of `U₀`, `V₀` and `U₀ ∩ V₀` into `U₀ ∪ V₀` and into
one another, and their naturality in the stage and compatibility with the comparison maps is
that of restriction; what is left to supply is the two connecting homomorphisms together with
their own naturality and the six exactness statements. -/
def mayerVietorisHomSequenceOfBoundary
    (stageBoundary : ∀ (n₀ n₁ : ℤ), n₀ + 1 = n₁ → ∀ i : D.LaterIndex,
      D.restrictHomStage K₀ (U₀ ⊓ V₀) hinf (L n₀) i →+
        D.restrictHomStage K₀ (U₀ ⊔ V₀) hsup (L n₁) i)
    (limitBoundary : ∀ (n₀ n₁ : ℤ), n₀ + 1 = n₁ →
      (D.restrictHomLimit K₀ (U₀ ⊓ V₀) hinf (L n₀) →+
        D.restrictHomLimit K₀ (U₀ ⊔ V₀) hsup (L n₁)))
    (stageBoundary_transition : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i j : D.LaterIndex)
        (h : i ≤ j) (z : D.restrictHomStage K₀ (U₀ ⊓ V₀) hinf (L n₀) i),
      stageBoundary n₀ n₁ hn j (D.restrictHomTransition K₀ (U₀ ⊓ V₀) hinf (L n₀) i j h z) =
        D.restrictHomTransition K₀ (U₀ ⊔ V₀) hsup (L n₁) i j h (stageBoundary n₀ n₁ hn i z))
    (limitBoundary_comparison : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i : D.LaterIndex)
        (z : D.restrictHomStage K₀ (U₀ ⊓ V₀) hinf (L n₀) i),
      D.restrictHomComparison K₀ (U₀ ⊔ V₀) hsup (L n₁) i (stageBoundary n₀ n₁ hn i z) =
        limitBoundary n₀ n₁ hn (D.restrictHomComparison K₀ (U₀ ⊓ V₀) hinf (L n₀) i z))
    (exact_stageRestriction_stageDifference : ∀ (n : ℤ) (i : D.LaterIndex),
      Function.Exact (D.mayerVietorisStageRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n i)
        (D.mayerVietorisStageDifference K₀ L U₀ V₀ hU₀ hV₀ hinf n i))
    (exact_stageDifference_stageBoundary : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i : D.LaterIndex),
      Function.Exact (D.mayerVietorisStageDifference K₀ L U₀ V₀ hU₀ hV₀ hinf n₀ i)
        (stageBoundary n₀ n₁ hn i))
    (exact_stageBoundary_stageRestriction : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i : D.LaterIndex),
      Function.Exact (stageBoundary n₀ n₁ hn i)
        (D.mayerVietorisStageRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n₁ i))
    (exact_limitRestriction_limitDifference : ∀ n : ℤ,
      Function.Exact (D.mayerVietorisLimitRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n)
        (D.mayerVietorisLimitDifference K₀ L U₀ V₀ hU₀ hV₀ hinf n))
    (exact_limitDifference_limitBoundary : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁),
      Function.Exact (D.mayerVietorisLimitDifference K₀ L U₀ V₀ hU₀ hV₀ hinf n₀)
        (limitBoundary n₀ n₁ hn))
    (exact_limitBoundary_limitRestriction : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁),
      Function.Exact (limitBoundary n₀ n₁ hn)
        (D.mayerVietorisLimitRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup n₁)) :
    D.MayerVietorisHomSequence K₀ L U₀ V₀ hU₀ hV₀ hinf hsup where
  stageRestriction := D.mayerVietorisStageRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup
  stageDifference := D.mayerVietorisStageDifference K₀ L U₀ V₀ hU₀ hV₀ hinf
  stageBoundary := stageBoundary
  limitRestriction := D.mayerVietorisLimitRestriction K₀ L U₀ V₀ hU₀ hV₀ hsup
  limitDifference := D.mayerVietorisLimitDifference K₀ L U₀ V₀ hU₀ hV₀ hinf
  limitBoundary := limitBoundary
  stageRestriction_transition :=
    D.mayerVietorisStageRestriction_transition K₀ L U₀ V₀ hU₀ hV₀ hsup
  stageDifference_transition :=
    D.mayerVietorisStageDifference_transition K₀ L U₀ V₀ hU₀ hV₀ hinf
  stageBoundary_transition := stageBoundary_transition
  limitRestriction_comparison :=
    D.mayerVietorisLimitRestriction_comparison K₀ L U₀ V₀ hU₀ hV₀ hsup
  limitDifference_comparison :=
    D.mayerVietorisLimitDifference_comparison K₀ L U₀ V₀ hU₀ hV₀ hinf
  limitBoundary_comparison := limitBoundary_comparison
  exact_stageRestriction_stageDifference := exact_stageRestriction_stageDifference
  exact_stageDifference_stageBoundary := exact_stageDifference_stageBoundary
  exact_stageBoundary_stageRestriction := exact_stageBoundary_stageRestriction
  exact_limitRestriction_limitDifference := exact_limitRestriction_limitDifference
  exact_limitDifference_limitBoundary := exact_limitDifference_limitBoundary
  exact_limitBoundary_limitRestriction := exact_limitBoundary_limitRestriction

end Sup

end AlgebraicGeometry.RelativeDescentSituation

end
