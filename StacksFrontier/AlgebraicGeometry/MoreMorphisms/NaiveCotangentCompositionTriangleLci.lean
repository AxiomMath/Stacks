module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentConeQuasiIso
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentLciStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0FV3: the triangle of naive cotangent complexes of a complete intersection morphism

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and assume `f` is a local complete
intersection morphism.  Then the canonical map

`c : f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]`

of Stacks 0E1Z is an **isomorphism in `D(𝒪_X)`**, so the triangle of the mapping cocone of the
canonical map `NL_{X/Z} ⟶ NL_{X/Y}` may be read with `f^*NL_{Y/Z}` as its first vertex: that is
the canonical distinguished triangle

`f^*NL_{Y/Z} ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ f^*NL_{Y/Z}[1]`

of **Stacks 0FV3**, whose first two morphisms are the canonical maps and whose long exact sequence
of cohomology sheaves is the six-term exact sequence of Stacks 0E44.

## Main results

* `Stacks.NaiveCotangentCompositionTriangle.isIso_Q_map_coneMap_of_lci`: **the comparison is an
  isomorphism in `D(𝒪_X)`.**
* `Stacks.NaiveCotangentCompositionTriangle.lciTriangle_distinguished`: **the triangle is
  distinguished**, with `lciTriangle_mor₁` and `lciTriangle_mor₂` identifying its first two
  morphisms as the canonical maps `f^*NL_{Y/Z} ⟶ NL_{X/Z}` and `NL_{X/Z} ⟶ NL_{X/Y}`.
* `Stacks.NaiveCotangentCompositionTriangle.lciTriangle_recovers_sixTerm`: **the six-term exact
  sequence of Stacks 0E44 recovered from the triangle.**

## Implementation notes

**Everything here is an instantiation.**  The derived-category work is done for a pair of
composable morphisms of ringed spaces in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentConeQuasiIso`, under the one
hypothesis `Stacks.SheafOfModules.StalkwiseInjectiveOnH₁` that the canonical map `c₁` of
Stacks 0E1Y is injective on `H₁` at every stalk; what this file adds is that a local complete
intersection morphism of schemes satisfies that hypothesis, which is
`Stacks.NaiveCotangentLciStalk.injective_onH₁_nlExtensionBaseChangeMap_stalk_of_lci`, and
therefore the assertions of Stacks 0FV3.

**The sign.**  The projection `C(φ)[-1] ⟶ K` out of the mapping cocone is the *negative* of the
projection through which Stacks 0E1Z characterises the comparison
(`Stacks.NaiveCotangentCompositionTriangle.coneMap_comp_fst`), so the comparison used to replace
the first vertex is `-c` rather than `c`; it is an isomorphism exactly when `c` is, and with it
the first morphism of the triangle comes out as the canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}` with
no sign.

**The recovery of the six-term sequence.**  The first two morphisms of the triangle are the images
under `DerivedCategory.Q` of the canonical chain maps `f^*NL_{Y/Z} ⟶ NL_{X/Z}` and
`NL_{X/Z} ⟶ NL_{X/Y}` (`lciTriangle_mor₁`, `lciTriangle_mor₂`), and the connecting morphism of
the six-term sequence, `Stacks.SheafOfModules.ringedSpaceJacobiZariskiConnecting`, is by
construction the connecting morphism of the long exact sequence of the cone read through the
comparison of Stacks 0E1Z; so the five assertions bundled in `lciTriangle_recovers_sixTerm` are
the long exact sequence of cohomology sheaves of this triangle, and they are the six-term exact
sequence of Stacks 0E44.  Outside degrees `-1` and `0` all three vertices have vanishing
cohomology (`Stacks.SheafOfModules.isZero_homology_spaceNaiveCotangentCone`,
`Stacks.SheafOfModules.isZero_homology_spaceBaseChangeNaiveCotangentComplex` and
`Stacks.SheafOfModules.naiveCotangentComplex_isZero_homology`), which is what truncates that long
exact sequence to six terms.

## References

* [Stacks Project, Tag 0FV3](https://stacks.math.columbia.edu/tag/0FV3)
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the canonical map and
  the six-term exact sequence of a pair of composable morphisms of ringed spaces.
* [Stacks Project, Tag 0E44](https://stacks.math.columbia.edu/tag/0E44), the six-term exact
  sequence for a pair of composable morphisms of schemes.
* [Stacks Project, Tag 069F](https://stacks.math.columbia.edu/tag/069F), local complete
  intersection morphisms.
* [Stacks Project, Tag 07D4](https://stacks.math.columbia.edu/tag/07D4), the ring-level
  injectivity at the left end of the Jacobi-Zariski sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry CochainComplex
open Stacks.SheafOfModules

universe t u

noncomputable section

namespace Stacks.NaiveCotangentCompositionTriangle

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **A local complete intersection morphism satisfies the one extra input.**  For `f` a local
complete intersection morphism the canonical map `c₁` of Stacks 0E1Y, for the tower
`f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X`, is injective on `H₁` at every stalk.  This is where the complete
intersection hypothesis enters, and the only place it does. -/
theorem stalkwiseInjectiveOnH₁_of_lci (hf : IsLocalCompleteIntersectionMorphism f) :
    StalkwiseInjectiveOnH₁
      (inverseImageBaseRing f.toLRSHom.toShHom g.toLRSHom.toShHom)
      (inverseImageMiddleRing f.toLRSHom.toShHom) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap f.toLRSHom.toShHom g.toLRSHom.toShHom)
      (ringedSpaceStructureMap f.toLRSHom.toShHom) :=
  fun z =>
    Stacks.NaiveCotangentLciStalk.injective_onH₁_nlExtensionBaseChangeMap_stalk_of_lci f g hf z

section Derived

variable [HasDerivedCategory.{t} (_root_.SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology (X.toRingedSpace : TopCat)) X.toRingedSpace.sheaf))]

/-- **Stacks 0FV3, the isomorphism.**  For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z` with
`f` a local complete intersection morphism, the canonical map

`f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]`

of Stacks 0E1Z is an isomorphism in `D(𝒪_X)`.

This is the reduction the source makes: the triangle of Stacks 0FV3 is the triangle of the
mapping cocone of `NL_{X/Z} ⟶ NL_{X/Y}` with its first vertex replaced by `f^*NL_{Y/Z}` along
this isomorphism.  The map is surjective on `H^{-1}` and an isomorphism on `H⁰` for an arbitrary
pair of composable morphisms of ringed spaces; injectivity on `H^{-1}` is what the complete
intersection hypothesis supplies, through Stacks 07D4 at the stalks. -/
@[stacks 0FV3 "the canonical map f^*NL_{Y/Z} -> C(NL_{X/Z} -> NL_{X/Y})[-1] of 0E1Z is an \
ISOMORPHISM in D(O_X) when X -> Y is a complete intersection morphism, which is the reduction \
the source's proof makes"]
theorem isIso_Q_map_coneMap_of_lci (hf : IsLocalCompleteIntersectionMorphism f) :
    IsIso (DerivedCategory.Q.map
      (ringedSpaceNaiveCotangentConeMap f.toLRSHom.toShHom g.toLRSHom.toShHom)) :=
  isIso_Q_map_ringedSpaceNaiveCotangentConeMap f.toLRSHom.toShHom g.toLRSHom.toShHom
    (stalkwiseInjectiveOnH₁_of_lci f g hf)

/-- **Stacks 0FV3, the triangle.**  The triangle

`f^*NL_{Y/Z} ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ f^*NL_{Y/Z}[1]`

of `D(𝒪_X)`, for `f` a local complete intersection morphism: the triangle of the mapping cocone
of the canonical map `NL_{X/Z} ⟶ NL_{X/Y}` with its first vertex replaced by `f^*NL_{Y/Z}` along
the comparison of Stacks 0E1Z, which `isIso_Q_map_coneMap_of_lci` makes an isomorphism. -/
def lciTriangle (hf : IsLocalCompleteIntersectionMorphism f) :=
  coneTriangle f.toLRSHom.toShHom g.toLRSHom.toShHom (stalkwiseInjectiveOnH₁_of_lci f g hf)

/-- **The first morphism of the triangle is the canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}`.** -/
theorem lciTriangle_mor₁ (hf : IsLocalCompleteIntersectionMorphism f) :
    (lciTriangle f g hf).mor₁ =
      DerivedCategory.Q.map
        (pulledNaiveCotangentMap f.toLRSHom.toShHom g.toLRSHom.toShHom) :=
  coneTriangle_mor₁ f.toLRSHom.toShHom g.toLRSHom.toShHom
    (stalkwiseInjectiveOnH₁_of_lci f g hf)

/-- **The second morphism of the triangle is the canonical map `NL_{X/Z} ⟶ NL_{X/Y}`.** -/
theorem lciTriangle_mor₂ (hf : IsLocalCompleteIntersectionMorphism f) :
    (lciTriangle f g hf).mor₂ =
      DerivedCategory.Q.map
        (relativeNaiveCotangentMap f.toLRSHom.toShHom g.toLRSHom.toShHom) :=
  coneTriangle_mor₂ f.toLRSHom.toShHom g.toLRSHom.toShHom
    (stalkwiseInjectiveOnH₁_of_lci f g hf)

/-- **Stacks 0FV3.**  For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z` with `f` a local
complete intersection morphism, the canonical triangle

`f^*NL_{Y/Z} ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ f^*NL_{Y/Z}[1]`

is a distinguished triangle of `D(𝒪_X)`: it is the triangle of the mapping cocone of the
canonical map `NL_{X/Z} ⟶ NL_{X/Y}`, which is distinguished, with its first vertex replaced along
the comparison of Stacks 0E1Z, an isomorphism by `isIso_Q_map_coneMap_of_lci`.  Its first two
morphisms are the canonical maps, by `lciTriangle_mor₁` and `lciTriangle_mor₂`. -/
@[stacks 0FV3 "the canonical distinguished triangle f^*NL_{Y/Z} -> NL_{X/Z} -> NL_{X/Y} -> \
f^*NL_{Y/Z}[1] of D(O_X) for a complete intersection morphism X -> Y, with its first two \
morphisms the canonical maps (lciTriangle_mor₁, lciTriangle_mor₂)", sga "6 VIII 2.6" "more general"]
theorem lciTriangle_distinguished (hf : IsLocalCompleteIntersectionMorphism f) :
    lciTriangle f g hf ∈ distTriang _ :=
  coneTriangle_distinguished f.toLRSHom.toShHom g.toLRSHom.toShHom
    (stalkwiseInjectiveOnH₁_of_lci f g hf)

/-- **Stacks 0FV3: the triangle recovers the six-term exact sequence of Stacks 0E44.**  The long
exact sequence of cohomology sheaves of the triangle

`f^*NL_{Y/Z} ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ f^*NL_{Y/Z}[1]`

is the six-term exact sequence

`H^{-1}(f^*NL_{Y/Z}) ⟶ H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) --∂--> H⁰(f^*NL_{Y/Z}) ⟶`
`H⁰(NL_{X/Z}) ⟶ H⁰(NL_{X/Y}) ⟶ 0`:

its five assertions are exactness at the four interior terms and the final `⟶ 0`.  The two arrows
are the maps induced by the canonical chain maps, whose images under `DerivedCategory.Q` are the
first two morphisms of the triangle by `lciTriangle_mor₁` and `lciTriangle_mor₂`, and the
connecting morphism is `Stacks.SheafOfModules.ringedSpaceJacobiZariskiConnecting`, the connecting
morphism of the long exact sequence of the cone read through the comparison of Stacks 0E1Z.  The
sequence has six terms and no more because all three vertices have vanishing cohomology outside
degrees `-1` and `0`. -/
@[stacks 0FV3 "the recovery of the six-term exact sequence of 0E44 from lciTriangle: its first \
two morphisms are the images under Q of the canonical chain maps f^*NL_{Y/Z} -> NL_{X/Z} and \
NL_{X/Z} -> NL_{X/Y}, and the six-term sequence of the maps those induce on cohomology \
sheaves, with the connecting morphism of the long exact sequence of the cone, is exact at its \
four interior terms and ends in `-> 0`"]
theorem lciTriangle_recovers_sixTerm (hf : IsLocalCompleteIntersectionMorphism f) :
    (lciTriangle f g hf).mor₁ =
        DerivedCategory.Q.map
          (pulledNaiveCotangentMap f.toLRSHom.toShHom g.toLRSHom.toShHom) ∧
      (lciTriangle f g hf).mor₂ =
        DerivedCategory.Q.map
          (relativeNaiveCotangentMap f.toLRSHom.toShHom g.toLRSHom.toShHom) ∧
      (ringedSpaceJacobiZariskiHomologySequence f.toLRSHom.toShHom
        g.toLRSHom.toShHom (-1)).Exact ∧
      (ShortComplex.mk
        (HomologicalComplex.homologyMap
          (relativeNaiveCotangentMap f.toLRSHom.toShHom g.toLRSHom.toShHom) (-1))
        (ringedSpaceJacobiZariskiConnecting f.toLRSHom.toShHom g.toLRSHom.toShHom)
        (homologyMap_comp_ringedSpaceJacobiZariskiConnecting
          f.toLRSHom.toShHom g.toLRSHom.toShHom)).Exact ∧
      (ShortComplex.mk
        (ringedSpaceJacobiZariskiConnecting f.toLRSHom.toShHom g.toLRSHom.toShHom)
        (HomologicalComplex.homologyMap
          (pulledNaiveCotangentMap f.toLRSHom.toShHom g.toLRSHom.toShHom) 0)
        (ringedSpaceJacobiZariskiConnecting_comp_homologyMap
          f.toLRSHom.toShHom g.toLRSHom.toShHom)).Exact ∧
      (ringedSpaceJacobiZariskiHomologySequence f.toLRSHom.toShHom
        g.toLRSHom.toShHom 0).Exact ∧
      Epi (HomologicalComplex.homologyMap
        (relativeNaiveCotangentMap f.toLRSHom.toShHom g.toLRSHom.toShHom) 0) :=
  ⟨lciTriangle_mor₁ f g hf, lciTriangle_mor₂ f g hf,
    exact_ringedSpaceJacobiZariskiHomologySequence_negOne
      f.toLRSHom.toShHom g.toLRSHom.toShHom,
    exact_ringedSpaceJacobiZariskiSixTerm_negOne f.toLRSHom.toShHom g.toLRSHom.toShHom,
    exact_ringedSpaceJacobiZariskiSixTerm_zero f.toLRSHom.toShHom g.toLRSHom.toShHom,
    exact_ringedSpaceJacobiZariskiHomologySequence_zero
      f.toLRSHom.toShHom g.toLRSHom.toShHom,
    epi_homologyMap_ringedSpaceRelativeNaiveCotangentComplexMap_zero
      f.toLRSHom.toShHom g.toLRSHom.toShHom⟩

end Derived

end Stacks.NaiveCotangentCompositionTriangle

end

end
