module

public import StacksFrontier.Algebra.Homology.MappingCoconeConnecting
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentCompositionTriangleLci
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms
public import StacksFrontier.CategoryTheory.Triangulated.DistinguishedOfIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0FV3: the triangle in the arrows of Stacks 0E44, and the recovery of its six-term sequence

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes with `f` a local complete intersection
morphism.  `StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentCompositionTriangleLci`
produces the distinguished triangle

`f^*NL_{Y/Z} ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ f^*NL_{Y/Z}[1]`

of **Stacks 0FV3** over the *iterated* spelling of `NL_{X/Z}`, the naive cotangent complex of
`𝒪_X` over `f⁻¹g⁻¹𝒪_Z`, which is the spelling the comparison of Stacks 0E1Z is written in.  The
six-term exact sequence of **Stacks 0E44** is written, in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms`, over
`AlgebraicGeometry.Scheme.naiveCotangentComplex (f ≫ g)` instead, with its two chain maps
`Stacks.NaiveCotangentSixTermSequence.pullbackToTotalMap` and `totalToRelativeMap` and its
connecting map `Stacks.NaiveCotangentSixTermSequence.jacobiZariskiConnecting`.

This file puts the triangle in those arrows and identifies its connecting morphism with that
connecting map, which is what it means for the triangle to recover the six-term exact sequence.

## Main definitions

* `Stacks.NaiveCotangentCompositionTriangle.lciSchemeTriangle`: **the triangle of Stacks 0FV3 in
  the arrows of Stacks 0E44**, whose second vertex is `NL_{X/Z} = NL_{f ≫ g}` and whose first
  two morphisms are the images under `DerivedCategory.Q` of `pullbackToTotalMap` and
  `totalToRelativeMap`.

## Main results

* `Stacks.NaiveCotangentCompositionTriangle.lciSchemeTriangle_distinguished`: **it is a
  distinguished triangle of `D(𝒪_X)`**, with `lciSchemeTriangle_mor₁` and
  `lciSchemeTriangle_mor₂` identifying its first two morphisms.
* `Stacks.NaiveCotangentCompositionTriangle.δ_lciSchemeTriangle_comp_map`: **its connecting
  morphism, read along `H⁰` of the comparison of Stacks 0E1Z, is the connecting morphism of the
  triangle of the mapping cocone**, up to the sign of the cocone projection.
* `Stacks.NaiveCotangentCompositionTriangle.connecting_comp_homologyMap_eq_homologyδOfTriangle`:
  **the connecting map of the six-term sequence of Stacks 0E44, read along `H⁰` of the same
  comparison, is the connecting morphism of the long exact sequence of that triangle.**
* `Stacks.NaiveCotangentCompositionTriangle.lciSchemeTriangle_recovers_sixTerm`: **the recovery
  of the six-term exact sequence of Stacks 0E44**, bundling the two identifications of arrows,
  the two of the connecting morphism, and the exactness of the sequence at its four interior
  terms together with its final `⟶ 0`.

## Implementation notes

**The second vertex.**  Only the middle object of the triangle moves: `NL_{X/Z}` in its iterated
spelling is identified with `NL_{f ≫ g}` by
`Stacks.NaiveCotangentSixTermSequence.totalCompIso`, and
`CategoryTheory.Pretriangulated.distTriang_of_iso_obj₂` transports the triangle along the image
of that isomorphism under `DerivedCategory.Q`.  The two morphisms through the moved vertex come
out as the images under `Q` of the two chain maps of Stacks 0E44 — for the first one because
`pullbackToTotalMap` is the canonical map of Stacks 0E1Z followed by the inverse of
`totalCompIso`, which is `pullbackToTotalMap_comp_totalCompIso_hom`.

**The connecting morphism and its sign.**  The triangle of Stacks 0FV3 is the triangle of the
mapping cocone of `NL_{X/Z} ⟶ NL_{X/Y}` with its first vertex replaced by `f^*NL_{Y/Z}` along
the comparison `c` of Stacks 0E1Z, which the complete intersection hypothesis makes an
isomorphism of `D(𝒪_X)`; the replacement uses `-c`, because the projection out of the mapping
cocone is the negative of the projection through which Stacks 0E1Z characterises `c`, and that
is what makes the first morphism of the triangle the canonical map with no sign.  Composing the
connecting morphism of the triangle with `H⁰(c)` therefore gives the *negative* of the
connecting morphism of the triangle of the mapping cocone, which is
`δ_lciSchemeTriangle_comp_map`; the connecting map of the six-term sequence of Stacks 0E44 has
the other sign, `connecting_comp_homologyMap_eq_homologyδOfTriangle`, since it is built from `c`
and not from `-c`.  Exactness is insensitive to both signs, and
`CochainComplex.homologyδOfTriangle_mappingCocone_triangle` is what makes the connecting map of
Stacks 0E44 a triangle connecting morphism at all.

## References

* [Stacks Project, Tag 0FV3](https://stacks.math.columbia.edu/tag/0FV3)
* [Stacks Project, Tag 0E44](https://stacks.math.columbia.edu/tag/0E44), the six-term exact
  sequence of a pair of composable morphisms of schemes.
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the canonical map
  `f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]` and the six-term sequence of a pair of composable
  morphisms of ringed spaces.
* [Stacks Project, Tag 069F](https://stacks.math.columbia.edu/tag/069F), local complete
  intersection morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry CochainComplex
open Stacks.SheafOfModules
open Stacks.NaiveCotangentSixTermSequence

universe t u

noncomputable section

namespace Stacks.NaiveCotangentCompositionTriangle

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}` of Stacks 0E44, followed by the identification of
`NL_{X/Z} = NL_{f ≫ g}` with its iterated spelling, is the canonical map of Stacks 0E1Z. -/
theorem pullbackToTotalMap_comp_totalCompIso_hom :
    pullbackToTotalMap f g ≫ (totalCompIso f g).hom = iteratedPullbackMap f g := by
  rw [pullbackToTotalMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The connecting map of the six-term sequence of Stacks 0E44, composed with the map induced on
`H⁰` by the canonical map `c` of Stacks 0E1Z, is the connecting morphism of the cone of
`NL_{X/Z} ⟶ NL_{X/Y}`: the connecting map is that morphism followed by the inverse of `H⁰(c)`. -/
theorem connecting_comp_homologyMap_coneMap :
    jacobiZariskiConnecting f g ≫ HomologicalComplex.homologyMap
        (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom f) (ringedSpaceHom g)) 0 =
      CochainComplex.coneHomologyConnecting (iteratedRelativeMap f g) (-1) 0 (by omega) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun k => CochainComplex.coneHomologyConnecting
          (iteratedRelativeMap f g) (-1) 0 (by omega) ≫ k) (IsIso.inv_hom_id _)).trans
      (Category.comp_id _))

section Derived

variable [HasDerivedCategory.{t} (_root_.SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology (X.toRingedSpace : TopCat)) X.toRingedSpace.sheaf))]

omit [HasDerivedCategory.{t} (_root_.SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology (X.toRingedSpace : TopCat)) X.toRingedSpace.sheaf))] in
/-- **The connecting map of Stacks 0E44 is a triangle connecting morphism.**  Composed with the
map induced on `H⁰` by the canonical map of Stacks 0E1Z it is the connecting morphism of the long
exact sequence of the triangle

`C(NL_{X/Z} ⟶ NL_{X/Y})[-1] ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1][1]`

of the mapping cocone, whose image in `D(𝒪_X)` is the triangle of Stacks 0FV3 before its first
vertex is replaced by `f^*NL_{Y/Z}` along that same map. -/
@[stacks 0FV3 "the connecting map of the six-term sequence of 0E44, read along H^0 of the \
canonical map of 0E1Z, is the connecting morphism of the long exact sequence of the triangle \
of the mapping cocone of NL_{X/Z} -> NL_{X/Y}"]
theorem connecting_comp_homologyMap_eq_homologyδOfTriangle :
    jacobiZariskiConnecting f g ≫ HomologicalComplex.homologyMap
        (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom f) (ringedSpaceHom g)) 0 =
      CochainComplex.homologyδOfTriangle
        (CochainComplex.mappingCocone.triangle (iteratedRelativeMap f g)) (-1) 0 (by omega) :=
  (connecting_comp_homologyMap_coneMap f g).trans
    (CochainComplex.homologyδOfTriangle_mappingCocone_triangle
      (iteratedRelativeMap f g) (-1) 0 (by omega)).symm

/-- The comparison of Stacks 0E1Z with the sign that replaces the first vertex of the triangle
of Stacks 0FV3: it is the negative of the canonical map `f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]`
read in `D(𝒪_X)`. -/
theorem coneComparisonIso_hom (hf : IsLocalCompleteIntersectionMorphism f) :
    (coneComparisonIso (ringedSpaceHom f) (ringedSpaceHom g)
        (stalkwiseInjectiveOnH₁_of_lci f g hf)).hom =
      -(DerivedCategory.Q.map
        (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom f) (ringedSpaceHom g))) :=
  rfl

/-- The inverse of that comparison, followed by the canonical map of Stacks 0E1Z, is `-𝟙`. -/
theorem coneComparisonIso_inv_comp (hf : IsLocalCompleteIntersectionMorphism f) :
    (coneComparisonIso (ringedSpaceHom f) (ringedSpaceHom g)
          (stalkwiseInjectiveOnH₁_of_lci f g hf)).inv ≫
        DerivedCategory.Q.map
          (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom f) (ringedSpaceHom g)) =
      -(𝟙 _) := by
  rw [Iso.inv_comp_eq, coneComparisonIso_hom f g hf]
  simp

/-- The third morphism of the triangle of Stacks 0FV3: the third morphism of the triangle of the
mapping cocone, followed by the shift of the inverse of the comparison of Stacks 0E1Z. -/
theorem lciTriangle_mor₃ (hf : IsLocalCompleteIntersectionMorphism f) :
    (lciTriangle f g hf).mor₃ =
      (triangle (ringedSpaceHom f) (ringedSpaceHom g)).mor₃ ≫
        (CategoryTheory.shiftFunctor _ (1 : ℤ)).map
          (coneComparisonIso (ringedSpaceHom f) (ringedSpaceHom g)
            (stalkwiseInjectiveOnH₁_of_lci f g hf)).inv :=
  rfl

/-- **The triangle of Stacks 0FV3 in the arrows of Stacks 0E44.**  The triangle

`f^*NL_{Y/Z} ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ f^*NL_{Y/Z}[1]`

of `D(𝒪_X)` with `NL_{X/Z}` the naive cotangent complex of the composite `f ≫ g` and its first
two morphisms the images under `DerivedCategory.Q` of the two canonical chain maps of
Stacks 0E44. -/
def lciSchemeTriangle (hf : IsLocalCompleteIntersectionMorphism f) :
    Triangle (DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology (X.toRingedSpace : TopCat)) X.toRingedSpace.sheaf))) :=
  Triangle.mk (DerivedCategory.Q.map (pullbackToTotalMap f g))
    (DerivedCategory.Q.map (totalToRelativeMap f g))
    ((triangle (ringedSpaceHom f) (ringedSpaceHom g)).mor₃ ≫
      (CategoryTheory.shiftFunctor _ (1 : ℤ)).map
        (coneComparisonIso (ringedSpaceHom f) (ringedSpaceHom g)
          (stalkwiseInjectiveOnH₁_of_lci f g hf)).inv)

/-- **The first morphism of the triangle is the canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}` of
Stacks 0E44.** -/
theorem lciSchemeTriangle_mor₁ (hf : IsLocalCompleteIntersectionMorphism f) :
    (lciSchemeTriangle f g hf).mor₁ = DerivedCategory.Q.map (pullbackToTotalMap f g) :=
  rfl

/-- **The second morphism of the triangle is the canonical map `NL_{X/Z} ⟶ NL_{X/Y}` of
Stacks 0E44.** -/
theorem lciSchemeTriangle_mor₂ (hf : IsLocalCompleteIntersectionMorphism f) :
    (lciSchemeTriangle f g hf).mor₂ = DerivedCategory.Q.map (totalToRelativeMap f g) :=
  rfl

/-- **Stacks 0FV3.**  For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z` with `f` a local
complete intersection morphism, the canonical triangle

`f^*NL_{Y/Z} ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ f^*NL_{Y/Z}[1]`

is a distinguished triangle of `D(𝒪_X)`, with `NL_{X/Z}` the naive cotangent complex of `f ≫ g`
and its first two morphisms the two canonical chain maps of the six-term exact sequence of
Stacks 0E44.

It is the triangle of `Stacks.NaiveCotangentCompositionTriangle.lciTriangle` with its second
vertex transported along the identification of `NL_{f ≫ g}` with its iterated spelling. -/
@[stacks 0FV3 "the canonical distinguished triangle f^*NL_{Y/Z} -> NL_{X/Z} -> NL_{X/Y} -> \
f^*NL_{Y/Z}[1] of D(O_X) for a complete intersection morphism X -> Y, written over the \
complexes and the two canonical chain maps of the six-term sequence of 0E44 \
(lciSchemeTriangle_mor₁, lciSchemeTriangle_mor₂)", sga "6 VIII 2.6" "more general"]
theorem lciSchemeTriangle_distinguished (hf : IsLocalCompleteIntersectionMorphism f) :
    lciSchemeTriangle f g hf ∈ distTriang _ :=
  distTriang_of_iso_obj₂ (lciTriangle_distinguished f g hf)
    (DerivedCategory.Q.mapIso (totalCompIso f g)).symm
    (DerivedCategory.Q.map (pullbackToTotalMap f g))
    (DerivedCategory.Q.map (totalToRelativeMap f g)) _
    (((DerivedCategory.Q.map_comp _ _).symm.trans
      (congrArg DerivedCategory.Q.map
        (pullbackToTotalMap_comp_totalCompIso_hom f g))).trans (lciTriangle_mor₁ f g hf).symm)
    ((DerivedCategory.Q.map_comp (totalCompIso f g).hom (iteratedRelativeMap f g)).trans
      (congrArg (fun k => DerivedCategory.Q.map (totalCompIso f g).hom ≫ k)
        (lciTriangle_mor₂ f g hf).symm))
    (lciTriangle_mor₃ f g hf).symm

/-- The connecting morphism of the triangle of Stacks 0FV3 is the connecting morphism of the
triangle of the mapping cocone, followed by the map induced on `H⁰` by the inverse of the
comparison of Stacks 0E1Z. -/
@[reassoc]
theorem δ_lciSchemeTriangle (hf : IsLocalCompleteIntersectionMorphism f) :
    DerivedCategory.HomologySequence.δ (lciSchemeTriangle f g hf) (-1) 0 (by omega) =
      DerivedCategory.HomologySequence.δ
          (triangle (ringedSpaceHom f) (ringedSpaceHom g)) (-1) 0 (by omega) ≫
        (DerivedCategory.homologyFunctor _ 0).map
          (coneComparisonIso (ringedSpaceHom f) (ringedSpaceHom g)
            (stalkwiseInjectiveOnH₁_of_lci f g hf)).inv :=
  CategoryTheory.Functor.shiftMap_comp (DerivedCategory.homologyFunctor _ 0) _ _ (-1) 0 (by omega)

/-- **The connecting morphism of the triangle of Stacks 0FV3.**  Composed with the map induced on
`H⁰` by the canonical map of Stacks 0E1Z it is the negative of the connecting morphism of the
triangle of the mapping cocone of `NL_{X/Z} ⟶ NL_{X/Y}`.  The sign is the one between the
projection out of the mapping cocone and the projection through which Stacks 0E1Z characterises
its canonical map; it is the price of the triangle's first morphism being the canonical map
`f^*NL_{Y/Z} ⟶ NL_{X/Z}` with no sign. -/
@[stacks 0FV3 "the connecting morphism of the triangle, read along H^0 of the canonical map of \
0E1Z, is the negative of the connecting morphism of the long exact sequence of the triangle of \
the mapping cocone of NL_{X/Z} -> NL_{X/Y}"]
theorem δ_lciSchemeTriangle_comp_map (hf : IsLocalCompleteIntersectionMorphism f) :
    DerivedCategory.HomologySequence.δ (lciSchemeTriangle f g hf) (-1) 0 (by omega) ≫
        (DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (J := Opens.grothendieckTopology (X.toRingedSpace : TopCat))
              X.toRingedSpace.sheaf)) (0 : ℤ)).map (DerivedCategory.Q.map
          (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom f) (ringedSpaceHom g))) =
      -(DerivedCategory.HomologySequence.δ
        (triangle (ringedSpaceHom f) (ringedSpaceHom g)) (-1) 0 (by omega)) := by
  rw [δ_lciSchemeTriangle f g hf]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => DerivedCategory.HomologySequence.δ
          (triangle (ringedSpaceHom f) (ringedSpaceHom g)) (-1) 0 (by omega) ≫ k)
        ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
          ((congrArg _ (coneComparisonIso_inv_comp f g hf)).trans
            ((CategoryTheory.Functor.map_neg _).trans
              (congrArg Neg.neg (CategoryTheory.Functor.map_id _ _)))))).trans
      ((Preadditive.comp_neg _ _).trans (congrArg Neg.neg (Category.comp_id _))))

/-- **Stacks 0FV3: the triangle recovers the six-term exact sequence of Stacks 0E44.**  For
morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z` with `f` a local complete intersection
morphism, the long exact sequence of cohomology sheaves of the distinguished triangle

`f^*NL_{Y/Z} ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ f^*NL_{Y/Z}[1]`

is the six-term exact sequence

`H^{-1}(f^*NL_{Y/Z}) ⟶ H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) --∂--> f^*Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶`
`Ω_{X/Y} ⟶ 0`

of Stacks 0E44.  The nine assertions below are: its first two morphisms are the images under
`DerivedCategory.Q` of the two canonical chain maps `pullbackToTotalMap` and
`totalToRelativeMap` of Stacks 0E44, which induce four of the five arrows; its connecting
morphism and the connecting map `jacobiZariskiConnecting` of Stacks 0E44 both become, along the
map induced on `H⁰` by the canonical map of Stacks 0E1Z, the connecting morphism of the long
exact sequence of the triangle of the mapping cocone — up to the sign of the cocone projection;
and the sequence of those arrows is exact at its four interior terms and ends in `⟶ 0`.  The
last three terms are `f^*Ω_{Y/Z}`, `Ω_{X/Z}` and `Ω_{X/Y}` by
`Stacks.NaiveCotangentSixTermSequence.pullbackHomologyZeroIso` and Stacks 0D0J. -/
@[stacks 0FV3 "the recovery of the six-term exact sequence of 0E44 from lciSchemeTriangle: its \
first two morphisms are the images under Q of the two canonical chain maps of 0E44, its \
connecting morphism and the connecting map of 0E44 are both the connecting morphism of the long \
exact sequence of the triangle of the mapping cocone read along H^0 of the canonical map of \
0E1Z, and the six-term sequence of those arrows is exact at its four interior terms and ends in \
`-> 0`"]
theorem lciSchemeTriangle_recovers_sixTerm (hf : IsLocalCompleteIntersectionMorphism f) :
    (lciSchemeTriangle f g hf).mor₁ = DerivedCategory.Q.map (pullbackToTotalMap f g) ∧
      (lciSchemeTriangle f g hf).mor₂ = DerivedCategory.Q.map (totalToRelativeMap f g) ∧
      DerivedCategory.HomologySequence.δ (lciSchemeTriangle f g hf) (-1) 0 (by omega) ≫
          (DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (J := Opens.grothendieckTopology (X.toRingedSpace : TopCat))
              X.toRingedSpace.sheaf)) (0 : ℤ)).map (DerivedCategory.Q.map
            (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom f) (ringedSpaceHom g))) =
        -(DerivedCategory.HomologySequence.δ
          (triangle (ringedSpaceHom f) (ringedSpaceHom g)) (-1) 0 (by omega)) ∧
      jacobiZariskiConnecting f g ≫ HomologicalComplex.homologyMap
          (ringedSpaceNaiveCotangentConeMap (ringedSpaceHom f) (ringedSpaceHom g)) 0 =
        CochainComplex.homologyδOfTriangle
          (CochainComplex.mappingCocone.triangle (iteratedRelativeMap f g)) (-1) 0 (by omega) ∧
      (ShortComplex.mk (HomologicalComplex.homologyMap (pullbackToTotalMap f g) (-1))
        (HomologicalComplex.homologyMap (totalToRelativeMap f g) (-1))
        (homologyMap_pullbackToTotalMap_comp_totalToRelativeMap f g (-1))).Exact ∧
      (ShortComplex.mk (HomologicalComplex.homologyMap (totalToRelativeMap f g) (-1))
        (jacobiZariskiConnecting f g)
        (homologyMap_totalToRelativeMap_comp_connecting f g)).Exact ∧
      (ShortComplex.mk (jacobiZariskiConnecting f g)
        (HomologicalComplex.homologyMap (pullbackToTotalMap f g) 0)
        (connecting_comp_homologyMap_pullbackToTotalMap f g)).Exact ∧
      (ShortComplex.mk (HomologicalComplex.homologyMap (pullbackToTotalMap f g) 0)
        (HomologicalComplex.homologyMap (totalToRelativeMap f g) 0)
        (homologyMap_pullbackToTotalMap_comp_totalToRelativeMap f g 0)).Exact ∧
      Epi (HomologicalComplex.homologyMap (totalToRelativeMap f g) 0) :=
  ⟨lciSchemeTriangle_mor₁ f g hf, lciSchemeTriangle_mor₂ f g hf,
    δ_lciSchemeTriangle_comp_map f g hf,
    connecting_comp_homologyMap_eq_homologyδOfTriangle f g,
    exact_sixTerm_negOne_total f g, exact_sixTerm_negOne_relative f g,
    exact_sixTerm_zero_pullback f g, exact_sixTerm_zero_total f g,
    epi_homologyMap_totalToRelativeMap_zero f g⟩

end Derived

end Stacks.NaiveCotangentCompositionTriangle

end

end
