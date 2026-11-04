module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence

/-!
# The triangle of naive cotangent complexes of a composition

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be composable morphisms of ringed spaces.  The canonical map
`NL_{X/Z} ⟶ NL_{X/Y}` of complexes of `𝒪_X`-modules sits in the distinguished triangle

```
C(NL_{X/Z} ⟶ NL_{X/Y})[-1] ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1][1]
```

of `D(𝒪_X)`, and the canonical map `f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]` carries
`f^*NL_{Y/Z}` into its first vertex compatibly with the canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}`.
Once that comparison is invertible the first vertex may be replaced by `f^*NL_{Y/Z}`.

## Main definitions

* `Stacks.NaiveCotangentCompositionTriangle.relativeNaiveCotangentMap`: the canonical map
  `NL_{X/Z} ⟶ NL_{X/Y}`, and
  `Stacks.NaiveCotangentCompositionTriangle.pulledNaiveCotangentMap`: the canonical map
  `f^*NL_{Y/Z} ⟶ NL_{X/Z}`.
* `Stacks.NaiveCotangentCompositionTriangle.triangle`: the triangle displayed above, the image
  in `D(𝒪_X)` of the triangle of the mapping cocone of the canonical map `NL_{X/Z} ⟶ NL_{X/Y}`.

## Main results

* `Stacks.NaiveCotangentCompositionTriangle.triangle_distinguished`: the triangle is
  distinguished, `triangle_mor₁` and `triangle_mor₂` identifying its first two morphisms as the
  projection out of the mapping cocone and the canonical map `NL_{X/Z} ⟶ NL_{X/Y}`.
* `Stacks.NaiveCotangentCompositionTriangle.coneMap_comp_fst`: the canonical map of
  Stacks 0E1Z, composed with the projection of the mapping cocone onto `NL_{X/Z}`, is the
  canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}` up to sign.  This is what makes that comparison a lift
  of the canonical map, hence the triangle the triangle of a composition rather than an
  arbitrary triangle on a cone.

## Implementation notes

The three naive cotangent complexes are those of the sequence of sheaves of commutative rings
`f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` on `X`, in the iterated spelling of the canonical map of
Stacks 0E1Z: `NL_{X/Z}` is the naive cotangent complex of `𝒪_X` over `f⁻¹g⁻¹𝒪_Z` rather than
over `(g ∘ f)⁻¹𝒪_Z`.  Keeping the iterated spelling is what lets the comparison of Stacks 0E1Z
be used as it stands.

The shift by `-1` of the mapping cone is `CochainComplex.mappingCocone`, so the triangle on the
cone is taken in the unrotated form `CochainComplex.mappingCocone.triangle`, whose first vertex
is already the shifted cone and whose first morphism is the projection
`CochainComplex.mappingCocone.fst`.  That projection is the negative of the projection `pShift`
obtained by shifting the third morphism of the triangle of the mapping cone, which is the
projection through which Stacks 0E1Z characterises the comparison; this is the source of the
sign in `coneMap_comp_fst`.

`D(𝒪_X)` is the derived category of the abelian category of sheaves of `𝒪_X`-modules, and the
`HasDerivedCategory` hypothesis is carried in the spelling
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf 𝒪_X)` in which the naive cotangent complex
of a morphism of ringed spaces is built, as in `Stacks.Sheaves.RingedSpaceCotangent`.

Invertibility in `D(𝒪_X)` of the comparison of Stacks 0E1Z is exactly the assertion that the
first vertex of the triangle is `f^*NL_{Y/Z}`; it is not proved here, and it is where the
complete intersection hypothesis of Stacks 0FV3 enters.  It is proved in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentCompositionTriangleLci`
(`Stacks.NaiveCotangentCompositionTriangle.isIso_Q_map_coneMap_of_lci`), where the triangle of
Stacks 0FV3 with `f^*NL_{Y/Z}` as its first vertex is built from it.

## References

* [Stacks Project, Tag 0FV3](https://stacks.math.columbia.edu/tag/0FV3)
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z), the canonical map
  `f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]` and its defining property.
* [Stacks Project, Tag 0E44](https://stacks.math.columbia.edu/tag/0E44), the six-term exact
  sequence of cohomology sheaves.
* [Stacks Project, Tag 08RI](https://stacks.math.columbia.edu/tag/08RI), part (2),
  factorisation through a shifted cone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry CochainComplex
open Stacks.SheafOfModules

universe t u

namespace Stacks.NaiveCotangentCompositionTriangle

/-! ### The two projections out of the shifted cone -/

section Projections

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The projection `C(φ)[-1] ⟶ K` out of the mapping cocone is the negative of the projection
obtained by shifting the third morphism `C(φ) ⟶ K[1]` of the triangle of the mapping cone: the
latter morphism carries a sign that the former does not. -/
private theorem mappingCocone_fst_eq_neg_pShift : mappingCocone.fst φ = -pShift φ := by
  ext p
  simp [mappingCocone.fst, pShift, mappingCone.triangle,
    HomComplex.Cochain.leftShift_v ((mappingCone.fst φ : HomComplex.Cochain (mappingCone φ) K 1))
      (-1) 0 (by lia) p p (by lia) (p + -1) (by lia),
    HomComplex.Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl,
    HomComplex.Cochain.v_comp_XIsoOfEq_hom,
    CategoryTheory.shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f',
    shiftFunctorZero_hom_app_f]
  rfl

end Projections

/-! ### The canonical maps -/

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The canonical map `NL_{X/Z} ⟶ NL_{X/Y}` of complexes of `𝒪_X`-modules attached to the
factorisation `f⁻¹g⁻¹𝒪_Z ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure morphism of `𝒪_X`. -/
noncomputable abbrev relativeNaiveCotangentMap :
    Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
        (Opens.grothendieckTopology (X : TopCat)) (inverseImageBaseRing f g) X.sheaf
        (inverseImageFirstRingMap f g ≫ ringedSpaceStructureMap f) ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
        (Opens.grothendieckTopology (X : TopCat)) (inverseImageMiddleRing f) X.sheaf
        (ringedSpaceStructureMap f) :=
  spaceRelativeNaiveCotangentComplexMap (inverseImageBaseRing f g) (inverseImageMiddleRing f)
    X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)

/-- The canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}` of complexes of `𝒪_X`-modules: the canonical map
`NL_{f⁻¹𝒪_Y/f⁻¹g⁻¹𝒪_Z} ⊗ 𝒪_X ⟶ NL_{X/Z}`, precomposed with the identification of `f^*NL_{Y/Z}`
with that base change. -/
noncomputable abbrev pulledNaiveCotangentMap :
    pulledNaiveCotangentComplex f g ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u}
        (Opens.grothendieckTopology (X : TopCat)) (inverseImageBaseRing f g) X.sheaf
        (inverseImageFirstRingMap f g ≫ ringedSpaceStructureMap f) :=
  (pulledNaiveCotangentComparison f g).hom ≫
    spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing f g) (inverseImageMiddleRing f)
      X.sheaf (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)

/-- **Stacks 0FV3**, the comparison.  The canonical map
`f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]` of Stacks 0E1Z, composed with the projection of the
mapping cocone onto `NL_{X/Z}`, is the negative of the canonical map `f^*NL_{Y/Z} ⟶ NL_{X/Z}`.
This is what makes the comparison a lift of that canonical map; the sign is the one between the
projection out of the mapping cocone and the projection of Stacks 0E1Z. -/
@[stacks 0FV3 "the canonical map f^*NL_{Y/Z} -> C(NL_{X/Z} -> NL_{X/Y})[-1] of 0E1Z and its \
compatibility, up to the sign of the cocone projection, with the canonical map f^*NL_{Y/Z} -> \
NL_{X/Z}; NOT its invertibility, which is where the complete intersection hypothesis enters and \
which is isIso_Q_map_coneMap_of_lci"]
theorem coneMap_comp_fst :
    ringedSpaceNaiveCotangentConeMap f g ≫ mappingCocone.fst (relativeNaiveCotangentMap f g) =
      -pulledNaiveCotangentMap f g := by
  rw [mappingCocone_fst_eq_neg_pShift, Preadditive.comp_neg,
    ringedSpaceNaiveCotangentConeMap_comp_pShift]

/-! ### The triangle -/

section Derived

variable [HasDerivedCategory.{t} (_root_.SheafOfModules.{u}
  (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology (X : TopCat)) X.sheaf))]

/-- The triangle `C(NL_{X/Z} ⟶ NL_{X/Y})[-1] ⟶ NL_{X/Z} ⟶ NL_{X/Y} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})` of
`D(𝒪_X)`: the image of the triangle of the mapping cocone of the canonical map
`NL_{X/Z} ⟶ NL_{X/Y}`. -/
noncomputable def triangle :
    Triangle (DerivedCategory (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology (X : TopCat)) X.sheaf))) :=
  DerivedCategory.Q.mapTriangle.obj (mappingCocone.triangle (relativeNaiveCotangentMap f g))

/-- **Stacks 0FV3**, the triangle.  The triangle on the canonical map `NL_{X/Z} ⟶ NL_{X/Y}`,
with the shift by `-1` of its cone as first vertex, is a distinguished triangle of `D(𝒪_X)`. -/
@[stacks 0FV3 "the distinguished triangle C(NL_{X/Z} -> NL_{X/Y})[-1] -> NL_{X/Z} -> NL_{X/Y} \
-> C(NL_{X/Z} -> NL_{X/Y})[-1][1] of D(O_X), whose second morphism is the canonical map, \
together with the canonical map of 0E1Z into its first vertex (coneMap_comp_fst); NOT the \
invertibility of that comparison, which is where the complete intersection hypothesis enters, \
and NOT the recovery of the six-term exact sequence of 0E44 -- those two are \
isIso_Q_map_coneMap_of_lci and lciTriangle_recovers_sixTerm, and the triangle with \
f^*NL_{Y/Z} as its first vertex is lciTriangle_distinguished"]
theorem triangle_distinguished : triangle f g ∈ distTriang _ :=
  DerivedCategory.mappingCocone_triangle_distinguished _

/-- The first morphism of the triangle is the projection out of the mapping cocone. -/
theorem triangle_mor₁ :
    (triangle f g).mor₁ =
      DerivedCategory.Q.map (mappingCocone.fst (relativeNaiveCotangentMap f g)) :=
  rfl

/-- The second morphism of the triangle is the canonical map `NL_{X/Z} ⟶ NL_{X/Y}`. -/
theorem triangle_mor₂ :
    (triangle f g).mor₂ = DerivedCategory.Q.map (relativeNaiveCotangentMap f g) :=
  rfl

end Derived

end Stacks.NaiveCotangentCompositionTriangle

end
