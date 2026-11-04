module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentConeHomologyZero
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSheaves

/-!
# The connecting morphism and the last two exactness assertions of Stacks 0E1Y and 0E1Z

Let `A ⟶ B ⟶ C` be morphisms of sheaves of commutative rings on a topological space.  Four of
the six assertions of the exact sequence of Stacks 0E1Y are statements about the two canonical
maps `c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}` and `g : NL_{C/A} ⟶ NL_{C/B}` alone, proved in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentJacobiZariskiSheaves`.  The remaining two,
exactness at `H^{-1}(NL_{C/B})` and at `H⁰(NL_{B/A} ⊗_B C)`, involve the sixth arrow of the
sequence, the connecting morphism

`∂ : H^{-1}(NL_{C/B}) ⟶ H⁰(NL_{B/A} ⊗_B C)`,

which this file defines, and which does not exist until the canonical map
`c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]` of Stacks 0E1Y is known to be an isomorphism on `H⁰`
(`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`).  Given that, `∂` is
the connecting morphism `H^{-1}(NL_{C/B}) ⟶ H⁰(C(g)[-1])` of the long exact sequence of the cone
followed by the inverse of `H⁰(c)`, and the two exactness assertions are the exactness of that
long exact sequence at `H^{-1}(NL_{C/B})` and at `H⁰(C(g)[-1])`, transported along `H⁰(c)`.  All
three are then transported to a pair of composable morphisms of ringed spaces, where they are
the corresponding assertions of Stacks 0E1Z for the tower `(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X`, the
first term being carried along the identification of Stacks 08TM.

With this file the six-term exact sequences of Stacks 0E1Y and of Stacks 0E1Z are complete.

## Main definitions

* `Stacks.SheafOfModules.spaceJacobiZariskiConnecting`: **the connecting morphism
  `H^{-1}(NL_{C/B}) ⟶ H⁰(NL_{B/A} ⊗_B C)`** of Stacks 0E1Y.
* `Stacks.SheafOfModules.ringedSpaceJacobiZariskiConnecting`: **the connecting morphism
  `H^{-1}(NL_{X/Y}) ⟶ H⁰(f^*NL_{Y/Z})`** of Stacks 0E1Z.
* `Stacks.SheafOfModules.spaceJacobiZariskiSixTermZeroIso`,
  `spaceJacobiZariskiSixTermNegOneIso` and their ringed-space counterparts: the two segments of
  the sequence, as isomorphic to segments of the long exact sequence of the cone.

## Main results

* `Stacks.SheafOfModules.exact_spaceJacobiZariskiSixTerm_zero` and
  `exact_spaceJacobiZariskiSixTerm_negOne`: **the six-term sequence of Stacks 0E1Y is exact at
  `H⁰(NL_{B/A} ⊗_B C)` and at `H^{-1}(NL_{C/B})`.**
* `Stacks.SheafOfModules.exact_ringedSpaceJacobiZariskiSixTerm_zero` and
  `exact_ringedSpaceJacobiZariskiSixTerm_negOne`: **the six-term sequence of Stacks 0E1Z is
  exact at `H⁰(f^*NL_{Y/Z})` and at `H^{-1}(NL_{X/Y})`.**
* `Stacks.SheafOfModules.isIso_homologyMap_ringedSpaceNaiveCotangentConeMap_zero`: the canonical
  map of Stacks 0E1Z is an isomorphism on `H⁰`.
* `Stacks.SheafOfModules.inv_homologyMap_spaceNaiveCotangentConeMap_comp` and its ringed-space
  counterpart: the inverse of `H⁰(c)` followed by the map induced by `c₁` is the map induced by
  the projection of the shifted cone, which is the square identifying the two sequences.

## Implementation notes

The two isomorphisms of short complexes are given their own declarations rather than being
inlined into `CategoryTheory.ShortComplex.exact_of_iso`, because `ShortComplex.isoMk` cannot
elaborate its component isomorphisms while the source short complex is still a metavariable.

`Stacks.SheafOfModules.spaceNaiveCotangentConeHomologyConnecting` unfolds to a plain definition,
so `rw` does not see through it to `CochainComplex.coneHomologyConnecting`; the two vanishing
composites are therefore stated at the former and proved by an `exact` of the latter, which is
tolerant of the unfolding.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y)
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z)
* [Stacks Project, Tag 08RI](https://stacks.math.columbia.edu/tag/08RI), the long exact sequence
  of the cone.
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM), the inverse image of
  the naive cotangent complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.SheafOfModules


/-! ### Sheaves of rings on a topological space -/

section Space

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C)

/-- **Stacks 0E1Y, the connecting morphism of the six-term sequence**
`∂ : H^{-1}(NL_{C/B}) ⟶ H⁰(NL_{B/A} ⊗_B C)`, for morphisms `A ⟶ B ⟶ C` of sheaves of
commutative rings on a topological space.

It is the connecting morphism of the long exact sequence of the cone of
`g : NL_{C/A} ⟶ NL_{C/B}`, whose target `H⁰(C(g)[-1])` is identified with
`H⁰(NL_{B/A} ⊗_B C)` by the canonical map `c` of Stacks 0E1Y, an isomorphism on `H⁰` by
`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`. -/
@[stacks 0E1Y "the connecting morphism H^{-1}(NL_{C/B}) -> H^0(NL_{B/A} ⊗_B C)"]
noncomputable def spaceJacobiZariskiConnecting :=
  spaceNaiveCotangentConeHomologyConnecting A B C a b (-1) 0 (by ring) ≫
    inv (HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) 0)

/-- The connecting morphism `∂` is the connecting morphism `H^{-1}(NL_{C/B}) ⟶ H⁰(C(g)[-1])` of
the cone followed by the inverse of `H⁰(c)`. -/
theorem spaceJacobiZariskiConnecting_eq :
    spaceJacobiZariskiConnecting A B C a b =
      spaceNaiveCotangentConeHomologyConnecting A B C a b (-1) 0 (by ring) ≫
        inv (HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) 0) :=
  rfl

/-- The inverse of `H⁰(c)` followed by the map induced by `c₁` is the map induced by the
projection of the shifted cone. -/
theorem inv_homologyMap_spaceNaiveCotangentConeMap_comp :
    inv (HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) 0) ≫
        HomologicalComplex.homologyMap (spaceBaseChangeNaiveCotangentMap A B C a b) 0 =
      HomologicalComplex.homologyMap
        (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) 0 := by
  rw [← spaceNaiveCotangentConeMap_homologyMap_comp_pShift A B C a b 0, ← Category.assoc,
    IsIso.inv_hom_id, Category.id_comp]

/-- The composite `H^{-1}(NL_{C/B}) --∂--> H⁰(NL_{B/A} ⊗_B C) ⟶ H⁰(NL_{C/A})` vanishes. -/
theorem spaceJacobiZariskiConnecting_comp_homologyMap :
    spaceJacobiZariskiConnecting A B C a b ≫
        HomologicalComplex.homologyMap (spaceBaseChangeNaiveCotangentMap A B C a b) 0 = 0 := by
  rw [spaceJacobiZariskiConnecting_eq, Category.assoc,
    inv_homologyMap_spaceNaiveCotangentConeMap_comp]
  exact CochainComplex.coneHomologyConnecting_comp_homologyMap_pShift
    (spaceRelativeNaiveCotangentComplexMap A B C a b) (-1) 0 (by ring)

/-- The composite `H^{-1}(NL_{C/A}) ⟶ H^{-1}(NL_{C/B}) --∂--> H⁰(NL_{B/A} ⊗_B C)` vanishes. -/
theorem homologyMap_comp_spaceJacobiZariskiConnecting :
    HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap A B C a b) (-1) ≫
      spaceJacobiZariskiConnecting A B C a b = 0 := by
  rw [spaceJacobiZariskiConnecting_eq, ← Category.assoc]
  erw [CochainComplex.homologyMap_comp_coneHomologyConnecting _ (-1) 0 (by ring),
    Limits.zero_comp]

/-- The sequence `H^{-1}(NL_{C/B}) --∂--> H⁰(NL_{B/A} ⊗_B C) ⟶ H⁰(NL_{C/A})` is the segment
`H^{-1}(NL_{C/B}) --∂--> H⁰(C(g)[-1]) ⟶ H⁰(NL_{C/A})` of the long exact sequence of the cone,
transported along the isomorphism `H⁰(c)`. -/
noncomputable def spaceJacobiZariskiSixTermZeroIso :
    ShortComplex.mk (spaceNaiveCotangentConeHomologyConnecting A B C a b (-1) 0 (by ring))
        (HomologicalComplex.homologyMap
          (pShift (spaceRelativeNaiveCotangentComplexMap A B C a b)) 0)
        (CochainComplex.coneHomologyConnecting_comp_homologyMap_pShift
          (spaceRelativeNaiveCotangentComplexMap A B C a b) (-1) 0 (by ring)) ≅
      ShortComplex.mk (spaceJacobiZariskiConnecting A B C a b)
        (HomologicalComplex.homologyMap (spaceBaseChangeNaiveCotangentMap A B C a b) 0)
        (spaceJacobiZariskiConnecting_comp_homologyMap A B C a b) :=
  ShortComplex.isoMk (Iso.refl _)
    (asIso (HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) 0)).symm
    (Iso.refl _)
    ((Category.id_comp _).trans (spaceJacobiZariskiConnecting_eq A B C a b))
    ((inv_homologyMap_spaceNaiveCotangentConeMap_comp A B C a b).trans
      (Category.comp_id _).symm)

/-- The sequence `H^{-1}(NL_{C/A}) ⟶ H^{-1}(NL_{C/B}) --∂--> H⁰(NL_{B/A} ⊗_B C)` is the segment
`H^{-1}(NL_{C/A}) ⟶ H^{-1}(NL_{C/B}) --∂--> H⁰(C(g)[-1])` of the long exact sequence of the cone,
transported along the isomorphism `H⁰(c)`. -/
noncomputable def spaceJacobiZariskiSixTermNegOneIso :
    ShortComplex.mk
        (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap A B C a b) (-1))
        (spaceNaiveCotangentConeHomologyConnecting A B C a b (-1) 0 (by ring))
        (CochainComplex.homologyMap_comp_coneHomologyConnecting
          (spaceRelativeNaiveCotangentComplexMap A B C a b) (-1) 0 (by ring)) ≅
      ShortComplex.mk
        (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap A B C a b) (-1))
        (spaceJacobiZariskiConnecting A B C a b)
        (homologyMap_comp_spaceJacobiZariskiConnecting A B C a b) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (asIso (HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap A B C a b) 0)).symm
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (spaceJacobiZariskiConnecting_eq A B C a b))

/-- **Stacks 0E1Y, exactness at `H⁰(NL_{B/A} ⊗_B C)`.**  For morphisms `A ⟶ B ⟶ C` of sheaves of
commutative rings on a topological space the sequence

`H^{-1}(NL_{C/B}) --∂--> H⁰(NL_{B/A} ⊗_B C) ⟶ H⁰(NL_{C/A})`

of cohomology sheaves is exact at the middle term.

This is the exactness of the long exact sequence of the cone at `H⁰(C(g)[-1])`
(`Stacks.SheafOfModules.spaceNaiveCotangentCone_homology_exact_cone`), transported along the
isomorphism `H⁰(c)` of
`Stacks.SheafOfModules.isIso_homologyMap_spaceNaiveCotangentConeMap_zero`. -/
@[stacks 0E1Y "exactness of the six-term sequence at H^0(NL_{B/A} ⊗_B C)"]
theorem exact_spaceJacobiZariskiSixTerm_zero :
    (ShortComplex.mk (spaceJacobiZariskiConnecting A B C a b)
      (HomologicalComplex.homologyMap (spaceBaseChangeNaiveCotangentMap A B C a b) 0)
      (spaceJacobiZariskiConnecting_comp_homologyMap A B C a b)).Exact :=
  ShortComplex.exact_of_iso (spaceJacobiZariskiSixTermZeroIso A B C a b)
    (spaceNaiveCotangentCone_homology_exact_cone A B C a b (-1) 0 (by ring))

/-- **Stacks 0E1Y, exactness at `H^{-1}(NL_{C/B})`.**  For morphisms `A ⟶ B ⟶ C` of sheaves of
commutative rings on a topological space the sequence

`H^{-1}(NL_{C/A}) ⟶ H^{-1}(NL_{C/B}) --∂--> H⁰(NL_{B/A} ⊗_B C)`

of cohomology sheaves is exact at the middle term.

This is the exactness of the long exact sequence of the cone at `H^{-1}(NL_{C/B})`
(`Stacks.SheafOfModules.spaceNaiveCotangentCone_homology_exact_target`), transported along the
isomorphism `H⁰(c)`. -/
@[stacks 0E1Y "exactness of the six-term sequence at H^{-1}(NL_{C/B})"]
theorem exact_spaceJacobiZariskiSixTerm_negOne :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap A B C a b) (-1))
      (spaceJacobiZariskiConnecting A B C a b)
      (homologyMap_comp_spaceJacobiZariskiConnecting A B C a b)).Exact :=
  ShortComplex.exact_of_iso (spaceJacobiZariskiSixTermNegOneIso A B C a b)
    (spaceNaiveCotangentCone_homology_exact_target A B C a b (-1) 0 (by ring))

end Space

/-! ### Ringed spaces -/

section RingedSpace

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Stacks 0E1Z: the canonical map `f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]` is an
isomorphism on `H⁰`.**  It is the identification of Stacks 08TM, an isomorphism, followed by
the canonical map of Stacks 0E1Y for the tower `(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X`. -/
instance isIso_homologyMap_ringedSpaceNaiveCotangentConeMap_zero :
    IsIso (HomologicalComplex.homologyMap (ringedSpaceNaiveCotangentConeMap f g) 0) := by
  have hcomp : HomologicalComplex.homologyMap (ringedSpaceNaiveCotangentConeMap f g) 0 =
      HomologicalComplex.homologyMap (pulledNaiveCotangentComparison f g).hom 0 ≫
        HomologicalComplex.homologyMap (spaceNaiveCotangentConeMap (inverseImageBaseRing f g)
          (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
          (ringedSpaceStructureMap f)) 0 :=
    HomologicalComplex.homologyMap_comp _ _ 0
  rw [hcomp]
  exact IsIso.comp_isIso' (isIso_homologyMap_pulledNaiveCotangentComparison f g 0)
    (isIso_homologyMap_spaceNaiveCotangentConeMap_zero (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f))

/-- **Stacks 0E1Z, the connecting morphism of the six-term sequence**
`∂ : H^{-1}(NL_{X/Y}) ⟶ H⁰(f^*NL_{Y/Z})`, for composable morphisms of ringed spaces. -/
@[stacks 0E1Z "the connecting morphism H^{-1}(NL_{X/Y}) -> H^0(f^*NL_{Y/Z})"]
noncomputable def ringedSpaceJacobiZariskiConnecting :=
  ringedSpaceNaiveCotangentConeHomologyConnecting f g (-1) 0 (by ring) ≫
    inv (HomologicalComplex.homologyMap (ringedSpaceNaiveCotangentConeMap f g) 0)

/-- The connecting morphism `∂` is the connecting morphism `H^{-1}(NL_{X/Y}) ⟶ H⁰(C[-1])` of
the cone of `NL_{X/Z} ⟶ NL_{X/Y}` followed by the inverse of `H⁰` of the canonical map
`f^*NL_{Y/Z} ⟶ C(NL_{X/Z} ⟶ NL_{X/Y})[-1]`. -/
theorem ringedSpaceJacobiZariskiConnecting_eq :
    ringedSpaceJacobiZariskiConnecting f g =
      ringedSpaceNaiveCotangentConeHomologyConnecting f g (-1) 0 (by ring) ≫
        inv (HomologicalComplex.homologyMap (ringedSpaceNaiveCotangentConeMap f g) 0) :=
  rfl

/-- The inverse of `H⁰` of the canonical map of Stacks 0E1Z followed by the map induced by
`f^*NL_{Y/Z} ⟶ NL_{X/Z}` is the map induced by the projection of the shifted cone. -/
theorem inv_homologyMap_ringedSpaceNaiveCotangentConeMap_comp :
    inv (HomologicalComplex.homologyMap (ringedSpaceNaiveCotangentConeMap f g) 0) ≫
        HomologicalComplex.homologyMap ((pulledNaiveCotangentComparison f g).hom ≫
          spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing f g)
            (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
            (ringedSpaceStructureMap f)) 0 =
      HomologicalComplex.homologyMap (pShift (spaceRelativeNaiveCotangentComplexMap
        (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
        (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f))) 0 := by
  rw [IsIso.inv_comp_eq]
  exact (congrArg (fun φ => HomologicalComplex.homologyMap φ 0)
      (ringedSpaceNaiveCotangentConeMap_comp_pShift f g)).symm.trans
    (HomologicalComplex.homologyMap_comp _ _ 0)

/-- The composite `H^{-1}(NL_{X/Y}) --∂--> H⁰(f^*NL_{Y/Z}) ⟶ H⁰(NL_{X/Z})` vanishes. -/
theorem ringedSpaceJacobiZariskiConnecting_comp_homologyMap :
    ringedSpaceJacobiZariskiConnecting f g ≫
        HomologicalComplex.homologyMap ((pulledNaiveCotangentComparison f g).hom ≫
          spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing f g)
            (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
            (ringedSpaceStructureMap f)) 0 = 0 := by
  rw [ringedSpaceJacobiZariskiConnecting_eq, Category.assoc,
    inv_homologyMap_ringedSpaceNaiveCotangentConeMap_comp]
  exact CochainComplex.coneHomologyConnecting_comp_homologyMap_pShift
    (spaceRelativeNaiveCotangentComplexMap (inverseImageBaseRing f g)
      (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
      (ringedSpaceStructureMap f)) (-1) 0 (by ring)

/-- The composite `H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) --∂--> H⁰(f^*NL_{Y/Z})` vanishes. -/
theorem homologyMap_comp_ringedSpaceJacobiZariskiConnecting :
    HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap
        (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
        (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) (-1) ≫
      ringedSpaceJacobiZariskiConnecting f g = 0 := by
  rw [ringedSpaceJacobiZariskiConnecting_eq, ← Category.assoc]
  erw [CochainComplex.homologyMap_comp_coneHomologyConnecting _ (-1) 0 (by ring),
    Limits.zero_comp]

/-- The sequence `H^{-1}(NL_{X/Y}) --∂--> H⁰(f^*NL_{Y/Z}) ⟶ H⁰(NL_{X/Z})` is the corresponding
segment of the long exact sequence of the cone, transported along the isomorphism `H⁰` of the
canonical map of Stacks 0E1Z. -/
noncomputable def ringedSpaceJacobiZariskiSixTermZeroIso :
    ShortComplex.mk (ringedSpaceNaiveCotangentConeHomologyConnecting f g (-1) 0 (by ring))
        (HomologicalComplex.homologyMap (pShift (spaceRelativeNaiveCotangentComplexMap
          (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
          (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f))) 0)
        (CochainComplex.coneHomologyConnecting_comp_homologyMap_pShift
          (spaceRelativeNaiveCotangentComplexMap (inverseImageBaseRing f g)
            (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
            (ringedSpaceStructureMap f)) (-1) 0 (by ring)) ≅
      ShortComplex.mk (ringedSpaceJacobiZariskiConnecting f g)
        (HomologicalComplex.homologyMap ((pulledNaiveCotangentComparison f g).hom ≫
          spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing f g)
            (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
            (ringedSpaceStructureMap f)) 0)
        (ringedSpaceJacobiZariskiConnecting_comp_homologyMap f g) :=
  ShortComplex.isoMk (Iso.refl _)
    (asIso (HomologicalComplex.homologyMap (ringedSpaceNaiveCotangentConeMap f g) 0)).symm
    (Iso.refl _)
    ((Category.id_comp _).trans (ringedSpaceJacobiZariskiConnecting_eq f g))
    ((inv_homologyMap_ringedSpaceNaiveCotangentConeMap_comp f g).trans
      (Category.comp_id _).symm)

/-- The sequence `H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) --∂--> H⁰(f^*NL_{Y/Z})` is the
corresponding segment of the long exact sequence of the cone, transported along the isomorphism
`H⁰` of the canonical map of Stacks 0E1Z. -/
noncomputable def ringedSpaceJacobiZariskiSixTermNegOneIso :
    ShortComplex.mk
        (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap
          (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
          (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) (-1))
        (ringedSpaceNaiveCotangentConeHomologyConnecting f g (-1) 0 (by ring))
        (CochainComplex.homologyMap_comp_coneHomologyConnecting
          (spaceRelativeNaiveCotangentComplexMap (inverseImageBaseRing f g)
            (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
            (ringedSpaceStructureMap f)) (-1) 0 (by ring)) ≅
      ShortComplex.mk
        (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap
          (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
          (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) (-1))
        (ringedSpaceJacobiZariskiConnecting f g)
        (homologyMap_comp_ringedSpaceJacobiZariskiConnecting f g) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (asIso (HomologicalComplex.homologyMap (ringedSpaceNaiveCotangentConeMap f g) 0)).symm
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (ringedSpaceJacobiZariskiConnecting_eq f g))

/-- **Stacks 0E1Z, exactness at `H⁰(f^*NL_{Y/Z})`.**  For composable morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z` the sequence

`H^{-1}(NL_{X/Y}) --∂--> H⁰(f^*NL_{Y/Z}) ⟶ H⁰(NL_{X/Z})`

of cohomology sheaves is exact at the middle term. -/
@[stacks 0E1Z "exactness of the six-term sequence at H^0(f^*NL_{Y/Z})"]
theorem exact_ringedSpaceJacobiZariskiSixTerm_zero :
    (ShortComplex.mk (ringedSpaceJacobiZariskiConnecting f g)
      (HomologicalComplex.homologyMap ((pulledNaiveCotangentComparison f g).hom ≫
        spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing f g)
          (inverseImageMiddleRing f) X.sheaf (inverseImageFirstRingMap f g)
          (ringedSpaceStructureMap f)) 0)
      (ringedSpaceJacobiZariskiConnecting_comp_homologyMap f g)).Exact :=
  ShortComplex.exact_of_iso (ringedSpaceJacobiZariskiSixTermZeroIso f g)
    (ringedSpaceNaiveCotangentCone_homology_exact_cone f g (-1) 0 (by ring))

/-- **Stacks 0E1Z, exactness at `H^{-1}(NL_{X/Y})`.**  For composable morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z` the sequence

`H^{-1}(NL_{X/Z}) ⟶ H^{-1}(NL_{X/Y}) --∂--> H⁰(f^*NL_{Y/Z})`

of cohomology sheaves is exact at the middle term. -/
@[stacks 0E1Z "exactness of the six-term sequence at H^{-1}(NL_{X/Y})"]
theorem exact_ringedSpaceJacobiZariskiSixTerm_negOne :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (spaceRelativeNaiveCotangentComplexMap
        (inverseImageBaseRing f g) (inverseImageMiddleRing f) X.sheaf
        (inverseImageFirstRingMap f g) (ringedSpaceStructureMap f)) (-1))
      (ringedSpaceJacobiZariskiConnecting f g)
      (homologyMap_comp_ringedSpaceJacobiZariskiConnecting f g)).Exact :=
  ShortComplex.exact_of_iso (ringedSpaceJacobiZariskiSixTermNegOneIso f g)
    (ringedSpaceNaiveCotangentCone_homology_exact_target f g (-1) 0 (by ring))

end RingedSpace

end Stacks.SheafOfModules

end

end
