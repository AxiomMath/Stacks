module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentConeMap

/-!
# The long exact sequence of the cone of `NL_{C/A} ⟶ NL_{C/B}`

Let `a : A ⟶ B` and `b : B ⟶ C` be morphisms of sheaves of commutative rings on a site and let
`g : NL_{C/A} ⟶ NL_{C/B}` be the canonical chain map of complexes of sheaves of `C`-modules.
The cone `C(g)` sits in a short exact sequence of complexes

`0 ⟶ NL_{C/B} ⟶ C(g) ⟶ NL_{C/A}[1] ⟶ 0`

which is split in each degree, since `C(g)ⁿ = NL_{C/B}ⁿ ⊕ NL_{C/A}ⁿ⁺¹`.  This file records that
sequence, its short exactness, and the long exact sequence of cohomology sheaves that the snake
lemma attaches to it.  Together with the comparison of `NL_{B/A} ⊗_B C` with `C(g)[-1]` along
the canonical map of **Stacks 0E1Y**, this long exact sequence is the six-term exact sequence of
that tag: the naive cotangent complex has no cohomology outside degrees `-1` and `0`, so only
six of its terms are possibly nonzero.

The short exact sequence is obtained from Mathlib's `CochainComplex.mappingCone`: it is the
short complex underlying the rotation of the cone triangle
`NL_{C/A} ⟶ NL_{C/B} ⟶ C(g) ⟶ NL_{C/A}[1]`, so that

* `X₁` is `NL_{C/B}` and the first map is `CochainComplex.mappingCone.inr g`,
* `X₂` is `C(g)`,
* `X₃` is `NL_{C/A}[1]` and the second map is `(CochainComplex.mappingCone.triangle g).mor₃`.

No derived category is involved, and no hypothesis beyond the data `A ⟶ B ⟶ C` is assumed.

## Main definitions

* `Stacks.SheafOfModules.naiveCotangentConeShortComplex`: the short complex
  `NL_{C/B} ⟶ C(g) ⟶ NL_{C/A}[1]`.
* `Stacks.SheafOfModules.naiveCotangentConeConnecting`: the connecting morphism
  `Hⁱ(NL_{C/A}[1]) ⟶ Hʲ(NL_{C/B})` of the long exact sequence.
* `Stacks.SheafOfModules.naiveCotangentConeHomologyConnecting`: the connecting morphism
  `Hⁱ(NL_{C/B}) ⟶ H^{i+1}(C(g)[-1])` of the cone triangle, whose target is where the canonical
  map of Stacks 0E1Y lands.  This is the connecting arrow of the six-term sequence of that tag,
  read before the comparison of `H⁰(NL_{B/A} ⊗_B C)` with `H⁰(C(g)[-1])`.
* `Stacks.SheafOfModules.naiveCotangentShiftHomologyIso` and
  `Stacks.SheafOfModules.shiftedNaiveCotangentConeHomologyIso`: the identifications
  `Hⁱ(NL_{C/A}[1]) ≅ H^{1+i}(NL_{C/A})` and `Hⁱ(C(g)[-1]) ≅ H^{i-1}(C(g))`, which turn the
  long exact sequence below into a statement about the cohomology sheaves of the three naive
  cotangent complexes and about the target of the canonical map of Stacks 0E1Y.

## Main results

* `Stacks.SheafOfModules.naiveCotangentConeShortComplex_shortExact`: the sequence
  `0 ⟶ NL_{C/B} ⟶ C(g) ⟶ NL_{C/A}[1] ⟶ 0` is short exact, because it is split in every
  degree.
* `Stacks.SheafOfModules.naiveCotangentCone_homology_exact₁`,
  `Stacks.SheafOfModules.naiveCotangentCone_homology_exact₂` and
  `Stacks.SheafOfModules.naiveCotangentCone_homology_exact₃`: the three exactness statements of
  the long exact sequence of cohomology sheaves.
* `Stacks.SheafOfModules.naiveCotangentComplex_isZero_homology`: the naive cotangent complex has
  no cohomology outside degrees `-1` and `0`.  This is what truncates the long exact sequence to
  six terms.
* `Stacks.SheafOfModules.homologyMap_naiveCotangentConeMap_comp_pShift`: the map induced on
  cohomology sheaves by the canonical map of Stacks 0E1Y, composed with the projection of the
  shifted cone, is the map induced by `c₁`.
* `Stacks.SheafOfModules.naiveCotangentCone_homology_exact_target`,
  `Stacks.SheafOfModules.naiveCotangentCone_homology_exact_cone` and
  `Stacks.SheafOfModules.naiveCotangentCone_homology_exact_source`: **the long exact sequence
  `Hⁱ(NL_{C/A}) ⟶ Hⁱ(NL_{C/B}) --∂--> H^{i+1}(C(g)[-1]) ⟶ H^{i+1}(NL_{C/A}) ⟶ H^{i+1}(NL_{C/B})`
  of the cone**, in the three places the six-term sequence of Stacks 0E1Y consumes it: for
  `i = -1` the first is its exactness at `H^{-1}(NL_{C/B})` and the second its exactness at
  `H⁰(NL_{B/A} ⊗_B C)`, and the third is its exactness at `H⁰(NL_{C/A})` (`i = -1`) and at
  `H^{-1}(NL_{C/A})` (`i = -2`) — in each case read before the comparison of
  `H^j(NL_{B/A} ⊗_B C)` with `H^j(C(g)[-1])` along the canonical map.  The maps are the canonical
  ones, with no sign: see the section *The long exact sequence of the shifted cone* of
  `StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit`.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y)
* [Stacks Project, Tag 0111](https://stacks.math.columbia.edu/tag/0111), the long exact sequence
  of cohomology attached to a short exact sequence of complexes.
* [Stacks Project, Tag 014E](https://stacks.math.columbia.edu/tag/014E), the cone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules


variable {S : Type u} [Category.{v} S] (J : GrothendieckTopology S)
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-! ### The vanishing of the cohomology of the naive cotangent complex -/

/-- **The naive cotangent complex has no cohomology outside degrees `-1` and `0`**, because it
has no terms there.  This is what makes the exact sequence of Stacks 0E1Y six-term rather than
infinite. -/
theorem naiveCotangentComplex_isZero_homology (A B : Sheaf J CommRingCat.{max u v w})
    (a : A ⟶ B) (i : ℤ) (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((naiveCotangentComplex.{v, u, max u v w, max u v w} J A B a).homology i) :=
  (HomologicalComplex.ExactAt.of_isZero
    (naiveCotangentComplex_isZero_X.{v, u, max u v w, max u v w} J A B a i hneg
      hzero)).isZero_homology

variable (A B C : Sheaf J CommRingCat.{max u v w}) (a : A ⟶ B) (b : B ⟶ C)

/-! ### The degreewise split short exact sequence of the cone -/

/-- **The short complex `NL_{C/B} ⟶ C(g) ⟶ NL_{C/A}[1]`** attached to the canonical chain map
`g : NL_{C/A} ⟶ NL_{C/B}`: the short complex underlying the rotation of the cone triangle of
`g`.  Its first map is `CochainComplex.mappingCone.inr g` and its second map is
`(CochainComplex.mappingCone.triangle g).mor₃`. -/
noncomputable abbrev naiveCotangentConeShortComplex :
    ShortComplex (CochainComplex
      (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C)) ℤ) :=
  CochainComplex.mappingCone.triangleRotateShortComplex
    (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b)

/-- **The sequence `0 ⟶ NL_{C/B} ⟶ C(g) ⟶ NL_{C/A}[1] ⟶ 0` is short exact.**  In each degree
it is the split sequence `0 ⟶ NL_{C/B}ⁿ ⟶ NL_{C/B}ⁿ ⊕ NL_{C/A}ⁿ⁺¹ ⟶ NL_{C/A}ⁿ⁺¹ ⟶ 0` attached
to the biproduct decomposition of the cone. -/
theorem naiveCotangentConeShortComplex_shortExact :
    (naiveCotangentConeShortComplex.{v, u, w} J A B C a b).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    (CochainComplex.mappingCone.triangleRotateShortComplexSplitting
      (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) n).shortExact

/-! ### The long exact sequence of cohomology sheaves -/

/-- **The connecting morphism of the long exact sequence of the cone**,
`Hⁱ(NL_{C/A}[1]) ⟶ H^{i+1}(NL_{C/B})`.  Composed with the identification
`Hⁱ(NL_{C/A}[1]) ≅ H^{i+1}(NL_{C/A})` of `naiveCotangentShiftHomologyIso` it is, up to sign, the
map induced by `g` on cohomology sheaves; in the six-term sequence of Stacks 0E1Y it is the
place where the connecting arrow `H^{-1}(NL_{C/B}) ⟶ H⁰(NL_{B/A} ⊗_B C)` comes from. -/
noncomputable def naiveCotangentConeConnecting (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (naiveCotangentConeShortComplex.{v, u, w} J A B C a b).X₃.homology i ⟶
      (naiveCotangentConeShortComplex.{v, u, w} J A B C a b).X₁.homology j :=
  (naiveCotangentConeShortComplex_shortExact.{v, u, w} J A B C a b).δ i j hij

/-- **Exactness of `Hⁱ(NL_{C/A}[1]) ⟶ Hʲ(NL_{C/B}) ⟶ Hʲ(C(g))`** for `j = i + 1`. -/
theorem naiveCotangentCone_homology_exact₁ (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (ShortComplex.mk (naiveCotangentConeConnecting.{v, u, w} J A B C a b i j hij)
      (HomologicalComplex.homologyMap
        (naiveCotangentConeShortComplex.{v, u, w} J A B C a b).f j)
      (ShortComplex.ShortExact.δ_comp
        (naiveCotangentConeShortComplex_shortExact.{v, u, w} J A B C a b) i j hij)).Exact :=
  (naiveCotangentConeShortComplex_shortExact.{v, u, w} J A B C a b).homology_exact₁ i j hij

/-- **Exactness of `Hⁱ(NL_{C/B}) ⟶ Hⁱ(C(g)) ⟶ Hⁱ(NL_{C/A}[1])`.** -/
theorem naiveCotangentCone_homology_exact₂ (i : ℤ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (naiveCotangentConeShortComplex.{v, u, w} J A B C a b).f i)
      (HomologicalComplex.homologyMap
        (naiveCotangentConeShortComplex.{v, u, w} J A B C a b).g i)
      (by rw [← HomologicalComplex.homologyMap_comp,
        (naiveCotangentConeShortComplex.{v, u, w} J A B C a b).zero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (naiveCotangentConeShortComplex_shortExact.{v, u, w} J A B C a b).homology_exact₂ i

/-- **Exactness of `Hⁱ(C(g)) ⟶ Hⁱ(NL_{C/A}[1]) ⟶ Hʲ(NL_{C/B})`** for `j = i + 1`. -/
theorem naiveCotangentCone_homology_exact₃ (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (naiveCotangentConeShortComplex.{v, u, w} J A B C a b).g i)
      (naiveCotangentConeConnecting.{v, u, w} J A B C a b i j hij)
      (ShortComplex.ShortExact.comp_δ
        (naiveCotangentConeShortComplex_shortExact.{v, u, w} J A B C a b) i j hij)).Exact :=
  (naiveCotangentConeShortComplex_shortExact.{v, u, w} J A B C a b).homology_exact₃ i j hij

/-! ### Reading the shifted terms -/

/-- The identification `Hⁱ(NL_{C/A}[1]) ≅ H^{1+i}(NL_{C/A})` of the third term of the short
exact sequence of the cone with a cohomology sheaf of `NL_{C/A}`. -/
noncomputable def naiveCotangentShiftHomologyIso (i j : ℤ) (hij : 1 + i = j) :
    (naiveCotangentConeShortComplex.{v, u, w} J A B C a b).X₃.homology i ≅
      (naiveCotangentComplex.{v, u, max u v w, max u v w} J A C (a ≫ b)).homology j :=
  ((HomologicalComplex.homologyFunctor
      (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C))
      (ComplexShape.up ℤ) 0).shiftIso 1 i j hij).app
    (naiveCotangentComplex.{v, u, max u v w, max u v w} J A C (a ≫ b))

/-- The identification `Hⁱ(C(g)[-1]) ≅ H^{i-1}(C(g))` of a cohomology sheaf of the target of the
canonical map of Stacks 0E1Y with a cohomology sheaf of the cone, which is the middle term of
the short exact sequence above. -/
noncomputable def shiftedNaiveCotangentConeHomologyIso (i j : ℤ) (hij : -1 + i = j) :
    ((CategoryTheory.shiftFunctor (CochainComplex
          (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C)) ℤ)
          (-1 : ℤ)).obj
        (CochainComplex.mappingCone
          (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b))).homology i ≅
      (naiveCotangentConeShortComplex.{v, u, w} J A B C a b).X₂.homology j :=
  ((HomologicalComplex.homologyFunctor
      (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C))
      (ComplexShape.up ℤ) 0).shiftIso (-1) i j hij).app
    (CochainComplex.mappingCone (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b))

/-! ### The cone sequence read along the canonical map of Stacks 0E1Y

The canonical map `c : NL_{B/A} ⊗_B C ⟶ C(g)[-1]` of Stacks 0E1Y satisfies `c ≫ pShift g = c₁`,
so on cohomology sheaves it factors the map induced by `c₁`.  Reading the long exact sequence of
the cone through `CochainComplex.homologyMap_pShift`, which identifies the map induced by
`pShift g` with the one induced by the third morphism of the cone triangle, turns the three
exactness statements above into statements about `Hⁱ(c₁)`, `Hⁱ(g)` and the connecting morphism
`CochainComplex.coneHomologyConnecting`, whose target `H^{i+1}(C(g)[-1])` is the source of the
six-term sequence's `H⁰(NL_{B/A} ⊗_B C)` once `H⁰(c)` is known to be an isomorphism. -/

/-- **The canonical map of Stacks 0E1Y on cohomology sheaves, composed with the projection of
the shifted cone**, is the map induced by `c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}`. -/
theorem homologyMap_naiveCotangentConeMap_comp_pShift (i : ℤ) :
    HomologicalComplex.homologyMap (naiveCotangentConeMap.{v, u, w} J A B C a b) i ≫
        HomologicalComplex.homologyMap
          (pShift (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b)) i =
      HomologicalComplex.homologyMap
        (baseChangeNaiveCotangentMap.{v, u, w} J A B C a b) i := by
  rw [← HomologicalComplex.homologyMap_comp,
    naiveCotangentConeMap_comp_pShift.{v, u, w} J A B C a b]

/-- **The connecting morphism `Hⁱ(NL_{C/B}) ⟶ H^{i+1}(C(g)[-1])`** of the cone of
`g : NL_{C/A} ⟶ NL_{C/B}`.  For `i = -1` its target is, through `H⁰(c)`, the term
`H⁰(NL_{B/A} ⊗_B C)` of the six-term exact sequence of Stacks 0E1Y, so this is the connecting
arrow of that sequence read before the comparison. -/
noncomputable def naiveCotangentConeHomologyConnecting (i j : ℤ) (hij : -1 + j = i) :
    (naiveCotangentComplex.{v, u, max u v w, max u v w} J B C b).homology i ⟶
      ((CategoryTheory.shiftFunctor (CochainComplex
            (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C)) ℤ)
            (-1 : ℤ)).obj
          (CochainComplex.mappingCone
            (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b))).homology j :=
  CochainComplex.coneHomologyConnecting
    (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) i j hij

/-- **Exactness of `Hⁱ(NL_{C/A}) ⟶ Hⁱ(NL_{C/B}) --∂--> H^{i+1}(C(g)[-1])`.**  For `i = -1` this
is the exactness of the six-term sequence of Stacks 0E1Y at `H^{-1}(NL_{C/B})`, read before the
comparison of `H⁰(NL_{B/A} ⊗_B C)` with `H⁰(C(g)[-1])` along the canonical map. -/
theorem naiveCotangentCone_homology_exact_target (i j : ℤ) (hij : -1 + j = i) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) i)
      (naiveCotangentConeHomologyConnecting.{v, u, w} J A B C a b i j hij)
      (CochainComplex.homologyMap_comp_coneHomologyConnecting
        (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) i j hij)).Exact :=
  CochainComplex.mappingCone_homology_exact_target
    (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) i j hij

/-- **Exactness of `Hⁱ(NL_{C/B}) --∂--> Hʲ(C(g)[-1]) ⟶ Hʲ(NL_{C/A})`.**  For `i = -1`, so
`j = 0`, this is the exactness of the six-term sequence of Stacks 0E1Y at
`H⁰(NL_{B/A} ⊗_B C)`, read before the comparison of that term with `H⁰(C(g)[-1])` along the
canonical map. -/
theorem naiveCotangentCone_homology_exact_cone (i j : ℤ) (hij : -1 + j = i) :
    (ShortComplex.mk
      (naiveCotangentConeHomologyConnecting.{v, u, w} J A B C a b i j hij)
      (HomologicalComplex.homologyMap
        (pShift (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b)) j)
      (CochainComplex.coneHomologyConnecting_comp_homologyMap_pShift
        (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) i j hij)).Exact :=
  CochainComplex.mappingCone_homology_exact_cone
    (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) i j hij

/-- **Exactness of `Hʲ(C(g)[-1]) ⟶ Hʲ(NL_{C/A}) ⟶ Hʲ(NL_{C/B})`.**  For `j = 0` this is the
exactness of the six-term sequence of Stacks 0E1Y at `H⁰(NL_{C/A})` and for `j = -1` its
exactness at `H^{-1}(NL_{C/A})`, in both cases read before the comparison of
`H^j(NL_{B/A} ⊗_B C)` with `H^j(C(g)[-1])` along the canonical map. -/
theorem naiveCotangentCone_homology_exact_source (i j : ℤ) (hij : -1 + j = i) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (pShift (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b)) j)
      (HomologicalComplex.homologyMap
        (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) j)
      (CochainComplex.homologyMap_pShift_comp_homologyMap
        (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) i j hij)).Exact :=
  CochainComplex.mappingCone_homology_exact_source
    (relativeNaiveCotangentComplexMap.{v, u, w} J A B C a b) i j hij

end Stacks.SheafOfModules

end
