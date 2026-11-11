module

public import StacksFrontier.Cotangent.EtaleVanishingUnconditional
public import StacksFrontier.Cotangent.SmoothRingMap
public import StacksFrontier.Cotangent.SmoothVanishing

/-!
# Lemma 08R5 for a smooth ring map

`StacksFrontier.Cotangent.SmoothRingMap` and `StacksFrontier.Cotangent.SmoothVanishing` prove the
statement of [Stacks, Tag 08R5] for distinguished triangles on the vertices of the display
92.7.0.1 taken as parameters: two named ones for a chart `A → P → B`, and the quantified forms
`CommAlgCat.HasFundamentalTriangles` and `CommAlgCat.HasFundamentalTriangle`, where the towers
are built inside the proof. Those files are upstream of Proposition 08QX,
`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`. This file proves both predicates from
Proposition 08QX and states the lemma under exactly the source's hypotheses.

## Main results

* `CommAlgCat.hasFundamentalTriangles` and `CommAlgCat.hasFundamentalTriangle`: Proposition 08QX
  in the two quantified shapes the files above take it in.
* `CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional`:
  **[Stacks, Tag 08R5]**: for a smooth ring map `A → B`, the isomorphism
  `L_{B/A} ≅ Ω[B⁄A][0]` in `D(B)`, with
  `CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_smooth_unconditional`
  its existence form, the covering declaration of the section **[Stacks, Tag 08R4]**.
* `CommAlgCat.isZero_homology_cotangentComplex_of_smooth_unconditional`: the vanishing of the
  cohomology of `L_{B/A}` outside degree `0` for a smooth ring map.
* `CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale_unconditional`
  and
  `nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth_unconditional`
  in `CommAlgCat`:
  the same isomorphism for a chart `A → P → B` and for a standard smooth ring map.

## References

* [Stacks Project, Tag 08R4](https://stacks.math.columbia.edu/tag/08R4)
* [Stacks Project, Tag 08R5](https://stacks.math.columbia.edu/tag/08R5)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX), the fundamental
  triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CommAlgCat

attribute [local instance] diagonalAlgebra

/-- **Proposition 08QX, in the shape `CommAlgCat.HasFundamentalTriangles`.** Every tower of
rings in one universe has a distinguished triangle on the three vertices of the display of
Equation 92.7.0.1: this is `CommAlgCat.productFundamentalTriangle_distinguished`. -/
theorem hasFundamentalTriangles : HasFundamentalTriangles.{u} := by
  intro R _ S _ T _ _ _ _ _
  exact exists_distTriang_fundamentalVertex.{u} R S T

/-- **Proposition 08QX, in the shape `CommAlgCat.HasFundamentalTriangle`.** Every tower of
rings in one universe has a distinguished triangle on the three vertices of the display of
Equation 92.7.0.1: this is `CommAlgCat.productFundamentalTriangle_distinguished`. -/
theorem hasFundamentalTriangle : HasFundamentalTriangle.{u} := by
  intro A B C _ _ _ _ _ _ _
  exact exists_distTriang_fundamentalVertex.{u} A B C

section Chart

variable (A : Type u) [CommRing A] (P : Type u) [CommRing P] [Algebra A P]
  (B : Type u) [CommRing B] [Algebra A B] [Algebra P B] [IsScalarTower A P B]

/-- **The cotangent complex of a chart.** Let `A → P → B` be ring maps with `P` a polynomial
algebra over `A` and `P → B` étale. Then `L_{B/A} = Ω[B⁄A][0]` in `D(B)`.

This is `CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale` at the
fundamental triangles of the towers `A → P → B` and `B → B ⊗_P B → B` that Proposition 08QX
provides. The smooth case, [Stacks, Tag 08R5], is
`CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional`. -/
theorem nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale_unconditional
    (hP : Algebra.IsPolynomialAlgebra A P) [Algebra.Etale P B] :
    Nonempty
      (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
          (ModuleCat.of B (KaehlerDifferential A B))) := by
  have := isScalarTower_diagonalAlgebra P B
  obtain ⟨_, _, _, hT⟩ := exists_distTriang_fundamentalVertex.{u} A P B
  obtain ⟨_, _, _, hT'⟩ := exists_distTriang_fundamentalVertex.{u} B (B ⊗[P] B) B
  exact nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale A P B hP hT hT'

end Chart

section StandardSmooth

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

/-- **The cotangent complex of a standard smooth ring map.** For `A → B` standard smooth,
`L_{B/A} = Ω[B⁄A][0]` in `D(B)`. This is
`CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth` with
Proposition 08QX supplied by `CommAlgCat.hasFundamentalTriangles`. The smooth case,
[Stacks, Tag 08R5], is
`CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional`. -/
theorem nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth_unconditional
    [Algebra.IsStandardSmooth A B] :
    Nonempty
      (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
          (ModuleCat.of B (KaehlerDifferential A B))) :=
  nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth A B
    hasFundamentalTriangles

end StandardSmooth

section Smooth

/-- **The cohomology of `L_{B/A}` for a smooth ring map.** For a smooth ring map `A → B`,
`Hⁱ(L_{B/A}) = 0` for `i ≠ 0`. This is `CommAlgCat.isZero_homology_cotangentComplex_of_smooth`
with Proposition 08QX supplied by `CommAlgCat.hasFundamentalTriangle`; together with Tag 08QF it
gives [Stacks, Tag 08R5], which is
`CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional`. -/
theorem isZero_homology_cotangentComplex_of_smooth_unconditional
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((cotangentComplex A (CommAlgCat.of A B)).homology i) :=
  isZero_homology_cotangentComplex_of_smooth hasFundamentalTriangle A B i hi

/-- **[Stacks, Tag 08R5].** For a smooth ring map `A → B`, the identification
`L_{B/A} ≅ Ω[B⁄A][0]` in `D(B)` of the cotangent complex with the module of Kähler
differentials placed in cohomological degree `0`. This is
`CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmooth` with Proposition 08QX
supplied by `CommAlgCat.hasFundamentalTriangle`. -/
@[stacks 08R5 "the lemma in full and as data: for a SMOOTH ring map `A → B` \
(`Algebra.Smooth A B`, formally smooth and of finite presentation, as in Stacks), \
the isomorphism `L_{B/A} ≅ Ω[B⁄A][0]` in `D(B)`. No hypothesis beyond smoothness: \
the fundamental triangle used along the proof is Tag 08QX, \
`CommAlgCat.productFundamentalTriangle_distinguished`, and the reduction to the standard smooth \
case is Lemma 00TA through `Algebra.Smooth.exists_span_eq_top_isStandardSmooth` with the \
localization step of Lemma 08R3, as in the source's proof"]
noncomputable def cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Algebra.Smooth A B] :
    cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        (ModuleCat.of B (KaehlerDifferential A B)) :=
  cotangentComplexDerivedIsoKaehlerDifferentialOfSmooth hasFundamentalTriangle A B

/-- **[Stacks, Tag 08R5]**, in existence form: for a smooth ring map `A → B`,
`L_{B/A} = Ω[B⁄A][0]` in `D(B)`. This is also the covering declaration of the section
**[Stacks, Tag 08R4]**, whose one result is Lemma 08R5. -/
@[stacks 08R4 "the SECTION tag `\\section{Smooth ring maps}`, covered by its lemma 08R5, stated \
here in full. The remark opening the section introduces `weakly quasi-regular` surjections \
`C → B` (kernel `I` with `I/I²` flat over `B` and `Tor_*^C(B, B)` the exterior algebra on \
`I/I²`) to say what a generalization of Lemma 08R2 from étale to smooth maps would look at; \
the source then says `For the moment we just stick to smooth ring maps`, so that remark states \
no result and introduces nothing the section uses"]
theorem nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_smooth_unconditional
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Algebra.Smooth A B] :
    Nonempty (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        (ModuleCat.of B (KaehlerDifferential A B))) :=
  ⟨cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional A B⟩

end Smooth

end CommAlgCat

end
