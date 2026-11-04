module

public import StacksFrontier.Cotangent.EtaleVanishingUnconditional
public import StacksFrontier.Cotangent.SmoothRingMap
public import StacksFrontier.Cotangent.SmoothVanishing

/-!
# Lemma 08R5 with the fundamental triangles supplied

`StacksFrontier.Cotangent.SmoothRingMap` and `StacksFrontier.Cotangent.SmoothVanishing` prove
[Stacks, Tag 08R5] (and cover the section tag 08R4) for distinguished triangles on the vertices
of the display 92.7.0.1 taken as parameters: two named ones for a chart `A → P → B`, and the
whole of Proposition 08QX, as `CommAlgCat.HasFundamentalTriangles` and
`CommAlgCat.HasFundamentalTriangle`, where the towers are built inside the proof. Those files
are upstream of Proposition 08QX. This file proves both predicates from Proposition 08QX,
`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier.Cotangent.Triangle.ProductDescent`, and states the lemma under exactly the source's
hypotheses.

## Main results

* `CommAlgCat.hasFundamentalTriangles` and `CommAlgCat.hasFundamentalTriangle`: Proposition 08QX
  in the two quantified shapes the files above take it in.
* `CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale_unconditional`:
  **[Stacks, Tag 08R5]** for a chart `A → P → B`.
* `nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth_unconditional`
  in `CommAlgCat`: **[Stacks, Tag 08R5]** for a standard smooth ring map, covering the section tag
  **[Stacks, Tag 08R4]**.
* `CommAlgCat.isZero_homology_cotangentComplex_of_smooth_unconditional` and
  `CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional`:
  **[Stacks, Tag 08R5]** for a smooth ring map, as the vanishing of the cohomology outside
  degree `0` and as the isomorphism `L_{B/A} ≅ Ω[B⁄A][0]` in `D(B)`.

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

/-- **Stacks Project, Tag 08R5**, for a chart. Let `A → P → B` be ring maps with `P` a
polynomial algebra over `A` and `P → B` étale. Then `L_{B/A} = Ω[B⁄A][0]` in `D(B)`.

This is `CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_etale` at the
fundamental triangles of the towers `A → P → B` and `B → B ⊗_P B → B` that Proposition 08QX
provides. -/
@[stacks 08R5 "the lemma for a ring map `A → B` presented by a CHART: a factorization \
`A → P → B` with `P` a polynomial algebra over `A` and `P → B` étale. NOTHING is carried: the \
fundamental triangles of `A → P → B` and of `B → B ⊗_P B → B` are both Proposition 08QX, \
`CommAlgCat.productFundamentalTriangle_distinguished`. The conclusion is the source's, \
`L_{B/A} = Ω_{B/A}[0]`, read as an isomorphism in `D(B)` in the same spelling as Tag 08QH; \
the full smooth case is \
`CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional`"]
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

/-- **Stacks Project, Tag 08R5** for a standard smooth ring map, and the covering declaration
for the section tag **08R4**. This is
`CommAlgCat.nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_isStandardSmooth` with
Proposition 08QX supplied by `CommAlgCat.hasFundamentalTriangles`. -/
@[stacks 08R4 "the SECTION tag `\\section{Smooth ring maps}`; its lemma is 08R5", stacks 08R5 "\
the lemma for a STANDARD SMOOTH ring map, `Algebra.IsStandardSmooth A B`. The chart \
`A → A[x_1, …, x_n] → B` with étale second map is BUILT, not assumed — it is Mathlib's \
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`, which is the content of the source's \
appeal to Algebra, Lemma 00TA. NOTHING is carried: the towers the fundamental triangle is \
needed for are built inside the proof and Proposition 08QX, \
`CommAlgCat.productFundamentalTriangle_distinguished`, holds at each of them. The full smooth \
case is `CommAlgCat.cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional`. The \
conclusion is the source's, `L_{B/A} = Ω_{B/A}[0]`, read as an isomorphism in `D(B)` in the \
same spelling as Tag 08QH. As for 08R4: the section's only mathematical content is Lemma 08R5, \
so this declaration covers it; the definitional remark opening the section introduces `weakly \
quasi-regular` ring maps only to say what a generalization of Lemma 08R2 would look at, and the \
source then says `For the moment we just stick to smooth ring maps`, so it states no result and \
nothing is defined for it"]
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

/-- **[Stacks, Tag 08R5], the vanishing.** For a smooth ring map `A → B`, `Hⁱ(L_{B/A}) = 0` for
`i ≠ 0`. This is `CommAlgCat.isZero_homology_cotangentComplex_of_smooth` with Proposition 08QX
supplied by `CommAlgCat.hasFundamentalTriangle`. -/
@[stacks 08R5 "the vanishing: `Hⁱ(L_{B/A}) = 0` for every `i ≠ 0`, which together with Tag \
08QF in degree 0 is the lemma. NOTHING is carried: the fundamental triangle is Tag 08QX, \
`CommAlgCat.productFundamentalTriangle_distinguished`, applied at each of the towers the proof \
produces"]
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
@[stacks 08R5 "the lemma in full and as data: the isomorphism `L_{B/A} ≅ Ω[B⁄A][0]` in `D(B)`, \
for a SMOOTH ring map and with NOTHING carried — the fundamental triangle is Tag 08QX, \
`CommAlgCat.productFundamentalTriangle_distinguished`. Nothing beyond smoothness is assumed, \
and the conclusion is the source's whole equality rather than only its degree 0 part"]
noncomputable def cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Algebra.Smooth A B] :
    cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        (ModuleCat.of B (KaehlerDifferential A B)) :=
  cotangentComplexDerivedIsoKaehlerDifferentialOfSmooth hasFundamentalTriangle A B

/-- **[Stacks, Tag 08R5]**, in existence form: for a smooth ring map `A → B`,
`L_{B/A} = Ω[B⁄A][0]` in `D(B)`. -/
theorem nonempty_cotangentComplexDerived_iso_kaehlerDifferential_of_smooth_unconditional
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Algebra.Smooth A B] :
    Nonempty (cotangentComplexDerived.{u, u} A (CommAlgCat.of A B) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        (ModuleCat.of B (KaehlerDifferential A B))) :=
  ⟨cotangentComplexDerivedIsoKaehlerDifferentialOfSmoothUnconditional A B⟩

end Smooth

end CommAlgCat

end
