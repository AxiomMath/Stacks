module

public import StacksFrontier.AlgebraicGeometry.Conormal.ChartGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ConormalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexVanishingDifferential
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedAlgebra

/-!
# Chart-local comparison of conormal algebras from a comparison of associated graded algebras

Let `i : Z ⟶ X` and `i' : Z ⟶ X'` be immersions with the same source, let `V` and `V'` be affine
opens of `X` and `X'` over which `i` and `i'` restrict to closed immersions, and suppose the two
preimages agree, `i' ⁻¹ᵁ V' = i ⁻¹ᵁ V`. On that open the two conormal algebras of Stacks 0630 are
described by the associated graded algebras of the two kernel ideals, by Stacks 0633 — this is
`AlgebraicGeometry.affineSectionsEquiv`.

This file transports a comparison of those two *algebraic* associated graded algebras to a
comparison of the *geometric* conormal algebras on that chart, in the shape the gluing pipeline
`Stacks.Conormal.gradedAlgebraIsoOfChartIso` consumes: a family of isomorphisms of the sections
of the degree `n` pieces, one for every `n : ℤ`, multiplicative and unital on that chart. The
comparison of associated graded algebras that Stacks 0CAY produces,
`Stacks.ConormalApproximation.exists_finiteType_coefficients_associatedGraded_equiv`, is of
exactly this kind.

Nothing here is about a basis: one chart is treated, and a family of charts covering `Z` on
which the hypotheses hold is the caller's to supply.

## Main definitions

* `Stacks.Conormal.ChartAssociatedGradedEquiv`: a comparison of the associated graded algebras of
  the two kernel ideals on the chart — a degreewise additive equivalence which is linear over the
  functions of the source chart, multiplicative for `AssociatedGraded.homogeneousMul` and unital.
* `Stacks.Conormal.chartSectionsAddEquiv`: the resulting additive comparison of the sections of
  the degree `n` pieces of the two conormal algebras, for `n : ℕ`.
* `Stacks.Conormal.chartSectionsIso`: the same as an isomorphism of modules over the functions of
  the chart, and `Stacks.Conormal.chartSectionsIsoInt` its extension to every integer degree.
* `Stacks.Conormal.IsChartRestriction`: the condition that the comparison on a pair of charts
  contained in another pair *in both ambients* is the restriction of the comparison on the larger
  pair, stated on representatives.
* `Stacks.Conormal.ChartQuotientPresentation`: an identification of the chart ring with a concrete
  quotient `A ⧸ R` of an ambient ring carrying the kernel ideal to the ideal that `J` generates —
  the data about the particular immersion that an `AssociatedGraded.GradedAlgEquiv` over `A` needs
  in order to be read as a `ChartAssociatedGradedEquiv`.
* `Stacks.Conormal.quotientPresentationPieceEquiv`: the degreewise comparison such a pair of
  presentations and such a `GradedAlgEquiv` determine.
* `Stacks.Conormal.ChartQuotientPresentationHom`: a comparison of the presentations of two nested
  pairs of charts — a ring map of the two ambient rings compatible with both presentations, with
  `Stacks.Conormal.ChartQuotientPresentationHom.refl` the check that the data is available.

## Main results

* `Stacks.Conormal.chartSectionsAddEquiv_smul`: **the comparison of sections is linear over the
  functions on the chart**, not merely over those of the ambient chart. This is what makes it an
  isomorphism of modules, and it is where the surjectivity of the map on functions of a closed
  immersion is used.
* `Stacks.Conormal.chartSectionsAddEquiv_mul` and `Stacks.Conormal.chartSectionsAddEquiv_one`:
  it is multiplicative and unital.
* `Stacks.Conormal.chartSectionsIsoInt_mul` and `Stacks.Conormal.chartSectionsIsoInt_one`: the
  same in every integer degree, which is the form
  `Stacks.BasisRestriction.IsMultiplicativeOnBasis` takes at one member of a basis.
* `Stacks.Conormal.chartSectionsAddEquiv_restrict` and
  `Stacks.Conormal.chartSectionsIsoInt_restrict`: **the comparison of sections commutes with the
  restriction to a smaller pair of charts**, as soon as the two algebraic comparisons do. This is
  the form `Stacks.BasisRestriction.IsCompatibleOnBasis` takes between two nested members of a
  basis, and `Stacks.Conormal.isChartRestriction_refl` is the check that its hypothesis is
  satisfiable.
* `Stacks.Conormal.ChartAssociatedGradedEquiv.ofQuotientPresentation`: **a comparison of the
  associated graded algebras of two concrete quotients of one ambient ring is a chart-local
  comparison**, given a presentation of each chart ring as one of those quotients and the
  compatibility that the two presentations present the same source chart. This is what closes the
  gap between `AssociatedGraded.GradedAlgEquiv.quotientPieceEquiv` and
  `ChartAssociatedGradedEquiv`.
* `Stacks.Conormal.quotientPresentationPieceEquiv_mk_of_lift`: **the comparison on
  representatives**, when the comparison of associated graded algebras is induced by the identity
  of the ambient ring: lift a representative to the ambient ring and read it off on the other
  side.
* `Stacks.Conormal.isChartRestriction_ofQuotientPresentation`: **the comparisons built from two
  compared presentations satisfy the restriction condition**, which is what a family of them needs
  in order to glue.

## Implementation notes

The three ingredients are combined as stated, with two conversions.

The multiplication of the associated graded algebra of `Stacks.Conormal.chartIdeal` that
`AlgebraicGeometry.AffineSectionsEquiv` is stated with is
`AssociatedGraded.homogeneousSMul`, the action of `Gr_I(A)` on itself, whereas
`AssociatedGraded.GradedAlgEquiv` is stated with the internal multiplication
`AssociatedGraded.homogeneousMul`. For `M = A` these are the same operation, by
`AssociatedGraded.homogeneousMul_eq_homogeneousSMul`.

The comparison of associated graded algebras asked for by `ChartAssociatedGradedEquiv` is the
associated graded algebra of each ambient chart *ring* for its own kernel ideal, which is what the
chart-local description of the conormal algebra is stated with. A comparison in the shape
`AssociatedGraded.GradedAlgEquiv J (A ⧸ R) (A ⧸ R')`, with the filtration taken over an ambient
ring `A` of which the two chart rings are quotients — the shape Stacks 07VF and hence Stacks 0CAY
produce — is read in that form by `AssociatedGraded.GradedAlgEquiv.quotientPieceEquiv`, whose
scalar law `quotientPieceEquiv_smul_mk` supplies the `map_smul` field for any pair of chart
functions lifting to a common element of `A`. The identification of the chart ring with that
quotient, which is data about the particular immersion, is
`Stacks.Conormal.ChartQuotientPresentation`, and
`Stacks.Conormal.ChartAssociatedGradedEquiv.ofQuotientPresentation` performs the conversion. It
transports the pieces along the presentation by
`AssociatedGraded.pieceEquivOfRingEquiv`, whose semilinearity carries the action of a chart
function to the action of its image in the quotient, and reads the `map_smul` field off
`quotientPieceEquiv_smul_mk` for a common lift: the lift of a chart function on the one side need
not be *the* lift on the other, but the two differ by an element of the kernel ideal, which
annihilates every homogeneous class by `AssociatedGraded.smul_eq_zero_of_mem`.

The equality of the two preimages is carried by `AddEquiv.cast`, and passed through the scalar
action, the graded multiplication and the unit by `Stacks.Conormal.sectionSmul_cast`,
`Stacks.Conormal.gradedMul_cast` and `Stacks.Conormal.gradedOne_cast`.

`ChartAssociatedGradedEquiv` is data on *one* pair of charts, and its fields say nothing about
any other pair; compatibility of a family of such comparisons with restriction is therefore a
condition on the family, `Stacks.Conormal.IsChartRestriction`, and not a consequence of the
fields. It is stated on representatives, which is the only shape available: the chart-local
presentations of the conormal algebra restrict along a containment of the charts *in the ambient
schemes*, by `Stacks.Conormal.ConormalAlgebraData.localMap_naturality`, and a containment of the
opens they cut out in the source gives no map between the associated graded algebras at all.

The extension from `ℕ` to `ℤ` is by pattern matching on the integer, so that the nonnegative case
is the degree already constructed with no transport at all; in a negative degree both conormal
algebras are zero, by the `negative_isZero` field of Stacks 0630, so every section vanishes and
the two sides are isomorphic for that reason. Multiplicativity in a degree with a negative factor
holds because one of the two arguments is then zero.

## References

* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v w

namespace Stacks.Conormal

variable {Z X X' : Scheme.{u}}

/-- **A chart-local comparison of the associated graded algebras of two immersions with a common
source.** The data is a degreewise additive equivalence between the associated graded algebras of
the two kernel ideals on the two ambient charts, linear over any pair of ambient functions with
the same image on the common source chart, multiplicative, and carrying the unit to the unit. -/
structure ChartAssociatedGradedEquiv (i : Z ⟶ X) (i' : Z ⟶ X') [IsImmersion i] [IsImmersion i']
    (V : X.affineOpens) (V' : X'.affineOpens) (hpre : i' ⁻¹ᵁ V'.1 = i ⁻¹ᵁ V.1) where
  /-- The comparison in each nonnegative degree. -/
  equiv (n : ℕ) :
    AssociatedGraded.piece (M := Γ(X, V)) (chartIdeal i V) n ≃+
      AssociatedGraded.piece (M := Γ(X', V')) (chartIdeal i' V') n
  /-- It is linear over any two functions on the ambient charts with the same image on the common
  source chart. -/
  map_smul (n : ℕ) (r : Γ(X, V)) (r' : Γ(X', V'))
      (hr : (AddEquiv.cast (M := fun T : Z.Opens => Γ(Z, T)) hpre) ((i'.app V').hom r') =
        (i.app V).hom r)
      (x : AssociatedGraded.piece (M := Γ(X, V)) (chartIdeal i V) n) :
    equiv n (r • x) = r' • equiv n x
  /-- It is multiplicative. -/
  map_homogeneousMul (n m : ℕ)
      (x : AssociatedGraded.piece (M := Γ(X, V)) (chartIdeal i V) n)
      (y : AssociatedGraded.piece (M := Γ(X, V)) (chartIdeal i V) m) :
    equiv (n + m) (AssociatedGraded.homogeneousMul (chartIdeal i V) x y) =
      AssociatedGraded.homogeneousMul (chartIdeal i' V') (equiv n x) (equiv m y)
  /-- It carries the unit to the unit. -/
  map_homogeneousOne :
    equiv 0 (AssociatedGraded.homogeneousOne (M := Γ(X, V)) (chartIdeal i V)) =
      AssociatedGraded.homogeneousOne (M := Γ(X', V')) (chartIdeal i' V')

/-- **The identity is a chart-local comparison**, of the chart data of one immersion with itself.
The scalar law holds because two functions on the ambient chart with the same image on the source
chart differ by an element of the kernel ideal, and that ideal annihilates every homogeneous
class by `AssociatedGraded.smul_eq_zero_of_mem`. -/
def ChartAssociatedGradedEquiv.refl (i : Z ⟶ X) [IsImmersion i] (V : X.affineOpens) :
    ChartAssociatedGradedEquiv i i V V rfl where
  equiv _ := AddEquiv.refl _
  map_smul n r r' hr x := by
    have hr' : (i.app V).hom r' = (i.app V).hom r := hr
    have hker : r - r' ∈ chartIdeal i V := by
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact hr'.symm
    have h := AssociatedGraded.smul_eq_zero_of_mem (chartIdeal i V) n hker x
    rw [sub_smul, sub_eq_zero] at h
    exact h
  map_homogeneousMul _ _ _ _ := rfl
  map_homogeneousOne := rfl

/-! ### The chart ring as a concrete quotient

The shape in which Stacks 07VF, and hence Stacks 0CAY, produces a comparison of associated graded
algebras is an `AssociatedGraded.GradedAlgEquiv J (A ⧸ R) (A ⧸ R')`: the two rings compared are
two *concrete* quotients of one ambient ring `A`, and the filtration is by the powers of an ideal
`J` of `A`. A `ChartAssociatedGradedEquiv` instead compares the associated graded algebras of the
two chart rings `Γ(X, V)` and `Γ(X', V')` for their own kernel ideals. What converts the one into
the other is the identification of each chart ring with its quotient — for the immersions Stacks
0CAY is about, that `Γ(X, V) = B ⊗_{C,σ} D` is the quotient of `A = D[x_1, …, x_n]` by the module
of relations, and that the kernel ideal of the fibre on that chart is the one `I ⊆ D` generates
there. That is data about the particular immersion, carried by
`Stacks.Conormal.ChartQuotientPresentation`, and the conversion is
`Stacks.Conormal.ChartAssociatedGradedEquiv.ofQuotientPresentation`. -/

/-- **A presentation of the chart ring of an immersion as a concrete quotient.** The data is a
ring isomorphism of the functions on the ambient chart `V` with a quotient `A ⧸ R` of an ambient
ring, carrying the kernel ideal of the immersion on that chart to the ideal that `J` generates in
`A ⧸ R`. For the immersions of Stacks 0CAY this is the statement that the chart is
`Spec(B ⊗_{C,σ} D)`, a quotient of `A = D[x_1, …, x_n]`, and that the fibre is cut out in it by
the ideal `I ⊆ D` generates. -/
structure ChartQuotientPresentation (i : Z ⟶ X) (V : X.affineOpens)
    {A : Type v} [CommRing A] (J R : Ideal A) where
  /-- The identification of the chart ring with the quotient. -/
  equiv : Γ(X, V) ≃+* A ⧸ R
  /-- It carries the kernel ideal of the immersion on the chart to the ideal `J` generates in the
  quotient. -/
  map_chartIdeal :
    (chartIdeal i V).map (equiv : Γ(X, V) →+* A ⧸ R) = J.map (Ideal.Quotient.mk R)

/-- **Every chart ring presents itself**, with the ambient ring the chart ring, the ideal `R` zero
and `J` the kernel ideal. The trivial presentation; it is what shows the data of a
`ChartQuotientPresentation` is available at all. -/
def ChartQuotientPresentation.self (i : Z ⟶ X) (V : X.affineOpens) :
    ChartQuotientPresentation i V (chartIdeal i V) (⊥ : Ideal Γ(X, V)) where
  equiv := (RingEquiv.quotientBot Γ(X, V)).symm
  map_chartIdeal := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)
      (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)
    · exact Ideal.mem_map_of_mem _ hx
    · exact Ideal.mem_map_of_mem _ hx

/-- **The map to the functions on the source chart that a presentation defines**: reduce modulo
`R`, identify with the functions on the ambient chart, restrict to the source. Two presentations,
over the same ambient ring, present the *same* source chart exactly when these two maps agree,
which is the compatibility
`Stacks.Conormal.ChartAssociatedGradedEquiv.ofQuotientPresentation` asks for. -/
def ChartQuotientPresentation.toSourceHom {i : Z ⟶ X} {V : X.affineOpens}
    {A : Type v} [CommRing A] {J R : Ideal A} (p : ChartQuotientPresentation i V J R) :
    A →+* Γ(Z, i ⁻¹ᵁ V.1) :=
  (i.app V).hom.comp ((p.equiv.symm : (A ⧸ R) →+* Γ(X, V)).comp (Ideal.Quotient.mk R))

/-- The map `ChartQuotientPresentation.toSourceHom` sends `a` to the pullback along `i` to the
source chart of the function corresponding to the class of `a` modulo `R`. -/
@[simp]
theorem ChartQuotientPresentation.toSourceHom_apply {i : Z ⟶ X} {V : X.affineOpens}
    {A : Type v} [CommRing A] {J R : Ideal A} (p : ChartQuotientPresentation i V J R) (a : A) :
    p.toSourceHom a = (i.app V).hom (p.equiv.symm (Ideal.Quotient.mk R a)) :=
  rfl

/-- A presentation carries the `n`-th term of the filtration of the chart ring by the kernel
ideal into the `n`-th term of the `J`-adic filtration of the quotient taken over the ambient
ring. -/
theorem ChartQuotientPresentation.equiv_mem_power {i : Z ⟶ X} {V : X.affineOpens}
    {A : Type v} [CommRing A] {J R : Ideal A} (p : ChartQuotientPresentation i V J R) (n : ℕ)
    {x : Γ(X, V)} (hx : x ∈ AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) n) :
    p.equiv x ∈ AssociatedGraded.power (M := A ⧸ R) J n :=
  (AssociatedGraded.mem_power_map_iff J R n).1
    (AssociatedGraded.map_mem_power_of_map_le (p.equiv : Γ(X, V) →+* A ⧸ R)
      p.map_chartIdeal.le n hx)

/-- The inverse of a presentation carries the `n`-th term of the `J`-adic filtration of the
quotient back into the `n`-th term of the filtration of the chart ring by the kernel ideal. -/
theorem ChartQuotientPresentation.symm_mem_power {i : Z ⟶ X} {V : X.affineOpens}
    {A : Type v} [CommRing A] {J R : Ideal A} (p : ChartQuotientPresentation i V J R) (n : ℕ)
    {y : A ⧸ R} (hy : y ∈ AssociatedGraded.power (M := A ⧸ R) J n) :
    p.equiv.symm y ∈ AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) n :=
  AssociatedGraded.map_mem_power_of_map_le (p.equiv.symm : (A ⧸ R) →+* Γ(X, V))
    (AssociatedGraded.map_symm_eq_of_map_eq p.equiv p.map_chartIdeal).le n
    ((AssociatedGraded.mem_power_map_iff J R n).2 hy)

/-- **Every representative of the filtration of the chart ring lifts to the ambient ring**: a
function in `I(V)ⁿ` is, under the presentation, the class of an element of `Jⁿ`. -/
theorem ChartQuotientPresentation.exists_lift {i : Z ⟶ X} {V : X.affineOpens}
    {A : Type v} [CommRing A] {J R : Ideal A} (p : ChartQuotientPresentation i V J R) (n : ℕ)
    (a : AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) n) :
    ∃ z : AssociatedGraded.power (M := A) J n,
      Ideal.Quotient.mk R (z : A) = p.equiv (a : Γ(X, V)) := by
  have h := p.equiv_mem_power n a.property
  rw [← AssociatedGraded.map_mkQ_power J R n] at h
  obtain ⟨z, hz, hzeq⟩ := h
  exact ⟨⟨z, hz⟩, hzeq⟩

section QuotientPresentation

variable {i : Z ⟶ X} {i' : Z ⟶ X'} [IsImmersion i] [IsImmersion i']
  {V : X.affineOpens} {V' : X'.affineOpens}
  {A : Type v} [CommRing A] {J R R' : Ideal A}
  (pV : ChartQuotientPresentation i V J R) (pV' : ChartQuotientPresentation i' V' J R')
  (e : AssociatedGraded.GradedAlgEquiv J (A ⧸ R) (A ⧸ R'))

/-- **The comparison of the degree `n` pieces of the two kernel ideals determined by two
presentations of the chart rings and a comparison of the associated graded algebras of the two
quotients**: transport along the one presentation, the given comparison read in the quotient
rings' own graded algebras by `AssociatedGraded.GradedAlgEquiv.quotientPieceEquiv`, and transport
back along the other presentation. -/
noncomputable def quotientPresentationPieceEquiv (n : ℕ) :
    AssociatedGraded.piece (M := Γ(X, V)) (chartIdeal i V) n ≃+
      AssociatedGraded.piece (M := Γ(X', V')) (chartIdeal i' V') n :=
  ((AssociatedGraded.pieceEquivOfRingEquiv pV.equiv pV.map_chartIdeal n).trans
      (e.quotientPieceEquiv n).toAddEquiv).trans
    (AssociatedGraded.pieceEquivOfRingEquiv pV'.equiv pV'.map_chartIdeal n).symm

omit [IsImmersion i] [IsImmersion i'] in
/-- The comparison `quotientPresentationPieceEquiv` applied to `x` is the composite of the
transport along the first presentation, the comparison of the quotients' pieces, and the inverse
transport along the second presentation. -/
theorem quotientPresentationPieceEquiv_apply (n : ℕ)
    (x : AssociatedGraded.piece (M := Γ(X, V)) (chartIdeal i V) n) :
    quotientPresentationPieceEquiv pV pV' e n x =
      (AssociatedGraded.pieceEquivOfRingEquiv pV'.equiv pV'.map_chartIdeal n).symm
        (e.quotientPieceEquiv n
          (AssociatedGraded.pieceEquivOfRingEquiv pV.equiv pV.map_chartIdeal n x)) :=
  rfl

omit [IsImmersion i] [IsImmersion i'] in
/-- **The comparison on representatives, when the comparison of associated graded algebras is
induced by the identity of the ambient ring.** A representative `a` of `I(V)ⁿ` lifts to `z ∈ Jⁿ`
in the ambient ring; the comparison carries the class of `a` to the class of the function on the
other chart that `z` presents. This is the only form in which the comparison can be computed, and
it is what the compatibility with restriction is read off. -/
theorem quotientPresentationPieceEquiv_mk_of_lift (hind : e.IsInducedByIdentity) (n : ℕ)
    (a : AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) n)
    (z : AssociatedGraded.power (M := A) J n)
    (hz : Ideal.Quotient.mk R (z : A) = pV.equiv (a : Γ(X, V))) :
    quotientPresentationPieceEquiv pV pV' e n (AssociatedGraded.mk (chartIdeal i V) n a) =
      AssociatedGraded.mk (chartIdeal i' V') n
        ⟨pV'.equiv.symm (Ideal.Quotient.mk R' (z : A)),
          pV'.symm_mem_power n
            (AssociatedGraded.mk_mem_power_quotient J R' n z.property)⟩ := by
  have key : AssociatedGraded.pieceEquivOfRingEquiv pV.equiv pV.map_chartIdeal n
      (AssociatedGraded.mk (chartIdeal i V) n a) =
      AssociatedGraded.mk (J.map (Ideal.Quotient.mk R)) n
        ⟨Ideal.Quotient.mk R (z : A),
          (AssociatedGraded.mem_power_map_iff J R n).2
            (AssociatedGraded.mk_mem_power_quotient J R n z.property)⟩ := by
    rw [AssociatedGraded.pieceEquivOfRingEquiv_mk]
    exact congrArg _ (Subtype.ext hz.symm)
  rw [quotientPresentationPieceEquiv_apply, key,
    e.quotientPieceEquiv_mk_of_isInducedByIdentity hind n z,
    AssociatedGraded.pieceEquivOfRingEquiv_symm_mk]

/-- **The concrete identification of the two chart rings with two quotients of one ambient ring
turns a comparison of the associated graded algebras of those quotients into a chart-local
comparison.** The compatibility `hcompat` is the statement that the two presentations present the
*same* source chart: the two composite ring maps `A → Γ(Z, i⁻¹V)` they define — reduce modulo `R`,
identify with `Γ(X, V)`, restrict to the source; and the same with `R'`, `V'` — agree. That is
what makes a scalar on the one ambient chart and a scalar on the other, both lifted from a common
element of `A`, act alike. -/
noncomputable def ChartAssociatedGradedEquiv.ofQuotientPresentation
    {hpre : i' ⁻¹ᵁ V'.1 = i ⁻¹ᵁ V.1}
    (hcompat : ∀ a : A,
      (AddEquiv.cast (M := fun T : Z.Opens => Γ(Z, T)) hpre) (pV'.toSourceHom a) =
        pV.toSourceHom a) :
    ChartAssociatedGradedEquiv i i' V V' hpre where
  equiv n := quotientPresentationPieceEquiv pV pV' e n
  map_smul n r r' hr x := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (pV.equiv r)
    have hlift : pV.equiv.symm (Ideal.Quotient.mk R a) = r := by
      rw [ha, pV.equiv.symm_apply_apply]
    have hker : pV'.equiv.symm (Ideal.Quotient.mk R' a) - r' ∈ chartIdeal i' V' := by
      have h1 := hcompat a
      rw [ChartQuotientPresentation.toSourceHom_apply,
        ChartQuotientPresentation.toSourceHom_apply, hlift] at h1
      have h2 : (i'.app V').hom (pV'.equiv.symm (Ideal.Quotient.mk R' a)) =
          (i'.app V').hom r' :=
        (AddEquiv.cast (M := fun T : Z.Opens => Γ(Z, T)) hpre).injective (h1.trans hr.symm)
      rw [RingHom.mem_ker, map_sub, sub_eq_zero]
      exact h2
    have hsmul : ∀ w : AssociatedGraded.piece (M := Γ(X', V')) (chartIdeal i' V') n,
        pV'.equiv.symm (Ideal.Quotient.mk R' a) • w = r' • w := by
      intro w
      have h := AssociatedGraded.smul_eq_zero_of_mem (chartIdeal i' V') n hker w
      rw [sub_smul, sub_eq_zero] at h
      exact h
    rw [quotientPresentationPieceEquiv_apply, quotientPresentationPieceEquiv_apply,
      AssociatedGraded.pieceEquivOfRingEquiv_smul, ← ha,
      AssociatedGraded.GradedAlgEquiv.quotientPieceEquiv_smul_mk,
      AssociatedGraded.pieceEquivOfRingEquiv_symm_smul, hsmul]
  map_homogeneousMul n m x y := by
    rw [quotientPresentationPieceEquiv_apply, quotientPresentationPieceEquiv_apply,
      quotientPresentationPieceEquiv_apply,
      AssociatedGraded.pieceEquivOfRingEquiv_homogeneousMul,
      AssociatedGraded.GradedAlgEquiv.quotientPieceEquiv_homogeneousMul,
      AssociatedGraded.pieceEquivOfRingEquiv_symm_homogeneousMul]
  map_homogeneousOne := by
    rw [quotientPresentationPieceEquiv_apply,
      AssociatedGraded.pieceEquivOfRingEquiv_homogeneousOne,
      AssociatedGraded.GradedAlgEquiv.quotientPieceEquiv_homogeneousOne,
      AssociatedGraded.pieceEquivOfRingEquiv_symm_homogeneousOne]

end QuotientPresentation

section Comparison

variable (i : Z ⟶ X) (i' : Z ⟶ X') [IsImmersion i] [IsImmersion i']
  (V : X.affineOpens) (V' : X'.affineOpens)
  (hV : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl))
  (hV' : IsClosedImmersion (i'.resLE V'.1 (i' ⁻¹ᵁ V'.1) le_rfl))
  {hpre : i' ⁻¹ᵁ V'.1 = i ⁻¹ᵁ V.1} (c : ChartAssociatedGradedEquiv i i' V V' hpre)

/-- **The comparison of the sections of the degree `n` pieces of the two conormal algebras on the
chart**, for `n : ℕ`: the chart-local description of Stacks 0633 of the one, the given comparison
of associated graded algebras, and the chart-local description of the other, transported along the
equality of the two preimages. -/
def chartSectionsAddEquiv (n : ℕ) :
    ((conormalAlgebra i).algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)) ≃+
      ((conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)) :=
  ((((affineSectionsEquiv i V hV).equiv n).symm.trans (c.equiv n)).trans
      ((affineSectionsEquiv i' V' hV').equiv n)).trans
    (AddEquiv.cast (M := fun T : Z.Opens =>
      ((conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op T)) hpre)

/-- The comparison of sections is the stated composite. -/
theorem chartSectionsAddEquiv_apply (n : ℕ)
    (z : ((conormalAlgebra i).algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))) :
    chartSectionsAddEquiv i i' V V' hV hV' c n z =
      (AddEquiv.cast (M := fun T : Z.Opens =>
          ((conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op T)) hpre)
        ((affineSectionsEquiv i' V' hV').equiv n
          (c.equiv n (((affineSectionsEquiv i V hV).equiv n).symm z))) :=
  rfl

/-- **The comparison of sections is linear over the functions on the chart.** Both chart-local
descriptions are linear only over the functions on the respective ambient charts; the map on
functions of a closed immersion is surjective, so a scalar on the chart is the image of one on
each ambient chart, and the hypothesis of `ChartAssociatedGradedEquiv.map_smul` applies to the
resulting pair. -/
theorem chartSectionsAddEquiv_smul (n : ℕ)
    (s : Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)))
    (x : ((conormalAlgebra i).algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))) :
    chartSectionsAddEquiv i i' V V' hV hV' c n (s • x) =
      s • chartSectionsAddEquiv i i' V V' hV hV' c n x := by
  obtain ⟨r, hr⟩ := app_surjective_of_closedRestriction i V hV
    (show Γ(Z, i ⁻¹ᵁ V.1) from s)
  obtain ⟨r', hr'⟩ := app_surjective_of_closedRestriction i' V' hV'
    ((AddEquiv.cast (M := fun T : Z.Opens => Γ(Z, T)) hpre).symm (show Γ(Z, i ⁻¹ᵁ V.1) from s))
  have hrr' : (AddEquiv.cast (M := fun T : Z.Opens => Γ(Z, T)) hpre) ((i'.app V').hom r') =
      (i.app V).hom r := by
    rw [hr', AddEquiv.apply_symm_apply, hr]
  have h1 : ((affineSectionsEquiv i V hV).equiv n).symm (s • x) =
      r • ((affineSectionsEquiv i V hV).equiv n).symm x := by
    refine ((affineSectionsEquiv i V hV).equiv n).symm_apply_eq.2 ?_
    rw [(affineSectionsEquiv i V hV).map_smul n r, AddEquiv.apply_symm_apply, hr]
  rw [chartSectionsAddEquiv_apply, chartSectionsAddEquiv_apply, h1,
    c.map_smul n r r' hrr', (affineSectionsEquiv i' V' hV').map_smul n r',
    sectionSmul_cast ((conormalAlgebra i').algebra.piece (n : ℤ)) hpre, hrr', hr]

/-- **The comparison of sections is multiplicative.** -/
theorem chartSectionsAddEquiv_mul (n m : ℕ)
    (x : ((conormalAlgebra i).algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)))
    (y : ((conormalAlgebra i).algebra.piece (m : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))) :
    chartSectionsAddEquiv i i' V V' hV hV' c (n + m)
        (((conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ V.1)) x y) =
      ((conormalAlgebra i').algebra.mul (n : ℤ) (m : ℤ)).app (op (i ⁻¹ᵁ V.1))
        (chartSectionsAddEquiv i i' V V' hV hV' c n x)
        (chartSectionsAddEquiv i i' V V' hV hV' c m y) := by
  obtain ⟨a, rfl⟩ := ((affineSectionsEquiv i V hV).equiv n).surjective x
  obtain ⟨b, rfl⟩ := ((affineSectionsEquiv i V hV).equiv m).surjective y
  rw [← (affineSectionsEquiv i V hV).map_mul n m a b]
  rw [chartSectionsAddEquiv_apply, chartSectionsAddEquiv_apply, chartSectionsAddEquiv_apply,
    AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
    ← AssociatedGraded.homogeneousMul_eq_homogeneousSMul, c.map_homogeneousMul,
    AssociatedGraded.homogeneousMul_eq_homogeneousSMul,
    (affineSectionsEquiv i' V' hV').map_mul n m,
    gradedMul_cast (conormalAlgebra i').algebra (n : ℤ) (m : ℤ) hpre]

/-- **The comparison of sections carries the unit to the unit.** -/
theorem chartSectionsAddEquiv_one :
    chartSectionsAddEquiv i i' V V' hV hV' c 0
        ((conormalAlgebra i).algebra.one.eval (op (i ⁻¹ᵁ V.1))) =
      (conormalAlgebra i').algebra.one.eval (op (i ⁻¹ᵁ V.1)) := by
  rw [← (affineSectionsEquiv i V hV).map_one, chartSectionsAddEquiv_apply,
    AddEquiv.symm_apply_apply]
  rw [show (AssociatedGraded.mk (chartIdeal i V) 0
      (⟨1, by simp [AssociatedGraded.power]⟩ :
        AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) 0)) =
      AssociatedGraded.homogeneousOne (M := Γ(X, V)) (chartIdeal i V) from rfl,
    c.map_homogeneousOne,
    show AssociatedGraded.homogeneousOne (M := Γ(X', V')) (chartIdeal i' V') =
      AssociatedGraded.mk (chartIdeal i' V') 0
        (⟨1, by simp [AssociatedGraded.power]⟩ :
          AssociatedGraded.power (M := Γ(X', V')) (chartIdeal i' V') 0) from rfl,
    (affineSectionsEquiv i' V' hV').map_one,
    gradedOne_cast (conormalAlgebra i').algebra hpre]

/-- **The comparison of the sections of the degree `n` pieces, as an isomorphism of modules over
the functions on the chart**, for `n : ℕ`. -/
def chartSectionsIso (n : ℕ) :
    ((conormalAlgebra i).algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)) ≅
      ((conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1)) :=
  (AddEquiv.toLinearEquiv (chartSectionsAddEquiv i i' V V' hV hV' c n)
    (chartSectionsAddEquiv_smul i i' V V' hV hV' c n)).toModuleIso

/-- The isomorphism `chartSectionsIso` acts on sections as `chartSectionsAddEquiv`. -/
@[simp]
theorem chartSectionsIso_hom_apply (n : ℕ)
    (z : ((conormalAlgebra i).algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))) :
    (chartSectionsIso i i' V V' hV hV' c n).hom z =
      chartSectionsAddEquiv i i' V V' hV hV' c n z :=
  rfl

/-- **The comparison of sections in every integer degree.** In a nonnegative degree it is
`Stacks.Conormal.chartSectionsIso`; in a negative degree both pieces of both conormal algebras are
zero objects, so all their sections vanish. -/
def chartSectionsIsoInt : ∀ n : ℤ,
    ((conormalAlgebra i).algebra.piece n).val.obj (op (i ⁻¹ᵁ V.1)) ≅
      ((conormalAlgebra i').algebra.piece n).val.obj (op (i ⁻¹ᵁ V.1))
  | (n : ℕ) => chartSectionsIso i i' V V' hV hV' c n
  | Int.negSucc n =>
      haveI hneg : (Int.negSucc n) < 0 := Int.negSucc_lt_zero n
      have hz : ∀ z : ((conormalAlgebra i).algebra.piece (Int.negSucc n)).val.obj
          (op (i ⁻¹ᵁ V.1)), z = 0 := fun z =>
        Stacks.SheafOfModules.section_eq_zero_of_isZero
          ((conormalAlgebra i).negative_isZero _ hneg) _ z
      have hz' : ∀ z : ((conormalAlgebra i').algebra.piece (Int.negSucc n)).val.obj
          (op (i ⁻¹ᵁ V.1)), z = 0 := fun z =>
        Stacks.SheafOfModules.section_eq_zero_of_isZero
          ((conormalAlgebra i').negative_isZero _ hneg) _ z
      (LinearEquiv.ofLinearMap 0 0 (LinearMap.ext fun z => (hz' z).symm)
        (LinearMap.ext fun z => (hz z).symm)).toModuleIso

/-- In a nonnegative degree the integer-degree family is the degree already constructed. -/
theorem chartSectionsIsoInt_natCast (n : ℕ) :
    chartSectionsIsoInt i i' V V' hV hV' c (n : ℤ) =
      chartSectionsIso i i' V V' hV hV' c n :=
  rfl

/-- **The comparison of sections is multiplicative in every pair of integer degrees** — the form
`Stacks.BasisRestriction.IsMultiplicativeOnBasis` takes at one member of a basis. In a negative
degree the argument is zero, so both sides vanish. -/
theorem chartSectionsIsoInt_mul : ∀ (p q : ℤ)
    (x : ((conormalAlgebra i).algebra.piece p).val.obj (op (i ⁻¹ᵁ V.1)))
    (y : ((conormalAlgebra i).algebra.piece q).val.obj (op (i ⁻¹ᵁ V.1))),
    (chartSectionsIsoInt i i' V V' hV hV' c (p + q)).hom
        (((conormalAlgebra i).algebra.mul p q).app (op (i ⁻¹ᵁ V.1)) x y) =
      ((conormalAlgebra i').algebra.mul p q).app (op (i ⁻¹ᵁ V.1))
        ((chartSectionsIsoInt i i' V V' hV hV' c p).hom x)
        ((chartSectionsIsoInt i i' V V' hV hV' c q).hom y)
  | (n : ℕ), (m : ℕ), x, y => chartSectionsAddEquiv_mul i i' V V' hV hV' c n m x y
  | Int.negSucc n, q, x, y => by
      have hx : x = 0 :=
        Stacks.SheafOfModules.section_eq_zero_of_isZero
          ((conormalAlgebra i).negative_isZero _ (Int.negSucc_lt_zero n)) _ x
      subst hx
      simp only [map_zero, AddMonoidHom.zero_apply]
  | (n : ℕ), Int.negSucc m, x, y => by
      have hy : y = 0 :=
        Stacks.SheafOfModules.section_eq_zero_of_isZero
          ((conormalAlgebra i).negative_isZero _ (Int.negSucc_lt_zero m)) _ y
      subst hy
      simp only [map_zero]

/-- **The comparison of sections carries the unit to the unit**, in the integer-degree family. -/
theorem chartSectionsIsoInt_one :
    (chartSectionsIsoInt i i' V V' hV hV' c 0).hom
        ((conormalAlgebra i).algebra.one.eval (op (i ⁻¹ᵁ V.1))) =
      (conormalAlgebra i').algebra.one.eval (op (i ⁻¹ᵁ V.1)) :=
  chartSectionsAddEquiv_one i i' V V' hV hV' c

end Comparison

/-! ### Restriction to a smaller pair of charts -/

section Restriction

/-- Restriction to a smaller affine chart, as a map on the degree-`n` term of the `I`-adic
filtration of the chart ring: the restriction of a function in `I(V)ⁿ` lies in `I(W)ⁿ`, by
`Stacks.Conormal.map_mem_chartIdeal_pow`. -/
def chartPowerRestrict (i : Z ⟶ X) {V W : X.affineOpens} (hWV : W.1 ≤ V.1) (n : ℕ)
    (a : AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) n) :
    AssociatedGraded.power (M := Γ(X, W)) (chartIdeal i W) n :=
  ⟨X.presheaf.map (homOfLE hWV).op (a : Γ(X, V)), by
    simpa only [AssociatedGraded.ring_power_eq] using
      map_mem_chartIdeal_pow i hWV n
        (by simpa only [AssociatedGraded.ring_power_eq] using a.property)⟩

/-- The underlying function of `chartPowerRestrict i hWV n a` is the restriction of `a` from `V`
to `W`. -/
@[simp]
theorem chartPowerRestrict_coe (i : Z ⟶ X) {V W : X.affineOpens} (hWV : W.1 ≤ V.1) (n : ℕ)
    (a : AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) n) :
    (chartPowerRestrict i hWV n a : Γ(X, W)) =
      X.presheaf.map (homOfLE hWV).op (a : Γ(X, V)) :=
  rfl

variable (i : Z ⟶ X) (i' : Z ⟶ X') [IsImmersion i] [IsImmersion i']
  (V W : X.affineOpens) (V' W' : X'.affineOpens)
  (hV : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl))
  (hW : IsClosedImmersion (i.resLE W.1 (i ⁻¹ᵁ W.1) le_rfl))
  (hV' : IsClosedImmersion (i'.resLE V'.1 (i' ⁻¹ᵁ V'.1) le_rfl))
  (hW' : IsClosedImmersion (i'.resLE W'.1 (i' ⁻¹ᵁ W'.1) le_rfl))
  {hpreV : i' ⁻¹ᵁ V'.1 = i ⁻¹ᵁ V.1} {hpreW : i' ⁻¹ᵁ W'.1 = i ⁻¹ᵁ W.1}
  (c : ChartAssociatedGradedEquiv i i' V V' hpreV)
  (d : ChartAssociatedGradedEquiv i i' W W' hpreW)
  (hWV : W.1 ≤ V.1) (hWV' : W'.1 ≤ V'.1)

/-- **The comparison on a smaller pair of charts is the restriction of the comparison on a larger
pair.** This is stated on representatives, exactly as the naturality
`Stacks.Conormal.ConormalAlgebraData.localMap_naturality` of the chart-local presentations is:
whenever the class of a representative `a` upstairs goes to the class of `a'`, the class of the
restriction of `a` goes to the class of the restriction of `a'`.

A single `Stacks.Conormal.ChartAssociatedGradedEquiv` is data on one pair of charts and says
nothing about any other pair, so this is a genuine condition on a *family* of such comparisons,
not a consequence of the fields of one of them. -/
def IsChartRestriction : Prop :=
  ∀ (n : ℕ) (a : AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) n)
    (a' : AssociatedGraded.power (M := Γ(X', V')) (chartIdeal i' V') n),
    c.equiv n (AssociatedGraded.mk (chartIdeal i V) n a) =
      AssociatedGraded.mk (chartIdeal i' V') n a' →
    d.equiv n (AssociatedGraded.mk (chartIdeal i W) n (chartPowerRestrict i hWV n a)) =
      AssociatedGraded.mk (chartIdeal i' W') n (chartPowerRestrict i' hWV' n a')

/-- Two representatives of the degree `n` term of a filtration have the same class exactly when
their difference lies in the degree `n + 1` term. -/
private theorem mk_eq_mk_iff_sub_mem {A : Type*} [CommRing A] {M : Type*} [CommRing M] [Algebra A M]
    (I : Ideal A) (n : ℕ) (a b : AssociatedGraded.power (M := M) I n) :
    AssociatedGraded.mk I n a = AssociatedGraded.mk I n b ↔
      (a : M) - (b : M) ∈ AssociatedGraded.power (M := M) I (n + 1) :=
  Submodule.Quotient.eq _

/-- Restriction to a smaller affine chart carries the `n`-th term of the filtration of the chart
ring by the kernel ideal into the `n`-th term for the smaller chart. -/
private theorem restrict_mem_power_chartIdeal (i : Z ⟶ X) [IsImmersion i] {V W : X.affineOpens}
    (hWV : W.1 ≤ V.1) (n : ℕ) {x : Γ(X, V)}
    (hx : x ∈ AssociatedGraded.power (M := Γ(X, V)) (chartIdeal i V) n) :
    X.presheaf.map (homOfLE hWV).op x ∈
      AssociatedGraded.power (M := Γ(X, W)) (chartIdeal i W) n := by
  simpa only [AssociatedGraded.ring_power_eq] using
    map_mem_chartIdeal_pow i hWV n (by simpa only [AssociatedGraded.ring_power_eq] using hx)

/-- **The identity comparisons of one immersion with itself satisfy the restriction
condition.** Two representatives with the same homogeneous class differ by an element of
`I(V)ⁿ⁺¹`, whose restriction lies in `I(W)ⁿ⁺¹`; so the condition is satisfiable, and in
particular says nothing false about a pair of representatives. -/
theorem isChartRestriction_refl :
    IsChartRestriction i i V W V W (ChartAssociatedGradedEquiv.refl i V)
      (ChartAssociatedGradedEquiv.refl i W) hWV hWV := by
  intro n a a' h
  refine (mk_eq_mk_iff_sub_mem _ n _ _).2 ?_
  rw [chartPowerRestrict_coe, chartPowerRestrict_coe, ← map_sub]
  exact restrict_mem_power_chartIdeal i hWV (n + 1) ((mk_eq_mk_iff_sub_mem _ n a a').1 h)

/-- **The chart-local comparison of sections commutes with restriction to a smaller pair of
charts**, in a nonnegative degree, as soon as the two algebraic comparisons do.

Every section over the larger chart is the class of a representative `a` of `I(V)ⁿ`, by
surjectivity of the chart-local description; its restriction is the class of the restriction of
`a`, by the naturality of the chart-local presentations on both sides, and in between the
hypothesis `IsChartRestriction` carries one class of representatives to the other. The transport
along the equality of the two preimages is moved past the restriction maps by
`Stacks.Conormal.moduleSectionMap_cast`. -/
theorem chartSectionsAddEquiv_restrict
    (hres : IsChartRestriction i i' V W V' W' c d hWV hWV')
    (hZ : i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1) (n : ℕ)
    (z : ((conormalAlgebra i).algebra.piece (n : ℤ)).val.obj (op (i ⁻¹ᵁ V.1))) :
    chartSectionsAddEquiv i i' W W' hW hW' d n
        (((conormalAlgebra i).algebra.piece (n : ℤ)).val.map (homOfLE hZ).op z) =
      ((conormalAlgebra i').algebra.piece (n : ℤ)).val.map (homOfLE hZ).op
        (chartSectionsAddEquiv i i' V V' hV hV' c n z) := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _
    (((affineSectionsEquiv i V hV).equiv n).symm z)
  have hz : z = (affineSectionsEquiv i V hV).equiv n
      (AssociatedGraded.mk (chartIdeal i V) n a) := by
    rw [show AssociatedGraded.mk (chartIdeal i V) n a =
      ((affineSectionsEquiv i V hV).equiv n).symm z from ha, AddEquiv.apply_symm_apply]
  subst hz
  obtain ⟨a', ha'⟩ := Submodule.Quotient.mk_surjective _
    (c.equiv n (AssociatedGraded.mk (chartIdeal i V) n a))
  have hc : c.equiv n (AssociatedGraded.mk (chartIdeal i V) n a) =
      AssociatedGraded.mk (chartIdeal i' V') n a' := ha'.symm
  have hleft : ((conormalAlgebra i).algebra.piece (n : ℤ)).val.map (homOfLE hZ).op
        ((affineSectionsEquiv i V hV).equiv n (AssociatedGraded.mk (chartIdeal i V) n a)) =
      (affineSectionsEquiv i W hW).equiv n
        (AssociatedGraded.mk (chartIdeal i W) n (chartPowerRestrict i hWV n a)) := by
    rw [(affineSectionsEquiv i V hV).map_mk, (affineSectionsEquiv i W hW).map_mk]
    exact (conormalAlgebra i).localMap_naturality V W hWV hZ hV hW n _ _ rfl
  have hright : ((conormalAlgebra i').algebra.piece (n : ℤ)).val.map
        (homOfLE (i'.preimage_mono hWV')).op
        ((affineSectionsEquiv i' V' hV').equiv n (AssociatedGraded.mk (chartIdeal i' V') n a')) =
      (affineSectionsEquiv i' W' hW').equiv n
        (AssociatedGraded.mk (chartIdeal i' W') n (chartPowerRestrict i' hWV' n a')) := by
    rw [(affineSectionsEquiv i' V' hV').map_mk, (affineSectionsEquiv i' W' hW').map_mk]
    exact (conormalAlgebra i').localMap_naturality V' W' hWV' (i'.preimage_mono hWV') hV' hW'
      n _ _ rfl
  have hcast := moduleSectionMap_cast ((conormalAlgebra i').algebra.piece (n : ℤ)) hpreV hpreW
    (i'.preimage_mono hWV') hZ
    ((affineSectionsEquiv i' V' hV').equiv n (AssociatedGraded.mk (chartIdeal i' V') n a'))
  refine Eq.trans (chartSectionsAddEquiv_apply i i' W W' hW hW' d n _) ?_
  rw [hleft, AddEquiv.symm_apply_apply, hres n a a' hc, ← hright, hcast,
    chartSectionsAddEquiv_apply, AddEquiv.symm_apply_apply, hc]

/-- **The chart-local comparison of sections commutes with restriction to a smaller pair of
charts, in every integer degree.** In a nonnegative degree this is
`Stacks.Conormal.chartSectionsAddEquiv_restrict`; in a negative degree the target piece is a zero
object, so both sides vanish. -/
theorem chartSectionsIsoInt_restrict
    (hres : IsChartRestriction i i' V W V' W' c d hWV hWV')
    (hZ : i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1) : ∀ (p : ℤ)
    (z : ((conormalAlgebra i).algebra.piece p).val.obj (op (i ⁻¹ᵁ V.1))),
    (chartSectionsIsoInt i i' W W' hW hW' d p).hom
        (((conormalAlgebra i).algebra.piece p).val.map (homOfLE hZ).op z) =
      ((conormalAlgebra i').algebra.piece p).val.map (homOfLE hZ).op
        ((chartSectionsIsoInt i i' V V' hV hV' c p).hom z)
  | (n : ℕ), z =>
      chartSectionsAddEquiv_restrict i i' V W V' W' hV hW hV' hW' c d hWV hWV' hres hZ n z
  | Int.negSucc n, _z =>
      (Stacks.SheafOfModules.section_eq_zero_of_isZero
          ((conormalAlgebra i').negative_isZero _ (Int.negSucc_lt_zero n)) _ _).trans
        (Stacks.SheafOfModules.section_eq_zero_of_isZero
          ((conormalAlgebra i').negative_isZero _ (Int.negSucc_lt_zero n)) _ _).symm

end Restriction

/-! ### The presentations of two nested pairs of charts, compared

`Stacks.Conormal.IsChartRestriction` is a condition on a *pair* of chart-local comparisons, so
nothing about one `ChartQuotientPresentation` can discharge it. What does discharge it is a
comparison of the two presentations: a ring map between the two ambient rings carrying the one
filtration ideal into the other and compatible with both presentations. Together with the fact
that each comparison of associated graded algebras is induced by the identity of its ambient ring
— `AssociatedGraded.GradedAlgEquiv.IsInducedByIdentity`, which the comparison of Stacks 07VF has
by `associatedGraded_coker_algEquiv_isInducedByIdentity` — that is exactly enough: a lift of a
representative over the larger chart maps to a lift of its restriction over the smaller one, and
the comparison reads both off the same lift. -/

section RestrictionPresentation

/-- **A comparison of the chart presentations of two nested pairs of charts.** The data is a ring
map of the two ambient rings carrying the one filtration ideal into the other, under which both
presentations of the smaller pair are the restrictions of those of the larger pair. The two
commutation laws are stated on classes of ambient elements, which is the only form available: the
presentations are isomorphisms onto the two quotients, so a law stated on chart functions would
force the restriction map itself to be an isomorphism. -/
structure ChartQuotientPresentationHom {i : Z ⟶ X} {i' : Z ⟶ X'}
    {V W : X.affineOpens} {V' W' : X'.affineOpens} (hWV : W.1 ≤ V.1) (hWV' : W'.1 ≤ V'.1)
    {A : Type v} [CommRing A] {J R R' : Ideal A}
    (pV : ChartQuotientPresentation i V J R) (pV' : ChartQuotientPresentation i' V' J R')
    {B : Type w} [CommRing B] {K S S' : Ideal B}
    (pW : ChartQuotientPresentation i W K S) (pW' : ChartQuotientPresentation i' W' K S') where
  /-- The map of the two ambient rings. -/
  hom : A →+* B
  /-- It carries the filtration ideal of the larger pair into that of the smaller pair. -/
  map_ideal : J.map hom ≤ K
  /-- The presentation of the smaller chart of the first immersion is the restriction of the
  presentation of the larger one. -/
  left_commutes (a : A) :
    pW.equiv (X.presheaf.map (homOfLE hWV).op (pV.equiv.symm (Ideal.Quotient.mk R a))) =
      Ideal.Quotient.mk S (hom a)
  /-- The same for the second immersion. -/
  right_commutes (a : A) :
    pW'.equiv (X'.presheaf.map (homOfLE hWV').op (pV'.equiv.symm (Ideal.Quotient.mk R' a))) =
      Ideal.Quotient.mk S' (hom a)

/-- **A pair of presentations is compared with itself**, by the identity of the ambient ring: the
restriction along `V ≤ V` is the identity. This is the check that the data of a
`ChartQuotientPresentationHom` is available at all. -/
def ChartQuotientPresentationHom.refl {i : Z ⟶ X} {i' : Z ⟶ X'} {V : X.affineOpens}
    {V' : X'.affineOpens} {A : Type v} [CommRing A] {J R R' : Ideal A}
    (pV : ChartQuotientPresentation i V J R) (pV' : ChartQuotientPresentation i' V' J R') :
    ChartQuotientPresentationHom (le_refl V.1) (le_refl V'.1) pV pV' pV pV' where
  hom := RingHom.id A
  map_ideal := (Ideal.map_id J).le
  left_commutes a := by
    rw [show (homOfLE (le_refl V.1)) = 𝟙 V.1 from Subsingleton.elim _ _, op_id,
      CategoryTheory.Functor.map_id, CommRingCat.id_apply, RingEquiv.apply_symm_apply]
    rfl
  right_commutes a := by
    rw [show (homOfLE (le_refl V'.1)) = 𝟙 V'.1 from Subsingleton.elim _ _, op_id,
      CategoryTheory.Functor.map_id, CommRingCat.id_apply, RingEquiv.apply_symm_apply]
    rfl

/-- **The chart-local comparisons built from two compared presentations are compatible with
restriction.** Lift a representative `a` of `I(V)ⁿ` to `z ∈ Jⁿ` in the ambient ring of the larger
pair. Both comparisons are induced by the identity of their ambient rings, so over the larger pair
the class of `a` goes to the class of the function that `z` presents on the primed side, and over
the smaller pair the class of the restriction of `a` goes to the class of the function that the
image `φ(z)` presents — which by `right_commutes` is the restriction of the former. The two
classes agree because the difference of their representatives restricts into `I(W')ⁿ⁺¹`, by
`Stacks.Conormal.map_mem_chartIdeal_pow`. -/
theorem isChartRestriction_ofQuotientPresentation
    {i : Z ⟶ X} {i' : Z ⟶ X'} [IsImmersion i] [IsImmersion i']
    {V W : X.affineOpens} {V' W' : X'.affineOpens} {hWV : W.1 ≤ V.1} {hWV' : W'.1 ≤ V'.1}
    {A : Type v} [CommRing A] {J R R' : Ideal A}
    {pV : ChartQuotientPresentation i V J R} {pV' : ChartQuotientPresentation i' V' J R'}
    {eV : AssociatedGraded.GradedAlgEquiv J (A ⧸ R) (A ⧸ R')}
    {B : Type w} [CommRing B] {K S S' : Ideal B}
    {pW : ChartQuotientPresentation i W K S} {pW' : ChartQuotientPresentation i' W' K S'}
    {eW : AssociatedGraded.GradedAlgEquiv K (B ⧸ S) (B ⧸ S')}
    (hindV : eV.IsInducedByIdentity) (hindW : eW.IsInducedByIdentity)
    (phi : ChartQuotientPresentationHom hWV hWV' pV pV' pW pW')
    {hpreV : i' ⁻¹ᵁ V'.1 = i ⁻¹ᵁ V.1} {hpreW : i' ⁻¹ᵁ W'.1 = i ⁻¹ᵁ W.1}
    (hcompatV : ∀ a : A,
      (AddEquiv.cast (M := fun T : Z.Opens => Γ(Z, T)) hpreV) (pV'.toSourceHom a) =
        pV.toSourceHom a)
    (hcompatW : ∀ b : B,
      (AddEquiv.cast (M := fun T : Z.Opens => Γ(Z, T)) hpreW) (pW'.toSourceHom b) =
        pW.toSourceHom b) :
    IsChartRestriction i i' V W V' W'
      (ChartAssociatedGradedEquiv.ofQuotientPresentation pV pV' eV hcompatV)
      (ChartAssociatedGradedEquiv.ofQuotientPresentation pW pW' eW hcompatW) hWV hWV' := by
  intro n a a' h
  obtain ⟨z, hz⟩ := pV.exists_lift n a
  rw [show (ChartAssociatedGradedEquiv.ofQuotientPresentation pV pV' eV hcompatV).equiv n =
      quotientPresentationPieceEquiv pV pV' eV n from rfl,
    quotientPresentationPieceEquiv_mk_of_lift pV pV' eV hindV n a z hz] at h
  have hdiff := (mk_eq_mk_iff_sub_mem _ n _ a').1 h
  have hlift : Ideal.Quotient.mk S (phi.hom (z : A)) =
      pW.equiv ((chartPowerRestrict i hWV n a : Γ(X, W))) := by
    rw [chartPowerRestrict_coe, ← phi.left_commutes (z : A), hz, pV.equiv.symm_apply_apply]
  rw [show (ChartAssociatedGradedEquiv.ofQuotientPresentation pW pW' eW hcompatW).equiv n =
      quotientPresentationPieceEquiv pW pW' eW n from rfl,
    quotientPresentationPieceEquiv_mk_of_lift pW pW' eW hindW n
      (chartPowerRestrict i hWV n a)
      ⟨phi.hom (z : A),
        AssociatedGraded.map_mem_power_of_map_le phi.hom phi.map_ideal n z.property⟩ hlift]
  refine (mk_eq_mk_iff_sub_mem _ n _ _).2 ?_
  change pW'.equiv.symm (Ideal.Quotient.mk S' (phi.hom (z : A))) -
      (chartPowerRestrict i' hWV' n a' : Γ(X', W')) ∈
    AssociatedGraded.power (M := Γ(X', W')) (chartIdeal i' W') (n + 1)
  have hres : pW'.equiv.symm (Ideal.Quotient.mk S' (phi.hom (z : A))) =
      X'.presheaf.map (homOfLE hWV').op (pV'.equiv.symm (Ideal.Quotient.mk R' (z : A))) := by
    rw [← phi.right_commutes (z : A), pW'.equiv.symm_apply_apply]
  rw [hres, chartPowerRestrict_coe, ← map_sub]
  exact restrict_mem_power_chartIdeal i' hWV' (n + 1) hdiff

end RestrictionPresentation

end Stacks.Conormal

end
