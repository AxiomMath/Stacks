module

public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.SegreCharts
public import StacksFrontier.AlgebraicGeometry.SegreEmbedding.PolyChart
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.MY

/-!
# The Segre projections, I: the substitution homomorphisms and their domains

`Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegre_of_projSegreIso` reduces Stacks Tag
01WD to a single isomorphism

`Proj (Segre product) ≅ ℙᵐ × ℙⁿ`,

and the direction of that isomorphism which is not yet begun is the one *out* of `Proj` of the
Segre product: the two Segre projections to the two factors.  Neither projection comes from a
graded ring homomorphism defined on the whole of the Segre product, because there is none: a
degree-preserving ring map from the polynomial ring on `X` into the Segre product must send `x_i`
to an element of `x`-degree one *and* `y`-degree one, so it must choose a `y`-variable.  This
file makes that choice, one `y`-variable at a time, and shows that the resulting partially
defined morphisms cover `Proj` of the Segre product and are pairwise compatible at the level of
the ring.

## Main definitions

* `Stacks.RingTheory.SegreProjection.substLeft R X Y j`: the `R`-algebra homomorphism from the
  polynomial ring on `X` to the Segre product sending `x_i` to the generator `x_i * y_j`.
* `Stacks.RingTheory.SegreProjection.substRight R X Y i`: the mirror image, from the polynomial
  ring on `Y`, sending `y_j` to `x_i * y_j`.
* `Stacks.RingTheory.SegreProjection.substLeftGraded`,
  `Stacks.RingTheory.SegreProjection.substRightGraded`: the same maps as graded ring
  homomorphisms, from the total-degree grading to the grading of the Segre product.  These are
  what `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` consumes.

## Main results

* `Stacks.RingTheory.SegreProjection.val_substLeft`: **the scaling formula.**  On a homogeneous
  polynomial of degree `d`, the substitution is multiplication by `y_j ^ d` after renaming the
  variables into the left summand.  Every other result here is a consequence.

* `Stacks.RingTheory.SegreProjection.substLeft_mul_comm`: **the compatibility identity.**  For
  `p` and `q` homogeneous *of the same degree*,

  `substLeft j p * substLeft k q = substLeft k p * substLeft j q`,

  which by the scaling formula is the commutativity of `y_j ^ d * y_k ^ d`.  This is the
  algebraic content of the statement that the partially defined projections agree on overlaps:
  the comparison of the two induced maps on the chart at `x_i * y_j` and the chart at
  `x_{i'} * y_k` is, after clearing denominators, exactly this identity.

* `Stacks.RingTheory.SegreProjection.iSup_mapDomain_substLeftGraded_eq_top`: the domains of
  definition of the substitutions, as `j` ranges over `Y`, cover `Proj` of the Segre product.
  Together with the previous item this is the input of a gluing argument; the gluing itself is
  not performed here.

## Implementation notes

The scaling formula is Euler's identity, in the form already proved as
`Stacks.AlgebraicGeometry.PolyChart.eval₂_mul_left_of_isHomogeneous`: substituting `c * g v` for
the variables of a polynomial homogeneous of degree `d` multiplies the value by `c ^ d`.  Here
`c` is `y_j` and `g` is the inclusion of the variables into the left summand.

Membership in the grading is *not* proved from the scaling formula, which would require knowing
how renaming interacts with the two weight functions; it is deduced instead from
`Stacks.RingTheory.SegreProduct.aeval_gen_mem_gradePiece`, by factoring the substitution through
the polynomial ring on `X × Y`: renaming `x_i` to `z_{i j}` preserves total-degree homogeneity
(`MvPolynomial.IsHomogeneous.rename_isHomogeneous`), and the Segre presentation is already known
to be graded.

As in the rest of this directory both gradings are definitions rather than instances, so the
statements that need them take them as ordinary instance binders.

## What is not done

No morphism of schemes is constructed here.  What this file provides is the two inputs a gluing
argument needs — a cover of `Proj` of the Segre product by the domains of definition, and the
ring-level identity that makes the partial maps agree — and nothing is proved about the glued
map, its target, or whether it is an isomorphism.  In particular the hypothesis of
`Stacks.AlgebraicGeometry.SegreClosedImmersion.absoluteSegre_of_projSegreIso` is still open.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public section

open AlgebraicGeometry MvPolynomial
open Stacks.RingTheory.SegreProduct

namespace Stacks.RingTheory.SegreProjection

universe u v

variable (R : Type u) [CommRing R] (X Y : Type v)

/-! ### The substitutions -/

/-- **Substitution of `x_i * y_j` for `x_i`.**  For a fixed variable `y_j` of the second group,
the `R`-algebra homomorphism from the polynomial ring on the first group of variables into the
Segre product sending each `x_i` to the generator `x_i * y_j`. -/
public noncomputable def substLeft (j : Y) : MvPolynomial X R →ₐ[R] segre R X Y :=
  MvPolynomial.aeval fun i : X => (⟨gen R X Y (i, j), gen_mem_segre R X Y (i, j)⟩ : segre R X Y)

/-- **Substitution of `x_i * y_j` for `y_j`**, the mirror image of
`Stacks.RingTheory.SegreProjection.substLeft`. -/
public noncomputable def substRight (i : X) : MvPolynomial Y R →ₐ[R] segre R X Y :=
  MvPolynomial.aeval fun j : Y => (⟨gen R X Y (i, j), gen_mem_segre R X Y (i, j)⟩ : segre R X Y)

/-- `substLeft j` sends the variable `x_i` to the generator `x_i * y_j`. -/
@[simp] public theorem substLeft_X (j : Y) (i : X) :
    substLeft R X Y j (MvPolynomial.X i) =
      (⟨gen R X Y (i, j), gen_mem_segre R X Y (i, j)⟩ : segre R X Y) :=
  MvPolynomial.aeval_X _ _

/-- `substRight i` sends the variable `y_j` to the generator `x_i * y_j`. -/
@[simp] public theorem substRight_X (i : X) (j : Y) :
    substRight R X Y i (MvPolynomial.X j) =
      (⟨gen R X Y (i, j), gen_mem_segre R X Y (i, j)⟩ : segre R X Y) :=
  MvPolynomial.aeval_X _ _

/-! ### The scaling formula -/

/-- The inclusion of the polynomial ring on `X` into the polynomial ring on `X ⊕ Y`, written as an
evaluation so that Euler's scaling identity applies to it directly. -/
public noncomputable def inclLeft : MvPolynomial X R →+* MvPolynomial (X ⊕ Y) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun i : X => MvPolynomial.X (Sum.inl i)

/-- The mirror image of `Stacks.RingTheory.SegreProjection.inclLeft`. -/
public noncomputable def inclRight : MvPolynomial Y R →+* MvPolynomial (X ⊕ Y) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun j : Y => MvPolynomial.X (Sum.inr j)

/-- In the polynomial ring on `X ⊕ Y`, `substLeft j p` is `p` evaluated at
`x_i ↦ y_j * x_i`. -/
public theorem val_substLeft_apply (j : Y) (p : MvPolynomial X R) :
    ((substLeft R X Y j p : segre R X Y) : MvPolynomial (X ⊕ Y) R) =
      MvPolynomial.eval₂ MvPolynomial.C
        (fun i : X => MvPolynomial.X (Sum.inr j) * MvPolynomial.X (Sum.inl i)) p := by
  rw [← Subalgebra.val_apply, substLeft, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_def,
    MvPolynomial.algebraMap_eq]
  congr 1
  funext i
  exact (gen_eq R X Y (i, j)).trans (mul_comm _ _)

/-- In the polynomial ring on `X ⊕ Y`, `substRight i q` is `q` evaluated at
`y_j ↦ x_i * y_j`. -/
public theorem val_substRight_apply (i : X) (q : MvPolynomial Y R) :
    ((substRight R X Y i q : segre R X Y) : MvPolynomial (X ⊕ Y) R) =
      MvPolynomial.eval₂ MvPolynomial.C
        (fun j : Y => MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr j)) q := by
  rw [← Subalgebra.val_apply, substRight, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_def,
    MvPolynomial.algebraMap_eq]
  congr 1

/-- **The scaling formula.**  On a polynomial homogeneous of degree `d`, substituting `x_i * y_j`
for `x_i` is the same as renaming the variables into the left summand and multiplying by
`y_j ^ d`.  This is Euler's identity. -/
public theorem val_substLeft {d : ℕ} (j : Y) {p : MvPolynomial X R} (hp : p.IsHomogeneous d) :
    ((substLeft R X Y j p : segre R X Y) : MvPolynomial (X ⊕ Y) R) =
      MvPolynomial.X (Sum.inr j) ^ d * inclLeft R X Y p := by
  rw [val_substLeft_apply,
    Stacks.AlgebraicGeometry.PolyChart.eval₂_mul_left_of_isHomogeneous _ _ _ hp]
  rfl

/-- The mirror image of `Stacks.RingTheory.SegreProjection.val_substLeft`. -/
public theorem val_substRight {d : ℕ} (i : X) {q : MvPolynomial Y R} (hq : q.IsHomogeneous d) :
    ((substRight R X Y i q : segre R X Y) : MvPolynomial (X ⊕ Y) R) =
      MvPolynomial.X (Sum.inl i) ^ d * inclRight R X Y q := by
  rw [val_substRight_apply,
    Stacks.AlgebraicGeometry.PolyChart.eval₂_mul_left_of_isHomogeneous _ _ _ hq]
  rfl

/-! ### The compatibility identity -/

/-- **The compatibility identity.**  Two substitutions, at `y_j` and at `y_k`, commute across a
pair of polynomials homogeneous of the *same* degree.  By the scaling formula both sides are
`y_j ^ d * y_k ^ d` times the product of the two renamed polynomials.

This is the algebraic content of the agreement of the two partially defined Segre projections on
the overlap of their domains: on the chart at `x_i * y_j` the projection carries
`a / (x_i * x_{i'}) ^ N` to `substLeft j a / substLeft j ((x_i * x_{i'}) ^ N)`, and on the chart
at `x_{i'} * y_k` to `substLeft k a / substLeft k ((x_i * x_{i'}) ^ N)`; the two fractions have
equal cross products precisely by this identity, applied to `a` and `(x_i * x_{i'}) ^ N`, which
are both homogeneous of degree `2 * N`. -/
public theorem substLeft_mul_comm {d : ℕ} (j k : Y) {p q : MvPolynomial X R}
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) :
    substLeft R X Y j p * substLeft R X Y k q =
      substLeft R X Y k p * substLeft R X Y j q := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul, val_substLeft R X Y j hp, val_substLeft R X Y k hq,
    val_substLeft R X Y k hp, val_substLeft R X Y j hq]
  ring

/-- The mirror image of `Stacks.RingTheory.SegreProjection.substLeft_mul_comm`. -/
public theorem substRight_mul_comm {d : ℕ} (i i' : X) {p q : MvPolynomial Y R}
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) :
    substRight R X Y i p * substRight R X Y i' q =
      substRight R X Y i' p * substRight R X Y i q := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_mul, val_substRight R X Y i hp, val_substRight R X Y i' hq,
    val_substRight R X Y i' hp, val_substRight R X Y i hq]
  ring

/-! ### The substitutions respect the gradings -/

/-- `substLeft j` factors through the polynomial ring on `X × Y`: it renames `x_i` to `z_{i j}`
and then applies the Segre presentation `z_{i j} ↦ x_i * y_j`. -/
public theorem substLeft_eq_presentation_rename (j : Y) (p : MvPolynomial X R) :
    ((substLeft R X Y j p : segre R X Y) : MvPolynomial (X ⊕ Y) R) =
      MvPolynomial.aeval (gen R X Y) (MvPolynomial.rename (fun i : X => (i, j)) p) := by
  rw [← Subalgebra.val_apply, substLeft, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_rename]
  rfl

/-- `substRight i` factors through the polynomial ring on `X × Y`: it renames `y_j` to `z_{i j}`
and then applies the Segre presentation `z_{i j} ↦ x_i * y_j`. -/
public theorem substRight_eq_presentation_rename (i : X) (q : MvPolynomial Y R) :
    ((substRight R X Y i q : segre R X Y) : MvPolynomial (X ⊕ Y) R) =
      MvPolynomial.aeval (gen R X Y) (MvPolynomial.rename (fun j : Y => (i, j)) q) := by
  rw [← Subalgebra.val_apply, substRight, MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_rename]
  rfl

/-- `substLeft j` sends a polynomial homogeneous of degree `d` into the degree-`d` piece of the
grading of the Segre product. -/
public theorem substLeft_mem_grading {d : ℕ} (j : Y) {p : MvPolynomial X R}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule X R d) :
    substLeft R X Y j p ∈ grading R X Y d := by
  rw [mem_grading, substLeft_eq_presentation_rename]
  exact aeval_gen_mem_gradePiece R X Y
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.IsHomogeneous.rename_isHomogeneous
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)))

/-- `substRight i` sends a polynomial homogeneous of degree `d` into the degree-`d` piece of the
grading of the Segre product. -/
public theorem substRight_mem_grading {d : ℕ} (i : X) {q : MvPolynomial Y R}
    (hq : q ∈ MvPolynomial.homogeneousSubmodule Y R d) :
    substRight R X Y i q ∈ grading R X Y d := by
  rw [mem_grading, substRight_eq_presentation_rename]
  exact aeval_gen_mem_gradePiece R X Y
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.IsHomogeneous.rename_isHomogeneous
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hq)))

/-- **The substitution as a graded ring homomorphism**, from the total-degree grading of the
polynomial ring on `X` to the grading of the Segre product.  This is the form consumed by
`Stacks.AlgebraicGeometry.ProjShared.mapDomain` and
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`. -/
public noncomputable def substLeftGraded (j : Y) :
    MvPolynomial.homogeneousSubmodule X R →+*ᵍ grading R X Y where
  toRingHom := (substLeft R X Y j).toRingHom
  map_mem {_ _} hx := substLeft_mem_grading R X Y _ hx

/-- The mirror image of `Stacks.RingTheory.SegreProjection.substLeftGraded`. -/
public noncomputable def substRightGraded (i : X) :
    MvPolynomial.homogeneousSubmodule Y R →+*ᵍ grading R X Y where
  toRingHom := (substRight R X Y i).toRingHom
  map_mem {_ _} hx := substRight_mem_grading R X Y _ hx

/-- The underlying map of `substLeftGraded j` is `substLeft j`. -/
@[simp] public theorem substLeftGraded_apply (j : Y) (p : MvPolynomial X R) :
    substLeftGraded R X Y j p = substLeft R X Y j p :=
  rfl

/-- The underlying map of `substRightGraded i` is `substRight i`. -/
@[simp] public theorem substRightGraded_apply (i : X) (q : MvPolynomial Y R) :
    substRightGraded R X Y i q = substRight R X Y i q :=
  rfl

end Stacks.RingTheory.SegreProjection

/-! ### The domains of definition cover `Proj` of the Segre product -/

namespace Stacks.AlgebraicGeometry.SegreProjection

open Stacks.RingTheory.SegreProjection Stacks.AlgebraicGeometry.ProjShared
open Stacks.AlgebraicGeometry.ProjTwistChain

universe u v

variable (R : Type u) [CommRing R] (X Y : Type v) [GradedAlgebra (grading R X Y)]

omit [GradedAlgebra (grading R X Y)] in
/-- `substLeftGraded j` sends the variable `x_i` to the generator `x_i * y_j`. -/
public theorem substLeftGraded_X (j : Y) (i : X) :
    substLeftGraded R X Y j (MvPolynomial.X i) = SegreCharts.genSub R X Y (i, j) := by
  rw [substLeftGraded_apply, substLeft_X]
  rfl

omit [GradedAlgebra (grading R X Y)] in
/-- `substRightGraded i` sends the variable `y_j` to the generator `x_i * y_j`. -/
public theorem substRightGraded_X (i : X) (j : Y) :
    substRightGraded R X Y i (MvPolynomial.X j) = SegreCharts.genSub R X Y (i, j) := by
  rw [substRightGraded_apply, substRight_X]
  rfl

/-- The chart at `x_i * y_j` lies in the domain of definition of the substitution at `y_j`. -/
public theorem basicOpen_genSub_le_mapDomain (i : X) (j : Y) :
    AlgebraicGeometry.Proj.basicOpen (grading R X Y) (SegreCharts.genSub R X Y (i, j)) ≤
      mapDomain (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
        (substLeftGraded R X Y j) := by
  rw [← substLeftGraded_X R X Y j i]
  exact basicOpen_le_mapDomain _ _ _ one_pos
    (MvPolynomial.isHomogeneous_X R i : MvPolynomial.X i ∈ _)

/-- **The domains of definition cover.**  As `y_j` ranges over the second group of variables, the
opens on which the substitution at `y_j` induces a morphism to `Proj` of the polynomial ring on
`X` cover the whole of `Proj` of the Segre product. -/
public theorem iSup_mapDomain_substLeftGraded_eq_top :
    (⨆ j : Y, mapDomain (MvPolynomial.homogeneousSubmodule X R) (grading R X Y)
      (substLeftGraded R X Y j)) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← SegreCharts.iSup_basicOpen_genSub_eq_top R X Y]
  refine iSup_le fun p => le_iSup_of_le p.2 ?_
  exact basicOpen_genSub_le_mapDomain R X Y p.1 p.2

/-- The mirror image of
`Stacks.AlgebraicGeometry.SegreProjection.iSup_mapDomain_substLeftGraded_eq_top`. -/
public theorem iSup_mapDomain_substRightGraded_eq_top :
    (⨆ i : X, mapDomain (MvPolynomial.homogeneousSubmodule Y R) (grading R X Y)
      (substRightGraded R X Y i)) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← SegreCharts.iSup_basicOpen_genSub_eq_top R X Y]
  refine iSup_le fun p => le_iSup_of_le p.1 ?_
  rw [← substRightGraded_X R X Y p.1 p.2]
  exact basicOpen_le_mapDomain _ _ _ one_pos
    (MvPolynomial.isHomogeneous_X R p.2 : MvPolynomial.X p.2 ∈ _)

end Stacks.AlgebraicGeometry.SegreProjection

end
