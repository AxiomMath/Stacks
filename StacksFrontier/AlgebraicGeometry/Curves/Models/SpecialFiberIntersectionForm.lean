module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.IntersectionForm
public import StacksFrontier.AlgebraicGeometry.Curves.Models.DegreePairingSymmetry
import StacksCore.Tactic.StacksAttribute

/-!
# The four properties of the intersection form of the special fibre

In the situation of [Stacks, Tag 0C61] let `C_Z` run over the irreducible components of the
special fibre of a regular proper model `X ⟶ Spec(R)`, each with its reduced induced structure,
let `m_Z` be its multiplicity in `X_k`, so that `X_k = ∑ m_Z C_Z` by [Stacks, Tag 0C5Z], and let

`(∑_Z a_Z C_Z · ∑_Y b_Y C_Y) = ⟨a, 𝒪_X(∑_Y b_Y C_Y)⟩`

be the symmetric bilinear form of [Stacks, Tag 0C65]. [Stacks, Tag 0C66] records four properties
of this form, and all four are proved here at the hypotheses of the tag:

1. `(C_Z · C_Y) ≥ 0` for `Z ≠ Y`, with equality if and only if `C_Z ∩ C_Y = ∅`;
2. `(∑_Z m_Z C_Z · C_Y) = 0`;
3. there is no nonempty proper set `I` of components with `(C_Z · C_Y) = 0` for all `Z ∈ I` and
   `Y ∉ I`;
4. `(∑_Z a_Z C_Z · ∑_Z a_Z C_Z) ≤ 0` for every rational family `a`, with equality if and only if
   `a_Z = q m_Z` for a single `q ∈ ℚ`.

## Main results

* `Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix_nonneg_and_eq_zero_iff`
  — part (1).
* `Stacks.Models.RegularProperModelSituation.specialFiberIntersectionProduct_multiplicity_eq_zero`
  — part (2), in the orientation of the source.
* `Stacks.Models.RegularProperModelSituation.not_forall_specialFiberIntersectionMatrix_eq_zero`
  — part (3).
* `Stacks.Models.RegularProperModelSituation.specialFiberIntersectionForm_nonpos_and_eq_zero_iff`
  — part (4), the negative semidefiniteness together with its equality case.
* `Stacks.Models.RegularProperModelSituation.specialFiberIntersectionProduct_eq_sum_sum` — the
  intersection product expanded by the intersection matrix, which identifies the quadratic form
  of part (4) with the form of [Stacks, Tag 0C65] on integral nonnegative families.

## Implementation notes

**Why this is a separate module from `IntersectionForm.lean`.** Part (1) is a statement about
the degree of `𝒪_X(C_Y)` on the integral proper curve `C_Z`, and the geometric input for it —
nonnegativity and strict positivity of that degree — is proved in
`StacksFrontier/AlgebraicGeometry/Curves/Models/IntersectionForm.lean`, as is the deduction of
part (4) from the other three through [Stacks, Tag 0C5X]. Parts (2) and (4) additionally need the
symmetry of the form, [Stacks, Tag 0C64], which lives in
`StacksFrontier/AlgebraicGeometry/Curves/Models/DegreePairingSymmetry.lean`; and that file is
downstream of `IntersectionForm.lean`, through `ModelNumericalType.lean` and
`GenusFormulaSpecialFiber.lean`. So the four clauses are assembled here, where both halves are
visible, rather than in either of the two files they draw on.

**One intersection matrix.** The matrix `(C_Z · C_Y)` is
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix` of
`ModelNumericalType.lean`, the same one that the numerical type of [Stacks, Tag 0CA4] and the
symmetry clause of [Stacks, Tag 0C64] use; it is not redefined here. Its entries are identified
with the degrees `deg(𝒪_X(C_Y)|_{C_Z})` by
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionMatrix_eq_componentDegree`,
which is the spelling in which the geometric input for part (1) is available.

**Rational, not integral, coefficients in part (4).** The equality case asserts `a_Z = q m_Z` for
a rational `q`, so the quadratic form is taken on families valued in `ℚ`, where it is the double
sum `∑_Z ∑_Y a_Z a_Y (C_Z · C_Y)`. The form
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionProduct` cannot state this
directly: its second coefficient family is `ℕ`-valued, because only a nonnegative combination of
the components is an effective Cartier divisor whose invertible module `𝒪_X(∑ b_Y C_Y)` the
pairing can be taken against. That the double sum is the same form is
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionProduct_eq_sum_sum`.

**`DecidableEq` on the components.** The matrix is defined from the divisor degree at the basis
family `Pi.single Y 1`, so decidable equality of the index type is an instance argument, exactly
as in `ModelNumericalType.lean`, `GenusFormulaSpecialFiber.lean`, `DegreePairingSymmetry.lean`,
`ModelPicardNumericalType.lean` and `PicardSequence.lean`.

## References

* [Stacks Project, Tag 0C66](https://stacks.math.columbia.edu/tag/0C66)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C62](https://stacks.math.columbia.edu/tag/0C62)
* [Stacks Project, Tag 0C64](https://stacks.math.columbia.edu/tag/0C64)
* [Stacks Project, Tag 0C65](https://stacks.math.columbia.edu/tag/0C65)
* [Stacks Project, Tag 0C5X](https://stacks.math.columbia.edu/tag/0C5X)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})
  [DecidableEq (irreducibleComponents S.specialFiber)]

/-! ### Part (1): `(C_Z · C_Y) ≥ 0` for `Z ≠ Y`, with equality exactly for disjoint components -/

/-- **Stacks Project, Tag 0C66, part (1).** For two distinct irreducible components `C_Z ≠ C_Y` of
the special fibre of a regular proper model, `(C_Z · C_Y) ≥ 0`, and `(C_Z · C_Y) = 0` if and only
if `C_Z ∩ C_Y = ∅`.

The entry `(C_Z · C_Y)` is the degree of `𝒪_X(C_Y)` on `C_Z`. Since `C_Z ≠ C_Y` are distinct
irreducible components, `C_Z ⊄ C_Y`, so the canonical section of `𝒪_X(C_Y)` restricts to a
*nonzero* global section of `𝒪_X(C_Y)|_{C_Z}` on the integral proper curve `C_Z`, whose zero
scheme is the scheme-theoretic intersection `C_Z ∩ C_Y`. Part (1) of [Stacks, Tag 0B40] then
gives `(C_Z · C_Y) ≥ 0`, and part (2) of that tag gives `(C_Z · C_Y) > 0` exactly when the zero
scheme is nonempty, that is exactly when `C_Z` meets `C_Y`. -/
@[stacks 0C66 "part (1): (C_Z · C_Y) ≥ 0 for Z ≠ Y, with equality if and only if C_Z ∩ C_Y = ∅"]
theorem specialFiberIntersectionMatrix_nonneg_and_eq_zero_iff
    {Z Y : irreducibleComponents S.specialFiber} (h : Z ≠ Y) :
    0 ≤ S.specialFiberIntersectionMatrix Z Y ∧
      (S.specialFiberIntersectionMatrix Z Y = 0 ↔ (Z.1 : Set S.specialFiber) ∩ Y.1 = ∅) := by
  have := S.isEffectiveCartierDivisor_specialFiberComponent Y
  have hDE := S.not_supportSet_specialFiberComponentIdeal_subset h
  have hmat := S.specialFiberIntersectionMatrix_eq_componentDegree Z Y
  have hnn : 0 ≤ S.specialFiberIntersectionMatrix Z Y := by
    rw [hmat]
    exact componentDegree_invertibleSheaf_nonneg S.k (S.specialFiberComponentIdeal Z)
      (S.specialFiberComponentIdeal Y) (S.specialFiberComponentToSpec Z)
      (S.isProper_specialFiberComponentToSpec Z)
      (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z) hDE
  have hpos : 0 < S.specialFiberIntersectionMatrix Z Y ↔
      ((Z.1 : Set S.specialFiber) ∩ Y.1).Nonempty := by
    rw [hmat, componentDegree_invertibleSheaf_pos_iff S.k (S.specialFiberComponentIdeal Z)
      (S.specialFiberComponentIdeal Y) (S.specialFiberComponentToSpec Z)
      (S.isProper_specialFiberComponentToSpec Z)
      (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z) hDE,
      S.nonempty_inter_supportSet_specialFiberComponentIdeal_iff]
  refine ⟨hnn, ?_⟩
  rw [← Set.not_nonempty_iff_eq_empty, ← hpos]
  omega

/-- The multiplicity vector is killed by every row of the intersection matrix. -/
private theorem sum_multiplicity_mul_specialFiberIntersectionMatrix_eq_zero
    (Z : irreducibleComponents S.specialFiber) :
    ∑ Y, (S.specialFiberMultiplicity Y : ℤ) * S.specialFiberIntersectionMatrix Z Y = 0 :=
  sum_multiplicity_mul_intersectionMatrix_eq_zero_of_expansion S
    (fun W => S.specialFiberComponentIdeal W) (fun W => S.specialFiberComponentToSpec W)
    (fun W => S.isProper_specialFiberComponentToSpec W)
    (fun W => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent W)
    S.specialFiberIntersectionMatrix S.specialFiberMultiplicity
    (fun W => S.isEffectiveCartierDivisor_specialFiberComponent W)
    (fun c W => S.specialFiberDivisorDegree_eq_sum W c) S.specialFiberIdeal_eq_prod Z

/-! ### Part (2): the whole special fibre is orthogonal to each component -/

/-- **Stacks Project, Tag 0C66, part (2).** The special fibre `X_k = ∑_Z m_Z C_Z` of a regular
proper model is orthogonal to each of its irreducible components, `(∑_Z m_Z C_Z · C_Y) = 0`.

This is the orientation in which the source states the clause. By the symmetry of the form,
[Stacks, Tag 0C64], it equals `(C_Y · ∑_Z m_Z C_Z)`, which is the degree on `C_Y` of
`𝒪_X(∑_Z m_Z C_Z) = 𝒪_X(X_k)`; and that invertible module is trivial, the special fibre being cut
out by a uniformizer of the discrete valuation ring, so the degree vanishes. -/
@[stacks 0C66 "part (2): (∑_Z m_Z C_Z · C_Y) = 0, the special fibre is orthogonal to each \
component", sga "7 X 1.8" "partial"]
theorem specialFiberIntersectionProduct_multiplicity_eq_zero
    (Y : irreducibleComponents S.specialFiber) :
    S.specialFiberIntersectionProduct (fun Z => (S.specialFiberMultiplicity Z : ℤ))
      (Pi.single Y 1) = 0 := by
  have hcast : (fun Z => (((Pi.single Y 1 : irreducibleComponents S.specialFiber → ℕ) Z : ℕ) : ℤ))
      = (Pi.single Y 1 : irreducibleComponents S.specialFiber → ℤ) := by
    funext Z
    by_cases hZ : Z = Y
    · subst hZ; simp
    · simp [Pi.single_eq_of_ne hZ]
  rw [S.specialFiberIntersectionProduct_comm S.specialFiberMultiplicity (Pi.single Y 1), hcast,
    S.specialFiberIntersectionProduct_single Y S.specialFiberMultiplicity]
  rw [S.specialFiberDivisorDegree_eq_sum]
  exact sum_multiplicity_mul_specialFiberIntersectionMatrix_eq_zero S Y

/-! ### Part (3): the intersection graph of the special fibre is connected -/

/-- **Stacks Project, Tag 0C66, part (3).** There is no nonempty proper set `I` of irreducible
components of the special fibre with `(C_Z · C_Y) = 0` for all `Z ∈ I` and all `Y ∉ I`.

By part (1) such an `I` would make every component in `I` disjoint from every component not in
`I`, so the special fibre would be the union of the two disjoint nonempty closed sets
`⋃_{Z ∈ I} C_Z` and `⋃_{Y ∉ I} C_Y` — the components cover the special fibre, and there are
finitely many of them, so both unions are closed. That contradicts the connectedness of the
special fibre, [Stacks, Tag 0C62]. -/
@[stacks 0C66 "part (3): no nonempty proper set I of components has (C_Z · C_Y) = 0 for all Z in \
I and all Y not in I"]
theorem not_forall_specialFiberIntersectionMatrix_eq_zero
    (I : Set (irreducibleComponents S.specialFiber)) (hne : I.Nonempty) (hI : I ≠ Set.univ) :
    ¬ ∀ Z ∈ I, ∀ Y ∉ I, S.specialFiberIntersectionMatrix Z Y = 0 := by
  intro h
  classical
  obtain ⟨Y₀, hY₀⟩ : ∃ Y, Y ∉ I := by
    by_contra hall
    push Not at hall
    exact hI (Set.eq_univ_of_forall hall)
  obtain ⟨Z₀, hZ₀⟩ := hne
  have hclosed : ∀ J : Set (irreducibleComponents S.specialFiber),
      IsClosed (⋃ Z ∈ J, (Z.1 : Set S.specialFiber)) := fun J =>
    (Set.toFinite J).isClosed_biUnion fun Z _ => isClosed_of_mem_irreducibleComponents _ Z.2
  have hdisj : Disjoint (⋃ Z ∈ I, (Z.1 : Set S.specialFiber))
      (⋃ Y ∈ Iᶜ, (Y.1 : Set S.specialFiber)) := by
    rw [Set.disjoint_left]
    intro y hyU hyV
    obtain ⟨Z, hZ, hyZ⟩ := Set.mem_iUnion₂.1 hyU
    obtain ⟨Y, hY, hyY⟩ := Set.mem_iUnion₂.1 hyV
    have hZY : Z ≠ Y := fun e => hY (e ▸ hZ)
    have h0 := ((S.specialFiberIntersectionMatrix_nonneg_and_eq_zero_iff hZY).2).1 (h Z hZ Y hY)
    exact (Set.eq_empty_iff_forall_notMem.1 h0) y ⟨hyZ, hyY⟩
  have hcover : (⋃ Z ∈ I, (Z.1 : Set S.specialFiber)) ∪
      (⋃ Y ∈ Iᶜ, (Y.1 : Set S.specialFiber)) = Set.univ := by
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨Z, hZ⟩ := S.exists_mem_specialFiberComponent y
    by_cases hZI : Z ∈ I
    · exact Or.inl (Set.mem_iUnion₂.2 ⟨Z, hZI, hZ⟩)
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨Z, hZI, hZ⟩)
  obtain ⟨y, -, hyU, hyV⟩ := isPreconnected_closed_iff.1
    S.isConnected_univ_specialFiber.isPreconnected _ _ (hclosed I) (hclosed Iᶜ)
    hcover.symm.subset
    (by
      obtain ⟨y, hy⟩ := Z₀.2.1.nonempty
      exact ⟨y, trivial, Set.mem_iUnion₂.2 ⟨Z₀, hZ₀, hy⟩⟩)
    (by
      obtain ⟨y, hy⟩ := Y₀.2.1.nonempty
      exact ⟨y, trivial, Set.mem_iUnion₂.2 ⟨Y₀, hY₀, hy⟩⟩)
  exact Set.disjoint_left.1 hdisj hyU hyV

/-! ### Part (4): negative semidefiniteness, with the line `ℚ·m` as its nullspace -/

/-- **The intersection product expanded by the intersection matrix**,
`(∑_Z a_Z C_Z · ∑_Y b_Y C_Y) = ∑_Z ∑_Y a_Z b_Y (C_Z · C_Y)`. This identifies the quadratic form
of part (4) below with the form of [Stacks, Tag 0C65] wherever both are defined, that is on
families `a` valued in `ℤ` and `b` valued in `ℕ`. -/
theorem specialFiberIntersectionProduct_eq_sum_sum
    (a : irreducibleComponents S.specialFiber → ℤ)
    (b : irreducibleComponents S.specialFiber → ℕ) :
    S.specialFiberIntersectionProduct a b =
      ∑ Z, ∑ Y, a Z * (b Y : ℤ) * S.specialFiberIntersectionMatrix Z Y := by
  rw [specialFiberIntersectionProduct, intersectionProduct_eq_degreePairing_divisorSheaf,
    degreePairing]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [show componentDegree S.k (S.specialFiberComponentIdeal Z) (S.specialFiberComponentToSpec Z)
        (S.isProper_specialFiberComponentToSpec Z)
        (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
        (divisorSheaf S Finset.univ (fun W => S.specialFiberComponentIdeal W) b)
        (isInvertible_divisorSheaf S Finset.univ (fun W => S.specialFiberComponentIdeal W) b
          fun W _ => S.isEffectiveCartierDivisor_specialFiberComponent W) =
      S.specialFiberDivisorDegree Z b from rfl,
    S.specialFiberDivisorDegree_eq_sum Z b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun Y _ => by ring

/-- **Stacks Project, Tag 0C66, part (4).** For every family `a` of *rational* coefficients on the
irreducible components of the special fibre of a regular proper model,

`(∑_Z a_Z C_Z · ∑_Z a_Z C_Z) ≤ 0`,

and equality holds if and only if there is a single `q ∈ ℚ` with `a_Z = q m_Z` for every `Z`.

This is the source's own deduction from the other three parts through the linear algebra of
[Stacks, Tag 0C5X]: the intersection matrix is symmetric by [Stacks, Tag 0C64], has nonnegative
off-diagonal entries by part (1), kills the strictly positive multiplicity vector `m` by part (2)
— each multiplicity is positive by [Stacks, Tag 0C5Z] — and is irreducible by part (3). A
symmetric matrix with those three properties is negative semidefinite with nullspace exactly the
line spanned by `m`.

The form is written as the double sum `∑_Z ∑_Y a_Z a_Y (C_Z · C_Y)`, which is the bilinear
extension to rational coefficients of the form of [Stacks, Tag 0C65]; the two agree wherever both
are defined, by
`Stacks.Models.RegularProperModelSituation.specialFiberIntersectionProduct_eq_sum_sum`. -/
@[stacks 0C66 "part (4): (∑_Z a_Z C_Z · ∑_Z a_Z C_Z) ≤ 0 for rational a, with equality if and \
only if a_Z = q m_Z for a single rational q",
  sga "7 X 1.15" "partial",
  sga "7 X 1.8" "special case"]
theorem specialFiberIntersectionForm_nonpos_and_eq_zero_iff
    (a : irreducibleComponents S.specialFiber → ℚ) :
    ∑ Z, ∑ Y, a Z * a Y * (S.specialFiberIntersectionMatrix Z Y : ℚ) ≤ 0 ∧
      (∑ Z, ∑ Y, a Z * a Y * (S.specialFiberIntersectionMatrix Z Y : ℚ) = 0 ↔
        ∃ q : ℚ, ∀ Z, a Z = q * (S.specialFiberMultiplicity Z : ℚ)) := by
  have hoffDiag : ∀ Z Y, Z ≠ Y → 0 ≤ S.specialFiberIntersectionMatrix Z Y := fun _ _ hZY =>
    (S.specialFiberIntersectionMatrix_nonneg_and_eq_zero_iff hZY).1
  exact ⟨intersectionForm_nonpos_of_properties S.specialFiberIntersectionMatrix
      S.specialFiberMultiplicity hoffDiag S.specialFiberIntersectionMatrix_comm
      S.specialFiberMultiplicity_pos
      (sum_multiplicity_mul_specialFiberIntersectionMatrix_eq_zero S) a,
    intersectionForm_eq_zero_iff_of_properties S.specialFiberIntersectionMatrix
      S.specialFiberMultiplicity hoffDiag S.specialFiberIntersectionMatrix_comm
      S.specialFiberMultiplicity_pos
      (sum_multiplicity_mul_specialFiberIntersectionMatrix_eq_zero S)
      S.not_forall_specialFiberIntersectionMatrix_eq_zero a⟩

end RegularProperModelSituation

end Stacks.Models

end
