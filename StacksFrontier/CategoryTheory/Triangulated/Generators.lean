module

import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.CategoryTheory.ObjectProperty.ClosureShift
import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generators of triangulated categories

This file collects the formalizations of [Stacks, Tag 0FX9], [Stacks, Tag 0ATG],
[Stacks, Tag 09SJ], [Stacks, Tag 09SL], [Stacks, Tag 0FXA], [Stacks, Tag 09SK].

## References

* [Stacks, Tag 0FX9](https://stacks.math.columbia.edu/tag/0FX9)
* [Stacks, Tag 0ATG](https://stacks.math.columbia.edu/tag/0ATG)
* [Stacks, Tag 09SJ](https://stacks.math.columbia.edu/tag/09SJ)
* [Stacks, Tag 09SL](https://stacks.math.columbia.edu/tag/09SL)
* [Stacks, Tag 0FXA](https://stacks.math.columbia.edu/tag/0FXA)
* [Stacks, Tag 09SK](https://stacks.math.columbia.edu/tag/09SK)
-/

section

/-!
# Generators of triangulated categories

Let `C` be a (pre)triangulated category and let `P` be a property of objects of `C`, viewed as the
full subcategory it spans; the classical case is a single object `E`, that is
`P = ObjectProperty.singleton E`. Write `smd` for closure under direct summands (retracts), `add`
for closure under finite direct sums, and `A ⋆ B` for the objects fitting in a distinguished
triangle `A' ⟶ X ⟶ B' ⟶ A'⟦1⟧` with `A' ∈ A` and `B' ∈ B`. The objects reachable from `P` by
shifts, finite direct sums, summands and at most `n` extensions form
`⟨P⟩ₙ = ObjectProperty.triangEnvelopeIter n`, and their union
`⟨P⟩ = ⋃ₙ ⟨P⟩ₙ = ObjectProperty.triangEnvelope` is the *triangulated envelope* of `P`. The property
`P` is a *strong generator* when `⟨P⟩ₙ = C` for some `n`, a *classical generator* when `⟨P⟩ = C`,
and a *weak generator* when every nonzero object receives a nonzero map from some shift of an
object of `P` ([Stacks, Tag 09SJ]).

This file collects four facts about these notions.

* Only *boundedly many* shifts are ever needed: `⟨P⟩ₙ` is the increasing union over `m` of the
  subcategories `smd(add(P[-m, m])^{⋆ n})` built from the shifts of `P` in the range `[-m, m]`
  alone. Every construction involved is finitary, so an object of `⟨P⟩ₙ` is assembled from finitely
  many shifts of objects of `P`.
* The triangulated envelope is the smallest strictly full, saturated (thick) triangulated
  subcategory containing `P`, and it is the union over `n` and `m` of the subcategories
  `smd(add(P[-m, m])^{⋆ n})`.
* A classical generator is a weak generator: an object receiving only zero maps from the shifts of
  `P` receives only zero maps from every object of `⟨P⟩ = C`, in particular `𝟙 Y = 0`, so `Y` is a
  zero object.
* A strong generator is a classical one, and the converse holds as soon as *some* finite family of
  objects is a strong generator: each object of a strong generator, being in `⟨P⟩ = C`, already
  lies in `⟨P⟩ₘ` for one fixed `m`, and then `⟨X⟩ₙ ⊆ ⟨⟨P⟩ₘ⟩ₙ ⊆ ⟨P⟩` at a level bounded in terms of
  `n` and `m`.

## Main results

* `CategoryTheory.ObjectProperty.triangEnvelopeIter_eq_iSup_retractClosure_extensionProductIter`:
  boundedly many shifts suffice in `⟨P⟩ₙ`.
* `CategoryTheory.ObjectProperty.triangEnvelope_eq_iSup_and_isSaturated_and_le_iff`: `⟨P⟩` is the
  union over `n` and `m` of the `smd(add(P[-m, m])^{⋆ n})`, it is closed under isomorphisms,
  saturated and a triangulated subcategory, and it is contained in every strictly full, saturated
  triangulated subcategory containing `P`.
* `IsClassicalTriangulatedGenerator.isZero_of_rightOrthogonal_shiftClosure` (in the
  `CategoryTheory.ObjectProperty` namespace): if `P` is a classical generator, then every object
  right orthogonal to the shifts of `P` is a zero object.
* `CategoryTheory.ObjectProperty.IsClassicalTriangulatedGenerator.isStrongTriangulatedGenerator`:
  if a finite family of objects of `C` is a strong triangulated generator, then every classical
  triangulated generator of `C` is a strong triangulated generator.

## Implementation notes

Throughout, an arbitrary object property `P` replaces the source's single object `E`; the source's
statements are the case `P = ObjectProperty.singleton E`, and no step of any argument uses that `P`
is a single object. The source itself notes that Definition [Stacks, Tag 09SJ] generalizes to a
family of objects, and Mathlib's `IsClassicalTriangulatedGenerator` is already stated for a
property. The indexing is Mathlib's: `P.triangEnvelopeIter n` counts *extensions*, so it is the
source's `⟨P⟩_{n + 1}`, and the source's ranges `n ≥ 1`, `m ≥ 1` become `n, m : ℕ` unrestricted,
which is the same union because both families are monotone.

The shifted family `P[-m, m]` is spelled `⨆ i ∈ Set.Icc (-m) m, P.isoClosure.shift i`. Here
`ObjectProperty.shift` is the *inverse* image under the shift functor, so `P.isoClosure.shift i` is
the property of objects isomorphic to `Y⟦-i⟧` with `Y ∈ P`; the `isoClosure` is what makes the
union over all `i : ℤ` agree with `ObjectProperty.shiftClosure` (compare
`ObjectProperty.shiftClosure_eq_iSup`, which assumes `P.IsClosedUnderIsomorphisms` instead), and
dropping it would make the statement false for a property that is not closed under isomorphisms.
The source's `smd` is `ObjectProperty.retractClosure`, `add` is
`ObjectProperty.binaryProductsClosure`, and `⋆` iterated `n` times is
`ObjectProperty.extensionProductIter`.

*Boundedly many shifts.* The source's lemma is a chain of four descriptions of `⟨E⟩ₙ`; three of
them are already available, so what is proved here is the fourth.
`⟨E⟩ₙ = smd(⟨E⟩₁ ⋆ … ⋆ ⟨E⟩₁) = smd(⟨E⟩₁^{⋆n})` is how `ObjectProperty.triangEnvelopeIter` is
defined (`triangEnvelopeIter_zero`, `triangEnvelopeIter_succ`, `extensionProductIter_succ`), and
`⟨E⟩_{n + n'} = smd(⟨E⟩ₙ ⋆ ⟨E⟩_{n'})` is `ObjectProperty.triangEnvelopeIter_add`. Here
`[IsTriangulated C]` is *not* assumed, since the union description uses only that each closure
operation is finitary, not the octahedron axiom. The inner closure under retracts present in the
definition of `triangEnvelopeIter` is absent from the union description; it is removed at the
outset by Mathlib's `ObjectProperty.retractClosure_extensionProductIter_retractClosure`
([Stacks, Tag 0FX2]), after which the two sides differ only in the property being closed. Two of
the closure operations commute with *arbitrary* suprema for a formal reason, membership in a
supremum being an existential statement over the index: the closure under retracts
(`retractClosure_iSup`) and the extension product in each variable separately
(`extensionProduct_iSup_left`, `extensionProduct_iSup_right`). What directedness of the index is
for is the passage from a supremum over pairs of indices to one over the diagonal, needed because
an extension involves two objects at once (`iSup_iSup_eq_iSup_diag`); and it is what makes the
closure under finite direct sums commute with the supremum (`limitsClosure_iSup`), that being the
one operation whose finitariness rests on finiteness of a diagram rather than on an existential
quantifier.

*Saturated versus stable under retracts.* Reading `smd` as retract closure rather than as literal
summand closure costs nothing: in a pretriangulated category a strictly full subcategory is
saturated (`ObjectProperty.IsSaturated`, [Stacks, Tag 05RB]) if and only if it is stable under
retracts. One direction needs no triangulated structure at all, since `X` is a retract of `X ⊞ Y`;
the other uses that a distinguished triangle whose first map is a split monomorphism splits
(`Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`), so that a retract of `Y` is a direct
summand of `Y`. It needs no octahedron axiom. This is also why the minimality conjunct of the
envelope is stated with the source's hypotheses on the comparison subcategory `Q` — strictly full,
saturated, triangulated — which are weaker than the `[Q.IsStableUnderRetracts]` of
`ObjectProperty.triangEnvelope_le_iff`. The hypothesis `[P.Nonempty]` there replaces the source's
"let `E` be an object", and is used, since `⟨⊥⟩ = ⊥` contains no zero object and so is not a
triangulated subcategory.

*Weak generation.* Being a weak generator is spelled by its contrapositive, and spelled out rather
than named, since Mathlib has predicates for parts (1) and (2) of [Stacks, Tag 09SJ] but none for
part (3): "for every nonzero `Y` there are `n : ℤ` and a nonzero map `E ⟶ Y⟦n⟧`" is the same
condition as "an object `Y` such that every map `X ⟶ Y` with `X` a shift of an object of `P`
vanishes is zero", because `Hom(E, Y⟦n⟧) = 0` for all `n` if and only if `Hom(E⟦-n⟧, Y) = 0` for
all `n`. The resulting spelling `(P.shiftClosure ℤ).rightOrthogonal Y → IsZero Y`
(`ObjectProperty.rightOrthogonal`, [Stacks, Tag 0FXB]) is the one used for this same condition in
[Stacks, Tags 09SN, 0A8F and 0A8G], so the conclusion here discharges their hypothesis verbatim.
`IsZero Y` rather than `Y = 0` is the isomorphism-invariant reading of the source's `K = 0`. Only
`Pretriangulated C` is assumed, although the source says triangulated: the argument needs that the
objects admitting only the zero map to `Y` are closed under shifts (which is the hypothesis),
retracts ([Stacks, Tag 0FXC]), finite direct sums and extensions of distinguished triangles
(`Pretriangulated.Triangle.coyoneda_exact₂`), and never the octahedron axiom. The two closure
properties of the left orthogonal that the argument needs are stability under shifts and
extensions, which Mathlib has for the left orthogonal of any shift-stable property of objects
(`ObjectProperty.leftOrthogonal.IsTriangulated`), and stability under retracts, which Mathlib does
not have; it is proved here as `leftOrthogonal_isStableUnderRetracts`, for an arbitrary property of
objects of a category with zero morphisms, since a map out of a retract `X` of `X'` factors as
`X ⟶ X' ⟶ X ⟶ Y`. This route obtains the vanishing of `Hom(E', Y)` for all `E'` in `⟨E⟩`
([Stacks, Tag 09SK]) from the universal property of the triangulated envelope rather than by the
source's induction on the number of extensions.

*Classical implies strong.* The ambient strong generator is carried by an explicit witness, a
*finite* family `X : ι → C` with `ObjectProperty.ofObj X` a strong generator, rather than by the
source's single object `E'`. Some finiteness is essential here and not merely convenient: for an
arbitrary object property the hypothesis would be vacuous, since `⊤` is a strong generator of every
category (with `n = 0`), while the conclusion is not automatic. Finiteness is what turns the
pointwise bounds `X i ∈ ⟨P⟩_{mᵢ}` supplied by `⟨P⟩ = C` into the single bound `ofObj X ≤ ⟨P⟩ₘ` the
argument needs. The source's case is `ι = Unit`, where `ObjectProperty.ofObj X` is
`ObjectProperty.singleton E'` by definition; the empty family is allowed and harmless, the
statement then being monotonicity of `⟨·⟩ₙ`. `[IsTriangulated C]` is assumed: the levels add up,
`⟨P⟩_{n + m + 1} = smd(⟨P⟩ₙ ⋆ ⟨P⟩ₘ)` (`ObjectProperty.triangEnvelopeIter_add`), only in the
presence of the octahedron axiom. The level `m + n (m + 1)` reached is the source's `n m`, since
Mathlib's `⟨P⟩ₙ` counts extensions and `m + n (m + 1) + 1 = (n + 1) (m + 1)`. That `⟨R⟩₀ = R` for
`R = ⟨P⟩ₘ` is the step the source leaves to its citation of [Stacks, Tag 0FX3]; it rests on the
facts, proved here, that a property of objects closed under isomorphisms and under the chosen
binary product of two of its objects is closed under binary products, and that the closure under
retracts of a property closed under binary products, and the extension product of two such, are
again closed under binary products — [Stacks, Tag 0FX3] (2) and (1), for arbitrary properties in
place of `add(A)` and `add(B)`, the latter by the product of two distinguished triangles
(`Pretriangulated.productTriangle_distinguished`).

## References

* [Stacks project, Tag 09SL](https://stacks.math.columbia.edu/tag/09SL)
* [Stacks project, Tag 0ATG](https://stacks.math.columbia.edu/tag/0ATG)
* [Stacks project, Tag 0FX9](https://stacks.math.columbia.edu/tag/0FX9)
* [Stacks project, Tag 0FXA](https://stacks.math.columbia.edu/tag/0FXA)
* [Stacks project, Tag 09SJ](https://stacks.math.columbia.edu/tag/09SJ)
* [Stacks project, Tag 09SK](https://stacks.math.columbia.edu/tag/09SK)
* [Stacks project, Tag 05RB](https://stacks.math.columbia.edu/tag/05RB)
* [Stacks project, Tag 0FX3](https://stacks.math.columbia.edu/tag/0FX3)
* [Bondal and Van den Bergh, *Generators and representability of functors in commutative and
  noncommutative geometry*][bondal_vandenbergh_2003]
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

/-! ### Finitariness of the closure operations -/

section Lattice

variable {α : Type*} [CompleteLattice α]

/-- A family `F` monotone in each of two indices ranging over a directed preorder has the
same supremum as its diagonal. -/
private lemma iSup_iSup_eq_iSup_diag {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    {F : ι → ι → α} (hF : ∀ ⦃i i' j j'⦄, i ≤ i' → j ≤ j' → F i j ≤ F i' j') :
    ⨆ i, ⨆ j, F i j = ⨆ i, F i i :=
  le_antisymm (iSup₂_le fun i j ↦
      let ⟨k, hik, hjk⟩ := exists_ge_ge i j
      (hF hik hjk).trans (le_iSup (fun k ↦ F k k) k))
    (iSup_mono fun i ↦ le_iSup (F i) i)

variable (Q : ℤ → α)

/-- The supremum of `Q` over the interval `[-m, m]` increases with `m`. -/
private lemma monotone_biSup_Icc_natCast :
    Monotone fun m : ℕ ↦ ⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ), Q i := fun _ _ _ ↦
  biSup_mono (Set.Icc_subset_Icc (by omega) (by omega))

/-- Every integer lies in `[-m, m]` for some natural number `m`, so the suprema of `Q` over
these intervals exhaust the supremum of `Q` over all of `ℤ`. -/
private lemma iSup_biSup_Icc_natCast :
    ⨆ m : ℕ, ⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ), Q i = ⨆ i, Q i :=
  le_antisymm (iSup_le fun _ ↦ iSup₂_le fun i _ ↦ le_iSup Q i)
    (iSup_le fun i ↦ le_iSup_of_le i.natAbs (le_iSup₂_of_le i ⟨by omega, by omega⟩ le_rfl))

end Lattice

section Finitary

variable {C : Type*} [Category C]

/-- The closure under retracts commutes with arbitrary suprema. -/
private lemma retractClosure_iSup {ι : Sort*} (Q : ι → ObjectProperty C) :
    (⨆ i, Q i).retractClosure = ⨆ i, (Q i).retractClosure := by
  refine le_antisymm ?_ (iSup_le fun i ↦ monotone_retractClosure (le_iSup Q i))
  rintro X ⟨Y, hY, ⟨r⟩⟩
  rw [prop_iSup_iff] at hY ⊢
  obtain ⟨i, hi⟩ := hY
  exact ⟨i, Y, hi, ⟨r⟩⟩

/-- The closure under limits of *finite* shapes is finitary: it commutes with the supremum
of a monotone family of properties indexed by a nonempty directed preorder. -/
private lemma limitsClosure_iSup {β : Type*} (J : β → Type*) [∀ b, Category (J b)]
    [∀ b, Finite (J b)] {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    {Q : ι → ObjectProperty C} (hQ : Monotone Q) :
    (⨆ i, Q i).limitsClosure J = ⨆ i, (Q i).limitsClosure J := by
  refine le_antisymm ?_ (iSup_le fun i ↦ limitsClosure_monotone _ (le_iSup Q i))
  intro X hX
  induction hX with
  | of_mem X hX =>
      rw [prop_iSup_iff] at hX ⊢
      obtain ⟨i, hi⟩ := hX
      exact ⟨i, le_limitsClosure _ _ _ hi⟩
  | of_isoClosure e hX ih =>
      rw [prop_iSup_iff] at ih ⊢
      obtain ⟨i, hi⟩ := ih
      exact ⟨i, prop_of_iso _ e hi⟩
  | of_limitPresentation pres h ih =>
      choose f hf using fun j ↦ (prop_iSup_iff _ _).mp (ih j)
      obtain ⟨M, hM⟩ := Finite.exists_le f
      rw [prop_iSup_iff]
      exact ⟨M, .of_limitPresentation pres fun j ↦
        limitsClosure_monotone _ (hQ (hM j)) _ (hf j)⟩

/-- The closure under finite direct sums is finitary. -/
private lemma binaryProductsClosure_iSup {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] {Q : ι → ObjectProperty C} (hQ : Monotone Q) :
    (⨆ i, Q i).binaryProductsClosure = ⨆ i, (Q i).binaryProductsClosure :=
  limitsClosure_iSup _ hQ

/-- The closure under shifts already contains the closure under isomorphisms. -/
private lemma shiftClosure_isoClosure {A : Type*} [AddMonoid A] [HasShift C A]
    (P : ObjectProperty C) : P.isoClosure.shiftClosure A = P.shiftClosure A :=
  le_antisymm (by rw [shiftClosure_le_iff, isoClosure_le_iff]; exact le_shiftClosure P)
    (monotone_shiftClosure P.le_isoClosure)

/-- The closure of `P` under shifts is the increasing union of the shifts of `P` in the
ranges `[-m, m]`. -/
private lemma iSup_biSup_shift_Icc_eq_shiftClosure [HasShift C ℤ] (P : ObjectProperty C) :
    ⨆ m : ℕ, (⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ), P.isoClosure.shift i) = P.shiftClosure ℤ := by
  rw [iSup_biSup_Icc_natCast, ← shiftClosure_eq_iSup, shiftClosure_isoClosure]

end Finitary

section BoundedShifts

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- The extension product commutes with arbitrary suprema in its first variable: an
extension of a fixed `B` by an object satisfying one of the `A i` is an extension of `B` by
an object satisfying `A i` for a single `i`. -/
private lemma extensionProduct_iSup_left {ι : Sort*} (A : ι → ObjectProperty C)
    (B : ObjectProperty C) :
    extensionProduct (⨆ i, A i) B = ⨆ i, extensionProduct (A i) B := by
  refine le_antisymm ?_ (iSup_le fun i ↦ monotone_extensionProduct_left _ (le_iSup A i))
  rintro X ⟨Y, Z, f, g, h, hT, hY, hZ⟩
  rw [prop_iSup_iff] at hY ⊢
  obtain ⟨i, hi⟩ := hY
  exact ⟨i, Y, Z, f, g, h, hT, hi, hZ⟩

/-- The extension product commutes with arbitrary suprema in its second variable. -/
private lemma extensionProduct_iSup_right {ι : Sort*} (A : ObjectProperty C)
    (B : ι → ObjectProperty C) :
    extensionProduct A (⨆ i, B i) = ⨆ i, extensionProduct A (B i) := by
  refine le_antisymm ?_ (iSup_le fun i ↦ monotone_extensionProduct_right _ (le_iSup B i))
  rintro X ⟨Y, Z, f, g, h, hT, hY, hZ⟩
  rw [prop_iSup_iff] at hZ ⊢
  obtain ⟨i, hi⟩ := hZ
  exact ⟨i, Y, Z, f, g, h, hT, hY, hi⟩

/-- Iterated extension products are finitary: `n` extensions of members of a monotone family
indexed by a directed preorder can be performed inside a single member of the family. -/
private lemma extensionProductIter_iSup {ι : Type*} [Preorder ι] [IsDirectedOrder ι]
    {Q : ι → ObjectProperty C} (hQ : Monotone Q) (n : ℕ) :
    (⨆ i, Q i).extensionProductIter n = ⨆ i, (Q i).extensionProductIter n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [extensionProductIter_succ, ih, extensionProduct_iSup_left]
      simp only [extensionProduct_iSup_right, extensionProductIter_succ]
      exact iSup_iSup_eq_iSup_diag fun _ _ _ _ h h' ↦
        (monotone_extensionProduct_left _ (hQ h)).trans
          (monotone_extensionProduct_right _ (monotone_extensionProductIter (hQ h') n))

/-- The three finitariness lemmas at once: the objects reachable from a supremum of a
monotone family `Q` by finite direct sums, `n` extensions and retracts are those reachable
in the same way from a single `Q i`. -/
private lemma retractClosure_extensionProductIter_binaryProductsClosure_iSup {ι : Type*}
    [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {Q : ι → ObjectProperty C} (hQ : Monotone Q)
    (n : ℕ) :
    ((⨆ i, Q i).binaryProductsClosure.extensionProductIter n).retractClosure =
      ⨆ i, ((Q i).binaryProductsClosure.extensionProductIter n).retractClosure := by
  rw [binaryProductsClosure_iSup hQ,
    extensionProductIter_iSup (fun _ _ h ↦ limitsClosure_monotone _ (hQ h)) n,
    retractClosure_iSup]

/-- Only boundedly many shifts are needed in the triangulated envelope: the objects
reachable from `P` by shifts, finite direct sums, retracts and at most `n` extensions form
the increasing union, over `m : ℕ`, of the objects reachable in the same way but using only
the shifts of `P` in the range `[-m, m]`. In the notation of the Stacks project, for
`n ≥ 1` we have `⟨E⟩ₙ = ⋃_{m ≥ 1} smd(add(E[-m, m])^{⋆ n})`. -/
@[stacks 0FX9]
public theorem triangEnvelopeIter_eq_iSup_retractClosure_extensionProductIter
    (P : ObjectProperty C) (n : ℕ) :
    P.triangEnvelopeIter n =
      ⨆ m : ℕ, ((⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ),
        P.isoClosure.shift i).binaryProductsClosure.extensionProductIter n).retractClosure := by
  rw [triangEnvelopeIter, retractClosure_extensionProductIter_retractClosure,
    ← iSup_biSup_shift_Icc_eq_shiftClosure P]
  exact retractClosure_extensionProductIter_binaryProductsClosure_iSup
    (monotone_biSup_Icc_natCast _) n

end BoundedShifts

/-! ### Saturated subcategories and stability under retracts -/

section Saturated

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- A strictly full subcategory of a category with zero morphisms which is stable under
retracts is saturated in the sense of [Stacks, Tag 05RB]: a direct summand of an object of
the subcategory again lies in it, since `X` is a retract of `X ⊞ Y`. -/
private lemma isSaturated_of_isStableUnderRetracts (Q : ObjectProperty C)
    [Q.IsStableUnderRetracts] : Q.IsSaturated where
  isoClosure_of_biprod_left {X Y} _ h := by
    rw [Q.isoClosure_eq_self] at h ⊢
    exact Q.prop_of_retract ⟨biprod.inl, biprod.fst, by simp⟩ h
  isoClosure_of_biprod_right {X Y} _ h := by
    rw [Q.isoClosure_eq_self] at h ⊢
    exact Q.prop_of_retract ⟨biprod.inr, biprod.snd, by simp⟩ h

end Saturated

section Retracts

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- A strictly full saturated subcategory ([Stacks, Tag 05RB]) of a pretriangulated category
is stable under retracts: if `X` is a retract of `Y`, then `X⟦1⟧`'s inclusion is a split
monomorphism, so the third map of any distinguished triangle on the inclusion vanishes, the
triangle splits, and `X` is a direct summand of `Y`. -/
public lemma isStableUnderRetracts_of_isSaturated_of_isClosedUnderIsomorphisms
    (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms] [Q.IsSaturated] :
    Q.IsStableUnderRetracts where
  of_retract {X Y} ret hY := by
    obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle ret.i
    have hi : IsSplitMono (ret.i⟦(1 : ℤ)⟧') :=
      ⟨⟨⟨ret.r⟦(1 : ℤ)⟧', by simp [← CategoryTheory.Functor.map_comp, ret.retract]⟩⟩⟩
    have h0 : h = 0 := by
      have h1 := comp_distTriang_mor_zero₃₁ _ mem
      simp only [Triangle.mk_mor₃, Triangle.mk_mor₁, Triangle.mk_obj₁] at h1
      exact (cancel_mono (ret.i⟦(1 : ℤ)⟧')).1 (by simpa using h1)
    obtain ⟨e, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ mem h0
    have hQ : Q.isoClosure (X ⊞ Z) := Q.le_isoClosure _ (Q.prop_of_iso e hY)
    exact Q.isoClosure_eq_self ▸ IsSaturated.isoClosure_of_biprod_left hQ

/-- The triangulated envelope `⟨P⟩ = ⋃ₙ ⟨P⟩ₙ` of a nonempty object property `P` of a
triangulated category is the union over `n, m` of the subcategories `smd(add(P[-m, m])^{⋆ n})`;
it is closed under isomorphisms (strictly full), saturated (thick) and a triangulated
subcategory; and it is contained in a strictly full, saturated triangulated subcategory `Q`
exactly when `P` is, so that it is the smallest such subcategory containing `P`. -/
@[stacks 0ATG, sga "4½ Etat_0 2.3.3" "more general"]
public theorem triangEnvelope_eq_iSup_and_isSaturated_and_le_iff
    (P : ObjectProperty C) [P.Nonempty] [IsTriangulated C] :
    (P.triangEnvelope = ⨆ n : ℕ, ⨆ m : ℕ,
        ((⨆ i ∈ Set.Icc (-(m : ℤ)) (m : ℤ),
          P.isoClosure.shift i).binaryProductsClosure.extensionProductIter n).retractClosure) ∧
      P.triangEnvelope.IsClosedUnderIsomorphisms ∧ P.triangEnvelope.IsSaturated ∧
      P.triangEnvelope.IsTriangulated ∧
      ∀ Q : ObjectProperty C, Q.IsClosedUnderIsomorphisms → Q.IsSaturated → Q.IsTriangulated →
        (P.triangEnvelope ≤ Q ↔ P ≤ Q) := by
  refine ⟨?_, inferInstance, isSaturated_of_isStableUnderRetracts _, inferInstance,
    fun Q _ _ _ => ?_⟩
  · rw [triangEnvelope]
    exact iSup_congr (triangEnvelopeIter_eq_iSup_retractClosure_extensionProductIter P)
  · have := isStableUnderRetracts_of_isSaturated_of_isClosedUnderIsomorphisms Q
    exact P.triangEnvelope_le_iff

end Retracts

/-! ### Weak generators -/

section WeakGeneratorDef

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasShift C ℤ]

/-- A property of objects `P` of a category `C` with zero morphisms and a shift by `ℤ` is a
*weak generator*, or simply a *generator*, if every object `K` receiving only zero maps from the
shifts of the objects satisfying `P` is zero; equivalently, if every nonzero object `K` admits an
integer `n` and a nonzero map `E ⟶ K⟦n⟧` from an object `E` satisfying `P`
(`isWeakTriangulatedGenerator_iff`). -/
@[stacks 09SJ "(3)"]
public def IsWeakTriangulatedGenerator (P : ObjectProperty C) : Prop :=
  ∀ K : C, (P.shiftClosure ℤ).rightOrthogonal K → IsZero K

/-- A weak generator in the source's own words: `P` is a weak generator if and only if for every
nonzero object `K` there are an object `E` satisfying `P`, an integer `n` and a nonzero map
`E ⟶ K⟦n⟧`. For `P = ObjectProperty.singleton E` this is literally Definition
[Stacks, Tag 09SJ](3). -/
@[stacks 09SJ "(3), in the source's literal form: for every nonzero K an integer n and a nonzero \
  map E ⟶ K⟦n⟧"]
public theorem isWeakTriangulatedGenerator_iff (P : ObjectProperty C) :
    P.IsWeakTriangulatedGenerator ↔
      ∀ K : C, ¬ IsZero K → ∃ E, P E ∧ ∃ (n : ℤ) (f : E ⟶ K⟦n⟧), f ≠ 0 := by
  -- A shift is an equivalence, hence a right adjoint, hence preserves zero morphisms, and it is
  -- faithful: so it reflects the vanishing of a morphism, with no additivity assumption.
  have reflects : ∀ (m : ℤ) {X Y : C} (g : X ⟶ Y), (shiftFunctor C m).map g = 0 → g = 0 := by
    intro m X Y g hg
    have hz : (shiftFunctor C m).PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_isRightAdjoint _
    exact (shiftFunctor C m).map_injective (by rw [hg, hz.map_zero])
  constructor
  · intro h K hK
    by_contra hc
    refine hK (h K ?_)
    intro X f hX
    obtain ⟨E, a, e, hE⟩ := hX
    simp only [not_exists, not_and, not_not] at hc
    have ε : (E⟦a⟧)⟦-a⟧ ≅ E := (shiftFunctorCompIsoId C a (-a) (by simp)).app E
    have h1 : ε.inv ≫ (shiftFunctor C (-a)).map (e.inv ≫ f) = 0 := hc E hE (-a) _
    have h2 : e.inv ≫ f = 0 := reflects (-a) _ (by
      rw [← Iso.hom_inv_id_assoc ε ((shiftFunctor C (-a)).map (e.inv ≫ f)), h1, comp_zero])
    rw [← Iso.hom_inv_id_assoc e f, h2, comp_zero]
  · intro h K hK
    by_contra hnz
    obtain ⟨E, hE, n, f, hf⟩ := h K hnz
    have i := (shiftFunctorCompIsoId C n (-n) (by simp)).app K
    have h1 : (shiftFunctor C (-n)).map f ≫ i.hom = 0 := hK _ ⟨E, -n, Iso.refl _, hE⟩
    exact hf (reflects (-n) f ((cancel_mono i.hom).mp (by rw [h1, zero_comp])))

end WeakGeneratorDef

/-! ### A classical generator is a weak generator -/

section WeakGenerator

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- The left orthogonal of a property of objects is stable under retracts: a map out of a retract
`X` of `X'` factors through `X'`. -/
private lemma leftOrthogonal_isStableUnderRetracts (P : ObjectProperty C) :
    P.leftOrthogonal.IsStableUnderRetracts where
  of_retract {X X'} h hX' Z f hZ := by
    have hf : h.i ≫ h.r ≫ f = f := by rw [← Category.assoc, h.retract, Category.id_comp]
    rw [← hf, hX' (h.r ≫ f) hZ, comp_zero]

end WeakGenerator

section WeakGeneratorMain

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Stacks 09SL**: a classical generator of a (pre)triangulated category is a weak generator.
If the triangulated envelope of an object property `P` is everything, then an object `Y` which
receives only zero maps from the shifts of the objects of `P` — equivalently, an object `Y` with
`Hom(X, Y⟦n⟧) = 0` for every `X` satisfying `P` and every `n : ℤ` — is a zero object. -/
@[stacks 09SL]
public theorem IsClassicalTriangulatedGenerator.isZero_of_rightOrthogonal_shiftClosure
    {P : ObjectProperty C} (hP : P.IsClassicalTriangulatedGenerator) {Y : C}
    (hY : (P.shiftClosure ℤ).rightOrthogonal Y) : IsZero Y := by
  -- `Q := ((singleton Y).shiftClosure ℤ).leftOrthogonal` is the property of objects admitting
  -- only zero maps to the shifts of `Y`; it is stable under retracts, shifts and extensions.
  have _ := leftOrthogonal_isStableUnderRetracts ((singleton Y).shiftClosure ℤ)
  -- Every object satisfying `P` satisfies `Q`, by shift-stability of the right orthogonal.
  have hPQ : P ≤ ((singleton Y).shiftClosure ℤ).leftOrthogonal := by
    intro X hX Z f hZ
    obtain ⟨W, n, e, hW⟩ := hZ
    obtain rfl := (singleton_iff _ _).1 hW
    have hYn : (P.shiftClosure ℤ).rightOrthogonal (Y⟦n⟧) := le_shift _ n Y hY
    rw [← cancel_mono e.hom, zero_comp]
    exact hYn _ (le_shiftClosure (A := ℤ) P X hX)
  -- Hence `⟨P⟩ ≤ Q`, and `⟨P⟩` is everything, so `Q Y` holds.
  have hle : (⊤ : ObjectProperty C) ≤ ((singleton Y).shiftClosure ℤ).leftOrthogonal :=
    hP ▸ (triangEnvelope_le_iff P).2 hPQ
  -- `𝟙 Y : Y ⟶ Y` is a map to the shift `Y⟦0⟧ ≅ Y`, so it vanishes.
  rw [IsZero.iff_id_eq_zero]
  exact hle Y trivial (𝟙 Y)
    ⟨Y, 0, ((shiftFunctorZero C ℤ).app Y).symm, (singleton_iff Y Y).2 rfl⟩

end WeakGeneratorMain

/-! ### A classical generator of a category with a strong generator is a strong generator -/

section StrongGenerator

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- The objects reachable from `P` by shifts, finite direct sums, direct summands and at most
`m` extensions are closed under binary products. -/
private lemma isClosedUnderBinaryProducts_triangEnvelopeIter (P : ObjectProperty C) (m : ℕ) :
    (P.triangEnvelopeIter m).IsClosedUnderBinaryProducts := by
  have h₀ := isClosedUnderBinaryProducts_retractClosure (P.shiftClosure ℤ).binaryProductsClosure
  induction m with
  | zero => rw [triangEnvelopeIter_zero]; exact h₀
  | succ m hm =>
    rw [triangEnvelopeIter_succ]
    have := isClosedUnderBinaryProducts_extensionProduct
      (P.shiftClosure ℤ).binaryProductsClosure.retractClosure (P.triangEnvelopeIter m)
    exact isClosedUnderBinaryProducts_retractClosure _

/-- A property of objects stable under shifts, binary products and retracts is its own level
zero: nothing new is reached from it by shifts, finite direct sums and direct summands. -/
private lemma triangEnvelopeIter_zero_eq_self (R : ObjectProperty C) [R.IsStableUnderRetracts]
    [R.IsStableUnderShift ℤ] [R.IsClosedUnderBinaryProducts] :
    R.triangEnvelopeIter 0 = R := by
  refine le_antisymm ?_ (R.le_triangEnvelopeIter 0)
  rw [triangEnvelopeIter_zero, retractClosure_le_iff]
  exact limitsClosure_le (by rw [shiftClosure_le_iff])

/-- The levels of the triangulated envelope multiply: `n` extensions of objects of `⟨P⟩ₘ` are
reached from `P` by `m + n (m + 1)` extensions. In the source's indexing, where `⟨P⟩ₙ` counts
the *factors* rather than the extensions, this is `⟨⟨P⟩ₘ⟩ₙ ⊆ ⟨P⟩_{n m}`. -/
lemma triangEnvelopeIter_triangEnvelopeIter_le [IsTriangulated C] (P : ObjectProperty C)
    (m n : ℕ) :
    (P.triangEnvelopeIter m).triangEnvelopeIter n ≤ P.triangEnvelopeIter (m + n * (m + 1)) := by
  have := isClosedUnderBinaryProducts_triangEnvelopeIter P m
  induction n with
  | zero => simpa using (triangEnvelopeIter_zero_eq_self (P.triangEnvelopeIter m)).le
  | succ n ih =>
    rw [triangEnvelopeIter_succ, ← triangEnvelopeIter_zero,
      triangEnvelopeIter_zero_eq_self (P.triangEnvelopeIter m),
      show m + (n + 1) * (m + 1) = (m + 1) + (m + n * (m + 1)) by ring,
      P.triangEnvelopeIter_add (n' := m)]
    exact monotone_retractClosure (monotone_extensionProduct_right _ ih)

/-- A finite family of objects of the triangulated envelope of `P` lies in a single level
`⟨P⟩ₘ` of it. -/
private lemma exists_ofObj_le_triangEnvelopeIter (P : ObjectProperty C) {ι : Type*} [Finite ι]
    {X : ι → C} (hX : ∀ i, P.triangEnvelope (X i)) :
    ∃ m, ofObj X ≤ P.triangEnvelopeIter m := by
  choose f hf using fun i ↦ (P.prop_triangEnvelope_iff (X i)).1 (hX i)
  obtain ⟨M, hM⟩ := Finite.exists_le f
  exact ⟨M, (ofObj_le_iff X _).2 fun i ↦ P.monotone'_triangEnvelopeIter (hM i) _ (hf i)⟩

/-- **Stacks 0FXA**: in a triangulated category which has a strong generator, every classical
generator is a strong generator. Here the ambient strong generator is a finite family of objects
`X : ι → C` (the source's case is a single object, `ι = Unit`), and the classical generator is an
object property `P` (the source's case is `P = ObjectProperty.singleton E`). -/
@[stacks 0FXA]
public theorem IsClassicalTriangulatedGenerator.isStrongTriangulatedGenerator [IsTriangulated C]
    {P : ObjectProperty C} (hP : P.IsClassicalTriangulatedGenerator)
    {ι : Type*} [Finite ι] {X : ι → C} (hX : (ofObj X).IsStrongTriangulatedGenerator) :
    P.IsStrongTriangulatedGenerator := by
  obtain ⟨n, hn⟩ := hX
  obtain ⟨m, hm⟩ := exists_ofObj_le_triangEnvelopeIter P (X := X) fun i ↦ by rw [hP]; trivial
  refine ⟨m + n * (m + 1), top_le_iff.1 ?_⟩
  calc (⊤ : ObjectProperty C) = (ofObj X).triangEnvelopeIter n := hn.symm
    _ ≤ (P.triangEnvelopeIter m).triangEnvelopeIter n := monotone_triangEnvelopeIter hm n
    _ ≤ _ := triangEnvelopeIter_triangEnvelopeIter_le P m n

end StrongGenerator

end CategoryTheory.ObjectProperty

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Throughout, let `D` be a triangulated category, with shift functor `[1]`, `[n]`
the `n`-fold shift (`n : ℤ`), and `Hom(X, Y)` the morphisms `X ⟶ Y`. A
distinguished triangle is written `A ⟶ X ⟶ B ⟶ A[1]`.

We identify a (strictly) full subcategory of `D` with the corresponding subset
of `Ob(D)` (modelled here as a `Set D`); all subcategories are taken to be
strictly full (closed under isomorphism).

## Definition 1 (Operations on full subcategories), Stacks Section 13.35 (tag 0FX0)

Let `A, B` be full subcategories of `D`.

1. For an object `E`, the shift category `shiftCat E` (written `E[-∞,∞]`) is the
   full subcategory of all objects isomorphic to some shift `E[n]`, `n : ℤ`.
2. `smd A` is the full subcategory of all objects isomorphic to a direct summand
   of an object of `A`.
3. `add A` is the full subcategory of all objects isomorphic to a finite direct
   sum `⨁ᵢ Aᵢ` of objects `Aᵢ ∈ A` (`r ≥ 0`, the empty sum being a zero object).
4. `A ⋆ B` (`star A B`) is the full subcategory of all objects `X` that fit into
   a distinguished triangle `A ⟶ X ⟶ B ⟶ A[1]` with `A ∈ A` and `B ∈ B`.

## Definition 2 (The subcategories ⟨E⟩_n and ⟨E⟩), Stacks tag 09SI

Let `E` be an object of `D`.

1. `gen₁ E := smd (add (shiftCat E))`.
2. For `n > 1`, `genN E n := smd (gen₁ E ⋆ genN E (n-1))`.
3. `gen E := ⋃ n ≥ 1, genN E n`.

## Main Statement, Stacks tag 09SK (Lemma 13.36.4)

Let `E, K` be objects of `D`. The following are equivalent:
1. `Hom(E, K[i]) = 0` for all `i : ℤ`;
2. `Hom(E', K) = 0` for all objects `E' ∈ gen E`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.TriangulatedGenerators

variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasFiniteBiproducts D]

-- Main Definition(s)

/-- `shiftCat E` (i.e. `E[-∞,∞]`): the strictly full subcategory of all objects
isomorphic to some shift `E[n]`, `n : ℤ`. -/
def shiftCat (E : D) : Set D :=
  {X | ∃ n : ℤ, Nonempty (X ≅ (shiftFunctor D n).obj E)}

/-- `gen₁ E := smd (add (shiftCat E))`, i.e. `⟨E⟩₁`. -/
def gen₁ (E : D) : Set D := smd (add (shiftCat E))

/-- `genN E n := ⟨E⟩_{n+1}` (0-indexed): `genN E 0 = ⟨E⟩₁`, and for `n ≥ 1`,
`genN E n = smd (gen₁ E ⋆ genN E (n-1))`, matching `⟨E⟩_{n+1} = smd(⟨E⟩₁ ⋆ ⟨E⟩_n)`. -/
def genN (E : D) : ℕ → Set D
  | 0 => gen₁ E
  | (n + 1) => smd (starOp (gen₁ E) (genN E n))

/-- `gen E := ⋃ n, genN E n`, i.e. `⟨E⟩ = ⋃_{m ≥ 1} ⟨E⟩_m`. -/
def gen (E : D) : Set D := ⋃ n : ℕ, genN E n

-- Auxiliary: the "right-vanishing" property `∀ f : X ⟶ K, f = 0`.

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated
    D] [HasFiniteBiproducts D] [HasShift D ℤ] in
/-- SANITY CHECK PASSED
Closure under isomorphism for the right-vanishing property.
Argument: if `e : X ≅ X'` and every `X ⟶ K` is zero, then for `f : X' ⟶ K` we
have `e.hom ≫ f = 0`, and pre-composing with `e.inv` (using `e.inv ≫ e.hom = 𝟙`)
gives `f = 0`.
Lean hint: `obtain ⟨e⟩ := h; intro f; have := hX (e.hom ≫ f); ...; simpa`. -/
theorem vanish_iso (K X X' : D) (h : Nonempty (X ≅ X'))
    (hX : ∀ f : X ⟶ K, f = 0) : ∀ f : X' ⟶ K, f = 0 := by
  obtain ⟨e⟩ := h
  intro f
  simpa using congrArg (e.inv ≫ ·) (hX (e.hom ≫ f))

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    [IsTriangulated D] [HasFiniteBiproducts D] in
/-- SANITY CHECK PASSED
The right-vanishing property holds on `shiftCat E` provided `Hom(E, K[i]) = 0`
for all `i`.
Argument: any `X ∈ shiftCat E` is iso to `E[n]`; by `vanish_iso` it suffices to
kill all `g : E[n] ⟶ K`. The shift equivalence adjunction `(shiftEquiv D n).toAdjunction`
gives `Hom(E[n], K) ≅ Hom(E, K[-n])`, and the latter is zero by hypothesis at `i = -n`.
Lean hint: `(shiftEquiv D n).toAdjunction.homEquiv E K`, then `hyp (-n)`. -/
theorem vanish_shiftCat (E K : D)
    (hyp : ∀ (i : ℤ) (f : E ⟶ (shiftFunctor D i).obj K), f = 0) :
    ∀ X ∈ shiftCat E, ∀ f : X ⟶ K, f = 0 := by
  rintro X ⟨n, ⟨e⟩⟩
  refine vanish_iso K _ X ⟨e.symm⟩ ?_
  -- show vanishing on `E[n]`
  intro g
  let q := (shiftEquiv D n).toAdjunction.homEquiv E K
  rw [← q.symm_apply_apply g, hyp (-n) (q g)]
  simp [q, Adjunction.homEquiv_symm_apply]

omit [HasShift D ℤ] [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D]
    [IsTriangulated D] in
/-- SANITY CHECK PASSED
Closure under `add` for the right-vanishing property.
Argument: any `X ∈ add A` is iso to a finite biproduct `⨁ fobj`; by `vanish_iso`
reduce to killing `g : ⨁ fobj ⟶ K`. By `biproduct.hom_ext'` it suffices that each
component `ι_j ≫ g = 0`, which holds since `fobj j ∈ A`.
Lean hint: `biproduct.hom_ext'`, then `hA _ (hmem j)`. -/
theorem vanish_add (K : D) {A : Set D} (hA : ∀ X ∈ A, ∀ f : X ⟶ K, f = 0) :
    ∀ X ∈ add A, ∀ f : X ⟶ K, f = 0 := by
  rintro X ⟨r, fobj, hmem, ⟨e⟩⟩
  refine vanish_iso K _ X ⟨e.symm⟩ ?_
  exact fun g ↦ biproduct.hom_ext' _ _ fun j ↦ (hA _ (hmem j) _).trans comp_zero.symm

omit [IsTriangulated D] [HasFiniteBiproducts D] in
/-- SANITY CHECK PASSED
Closure under `smd` for the right-vanishing property.
Argument: `X ∈ smd A` means there is `Z ∈ A` and `e : Z ≅ X ⊞ Y`. The composite
`biprod.inl ≫ e.inv : X ⟶ Z` is a split mono with retraction `e.hom ≫ biprod.fst`.
For `g : X ⟶ K`, write `g = (biprod.inl ≫ e.inv) ≫ (e.hom ≫ biprod.fst ≫ g)`; the
second factor is a `Z ⟶ K`, which is zero since `Z ∈ A`.
Lean hint: `biprod.inl_inv` cancellation via `simp`, then `hA Z hZ`. -/
theorem vanish_smd (K : D) {A : Set D} (hA : ∀ X ∈ A, ∀ f : X ⟶ K, f = 0) :
    ∀ X ∈ smd A, ∀ f : X ⟶ K, f = 0 := by
  rintro X ⟨Z, Y, hZ, ⟨e⟩⟩ g
  have key : (biprod.inl ≫ e.inv) ≫ (e.hom ≫ biprod.fst ≫ g) = g := by simp
  rw [← key, hA Z hZ (e.hom ≫ biprod.fst ≫ g), comp_zero]

omit [IsTriangulated D] [HasFiniteBiproducts D] in
/-- SANITY CHECK PASSED
Closure under `star` for the right-vanishing property.
Argument: `X ∈ star A B` fits a distinguished triangle `T : A' ⟶ X ⟶ B' ⟶ A'[1]`
with `A' ∈ A`, `B' ∈ B`, `T.obj₂ ≅ X`. By `vanish_iso` reduce to `f : T.obj₂ ⟶ K`.
Since `A' ∈ A`, `T.mor₁ ≫ f = 0`; exactness of `Hom(-,K)` at the middle vertex
(`Triangle.yoneda_exact₂`, the practical form of Stacks 0149 / 0146) yields `g : B' ⟶ K`
with `f = T.mor₂ ≫ g`. As `B' ∈ B`, `g = 0`, so `f = 0`.
Lean hint: `Triangle.yoneda_exact₂ T hT f h1`. -/
theorem vanish_star (K : D) {A B : Set D}
    (hA : ∀ X ∈ A, ∀ f : X ⟶ K, f = 0)
    (hB : ∀ X ∈ B, ∀ f : X ⟶ K, f = 0) :
    ∀ X ∈ starOp A B, ∀ f : X ⟶ K, f = 0 := by
  rintro X ⟨T, hT, hT1, hT3, ⟨e⟩⟩
  refine vanish_iso K _ X ⟨e⟩ ?_
  intro f
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T hT f (hA _ hT1 _)
  rw [hg, hB _ hT3 g, comp_zero]

omit [IsTriangulated D] in
/-- SANITY CHECK PASSED
The right-vanishing property holds on `gen₁ E`.
Argument: `gen₁ E = smd (add (shiftCat E))`; compose the three closure lemmas. -/
theorem vanish_gen₁ (E K : D)
    (hyp : ∀ (i : ℤ) (f : E ⟶ (shiftFunctor D i).obj K), f = 0) :
    ∀ X ∈ gen₁ E, ∀ f : X ⟶ K, f = 0 :=
  vanish_smd K (vanish_add K (vanish_shiftCat E K hyp))

omit [IsTriangulated D] in
/-- SANITY CHECK PASSED
The right-vanishing property holds on `genN E n` for all `n`.
Argument: induction on `n`. Base `genN E 0 = gen₁ E` by `vanish_gen₁`. Step:
`genN E (m+1) = smd (star (gen₁ E) (genN E m))`; combine `vanish_smd`, `vanish_star`,
`vanish_gen₁`, and the inductive hypothesis. -/
theorem vanish_genN (E K : D)
    (hyp : ∀ (i : ℤ) (f : E ⟶ (shiftFunctor D i).obj K), f = 0) :
    ∀ n : ℕ, ∀ X ∈ genN E n, ∀ f : X ⟶ K, f = 0 := by
  intro n
  induction n with
  | zero => exact vanish_gen₁ E K hyp
  | succ m ih => exact vanish_smd K (vanish_star K (vanish_gen₁ E K hyp) ih)

-- Membership facts for the backward direction.

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated
    D] [HasFiniteBiproducts D] [Preadditive D] in
/-- SANITY CHECK PASSED
A shift `E[n]` lies in `shiftCat E` (witnessed by `Iso.refl`). -/
theorem shift_mem_shiftCat (E : D) (n : ℤ) :
    (shiftFunctor D n).obj E ∈ shiftCat E :=
  ⟨n, ⟨Iso.refl _⟩⟩

omit [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated
    D] [HasShift D ℤ] in
/-- SANITY CHECK PASSED
Any member of `A` is in `add A` (as the one-term biproduct). -/
theorem mem_add (A : Set D) (X : D) (hX : X ∈ A) : X ∈ add A :=
  ⟨1, fun _ => X, fun _ => hX, ⟨(biproductUniqueIso fun _ => X).symm⟩⟩

omit [IsTriangulated D] [HasFiniteBiproducts D] in
/-- SANITY CHECK PASSED
Any member of `A` is in `smd A` (as a summand of `X ⊞ 0`). -/
theorem mem_smd (A : Set D) (X : D) (hX : X ∈ A) : X ∈ smd A := by
  obtain ⟨Z, hZ⟩ := (HasZeroObject.zero (C := D))
  exact ⟨X, Z, hX, ⟨isoBiprodZero hZ⟩⟩

omit [IsTriangulated D] in
/-- SANITY CHECK PASSED
`shiftCat E ⊆ gen₁ E`. -/
theorem shiftCat_subset_gen₁ (E : D) : shiftCat E ⊆ gen₁ E :=
  fun X hX ↦ mem_smd _ X (mem_add _ X hX)

omit [IsTriangulated D] in
/-- SANITY CHECK PASSED
A shift `E[n]` lies in `gen E` (it is in `gen₁ E = genN E 0`). -/
theorem shift_mem_gen (E : D) (n : ℤ) :
    (shiftFunctor D n).obj E ∈ gen E := by
  refine Set.mem_iUnion.2 ⟨0, ?_⟩
  show (shiftFunctor D n).obj E ∈ gen₁ E
  exact shiftCat_subset_gen₁ E (shift_mem_shiftCat E n)

-- Main Statement(s)

omit [IsTriangulated D] in
/-- Stacks tag `09SK` (Lemma 13.36.4). For objects `E, K` of a triangulated
category `D`, the following are equivalent:
1. `Hom(E, K[i]) = 0` for all `i : ℤ`;
2. `Hom(E', K) = 0` for all `E' ∈ ⟨E⟩`. -/
@[stacks 09SK]
theorem hom_vanishing_iff_gen (E K : D) :
    (∀ i : ℤ, ∀ f : E ⟶ (shiftFunctor D i).obj K, f = 0) ↔
      (∀ E' ∈ gen E, ∀ f : E' ⟶ K, f = 0) := by
  -- SANITY CHECK PASSED
  -- Forward (1 ⇒ 2): unfold `gen E = ⋃ n, genN E n`; any `E' ∈ gen E` is in some
  -- `genN E n`, so `vanish_genN` kills `E' ⟶ K`.
  -- Backward (2 ⇒ 1): `E[-i] ∈ gen E` (`shift_mem_gen`), so all `E[-i] ⟶ K` vanish;
  -- transport along the shift adjunction `Hom(E[-i],K) ≅ Hom(E, K[i])` (via `eqToHom`
  -- identifying `K[-(-i)] = K[i]`) to conclude `Hom(E, K[i]) = 0`.
  constructor
  · -- forward direction
    intro hyp E' hE' f
    obtain ⟨n, hmem⟩ := Set.mem_iUnion.1 hE'
    exact vanish_genN E K hyp n E' hmem f
  · -- backward direction
    intro hgen i f
    -- `E[-i] ∈ gen E`, hence vanishing of all `E[-i] ⟶ K`.
    have α := (shiftFunctorCompIsoId D i (-i) (by simp)).app K
    have h1 : (shiftFunctor D (-i)).map f ≫ α.hom = 0 := hgen _ (shift_mem_gen E (-i)) _
    refine (shiftFunctor D (-i)).map_injective ?_
    rw [Functor.map_zero]
    exact (cancel_mono α.hom).mp (by rw [h1, zero_comp])

end Stacks.TriangulatedGenerators

end

end
