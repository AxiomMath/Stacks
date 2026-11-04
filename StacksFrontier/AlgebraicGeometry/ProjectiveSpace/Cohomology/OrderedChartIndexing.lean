module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.MiddleDegrees
public import StacksFrontier.RingTheory.Cech.OrderedIndexing

/-!
# The Čech cochains of a twist on projective space, indexed by increasing tuples

The degree-`p` Čech cochains of the standard cover of `ℙⁿ_R` for `𝒪(d)` in the monomial model
are the Laurent coefficient families concentrated on the `(p + 1)`-element index sets, with the
value at `S` lying in the chart `Stacks.ProjectiveSpace.Cohomology.twistChart R n d S`; this is
the submodule `Stacks.ProjectiveSpace.Cohomology.laurentCechCochains R n d p`. Since a
`(p + 1)`-element subset of `{0, …, n}` is the same thing as a strictly increasing tuple
`Fin (p + 1) → Fin (n + 1)`, that submodule is also the dependent product
$$ \prod_{i_0 < \cdots < i_p} \Gamma\bigl(D_+(T_{i_0} \cdots T_{i_p}), \mathcal{O}(d)\bigr), $$
which is the shape in which the ordered Čech complex of a cover is usually written: no
cardinality condition on the index and no ambient module of all index sets.

This file sets up that reindexing and reads the Čech differential in it. In the subset indexing
the differential is the signed sum over the elements of an index set, with the sign
`Cech.cechSign`; in the tuple indexing it is the alternating sum
`∑_j (-1)^j c_{i_0 … \widehat{i_j} … i_{p+1}}` over the omitted positions. The two agree, which
is the content of `coe_ordChartEquiv_laurentCechDiffRestrict`.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.OrdTuple`: the strictly increasing tuples
  `Fin (p + 1) → Fin (n + 1)`, the index type of the degree-`p` ordered Čech cochains.
* `Stacks.ProjectiveSpace.Cohomology.ordChartFamily`: the family of chart sections of a Čech
  cochain, indexed by increasing tuples.
* `Stacks.ProjectiveSpace.Cohomology.ordChartCochain`: the Čech cochain assembled from a family
  of chart sections indexed by increasing tuples, in the other direction.
* `Stacks.ProjectiveSpace.Cohomology.ordChartEquiv`: **the reindexing** — the degree-`p` Čech
  cochains are the dependent product of the charts over the increasing tuples.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.coe_ordChartEquiv_apply`: the reindexed cochain at a tuple
  is the value of the cochain at the set of values of that tuple.
* `Stacks.ProjectiveSpace.Cohomology.coe_ordChartEquiv_laurentCechDiffRestrict`: **the Čech
  differential in the tuple indexing is the alternating sum over the omitted positions.**

## Implementation notes

The target of `Stacks.ProjectiveSpace.Cohomology.ordChartEquiv` is a *dependent* product — the
chart depends on the tuple — so the two components of an equality of families are compared
separately, the index by `Subtype.ext` and the section by
`Stacks.ProjectiveSpace.Cohomology.coe_congr_ordTuple`. For the same reason every statement
about a value of the reindexing is phrased after coercion into the ambient module
`(Fin (n + 1) → ℤ) →₀ R` of all Laurent coefficient families, where the charts are invisible.

The set of values of a tuple is spelled `Set.range i` in the charts, because that is how
`Stacks.ProjectiveSpace.Cohomology.twistChart` takes its argument, and
`Finset.image i Finset.univ` in the cochains, because that is how
`Stacks.ProjectiveSpace.Cohomology.laurentCechCochains` takes its index;
`Stacks.ProjectiveSpace.Cohomology.coe_image_univ_eq_range` passes between the two.

## References

* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {n : ℕ} {d : ℤ} {p : ℕ}

/-- The index type of the degree-`p` ordered Čech cochains of a cover by `n + 1` opens: the
strictly increasing tuples `Fin (p + 1) → Fin (n + 1)`, one for each `(p + 1)`-element set of
indices. -/
abbrev OrdTuple (n p : ℕ) : Type := {i : Fin (p + 1) → Fin (n + 1) // StrictMono i}

/-- A strictly increasing tuple `Fin (p + 1) → Fin (n + 1)` takes `p + 1` distinct values. -/
theorem card_image_univ_of_strictMono {i : Fin (p + 1) → Fin (n + 1)} (hi : StrictMono i) :
    (Finset.image i Finset.univ).card = p + 1 := by
  rw [Finset.card_image_of_injective _ hi.injective, Finset.card_univ, Fintype.card_fin]

/-- The set of values of a tuple is the underlying set of the image of the whole index type. -/
theorem coe_image_univ_eq_range (i : Fin (p + 1) → Fin (n + 1)) :
    (Finset.image i Finset.univ : Set (Fin (n + 1))) = Set.range i := by
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- Listing the values of a strictly increasing tuple in increasing order returns the tuple. -/
theorem orderEmbOfFin_image_univ {i : Fin (p + 1) → Fin (n + 1)} (hi : StrictMono i)
    (h : (Finset.image i Finset.univ).card = p + 1) :
    ⇑((Finset.image i Finset.univ).orderEmbOfFin h) = i :=
  (Finset.orderEmbOfFin_unique h
    (fun x => Finset.mem_image.2 ⟨x, Finset.mem_univ x, rfl⟩) hi).symm

/-- The set of values of the increasing enumeration of a finite set is that set. -/
theorem image_orderEmbOfFin_univ (S : Finset (Fin (n + 1))) (h : S.card = p + 1) :
    Finset.image ⇑(S.orderEmbOfFin h) Finset.univ = S :=
  Finset.coe_injective (by rw [coe_image_univ_eq_range, Finset.range_orderEmbOfFin])

/-- Two values of a family of chart sections indexed by increasing tuples have the same
underlying Laurent coefficient family as soon as the tuples agree. This is the congruence lemma
the dependence of the chart on the tuple makes necessary. -/
theorem coe_congr_ordTuple (f : (i : OrdTuple n p) → twistChart R n d (Set.range i.1))
    {i j : OrdTuple n p} (h : i = j) :
    (f i : (Fin (n + 1) → ℤ) →₀ R) = (f j : (Fin (n + 1) → ℤ) →₀ R) := by
  subst h
  rfl

/-- The family of chart sections of a degree-`p` Čech cochain, indexed by increasing tuples: the
value at a tuple is the value of the cochain at the set of values of that tuple. -/
def ordChartFamily (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ)
    (c : laurentCechCochains R n d p) (i : OrdTuple n p) : twistChart R n d (Set.range i.1) :=
  ⟨(c : LaurentCochain R n) (Finset.image i.1 Finset.univ), by
    rw [← coe_image_univ_eq_range i.1]
    exact (mem_laurentCechCochains.1 c.2).1 _⟩

/-- The underlying Laurent coefficient family of a value of `ordChartFamily`. -/
@[simp]
theorem coe_ordChartFamily (c : laurentCechCochains R n d p) (i : OrdTuple n p) :
    (ordChartFamily R n d p c i : (Fin (n + 1) → ℤ) →₀ R)
      = (c : LaurentCochain R n) (Finset.image i.1 Finset.univ) :=
  rfl

/-- The Čech cochain assembled from a family of chart sections indexed by increasing tuples: on
a `(p + 1)`-element index set its value is the value of the family at the increasing enumeration
of that set, and on an index set of any other size it is zero. -/
def ordChartCochain (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ)
    (f : (i : OrdTuple n p) → twistChart R n d (Set.range i.1)) : LaurentCochain R n :=
  fun S =>
    if h : S.card = p + 1 then
      ↑(f ⟨⇑(S.orderEmbOfFin h), (S.orderEmbOfFin h).strictMono⟩)
    else 0

/-- The value of `ordChartCochain` on an index set of the right size. -/
@[simp]
theorem ordChartCochain_apply (f : (i : OrdTuple n p) → twistChart R n d (Set.range i.1))
    {S : Finset (Fin (n + 1))} (h : S.card = p + 1) :
    ordChartCochain R n d p f S = ↑(f ⟨⇑(S.orderEmbOfFin h), (S.orderEmbOfFin h).strictMono⟩) :=
  dite_eq_left h

/-- `ordChartCochain` vanishes on index sets of the wrong size. -/
@[simp]
theorem ordChartCochain_apply_of_card_ne
    (f : (i : OrdTuple n p) → twistChart R n d (Set.range i.1))
    {S : Finset (Fin (n + 1))} (h : S.card ≠ p + 1) :
    ordChartCochain R n d p f S = 0 :=
  dite_eq_right h

/-- `ordChartCochain` is a degree-`p` Čech cochain. -/
theorem ordChartCochain_mem (f : (i : OrdTuple n p) → twistChart R n d (Set.range i.1)) :
    ordChartCochain R n d p f ∈ laurentCechCochains R n d p := by
  refine ⟨fun S => ?_, fun S hS => ordChartCochain_apply_of_card_ne f hS⟩
  by_cases h : S.card = p + 1
  · rw [ordChartCochain_apply f h, ← Finset.range_orderEmbOfFin S h]
    exact (f ⟨⇑(S.orderEmbOfFin h), (S.orderEmbOfFin h).strictMono⟩).2
  · rw [ordChartCochain_apply_of_card_ne f h]
    exact zero_mem _

/-- **The degree-`p` Čech cochains of `𝒪(d)` on `ℙⁿ_R` in the monomial model are the dependent
product of the charts over the strictly increasing tuples `Fin (p + 1) → Fin (n + 1)`**: a
cochain goes to the family of its values at the sets of values of those tuples, and a family
goes to the cochain supported on the `(p + 1)`-element index sets that it prescribes. -/
def ordChartEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (p : ℕ) :
    laurentCechCochains R n d p ≃ₗ[R]
      ((i : OrdTuple n p) → twistChart R n d (Set.range i.1)) where
  toFun := ordChartFamily R n d p
  map_add' _ _ := funext fun _ => Subtype.ext rfl
  map_smul' _ _ := funext fun _ => Subtype.ext rfl
  invFun f := ⟨ordChartCochain R n d p f, ordChartCochain_mem f⟩
  left_inv c := Subtype.ext (funext fun S => by
    change ordChartCochain R n d p (ordChartFamily R n d p c) S = (c : LaurentCochain R n) S
    by_cases h : S.card = p + 1
    · rw [ordChartCochain_apply _ h, coe_ordChartFamily]
      exact congrArg (c : LaurentCochain R n) (image_orderEmbOfFin_univ S h)
    · rw [ordChartCochain_apply_of_card_ne _ h]
      exact ((mem_laurentCechCochains.1 c.2).2 S h).symm)
  right_inv f := funext fun i => Subtype.ext (by
    change ordChartCochain R n d p f (Finset.image i.1 Finset.univ)
      = (f i : (Fin (n + 1) → ℤ) →₀ R)
    rw [ordChartCochain_apply f (card_image_univ_of_strictMono i.2)]
    exact coe_congr_ordTuple f
      (Subtype.ext (orderEmbOfFin_image_univ i.2 (card_image_univ_of_strictMono i.2))))

/-- The reindexed cochain at an increasing tuple is the value of the cochain at the set of
values of that tuple. -/
@[simp]
theorem coe_ordChartEquiv_apply (c : laurentCechCochains R n d p) (i : OrdTuple n p) :
    ((ordChartEquiv R n d p c i : twistChart R n d (Set.range i.1)) : (Fin (n + 1) → ℤ) →₀ R)
      = (c : LaurentCochain R n) (Finset.image i.1 Finset.univ) :=
  rfl

/-- **The Čech differential of the standard cover of `ℙⁿ_R` in the tuple indexing is the
alternating sum over the omitted positions**: the signed sum over the elements of an index set
that defines `laurentCechDiff` becomes `∑_j (-1)^j c_{i₀ … î_j … i_{p+1}}` once the cochains are
reindexed by strictly increasing tuples. -/
theorem coe_ordChartEquiv_laurentCechDiffRestrict (c : laurentCechCochains R n d p)
    (i : OrdTuple n (p + 1)) :
    ((ordChartEquiv R n d (p + 1) (laurentCechDiffRestrict R n d p c) i :
        twistChart R n d (Set.range i.1)) : (Fin (n + 1) → ℤ) →₀ R)
      = ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          ((ordChartEquiv R n d p c ⟨i.1 ∘ j.succAbove, i.2.comp (Fin.strictMono_succAbove j)⟩ :
              twistChart R n d (Set.range (i.1 ∘ j.succAbove))) : (Fin (n + 1) → ℤ) →₀ R) := by
  have hS : (Finset.image i.1 Finset.univ).card = p + 1 + 1 :=
    card_image_univ_of_strictMono i.2
  have hemb : ⇑((Finset.image i.1 Finset.univ).orderEmbOfFin hS) = i.1 :=
    orderEmbOfFin_image_univ i.2 hS
  rw [coe_ordChartEquiv_apply, laurentCechDiffRestrict_coe, laurentCechDiff_apply,
    Finset.sum_image i.2.injective.injOn]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : i.1 j = (Finset.image i.1 Finset.univ).orderEmbOfFin hS j :=
    (congrFun hemb j).symm
  have hmem := (Finset.image i.1 Finset.univ).orderEmbOfFin_mem hS j
  have hcard : ((Finset.image i.1 Finset.univ).erase
      ((Finset.image i.1 Finset.univ).orderEmbOfFin hS j)).card = p + 1 := by
    have := Finset.card_erase_of_mem hmem
    omega
  have hsign : Cech.cechSign (Finset.image i.1 Finset.univ) (i.1 j) = (-1 : ℤ) ^ (j : ℕ) := by
    rw [hj]
    exact Cech.cechSign_orderEmbOfFin _ hS j
  have herase : (Finset.image i.1 Finset.univ).erase (i.1 j)
      = Finset.image (i.1 ∘ j.succAbove) Finset.univ := by
    rw [hj, ← image_orderEmbOfFin_univ _ hcard,
      Cech.orderEmbOfFin_erase (Finset.image i.1 Finset.univ) hS j hcard, hemb]
  rw [hsign, herase, coe_ordChartEquiv_apply]

end Stacks.ProjectiveSpace.Cohomology

end
