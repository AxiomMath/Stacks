module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.IdealPowerHomColimit.Restriction
public import Mathlib.Topology.LocallyFinite

/-!
# Products of locally finite families of quasi-coherent ideal sheaves

A family of quasi-coherent ideal sheaves whose supports form a locally finite family of closed
subsets has a product: on an affine open it is the finite product of the members whose support
meets it.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.locallyFiniteProd`: the product.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.ideal_locallyFiniteProd`: its ideal on an affine open.
* `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_locallyFiniteProd`: its support is the
  union of the supports.
* `AlgebraicGeometry.Scheme.IdealSheafData.locallyFiniteProd_eq_mul`: each member is a factor.
* `AlgebraicGeometry.Scheme.IdealSheafData.fg_ideal_locallyFiniteProd`: a product of ideal
  sheaves of finite type has finitely generated ideals.

## References

* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- A point of an open lies in the zero locus of a finite product of ideals of sections exactly
when it lies in the zero locus of one of the factors. -/
theorem _root_.AlgebraicGeometry.Scheme.mem_zeroLocus_prod {ι : Type*} {U : X.Opens}
    (s : Finset ι) (I : ι → Ideal Γ(X, U)) {x : X} (hx : x ∈ U) :
    x ∈ X.zeroLocus (U := U) ↑(∏ i ∈ s, I i) ↔
      ∃ i ∈ s, x ∈ X.zeroLocus (U := U) (I i : Set Γ(X, U)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [X.zeroLocus_univ, hx]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Scheme.zeroLocus_mul, Set.mem_union, ih]
    simp only [Finset.mem_insert, exists_eq_or_imp]

variable {ι : Type*} (F : ι → X.IdealSheafData)
  (hF : LocallyFinite fun i => ((F i).support : Set X))

/-- The finite set of members of a locally finite family whose support meets an affine open. -/
def supportMeets (U : X.affineOpens) : Finset ι :=
  (hF.finite_nonempty_inter_compact U.2.isCompact).toFinset

/-- Membership in `supportMeets`: the support of the member meets the affine open. -/
theorem mem_supportMeets {U : X.affineOpens} {i : ι} :
    i ∈ supportMeets F hF U ↔ ((F i).support ∩ (U : Set X) : Set X).Nonempty := by
  simp [supportMeets]

/-- The product of the ideals of a locally finite family over a finite set of indices containing
every member whose support meets the affine open does not depend on the finite set. -/
theorem prod_ideal_eq_of_subset (U : X.affineOpens) {s t : Finset ι}
    (hs : ∀ i, ((F i).support ∩ (U : Set X) : Set X).Nonempty → i ∈ s) (hst : s ⊆ t) :
    ∏ i ∈ t, (F i).ideal U = ∏ i ∈ s, (F i).ideal U := by
  refine (Finset.prod_subset hst fun i _ hi => ?_).symm
  have : ¬ ((F i).support ∩ (U : Set X) : Set X).Nonempty := fun h => hi (hs i h)
  rw [ideal_eq_top_of_disjoint_support (F i) U
    (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp this)).symm,
    Ideal.one_eq_top]

/-- The product of a locally finite family of quasi-coherent ideal sheaves: on an affine open it
is the product of the finitely many members whose support meets it, and its support is the union
of the supports. -/
def locallyFiniteProd : X.IdealSheafData :=
  mkOfMemSupportIff (fun U => ∏ i ∈ supportMeets F hF U, (F i).ideal U)
    (fun U f => by
      classical
      rw [Ideal.map.eq_def]
      change Ideal.mapHom _ _ = _
      rw [map_prod]
      change ∏ i ∈ supportMeets F hF U, Ideal.map _ ((F i).ideal U) = _
      simp only [map_ideal_basicOpen]
      refine prod_ideal_eq_of_subset F (X.affineBasicOpen f)
        (fun i hi => (mem_supportMeets F hF).2 hi) fun i hi => (mem_supportMeets F hF).2 ?_
      obtain ⟨x, hx, hxU⟩ := (mem_supportMeets F hF).1 hi
      exact ⟨x, hx, X.basicOpen_le f hxU⟩)
    (⋃ i, (F i).supportSet)
    (fun U x hxU => by
      rw [Scheme.mem_zeroLocus_prod _ _ hxU, Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, (mem_supportMeets F hF).2 ⟨x, hi, hxU⟩,
          ((F i).mem_support_iff_of_mem (U := U) hxU).1 hi⟩
      · rintro ⟨i, -, hi⟩
        exact ⟨i, ((F i).mem_support_iff_of_mem (U := U) hxU).2 hi⟩)

/-- The ideal of the product of a locally finite family on an affine open is the product of the
ideals of the members over any finite set of indices containing those whose support meets it. -/
theorem ideal_locallyFiniteProd (U : X.affineOpens) (s : Finset ι)
    (hs : ∀ i, ((F i).support ∩ (U : Set X) : Set X).Nonempty → i ∈ s) :
    (locallyFiniteProd F hF).ideal U = ∏ i ∈ s, (F i).ideal U := by
  classical
  show ∏ i ∈ supportMeets F hF U, (F i).ideal U = _
  rw [← prod_ideal_eq_of_subset F U (s := supportMeets F hF U)
    (fun i hi => (mem_supportMeets F hF).2 hi) (Finset.subset_union_left (s₂ := s)),
    prod_ideal_eq_of_subset F U hs (Finset.subset_union_right (s₁ := supportMeets F hF U))]

/-- The support of the product of a locally finite family is the union of the supports. -/
theorem coe_support_locallyFiniteProd :
    ((locallyFiniteProd F hF).support : Set X) = ⋃ i, ((F i).support : Set X) :=
  rfl

include hF in
/-- Replacing one member of a locally finite family by the unit ideal keeps it locally finite. -/
theorem locallyFinite_update_top [DecidableEq ι] (i : ι) :
    LocallyFinite fun j => ((Function.update F i ⊤ j).support : Set X) := by
  refine hF.subset fun j => ?_
  obtain rfl | hj := eq_or_ne j i <;> simp [Function.update_of_ne, *]

/-- The product of a locally finite family is the member `F i` times the product of the family
in which that member is replaced by the unit ideal. -/
theorem locallyFiniteProd_eq_mul [DecidableEq ι] (i : ι) :
    locallyFiniteProd F hF =
      F i * locallyFiniteProd (Function.update F i ⊤) (locallyFinite_update_top F hF i) := by
  ext U : 2
  let s := insert i (supportMeets F hF U)
  have hs : ∀ j, ((F j).support ∩ (U : Set X) : Set X).Nonempty → j ∈ s :=
    fun j hj => Finset.mem_insert_of_mem ((mem_supportMeets F hF).2 hj)
  have hs' : ∀ j, ((Function.update F i ⊤ j).support ∩ (U : Set X) : Set X).Nonempty →
      j ∈ s := fun j hj => by
    by_cases hji : j = i
    · exact hji ▸ Finset.mem_insert_self _ _
    · exact hs j (by rwa [Function.update_of_ne hji] at hj)
  rw [ideal_mul, Pi.mul_apply, ideal_locallyFiniteProd F hF U s hs,
    ideal_locallyFiniteProd _ _ U s hs', ← Finset.mul_prod_erase s _ (Finset.mem_insert_self _ _),
    ← Finset.mul_prod_erase s (fun j => (Function.update F i ⊤ j).ideal U)
      (Finset.mem_insert_self _ _)]
  simp only [Function.update_self, ideal_top, Pi.top_apply, Ideal.top_mul]
  exact congrArg _ (Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])

/-- A locally finite product of ideal sheaves of finite type, in the sense that their ideals on
affine opens are finitely generated, has finitely generated ideals on affine opens. -/
theorem fg_ideal_locallyFiniteProd (h : ∀ i (U : X.affineOpens), ((F i).ideal U).FG)
    (U : X.affineOpens) : ((locallyFiniteProd F hF).ideal U).FG := by
  classical
  show (∏ i ∈ supportMeets F hF U, (F i).ideal U).FG
  exact Finset.prod_induction _ _ (fun I J hI hJ => hI.mul hJ) ⟨{1}, by simp⟩ fun i _ => h i U

end AlgebraicGeometry.Scheme.IdealSheafData
