module

public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Compatible

/-!
# The degree-one cocycles of the Čech complex are the compatible families

Let `R` be a commutative ring, `f : Fin r → R` a finite family and `M` an `R`-module. The
degree-one term of the extended alternating Čech complex of
`StacksFrontier/RingTheory/Cech/Substrate.lean` is the direct sum

`C¹ = ⨁_{#s = 1} M_{∏ i ∈ s, f i}`,

indexed by the one-element subsets of `Fin r`, and the degree-two term is indexed by the
two-element subsets. This file identifies the kernel of `Cech.cechD f M 1` with the Čech compatible
families of `StacksFrontier/RingTheory/LocalCohomology/SectionsIso/Compatible.lean`.

The work is index bookkeeping. Reindexing `{s : Finset (Fin r) // s.card = 1}` by `Fin r` turns the
direct sum into the product `∏ i, M_{f_i}`, and the component of `d¹ x` at a two-element set
`{a, b}` is

`cechSign {a} b • (x_a in M_{f_a f_b}) + cechSign {b} a • (x_b in M_{f_a f_b})`,

the two contributions coming from inserting `b` into `{a}` and `a` into `{b}`. The two signs are
opposite — one of `a < b`, `b < a` holds, and `cechSign {a} b` is `-1` exactly when `a < b` — so
the component vanishes exactly when the two images in `M_{f_a f_b}` agree. Since each sign is its
own inverse, no case distinction on the order of `a` and `b` is needed.

## Main definitions

* `Stacks.LocalCohomology.cardOneEquiv` — the one-element subsets of `Fin r` are `Fin r`.
* `Stacks.LocalCohomology.cechComponentOne` — the component of a degree-one Čech cochain at a
  singleton.
* `Stacks.LocalCohomology.cechTermOneEquiv` — `C¹ ≅ ∏ i, M_{f_i}`.
* `Stacks.LocalCohomology.kerCechDOneEquivCechCompatible` — **the degree-one cocycles are the
  compatible families**.

## Main results

* `Stacks.LocalCohomology.cechComponentTwo_cechD_one` — the component of `d¹ x` at a two-element
  set, as a signed difference of two transition maps.
* `Stacks.LocalCohomology.mem_ker_cechD_one_iff` — a degree-one cochain is a cocycle exactly when
  the corresponding family of fractions is Čech compatible.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe v u

namespace Stacks.LocalCohomology

/-! ### Two pieces of arithmetic -/

variable {r : ℕ}

/-- The Čech sign attached to inserting `b` into the singleton `{a}`: it is `-1` exactly when `a`
precedes `b`, because `a` is then the one element of `{a}` to the left of the insertion point. -/
theorem cechSign_singleton (a b : Fin r) :
    Cech.cechSign ({a} : Finset (Fin r)) b = if a < b then -1 else 1 := by
  unfold Cech.cechSign
  rw [Finset.filter_singleton]
  by_cases h : a < b
  · rw [ite_eq_left h, ite_eq_left h, Finset.card_singleton, pow_one]
  · rw [ite_eq_right h, ite_eq_right h, Finset.card_empty, pow_zero]

/-- The two signs with which a pair of distinct indices contributes to the same two-element set are
opposite. -/
theorem cechSign_singleton_add_cechSign_singleton {a b : Fin r} (hab : a ≠ b) :
    Cech.cechSign ({a} : Finset (Fin r)) b + Cech.cechSign ({b} : Finset (Fin r)) a = 0 := by
  rw [cechSign_singleton, cechSign_singleton]
  rcases lt_or_gt_of_ne hab with h | h
  · rw [ite_eq_left h, ite_eq_right (asymm h)]
    ring
  · rw [ite_eq_right (asymm h), ite_eq_left h]
    ring

/-- Every Čech sign is its own inverse. -/
theorem cechSign_mul_self (s : Finset (Fin r)) (i : Fin r) :
    Cech.cechSign s i * Cech.cechSign s i = 1 := by
  unfold Cech.cechSign
  rw [← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

/-- Two elements of an abelian group whose signed sum vanishes, the signs being opposite and
each its own inverse, are equal. -/
theorem eq_of_zsmul_add_zsmul_eq_zero {N : Type*} [AddCommGroup N] {s t : ℤ}
    (hst : s + t = 0) (hs : s * s = 1) {za zb : N} (h : s • za + t • zb = 0) : za = zb := by
  obtain rfl : t = -s := by omega
  have h2 : s • (za - zb) = 0 := by rwa [smul_sub, sub_eq_add_neg, ← neg_smul]
  have h3 : za - zb = 0 := by rw [← one_smul ℤ (za - zb), ← hs, mul_smul, h2, smul_zero]
  exact sub_eq_zero.mp h3

/-! ### Components of the Čech terms -/

variable {R : Type u} [CommRing R] (f : Fin r → R) (M : ModuleCat.{v} R)

/-- The component of a Čech cochain of degree `p` at a given `p`-element set of indices. -/
abbrev cechComponent (p : ℕ) (t : {t : Finset (Fin r) // t.card = p}) :
    Cech.cechTerm f (M : Type _) p →ₗ[R] Cech.cechMod f (M : Type _) t.1 :=
  DirectSum.component R {t : Finset (Fin r) // t.card = p}
    (fun u => Cech.cechMod f (M : Type _) u.1) t

/-- The component of the inclusion of a summand at an index with the *same* underlying set of
indices, which need not be the same term of the subtype: the two localizations are then the same,
and the comparison is the transition map along an equality. -/
theorem cechComponent_lof_of_eq {p : ℕ} (j t : {t : Finset (Fin r) // t.card = p})
    (h : j.1 = t.1) (z : Cech.cechMod f (M : Type _) j.1) :
    cechComponent f M p t (DirectSum.lof R _ (fun u => Cech.cechMod f (M : Type _) u.1) j z) =
      Cech.cechι f (M : Type _) (le_of_eq h) z := by
  obtain rfl : j = t := Subtype.ext h
  rw [cechComponent, DirectSum.component.lof_self]
  exact (LinearMap.congr_fun (Cech.cechι_rfl f (M : Type _) j.1) z).symm

/-- The component of the inclusion of a summand at a different set of indices vanishes. -/
theorem cechComponent_lof_of_ne {p : ℕ} (j t : {t : Finset (Fin r) // t.card = p})
    (h : j.1 ≠ t.1) (z : Cech.cechMod f (M : Type _) j.1) :
    cechComponent f M p t (DirectSum.lof R _ (fun u => Cech.cechMod f (M : Type _) u.1) j z) =
      0 := by
  rw [cechComponent, DirectSum.component.of,
    dite_eq_right fun he => h (congrArg Subtype.val he)]

/-- The component of a degree-one Čech cochain at the singleton `{i}`: its `i`-th coordinate as an
element of `M_{f_i}`. -/
abbrev cechComponentOne (i : Fin r) :
    Cech.cechTerm f (M : Type _) 1 →ₗ[R] Cech.cechMod f (M : Type _) {i} :=
  cechComponent f M 1 ⟨{i}, Finset.card_singleton i⟩

/-! ### The degree-one differential in coordinates -/

/-- **The component of `d¹ x` at a two-element set.** Only the two singletons contained in
`{a, b}` contribute, through the transition maps into `M_{f_a f_b}` and with the signs of the two
insertion orders. -/
theorem cechComponentTwo_cechD_one {a b : Fin r} (hab : a ≠ b)
    (x : Cech.cechTerm f (M : Type _) 1) :
    cechComponent f M 2 ⟨{a, b}, Finset.card_pair hab⟩ (Cech.cechD f (M : Type _) 1 x) =
      Cech.cechSign ({a} : Finset (Fin r)) b •
          Cech.cechι f (M : Type _) (Finset.singleton_subset_iff.2
            (Finset.mem_insert_self a {b})) (cechComponentOne f M a x) +
        Cech.cechSign ({b} : Finset (Fin r)) a •
          Cech.cechι f (M : Type _) (Finset.singleton_subset_iff.2
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))
            (cechComponentOne f M b x) := by
  refine DirectSum.induction_on x ?_ (fun s m => ?_) (fun u v hu hv => ?_)
  · simp only [map_zero, zsmul_zero, add_zero]
  on_goal 2 =>
    simp only [map_add, zsmul_add]
    rw [hu, hv]
    abel
  obtain ⟨S, hS⟩ := s
  obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hS
  rw [← DirectSum.lof_eq_of R, Cech.cechD_lof, map_sum]
  simp only [map_zsmul]
  have hjc : ∀ j : {x : Fin r // x ∈ ({c} : Finset (Fin r))ᶜ}, j.1 ≠ c :=
    fun j h => Finset.mem_compl.1 j.2 (Finset.mem_singleton.2 h)
  have hmem : ∀ j p q : Fin r, ({j, c} : Finset (Fin r)) = {p, q} →
      (j = p ∨ j = q) ∧ (c = p ∨ c = q) := fun j p q h =>
    ⟨by simpa using (Finset.ext_iff.1 h j).1 (by simp),
      by simpa using (Finset.ext_iff.1 h c).1 (by simp)⟩
  by_cases hca : c = a
  · subst hca
    rw [cechComponent_lof_of_eq f M _ _ rfl,
      cechComponent_lof_of_ne f M _ _ fun he => hab (Finset.singleton_inj.mp he)]
    simp only [map_zero, zsmul_zero, add_zero]
    refine (Finset.sum_eq_single_of_mem ⟨b, Finset.mem_compl.2 fun h =>
      hab (Finset.mem_singleton.1 h).symm⟩ (Finset.mem_attach _ _) fun j _ hj => ?_).trans ?_
    · rw [cechComponent_lof_of_ne f M _ _ ?_, zsmul_zero]
      exact fun he => hj (Subtype.ext ((hmem j.1 c b he).1.resolve_left (hjc j)))
    · rw [cechComponent_lof_of_eq f M _ _ (Finset.pair_comm b c)]
      simp only [Cech.cechι_cechι]
  by_cases hcb : c = b
  · subst hcb
    rw [cechComponent_lof_of_ne f M _ _ fun he => hca (Finset.singleton_inj.mp he),
      cechComponent_lof_of_eq f M _ _ rfl]
    simp only [map_zero, zsmul_zero, zero_add]
    refine (Finset.sum_eq_single_of_mem ⟨a, Finset.mem_compl.2 fun h =>
      hca (Finset.mem_singleton.1 h).symm⟩ (Finset.mem_attach _ _) fun j _ hj => ?_).trans ?_
    · rw [cechComponent_lof_of_ne f M _ _ ?_, zsmul_zero]
      exact fun he => hj (Subtype.ext ((hmem j.1 a c he).1.resolve_right (hjc j)))
    · rw [cechComponent_lof_of_eq f M _ _ rfl]
      simp only [Cech.cechι_cechι]
  rw [cechComponent_lof_of_ne f M _ _ fun he => hca (Finset.singleton_inj.mp he),
    cechComponent_lof_of_ne f M _ _ fun he => hcb (Finset.singleton_inj.mp he)]
  simp only [map_zero, zsmul_zero, add_zero]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [cechComponent_lof_of_ne f M _ _ ?_, zsmul_zero]
  exact fun he => ((hmem j.1 a b he).2).elim hca hcb

/-! ### The kernel -/

/-- The one-element subsets of `Fin r` are the elements of `Fin r`. -/
def cardOneEquiv (r : ℕ) : {s : Finset (Fin r) // s.card = 1} ≃ Fin r where
  toFun s := (Finset.card_eq_one.mp s.2).choose
  invFun i := ⟨{i}, Finset.card_singleton i⟩
  left_inv s := Subtype.ext (Finset.card_eq_one.mp s.2).choose_spec.symm
  right_inv i :=
    (Finset.singleton_inj.mp (Finset.card_eq_one.mp (Finset.card_singleton i)).choose_spec).symm

/-- **`C¹ ≅ ∏ i, M_{f_i}`.** The degree-one term of the Čech complex, written as the product of
the localizations at the individual elements. -/
def cechTermOneEquiv :
    Cech.cechTerm f (M : Type _) 1 ≃ₗ[R] ∀ i : Fin r, Cech.cechMod f (M : Type _) {i} :=
  (DirectSum.linearEquivFunOnFintype R {s : Finset (Fin r) // s.card = 1}
      (fun s => Cech.cechMod f (M : Type _) s.1)).trans
    (LinearEquiv.piCongrLeft' R (fun s : {s : Finset (Fin r) // s.card = 1} =>
      Cech.cechMod f (M : Type _) s.1) (cardOneEquiv r))

/-- The coordinate of `cechTermOneEquiv f M x` at `i` is the component of `x` at the singleton
`{i}`. -/
@[simp]
theorem cechTermOneEquiv_apply (x : Cech.cechTerm f (M : Type _) 1) (i : Fin r) :
    cechTermOneEquiv f M x i = cechComponentOne f M i x :=
  rfl

/-- **The degree-one cocycle condition is Čech compatibility.** A degree-one Čech cochain is
killed by the differential exactly when the images of its coordinates in every further
localization agree: the component of `d¹ x` at a two-element set is the difference of the two
images, up to the common sign. -/
theorem mem_ker_cechD_one_iff (x : Cech.cechTerm f (M : Type _) 1) :
    x ∈ LinearMap.ker (Cech.cechD f (M : Type _) 1) ↔
      cechTermOneEquiv f M x ∈ cechCompatible f M := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hx
    have pair : ∀ (a b : Fin r) (hab : a ≠ b),
        Cech.cechι f (M : Type _) (Finset.singleton_subset_iff.2
            (Finset.mem_insert_self a {b})) (cechComponentOne f M a x) =
          Cech.cechι f (M : Type _) (Finset.singleton_subset_iff.2
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)))
            (cechComponentOne f M b x) := fun a b hab =>
      eq_of_zsmul_add_zsmul_eq_zero (cechSign_singleton_add_cechSign_singleton hab)
        (cechSign_mul_self _ _) (by rw [← cechComponentTwo_cechD_one f M hab x, hx, map_zero])
    intro a b t ha hb
    simp only [cechTermOneEquiv_apply]
    obtain rfl | hab := eq_or_ne a b
    · rfl
    have hsub : ({a, b} : Finset (Fin r)) ⊆ t :=
      Finset.insert_subset ha (Finset.singleton_subset_iff.2 hb)
    rw [← Cech.cechι_cechι f (M : Type _) (Finset.singleton_subset_iff.2
        (Finset.mem_insert_self a {b})) hsub,
      ← Cech.cechι_cechι f (M : Type _) (Finset.singleton_subset_iff.2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))) hsub,
      pair a b hab]
  · intro hx
    refine DirectSum.ext_component R fun t => ?_
    rw [map_zero]
    obtain ⟨T, hT⟩ := t
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hT
    have h := hx a b {a, b} (Finset.mem_insert_self a {b})
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    simp only [cechTermOneEquiv_apply] at h
    refine (cechComponentTwo_cechD_one f M hab x).trans ?_
    rw [h, ← add_smul, cechSign_singleton_add_cechSign_singleton hab, zero_smul]

/-- **The degree-one cocycles of the Čech complex are the Čech compatible families.** -/
def kerCechDOneEquivCechCompatible :
    LinearMap.ker (Cech.cechD f (M : Type _) 1) ≃ₗ[R] cechCompatible f M where
  toFun x := ⟨cechTermOneEquiv f M x.1, (mem_ker_cechD_one_iff f M x.1).1 x.2⟩
  map_add' x y := Subtype.ext (map_add (cechTermOneEquiv f M) x.1 y.1)
  map_smul' c x := Subtype.ext (map_smul (cechTermOneEquiv f M) c x.1)
  invFun y := ⟨(cechTermOneEquiv f M).symm y.1,
    (mem_ker_cechD_one_iff f M _).2 (by simp)⟩
  left_inv x := Subtype.ext ((cechTermOneEquiv f M).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((cechTermOneEquiv f M).apply_symm_apply y.1)

end Stacks.LocalCohomology

end
