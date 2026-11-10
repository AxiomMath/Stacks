module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Order.Filter.Pi
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.NhdsWithin
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalProperties
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut

/-!
# Finite products of taut maps of topological finite type

The conjunction of tautness and being topologically of finite type is stable under finite
products of targets: if each `f i : B →+* A i` is taut and topologically of finite type, then so
is the induced map `B →+* ∀ i, A i` for the product ring and product topology.

## Main results

* `TopologicalRing.tautAndFiniteType_finiteProductPreserves`: the finite-product axiom of
  Situation 0CBA for the property "taut and topologically of finite type".

## References

* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
-/

@[expose] public section

namespace TopologicalRing

section

/-- The underlying set of `Ideal.pi J` is the product of the underlying sets of the `J i`. -/
private theorem coe_ideal_pi {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)]
    (J : ∀ i, Ideal (A i)) :
    (Ideal.pi J : Set (∀ i, A i)) = Set.univ.pi fun i ↦ (J i : Set (A i)) := by
  ext x
  simp only [Set.mem_univ_pi, SetLike.mem_coe]
  exact Iff.rfl

/-- Multiplying the extension of an element of the base by the idempotent-like element
`Pi.single i 1` isolates the `i`-th component. -/
private theorem single_eq_single_one_mul {ι : Type*} [DecidableEq ι] {B : Type*} {A : ι → Type*}
    [CommRing B] [∀ i, CommRing (A i)] (f : ∀ i, B →+* A i) (i : ι) (b : B) :
    Pi.single i (f i b) = Pi.single i (1 : A i) * RingHom.pi f b := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

/-- The set of elements of a factor whose `Pi.single` image lies in a given ideal of the product
is an ideal of that factor. -/
private def singlePreimageIdeal {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] (K : Ideal (∀ i, A i)) (i : ι) : Ideal (A i) where
  carrier := {a : A i | Pi.single i a ∈ K}
  zero_mem' := by
    change Pi.single i (0 : A i) ∈ K
    rw [Pi.single_zero]
    exact K.zero_mem
  add_mem' {a b} ha hb := by
    change Pi.single i (a + b) ∈ K
    rw [Pi.single_add]
    exact K.add_mem ha hb
  smul_mem' c a ha := by
    change Pi.single i (c • a) ∈ K
    rw [smul_eq_mul, Pi.single_mul]
    exact K.mul_mem_left (Pi.single i c) ha

/-- The extension of an ideal of the base along the product map is the product of its extensions
along the factor maps. -/
private theorem map_pi_eq_ideal_pi {ι : Type*} [Finite ι] {B : Type*}
    {A : ι → Type*} [CommRing B] [∀ i, CommRing (A i)] (f : ∀ i, B →+* A i) (I : Ideal B) :
    Ideal.map (RingHom.pi f) I = Ideal.pi fun i ↦ Ideal.map (f i) I := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun b hb i ↦ ?_
    exact Ideal.mem_map_of_mem (f i) hb
  · intro x hx
    have hsingle (i : ι) : Ideal.map (f i) I ≤
        singlePreimageIdeal (Ideal.map (RingHom.pi f) I) i := by
      refine Ideal.map_le_iff_le_comap.mpr fun b hb ↦ ?_
      change Pi.single i (f i b) ∈ Ideal.map (RingHom.pi f) I
      rw [single_eq_single_one_mul f i b]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hb)
    rw [← Finset.univ_sum_single x]
    exact Ideal.sum_mem _ fun i _ ↦ hsingle i (hx i)

/-- The closure of a product ideal is the product of the closures. -/
private theorem closure_pi_ideal {ι : Type*} {A : ι → Type*} [∀ i, CommRing (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)] (J : ∀ i, Ideal (A i)) :
    Ideal.closure (Ideal.pi J) = Ideal.pi fun i ↦ Ideal.closure (J i) := by
  apply SetLike.ext'
  rw [Ideal.coe_closure, coe_ideal_pi, coe_ideal_pi, closure_pi_set]
  simp only [Ideal.coe_closure]

/-- The underlying set of the closed extension of an ideal of the base along the product map. -/
private theorem coe_closure_map_pi {ι : Type*} [Finite ι] {B : Type*}
    {A : ι → Type*} [CommRing B] [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)] (f : ∀ i, B →+* A i) (I : Ideal B) :
    (Ideal.closure (Ideal.map (RingHom.pi f) I) : Set (∀ i, A i)) =
      Set.univ.pi fun i ↦ (Ideal.closure (Ideal.map (f i) I) : Set (A i)) := by
  rw [map_pi_eq_ideal_pi, closure_pi_ideal, coe_ideal_pi]

end

section

/-- A finite product of taut maps out of a common base is taut. -/
private theorem isTaut_pi {ι : Type*} [Finite ι] {B : Type*} {A : ι → Type*}
    [CommRing B] [TopologicalSpace B] [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)] (f : ∀ i, B →+* A i) (hf : ∀ i, RingHom.IsTaut (f i)) :
    RingHom.IsTaut (RingHom.pi f) := by
  classical
  have hopen (I : Ideal B) (hI : IsOpen (I : Set B)) :
      IsOpen (Ideal.closure (Ideal.map (RingHom.pi f) I) : Set (∀ i, A i)) := by
    rw [coe_closure_map_pi]
    exact isOpen_set_pi Set.finite_univ fun i _ ↦ (hf i).1 I hI
  refine ⟨hopen, ⟨fun U ↦ ⟨fun hU ↦ ?_, ?_⟩⟩⟩
  · rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨S, -, t, ht, htU⟩ := hU
    choose I hIopen hIt using fun i ↦ ((hf i).2.mem_iff.mp (ht i))
    refine ⟨⨅ i, I i, ?_, ?_⟩
    · rw [Submodule.coe_iInf]
      exact isOpen_iInter_of_finite hIopen
    · refine Set.Subset.trans ?_ htU
      rw [coe_closure_map_pi]
      refine Set.pi_mono' (fun i _ ↦ Set.Subset.trans ?_ (hIt i)) (Set.subset_univ S)
      simpa only [Ideal.coe_closure] using
        closure_mono (Ideal.map_mono (iInf_le I i))
  · rintro ⟨I, hI, hIU⟩
    exact Filter.mem_of_superset
      (((hopen I hI).mem_nhds (Ideal.zero_mem _))) hIU

end

section

/-- The subring of a factor consisting of the elements whose `Pi.single` image lies in the range
of a given homomorphism into the product, given that the `i`-th unit vector is in that range. -/
private def singlePreimageSubring {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] {P : Type*} [CommRing P] (H : P →+* ∀ i, A i) (i : ι)
    (h1 : Pi.single i (1 : A i) ∈ H.range) : Subring (A i) where
  carrier := {a : A i | Pi.single i a ∈ H.range}
  zero_mem' := by
    change Pi.single i (0 : A i) ∈ H.range
    rw [Pi.single_zero]
    exact H.range.zero_mem
  one_mem' := h1
  add_mem' {a b} ha hb := by
    change Pi.single i (a + b) ∈ H.range
    rw [Pi.single_add]
    exact H.range.add_mem ha hb
  mul_mem' {a b} ha hb := by
    change Pi.single i (a * b) ∈ H.range
    rw [Pi.single_mul]
    exact H.range.mul_mem ha hb
  neg_mem' {a} ha := by
    change Pi.single i (-a) ∈ H.range
    rw [Pi.single_neg]
    exact H.range.neg_mem ha

/-- Membership in `singlePreimageSubring` says that the `Pi.single` image is in the range. -/
private theorem mem_singlePreimageSubring {ι : Type*} [DecidableEq ι] {A : ι → Type*}
    [∀ i, CommRing (A i)] {P : Type*} [CommRing P] (H : P →+* ∀ i, A i) (i : ι)
    (h1 : Pi.single i (1 : A i) ∈ H.range) (a : A i) :
    a ∈ singlePreimageSubring H i h1 ↔ Pi.single i a ∈ H.range := Iff.rfl

/-- Prescribing the image of the base ring and the image of each variable determines a ring
homomorphism out of a multivariate polynomial algebra. -/
private theorem exists_ringHom_mvPolynomial {σ B S : Type*} [CommSemiring B] [CommSemiring S]
    (φ : B →+* S) (v : σ → S) :
    ∃ H : MvPolynomial σ B →+* S,
      (∀ b, H (MvPolynomial.C b) = φ b) ∧ ∀ s, H (MvPolynomial.X s) = v s :=
  ⟨MvPolynomial.eval₂Hom φ v, MvPolynomial.eval₂Hom_C φ v, MvPolynomial.eval₂Hom_X' φ v⟩

/-- A presentation with dense image by a polynomial algebra in finitely many variables indexed by
an arbitrary finite type can be re-indexed by `Fin n`. -/
private theorem isTopologicallyOfFiniteType_of_finite {B C : Type*} [CommRing B] [CommRing C]
    [TopologicalSpace C] {τ : Type*} [Finite τ] (φ : B →+* C) (F : MvPolynomial τ B →+* C)
    (hFC : F.comp MvPolynomial.C = φ) (hF : DenseRange F) :
    TopologicalRing.IsTopologicallyOfFiniteType φ := by
  classical
  have : Fintype τ := Fintype.ofFinite τ
  set E := MvPolynomial.renameEquiv B (Fintype.equivFin τ).symm with hE
  refine ⟨Fintype.card τ, F.comp (E : MvPolynomial (Fin (Fintype.card τ)) B →+* _), ?_, ?_⟩
  · ext b
    change F (E (MvPolynomial.C b)) = φ b
    rw [show E (MvPolynomial.C b) = MvPolynomial.C b from by simp [hE]]
    exact DFunLike.congr_fun hFC b
  · rw [denseRange_iff_closure_range,
      show Set.range (F.comp (E : MvPolynomial (Fin (Fintype.card τ)) B →+* _)) =
          Set.range F from by
        rw [RingHom.coe_comp]
        exact E.surjective.range_comp F]
    exact denseRange_iff_closure_range.mp hF

/-- A finite product of maps that are topologically of finite type over a common base is
topologically of finite type. -/
private theorem isTopologicallyOfFiniteType_pi {ι : Type*} [Finite ι] {B : Type*}
    {A : ι → Type*} [CommRing B] [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    (f : ∀ i, B →+* A i)
    (hf : ∀ i, TopologicalRing.IsTopologicallyOfFiniteType (f i)) :
    TopologicalRing.IsTopologicallyOfFiniteType (RingHom.pi f) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose n g hgC hgdense using hf
  obtain ⟨H, hHC, hHX⟩ := exists_ringHom_mvPolynomial (RingHom.pi f)
    (Sum.elim (fun p : (i : ι) × Fin (n i) ↦ Pi.single p.1 (g p.1 (MvPolynomial.X p.2)))
      (fun i : ι ↦ Pi.single i (1 : A i)))
  have hHXl (i : ι) (k : Fin (n i)) :
      H (MvPolynomial.X (Sum.inl ⟨i, k⟩)) = Pi.single i (g i (MvPolynomial.X k)) :=
    hHX (Sum.inl ⟨i, k⟩)
  have hHXr (i : ι) : H (MvPolynomial.X (Sum.inr i)) = Pi.single i (1 : A i) :=
    hHX (Sum.inr i)
  have hone (i : ι) : Pi.single i (1 : A i) ∈ H.range :=
    ⟨MvPolynomial.X (Sum.inr i), hHXr i⟩
  have hgmem (i : ι) (p : MvPolynomial (Fin (n i)) B) :
      g i p ∈ singlePreimageSubring H i (hone i) := by
    induction p using MvPolynomial.induction_on with
    | C b =>
      rw [mem_singlePreimageSubring,
        show g i (MvPolynomial.C b) = f i b from DFunLike.congr_fun (hgC i) b,
        single_eq_single_one_mul f i b]
      exact H.range.mul_mem (hone i) ⟨MvPolynomial.C b, hHC b⟩
    | add p q hp hq => simpa only [map_add] using
        (singlePreimageSubring H i (hone i)).add_mem hp hq
    | mul_X p k hp =>
      have hX : g i (MvPolynomial.X k) ∈ singlePreimageSubring H i (hone i) :=
        (mem_singlePreimageSubring H i (hone i) _).mpr
          ⟨MvPolynomial.X (Sum.inl ⟨i, k⟩), hHXl i k⟩
      simpa only [map_mul] using (singlePreimageSubring H i (hone i)).mul_mem hp hX
  have hsub : (Set.univ.pi fun i ↦ Set.range (g i)) ⊆ Set.range H := by
    intro x hx
    rw [← Finset.univ_sum_single x]
    refine H.range.sum_mem fun i _ ↦ ?_
    obtain ⟨p, hp⟩ := hx i (Set.mem_univ i)
    rw [← hp]
    exact (mem_singlePreimageSubring H i (hone i) _).mp (hgmem i p)
  have hclosure : closure (Set.univ.pi fun i ↦ Set.range (g i)) =
      (Set.univ : Set (∀ i, A i)) := by
    rw [closure_pi_set]
    refine Set.eq_univ_of_forall fun x i _ ↦ ?_
    change x i ∈ closure (Set.range (g i))
    rw [(hgdense i).closure_range]
    exact Set.mem_univ _
  refine isTopologicallyOfFiniteType_of_finite (RingHom.pi f) H (RingHom.ext hHC) ?_
  rw [denseRange_iff_closure_range]
  exact Set.eq_univ_of_subset (closure_mono hsub) hclosure

end

section

universe u

/-- Tautness together with topological finite type is stable under finite products of targets:
this is the finite-product axiom of the local-property situation. -/
public theorem tautAndFiniteType_finiteProductPreserves :
    TopologicalRing.FiniteProductPreserves.{u} TopologicalRing.IsCountablyWeaklyAdmissible
      (fun φ ↦ RingHom.IsTaut φ ∧ TopologicalRing.IsTopologicallyOfFiniteType φ) := by
  intro B _ _ _ _ _hB _hBcount ι _ A _ _ _ _ _hA _hAcount f _hf _hCB _hCA hP
  exact ⟨isTaut_pi f fun i ↦ (hP i).1, isTopologicallyOfFiniteType_pi f fun i ↦ (hP i).2⟩

end

end TopologicalRing

end
