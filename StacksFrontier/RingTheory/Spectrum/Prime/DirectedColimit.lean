module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.RingTheory.MvPolynomial.DirectedColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible sets over a directed colimit of rings

Let `(G i)` be a directed system of commutative rings with colimit `A`.  A constructible subset of
`Spec (G i)` is cut out by finitely many elements of `G i`, and whether it is empty is a finite
algebraic condition — radical membership in a finitely generated ideal.  Since both the elements
and the certificate of membership live at a finite stage, emptiness of such a set after pulling
back to `Spec A` is already visible at a finite stage:

* `PrimeSpectrum.exists_ge_preimage_eq_empty_of_isConstructible_of_directed`: a constructible
  subset of `Spec (G i)` whose preimage in `Spec A` is empty has empty preimage in `Spec (G j)`
  for some `j ≥ i`.

Together with Chevalley's theorem this descends surjectivity on spectra from the colimit to a
stage, which is the affine case of the limit argument of Stacks 07RR:

* `PrimeSpectrum.exists_ge_range_comap_subset_range_comap_of_directed`: if `G i → C` is of finite
  presentation and `Spec D → Spec A` is surjective for a ring `D` receiving compatible maps from
  `A` and from `C`, then at some stage `j ≥ i` the whole of `Spec (G j)` maps into the image of
  `Spec C → Spec (G i)`.
* `PrimeSpectrum.exists_ge_surjective_comap_tensorProduct_of_directed`: hence
  `Spec (G j ⊗_{G i} C) → Spec (G j)` is surjective at that stage.

The second step uses that the image of a base change is the preimage of the image, which is proved
here in the generality in which it is true:

* `PrimeSpectrum.mem_range_comap_tensorProduct_of_mem_range_comap`: a prime of `T` whose
  contraction to `R` is in the image of `Spec S → Spec R` is in the image of
  `Spec (T ⊗[R] S) → Spec T`.

## Main results

* `PrimeSpectrum.BasicConstructibleSetData.toSet_eq_empty_iff`: a basic constructible set
  `V(g₁, …, gₙ) ∖ V(f)` is empty exactly when `f` lies in the radical of `(g₁, …, gₙ)`.
* `PrimeSpectrum.exists_ge_preimage_eq_empty_of_isConstructible_of_directed`.
* `PrimeSpectrum.mem_range_comap_tensorProduct_of_mem_range_comap`.
* `PrimeSpectrum.surjective_comap_algebraMap_of_algEquiv`.
* `PrimeSpectrum.exists_ge_range_comap_subset_range_comap_of_directed`.
* `PrimeSpectrum.exists_ge_surjective_comap_tensorProduct_of_directed`.

## Implementation notes

The finite data describing a constructible subset of a spectrum is Mathlib's
`PrimeSpectrum.ConstructibleSetData`, a `Finset` of tuples `(f, g₁, …, gₙ)`; it is functorial for
*preimages* (`PrimeSpectrum.ConstructibleSetData.toSet_map`), which is exactly what is needed here.
The descent of the emptiness certificate is `Ring.exists_ge_mem_radical_span_range_of_directed`,
and the pass from one stage to a later one is monotone because the data at the later stage is the
image of the data at the earlier one, so its set is a further preimage of the empty set.

The hypothesis on the colimit side is deliberately phrased with the ring `D` and the two maps into
it, rather than with a base change: in Stacks 07SQ the ring `D` is the coordinate ring `B` of the
étale chart over the limit, `C` is its model `B_i` at a stage, and the square commutes by
construction, whereas `B` is only *isomorphic* to `A ⊗_{G i} B_i`.

The base-change half, `mem_range_comap_tensorProduct_of_mem_range_comap`, is the fibre criterion
`PrimeSpectrum.nontrivial_iff_mem_rangeComap` read on both sides: it turns both memberships into
non-vanishing of a residue-field fibre, and then two applications of
`Algebra.TensorProduct.cancelBaseChange` identify
`κ(q) ⊗[T] (T ⊗[R] S) ≅ κ(q) ⊗[R] S ≅ κ(q) ⊗[κ(p)] (κ(p) ⊗[R] S)`, where `p` is the contraction of
`q`.  The `κ(p)`-algebra structure on `κ(q)` is `Ideal.ResidueField.mapₐ`, which is an `R`-algebra
map, so the tower `R → κ(p) → κ(q)` is `IsScalarTower.of_algebraMap_eq` applied to its `commutes`
field; and `κ(p) → κ(q)` is an extension of fields, hence free and faithfully flat, so the last
tensor factor cannot kill a nonzero module (`Module.FaithfullyFlat.lTensor_nontrivial`).  No
hypothesis of finite presentation or flatness is needed for this half.

## References

* [Stacks Project, Tag 07RR](https://stacks.math.columbia.edu/tag/07RR)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public section

universe u v w

open TensorProduct

namespace PrimeSpectrum

/-! ### Emptiness of a basic constructible set -/

/-- **A basic constructible set is empty exactly when its defining element is in the radical of
its defining ideal.**  The basic constructible set of a tuple `(f, g₁, …, gₙ)` is
`V(g₁, …, gₙ) ∖ V(f)`, which is empty exactly when every prime containing `g₁, …, gₙ` contains
`f`, that is, when `f` lies in the radical of the ideal they generate. -/
theorem BasicConstructibleSetData.toSet_eq_empty_iff {R : Type u} [CommRing R]
    (C : BasicConstructibleSetData R) :
    C.toSet = ∅ ↔ C.f ∈ (Ideal.span (Set.range C.g)).radical := by
  rw [BasicConstructibleSetData.toSet, Set.sdiff_eq_empty, ← zeroLocus_span (Set.range C.g),
    ← zeroLocus_span {C.f}, zeroLocus_subset_zeroLocus_iff, Ideal.span_le,
    Set.singleton_subset_iff, SetLike.mem_coe]

/-! ### Descending emptiness along a directed colimit -/

variable {ι : Type u} [Preorder ι] {G : ι → Type v} [∀ i, CommRing (G i)]
  {f : ∀ i j, i ≤ j → G i →+* G j} {A : Type w} [CommRing A] {φ : ∀ i, G i →+* A}

/-- **A constructible set which becomes empty over a directed colimit is already empty at a
stage.**  Let `(G i)` be a directed system of rings with colimit `A`, presented by a jointly
surjective compatible family `φ` whose kernels are exhausted at later stages, and let `Z` be a
constructible subset of `Spec (G i)` whose preimage in `Spec A` is empty.  Then the preimage of `Z`
in `Spec (G j)` is empty for some `j ≥ i`. -/
@[ega "IV 8.3.3" "special case"]
theorem exists_ge_preimage_eq_empty_of_isConstructible_of_directed [IsDirectedOrder ι]
    [DirectedSystem G fun i j h ↦ f i j h]
    (hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x)
    (hsurj : ∀ a : A, ∃ (i : ι) (x : G i), φ i x = a)
    (hzero : ∀ (i : ι) (x : G i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    {i : ι} {Z : Set (PrimeSpectrum (G i))} (hZ : Topology.IsConstructible Z)
    (hempty : comap (φ i) ⁻¹' Z = ∅) :
    ∃ (j : ι) (h : i ≤ j), comap (f i j h) ⁻¹' Z = ∅ := by
  classical
  have : Nonempty ι := ⟨i⟩
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hZ
  -- At the colimit every basic piece of the data is empty, so its defining element is in the
  -- radical of its defining ideal.
  have hbasic : ∀ C ∈ S, ∃ (j : ι) (h : i ≤ j), (C.map (f i j h)).toSet = ∅ := by
    intro C hC
    have h0 : (C.map (φ i)).toSet = ∅ := by
      rw [← Set.subset_empty_iff, ← hempty]
      refine Set.Subset.trans ?_ (Set.preimage_mono (Set.subset_biUnion_of_mem hC))
      rw [BasicConstructibleSetData.toSet_map]
    rw [BasicConstructibleSetData.toSet_eq_empty_iff] at h0
    obtain ⟨j, hij, hj⟩ := Ring.exists_ge_mem_radical_span_range_of_directed hφ hsurj hzero
      C.g C.f h0
    exact ⟨j, hij, by rw [BasicConstructibleSetData.toSet_eq_empty_iff]; exact hj⟩
  -- Choose a single stage dominating the finitely many stages so obtained.
  choose! jj hjj hjj' using hbasic
  obtain ⟨m, hm⟩ := Finset.exists_le (insert i (S.image jj))
  have him : i ≤ m := hm i (Finset.mem_insert_self _ _)
  refine ⟨m, him, ?_⟩
  rw [ConstructibleSetData.toSet]
  simp only [Set.preimage_iUnion]
  refine Set.iUnion_eq_empty.mpr fun C ↦ Set.iUnion_eq_empty.mpr fun hC ↦ ?_
  have hjm : jj C ≤ m := hm (jj C) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jj hC))
  -- The data at stage `m` is the image of the data at stage `jj C`, so its set is empty too.
  rw [← BasicConstructibleSetData.toSet_map,
    show f i m him = (f (jj C) m hjm).comp (f i (jj C) (hjj C hC)) from
      RingHom.ext fun x ↦ (DirectedSystem.map_map' f (hjj C hC) hjm x).symm,
    BasicConstructibleSetData.map_comp, BasicConstructibleSetData.toSet_map, hjj' C hC,
    Set.preimage_empty]

/-! ### Descending surjectivity on spectra -/

/-- **Surjectivity on spectra over a directed colimit descends to a stage.**  Let `(G i)` be a
directed system of rings with colimit `A`, let `ψ : G i → C` be of finite presentation, and let `D`
be a ring with ring maps `χ : A → D` and `θ : C → D` making the square with `φ i` and `ψ` commute.
If `Spec D → Spec A` is surjective, then at some stage `j ≥ i` the image of `Spec (G j)` in
`Spec (G i)` lies inside the image of `Spec C`.

This is the affine case of the limit argument of Stacks 07RR: the image of `Spec C` is
constructible by Chevalley's theorem, surjectivity over the colimit says that its complement pulls
back to the empty set in `Spec A`, and `exists_ge_preimage_eq_empty_of_isConstructible_of_directed`
makes the complement pull back to the empty set already at a stage. -/
theorem exists_ge_range_comap_subset_range_comap_of_directed [IsDirectedOrder ι]
    [DirectedSystem G fun i j h ↦ f i j h]
    (hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x)
    (hsurj : ∀ a : A, ∃ (i : ι) (x : G i), φ i x = a)
    (hzero : ∀ (i : ι) (x : G i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    {i : ι} {C : Type*} [CommRing C] {ψ : G i →+* C} (hψ : ψ.FinitePresentation)
    {D : Type*} [CommRing D] (χ : A →+* D) (θ : C →+* D)
    (hcomm : χ.comp (φ i) = θ.comp ψ)
    (hD : Function.Surjective (comap χ)) :
    ∃ (j : ι) (h : i ≤ j),
      Set.range (comap (f i j h)) ⊆ Set.range (comap ψ) := by
  have hc : Topology.IsConstructible ((Set.range (comap ψ))ᶜ) :=
    (isConstructible_range_comap hψ).compl
  have hempty : comap (φ i) ⁻¹' (Set.range (comap ψ))ᶜ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun p hp ↦ hp ?_
    obtain ⟨r, rfl⟩ := hD p
    exact ⟨comap θ r, by
      rw [← comap_comp_apply, ← comap_comp_apply, ← hcomm]⟩
  obtain ⟨j, hij, hj⟩ :=
    exists_ge_preimage_eq_empty_of_isConstructible_of_directed hφ hsurj hzero hc hempty
  refine ⟨j, hij, fun p hp ↦ ?_⟩
  by_contra hnot
  obtain ⟨q, rfl⟩ := hp
  exact absurd (show q ∈ comap (f i j hij) ⁻¹' (Set.range (comap ψ))ᶜ from hnot)
    (hj ▸ Set.notMem_empty q)

/-! ### The image of a base change is the preimage of the image -/

omit [Preorder ι] in
/-- **Surjectivity on spectra is transported along an algebra isomorphism.**  If
`Spec B → Spec R` is surjective and `B` and `B'` are isomorphic as `R`-algebras, then
`Spec B' → Spec R` is surjective. -/
theorem surjective_comap_algebraMap_of_algEquiv {R B B' : Type*} [CommRing R] [CommRing B]
    [CommRing B'] [Algebra R B] [Algebra R B'] (e : B ≃ₐ[R] B')
    (h : Function.Surjective (comap (algebraMap R B))) :
    Function.Surjective (comap (algebraMap R B')) := by
  intro p
  obtain ⟨x, hx⟩ := h p
  refine ⟨comap (e.symm : B' →+* B) x, ?_⟩
  rw [← comap_comp_apply, show ((e.symm : B' →+* B).comp (algebraMap R B')) = algebraMap R B from
    RingHom.ext fun r ↦ by simp]
  exact hx

omit [Preorder ι] in
/-- **A prime lying over a prime in the image of `Spec S → Spec R` is in the image of the base
change.**  For `R`-algebras `S` and `T` and a prime `q` of `T` whose contraction to `R` lies in the
image of `Spec S → Spec R`, the prime `q` itself lies in the image of
`Spec (T ⊗[R] S) → Spec T`.

Equivalently: the image of `Spec (T ⊗[R] S) → Spec T` is the preimage of the image of
`Spec S → Spec R`, the inclusion `⊆` being automatic.  Both memberships are read through the fibre
criterion `PrimeSpectrum.nontrivial_iff_mem_rangeComap`; see the module docstring. -/
theorem mem_range_comap_tensorProduct_of_mem_range_comap {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (q : PrimeSpectrum T)
    (hq : comap (algebraMap R T) q ∈ Set.range (comap (algebraMap R S))) :
    q ∈ Set.range (comap (algebraMap T (T ⊗[R] S))) := by
  classical
  set p := comap (algebraMap R T) q with hp
  rw [← PrimeSpectrum.nontrivial_iff_mem_rangeComap] at hq ⊢
  have hf : p.asIdeal = q.asIdeal.comap (algebraMap R T) := by rw [hp, comap_asIdeal]
  -- The residue field of `q` is an extension of the residue field of `p`, over `R`.
  let e : p.asIdeal.ResidueField →ₐ[R] q.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal (Algebra.ofId R T) hf
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField := e.toRingHom.toAlgebra
  have _ : IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (e.commutes x).symm
  -- An extension of fields is free, hence faithfully flat.
  have _ : Module.Free p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    Module.Free.of_divisionRing _ _
  have _ : Module.FaithfullyFlat p.asIdeal.ResidueField q.asIdeal.ResidueField := inferInstance
  have _ := hq
  -- `κ(q) ⊗[T] (T ⊗[R] S) ≅ κ(q) ⊗[R] S ≅ κ(q) ⊗[κ(p)] (κ(p) ⊗[R] S)`.
  have e₁ := (Algebra.TensorProduct.cancelBaseChange R T T q.asIdeal.ResidueField S).toEquiv
  have e₂ := (Algebra.TensorProduct.cancelBaseChange R p.asIdeal.ResidueField
    p.asIdeal.ResidueField q.asIdeal.ResidueField S).toEquiv
  rw [e₁.nontrivial_congr, ← e₂.nontrivial_congr]
  infer_instance

/-- **Surjectivity on spectra descends to a stage, for the base change at that stage.**  Let
`(G i)` be a directed system of rings with colimit `A`, let `C` be a `G i`-algebra whose structure
map is of finite presentation, and let `D` be a ring with ring maps `χ : A → D` and `θ : C → D`
making the square with `φ i` and `algebraMap (G i) C` commute.  If `Spec D → Spec A` is surjective,
then `Spec (G j ⊗_{G i} C) → Spec (G j)` is surjective for some `j ≥ i`.

This is the affine, ring-theoretic form of Stacks 07RR as Stacks 07SQ consumes it: `D` is the
coordinate ring of the étale chart over the limit and `C` its model at the stage `i`. -/
theorem exists_ge_surjective_comap_tensorProduct_of_directed [IsDirectedOrder ι]
    [DirectedSystem G fun i j h ↦ f i j h]
    (hφ : ∀ i j (h : i ≤ j) (x : G i), φ j (f i j h x) = φ i x)
    (hsurj : ∀ a : A, ∃ (i : ι) (x : G i), φ i x = a)
    (hzero : ∀ (i : ι) (x : G i), φ i x = 0 → ∃ (j : ι) (h : i ≤ j), f i j h x = 0)
    {i : ι} {C : Type*} [CommRing C] [Algebra (G i) C]
    (hC : (algebraMap (G i) C).FinitePresentation)
    {D : Type*} [CommRing D] (χ : A →+* D) (θ : C →+* D)
    (hcomm : χ.comp (φ i) = θ.comp (algebraMap (G i) C))
    (hD : Function.Surjective (comap χ)) :
    ∃ (j : ι) (h : i ≤ j),
      letI := (f i j h).toAlgebra
      Function.Surjective (comap (algebraMap (G j) (G j ⊗[G i] C))) := by
  obtain ⟨j, hij, hsub⟩ :=
    exists_ge_range_comap_subset_range_comap_of_directed hφ hsurj hzero hC χ θ hcomm hD
  refine ⟨j, hij, ?_⟩
  let _ := (f i j hij).toAlgebra
  intro q
  refine mem_range_comap_tensorProduct_of_mem_range_comap q ?_
  rw [RingHom.algebraMap_toAlgebra]
  exact hsub ⟨q, rfl⟩

end PrimeSpectrum

end
