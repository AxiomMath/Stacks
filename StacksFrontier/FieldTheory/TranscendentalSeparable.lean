module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import StacksFrontier.FieldTheory.Separable.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Separable generation after a finite purely inseparable base change

Proof of [stacks, 04KM]: a finitely generated field extension `K/k` becomes separably generated
after a finite purely inseparable base change, the two new fields being realized inside a
prescribed perfect extension `Ω/K`.

## Main results

* `Stacks.FieldTheory.SeparatingBaseChange.solution`: the statement of Stacks Tag 04KM.

## Implementation notes

Both fields of the square are cut out by one finite set `T` of elements of the perfect closure
`perfectClosure k Ω` of `k` in `Ω`: the top field is `K' = K(T)` and the bottom one is
`k' = k(T)` formed inside `K'`, so `T` is the set of `p`-power roots of elements of `k` that the
source adjoins. With `T` in hand the four conditions on the square are formal: elements of
`perfectClosure k Ω` are integral over `k`, hence over `K`, so both adjunctions are finite
(`IntermediateField.finiteDimensional_adjoin`), and both lie below the relevant perfect closure,
so both are purely inseparable (`le_perfectClosure_iff`).

The content is the existence of `T`. The source runs an induction on the degree `[K : K_sep]` of
the inseparable part of `K` over a transcendence basis; that induction is replaced here by a
descent from the perfect closure `P = perfectClosure k Ω`, which is a perfect field
(`IntermediateField.perfectClosure.perfectField`) and so already carries the conclusion: the
compositum `M = P(K)` is finitely generated over `P`, hence has a separating transcendence basis
`s` by `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`. Only finitely much of `P`
is used by that datum — finitely many elements of `P` to put `s` inside `K(T)`, and finitely many
more to make a finite generating set of `K` separable over `k(T)(s)` — and collecting them gives
`T`.

The lemma that carries this descent is `exists_finset_subset_isSeparable_adjoin_union`:
separability of an element over `F(P ∪ V)`, for an arbitrary set `P`, already holds over
`F(T ∪ V)` for some finite `T ⊆ P`, because only the finitely many coefficients of one minimal
polynomial are used. It is assembled from `isSeparable_of_le_of_coeff_mem`, which descends
separability to a subfield containing those coefficients, and
`exists_finset_subset_forall_of_monotone`, which merges the finitely many finite witnesses so
obtained into a single one; that merging serves the two other places where finitely many elements
of `P` have to be collected as well.

The two fields of the square are nested (`k' : IntermediateField k ↥K'`) while the descent takes
place among intermediate fields of `Ω/k`; `IntermediateField.lift` bridges the two, and
`isSeparable_lift_iff` transports separability along it.

Two general facts about separability are proved here for want of a home upstream:
`isSeparable_of_mem_adjoin_union`, that adjoining elements separable over `A` to `A` creates no
inseparability, and `isSeparablyGenerated_of_algebraicIndependent`, that an algebraically
independent set over which the extension is separable is a separating transcendence basis in the
sense of [stacks, 030O](1).

## References

* [Stacks Project, Tag 04KM](https://stacks.math.columbia.edu/tag/04KM)
-/

@[expose] public section

namespace Stacks.FieldTheory.SeparatingBaseChange

open IntermediateField

/-- Finitely many finite witnesses inside `P` merge into one: if a property of finite subsets of
`P` is monotone and some witness has it for each index of a finite index set, then a single
witness has it for every index, namely the union of the witnesses. -/
private theorem exists_finset_subset_forall_of_monotone {α ι : Type*} {P : Set α}
    {p : Finset α → ι → Prop} (hp : ∀ {T T' : Finset α}, T ⊆ T' → ∀ i, p T i → p T' i)
    {s : Finset ι} (h : ∀ i ∈ s, ∃ T : Finset α, (T : Set α) ⊆ P ∧ p T i) :
    ∃ T : Finset α, (T : Set α) ⊆ P ∧ ∀ i ∈ s, p T i := by
  classical
  choose! T hTP hTp using h
  refine ⟨s.biUnion T, ?_, fun i hi ↦ hp (Finset.subset_biUnion_of_mem T hi) i (hTp i hi)⟩
  simp only [Finset.coe_biUnion, Set.iUnion_subset_iff]
  exact fun i hi ↦ hTP i (by simpa using hi)

section Ambient

variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]

/-- Separability over a subfield persists over a larger subfield of the same field. -/
private theorem isSeparable_of_le {A B : IntermediateField F Ω} (h : A ≤ B) {x : Ω}
    (hx : IsSeparable ↥A x) : IsSeparable ↥B x :=
  hx.tower_top (L := extendScalars h)

/-- Separability descends to a subfield containing the coefficients of the minimal polynomial. -/
private theorem isSeparable_of_le_of_coeff_mem {A B : IntermediateField F Ω} (h : A ≤ B) {x : Ω}
    (hx : IsSeparable ↥B x) (hco : ∀ i, (((minpoly ↥B x).coeff i : ↥B) : Ω) ∈ A) :
    IsSeparable ↥A x := by
  have hlift : minpoly ↥B x ∈ Polynomial.lifts (inclusion h : ↥A →+* ↥B) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n ↦ ⟨⟨_, hco n⟩, Subtype.ext rfl⟩
  obtain ⟨q, hq⟩ := hlift
  replace hq : Polynomial.map (inclusion h : ↥A →+* ↥B) q = minpoly ↥B x := hq
  have hsepq : q.Separable := by
    rw [← Polynomial.separable_map (inclusion h : ↥A →+* ↥B), hq]; exact hx
  have hcomp : (algebraMap ↥B Ω).comp (inclusion h : ↥A →+* ↥B) = algebraMap ↥A Ω :=
    RingHom.ext fun _ ↦ rfl
  refine hsepq.of_dvd (minpoly.dvd _ _ ?_)
  rw [Polynomial.aeval_def, ← hcomp, ← Polynomial.eval₂_map, hq]
  simpa [Polynomial.aeval_def] using minpoly.aeval ↥B x

/-- Adjoining elements separable over an intermediate field `A` creates no inseparability: every
element of `F(G ∪ A)` is separable over `A` as soon as every element of `G` is. -/
private theorem isSeparable_of_mem_adjoin_union (A : IntermediateField F Ω) {G : Set Ω}
    (hG : ∀ y ∈ G, IsSeparable ↥A y) {x : Ω} (hx : x ∈ adjoin F (G ∪ (A : Set Ω))) :
    IsSeparable ↥A x := by
  have h : adjoin F (G ∪ (A : Set Ω)) ≤ restrictScalars F (separableClosure ↥A Ω) :=
    adjoin_le_iff.mpr (Set.union_subset (fun y hy ↦ mem_separableClosure_iff.mpr (hG y hy))
      (le_restrictScalars_separableClosure A))
  exact mem_separableClosure_iff.mp (h hx)

/-- An algebraically independent set over which the extension is separable is a separating
transcendence basis, hence witnesses separable generation in the sense of [stacks, 030O](1). -/
private theorem isSeparablyGenerated_of_algebraicIndependent {σ : Set Ω}
    (hind : AlgebraicIndependent F ((↑) : σ → Ω)) (hsep : Algebra.IsSeparable ↥(adjoin F σ) Ω) :
    Algebra.IsSeparablyGenerated F Ω := by
  refine ⟨σ, hind.isTranscendenceBasis_iff_isAlgebraic.mpr ?_, hsep⟩
  rw [Subtype.range_coe, ← isAlgebraic_adjoin_iff_top]
  exact Algebra.IsSeparable.isAlgebraic ↥(adjoin F σ) Ω

/-- Enlarging the finite half of a two-part adjunction. -/
private theorem adjoin_union_mono_left {T T' : Finset Ω} (h : T ⊆ T') (V : Set Ω) :
    adjoin F ((T : Set Ω) ∪ V) ≤ adjoin F ((T' : Set Ω) ∪ V) :=
  adjoin.mono F _ _ (Set.union_subset_union_left V (by exact_mod_cast h))

/-- Only finitely many elements of `P` are needed: if `x` lies in the subextension of `Ω/F`
generated by `P ∪ V`, then it lies in the one generated by `T ∪ V` for some finite `T ⊆ P`. -/
private theorem exists_finset_subset_mem_adjoin_union (P V : Set Ω) {x : Ω}
    (hx : x ∈ adjoin F (P ∪ V)) :
    ∃ T : Finset Ω, (T : Set Ω) ⊆ P ∧ x ∈ adjoin F ((T : Set Ω) ∪ V) := by
  rw [Set.union_comm, ← adjoin_adjoin_left] at hx
  obtain ⟨T, hTP, hT⟩ := exists_finset_of_mem_adjoin (F := ↥(adjoin F V)) hx
  exact ⟨T, hTP, by rw [Set.union_comm, ← adjoin_adjoin_left]; exact hT⟩

/-- **Finite descent of separability.** If `x` is separable over the subextension of `Ω/F`
generated by `P ∪ V`, then it is already separable over the one generated by `T ∪ V` for some
finite `T ⊆ P`: only the finitely many coefficients of the minimal polynomial of `x` occur, and
each of them needs only finitely much of `P`.

This is the step that makes the base field `k'` of [stacks, 04KM] *finite* over `k`, `P` being
the perfect closure of `k` in `Ω`, which is infinite over `k` in general. -/
private theorem exists_finset_subset_isSeparable_adjoin_union (P V : Set Ω) {x : Ω}
    (hx : IsSeparable ↥(adjoin F (P ∪ V)) x) :
    ∃ T : Finset Ω, (T : Set Ω) ⊆ P ∧ IsSeparable ↥(adjoin F ((T : Set Ω) ∪ V)) x := by
  set B := adjoin F (P ∪ V)
  obtain ⟨T, hTP, hT⟩ := exists_finset_subset_forall_of_monotone (P := P)
    (p := fun T i ↦ (((minpoly ↥B x).coeff i : ↥B) : Ω) ∈ adjoin F ((T : Set Ω) ∪ V))
    (fun hTT' _ hi ↦ adjoin_union_mono_left hTT' V hi)
    (s := Finset.range ((minpoly ↥B x).natDegree + 1))
    (fun i _ ↦ exists_finset_subset_mem_adjoin_union P V ((minpoly ↥B x).coeff i).2)
  refine ⟨T, hTP, isSeparable_of_le_of_coeff_mem
    (adjoin.mono F _ _ (Set.union_subset_union_left V hTP)) hx fun i ↦ ?_⟩
  by_cases hi : i ∈ Finset.range ((minpoly ↥B x).natDegree + 1)
  · exact hT i hi
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hi)]
    simp

/-- A generating set of an intermediate field generates it as an extension in its own right. -/
private theorem adjoin_preimage_val_eq_top (M : IntermediateField F Ω) {S : Set Ω}
    (hS : adjoin F S = M) : adjoin F (Subtype.val ⁻¹' S : Set ↥M) = ⊤ := by
  have hsub : S ⊆ Set.range (Subtype.val : ↥M → Ω) :=
    fun x hx ↦ ⟨⟨x, hS ▸ subset_adjoin F S hx⟩, rfl⟩
  refine lift_injective M ?_
  rw [lift_adjoin, lift_top, Set.image_preimage_eq_of_subset hsub, hS]

/-- Separability of an element of an intermediate field `M` over a subextension `D` of `M` is the
separability of the underlying element of the ambient field over the lift of `D`. -/
private theorem isSeparable_lift_iff {M : IntermediateField F Ω} (D : IntermediateField F ↥M)
    (x : ↥M) : IsSeparable ↥(lift D) (x : Ω) ↔ IsSeparable ↥D x := by
  set N : IntermediateField ↥(lift D) Ω := extendScalars (lift_le D)
  let e₁ : ↥D ≃+* ↥(lift D) := (liftAlgEquiv D).toRingEquiv
  let e₂ : ↥M ≃+* ↥N :=
    { toFun := fun y ↦ ⟨y.1, y.2⟩, invFun := fun y ↦ ⟨y.1, y.2⟩,
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl,
      map_mul' := fun _ _ ↦ rfl, map_add' := fun _ _ ↦ rfl }
  have he : (algebraMap ↥(lift D) ↥N).comp (e₁ : ↥D →+* ↥(lift D))
      = (e₂ : ↥M →+* ↥N).comp (algebraMap ↥D ↥M) := RingHom.ext fun _ ↦ Subtype.ext rfl
  have he' : (algebraMap ↥D ↥M).comp (e₁.symm : ↥(lift D) →+* ↥D)
      = (e₂.symm : ↥N →+* ↥M).comp (algebraMap ↥(lift D) ↥N) := RingHom.ext fun _ ↦ Subtype.ext rfl
  have hmin : minpoly ↥(lift D) ((x : Ω)) = minpoly ↥(lift D) (e₂ x) :=
    minpoly.algHom_eq N.val Subtype.val_injective (e₂ x)
  have hiff : IsSeparable ↥(lift D) ((x : Ω)) ↔ IsSeparable ↥(lift D) (e₂ x) := by
    unfold IsSeparable
    rw [hmin]
  rw [hiff]
  exact ⟨fun h ↦ by simpa using IsSeparable.of_equiv_equiv e₁.symm e₂.symm he' h,
    IsSeparable.of_equiv_equiv e₁ e₂ he⟩

/-- Elements of the perfect closure of `F` in `Ω` are integral over `F`. -/
private theorem isIntegral_of_mem_perfectClosure {x : Ω} (hx : x ∈ perfectClosure F Ω) :
    IsIntegral F x :=
  (Algebra.IsIntegral.isIntegral (⟨x, hx⟩ : ↥(perfectClosure F Ω))).map (perfectClosure F Ω).val

end Ambient

section Tower

variable {k K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
  [IsScalarTower k K Ω]

/-- The subextension of `Ω/k` generated by `K` and a set `S` is the subextension of `Ω/K`
generated by `S`. -/
private theorem restrictScalars_adjoin_base (S : Set Ω) :
    restrictScalars k (adjoin K S) = adjoin k (Set.range (algebraMap K Ω) ∪ S) := by
  refine le_antisymm ?_ (adjoin_le_iff.mpr (Set.union_subset ?_ (subset_adjoin K S)))
  · have hr : ∀ y : K, algebraMap K Ω y ∈ adjoin k (Set.range (algebraMap K Ω) ∪ S) :=
      fun y ↦ subset_adjoin k _ (Or.inl ⟨y, rfl⟩)
    have hle : adjoin K S ≤
        (adjoin k (Set.range (algebraMap K Ω) ∪ S)).toSubfield.toIntermediateField hr :=
      adjoin_le_iff.mpr fun y hy ↦ subset_adjoin k _ (Or.inr hy)
    exact fun x hx ↦ hle hx
  · rintro y ⟨z, rfl⟩
    exact algebraMap_mem _ z

/-- Adjoining to `k` the part inside `K'` of a finite set of the perfect closure of `k` in `Ω`
is finite. -/
private theorem finiteDimensional_adjoin_preimage_of_subset_perfectClosure
    (k : Type*) {K Ω : Type*} [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω]
    [Algebra K Ω] [IsScalarTower k K Ω] (K' : IntermediateField K Ω) {T : Finset Ω}
    (hT : (T : Set Ω) ⊆ (perfectClosure k Ω : Set Ω)) :
    FiniteDimensional k ↥(adjoin k (Subtype.val ⁻¹' (T : Set Ω) : Set ↥K')) := by
  have : Finite ↥(Subtype.val ⁻¹' (T : Set Ω) : Set ↥K') :=
    (Set.Finite.preimage Subtype.val_injective.injOn T.finite_toSet).to_subtype
  exact finiteDimensional_adjoin fun x hx ↦
    (isIntegral_algHom_iff (K'.val.restrictScalars k) Subtype.val_injective).mp
      (isIntegral_of_mem_perfectClosure (hT hx))

end Tower

/-- The mathematical content of [stacks, 04KM], at the level of intermediate fields of `Ω/k`:
finitely many elements `T` of the perfect closure of `k` in `Ω` suffice, in the sense that the
compositum `K(T)` has a separating transcendence basis over `k(T)`. -/
private theorem exists_finset_subset_perfectClosure_isTranscendenceBasis_isSeparable
    (k K Ω : Type*) [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
    [IsScalarTower k K Ω] [PerfectField Ω] [Algebra.EssFiniteType k K] :
    ∃ (T : Finset Ω) (s : Set Ω), (T : Set Ω) ⊆ (perfectClosure k Ω : Set Ω) ∧
      s ⊆ (adjoin K (T : Set Ω) : Set Ω) ∧ AlgebraicIndependent k ((↑) : s → Ω) ∧
      ∀ x ∈ adjoin K (T : Set Ω), IsSeparable ↥(adjoin k ((T : Set Ω) ∪ s)) x := by
  classical
  set P : IntermediateField k Ω := perfectClosure k Ω
  -- a finite generating set `G` of the image of `K` in `Ω`
  obtain ⟨g, hg⟩ := IntermediateField.fg_top k K
  set G : Set Ω := (IsScalarTower.toAlgHom k K Ω) '' (g : Set K) with hG
  have hKΩadj : Set.range (algebraMap K Ω) ⊆ (adjoin k G : Set Ω) := by
    rintro y ⟨z, rfl⟩
    have hmap : (adjoin k (g : Set K)).map (IsScalarTower.toAlgHom k K Ω) = adjoin k G := by
      rw [adjoin_map, hG]
    rw [← hmap]
    exact ⟨z, by rw [hg]; exact mem_top, rfl⟩
  -- the compositum `M = P(K)`, finitely generated over the perfect field `P`
  set M : IntermediateField ↥P Ω := adjoin ↥P G
  have hKΩM : Set.range (algebraMap K Ω) ⊆ (M : Set Ω) := fun y hy ↦
    (adjoin_le_iff.mpr (subset_adjoin ↥P G) : adjoin k G ≤ restrictScalars k M) (hKΩadj hy)
  have hMfg : Algebra.EssFiniteType ↥P ↥M := by
    rw [← IntermediateField.fg_top_iff]
    exact IntermediateField.fg_def.mpr ⟨Subtype.val ⁻¹' G,
      ((g.finite_toSet.image _).preimage Subtype.val_injective.injOn),
      adjoin_preimage_val_eq_top M rfl⟩
  obtain ⟨s₀, hb, hsep0⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField ↥P ↥M
  set sF : Finset Ω := s₀.image Subtype.val with hsF
  set s : Set Ω := (sF : Set Ω) with hs
  have hsimg : s = Subtype.val '' (s₀ : Set ↥M) := by simp [hs, hsF]
  have hsM : s ⊆ (M : Set Ω) := by rw [hsimg]; rintro _ ⟨y, -, rfl⟩; exact y.2
  -- the separating transcendence basis of `M/P` is algebraically independent over `k`
  have hind : AlgebraicIndependent k ((↑) : s → Ω) := by
    have h : AlgebraicIndependent ↥P ((↑) : s → Ω) := by
      rw [hsimg]
      exact (hb.1.map' (f := M.val) Subtype.val_injective).image
    exact h.restrictScalars (FaithfulSMul.algebraMap_injective k ↥P)
  -- and `M` is separable over `k(P ∪ s)`, read inside `Ω`
  have hsepQ : ∀ x ∈ M, IsSeparable ↥(adjoin k ((P : Set Ω) ∪ s)) x := by
    intro x hx
    have h : IsSeparable ↥(lift (adjoin ↥P (s₀ : Set ↥M))) x :=
      (isSeparable_lift_iff _ _).mpr (Algebra.IsSeparable.isSeparable _ (⟨x, hx⟩ : ↥M))
    rw [lift_adjoin, ← hsimg] at h
    rw [← restrictScalars_adjoin k P s]
    exact h
  -- finitely much of `P` makes the generators of `K` separable, and puts `s` inside `K(T)`
  obtain ⟨T₁, hT₁P, hT₁⟩ := exists_finset_subset_forall_of_monotone (P := (P : Set Ω))
    (p := fun T y ↦ IsSeparable ↥(adjoin k ((T : Set Ω) ∪ s)) (algebraMap K Ω y))
    (fun hTT' _ hy ↦ isSeparable_of_le (adjoin_union_mono_left hTT' s) hy) (s := g)
    (fun y _ ↦ exists_finset_subset_isSeparable_adjoin_union _ s (hsepQ _ (hKΩM ⟨y, rfl⟩)))
  obtain ⟨T₂, hT₂P, hT₂⟩ := exists_finset_subset_forall_of_monotone (P := (P : Set Ω))
    (p := fun T z ↦ z ∈ adjoin k ((T : Set Ω) ∪ G))
    (fun hTT' _ hz ↦ adjoin_union_mono_left hTT' G hz) (s := sF)
    (fun z hz ↦ exists_finset_subset_mem_adjoin_union _ G
      (by rw [← restrictScalars_adjoin k P G]; exact hsM (by simpa [hs] using hz)))
  set T : Finset Ω := T₁ ∪ T₂ with hT
  have hT₁T : T₁ ⊆ T := Finset.subset_union_left
  have hT₂T : T₂ ⊆ T := Finset.subset_union_right
  refine ⟨T, s, ?_, ?_, hind, ?_⟩
  · rw [hT, Finset.coe_union]
    exact Set.union_subset hT₁P hT₂P
  · -- the transcendence basis lies in `K(T)`
    have h : adjoin k ((T₂ : Set Ω) ∪ G) ≤ restrictScalars k (adjoin K (T : Set Ω)) := by
      rw [adjoin_le_iff]
      refine Set.union_subset (fun y hy ↦ subset_adjoin K _ (Finset.coe_subset.mpr hT₂T hy))
        (fun y hy ↦ ?_)
      obtain ⟨w, -, rfl⟩ := hy
      exact algebraMap_mem _ w
    exact fun z hz ↦ h (hT₂ z (by simpa [hs] using hz))
  · -- everything in `K(T)` is separable over `k(T)(s)`
    set A : IntermediateField k Ω := adjoin k ((T : Set Ω) ∪ s)
    have hgen : ∀ y ∈ G, IsSeparable ↥A y := by
      rintro y ⟨w, hw, rfl⟩
      exact isSeparable_of_le (adjoin_union_mono_left hT₁T s) (hT₁ w hw)
    have h : adjoin k (Set.range (algebraMap K Ω) ∪ (T : Set Ω))
        ≤ adjoin k (G ∪ (A : Set Ω)) := by
      rw [adjoin_le_iff]
      exact Set.union_subset (fun y hy ↦ adjoin.mono k G _ Set.subset_union_left (hKΩadj hy))
        (fun y hy ↦ subset_adjoin k _ (Or.inr (subset_adjoin k _ (Or.inl hy))))
    intro x hx
    refine isSeparable_of_mem_adjoin_union A hgen (h ?_)
    rw [← restrictScalars_adjoin_base (k := k) (T : Set Ω)]
    exact hx

/-- The mathematical content of [stacks, 04KM]: for a finitely generated field extension `K/k`
inside a perfect field `Ω`, finitely many elements `T` of the perfect closure of `k` in `Ω`
suffice, in the sense that `K(T)` is separably generated over `k(T)`. -/
private theorem exists_finset_subset_perfectClosure_isSeparablyGenerated
    (k K Ω : Type*) [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
    [IsScalarTower k K Ω] [PerfectField Ω] [Algebra.EssFiniteType k K] :
    ∃ T : Finset Ω, (T : Set Ω) ⊆ (perfectClosure k Ω : Set Ω) ∧
      Algebra.IsSeparablyGenerated
        ↥(adjoin k (Subtype.val ⁻¹' (T : Set Ω) : Set ↥(adjoin K (T : Set Ω))))
        ↥(adjoin K (T : Set Ω)) := by
  obtain ⟨T, s, hTP, hsK, hind, hsep⟩ :=
    exists_finset_subset_perfectClosure_isTranscendenceBasis_isSeparable k K Ω
  refine ⟨T, hTP, ?_⟩
  set K' : IntermediateField K Ω := adjoin K (T : Set Ω)
  set S : Set ↥K' := Subtype.val ⁻¹' (T : Set Ω)
  set σ : Set ↥K' := Subtype.val ⁻¹' s
  set k' : IntermediateField k ↥K' := adjoin k S
  have hrange : Set.range (Subtype.val : ↥K' → Ω) = (K' : Set Ω) := Subtype.range_coe
  have himT : Subtype.val '' S = (T : Set Ω) :=
    Set.image_preimage_eq_of_subset (by rw [hrange]; exact subset_adjoin K _)
  have himσ : Subtype.val '' σ = s :=
    Set.image_preimage_eq_of_subset (by rw [hrange]; exact hsK)
  -- `k'` is finite, hence algebraic, over `k`
  have hfin : FiniteDimensional k ↥k' :=
    finiteDimensional_adjoin_preimage_of_subset_perfectClosure k K' hTP
  have halg : Algebra.IsAlgebraic k ↥k' := Algebra.IsAlgebraic.of_finite k ↥k'
  -- the lift of `k'(σ)` to `Ω` is `k(T)(s)`
  have hliftk' : lift (F := restrictScalars k K') k' = adjoin k (T : Set Ω) :=
    (lift_adjoin k (restrictScalars k K') S).trans (congrArg (adjoin k) himT)
  have hc : Subtype.val '' (k' : Set ↥K')
      = ((adjoin k (T : Set Ω) : IntermediateField k Ω) : Set Ω) := by rw [← hliftk']; rfl
  have hEq : adjoin k (Subtype.val '' ((k' : Set ↥K') ∪ σ)) = adjoin k ((T : Set Ω) ∪ s) := by
    rw [Set.image_union, himσ, hc, adjoin_union, adjoin_self, ← adjoin_union]
  have hliftR : lift (F := restrictScalars k K') (adjoin k ((k' : Set ↥K') ∪ σ))
      = adjoin k ((T : Set Ω) ∪ s) :=
    (lift_adjoin k (restrictScalars k K') ((k' : Set ↥K') ∪ σ)).trans hEq
  -- separability of `K'` over `k'(σ)`, transported from `Ω`
  have hsepR : Algebra.IsSeparable ↥(adjoin ↥k' σ) ↥K' := by
    refine ⟨fun x ↦ ?_⟩
    have h : IsSeparable ↥(adjoin k ((k' : Set ↥K') ∪ σ)) x := (isSeparable_lift_iff _ _).mp
      (isSeparable_of_le (le_of_eq hliftR.symm) (hsep (x : Ω) x.2))
    exact isSeparable_of_le (le_of_eq (restrictScalars_adjoin k k' σ).symm) h
  -- and `σ` is a transcendence basis of `K'` over `k'`
  have hindK' : AlgebraicIndependent k ((↑) : σ → ↥K') := by
    refine AlgebraicIndependent.of_comp (K'.val.restrictScalars k) ?_
    let e : σ ≃ s :=
      { toFun := fun z ↦ ⟨((z : ↥K') : Ω), z.2⟩
        invFun := fun z ↦ ⟨⟨(z : Ω), hsK z.2⟩, z.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact hind.comp e e.injective
  exact isSeparablyGenerated_of_algebraicIndependent
    ((Algebra.IsAlgebraic.algebraicIndependent_iff k ↥k').mp hindK') hsepR

/-- For a finitely generated field extension `K/k` and a perfect field extension `Ω/K`, there are
an intermediate field `K'` of `Ω/K`, finite and purely inseparable over `K`, and an intermediate
field `k'` of `K'/k`, finite and purely inseparable over `k`, such that `K'/k'` is separably
generated. -/
public theorem solution
    (k K Ω : Type*) [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
    [IsScalarTower k K Ω] [PerfectField Ω] [Algebra.EssFiniteType k K] :
    ∃ (K' : IntermediateField K Ω) (k' : IntermediateField k ↥K'),
      Module.Finite K ↥K' ∧ IsPurelyInseparable K ↥K' ∧
      Module.Finite k ↥k' ∧ IsPurelyInseparable k ↥k' ∧
      Algebra.IsSeparablyGenerated ↥k' ↥K' := by
  obtain ⟨T, hT, hsg⟩ := exists_finset_subset_perfectClosure_isSeparablyGenerated k K Ω
  obtain ⟨q, hq⟩ := ExpChar.exists k
  have hqK : ExpChar K q := expChar_of_injective_algebraMap (algebraMap k K).injective q
  set K' : IntermediateField K Ω := adjoin K (T : Set Ω)
  set S : Set ↥K' := Subtype.val ⁻¹' (T : Set Ω)
  refine ⟨K', adjoin k S, ?_, ?_, ?_, ?_, hsg⟩
  · exact finiteDimensional_adjoin fun x hx ↦ (isIntegral_of_mem_perfectClosure (hT hx)).tower_top
  · refine (le_perfectClosure_iff K Ω K').mp (adjoin_le_iff.mpr fun x hx ↦ ?_)
    obtain ⟨n, c, hc⟩ := (mem_perfectClosure_iff_pow_mem q).mp (hT hx)
    exact (mem_perfectClosure_iff_pow_mem q).mpr
      ⟨n, algebraMap k K c, by rw [← IsScalarTower.algebraMap_apply]; exact hc⟩
  · exact finiteDimensional_adjoin_preimage_of_subset_perfectClosure k K' hT
  · refine (le_perfectClosure_iff k ↥K' _).mp (adjoin_le_iff.mpr fun x hx ↦ ?_)
    obtain ⟨n, c, hc⟩ := (mem_perfectClosure_iff_pow_mem q).mp (hT hx)
    refine (mem_perfectClosure_iff_pow_mem q).mpr ⟨n, c, Subtype.val_injective ?_⟩
    push_cast
    exact hc

end Stacks.FieldTheory.SeparatingBaseChange

end

/-!
# Separable generation after a finite purely inseparable base change

Let `K/k` be a finitely generated field extension. Then there is a diagram of fields
```
K  →  K'
↑     ↑
k  →  k'
```
in which `k'/k` and `K'/K` are finite purely inseparable extensions and `K'/k'` is separably
generated, i.e. has a separating transcendence basis in the sense of [stacks, 030O](1).

In characteristic zero, and more generally whenever `K/k` is already separably generated, the
diagram is the trivial one `k' = k`, `K' = K`; the content is in characteristic `p`, where one
chooses a transcendence basis `x₁, …, x_r` of `K/k`, adjoins to `k` finitely many `p`-power
roots of elements of `k` and to `K` the roots `x_i^{1/p}` together with those, and shows by
induction on the degree `[K : K_{sep}]` of the inseparable part of `K/k(x₁, …, x_r)` that
finitely many such steps make a separating transcendence basis appear.

This is the engine behind [stacks, 030R], where the conclusion is upgraded from "separably
generated" to "separable" by [stacks, 030X], and the extension `K'/K` is cut down to the
compositum `k'K`.

## Main results

* `exists_isPurelyInseparable_and_isSeparablyGenerated_of_essFiniteType`: the diagram above
  exists inside any prescribed perfect field extension `Ω/K`.

## Implementation notes

The two fields the source produces are realized as intermediate fields of an ambient extension
`Ω/K` assumed perfect: `K'` is an intermediate field of `Ω/K` and `k'` an intermediate field of
`K'/k`, so all four fields of the square and all four maps between them are canonical and every
`Algebra` instance is inferred rather than chosen. This is a strengthening of the source's
abstract diagram, not a specialization: the fields the source constructs are purely inseparable
over `K` resp. `k`, hence generated by `p`-power roots of elements of `K`, and such roots are
unique when they exist and do exist in every perfect extension of `K`, so any perfect `Ω/K`
receives the diagram. Conversely the source's statement is the case `Ω = AlgebraicClosure K`.
Dependents that already work inside a fixed `Ω` — the usual situation, since one wants `k'` and
`K` in one place, e.g. to form the compositum `k'K` of [stacks, 030R] — get the diagram there
without transporting along an isomorphism. This is also the shape of [stacks, 030R] as stated in
this project, so that its proof can cite this lemma directly.

`K/k` finitely generated *as a field extension* is `Algebra.EssFiniteType k K`, which for field
extensions is exactly that (`IntermediateField.fg_top_iff`); `Algebra.FiniteType k K` would be
the strictly stronger "finitely generated as an algebra".

"Separably generated" is `Algebra.IsSeparablyGenerated` of [stacks, 030O](1); Mathlib has no
such predicate, only the two existence results of this shape for a perfect base
(`exists_isTranscendenceBasis_and_isSeparable_of_perfectField`) and under linear disjointness of
`p`-th powers
(`exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType`).
Note that it is *not* Mathlib's `Algebra.IsSeparable ↥k' ↥K'`, which asks that every element of
`K'` have separable minimal polynomial over `k'` and therefore already forces `K'/k'` algebraic:
that reading of the source's "separable" would make the conclusion false as soon as
`trdeg_k K > 0`. The source's "separable" for a possibly transcendental extension is
[stacks, 030O](2), `Algebra.IsSeparableExtension`, and for `K'/k'` it is a consequence of the
conclusion here, by [stacks, 030X].

Finiteness of `K'/K` and of `k'/k` is stated as `Module.Finite` alongside pure inseparability
rather than being left to follow from finite generation, matching the source's "finite purely
inseparable" and the form [stacks, 030R] uses.

Faithfulness, on the four points a reader should check against the source.
(1) No hypothesis is dead: `Algebra.EssFiniteType k K` is what makes a *finite* `k'` suffice (the
perfect closure of `k` works for any `K/k`, but is infinite over `k`), and `PerfectField Ω` with
`IsScalarTower k K Ω` is what makes the `p`-power roots cutting out `k'` and `K'` available in
the prescribed ambient field; nothing assumes `K/k` algebraic or of positive characteristic.
(2) The bases are the source's: `k'` is an extension of `k` and `K'` one of `K`, the separating
transcendence basis is taken over `k'` (not over `k`, and not over `k'(x_i)` for a basis chosen
in advance), and pure inseparability of `k'` is over `k`, of `K'` over `K`.
(3) The maps of the source's square are pinned, not merely asserted to exist: `k → k'` and
`k' → K'` are the algebra maps of `k' : IntermediateField k ↥K'`, `K → K'` that of
`K' : IntermediateField K Ω`, and `k → K` the given one, the square commuting by
`IsScalarTower k K Ω`; an unpinned diagram of abstract fields would leave the commutativity of
the square unstated.
(4) The instantiation is not degenerate: for `k = 𝔽_p(t)`, `K = k(t^{1/p}, x)` with `x`
transcendental and `Ω` a perfect closure of `K`, the choice `k' = k` fails, since `K` contains a
`p`-th root of `t ∈ k` outside `k`, so `k^{1/p} ⊗_k K` is not reduced and `K/k` is not separably
generated; the choice `k' = K'` fails too, since `Module.Finite k ↥k'` would force `K/k` finite
while `trdeg_k K = 1`; and `k' = k(t^{1/p})`, `K' = K` satisfies every conjunct, `K'/k'` being
purely transcendental of degree of transcendence `1`.

## References

* [Stacks Project, Tag 04KM](https://stacks.math.columbia.edu/tag/04KM)
-/

@[expose] public section

/-- **Stacks 04KM.** Let `K/k` be a finitely generated field extension and let `Ω/K` be a perfect
field extension. Then inside `Ω` there is a diagram
```
K  →  K'
↑     ↑
k  →  k'
```
with `k'/k` and `K'/K` finite purely inseparable and `K'/k'` separably generated. -/
@[stacks 04KM]
public theorem exists_isPurelyInseparable_and_isSeparablyGenerated_of_essFiniteType
    (k K Ω : Type*) [Field k] [Field K] [Field Ω] [Algebra k K] [Algebra k Ω] [Algebra K Ω]
    [IsScalarTower k K Ω] [PerfectField Ω] [Algebra.EssFiniteType k K] :
    ∃ (K' : IntermediateField K Ω) (k' : IntermediateField k ↥K'),
      Module.Finite K ↥K' ∧ IsPurelyInseparable K ↥K' ∧
      Module.Finite k ↥k' ∧ IsPurelyInseparable k ↥k' ∧
      Algebra.IsSeparablyGenerated ↥k' ↥K' := by apply
                                                   Stacks.FieldTheory.SeparatingBaseChange.solution

end

end

/-!
# Separating transcendence bases of a finitely generated extension

Stacks 030Q (Lemma 10.42.3). Let `K/k` be a field extension that is both
separably generated over `k` and finitely generated over `k`. Set
`r = trdeg_k(K)` (a finite natural number, since `K/k` is finitely generated).
Then there exist elements `x_1, ..., x_{r+1} ∈ K` such that:

1. `x_1, ..., x_r` is a transcendence basis of `K` over `k`;
2. `K = k(x_1, ..., x_{r+1})`; and
3. `x_{r+1}` is separable over the subfield `k(x_1, ..., x_r) ⊆ K`
   (note `x_{r+1}` is algebraic over `k(x_1, ..., x_r)` by item (1)).
-/

@[expose] public section
-- Definition 1 (Algebraic independence / transcendence basis). A subset
-- `S ⊆ K` is algebraically independent over `k` if the `k`-algebra map
-- `k[X_s : s ∈ S] → K`, `X_s ↦ s`, is injective. A transcendence basis of
-- `K` over `k` is an algebraically independent subset over which `K` is
-- algebraic. In Mathlib this is `IsTranscendenceBasis k x`, stated for an
-- indexing function `x : ι → K` (algebraic independence forces `x` injective).
-- The transcendence degree `trdeg_k(K)` is the cardinality of any transcendence
-- basis; in Mathlib it is `Algebra.trdeg k K : Cardinal`.
--
-- Definition 2 (Finitely generated field extension). `K/k` is finitely
-- generated if there exist finitely many `α_1, ..., α_n ∈ K` with
-- `K = k(α_1, ..., α_n)`. In Mathlib this is `(⊤ : IntermediateField k K).FG`.
--
-- Definition 3 (Separable algebraic element / extension). For `α` algebraic
-- over `F`, `α` is separable over `F` if its minimal polynomial has no repeated
-- roots. In Mathlib the per-element predicate is `IsSeparable F α`, and the
-- extension predicate is `Algebra.IsSeparable F E`.
--
-- Definition 4 (Separably generated field extension, Stacks 030O). `K/k` is
-- separably generated over `k` if there exists a transcendence basis of `K`
-- over `k` such that `K` is a separable algebraic extension of the subfield
-- generated by that basis. We formalize this as `SeparablyGenerated` below.

/-- `K/k` is *separably generated* if there is a transcendence basis
`x : ι → K` of `K` over `k` such that `K` is a separable (algebraic) extension
of the subfield `k(x_i : i ∈ ι)` generated by the basis. Here algebraicity of
`K` over the generated subfield is automatic from `IsTranscendenceBasis`, so the
remaining content is separability. (Stacks 030O / Definition 4.) -/
@[sga "1 II 5.6"]
def SeparablyGenerated (k K : Type*) [Field k] [Field K] [Algebra k K] : Prop :=
  ∃ (ι : Type) (x : ι → K), IsTranscendenceBasis k x ∧
    Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K

/-- Stacks 030Q (Lemma 10.42.3). If `K/k` is separably generated and finitely
generated, with transcendence degree `r`, then there are `x_1, ..., x_{r+1} ∈ K`
(here packaged as `x : Fin (r+1) → K`) such that:

1. `x_1, ..., x_r` (the entries `x i.castSucc`) form a transcendence basis of
   `K` over `k`;
2. `K = k(x_1, ..., x_{r+1})` (the adjoin of the whole tuple is `⊤`); and
3. `x_{r+1}` (the entry `x (Fin.last r)`) is separable over the subfield
   `k(x_1, ..., x_r)` generated by the first `r` entries. -/
@[stacks 030Q]
theorem separablyGenerated_fg_exists_primitive_transcendence_basis
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    (hsep : SeparablyGenerated k K)
    (hfg : (⊤ : IntermediateField k K).FG)
    (r : ℕ) (hr : Algebra.trdeg k K = r) :
    ∃ x : Fin (r + 1) → K,
      IsTranscendenceBasis k (fun i : Fin r => x i.castSucc) ∧
      IntermediateField.adjoin k (Set.range x) = ⊤ ∧
      IsSeparable
        (↥(IntermediateField.adjoin k (Set.range (fun i : Fin r => x i.castSucc))))
        (x (Fin.last r)) := by
  classical
  -- Unpack the separably-generated hypothesis.
  obtain ⟨ι, x, hxTB, hxSep⟩ := hsep
  -- The index type `ι` of the transcendence basis has cardinality `r`.
  have hcard : Cardinal.mk ι = (r : Cardinal.{0}) := by
    have h2 := hxTB.lift_cardinalMk_eq_trdeg
    rw [hr] at h2
    simp only [Cardinal.lift_natCast] at h2
    rw [show ((r : Cardinal.{_})) = Cardinal.lift.{_, 0} (r : Cardinal.{0}) by simp] at h2
    exact Cardinal.lift_inj.mp h2
  -- Hence a bijection `e : ι ≃ Fin r`.
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin r) := by
    rw [Cardinal.mk_eq_nat_iff] at hcard; exact hcard
  -- Reindex the basis to be indexed by `Fin r`.
  set y : Fin r → K := x ∘ e.symm with hy
  have hyTB : IsTranscendenceBasis k y := (isTranscendenceBasis_equiv e.symm).mpr hxTB
  have hrange : Set.range y = Set.range x := EquivLike.range_comp x e.symm
  -- The intermediate field generated by the transcendence basis.
  set F : IntermediateField k K := IntermediateField.adjoin k (Set.range y) with hF
  have hFeq : F = IntermediateField.adjoin k (Set.range x) := by rw [hF, hrange]
  -- `K` is algebraic over `F`.
  have halg : Algebra.IsAlgebraic F K := by
    rw [hFeq]; exact hxTB.isAlgebraic_field
  have hAlgInt : Algebra.IsIntegral F K := Algebra.isAlgebraic_iff_isIntegral.mp halg
  -- `K` is separable over `F`.
  have hSepInst : Algebra.IsSeparable F K := by rw [hFeq]; exact hxSep
  -- `K` is finite-dimensional over `F`, using finite generation of `K/k`.
  have hfin : FiniteDimensional F K := by
    obtain ⟨S, hS⟩ := hfg
    -- `K` is generated over `F` by the same finite set.
    have hStop : IntermediateField.adjoin F (↑S : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro z _
      have hz : z ∈ IntermediateField.adjoin k (↑S : Set K) := by rw [hS]; trivial
      have hle : IntermediateField.adjoin k (↑S : Set K)
          ≤ (IntermediateField.adjoin F (↑S : Set K)).restrictScalars k := by
        rw [IntermediateField.adjoin_le_iff]
        exact IntermediateField.subset_adjoin F (↑S : Set K)
      exact hle hz
    have hInteg : ∀ z ∈ (↑S : Set K), IsIntegral F z :=
      fun z _ => Algebra.IsIntegral.isIntegral z
    have hfd : FiniteDimensional F ↥(IntermediateField.adjoin F (↑S : Set K)) :=
      IntermediateField.finiteDimensional_adjoin hInteg
    rw [hStop] at hfd
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  -- Primitive element theorem: `K = F⟮θ⟯` for some `θ`.
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F K
  -- Assemble the `(r+1)`-tuple by appending `θ`.
  refine ⟨(Fin.snoc y θ : Fin (r + 1) → K), ?_, ?_, ?_⟩
  · -- First `r` entries are exactly `y`, a transcendence basis.
    have : (fun i : Fin r => (Fin.snoc y θ : Fin (r + 1) → K) i.castSucc) = y := by
      funext i; simp [Fin.snoc_castSucc]
    rw [this]; exact hyTB
  · -- The whole tuple generates `K`.
    have hrng : Set.range (Fin.snoc y θ : Fin (r + 1) → K) = Set.range y ∪ {θ} := by
      rw [Fin.range_snoc, Set.insert_eq, Set.union_comm]
    rw [hrng]
    -- `adjoin k (range y ∪ {θ}) = restrictScalars k (adjoin F {θ})`.
    have hcomm := IntermediateField.adjoin_adjoin_left k (Set.range y) {θ}
    rw [← hcomm, ← hF]
    -- `adjoin F {θ} = F⟮θ⟯ = ⊤`.
    rw [show IntermediateField.adjoin F ({θ} : Set K) = (⊤ : IntermediateField F K) from hθ]
    simp
  · -- `θ` is separable over the field generated by the first `r` entries.
    have hbase : (fun i : Fin r => (Fin.snoc y θ : Fin (r + 1) → K) i.castSucc) = y := by
      funext i; simp [Fin.snoc_castSucc]
    rw [hbase]
    simp only [Fin.snoc_last]
    -- the base field equals `F`.
    show IsSeparable (↥(IntermediateField.adjoin k (Set.range y))) θ
    rw [← hF]
    exact Algebra.IsSeparable.isSeparable' θ

end
