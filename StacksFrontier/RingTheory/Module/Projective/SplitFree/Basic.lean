module

public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.RingTheory.Module.Projective.SplitFree.Fibres
public import StacksFrontier.Topology.Dimension.Codimension

/-!
# Serre's splitting theorem

Let `M` be a finitely presented module over a commutative ring `R`. Serre's splitting theorem says
that if the space of closed points of `Spec R` is Noetherian of dimension at most `d`, and at
every closed point the localisation of `M` has a free direct summand of rank greater than `d`,
then `M` itself has a free direct summand of rank one. The proof runs on the canonical quotients
`V(x)` of `StacksFrontier.RingTheory.Module.Projective.SplitFree.Fibres`: one adjoins sections one at
a time, prescribing the new section at finitely many points so that the locus where the chosen
sections become linearly dependent gains codimension at each step. Once that codimension exceeds
the dimension of the space, the dependent locus is empty and a single section generates a free
rank-one summand.

## Main definitions

There are no new definitions.

## Main results

* `exists_section_dependentLocus_subset_union_of_card_add_le_finrank`: Serre's proposition — a
  further section can be prescribed at finitely many points so that the enlarged dependent locus
  is contained in the old one together with a closed set of controlled codimension.
* `exists_linearEquiv_prod_of_local_free_summand_rank_gt_dimension`: Serre's theorem — a finitely
  presented module whose local ranks all exceed the dimension of the space of closed points splits
  off a free summand of rank one.

## Implementation notes

A finite list of sections and a finite list of prescribed points are represented by families over
finite types. Irreducible components of a closed subset are expressed intrinsically as maximal
irreducible closed subsets of the ambient closed-point space, and a free direct summand of rank
`r` of a localisation by a family of `r` elements whose linear-combination map admits a linear
retraction. The complementary module in the conclusion is chosen as a submodule of `M`.

## References

* [Serre-projective, Theorem 1]
* [Serre-projective, Theorem 2]
* [Stacks, Tag 0GVB](https://stacks.math.columbia.edu/tag/0GVB)
* [Stacks, Tag 0GVC](https://stacks.math.columbia.edu/tag/0GVC)
-/

@[expose] public section

universe u v w

open scoped Pointwise

section DependentLocus

open TopologicalSpace

private lemma dependentLocus_isClosed
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] {h : ℕ} (sections : Fin h → M) :
    IsClosed {y : ClosedPointSpace R | ¬LinearIndependent (ClosedPointResidueField y)
      (fun i ↦ (canonicalKernel M y).mkQ (sectionAt y (sections i)))} := by
  apply isOpen_compl_iff.mp
  have hopen (f : R) : IsOpen {y : ClosedPointSpace R | f ∉ y.1.asIdeal} :=
    (PrimeSpectrum.basicOpen f).isOpen.preimage continuous_subtype_val
  have heq : {y : ClosedPointSpace R | LinearIndependent (ClosedPointResidueField y)
      (fun i ↦ (canonicalKernel M y).mkQ (sectionAt y (sections i)))} =
      ⋃ f : {f : R // SplitsAfterInverting f sections},
        {y : ClosedPointSpace R | f.1 ∉ y.1.asIdeal} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ((canonical_exact_and_splits_iff_linearIndependent y).2.2.2 h sections).symm.trans
      ⟨fun ⟨f, hf, hs⟩ ↦ ⟨⟨f, hs⟩, hf⟩, fun ⟨⟨f, hs⟩, hf⟩ ↦ ⟨f, hf, hs⟩⟩
  have hcomp : {y : ClosedPointSpace R | ¬LinearIndependent (ClosedPointResidueField y)
      (fun i ↦ (canonicalKernel M y).mkQ (sectionAt y (sections i)))}ᶜ =
      {y : ClosedPointSpace R | LinearIndependent (ClosedPointResidueField y)
      (fun i ↦ (canonicalKernel M y).mkQ (sectionAt y (sections i)))} := by
    ext y
    simp
  rw [hcomp, heq]
  exact isOpen_iUnion fun f ↦ hopen f.1

/-- An irreducible set contained in a finite union of closed sets lies in one of them. -/
private lemma exists_mem_subset_of_subset_sUnion {X : Type u} [TopologicalSpace X]
    {S : Set (Set X)} (hSf : S.Finite) (hSc : ∀ t ∈ S, IsClosed t) {Z : Set X}
    (hZ : IsIrreducible Z) (hZS : Z ⊆ ⋃₀ S) : ∃ t ∈ S, Z ⊆ t := by
  obtain ⟨t, ht, hZt⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ hSf.toFinset
    (by simpa using hSc) (by simpa using hZS)
  exact ⟨t, hSf.mem_toFinset.mp ht, hZt⟩

/-- An irreducible closed set contained in the union of two closed sets lies in one of them. -/
private lemma irreducible_subset_or_of_subset_union {X : Type u} [TopologicalSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) {Z : IrreducibleCloseds X}
    (h : (Z : Set X) ⊆ A ∪ B) : (Z : Set X) ⊆ A ∨ (Z : Set X) ⊆ B :=
  (isPreirreducible_iff_isClosed_union_isClosed.mp Z.isIrreducible.2) A B hA hB h

private lemma irreducible_subset_component {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] {C : Set X} (hC : IsClosed C)
    (T : IrreducibleCloseds X) (hTC : (T : Set X) ⊆ C) :
    ∃ Z : IrreducibleCloseds X, T ≤ Z ∧
      Maximal (fun W : IrreducibleCloseds X ↦ (W : Set X) ⊆ C) Z := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  have hchoose (W : IrreducibleCloseds X) (hWC : (W : Set X) ⊆ C) :
      ∃ s ∈ S, (W : Set X) ⊆ s := by
    exact exists_mem_subset_of_subset_sUnion hSf hSc W.isIrreducible (hS ▸ hWC)
  obtain ⟨t, htS, hTt⟩ := hchoose T hTC
  obtain ⟨z, htz, hz⟩ := hSf.exists_le_maximal htS
  let Z : IrreducibleCloseds X := ⟨z, hSi z hz.prop, hSc z hz.prop⟩
  have hZC : (Z : Set X) ⊆ C := by
    change z ⊆ C
    rw [hS]
    exact Set.subset_sUnion_of_mem hz.prop
  refine ⟨Z, hTt.trans htz, ⟨hZC, ?_⟩⟩
  intro W hWC hZW
  obtain ⟨s, hsS, hWs⟩ := hchoose W hWC
  have hzs : z ⊆ s := (show (Z : Set X) ⊆ (W : Set X) from hZW).trans hWs
  have hzs_eq : z = s := hz.eq_of_le hsS hzs
  change (W : Set X) ⊆ z
  exact hzs_eq ▸ hWs

private lemma finite_components {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] {C : Set X} (hC : IsClosed C) :
    {Z : IrreducibleCloseds X |
      Maximal (fun W : IrreducibleCloseds X ↦ (W : Set X) ⊆ C) Z}.Finite := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  apply Set.Finite.of_injOn (f := fun Z : IrreducibleCloseds X ↦ (Z : Set X))
    (t := S) ?_ ?_ hSf
  · intro Z hZ
    change Maximal (fun W : IrreducibleCloseds X ↦ (W : Set X) ⊆ C) Z at hZ
    obtain ⟨t, htS', hZt⟩ :=
      exists_mem_subset_of_subset_sUnion hSf hSc Z.isIrreducible (hS ▸ hZ.prop)
    let T : IrreducibleCloseds X := ⟨t, hSi t htS', hSc t htS'⟩
    have hTC : (T : Set X) ⊆ C := by
      change t ⊆ C
      rw [hS]
      exact Set.subset_sUnion_of_mem htS'
    have hZT : Z = T := hZ.eq_of_le hTC hZt
    simpa [hZT, T] using htS'
  · exact fun _ _ _ _ h ↦ SetLike.coe_injective h

private lemma mem_component_of_mem_closed {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] {C : Set X} (hC : IsClosed C) {y : X} (hy : y ∈ C) :
    ∃ Z : IrreducibleCloseds X,
      Maximal (fun W : IrreducibleCloseds X ↦ (W : Set X) ⊆ C) Z ∧ y ∈ Z := by
  let T : IrreducibleCloseds X :=
    ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hTC : (T : Set X) ⊆ C := hC.closure_subset_iff.mpr (by simpa [T] using hy)
  obtain ⟨Z, hTZ, hZ⟩ := irreducible_subset_component hC T hTC
  exact ⟨Z, hZ, hTZ (subset_closure (Set.mem_singleton y))⟩

private lemma exists_point_unique_to_component {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] {C F : Set X} (hC : IsClosed C) (hF : IsClosed F)
    (Z : IrreducibleCloseds X)
    (hZ : Maximal (fun W : IrreducibleCloseds X ↦ (W : Set X) ⊆ C) Z)
    (hZF : ¬(Z : Set X) ⊆ F) :
    ∃ y : X, y ∈ Z ∧ y ∉ F ∧
      ∀ W : IrreducibleCloseds X,
        Maximal (fun T : IrreducibleCloseds X ↦ (T : Set X) ⊆ C) W →
        W ≠ Z → y ∉ W := by
  classical
  let K : Set (IrreducibleCloseds X) :=
    {W | Maximal (fun T : IrreducibleCloseds X ↦ (T : Set X) ⊆ C) W}
  let S : Set (Set X) := (fun W : IrreducibleCloseds X ↦ (W : Set X)) '' (K \ {Z})
  have hSf : S.Finite := (finite_components hC).sdiff.image _
  have hSc : ∀ t ∈ insert F S, IsClosed t := by
    intro t ht
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact hF
    · obtain ⟨W, _, rfl⟩ := ht
      exact W.isClosed
  have hnot : ¬(Z : Set X) ⊆ ⋃₀ insert F S := by
    intro hcover
    obtain ⟨t, ht', hZt⟩ :=
      exists_mem_subset_of_subset_sUnion (hSf.insert F) hSc Z.isIrreducible hcover
    rcases Set.mem_insert_iff.mp ht' with rfl | ⟨W, hWK, rfl⟩
    · exact hZF hZt
    · have hW : Maximal (fun T : IrreducibleCloseds X ↦ (T : Set X) ⊆ C) W := hWK.1
      exact Set.mem_compl_singleton_iff.mp hWK.2 (hZ.eq_of_le hW.prop hZt).symm
  obtain ⟨y, hyZ, hyout⟩ := Set.not_subset.mp hnot
  refine ⟨y, hyZ, fun hy ↦ hyout (Set.mem_sUnion.mpr ⟨F, Set.mem_insert _ _, hy⟩), ?_⟩
  intro W hW hWZ hyW
  exact hyout (Set.mem_sUnion.mpr
    ⟨W, Set.mem_insert_of_mem _ ⟨W, ⟨hW, by simpa using hWZ⟩, rfl⟩, hyW⟩)

private lemma codimension_succ_le_of_lt {X : Type u} [TopologicalSpace X]
    {Z W : IrreducibleCloseds X} {k : ℕ} (hZW : Z < W)
    (hk : (k : ℕ∞) ≤ codimension W) :
    ((k + 1 : ℕ) : ℕ∞) ≤ codimension Z := by
  rw [codimension_eq_coheight] at hk ⊢
  simpa only [Nat.cast_add, Nat.cast_one] using
    (add_le_add_left hk 1).trans (Order.coheight_add_one_le hZW)

private noncomputable abbrev valueAt {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (x : ClosedPointSpace R) (s : M) :
    CanonicalQuotient M x :=
  (canonicalKernel M x).mkQ (sectionAt x s)

private lemma valueAt_add {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (x : ClosedPointSpace R) (s t : M) :
    valueAt x (s + t) = valueAt x s + valueAt x t := by
  simp [valueAt, sectionAt]

private lemma valueAt_smul {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (x : ClosedPointSpace R) (f : R) (s : M) :
    valueAt x (f • s) = Ideal.Quotient.mk x.1.asIdeal f • valueAt x s := by
  change (canonicalKernel M x).mkQ (Submodule.Quotient.mk (f • s)) =
    Ideal.Quotient.mk x.1.asIdeal f •
      (canonicalKernel M x).mkQ (Submodule.Quotient.mk s)
  rw [← Module.Quotient.mk_smul_mk M x.1.asIdeal f s, map_smul]

private lemma valueAt_smul_of_one {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (x : ClosedPointSpace R) (f : R) (s : M)
    (hf : Ideal.Quotient.mk x.1.asIdeal f = 1) :
    valueAt x (f • s) = valueAt x s := by
  rw [valueAt_smul, hf, one_smul]

private lemma valueAt_smul_of_zero {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (x : ClosedPointSpace R) (f : R) (s : M)
    (hf : Ideal.Quotient.mk x.1.asIdeal f = 0) :
    valueAt x (f • s) = 0 := by
  rw [valueAt_smul, hf, zero_smul]

private lemma independent_snoc_iff
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {h : ℕ} (sections : Fin h → M) (s : M) (y : ClosedPointSpace R) :
    LinearIndependent (ClosedPointResidueField y)
      (fun i ↦ valueAt y ((Fin.snoc sections s) i)) ↔
      LinearIndependent (ClosedPointResidueField y) (fun i ↦ valueAt y (sections i)) ∧
        valueAt y s ∉ Submodule.span (ClosedPointResidueField y)
          (Set.range fun i ↦ valueAt y (sections i)) := by
  change LinearIndependent (ClosedPointResidueField y)
    (valueAt (M := M) y ∘ Fin.snoc sections s) ↔ _
  rw [Fin.comp_snoc, linearIndependent_finSnoc]
  rfl

private lemma independent_snoc_add_smul
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    {n : ℕ} (v : Fin n → V) (u t : V) (a : K)
    (h : LinearIndependent K (Fin.snoc (Fin.snoc v u) t)) :
    LinearIndependent K (Fin.snoc v (u + a • t)) := by
  let P := Submodule.span K (Set.range v)
  let Q := Submodule.span K (Set.range (Fin.snoc v u))
  have h1 : LinearIndependent K (Fin.snoc v u) := (linearIndependent_finSnoc.mp h).1
  have h0 : LinearIndependent K v := (linearIndependent_finSnoc.mp h1).1
  have hu : u ∉ P := (linearIndependent_finSnoc.mp h1).2
  have ht : t ∉ Q := (linearIndependent_finSnoc.mp h).2
  have hrange : Set.range v ⊆ Set.range (Fin.snoc v u) := by
    rintro z ⟨i, rfl⟩
    exact ⟨i.castSucc, by simp⟩
  have hPQ : P ≤ Q := Submodule.span_mono hrange
  have huQ : u ∈ Q := Submodule.subset_span ⟨Fin.last n, by simp⟩
  refine linearIndependent_finSnoc.mpr ⟨h0, fun hsum ↦ ?_⟩
  by_cases ha : a = 0
  · exact hu (by simpa [ha] using hsum)
  · apply ht
    apply (Q.smul_mem_iff ha).mp
    have hdiff : (u + a • t) - u ∈ Q := Q.sub_mem (hPQ hsum) huQ
    convert hdiff using 1
    abel

private noncomputable abbrev dependentLocus
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {h : ℕ} (sections : Fin h → M) : Set (ClosedPointSpace R) :=
  {y | ¬LinearIndependent (ClosedPointResidueField y) (fun i ↦ valueAt y (sections i))}

private abbrev codimComponentsGe {X : Type u} [TopologicalSpace X]
    (C : Set X) (k : ℕ) : Prop :=
  ∀ Z : IrreducibleCloseds X,
    Maximal (fun W : IrreducibleCloseds X ↦ (W : Set X) ⊆ C) Z →
      (k : ℕ∞) ≤ codimension Z

/-- An irreducible closed subset of `G` of codimension less than `k + 1` is a maximal component
of `G` when all components of `G` have codimension at least `k`. -/
private lemma exists_component_eq_of_not_codimension_succ_le {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] {G : Set X} {k : ℕ} (hG : IsClosed G) (hcod : codimComponentsGe G k)
    {Z : IrreducibleCloseds X} (hZG : (Z : Set X) ⊆ G)
    (hnot : ¬((k + 1 : ℕ) : ℕ∞) ≤ codimension Z) :
    ∃ W : IrreducibleCloseds X,
      Maximal (fun T : IrreducibleCloseds X ↦ (T : Set X) ⊆ G) W ∧ Z = W := by
  obtain ⟨W, hZW, hW⟩ := irreducible_subset_component hG Z hZG
  refine ⟨W, hW, ?_⟩
  by_contra hne
  exact hnot (codimension_succ_le_of_lt (lt_of_le_of_ne hZW hne) (hcod W hW))

private lemma exists_scalar_values
    {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
    (x : ι → ClosedPointSpace R) (hx : Function.Injective x)
    (a : ∀ i, ClosedPointResidueField (x i)) :
    ∃ f : R, ∀ i, Ideal.Quotient.mk (x i).1.asIdeal f = a i := by
  classical
  let _ := Fintype.ofFinite ι
  have hmax (i : ι) : (x i).1.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (x i).1).mp (x i).2
  have hcoprime : Pairwise fun i j ↦ IsCoprime (x i).1.asIdeal (x j).1.asIdeal := by
    intro i j hij
    have _ : (x i).1.asIdeal.IsMaximal := hmax i
    have _ : (x j).1.asIdeal.IsMaximal := hmax j
    exact Ideal.isCoprime_of_isMaximal (fun h ↦
      hij (hx (Subtype.ext (PrimeSpectrum.ext h))))
  obtain ⟨f, hf⟩ := Ideal.pi_quotient_surjective hcoprime a
  exact ⟨f, hf⟩

private lemma closed_controlled_components {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] {C F : Set X} (hC : IsClosed C)
    {k : ℕ}
    (hcod : ∀ Z : IrreducibleCloseds X,
      Maximal (fun W : IrreducibleCloseds X ↦ (W : Set X) ⊆ C) Z →
      ¬(Z : Set X) ⊆ F → (k : ℕ∞) ≤ codimension Z) :
    ∃ F' : Set X, IsClosed F' ∧ C ⊆ F ∪ F' ∧ codimComponentsGe F' k := by
  classical
  let K : Set (IrreducibleCloseds X) :=
    {Z | Maximal (fun W : IrreducibleCloseds X ↦ (W : Set X) ⊆ C) Z ∧
      ¬(Z : Set X) ⊆ F}
  let S : Set (Set X) := (fun Z : IrreducibleCloseds X ↦ (Z : Set X)) '' K
  have hKf : K.Finite := (finite_components hC).subset fun _ hZ ↦ hZ.1
  have hSf : S.Finite := hKf.image _
  have hSc : ∀ T ∈ S, IsClosed T := by
    rintro T ⟨Z, hZ, rfl⟩
    exact Z.isClosed
  have hSclosed : IsClosed (⋃₀ S) := by
    rw [Set.sUnion_eq_biUnion]
    exact hSf.isClosed_biUnion hSc
  refine ⟨⋃₀ S, hSclosed, ?_, ?_⟩
  · intro y hyC
    obtain ⟨Z, hZ, hyZ⟩ := mem_component_of_mem_closed hC hyC
    by_cases hZF : (Z : Set X) ⊆ F
    · exact Or.inl (hZF hyZ)
    · exact Or.inr (Set.mem_sUnion.mpr ⟨(Z : Set X), ⟨Z, ⟨hZ, hZF⟩, rfl⟩, hyZ⟩)
  · intro Z hZ
    have hZS : (Z : Set X) ⊆ ⋃₀ S := hZ.prop
    obtain ⟨T, hTS', hZT⟩ := exists_mem_subset_of_subset_sUnion hSf hSc Z.isIrreducible hZS
    obtain ⟨W, hWK, rfl⟩ := hTS'
    obtain rfl := hZ.eq_of_le (Set.subset_sUnion_of_mem ⟨W, hWK, rfl⟩) hZT
    exact hcod _ hWK.1 hWK.2

/-- Suppose that the dependent locus of `h` sections of a finitely presented module is contained
in a closed set `F` of the Noetherian space of closed points. If every canonical quotient `V(y)`
has dimension at least `h + k`, then one can choose a further section with arbitrary prescribed
values at finitely many distinct points of `F`. The new dependent locus is contained in `F`
together with a closed set all of whose irreducible components have codimension at least `k`. -/
@[stacks 0GVB]
theorem exists_section_dependentLocus_subset_union_of_card_add_le_finrank
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [NoetherianSpace (ClosedPointSpace R)]
    {h k : ℕ} (sections : Fin h → M) (F : Set (ClosedPointSpace R)) (hF : IsClosed F)
    (hsections :
      {y | ¬LinearIndependent (ClosedPointResidueField y)
        (fun i ↦ (canonicalKernel M y).mkQ (sectionAt y (sections i)))} ⊆ F)
    {ι : Type w} [Finite ι] (x : ι → ClosedPointSpace R) (hx : Function.Injective x)
    (hxF : ∀ i, x i ∈ F) (v : ∀ i, CanonicalQuotient M (x i))
    (hdim : ∀ y : ClosedPointSpace R,
      h + k ≤ Module.finrank (ClosedPointResidueField y) (CanonicalQuotient M y)) :
    ∃ (s : M) (F' : Set (ClosedPointSpace R)),
      (∀ i, (canonicalKernel M (x i)).mkQ (sectionAt (x i) s) = v i) ∧
        IsClosed F' ∧
        {y | ¬LinearIndependent (ClosedPointResidueField y)
          (fun i ↦ (canonicalKernel M y).mkQ
            (sectionAt y ((Fin.snoc sections s : Fin (h + 1) → M) i)))} ⊆ F ∪ F' ∧
        ∀ Z : IrreducibleCloseds (ClosedPointSpace R),
          Maximal (fun W : IrreducibleCloseds (ClosedPointSpace R) ↦
            (W : Set (ClosedPointSpace R)) ⊆ F') Z →
            (k : ℕ∞) ≤ codimension Z := by
  classical
  induction k generalizing h sections F ι x v with
  | zero =>
      obtain ⟨s, hs⟩ := pi_canonicalQuotient_mkQ_sectionAt_surjective x hx v
      refine ⟨s, Set.univ, ?_, isClosed_univ, ?_, ?_⟩
      · exact fun i ↦ congrFun hs i
      · intro y hy
        exact Or.inr (Set.mem_univ y)
      · intro Z hZ
        exact zero_le
  | succ k ih =>
      have hdim0 (y : ClosedPointSpace R) :
          h + k ≤ Module.finrank (ClosedPointResidueField y) (CanonicalQuotient M y) := by
        exact (Nat.add_le_add_left (Nat.le_succ k) h).trans (hdim y)
      obtain ⟨u, G, hu, hG, hsubG, hcodG⟩ :=
        ih sections F hF hsections x hx hxF v hdim0
      let KG : Set (IrreducibleCloseds (ClosedPointSpace R)) :=
        {Z | Maximal (fun W : IrreducibleCloseds (ClosedPointSpace R) ↦
          (W : Set (ClosedPointSpace R)) ⊆ G) Z ∧
          ¬(Z : Set (ClosedPointSpace R)) ⊆ F}
      have hKGf : KG.Finite := (finite_components hG).subset (by
        intro Z hZ
        exact hZ.1)
      let : Fintype KG := hKGf.fintype
      let yg : KG → ClosedPointSpace R := fun Z ↦
        Classical.choose (exists_point_unique_to_component hG hF Z.1 Z.2.1 Z.2.2)
      have hyg (Z : KG) : yg Z ∈ (Z.1 : Set (ClosedPointSpace R)) ∧
          yg Z ∉ F ∧ ∀ W : IrreducibleCloseds (ClosedPointSpace R),
            Maximal (fun T : IrreducibleCloseds (ClosedPointSpace R) ↦
              (T : Set (ClosedPointSpace R)) ⊆ G) W → W ≠ Z.1 → yg Z ∉ W :=
        Classical.choose_spec (exists_point_unique_to_component hG hF Z.1 Z.2.1 Z.2.2)
      have hLI (Z : KG) : LinearIndependent (ClosedPointResidueField (yg Z))
          (fun i ↦ valueAt (yg Z) (sections i)) := by
        by_contra hn
        exact (hyg Z).2.1 (hsections hn)
      have hextra (Z : KG) : ∃ w : CanonicalQuotient M (yg Z),
          valueAt (yg Z) u + w ∉ Submodule.span (ClosedPointResidueField (yg Z))
            (Set.range fun i ↦ valueAt (yg Z) (sections i)) := by
        have hlt : h < Module.finrank (ClosedPointResidueField (yg Z))
            (CanonicalQuotient M (yg Z)) := by
          have := hdim (yg Z)
          omega
        obtain ⟨r, hr⟩ := exists_linearIndependent_snoc_of_lt_finrank (hLI Z) hlt
        refine ⟨r - valueAt (yg Z) u, ?_⟩
        rw [show valueAt (yg Z) u + (r - valueAt (yg Z) u) = r by abel]
        exact (linearIndependent_finSnoc.mp hr).2
      let w (Z : KG) : CanonicalQuotient M (yg Z) := Classical.choose (hextra Z)
      have hw (Z : KG) : valueAt (yg Z) u + w Z ∉
          Submodule.span (ClosedPointResidueField (yg Z))
            (Set.range fun i ↦ valueAt (yg Z) (sections i)) :=
        Classical.choose_spec (hextra Z)
      let J := Fin (Fintype.card KG)
      let eG : J ≃ KG := (Fintype.equivFin KG).symm
      let x' : Sum ι J → ClosedPointSpace R := Sum.elim x (yg ∘ eG)
      have hx' : Function.Injective x' := by
        intro a b hab
        cases a with
        | inl i =>
          cases b with
          | inl j =>
            change x i = x j at hab
            exact congrArg Sum.inl (hx hab)
          | inr j =>
            exfalso
            change x i = yg (eG j) at hab
            exact (hyg (eG j)).2.1 (hab ▸ hxF i)
        | inr j =>
          cases b with
          | inl i =>
            exfalso
            change yg (eG j) = x i at hab
            exact (hyg (eG j)).2.1 (hab.symm ▸ hxF i)
          | inr l =>
            change yg (eG j) = yg (eG l) at hab
            by_cases hZW : eG j = eG l
            · exact congrArg Sum.inr (eG.injective hZW)
            · exfalso
              have hneq : (eG l).1 ≠ (eG j).1 := by
                intro h
                exact hZW (Subtype.ext h.symm)
              apply (hyg (eG j)).2.2 (eG l).1 (eG l).2.1 hneq
              exact hab.symm ▸ (hyg (eG l)).1
      have hx'FG (a : Sum ι J) : x' a ∈ F ∪ G := by
        cases a with
        | inl i => exact Or.inl (hxF i)
        | inr j => exact Or.inr ((eG j).2.1.prop (hyg (eG j)).1)
      let v' : ∀ a : Sum ι J, CanonicalQuotient M (x' a) := fun a ↦
        match a with
        | .inl _ => 0
        | .inr j => w (eG j)
      have hdim1 (y : ClosedPointSpace R) :
          (h + 1) + k ≤ Module.finrank (ClosedPointResidueField y) (CanonicalQuotient M y) := by
        have := hdim y
        omega
      obtain ⟨t, H, ht, hH, hsubH, hcodH⟩ :=
        ih (Fin.snoc sections u) (F ∪ G) (hF.union hG) hsubG
          x' hx' hx'FG v' hdim1
      let KH : Set (IrreducibleCloseds (ClosedPointSpace R)) :=
        {Z | Maximal (fun W : IrreducibleCloseds (ClosedPointSpace R) ↦
          (W : Set (ClosedPointSpace R)) ⊆ H) Z ∧
          ¬(Z : Set (ClosedPointSpace R)) ⊆ F ∪ G}
      have hKHf : KH.Finite := (finite_components hH).subset (by
        intro Z hZ
        exact hZ.1)
      let : Fintype KH := hKHf.fintype
      let zh : KH → ClosedPointSpace R := fun Z ↦
        Classical.choose
          (exists_point_unique_to_component hH (hF.union hG) Z.1 Z.2.1 Z.2.2)
      have hzh (Z : KH) : zh Z ∈ (Z.1 : Set (ClosedPointSpace R)) ∧
          zh Z ∉ F ∪ G ∧ ∀ W : IrreducibleCloseds (ClosedPointSpace R),
            Maximal (fun T : IrreducibleCloseds (ClosedPointSpace R) ↦
              (T : Set (ClosedPointSpace R)) ⊆ H) W → W ≠ Z.1 → zh Z ∉ W :=
        Classical.choose_spec
          (exists_point_unique_to_component hH (hF.union hG) Z.1 Z.2.1 Z.2.2)
      let L := Fin (Fintype.card KH)
      let eH : L ≃ KH := (Fintype.equivFin KH).symm
      have hyinj : Function.Injective (yg ∘ eG) := by
        intro j l heq
        have hsum : (Sum.inr j : Sum ι J) = Sum.inr l := hx' heq
        exact Sum.inr.inj hsum
      have hzinj : Function.Injective (zh ∘ eH) := by
        intro j l hab
        change zh (eH j) = zh (eH l) at hab
        apply eH.injective
        by_contra hneq
        have hne : (eH l).1 ≠ (eH j).1 := by
          intro heq
          exact hneq (Subtype.ext heq.symm)
        exact (hzh (eH j)).2.2 (eH l).1 (eH l).2.1 hne
          (hab.symm ▸ (hzh (eH l)).1)
      let q : Sum J L → ClosedPointSpace R :=
        Sum.elim (yg ∘ eG) (zh ∘ eH)
      have hq : Function.Injective q := by
        intro a b hab
        cases a with
        | inl j =>
          cases b with
          | inl l => exact congrArg Sum.inl (hyinj hab)
          | inr l =>
            exfalso
            change yg (eG j) = zh (eH l) at hab
            have hyG : yg (eG j) ∈ G := (eG j).2.1.prop (hyg (eG j)).1
            exact (hzh (eH l)).2.1 (Or.inr (hab.symm ▸ hyG))
        | inr j =>
          cases b with
          | inl l =>
            exfalso
            change zh (eH j) = yg (eG l) at hab
            have hyG : yg (eG l) ∈ G := (eG l).2.1.prop (hyg (eG l)).1
            exact (hzh (eH j)).2.1 (Or.inr (hab ▸ hyG))
          | inr l => exact congrArg Sum.inr (hzinj hab)
      let a : ∀ p : Sum J L, ClosedPointResidueField (q p) := fun p ↦
        match p with
        | .inl _ => 1
        | .inr _ => 0
      obtain ⟨f, hf⟩ := exists_scalar_values q hq a
      let s : M := u + f • t
      have hsval (i : ι) : valueAt (x i) s = v i := by
        have htx : valueAt (x i) t = 0 := ht (Sum.inl i)
        change valueAt (x i) (u + f • t) = v i
        rw [valueAt_add, valueAt_smul, htx, smul_zero, add_zero]
        exact hu i
      have hDclosed : IsClosed (dependentLocus (R := R) (Fin.snoc sections s)) :=
        dependentLocus_isClosed (Fin.snoc sections s)
      have hDsubset : dependentLocus (R := R) (Fin.snoc sections s) ⊆ (F ∪ G) ∪ H := by
        intro y hy
        by_contra hnot
        have hraw : LinearIndependent (ClosedPointResidueField y)
            (fun i ↦ valueAt y ((Fin.snoc (Fin.snoc sections u) t) i)) := by
          by_contra hn
          exact hnot (hsubH hn)
        change LinearIndependent (ClosedPointResidueField y)
          (valueAt (M := M) y ∘ Fin.snoc (Fin.snoc sections u) t) at hraw
        rw [Fin.comp_snoc, Fin.comp_snoc] at hraw
        have hLI' := independent_snoc_add_smul
          (fun i ↦ valueAt y (sections i)) (valueAt y u) (valueAt y t)
          (Ideal.Quotient.mk y.1.asIdeal f) hraw
        have hs_y : valueAt y s = valueAt y u +
            Ideal.Quotient.mk y.1.asIdeal f • valueAt y t := by
          change valueAt y (u + f • t) = _
          rw [valueAt_add, valueAt_smul]
        have hLI_s : LinearIndependent (ClosedPointResidueField y)
            (fun i ↦ valueAt y ((Fin.snoc sections s) i)) := by
          change LinearIndependent (ClosedPointResidueField y)
            (valueAt (M := M) y ∘ Fin.snoc sections s)
          rw [Fin.comp_snoc]
          rw [hs_y]
          exact hLI'
        exact hy hLI_s
      obtain ⟨F', hF'closed, hF'sub, hF'cod⟩ :=
        closed_controlled_components hDclosed (F := F) (k := k + 1) (by
          intro Z hZ hZF
          by_contra hnotcod
          have hZG : ¬(Z : Set (ClosedPointSpace R)) ⊆ G := by
            intro hZG
            obtain ⟨W, hW, rfl⟩ :=
              exists_component_eq_of_not_codimension_succ_le hG hcodG hZG hnotcod
            let ZG : KG := ⟨Z, hW, hZF⟩
            let j : J := eG.symm ZG
            have hj : eG j = ZG := eG.apply_symm_apply ZG
            have hyZ : yg (eG j) ∈ Z := by
              rw [hj]
              exact (hyg ZG).1
            have hfj : Ideal.Quotient.mk (yg (eG j)).1.asIdeal f = 1 :=
              hf (Sum.inl j)
            have htj : valueAt (yg (eG j)) t = w (eG j) := ht (Sum.inr j)
            have hsv : valueAt (yg (eG j)) s =
                valueAt (yg (eG j)) u + w (eG j) := by
              change valueAt (yg (eG j)) (u + f • t) = _
              rw [valueAt_add, valueAt_smul_of_one _ _ _ hfj, htj]
            have hLIy : LinearIndependent (ClosedPointResidueField (yg (eG j)))
                (fun i ↦ valueAt (yg (eG j)) ((Fin.snoc sections s) i)) :=
              (independent_snoc_iff sections s (yg (eG j))).2
                ⟨hLI (eG j), by simpa only [hsv] using hw (eG j)⟩
            exact (hZ.prop hyZ) hLIy
          have hZH : ¬(Z : Set (ClosedPointSpace R)) ⊆ H := by
            intro hZH
            obtain ⟨W, hW, rfl⟩ :=
              exists_component_eq_of_not_codimension_succ_le hH hcodH hZH hnotcod
            have hWFG : ¬(Z : Set (ClosedPointSpace R)) ⊆ F ∪ G := fun hZFG ↦
              (irreducible_subset_or_of_subset_union hF hG hZFG).elim hZF hZG
            let ZH : KH := ⟨Z, hW, hWFG⟩
            let l : L := eH.symm ZH
            have hl : eH l = ZH := eH.apply_symm_apply ZH
            have hzZ : zh (eH l) ∈ Z := by
              rw [hl]
              exact (hzh ZH).1
            have hfl : Ideal.Quotient.mk (zh (eH l)).1.asIdeal f = 0 :=
              hf (Sum.inr l)
            have hsv : valueAt (zh (eH l)) s = valueAt (zh (eH l)) u := by
              change valueAt (zh (eH l)) (u + f • t) = _
              rw [valueAt_add, valueAt_smul_of_zero _ _ _ hfl, add_zero]
            have hLIu : LinearIndependent (ClosedPointResidueField (zh (eH l)))
                (fun i ↦ valueAt (zh (eH l)) ((Fin.snoc sections u) i)) := by
              by_contra hn
              exact (hzh (eH l)).2.1 (hsubG hn)
            have hLIz : LinearIndependent (ClosedPointResidueField (zh (eH l)))
                (fun i ↦ valueAt (zh (eH l)) ((Fin.snoc sections s) i)) := by
              rw [independent_snoc_iff] at hLIu ⊢
              exact ⟨hLIu.1, hsv ▸ hLIu.2⟩
            exact (hZ.prop hzZ) hLIz
          have hZunion : (Z : Set (ClosedPointSpace R)) ⊆ F ∪ (G ∪ H) :=
            by simpa only [Set.union_assoc] using (hZ.prop.trans hDsubset)
          rcases irreducible_subset_or_of_subset_union hF (hG.union hH) hZunion with hZF' | hZGH
          · exact hZF hZF'
          · exact (irreducible_subset_or_of_subset_union hG hH hZGH).elim hZG hZH)
      refine ⟨s, F', hsval, hF'closed, ?_, hF'cod⟩
      exact hF'sub

end DependentLocus

section RankOneSplitting

open Set Order TopologicalSpace Topology

private lemma closed_eq_empty_of_components_codimension_gt
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Set X) (hF : IsClosed F)
    (hcodim : ∀ Z : IrreducibleCloseds X,
      Maximal (fun W : IrreducibleCloseds X ↦ (W : Set X) ⊆ F) Z →
        (d + 1 : ℕ∞) ≤ codimension Z) : F = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨Z, hmax, -⟩ := mem_component_of_mem_closed hF hx
  have hc := hcodim Z hmax
  have hupper : (codimension Z : WithBot ℕ∞) ≤ topologicalKrullDim X :=
    Order.coheight_le_krullDim Z
  have : ((d + 1 : ℕ∞) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) :=
    (WithBot.coe_le_coe.mpr hc).trans (hupper.trans hdim)
  have hen : (d + 1 : ℕ∞) ≤ (d : ℕ∞) := WithBot.coe_le_coe.mp this
  have hnat : d + 1 ≤ d := ENat.natCast_le_natCast.mp hen
  omega

private lemma card_le_finrank_of_local_retraction
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] (x : ClosedPointSpace R) (r : ℕ)
    (s : Fin r → LocalizedModule x.1.asIdeal.primeCompl M)
    (p : LocalizedModule x.1.asIdeal.primeCompl M →ₗ[Localization x.1.asIdeal.primeCompl]
      (Fin r → Localization x.1.asIdeal.primeCompl))
    (hp : p.comp (Fintype.linearCombination (Localization x.1.asIdeal.primeCompl) s) =
      LinearMap.id) :
    r ≤ Module.finrank (ClosedPointResidueField x) (CanonicalQuotient M x) := by
  classical
  let S := x.1.asIdeal.primeCompl
  let L := Localization S
  have hpij (i j : Fin r) : p (s j) i = if i = j then 1 else 0 := by
    have h := congrFun (LinearMap.congr_fun hp (Pi.single j 1)) i
    by_cases hij : i = j
    · subst i
      simpa [Fintype.linearCombination_apply] using h
    · simpa [Fintype.linearCombination_apply, hij, Ne.symm hij] using h
  let ell (i : Fin r) : LocalizedModule S M →ₗ[R] L :=
    ((LinearMap.proj i).comp p).restrictScalars R
  have hex (i : Fin r) : ∃ (phi : Module.Dual R M) (t : S),
      (Algebra.linearMap R L) ∘ₗ phi = t •
        (ell i ∘ₗ LocalizedModule.mkLinearMap S M) :=
    Module.FinitePresentation.exists_lift_of_isLocalizedModule S
      (Algebra.linearMap R L) (ell i ∘ₗ LocalizedModule.mkLinearMap S M)
  choose phi t ht using hex
  choose mu hu using fun j ↦ IsLocalizedModule.surj S
    (LocalizedModule.mkLinearMap S M) (s j)
  let q : R →+* ClosedPointResidueField x := Ideal.Quotient.mk x.1.asIdeal
  have hunit (y : S) : IsUnit (q y.1) :=
    isUnit_iff_ne_zero.mpr fun hy ↦ y.2 (Ideal.Quotient.eq_zero_iff_mem.mp hy)
  let rho : L →+* ClosedPointResidueField x := IsLocalization.lift hunit
  have hrho (a : R) : rho (algebraMap R L a) = q a := IsLocalization.lift_eq hunit a
  have heval (i j : Fin r) :
      q (phi i (mu j).1) = q (t i).1 * q (mu j).2.1 * (if i = j then 1 else 0) := by
    have h := congrArg rho (LinearMap.congr_fun (ht i) (mu j).1)
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, ell, LinearMap.coe_restrictScalars,
      LinearMap.proj_apply, LinearMap.smul_apply, Submonoid.smul_def] at h
    rw [Algebra.smul_def, map_mul, hrho, hrho] at h
    have hp' : rho (p (LocalizedModule.mkLinearMap S M (mu j).1) i) =
        q (mu j).2.1 * (if i = j then 1 else 0) := by
      rw [← hu j, LinearMap.map_smul_of_tower, Pi.smul_apply, Submonoid.smul_def, Algebra.smul_def,
        map_mul, hrho, hpij]
      split <;> simp
    rw [h, hp']
    ring
  let vec (j : Fin r) : CanonicalQuotient M x :=
    (q (mu j).2.1)⁻¹ • (canonicalKernel M x).mkQ (sectionAt x (mu j).1)
  let dual (i : Fin r) : Module.Dual (ClosedPointResidueField x) (CanonicalQuotient M x) :=
    (q (t i).1)⁻¹ • (canonicalKernel M x).liftQ (fiberFunctional x (phi i))
      fun y hy ↦ (mem_canonicalKernel_iff x y).mp hy (phi i)
  have hli : LinearIndependent (ClosedPointResidueField x) vec := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one _ dual
    · intro i j hij
      simp only [dual, vec, LinearMap.smul_apply, map_smul]
      change (q (mu j).2.1)⁻¹ * ((q (t i).1)⁻¹ *
        fiberFunctional x (phi i) (sectionAt x (mu j).1)) = 0
      rw [fiberFunctional_sectionAt, heval]
      simp [hij]
    · intro i
      simp only [dual, vec, LinearMap.smul_apply, map_smul]
      change (q (mu i).2.1)⁻¹ * ((q (t i).1)⁻¹ *
        fiberFunctional x (phi i) (sectionAt x (mu i).1)) = 1
      rw [fiberFunctional_sectionAt, heval]
      simp [(hunit (t i)).ne_zero, (hunit (mu i).2).ne_zero]
  simpa using hli.fintype_card_le_finrank

/-- Let `M` be a finitely presented module over a commutative ring whose Noetherian space of
closed points has dimension at most `d`. If at every closed point the localization of `M` has
a free direct summand of some rank strictly greater than `d`, then a rank-one free summand
splits from `M`. -/
@[stacks 0GVC]
theorem exists_linearEquiv_prod_of_local_free_summand_rank_gt_dimension
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] [NoetherianSpace (ClosedPointSpace R)]
    (d : ℕ) (hdim : topologicalKrullDim (ClosedPointSpace R) ≤ (d : WithBot ℕ∞))
    (hlocal : ∀ x : ClosedPointSpace R,
      ∃ r : ℕ, d < r ∧
        ∃ s : Fin r → LocalizedModule x.1.asIdeal.primeCompl M,
          ∃ p : LocalizedModule x.1.asIdeal.primeCompl M →ₗ[Localization x.1.asIdeal.primeCompl]
              (Fin r → Localization x.1.asIdeal.primeCompl),
            p.comp (Fintype.linearCombination (Localization x.1.asIdeal.primeCompl) s) =
              LinearMap.id) :
    ∃ N : Submodule R M, Nonempty (M ≃ₗ[R] R × N) := by
  classical
  have hfd (y : ClosedPointSpace R) :
      d + 1 ≤ Module.finrank (ClosedPointResidueField y) (CanonicalQuotient M y) := by
    obtain ⟨r, hdr, s, p, hp⟩ := hlocal y
    exact (by omega : d + 1 ≤ r).trans (card_le_finrank_of_local_retraction y r s p hp)
  let sections : Fin 0 → M := Fin.elim0
  obtain ⟨s, F, -, hF, hdep, hcodim⟩ :=
    exists_section_dependentLocus_subset_union_of_card_add_le_finrank
      (k := d + 1) sections ∅ isClosed_empty (by
        intro (y : ClosedPointSpace R) hy
        exact (hy (linearIndependent_empty_type :
          LinearIndependent (ClosedPointResidueField y)
            (fun i : Fin 0 ↦ (canonicalKernel M y).mkQ (sectionAt y (sections i))))).elim)
      (x := fun i : Fin 0 ↦ i.elim0) (fun i ↦ i.elim0)
      (by simp) (fun i : Fin 0 ↦ i.elim0) (fun y ↦ by simpa only [zero_add] using hfd y)
  have hFempty : F = ∅ :=
    closed_eq_empty_of_components_codimension_gt d hdim F hF (by simpa using hcodim)
  have hli (y : ClosedPointSpace R) : LinearIndependent (ClosedPointResidueField y)
      (fun _ : Fin 1 ↦ (canonicalKernel M y).mkQ (sectionAt y s)) := by
    by_contra hn
    have : y ∈ F := by
      simpa using hdep (by simpa [sections, Fin.snoc] using hn)
    simp [hFempty] at this
  let ev : Module.Dual R M →ₗ[R] R :=
    { toFun := fun phi ↦ phi s
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hev : Function.Surjective ev := by
    rw [← LinearMap.range_eq_top]
    by_contra hrange
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal ev.range hrange
    let x : ClosedPointSpace R :=
      ⟨⟨I, hI.isPrime⟩, (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hI⟩
    have hnz : (canonicalKernel M x).mkQ (sectionAt x s) ≠ 0 := by
      exact (hli x).ne_zero 0
    have hnotmem : sectionAt x s ∉ canonicalKernel M x := by
      simpa [Submodule.Quotient.mk_eq_zero] using hnz
    rw [mem_canonicalKernel_iff] at hnotmem
    push Not at hnotmem
    obtain ⟨phi, hphi⟩ := hnotmem
    have hmem : phi s ∈ I := hle ⟨phi, rfl⟩
    exact hphi (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
  obtain ⟨phi, hphi⟩ := hev 1
  have hphis : phi s = 1 := by simpa [ev] using hphi
  let e : M →ₗ[R] R × LinearMap.ker phi :=
    { toFun := fun m ↦ (phi m, ⟨m - phi m • s, by simp [hphis]⟩)
      map_add' := by
        intro a b
        apply Prod.ext
        · exact map_add phi a b
        · apply Subtype.ext
          change a + b - phi (a + b) • s =
            (a - phi a • s) + (b - phi b • s)
          rw [map_add, add_smul]
          abel
      map_smul' := by
        intro a b
        apply Prod.ext
        · exact map_smul phi a b
        · apply Subtype.ext
          change a • b - phi (a • b) • s = a • (b - phi b • s)
          simp only [map_smul, smul_eq_mul, mul_smul, smul_sub] }
  refine ⟨LinearMap.ker phi, ⟨LinearEquiv.ofBijective e ?_⟩⟩
  constructor
  · intro a b hab
    have h1 : phi a = phi b := congrArg Prod.fst hab
    have h2 : a - phi a • s = b - phi b • s := congrArg (fun z ↦ (z.2 : M)) hab
    simpa [h1] using h2
  · rintro ⟨a, n⟩
    refine ⟨a • s + n, ?_⟩
    apply Prod.ext
    · simp [e, hphis]
    · apply Subtype.ext
      simp [e, hphis]

end RankOneSplitting
