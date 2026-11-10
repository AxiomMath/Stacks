module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.InitialSpan

/-!
# The determinant map of a short exact sequence

For a short exact sequence `0 → K → L → M → 0` of finite-length modules over a local ring,
concatenating an admissible sequence in `K` with lifts of an admissible sequence in `M`
gives an admissible sequence in `L`, and its symbol depends only on the two symbols it was
built from. This defines a canonical linear map from the tensor product of the outer
determinants to the determinant of the middle module.

## Main definitions

* `Module.FiniteLength.IsDeterminantExactSequenceMap` is the defining rule for the map.
* `Module.FiniteLength.determinantExactSequenceMap` is the canonical determinant map
  associated to a short exact sequence.

## Main results

* `Module.FiniteLength.existsUnique_determinantExactSequenceMap` is the existence and
  uniqueness of a map obeying the rule.
* `Module.FiniteLength.determinantExactSequenceMap_spec` gives its value on nonzero symbols.
* `Module.FiniteLength.eq_determinantExactSequenceMap` records the canonicity of the
  construction.

## Implementation notes

The short exact sequence is represented by two linear maps, exactness at the middle term,
injectivity of the first map, and surjectivity of the second. The predicate
`IsDeterminantExactSequenceMap` records the defining rule, including both the length
identification needed to concatenate the sequences and admissibility of the concatenation.
The map is selected from the unique map satisfying this rule; its specification and
uniqueness lemmas let clients use it without unfolding that selection.

The work of the file is to check that the concatenated symbol is well defined: it does not
depend on the choice of lifts, and it transforms correctly under each of the three
determinant relations applied to either of the two factors.

## References

* [Stacks Project, Tag 02PA](https://stacks.math.columbia.edu/tag/02PA)
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
namespace Module.FiniteLength

universe u v w x

/-- The length of the middle term of a short exact sequence of finite-length modules is the
sum of the lengths of the outer terms. -/
public lemma exactSequence_moduleLength
    {R : Type u} [CommRing R] {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p) (hK : IsFiniteLength R K)
    (hM : IsFiniteLength R M) :
    moduleLength R L = moduleLength R K + moduleLength R M := by
  unfold moduleLength
  rw [Module.length_eq_add_of_exact i p hi hp hip,
    ENat.toNat_add (Module.length_ne_top_iff.mpr hK) (Module.length_ne_top_iff.mpr hM)]

/-- An entry of the left block of a concatenated sequence lies in the span of the entries
preceding a later index of the left block. -/
private lemma append_left_mem_spanBefore
    {R : Type u} [Ring R] {L : Type w} [AddCommGroup L] [Module R L]
    {n m ell : ℕ} (h : ell = n + m) (g : Fin n → L) (f : Fin m → L)
    (a : Fin (n + m)) (j : Fin n) (hj : j.val < a.val) :
    g j ∈ spanBefore (R := R)
      (fun k : Fin ell ↦ Fin.append g f (Fin.cast h k)) (Fin.cast h.symm a) := by
  refine Submodule.subset_span ⟨Fin.cast h.symm (Fin.castAdd m j), ?_, ?_⟩
  · change (Fin.cast h.symm (Fin.castAdd m j)).val < (Fin.cast h.symm a).val
    simpa only [Fin.val_cast, Fin.val_castAdd] using hj
  · simp

/-- An entry of the left block of a concatenated sequence lies in the span of the entries
preceding an index of the right block. -/
private lemma append_right_mem_spanBefore
    {R : Type u} [Ring R] {L : Type w} [AddCommGroup L] [Module R L]
    {n m ell : ℕ} (h : ell = n + m) (g : Fin n → L) (f : Fin m → L)
    (a : Fin (n + m)) (j : Fin m) (hj : n + j.val < a.val) :
    f j ∈ spanBefore (R := R)
      (fun k : Fin ell ↦ Fin.append g f (Fin.cast h k)) (Fin.cast h.symm a) := by
  refine Submodule.subset_span ⟨Fin.cast h.symm (Fin.natAdd n j), ?_, ?_⟩
  · change (Fin.cast h.symm (Fin.natAdd n j)).val < (Fin.cast h.symm a).val
    simpa only [Fin.val_cast, Fin.val_natAdd] using hj
  · simp

/-- On the left block, the span of the preceding entries of the concatenation is the image of
the span of the preceding entries of the sequence in the submodule. -/
private lemma append_left_spanBefore
    {R : Type u} [Ring R] {K : Type v} {L : Type w}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    {n m ell : ℕ} (h : ell = n + m) (i : K →ₗ[R] L)
    (e : Fin n → K) (f : Fin m → L) (a : Fin n) (z : K)
    (hz : z ∈ spanBefore (R := R) e a) :
    i z ∈ spanBefore (R := R)
      (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k))
      (Fin.cast h.symm (Fin.castAdd m a)) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨j, hj, rfl⟩ := hz
      exact append_left_mem_spanBefore h (fun b ↦ i (e b)) f
        (Fin.castAdd m a) j hj
  | zero => simp
  | add x y hx hy ihx ihy => simpa using
      (spanBefore (R := R)
        (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k))
        (Fin.cast h.symm (Fin.castAdd m a))).add_mem ihx ihy
  | smul r x hx ih => simpa using
      (spanBefore (R := R)
        (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k))
        (Fin.cast h.symm (Fin.castAdd m a))).smul_mem r ih

/-- An element of the kernel of the projection that lies in the span of the preceding entries
of the quotient sequence is, after lifting, in the span of the preceding entries of the
concatenation. -/
private lemma append_kernel_mem_spanBefore
    {R : Type u} [Ring R] {K : Type v} {L : Type w}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    {n m ell : ℕ} (h : ell = n + m) (i : K →ₗ[R] L)
    (e : Fin n → K) (he : Submodule.span R (Set.range e) = ⊤)
    (f : Fin m → L) (a : Fin m) (z : K) :
    i z ∈ spanBefore (R := R)
      (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k))
      (Fin.cast h.symm (Fin.natAdd n a)) := by
  let T : Submodule R L := spanBefore (R := R)
    (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k))
    (Fin.cast h.symm (Fin.natAdd n a))
  have hspan_i : (Submodule.span R (Set.range e)).map i ≤ T := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact append_left_mem_spanBefore h (fun b ↦ i (e b)) f
      (Fin.natAdd n a) j (by have := j.isLt; simp only [Fin.val_natAdd]; omega)
  exact hspan_i ⟨z, he ▸ Submodule.mem_top, rfl⟩

/-- Every element of the span of the entries preceding an index of the right block has a
representative of a specific shape: the lift of an element of the span of the preceding
entries of the quotient sequence, corrected by an element of the submodule. -/
private lemma exists_lift_spanBefore_append
    {R : Type u} [Ring R] {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    {n m ell : ℕ} (h : ell = n + m)
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (e : Fin n → K) (f : Fin m → L) (fbar : Fin m → M)
    (hf : ∀ a, p (f a) = fbar a) (a : Fin m) (x : M)
    (hx : x ∈ spanBefore (R := R) fbar a) :
    ∃ y : L, y ∈ spanBefore (R := R)
      (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k))
      (Fin.cast h.symm (Fin.natAdd n a)) ∧ p y = x := by
  let T : Submodule R L := spanBefore (R := R)
    (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k))
    (Fin.cast h.symm (Fin.natAdd n a))
  have hmap : spanBefore (R := R) fbar a ≤ T.map p := by
    apply Submodule.span_le.mpr
    rintro z ⟨j, hj, rfl⟩
    refine Submodule.mem_map.mpr ⟨f j, ?_, hf j⟩
    exact append_right_mem_spanBefore h (fun b ↦ i (e b)) f
      (Fin.natAdd n a) j (by simpa only [Fin.val_natAdd] using Nat.add_lt_add_left hj n)
  exact Submodule.mem_map.mp (hmap hx)

/-- On the right block, the projection carries the span of the preceding entries of the
concatenation onto the span of the preceding entries of the quotient sequence. -/
private lemma append_right_spanBefore
    {R : Type u} [CommRing R] {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    {n m ell : ℕ} (h : ell = n + m) (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hip : Function.Exact i p) (e : Fin n → K)
    (he : Submodule.span R (Set.range e) = ⊤)
    (f : Fin m → L) (fbar : Fin m → M) (hf : ∀ a, p (f a) = fbar a)
    (a b : Fin m) (r : R)
    (hr : r • fbar a ∈ spanBefore (R := R) fbar b) :
    r • f a ∈ spanBefore (R := R)
      (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k))
      (Fin.cast h.symm (Fin.natAdd n b)) := by
  let T : Submodule R L := spanBefore (R := R)
    (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k))
    (Fin.cast h.symm (Fin.natAdd n b))
  obtain ⟨y, hy, hpy⟩ :=
    exists_lift_spanBefore_append h i p e f fbar hf b (r • fbar a) hr
  have hrange : r • f a - y ∈ LinearMap.range i := by
    rw [← hip.linearMap_ker_eq, LinearMap.mem_ker, map_sub, hpy, map_smul, hf a, sub_self]
  obtain ⟨z, hzi⟩ := LinearMap.mem_range.mp hrange
  have hiz : i z ∈ T := append_kernel_mem_spanBefore h i e he f b z
  change r • f a ∈ T
  rw [show r • f a = y + i z by rw [hzi]; abel]
  exact T.add_mem hy hiz

/-- The concatenation of an admissible sequence in the submodule with lifts of an admissible
sequence in the quotient is admissible. -/
private lemma admissible_append_exact
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    {n m ell : ℕ} (h : ell = n + m)
    (i : K →ₗ[R] L) (p : L →ₗ[R] M) (hip : Function.Exact i p)
    (e : Fin n → K) (he : IsAdmissibleSequence (R := R) e)
    (hspan : Submodule.span R (Set.range e) = ⊤)
    (f : Fin m → L) (fbar : Fin m → M)
    (hf : ∀ a, p (f a) = fbar a)
    (hbar : IsAdmissibleSequence (R := R) fbar) :
    IsAdmissibleSequence (R := R)
      (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k)) := by
  cases h
  intro j r hr
  cases j using Fin.addCases with
  | left a =>
      simpa only [Fin.cast_refl, id_eq, Fin.append_left, map_smul] using
        (append_left_spanBefore rfl i e f a (r • e a) (he a r hr))
  | right a =>
      simpa only [Fin.cast_refl, id_eq, Fin.append_right] using
        (append_right_spanBefore rfl i p hip e hspan f fbar hf a a r (hbar a r hr))

/-- Two lifts of the same quotient entry differ by an element of the submodule, hence by an
element of the span of the entries preceding it in the concatenation. -/
private lemma append_lift_difference_mem_spanBefore
    {R : Type u} [CommRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    {n m ell : ℕ} (h : ell = n + m)
    (i : K →ₗ[R] L) (p : L →ₗ[R] M) (hip : Function.Exact i p)
    (e : Fin n → K) (he : Submodule.span R (Set.range e) = ⊤)
    (f f' : Fin m → L) (a : Fin m)
    (hpa : p (f a) = p (f' a)) :
    f a - f' a ∈ spanBefore (R := R)
      (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k))
      (Fin.cast h.symm (Fin.natAdd n a)) := by
  have hker : f a - f' a ∈ LinearMap.ker p := by
    rw [LinearMap.mem_ker, map_sub, hpa]
    simp
  have hrange : f a - f' a ∈ LinearMap.range i := by
    rw [← hip.linearMap_ker_eq]
    exact hker
  obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hrange
  rw [← hz]
  exact append_kernel_mem_spanBefore h i e he f a z

/-- Updating an entry of the right block of a concatenation is the concatenation with the
corresponding lift updated. -/
private lemma append_update_right
    {L : Type w} {n m ell : ℕ} (h : ell = n + m)
    (g : Fin n → L) (f : Fin m → L) (a : Fin m) (z : L) :
    Function.update
      (fun k : Fin ell ↦ Fin.append g f (Fin.cast h k))
      (Fin.cast h.symm (Fin.natAdd n a)) z =
    (fun k : Fin ell ↦ Fin.append g (Function.update f a z) (Fin.cast h k)) := by
  classical
  cases h
  funext j
  cases j using Fin.addCases with
  | left b =>
      have hne : Fin.castAdd m b ≠ Fin.natAdd n a := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        have := b.isLt
        omega
      simp only [Fin.cast_refl, id_eq, Fin.append_left,
        Function.update_of_ne hne]
  | right b =>
      by_cases hba : b = a
      · subst b
        simp only [Fin.cast_refl, id_eq, Fin.append_right, Function.update_self]
      · have hne : Fin.natAdd n b ≠ Fin.natAdd n a := by
          intro heq
          apply hba
          apply Fin.ext
          have hv := congrArg Fin.val heq
          simp only [Fin.val_natAdd] at hv
          omega
        simp only [Fin.cast_refl, id_eq, Fin.append_right,
          Function.update_of_ne hne, Function.update_of_ne hba]

/-- Updating an entry of the left block of a concatenation is the concatenation with the
corresponding entry of the submodule sequence updated. -/
private lemma append_update_left
    {K : Type v} {L : Type w} {n m ell : ℕ} (h : ell = n + m)
    (i : K → L) (e : Fin n → K) (f : Fin m → L) (a : Fin n) (z : K) :
    Function.update
      (fun k : Fin ell ↦ Fin.append (fun b ↦ i (e b)) f (Fin.cast h k))
      (Fin.cast h.symm (Fin.castAdd m a)) (i z) =
    (fun k : Fin ell ↦
      Fin.append (fun b ↦ i (Function.update e a z b)) f (Fin.cast h k)) := by
  classical
  cases h
  funext j
  cases j using Fin.addCases with
  | left b =>
      by_cases hba : b = a
      · subst b
        simp only [Fin.cast_refl, id_eq, Fin.append_left, Function.update_self]
      · have hne : Fin.castAdd m b ≠ Fin.castAdd m a := by
          intro heq
          apply hba
          exact Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val heq)
        simp only [Fin.cast_refl, id_eq, Fin.append_left,
          Function.update_of_ne hne, Function.update_of_ne hba]
  | right b =>
      have hne : Fin.natAdd n b ≠ Fin.castAdd m a := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        have := a.isLt
        omega
      simp only [Fin.cast_refl, id_eq, Fin.append_right, Function.update_of_ne hne]

/-- Exchanging two entries of the left block of a concatenation is the concatenation with the
corresponding entries of the submodule sequence exchanged. -/
private lemma append_swap_left
    {K : Type v} {L : Type w} {n m ell : ℕ} (h : ell = n + m)
    (i : K → L) (e : Fin n → K) (f : Fin m → L) (a b : Fin n) :
    Function.update
      (Function.update
        (fun k : Fin ell ↦ Fin.append (fun j ↦ i (e j)) f (Fin.cast h k))
        (Fin.cast h.symm (Fin.castAdd m b)) (i (e a)))
      (Fin.cast h.symm (Fin.castAdd m a)) (i (e b)) =
    (fun k : Fin ell ↦ Fin.append
      (fun j ↦ i (Function.update (Function.update e b (e a)) a (e b) j))
      f (Fin.cast h k)) := by
  calc
    _ = Function.update
      (fun k : Fin ell ↦ Fin.append
        (fun j ↦ i (Function.update e b (e a) j)) f (Fin.cast h k))
      (Fin.cast h.symm (Fin.castAdd m a)) (i (e b)) := by
        rw [append_update_left h i e f b (e a)]
    _ = _ := append_update_left h i (Function.update e b (e a)) f a (e b)

/-- Exchanging two entries of the right block of a concatenation is the concatenation with the
corresponding lifts exchanged. -/
private lemma append_swap_right
    {L : Type w} {n m ell : ℕ} (h : ell = n + m)
    (g : Fin n → L) (f : Fin m → L) (a b : Fin m) :
    Function.update
      (Function.update
        (fun k : Fin ell ↦ Fin.append g f (Fin.cast h k))
        (Fin.cast h.symm (Fin.natAdd n b)) (f a))
      (Fin.cast h.symm (Fin.natAdd n a)) (f b) =
    (fun k : Fin ell ↦ Fin.append g
      (Function.update (Function.update f b (f a)) a (f b))
      (Fin.cast h k)) := by
  calc
    _ = Function.update
      (fun k : Fin ell ↦ Fin.append g (Function.update f b (f a)) (Fin.cast h k))
      (Fin.cast h.symm (Fin.natAdd n a)) (f b) := by
        rw [append_update_right h g f b (f a)]
    _ = _ := append_update_right h g (Function.update f b (f a)) a (f b)

/-- The unit-change relation for a sequence and the update of one of its entries. -/
private lemma symbol_unitChange_of_update_eq
    {R : Type u} [CommRing R] [IsLocalRing R] {L : Type w} [AddCommGroup L] [Module R L]
    {s s' : Fin (moduleLength R L) → L} (hs : IsAdmissibleSequence (R := R) s)
    (hs' : IsAdmissibleSequence (R := R) s') (a : Fin (moduleLength R L)) (unit : Rˣ)
    (z x : L) (ha : s a = (unit : R) • z + x) (hx : x ∈ spanBefore (R := R) s a)
    (heq : Function.update s a z = s') :
    symbol ⟨s, hs⟩ = IsLocalRing.residue R unit • symbol ⟨s', hs'⟩ := by
  subst heq
  exact symbol_unitChange ⟨s, hs⟩ a unit z x ha hx hs'

/-- The adjacent-transposition relation for a sequence and the exchange of two of its
entries. -/
private lemma symbol_swap_of_update_eq
    {R : Type u} [CommRing R] [IsLocalRing R] {L : Type w} [AddCommGroup L] [Module R L]
    {s s' : Fin (moduleLength R L) → L} (hs : IsAdmissibleSequence (R := R) s)
    (hs' : IsAdmissibleSequence (R := R) s') (a b : Fin (moduleLength R L))
    (hba : b.val + 1 = a.val)
    (ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R → r • s a ∈ spanBefore (R := R) s b)
    (heq : Function.update (Function.update s b (s a)) a (s b) = s') :
    symbol ⟨s, hs⟩ = -symbol ⟨s', hs'⟩ := by
  subst heq
  exact symbol_swap ⟨s, hs⟩ a b hba ha hs'

/-- Replacing a lift by another lift of the same quotient entry does not change the symbol of
the concatenation. -/
private lemma symbol_append_update_right
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M) (hip : Function.Exact i p)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K)
    (he : Submodule.span R (Set.range e.1) = ⊤)
    (fbar : AdmissibleSequence R M)
    (f : Fin (moduleLength R M) → L)
    (hf : ∀ a, p (f a) = fbar.1 a)
    (a : Fin (moduleLength R M)) (z : L)
    (hz : p z = fbar.1 a)
    (hs : IsAdmissibleSequence (R := R)
      (fun k : Fin (moduleLength R L) ↦ Fin.append (fun b ↦ i (e.1 b)) f (Fin.cast hlen k)))
    (hs' : IsAdmissibleSequence (R := R)
      (fun k : Fin (moduleLength R L) ↦
        Fin.append (fun b ↦ i (e.1 b)) (Function.update f a z) (Fin.cast hlen k))) :
    symbol ⟨_, hs⟩ = symbol ⟨_, hs'⟩ := by
  classical
  have hmem := append_lift_difference_mem_spanBefore hlen i p hip e.1 he f
    (Function.update f a z) a (by simp [hf a, hz])
  rw [Function.update_self] at hmem
  simpa using symbol_unitChange_of_update_eq hs hs' _ 1 z (f a - z) (by simp) hmem
    (append_update_right hlen (fun b ↦ i (e.1 b)) f a z)

/-- The symbol of the concatenation does not depend on the choice of lifts. -/
private lemma symbol_append_lifts_eq
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M) (hip : Function.Exact i p)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K)
    (he : Submodule.span R (Set.range e.1) = ⊤)
    (fbar : AdmissibleSequence R M)
    (f g : Fin (moduleLength R M) → L)
    (hf : ∀ a, p (f a) = fbar.1 a)
    (hg : ∀ a, p (g a) = fbar.1 a)
    (hfa : IsAdmissibleSequence (R := R)
      (fun k : Fin (moduleLength R L) ↦
        Fin.append (fun b ↦ i (e.1 b)) f (Fin.cast hlen k)))
    (hga : IsAdmissibleSequence (R := R)
      (fun k : Fin (moduleLength R L) ↦
        Fin.append (fun b ↦ i (e.1 b)) g (Fin.cast hlen k))) :
    symbol ⟨_, hfa⟩ = symbol ⟨_, hga⟩ := by
  classical
  let u (s : Finset (Fin (moduleLength R M))) (a : Fin (moduleLength R M)) : L :=
    if a ∈ s then g a else f a
  have hu (s : Finset (Fin (moduleLength R M))) (a) : p (u s a) = fbar.1 a := by
    by_cases ha : a ∈ s <;> simp [u, ha, hf a, hg a]
  have hA (s : Finset (Fin (moduleLength R M))) :
      IsAdmissibleSequence (R := R)
        (fun k : Fin (moduleLength R L) ↦
          Fin.append (fun b ↦ i (e.1 b)) (u s) (Fin.cast hlen k)) :=
    admissible_append_exact hlen i p hip e.1 e.2 he (u s) fbar.1 (hu s) fbar.2
  let E (s : Finset (Fin (moduleLength R M))) : AdmissibleSequence R L :=
    ⟨fun k ↦ Fin.append (fun b ↦ i (e.1 b)) (u s) (Fin.cast hlen k), hA s⟩
  have hstep (s : Finset (Fin (moduleLength R M)))
      (a : Fin (moduleLength R M)) (ha : a ∉ s) :
      symbol (E s) = symbol (E (insert a s)) := by
    have hup : Function.update (u s) a (g a) = u (insert a s) := by
      funext b
      by_cases hba : b = a
      · subst b
        simp [u]
      · simp [u, Finset.mem_insert, hba]
    have hz : p (g a) = fbar.1 a := hg a
    have huA : IsAdmissibleSequence (R := R)
        (fun k : Fin (moduleLength R L) ↦
          Fin.append (fun b ↦ i (e.1 b))
            (Function.update (u s) a (g a)) (Fin.cast hlen k)) := by
      rw [hup]
      exact hA (insert a s)
    have hs := symbol_append_update_right i p hip hlen e he fbar (u s) (hu s)
      a (g a) hz (hA s) huA
    simpa only [E, hup] using hs
  have hall (s : Finset (Fin (moduleLength R M))) :
      symbol (E ∅) = symbol (E s) := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert a s ha ih => exact ih.trans (hstep s a ha)
  have hstart : E ∅ =
      (⟨fun k ↦ Fin.append (fun b ↦ i (e.1 b)) f (Fin.cast hlen k), hfa⟩ :
        AdmissibleSequence R L) := by
    apply Subtype.ext
    funext k
    simp [E, u]
  have hend : E Finset.univ =
      (⟨fun k ↦ Fin.append (fun b ↦ i (e.1 b)) g (Fin.cast hlen k), hga⟩ :
        AdmissibleSequence R L) := by
    apply Subtype.ext
    funext k
    simp [E, u]
  simpa only [hstart, hend] using hall Finset.univ

/-- The symbol of the concatenation of an admissible sequence in the submodule with lifts of
an admissible sequence in the quotient, taken to be zero when either symbol vanishes. -/
private noncomputable def concatSymbol
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K) (fbar : AdmissibleSequence R M) :
    determinant R L := by
  classical
  by_cases he : symbol e = 0
  · exact 0
  by_cases hf : symbol fbar = 0
  · exact 0
  let f : Fin (moduleLength R M) → L :=
    fun a ↦ Classical.choose (hp (fbar.1 a))
  have hlift : ∀ a, p (f a) = fbar.1 a :=
    fun a ↦ Classical.choose_spec (hp (fbar.1 a))
  have hspan := span_eq_top_of_symbol_ne_zero hK e he
  exact symbol ⟨fun k ↦ Fin.append (fun b ↦ i (e.1 b)) f (Fin.cast hlen k),
    admissible_append_exact hlen i p hip e.1 e.2 hspan f fbar.1 hlift fbar.2⟩

/-- `concatSymbol` is computed by any choice of lifts. -/
private lemma concatSymbol_eq_of_lifts
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K) (fbar : AdmissibleSequence R M)
    (he : symbol e ≠ 0) (hf : symbol fbar ≠ 0)
    (f : Fin (moduleLength R M) → L)
    (hflift : ∀ a, p (f a) = fbar.1 a) :
    concatSymbol i p hp hip hK hlen e fbar =
      symbol ⟨fun k ↦ Fin.append (fun b ↦ i (e.1 b)) f (Fin.cast hlen k),
        admissible_append_exact hlen i p hip e.1 e.2 (span_eq_top_of_symbol_ne_zero hK e he)
          f fbar.1 hflift fbar.2⟩ := by
  classical
  unfold concatSymbol
  simp only [dite_eq_right he, dite_eq_right hf]
  exact symbol_append_lifts_eq i p hip hlen e
    (span_eq_top_of_symbol_ne_zero hK e he) fbar
    (fun a ↦ Classical.choose (hp (fbar.1 a))) f
    (fun a ↦ Classical.choose_spec (hp (fbar.1 a))) hflift _ _

/-- `concatSymbol` vanishes when the symbol in the submodule does. -/
private lemma concatSymbol_eq_zero_of_left
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K) (fbar : AdmissibleSequence R M)
    (he : symbol e = 0) : concatSymbol i p hp hip hK hlen e fbar = 0 := by
  simp only [concatSymbol, dite_eq_left he]

/-- `concatSymbol` vanishes when the symbol in the quotient does. -/
private lemma concatSymbol_eq_zero_of_right
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K) (fbar : AdmissibleSequence R M)
    (hf : symbol fbar = 0) : concatSymbol i p hp hip hK hlen e fbar = 0 := by
  unfold concatSymbol
  split_ifs with he
  · rfl
  · simp

/-- A relation `concatSymbol e = c • concatSymbol e'` in the submodule variable reduces to the
case where all symbols involved are nonzero. -/
private lemma concatSymbol_smul_left_of_ne_zero
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e e' : AdmissibleSequence R K) (fbar : AdmissibleSequence R M)
    (c : IsLocalRing.ResidueField R) (hc : c ≠ 0) (hsym : symbol e = c • symbol e')
    (main : symbol e ≠ 0 → symbol e' ≠ 0 → symbol fbar ≠ 0 →
      concatSymbol i p hp hip hK hlen e fbar = c • concatSymbol i p hp hip hK hlen e' fbar) :
    concatSymbol i p hp hip hK hlen e fbar = c • concatSymbol i p hp hip hK hlen e' fbar := by
  by_cases hf : symbol fbar = 0
  · rw [concatSymbol_eq_zero_of_right i p hp hip hK hlen e fbar hf,
      concatSymbol_eq_zero_of_right i p hp hip hK hlen e' fbar hf, smul_zero]
  by_cases he : symbol e = 0
  · have he' : symbol e' = 0 := (smul_eq_zero.mp (hsym.symm.trans he)).resolve_left hc
    rw [concatSymbol_eq_zero_of_left i p hp hip hK hlen e fbar he,
      concatSymbol_eq_zero_of_left i p hp hip hK hlen e' fbar he', smul_zero]
  exact main he (fun hz ↦ he (by rw [hsym, hz, smul_zero])) hf

/-- A relation `concatSymbol fbar = c • concatSymbol fbar'` in the quotient variable reduces to
the case where all symbols involved are nonzero. -/
private lemma concatSymbol_smul_right_of_ne_zero
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K) (fbar fbar' : AdmissibleSequence R M)
    (c : IsLocalRing.ResidueField R) (hc : c ≠ 0) (hsym : symbol fbar = c • symbol fbar')
    (main : symbol e ≠ 0 → symbol fbar ≠ 0 → symbol fbar' ≠ 0 →
      concatSymbol i p hp hip hK hlen e fbar = c • concatSymbol i p hp hip hK hlen e fbar') :
    concatSymbol i p hp hip hK hlen e fbar = c • concatSymbol i p hp hip hK hlen e fbar' := by
  by_cases he : symbol e = 0
  · rw [concatSymbol_eq_zero_of_left i p hp hip hK hlen e fbar he,
      concatSymbol_eq_zero_of_left i p hp hip hK hlen e fbar' he, smul_zero]
  by_cases hf : symbol fbar = 0
  · have hf' : symbol fbar' = 0 := (smul_eq_zero.mp (hsym.symm.trans hf)).resolve_left hc
    rw [concatSymbol_eq_zero_of_right i p hp hip hK hlen e fbar hf,
      concatSymbol_eq_zero_of_right i p hp hip hK hlen e fbar' hf', smul_zero]
  exact main he hf (fun hz ↦ hf (by rw [hsym, hz, smul_zero]))

/-- `concatSymbol` obeys the unit-change relation in the submodule variable. -/
private lemma concatSymbol_unitChange_left
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K) (fbar : AdmissibleSequence R M)
    (a : Fin (moduleLength R K)) (unit : Rˣ) (replacement x : K)
    (ha : e.1 a = (unit : R) • replacement + x)
    (hx : x ∈ spanBefore (R := R) e.1 a)
    (hreplacement : IsAdmissibleSequence (R := R)
      (Function.update e.1 a replacement)) :
    concatSymbol i p hp hip hK hlen e fbar =
      IsLocalRing.residue R unit • concatSymbol i p hp hip hK hlen
        ⟨Function.update e.1 a replacement, hreplacement⟩ fbar := by
  refine concatSymbol_smul_left_of_ne_zero i p hp hip hK hlen e _ fbar _
    ((Units.isUnit unit).map (IsLocalRing.residue R)).ne_zero
    (symbol_unitChange e a unit replacement x ha hx hreplacement) fun he he' hf ↦ ?_
  choose f hlift using fun b ↦ hp (fbar.1 b)
  rw [concatSymbol_eq_of_lifts i p hp hip hK hlen _ fbar he hf f hlift,
    concatSymbol_eq_of_lifts i p hp hip hK hlen _ fbar he' hf f hlift]
  exact symbol_unitChange_of_update_eq _ _ (Fin.cast hlen.symm (Fin.castAdd _ a)) unit
    (i replacement) (i x) (by simp [ha]) (append_left_spanBefore hlen i e.1 f a x hx)
    (append_update_left hlen i e.1 f a replacement)

/-- `concatSymbol` obeys the adjacent-transposition relation in the submodule variable. -/
private lemma concatSymbol_swap_left
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K) (fbar : AdmissibleSequence R M)
    (a b : Fin (moduleLength R K)) (hba : b.val + 1 = a.val)
    (ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
      r • e.1 a ∈ spanBefore (R := R) e.1 b)
    (hswap : IsAdmissibleSequence (R := R)
      (Function.update (Function.update e.1 b (e.1 a)) a (e.1 b))) :
    concatSymbol i p hp hip hK hlen e fbar =
      -concatSymbol i p hp hip hK hlen
        ⟨Function.update (Function.update e.1 b (e.1 a)) a (e.1 b), hswap⟩ fbar := by
  rw [← neg_one_smul (IsLocalRing.ResidueField R)]
  refine concatSymbol_smul_left_of_ne_zero i p hp hip hK hlen e _ fbar _ (by simp)
    (by rw [neg_one_smul]; exact symbol_swap e a b hba ha hswap) fun he he' hf ↦ ?_
  choose f hlift using fun j ↦ hp (fbar.1 j)
  rw [concatSymbol_eq_of_lifts i p hp hip hK hlen _ fbar he hf f hlift,
    concatSymbol_eq_of_lifts i p hp hip hK hlen _ fbar he' hf f hlift, neg_one_smul]
  refine symbol_swap_of_update_eq _ _ (Fin.cast hlen.symm (Fin.castAdd _ a))
    (Fin.cast hlen.symm (Fin.castAdd _ b)) (by simpa using hba) (fun r hr ↦ ?_) ?_
  · simpa using append_left_spanBefore hlen i e.1 f b (r • e.1 a) (ha r hr)
  · simpa using append_swap_left hlen i e.1 f a b

/-- `concatSymbol` obeys the unit-change relation in the quotient variable. -/
private lemma concatSymbol_unitChange_right
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K) (fbar : AdmissibleSequence R M)
    (a : Fin (moduleLength R M)) (unit : Rˣ) (replacement x : M)
    (ha : fbar.1 a = (unit : R) • replacement + x)
    (hx : x ∈ spanBefore (R := R) fbar.1 a)
    (hreplacement : IsAdmissibleSequence (R := R)
      (Function.update fbar.1 a replacement)) :
    concatSymbol i p hp hip hK hlen e fbar =
      IsLocalRing.residue R unit • concatSymbol i p hp hip hK hlen e
        ⟨Function.update fbar.1 a replacement, hreplacement⟩ := by
  refine concatSymbol_smul_right_of_ne_zero i p hp hip hK hlen e fbar _ _
    ((Units.isUnit unit).map (IsLocalRing.residue R)).ne_zero
    (symbol_unitChange fbar a unit replacement x ha hx hreplacement) fun he hf hf' ↦ ?_
  choose f hlift using fun j ↦ hp (fbar.1 j)
  obtain ⟨y, hy, hpy⟩ := exists_lift_spanBefore_append hlen i p e.1 f fbar.1 hlift a x hx
  let z : L := (↑unit⁻¹ : R) • (f a - y)
  have hrel : f a = (unit : R) • z + y := by
    simp [z, smul_smul]
  have hpz : p z = replacement := by
    calc
      p z = (↑unit⁻¹ : R) • (p (f a) - p y) := by simp [z]
      _ = (↑unit⁻¹ : R) • ((unit : R) • replacement) := by
        rw [hlift a, hpy, ha, add_sub_cancel_right]
      _ = replacement := by simp [smul_smul]
  have hlift' : ∀ j, p (Function.update f a z j) =
      (Function.update fbar.1 a replacement) j := by
    intro j
    by_cases hj : j = a
    · subst j
      simpa using hpz
    · simpa [Function.update_of_ne hj] using hlift j
  rw [concatSymbol_eq_of_lifts i p hp hip hK hlen e fbar he hf f hlift,
    concatSymbol_eq_of_lifts i p hp hip hK hlen e _ he hf' _ hlift']
  exact symbol_unitChange_of_update_eq _ _ (Fin.cast hlen.symm (Fin.natAdd _ a)) unit z y
    (by simpa using hrel) hy (append_update_right hlen (fun j ↦ i (e.1 j)) f a z)

/-- `concatSymbol` obeys the adjacent-transposition relation in the quotient variable. -/
private lemma concatSymbol_swap_right
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K) (fbar : AdmissibleSequence R M)
    (a b : Fin (moduleLength R M)) (hba : b.val + 1 = a.val)
    (ha : ∀ r, r ∈ IsLocalRing.maximalIdeal R →
      r • fbar.1 a ∈ spanBefore (R := R) fbar.1 b)
    (hswap : IsAdmissibleSequence (R := R)
      (Function.update (Function.update fbar.1 b (fbar.1 a)) a (fbar.1 b))) :
    concatSymbol i p hp hip hK hlen e fbar =
      -concatSymbol i p hp hip hK hlen e
        ⟨Function.update (Function.update fbar.1 b (fbar.1 a)) a (fbar.1 b), hswap⟩ := by
  rw [← neg_one_smul (IsLocalRing.ResidueField R)]
  refine concatSymbol_smul_right_of_ne_zero i p hp hip hK hlen e fbar _ _ (by simp)
    (by rw [neg_one_smul]; exact symbol_swap fbar a b hba ha hswap) fun he hf hf' ↦ ?_
  choose f hlift using fun j ↦ hp (fbar.1 j)
  have hlift' : ∀ j, p (Function.update (Function.update f b (f a)) a (f b) j) =
      (Function.update (Function.update fbar.1 b (fbar.1 a)) a (fbar.1 b)) j := by
    intro j
    by_cases hja : j = a
    · subst j
      simp [hlift b]
    by_cases hjb : j = b
    · subst j
      simp [hja, hlift a]
    · simp [hja, hjb, hlift j]
  rw [concatSymbol_eq_of_lifts i p hp hip hK hlen e fbar he hf f hlift,
    concatSymbol_eq_of_lifts i p hp hip hK hlen e _ he hf' _ hlift', neg_one_smul]
  have hspan := span_eq_top_of_symbol_ne_zero hK e he
  refine symbol_swap_of_update_eq _ _ (Fin.cast hlen.symm (Fin.natAdd _ a))
    (Fin.cast hlen.symm (Fin.natAdd _ b)) (by simp; omega) (fun r hr ↦ ?_) ?_
  · simpa using append_right_spanBefore hlen i p hip e.1 hspan f fbar.1 hlift a b r (ha r hr)
  · simpa using append_swap_right hlen (fun j ↦ i (e.1 j)) f a b

/-- The bilinear map on the free vector spaces on symbols induced by `concatSymbol`. -/
private noncomputable def freePair
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M) :
    DeterminantFree R K →ₗ[IsLocalRing.ResidueField R]
      DeterminantFree R M →ₗ[IsLocalRing.ResidueField R] determinant R L :=
  Finsupp.linearCombination (IsLocalRing.ResidueField R) fun e ↦
    Finsupp.linearCombination (IsLocalRing.ResidueField R) fun f ↦
      concatSymbol i p hp hip hK hlen e f

/-- `freePair` on a pair of single symbols. -/
private lemma freePair_single_single
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K)
    (hlen : moduleLength R L = moduleLength R K + moduleLength R M)
    (e : AdmissibleSequence R K) (f : AdmissibleSequence R M) :
    freePair i p hp hip hK hlen (Finsupp.single e 1) (Finsupp.single f 1) =
      concatSymbol i p hp hip hK hlen e f := by
  simp [freePair]

/-- The class of a multiple of a basis vector in the determinant is the multiple of the
symbol. -/
private lemma mk_single_eq_smul_symbol
    {R : Type u} [CommRing R] [IsLocalRing R] {M : Type x} [AddCommGroup M] [Module R M]
    (e : AdmissibleSequence R M) (c : IsLocalRing.ResidueField R) :
    (Submodule.Quotient.mk (Finsupp.single e c) : determinant R M) = c • symbol e := by
  change Submodule.Quotient.mk (Finsupp.single e c) =
    c • Submodule.Quotient.mk (Finsupp.single e 1)
  rw [show Finsupp.single e c = c • Finsupp.single e (1 : IsLocalRing.ResidueField R) by simp]
  rfl

/-- A linear map out of a free vector space vanishes if it vanishes on every basis vector. -/
private lemma finsupp_linearMap_eq_zero
    {α : Type*} {k : Type*} {N : Type*} [Semiring k] [AddCommMonoid N] [Module k N]
    (F : (α →₀ k) →ₗ[k] N) (h : ∀ a, F (Finsupp.single a 1) = 0) : F = 0 :=
  Finsupp.lhom_ext fun a b ↦ by
    rw [show Finsupp.single a b = b • Finsupp.single a (1 : k) by simp, map_smul, h, smul_zero,
      LinearMap.zero_apply]

/-- Two linear maps out of the tensor product of the outer determinants that agree on tensors
of symbols are equal. -/
private lemma eq_of_symbol_tensors
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {M : Type x} {L : Type w}
    [AddCommGroup K] [Module R K] [AddCommGroup M] [Module R M]
    [AddCommGroup L] [Module R L]
    (g h : determinant R K ⊗[IsLocalRing.ResidueField R] determinant R M
      →ₗ[IsLocalRing.ResidueField R] determinant R L)
    (heq : ∀ (e : AdmissibleSequence R K) (f : AdmissibleSequence R M),
      g (symbol e ⊗ₜ[IsLocalRing.ResidueField R] symbol f) =
        h (symbol e ⊗ₜ[IsLocalRing.ResidueField R] symbol f)) : g = h := by
  classical
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [hz, hz']
  | tmul a b =>
    induction a using Submodule.Quotient.induction_on with
    | H za =>
      induction za using Finsupp.induction_linear with
      | zero => simp
      | add za za' hza hza' => simpa [TensorProduct.add_tmul] using congrArg₂ (· + ·) hza hza'
      | single e c =>
        induction b using Submodule.Quotient.induction_on with
        | H zb =>
          induction zb using Finsupp.induction_linear with
          | zero => simp
          | add zb zb' hzb hzb' =>
              simpa [TensorProduct.tmul_add] using congrArg₂ (· + ·) hzb hzb'
          | single f d =>
              rw [mk_single_eq_smul_symbol e c, mk_single_eq_smul_symbol f d,
                TensorProduct.smul_tmul_smul]
              simpa only [map_smul] using
                congrArg (fun z ↦ (c * d) • z) (heq e f)

/-- A linear map on determinants satisfies the defining rule for a short exact sequence if,
on a tensor of nonzero symbols, it concatenates the image of the first sequence with any
choice of lifts of the second sequence. -/
public def IsDeterminantExactSequenceMap
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (gamma :
      determinant R K ⊗[IsLocalRing.ResidueField R] determinant R M
        →ₗ[IsLocalRing.ResidueField R] determinant R L) : Prop :=
  ∀ (e : AdmissibleSequence R K) (fbar : AdmissibleSequence R M),
    symbol e ≠ 0 → symbol fbar ≠ 0 →
      ∀ (f : Fin (moduleLength R M) → L),
        (∀ a, p (f a) = fbar.1 a) →
          ∃ hlength : moduleLength R L = moduleLength R K + moduleLength R M,
            ∃ hadmissible : IsAdmissibleSequence (R := R)
              (fun a ↦ Fin.append (fun b ↦ i (e.1 b)) f (Fin.cast hlength a)),
              gamma (symbol e ⊗ₜ[IsLocalRing.ResidueField R] symbol fbar) =
                symbol ⟨fun a ↦
                  Fin.append (fun b ↦ i (e.1 b)) f (Fin.cast hlength a), hadmissible⟩

/-- A map obeying the defining rule of the determinant map of a short exact sequence is
unique. -/
private lemma determinantExactSequenceMap_unique
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M) (hp : Function.Surjective p)
    (g h : determinant R K ⊗[IsLocalRing.ResidueField R] determinant R M
      →ₗ[IsLocalRing.ResidueField R] determinant R L)
    (hg : IsDeterminantExactSequenceMap i p g)
    (hh : IsDeterminantExactSequenceMap i p h) : g = h := by
  classical
  apply eq_of_symbol_tensors g h
  intro e f
  by_cases he : symbol e = 0
  · simp [he]
  by_cases hf : symbol f = 0
  · simp [hf]
  let lifts : Fin (moduleLength R M) → L :=
    fun a ↦ Classical.choose (hp (f.1 a))
  have hlifts : ∀ a, p (lifts a) = f.1 a :=
    fun a ↦ Classical.choose_spec (hp (f.1 a))
  obtain ⟨_, _, hgeq⟩ := hg e f he hf lifts hlifts
  obtain ⟨_, _, hheq⟩ := hh e f he hf lifts hlifts
  exact hgeq.trans hheq.symm

/-- There is a unique linear map satisfying the concatenation rule for a short exact
sequence of finite-length modules. -/
public theorem existsUnique_determinantExactSequenceMap
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K) (_hL : IsFiniteLength R L) (hM : IsFiniteLength R M) :
    ∃! gamma :
      determinant R K ⊗[IsLocalRing.ResidueField R] determinant R M →ₗ[IsLocalRing.ResidueField R]
        determinant R L,
      IsDeterminantExactSequenceMap i p gamma := by
  classical
  let hlen := exactSequence_moduleLength i p hi hp hip hK hM
  let F := freePair i p hp hip hK hlen
  have hleft : determinantRelations R K ≤ F.ker := by
    rw [determinantRelations]
    apply Submodule.span_le.mpr
    intro z hz
    change DeterminantRelation z at hz
    apply LinearMap.mem_ker.mpr
    apply finsupp_linearMap_eq_zero
    intro f
    cases hz with
    | dependent e a ha =>
      have he : symbol e = 0 := symbol_eq_zero_of_mem_spanBefore e a ha
      simp [F, freePair_single_single, concatSymbol_eq_zero_of_left i p hp hip hK hlen e f he]
    | unitChange e a unit replacement x ha hx hreplacement =>
      simp only [map_sub, LinearMap.sub_apply]
      rw [freePair_single_single]
      rw [map_smul, LinearMap.smul_apply, freePair_single_single]
      exact sub_eq_zero.mpr (concatSymbol_unitChange_left i p hp hip hK hlen e f a
        unit replacement x ha hx hreplacement)
    | swap e a b hba ha hswap =>
      simpa [F, freePair_single_single, map_add] using
        add_eq_zero_iff_eq_neg.mpr
          (concatSymbol_swap_left i p hp hip hK hlen e f a b hba ha hswap)
  have hright : determinantRelations R M ≤ F.flip.ker := by
    rw [determinantRelations]
    apply Submodule.span_le.mpr
    intro z hz
    change DeterminantRelation z at hz
    apply LinearMap.mem_ker.mpr
    apply finsupp_linearMap_eq_zero
    intro e
    cases hz with
    | dependent f a ha =>
      have hf : symbol f = 0 := symbol_eq_zero_of_mem_spanBefore f a ha
      simp [F, LinearMap.flip_apply, freePair_single_single,
        concatSymbol_eq_zero_of_right i p hp hip hK hlen e f hf]
    | unitChange f a unit replacement x ha hx hreplacement =>
      simp only [LinearMap.flip_apply, map_sub, LinearMap.sub_apply]
      rw [freePair_single_single]
      rw [map_smul, freePair_single_single]
      exact sub_eq_zero.mpr (concatSymbol_unitChange_right i p hp hip hK hlen e f a
        unit replacement x ha hx hreplacement)
    | swap f a b hba ha hswap =>
      simpa [F, LinearMap.flip_apply, freePair_single_single, map_add] using
        add_eq_zero_iff_eq_neg.mpr
          (concatSymbol_swap_right i p hp hip hK hlen e f a b hba ha hswap)
  let G := F.liftQ₂ (determinantRelations R K) (determinantRelations R M) hleft hright
  let gamma : determinant R K ⊗[IsLocalRing.ResidueField R] determinant R M
      →ₗ[IsLocalRing.ResidueField R] determinant R L := TensorProduct.lift G
  have hgamma : IsDeterminantExactSequenceMap i p gamma := by
    intro e f he hf lifts hlifts
    refine ⟨hlen, ?_, ?_⟩
    · exact admissible_append_exact hlen i p hip e.1 e.2
        (span_eq_top_of_symbol_ne_zero hK e he) lifts f.1 hlifts f.2
    · simp only [gamma, TensorProduct.lift.tmul, G, symbol, LinearMap.liftQ₂_mk]
      rw [freePair_single_single]
      exact concatSymbol_eq_of_lifts i p hp hip hK hlen e f he hf lifts hlifts
  exact ⟨gamma, hgamma, fun g hg ↦ determinantExactSequenceMap_unique i p hp g gamma hg hgamma⟩

/-- **Stacks Project, Tag 02PA (determinant exact-sequence map).** The canonical linear map
from the tensor product of the determinants of the outer terms of a short exact sequence to
the determinant of its middle term. -/
@[stacks 02PA "detexactsequencemap", implicit_reducible]
public noncomputable def determinantExactSequenceMap
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K) (hL : IsFiniteLength R L) (hM : IsFiniteLength R M) :
    determinant R K ⊗[IsLocalRing.ResidueField R] determinant R M →ₗ[IsLocalRing.ResidueField R]
      determinant R L :=
  Classical.choose
    (existsUnique_determinantExactSequenceMap i p hi hp hip hK hL hM)

/-- The determinant map of a short exact sequence has the prescribed value on nonzero
symbols, independently of the chosen lifts. -/
public theorem determinantExactSequenceMap_spec
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K) (hL : IsFiniteLength R L) (hM : IsFiniteLength R M) :
    IsDeterminantExactSequenceMap i p
      (determinantExactSequenceMap i p hi hp hip hK hL hM) :=
  (Classical.choose_spec
    (existsUnique_determinantExactSequenceMap i p hi hp hip hK hL hM)).1

/-- The defining rule uniquely characterizes the determinant map of a short exact
sequence. -/
public theorem eq_determinantExactSequenceMap
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {M : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup M] [Module R M]
    (i : K →ₗ[R] L) (p : L →ₗ[R] M)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hip : Function.Exact i p)
    (hK : IsFiniteLength R K) (hL : IsFiniteLength R L) (hM : IsFiniteLength R M)
    {gamma :
      determinant R K ⊗[IsLocalRing.ResidueField R] determinant R M →ₗ[IsLocalRing.ResidueField R]
        determinant R L}
    (hgamma : IsDeterminantExactSequenceMap i p gamma) :
    gamma = determinantExactSequenceMap i p hi hp hip hK hL hM :=
  (Classical.choose_spec
    (existsUnique_determinantExactSequenceMap i p hi hp hip hK hL hM)).2 gamma hgamma

end Module.FiniteLength
end
