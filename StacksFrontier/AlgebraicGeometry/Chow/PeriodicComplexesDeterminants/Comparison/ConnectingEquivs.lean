module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Automorphisms
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Formula

/-!
# The connecting isomorphisms of a morphism of periodic complexes

An exact morphism `α` of finite-length two-periodic complexes whose differentials vanish on its
kernel and cokernel has two connecting isomorphisms from the cokernel to the kernel.

This file also contains the private lemmas used in the proof of the comparison formula: the
determinant functor on symbols, injectivity of tensoring with a module of rank one, spanning and
admissibility of appended and transported generating sequences, and the factorisation of a
linear map through the image of another.

## Main definitions

* `AlgebraicGeometry.connectingEquivLeft` is the connecting isomorphism obtained by lifting
  along `φ'` and then applying `ψ`.
* `AlgebraicGeometry.connectingEquivs` gives the two connecting isomorphisms, specified by
  lifts.

## Implementation notes

The cokernel is the quotient by the range of `α`, and the kernel is its submodule kernel. The
two equations in the type of `AlgebraicGeometry.connectingEquivs` describe the compositions of
the connecting homomorphisms of the two short exact sequences, without a choice of lifts.

## References

* [Stacks Project, Tag 02PV](https://stacks.math.columbia.edu/tag/02PV)
-/

@[expose] public section

noncomputable section

open CategoryTheory

open scoped TensorProduct

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v w

/-- The determinant functor multiplies a symbol by the determinant of the automorphism. -/
private theorem determinantFunctor_map_apply_symbol
    {R : Type u} [CommRing R] [IsLocalRing R]
    (O : FiniteLengthModuleIso.{u, v} R) (f : O ⟶ O)
    (s : AdmissibleSequence R O.of.obj) :
    ((((determinantFunctor.{u, v} R).mapLinearEquiv f).det : IsLocalRing.ResidueField R)) •
        symbol s =
      symbol
        ⟨fun i ↦ f.iso.hom.hom.hom
            (s.1 (Fin.cast
              ((determinantFunctor.{u, v} R).map_length f).symm i)),
          (determinantFunctor.{u, v} R).map_admissible f s⟩ := by
  classical
  let F := determinantFunctor.{u, v} R
  have hdim : Module.finrank (IsLocalRing.ResidueField R)
      (determinant R O.of.obj) = 1 :=
    finrank_determinant_eq_one O.of.property
  have hmap : F.mapLinearEquiv f (symbol s) =
      symbol
        ⟨fun i ↦ f.iso.hom.hom.hom (s.1 (Fin.cast (F.map_length f).symm i)),
          F.map_admissible f s⟩ := F.map_symbol f s
  have hscale := linearEquiv_eq_det_smul_id hdim (F.mapLinearEquiv f)
  change (F.mapLinearEquiv f).toLinearMap (symbol s) = _ at hmap
  rw [hscale] at hmap
  simpa only [LinearMap.smul_apply, LinearMap.id_apply] using hmap

/-- A one-dimensional vector space has a coordinate isomorphism taking a prescribed nonzero
vector to one. -/
private theorem exists_coordinate_equiv_of_finrank_one
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : Module.finrank K V = 1)
    (v : V) (hv : v ≠ 0) : ∃ e : V ≃ₗ[K] K, e v = 1 := by
  let f := LinearMap.toSpanSingleton K V v
  have hspan : (K ∙ v : Submodule K V) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton hv, hV]
  have hsurj : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    rw [LinearMap.range_toSpanSingleton, hspan]
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hV])).2 hsurj
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨e.symm, ?_⟩
  have hv' : f 1 = v := by simp [f]
  rw [← hv']
  exact e.symm_apply_apply 1

/-- Tensoring on the right with a nonzero vector of a one-dimensional space is injective. -/
private theorem tensor_right_injective_of_finrank_one
    {K : Type u} {V : Type v} {W : Type w} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] (hV : Module.finrank K V = 1)
    (v : V) (hv : v ≠ 0) :
    Function.Injective (fun x : W => x ⊗ₜ[K] v) := by
  obtain ⟨e, he⟩ := exists_coordinate_equiv_of_finrank_one hV v hv
  let b : W →ₗ[K] V →ₗ[K] W := {
    toFun := fun x => {
      toFun := fun y => e y • x
      map_add' := by intro y z; simp [add_smul]
      map_smul' := by intro c y; simp [map_smul, smul_smul] }
    map_add' := by intro x y; ext z; simp [smul_add]
    map_smul' := by
      intro c x
      ext z
      change e z • (c • x) = c • (e z • x)
      rw [smul_smul, smul_smul, mul_comm] }
  intro x y hxy
  have h := congrArg (TensorProduct.lift b) hxy
  have hx : (TensorProduct.lift b) (x ⊗ₜ[K] v) = x := by simp [b, he]
  have hy : (TensorProduct.lift b) (y ⊗ₜ[K] v) = y := by simp [b, he]
  rw [hx, hy] at h
  exact h

/-- Tensoring on the left with a nonzero vector of a one-dimensional space is injective. -/
private theorem tensor_left_injective_of_finrank_one
    {K : Type u} {V : Type v} {W : Type w} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] (hV : Module.finrank K V = 1)
    (v : V) (hv : v ≠ 0) :
    Function.Injective (fun x : W => v ⊗ₜ[K] x) := by
  intro x y hxy
  have hcomm := congrArg (TensorProduct.comm K V W) hxy
  simpa only [TensorProduct.comm_tmul] using
    (tensor_right_injective_of_finrank_one hV v hv hcomm)

/-- A spanning family of the kernel, concatenated with lifts of a spanning family of the
quotient, spans the middle term of a short exact sequence. -/
private lemma append_spans_of_exact
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {Q : Type*}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup Q] [Module R Q]
    {n m : ℕ} (i : K →ₗ[R] L) (p : L →ₗ[R] Q)
    (_hi : Function.Injective i) (_hp : Function.Surjective p)
    (hex : Function.Exact i p) (e : Fin n → K) (f : Fin m → Q)
    (lift : Fin m → L) (hlift : ∀ j, p (lift j) = f j)
    (he : Submodule.span R (Set.range e) = ⊤)
    (hf : Submodule.span R (Set.range f) = ⊤) :
    Submodule.span R (Set.range (Fin.append (fun j ↦ i (e j)) lift)) = ⊤ := by
  let W : Submodule R L :=
    Submodule.span R (Set.range (Fin.append (fun j ↦ i (e j)) lift))
  have hfirst (j : Fin n) : i (e j) ∈ W :=
    Submodule.subset_span ⟨Fin.castAdd m j, by simp⟩
  have hliftW (j : Fin m) : lift j ∈ W :=
    Submodule.subset_span ⟨Fin.natAdd n j, by simp⟩
  have hmap : W.map p = ⊤ := by
    refine top_unique (hf ▸ Submodule.span_le.mpr ?_)
    rintro y ⟨j, rfl⟩
    exact Submodule.mem_map.mpr ⟨lift j, hliftW j, hlift j⟩
  apply top_unique
  intro x _
  have hpx : p x ∈ W.map p := by rw [hmap]; exact Submodule.mem_top
  obtain ⟨y, hyW, hpy⟩ := Submodule.mem_map.mp hpx
  have hker : x - y ∈ LinearMap.ker p := by
    rw [LinearMap.mem_ker, map_sub, hpy]
    simp
  have hrange : x - y ∈ LinearMap.range i := by
    rw [← hex.linearMap_ker_eq]
    exact hker
  obtain ⟨z, hzi⟩ := LinearMap.mem_range.mp hrange
  have hmapfirst : (Submodule.span R (Set.range e)).map i ≤ W := by
    rw [Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact hfirst j
  have hz : z ∈ Submodule.span R (Set.range e) := by rw [he]; exact Submodule.mem_top
  have hiz : i z ∈ W := hmapfirst ⟨z, hz, rfl⟩
  have hx : x = y + i z := by
    calc
      x = y + (x - y) := by abel
      _ = y + i z := by rw [← hzi]
  rw [hx]
  exact W.add_mem hyW hiz

/-- The image of a spanning family under an isomorphism spans. -/
private lemma span_top_map_linearEquiv
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    {n : ℕ} (e : Fin n → M) (he : Submodule.span R (Set.range e) = ⊤)
    (f : M ≃ₗ[R] N) :
    Submodule.span R (Set.range (f ∘ e)) = ⊤ := by
  calc
    Submodule.span R (Set.range (f ∘ e)) =
        (Submodule.span R (Set.range e)).map f.toLinearMap := by
      rw [Submodule.map_span]
      congr 1
      ext x
      simp
    _ = ⊤ := by
      rw [he, Submodule.map_top, LinearMap.range_eq_top.mpr f.surjective]

/-- Reindexing a spanning family along an equality of lengths still spans. -/
private lemma span_top_sequence_cast
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {n m : ℕ} (h : m = n) (e : Fin n → M)
    (he : Submodule.span R (Set.range e) = ⊤) :
    Submodule.span R (Set.range (fun i : Fin m => e (Fin.cast h i))) = ⊤ := by
  have hset : Set.range (fun i : Fin m => e (Fin.cast h i)) = Set.range e := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast h i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast h.symm i, by simp⟩
  rw [hset]
  exact he

/-- Reindexing a concatenated spanning family along an equality of lengths still spans. -/
private lemma span_top_append_cast
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {n m ℓ : ℕ} (h : ℓ = n + m)
    (pre : Fin n → M) (tail : Fin m → M)
    (he : Submodule.span R (Set.range (Fin.append pre tail)) = ⊤) :
    Submodule.span R
      (Set.range (fun j : Fin ℓ => Fin.append pre tail (Fin.cast h j))) = ⊤ := by
  exact span_top_sequence_cast h _ he

/-- The concatenation of a spanning admissible sequence of the kernel with lifts of one of the
quotient is an admissible spanning sequence of the middle term. -/
private theorem extend_generating_sequence
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K : Type v} {L : Type w} {Q : Type*}
    [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
    [AddCommGroup Q] [Module R Q]
    (i : K →ₗ[R] L) (p : L →ₗ[R] Q)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p)
    (hK : IsFiniteLength R K) (hL : IsFiniteLength R L) (hQ : IsFiniteLength R Q)
    (e : AdmissibleSequence R K)
    (he : Submodule.span R (Set.range e.1) = ⊤)
    (f : AdmissibleSequence R Q)
    (hf : Submodule.span R (Set.range f.1) = ⊤)
    (lift : Fin (moduleLength R Q) → L)
    (hlift : ∀ j, p (lift j) = f.1 j) :
    ∃ hlen : moduleLength R L = moduleLength R K + moduleLength R Q,
      ∃ _hadm : IsAdmissibleSequence (R := R)
        (fun a ↦ Fin.append (fun b ↦ i (e.1 b)) lift (Fin.cast hlen a)),
        Submodule.span R (Set.range
          (fun a ↦ Fin.append (fun b ↦ i (e.1 b)) lift (Fin.cast hlen a))) = ⊤ := by
  have he0 := symbol_ne_zero_of_span_top hK e he
  have hf0 := symbol_ne_zero_of_span_top hQ f hf
  have hspec := determinantExactSequenceMap_spec i p hi hp hex hK hL hQ
  obtain ⟨hlen, hadm, _⟩ := hspec e f he0 hf0 lift hlift
  refine ⟨hlen, hadm, ?_⟩
  have hspan := append_spans_of_exact i p hi hp hex e.1 f.1 lift hlift he hf
  exact span_top_sequence_cast hlen _ hspan

/-- The image of an admissible sequence under a linear map is admissible. -/
private lemma map_admissible_sequence
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    {n : ℕ} (f : M →ₗ[R] N) (e : Fin n → M)
    (he : IsAdmissibleSequence (R := R) e) :
    IsAdmissibleSequence (R := R) (f ∘ e) := by
  intro i r hr
  have hmem := he i r hr
  have hmap : (Submodule.span R (e '' Set.Iio i)).map f ≤
      Submodule.span R ((f ∘ e) '' Set.Iio i) := by
    rw [Submodule.map_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨j, hj, rfl⟩
  change r • f (e i) ∈ Submodule.span R ((f ∘ e) '' Set.Iio i)
  rw [← map_smul]
  exact hmap ⟨r • e i, hmem, rfl⟩

/-- If the prefix of an admissible concatenation dies under `p`, the image of its tail is
admissible. -/
private lemma admissible_tail_of_zero_prefix
    {R : Type u} [CommRing R] [IsLocalRing R]
    {L : Type v} {Q : Type w} [AddCommGroup L] [Module R L]
    [AddCommGroup Q] [Module R Q]
    {n m : ℕ} (p : L →ₗ[R] Q) (pre : Fin n → L) (tail : Fin m → L)
    (hzero : ∀ i, p (pre i) = 0)
    (h : IsAdmissibleSequence (R := R) (Fin.append pre tail)) :
    IsAdmissibleSequence (R := R) (p ∘ tail) := by
  have hmapped := map_admissible_sequence p (Fin.append pre tail) h
  have happend : p ∘ Fin.append pre tail = Fin.append (p ∘ pre) (p ∘ tail) := by
    funext i
    exact Fin.addCases (fun a ↦ by simp) (fun b ↦ by simp) i
  rw [happend] at hmapped
  have htail (j : Fin m) (r : R) (hr : r ∈ IsLocalRing.maximalIdeal R) :=
    hmapped (Fin.natAdd n j) r hr
  intro j r hr
  have hspan : spanBefore (R := R)
      (fun i ↦ Fin.append (p ∘ pre) (p ∘ tail) i) (Fin.natAdd n j) ≤
      spanBefore (R := R) (p ∘ tail) j := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    revert hi
    refine Fin.addCases ?_ ?_ i
    · intro a _
      simp only [Fin.append_left, Function.comp_apply]
      simp [hzero]
    · intro b hi
      simp only [Fin.append_right, Function.comp_apply]
      apply Submodule.subset_span
      refine ⟨b, ?_, rfl⟩
      have hlt : (Fin.natAdd n b) < Fin.natAdd n j := by
        simpa only [Set.mem_Iio] using hi
      have hval := Fin.lt_def.mp hlt
      have hval' : b.val < j.val := by
        have hval'' : n + b.val < n + j.val := by
          simpa only [Fin.val_natAdd] using hval
        omega
      exact Fin.lt_def.mpr hval'
  change r • (p (tail j)) ∈ _
  have hmem := htail j r hr
  simpa only [Fin.append_right, Function.comp_apply] using hspan hmem

/-- If the prefix of a spanning concatenation dies under a surjection, the image of its tail
spans. -/
private lemma append_tail_spans_of_surjective
    {R : Type u} [CommRing R]
    {L : Type v} {Q : Type w} [AddCommGroup L] [Module R L]
    [AddCommGroup Q] [Module R Q]
    {n m : ℕ} (p : L →ₗ[R] Q) (hp : Function.Surjective p)
    (pre : Fin n → L) (tail : Fin m → L)
    (hzero : ∀ i, p (pre i) = 0)
    (hspan : Submodule.span R (Set.range (Fin.append pre tail)) = ⊤) :
    Submodule.span R (Set.range (p ∘ tail)) = ⊤ := by
  apply top_unique
  intro q _
  obtain ⟨x, rfl⟩ := hp q
  have hmap : (Submodule.span R (Set.range (Fin.append pre tail))).map p ≤
      Submodule.span R (Set.range (p ∘ tail)) := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, rfl⟩ := hx
    refine Fin.addCases ?_ ?_ i
    · intro a
      rw [Fin.append_left]
      simp [hzero]
    · intro b
      rw [Fin.append_right]
      exact Submodule.subset_span ⟨b, rfl⟩
  have hx : x ∈ Submodule.span R (Set.range (Fin.append pre tail)) := by
    rw [hspan]
    exact Submodule.mem_top
  have hpx : p x ∈ (Submodule.span R (Set.range (Fin.append pre tail))).map p :=
    Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  exact hmap hpx

/-- A map killing the kernel of `f` factors through the image of `f`. -/
private noncomputable def factorThroughRange
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} {Q : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] N) (g : M →ₗ[R] Q)
    (hker : LinearMap.ker f ≤ LinearMap.ker g) : LinearMap.range f →ₗ[R] Q :=
  let q := LinearMap.quotKerEquivRange f
  (LinearMap.ker f).liftQ g hker |>.comp q.symm.toLinearMap

/-- The factorisation through the image recovers the original map. -/
private theorem factorThroughRange_apply
    {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} {Q : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q]
    (f : M →ₗ[R] N) (g : M →ₗ[R] Q)
    (hker : LinearMap.ker f ≤ LinearMap.ker g) (x : M) :
    factorThroughRange f g hker ⟨f x, LinearMap.mem_range_self f x⟩ = g x := by
  let q := LinearMap.quotKerEquivRange f
  have hq : q.symm ⟨f x, LinearMap.mem_range_self f x⟩ =
      (LinearMap.ker f).mkQ x :=
    q.injective <| (q.apply_symm_apply _).trans
      (Subtype.ext (LinearMap.quotKerEquivRange_apply_mk f x)).symm
  simp [factorThroughRange, q, hq]

/-- Exactness from an equality of a kernel and a range. -/
private theorem exact_of_ker_eq_range
    {R : Type u} [Semiring R]
    {K : Type v} {L : Type w} {Q : Type*}
    [AddCommMonoid K] [Module R K] [AddCommMonoid L] [Module R L]
    [AddCommMonoid Q] [Module R Q]
    (i : K →ₗ[R] L) (p : L →ₗ[R] Q)
    (h : LinearMap.ker p = LinearMap.range i) : Function.Exact i p := by
  rw [LinearMap.exact_iff]
  exact h

/-- One of the two connecting isomorphisms of an exact morphism of two-periodic complexes:
the one obtained by lifting along `φ'` and then applying `ψ`. -/
noncomputable def connectingEquivLeft
    {R : Type u} {M : Type v} {M' : Type w}
    [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (φ ψ : M →ₗ[R] M) (φ' ψ' : M' →ₗ[R] M') (α : M →ₗ[R] M')
    (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (hφ'ψ' : Function.Exact φ' ψ') (hψ'φ' : Function.Exact ψ' φ')
    (hαφ : α.comp φ = φ'.comp α) (hαψ : α.comp ψ = ψ'.comp α)
    (hKφ : LinearMap.ker α ≤ LinearMap.ker φ)
    (hKψ : LinearMap.ker α ≤ LinearMap.ker ψ)
    (hQφ : LinearMap.range φ' ≤ LinearMap.range α)
    (hQψ : LinearMap.range ψ' ≤ LinearMap.range α) :
    {e : (M' ⧸ LinearMap.range α) ≃ₗ[R] LinearMap.ker α //
      ∀ (x' : M') (y : M), α y = φ' x' →
        ((e (Submodule.Quotient.mk x') : LinearMap.ker α) : M) = ψ y} := by
  let qα := LinearMap.quotKerEquivRange α
  let φinto : M' →ₗ[R] LinearMap.range α :=
    LinearMap.codRestrict (LinearMap.range α) φ'
      (fun x ↦ hQφ (LinearMap.mem_range_self φ' x))
  let yclass := qα.symm.toLinearMap.comp φinto
  have hqClass (x : M') (y : M) (hxy : α y = φ' x) :
      yclass x = (LinearMap.ker α).mkQ y := by
    apply qα.injective
    change qα (qα.symm (φinto x)) = qα ((LinearMap.ker α).mkQ y)
    rw [qα.apply_symm_apply]
    have hmk : (qα ((LinearMap.ker α).mkQ y) : M') = α y := by
      change (LinearMap.quotKerEquivRange α ((LinearMap.ker α).mkQ y) : M') = α y
      exact LinearMap.quotKerEquivRange_apply_mk α y
    apply Subtype.ext
    change (φinto x : M') = (qα ((LinearMap.ker α).mkQ y) : M')
    rw [hmk]
    simpa [φinto] using hxy.symm
  let ψbar : (M ⧸ LinearMap.ker α) →ₗ[R] M :=
    (LinearMap.ker α).liftQ ψ hKψ
  have hland : ∀ x : M', α (ψbar (yclass x)) = 0 := by
    intro x
    obtain ⟨y, hy⟩ := (φinto x).property
    have hy' : α y = φ' x := by simpa [φinto] using hy
    have hquot := hqClass x y hy'
    rw [hquot]
    change α (ψ y) = 0
    have h := congrArg (fun f : M →ₗ[R] M' => f y) hαψ
    have hz : ψ'.comp φ' = 0 := by
      ext x
      change φ' x ∈ LinearMap.ker ψ'
      rw [hφ'ψ'.linearMap_ker_eq]
      exact LinearMap.mem_range_self φ' x
    have hzero : ψ' (φ' x) = 0 := by
      simpa [LinearMap.comp_apply] using congrArg (fun f : M' →ₗ[R] M' => f x) hz
    have hcomm : α (ψ y) = ψ' (α y) := by
      simpa [LinearMap.comp_apply] using h
    calc
      α (ψ y) = ψ' (α y) := hcomm
      _ = ψ' (φ' x) := by rw [hy']
      _ = 0 := hzero
  let g : M' →ₗ[R] LinearMap.ker α :=
    LinearMap.codRestrict (LinearMap.ker α) (ψbar.comp yclass)
      (fun x ↦ LinearMap.mem_ker.mpr (hland x))
  have hkill : LinearMap.range α ≤ LinearMap.ker g := by
    intro z hz
    obtain ⟨z, rfl⟩ := hz
    apply LinearMap.mem_ker.mpr
    obtain ⟨y, hy⟩ := (φinto (α z)).property
    have hαz : φ' (α z) = α (φ z) := by
      have := congrArg (fun f : M →ₗ[R] M' => f z) hαφ
      simpa [LinearMap.comp_apply] using this.symm
    have hquot := hqClass (α z) (φ z) hαz.symm
    apply Subtype.ext
    change ψbar (yclass (α z)) = 0
    rw [hquot]
    change ψ (φ z) = 0
    have hz : ψ.comp φ = 0 := by
      ext x
      change φ x ∈ LinearMap.ker ψ
      rw [hφψ.linearMap_ker_eq]
      exact LinearMap.mem_range_self φ x
    simpa [LinearMap.comp_apply] using congrArg (fun f : M →ₗ[R] M => f z) hz
  let f := (LinearMap.range α).liftQ g hkill
  have hspec (x : M') (y : M) (hxy : α y = φ' x) :
      (f (Submodule.Quotient.mk x) : M) = ψ y := by
    have hquot := hqClass x y hxy
    simp only [f, Submodule.liftQ_apply]
    change (g x : M) = ψ y
    change (ψbar (yclass x) : M) = ψ y
    rw [hquot]
    simp [ψbar, Submodule.liftQ_apply]
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro x hx
      obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective (LinearMap.range α) x
      have hx' : g x' = 0 := by
        simpa [f, Submodule.liftQ_apply] using hx
      obtain ⟨y, hy⟩ := (φinto x').property
      have hy' : α y = φ' x' := by simpa [φinto] using hy
      have hquot := hqClass x' y hy'
      have hψy : ψ y = 0 := by
        have h0 := congrArg (fun z : LinearMap.ker α => (z : M)) hx'
        change (ψbar (yclass x') : M) = 0 at h0
        rw [hquot] at h0
        exact h0
      have hyφ : y ∈ LinearMap.range φ := by
        rw [← hφψ.linearMap_ker_eq]
        exact LinearMap.mem_ker.mpr hψy
      rcases hyφ with ⟨z, rfl⟩
      have hφeq : φ' (x' - α z) = 0 := by
        have hαφ' := congrArg (fun f : M →ₗ[R] M' => f z) hαφ
        have hz : φ' (α z) = α (φ z) := by
          simpa [LinearMap.comp_apply] using hαφ'.symm
        have hαx : α (φ z) = φ' x' := by
          simpa [φinto] using hy
        simp [map_sub, hz, hαx]
      have hxrange : x' - α z ∈ LinearMap.range ψ' := by
        rw [← hψ'φ'.linearMap_ker_eq]
        exact LinearMap.mem_ker.mpr hφeq
      have hxrangeα : x' - α z ∈ LinearMap.range α := hQψ hxrange
      have hxmem : x' ∈ LinearMap.range α := by
        rcases hxrangeα with ⟨t, ht⟩
        refine ⟨z + t, ?_⟩
        rw [map_add, ht]
        simp
      exact (Submodule.Quotient.eq (LinearMap.range α)).2 (by simpa using hxmem)
    · exact bot_le
  have hsurj : Function.Surjective f := by
    intro k
    have hkφ : (k : M) ∈ LinearMap.ker φ := hKφ k.property
    obtain ⟨y, hy⟩ := (hψφ.linearMap_ker_eq ▸ hkφ)
    have hαyker : α y ∈ LinearMap.ker ψ' := by
      apply LinearMap.mem_ker.mpr
      have h := congrArg (fun f : M →ₗ[R] M' => f y) hαψ
      have hαy : α (ψ y) = 0 := by rw [hy]; exact k.property
      have hcomm : α (ψ y) = ψ' (α y) := by simpa [LinearMap.comp_apply] using h
      rw [← hcomm]
      exact hαy
    obtain ⟨x', hx'⟩ := hφ'ψ'.linearMap_ker_eq ▸ hαyker
    refine ⟨Submodule.Quotient.mk x', ?_⟩
    apply Subtype.ext
    calc
      (f (Submodule.Quotient.mk x') : M) = ψ y := hspec x' y hx'.symm
      _ = k := hy
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, hspec⟩

/-- **Stacks Project, Tag 02PV.** The two connecting isomorphisms associated to an exact
morphism of two-periodic complexes. The first uses `φ'` then `ψ`, and the second uses `ψ'`
then `φ`. -/
@[stacks 02PV "connecting isomorphisms"]
noncomputable def connectingEquivs
    {R : Type u} {M : Type v} {M' : Type w}
    [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (φ ψ : M →ₗ[R] M) (φ' ψ' : M' →ₗ[R] M') (α : M →ₗ[R] M')
    (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (hφ'ψ' : Function.Exact φ' ψ') (hψ'φ' : Function.Exact ψ' φ')
    (hαφ : α.comp φ = φ'.comp α) (hαψ : α.comp ψ = ψ'.comp α)
    (hKφ : LinearMap.ker α ≤ LinearMap.ker φ)
    (hKψ : LinearMap.ker α ≤ LinearMap.ker ψ)
    (hQφ : LinearMap.range φ' ≤ LinearMap.range α)
    (hQψ : LinearMap.range ψ' ≤ LinearMap.range α) :
    {e : ((M' ⧸ LinearMap.range α) ≃ₗ[R] LinearMap.ker α) ×
        ((M' ⧸ LinearMap.range α) ≃ₗ[R] LinearMap.ker α) //
      (∀ (x' : M') (y : M), α y = φ' x' →
        ((e.1 (Submodule.Quotient.mk x') : LinearMap.ker α) : M) = ψ y) ∧
      (∀ (x' : M') (y : M), α y = ψ' x' →
        ((e.2 (Submodule.Quotient.mk x') : LinearMap.ker α) : M) = φ y)} := by
  let e₀ := connectingEquivLeft φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
    hαφ hαψ hKφ hKψ hQφ hQψ
  let e₁ := connectingEquivLeft ψ φ ψ' φ' α hψφ hφψ hψ'φ' hφ'ψ'
    hαψ hαφ hKψ hKφ hQψ hQφ
  refine ⟨(e₀.1, e₁.1), ?_⟩
  constructor
  · intro x' y hxy
    exact e₀.2 x' y hxy
  · intro x' y hxy
    exact e₁.2 x' y hxy

end AlgebraicGeometry
