module

public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.Data.Matrix.Basis
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AbsolutelyIrreducible

/-!
# A submodule of `Oⁿ` spanning `Eⁿ` contains `d • Oⁿ`

Let `O` be a domain with fraction field `E`. A submodule `N ⊆ ι → O`, `ι` finite, whose image spans
`ι → E` over `E` contains `d • (ι → O)` for some nonzero `d ∈ O`: write each standard basis vector
as an `E`-combination of elements of `N` and clear denominators.

Applied to the `O`-span of `σ(G) ⊆ M_m(O)` for an absolutely irreducible representation `σ`, whose
`E`-span is `M_m(E)` by Burnside's theorem, this gives the uniform bound behind the irreducibility
dichotomy at finite level in the proof that the Fourier transform of an irreducible sheaf is
irreducible: a `σ`-stable submodule of `(O/ℓⁿ)ᵐ` containing a vector `v` contains
`d · vⱼ · (O/ℓⁿ)ᵐ` for every coordinate `vⱼ` of `v`
(`Stacks.EtaleCohomology.smul_mem_of_forall_matrix_mem`).

## Main results

* `Stacks.EtaleCohomology.span_range_eq_top_of_forall_mulVec_map_mem`: a family of matrices over
  `E`, closed under products and containing `1`, which stabilizes no proper nonzero subspace over
  an algebraically closed `K ⊇ E` spans `M_ι(E)` over `E` (Burnside over `K` and a dimension
  count).
* `Stacks.EtaleCohomology.eq_bot_or_eq_top_of_span_range_eq_top`: the converse, over any
  extension `K`.
* `Stacks.EtaleCohomology.exists_ne_zero_smul_mem_of_span_eq_top`.
* `Stacks.EtaleCohomology.smul_mem_of_forall_matrix_mem`.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.EtaleCohomology

section Lattice

variable {O : Type*} (E : Type*) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
  [IsFractionRing O E] {ι : Type*}

/-- A scalar multiple `c • w` lies in a submodule of `J → B` once `c` times each standard basis
vector does. -/
private theorem smul_mem_of_forall_smul_single_mem {J B : Type*} [Finite J] [DecidableEq J]
    [CommRing B] (S : Submodule B (J → B)) (c : B) (h : ∀ i, c • (Pi.single i 1 : J → B) ∈ S)
    (w : J → B) :
    c • w ∈ S := by
  have := Fintype.ofFinite J
  rw [← Finset.univ_sum_single w, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : c • (Pi.single i (w i) : J → B) = w i • c • (Pi.single i 1 : J → B) := by
    ext k
    by_cases h : k = i <;> simp [h, mul_comm]
  rw [this]
  exact S.smul_mem _ (h i)

/-- If the matrices of a set `S₀` over `A` map a submodule `S ⊆ B^J` into itself, so do all
matrices in the `A`-span of `S₀`. -/
private theorem mulVec_map_mem_of_mem_span {J A B : Type*} [Fintype J] [CommRing A] [CommRing B]
    [Algebra A B]
    (S₀ : Set (Matrix J J A)) (S : Submodule B (J → B))
    (hS : ∀ M ∈ S₀, ∀ v ∈ S, M.map (algebraMap A B) *ᵥ v ∈ S) {X : Matrix J J A}
    (hX : X ∈ Submodule.span A S₀) : ∀ v ∈ S, X.map (algebraMap A B) *ᵥ v ∈ S := by
  induction hX using Submodule.span_induction with
  | mem M hM => exact hS M hM
  | zero => exact fun v _ => by simp
  | add X Y _ _ hX hY =>
    exact fun v hv => by
      rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec]
      exact S.add_mem (hX v hv) (hY v hv)
  | smul c X _ hX =>
    exact fun v hv => by
      have : (c • X).map (algebraMap A B) = algebraMap A B c • X.map (algebraMap A B) := by
        ext a b
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      rw [this, Matrix.smul_mulVec]
      exact S.smul_mem _ (hX v hv)

/-- A submodule of `ι → O` whose image spans `ι → E` contains a nonzero multiple of each standard
basis vector. -/
private theorem exists_ne_zero_smul_single_mem_of_span_eq_top [DecidableEq ι]
    (N : Submodule O (ι → O))
    (hN : Submodule.span E ((fun v : ι → O => algebraMap O E ∘ v) '' N) = ⊤) (i : ι) :
    ∃ d : O, d ≠ 0 ∧ d • (Pi.single i 1 : ι → O) ∈ N := by
  classical
  let φ : (ι → O) →ₗ[O] (ι → E) := LinearMap.pi fun i =>
    (Algebra.linearMap O E).comp (LinearMap.proj i)
  have hφ : Function.Injective φ := fun v w h => funext fun i =>
    IsFractionRing.injective O E (congrFun h i)
  have hmem : (Pi.single i 1 : ι → E) ∈ Submodule.span E
      ((fun v : ι → O => algebraMap O E ∘ v) '' N) := hN ▸ Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hmem
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    c.support (fun v => c v)
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  choose a ha using hint
  have : φ (b • (Pi.single i 1 : ι → O)) =
      φ (∑ v ∈ c.support.attach, a v.1 v.2 • v.1) := by
    rw [map_smul, map_sum]
    have h1 : φ (Pi.single i 1) = (Pi.single i 1 : ι → E) := by
      ext k
      by_cases h : k = i <;> simp [φ, h]
    rw [h1, ← hsum, Finsupp.linearCombination_apply, Finsupp.sum, Finset.smul_sum,
      ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hav := ha v.1 v.2
    simp only [Algebra.smul_def] at hav
    ext k
    have hφv : φ v.1 k = algebraMap O E (v.1 k) := rfl
    rw [Pi.smul_apply, Pi.smul_apply, LinearMap.map_smul, Pi.smul_apply, hφv, Function.comp_apply,
      smul_eq_mul, Algebra.smul_def, Algebra.smul_def, hav]
    ring
  rw [hφ this]
  exact Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ (hc v.2)

/-- **A submodule of `ι → O` whose image spans `ι → E` contains `d • (ι → O)`** for a nonzero
`d ∈ O`. -/
theorem exists_ne_zero_smul_mem_of_span_eq_top [Finite ι] (N : Submodule O (ι → O))
    (hN : Submodule.span E ((fun v : ι → O => algebraMap O E ∘ v) '' N) = ⊤) :
    ∃ d : O, d ≠ 0 ∧ ∀ v : ι → O, d • v ∈ N := by
  classical
  have := Fintype.ofFinite ι
  -- each standard basis vector, up to a nonzero scalar, lies in `N`
  choose d hd hdN using exists_ne_zero_smul_single_mem_of_span_eq_top E N hN
  refine ⟨∏ i, d i, Finset.prod_ne_zero_iff.2 fun i _ => hd i, fun v => ?_⟩
  refine smul_mem_of_forall_smul_single_mem N _ (fun i => ?_) v
  have : (∏ j, d j) • (Pi.single i 1 : ι → O) =
      (∏ j ∈ Finset.univ.erase i, d j) • (d i • (Pi.single i 1 : ι → O)) := by
    rw [smul_smul, mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [this]
  exact N.smul_mem _ (hdN i)

end Lattice

section Absolute

variable {E K ι A : Type*} [Field E] [Field K] [IsAlgClosed K] [Algebra E K] [Fintype ι]
  [DecidableEq ι]

/-- **Burnside for a family of matrices**: if `M : A → M_ι(E)` is closed under products, contains
`1`, and its image over an algebraically closed field `K ⊇ E` stabilizes no subspace of `K^ι`
other than `0` and `K^ι`, then the images of the `M a` span `End_K(K^ι)` over `K`. -/
private theorem span_range_toLin'_map_eq_top [Nonempty ι] (M : A → Matrix ι ι E)
    (hmul : ∀ a b, ∃ c, M a * M b = M c) (hone : ∃ a, M a = 1)
    (hirr : ∀ W : Submodule K (ι → K), (∀ a, ∀ v ∈ W, (M a).map (algebraMap E K) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    Submodule.span K (Set.range fun a => Matrix.toLin' ((M a).map (algebraMap E K))) = ⊤ := by
  classical
  let f : A → Module.End K (ι → K) := fun a => Matrix.toLin' ((M a).map (algebraMap E K))
  -- the image of the family is a submonoid
  let s : Submonoid (Module.End K (ι → K)) :=
    { carrier := Set.range f
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        obtain ⟨c, hc⟩ := hmul a b
        refine ⟨c, ?_⟩
        simp only [f, ← hc, Matrix.map_mul, Matrix.toLin'_mul, Module.End.mul_eq_comp]
      one_mem' := by
        obtain ⟨a, ha⟩ := hone
        refine ⟨a, ?_⟩
        simp only [f, ha, Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
        rfl }
  -- Burnside over `K`
  have hS : Algebra.adjoin K (Set.range f) = ⊤ :=
    subalgebra_eq_top_of_forall_stable _ fun W hW => hirr W fun a v hv => by
      have := hW _ (Algebra.subset_adjoin ⟨a, rfl⟩) v hv
      rwa [Matrix.toLin'_apply] at this
  have h1 := congrArg Subalgebra.toSubmodule hS
  rw [Algebra.adjoin_eq_span, Algebra.top_toSubmodule] at h1
  refine eq_top_iff.2 (h1.symm.le.trans (Submodule.span_le.2 fun x hx => ?_))
  have : Submonoid.closure (Set.range f) ≤ s := Submonoid.closure_le.2 le_rfl
  exact Submodule.subset_span (this hx)

omit [IsAlgClosed K] in
/-- If the images over `K ⊇ E` of a family of matrices `M a` over `E` span `End_K(K^ι)` over `K`,
then `dim_K End_K(K^ι)` is at most the dimension of the `E`-span of the `M a`. -/
private theorem finrank_end_le_finrank_span_of_span_toLin'_map_eq_top (M : A → Matrix ι ι E)
    (hspanK :
      Submodule.span K (Set.range fun a => Matrix.toLin' ((M a).map (algebraMap E K))) = ⊤) :
    Module.finrank K (Module.End K (ι → K)) ≤
      Module.finrank E (Submodule.span E (Set.range M)) := by
  classical
  let f : A → Module.End K (ι → K) := fun a => Matrix.toLin' ((M a).map (algebraMap E K))
  -- the `E`-span and a basis of it
  set Aspan := Submodule.span E (Set.range M)
  let b := Module.finBasis E Aspan
  let Ψ : Matrix ι ι E →ₗ[E] Matrix ι ι K := (Algebra.linearMap E K).mapMatrix
  let Θ : Matrix ι ι K ≃ₗ[K] Module.End K (ι → K) := Matrix.toLin'
  have hcover : Set.range f ⊆ Submodule.span K (Set.range fun i => Θ (Ψ (b i))) := by
    rintro _ ⟨a, rfl⟩
    have hx : M a ∈ Aspan := Submodule.subset_span ⟨a, rfl⟩
    have : f a = ∑ i, algebraMap E K (b.repr ⟨M a, hx⟩ i) • Θ (Ψ (b i)) := by
      have h2 : M a = ∑ i, b.repr ⟨M a, hx⟩ i • (b i : Matrix ι ι E) := by
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using
          (congrArg Subtype.val (b.sum_repr ⟨M a, hx⟩)).symm
      change Θ (Ψ (M a)) = _
      conv_lhs => rw [h2]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← algebraMap_smul K, map_smul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  calc Module.finrank K (Module.End K (ι → K))
      = Module.finrank K (⊤ : Submodule K (Module.End K (ι → K))) := finrank_top _ _ |>.symm
    _ ≤ Module.finrank K (Submodule.span K (Set.range fun i => Θ (Ψ (b i)))) :=
        Submodule.finrank_mono (hspanK.symm.le.trans (Submodule.span_le.2 hcover))
    _ ≤ (Set.range fun i => Θ (Ψ (b i))).toFinset.card := finrank_span_le_card _
    _ ≤ Fintype.card (Fin (Module.finrank E Aspan)) := by
        rw [Set.toFinset_range]
        exact Finset.card_image_le
    _ = Module.finrank E Aspan := Fintype.card_fin _

/-- **An absolutely irreducible family of matrices spans all matrices.** If `M : A → M_ι(E)` is
closed under products, contains `1`, and its image over an algebraically closed field `K ⊇ E`
stabilizes no subspace of `K^ι` other than `0` and `K^ι`, then the `E`-span of the `M a` is
`M_ι(E)`: by Burnside's theorem the `K`-span of their images is `M_ι(K)`, and it is spanned by the
images of an `E`-basis of the `E`-span, so that `E`-span has dimension `|ι|²`. -/
theorem span_range_eq_top_of_forall_mulVec_map_mem (M : A → Matrix ι ι E)
    (hmul : ∀ a b, ∃ c, M a * M b = M c) (hone : ∃ a, M a = 1)
    (hirr : ∀ W : Submodule K (ι → K), (∀ a, ∀ v ∈ W, (M a).map (algebraMap E K) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    Submodule.span E (Set.range M) = ⊤ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  apply Submodule.eq_top_of_finrank_eq
  refine le_antisymm (Submodule.finrank_le _) ?_
  calc Module.finrank E (Matrix ι ι E) = Fintype.card ι * Fintype.card ι := by
        simp [Module.finrank_matrix]
    _ = Module.finrank K (Module.End K (ι → K)) := by
        rw [Module.finrank_linearMap]; simp
    _ ≤ _ := finrank_end_le_finrank_span_of_span_toLin'_map_eq_top M
        (span_range_toLin'_map_eq_top M hmul hone hirr)

omit [IsAlgClosed K] [DecidableEq ι] in
/-- **A family of matrices spanning `M_ι(E)` is irreducible over every extension**: the matrices
over `E` whose images stabilize a subspace `W ⊆ K^ι` form an `E`-subspace, which contains the
family, hence all matrix units, and a subspace stable under the matrix units is `0` or `K^ι`. -/
theorem eq_bot_or_eq_top_of_span_range_eq_top (M : A → Matrix ι ι E)
    (hspan : Submodule.span E (Set.range M) = ⊤) (W : Submodule K (ι → K))
    (hW : ∀ a, ∀ v ∈ W, (M a).map (algebraMap E K) *ᵥ v ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  have hT : ∀ X : Matrix ι ι E, ∀ v ∈ W, X.map (algebraMap E K) *ᵥ v ∈ W := fun X =>
    mulVec_map_mem_of_mem_span _ W (by rintro _ ⟨a, rfl⟩; exact hW a) (hspan ▸ Submodule.mem_top)
  have hunit : ∀ i j, ∀ v ∈ W, v j • (Pi.single i 1 : ι → K) ∈ W := fun i j v hv => by
    simpa [Matrix.single_mulVec_eq] using hT (Matrix.single i j 1) v hv
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
  refine eq_top_iff.mpr fun v _ => ?_
  simpa using smul_mem_of_forall_smul_single_mem W 1 (fun i => by
    simpa [smul_smul, inv_mul_cancel₀ hj] using W.smul_mem (w j)⁻¹ (hunit i j w hw)) v

end Absolute

section Stable

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R] {ι : Type*} [Fintype ι]

/-- **A submodule stable under matrices whose `O`-span contains `d • M_ι(O)`** contains, with a
vector `v`, all of `d · vⱼ · R^ι` for every coordinate `vⱼ`. -/
theorem smul_mem_of_forall_matrix_mem (S₀ : Set (Matrix ι ι O)) (d : O)
    (hd : ∀ M : Matrix ι ι O, d • M ∈ Submodule.span O S₀) (S : Submodule R (ι → R))
    (hS : ∀ M ∈ S₀, ∀ v ∈ S, M.map (algebraMap O R) *ᵥ v ∈ S) {v : ι → R} (hv : v ∈ S) (j : ι)
    (w : ι → R) : (algebraMap O R d * v j) • w ∈ S := by
  classical
  refine smul_mem_of_forall_smul_single_mem S _ (fun i => ?_) w
  simpa [Matrix.single_mulVec_eq] using
    mulVec_map_mem_of_mem_span S₀ S hS (hd (Matrix.single i j 1)) v hv

end Stable

end Stacks.EtaleCohomology

end
