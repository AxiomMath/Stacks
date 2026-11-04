module

public import StacksFrontier.AlgebraicGeometry.Duality.FunnyMapDeterminantLine

/-!
# Naturality of the canonical maps of Tag 0FL8 under surjective quasi-isomorphisms

Consider two diagrams as in Stacks Tag 0FL8 over the same commutative ring `R`: short exact
sequences `0 → K' → L' → M⁰' → 0` and `0 → K → L → M⁰ → 0` with compatible two-term complexes
`M⁻¹' → M⁰'` and `M⁻¹ → M⁰` of finite free modules, of ranks `n'` and `n`. A morphism between
them consists of an isomorphism `κ : K' ≅ K`, a map `λ : L' → L` and a morphism `μ` of two-term
complexes, compatible with all the maps. When `μ` is a degreewise-surjective quasi-isomorphism,
the induced map `H⁰(λ)` is bijective, the determinant lines are identified by the isomorphism of
Stacks Tag 0FJJ, and the canonical maps `cᵖ` of Tag 0FL8 are compatible:
`(⋀ᵖκ ⊗ Θ) ∘ c'ᵖ = cᵖ ∘ ⋀ᵖH⁰(λ)`, with no sign.

## Main definitions

* `Stacks.DeRham.twoTermDeterminantEquivOfSurjectiveQuasiIso`: the isomorphism `Θ` of the
  determinant lines of Tag 0FL8 induced by a degreewise-surjective quasi-isomorphism: the
  isomorphism of Tag 0FJJ read through `twoTermDeterminantEquivDeterminantLine` on both sides.
* `Stacks.DeRham.insertWedge`: inserting a fixed block of vectors into a wedge, after its
  first `p` factors.

## Main results

* `Stacks.DeRham.funnyMap_naturality_of_surjectiveQuasiIso`: the naturality of the canonical
  maps.
* `Stacks.DeRham.bijective_mapQ_of_surjectiveQuasiIso`: the induced map on `H⁰` is bijective.
* `Stacks.DeRham.twoTermDeterminantEquivOfSurjectiveQuasiIso_twoTermDeterminantElement`: `Θ`
  preserves the canonical elements (Tag 0FJJ).
* `Stacks.DeRham.twoTermDeterminantEquivOfSurjectiveQuasiIso_spec`: the characterization of `Θ`
  on top wedges.
* `Stacks.DeRham.topWedgeProjection_comp_insertWedge`: the projection `π_p` of a wedge into
  which a block killed by the retraction has been inserted.

## Implementation notes

The source rank `n'` is `m + n` with `m` the constant rank of the finite projective module
`ker μ⁻¹` (over the zero ring everything vanishes). With the retraction `r' = κ⁻¹ ∘ r ∘ λ` of
`K' → L'`, the factors `d'(x)` for `x ∈ ker μ⁻¹` are killed by `r'`, so they can only enter the
`M⁰'`-factor of the projection `π_p`; this is `topWedgeProjection_comp_insertWedge`, whose proof
expands a wedge of vectors in `range i ∪ ker r` and kills the terms with more than `n` factors
in `ker r` (`topWedgeProjection_eq_zero_of_card_lt_left`). The determinant of `ker μ⁻¹` need not
be free, so instead of choosing adapted bases the two sides are compared after evaluating at the
top wedge of a basis of `M⁻¹` and wedging with `δ x` for every `x` in the determinant of the
kernel complex (`eq_of_forall_lTensor_kernelDeterminantEquiv`); this is faithful because that
determinant is an invertible module, and on `x = x₁ ∧ ⋯ ∧ xₘ` the defining property of the
isomorphism of Tag 0FJJ turns the comparison into the insertion formula above. The block
`d'(x₁), …, d'(xₘ)` is inserted between the `p` factors and the lifts `d'(t₁), …, d'(tₙ)` of
the images of a basis of `M⁻¹`, which is the order in which both determinant equivalences place
it, so no sign appears.

## References

* [Stacks Project, Tag 0FL8](https://stacks.math.columbia.edu/tag/0FL8)
* [Stacks Project, Tag 0FJJ](https://stacks.math.columbia.edu/tag/0FJJ)
-/

@[expose] public section

namespace Stacks.DeRham

open scoped TensorProduct

section Projection

variable {R : Type*} [CommRing R] {K : Type*} {L : Type*} {Mzero : Type*}
variable [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
variable [AddCommGroup Mzero] [Module R Mzero]

/-- The projection `π_p` of Tag 0FL8 kills every wedge more than `n` of whose factors lie in
the kernel of the retraction. -/
theorem topWedgeProjection_eq_zero_of_card_lt_left {p n : ℕ} (r : L →ₗ[R] K)
    (π : L →ₗ[R] Mzero) (w : Fin (p + n) → L) (S : Finset (Fin (p + n))) (hcard : n < S.card)
    (hS : ∀ j ∈ S, r (w j) = 0) :
    topWedgeProjection p n r π (exteriorPower.ιMulti R (p + n) w) = 0 := by
  classical
  rw [topWedgeProjection_apply_ιMulti, AlternatingMap.domCoprod_apply, _root_.sum_apply]
  apply Finset.sum_eq_zero
  intro τ _
  induction τ using Quotient.inductionOn' with | _ σ
  rw [AlternatingMap.domCoprod.summand_mk'']
  set v : Fin p ⊕ Fin n → L := (w ∘ finSumFinEquiv) with hv
  set A : Finset (Fin p ⊕ Fin n) := S.image finSumFinEquiv.symm with hA
  have hAcard : A.card = S.card :=
    Finset.card_image_of_injective _ finSumFinEquiv.symm.injective
  have hAmem : ∀ a ∈ A, r (v a) = 0 := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ha
    simpa [hv, Function.comp_apply] using hS j hj
  obtain ⟨j, hj⟩ : ∃ j : Fin p, σ (Sum.inl j) ∈ A := by
    by_contra hcon
    simp only [not_exists] at hcon
    have hsub : A.image σ.symm ⊆ Finset.univ.image (Sum.inr : Fin n → Fin p ⊕ Fin n) := by
      intro y hy
      obtain ⟨a, haA, rfl⟩ := Finset.mem_image.1 hy
      rcases h3 : σ.symm a with c | c
      · refine absurd ?_ (hcon c)
        have hac : σ (Sum.inl c) = a := by rw [← h3]; simp
        rw [hac]
        exact haA
      · exact Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩
    have h1 : (A.image σ.symm).card = S.card := by
      rw [Finset.card_image_of_injective _ σ.symm.injective, hAcard]
    have h2 : (Finset.univ.image (Sum.inr : Fin n → Fin p ⊕ Fin n)).card = n := by
      rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ,
        Fintype.card_fin]
    have := Finset.card_le_card hsub
    rw [h1, h2] at this
    omega
  have hzero : ((exteriorPower.ιMulti R p).compLinearMap r) (fun t => v (σ (Sum.inl t))) = 0 := by
    rw [AlternatingMap.compLinearMap_apply]
    exact AlternatingMap.map_coord_zero _ j (hAmem _ hj)
  simp only [smul_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply, AlternatingMap.coe_multilinearMap]
  rw [hzero, TensorProduct.zero_tmul, smul_zero]

/-- Naturality of the projection `π_p` of Tag 0FL8 on generators: maps of the three modules
compatible with the retractions and the projections intertwine the projections. -/
theorem map_topWedgeProjection_ιMulti {K₂ L₂ Z₂ : Type*} [AddCommGroup K₂] [Module R K₂]
    [AddCommGroup L₂] [Module R L₂] [AddCommGroup Z₂] [Module R Z₂] (p n : ℕ)
    (f : K →ₗ[R] K₂) (g : Mzero →ₗ[R] Z₂) (l : L →ₗ[R] L₂) (r : L →ₗ[R] K)
    (π : L →ₗ[R] Mzero) (r₂ : L₂ →ₗ[R] K₂) (π₂ : L₂ →ₗ[R] Z₂)
    (hr : ∀ x, f (r x) = r₂ (l x)) (hπ : ∀ x, g (π x) = π₂ (l x)) (v : Fin (p + n) → L) :
    TensorProduct.map (exteriorPower.map p f) (exteriorPower.map n g)
        (topWedgeProjection p n r π (exteriorPower.ιMulti R (p + n) v)) =
      topWedgeProjection p n r₂ π₂ (exteriorPower.ιMulti R (p + n) (l ∘ v)) := by
  rw [topWedgeProjection_apply_ιMulti, topWedgeProjection_apply_ιMulti,
    AlternatingMap.domCoprod_apply, AlternatingMap.domCoprod_apply,
    _root_.sum_apply, _root_.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  induction σ using Quotient.inductionOn' with
  | _ σ =>
      rw [AlternatingMap.domCoprod.summand_mk'', AlternatingMap.domCoprod.summand_mk'']
      simp [MultilinearMap.domCoprod_apply, exteriorPower.map_apply_ιMulti, Function.comp_def,
        hr, hπ]

/-- Wedging on the right with a fixed family `a` of `m` vectors, with the sign that makes it
insert `a` between the first `p` and the last `n` factors. -/
noncomputable def insertWedge (p m n : ℕ) (a : Fin m → L) :
    (⋀[R]^(p + n) L) →ₗ[R] ⋀[R]^(p + (m + n)) L :=
  ((-1 : R) ^ (m * n)) • ((exteriorPower.degCongr (by omega : p + n + m = p + (m + n))).toLinearMap
    ∘ₗ (exteriorPower.wedgeMul (R := R) (p + n) m).flip (exteriorPower.ιMulti R m a))

/-- Inserting a block of `m` vectors into a wedge with `n` trailing factors. -/
private theorem insertWedge_wedgeMul_aux (p m n : ℕ) (a : Fin m → L) (η : ⋀[R]^p L)
    (c : Fin n → L) :
    insertWedge (R := R) p m n a
        (exteriorPower.wedgeMul (R := R) p n η (exteriorPower.ιMulti R n c)) =
      exteriorPower.wedgeMul (R := R) p (m + n) η
        (exteriorPower.ιMulti R (m + n) (Fin.append a c)) := by
  refine Subtype.ext ?_
  simp only [insertWedge, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.flip_apply,
    LinearEquiv.coe_coe, exteriorPower.coe_neg_one_pow_smul, exteriorPower.coe_degCongr,
    exteriorPower.wedgeMul_apply_coe, exteriorPower.ιMulti_apply_coe]
  rw [← ExteriorAlgebra.ιMulti_mul_ιMulti a c,
    exteriorPower.mul_comm_of_mem (ExteriorAlgebra.ιMulti_range R m ⟨a, rfl⟩)
      (ExteriorAlgebra.ιMulti_range R n ⟨c, rfl⟩), ← mul_assoc (η : ExteriorAlgebra R L),
    ← ((Commute.neg_one_left (η : ExteriorAlgebra R L)).pow_left (m * n)).eq,
    mul_assoc, mul_assoc]

/-- Inserting the block `a` into a wedge of generators concatenates the three families. -/
theorem insertWedge_ιMulti (p m n : ℕ) (a : Fin m → L) (u : Fin p → L) (w : Fin n → L) :
    insertWedge (R := R) p m n a (exteriorPower.ιMulti R (p + n) (Fin.append u w)) =
      exteriorPower.ιMulti R (p + (m + n)) (Fin.append u (Fin.append a w)) := by
  rw [← exteriorPower.wedgeMul_ιMulti, insertWedge_wedgeMul_aux, exteriorPower.wedgeMul_ιMulti]

open scoped Classical in
/-- The number of factors of `Fin.append u (Fin.append a w)` killed by `r` exceeds that of
`Fin.append u w` by `m`, when `r` kills every factor of `a`. -/
private theorem card_filter_append_append {p m n : ℕ} (r : L →ₗ[R] K) (a : Fin m → L)
    (ha : ∀ k, r (a k) = 0) (u : Fin p → L) (w : Fin n → L) :
    (Finset.univ.filter fun j => r (Fin.append u (Fin.append a w) j) = 0).card =
      (Finset.univ.filter fun j => r (Fin.append u w j) = 0).card + m := by
  classical
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_add, Fin.sum_univ_add,
    Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, ha, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

/-- **Inserting a block of vectors killed by the retraction.** If `r` kills each `a k`, then
the projection `π_p` of `ζ` with the block `a` inserted after the first `p` factors is obtained
from that of `ζ` by wedging the `M⁰`-factor on the left with `π(a)`. -/
theorem topWedgeProjection_comp_insertWedge {p m n : ℕ} {i : K →ₗ[R] L} (r : L →ₗ[R] K)
    (π : L →ₗ[R] Mzero) (hr : r.comp i = LinearMap.id) (hπi : π.comp i = 0) (a : Fin m → L)
    (ha : ∀ k, r (a k) = 0) :
    (topWedgeProjection p (m + n) r π) ∘ₗ insertWedge p m n a =
      ((exteriorPower.wedgeMul (R := R) m n (exteriorPower.ιMulti R m (π ∘ a))).lTensor
        (⋀[R]^p K)) ∘ₗ topWedgeProjection p n r π := by
  classical
  have hri : ∀ k, r (i k) = k := fun k => LinearMap.congr_fun hr k
  have hspan : Submodule.span R (Set.range i ∪ (LinearMap.ker r : Set L)) = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun x => ?_
    have hx : x = i (r x) + (x - i (r x)) := by abel
    rw [hx]
    refine Submodule.add_mem _ (Submodule.subset_span (Or.inl ⟨r x, rfl⟩))
      (Submodule.subset_span (Or.inr ?_))
    simp [hri]
  refine LinearMap.ext_on (exteriorPower.ιMulti_span_of_span R (p + n) L hspan) ?_
  rintro - ⟨y, hy, rfl⟩
  set A : Finset (Fin (p + n)) := Finset.univ.filter (fun j => y j ∈ Set.range i)
    with hAdef
  have hAmem : ∀ j, j ∈ A ↔ y j ∈ Set.range i := by intro j; simp [hAdef]
  have hysplit : y = Fin.append (fun j => y (Fin.castAdd n j))
      (fun j => y (Fin.natAdd p j)) := (Fin.append_castAdd_natAdd).symm
  rcases lt_or_ge A.card p with hlt | hge
  · -- fewer than `p` factors in `range i`: more than `n` factors in `ker r`
    have hAc : ∀ j ∈ Aᶜ, r (y j) = 0 := by
      intro j hj
      have hjA : y j ∉ Set.range i := fun h => (Finset.mem_compl.1 hj) ((hAmem j).2 h)
      rcases hy (Set.mem_range_self j) with h | h
      · exact absurd h hjA
      · exact h
    have hcardc : n < (Aᶜ : Finset (Fin (p + n))).card := by
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    have hsub : Aᶜ ⊆ Finset.univ.filter fun j => r (y j) = 0 := fun j hj => by
      simpa using hAc j hj
    have hle := Finset.card_le_card hsub
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      topWedgeProjection_eq_zero_of_card_lt_left r π y _ hcardc hAc, map_zero, hysplit,
      insertWedge_ιMulti]
    refine topWedgeProjection_eq_zero_of_card_lt_left r π _
      (Finset.univ.filter fun j => r (Fin.append (fun j => y (Fin.castAdd n j))
        (Fin.append a (fun j => y (Fin.natAdd p j))) j) = 0) ?_ (fun j hj => by simpa using hj)
    rw [card_filter_append_append r a ha, ← hysplit]
    omega
  · -- at least `p` factors in `range i`: sort `p` of them to the front
    obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq hge
    set B : Finset (Fin (p + n)) :=
      Finset.univ.image (Fin.castAdd n : Fin p → Fin (p + n)) with hBdef
    have hBcard : B.card = p := by
      rw [hBdef, Finset.card_image_of_injective _ (Fin.castAdd_injective p n),
        Finset.card_univ, Fintype.card_fin]
    have hcardeq : Fintype.card {j : Fin (p + n) // j ∈ B} =
        Fintype.card {j : Fin (p + n) // j ∈ A'} := by
      simp only [Fintype.card_coe, hBcard, hA'card]
    set e := Fintype.equivOfCardEq hcardeq with hedef
    set σ : Equiv.Perm (Fin (p + n)) := e.extendSubtype with hσdef
    have hmemA : ∀ j : Fin p, y (σ (Fin.castAdd n j)) ∈ Set.range i := by
      intro j
      have h1 : (Fin.castAdd n j : Fin (p + n)) ∈ B :=
        Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
      have h2 : σ (Fin.castAdd n j) ∈ A' := Equiv.extendSubtype_mem e _ h1
      exact (hAmem _).1 (hA'sub h2)
    choose kk hkk using hmemA
    set l : Fin n → L := fun j => y (σ (Fin.natAdd p j)) with hldef
    have hyσ : y ∘ σ = Fin.append (i ∘ kk) l := by
      funext j
      refine Fin.addCases (fun c => ?_) (fun c => ?_) j
      · rw [Fin.append_left]
        simpa using (hkk c).symm
      · rw [Fin.append_right]
        rfl
    have hperm : exteriorPower.ιMulti R (p + n) y =
        Equiv.Perm.sign σ • exteriorPower.ιMulti R (p + n) (y ∘ σ) := by
      rw [(exteriorPower.ιMulti R (p + n)).map_perm y σ, smul_smul, Int.units_mul_self,
        one_smul]
    rw [hperm, Units.smul_def, map_zsmul, map_zsmul, hyσ, LinearMap.comp_apply,
      LinearMap.comp_apply, insertWedge_ιMulti, topWedgeProjection_apply_append r π hr hπi,
      topWedgeProjection_apply_append r π hr hπi, LinearMap.lTensor_tmul,
      exteriorPower.wedgeMul_ιMulti, comp_append]

/-- Inserting a block of `m` vectors into a wedge with `n` trailing factors. -/
theorem insertWedge_wedgeMul (p m n : ℕ) (a : Fin m → L) (η : ⋀[R]^p L) (c : Fin n → L) :
    insertWedge (R := R) p m n a
        (exteriorPower.wedgeMul (R := R) p n η (exteriorPower.ιMulti R n c)) =
      exteriorPower.wedgeMul (R := R) p (m + n) η
        (exteriorPower.ιMulti R (m + n) (Fin.append a c)) :=
  insertWedge_wedgeMul_aux p m n a η c

end Projection

section Determinant

variable {R : Type*} [CommRing R]

/-- Tensoring with an invertible module is faithful on elements: if `A ⊗ x = B ⊗ x` for every
`x` in an invertible module, then `A = B`. -/
theorem eq_of_forall_tmul_eq_of_invertible {W P : Type*} [AddCommGroup W] [Module R W]
    [AddCommGroup P] [Module R P] [Module.Invertible R P] {A B : W}
    (h : ∀ x : P, A ⊗ₜ[R] x = B ⊗ₜ[R] x) : A = B := by
  have hf : (LinearMap.toSpanSingleton R W A).rTensor P =
      (LinearMap.toSpanSingleton R W B).rTensor P := by
    refine TensorProduct.ext' fun t x => ?_
    simp only [LinearMap.rTensor_tmul, LinearMap.toSpanSingleton_apply]
    rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', h]
  have := (Module.Invertible.rTensorEquiv R W ((TensorProduct.comm R P (Module.Dual R P)).trans
    (Module.Invertible.linearEquiv R P))).injective
    (a₁ := LinearMap.toSpanSingleton R W A) (a₂ := LinearMap.toSpanSingleton R W B) hf
  simpa using LinearMap.congr_fun this 1

/-- The determinant equivalence of the short exact sequence of a surjection, read in the
exterior algebra: `x ⊗ y ↦ x ∧ y''` for any lift `y''` of `y`. -/
theorem coe_kernelDeterminantEquiv_tmul {M N : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f))
    (y : ProjectiveDeterminant.module (R := R) (M := N)) (y'' : ExteriorAlgebra R M)
    (hy : ExteriorAlgebra.map f y'' = (y : ExteriorAlgebra R N)) :
    (TwoTermComplex.kernelDeterminantEquiv f hf (x ⊗ₜ[R] y) : ExteriorAlgebra R M) =
      ExteriorAlgebra.map (LinearMap.ker f).subtype (x : ExteriorAlgebra R (LinearMap.ker f)) *
        y'' :=
  (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype f.exact_subtype_ker_map
      hf).property (TwoTermComplex.determinantAnnihilatorEquiv x)
    (TwoTermComplex.determinantAnnihilatorEquiv y) y'' hy

end Determinant

section Evaluation

variable {R : Type*} [CommRing R] {K L Mzero Mneg : Type*}
variable [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
variable [AddCommGroup Mzero] [Module R Mzero] [AddCommGroup Mneg] [Module R Mneg]

/-- Naturality of the projection `π_p` of Tag 0FL8: maps of the three modules compatible with
the retractions and the projections intertwine the projections. -/
theorem map_comp_topWedgeProjection {K₂ L₂ Z₂ : Type*} [AddCommGroup K₂] [Module R K₂]
    [AddCommGroup L₂] [Module R L₂] [AddCommGroup Z₂] [Module R Z₂] (p n : ℕ)
    (f : K →ₗ[R] K₂) (g : Mzero →ₗ[R] Z₂) (l : L →ₗ[R] L₂) (r : L →ₗ[R] K)
    (π : L →ₗ[R] Mzero) (r₂ : L₂ →ₗ[R] K₂) (π₂ : L₂ →ₗ[R] Z₂)
    (hr : ∀ x, f (r x) = r₂ (l x)) (hπ : ∀ x, g (π x) = π₂ (l x)) :
    TensorProduct.map (exteriorPower.map p f) (exteriorPower.map n g) ∘ₗ
        topWedgeProjection p n r π =
      topWedgeProjection p n r₂ π₂ ∘ₗ exteriorPower.map (p + n) l := by
  refine LinearMap.ext_on (exteriorPower.ιMulti_span (R := R) (n := p + n) (M := L)) ?_
  rintro - ⟨v, rfl⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti]
  exact map_topWedgeProjection_ιMulti p n f g l r π r₂ π₂ hr hπ v

/-- Evaluating the lift expression of Tag 0FL8 at an element `Y` of the top exterior power of
`M⁻¹` replaces the wedge of the `d(bⱼ)` by the image of `Y`, which removes the basis. -/
theorem lTensor_twoTermDeterminantEval_funnyMapLift (p n : ℕ) (r : L →ₗ[R] K)
    (π : L →ₗ[R] Mzero) (d : Mneg →ₗ[R] L) (b : Module.Basis (Fin n) R Mneg)
    (Y : ⋀[R]^n Mneg) (η : ⋀[R]^p L) :
    LinearMap.lTensor (⋀[R]^p K) (twoTermDeterminantEval n Y) (funnyMapLift p n r π d b η) =
      topWedgeProjection p n r π
        (exteriorPower.wedgeMul (R := R) p n η (exteriorPower.map n d Y)) := by
  have hY : exteriorPower.map n d Y = basisTopDual b Y • exteriorPower.ιMulti R n (d ∘ b) := by
    rw [eq_basisTopDual_smul b (exteriorPower.map n d) Y, exteriorPower.map_apply_ιMulti]
  rw [funnyMapLift_apply, hY, map_smul, map_smul]
  generalize topWedgeProjection p n r π
    (exteriorPower.wedgeMul (R := R) p n η (exteriorPower.ιMulti R n (d ∘ b))) = u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul ω z => simp [TensorProduct.tmul_smul]
  | add u v hu hv =>
      rw [TensorProduct.add_tmul, map_add, map_add, hu, hv, smul_add]

/-- Evaluating the lift expression of Tag 0FL8 at an element `Y` of the top exterior power of
`M⁻¹` whose image is the wedge of a block `a` killed by the retraction followed by a block
`c`: the projection of the wedge with `c`, with `π(a)` wedged into the `M⁰`-factor. -/
theorem lTensor_twoTermDeterminantEval_funnyMapLift_of_map_eq {p m n : ℕ} {i : K →ₗ[R] L}
    (r : L →ₗ[R] K) (π : L →ₗ[R] Mzero) (hr : r.comp i = LinearMap.id) (hπi : π.comp i = 0)
    (d : Mneg →ₗ[R] L) (b : Module.Basis (Fin (m + n)) R Mneg) (Y : ⋀[R]^(m + n) Mneg)
    (a : Fin m → L) (c : Fin n → L) (ha : ∀ j, r (a j) = 0)
    (hY : exteriorPower.map (m + n) d Y = exteriorPower.ιMulti R (m + n) (Fin.append a c))
    (η : ⋀[R]^p L) :
    LinearMap.lTensor (⋀[R]^p K) (twoTermDeterminantEval (m + n) Y)
        (funnyMapLift p (m + n) r π d b η) =
      LinearMap.lTensor (⋀[R]^p K)
        (exteriorPower.wedgeMul (R := R) m n (exteriorPower.ιMulti R m (π ∘ a)))
        (topWedgeProjection p n r π
          (exteriorPower.wedgeMul (R := R) p n η (exteriorPower.ιMulti R n c))) := by
  rw [lTensor_twoTermDeterminantEval_funnyMapLift, hY, ← insertWedge_wedgeMul,
    ← LinearMap.comp_apply (topWedgeProjection p (m + n) r π) (insertWedge p m n a),
    topWedgeProjection_comp_insertWedge r π hr hπi a ha, LinearMap.comp_apply]

/-- Evaluating the lift expression of Tag 0FL8 at the wedge of the basis, on the image of a
wedge under a map `l` compatible with the retractions and the projections, and composing with
a further map out of `⋀ⁿM⁰`. -/
theorem lTensor_comp_twoTermDeterminantEval_funnyMapLift_map {K' L' Z' W A B : Type*}
    [AddCommGroup K'] [Module R K'] [AddCommGroup L'] [Module R L'] [AddCommGroup Z']
    [Module R Z'] [AddCommGroup W] [Module R W] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (p n : ℕ) (f : K' →ₗ[R] K) (g : Z' →ₗ[R] Mzero)
    (l : L' →ₗ[R] L) (r' : L' →ₗ[R] K') (π' : L' →ₗ[R] Z') (r : L →ₗ[R] K) (π : L →ₗ[R] Mzero)
    (hr : ∀ x, f (r' x) = r (l x)) (hπ : ∀ x, g (π' x) = π (l x)) (d : Mneg →ₗ[R] L)
    (b : Module.Basis (Fin n) R Mneg) (c : Fin n → L') (hc : ∀ j, d (b j) = l (c j))
    (v : Fin p → L') (G₁ : B →ₗ[R] W) (G₂ : A →ₗ[R] B) (G₃ : (⋀[R]^n Mzero) →ₗ[R] A) :
    LinearMap.lTensor (⋀[R]^p K) (G₁ ∘ₗ G₂ ∘ₗ G₃ ∘ₗ twoTermDeterminantEval n
        (exteriorPower.ιMulti R n b)) (funnyMapLift p n r π d b
          (exteriorPower.ιMulti R p fun j => l (v j))) =
      LinearMap.lTensor (⋀[R]^p K) (G₁ ∘ₗ G₂ ∘ₗ G₃)
        (TensorProduct.map (exteriorPower.map p f) (exteriorPower.map n g)
          (topWedgeProjection p n r' π' (exteriorPower.wedgeMul (R := R) p n
            (exteriorPower.ιMulti R p v) (exteriorPower.ιMulti R n c)))) := by
  have hw : exteriorPower.wedgeMul (R := R) p n (exteriorPower.ιMulti R p fun j => l (v j))
      (exteriorPower.map n d (exteriorPower.ιMulti R n b)) =
      exteriorPower.map (p + n) l (exteriorPower.wedgeMul (R := R) p n
        (exteriorPower.ιMulti R p v) (exteriorPower.ιMulti R n c)) := by
    rw [exteriorPower.wedgeMul_map, exteriorPower.map_apply_ιMulti,
      exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
    congr 2
    funext j
    exact hc j
  rw [show G₁ ∘ₗ G₂ ∘ₗ G₃ ∘ₗ twoTermDeterminantEval n (exteriorPower.ιMulti R n b) =
      (G₁ ∘ₗ G₂ ∘ₗ G₃) ∘ₗ twoTermDeterminantEval n (exteriorPower.ιMulti R n b) from rfl,
    LinearMap.lTensor_comp, LinearMap.comp_apply, lTensor_twoTermDeterminantEval_funnyMapLift,
    hw, ← LinearMap.comp_apply (topWedgeProjection p n r π) (exteriorPower.map (p + n) l),
    ← map_comp_topWedgeProjection p n f g l r' π' r π hr hπ, LinearMap.comp_apply]

/-- Moving a map out of the second factor across a map of the first factor. -/
theorem lTensor_map_id_lTensor {P' P X X' W : Type*} [AddCommGroup P'] [Module R P']
    [AddCommGroup P] [Module R P] [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X']
    [AddCommGroup W] [Module R W] (f : P' →ₗ[R] P) (g : X →ₗ[R] X') (h : X →ₗ[R] W)
    (E : X' →ₗ[R] W) (hEg : E ∘ₗ g = h) (U : P' ⊗[R] X) :
    LinearMap.lTensor P E (TensorProduct.map f LinearMap.id (LinearMap.lTensor P' g U)) =
      TensorProduct.map f h U := by
  rw [← hEg]
  induction U using TensorProduct.induction_on with
  | zero => simp
  | tmul ω z => simp
  | add U₁ U₂ h₁ h₂ => simp only [map_add, h₁, h₂]

end Evaluation

section Faithful

variable {R : Type*} [CommRing R] {Mneg Mzero : Type*}
variable [AddCommGroup Mneg] [Module R Mneg]
variable [AddCommGroup Mzero] [Module R Mzero] [Module.Finite R Mzero] [Module.Projective R Mzero]

/-- An element of `P ⊗ det(M⁻¹ → M⁰)` is determined by its images, for all `x` in the
determinant of the kernel of a surjection `f : N' → M⁰`, under evaluation at the top wedge of a
basis of `M⁻¹` followed by `z ↦ x ∧ z̃` into `det N'`. -/
theorem eq_of_forall_lTensor_kernelDeterminantEquiv {P N' : Type*} [AddCommGroup P]
    [Module R P] [AddCommGroup N'] [Module R N'] [Module.Finite R N'] [Module.Projective R N']
    (f : N' →ₗ[R] Mzero) (hf : Function.Surjective f)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    (n : ℕ) (hzero : Nonempty (Module.Basis (Fin n) R Mzero)) (b : Module.Basis (Fin n) R Mneg)
    {U V : P ⊗[R] twoTermDeterminant R n Mneg Mzero}
    (h : ∀ x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f),
      LinearMap.lTensor P ((TwoTermComplex.kernelDeterminantEquiv f hf).toLinearMap ∘ₗ
          TensorProduct.mk R _ _ x ∘ₗ (determinantEquivExteriorPower n hzero).symm.toLinearMap ∘ₗ
          twoTermDeterminantEval n (exteriorPower.ιMulti R n b)) U =
        LinearMap.lTensor P ((TwoTermComplex.kernelDeterminantEquiv f hf).toLinearMap ∘ₗ
          TensorProduct.mk R _ _ x ∘ₗ (determinantEquivExteriorPower n hzero).symm.toLinearMap ∘ₗ
          twoTermDeterminantEval n (exteriorPower.ιMulti R n b)) V) :
    U = V := by
  set c : Module.Basis (Fin n) R Mzero := Classical.choice hzero
  set E₀ := determinantEquivExteriorPower n hzero
  set kz := TwoTermComplex.kernelDeterminantEquiv f hf
  set Q : twoTermDeterminant R n Mneg Mzero →ₗ[R] ⋀[R]^n Mzero :=
    twoTermDeterminantEval n (exteriorPower.ιMulti R n b)
  set Q' : (⋀[R]^n Mzero) →ₗ[R] twoTermDeterminant R n Mneg Mzero :=
    (TensorProduct.mk R _ _).flip (basisTopDual b)
  have hQ : Q' ∘ₗ Q = LinearMap.id := by
    refine TensorProduct.ext' fun z φ => ?_
    have hφ : φ = φ (exteriorPower.ιMulti R n b) • basisTopDual b :=
      linearMap_top_ext b (by simp)
    simp only [Q, Q', LinearMap.comp_apply, twoTermDeterminantEval_tmul, LinearMap.flip_apply,
      TensorProduct.mk_apply, LinearMap.id_apply]
    conv_rhs => rw [hφ]
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  have hQinj : Function.Injective (LinearMap.lTensor P Q) := by
    have hlQ : (LinearMap.lTensor P Q') ∘ₗ (LinearMap.lTensor P Q) = LinearMap.id := by
      rw [← LinearMap.lTensor_comp, hQ, LinearMap.lTensor_id]
    exact Function.LeftInverse.injective (g := LinearMap.lTensor P Q')
      fun u => LinearMap.congr_fun hlQ u
  apply hQinj
  set θ : Module.Dual R (⋀[R]^n Mzero) := basisTopDual c
  set ω : P ⊗[R] (⋀[R]^n Mzero) →ₗ[R] P :=
    (TensorProduct.rid R P).toLinearMap ∘ₗ LinearMap.lTensor P θ
  have hrec : ∀ W : P ⊗[R] (⋀[R]^n Mzero), W = ω W ⊗ₜ[R] exteriorPower.ιMulti R n c := by
    intro W
    induction W using TensorProduct.induction_on with
    | zero => simp
    | tmul a z =>
        have hz := eq_basisTopDual_smul c LinearMap.id z
        simp only [LinearMap.id_apply] at hz
        simp only [ω, θ, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
          TensorProduct.rid_tmul]
        rw [TensorProduct.smul_tmul, ← hz]
    | add W₁ W₂ h₁ h₂ => rw [map_add, TensorProduct.add_tmul, ← h₁, ← h₂]
  set ρ : ProjectiveDeterminant.module (R := R) (M := N') →ₗ[R]
      ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f) :=
    (TensorProduct.rid R _).toLinearMap ∘ₗ LinearMap.lTensor _ (θ ∘ₗ E₀.toLinearMap) ∘ₗ
      kz.symm.toLinearMap
  have hρ : ∀ (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f))
      (W : P ⊗[R] (⋀[R]^n Mzero)),
      LinearMap.lTensor P (ρ ∘ₗ kz.toLinearMap ∘ₗ TensorProduct.mk R _ _ x ∘ₗ
        E₀.symm.toLinearMap) W = ω W ⊗ₜ[R] x := by
    intro x W
    induction W using TensorProduct.induction_on with
    | zero => simp
    | tmul a z =>
        simp [ρ, ω, θ, TensorProduct.smul_tmul]
    | add W₁ W₂ h₁ h₂ => rw [map_add, h₁, h₂, map_add, TensorProduct.add_tmul]
  have hxs : ∀ x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f),
      ω (LinearMap.lTensor P Q U) ⊗ₜ[R] x = ω (LinearMap.lTensor P Q V) ⊗ₜ[R] x := by
    intro x
    have hx := congrArg (LinearMap.lTensor P ρ) (h x)
    simp only [LinearMap.lTensor_comp, LinearMap.comp_apply] at hx
    rw [← hρ, ← hρ]
    simpa only [LinearMap.lTensor_comp, LinearMap.comp_apply] using hx
  let _ := ProjectiveDeterminant.invertible (R := R) (M := LinearMap.ker f)
  rw [hrec (LinearMap.lTensor P Q U), hrec (LinearMap.lTensor P Q V),
    eq_of_forall_tmul_eq_of_invertible hxs]

end Faithful

section Naturality

variable {R : Type*} [CommRing R]
variable {K' L' Mneg' Mzero' K L Mneg Mzero : Type*}
variable [AddCommGroup K'] [Module R K'] [AddCommGroup L'] [Module R L']
variable [AddCommGroup Mneg'] [Module R Mneg'] [Module.Finite R Mneg'] [Module.Projective R Mneg']
variable [AddCommGroup Mzero'] [Module R Mzero'] [Module.Finite R Mzero']
  [Module.Projective R Mzero']
variable [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
variable [AddCommGroup Mneg] [Module R Mneg] [Module.Finite R Mneg] [Module.Projective R Mneg]
variable [AddCommGroup Mzero] [Module R Mzero] [Module.Finite R Mzero] [Module.Projective R Mzero]

/-- The canonical isomorphism of the determinant lines of Tag 0FL8 induced by a
degreewise-surjective quasi-isomorphism of two-term complexes of finite free modules: the
isomorphism of Tag 0FJJ, read through `twoTermDeterminantEquivDeterminantLine` on both sides. -/
noncomputable def twoTermDeterminantEquivOfSurjectiveQuasiIso (n' n : ℕ)
    (dM' : Mneg' →ₗ[R] Mzero') (dM : Mneg →ₗ[R] Mzero)
    (hzero' : Nonempty (Module.Basis (Fin n') R Mzero'))
    (hneg' : Nonempty (Module.Basis (Fin n') R Mneg'))
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg))
    (μ : TwoTermComplex.Hom dM' dM) (hs : μ.IsDegreewiseSurjective) (hq : μ.IsQuasiIso) :
    twoTermDeterminant R n' Mneg' Mzero' ≃ₗ[R] twoTermDeterminant R n Mneg Mzero :=
  let _ : Module.Finite R (LinearMap.ker μ.neg) := TwoTermComplex.kernel_finite μ.neg hs.1
  let _ : Module.Projective R (LinearMap.ker μ.neg) :=
    TwoTermComplex.kernel_projective μ.neg hs.1
  let _ : Module.Finite R (LinearMap.ker μ.zero) := TwoTermComplex.kernel_finite μ.zero hs.2
  let _ : Module.Projective R (LinearMap.ker μ.zero) :=
    TwoTermComplex.kernel_projective μ.zero hs.2
  (twoTermDeterminantEquivDeterminantLine n' dM' hzero' hneg').trans
    ((TwoTermComplex.determinantEquivOfSurjectiveQuasiIso dM' dM μ hs hq).equiv.trans
      (twoTermDeterminantEquivDeterminantLine n dM hzero hneg).symm)

/-- The isomorphism of determinant lines of Tag 0FL8 induced by a surjective
quasi-isomorphism is the isomorphism of Tag 0FJJ, read through the identifications with
`TwoTermComplex.determinantLine`. -/
theorem twoTermDeterminantEquivDeterminantLine_twoTermDeterminantEquivOfSurjectiveQuasiIso
    (n' n : ℕ) (dM' : Mneg' →ₗ[R] Mzero') (dM : Mneg →ₗ[R] Mzero)
    (hzero' : Nonempty (Module.Basis (Fin n') R Mzero'))
    (hneg' : Nonempty (Module.Basis (Fin n') R Mneg'))
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg))
    (μ : TwoTermComplex.Hom dM' dM) (hs : μ.IsDegreewiseSurjective) (hq : μ.IsQuasiIso)
    (t : twoTermDeterminant R n' Mneg' Mzero') :
    letI : Module.Finite R (LinearMap.ker μ.neg) := TwoTermComplex.kernel_finite μ.neg hs.1
    letI : Module.Projective R (LinearMap.ker μ.neg) :=
      TwoTermComplex.kernel_projective μ.neg hs.1
    letI : Module.Finite R (LinearMap.ker μ.zero) := TwoTermComplex.kernel_finite μ.zero hs.2
    letI : Module.Projective R (LinearMap.ker μ.zero) :=
      TwoTermComplex.kernel_projective μ.zero hs.2
    twoTermDeterminantEquivDeterminantLine n dM hzero hneg
        (twoTermDeterminantEquivOfSurjectiveQuasiIso n' n dM' dM hzero' hneg' hzero hneg μ hs hq
          t) =
      (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso dM' dM μ hs hq).equiv
        (twoTermDeterminantEquivDeterminantLine n' dM' hzero' hneg' t) := by
  simp [twoTermDeterminantEquivOfSurjectiveQuasiIso]

/-- **Stacks Project, Tag 0FJJ, for the determinant lines of Tag 0FL8.** The isomorphism of
determinant lines induced by a degreewise-surjective quasi-isomorphism carries the canonical
element of the source to that of the target. -/
theorem twoTermDeterminantEquivOfSurjectiveQuasiIso_twoTermDeterminantElement (n' n : ℕ)
    (dM' : Mneg' →ₗ[R] Mzero') (dM : Mneg →ₗ[R] Mzero)
    (hzero' : Nonempty (Module.Basis (Fin n') R Mzero'))
    (hneg' : Nonempty (Module.Basis (Fin n') R Mneg'))
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg))
    (μ : TwoTermComplex.Hom dM' dM) (hs : μ.IsDegreewiseSurjective) (hq : μ.IsQuasiIso) :
    twoTermDeterminantEquivOfSurjectiveQuasiIso n' n dM' dM hzero' hneg' hzero hneg μ hs hq
        (twoTermDeterminantElement R dM' hneg') = twoTermDeterminantElement R dM hneg := by
  obtain ⟨hK, hD⟩ := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_apply_delta dM' dM μ hs
    hq (isRankZero_of_basis dM hzero hneg)
  apply (twoTermDeterminantEquivDeterminantLine n dM hzero hneg).injective
  rwa [twoTermDeterminantEquivDeterminantLine_twoTermDeterminantEquivOfSurjectiveQuasiIso,
    twoTermDeterminantEquivDeterminantLine_twoTermDeterminantElement _ _ _ _ hK,
    twoTermDeterminantEquivDeterminantLine_twoTermDeterminantElement _ _ _ _
      (isRankZero_of_basis dM hzero hneg)]

/-- **The isomorphism of determinant lines of a surjective quasi-isomorphism, on the top
wedges.** Evaluating the image of `t` at `Y ∈ ⋀ⁿM⁻¹` and wedging with `δ x` for `x` in the
determinant of the kernel complex is evaluating `t` at `x ∧ Ỹ` for a lift `Ỹ` of `Y`. -/
theorem twoTermDeterminantEquivOfSurjectiveQuasiIso_spec (n' n : ℕ)
    (dM' : Mneg' →ₗ[R] Mzero') (dM : Mneg →ₗ[R] Mzero)
    (hzero' : Nonempty (Module.Basis (Fin n') R Mzero'))
    (hneg' : Nonempty (Module.Basis (Fin n') R Mneg'))
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg))
    (μ : TwoTermComplex.Hom dM' dM) (hs : μ.IsDegreewiseSurjective) (hq : μ.IsQuasiIso) :
    letI : Module.Finite R (LinearMap.ker μ.neg) := TwoTermComplex.kernel_finite μ.neg hs.1
    letI : Module.Projective R (LinearMap.ker μ.neg) :=
      TwoTermComplex.kernel_projective μ.neg hs.1
    letI : Module.Finite R (LinearMap.ker μ.zero) := TwoTermComplex.kernel_finite μ.zero hs.2
    letI : Module.Projective R (LinearMap.ker μ.zero) :=
      TwoTermComplex.kernel_projective μ.zero hs.2
    ∀ (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker μ.neg))
      (Y : ⋀[R]^n Mneg) (t : twoTermDeterminant R n' Mneg' Mzero'),
      TwoTermComplex.kernelDeterminantEquiv μ.zero hs.2
          (TwoTermComplex.delta μ.kernelDifferential
              (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso dM' dM μ hs hq).kernelRankZero
              x ⊗ₜ[R]
            (determinantEquivExteriorPower n hzero).symm (twoTermDeterminantEval n Y
              (twoTermDeterminantEquivOfSurjectiveQuasiIso n' n dM' dM hzero' hneg' hzero hneg
                μ hs hq t))) =
        (determinantEquivExteriorPower n' hzero').symm (twoTermDeterminantEval n'
          (determinantEquivExteriorPower n' hneg' (TwoTermComplex.kernelDeterminantEquiv μ.neg
            hs.1 (x ⊗ₜ[R] (determinantEquivExteriorPower n hneg).symm Y))) t) := by
  let _ : Module.Finite R (LinearMap.ker μ.neg) := TwoTermComplex.kernel_finite μ.neg hs.1
  let _ : Module.Projective R (LinearMap.ker μ.neg) :=
    TwoTermComplex.kernel_projective μ.neg hs.1
  let _ : Module.Finite R (LinearMap.ker μ.zero) := TwoTermComplex.kernel_finite μ.zero hs.2
  let _ : Module.Projective R (LinearMap.ker μ.zero) :=
    TwoTermComplex.kernel_projective μ.zero hs.2
  intro x Y t
  have h1 := twoTermDeterminantEquivDeterminantLine_apply n dM hzero hneg
    (twoTermDeterminantEquivOfSurjectiveQuasiIso n' n dM' dM hzero' hneg' hzero hneg μ hs hq t)
    ((determinantEquivExteriorPower n hneg).symm Y)
  rw [LinearEquiv.apply_symm_apply,
    twoTermDeterminantEquivDeterminantLine_twoTermDeterminantEquivOfSurjectiveQuasiIso] at h1
  rw [← h1, (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso dM' dM μ hs hq).compatibility,
    twoTermDeterminantEquivDeterminantLine_apply]

/-- Composing with the isomorphism of determinant lines of a surjective quasi-isomorphism,
evaluated at `Y` and wedged with `δ x`, is evaluating at `x ∧ Ỹ`, after tensoring with a map
`f` on the first factor. -/
theorem lTensor_comp_twoTermDeterminantEquivOfSurjectiveQuasiIso (n' n : ℕ)
    (dM' : Mneg' →ₗ[R] Mzero') (dM : Mneg →ₗ[R] Mzero)
    (hzero' : Nonempty (Module.Basis (Fin n') R Mzero'))
    (hneg' : Nonempty (Module.Basis (Fin n') R Mneg'))
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg))
    (μ : TwoTermComplex.Hom dM' dM) (hs : μ.IsDegreewiseSurjective) (hq : μ.IsQuasiIso)
    {P' P : Type*} [AddCommGroup P'] [Module R P'] [AddCommGroup P] [Module R P]
    (f : P' →ₗ[R] P) :
    letI : Module.Finite R (LinearMap.ker μ.neg) := TwoTermComplex.kernel_finite μ.neg hs.1
    letI : Module.Projective R (LinearMap.ker μ.neg) :=
      TwoTermComplex.kernel_projective μ.neg hs.1
    letI : Module.Finite R (LinearMap.ker μ.zero) := TwoTermComplex.kernel_finite μ.zero hs.2
    letI : Module.Projective R (LinearMap.ker μ.zero) :=
      TwoTermComplex.kernel_projective μ.zero hs.2
    ∀ (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker μ.neg))
      (Y : ⋀[R]^n Mneg) (U : P' ⊗[R] twoTermDeterminant R n' Mneg' Mzero'),
      LinearMap.lTensor P ((TwoTermComplex.kernelDeterminantEquiv μ.zero hs.2).toLinearMap ∘ₗ
          TensorProduct.mk R _ _ (TwoTermComplex.delta μ.kernelDifferential
            (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso dM' dM μ hs hq).kernelRankZero
              x) ∘ₗ (determinantEquivExteriorPower n hzero).symm.toLinearMap ∘ₗ
          twoTermDeterminantEval n Y)
          (TensorProduct.map f (twoTermDeterminantEquivOfSurjectiveQuasiIso n' n dM' dM hzero'
            hneg' hzero hneg μ hs hq).toLinearMap U) =
        LinearMap.lTensor P (determinantEquivExteriorPower n' hzero').symm.toLinearMap
          (TensorProduct.map f LinearMap.id (LinearMap.lTensor P' (twoTermDeterminantEval n'
            (determinantEquivExteriorPower n' hneg' (TwoTermComplex.kernelDeterminantEquiv μ.neg
              hs.1 (x ⊗ₜ[R] (determinantEquivExteriorPower n hneg).symm Y)))) U)) := by
  intro x Y U
  rw [lTensor_map_id_lTensor _ _ _ _ rfl, ← LinearMap.comp_apply (LinearMap.lTensor P _)
    (TensorProduct.map f _), LinearMap.lTensor_comp_map]
  exact congrArg (fun F => TensorProduct.map f F U) (LinearMap.ext fun t =>
    twoTermDeterminantEquivOfSurjectiveQuasiIso_spec n' n dM' dM hzero' hneg' hzero hneg μ hs hq
      x Y t)

/-- The map induced on `H⁰` by a morphism of 0FL8 diagrams which is an isomorphism on the
kernels, and a degreewise-surjective quasi-isomorphism on the two-term complexes, is
bijective. -/
theorem bijective_mapQ_of_surjectiveQuasiIso
    (i' : K' →ₗ[R] L') (π' : L' →ₗ[R] Mzero') (d' : Mneg' →ₗ[R] L') (dM' : Mneg' →ₗ[R] Mzero')
    (i : K →ₗ[R] L) (π : L →ₗ[R] Mzero) (d : Mneg →ₗ[R] L) (dM : Mneg →ₗ[R] Mzero)
    (hexact' : Function.Exact i' π') (hπ' : Function.Surjective π')
    (hsquare' : π'.comp d' = dM') (hi : Function.Injective i) (hexact : Function.Exact i π)
    (κ : K' ≃ₗ[R] K) (l : L' →ₗ[R] L) (μ : TwoTermComplex.Hom dM' dM)
    (hs : μ.IsDegreewiseSurjective) (hq : μ.IsQuasiIso)
    (hli : ∀ x, l (i' x) = i (κ x)) (hπl : ∀ x, π (l x) = μ.zero (π' x))
    (hld : ∀ x, l (d' x) = d (μ.neg x))
    (hl : LinearMap.range d' ≤ (LinearMap.range d).comap l) :
    Function.Bijective ((LinearMap.range d').mapQ (LinearMap.range d) l hl) := by
  let _ : Module.Finite R (LinearMap.ker μ.neg) := TwoTermComplex.kernel_finite μ.neg hs.1
  let _ : Module.Projective R (LinearMap.ker μ.neg) :=
    TwoTermComplex.kernel_projective μ.neg hs.1
  let _ : Module.Finite R (LinearMap.ker μ.zero) := TwoTermComplex.kernel_finite μ.zero hs.2
  let _ : Module.Projective R (LinearMap.ker μ.zero) :=
    TwoTermComplex.kernel_projective μ.zero hs.2
  have hacyc := (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso dM' dM μ hs hq).kernelAcyclic
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun q hq0 => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq0
    obtain ⟨y, hy⟩ := hq0
    obtain ⟨y', rfl⟩ := hs.1 y
    have hlx : l (x - d' y') = 0 := by rw [map_sub, hld, hy, sub_self]
    have hz : π' (x - d' y') ∈ LinearMap.ker μ.zero := by
      rw [LinearMap.mem_ker, ← hπl, hlx, map_zero]
    obtain ⟨a, ha⟩ := hacyc.2 ⟨π' (x - d' y'), hz⟩
    have ha' : dM' a = π' (x - d' y') := congrArg Subtype.val ha
    obtain ⟨k, hk⟩ := (hexact' (x - d' y' - d' a)).1 (by
      rw [map_sub, ← LinearMap.comp_apply π' d', hsquare', ha', sub_self])
    have hka : μ.neg (a : Mneg') = 0 := a.2
    have hk0 : k = 0 := by
      refine κ.injective (hi ?_)
      rw [← hli, hk, map_sub, hlx, hld, hka, map_zero, map_zero, map_zero, sub_zero]
    rw [hk0, map_zero, eq_comm, sub_eq_zero] at hk
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨y' + a, by rw [map_add, ← hk]; abel⟩
  · intro q
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨z, hz⟩ := hs.2 (π y)
    obtain ⟨x, rfl⟩ := hπ' z
    obtain ⟨k, hk⟩ := (hexact (y - l x)).1 (by rw [map_sub, hπl, hz, sub_self])
    refine ⟨Submodule.mkQ _ (x + i' (κ.symm k)), ?_⟩
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply, map_add, hli,
      LinearEquiv.apply_symm_apply, hk]
    congr 1
    abel

/-- The generator computation behind `funnyMap_naturality_of_surjectiveQuasiIso`, for a wedge
of `m` vectors of the kernel of `μ.neg`. -/
private theorem funnyMap_naturality_of_surjectiveQuasiIso_aux (m n p : ℕ)
    (i' : K' →ₗ[R] L') (π' : L' →ₗ[R] Mzero') (d' : Mneg' →ₗ[R] L') (dM' : Mneg' →ₗ[R] Mzero')
    (π : L →ₗ[R] Mzero) (d : Mneg →ₗ[R] L) (dM : Mneg →ₗ[R] Mzero)
    (hexact' : Function.Exact i' π') (hsquare' : π'.comp d' = dM')
    (hzero' : Nonempty (Module.Basis (Fin (m + n)) R Mzero'))
    (hneg' : Nonempty (Module.Basis (Fin (m + n)) R Mneg'))
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg))
    (κ : K' ≃ₗ[R] K) (l : L' →ₗ[R] L) (μ : TwoTermComplex.Hom dM' dM)
    (hs : μ.IsDegreewiseSurjective) (hq : μ.IsQuasiIso)
    (hπl : ∀ x, π (l x) = μ.zero (π' x)) (hld : ∀ x, l (d' x) = d (μ.neg x))
    (r : L →ₗ[R] K) (r' : L' →ₗ[R] K') (hr' : r'.comp i' = LinearMap.id)
    (hrr : ∀ x, κ.toLinearMap (r' x) = r (l x))
    (bN' : Module.Basis (Fin (m + n)) R Mneg') (bN : Module.Basis (Fin n) R Mneg)
    (t : Fin n → Mneg') (ht : ∀ j, μ.neg (t j) = bN j) (v' : Fin p → L') :
    letI : Module.Finite R (LinearMap.ker μ.neg) := TwoTermComplex.kernel_finite μ.neg hs.1
    letI : Module.Projective R (LinearMap.ker μ.neg) :=
      TwoTermComplex.kernel_projective μ.neg hs.1
    letI : Module.Finite R (LinearMap.ker μ.zero) := TwoTermComplex.kernel_finite μ.zero hs.2
    letI : Module.Projective R (LinearMap.ker μ.zero) :=
      TwoTermComplex.kernel_projective μ.zero hs.2
    ∀ (k : Fin m → LinearMap.ker μ.neg) (hk : ExteriorAlgebra.ιMulti R m k ∈
      ProjectiveDeterminant.submodule (R := R) (M := LinearMap.ker μ.neg)),
      LinearMap.lTensor (⋀[R]^p K)
          ((TwoTermComplex.kernelDeterminantEquiv μ.zero hs.2).toLinearMap ∘ₗ
            TensorProduct.mk R _ _ (TwoTermComplex.delta μ.kernelDifferential
              (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso dM' dM μ hs hq).kernelRankZero
                ⟨ExteriorAlgebra.ιMulti R m k, hk⟩) ∘ₗ
            (determinantEquivExteriorPower n hzero).symm.toLinearMap ∘ₗ
            twoTermDeterminantEval n (exteriorPower.ιMulti R n bN))
          (TensorProduct.map (exteriorPower.map p κ.toLinearMap)
            (twoTermDeterminantEquivOfSurjectiveQuasiIso (m + n) n dM' dM hzero' hneg' hzero hneg
              μ hs hq).toLinearMap
            (funnyMapLift p (m + n) r' π' d' bN' (exteriorPower.ιMulti R p v'))) =
        LinearMap.lTensor (⋀[R]^p K)
          ((TwoTermComplex.kernelDeterminantEquiv μ.zero hs.2).toLinearMap ∘ₗ
            TensorProduct.mk R _ _ (TwoTermComplex.delta μ.kernelDifferential
              (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso dM' dM μ hs hq).kernelRankZero
                ⟨ExteriorAlgebra.ιMulti R m k, hk⟩) ∘ₗ
            (determinantEquivExteriorPower n hzero).symm.toLinearMap ∘ₗ
            twoTermDeterminantEval n (exteriorPower.ιMulti R n bN))
          (funnyMapLift p n r π d bN (exteriorPower.ιMulti R p fun j => l (v' j))) := by
  let _ : Module.Finite R (LinearMap.ker μ.neg) := TwoTermComplex.kernel_finite μ.neg hs.1
  let _ : Module.Projective R (LinearMap.ker μ.neg) :=
    TwoTermComplex.kernel_projective μ.neg hs.1
  let _ : Module.Finite R (LinearMap.ker μ.zero) := TwoTermComplex.kernel_finite μ.zero hs.2
  let _ : Module.Projective R (LinearMap.ker μ.zero) :=
    TwoTermComplex.kernel_projective μ.zero hs.2
  intro k hk
  set a : Fin m → L' := fun j => d' (k j) with ha
  set c : Fin n → L' := fun j => d' (t j) with hc
  have hra : ∀ j, r' (a j) = 0 := by
    intro j
    have hk : μ.neg (k j) = 0 := (k j).2
    refine κ.injective ?_
    rw [map_zero]
    exact (hrr _).trans (by simp [ha, hld, hk])
  have hππ : ∀ x, μ.zero (π' x) = π (l x) := fun x => (hπl x).symm
  set X0 : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker μ.neg) :=
    ⟨ExteriorAlgebra.ιMulti R m k, hk⟩
  have hX0coe : (X0 : ExteriorAlgebra R (LinearMap.ker μ.neg)) = ExteriorAlgebra.ιMulti R m k :=
    rfl
  obtain ⟨Y, hYdef⟩ : ∃ Y : ⋀[R]^(m + n) Mneg', Y = determinantEquivExteriorPower (m + n) hneg'
      (TwoTermComplex.kernelDeterminantEquiv μ.neg hs.1
        (X0 ⊗ₜ[R] (determinantEquivExteriorPower n hneg).symm (exteriorPower.ιMulti R n bN))) :=
    ⟨_, rfl⟩
  have hY : exteriorPower.map (m + n) d' Y =
      exteriorPower.ιMulti R (m + n) (Fin.append a c) := by
    refine Subtype.ext ?_
    rw [exteriorPower.coe_map, hYdef, coe_determinantEquivExteriorPower,
      coe_kernelDeterminantEquiv_tmul μ.neg hs.1 _ _ (ExteriorAlgebra.ιMulti R n t)]
    · rw [hX0coe, map_mul, ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti,
        ExteriorAlgebra.map_apply_ιMulti, exteriorPower.ιMulti_apply_coe,
        ← ExteriorAlgebra.ιMulti_mul_ιMulti]
      rfl
    · have hbt : (μ.neg ∘ t) = bN := funext ht
      rw [ExteriorAlgebra.map_apply_ιMulti, hbt, coe_determinantEquivExteriorPower_symm,
        exteriorPower.ιMulti_apply_coe]
  have hfin : (determinantEquivExteriorPower (m + n) hzero').symm.toLinearMap ∘ₗ
      exteriorPower.wedgeMul (R := R) m n (exteriorPower.ιMulti R m (π' ∘ a)) =
      ((TwoTermComplex.kernelDeterminantEquiv μ.zero hs.2).toLinearMap ∘ₗ
        TensorProduct.mk R _ _ (TwoTermComplex.delta μ.kernelDifferential
          (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso dM' dM μ hs hq).kernelRankZero
            X0) ∘ₗ (determinantEquivExteriorPower n hzero).symm.toLinearMap) ∘ₗ
        exteriorPower.map n μ.zero := by
    refine LinearMap.ext fun z => Subtype.ext ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.mk_apply]
    rw [coe_kernelDeterminantEquiv_tmul μ.zero hs.2 _ _ (z : ExteriorAlgebra R Mzero')]
    · rw [coe_determinantEquivExteriorPower_symm, exteriorPower.wedgeMul_apply_coe,
        exteriorPower.ιMulti_apply_coe]
      congr 1
      show _ = ExteriorAlgebra.map (LinearMap.ker μ.zero).subtype
        (ExteriorAlgebra.map μ.kernelDifferential (X0 : ExteriorAlgebra R _))
      rw [hX0coe, ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti]
      congr 1
      funext j
      simp only [Function.comp_apply, Submodule.coe_subtype, ha]
      exact LinearMap.congr_fun hsquare' _
    · rw [coe_determinantEquivExteriorPower_symm, exteriorPower.coe_map]
  have hdc : ∀ j, d (bN j) = l (c j) := fun j => by simp [hc, hld, ht]
  rw [lTensor_comp_twoTermDeterminantEquivOfSurjectiveQuasiIso (m + n) n dM' dM hzero' hneg'
      hzero hneg μ hs hq (exteriorPower.map p κ.toLinearMap) X0 (exteriorPower.ιMulti R n bN),
    ← hYdef, lTensor_twoTermDeterminantEval_funnyMapLift_of_map_eq r' π' hr'
      (comp_eq_zero_of_exact hexact') d' bN' Y a c hra hY,
    lTensor_comp_twoTermDeterminantEval_funnyMapLift_map p n κ.toLinearMap μ.zero l r' π' r π
      hrr hππ d bN c hdc v', lTensor_map_id_lTensor _ _ _ _ rfl,
    ← LinearMap.comp_apply (LinearMap.lTensor _ _) (TensorProduct.map _ _),
    LinearMap.lTensor_comp_map, hfin]

/-- **Naturality of the canonical maps of Tag 0FL8 under surjective quasi-isomorphisms.**
A morphism from a 0FL8 diagram `(i', π', d', dM')` of rank `n'` to one `(i, π, d, dM)` of rank
`n`, which is an isomorphism `κ` on the kernels and a degreewise-surjective quasi-isomorphism
`μ` on the two-term complexes, intertwines the canonical maps: the map induced on `H⁰`, followed
by the canonical map of the target, is the canonical map of the source followed by `⋀ᵖκ`
tensored with the isomorphism of determinant lines of Tag 0FJJ. -/
theorem funnyMap_naturality_of_surjectiveQuasiIso (n' n p : ℕ)
    (i' : K' →ₗ[R] L') (π' : L' →ₗ[R] Mzero') (d' : Mneg' →ₗ[R] L') (dM' : Mneg' →ₗ[R] Mzero')
    (i : K →ₗ[R] L) (π : L →ₗ[R] Mzero) (d : Mneg →ₗ[R] L) (dM : Mneg →ₗ[R] Mzero)
    (hi' : Function.Injective i') (hexact' : Function.Exact i' π')
    (hπ' : Function.Surjective π') (hsquare' : π'.comp d' = dM')
    (hzero' : Nonempty (Module.Basis (Fin n') R Mzero'))
    (hneg' : Nonempty (Module.Basis (Fin n') R Mneg'))
    (hi : Function.Injective i) (hexact : Function.Exact i π)
    (hπ : Function.Surjective π) (hsquare : π.comp d = dM)
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg))
    (κ : K' ≃ₗ[R] K) (l : L' →ₗ[R] L) (μ : TwoTermComplex.Hom dM' dM)
    (hs : μ.IsDegreewiseSurjective) (hq : μ.IsQuasiIso)
    (hli : ∀ x, l (i' x) = i (κ x)) (hπl : ∀ x, π (l x) = μ.zero (π' x))
    (hld : ∀ x, l (d' x) = d (μ.neg x))
    (hl : LinearMap.range d' ≤ (LinearMap.range d).comap l)
    (η : ⋀[R]^p (L' ⧸ LinearMap.range d')) :
    TensorProduct.map (exteriorPower.map p κ.toLinearMap)
        (twoTermDeterminantEquivOfSurjectiveQuasiIso n' n dM' dM hzero' hneg' hzero hneg μ hs
          hq).toLinearMap
        (funnyMap n' i' π' d' dM' hi' hexact' hπ' hsquare' hzero' hneg' p η) =
      funnyMap n i π d dM hi hexact hπ hsquare hzero hneg p
        (exteriorPower.map p ((LinearMap.range d').mapQ (LinearMap.range d) l hl) η) := by
  classical
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton ((⋀[R]^p K) ⊗[R] twoTermDeterminant R n Mneg Mzero) :=
      Module.subsingleton R _
    exact Subsingleton.elim _ _
  let _ : Module.Finite R (LinearMap.ker μ.neg) := TwoTermComplex.kernel_finite μ.neg hs.1
  let _ : Module.Projective R (LinearMap.ker μ.neg) :=
    TwoTermComplex.kernel_projective μ.neg hs.1
  let _ : Module.Finite R (LinearMap.ker μ.zero) := TwoTermComplex.kernel_finite μ.zero hs.2
  let _ : Module.Projective R (LinearMap.ker μ.zero) :=
    TwoTermComplex.kernel_projective μ.zero hs.2
  -- the kernel of `μ.neg` has constant rank `n' - n`
  have hrank : ∀ q : PrimeSpectrum R,
      n' = Module.rankAtStalk (LinearMap.ker μ.neg) q + n := by
    intro q
    obtain ⟨s, hs'⟩ := Module.projective_lifting_property μ.neg LinearMap.id hs.1
    have h1 := congrFun (Module.rankAtStalk_eq_of_equiv
      ((LinearMap.exact_subtype_ker_map μ.neg).splitSurjectiveEquiv
        (LinearMap.ker μ.neg).injective_subtype ⟨s, hs'⟩).1) q
    rwa [Module.rankAtStalk_prod, Pi.add_apply, rankAtStalk_eq_of_basis (Classical.choice hneg') q,
      rankAtStalk_eq_of_basis (Classical.choice hneg) q] at h1
  obtain ⟨q₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  obtain ⟨m, hm⟩ : ∃ m, n' = m + n := ⟨_, hrank q₀⟩
  subst hm
  have hrk : ∀ q, Module.rankAtStalk (LinearMap.ker μ.neg) q = m := fun q =>
    (Nat.add_right_cancel (hrank q)).symm
  set bN' : Module.Basis (Fin (m + n)) R Mneg' := Classical.choice hneg'
  set bN : Module.Basis (Fin n) R Mneg := Classical.choice hneg
  obtain ⟨r, hr⟩ := exists_retraction n i π hi hexact hπ hzero
  have hri : ∀ k, r (i k) = k := fun k => LinearMap.congr_fun hr k
  set r' : L' →ₗ[R] K' := κ.symm.toLinearMap ∘ₗ r ∘ₗ l with hr'def
  have hr' : r'.comp i' = LinearMap.id := by
    ext x
    simp [hr'def, hli, hri]
  choose t ht using fun j => hs.1 (bN j)
  -- the reduction to generators
  suffices H : (TensorProduct.map (exteriorPower.map p κ.toLinearMap)
      (twoTermDeterminantEquivOfSurjectiveQuasiIso (m + n) n dM' dM hzero' hneg' hzero hneg
        μ hs hq).toLinearMap) ∘ₗ
      funnyMap (m + n) i' π' d' dM' hi' hexact' hπ' hsquare' hzero' hneg' p =
      funnyMap n i π d dM hi hexact hπ hsquare hzero hneg p ∘ₗ
        exteriorPower.map p ((LinearMap.range d').mapQ (LinearMap.range d) l hl) from
    LinearMap.congr_fun H η
  refine LinearMap.ext_on (exteriorPower.ιMulti_span R p (L' ⧸ LinearMap.range d')) ?_
  rintro _ ⟨v, rfl⟩
  choose v' hv' using fun j => (LinearMap.range d').mkQ_surjective (v j)
  obtain rfl : v = fun j => (LinearMap.range d').mkQ (v' j) := funext fun j => (hv' j).symm
  have hmap : exteriorPower.map p ((LinearMap.range d').mapQ (LinearMap.range d) l hl)
      (exteriorPower.ιMulti R p fun j => (LinearMap.range d').mkQ (v' j)) =
      exteriorPower.ιMulti R p fun j => (LinearMap.range d).mkQ (l (v' j)) := by
    rw [exteriorPower.map_apply_ιMulti]
    rfl
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hmap,
    funnyMap_apply_ιMulti (m + n) p i' π' d' dM' hi' hexact' hπ' hsquare' hzero' hneg' r' hr'
      bN' v',
    funnyMap_apply_ιMulti n p i π d dM hi hexact hπ hsquare hzero hneg r hr bN
      (fun j => l (v' j))]
  refine eq_of_forall_lTensor_kernelDeterminantEquiv μ.zero hs.2 n hzero bN (fun x' => ?_)
  -- every element of the determinant of `ker μ.zero` is the image of one of `ker μ.neg`
  obtain ⟨x, rfl⟩ : ∃ x, TwoTermComplex.delta μ.kernelDifferential
      (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso dM' dM μ hs hq).kernelRankZero x =
        x' :=
    (ProjectiveDeterminant.map_bijective (LinearEquiv.ofBijective μ.kernelDifferential
      (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso dM' dM μ hs hq).kernelAcyclic)).2 x'
  -- the determinant of `ker μ.neg` is spanned by wedges of `m` vectors
  obtain ⟨ξ, rfl⟩ := (LinearEquiv.ofEq _ _
    (determinantSubmodule_eq_exteriorPower_of_rankAtStalk hrk)).symm.surjective x
  have hξ : ξ ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R m)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hξ using Submodule.span_induction with
  | zero => simp
  | add ξ₁ ξ₂ _ _ h₁ h₂ =>
      simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, LinearMap.lTensor_add,
        LinearMap.add_apply, h₁, h₂]
  | smul a ξ _ h =>
      simp only [map_smul, LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.lTensor_smul,
        LinearMap.smul_apply, h]
  | mem ξ hξ =>
      obtain ⟨k, rfl⟩ := hξ
      exact funnyMap_naturality_of_surjectiveQuasiIso_aux m n p i' π' d' dM' π d dM hexact'
        hsquare' hzero' hneg' hzero hneg κ l μ hs hq hπl hld r r' hr' (by simp [hr'def]) bN' bN
        t ht v' k _

end Naturality

end Stacks.DeRham
