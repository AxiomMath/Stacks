module

public import StacksFrontier.LinearAlgebra.Matrix.AdditiveFunctorComplexCharSeries
public import StacksFrontier.LinearAlgebra.Matrix.CyclicMatrixCharSeries
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Traces of powers detect the characteristic series of a perfect complex through `Φ`

Let `Φ : Mod_R ⥤ Mod_Λ` be an additive functor with `Φ(O)` free over the commutative ring `Λ`, `φ`
the attached representation `R →+* M_r(Λ)`, `Q` a bounded complex of finite projective `R`-modules
with an endomorphism `g`, and `(gₓ)ₓ` a finite family of elements of `R` indexed by "points" of
degrees `dₓ ≥ 1`. Assume the torsion hypothesis `(H_N)` for `φ`, and the trace identities

`Tr(g ^ m | Q) = ∑_{dₓ ∣ m} dₓ · [gₓ ^ (m / dₓ)]` in `R^♮` for `1 ≤ m ≤ N`.

Then `det(1 - Φ(g) T | Φ(Q)) ≡ ∏ₓ det(1 - φ(gₓ) T ^ dₓ) (mod T ^ (N + 1))`.

This is the lisse case of [Stacks, Tag 03UZ], in the form of the key lemma
`Stacks.CharSeriesTraceDetection.coeff_det_eq_of_trace_pow` applied to the block diagonal matrices
`A = ⊕_{i even} Aᵢ` and `B = ⊕_{i odd} Aᵢ ⊕ ⊕ₓ C(dₓ, gₓ)`, where `Aᵢ` are the padded matrices of
`g` on the terms of `Q` and `C(d, g)` is the cyclic matrix with `g` in the corner: on the trace
side `Tr(C(d, g) ^ m) = d · g ^ (m / d)` when `d ∣ m` and `0` otherwise, and on the determinant
side `det(1 - φ(C(d, g)) T) = det(1 - φ(g) T ^ d)`.

## Main results

* `Stacks.CharSeriesTraceDetection.coeff_alternatingCharSeries_functor_eq`: the characteristic
  series of `Φ(g)` on `Φ(Q)` agrees with `∏ₓ det(1 - φ(gₓ) T ^ (dₓ + 1))` up to `T ^ N`.
* `Stacks.CharSeriesTraceDetection.coeff_perfectDerivedCharSeries_eq_prod`: the same for a
  perfect object of the derived category identified with `Φ(Q)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Matrix PowerSeries
open CategoryTheory.FilteredDerived

universe u v v' w w'

namespace Stacks.CharSeriesTraceDetection

/-! ### Agreement of power series up to a degree -/

section Truncation

variable {S : Type*} [CommRing S]

/-- If two power series agree in degrees `≤ N`, then so do their products with any power series
`c`. -/
theorem coeff_mul_eq_of_coeff_eq {a b : PowerSeries S} {N : ℕ}
    (h : ∀ j ≤ N, coeff j a = coeff j b) (c : PowerSeries S) :
    ∀ j ≤ N, coeff j (c * a) = coeff j (c * b) := by
  intro j hj
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have := Finset.mem_antidiagonal.1 hx
  rw [h x.2 (by omega)]

end Truncation

/-! ### The blocks -/

section Blocks

variable {R : Type u} [Ring R] {O : ModuleCat.{v} R} (eO : R ≃ₗ[R] O)
  (Q : CochainComplex (ModuleCat.{v} R) ℤ) (hQ : finiteProjectiveComplex R Q) (g : Q ⟶ Q)
  (S : Finset ℤ) {P : Type*} (dP : P → ℕ) (gP : P → R)

/-- The sizes of the blocks: `nᵢ` for a degree `i ∈ S`, and `dₓ + 1` for a point `x`. -/
def blockSize : {i // i ∈ S} ⊕ P → ℕ
  | Sum.inl i => degRank eO Q hQ i.1
  | Sum.inr x => dP x + 1

/-- The blocks of `A`: `Aᵢ` in even degrees, `0` otherwise. -/
def blocksEven : ∀ j : {i // i ∈ S} ⊕ P,
    Matrix (Fin (blockSize eO Q hQ S dP j)) (Fin (blockSize eO Q hQ S dP j)) R
  | Sum.inl i => if Even i.1 then degMatrix eO Q hQ g i.1 else 0
  | Sum.inr _ => 0

/-- The blocks of `B`: `Aᵢ` in odd degrees, and the cyclic matrix `C(dₓ, gₓ)` at a point. -/
def blocksOdd : ∀ j : {i // i ∈ S} ⊕ P,
    Matrix (Fin (blockSize eO Q hQ S dP j)) (Fin (blockSize eO Q hQ S dP j)) R
  | Sum.inl i => if Even i.1 then 0 else degMatrix eO Q hQ g i.1
  | Sum.inr x => cyclicMatrix (dP x) (gP x)

end Blocks

section Detection

variable {R : Type u} [Ring R] {Λ : Type w} [CommRing Λ]
  (Φ : ModuleCat.{v} R ⥤ ModuleCat.{v'} Λ) [Φ.Additive] {O : ModuleCat.{v} R} (eO : R ≃ₗ[R] O)
  {r : ℕ} (b : Φ.obj O ≃ₗ[Λ] (Fin r → Λ))
  (Q : CochainComplex (ModuleCat.{v} R) ℤ) (hQ : finiteProjectiveComplex R Q) (g : Q ⟶ Q)

/-- The characteristic series `det(1 - φ(0) T)` of the zero block matrix is `1`. -/
theorem det_one_sub_X_smul_blockMap_zero (n : Type) [Fintype n] [DecidableEq n] :
    (1 - (X : PowerSeries Λ) • (blockMap (functorRep Φ eO b) n 0).map (C (R := Λ))).det = 1 := by
  rw [map_zero, Matrix.map_zero _ (map_zero _), smul_zero, sub_zero, Matrix.det_one]

/-- **The lisse case of [Stacks, Tag 03UZ], algebraically.** Under the torsion hypothesis
`(H_N)` for `φ = functorRep Φ eO b` and the trace identities
`Tr(g ^ m | Q) = ∑_{(dₓ + 1) ∣ m} (dₓ + 1) · [gₓ ^ (m / (dₓ + 1))]` for `1 ≤ m ≤ N`, the
characteristic series of `Φ(g)` on `Φ(Q)` agrees with `∏ₓ det(1 - φ(gₓ) T ^ (dₓ + 1))` up to
`T ^ N`. -/
theorem coeff_alternatingCharSeries_functor_eq {N : ℕ}
    (H : TraceDetectionHypothesis (functorRep Φ eO b) N) (S : Finset ℤ)
    (hS : ∀ i ∉ S, IsZero (Q.X i)) {P : Type*} [Fintype P] (dP : P → ℕ) (gP : P → R)
    (htr : ∀ m, 0 < m → m ≤ N → ∃ h : Q ⟶ Q, (∀ i, (h.f i).hom = (g.f i).hom ^ m) ∧
      alternatingTrace R Q hQ h = ∑ x, if (dP x + 1) ∣ m then
        (dP x + 1) • q R (gP x ^ (m / (dP x + 1))) else 0) :
    ∀ j ≤ N, coeff j (alternatingCharSeries Λ _ (finiteProjectiveComplex_functor Φ eO b Q hQ)
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) : PowerSeries Λ) =
      coeff j (∏ x, (1 - (X : PowerSeries Λ) ^ (dP x + 1) •
        (functorRep Φ eO b (gP x)).map (C (R := Λ))).det) := by
  classical
  set φ := functorRep Φ eO b
  set k := blockSize eO Q hQ S dP
  set A := Matrix.blockDiagonal' (blocksEven eO Q hQ g S dP)
  set B := Matrix.blockDiagonal' (blocksOdd eO Q hQ g S dP gP)
  set d : ℤ → PowerSeries Λ := fun i => (1 - (X : PowerSeries Λ) • (blockMap φ
    (Fin (degRank eO Q hQ i)) (degMatrix eO Q hQ g i)).map (C (R := Λ))).det
  set pts : PowerSeries Λ := ∏ x, (1 - (X : PowerSeries Λ) ^ (dP x + 1) •
    (φ (gP x)).map (C (R := Λ))).det
  set c : PowerSeries Λ := (alternatingCharSeries Λ _ (finiteProjectiveComplex_functor Φ eO b Q hQ)
    ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) : PowerSeries Λ)
  have htrAB : ∀ m, 0 < m → m ≤ N → trq _ (A ^ m) = trq _ (B ^ m) := by
    intro m hm hmN
    obtain ⟨h, hgh, hh⟩ := htr m hm hmN
    have hsum := alternatingTrace_eq_sum_trq eO Q hQ g h hm hgh S hS
    rw [hh] at hsum
    have hz : ∀ (n : Type) [Fintype n] [DecidableEq n],
        trq n ((0 : Matrix n n R) ^ m) = 0 := fun n _ _ => by
      rw [zero_pow hm.ne', map_zero]
    have eA1 : ∀ a : {i // i ∈ S}, trq _ (blocksEven eO Q hQ g S dP (Sum.inl a) ^ m) =
        if Even a.1 then trq _ (degMatrix eO Q hQ g a.1 ^ m) else 0 := fun a => by
      show trq (Fin (degRank eO Q hQ a.1))
        ((if Even a.1 then degMatrix eO Q hQ g a.1 else 0) ^ m) = _
      split_ifs
      · rfl
      · exact hz _
    have eA2 : ∀ x : P, trq _ (blocksEven eO Q hQ g S dP (Sum.inr x) ^ m) = 0 := fun x =>
      hz (Fin (dP x + 1))
    have eB1 : ∀ a : {i // i ∈ S}, trq _ (blocksOdd eO Q hQ g S dP gP (Sum.inl a) ^ m) =
        if Even a.1 then 0 else trq _ (degMatrix eO Q hQ g a.1 ^ m) := fun a => by
      show trq (Fin (degRank eO Q hQ a.1))
        ((if Even a.1 then 0 else degMatrix eO Q hQ g a.1) ^ m) = _
      split_ifs
      · exact hz _
      · rfl
    have eB2 : ∀ x : P, trq _ (blocksOdd eO Q hQ g S dP gP (Sum.inr x) ^ m) =
        if (dP x + 1) ∣ m then (dP x + 1) • q R (gP x ^ (m / (dP x + 1))) else 0 := fun x => by
      show trq (Fin (dP x + 1)) (cyclicMatrix (dP x) (gP x) ^ m) = _
      rw [trq_apply, trace_cyclicMatrix_pow]
      split_ifs
      · rw [map_nsmul]
      · exact map_zero _
    rw [trq_blockDiagonal'_pow, trq_blockDiagonal'_pow, Fintype.sum_sum_type,
      Fintype.sum_sum_type]
    simp only [eA1, eA2, eB1, eB2, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_coe_sort S (fun i => if Even i then trq _ (degMatrix eO Q hQ g i ^ m)
      else 0), Finset.sum_coe_sort S (fun i => if Even i then 0
        else trq _ (degMatrix eO Q hQ g i ^ m)), hsum]
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have hKL : ∀ j ≤ N, coeff j (1 - (X : PowerSeries Λ) • (blockMap φ _ A).map (C (R := Λ))).det =
      coeff j (1 - (X : PowerSeries Λ) • (blockMap φ _ B).map (C (R := Λ))).det := by
    intro j hj
    rcases isEmpty_or_nonempty (Σ j, Fin (k j)) with hn | hne
    · rw [Matrix.det_isEmpty, Matrix.det_isEmpty]
    · obtain ⟨i₀⟩ := hne
      exact coeff_det_eq_of_trace_pow φ i₀ H A B htrAB hj
  have e0 : ∀ (n : Type) [Fintype n] [DecidableEq n],
      (1 - (X : PowerSeries Λ) • (blockMap φ n 0).map (C (R := Λ))).det = 1 := fun n _ _ =>
    det_one_sub_X_smul_blockMap_zero Φ eO b n
  have fA1 : ∀ a : {i // i ∈ S}, (1 - (X : PowerSeries Λ) • (blockMap φ _
      (blocksEven eO Q hQ g S dP (Sum.inl a))).map (C (R := Λ))).det =
      if Even a.1 then d a.1 else 1 := fun a => by
    show (1 - (X : PowerSeries Λ) • (blockMap φ (Fin (degRank eO Q hQ a.1))
      (if Even a.1 then degMatrix eO Q hQ g a.1 else 0)).map (C (R := Λ))).det = _
    split_ifs
    · rfl
    · exact e0 _
  have fA2 : ∀ x : P, (1 - (X : PowerSeries Λ) • (blockMap φ _
      (blocksEven eO Q hQ g S dP (Sum.inr x))).map (C (R := Λ))).det = 1 := fun x =>
    e0 (Fin (dP x + 1))
  have fB1 : ∀ a : {i // i ∈ S}, (1 - (X : PowerSeries Λ) • (blockMap φ _
      (blocksOdd eO Q hQ g S dP gP (Sum.inl a))).map (C (R := Λ))).det =
      if Even a.1 then 1 else d a.1 := fun a => by
    show (1 - (X : PowerSeries Λ) • (blockMap φ (Fin (degRank eO Q hQ a.1))
      (if Even a.1 then 0 else degMatrix eO Q hQ g a.1)).map (C (R := Λ))).det = _
    split_ifs
    · exact e0 _
    · rfl
  have fB2 : ∀ x : P, (1 - (X : PowerSeries Λ) • (blockMap φ _
      (blocksOdd eO Q hQ g S dP gP (Sum.inr x))).map (C (R := Λ))).det =
      (1 - (X : PowerSeries Λ) ^ (dP x + 1) • (φ (gP x)).map (C (R := Λ))).det := fun x =>
    det_one_sub_X_smul_blockMap_cyclicMatrix φ (dP x) (gP x)
  have hA : (1 - (X : PowerSeries Λ) • (blockMap φ _ A).map (C (R := Λ))).det =
      ∏ i ∈ S.filter (fun i => Even i), d i := by
    rw [det_one_sub_X_smul_blockMap_blockDiagonal', Fintype.prod_sum_type]
    simp only [fA1, fA2, Finset.prod_const_one, mul_one]
    rw [Finset.prod_coe_sort S (fun i => if Even i then d i else 1), Finset.prod_filter]
  have hB : (1 - (X : PowerSeries Λ) • (blockMap φ _ B).map (C (R := Λ))).det =
      (∏ i ∈ S.filter (fun i => ¬ Even i), d i) * pts := by
    rw [det_one_sub_X_smul_blockMap_blockDiagonal', Fintype.prod_sum_type]
    simp only [fB1, fB2]
    rw [Finset.prod_coe_sort S (fun i => if Even i then 1 else d i), Finset.prod_filter]
    simp only [ite_not, pts]
  have hc := alternatingCharSeries_functor_mul_prod_odd Φ eO b Q hQ g S hS
  set U : (PowerSeries Λ)ˣ := ∏ i ∈ S.filter (fun i => ¬ Even i),
    charUnitAt Λ _ (finiteProjectiveComplex_functor Φ eO b Q hQ) i
      (((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g).f i)
  have hU : (U : PowerSeries Λ) = ∏ i ∈ S.filter (fun i => ¬ Even i), d i := by
    rw [Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => coe_charUnitAt_functor Φ eO b Q hQ g i
  have hmain :
      ∀ j ≤ N, coeff j (c * (U : PowerSeries Λ)) = coeff j (pts * (U : PowerSeries Λ)) := by
    intro j hj
    have h1 := hKL j hj
    rw [hA, hB, ← hc, ← hU] at h1
    rwa [mul_comm pts]
  intro j hj
  have h2 := coeff_mul_eq_of_coeff_eq hmain (↑U⁻¹ : PowerSeries Λ) j hj
  rwa [mul_comm c, ← mul_assoc, Units.inv_mul, one_mul, mul_comm pts, ← mul_assoc,
    Units.inv_mul, one_mul] at h2

/-- **The lisse case of [Stacks, Tag 03UZ] for a perfect object of the derived category.** Let
`K` be a perfect complex of `Λ`-modules with an endomorphism `f`, identified with `Φ(Q)` so that
`f` corresponds to `Φ(g)`. Under `(H_N)` for `φ = functorRep Φ eO b` and the trace identities
`Tr(g ^ m | Q) = ∑_{x ∈ t, dₓ ∣ m} dₓ · [gₓ ^ (m / dₓ)]` for `1 ≤ m ≤ N`, the characteristic series
of `f` agrees with `∏_{x ∈ t} det(1 - φ(gₓ) T ^ dₓ)` up to `T ^ N`. -/
theorem coeff_perfectDerivedCharSeries_eq_prod [HasDerivedCategory.{w'} (ModuleCat.{v'} Λ)]
    {N : ℕ} (H : TraceDetectionHypothesis (functorRep Φ eO b) N)
    (K : DerivedCategory (ModuleCat.{v'} Λ)) (hK : StacksDraft.Perfect.IsPerfect K) (fK : K ⟶ K)
    (e : DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) ≅ K)
    (he : DerivedCategory.Q.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫ e.hom =
      e.hom ≫ fK)
    {ι : Type*} (t : Finset ι) (deg : ι → ℕ) (hdeg : ∀ x ∈ t, 0 < deg x) (gP : ι → R)
    (htr : ∀ m, 0 < m → m ≤ N → ∃ h : Q ⟶ Q, (∀ i, (h.f i).hom = (g.f i).hom ^ m) ∧
      alternatingTrace R Q hQ h = ∑ x ∈ t, if deg x ∣ m then
        deg x • q R (gP x ^ (m / deg x)) else 0) :
    ∀ j ≤ N, coeff j (perfectDerivedCharSeries Λ K hK fK : PowerSeries Λ) =
      coeff j (∏ x ∈ t, (1 - (X : PowerSeries Λ) ^ deg x •
        (functorRep Φ eO b (gP x)).map (C (R := Λ))).det) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset ℤ, ∀ i ∉ S, IsZero (Q.X i) := by
    obtain ⟨⟨⟨lo, hlo⟩, ⟨hi, hhi⟩⟩, -⟩ := hQ
    refine ⟨Finset.Icc lo hi, fun i hi' => ?_⟩
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hi'
    rcases hi' with h | h
    · exact Q.isZero_of_isStrictlyGE lo i h
    · exact Q.isZero_of_isStrictlyLE hi i h
  have hc : perfectDerivedCharSeries Λ K hK fK =
      alternatingCharSeries Λ _ (finiteProjectiveComplex_functor Φ eO b Q hQ)
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
    perfectDerivedCharSeries_eq_alternatingCharSeries Λ K hK fK _ _ e _ (by
      rw [← reassoc_of% he, Iso.hom_inv_id, Category.comp_id])
  have key := coeff_alternatingCharSeries_functor_eq Φ eO b Q hQ g H S hS
    (P := t) (fun x => deg x.1 - 1) (fun x => gP x.1) (by
      intro m hm hmN
      obtain ⟨h, hgh, hh⟩ := htr m hm hmN
      refine ⟨h, hgh, ?_⟩
      rw [hh, ← Finset.sum_coe_sort t]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Nat.sub_add_cancel (hdeg x.1 x.2)])
  intro j hj
  rw [hc, key j hj, ← Finset.prod_coe_sort t]
  congr 1
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Nat.sub_add_cancel (hdeg x.1 x.2)]

end Detection

/-! ### Powers of a chain endomorphism -/

section Powers

variable {R : Type u} [Ring R] {Q : CochainComplex (ModuleCat.{v} R) ℤ}

/-- The `m`-th power of a chain endomorphism is degreewise the `m`-th power. -/
theorem hom_f_endPow (g : Q ⟶ Q) (m : ℕ) (i : ℤ) :
    (((End.of g) ^ m : End Q).asHom.f i).hom = (g.f i).hom ^ m := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero, End.one_asHom, HomologicalComplex.id_f, ModuleCat.hom_id,
      Module.End.one_eq_id]
  | succ m ih =>
    rw [pow_succ, End.mul_asHom, HomologicalComplex.comp_f, ModuleCat.hom_comp, ih, pow_succ,
      Module.End.mul_eq_comp]

/-- `Q(g ^ m)` is intertwined with `f ^ m` by an isomorphism intertwining `Q(g)` and `f`. -/
theorem map_endPow_comp {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {A : C} {B : D}
    (g : A ⟶ A) (f : B ⟶ B) (e : G.obj A ≅ B) (he : G.map g ≫ e.hom = e.hom ≫ f) (m : ℕ) :
    G.map ((End.of g) ^ m : End A).asHom ≫ e.hom =
      e.hom ≫ ((End.of f) ^ m : End B).asHom := by
  induction m with
  | zero => simp [End.one_asHom]
  | succ m ih =>
    rw [pow_succ, pow_succ, End.mul_asHom, End.mul_asHom, G.map_comp, Category.assoc, ih,
      ← Category.assoc, he, Category.assoc]

section StandardModel

attribute [local instance] HasDerivedCategory.standard

/-- **The trace of `g ^ m` on a bounded finite projective representative is the trace of `f ^ m`
on the perfect object it represents.** -/
@[sga "4½ Rapport 4.3" "partial"]
theorem alternatingTrace_endPow_eq_perfectDerivedTrace (hQ : finiteProjectiveComplex R Q)
    (g : Q ⟶ Q) (KR : PerfectDerivedCategory.{u, v} R) (fR : KR.obj ⟶ KR.obj)
    (eR : DerivedCategory.Q.obj Q ≅ KR.obj)
    (heR : DerivedCategory.Q.map g ≫ eR.hom = eR.hom ≫ fR) (m : ℕ) :
    alternatingTrace R Q hQ ((End.of g) ^ m : End Q).asHom =
      perfectDerivedTrace R KR ((End.of fR) ^ m : End KR.obj).asHom := by
  refine (perfectDerivedTrace_eq_alternatingTrace R KR _ Q hQ eR _ ?_).symm
  rw [← reassoc_of% (map_endPow_comp DerivedCategory.Q g fR eR heR m), Iso.hom_inv_id,
    Category.comp_id]

end StandardModel

end Powers

/-! ### Traces concentrated in one degree and on a free module of rank one -/

section RankOneTrace

variable {R : Type u} [Ring R]

/-- **The trace of an endomorphism of a free module of rank one** which is right multiplication
by `h` in a coordinate `ε : M ≃ R` is the class of `h`. -/
@[sga "6 I 8.1.1" "special case"]
theorem projectiveModuleTrace_eq_q_of_linearEquiv {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (ε : M ≃ₗ[R] R) (φ : Module.End R M) (h : R)
    (hφ : ∀ x, ε (φ x) = ε x * h) :
    Stacks.Trace.projectiveModuleTrace R M φ = q R h := by
  let e1 : (Fin 1 → R) ≃ₗ[R] R := LinearEquiv.funUnique (Fin 1) R R
  let p' : (Fin 1 → R) →ₗ[R] M := ε.symm.toLinearMap ∘ₗ e1.toLinearMap
  let i' : M →ₗ[R] (Fin 1 → R) := e1.symm.toLinearMap ∘ₗ ε.toLinearMap
  have hpi : p'.comp i' = LinearMap.id := by
    ext x
    simp [p', i']
  rw [projectiveModuleTrace_eq_of_split R M φ p' i' hpi, freeModuleTrace_eq_trq, trq_apply,
    Matrix.trace_fin_one]
  congr 1
  simp only [endMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, p', i']
  rw [show e1 (Pi.single 0 1) = 1 by simp [e1], show (e1.symm (ε (φ (ε.symm 1)))) 0 =
    ε (φ (ε.symm 1)) by simp [e1], hφ, LinearEquiv.apply_symm_apply, one_mul]

/-- **The alternating trace of a complex concentrated in degree `0`** is the trace in degree
`0`. -/
theorem alternatingTrace_eq_of_isZero {Q : CochainComplex (ModuleCat.{v} R) ℤ}
    (hQ : finiteProjectiveComplex R Q) (hz : ∀ i ≠ 0, Limits.IsZero (Q.X i)) (g : Q ⟶ Q) :
    alternatingTrace R Q hQ g =
      letI : Module.Projective R (Q.X 0) := (hQ.2 0).1
      letI : Module.Finite R (Q.X 0) := (hQ.2 0).2
      Stacks.Trace.projectiveModuleTrace R (Q.X 0) (g.f 0).hom := by
  unfold alternatingTrace
  rw [finsum_eq_single _ 0 fun i hi => ?_]
  · simp
  · let : Module.Projective R (Q.X i) := (hQ.2 i).1
    let : Module.Finite R (Q.X i) := (hQ.2 i).2
    have := ModuleCat.subsingleton_of_isZero (hz i hi)
    show (if Even i then Stacks.Trace.projectiveModuleTrace R (Q.X i) (g.f i).hom
      else -Stacks.Trace.projectiveModuleTrace R (Q.X i) (g.f i).hom) = 0
    rw [projectiveModuleTrace_eq_zero_of_subsingleton, neg_zero, ite_self]

end RankOneTrace

end Stacks.CharSeriesTraceDetection
