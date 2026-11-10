module

public import StacksFrontier.RingTheory.Kaehler.DeRhamShiftedSum
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# The cohomology of a finite sum of shifted de Rham complexes

Let `R ⟶ A` be a map of commutative rings and `n : I → ℕ` a finite family of degrees. The
cohomology of the complex `M = ⨁_i Ω^•_{A/R}[-n_i]` (`Stacks.KatzOda.ShiftedSum.complex`) is the
direct sum of the shifted cohomologies of the algebraic de Rham complex:

`H^N(⨁_i Ω^•_{A/R}[-n_i]) ≅ ⨁_i H^{N - n_i}(Ω^•_{A/R})`,

where `Ω^•_{A/R}` is read as a complex indexed by `ℤ`, zero in negative degrees.

## Main definitions

* `Stacks.KatzOda.ShiftedSum.inj`, `Stacks.KatzOda.ShiftedSum.pr`: the inclusion of and the
  projection to the summand `Ω^•_{A/R}[-n_i]`, as maps of complexes.
* `Stacks.KatzOda.ShiftedSum.homologyEquiv`: the isomorphism above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.KatzOda.ShiftedSum

open Stacks.AlgebraicGeometry.AffineDifferentialsIso

variable {R A : CommRingCat.{u}} (gR : R ⟶ A) {I : Type u} [DecidableEq I] (n : I → ℕ)

/-- The algebraic de Rham complex `Ω^•_{A/R}`, indexed by `ℤ` and zero in negative degrees. -/
abbrev intComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  (ringDeRhamComplex gR).extend ComplexShape.embeddingUpNat

/-- The identification of the degree `p + k` term of `Ω^•_{A/R}` with the forms of degree `b`. -/
abbrev intXIso {p k : ℤ} (b : ℕ) (h : (b : ℤ) = p + k) :
    (intComplex gR).X (p + k) ≅ (ringDeRhamComplex gR).X b :=
  (ringDeRhamComplex gR).extendXIso ComplexShape.embeddingUpNat h

/-- The terms of `Ω^•_{A/R}` in negative degrees are zero. -/
theorem subsingleton_intComplex_X (p : ℤ) (hp : p < 0) :
    Subsingleton ((intComplex gR).X p) :=
  ModuleCat.isZero_iff_subsingleton.1 ((ringDeRhamComplex gR).isZero_extend_X _ p
    fun b hb => by
      have : ((b : ℕ) : ℤ) = p := hb
      omega)

/-- The inclusion of the summand `i`, in degree `p`. -/
def injF (i : I) (p : ℤ) : (intComplex gR).X (p + -(n i : ℤ)) →ₗ[R] MX gR n p :=
  LinearMap.single R (fun j : I => ∀ b : {b : ℕ // (n j : ℤ) + b = p}, (ringDeRhamComplex gR).X b.1)
      i ∘ₗ
    LinearMap.pi fun b => (intXIso gR b.1 (by have := b.2; omega)).hom.hom

/-- The projection to the summand `i`, in degree `p`. -/
def prF (i : I) (p : ℤ) : MX gR n p →ₗ[R] (intComplex gR).X (p + -(n i : ℤ)) :=
  if h : 0 ≤ p + -(n i : ℤ) then
    (intXIso gR (p + -(n i : ℤ)).toNat (by omega)).inv.hom ∘ₗ
      LinearMap.proj (R := R) (φ := fun b : {b : ℕ // (n i : ℤ) + b = p} =>
        (ringDeRhamComplex gR).X b.1) ⟨(p + -(n i : ℤ)).toNat, by omega⟩ ∘ₗ
      LinearMap.proj (R := R) (φ := fun j : I => ∀ b : {b : ℕ // (n j : ℤ) + b = p},
        (ringDeRhamComplex gR).X b.1) i
  else 0

/-- The `i`-th component of `injF i p x` is `x`, read as a form of the appropriate degree. -/
theorem injF_apply_self (i : I) (p : ℤ) (x : (intComplex gR).X (p + -(n i : ℤ)))
    (b : {b : ℕ // (n i : ℤ) + b = p}) :
    injF gR n i p x i b = (intXIso gR b.1 (by have := b.2; omega)).hom x := by
  simp only [injF, LinearMap.comp_apply, LinearMap.single_apply, Pi.single_eq_same,
    LinearMap.pi_apply]

/-- The `j`-th component of `injF i p x` vanishes for `j ≠ i`. -/
theorem injF_apply_ne {i j : I} (h : j ≠ i) (p : ℤ) (x : (intComplex gR).X (p + -(n i : ℤ))) :
    injF gR n i p x j = 0 := by
  simp only [injF, LinearMap.comp_apply, LinearMap.single_apply]
  exact Pi.single_eq_of_ne h _

omit [DecidableEq I] in
/-- For `p - n_i ≥ 0`, `prF i p x` is the component of `x` in the summand `i` of degree
`p - n_i`. -/
theorem prF_apply_of_le (i : I) (p : ℤ) (h : 0 ≤ p + -(n i : ℤ)) (x : MX gR n p) :
    prF gR n i p x = (intXIso gR (p + -(n i : ℤ)).toNat (by omega)).inv
      (x i ⟨(p + -(n i : ℤ)).toNat, by omega⟩) := by
  simp only [prF, dite_eq_left h, LinearMap.comp_apply, LinearMap.proj_apply]

/-- Projecting to the summand `i` after including into it is the identity. -/
theorem prF_injF_self (i : I) (p : ℤ) (x : (intComplex gR).X (p + -(n i : ℤ))) :
    prF gR n i p (injF gR n i p x) = x := by
  by_cases h : 0 ≤ p + -(n i : ℤ)
  · rw [prF_apply_of_le gR n i p h, injF_apply_self]
    exact Iso.hom_inv_id_apply _ _
  · have := subsingleton_intComplex_X gR (p + -(n i : ℤ)) (by omega)
    exact Subsingleton.elim _ _

/-- Projecting to the summand `j` after including into the summand `i ≠ j` is zero. -/
theorem prF_injF_ne {i j : I} (h : j ≠ i) (p : ℤ) (x : (intComplex gR).X (p + -(n i : ℤ))) :
    prF gR n j p (injF gR n i p x) = 0 := by
  by_cases hp : 0 ≤ p + -(n j : ℤ)
  · rw [prF_apply_of_le gR n j p hp, injF_apply_ne gR n h]
    exact map_zero _
  · simp only [prF, dite_eq_right hp, LinearMap.zero_apply]

/-- In each degree, `x = ∑_i injF i p (prF i p x)`. -/
theorem sum_injF_prF [Fintype I] (p : ℤ) (x : MX gR n p) :
    ∑ i, injF gR n i p (prF gR n i p x) = x := by
  funext j b
  rw [Finset.sum_apply, Finset.sum_eq_single j (fun i _ hij => by
      rw [injF_apply_ne gR n (Ne.symm hij)]) (fun h => absurd (Finset.mem_univ j) h),
    injF_apply_self]
  obtain ⟨b, hb⟩ := b
  have h0 : 0 ≤ p + -(n j : ℤ) := by omega
  rw [prF_apply_of_le gR n j p h0]
  obtain rfl : b = (p + -(n j : ℤ)).toNat := by omega
  exact Iso.inv_hom_id_apply _ _

/-- For `k : ℕ`, the action of the sign `(-1)^{-k}` agrees with that of the integer `(-1)^k`. -/
theorem negOnePow_smul_eq {M : Type*} [AddCommGroup M] (k : ℕ) (y : M) :
    (-(k : ℤ)).negOnePow • y = ((-1 : ℤ) ^ k) • y := by
  rw [Int.negOnePow_neg, Units.smul_def, Int.coe_negOnePow_natCast]

omit [DecidableEq I] in
/-- If `n_i + b = p`, then `prF i p x` is the component of `x` in the summand `i` of degree
`b`. -/
theorem prF_apply_of_eq (i : I) (p : ℤ) (b : ℕ) (hb : (n i : ℤ) + b = p) (x : MX gR n p) :
    prF gR n i p x = (intXIso gR b (by omega)).inv (x i ⟨b, hb⟩) := by
  obtain rfl : b = (p + -(n i : ℤ)).toNat := by omega
  exact prF_apply_of_le gR n i p (by omega) x

omit [DecidableEq I] in
/-- For `p - n_i < 0`, the projection `prF i p` is zero. -/
theorem prF_apply_of_lt (i : I) (p : ℤ) (h : p + -(n i : ℤ) < 0) (x : MX gR n p) :
    prF gR n i p x = 0 := by
  simp only [prF, dite_eq_right (not_le.2 h), LinearMap.zero_apply]

/-- In nonnegative degree `c`, the differential of `intComplex` is the de Rham differential
`d : Ω^c_{A/R} → Ω^{c+1}_{A/R}`. -/
theorem intComplex_d_apply (c : ℕ) {p k : ℤ} (hc : (c : ℤ) = p + k)
    (x : (intComplex gR).X (p + k)) :
    ((intComplex gR).d (p + k) (p + 1 + k)).hom x =
      (intXIso gR (k := k) (c + 1) (by push_cast; omega)).inv
        (((ringDeRhamComplex gR).d c (c + 1)).hom ((intXIso gR c hc).hom x)) := by
  rw [HomologicalComplex.extend_d_eq (ringDeRhamComplex gR) ComplexShape.embeddingUpNat
    (i := c) (j := c + 1) hc (by change ((c + 1 : ℕ) : ℤ) = _; push_cast; omega)]
  rfl

/-- The differential of `⨁_i Ω^•_{A/R}[-n_i]` on the summand `i` is `(-1)^{n_i} d`. -/
theorem dTo_injF (i : I) (p : ℤ) (x : (intComplex gR).X (p + -(n i : ℤ))) :
    dTo gR n p (p + 1) rfl (injF gR n i p x) =
      injF gR n i (p + 1) ((-(n i : ℤ)).negOnePow •
        ((intComplex gR).d (p + -(n i : ℤ)) (p + 1 + -(n i : ℤ))).hom x) := by
  funext j ⟨b, hb⟩
  rw [dTo_apply]
  by_cases hji : j = i
  · subst hji
    rcases b with _ | c
    · have := subsingleton_intComplex_X gR (p + -(n j : ℤ)) (by push_cast at hb; omega)
      change dAt gR n _ j 0 _ = _
      rw [dAt_zero, Subsingleton.elim x 0]
      simp
    · rw [dAt_succ, injF_apply_self, injF_apply_self, negOnePow_smul_eq, map_zsmul,
        intComplex_d_apply gR c (by push_cast at hb; omega)]
      exact congrArg _ (Iso.inv_hom_id_apply _ _).symm
  · rw [injF_apply_ne gR n hji]
    rcases b with _ | c
    · change dAt gR n _ j 0 _ = _
      rw [dAt_zero]
      rfl
    · rw [dAt_succ, injF_apply_ne gR n hji]
      simp

omit [DecidableEq I] in
/-- The projection to the summand `i` intertwines the differential of `⨁_i Ω^•_{A/R}[-n_i]`
with `(-1)^{n_i} d`. -/
theorem prF_dTo (i : I) (p : ℤ) (x : MX gR n p) :
    prF gR n i (p + 1) (dTo gR n p (p + 1) rfl x) =
      (-(n i : ℤ)).negOnePow •
        ((intComplex gR).d (p + -(n i : ℤ)) (p + 1 + -(n i : ℤ))).hom (prF gR n i p x) := by
  by_cases h1 : 0 ≤ p + 1 + -(n i : ℤ)
  · obtain ⟨b, hb⟩ : ∃ b : ℕ, (n i : ℤ) + b = p + 1 := ⟨(p + 1 + -(n i : ℤ)).toNat, by omega⟩
    rw [prF_apply_of_eq gR n i (p + 1) b hb, dTo_apply]
    rcases b with _ | c
    · rw [dAt_zero, map_zero, prF_apply_of_lt gR n i p (by push_cast at hb; omega), map_zero,
        smul_zero]
    · rw [dAt_succ, prF_apply_of_eq gR n i p c (by push_cast at hb; omega),
        negOnePow_smul_eq, map_zsmul,
        intComplex_d_apply gR c (by push_cast at hb; omega), Iso.inv_hom_id_apply]
  · have := subsingleton_intComplex_X gR (p + 1 + -(n i : ℤ)) (by omega)
    exact Subsingleton.elim _ _

/-- The differential of the shift `Ω^•_{A/R}[k]` is `(-1)^k` times that of `Ω^•_{A/R}`. -/
theorem shift_d_apply (k p q : ℤ) (x : (intComplex gR).X (p + k)) :
    ((((intComplex gR)⟦k⟧).d p q).hom x) =
      k.negOnePow • ((intComplex gR).d (p + k) (q + k)).hom x := by
  rw [CochainComplex.shiftFunctor_obj_d', Units.smul_def, ModuleCat.hom_zsmul, LinearMap.smul_apply,
    Units.smul_def]

/-- **The inclusion of the summand `Ω^•_{A/R}[-n_i]`**, as a map of complexes. -/
def inj (i : I) : (intComplex gR)⟦-(n i : ℤ)⟧ ⟶ complex gR n where
  f p := ModuleCat.ofHom (injF gR n i p)
  comm' p q h := by
    change p + 1 = q at h
    subst h
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change ((complex gR n).d p (p + 1)).hom (injF gR n i p x) =
      injF gR n i (p + 1) ((((intComplex gR)⟦-(n i : ℤ)⟧).d p (p + 1)).hom x)
    rw [complex_d_apply gR n rfl, dTo_injF, shift_d_apply]

/-- **The projection to the summand `Ω^•_{A/R}[-n_i]`**, as a map of complexes. -/
def pr (i : I) : complex gR n ⟶ (intComplex gR)⟦-(n i : ℤ)⟧ where
  f p := ModuleCat.ofHom (prF gR n i p)
  comm' p q h := by
    change p + 1 = q at h
    subst h
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (((intComplex gR)⟦-(n i : ℤ)⟧).d p (p + 1)).hom (prF gR n i p x) =
      prF gR n i (p + 1) (((complex gR n).d p (p + 1)).hom x)
    rw [complex_d_apply gR n rfl, prF_dTo, shift_d_apply]

/-- The projection to the summand `i` is a retraction of the inclusion of that summand. -/
theorem inj_pr_self (i : I) : inj gR n i ≫ pr gR n i = 𝟙 _ := by
  ext p : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact prF_injF_self gR n i p x

/-- The inclusion of the summand `i` followed by the projection to the summand `j ≠ i` is
zero. -/
theorem inj_pr_ne {i j : I} (h : j ≠ i) : inj gR n i ≫ pr gR n j = 0 := by
  ext p : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact prF_injF_ne gR n h p x

/-- The sum over `i` of the projections to the summands followed by the inclusions is the
identity of `⨁_i Ω^•_{A/R}[-n_i]`. -/
theorem sum_pr_inj [Fintype I] : ∑ i, pr gR n i ≫ inj gR n i = 𝟙 (complex gR n) := by
  ext p : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  change ((HomologicalComplex.eval _ _ p).map (∑ i, pr gR n i ≫ inj gR n i)).hom x = x
  rw [Functor.map_sum]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, HomologicalComplex.eval_map]
  exact sum_injF_prF gR n p x

/-! ### Cohomology -/

/-- The cohomology of `Ω^•_{A/R}[-n_i]` in degree `N` is the cohomology of `Ω^•_{A/R}` in degree
`N - n_i`. -/
def shiftHomologyIso (i : I) (N : ℤ) :
    ((intComplex gR)⟦-(n i : ℤ)⟧).homology N ≅ (intComplex gR).homology (N - n i) :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).shiftIso
      (-(n i : ℤ)) N (N - n i) (by omega)).app (intComplex gR)

/-- The cohomology of `Ω^•_{A/R}` in degree `N - n_i`, mapped to the cohomology of
`⨁_i Ω^•_{A/R}[-n_i]` in degree `N` by the inclusion of the `i`-th summand. -/
def homologyInj (i : I) (N : ℤ) :
    (intComplex gR).homology (N - n i) ⟶ (complex gR n).homology N :=
  (shiftHomologyIso gR n i N).inv ≫ HomologicalComplex.homologyMap (inj gR n i) N

/-- The cohomology of `⨁_i Ω^•_{A/R}[-n_i]` in degree `N`, mapped to the cohomology of
`Ω^•_{A/R}` in degree `N - n_i` by the projection to the `i`-th summand. -/
def homologyPr (i : I) (N : ℤ) :
    (complex gR n).homology N ⟶ (intComplex gR).homology (N - n i) :=
  HomologicalComplex.homologyMap (pr gR n i) N ≫ (shiftHomologyIso gR n i N).hom

/-- On cohomology, `homologyInj i N` followed by `homologyPr j N` is the map induced by
`inj i ≫ pr j`, up to the shift isomorphisms. -/
private theorem homologyInj_homologyPr_eq (i j : I) (N : ℤ) :
    homologyInj gR n i N ≫ homologyPr gR n j N = (shiftHomologyIso gR n i N).inv ≫
      HomologicalComplex.homologyMap (inj gR n i ≫ pr gR n j) N ≫
        (shiftHomologyIso gR n j N).hom := by
  rw [homologyInj, homologyPr, Category.assoc, ← Category.assoc
    (HomologicalComplex.homologyMap (inj gR n i) N), ← HomologicalComplex.homologyMap_comp]

/-- On cohomology, `homologyPr i N` is a retraction of `homologyInj i N`. -/
theorem homologyInj_homologyPr_self (i : I) (N : ℤ) :
    homologyInj gR n i N ≫ homologyPr gR n i N = 𝟙 _ := by
  rw [homologyInj_homologyPr_eq, inj_pr_self, HomologicalComplex.homologyMap_id,
    Category.id_comp, Iso.inv_hom_id]

/-- On cohomology, `homologyInj i N` followed by `homologyPr j N` is zero for `j ≠ i`. -/
theorem homologyInj_homologyPr_ne {i j : I} (h : j ≠ i) (N : ℤ) :
    homologyInj gR n i N ≫ homologyPr gR n j N = 0 := by
  rw [homologyInj_homologyPr_eq, inj_pr_ne gR n h, HomologicalComplex.homologyMap_zero]
  simp

/-- `homologyPr i N` followed by `homologyInj i N` is the map on cohomology induced by
`pr i ≫ inj i`. -/
theorem homologyPr_homologyInj (i : I) (N : ℤ) :
    homologyPr gR n i N ≫ homologyInj gR n i N =
      HomologicalComplex.homologyMap (pr gR n i ≫ inj gR n i) N := by
  rw [homologyInj, homologyPr, Category.assoc, Iso.hom_inv_id_assoc,
    HomologicalComplex.homologyMap_comp]

/-- **The inclusion of the `i`-th summand on cohomology classes**: the class of a cocycle `x` of
`Ω^•_{A/R}` in degree `N - n_i` goes to the class of `x` placed in the `i`-th summand. -/
theorem liftCycles_homologyπ_homologyInj (i : I) (N : ℤ) {P : ModuleCat.{u} R}
    (x : P ⟶ (intComplex gR).X (N - n i))
    (hx : x ≫ (intComplex gR).d (N - n i) (N - n i + 1) = 0)
    (y : P ⟶ (complex gR n).X N) (hy : y ≫ (complex gR n).d N (N + 1) = 0)
    (hxy : x ≫ (CochainComplex.shiftFunctorObjXIso (intComplex gR) (-(n i : ℤ)) N (N - n i)
      (by omega)).inv ≫ (inj gR n i).f N = y) :
    (intComplex gR).liftCycles x (N - n i + 1) (by simp) hx ≫
        (intComplex gR).homologyπ (N - n i) ≫ homologyInj gR n i N =
      (complex gR n).liftCycles y (N + 1) (by simp) hy ≫ (complex gR n).homologyπ N := by
  have hf : (x ≫ (CochainComplex.shiftFunctorObjXIso (intComplex gR) (-(n i : ℤ)) N (N - n i)
      (by omega)).inv) ≫ ((intComplex gR)⟦-(n i : ℤ)⟧).d N (N + 1) = 0 := by
    have h1 : (inj gR n i).f (N + 1) ≫ (pr gR n i).f (N + 1) = 𝟙 _ := by
      rw [← HomologicalComplex.comp_f, inj_pr_self, HomologicalComplex.id_f]
    rw [← Category.comp_id (_ ≫ ((intComplex gR)⟦-(n i : ℤ)⟧).d N (N + 1)), ← h1,
      Category.assoc, ← Category.assoc _ ((inj gR n i).f (N + 1)), ← (inj gR n i).comm,
      ← Category.assoc, ← Category.assoc, Category.assoc x, hxy, hy, zero_comp]
  have h := CochainComplex.liftCycles_shift_homologyπ (intComplex gR) _ (N + 1)
    (by simp) hf (N - n i) (by omega) (N - n i + 1) (by simp)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  have h' : _ = (intComplex gR).liftCycles x (N - n i + 1) (by simp) hx ≫
      (intComplex gR).homologyπ (N - n i) ≫ (shiftHomologyIso gR n i N).inv := h
  rw [homologyInj, show (intComplex gR).liftCycles x (N - n i + 1) (by simp) hx ≫
      (intComplex gR).homologyπ (N - n i) ≫ (shiftHomologyIso gR n i N).inv ≫
        HomologicalComplex.homologyMap (inj gR n i) N =
      ((intComplex gR).liftCycles x (N - n i + 1) (by simp) hx ≫
        (intComplex gR).homologyπ (N - n i) ≫ (shiftHomologyIso gR n i N).inv) ≫
        HomologicalComplex.homologyMap (inj gR n i) N by simp only [Category.assoc], ← h',
    Category.assoc, HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  congr 1
  simp only [Category.assoc, hxy]

variable [Fintype I]

/-- **The cohomology of a finite sum of shifted de Rham complexes**:
`⨁_i H^{N - n_i}(Ω^•_{A/R}) ≅ H^N(⨁_i Ω^•_{A/R}[-n_i])`, the sum of the maps induced by the
inclusions of the summands. -/
def homologyEquiv (N : ℤ) :
    (∀ i, (intComplex gR).homology (N - n i)) ≃ₗ[R] (complex gR n).homology N where
  toFun a := ∑ i, (homologyInj gR n i N).hom (a i)
  map_add' a a' := by
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
  invFun c i := (homologyPr gR n i N).hom c
  left_inv a := by
    funext j
    simp only [map_sum]
    rw [Finset.sum_eq_single j (fun i _ hij => by
        rw [← ConcreteCategory.comp_apply, homologyInj_homologyPr_ne gR n (Ne.symm hij)]
        rfl) (fun h => absurd (Finset.mem_univ j) h),
      ← ConcreteCategory.comp_apply, homologyInj_homologyPr_self]
    rfl
  right_inv c := by
    have key : ∑ i, homologyPr gR n i N ≫ homologyInj gR n i N = 𝟙 _ := by
      simp_rw [homologyPr_homologyInj]
      have h := (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) N).map_sum
        (fun i => pr gR n i ≫ inj gR n i) Finset.univ
      simp only [HomologicalComplex.homologyFunctor_map] at h
      refine h.symm.trans ?_
      rw [sum_pr_inj, HomologicalComplex.homologyMap_id]
    have h := congrArg (fun φ => φ.hom c) key
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
    exact h

/-- `homologyEquiv N` sends a family `(a_i)` to `∑_i homologyInj i N (a_i)`. -/
theorem homologyEquiv_apply (N : ℤ) (a : ∀ i, (intComplex gR).homology (N - n i)) :
    homologyEquiv gR n N a = ∑ i, (homologyInj gR n i N).hom (a i) :=
  rfl

end Stacks.KatzOda.ShiftedSum

end
