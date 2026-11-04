module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.KrullDimension.Zero
public import StacksFrontier.RingTheory.Smoothing.SpreadingOutResolutions

/-!
# Resolving a smoothing situation at a zero-dimensional prime

Let `R → A → Λ ⊃ q` be a local smoothing situation, so that `R` is Noetherian, `A` is of finite
presentation over `R` and `q` is a prime of `Λ`, and write `𝔥_A = √(H_{A/R} Λ)`. If `q` is minimal
over `𝔥_A`, the localized chain `R_p → A_p → Λ_q ⊃ q Λ_q` can be resolved, and the local ring
`Λ_q` has Krull dimension zero, then the chain `R → A → Λ ⊃ q` can be resolved already before
localizing.

Spreading out the localized resolution produces a factorization `A → C → Λ` with `C` of finite
presentation over `R` and an element `c` of the singular ideal of `C` whose image avoids `q`. The
dimension hypothesis makes the image in `Λ_q` of every generator `a_i` of `H_{A/R}` nilpotent, so
there are an integer `N` and an element `lam ∉ q` with `lam · (a_i)^N = 0` in `Λ`. Choosing a
presentation `C = A[x_1, …, x_n]/(f_1, …, f_m)` and a lift `g` of `c`, the resolving algebra is

`B = A[x_k, y_i, z, t_{i j}] / (f_j(x) - ∑_i y_i t_{i j}, z y_i)`,

mapping to `Λ` by `x_k ↦ x_k`, `y_i ↦ (a_i)^N`, `z ↦ lam` and `t_{i j} ↦ 0`. Inverting `a_i y_i`
kills `z`, so the first family of relations can be solved for the `t_{i j}` and `B_{a_i y_i}`
becomes a retract of a smooth algebra built from `A_{a_i}`; inverting `z g(x)` kills the `y_i`, so
`B_{z g(x)}` becomes a retract of a smooth algebra built from `C_c`. Hence `a_i y_i` and `z g(x)`
lie in the singular ideal of `B`, which gives `𝔥_A ⊆ 𝔥_B` and `𝔥_B ⊄ q`.

## Main results

* `Stacks.Smoothing.canBeResolved_of_localization_dim_zero`: a local smoothing situation whose
  localized chain can be resolved and whose localized target is zero-dimensional can be resolved.

## Implementation notes

The auxiliary algebra `B` is built from a presentation of `C` over `A` by `AuxAlgebra`, and the
two smoothness statements about its localizations are proved separately from the main argument;
each is a retract computation with its own smooth model.

## References

* [Stacks Project, Tag 07FA](https://stacks.math.columbia.edu/tag/07FA)
-/

@[expose] public section

namespace Stacks.Smoothing

open MvPolynomial

universe u v w

/-! ### Nilpotents at a zero-dimensional prime -/

/-- If the localization of `Λ` at a prime `q` is zero-dimensional, then for a finite family of
elements of `q` there are an exponent `N` and a single element outside `q` annihilating the `N`-th
power of every member of the family. -/
private theorem exists_notMem_forall_mul_pow_eq_zero {Λ : Type*} [CommRing Λ] (q : Ideal Λ)
    [q.IsPrime] (hdim : ringKrullDim (Localization.AtPrime q) = 0) {ι : Type*} [Finite ι]
    (x : ι → Λ) (hx : ∀ i, x i ∈ q) :
    ∃ (N : ℕ) (d : Λ), d ∉ q ∧ ∀ i, d * x i ^ N = 0 := by
  classical
  cases nonempty_fintype ι
  have hdimLE : Ring.KrullDimLE 0 (Localization.AtPrime q) :=
    Ring.krullDimLE_iff.mpr (by rw [hdim]; exact le_rfl)
  have hiff : ∀ y : Localization.AtPrime q, IsNilpotent y ↔ ¬ IsUnit y :=
    ((Ring.krullDimLE_zero_and_isLocalRing_tfae (Localization.AtPrime q)).out 1 3 rfl rfl).mp
      ⟨hdimLE, inferInstance⟩
  have hmem : ∀ i, algebraMap Λ (Localization.AtPrime q) (x i) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := fun i => by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)]
    exact Ideal.mem_map_of_mem _ (hx i)
  choose n hn using fun i =>
    (hiff _).mpr (by simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hmem i)
  have hpow : ∀ i, algebraMap Λ (Localization.AtPrime q) (x i ^ ∑ j, n j) = 0 := fun i => by
    rw [map_pow]
    exact pow_eq_zero_of_le
      (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (hn i)
  choose d hd using fun i =>
    (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) _).1 (hpow i)
  refine ⟨∑ j, n j, ((∏ j, d j : q.primeCompl) : Λ), (∏ j, d j : q.primeCompl).2, fun i => ?_⟩
  have hfactor : ((∏ j, d j : q.primeCompl) : Λ) =
      (d i : Λ) * ∏ j ∈ Finset.univ.erase i, (d j : Λ) := by
    simpa using (Finset.mul_prod_erase Finset.univ (fun j => (d j : Λ)) (Finset.mem_univ i)).symm
  rw [hfactor, mul_comm (d i : Λ), mul_assoc, hd i, mul_zero]

/-! ### The auxiliary algebra -/

/-- The variables of the auxiliary presentation: one variable `x k` for each generator `k` of a
presentation of `C` over `A`, one variable `y i` for each `i : ι`, one variable `z`, and one
variable `t i j` for each `i : ι` and each relation `j` of the presentation. -/
private abbrev AuxIndex (vars ι rels : Type*) := vars ⊕ ι ⊕ Unit ⊕ ι × rels

/-- The polynomial ring over `A` on the variables of the auxiliary presentation. -/
private abbrev AuxPoly (A : Type*) [CommRing A] (vars ι rels : Type*) :=
  MvPolynomial (AuxIndex vars ι rels) A

section Auxiliary

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] {vars rels : Type*}
  (ι : Type*) [Fintype ι] (P : Algebra.Presentation A C vars rels)

/-- The `A`-algebra map sending the `k`-th generator of the presentation `P` to the variable
`x k` of the auxiliary polynomial ring. -/
private noncomputable def auxLift : P.Ring →ₐ[A] AuxPoly A vars ι rels :=
  aeval fun k => X (Sum.inl k)

/-- Evaluating a polynomial of the presentation at the images of the generators under an
`A`-algebra map `φ : C → T` computes `φ` of its value in `C`. -/
private theorem aeval_eq_comp_aeval_val {T : Type*} [CommRing T] [Algebra A T] (φ : C →ₐ[A] T)
    (f : vars → T) (hf : ∀ k, f k = φ (P.val k)) (p : P.Ring) :
    aeval f p = φ (aeval P.val p) :=
  DFunLike.congr_fun
    (MvPolynomial.algHom_ext (f := (aeval f : P.Ring →ₐ[A] T)) (g := φ.comp (aeval P.val))
      fun k => by simp [hf k]) p

omit [Fintype ι] in
/-- Evaluating along `auxLift` only sees the variables `x k`. -/
private theorem aeval_auxLift {T : Type*} [CommRing T] [Algebra A T]
    (val : AuxIndex vars ι rels → T) (p : P.Ring) :
    aeval val (auxLift ι P p) = aeval (fun k => val (Sum.inl k)) p :=
  DFunLike.congr_fun
    (MvPolynomial.algHom_ext
      (f := (aeval val : AuxPoly A vars ι rels →ₐ[A] T).comp (auxLift ι P))
      (g := aeval fun k => val (Sum.inl k)) fun k => by simp [auxLift]) p

/-- The relations of the auxiliary presentation: `f_j(x) - ∑ i, y i * t i j` for each relation
`f_j` of `P`, and `z * y i` for each `i : ι`. -/
private noncomputable def auxRelation : rels ⊕ ι → AuxPoly A vars ι rels :=
  Sum.elim
    (fun j => auxLift ι P (P.relation j) -
      ∑ i, X (Sum.inr (Sum.inl i)) * X (Sum.inr (Sum.inr (Sum.inr (i, j)))))
    (fun i => X (Sum.inr (Sum.inr (Sum.inl ()))) * X (Sum.inr (Sum.inl i)))

/-- A value assignment satisfying the two displayed families of equations kills every auxiliary
relation. -/
private theorem aeval_auxRelation {T : Type*} [CommRing T] [Algebra A T]
    (val : AuxIndex vars ι rels → T)
    (h₁ : ∀ j, aeval (fun k => val (Sum.inl k)) (P.relation j) =
      ∑ i, val (Sum.inr (Sum.inl i)) * val (Sum.inr (Sum.inr (Sum.inr (i, j)))))
    (h₂ : ∀ i, val (Sum.inr (Sum.inr (Sum.inl ()))) * val (Sum.inr (Sum.inl i)) = 0)
    (k : rels ⊕ ι) : aeval val (auxRelation ι P k) = 0 := by
  cases k with
  | inl j =>
      simp only [auxRelation, Sum.elim_inl, map_sub, map_sum, map_mul, aeval_X,
        aeval_auxLift, h₁ j, sub_self]
  | inr i => simpa only [auxRelation, Sum.elim_inr, map_mul, aeval_X] using h₂ i

/-- The ideal generated by the auxiliary relations. -/
private noncomputable def auxIdeal : Ideal (AuxPoly A vars ι rels) :=
  Ideal.span (Set.range (auxRelation ι P))

/-- The auxiliary algebra `A[x, y, z, t]/(f_j(x) - ∑ y_i t_{i j}, z y_i)`. -/
private abbrev AuxAlgebra := AuxPoly A vars ι rels ⧸ auxIdeal ι P

/-- The auxiliary relations vanish in the auxiliary algebra. -/
private theorem mk_auxRelation (k : rels ⊕ ι) :
    Ideal.Quotient.mk (auxIdeal ι P) (auxRelation ι P k) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨k, rfl⟩)

/-- The ideal of auxiliary relations is finitely generated. -/
private theorem auxIdeal_fg [Finite rels] : (auxIdeal ι P).FG :=
  Submodule.fg_span (Set.finite_range _)

/-- A value assignment satisfying the auxiliary relations kills the ideal they generate. -/
private theorem auxIdeal_le_ker {T : Type*} [CommRing T] [Algebra A T]
    (val : AuxIndex vars ι rels → T) (h : ∀ k, aeval val (auxRelation ι P k) = 0) :
    auxIdeal ι P ≤ RingHom.ker ((aeval val : AuxPoly A vars ι rels →ₐ[A] T) : _ →+* T) := by
  rw [auxIdeal, Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  exact RingHom.mem_ker.mpr (h k)

/-- The `A`-algebra map out of the auxiliary algebra determined by a value assignment satisfying
the auxiliary relations. -/
private noncomputable def auxEval {T : Type*} [CommRing T] [Algebra A T]
    (val : AuxIndex vars ι rels → T) (h : ∀ k, aeval val (auxRelation ι P k) = 0) :
    AuxAlgebra ι P →ₐ[A] T :=
  Ideal.Quotient.liftₐ (auxIdeal ι P) (aeval val) fun _ hx =>
    RingHom.mem_ker.mp (auxIdeal_le_ker ι P val h hx)

/-- `auxEval` is computed on a polynomial by evaluating it at the chosen values. -/
private theorem auxEval_mk {T : Type*} [CommRing T] [Algebra A T]
    (val : AuxIndex vars ι rels → T) (h : ∀ k, aeval val (auxRelation ι P k) = 0)
    (p : AuxPoly A vars ι rels) :
    auxEval ι P val h (Ideal.Quotient.mk (auxIdeal ι P) p) = aeval val p :=
  DFunLike.congr_fun
    (Ideal.Quotient.liftₐ_comp (auxIdeal ι P) (aeval val)
      (fun _ hx => RingHom.mem_ker.mp (auxIdeal_le_ker ι P val h hx))) p

/-- The element `z · g(x)` of the auxiliary algebra, for a lift `g` of an element of the singular
ideal of `C`. -/
private noncomputable def auxZMulLift (g : P.Ring) : AuxAlgebra ι P :=
  Ideal.Quotient.mk (auxIdeal ι P)
    (X (Sum.inr (Sum.inr (Sum.inl ()))) * auxLift ι P g)

/-- The element `a i · y i` of the auxiliary algebra. -/
private noncomputable def auxSmulY (a : ι → A) (i : ι) : AuxAlgebra ι P :=
  algebraMap A (AuxAlgebra ι P) (a i) *
    Ideal.Quotient.mk (auxIdeal ι P) (X (Sum.inr (Sum.inl i)))

/-- The canonical `A`-algebra map from the auxiliary polynomial ring to a localization of the
auxiliary algebra. -/
private noncomputable def auxToLoc (x : AuxAlgebra ι P) :
    AuxPoly A vars ι rels →ₐ[A] Localization.Away x :=
  (IsScalarTower.toAlgHom A (AuxAlgebra ι P) (Localization.Away x)).comp
    (Ideal.Quotient.mkₐ A (auxIdeal ι P))

/-- The auxiliary relations vanish in any localization of the auxiliary algebra. -/
private theorem auxToLoc_auxRelation (x : AuxAlgebra ι P) (k : rels ⊕ ι) :
    auxToLoc ι P x (auxRelation ι P k) = 0 := by
  show (IsScalarTower.toAlgHom A (AuxAlgebra ι P) (Localization.Away x))
    (Ideal.Quotient.mk (auxIdeal ι P) (auxRelation ι P k)) = 0
  rw [mk_auxRelation, map_zero]

/-- If the localization of the auxiliary algebra at `x` is a retract of a smooth algebra `T`, via a
map `ρ` out of the auxiliary algebra inverting `x`, then it is smooth. -/
private theorem smooth_localization_away_of_retract {R : Type*} [CommRing R] [Algebra R A]
    (hfpB : Algebra.FinitePresentation R (AuxAlgebra ι P))
    {T : Type*} [CommRing T] [Algebra A T] [Algebra R T]
    [IsScalarTower R A T] (hT : Algebra.Smooth R T) (x : AuxAlgebra ι P)
    (ρ : AuxAlgebra ι P →ₐ[A] T) (tToL : T →ₐ[A] Localization.Away x) (hunit : IsUnit (ρ x))
    (hcomp : (tToL.comp ρ).comp (Ideal.Quotient.mkₐ A (auxIdeal ι P)) = auxToLoc ι P x) :
    Algebra.Smooth R (Localization.Away x) := by
  have hcompB : ∀ d : AuxAlgebra ι P,
      tToL (ρ d) = algebraMap (AuxAlgebra ι P) (Localization.Away x) d := fun d => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective d
    exact DFunLike.congr_fun hcomp p
  have hunitR : IsUnit ((ρ.restrictScalars R) x) := hunit
  let f : Localization.Away x →ₐ[R] T := IsLocalization.Away.liftAlgHom x hunitR
  have hRet : (tToL.restrictScalars R).comp f = AlgHom.id R (Localization.Away x) := by
    refine IsLocalization.algHom_ext (W := Submonoid.powers x) ?_
    ext d
    show tToL (IsLocalization.Away.lift x hunitR (algebraMap (AuxAlgebra ι P) _ d)) =
      algebraMap (AuxAlgebra ι P) _ d
    rw [IsLocalization.Away.lift_eq _ hunitR d]
    exact hcompB d
  have : Algebra.FormallySmooth R T := hT.formallySmooth
  have hfpL : Algebra.FinitePresentation (AuxAlgebra ι P) (Localization.Away x) :=
    IsLocalization.Away.finitePresentation x
  exact ⟨Algebra.FormallySmooth.of_retract f (tToL.restrictScalars R) hRet,
    Algebra.FinitePresentation.trans R (AuxAlgebra ι P) _⟩

section Smooth

variable {R : Type*} [CommRing R] [Algebra R A] [Algebra R C] [IsScalarTower R A C]

omit [Algebra R C] [IsScalarTower R A C] in
/-- The auxiliary algebra is of finite presentation over the base. -/
private theorem finitePresentation_auxAlgebra [Finite vars] [Finite rels]
    [Algebra.FinitePresentation R A] : Algebra.FinitePresentation R (AuxAlgebra ι P) :=
  have : Algebra.FinitePresentation R (AuxPoly A vars ι rels) := inferInstance
  Algebra.FinitePresentation.quotient (auxIdeal_fg ι P)

/-- Inverting `z · g(x)` makes the auxiliary algebra a retract of a smooth algebra, hence smooth.
Inverting `z` forces the `y i` to vanish, so the first family of relations becomes the relations
of `C`, and inverting `g(x)` inverts `c`; the resulting algebra is a retract of a localization of
a polynomial algebra over `C_c`, which is smooth because `c` lies in the singular ideal of `C`. -/
private theorem smooth_localization_away_auxZMulLift [Finite vars] [Finite rels]
    [Algebra.FinitePresentation R A] [Algebra.FinitePresentation R C] {c : C}
    (hc : c ∈ singularIdeal R C) (g : P.Ring) (hg : aeval P.val g = c) :
    Algebra.Smooth R (Localization.Away (auxZMulLift ι P g)) := by
  classical
  -- The smooth model `Tm = (C_c[t_{i j}, z])_z`.
  let Cc := Localization.Away c
  let Wm := (ι × rels) ⊕ Unit
  let Um := MvPolynomial Wm Cc
  let zU : Um := X (Sum.inr ())
  let Tm := Localization.Away zU
  have hCc : Algebra.Smooth R Cc := smooth_localization_away_of_mem_singularIdeal R C hc
  have : Algebra.Smooth Cc Um := ⟨inferInstance, inferInstance⟩
  have hUm : Algebra.Smooth R Um := Algebra.Smooth.comp R Cc Um
  have : Algebra.Smooth Um Tm := Algebra.Smooth.of_isLocalization_Away zU
  have hTm : Algebra.Smooth R Tm := Algebra.Smooth.comp R Um Tm
  -- The map from the auxiliary algebra to the model.
  let cToT : C →ₐ[A] Tm :=
    { toRingHom := algebraMap C Tm
      commutes' := fun x => (IsScalarTower.algebraMap_apply A C Tm x).symm }
  let val : AuxIndex vars ι rels → Tm := fun k => match k with
    | Sum.inl j => cToT (P.val j)
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (Sum.inl _)) => algebraMap Um Tm zU
    | Sum.inr (Sum.inr (Sum.inr ij)) => algebraMap Um Tm (X (Sum.inl ij))
  have hval : ∀ k, aeval val (auxRelation ι P k) = 0 := by
    refine aeval_auxRelation ι P val (fun j => ?_) (fun i => ?_)
    · rw [aeval_eq_comp_aeval_val P cToT (fun k => val (Sum.inl k)) (fun k => rfl),
        P.aeval_val_relation, map_zero]
      simp [val]
    · simp [val]
  let ρ : AuxAlgebra ι P →ₐ[A] Tm := auxEval ι P val hval
  have hρmk : ∀ p, ρ (Ideal.Quotient.mk (auxIdeal ι P) p) = aeval val p :=
    auxEval_mk ι P val hval
  have hρz : ρ (auxZMulLift ι P g) = algebraMap Um Tm zU * cToT c := by
    rw [auxZMulLift, hρmk, map_mul, aeval_X, aeval_auxLift,
      aeval_eq_comp_aeval_val P cToT (fun k => val (Sum.inl k)) (fun k => rfl), hg]
  have hunit : IsUnit (ρ (auxZMulLift ι P g)) := by
    rw [hρz]
    refine (IsLocalization.Away.algebraMap_isUnit zU).mul ?_
    have hcT : cToT c = algebraMap Cc Tm (algebraMap C Cc c) :=
      IsScalarTower.algebraMap_apply C Cc Tm c
    rw [hcT]
    exact (IsLocalization.Away.algebraMap_isUnit c).map (algebraMap Cc Tm)
  -- The localization of the auxiliary algebra, and what happens in it.
  let L := Localization.Away (auxZMulLift ι P g)
  let qL : AuxPoly A vars ι rels →ₐ[A] L := auxToLoc ι P (auxZMulLift ι P g)
  have hzgUnit : IsUnit (qL (X (Sum.inr (Sum.inr (Sum.inl ())))) * qL (auxLift ι P g)) := by
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (auxZMulLift ι P g)
  have hzUnit : IsUnit (qL (X (Sum.inr (Sum.inr (Sum.inl ()))))) :=
    (IsUnit.mul_iff.mp hzgUnit).1
  have hgUnit : IsUnit (qL (auxLift ι P g)) := (IsUnit.mul_iff.mp hzgUnit).2
  have hyzero : ∀ i, qL (X (Sum.inr (Sum.inl i))) = 0 := fun i => by
    refine hzUnit.mul_left_cancel ?_
    rw [mul_zero, ← map_mul]
    exact auxToLoc_auxRelation ι P _ (Sum.inr i)
  have hrelzero : ∀ j, qL (auxLift ι P (P.relation j)) = 0 := fun j => by
    have h := auxToLoc_auxRelation ι P (auxZMulLift ι P g) (Sum.inl j)
    rw [show auxRelation ι P (Sum.inl j) = auxLift ι P (P.relation j) -
      ∑ i, X (Sum.inr (Sum.inl i)) * X (Sum.inr (Sum.inr (Sum.inr (i, j)))) from rfl,
      map_sub, map_sum] at h
    rwa [Finset.sum_eq_zero (fun i _ => by rw [map_mul, hyzero i, zero_mul]), sub_zero] at h
  -- The induced map `C → L`.
  have hkerle : RingHom.ker (aeval P.val : P.Ring →ₐ[A] C).toRingHom ≤
      RingHom.ker (qL.comp (auxLift ι P)).toRingHom := by
    have hP : RingHom.ker (aeval P.val : P.Ring →ₐ[A] C).toRingHom = P.ker :=
      P.ker_eq_ker_aeval_val.symm
    rw [hP, ← P.span_range_relation_eq_ker, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact RingHom.mem_ker.mpr (hrelzero j)
  let cToL : C →ₐ[A] L :=
    AlgHom.liftOfSurjective (aeval P.val) (fun s => ⟨P.σ s, P.aeval_val_σ s⟩)
      (qL.comp (auxLift ι P)) hkerle
  have hcToL : ∀ p : P.Ring, cToL (aeval P.val p) = qL (auxLift ι P p) := fun p =>
    AlgHom.liftOfSurjective_apply _ _ _ _ p
  have hcUnit : IsUnit (cToL c) := by rwa [← hg, hcToL]
  -- The retraction `Tm → L`.
  let ccToL : Cc →ₐ[A] L := IsLocalization.Away.liftAlgHom c (f := cToL) hcUnit
  let valL : Wm → L := fun k => match k with
    | Sum.inl ij => qL (X (Sum.inr (Sum.inr (Sum.inr ij))))
    | Sum.inr _ => qL (X (Sum.inr (Sum.inr (Sum.inl ()))))
  let uToL : Um →ₐ[A] L := MvPolynomial.aevalTower ccToL valL
  have huz : uToL zU = qL (X (Sum.inr (Sum.inr (Sum.inl ())))) :=
    MvPolynomial.aevalTower_X ccToL valL (Sum.inr ())
  have huzUnit : IsUnit (uToL zU) := by rwa [huz]
  let tToL : Tm →ₐ[A] L := IsLocalization.Away.liftAlgHom zU (f := uToL) huzUnit
  have htU : ∀ y : Um, tToL (algebraMap Um Tm y) = uToL y := fun y => by
    show IsLocalization.Away.lift zU huzUnit (algebraMap Um Tm y) = uToL y
    rw [IsLocalization.Away.lift_eq]
    rfl
  have hCmap : ∀ x : C, tToL (cToT x) = cToL x := fun x => by
    show tToL (algebraMap C Tm x) = cToL x
    rw [IsScalarTower.algebraMap_apply C Cc Tm x, IsScalarTower.algebraMap_apply Cc Um Tm,
      htU, MvPolynomial.aevalTower_algebraMap]
    show IsLocalization.Away.lift c hcUnit (algebraMap C Cc x) = cToL x
    rw [IsLocalization.Away.lift_eq]
    rfl
  -- The retraction identity, checked on the variables.
  have hcomp : (tToL.comp ρ).comp (Ideal.Quotient.mkₐ A (auxIdeal ι P)) = qL := by
    refine MvPolynomial.algHom_ext fun k => ?_
    show tToL (ρ (Ideal.Quotient.mk (auxIdeal ι P) (X k))) = qL (X k)
    rw [hρmk, aeval_X]
    match k with
    | Sum.inl j =>
        show tToL (cToT (P.val j)) = qL (X (Sum.inl j))
        rw [hCmap]
        have h := hcToL (X j)
        rwa [aeval_X, show auxLift ι P (X j) = X (Sum.inl j) by simp [auxLift]] at h
    | Sum.inr (Sum.inl i) =>
        show tToL 0 = qL (X (Sum.inr (Sum.inl i)))
        rw [map_zero, hyzero i]
    | Sum.inr (Sum.inr (Sum.inl ())) =>
        show tToL (algebraMap Um Tm zU) = qL (X (Sum.inr (Sum.inr (Sum.inl ()))))
        rw [htU, huz]
    | Sum.inr (Sum.inr (Sum.inr ij)) =>
        show tToL (algebraMap Um Tm (X (Sum.inl ij))) =
          qL (X (Sum.inr (Sum.inr (Sum.inr ij))))
        rw [htU]
        exact MvPolynomial.aevalTower_X ccToL valL (Sum.inl ij)
  -- Conclusion: `L` is a retract of the smooth algebra `Tm`.
  exact smooth_localization_away_of_retract ι P (finitePresentation_auxAlgebra ι P) hTm _ ρ tToL
    hunit hcomp

omit [Algebra R C] [IsScalarTower R A C] in
/-- Inverting `a i · y i` makes the auxiliary algebra a retract of a smooth algebra, hence smooth.
Inverting `y i` forces `z` to vanish, and the `i`-th summand of the first family of relations can
then be solved for `t i j`; the resulting algebra is a retract of a localization of a polynomial
algebra over `A_{a i}`, which is smooth because `a i` lies in the singular ideal of `A`. -/
private theorem smooth_localization_away_auxSmulY [Finite vars] [Finite rels]
    [Algebra.FinitePresentation R A] (a : ι → A) (i : ι) (ha : a i ∈ singularIdeal R A) :
    Algebra.Smooth R (Localization.Away (auxSmulY ι P a i)) := by
  classical
  -- The smooth model `Ti = (A_{a i}[x, y, t_{k j} (k ≠ i)])_{y i}`.
  let Aa := Localization.Away (a i)
  let Wi := vars ⊕ ι ⊕ ({k : ι // k ≠ i} × rels)
  let Ui := MvPolynomial Wi Aa
  let yi : Ui := X (Sum.inr (Sum.inl i))
  let Ti := Localization.Away yi
  have hAa : Algebra.Smooth R Aa := smooth_localization_away_of_mem_singularIdeal R A ha
  have : Algebra.Smooth Aa Ui := ⟨inferInstance, inferInstance⟩
  have hUi : Algebra.Smooth R Ui := Algebra.Smooth.comp R Aa Ui
  have : Algebra.Smooth Ui Ti := Algebra.Smooth.of_isLocalization_Away yi
  have hTi : Algebra.Smooth R Ti := Algebra.Smooth.comp R Ui Ti
  -- Solving the relations in the model.
  have yiUnit : IsUnit (algebraMap Ui Ti yi) := IsLocalization.Away.algebraMap_isUnit yi
  let yiInv : Ti := ↑yiUnit.unit⁻¹
  let modelY : ι → Ti := fun k => algebraMap Ui Ti (X (Sum.inr (Sum.inl k)))
  let modelT : {k : ι // k ≠ i} → rels → Ti := fun k j =>
    algebraMap Ui Ti (X (Sum.inr (Sum.inr (k, j))))
  let modelTOther : ι → rels → Ti := fun k j => if hk : k ≠ i then modelT ⟨k, hk⟩ j else 0
  let sumOther : rels → Ti := fun j => ∑ k ∈ Finset.univ.erase i, modelY k * modelTOther k j
  let modelP : P.Ring →ₐ[A] Ti := aeval fun k => algebraMap Ui Ti (X (Sum.inl k))
  let solT : rels → Ti := fun j => yiInv * (modelP (P.relation j) - sumOther j)
  let tVal : ι → rels → Ti := fun k j => if hk : k = i then solT j else modelT ⟨k, hk⟩ j
  have hyInv : modelY i * yiInv = 1 := yiUnit.mul_val_inv
  have hsplit : ∀ j, (∑ k : ι, modelY k * tVal k j) = modelY i * solT j + sumOther j := fun j => by
    rw [← Finset.add_sum_erase Finset.univ (fun k : ι => modelY k * tVal k j) (Finset.mem_univ i)]
    congr 1
    · simp [tVal]
    · refine Finset.sum_congr rfl fun k hk => ?_
      simp [tVal, modelTOther, Finset.ne_of_mem_erase hk]
  have hsolve : ∀ j, modelY i * solT j + sumOther j = modelP (P.relation j) := fun j => by
    show modelY i * (yiInv * (modelP (P.relation j) - sumOther j)) + sumOther j = _
    rw [← mul_assoc, hyInv]
    ring
  let val : AuxIndex vars ι rels → Ti := fun k => match k with
    | Sum.inl j => algebraMap Ui Ti (X (Sum.inl j))
    | Sum.inr (Sum.inl k) => modelY k
    | Sum.inr (Sum.inr (Sum.inl _)) => 0
    | Sum.inr (Sum.inr (Sum.inr (k, j))) => tVal k j
  have hval : ∀ k, aeval val (auxRelation ι P k) = 0 := by
    refine aeval_auxRelation ι P val (fun j => ?_) (fun k => ?_)
    · exact (hsolve j).symm.trans (hsplit j).symm
    · exact zero_mul _
  let ρ : AuxAlgebra ι P →ₐ[A] Ti := auxEval ι P val hval
  have hρmk : ∀ p, ρ (Ideal.Quotient.mk (auxIdeal ι P) p) = aeval val p :=
    auxEval_mk ι P val hval
  have hunit : IsUnit (ρ (auxSmulY ι P a i)) := by
    rw [auxSmulY, map_mul, AlgHom.commutes, hρmk, aeval_X]
    refine IsUnit.mul ?_ yiUnit
    rw [IsScalarTower.algebraMap_apply A Aa Ti (a i)]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Aa) (a i)).map (algebraMap Aa Ti)
  -- The localization of the auxiliary algebra, and what happens in it.
  let L := Localization.Away (auxSmulY ι P a i)
  let qL : AuxPoly A vars ι rels →ₐ[A] L := auxToLoc ι P (auxSmulY ι P a i)
  have hprodUnit : IsUnit (algebraMap A L (a i) * qL (X (Sum.inr (Sum.inl i)))) := by
    show IsUnit (algebraMap A L (a i) *
      algebraMap (AuxAlgebra ι P) L (Ideal.Quotient.mk (auxIdeal ι P) (X (Sum.inr (Sum.inl i)))))
    rw [IsScalarTower.algebraMap_apply A (AuxAlgebra ι P) L (a i), ← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (auxSmulY ι P a i)
  have haUnit : IsUnit (algebraMap A L (a i)) := (IsUnit.mul_iff.mp hprodUnit).1
  have hyUnit : IsUnit (qL (X (Sum.inr (Sum.inl i)))) := (IsUnit.mul_iff.mp hprodUnit).2
  have hzzero : qL (X (Sum.inr (Sum.inr (Sum.inl ())))) = 0 := by
    refine hyUnit.mul_left_cancel ?_
    rw [mul_zero, mul_comm, ← map_mul]
    exact auxToLoc_auxRelation ι P _ (Sum.inr i)
  have hrel : ∀ j, qL (auxLift ι P (P.relation j)) =
      ∑ k : ι, qL (X (Sum.inr (Sum.inl k))) *
        qL (X (Sum.inr (Sum.inr (Sum.inr (k, j))))) := fun j => by
    have h := auxToLoc_auxRelation ι P (auxSmulY ι P a i) (Sum.inl j)
    rw [show auxRelation ι P (Sum.inl j) = auxLift ι P (P.relation j) -
      ∑ k, X (Sum.inr (Sum.inl k)) * X (Sum.inr (Sum.inr (Sum.inr (k, j)))) from rfl,
      map_sub, map_sum] at h
    simp only [map_mul] at h
    exact sub_eq_zero.mp h
  -- The retraction `Ti → L`.
  let aaToL : Aa →ₐ[A] L := IsLocalization.Away.liftAlgHom (a i) (f := Algebra.ofId A L) haUnit
  let valI : Wi → L := fun k => match k with
    | Sum.inl j => qL (X (Sum.inl j))
    | Sum.inr (Sum.inl k) => qL (X (Sum.inr (Sum.inl k)))
    | Sum.inr (Sum.inr (k, j)) => qL (X (Sum.inr (Sum.inr (Sum.inr (k.1, j)))))
  let uToL : Ui →ₐ[A] L := MvPolynomial.aevalTower aaToL valI
  have huy : uToL yi = qL (X (Sum.inr (Sum.inl i))) :=
    MvPolynomial.aevalTower_X aaToL valI (Sum.inr (Sum.inl i))
  have huyUnit : IsUnit (uToL yi) := by rwa [huy]
  let tToL : Ti →ₐ[A] L := IsLocalization.Away.liftAlgHom yi (f := uToL) huyUnit
  have htU : ∀ y : Ui, tToL (algebraMap Ui Ti y) = uToL y := fun y => by
    show IsLocalization.Away.lift yi huyUnit (algebraMap Ui Ti y) = uToL y
    rw [IsLocalization.Away.lift_eq]
    rfl
  have hmodelP : ∀ p : P.Ring, tToL (modelP p) = qL (auxLift ι P p) := fun p =>
    DFunLike.congr_fun
      (MvPolynomial.algHom_ext (f := (tToL.comp modelP : P.Ring →ₐ[A] L))
        (g := qL.comp (auxLift ι P)) fun k => by
          show tToL (modelP (X k)) = qL (auxLift ι P (X k))
          rw [show modelP (X k) = algebraMap Ui Ti (X (Sum.inl k)) by simp [modelP], htU,
            show auxLift ι P (X k) = X (Sum.inl k) by simp [auxLift]]
          exact MvPolynomial.aevalTower_X aaToL valI (Sum.inl k)) p
  have hmodelY : ∀ k, tToL (modelY k) = qL (X (Sum.inr (Sum.inl k))) := fun k => by
    show tToL (algebraMap Ui Ti (X (Sum.inr (Sum.inl k)))) = _
    rw [htU]
    exact MvPolynomial.aevalTower_X aaToL valI (Sum.inr (Sum.inl k))
  have hmodelT : ∀ (k : {k : ι // k ≠ i}) (j : rels), tToL (modelT k j) =
      qL (X (Sum.inr (Sum.inr (Sum.inr (k.1, j))))) := fun k j => by
    show tToL (algebraMap Ui Ti (X (Sum.inr (Sum.inr (k, j))))) = _
    rw [htU]
    exact MvPolynomial.aevalTower_X aaToL valI (Sum.inr (Sum.inr (k, j)))
  have hsumOther : ∀ j, tToL (sumOther j) = ∑ k ∈ Finset.univ.erase i,
      qL (X (Sum.inr (Sum.inl k))) * qL (X (Sum.inr (Sum.inr (Sum.inr (k, j))))) := fun j => by
    show tToL (∑ k ∈ Finset.univ.erase i, modelY k * modelTOther k j) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hki := Finset.ne_of_mem_erase hk
    rw [show modelY k * modelTOther k j = modelY k * modelT ⟨k, hki⟩ j by
      simp [modelTOther, hki], map_mul, hmodelY, hmodelT]
  have hsolT : ∀ j, tToL (solT j) = qL (X (Sum.inr (Sum.inr (Sum.inr (i, j))))) := fun j => by
    refine hyUnit.mul_left_cancel ?_
    have hinv : qL (X (Sum.inr (Sum.inl i))) * tToL yiInv = 1 := by
      rw [← hmodelY i, ← map_mul, hyInv, map_one]
    have hsum : (∑ k : ι, qL (X (Sum.inr (Sum.inl k))) *
        qL (X (Sum.inr (Sum.inr (Sum.inr (k, j)))))) =
        qL (X (Sum.inr (Sum.inl i))) * qL (X (Sum.inr (Sum.inr (Sum.inr (i, j))))) +
          ∑ k ∈ Finset.univ.erase i, qL (X (Sum.inr (Sum.inl k))) *
            qL (X (Sum.inr (Sum.inr (Sum.inr (k, j))))) :=
      (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).symm
    show qL (X (Sum.inr (Sum.inl i))) * tToL (yiInv * (modelP (P.relation j) - sumOther j)) = _
    rw [map_mul, ← mul_assoc, hinv, one_mul, map_sub, hmodelP, hsumOther, hrel j, hsum]
    ring
  -- The retraction identity, checked on the variables.
  have hcomp : (tToL.comp ρ).comp (Ideal.Quotient.mkₐ A (auxIdeal ι P)) = qL := by
    refine MvPolynomial.algHom_ext fun k => ?_
    show tToL (ρ (Ideal.Quotient.mk (auxIdeal ι P) (X k))) = qL (X k)
    rw [hρmk, aeval_X]
    match k with
    | Sum.inl j =>
        show tToL (algebraMap Ui Ti (X (Sum.inl j))) = qL (X (Sum.inl j))
        rw [htU]
        exact MvPolynomial.aevalTower_X aaToL valI (Sum.inl j)
    | Sum.inr (Sum.inl k) =>
        show tToL (modelY k) = qL (X (Sum.inr (Sum.inl k)))
        exact hmodelY k
    | Sum.inr (Sum.inr (Sum.inl ())) =>
        show tToL 0 = qL (X (Sum.inr (Sum.inr (Sum.inl ()))))
        rw [map_zero, hzzero]
    | Sum.inr (Sum.inr (Sum.inr (k, j))) =>
        show tToL (tVal k j) = qL (X (Sum.inr (Sum.inr (Sum.inr (k, j)))))
        by_cases hki : k = i
        · subst hki
          rw [show tVal k j = solT j by simp [tVal]]
          exact hsolT j
        · rw [show tVal k j = modelT ⟨k, hki⟩ j by simp [tVal, hki]]
          exact hmodelT ⟨k, hki⟩ j
  -- Conclusion: `L` is a retract of the smooth algebra `Ti`.
  exact smooth_localization_away_of_retract ι P (finitePresentation_auxAlgebra ι P) hTi _ ρ tToL
    hunit hcomp

end Smooth

end Auxiliary

/-! ### Resolving in dimension zero -/

/-- **Stacks 07FA.** Let `R → A → Λ ⊃ q` be a local smoothing situation with `q` minimal over
`𝔥_A = √(H_{A/R} Λ)`. If the localized chain `R_p → A_p → Λ_q ⊃ q Λ_q` can be resolved and `Λ_q`
has Krull dimension zero, then `R → A → Λ ⊃ q` can be resolved. -/
@[stacks 07FA]
theorem canBeResolved_of_localization_dim_zero (S : LocalSmoothingSituation.{u, v, w})
    (hq : S.q ∈ S.radicalSingularIdealExtension.minimalPrimes)
    (hresolve : S.IsResolvableAfterLocalizing)
    (hdim : ringKrullDim (Localization.AtPrime S.q) = 0) : S.CanBeResolved := by
  classical
  have : IsNoetherianRing S.A := Algebra.FiniteType.isNoetherianRing S.R S.A
  obtain ⟨N₀, a₀, hspan₀⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.FG.of_isNoetherianRing (singularIdeal S.R S.A))
  -- Index the generators of `H_{A/R}` by a type in `Type (max u w)`, so that the auxiliary
  -- algebra built below lands in `Type (max u v w)`.
  let ι : Type (max u w) := ULift.{max u w} (Fin N₀)
  let a : ι → S.A := fun i => a₀ i.down
  have hrange : Set.range a = Set.range a₀ := ULift.down_surjective.range_comp a₀
  have hspan : Ideal.span (Set.range a) = singularIdeal S.R S.A := by rwa [hrange]
  have haH : ∀ i, a i ∈ singularIdeal S.R S.A := fun i => by
    rw [← hspan]
    exact Ideal.subset_span ⟨i, rfl⟩
  have haq : ∀ i, algebraMap S.A S.Λ (a i) ∈ S.q := fun i =>
    hq.1.2 (Ideal.le_radical (Ideal.mem_map_of_mem _ (haH i)))
  obtain ⟨N, lam, hlam, hlamann⟩ :=
    exists_notMem_forall_mul_pow_eq_zero S.q hdim (fun i => algebraMap S.A S.Λ (a i)) haq
  -- Spread out the resolution of the localized chain.
  obtain ⟨C, hcommC, hRC, hAC, hCΛ, hRAC, hACΛ, hRCΛ, hCfp, hCnot⟩ :=
    exists_finitePresentation_factorization_singularIdeal_not_le S hq hresolve
  let : CommRing C := hcommC
  let : Algebra S.R C := hRC
  let : Algebra S.A C := hAC
  let : Algebra C S.Λ := hCΛ
  let : IsScalarTower S.R S.A C := hRAC
  let : IsScalarTower S.A C S.Λ := hACΛ
  let : IsScalarTower S.R C S.Λ := hRCΛ
  have : Algebra.FinitePresentation S.R C := hCfp
  have : Algebra.FiniteType S.A C := Algebra.FiniteType.of_restrictScalars_finiteType S.R S.A C
  have : Algebra.FinitePresentation S.A C :=
    (Algebra.FinitePresentation.of_finiteType (R := S.A) (A := C)).mp inferInstance
  obtain ⟨n, m, ⟨P⟩⟩ := Algebra.Presentation.exists_presentation_fin S.A C
  obtain ⟨c, hc, hcq⟩ : ∃ c, c ∈ singularIdeal S.R C ∧ algebraMap C S.Λ c ∉ S.q := by
    by_contra hn
    exact hCnot (Ideal.map_le_iff_le_comap.mpr fun x hx => not_not.mp fun hxq => hn ⟨x, hx, hxq⟩)
  -- The resolving algebra.
  let cToΛ : C →ₐ[S.A] S.Λ :=
    { toRingHom := algebraMap C S.Λ
      commutes' := fun x => (IsScalarTower.algebraMap_apply S.A C S.Λ x).symm }
  let val : AuxIndex (Fin n) ι (Fin m) → S.Λ := fun k => match k with
    | Sum.inl j => cToΛ (P.val j)
    | Sum.inr (Sum.inl i) => algebraMap S.A S.Λ (a i) ^ N
    | Sum.inr (Sum.inr (Sum.inl _)) => lam
    | Sum.inr (Sum.inr (Sum.inr _)) => 0
  have hval : ∀ k, aeval val (auxRelation ι P k) = 0 := by
    refine aeval_auxRelation ι P val (fun j => ?_) (fun i => ?_)
    · rw [aeval_eq_comp_aeval_val P cToΛ (fun k => val (Sum.inl k)) (fun k => rfl),
        P.aeval_val_relation, map_zero]
      simp [val]
    · exact hlamann i
  let B := AuxAlgebra ι P
  let φ : B →ₐ[S.A] S.Λ := auxEval ι P val hval
  let : Algebra B S.Λ := φ.toRingHom.toAlgebra
  have : IsScalarTower S.A B S.Λ := IsScalarTower.of_algHom φ
  have : IsScalarTower S.R B S.Λ := IsScalarTower.of_algHom (φ.restrictScalars S.R)
  have hφmk : ∀ p, algebraMap B S.Λ (Ideal.Quotient.mk (auxIdeal ι P) p) = aeval val p :=
    auxEval_mk ι P val hval
  have hfpB : Algebra.FinitePresentation S.R B := finitePresentation_auxAlgebra ι P
  refine ⟨B, inferInstance, (inferInstance : Algebra S.R B), (inferInstance : Algebra S.A B),
    (inferInstance : Algebra B S.Λ), inferInstance, inferInstance, inferInstance, hfpB, ?_, ?_⟩
  · -- `𝔥_A ⊆ 𝔥_B`, because `(a i)^(N+1)` is the image of an element of `H_{B/R}`.
    have hSing : ∀ i, auxSmulY ι P a i ∈ singularIdeal S.R B := fun i =>
      mem_singularIdeal_of_smooth_of_isLocalizationAway S.R B (Localization.Away (auxSmulY ι P a i))
        (smooth_localization_away_auxSmulY ι P a i (haH i))
    have hmapY : ∀ i, algebraMap B S.Λ (auxSmulY ι P a i) =
        algebraMap S.A S.Λ (a i) ^ (N + 1) := fun i => by
      rw [auxSmulY, map_mul, ← IsScalarTower.algebraMap_apply S.A B S.Λ (a i), hφmk, aeval_X]
      show algebraMap S.A S.Λ (a i) * algebraMap S.A S.Λ (a i) ^ N = _
      ring
    have hgen : ∀ i, algebraMap S.A S.Λ (a i) ∈
        (Ideal.map (algebraMap B S.Λ) (singularIdeal S.R B)).radical := fun i => by
      rw [Ideal.mem_radical_iff]
      exact ⟨N + 1, (hmapY i) ▸ Ideal.mem_map_of_mem (algebraMap B S.Λ) (hSing i)⟩
    refine Ideal.radical_le_radical_iff.mpr ?_
    rw [← hspan, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hgen i
  · -- `𝔥_B ⊄ q`, because the image of `z g(x)` avoids `q`.
    have hzSing : auxZMulLift ι P (P.σ c) ∈ singularIdeal S.R B :=
      mem_singularIdeal_of_smooth_of_isLocalizationAway S.R B
        (Localization.Away (auxZMulLift ι P (P.σ c)))
        (smooth_localization_away_auxZMulLift ι P hc (P.σ c) (P.aeval_val_σ c))
    have hmapZ : algebraMap B S.Λ (auxZMulLift ι P (P.σ c)) = lam * algebraMap C S.Λ c := by
      rw [auxZMulLift, hφmk, map_mul, aeval_X, aeval_auxLift,
        aeval_eq_comp_aeval_val P cToΛ (fun k => val (Sum.inl k)) (fun k => rfl),
        P.aeval_val_σ]
      rfl
    intro hle
    exact S.isPrimeQ.mul_notMem hlam hcq
      (hmapZ ▸ hle (Ideal.le_radical (Ideal.mem_map_of_mem (algebraMap B S.Λ) hzSing)))

end Stacks.Smoothing

end
