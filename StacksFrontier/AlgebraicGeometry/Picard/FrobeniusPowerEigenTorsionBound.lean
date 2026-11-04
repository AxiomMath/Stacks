module

public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusEigenTorsionBound
public import Mathlib.FieldTheory.Finite.Extension
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.GaloisTwistStageBaseChange

/-!
# The eigenvectors of a power of the Frobenius in `Pic(Y_k̄)[ℓⁿ]` are bounded

Let `Y` be a smooth proper geometrically irreducible curve over a finite field `k` with `q`
elements, `K` an algebraic closure of `k`, `F` the Frobenius of `K/k` and `m ≥ 1`. The `F^m`-fixed
torsion classes of `Pic(Y_K)` form a finite set: such a class is fixed by `Gal(K/E)` for every
finite intermediate field `E` of degree divisible by `m`
(`Stacks.Picard.galoisTwist_fixed_of_frobenius_pow_fixed`), and over a stage `E` over which `Y`
has a rational point these classes come from the finite torsion of `Pic(Y_E)` (Tag 0CDT), as in
`Stacks.Picard.finite_setOf_frobenius_fixed_isOfFinAddOrder`. A pairing `e` with
`e(σa, σb) = q e(a, b)` gives `e(σᵐa, σᵐb) = qᵐ e(a, b)`, so the `qᵐ`-eigenvectors of `σᵐ` on
`Pic(Y_K)[ℓⁿ]` are bounded independently of `n`.

This is the form in which the Frobenius eigenvectors of the Picard group of the compactification
of an open curve are bounded: a power `F^m` fixes the finitely many points at infinity.

## Main results

* `Stacks.Picard.galoisTwist_fixed_of_frobenius_pow_fixed`
* `Stacks.Picard.finite_setOf_frobenius_pow_fixed_isOfFinAddOrder`
* `Stacks.Picard.exists_forall_encard_torsion_eigen_frobenius_pow_le`
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

section Fixed

variable {k K : Type u} [Field k] [Fintype k] [Field K] [Algebra k K] [IsGalois k K]

/-- **A class fixed by `F^m` is fixed by `Gal(K/E)`** for every finite intermediate field `E`
whose degree is divisible by `m`. The class descends to a finite stage `E₁`, so it is fixed by
`Gal(K/E₁)`. An element `τ` of `Gal(K/E)` agrees with a power `F^j` on the finite field
`E₁ ⊔ E`, and `F^j` fixes `E`, so `[E : k] ∣ j` and `m ∣ j`. -/
theorem galoisTwist_fixed_of_frobenius_pow_fixed (X : Over (Spec (.of k)))
    [CompactSpace X.left] [QuasiSeparatedSpace X.left] (m : ℕ)
    (x : ofScheme (SchemeOver.baseChange k K X))
    (hx : schemePullbackClass
      (galoisTwist k K X (FiniteField.frobeniusAlgEquivOfAlgebraic k K ^ m)) x = x)
    (E : IntermediateField k K) [FiniteDimensional k E] (hm : m ∣ Module.finrank k E)
    (τ : K ≃ₐ[k] K) (hτ : τ ∈ E.fixingSubgroup) :
    schemePullbackClass (galoisTwist k K X τ) x = x := by
  let := galoisPicardAction k K X
  show τ • x = x
  obtain ⟨E₁, hE₁, p, y, hp₁, hp₂, hpy⟩ := exists_finiteSubextension_schemePullbackClass_eq X x
  have hle := fixingSubgroup_le_stabilizer_galoisPicardAction X E₁ p hp₁ hp₂ y
  rw [hpy] at hle
  set E₂ := E₁ ⊔ E
  have : FiniteDimensional k E₂ := IntermediateField.finiteDimensional_sup E₁ E
  have : Finite E₂ := Module.finite_of_finite k
  have : Finite E := Module.finite_of_finite k
  set F := FiniteField.frobeniusAlgEquivOfAlgebraic k K
  have hFx : F ^ m ∈ MulAction.stabilizer (K ≃ₐ[k] K) x := hx
  obtain ⟨j, hj⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k E₂).2
    (τ.restrictNormal E₂)
  -- `ρ = F^{-j} τ` is trivial on `E₂`
  have hρ : F ^ (-(j.1 : ℤ)) * τ ∈ E₂.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_zpow]
    show (F.restrictNormal E₂) ^ (-(j.1 : ℤ)) * τ.restrictNormal E₂ = 1
    rw [restrictNormal_frobeniusAlgEquivOfAlgebraic, ← hj, zpow_neg, zpow_natCast,
      inv_mul_cancel]
  -- hence `F^j` fixes `E`, so `m ∣ j`
  have hFj : F ^ (j.1 : ℤ) ∈ E.fixingSubgroup := by
    rw [show F ^ (j.1 : ℤ) = τ * (F ^ (-(j.1 : ℤ)) * τ)⁻¹ by group]
    exact mul_mem hτ (inv_mem (IntermediateField.fixingSubgroup_antitone le_sup_right hρ))
  have hdvd : m ∣ j.1 := by
    refine hm.trans ?_
    rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k E]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_zpow,
      zpow_natCast] at hFj
    change (F.restrictNormal E) ^ j.1 = 1 at hFj
    rwa [restrictNormal_frobeniusAlgEquivOfAlgebraic] at hFj
  obtain ⟨i, hi⟩ := hdvd
  have h1 : F ^ (j.1 : ℤ) ∈ MulAction.stabilizer (K ≃ₐ[k] K) x := by
    rw [zpow_natCast, hi, pow_mul]
    exact pow_mem hFx i
  rw [show τ = F ^ (j.1 : ℤ) * (F ^ (-(j.1 : ℤ)) * τ) by group]
  exact mul_mem h1 (hle (IntermediateField.fixingSubgroup_antitone le_sup_left hρ))

end Fixed

/-- The iterates of the restriction of `f` to the `r`-torsion are the restrictions of the
iterates of `f`. -/
private theorem coe_torsionByRestrict_iterate {A : Type*} [AddCommGroup A] (f : A →+ A) (r : ℤ)
    (i : ℕ) (a : Submodule.torsionBy ℤ A r) :
    (((torsionByRestrict f r)^[i] a : Submodule.torsionBy ℤ A r) : A) = f^[i] (a : A) := by
  induction i generalizing a with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

/-- If `e(σa, σb) = c e(a, b)` then `e(σⁱa, σⁱb) = cⁱ e(a, b)`. -/
private theorem pairing_iterate_eq_pow_smul {A N : Type*} [AddCommGroup A] [AddCommGroup N]
    (e : A →+ A →+ N) (σ : A → A)
    (c : ℤ) (he : ∀ a b, e (σ a) (σ b) = c • e a b) (i : ℕ) (a b : A) :
    e (σ^[i] a) (σ^[i] b) = (c ^ i) • e a b := by
  induction i generalizing a b with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, he, smul_smul, pow_succ,
      mul_comm]

/-- The fixed points of `σ` on the `ℓⁿ`-torsion are at most as many as the elements of any set
`S` containing the torsion fixed points of `σ`. -/
private theorem natCard_ker_torsionByRestrict_sub_id_le {A : Type*} [AddCommGroup A] (σ : A →+ A)
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) (n : ℕ) (S : Set A) [Finite S]
    (hS : ∀ z, σ z = z → IsOfFinAddOrder z → z ∈ S) :
    Nat.card (torsionByRestrict σ ((ℓ : ℤ) ^ n) - AddMonoidHom.id _).ker ≤ Nat.card S := by
  refine Nat.card_le_card_of_injective (fun a => ⟨a.1.1, hS _ ?_ ?_⟩) ?_
  · exact congrArg Subtype.val (sub_eq_zero.1 (AddMonoidHom.mem_ker.1 a.2))
  · refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨ℓ ^ n, pow_pos (Nat.pos_of_ne_zero hℓ) n, ?_⟩
    have h : ((ℓ : ℤ) ^ n) • (a.1.1 : A) = 0 := (Submodule.mem_torsionBy_iff _ _).1 a.1.2
    generalize (a.1.1 : A) = x at h ⊢
    rwa [← Nat.cast_pow, natCast_zsmul] at h
  · intro a b h
    exact Subtype.ext (Subtype.ext (congrArg Subtype.val h :))

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  [IsProper Y.hom] [Smooth Y.hom] [GeometricallyIrreducible Y.hom] [IsCurve k Y.hom]

omit [Fintype k] [IsProper Y.hom] [GeometricallyIrreducible Y.hom] in
/-- For `m ≠ 0` there is a finite intermediate field `E` of `k̄/k` of degree divisible by `m` over
which `Y` has a rational point. -/
private theorem exists_intermediateField_dvd_finrank_section [Finite k] (m : ℕ) [NeZero m] :
    ∃ (E : IntermediateField k (AlgebraicClosure k)) (_ : FiniteDimensional k E),
      m ∣ Module.finrank k E ∧
        ∃ pt : Spec (.of E) ⟶ (stageOver Y E).left, pt ≫ (stageOver Y E).hom = 𝟙 _ := by
  classical
  have := Fintype.ofFinite k
  set K := AlgebraicClosure k
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  -- a degree `m` subfield of `K`
  obtain ⟨p, hp⟩ := CharP.exists k
  have := hp
  have : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let ψ : FiniteField.Extension k p m →ₐ[k] K := IsAlgClosed.lift
  set E' : IntermediateField k K := ψ.fieldRange
  have hE' : Module.finrank k E' = m :=
    (LinearEquiv.finrank_eq ψ.equivFieldRange.toLinearEquiv).symm.trans
      (FiniteField.finrank_extension k p m)
  have : FiniteDimensional k E' := LinearEquiv.finiteDimensional ψ.equivFieldRange.toLinearEquiv
  -- a closed point and the finite stage containing `E'` it is rational over
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := Y.left)).exists_closed_singleton Set.univ_nonempty
  let : Algebra k (Y.left.residueField x) := (fieldToResidue Y.hom x).hom.toAlgebra
  have : Module.Finite k (Y.left.residueField x) :=
    Module.finite_of_finrank_pos (Stacks.EtaleCohomology.residueDegree_pos Y.hom x hx)
  let φ : Y.left.residueField x →ₐ[k] K := IsAlgClosed.lift
  have : FiniteDimensional k φ.fieldRange :=
    LinearEquiv.finiteDimensional φ.equivFieldRange.toLinearEquiv
  set E : IntermediateField k K := φ.fieldRange ⊔ E'
  refine ⟨E, IntermediateField.finiteDimensional_sup _ _,
    hE' ▸ IntermediateField.finrank_dvd_of_le_right le_sup_right, ?_⟩
  let φE : Y.left.residueField x →ₐ[k] E :=
    φ.codRestrict E.toSubalgebra fun a => (le_sup_left : φ.fieldRange ≤ E) ⟨a, rfl⟩
  let σE : Y.left.residueField x ⟶ CommRingCat.of E := CommRingCat.ofHom φE.toRingHom
  have hσE : fieldToResidue Y.hom x ≫ σE = CommRingCat.ofHom (algebraMap k E) := by
    ext c
    exact congrArg Subtype.val (φE.commutes c)
  let pt : Spec (.of E) ⟶ (stageOver Y E).left :=
    pullback.lift (Spec.map σE ≫ Y.left.fromSpecResidueField x) (𝟙 _)
      (by rw [Category.id_comp, (Stacks.EtaleCohomology.fromSpecResidueField_comp_eq_iff
        Y.hom E x σE).2 hσE])
  exact ⟨pt, pullback.lift_snd _ _ _⟩

omit [Smooth Y.hom] [GeometricallyIrreducible Y.hom] [IsCurve k Y.hom] in
/-- An `F^m`-fixed class of `Pic(Y_{k̄})`, carried to `Pic((Y_E)_{k̄})`, is fixed by `Gal(k̄/E)`
whenever `m ∣ [E : k]`. -/
private theorem schemePullbackClass_stageBaseChangeIso_inv_mem_galoisFixedClasses (m : ℕ)
    (z : ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y))
    (hz : schemePullbackClass (galoisTwist k (AlgebraicClosure k) Y
      (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m)) z = z)
    (E : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k E]
    (hmE : m ∣ Module.finrank k E) :
    schemePullbackClass (stageBaseChangeIso Y E).inv z ∈
      galoisFixedClasses E (AlgebraicClosure k) (stageOver Y E) := by
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  intro τ
  have hcomm : galoisTwist E (AlgebraicClosure k) (stageOver Y E) τ ≫
      (stageBaseChangeIso Y E).inv =
        (stageBaseChangeIso Y E).inv ≫ galoisTwist k (AlgebraicClosure k) Y
          (τ.restrictScalars k) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← galoisTwist_comp_stageBaseChangeIso_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [schemePullbackClass_comp, hcomm, ← schemePullbackClass_comp,
    galoisTwist_fixed_of_frobenius_pow_fixed Y m z hz E hmE _
      (restrictScalars_mem_fixingSubgroup E τ)]

/-- **The `F^m`-fixed torsion classes of `Pic(Y_{k̄})` form a finite set**, for a smooth proper
geometrically irreducible curve `Y` over a finite field `k` and `m ≥ 1`. -/
theorem finite_setOf_frobenius_pow_fixed_isOfFinAddOrder (m : ℕ) [NeZero m] :
    {z | schemePullbackClass (galoisTwist k (AlgebraicClosure k) Y
      (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m)) z = z ∧
        IsOfFinAddOrder z}.Finite := by
  classical
  set K := AlgebraicClosure k
  have : IsGalois k K := inferInstance
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : GeometricallyReduced Y.hom := geometricallyReduced_of_smooth Y.hom
  have : GeometricallyIntegral Y.hom :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible Y.hom
  obtain ⟨E, _, hmE, pt, hpt⟩ := exists_intermediateField_dvd_finrank_section Y m
  have : Finite E := Module.finite_of_finite k
  have : IsGalois E K := IsGalois.tower_top_of_isGalois k E K
  have : CompactSpace (stageOver Y E).left := compactSpace_stage Y E
  have : QuasiSeparatedSpace (stageOver Y E).left := quasiSeparatedSpace_stage Y E
  have hbij := bijOn_schemePullbackClass_galoisFixedClasses E K (stageOver Y E)
    (isIso_appTop_stage Y (isIso_globalSections_of_geometricallyIntegral k Y.hom) E) pt hpt
  -- the stage is a smooth proper curve over the finite field `E`
  set pE : (stageOver Y E).left ⟶ Spec (.of E) := (stageOver Y E).hom
  have : IsProper pE := inferInstanceAs (IsProper (pullback.snd Y.hom (spectrumMap k E)))
  have : Smooth pE := inferInstanceAs (Smooth (pullback.snd Y.hom (spectrumMap k E)))
  have : GeometricallyIntegral pE :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd Y.hom (spectrumMap k E)))
  have : IsIntegral (stageOver Y E).left := GeometricallyIntegral.isIntegral_of_subsingleton pE
  have : IsCurve E pE :=
    { topologicalKrullDim_eq_one :=
        (topologicalKrullDim_baseChange k E (pullback.fst Y.hom (spectrumMap k E)) pE Y.hom
          (IsPullback.of_hasPullback Y.hom (spectrumMap k E))).trans
          (IsCurve.topologicalKrullDim_eq_one Y.hom) }
  -- the comparison `Y_K ≅ (Y_E)_K`
  set e := stageBaseChangeIso Y E
  refine ((finite_setOf_isOfFinAddOrder pE).image fun w => schemePullbackClass e.hom
    (schemePullbackClass (pullback.fst (stageOver Y E).hom (spectrumMap E K)) w)).subset ?_
  rintro z ⟨hzσ, hz⟩
  set u := schemePullbackClass e.inv z
  have hu : u ∈ galoisFixedClasses E K (stageOver Y E) :=
    schemePullbackClass_stageBaseChangeIso_inv_mem_galoisFixedClasses Y m z hzσ E hmE
  obtain ⟨w, -, hw⟩ := hbij.surjOn hu
  let pr := pullback.fst (stageOver Y E).hom (spectrumMap E K)
  have hinj : Function.Injective (schemePullbackClassHom pr) :=
    fun a b h => hbij.injOn (Set.mem_univ a) (Set.mem_univ b) h
  refine ⟨w, ?_, ?_⟩
  · obtain ⟨n, hn, hnz⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hz
    have h2 : n • u = 0 := by
      have := map_nsmul (schemePullbackClassHom e.inv) n z
      rw [hnz, map_zero] at this
      exact this.symm
    have key : schemePullbackClassHom pr (n • w) = schemePullbackClassHom pr 0 := by
      rw [map_nsmul, map_zero]
      exact (congrArg (n • ·) hw).trans h2
    show IsOfFinAddOrder w
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, hinj key⟩
  · show schemePullbackClass e.hom (schemePullbackClass pr w) = z
    rw [hw, schemePullbackClass_comp, Iso.hom_inv_id, schemePullbackClass_id]

omit [IsProper Y.hom] [Smooth Y.hom] [GeometricallyIrreducible Y.hom] [IsCurve k Y.hom] in
/-- **The twist by `F^m` is the `m`-th iterate of the Frobenius on `Pic(Y_{k̄})`.** -/
theorem schemePullbackClass_galoisTwist_frobenius_pow (m : ℕ)
    (z : ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) :
    schemePullbackClass (galoisTwist k (AlgebraicClosure k) Y
      (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m)) z =
        (frobeniusPicardHom Y)^[m] z := by
  induction m generalizing z with
  | zero =>
    rw [pow_zero, galoisTwist_one, schemePullbackClass_id]
    rfl
  | succ m ih =>
    rw [pow_succ, galoisTwist_mul, ← schemePullbackClass_comp, ih, Function.iterate_succ_apply]
    rfl

/-- **The `qᵐ`-eigenvectors of `σᵐ` in `Pic(Y_{k̄})[ℓⁿ]` are bounded independently of `n`**, for
`σ` the Frobenius and `q = #k`, from the Weil pairing and the finiteness of `Pic(Y_k̄)[ℓⁿ]`:
`e(σᵐa, σᵐb) = qᵐ e(a, b)`, so the kernel of `σᵐ - qᵐ` is at most the kernel of `σᵐ - 1`, which
lies in the finite set of `F^m`-fixed torsion classes. -/
theorem exists_forall_encard_torsion_eigen_frobenius_pow_le (ℓ : ℕ) (hℓ : ℓ ≠ 0)
    (hfin : ∀ n : ℕ, Finite (Submodule.torsionBy ℤ
      (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n)))
    (hunit : ∀ n : ℕ, IsUnit ((Fintype.card k : ℤ) : ZMod (ℓ ^ n)))
    (hWeil : ∀ n : ℕ, ∃ e : Submodule.torsionBy ℤ
        (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n) →+
        Submodule.torsionBy ℤ
          (ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)) ((ℓ : ℤ) ^ n) →+
          ZMod (ℓ ^ n),
      (∀ a, (∀ b, e a b = 0) → a = 0) ∧
        ∀ a b, e (torsionByRestrict (frobeniusPicardHom Y) _ a)
          (torsionByRestrict (frobeniusPicardHom Y) _ b) = (Fintype.card k : ℤ) • e a b)
    (m : ℕ) [NeZero m] :
    ∃ C : ℕ, ∀ n : ℕ, {w : ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y) |
      ((ℓ : ℤ) ^ n) • w = 0 ∧ schemePullbackClass (galoisTwist k (AlgebraicClosure k) Y
        (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m)) w =
          ((Fintype.card k : ℤ) ^ m) • w}.encard ≤ C := by
  classical
  let P := ofScheme (SchemeOver.baseChange k (AlgebraicClosure k) Y)
  let σm : P →+ P := schemePullbackClassHom (galoisTwist k (AlgebraicClosure k) Y
    (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ^ m))
  let S := {z : P | σm z = z ∧ IsOfFinAddOrder z}
  have : Finite S := (finite_setOf_frobenius_pow_fixed_isOfFinAddOrder Y m).to_subtype
  refine ⟨Nat.card S, fun n => ?_⟩
  have := hfin n
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hℓ⟩
  let M := Submodule.torsionBy ℤ P ((ℓ : ℤ) ^ n)
  obtain ⟨e, he₀, he⟩ := hWeil n
  let σ := torsionByRestrict (frobeniusPicardHom Y) ((ℓ : ℤ) ^ n)
  let σM := torsionByRestrict σm ((ℓ : ℤ) ^ n)
  have hσM : ∀ a, σM a = σ^[m] a := fun a => Subtype.ext
    ((schemePullbackClass_galoisTwist_frobenius_pow Y m a).trans
      (coe_torsionByRestrict_iterate (frobeniusPicardHom Y) _ m a).symm)
  have he' : ∀ a b, e (σM a) (σM b) = ((Fintype.card k : ℤ) ^ m) • e a b := fun a b => by
    rw [hσM, hσM, pairing_iterate_eq_pow_smul e σ _ he]
  have hunit' : IsUnit (((Fintype.card k : ℤ) ^ m : ℤ) : ZMod (ℓ ^ n)) := by
    rw [Int.cast_pow]
    exact (hunit n).pow m
  have hker := natCard_ker_sub_smul_le e he₀ σM _ hunit' he'
  let Kq := (σM - ((Fintype.card k : ℤ) ^ m) • AddMonoidHom.id M).ker
  have hsub : {w : P | ((ℓ : ℤ) ^ n) • w = 0 ∧ σm w = ((Fintype.card k : ℤ) ^ m) • w} ⊆
      Set.range fun z : Kq => ((z : M) : P) := by
    rintro w ⟨hw, hσw⟩
    refine ⟨⟨⟨w, (Submodule.mem_torsionBy_iff _ _).2 hw⟩, ?_⟩, rfl⟩
    rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, sub_eq_zero]
    apply Subtype.ext
    simp only [σM, torsionByRestrict_apply, AddMonoidHom.smul_apply]
    exact hσw
  calc _ ≤ (Set.range fun z : Kq => ((z : M) : P)).encard := Set.encard_le_encard hsub
    _ ≤ (Set.univ : Set Kq).encard := by
        rw [← Set.image_univ]
        exact Set.encard_image_le _ _
    _ = Nat.card Kq := by rw [Set.encard_univ, ENat.card_eq_coe_natCard]
    _ ≤ _ := by
        exact_mod_cast hker.trans
          (natCard_ker_torsionByRestrict_sub_id_le σm hℓ n S fun _ h₁ h₂ => ⟨h₁, h₂⟩)

end Stacks.Picard
