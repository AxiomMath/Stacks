module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilTraceInputProof
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedFrobeniusCurveWeil
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusFieldExtension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldValuedPointCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DimensionZeroTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FrobeniusBaseChangeDegree

/-!
# Weil's formula for the powers of the Frobenius of a curve, and their fixed points

Let `k` be a finite field with `q = p ^ f` elements, `Y` a scheme over `k` and `k̄` an algebraic
closure of `k`, and let `π̄ = π_Y × id` be the base change of the geometric Frobenius of `Y` to
`Y_k̄`. For `m ≥ 1`:

* `(id × Spec(σ^m)) ∘ π̄^m` is the `fm`-fold absolute Frobenius of `Y_k̄`, `σ` the arithmetic
  Frobenius of `k̄`
  (`Stacks.EtaleCohomology.galoisBaseChange_comp_geometricFrobeniusBaseChangePow`);
* when `Y_k̄` is a smooth proper curve, Weil's formula in `Pic[ℓⁿ]` form
  (`Stacks.EtaleCohomology.weilTraceInput`) applies to the twisted Frobenius `π̄^m`, of degree
  `q^m`: `#Fix(π̄^m) = 1 - Tr((π̄^m)^* | Pic(Y_k̄)[ℓⁿ]) + q^m` in `ℤ/ℓⁿ`
  (`Stacks.EtaleCohomology.natCast_natCard_fixedSections_geometricFrobeniusBaseChangePow`);
* the `k̄`-points of `Y_k̄` fixed by `π̄^m` are the points of `Y` with values in the subfield
  `k_m ⊆ k̄` with `q^m` elements
  (`Stacks.EtaleCohomology.natCard_fixedSections_geometricFrobeniusBaseChangePow`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- A morphism `φ` of a curve with `Ψ ≫ φ = F^e` for an automorphism `Ψ` is not constant. -/
theorem not_constant_of_iso_comp_eq_absoluteFrobeniusPow {Ω : Type u} [Field Ω] {C : Scheme.{u}}
    (g : C ⟶ Spec (.of Ω)) [IsCurve Ω g] (p : ℕ) [Fact p.Prime] (hC : IsInCharacteristic C p)
    (e : ℕ) (φ : C ⟶ C) (Ψ : C ≅ C) (hΨ : Ψ.hom ≫ φ = absoluteFrobeniusPow C p hC e) :
    ¬ ∃ y : C, ∀ x : C, φ.base x = y := by
  rintro ⟨y, hy⟩
  have hall : ∀ x : C, x = y := fun x => by
    have h := absoluteFrobeniusPow_base_apply C p hC e x
    rw [← hΨ, Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← h]
    exact hy _
  have : Subsingleton (C : Type u) := ⟨fun a b => (hall a).trans (hall b).symm⟩
  have : DiscreteTopology (C : Type u) := Subsingleton.discreteTopology
  have hle := topologicalKrullDim_zero_of_discreteTopology (C : Type u)
  rw [IsCurve.topologicalKrullDim_eq_one g] at hle
  norm_num at hle

section Pow

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **`(id × Spec(τ)) ∘ π̄^m` is the `qm`-fold absolute Frobenius of `Y_k̄`** for an automorphism
`τ` of `k̄` raising to the power `p^{qm}`. -/
theorem galoisBaseChange_comp_geometricFrobeniusBaseChangePow (m : ℕ) (τ : kbar ≃ₐ[k] kbar)
    (hτ : ∀ x : kbar, τ x = x ^ p ^ (q * m)) :
    galoisBaseChange Y kbar τ ≫ geometricFrobeniusBaseChangePow Y kbar p q hcard m =
      absoluteFrobeniusPow (fieldBaseChange Y kbar) p
        (isInCharacteristic_fieldBaseChange Y kbar p) (q * m) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, geometricFrobeniusBaseChangePow_fst, galoisBaseChange_comp_fst_assoc,
      absoluteFrobeniusPow_naturality _ p _ (isInCharacteristic_of_over Y)]
  · rw [Category.assoc, geometricFrobeniusBaseChangePow_snd, galoisBaseChange_comp_snd,
      absoluteFrobeniusPow_naturality _ p _ (isInCharacteristic_specAlgebraMap k kbar p),
      specMap_eq_absoluteFrobeniusPow τ.toAlgHom.toRingHom p (q * m)
        (isInCharacteristic_specAlgebraMap k kbar p) (fun a ↦ hτ a)]

omit [Fact p.Prime] [CharP k p] in
/-- The `m`-th power of the arithmetic Frobenius raises to the power `p^{qm}`. -/
theorem arithmeticFrobenius_pow_apply [ExpChar kbar p] [PerfectRing kbar p] (m : ℕ) (x : kbar) :
    (arithmeticFrobenius k kbar p q hcard ^ m) x = x ^ p ^ (q * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, arithmeticFrobenius_apply, hcard, ← pow_mul,
        ← pow_add, Nat.mul_succ, add_comm]

variable [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar]
  [IsCurve kbar (pullback.snd Y.hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd Y.hom (specAlgebraMap k kbar))]
  [IsProper (pullback.snd Y.hom (specAlgebraMap k kbar))]

/-- **Weil's formula for `π̄^m`.** For `Y_k̄` a smooth proper curve, `m ≥ 1`, a prime `ℓ ≠ p` and
`n ≥ 1`: `#Fix(π̄^m) = 1 - Tr((π̄^m)^* | Pic(Y_k̄)[ℓⁿ]) + q^m` in `ℤ/ℓⁿ`. -/
theorem natCast_natCard_fixedSections_geometricFrobeniusBaseChangePow (m : ℕ) (hm : m ≠ 0)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : kbar) ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ((Nat.card (fixedSections (pullback.snd Y.hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChangePow Y kbar p q hcard m)) : ℤ) : ZMod (ℓ ^ n)) =
      1 - picardTorsionTrace (fieldBaseChange Y kbar)
          (Stacks.Picard.schemePullbackClassHom
            (geometricFrobeniusBaseChangePow Y kbar p q hcard m)) ℓ n +
        ((Fintype.card k ^ m : ℕ) : ZMod (ℓ ^ n)) := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have hC := isInCharacteristic_fieldBaseChange Y kbar p
  let Ψ := galoisBaseChangeIso Y kbar (arithmeticFrobenius k kbar p q hcard ^ m)
  have hΨ : Ψ.hom ≫ geometricFrobeniusBaseChangePow Y kbar p q hcard m =
      absoluteFrobeniusPow (fieldBaseChange Y kbar) p hC (q * m) :=
    galoisBaseChange_comp_geometricFrobeniusBaseChangePow Y kbar p q hcard m _
      (arithmeticFrobenius_pow_apply kbar p q hcard m)
  have hq : 0 < q * m := Nat.mul_pos (Nat.pos_of_ne_zero (ne_zero_of_card_eq_pow hcard))
    (Nat.pos_of_ne_zero hm)
  have w := geometricFrobeniusBaseChangePow_snd Y kbar p q hcard m
  have hnc := not_constant_of_iso_comp_eq_absoluteFrobeniusPow
    (pullback.snd Y.hom (specAlgebraMap k kbar)) p hC (q * m) _ Ψ hΨ
  have h := weilTraceInput kbar p (isAlgebraic_zmod_of_finite k kbar p) (fieldBaseChange Y kbar)
    (pullback.snd Y.hom (specAlgebraMap k kbar))
    (geometricFrobeniusBaseChangePow Y kbar p q hcard m) w hnc (q * m) hq hC Ψ hΨ ℓ n hℓ hn
  have hdeg := degreeOver_eq_pow_of_comp_eq_absoluteFrobeniusPow (k := kbar) p
    (pullback.snd Y.hom (specAlgebraMap k kbar)) hC
    (geometricFrobeniusBaseChangePow Y kbar p q hcard m) w hnc (q * m) hq Ψ hΨ
  rw [hdeg] at h
  rw [h, hcard, ← pow_mul]

end Pow

/-! ### The fixed points of `π̄^m` -/

section Fixed

variable {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k))) (kbar : Type u) [Field kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The `k̄`-point of `Y_k̄` over a `K`-valued point of `Y`, `K ⊆ k̄`. -/
def fieldValuedPointLift (K : IntermediateField k kbar) (b : fieldValuedPoints Y.hom K) :
    Spec (.of kbar) ⟶ fieldBaseChange Y kbar :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫ b.1) (𝟙 _) (by
    rw [Category.assoc, b.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq, Category.id_comp])

omit [Fintype k] in
/-- The composite of `fieldValuedPointLift` with the first projection is `b` composed with
`Spec k̄ ⟶ Spec K`. -/
@[reassoc (attr := simp)]
lemma fieldValuedPointLift_fst (K : IntermediateField k kbar) (b : fieldValuedPoints Y.hom K) :
    fieldValuedPointLift Y kbar K b ≫ pullback.fst Y.hom (specAlgebraMap k kbar) =
      Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫ b.1 :=
  pullback.lift_fst _ _ _

omit [Fintype k] in
/-- The lift `fieldValuedPointLift` is a section of the second projection. -/
@[reassoc (attr := simp)]
lemma fieldValuedPointLift_snd (K : IntermediateField k kbar) (b : fieldValuedPoints Y.hom K) :
    fieldValuedPointLift Y kbar K b ≫ pullback.snd Y.hom (specAlgebraMap k kbar) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- **The `k̄`-points of `Y_k̄` fixed by `π̄^m` are the points of `Y` with values in the subfield
`K ⊆ k̄` with `p^{qm}` elements.** -/
theorem natCard_fixedSections_geometricFrobeniusBaseChangePow (m : ℕ) (K : IntermediateField k kbar)
    [Fintype K] (hK : Fintype.card K = p ^ (q * m)) :
    Nat.card (fixedSections (pullback.snd Y.hom (specAlgebraMap k kbar))
        (geometricFrobeniusBaseChangePow Y kbar p q hcard m)) =
      Nat.card (fieldValuedPoints Y.hom K) := by
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have hk : IsInCharacteristic (Spec (.of kbar)) p := isInCharacteristic_specAlgebraMap k kbar p
  have hKc : IsInCharacteristic (Spec (.of K)) p := isInCharacteristic_specAlgebraMap k K p
  have hY : IsInCharacteristic Y.left p := isInCharacteristic_of_over Y
  have hepi : Epi (Spec.map (CommRingCat.ofHom (algebraMap K kbar))) :=
    Flat.epi_of_flat_of_surjective _
  have hFK : absoluteFrobeniusPow (Spec (.of K)) p hKc (q * m) = 𝟙 _ := by
    rw [← specMap_eq_absoluteFrobeniusPow (RingHom.id K) p (q * m) hKc (fun a => by
      rw [RingHom.id_apply, ← hK, FiniteField.pow_card])]
    exact Spec.map_id _
  let Φ : fieldValuedPoints Y.hom K → fixedSections (pullback.snd Y.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChangePow Y kbar p q hcard m) := fun b =>
    ⟨fieldValuedPointLift Y kbar K b, fieldValuedPointLift_snd Y kbar K b, by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, geometricFrobeniusBaseChangePow_fst, fieldValuedPointLift_fst_assoc,
          ← absoluteFrobeniusPow_naturality b.1 p hKc hY, hFK, Category.id_comp,
          fieldValuedPointLift_fst]
      · rw [Category.assoc, geometricFrobeniusBaseChangePow_snd]⟩
  refine (Nat.card_eq_of_bijective Φ ⟨fun b b' hbb => ?_, fun s => ?_⟩).symm
  · have h := congrArg (fun s => s.1 ≫ pullback.fst Y.hom (specAlgebraMap k kbar)) hbb
    simp only [Φ, fieldValuedPointLift_fst] at h
    exact Subtype.ext ((cancel_epi _).1 h)
  · set a := s.1 ≫ pullback.fst Y.hom (specAlgebraMap k kbar) with ha_def
    have hfix : Spec.map (CommRingCat.ofHom (iterateFrobenius kbar p (q * m))) ≫ a = a := by
      rw [specMap_eq_absoluteFrobeniusPow (iterateFrobenius kbar p (q * m)) p (q * m) hk
          (fun z => by rw [iterateFrobenius_def]),
        absoluteFrobeniusPow_naturality a p hk hY, ha_def, Category.assoc,
        ← geometricFrobeniusBaseChangePow_fst Y kbar p q hcard m, ← Category.assoc, s.2.2]
    have hstr : a ≫ Y.hom = specAlgebraMap k kbar := by
      rw [ha_def, Category.assoc, pullback.condition, ← Category.assoc, s.2.1, Category.id_comp]
    obtain ⟨⟨y, ι⟩, hya⟩ := (Scheme.SpecToEquivOfField kbar Y.left).symm.surjective a
    simp only [Scheme.SpecToEquivOfField_symm_apply] at hya
    have hισ : ι ≫ CommRingCat.ofHom (iterateFrobenius kbar p (q * m)) = ι := by
      have h1 : (Scheme.SpecToEquivOfField kbar Y.left).symm
          ⟨y, ι ≫ CommRingCat.ofHom (iterateFrobenius kbar p (q * m))⟩ =
          (Scheme.SpecToEquivOfField kbar Y.left).symm ⟨y, ι⟩ := by
        simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc]
        rwa [hya]
      exact eq_of_heq (Sigma.mk.inj_iff.1
        ((Scheme.SpecToEquivOfField kbar Y.left).symm.injective h1)).2
    have hmem : ∀ t, ι.hom t ∈ K := fun t => by
      have ht : (ι.hom t) ^ Fintype.card K = ι.hom t := by
        have h2 := congrArg (fun φ => φ.hom t) hισ
        simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
          iterateFrobenius_def] at h2
        rwa [hK]
      obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_pow_card_eq kbar _ ht
      rw [← hc]
      exact c.2
    let ι' : Y.left.residueField y ⟶ CommRingCat.of K :=
      CommRingCat.ofHom (ι.hom.codRestrict K hmem)
    have hιι' : ι' ≫ CommRingCat.ofHom (algebraMap K kbar) = ι := by
      ext t
      rfl
    let b₀ : Spec (.of K) ⟶ Y.left := Spec.map ι' ≫ Y.left.fromSpecResidueField y
    have hb₀ : Spec.map (CommRingCat.ofHom (algebraMap K kbar)) ≫ b₀ = a := by
      rw [← hya, ← Category.assoc, ← Spec.map_comp, hιι']
    have hb₀str : b₀ ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      refine (cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap K kbar)))).1 ?_
      rw [← Category.assoc, hb₀, hstr, specAlgebraMap_comp_specAlgebraMap K kbar]
    let b : fieldValuedPoints Y.hom K := ⟨b₀, hb₀str⟩
    refine ⟨b, Subtype.ext (pullback.hom_ext ?_ ?_)⟩
    · exact (fieldValuedPointLift_fst Y kbar K b).trans hb₀
    · exact (fieldValuedPointLift_snd Y kbar K b).trans s.2.1.symm

end Fixed

end Stacks.EtaleCohomology

end
