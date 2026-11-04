module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsFiltrationWeights

/-!
# Weights of a graded upper-triangular representation from its diagonal blocks

A variant of `isCharpolyNormMixedOfWeightLE_restrictScalarsRep_of_isGradedUpper` in which the
property of the pieces is a property `Pb` of the diagonal blocks themselves (as families of
matrices), not only of their Frobenius characteristic polynomials: if the weight bound holds on
`Hⁱ_c(X_k̄, ℱ_{Res_b Y'} ⊗ ℚ_ℓ)` for every `Y'` with `Pb`, it holds for every graded
upper-triangular `Y` each of whose diagonal blocks has `Pb`. With `Pb` "absolutely irreducible and
pure", this is the reduction of Laumon's theorem to absolutely irreducible representations
(Kedlaya, *Fourier transforms and p-adic Weil II*, §6).

## Main results

* `isCharpolyNormMixedOfWeightLE_restrictScalarsRep_of_isGradedUpper_blocks`: the weight bound for
  a graded upper-triangular representation whose diagonal blocks all satisfy `Pb`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)


/-- **Weights of `Res_b Y` by dévissage along the grading, block by block.**  Let `Pb` be a
property of families of square matrices over `E` which holds for the families of `0 × 0`
matrices. Suppose the bound `q, ι, w` holds on `Hⁱ_c(X_k̄, ℱ_{Res_b Y'} ⊗ ℚ_ℓ)` for every `Y'`
whose matrices have `Pb`, and that all the cohomology groups in sight are finite (rationally, and
at every finite level). Then it holds for every graded upper-triangular `Y` each of whose diagonal
blocks (in any enumeration of its coordinates) has `Pb`. -/
public theorem isCharpolyNormMixedOfWeightLE_restrictScalarsRep_of_isGradedUpper_blocks
    {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) (i : ℤ)
    {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {w : ℤ}
    (Pb : (a : ℕ) → (EtaleFundamentalGroup X.1 x → Matrix (Fin a) (Fin a) E) → Prop)
    (hPb : ∀ Z : EtaleFundamentalGroup X.1 x → Matrix (Fin 0) (Fin 0) E, Pb 0 Z)
    (hFD : ∀ {N : ℕ} (τ : EtaleFundamentalGroup X.1 x →* GL (Fin N) ℚ_[ℓ]) (hτ : Continuous τ),
      FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
        kbar (LAdicSheaf.representationSheaf B X x τ hτ) i))
    (hfin : ∀ {N : ℕ} (τ : EtaleFundamentalGroup X.1 x →* GL (Fin N) ℚ_[ℓ]) (hτ : Continuous τ)
      (m : ℕ), Finite ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
        (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.representationSheaf B X x τ hτ) m)))
    (hbase : ∀ {m : ℕ} (Y' : EtaleFundamentalGroup X.1 x →* GL (Fin m) E)
      (hY' : Continuous (restrictScalarsRep b Y'))
      [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
        kbar (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b Y') hY') i)],
      Pb m (fun g => (Y' g).val) →
      IsCharpolyNormMixedOfWeightLE q ι w
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b Y') hY') i).hom) :
    ∀ (m : ℕ) (Y : EtaleFundamentalGroup X.1 x →* GL (Fin m) E) (δ : Fin m → ℤ)
      (hup : ∀ g, IsGradedUpper δ (Y g).val) (hY : Continuous (restrictScalarsRep b Y))
      (_ : ∀ (t : ℤ) (a : ℕ) (e : Fin a → Fin m), Function.Injective e →
        (∀ i, δ i = t ↔ ∃ j, e j = i) → Pb a fun g => (Y g).val.submatrix e e),
      ∃ _ : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
        f j kbar (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b Y) hY) i),
      IsCharpolyNormMixedOfWeightLE q ι w
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
          (LAdicSheaf.representationSheaf B X x (restrictScalarsRep b Y) hY) i).hom := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro Y δ hup hY hblk
  have := hFD (restrictScalarsRep b Y) hY
  refine ⟨inferInstance, ?_⟩
  by_cases hconst : ∀ i₁ i₂, δ i₁ = δ i₂
  · refine hbase Y hY ?_
    rcases isEmpty_or_nonempty (Fin m) with hm | ⟨⟨i₀⟩⟩
    · obtain rfl : m = 0 := by
        by_contra h
        exact hm.false ⟨0, Nat.pos_of_ne_zero h⟩
      exact hPb _
    · simpa only [Matrix.submatrix_id_id] using hblk (δ i₀) m id Function.injective_id
        (fun i => ⟨fun _ => ⟨i, rfl⟩, fun _ => hconst i i₀⟩)
  · simp only [not_forall] at hconst
    obtain ⟨i₁, i₂, h₁₂⟩ := hconst
    have hne : (Finset.univ.image δ).Nonempty :=
      ⟨δ i₁, Finset.mem_image_of_mem δ (Finset.mem_univ _)⟩
    set t₀ := (Finset.univ.image δ).min' hne
    have ht₀ : ∀ i, t₀ ≤ δ i := fun i =>
      Finset.min'_le _ _ (Finset.mem_image_of_mem δ (Finset.mem_univ i))
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, δ i₀ = t₀ := by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (Finset.min'_mem _ hne)
      exact ⟨i, hi⟩
    obtain ⟨a, e₁, he₁, hre₁⟩ := exists_injective_forall_iff_exists fun i => δ i = t₀
    obtain ⟨c, e₂, he₂, hre₂⟩ := exists_injective_forall_iff_exists fun i => δ i ≠ t₀
    have hdisj : ∀ j j', e₁ j ≠ e₂ j' := fun j j' h =>
      (hre₂ (e₂ j')).2 ⟨j', rfl⟩ (h ▸ (hre₁ (e₁ j)).2 ⟨j, rfl⟩)
    have hcov : ∀ i, (∃ j, e₁ j = i) ∨ ∃ j, e₂ j = i := fun i =>
      (em (δ i = t₀)).imp (hre₁ i).1 (hre₂ i).1
    have hc : c < m := by
      have := Fintype.card_lt_of_injective_of_notMem e₂ he₂ (b := i₀)
        (fun ⟨j, hj⟩ => (hre₂ i₀).2 ⟨j, hj⟩ hi₀)
      simpa using this
    have hsE := isSplitting_coordMatrix (R := E) he₁ he₂ hdisj hcov
    have hKYJ : ∀ g, (coordMatrix (R := E) e₂)ᵀ * (Y g).val * coordMatrix (R := E) e₁ = 0 :=
      fun g => by
      refine (transpose_coordMatrix_mul_mul_coordMatrix (R := E) (Y g).val).trans ?_
      ext j' j''
      simp only [Matrix.submatrix_apply, Matrix.zero_apply]
      apply hup g
      have h1 : δ (e₁ j'') = t₀ := (hre₁ _).2 ⟨j'', rfl⟩
      have h2 : δ (e₂ j') ≠ t₀ := (hre₂ _).2 ⟨j', rfl⟩
      rw [h1]
      exact lt_of_le_of_ne (ht₀ _) (Ne.symm h2)
    have hst := fun g => hsE.stable_of_comp_eq_zero (hKYJ g)
    set α := hsE.subRep Y (fun g => (hst g).1)
    set γ := hsE.quotRep Y (fun g => (hst g).2)
    have hαv : ∀ g, (α g).val = (Y g).val.submatrix e₁ e₁ := fun g => by
      exact (IsSplitting.subRep_val _ _ _ _).trans
        (transpose_coordMatrix_mul_mul_coordMatrix (R := E) (Y g).val)
    have hγv : ∀ g, (γ g).val = (Y g).val.submatrix e₂ e₂ := fun g => by
      refine (IsSplitting.quotRep_val _ _ _ _).trans ?_
      have := transpose_coordMatrix_mul_mul_coordMatrix (R := E) (e₁ := e₂) (e₂ := e₂) (Y g).val
      exact this
    have hYc : Continuous fun g => (restrictScalarsRep b Y g).val := Units.continuous_val.comp hY
    have hcont : ∀ {a : ℕ} (e : Fin a → Fin m) (Z : EtaleFundamentalGroup X.1 x →* GL (Fin a) E),
        (∀ g, (Z g).val = (Y g).val.submatrix e e) →
        Continuous (restrictScalarsRep b Z) := fun e Z h =>
      continuous_restrictScalarsRep b Z (by
        rw [show (fun g => restrictScalarsMatrix b (Z g).val) = fun g =>
            (coordMatrix (R := ℚ_[ℓ]) (resIndex (d := d) e))ᵀ * (restrictScalarsRep b Y g).val *
              coordMatrix (resIndex e) from funext fun g => by
          rw [h, ← transpose_coordMatrix_mul_mul_coordMatrix (R := E),
            restrictScalarsMatrix_mul, restrictScalarsMatrix_mul,
            restrictScalarsMatrix_transpose_coordMatrix, restrictScalarsMatrix_coordMatrix]
          rfl]
        exact (continuous_const.matrix_mul hYc).matrix_mul continuous_const)
    have hα : Continuous (restrictScalarsRep b α) :=
      hcont e₁ α hαv
    have hγ : Continuous (restrictScalarsRep b γ) :=
      hcont e₂ γ hγv
    have hdisj' : ∀ p₁ p₂, resIndex (d := d) e₁ p₁ ≠ resIndex e₂ p₂ := fun p₁ p₂ h => by
      have h' := finProdFinEquiv.injective h
      exact hdisj _ _ (congrArg Prod.fst h')
    have hcov' : ∀ p', (∃ p₁, resIndex (d := d) e₁ p₁ = p') ∨
        ∃ p₂, resIndex (d := d) e₂ p₂ = p' := by
      intro p'
      obtain ⟨⟨i, l⟩, rfl⟩ := finProdFinEquiv.surjective p'
      rcases hcov i with ⟨j', rfl⟩ | ⟨j', rfl⟩
      · exact Or.inl ⟨finProdFinEquiv (j', l), resIndex_apply _ _ _⟩
      · exact Or.inr ⟨finProdFinEquiv (j', l), resIndex_apply _ _ _⟩
    have hsZ := isSplitting_coordMatrix (R := ℤ_[ℓ]) (resIndex_injective (d := d) he₁)
      (resIndex_injective (d := d) he₂) hdisj' hcov'
    have hJ : ∀ g, (restrictScalarsRep b Y g).val *
        (coordMatrix (R := ℤ_[ℓ]) (resIndex (d := d) e₁)).map (PadicInt.Coe.ringHom (p := ℓ)) =
        (coordMatrix (R := ℤ_[ℓ]) (resIndex (d := d) e₁)).map (PadicInt.Coe.ringHom (p := ℓ)) *
          (restrictScalarsRep b α g).val := fun g => by
      rw [coordMatrix_map, restrictScalarsRep_val, restrictScalarsRep_val,
        ← restrictScalarsMatrix_coordMatrix b, ← restrictScalarsMatrix_mul,
        ← restrictScalarsMatrix_mul, IsSplitting.subRep_val, ← (hst g).1]
    have hK : ∀ g, ((coordMatrix (R := ℤ_[ℓ]) (resIndex (d := d) e₂))ᵀ).map
        (PadicInt.Coe.ringHom (p := ℓ)) * (restrictScalarsRep b Y g).val =
        (restrictScalarsRep b γ g).val *
          ((coordMatrix (R := ℤ_[ℓ]) (resIndex (d := d) e₂))ᵀ).map
            (PadicInt.Coe.ringHom (p := ℓ)) := fun g => by
      rw [Matrix.transpose_map, coordMatrix_map, restrictScalarsRep_val, restrictScalarsRep_val,
        ← restrictScalarsMatrix_transpose_coordMatrix b, ← restrictScalarsMatrix_mul,
        ← restrictScalarsMatrix_mul, IsSplitting.quotRep_val, ← (hst g).2]
    have hαP : Pb a fun g => (α g).val := by
      rw [show (fun g => (α g).val) = fun g => (Y g).val.submatrix e₁ e₁ from funext hαv]
      exact hblk t₀ a e₁ he₁ hre₁
    have hγP : ∀ (t : ℤ) (a' : ℕ) (e' : Fin a' → Fin c), Function.Injective e' →
        (∀ j, (δ ∘ e₂) j = t ↔ ∃ j', e' j' = j) → Pb a' fun g => (γ g).val.submatrix e' e' := by
      intro t a' e' he' hre'
      by_cases ht : t = t₀
      · subst ht
        obtain rfl : a' = 0 := by
          by_contra h
          have h1 : δ (e₂ (e' ⟨0, Nat.pos_of_ne_zero h⟩)) = t₀ := (hre' _).2 ⟨_, rfl⟩
          exact (hre₂ _).2 ⟨_, rfl⟩ h1
        exact hPb _
      · have hre'' : ∀ i, δ i = t ↔ ∃ j', (e₂ ∘ e') j' = i := fun i => by
          constructor
          · intro hi
            obtain ⟨j'', rfl⟩ := (hre₂ i).1 (hi ▸ ht)
            obtain ⟨j', rfl⟩ := (hre' j'').1 hi
            exact ⟨j', rfl⟩
          · rintro ⟨j', rfl⟩
            exact (hre' (e' j')).2 ⟨j', rfl⟩
        rw [show (fun g => (γ g).val.submatrix e' e') =
            fun g => (Y g).val.submatrix (e₂ ∘ e') (e₂ ∘ e') from funext fun g => by
          rw [hγv, Matrix.submatrix_submatrix]]
        exact hblk t a' (e₂ ∘ e') (he₂.comp he') hre''
    have hγup : ∀ g, IsGradedUpper (δ ∘ e₂) (γ g).val := fun g j' j'' h => by
      rw [hγv]
      exact hup g _ _ h
    obtain ⟨hγd, hγw⟩ := ih c hc γ (δ ∘ e₂) hγup hγ hγP
    have := hFD _ hα
    have hαw := hbase α hα hαP
    exact isCharpolyNormMixedOfWeightLE_representationSheaf_of_isSplitting B X x f j kbar p n hcard
      hsZ hY hα hγ hJ hK i (hfin _ hα) hαw hγw

end Stacks.EtaleCohomology

end
