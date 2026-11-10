module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.LisseBiprod
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationMorphismIntertwiner
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafTracePow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveSheafBound
public import StacksFrontier.LinearAlgebra.IntertwinerKernelRepresentation

/-!
# The kernel of a surjection of lisse sheaves, in trace form

Let `X` be a connected scheme of finite type over a finite field and let `φ : A ⟶ F` be a
morphism of lisse ℓ-adic sheaves that is surjective on the rational stalks at the closed points.
Then there is a lisse sheaf `K`, the kernel of `φ` up to isogeny, with
`Tr(π_y^n | A_ȳ) = Tr(π_y^n | F_ȳ) + Tr(π_y^n | K_ȳ)` for every closed point `y` and every `n`.
This is the additivity of traces in a short exact sequence `0 → K → A → F → 0` of lisse
`ℚ_ℓ`-sheaves. It is used in the induction step of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), where `R² g_! G` is the quotient of a
lisse sheaf.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.bijective_rationalStalkMap_of_isogeny`: an isogeny is
  bijective on rational stalks.
* `Stacks.EtaleCohomology.LAdicSheaf.exists_isLisse_trace_rationalStalkFrobenius_pow_eq_add`:
  the kernel of a surjection of lisse sheaves, in trace form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.Frobenius

open scoped Matrix

universe u

namespace Stacks.EtaleCohomology

variable {B : BigEtaleSite.{u}} {X : B.Scheme} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1]

/-- **An isogeny is bijective on rational stalks**: if `φ ≫ ψ` and `ψ ≫ φ` are multiplication by
`ℓᴺ`, the map of rational stalks of `φ` has inverse `ℓ⁻ᴺ` times that of `ψ`. -/
theorem LAdicSheaf.bijective_rationalStalkMap_of_isogeny {F G : LAdicSheaf.{u, u + 1} B X ℓ}
    (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F)
    (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G) (s : GeometricPoint X.1) :
    Function.Bijective (LAdicSheaf.rationalStalkMap φ s) := by
  have hc : ((ℓ ^ N : ℕ) : ℚ_[ℓ]) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  have hcomp : ∀ {F' G' : LAdicSheaf.{u, u + 1} B X ℓ} (α : F' ⟶ G') (β : G' ⟶ F'),
      α ≫ β = (ℓ ^ N) • 𝟙 F' →
        LAdicSheaf.rationalStalkMap β s ∘ₗ LAdicSheaf.rationalStalkMap α s =
          ((ℓ ^ N : ℕ) : ℚ_[ℓ]) • LinearMap.id := by
    intro F' G' α β h
    rw [← LAdicSheaf.rationalStalkMap_nsmul_id, ← h]
    simp only [LAdicSheaf.rationalStalkMap, LAdicSheaf.stalkMap_comp, LinearMap.baseChange_comp]
  let e : LAdicSheaf.rationalStalkLeft B X ℓ F s ≃ₗ[ℚ_[ℓ]] LAdicSheaf.rationalStalkLeft B X ℓ G s :=
    LinearEquiv.ofLinearMap (LAdicSheaf.rationalStalkMap φ s)
      (((ℓ ^ N : ℕ) : ℚ_[ℓ])⁻¹ • LAdicSheaf.rationalStalkMap ψ s)
      (by rw [LinearMap.comp_smul, hcomp ψ φ h₂, smul_smul, inv_mul_cancel₀ hc, one_smul])
      (by rw [LinearMap.smul_comp, hcomp φ ψ h₁, smul_smul, inv_mul_cancel₀ hc, one_smul])
  exact e.bijective

/-- The rational stalk of a sheaf with trivialised ℓ-adic stalk is `ℚ_ℓ^r`. -/
def LAdicSheaf.LevelTrivialization.rationalStalkEquiv {F : LAdicSheaf.{u, u + 1} B X ℓ}
    {s : GeometricPoint X.1} {r : ℕ} (T : LAdicSheaf.LevelTrivialization F s r) :
    LAdicSheaf.rationalStalkLeft B X ℓ F s ≃ₗ[ℚ_[ℓ]] (Fin r → ℚ_[ℓ]) :=
  (T.stalkEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _).trans
    (TensorProduct.piScalarRight ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ] (Fin r))

/-- A map of ℓ-adic stalks which is multiplication by an integral matrix `M` in trivialisations is
multiplication by `M` over `ℚ_ℓ` on the rational stalks. -/
theorem LAdicSheaf.LevelTrivialization.rationalStalkEquiv_rationalStalkMap
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} {s : GeometricPoint X.1} {r r' : ℕ}
    (T : LAdicSheaf.LevelTrivialization F s r) (T' : LAdicSheaf.LevelTrivialization G s r')
    (Φ : F ⟶ G) (M : Matrix (Fin r') (Fin r) ℤ_[ℓ])
    (hM : ∀ v, T'.stalkEquiv (LAdicSheaf.stalkMap Φ s v) = M *ᵥ T.stalkEquiv v)
    (u : LAdicSheaf.rationalStalkLeft B X ℓ F s) :
    T'.rationalStalkEquiv (LAdicSheaf.rationalStalkMap Φ s u) =
      M.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) *ᵥ T.rationalStalkEquiv u := by
  induction u using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Matrix.mulVec_add]
  | tmul c v =>
    change TensorProduct.piScalarRight ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ] (Fin r')
        ((T'.stalkEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _)
          (LinearMap.baseChange ℚ_[ℓ] (LAdicSheaf.stalkMap Φ s) (c ⊗ₜ v))) =
      M.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) *ᵥ TensorProduct.piScalarRight ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ] (Fin r)
        ((T.stalkEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _) (c ⊗ₜ v))
    rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, TensorProduct.piScalarRightHom_tmul, hM]
    funext i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    change (M i j * _) • c = ((M i j : ℤ_[ℓ]) : ℚ_[ℓ]) * (_ • c)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
    rfl

variable (B X ℓ) [ConnectedSpace X.1]

/-- **The kernel of a surjection of lisse sheaves on a connected scheme, in trace form.** Let `X`
be connected and of finite type over a finite field `k`, and let `φ : A ⟶ F` be a morphism of
lisse ℓ-adic sheaves on `X` that is surjective on the rational stalks at the geometric points over
the closed points. Then there is a lisse ℓ-adic sheaf `K` with
`Tr(π_y^n | A_ȳ) = Tr(π_y^n | F_ȳ) + Tr(π_y^n | K_ȳ)` for every closed point `y` and every `n`. -/
theorem LAdicSheaf.exists_isLisse_trace_rationalStalkFrobenius_pow_eq_add
    {k : Type u} [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {A F : LAdicSheaf.{u, u + 1} B X ℓ} (hA : A.IsLisse) (hF : F.IsLisse) (φ : A ⟶ F)
    (hφ : ∀ y : closedPoints X.1,
      Function.Surjective (LAdicSheaf.rationalStalkMap φ (geometricPointAt X.1 y.1))) :
    ∃ K : LAdicSheaf.{u, u + 1} B X ℓ, K.IsLisse ∧ ∀ (y : closedPoints X.1) (n : ℕ),
      LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ A y.1
          (finite_residueField f y.1 y.2) ^ n) =
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ F y.1
            (finite_residueField f y.1 y.2) ^ n) +
          LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ K y.1
            (finite_residueField f y.1 y.2) ^ n) := by
  classical
  by_cases hne : Nonempty (closedPoints X.1)
  swap
  · exact ⟨A, hA, fun y => (hne ⟨y⟩).elim⟩
  obtain ⟨y₀⟩ := hne
  set x := geometricPointAt X.1 y₀.1
  have := compactSpace_etaleFundamentalGroup X.1 x
  obtain ⟨rA, ρA, hρA, φA, ψA, NA, hA₁, hA₂⟩ :=
    LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse (B := B) (X := X) (ℓ := ℓ) (x := x)
      (F := A) (hF := hA)
  obtain ⟨rF, ρF, hρF, φF, ψF, NF, hF₁, hF₂⟩ :=
    LAdicSheaf.exists_representationSheaf_isogeny_of_isLisse (B := B) (X := X) (ℓ := ℓ) (x := x)
      (F := F) (hF := hF)
  let Φ := ψA ≫ φ ≫ φF
  obtain ⟨M, hM, hMst⟩ := exists_intertwiner_stalkEquiv_stalkMap B X x
    (continuous_integralModel ρA hρA) (continuous_integralModel ρF hρF) (Iso.refl _) Φ
  set TA := representationLevelTrivialization B X x (integralModel ρA hρA)
    (continuous_integralModel ρA hρA) (Iso.refl (finiteEtaleFiberFunctor x))
  set TF := representationLevelTrivialization B X x (integralModel ρF hρF)
    (continuous_integralModel ρF hρF) (Iso.refl (finiteEtaleFiberFunctor x))
  have hΦ : Function.Surjective (LAdicSheaf.rationalStalkMap Φ x) := by
    have hcomp : LAdicSheaf.rationalStalkMap Φ x = LAdicSheaf.rationalStalkMap φF x ∘ₗ
        LAdicSheaf.rationalStalkMap φ x ∘ₗ LAdicSheaf.rationalStalkMap ψA x := by
      simp only [Φ, Stacks.EtaleCohomology.LAdicSheaf.rationalStalkMap_comp, LinearMap.comp_assoc]
    rw [hcomp]
    exact ((LAdicSheaf.bijective_rationalStalkMap_of_isogeny φF ψF NF hF₁ hF₂ x).2.comp
      (hφ y₀)).comp (LAdicSheaf.bijective_rationalStalkMap_of_isogeny ψA φA NA hA₂ hA₁ x).2
  let M' := M.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ])
  have hM' : Function.Surjective M'.mulVec := by
    intro z
    obtain ⟨w, rfl⟩ := TF.rationalStalkEquiv.surjective z
    obtain ⟨v, rfl⟩ := hΦ w
    exact ⟨TA.rationalStalkEquiv v,
      (TA.rationalStalkEquiv_rationalStalkMap TF Φ M hMst v).symm⟩
  set PA := (exists_conj_integral ρA hρA).choose
  set PF := (exists_conj_integral ρF hρF).choose
  have hσ : ∀ {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
      (hρ : Continuous ρ) (g : EtaleFundamentalGroup X.1 x),
      (integralModel ρ hρ g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) =
        (exists_conj_integral ρ hρ).choose⁻¹.val * (ρ g).val *
          (exists_conj_integral ρ hρ).choose.val := fun ρ hρ g => by
    have h := congrArg Units.val (map_integralModel ρ hρ g)
    rwa [Units.val_mul, Units.val_mul] at h
  have hM'g : ∀ g, M' * (integralModel ρA hρA g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) =
      (integralModel ρF hρF g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) * M' := fun g => by
    have h := congrArg (fun A => A.map (PadicInt.Coe.ringHom (p := ℓ))) (hM g)
    simp only [Matrix.map_mul] at h
    exact h
  let T := PF.val * M' * PA⁻¹.val
  have hT : ∀ g, T * (ρA g).val = (ρF g).val * T := fun g => by
    have hPA : PA⁻¹.val * (ρA g).val =
        (integralModel ρA hρA g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) * PA⁻¹.val := by
      rw [hσ ρA hρA, Matrix.mul_assoc _ PA.val, PA.mul_inv, Matrix.mul_one]
    have hPF : PF.val * (integralModel ρF hρF g).val.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) =
        (ρF g).val * PF.val := by
      rw [hσ ρF hρF, ← Matrix.mul_assoc, ← Matrix.mul_assoc, PF.mul_inv, Matrix.one_mul]
    simp only [T, Matrix.mul_assoc, hPA]
    rw [← Matrix.mul_assoc M', hM'g, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPF,
      Matrix.mul_assoc, Matrix.mul_assoc]
  have hTs : Function.Surjective T.mulVec := by
    intro z
    obtain ⟨v, hv⟩ := hM' (PF⁻¹.val *ᵥ z)
    refine ⟨PA.val *ᵥ v, ?_⟩
    calc T *ᵥ (PA.val *ᵥ v) = (T * PA.val) *ᵥ v := Matrix.mulVec_mulVec _ _ _
      _ = (PF.val * M') *ᵥ v := by
          simp only [T, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      _ = PF.val *ᵥ (M' *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = z := by
          rw [hv, Matrix.mulVec_mulVec, PF.mul_inv, Matrix.one_mulVec]
  obtain ⟨c, κ, hκ, htr⟩ := Stacks.LinearAlgebra.exists_kernelRepresentation_trace_pow_eq_add
    ρA ρF hρA T hT hTs
  refine ⟨LAdicSheaf.representationSheaf B X x κ hκ,
    LAdicSheaf.representationSheaf_isLisse B X x κ hκ, fun y n => ?_⟩
  have hiso : ∀ {G G' : LAdicSheaf.{u, u + 1} B X ℓ} (α : G ⟶ G') (β : G' ⟶ G) (N : ℕ),
      α ≫ β = (ℓ ^ N) • 𝟙 G → β ≫ α = (ℓ ^ N) • 𝟙 G' →
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ G y.1
            (finite_residueField f y.1 y.2) ^ n) =
          LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ G' y.1
            (finite_residueField f y.1 y.2) ^ n) := by
    intro G G' α β N h₁ h₂
    have := finite_residueField f y.1 y.2
    have hch := LAdicSheaf.charpoly_rationalStalkEnd_of_isogeny B X ℓ α β N h₁ h₂
      (frobeniusPointHom X.1 y.1)
    let fG := LAdicSheaf.rationalStalkEnd B X ℓ G (frobeniusPointHom X.1 y.1)
    let fG' := LAdicSheaf.rationalStalkEnd B X ℓ G' (frobeniusPointHom X.1 y.1)
    let b := Module.Free.chooseBasis ℚ_[ℓ]
      (LAdicSheaf.rationalStalkLeft B X ℓ G' (geometricPointAt X.1 y.1))
    have h2 := trace_pow_eq_of_charpoly_eq fG' (LinearMap.toMatrix b b fG')
      (LinearMap.charpoly_toMatrix fG' b).symm n
    have h1 := trace_pow_eq_of_charpoly_eq fG (LinearMap.toMatrix b b fG')
      (hch.trans (LinearMap.charpoly_toMatrix fG' b).symm) n
    exact h1.trans h2.symm
  rw [hiso φA ψA NA hA₁ hA₂, hiso φF ψF NF hF₁ hF₂,
    trace_rationalStalkFrobenius_representationSheaf_pow B X x f ρA hρA y n,
    trace_rationalStalkFrobenius_representationSheaf_pow B X x f ρF hρF y n,
    trace_rationalStalkFrobenius_representationSheaf_pow B X x f κ hκ y n]
  exact htr _ n

end Stacks.EtaleCohomology

end
