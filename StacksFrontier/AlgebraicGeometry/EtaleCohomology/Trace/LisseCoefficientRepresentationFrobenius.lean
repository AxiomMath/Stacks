module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCoefficientRepresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientSheafRationalStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RestrictScalarsLinearEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseKernelTrace

/-!
# The `E`-linear Frobenius on the stalks of a lisse sheaf with coefficients

Let `F` be a lisse ℓ-adic sheaf with coefficients in a `ℤ_ℓ`-algebra `O` on a connected scheme
`X`, `E = O[1/ℓ]` a finite extension of `ℚ_ℓ`, and let
`ρ, φ : F → ℱ_ρ, ψ : ℱ_ρ → F, τ : π₁(X, x̄) → GL_m(E), P, Q` be the data of
`Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse`: `Q ρ₀(g) P = Res_b τ(g)` and
`Q α(e) P = Res_b(e · 1)`, `α(o) = ℓ⁻ᴺ (ψ ∘ o ∘ φ)`. At a closed point `y` with finite residue
field, the rational stalk `ℚ_ℓ ⊗ F_ȳ` is an `E`-vector space
(`Stacks.EtaleCohomology.LAdicSheaf.CoefficientSheaf.rationalStalkModule`) on which the geometric
Frobenius is `E`-linear; its `E`-linear characteristic polynomial is that of `τ(F_y)`
(`Stacks.EtaleCohomology.charpoly_rationalStalkFrobenius_eq_restrictScalarsRep`).

Indeed the composite `Ψ : ℚ_ℓ ⊗ F_ȳ → ℚ_ℓ ⊗ (ℱ_ρ)_ȳ ≅ ℚ_ℓ^r → ℚ_ℓ^{md}` of the rational stalk map
of `φ` (bijective, `φ` being an isogeny), the trivialisation of the stalk of `ℱ_ρ` along a path
`t : ȳ ⇝ x̄` and multiplication by `Q` carries the action of `o ∈ O` to `ℓ⁻ᴺ (ψ ∘ o ∘ φ) = α(o)`,
hence (`E` being a localisation of `O`) that of every `e ∈ E` to `Q α(e) P = Res_b(e · 1)`, and the
geometric Frobenius to `Q ρ₀(F_y) P = Res_b τ(F_y)`;
`Stacks.EtaleCohomology.charpoly_eq_of_restrictScalarsMatrix` concludes. This is step (a) of the
purity of the representation `τ` of `G|_V` in Laumon's degeneration argument
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.LevelTrivialization.rationalStalkEquiv_baseChange`.
* `Stacks.EtaleCohomology.finite_rationalStalkLeft_of_isogeny`.
* `Stacks.EtaleCohomology.charpoly_rationalStalkFrobenius_eq_restrictScalarsRep`,
  `Stacks.EtaleCohomology.charpoly_rationalStalkFrobenius_eq_restrictScalarsRep_family`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix Stacks.Frobenius

open scoped IsMulCommutative

universe u

namespace Stacks.EtaleCohomology

section Trivialization

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

/-- **A `ℤ_ℓ`-linear map of ℓ-adic stalks which is multiplication by an integral matrix `M` in
trivialisations is multiplication by `M` over `ℚ_ℓ` on the rational stalks.** -/
public theorem LAdicSheaf.LevelTrivialization.rationalStalkEquiv_baseChange
    {F G : LAdicSheaf.{u, u + 1} B X ℓ} {s s' : GeometricPoint X.1} {r r' : ℕ}
    (T : LAdicSheaf.LevelTrivialization F s r) (T' : LAdicSheaf.LevelTrivialization G s' r')
    (L : LAdicSheaf.stalk B X ℓ F s →ₗ[ℤ_[ℓ]] LAdicSheaf.stalk B X ℓ G s')
    (M : Matrix (Fin r') (Fin r) ℤ_[ℓ]) (hM : ∀ v, T'.stalkEquiv (L v) = M *ᵥ T.stalkEquiv v)
    (w : LAdicSheaf.rationalStalkLeft B X ℓ F s) :
    T'.rationalStalkEquiv (LinearMap.baseChange ℚ_[ℓ] L w) =
      M.map ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) *ᵥ T.rationalStalkEquiv w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, Matrix.mulVec_zero]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, Matrix.mulVec_add]
  | tmul c v =>
    change TensorProduct.piScalarRight ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ] (Fin r')
        ((T'.stalkEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _) (LinearMap.baseChange ℚ_[ℓ] L (c ⊗ₜ v))) =
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

end Trivialization

section Frobenius

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime]
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
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O)
  {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]) (hρ : Continuous ρ)
  (φ : F.toLAdicSheaf ⟶ LAdicSheaf.representationSheaf B X x ρ hρ)
  (ψ : LAdicSheaf.representationSheaf B X x ρ hρ ⟶ F.toLAdicSheaf) (N : ℕ)
  (hφψ : φ ≫ ψ = (ℓ ^ N) • 𝟙 _) (hψφ : ψ ≫ φ = (ℓ ^ N) • 𝟙 _)

/-- **The rational stalk of `F` at `s̄` is `ℚ_ℓ^r`**, through the isogeny `φ : F → ℱ_ρ` and the
trivialisation of the stalk of `ℱ_ρ` along a path `t : s̄ ⇝ x̄`. -/
public def isogenyRationalStalkEquiv {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) :
    LAdicSheaf.rationalStalkLeft B X ℓ F.toLAdicSheaf s ≃ₗ[ℚ_[ℓ]] (Fin r → ℚ_[ℓ]) :=
  haveI := compactSpace_etaleFundamentalGroup X.1 x
  (LinearEquiv.ofBijective (LAdicSheaf.rationalStalkMap φ s)
    (LAdicSheaf.bijective_rationalStalkMap_of_isogeny φ ψ N hφψ hψφ s)).trans
    (representationLevelTrivialization B X x (integralModel ρ hρ)
      (continuous_integralModel ρ hρ) t).rationalStalkEquiv

/-- `isogenyRationalStalkEquiv` is the rational stalk map of `φ` followed by the trivialisation of
the rational stalk of `ℱ_ρ` along `t`. -/
public theorem isogenyRationalStalkEquiv_apply {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x)
    (v : LAdicSheaf.rationalStalkLeft B X ℓ F.toLAdicSheaf s) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    isogenyRationalStalkEquiv B X x F ρ hρ φ ψ N hφψ hψφ t v =
      (representationLevelTrivialization B X x (integralModel ρ hρ)
        (continuous_integralModel ρ hρ) t).rationalStalkEquiv
          (LAdicSheaf.rationalStalkMap φ s v) :=
  rfl

include hφψ hψφ in
/-- **The rational stalk of a sheaf isogenous to `ℱ_ρ` is finite-dimensional.** -/
public theorem finite_rationalStalkLeft_of_isogeny (s : GeometricPoint X.1) :
    Module.Finite ℚ_[ℓ] (LAdicSheaf.rationalStalkLeft B X ℓ F.toLAdicSheaf s) :=
  Module.Finite.equiv (isogenyRationalStalkEquiv B X x F ρ hρ φ ψ N hφψ hψφ
    (nonempty_finiteEtaleFiberFunctorIso X.1 s x).some).symm

/-- **The action of `o ∈ O` on the trivialised rational stalk is `ℓ⁻ᴺ (ψ ∘ o ∘ φ)`.** -/
public theorem isogenyRationalStalkEquiv_rationalStalkIntegralRingHom {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (o : O)
    (v : LAdicSheaf.rationalStalkLeft B X ℓ F.toLAdicSheaf s) :
    isogenyRationalStalkEquiv B X x F ρ hρ φ ψ N hφψ hψφ t (F.rationalStalkIntegralRingHom s o v) =
      isogenyCoefficientRingHom B X x F ρ hρ φ ψ N hφψ hψφ o *ᵥ
        isogenyRationalStalkEquiv B X x F ρ hρ φ ψ N hφψ hψφ t v := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  set T := representationLevelTrivialization B X x (integralModel ρ hρ)
    (continuous_integralModel ρ hρ) t
  have hcomp : LAdicSheaf.rationalStalkMap (ψ ≫ F.act o ≫ φ) s
      (LAdicSheaf.rationalStalkMap φ s v) =
      ((ℓ ^ N : ℕ) : ℚ_[ℓ]) • LAdicSheaf.rationalStalkMap φ s
        (LAdicSheaf.rationalStalkMap (F.act o) s v) := by
    rw [← LinearMap.comp_apply, ← LAdicSheaf.rationalStalkMap_comp, ← Category.assoc, hφψ,
      LAdicSheaf.rationalStalkMap_comp, LinearMap.comp_apply, LAdicSheaf.rationalStalkMap_nsmul_id,
      LinearMap.smul_apply, LinearMap.id_apply, map_smul, LAdicSheaf.rationalStalkMap_comp,
      LinearMap.comp_apply]
  have hM := LAdicSheaf.LevelTrivialization.rationalStalkEquiv_rationalStalkMap T T
    (isogenyCoefficientEnd B X x F ρ hρ φ ψ o) (isogenyCoefficientMatrix B X x F ρ hρ φ ψ o)
    (fun w => representationLevelTrivialization_stalkEquiv_stalkMap_of_hom B X x
      (continuous_integralModel ρ hρ) (continuous_integralModel ρ hρ) t _ w)
    (LAdicSheaf.rationalStalkMap φ s v)
  rw [isogenyRationalStalkEquiv_apply, isogenyRationalStalkEquiv_apply,
    isogenyCoefficientRingHom_apply, Matrix.smul_mulVec]
  calc _ = (((ℓ ^ N : ℕ) : ℚ_[ℓ]))⁻¹ • (((ℓ ^ N : ℕ) : ℚ_[ℓ]) •
        T.rationalStalkEquiv (LAdicSheaf.rationalStalkMap φ s
          (LAdicSheaf.rationalStalkMap (F.act o) s v))) := by
        rw [smul_smul,
          inv_mul_cancel₀ (Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)),
          one_smul]
        rfl
    _ = (((ℓ ^ N : ℕ) : ℚ_[ℓ]))⁻¹ • T.rationalStalkEquiv
          (LAdicSheaf.rationalStalkMap (isogenyCoefficientEnd B X x F ρ hρ φ ψ o) s
            (LAdicSheaf.rationalStalkMap φ s v)) :=
        congrArg (_ • ·) ((T.rationalStalkEquiv.map_smul _ _).symm.trans
          (congrArg T.rationalStalkEquiv hcomp.symm))
    _ = _ := by
        rw [hM, Nat.cast_pow]
        rfl

variable (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]
  (hOE : ∀ c : ℤ_[ℓ], algebraMap O E (algebraMap ℤ_[ℓ] O c) = algebraMap ℚ_[ℓ] E c)

/-- **The action of `e ∈ E` on the trivialised rational stalk is `α(e)`**
(`Stacks.EtaleCohomology.isogenyCoefficientAlgHom`). -/
public theorem isogenyRationalStalkEquiv_rationalStalkRingHom {s : GeometricPoint X.1}
    (t : finiteEtaleFiberFunctor s ≅ finiteEtaleFiberFunctor x) (e : E)
    (v : LAdicSheaf.rationalStalkLeft B X ℓ F.toLAdicSheaf s) :
    isogenyRationalStalkEquiv B X x F ρ hρ φ ψ N hφψ hψφ t (F.rationalStalkRingHom s E e v) =
      isogenyCoefficientAlgHom B X x F ρ hρ φ ψ N E hφψ hψφ hOE e *ᵥ
        isogenyRationalStalkEquiv B X x F ρ hρ φ ψ N hφψ hψφ t v := by
  set Φ := isogenyRationalStalkEquiv B X x F ρ hρ φ ψ N hφψ hψφ t
  let j : E →+* Module.End ℚ_[ℓ] (Fin r → ℚ_[ℓ]) :=
    (Φ.conjRingEquiv.toRingHom).comp (F.rationalStalkRingHom s E)
  let k : E →+* Module.End ℚ_[ℓ] (Fin r → ℚ_[ℓ]) :=
    (Matrix.toLinAlgEquiv'.toRingEquiv.toRingHom).comp
      (isogenyCoefficientAlgHom B X x F ρ hρ φ ψ N E hφψ hψφ hOE).toRingHom
  have hjk : j = k := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (ℓ : O)) (RingHom.ext fun o => ?_)
    refine LinearMap.ext fun w => ?_
    obtain ⟨v', rfl⟩ := Φ.surjective w
    change Φ (F.rationalStalkRingHom s E (algebraMap O E o) (Φ.symm (Φ v'))) =
      isogenyCoefficientAlgHom B X x F ρ hρ φ ψ N E hφψ hψφ hOE (algebraMap O E o) *ᵥ Φ v'
    rw [LinearEquiv.symm_apply_apply, F.rationalStalkRingHom_algebraMap_apply,
      isogenyRationalStalkEquiv_rationalStalkIntegralRingHom,
      isogenyCoefficientAlgHom_algebraMap, ← isogenyCoefficientRingHom_apply]
  have h := LinearMap.congr_fun (RingHom.congr_fun hjk e) (Φ v)
  change Φ (F.rationalStalkRingHom s E e (Φ.symm (Φ v))) = _ at h
  rwa [LinearEquiv.symm_apply_apply] at h

/-- **The geometric Frobenius on the trivialised rational stalk is `ρ₀(F_y)`**, `F_y` the
geometric Frobenius element transported along the path `t`. -/
public theorem isogenyRationalStalkEquiv_rationalStalkFrobenius (y : closedPoints X.1)
    [Finite (X.1.residueField y.1)]
    (t : finiteEtaleFiberFunctor (geometricPointAt X.1 y.1) ≅ finiteEtaleFiberFunctor x)
    (v : LAdicSheaf.rationalStalkLeft B X ℓ F.toLAdicSheaf (geometricPointAt X.1 y.1)) :
    haveI := compactSpace_etaleFundamentalGroup X.1 x
    isogenyRationalStalkEquiv B X x F ρ hρ φ ψ N hφψ hψφ t
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F.toLAdicSheaf y.1 inferInstance v) =
      (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
          (integralModel ρ hρ (frobeniusDataOfPath x y t).element⁻¹)).val *ᵥ
        isogenyRationalStalkEquiv B X x F ρ hρ φ ψ N hφψ hψφ t v := by
  have he : etaleFundamentalGroupMulEquiv t (frobeniusDataOfPath x y t).localElement⁻¹ =
      (frobeniusDataOfPath x y t).element⁻¹ :=
    (etaleFundamentalGroupMulEquiv t).map_inv _
  have := compactSpace_etaleFundamentalGroup X.1 x
  have hnat := LinearMap.congr_fun (LAdicSheaf.rationalStalkEnd_comp_rationalStalkMap φ
    (frobeniusPointHom X.1 y.1)) v
  simp only [LinearMap.comp_apply] at hnat
  have hM := LAdicSheaf.LevelTrivialization.rationalStalkEquiv_baseChange
    (representationLevelTrivialization B X x (integralModel ρ hρ) (continuous_integralModel ρ hρ) t)
    (representationLevelTrivialization B X x (integralModel ρ hρ) (continuous_integralModel ρ hρ) t)
    (LAdicSheaf.stalkEnd B X ℓ _ (frobeniusPointHom X.1 y.1))
    (integralModel ρ hρ (frobeniusDataOfPath x y t).element⁻¹).val
    (fun w => (representationLevelTrivialization_stalkEquiv_stalkEnd B X x
        (continuous_integralModel ρ hρ) t (frobeniusPointHom X.1 y.1) _
        (inv_localElement_hom x y t) w).trans
      (congrArg (fun g => (integralModel ρ hρ g).val *ᵥ
        (representationLevelTrivialization B X x (integralModel ρ hρ)
          (continuous_integralModel ρ hρ) t).stalkEquiv w) he))
    (LAdicSheaf.rationalStalkMap φ _ v)
  rw [isogenyRationalStalkEquiv_apply, isogenyRationalStalkEquiv_apply]
  exact (congrArg _ hnat.symm).trans hM

variable [FiniteDimensional ℚ_[ℓ] E] {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E)

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **The `E`-linear Frobenius on the rational stalk of a lisse sheaf with coefficients has the
characteristic polynomial of `τ(F_y)`**, for the data
`ρ, φ, ψ, N, τ, P, Q` of `Stacks.EtaleCohomology.exists_restrictScalarsRep_of_isLisse` and the
geometric Frobenius element `F_y` transported along any path `t : ȳ ⇝ x̄`. -/
public theorem charpoly_rationalStalkFrobenius_eq_restrictScalarsRep {m : ℕ}
    (τ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E)
    (P : Matrix (Fin r) (Fin (m * d)) ℚ_[ℓ]) (Q : Matrix (Fin (m * d)) (Fin r) ℚ_[ℓ])
    (hPQ : P * Q = 1)
    (hα : ∀ e : E, Q * isogenyCoefficientAlgHom B X x F ρ hρ φ ψ N E hφψ hψφ hOE e * P =
      restrictScalarsMatrix b (Matrix.scalar (Fin m) e))
    (hτ : ∀ g : EtaleFundamentalGroup X.1 x,
      haveI := compactSpace_etaleFundamentalGroup X.1 x
      Q * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (integralModel ρ hρ g)).val * P = (restrictScalarsRep b τ g).val)
    (hQP : Q * P = 1) (y : closedPoints X.1) [Finite (X.1.residueField y.1)]
    (t : finiteEtaleFiberFunctor (geometricPointAt X.1 y.1) ≅ finiteEtaleFiberFunctor x) :
    letI := F.rationalStalkModule (geometricPointAt X.1 y.1) E
    haveI := F.rationalStalkModule_isScalarTower (geometricPointAt X.1 y.1) E hOE
    haveI := finite_rationalStalkLeft_of_isogeny B X x F ρ hρ φ ψ N hφψ hψφ
      (geometricPointAt X.1 y.1)
    haveI : Module.Finite E (LAdicSheaf.rationalStalkLeft B X ℓ F.toLAdicSheaf
        (geometricPointAt X.1 y.1)) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    (F.rationalStalkFrobenius E y.1 inferInstance).charpoly =
      (τ (frobeniusDataOfPath x y t).element⁻¹).val.charpoly := by
  let := F.rationalStalkModule (geometricPointAt X.1 y.1) E
  have := F.rationalStalkModule_isScalarTower (geometricPointAt X.1 y.1) E hOE
  have := finite_rationalStalkLeft_of_isogeny B X x F ρ hρ φ ψ N hφψ hψφ
    (geometricPointAt X.1 y.1)
  have : Module.Finite E (LAdicSheaf.rationalStalkLeft B X ℓ F.toLAdicSheaf
      (geometricPointAt X.1 y.1)) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
  have := compactSpace_etaleFundamentalGroup X.1 x
  set Φ := isogenyRationalStalkEquiv B X x F ρ hρ φ ψ N hφψ hψφ t
  let Ψ := Φ.trans (Matrix.toLin'OfInv hPQ hQP)
  have hΨ : ∀ w, Ψ w = Q *ᵥ Φ w := fun _ => rfl
  refine charpoly_eq_of_restrictScalarsMatrix b Ψ (fun e w => ?_) _ _ (fun w => ?_)
  · rw [hΨ, hΨ, ← hα, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec (M := P), hPQ, Matrix.one_mulVec]
    exact congrArg (Q *ᵥ ·)
      (isogenyRationalStalkEquiv_rationalStalkRingHom B X x F ρ hρ φ ψ N hφψ hψφ E hOE t e w)
  · rw [hΨ, hΨ, ← restrictScalarsRep_val, ← hτ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec (M := P), hPQ, Matrix.one_mulVec]
    exact congrArg (Q *ᵥ ·)
      (isogenyRationalStalkEquiv_rationalStalkFrobenius B X x F ρ hρ φ ψ N hφψ hψφ y t w)

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **`Stacks.EtaleCohomology.charpoly_rationalStalkFrobenius_eq_restrictScalarsRep` for the
geometric Frobenius elements `Stacks.EtaleCohomology.geometricFrobeniusFamily`** at the closed
points of a scheme of finite type over a finite field. -/
public theorem charpoly_rationalStalkFrobenius_eq_restrictScalarsRep_family {k : Type u}
    [Field k] [Finite k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] {m : ℕ}
    (τ : EtaleFundamentalGroup X.1 x →* GL (Fin m) E)
    (P : Matrix (Fin r) (Fin (m * d)) ℚ_[ℓ]) (Q : Matrix (Fin (m * d)) (Fin r) ℚ_[ℓ])
    (hPQ : P * Q = 1)
    (hα : ∀ e : E, Q * isogenyCoefficientAlgHom B X x F ρ hρ φ ψ N E hφψ hψφ hOE e * P =
      restrictScalarsMatrix b (Matrix.scalar (Fin m) e))
    (hτ : ∀ g : EtaleFundamentalGroup X.1 x,
      haveI := compactSpace_etaleFundamentalGroup X.1 x
      Q * (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))
        (integralModel ρ hρ g)).val * P = (restrictScalarsRep b τ g).val)
    (hQP : Q * P = 1) (y : closedPoints X.1) :
    letI := F.rationalStalkModule (geometricPointAt X.1 y.1) E
    haveI := F.rationalStalkModule_isScalarTower (geometricPointAt X.1 y.1) E hOE
    haveI := finite_rationalStalkLeft_of_isogeny B X x F ρ hρ φ ψ N hφψ hψφ
      (geometricPointAt X.1 y.1)
    haveI : Module.Finite E (LAdicSheaf.rationalStalkLeft B X ℓ F.toLAdicSheaf
        (geometricPointAt X.1 y.1)) := Module.Finite.of_restrictScalars_finite ℚ_[ℓ] E _
    (F.rationalStalkFrobenius E y.1 (finite_residueField f y.1 y.2)).charpoly =
      (τ (geometricFrobeniusFamily f x y)).val.charpoly :=
  have := finite_residueField f y.1 y.2
  charpoly_rationalStalkFrobenius_eq_restrictScalarsRep B X x F ρ hρ φ ψ N hφψ hψφ E hOE b τ P Q
    hPQ hα hτ hQP y _

end Frobenius

end Stacks.EtaleCohomology

end
