module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafIntertwinerWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafShortExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BlockTriangularLattice
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicShortExactWeights

/-!
# Weights of `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` along a block upper-triangular representation

Let `T : π₁(X, x̄) → GL_r(ℚ_ℓ)` be a continuous representation which is block upper triangular
for a splitting `J, K` (`T J = J α`, `K T = γ K`) with diagonal blocks `α`, `γ`. If the weights of
`π_X^*` on `Hⁱ_c(X_k̄, ℱ_α ⊗ ℚ_ℓ)` and `Hⁱ_c(X_k̄, ℱ_γ ⊗ ℚ_ℓ)` are at most `b`, then so are the
weights of `π_X^*` on `Hⁱ_c(X_k̄, ℱ_T ⊗ ℚ_ℓ)`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.padicLevelMap_zero`: the level components of the zero
  morphism of `ℓ`-adic sheaves are zero.
* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_representationSheaf_of_isSplitting`: the
  weights of `ℱ_T ⊗ ℚ_ℓ` are bounded by those of its diagonal blocks `ℱ_α` and `ℱ_γ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
  Stacks.ConstantSheaf Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat

open scoped Stacks.DiscreteModuleTopology Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

omit [ConnectedSpace X.1] in
/-- The level components of the zero morphism are zero. -/
public theorem LAdicSheaf.padicLevelMap_zero (F G : LAdicSheaf B X ℓ) (n : ℕ) :
    LAdicSheaf.padicLevelMap (0 : F ⟶ G) n = 0 := by
  simpa using LAdicSheaf.padicLevelMap_add (0 : F ⟶ G) 0 n

variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)

/-- Let `T`, `α`, `γ` be continuous `ℚ_ℓ`-representations of `π₁(X, x̄)` with `T J = J α` and
`K T = γ K` for an integral splitting `J, K` of `ℤ_ℓ^r` into `ℤ_ℓ^a` and `ℤ_ℓ^c`. If the finite
levels of `Hⁱ_c(X_k̄, ℱ_α)` are finite and the characteristic roots of `π_X^*` on
`Hⁱ_c(X_k̄, ℱ_α ⊗ ℚ_ℓ)` and `Hⁱ_c(X_k̄, ℱ_γ ⊗ ℚ_ℓ)` have absolute values `q ^ (w / 2)` with
`w ≤ b`, so do those on `Hⁱ_c(X_k̄, ℱ_T ⊗ ℚ_ℓ)`. -/
public theorem isCharpolyNormMixedOfWeightLE_representationSheaf_of_isSplitting {r a c : ℕ}
    {J : Matrix (Fin r) (Fin a) ℤ_[ℓ]} {J' : Matrix (Fin a) (Fin r) ℤ_[ℓ]}
    {K : Matrix (Fin c) (Fin r) ℤ_[ℓ]} {K' : Matrix (Fin r) (Fin c) ℤ_[ℓ]}
    (hs : IsSplitting J J' K K')
    {T : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ]} (hT : Continuous T)
    {α : EtaleFundamentalGroup X.1 x →* GL (Fin a) ℚ_[ℓ]} (hα : Continuous α)
    {γ : EtaleFundamentalGroup X.1 x →* GL (Fin c) ℚ_[ℓ]} (hγ : Continuous γ)
    (hJ : ∀ g, (T g).val * J.map (PadicInt.Coe.ringHom (p := ℓ)) =
      J.map (PadicInt.Coe.ringHom (p := ℓ)) * (α g).val)
    (hK : ∀ g, K.map (PadicInt.Coe.ringHom (p := ℓ)) * (T g).val =
      (γ g).val * K.map (PadicInt.Coe.ringHom (p := ℓ))) (i : ℤ)
    [hTd : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f j kbar (LAdicSheaf.representationSheaf B X x T hT) i)]
    [hαd : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f j kbar (LAdicSheaf.representationSheaf B X x α hα) i)]
    [hγd : FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ
      f j kbar (LAdicSheaf.representationSheaf B X x γ hγ) i)]
    (hfin : ∀ m, Finite ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B X ℓ (LAdicSheaf.representationSheaf B X x α hα) m)))
    {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ}
    (hαw : IsCharpolyNormMixedOfWeightLE q ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
        (LAdicSheaf.representationSheaf B X x α hα) i).hom)
    (hγw : IsCharpolyNormMixedOfWeightLE q ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
        (LAdicSheaf.representationSheaf B X x γ hγ) i).hom) :
    IsCharpolyNormMixedOfWeightLE q ι b
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p n hcard
        (LAdicSheaf.representationSheaf B X x T hT) i).hom := by
  have := compactSpace_etaleFundamentalGroup X.1 x
  obtain ⟨P, T₁, hT₁, hT₁map, hT₁J, hT₁K⟩ := hs.exists_integral_conj T hT α hα γ hγ hJ hK
  set e := canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x
  have hmodel : ∀ g, (integralModel T hT g).val.map (PadicInt.Coe.ringHom (p := ℓ)) =
      ((exists_conj_integral T hT).choose⁻¹ * T g * (exists_conj_integral T hT).choose).val :=
    fun g => congrArg Units.val (map_integralModel T hT g)
  have h1 : ∀ g, (1 : Matrix (Fin r) (Fin r) ℚ_[ℓ]) * (T g).val = (T g).val * 1 := by simp
  obtain ⟨hT₁d, hT₁w⟩ := isCharpolyNormMixedOfWeightLE_representationLAdicSheaf_of_map_eq B X x e
    f j kbar p n hcard hT₁ (continuous_integralModel T hT) P _ hT₁map hmodel 1 h1 1 h1
    (Matrix.mul_one 1) i hTd
  obtain ⟨_, hTw⟩ := isCharpolyNormMixedOfWeightLE_representationLAdicSheaf_of_map_eq B X x e f j
    kbar p n hcard (continuous_integralModel T hT) hT₁ _ P hmodel hT₁map 1 h1 1 h1
    (Matrix.mul_one 1) i hT₁d
  refine hTw ?_
  have hJ₁ : ∀ g, J * (integralModel α hα g).val = (T₁ g).val * J := fun g => (hT₁J g).symm
  have hK₁ : ∀ g, K * (T₁ g).val = (integralModel γ hγ g).val * K := hT₁K
  set φ := representationLAdicSheafMap B X x e (continuous_integralModel α hα) hT₁ J hJ₁
  set ψ := representationLAdicSheafMap B X x e hT₁ (continuous_integralModel γ hγ) K hK₁
  have hw : ∀ m, LAdicSheaf.padicLevelMap φ m ≫ LAdicSheaf.padicLevelMap ψ m = 0 := fun m => by
    rw [← LAdicSheaf.padicLevelMap_comp, ← representationLAdicSheafMap_mul,
      representationLAdicSheafMap_eq_of_eq B X x e _ _ _ (fun g => by simp) hs.comp_zero,
      representationLAdicSheafMap_zero, LAdicSheaf.padicLevelMap_zero]
  have hS : ∀ m, (ShortComplex.mk _ _ (hw m)).ShortExact := fun m =>
    shortExact_padicLevelMap_representationLAdicSheafMap B X x (continuous_integralModel α hα) hT₁
      (continuous_integralModel γ hγ) J hJ₁ K hK₁
      (fun k => (hs.map (PadicInt.toZModPow k)).mulVec_injective)
      (fun k => (hs.map (PadicInt.toZModPow k)).mulVec_surjective)
      (fun k => (hs.map (PadicInt.toZModPow k)).exact) m (hw m)
  exact LAdicSheaf.isCharpolyNormMixedOfWeightLE_of_shortExact p n hcard φ ψ hw hS i hfin
    (h₁ := hαd) (h₃ := hγd) hαw hγw

end Stacks.EtaleCohomology

end
