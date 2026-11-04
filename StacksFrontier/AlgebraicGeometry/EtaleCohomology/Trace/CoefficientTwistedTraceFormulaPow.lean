module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientTwistedTraceFormulaStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedTraceFormulaPow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TwistedTraceTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationInverseImage
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperCohomologicalDimension.GeometricFibres
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicVanishingAbsolute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparableClosure

/-!
# The twisted trace formula for `c ∘ (π_X^*)^N` on the sheaf of `σ : π₁ → GL_m(O)`

Let `σ : π₁(X, x̄) → GL_m(O)` be continuous, `O` finite free over `ℤ_ℓ`, `X` geometrically
connected, separated of finite type and of dimension at most one over a finite field `k`, and
`ℓ ≠ p`. For `c ∈ O` and `N ≥ 1`,

```
∑_{deg x ∣ N} deg x · Tr_{O/ℤ_ℓ}(c · tr σ(F_x)^{N / deg x})
  = ∑ᵢ (-1)ⁱ Tr(c ∘ (π_X^*)^N | Hⁱ_c(X_k̄, ℱ_σ) ⊗ ℚ_ℓ).
```

Over a finite extension `k'` of `k`, a geometric point `x̄'` of `X' = X ×_k k'` over `x̄` exists,
and `g⁻¹ℱ_σ ≅ ℱ_{σ ∘ g_*}` compatibly with `c`
(`Stacks.EtaleCohomology.representationLAdicSheafInverseImageHom_naturality`); the twisted trace
formula for `ℱ_{σ ∘ g_*}` on `X'`
(`Stacks.EtaleCohomology.finsum_trace_coefficientScalar_comp_rationalStalkFrobenius`) is therefore
the one for `g⁻¹ℱ_σ`, and
`Stacks.EtaleCohomology.LAdicSheaf.finsum_trace_comp_pow_eq_of_traceFormula` applies.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.

## Main results

* `Stacks.EtaleCohomology.exists_geometricPoint_map_pullback_fst`
* `Stacks.EtaleCohomology.alternating_trace_coefficientScalar_comp_pow`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- **A geometric point lifts along `X ×_k k' ⟶ X`** for a finite extension `k'` of `k`. -/
public theorem exists_geometricPoint_map_pullback_fst {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (k' : Type u) [Field k'] [Algebra k k'] [Module.Finite k k']
    (x : GeometricPoint X) :
    ∃ x' : GeometricPoint (pullback f (specAlgebraMap k k')),
      x'.map (pullback.fst f (specAlgebraMap k k')) = x := by
  let Ω := x.residueField
  let xh := x.hom
  let φ₀ := Spec.preimage (xh ≫ f)
  let : Algebra k Ω := φ₀.hom.toAlgebra
  let τ : k' →ₐ[k] Ω := IsAlgClosed.lift
  have hcomm : xh ≫ f = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ specAlgebraMap k k' := by
    rw [specAlgebraMap, ← Spec.map_comp]
    have h₁ : CommRingCat.ofHom (algebraMap k k') ≫ CommRingCat.ofHom τ.toRingHom = φ₀ := by
      ext a
      exact τ.commutes a
    rw [h₁, Spec.map_preimage]
  refine ⟨⟨Ω, pullback.lift xh (Spec.map (CommRingCat.ofHom τ.toRingHom)) hcomm⟩, ?_⟩
  show GeometricPoint.mk x.residueField (pullback.lift xh _ hcomm ≫ pullback.fst f _) = x
  rw [pullback.lift_fst]

variable {ℓ : ℕ} [Fact ℓ.Prime] {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] {d : ℕ}
  (b : Module.Basis (Fin d) ℤ_[ℓ] O) {m : ℕ}
  (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  (σ : EtaleFundamentalGroup X.1 x →* GL (Fin m) O)
  (hρ : Continuous ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ))
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (J : CompactificationOf (Over.mk f)) (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [Algebra.IsAlgebraic k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (hcard : Fintype.card k = p ^ q)

local notation "e₀" => canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x

omit [Fintype k] [CharP k p] in
/-- **The twisted trace formula for `ℱ_σ` over every finite extension of `k`**, in the form of the
hypothesis of `Stacks.EtaleCohomology.LAdicSheaf.finsum_trace_comp_pow_eq_of_traceFormula`. -/
public theorem coefficientScalar_traceFormula_fieldExtension [Module.Free ℤ_[ℓ] O]
    [Module.Finite ℤ_[ℓ] O] (hℓp : ℓ ≠ p) (hdim : topologicalKrullDim X.1 ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hgc : GeometricallyConnected f) (c : O)
    (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Module.Finite k k']
    [Algebra k' kbar] [IsScalarTower k k' kbar] [CharP k' p]
    [IsNoetherian (fieldExtensionScheme B X f k').1] (q' : ℕ)
    (hcard' : Fintype.card k' = p ^ q') :
    ∑ᶠ (y : closedPoints (fieldExtensionScheme B X f k').1)
        (_ : residueDegree (pullback.snd f (specAlgebraMap k k')) y.1 = 1),
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkMap (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k')
              (representationLAdicSheafMap B X x e₀ hρ hρ (coefficientScalarRingHom b m c)
                (fun g => coefficientScalarRingHom_commute b m c (σ g).val)))
              (geometricPointAt _ y.1) ∘ₗ
            LAdicSheaf.rationalStalkFrobenius B (fieldExtensionScheme B X f k') ℓ
            (LAdicSheaf.inverseImage (fieldExtensionProj B X f k')
              (representationLAdicSheaf B X x e₀
                ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ)) y.1
            (finite_residueField (pullback.snd f (specAlgebraMap k k')) y.1 y.2) ^ 1) =
      ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _
        (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
            (LAdicSheaf.geometricCompactlySupportedCohomologyMap
              (X := fieldExtensionScheme B X f k') (pullback.snd f (specAlgebraMap k k'))
              (compactificationFieldBaseChange f J k') kbar
              (LAdicSheaf.inverseImageMap (fieldExtensionProj B X f k')
                (representationLAdicSheafMap B X x e₀ hρ hρ (coefficientScalarRingHom b m c)
                  (fun g => coefficientScalarRingHom_commute b m c (σ g).val))) i)).hom ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B
            (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
            (compactificationFieldBaseChange f J k') kbar p q' hcard'
            (LAdicSheaf.inverseImage (fieldExtensionProj B X f k')
              (representationLAdicSheaf B X x e₀
                ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ)) i).hom) := by
  have : Algebra.IsAlgebraic k' kbar := Algebra.IsAlgebraic.tower_top (K := k) k'
  let s := specAlgebraMap k k'
  have : ConnectedSpace (fieldExtensionScheme B X f k').1 :=
    hgc.geometrically_connectedSpace s (pullback.fst f s) (pullback.snd f s)
      (IsPullback.of_hasPullback f s)
  have hdim' : topologicalKrullDim (fieldExtensionScheme B X f k').1 ≤ 1 := by
    exact_mod_cast topologicalKrullDim_pullback_le_of_fiber f ((1 : ℕ) : WithBot ℕ∞)
      (fun y ↦ (topologicalKrullDim_fiber_of_spec_field k f y).le.trans hdim) s
  obtain ⟨x', rfl⟩ := exists_geometricPoint_map_pullback_fst f k' x
  let g := fieldExtensionProj B X f k'
  let ρ := (Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ
  let φ := (etaleFundamentalGroupMap g.hom x').toMonoidHom
  let σ' := σ.comp φ
  have hρ' : Continuous ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ') :=
    hρ.comp (etaleFundamentalGroupMap g.hom x').continuous
  let β := (nonempty_pullback_inverse_iso B g x').some
  let Φ := asIso (representationLAdicSheafInverseImageHom B g x' β ρ hρ)
  have hΦ := representationLAdicSheafInverseImageHom_naturality B g x' β ρ hρ hρ
    (coefficientScalarRingHom b m c) (fun g => coefficientScalarRingHom_commute b m c (σ g).val)
  have h2 := finsum_trace_coefficientScalar_comp_rationalStalkFrobenius b B
    (fieldExtensionScheme B X f k') x' σ' hρ' (pullback.snd f (specAlgebraMap k k'))
    (compactificationFieldBaseChange f J k') kbar p q' hcard' hℓp hdim' c
  refine Eq.trans (finsum_congr fun y => finsum_congr fun _ =>
    LAdicSheaf.trace_rationalStalkMap_comp_rationalStalkFrobenius_of_iso Φ _ _ hΦ y.1 _ 1)
    (h2.trans (finsum_congr fun i => congrArg (fun z => (if Even i then (1 : ℚ_[ℓ]) else -1) * z)
      ?_))
  have h3 := LAdicSheaf.trace_rationalMap_comp_rationalFrobenius_pow_of_iso
    (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f J k') kbar p q' hcard'
    Φ _ _ hΦ i 1
  rw [pow_one, pow_one] at h3
  exact h3.symm

/-- **The twisted trace formula for `c ∘ (π_X^*)^N` on the sheaf of `σ : π₁ → GL_m(O)`**: for `X`
geometrically connected of dimension at most one over `k`, `ℓ ≠ p`, `c ∈ O` and `N ≥ 1`,
`∑_{deg x ∣ N} deg x · Tr_{O/ℤ_ℓ}(c · tr σ(F_x)^{N / deg x}) =
∑ᵢ (-1)ⁱ Tr(c ∘ (π_X^*)^N | Hⁱ_c(X_k̄, ℱ_σ) ⊗ ℚ_ℓ)`. -/
public theorem alternating_trace_coefficientScalar_comp_pow [Module.Free ℤ_[ℓ] O]
    [Module.Finite ℤ_[ℓ] O] (hℓp : ℓ ≠ p) (hdim : topologicalKrullDim X.1 ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hgc : GeometricallyConnected f) (c : O) (N : ℕ) (hN : N ≠ 0) :
    ∑ᶠ (y : closedPoints X.1) (_ : residueDegree f y.1 ∣ N), (residueDegree f y.1 : ℚ_[ℓ]) *
        algebraMap ℤ_[ℓ] ℚ_[ℓ] (Algebra.trace ℤ_[ℓ] O
          (c * ((σ (geometricFrobeniusFamily f x y)).val ^ (N / residueDegree f y.1)).trace)) =
      ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _
        (((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
            (LAdicSheaf.geometricCompactlySupportedCohomologyMap f J kbar
              (representationLAdicSheafMap B X x e₀ hρ hρ (coefficientScalarRingHom b m c)
                (fun g => coefficientScalarRingHom_commute b m c (σ g).val)) i)).hom ∘ₗ
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f J kbar p q hcard
            (representationLAdicSheaf B X x e₀
              ((Units.map (coefficientMatrixRingHom b m).toMonoidHom).comp σ) hρ) i).hom ^ N) := by
  refine Eq.trans (finsum_congr fun y => finsum_congr fun _ => congrArg (fun z =>
    (residueDegree f y.1 : ℚ_[ℓ]) * z)
    (trace_rationalStalkMap_coefficientScalar_comp_rationalStalkFrobenius_pow B X x b σ hρ f c y
      (N / residueDegree f y.1)).symm) ?_
  exact LAdicSheaf.finsum_trace_comp_pow_eq_of_traceFormula B X ℓ f J kbar p q hcard _ _
    (fun k' _ _ _ _ _ _ _ _ q' hcard' => coefficientScalar_traceFormula_fieldExtension b B X x σ hρ
      f J kbar p hℓp hdim hgc c k' q' hcard') N hN

end Stacks.EtaleCohomology

end
