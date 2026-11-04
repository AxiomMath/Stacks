module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocalTermsSmoothBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocalTermsKilledByIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationBasePoint

/-!
# The local terms at infinity of `ℱ_τ` built at any base point

`Stacks.EtaleCohomology.LAdicSheaf.exists_localTermsKilledBy_of_smooth` bounds the local terms at
the boundary of `ℱ_τ` for `τ` a representation of `π₁(V, η̄)` at the geometric generic point. For
`τ` at an arbitrary geometric point `x̄` of `V`, an isomorphism of fibre functors `t : F_x̄ ≅ F_η̄`
identifies `ℱ_τ` with `ℱ_{τ ∘ φ_t}` built at `η̄`
(`Stacks.EtaleCohomology.representationLAdicSheafBasePointIso`); if the inertia groups at infinity
fix no nonzero vector of `τ ∘ φ_t`, one power of `ℓ` kills the local terms of `ℱ_τ`
(`Stacks.EtaleCohomology.LAdicSheaf.exists_localTermsKilledBy_of_basePoint`). This is how Poincaré
duality is applied to the fibres of the Fourier family, whose representations are given at a
geometric point over the base point of `σ` ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.exists_localTermsKilledBy_of_basePoint`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (V : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B V.1 V.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian V.1] [Fact ℓ.Prime] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
  (k : Type u) [Field k] [Finite k] (f : V.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar]
  [IsCurve kbar (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))]
  (p : ℕ) [Fact p.Prime] [CharP k p]

include ℓ in
/-- **The local terms at infinity of `ℱ_τ` for `τ` at any base point.** For a smooth affine curve
`V` over a finite field with a compactification `j` such that `X̄_k̄` is a smooth curve, `ℓ ≠ p`,
and `τ : π₁(V, x̄) → GL_r(ℚ_ℓ)` continuous: if for every separable closure `L` and algebraic
closure `Ω` of the function field, every isomorphism `t` of fibre functors from `x̄` to the
geometric generic point and every place `(A, P)` at infinity, the inertia group of `P` fixes no
nonzero vector of `τ ∘ φ_t`, then one power `ℓ ^ K` kills the local terms of `ℱ_τ`. -/
theorem LAdicSheaf.exists_localTermsKilledBy_of_basePoint
    (h : LAdicSheaf.LocalTermsSmoothBoundaryStalkInput.{u}) (hℓp : ℓ ≠ p)
    (x : GeometricPoint V.1) {r : ℕ} (τ : EtaleFundamentalGroup V.1 x →* GL (Fin r) ℚ_[ℓ])
    (hτ : Continuous τ)
    (hinv : ∀ (L Ω : Type u) [Field L] [Field Ω]
      [Algebra (V.1.residueField (genericPoint V.1)) L]
      [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
      [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
      [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
      [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
      (t : finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor ((algebraicClosureGeometricPoint
        (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1))))
      (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [Algebra A (V.1.residueField (genericPoint V.1))]
      [IsFractionRing A (V.1.residueField (genericPoint V.1))] [Algebra A L]
      [IsScalarTower A (V.1.residueField (genericPoint V.1)) L]
      (P : Ideal (integralClosure A L)) [P.IsMaximal],
      (∃ a : Γ(V.1, ⊤), (V.1.evaluation ⊤ (genericPoint V.1) trivial).hom a ∉
        Set.range (algebraMap A (V.1.residueField (genericPoint V.1)))) →
      Representation.invariants ((matrixRepresentation
        (τ.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom)).comp
          (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype) = ⊥) :
    ∃ K : ℕ, LAdicSheaf.LocalTermsKilledBy B V ℓ f j kbar
      (LAdicSheaf.representationSheaf B V x τ hτ) K := by
  let Kf := V.1.residueField (genericPoint V.1)
  let Ω := AlgebraicClosure Kf
  let L := ↥(separableClosure Kf Ω)
  let η := (algebraicClosureGeometricPoint Kf Ω).map (V.1.fromSpecResidueField (genericPoint V.1))
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso_of_connectedSpace V.1 x η
  have := compactSpace_etaleFundamentalGroup V.1 x
  let φ := etaleFundamentalGroupBasePointHom t
  let ρ₀ := (integralModel τ hτ).comp φ.toMonoidHom
  have hρ₀ : Continuous ρ₀ := (continuous_integralModel τ hτ).comp φ.continuous
  obtain ⟨K, hK⟩ := LAdicSheaf.exists_localTermsKilledBy_of_smoothBoundary B V ℓ k f j kbar p hℓp
    L Ω r h ρ₀ hρ₀ (by
      intro A _ _ _ _ _ _ _ P _ _ hℓA hA
      let := IsIntegralClosure.MulSemiringAction A Kf L (integralClosure A L)
      refine exists_inertiaLevelsKilledBy_inertia A _ L P hℓA _
        (hρ₀.comp (galoisToFundamentalGroup V.1 L Ω).continuous) ?_
      intro v hv
      obtain ⟨Pm, hPm⟩ : ∃ Pm : GL (Fin r) ℚ_[ℓ], ∀ g, Matrix.GeneralLinearGroup.map
          (PadicInt.Coe.ringHom (p := ℓ)) (integralModel τ hτ g) = Pm⁻¹ * τ g * Pm :=
        ⟨_, map_integralModel τ hτ⟩
      let φQ : ℤ_[ℓ] →+* ℚ_[ℓ] := PadicInt.Coe.ringHom
      let vQ : Fin r → ℚ_[ℓ] := φQ ∘ v
      have hfix : ∀ g : EtaleFundamentalGroup V.1 x,
          ((integralModel τ hτ g : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v →
          ((τ g : GL (Fin r) ℚ_[ℓ]) : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ
            ((Pm : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ vQ) =
              (Pm : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ vQ := by
        intro g hg
        have h2 := hPm g
        have hmapv : ((Matrix.GeneralLinearGroup.map φQ (integralModel τ hτ g) : GL (Fin r) ℚ_[ℓ]) :
            Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ vQ = vQ := by
          show φQ.mapMatrix ((integralModel τ hτ g : GL (Fin r) ℤ_[ℓ]) :
            Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ (φQ ∘ v) = φQ ∘ v
          funext i
          rw [RingHom.mapMatrix_apply, ← RingHom.map_mulVec, hg]
          rfl
        have hτg : τ g * Pm = Pm * Matrix.GeneralLinearGroup.map φQ (integralModel τ hτ g) := by
          rw [h2]; group
        rw [mulVec_mulVec, ← Units.val_mul, hτg, Units.val_mul, ← mulVec_mulVec, hmapv]
      have hmem : (Pm : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ vQ ∈ Representation.invariants
          ((matrixRepresentation (τ.comp φ.toMonoidHom)).comp
            (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype) := by
        rw [Representation.mem_invariants]
        rintro ⟨g, hg⟩
        obtain ⟨σ, hσ, rfl⟩ :=
          (Stacks.FundamentalGroup.mem_curvePointInertia_iff V.1 L Ω A P g).1 hg
        rw [MonoidHom.comp_apply, Subgroup.coe_subtype, matrixRepresentation_apply]
        exact hfix _ (hv σ hσ)
      rw [hinv L Ω t A P hA, Submodule.mem_bot] at hmem
      have hvQ : vQ = 0 := by
        have := congrArg (fun y => ((Pm⁻¹ : GL (Fin r) ℚ_[ℓ]) : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ y)
          hmem
        simpa [mulVec_mulVec, ← Units.val_mul] using this
      funext i
      have := congrFun hvQ i
      exact PadicInt.coe_eq_zero.1 this)
  exact ⟨K, LAdicSheaf.LocalTermsKilledBy.of_iso
    (representationLAdicSheafBasePointIso B V t (continuous_integralModel τ hτ)).symm hK⟩

end Stacks.EtaleCohomology

end
