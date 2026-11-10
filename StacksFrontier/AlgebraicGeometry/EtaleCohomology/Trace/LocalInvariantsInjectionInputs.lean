module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsWeightsOfInjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportConnectingMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupportFunctoriality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationFunctoriality

/-!
# The inputs of `H⁰_loc ⊆ H¹_c` (Weil II 1.8)

The injection of the local invariants at a missing point `y` of a curve `V ⊆ W ⊆ 𝔸¹_k` into
`H¹_c(V_k̄, ℱ_τ ⊗ ℚ_ℓ)`, `Stacks.EtaleCohomology.CurveLocalInvariantsInjectionInput`, comes from
the connecting map of `0 → j_! j⁻¹ j_* ℱₙ → j_* ℱₙ → i_* i⁻¹ j_* ℱₙ → 0` on `W`
(`Stacks.EtaleCohomology.compactSupportSheafδ`). Besides that, it needs three geometric facts,
stated here as propositions.

* `Stacks.EtaleCohomology.AffineCurveDirectImageCompactSupportZeroInput`:
  `H⁰_c(W_k̄, j_* G) = 0` for `W` a smooth affine curve and `G` locally constant on a dense open
  `V` with `V_k̄` connected. This makes the connecting map injective.
* `Stacks.EtaleCohomology.ClosedPartStalkCompactSupportInput`: the stalk at the geometric point
  over a closed point `y` of `Z` embeds into `H⁰_c(X_k̄, i_* i⁻¹ -)`, naturally, carrying the
  geometric Frobenius of `κ(y)` to `(π_X^*) ^ deg y`.
* `Stacks.EtaleCohomology.CurvePointInertiaStalkInput`: the stalk at `ȳ` of `j_*` of the levels
  of `ℱ_{ρ₀}` is the module of `ρ₀`-invariants of the inertia `curvePointInertia` at `y`, level by
  level and compatibly with the transition maps, with the intertwiners and with the geometric
  Frobenius `ρ₀(φ Fr⁻¹)`.

These propositions are not registered and are not hypotheses of any registered statement.

The standard model `HasDerivedCategory.standard` is used because compactly supported cohomology is
defined there.

## Main definitions

* `Stacks.EtaleCohomology.AffineCurveDirectImageCompactSupportZeroInput`
* `Stacks.EtaleCohomology.ClosedPartStalkCompactSupportInput`
* `Stacks.EtaleCohomology.CurvePointInertiaStalkInput`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.Scheme
open scoped Pointwise Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-- **`H⁰_c(W_k̄, j_* G) = 0`** for a smooth affine curve `W` over a finite field, an open
immersion `j : V ⟶ W` with `V_k̄` connected, and a finite type locally constant sheaf `G` of
`Λ`-modules on `V`: a compactly supported section of `j_* G` vanishes at a point at infinity of
`W`, hence everywhere. -/
public def AffineCurveDirectImageCompactSupportZeroInput : Prop :=
  ∀ {k : Type u} [Field k] [Fintype k] {W V : Scheme.{u}} (fW : W ⟶ Spec (.of k))
    [IsCurve k fW] [Smooth fW] [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW]
    [IsAffine W] (jWb : CompactificationOf (Over.mk fW)) (kbar : Type u) [Field kbar]
    [IsAlgClosed kbar] [Algebra k kbar] (jW : V ⟶ W) [IsOpenImmersion jW] [Nonempty V]
    [ConnectedSpace ↥(Limits.pullback (jW ≫ fW)
      (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (Λ : Type) [CommRing Λ] (G : EtaleModules.{u, 0} Λ V),
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ V.smallEtaleTopology G →
      IsZero ((compactSupportSheafCohomology Λ fW jWb kbar 0).obj
        ((etaleModuleDirectImage.{u, 0} Λ jW).obj G))

/-- **The stalk at a closed point of `Z` embeds into `H⁰_c(X_k̄, i_* i⁻¹ -)`**, naturally in the
sheaf, carrying the geometric Frobenius of `κ(y)` on the stalk to `(π_X^*) ^ deg y`, where
`#κ(y) = (#k) ^ deg y`. -/
public def ClosedPartStalkCompactSupportInput : Prop :=
  ∀ {k : Type u} [Field k] [Fintype k] {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ n)
    (iZ : Z ⟶ X) [IsClosedImmersion iZ] [IsReduced Z] [IsFinite (iZ ≫ f)]
    (y : X) (_ : y ∈ Set.range iZ.base) [Finite (X.residueField y)] (Λ : Type) [CommRing Λ],
    ∃ (dy : ℕ) (_ : 0 < dy) (_ : Nat.card (X.residueField y) = (p ^ n) ^ dy)
      (s : (Scheme.pointSmallEtale (Stacks.Frobenius.geometricPointAt X y).hom).sheafFiber ⟶
        etaleModuleClosedPart Λ iZ ⋙ compactSupportSheafCohomology Λ f j kbar 0),
      (∀ G, Function.Injective (s.app G).hom) ∧
      ∀ G, (s.app G).hom ∘ₗ (Stacks.Frobenius.frobeniusStalk (ModuleCat.{u + 1} Λ) X y G).hom =
        (((compactSupportSheafFrobenius Λ f j kbar p n hcard 0).app
          ((etaleModuleClosedPart Λ iZ).obj G)).hom ^ dy) ∘ₗ (s.app G).hom

/-- **The stalk at a missing point of `j_*` of the levels of `ℱ_{ρ₀}` is the module of inertia
invariants** (Weil II 1.8, `H⁰_loc`), in the setting of
`Stacks.EtaleCohomology.CurveLocalInvariantsInjectionInput`, for an integral continuous
`ρ₀ : π₁(V, x̄) → GL_r(ℤ_ℓ)`. Level by level there are injective additive maps
`εₙ : (j_* ℱₙ)_ȳ → (ℤ/ℓⁿ⁺¹)^r`, `ℤ_ℓ`-semilinear, compatible with the transition maps, with the
morphisms induced by the intertwiners of `ρ₀` and with the geometric Frobenius `ρ₀(φ Fr⁻¹)`.
Every reduction of a `curvePointInertia`-invariant vector of `ℤ_ℓ^r` lies in their images. -/
public def CurvePointInertiaStalkInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (V : B.Scheme) (ℓ : ℕ)
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
    (k : Type u) [Field k] [Fintype k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p : ℕ) [Fact p.Prime] [CharP k p] (_ : ℓ ≠ p)
    -- the curve `W ⊇ V` and the missing point `y`
    (W : B.Scheme) (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW]
    [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
    (eW : W.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion eW]
    (_ : eW ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = fW)
    (jW : V.1 ⟶ W.1) [IsOpenImmersion jW]
    (_ : jW ≫ fW = f) (y : W.1) (_ : IsClosed ({y} : Set W.1)) (_ : y ∉ Set.range jW.base)
    (hy : jW.base (genericPoint V.1) ⤳ y)
    -- the local field at `y`
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (V.1.residueField (genericPoint V.1)) L]
    [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
    [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
    [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (V.1.residueField (genericPoint V.1))]
    [IsFractionRing A (V.1.residueField (genericPoint V.1))] [Algebra A L]
    [IsScalarTower A (V.1.residueField (genericPoint V.1)) L]
    [Finite (IsLocalRing.ResidueField A)]
    (eA : A ≃+* W.1.presheaf.stalk y)
    (_ : ∀ a : A, algebraMap A (V.1.residueField (genericPoint V.1)) a =
      (curveLocalRingToFunctionField jW hy).hom (eA a))
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (Fr : Gal(L / V.1.residueField (genericPoint V.1)))
    (_ :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    (r : ℕ) (ρ₀ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀) [Finite (W.1.residueField y)],
    letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
      (integralClosure A L)
    let x : GeometricPoint V.1 := (algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1))
    let ℱ : LAdicSheaf.{u, u + 1} B V ℓ := representationLAdicSheaf B V x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V x) ρ₀ hρ₀
    let stalk : Sheaf W.1.smallEtaleTopology (ModuleCat.{u + 1} ℤ_[ℓ]) ⥤ ModuleCat.{u + 1} ℤ_[ℓ] :=
      (Scheme.pointSmallEtale (Stacks.Frobenius.geometricPointAt W.1 y).hom).sheafFiber
    let D : Sheaf (SmallEtale.topology B V.1 V.2) (ModuleCat.{u + 1} ℤ_[ℓ]) ⥤
        Sheaf W.1.smallEtaleTopology (ModuleCat.{u + 1} ℤ_[ℓ]) :=
      (SmallEtale.sheafEquiv B V.1 V.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor ⋙
        etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jW
    ∃ ε : ∀ n : ℕ, (stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))) →+
        (Fin r → ZMod (ℓ ^ (n + 1))),
      (∀ n, Function.Injective (ε n)) ∧
      (∀ n (c : ℤ_[ℓ]) (w : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))),
        ε n (c • w) = PadicInt.toZModPow (n + 1) c • ε n w) ∧
      (∀ n (w : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ (n + 1)))),
        ε n ((stalk.map (D.map (LAdicSheaf.padicTransition B V ℓ ℱ n))).hom w) = fun i =>
          ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))
            (ε (n + 1) w i)) ∧
      (∀ (M : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (hM : ∀ g, M * (ρ₀ g).val = (ρ₀ g).val * M) n
        (w : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))),
        ε n ((stalk.map (D.map (LAdicSheaf.padicLevelMap
            (representationLAdicSheafMap B V x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V x) hρ₀ hρ₀ M hM)
            n))).hom w) =
          (M.map (PadicInt.toZModPow (n + 1))) *ᵥ ε n w) ∧
      (∀ n (w : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))),
        ε n ((Stacks.Frobenius.frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ]) W.1 y
            (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))).hom w) =
          ((ρ₀ ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹)).val.map
            (PadicInt.toZModPow (n + 1))) *ᵥ ε n w) ∧
      ∀ v : Fin r → ℤ_[ℓ],
        (∀ σ ∈ Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P, (ρ₀ σ).val *ᵥ v = v) →
          ∀ n, (fun i => PadicInt.toZModPow (n + 1) (v i)) ∈ Set.range (ε n)

end Stacks.EtaleCohomology
