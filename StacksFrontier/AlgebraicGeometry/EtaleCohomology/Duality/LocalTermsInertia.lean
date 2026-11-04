module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.BoundaryLocalTerms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TameInertiaLevelBounds
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankinTraceFormula
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.CurvePointInertia
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationSheaf

/-!
# The local terms at infinity of `ℱ_τ` on a curve are bounded when inertia has no invariants

Let `V` be a smooth affine curve over a finite field `k`, `j : V ⟶ X̄` a compactification,
`k̄` an algebraic closure of `k` and `τ : π₁(V, η̄) → GL_r(ℚ_ℓ)` continuous, `ℓ ≠ char k`. If at
every place of the function field `K` of `V` at infinity (a discrete valuation ring `A` of `K`
not containing all functions on `V`) the inertia group fixes no nonzero vector of `ℚ_ℓ ^ r`,
then the local terms of `ℱ_τ` at the boundary are killed by one power `ℓ ^ K`
(`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy`): this is
`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsInertiaInput`.

The proof splits into an algebraic and a geometric half.

* Algebraic (proved here): for a place `(A, P)` with finite residue field of characteristic
  `≠ ℓ`, the inertia group `I_P` has the `ℓ`-adic tame character
  (`Stacks.FundamentalGroup.exists_ladicTameCharacter`), so
  `Stacks.EtaleCohomology.exists_forall_levelInvariants_and_levelCocycles_killed` bounds
  `H⁰(I_P, Mₙ)` and `H¹(I_P, Mₙ)` uniformly in `n`, `Mₙ` the levels of an integral model of `τ`
  (`Stacks.EtaleCohomology.exists_inertiaLevelsKilledBy_inertia`).
* Geometric (`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsStalkInput`, a named input): the
  stalks of `j'_* Fₙ` and of `R¹j'_* Fₙ` at a geometric point at infinity of `X̄_k̄` are
  (finite sums over the branches there of) `H⁰(I_P, Mₙ)` and `H¹(I_P, Mₙ)` — Stacks 03Q9 for the
  strict henselization, whose generic fibre is the spectrum of the fraction field `K^{sh}` with
  absolute Galois group `I_P`, and Stacks 03QU; the boundary is finite; so uniform per-place
  bounds give one bound for the sheaves.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsInertiaInput` — the statement consumed by the
  Poincaré duality development.
* `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsStalkInput` — the geometric input.

## Main results

* `Stacks.EtaleCohomology.exists_inertiaLevelsKilledBy_inertia`.
* `Stacks.EtaleCohomology.LAdicSheaf.localTermsInertiaInput_of_localTermsStalkInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Matrix

universe u v w

namespace Stacks.EtaleCohomology

/-- **Uniform level bounds at the inertia group of a place.** For a discrete valuation ring `A`
with finite residue field of characteristic `≠ ℓ`, fraction field `K`, a separable closure `L`
of `K`, a place `P` of `L` over `A` and a continuous `ρ : Gal(L/K) → GL_r(ℤ_ℓ)` whose inertia
group `I_P` fixes no nonzero vector, one power of `ℓ` kills `H⁰(I_P, Mₙ)` and `H¹(I_P, Mₙ)` for
all levels `Mₙ = (ℤ/ℓⁿ⁺¹) ^ r` of `ρ`. -/
theorem exists_inertiaLevelsKilledBy_inertia {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [IsSepClosure K L]
    [Algebra A L] [IsScalarTower A K L]
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    [Finite (IsLocalRing.ResidueField A)]
    (hℓ : ℓ ≠ ringChar (IsLocalRing.ResidueField A))
    (ρ : Gal(L/K) →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ) :
    letI := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
    (∀ v : Fin r → ℤ_[ℓ], (∀ σ ∈ P.inertia Gal(L/K),
      (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v) → v = 0) →
    ∃ e : ℕ, InertiaLevelsKilledBy (P.inertia Gal(L/K)) ρ e := by
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  intro hinv
  have : IsGalois K L := IsSepClosure.isGalois
  obtain ⟨t, ht, htame, -, -⟩ := Stacks.FundamentalGroup.exists_ladicTameCharacter A K L P ℓ hℓ
  exact exists_inertiaLevelsKilledBy (P.inertia Gal(L/K)) (isClosed_inertia A K L P) t ht htame
    ρ hρ hinv

/-- **The geometric input: per-place bounds on inertia cohomology bound the local terms.** For a
smooth affine curve `V` over a finite field `k` of characteristic `p ≠ ℓ`, a compactification
`j : V ⟶ X̄`, an algebraic closure `k̄` of `k` and a continuous `ρ₀ : π₁(V, η̄) → GL_r(ℤ_ℓ)`:
if at every place `(A, P)` of the function field `K` at infinity (a discrete valuation ring `A` of
`K` some function on `V` is not in) with finite residue field of characteristic `≠ ℓ`, some power
`ℓ ^ e` kills `H⁰(I_P, Mₙ)` and `H¹(I_P, Mₙ)` for all levels `Mₙ` of `ρ₀`
(`Stacks.EtaleCohomology.InertiaLevelsKilledBy`), then one power of `ℓ` kills the local terms of
`ℱ_{ρ₀}` at the boundary.

Mathematically: the stalks of `j'_* Fₙ` and `R¹j'_* Fₙ` at a geometric point `s̄` of
`X̄_k̄ ∖ V_k̄` are `H⁰` and `H¹` of `V ×_{X̄} Spec 𝒪^{sh}_{X̄, s̄} = ∐ Spec K^{sh}_i` (Stacks 03Q9,
the strict henselization of `X̄_k̄` at `s̄` being that of `X̄` at its image), one field for each
branch of `X̄` there, each a place of `K` at infinity whose absolute Galois group is an inertia
group `I_P`; by Stacks 03QU these are `⊕ H⁰(I_P, Mₙ)` and `⊕ H¹(I_P, Mₙ)` (continuous cocycles);
away from the boundary both sheaves vanish; the boundary has finitely many points, and stalks
detect `ℓ ^ K • 𝟙 = 0`. This proposition is not registered and is not a hypothesis of any
registered statement. -/
public def LAdicSheaf.LocalTermsStalkInput : Prop :=
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
    (k : Type u) [Field k] [Finite k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p : ℕ) [Fact p.Prime] [CharP k p] (_ : ℓ ≠ p)
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (V.1.residueField (genericPoint V.1)) L]
    [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
    [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
    [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
    (r : ℕ) (ρ₀ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀),
    (∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [Algebra A (V.1.residueField (genericPoint V.1))]
      [IsFractionRing A (V.1.residueField (genericPoint V.1))] [Algebra A L]
      [IsScalarTower A (V.1.residueField (genericPoint V.1)) L]
      (P : Ideal (integralClosure A L)) [P.IsMaximal] [Finite (IsLocalRing.ResidueField A)],
      ℓ ≠ ringChar (IsLocalRing.ResidueField A) →
      (∃ a : Γ(V.1, ⊤), (V.1.evaluation ⊤ (genericPoint V.1) trivial).hom a ∉
        Set.range (algebraMap A (V.1.residueField (genericPoint V.1)))) →
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      ∃ e : ℕ, InertiaLevelsKilledBy (P.inertia Gal(L / V.1.residueField (genericPoint V.1)))
        (ρ₀.comp (galoisToFundamentalGroup V.1 L Ω).toMonoidHom) e) →
    ∃ K : ℕ, LAdicSheaf.LocalTermsKilledBy B V ℓ f j kbar
      (representationLAdicSheaf B V ((algebraicClosureGeometricPoint
        (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V _) ρ₀ hρ₀) K

/-- **The local terms at infinity of `ℱ_τ` are bounded when inertia has no invariants** (Weil II
1.8; the hypothesis under which Poincaré duality on the affine curve `V` pairs `H¹_c` with
`H¹_c` of the dual). For a smooth affine curve `V` over a finite field `k` of characteristic
`p ≠ ℓ`, a compactification `j : V ⟶ X̄`, an algebraic closure `k̄` of `k`, and a continuous
`τ : π₁(V, η̄) → GL_r(ℚ_ℓ)` at the geometric generic point: if at every place `(A, P)` of the
function field at infinity (a discrete valuation ring `A` of `K` some function on `V` is not in)
the inertia group `Stacks.FundamentalGroup.curvePointInertia` fixes no nonzero vector, then one
power `ℓ ^ K` kills the local terms of `ℱ_τ` at the boundary
(`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsKilledBy`). The hypothesis is the first half of the
conclusion of `Stacks.ArtinSchreier.exists_forall_invariants_eq_bot_and_subsingleton_coinvariants`;
no hypothesis on coinvariants is needed. -/
public def LAdicSheaf.LocalTermsInertiaInput : Prop :=
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
    (k : Type u) [Field k] [Finite k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p : ℕ) [Fact p.Prime] [CharP k p] (_ : ℓ ≠ p)
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (V.1.residueField (genericPoint V.1)) L]
    [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
    [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
    [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
    (r : ℕ) (τ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℚ_[ℓ]) (hτ : Continuous τ),
    (∀ (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [Algebra A (V.1.residueField (genericPoint V.1))]
      [IsFractionRing A (V.1.residueField (genericPoint V.1))] [Algebra A L]
      [IsScalarTower A (V.1.residueField (genericPoint V.1)) L]
      (P : Ideal (integralClosure A L)) [P.IsMaximal],
      (∃ a : Γ(V.1, ⊤), (V.1.evaluation ⊤ (genericPoint V.1) trivial).hom a ∉
        Set.range (algebraMap A (V.1.residueField (genericPoint V.1)))) →
      Representation.invariants ((matrixRepresentation τ).comp
        (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype) = ⊥) →
    ∃ K : ℕ, LAdicSheaf.LocalTermsKilledBy B V ℓ f j kbar
      (LAdicSheaf.representationSheaf B V _ τ hτ) K

/-- **`LocalTermsInertiaInput` from the geometric input.** The integral model `ρ₀` of `τ`
(`Stacks.EtaleCohomology.integralModel`) is conjugate to `τ` over `ℚ_ℓ`, so the inertia groups
fix no nonzero vector of `ℤ_ℓ ^ r` under `ρ₀`, and
`Stacks.EtaleCohomology.exists_inertiaLevelsKilledBy_inertia` gives the per-place bounds that
`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsStalkInput` turns into the bound on the local
terms of `ℱ_τ = ℱ_{ρ₀}`. -/
theorem LAdicSheaf.localTermsInertiaInput_of_localTermsStalkInput
    (h : LAdicSheaf.LocalTermsStalkInput.{u}) : LAdicSheaf.LocalTermsInertiaInput.{u} := by
  intro B V ℓ i1 i2 i3 i4 i5 i6 i7 i8 k i9 i10 f i11 i12 i13 i14 j kbar i15 i16 i17 p i18 i19 hℓp
    L Ω i20 i21 i22 i23 i24 i25 i26 i27 i28 r τ hτ hinvτ
  have := compactSpace_etaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
    (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
  refine h B V ℓ k f j kbar p hℓp L Ω r (integralModel τ hτ) (continuous_integralModel τ hτ) ?_
  intro A _ _ _ _ _ _ _ P _ _ hℓA hA
  let := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
    (integralClosure A L)
  refine exists_inertiaLevelsKilledBy_inertia A _ L P hℓA _
    ((continuous_integralModel τ hτ).comp (galoisToFundamentalGroup V.1 L Ω).continuous) ?_
  intro v hv
  let x := (algebraicClosureGeometricPoint (V.1.residueField (genericPoint V.1)) Ω).map
    (V.1.fromSpecResidueField (genericPoint V.1))
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
      ((matrixRepresentation τ).comp
        (Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P).subtype) := by
    rw [Representation.mem_invariants]
    rintro ⟨g, hg⟩
    obtain ⟨σ, hσ, rfl⟩ := (Stacks.FundamentalGroup.mem_curvePointInertia_iff V.1 L Ω A P g).1 hg
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, matrixRepresentation_apply]
    exact hfix _ (hv σ hσ)
  rw [hinvτ A P hA, Submodule.mem_bot] at hmem
  have hvQ : vQ = 0 := by
    have := congrArg (fun y => ((Pm⁻¹ : GL (Fin r) ℚ_[ℓ]) : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ y) hmem
    simpa [mulVec_mulVec, ← Units.val_mul] using this
  funext i
  have := congrFun hvQ i
  exact PadicInt.coe_eq_zero.1 this

end Stacks.EtaleCohomology

end
