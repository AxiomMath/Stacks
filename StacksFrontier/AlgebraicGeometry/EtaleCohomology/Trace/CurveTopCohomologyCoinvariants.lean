module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseBaseFieldTwist
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyLisseBaseField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyCoverCount
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyLevels
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyTransition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LevelCoinvariantsModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIICurveBoundAffineLineInputs

/-!
# `H²_c` of `ℱ_τ` on a smooth geometrically connected curve is the geometric coinvariants

Let `U` be a smooth geometrically connected curve over a finite field `k` with `q` elements, `k̄`
an algebraic closure and `τ : π₁(U, x̄) → GL_r(ℚ_ℓ)` continuous, `ℓ ≠ p`. Then
`H²_c(U_k̄, ℱ_τ ⊗ ℚ_ℓ)` is the coinvariants of `τ` under the geometric fundamental group
`π₁(U_k̄) = ker(π₁(U) → π₁(Spec k))`, the canonical Frobenius `π_U^*` acting as `q · τ(φ)` for any
`φ` lying over the inverse of the Frobenius of `k` ([Stacks, Tag 03VN]).

## Main results

* `exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_trivial`.
* `LAdicSheaf.exists_linearEquiv_compactSupportSheafCohomology_two_levelModule`.
* `Stacks.EtaleCohomology.curveCoinvariantsInput`: the proposition
  `Stacks.EtaleCohomology.CurveCoinvariantsInput` holds.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Trivial geometric monodromy -/

section Trivial

variable (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] {k : Type u} [Field k]
  [Fintype k] (f : U.1 ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f)) (kbar : Type u)
  [Field kbar] [Algebra k kbar] [IsAlgClosed kbar] (m : ℕ) [NeZero m] (p q : ℕ) [Fact p.Prime]
  [CharP k p] (hcard : Fintype.card k = p ^ q) (x : GeometricPoint U.1)
  (hs : Function.Surjective (etaleFundamentalGroupMap f x))
  (Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) (EtaleFundamentalGroup U.1 x))
  (hQ : ∀ g, etaleFundamentalGroupMap f x g = 1 → Q.obj.obj.obj.ρ g = 1)

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
include hs hQ in
/-- **`H²_c(U_k̄, ℱ_Q) ≅ Q` with `π_U^* = q · φ`**, for a finite `ℤ/m`-module `Q` with a continuous
action of `π₁(U, x̄)` on which the geometric fundamental group acts trivially, `m` invertible in
`k̄` and `φ` lying over the inverse of the Frobenius of `k`. -/
theorem exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_trivial
    (hm : IsUnit (m : kbar)) (hgi : GeometricallyIrreducible f) (φ : EtaleFundamentalGroup U.1 x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p q hcard (x.map f))⁻¹) :
    ∃ θ : (compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
        ((lisseEtaleSheaf B U x (ZMod m)).obj Q) ≃+ Q.obj.obj.obj.V,
      ∀ t, θ (((compactSupportSheafFrobenius (ZMod m) f j kbar p q hcard 2).app
          ((lisseEtaleSheaf B U x (ZMod m)).obj Q)).hom t) =
        (p ^ q : ℕ) • (Q.obj.obj.obj.ρ φ).asHom.hom (θ t) := by
  obtain ⟨u₀, _, h₀⟩ := exists_isIso_twist_lisseEtaleSheaf_baseField B U f kbar m p q hcard x hs
    Q hQ φ hφ
  exact exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_twist B U f j kbar m p
    q hcard x hs Q hQ hm hgi φ u₀ h₀

end Trivial

/-! ### The levels of `ℱ_τ` -/

section Levels

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime] [ConnectedSpace U.1]
  {k : Type u} [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar]
  [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) (x : GeometricPoint U.1)
  {r : ℕ} (τ : EtaleFundamentalGroup U.1 x →* GL (Fin r) ℚ_[ℓ]) (hτ : Continuous τ)

/-- **`H²_c(U_k̄, ℱ_{ρ,n+1}) ≅ ((ℤ/ℓ^{n+1})^r)_{π₁(U_k̄)}` with `π_U^* = q · ρ(φ)`** ([Stacks,
Tag 03VK] at a finite level), for a smooth geometrically connected curve `U` over a finite field,
`ρ` the integral model of `τ` and `φ` over the inverse of the Frobenius of `k`. -/
theorem LAdicSheaf.exists_linearEquiv_compactSupportSheafCohomology_two_levelModule (hℓ : ℓ ≠ p)
    (φ : EtaleFundamentalGroup U.1 x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p q hcard (x.map f))⁻¹) (n : ℕ) :
    ∃ e : (compactSupportSheafCohomology (ZMod (ℓ ^ (n + 1))) f j kbar 2).obj
        ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} (integralModel τ hτ) (continuous_integralModel τ hτ)
            (n + 1))) ≃ₗ[ZMod (ℓ ^ (n + 1))]
        levelCoinvariants (etaleFundamentalGroupMap f x).toMonoidHom.ker (integralModel τ hτ)
          (n + 1),
      ∀ t, e (((compactSupportSheafFrobenius (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard 2).app
          ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).obj
            (levelModule.{u + 1, u + 1} (integralModel τ hτ) (continuous_integralModel τ hτ)
              (n + 1)))).hom t) =
        ((p ^ q : ℕ) : ZMod (ℓ ^ (n + 1))) •
          levelCoinvariantsFrobenius (etaleFundamentalGroupMap f x).toMonoidHom.ker
            (integralModel τ hτ) φ (n + 1) (e t) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsCurve k f := isCurve_of_smoothOfRelativeDimension_one_of_connectedSpace f
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := (Algebra.charP_iff k kbar p).1 inferInstance
  have := compactSpace_etaleFundamentalGroup U.1 x
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have hm : IsUnit (((ℓ ^ (n + 1) : ℕ)) : kbar) := by
    refine IsUnit.mk0 _ ?_
    rw [Nat.cast_pow]
    refine pow_ne_zero _ fun h => hℓ ?_
    rw [CharP.cast_eq_zero_iff kbar p] at h
    exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1 h).symm
  have hgi : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_connectedSpace_pullback_isAlgClosure kbar f ‹_›
  have hs : Function.Surjective (etaleFundamentalGroupMap f x) :=
    surjective_etaleFundamentalGroupMap_isAlgClosed k kbar f x
  have hdim : topologicalKrullDim U.1 ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  have hQ : ∀ g, etaleFundamentalGroupMap f x g = 1 →
      (levelCoinvariantsModule (etaleFundamentalGroupMap f x).toMonoidHom.ker (integralModel τ hτ)
        (continuous_integralModel τ hτ) (n + 1)).obj.obj.obj.ρ g = 1 := fun g hg =>
    End.ext (ModuleCat.hom_ext (LinearMap.ext fun v =>
      levelCoinvariantsRepresentation_eq_of_mem (etaleFundamentalGroupMap f x).toMonoidHom.ker
        (integralModel τ hτ) (n + 1) (MonoidHom.mem_ker.2 hg) v))
  obtain ⟨θ, hθ⟩ := exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_trivial
    B U f j kbar (ℓ ^ (n + 1)) p q hcard x hs
    (levelCoinvariantsModule (etaleFundamentalGroupMap f x).toMonoidHom.ker (integralModel τ hτ)
      (continuous_integralModel τ hτ) (n + 1)) hQ hm hgi φ hφ
  have hsurj := surjective_compactSupportSheafCohomology_two_lisseEtaleSheaf_map B U x f j kbar
    (ℓ ^ (n + 1)) hdim
    (levelCoinvariantsQuotient (etaleFundamentalGroupMap f x).toMonoidHom.ker (integralModel τ hτ)
      (continuous_integralModel τ hτ) (n + 1))
    (surjective_levelCoinvariantsQuotient (etaleFundamentalGroupMap f x).toMonoidHom.ker
      (integralModel τ hτ) (continuous_integralModel τ hτ) (n + 1))
  have hle := LAdicSheaf.natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule_le
    B U ℓ f j kbar p x τ hτ hℓ n
  have := LAdicSheaf.finite_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule
    B U ℓ f j kbar p x τ hτ hℓ n
  let g := (compactSupportSheafCohomology (ZMod (ℓ ^ (n + 1))) f j kbar 2).map
    ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).map
      (levelCoinvariantsQuotient (etaleFundamentalGroupMap f x).toMonoidHom.ker
        (integralModel τ hτ) (continuous_integralModel τ hτ) (n + 1)))
  let F := AddMonoidHom.mk' (fun t => (θ (g.hom t)).down)
    fun a b => by rw [map_add, map_add]; rfl
  have hFs : Function.Surjective F := fun y => by
    obtain ⟨z, hz⟩ := θ.surjective (ULift.up y)
    obtain ⟨t, rfl⟩ := hsurj z
    exact ⟨t, congrArg ULift.down hz⟩
  have hbij : Function.Bijective F := hFs.bijective_of_nat_card_le hle
  refine ⟨LinearEquiv.ofBijective (F.toZModLinearMap (ℓ ^ (n + 1))) hbij, fun t => ?_⟩
  have hnat := congrArg (fun h => h.hom t)
    ((compactSupportSheafFrobenius (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard 2).naturality
      ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).map
        (levelCoinvariantsQuotient (etaleFundamentalGroupMap f x).toMonoidHom.ker
          (integralModel τ hτ) (continuous_integralModel τ hτ) (n + 1))))
  change (θ (g.hom (((compactSupportSheafFrobenius (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard 2).app
        ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} (integralModel τ hτ) (continuous_integralModel τ hτ)
            (n + 1)))).hom t))).down = _
  rw [← ModuleCat.comp_apply, ← hnat, ModuleCat.comp_apply, hθ,
    ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (n + 1)))]
  rfl

end Levels

/-! ### The coinvariants input of the curve case of Tag 03VH -/

/-- **`H²_c(U_k̄, ℱ_τ ⊗ ℚ_ℓ)` is the geometric coinvariants of `τ`, twisted by `(-1)`**: on a
smooth geometrically connected curve over a finite field with `q` elements and for every `φ` over
the inverse of the Frobenius, there is an isomorphism with the coinvariants of `τ` under
`π₁(U_k̄)` carrying `π_U^*` to `q · τ(φ)`. -/
theorem curveCoinvariantsInput : CurveCoinvariantsInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ j kbar _ _ _ _ p n _ _ hcard hℓ x r τ hτ φ hφ
  have := compactSpace_etaleFundamentalGroup U.1 x
  have : IsCurve k f := isCurve_of_smoothOfRelativeDimension_one_of_connectedSpace f
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have hdim : topologicalKrullDim U.1 ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  refine LAdicSheaf.exists_linearEquiv_coinvariants_of_levels B U ℓ f j kbar p n hcard x τ hτ
    (etaleFundamentalGroupMap f x).toMonoidHom.ker φ (fun N => ?_)
    (LAdicSheaf.surjective_geometricCompactlySupportedCohomologySystem_map_two B U ℓ f j kbar
      (LAdicSheaf.representationSheaf B U x τ hτ) hdim)
  exact LAdicSheaf.exists_linearEquiv_compactSupportSheafCohomology_two_levelModule B U
    ℓ f j kbar p n hcard x τ hτ hℓ φ hφ N

end Stacks.EtaleCohomology

end
