module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyCoinvariants
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTopCohomologyLisseBaseFieldNatural

/-!
# `H²_c` of `ℱ_τ` on a smooth geometrically connected curve, naturally in the coefficients

The level isomorphisms `H²_c(U_k̄, ℱ_{ρ,n+1}) ≅ ((ℤ/ℓ^{n+1})^r)_{π₁(U_k̄)}` of
`LAdicSheaf.exists_linearEquiv_compactSupportSheafCohomology_two_levelModule`
can be chosen natural in the endomorphisms of the level module which descend to the coinvariants:
the identification `H²_c(U_k̄, ℱ_Q) ≅ Q` for `Q` with trivial geometric monodromy is natural in `Q`
(`exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_trivial_natural`).

## Main results

* `exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_trivial_natural`:
  `H²_c(U_k̄, ℱ_Q) ≅ Q`, compatibly with the Frobenius and naturally in `Q`, for `Q` with trivial
  geometric monodromy.
* `LAdicSheaf.exists_linearEquiv_compactSupportSheafCohomology_two_levelModule_natural`:
  `H²_c(U_k̄, ℱ_{ρ,n+1}) ≅ ((ℤ/ℓ^{n+1})^r)_{π₁(U_k̄)}`, compatibly with the Frobenius and naturally
  in the endomorphisms of the level module which descend to the coinvariants.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- A power of a prime `ℓ ≠ p` is invertible in a field of characteristic `p`. -/
private theorem isUnit_natCast_pow_of_ne_charP {K : Type*} [Field K] {p ℓ : ℕ} [Fact p.Prime]
    [Fact ℓ.Prime] [CharP K p] (hℓ : ℓ ≠ p) (n : ℕ) : IsUnit ((ℓ ^ n : ℕ) : K) := by
  refine IsUnit.mk0 _ ?_
  rw [Nat.cast_pow]
  refine pow_ne_zero _ fun h => hℓ ?_
  rw [CharP.cast_eq_zero_iff K p] at h
  exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1 h).symm

/-- A normal subgroup `H` acts trivially on the level coinvariants for `H`. -/
private theorem levelCoinvariantsModule_ρ_eq_one_of_mem {G : Type (u + 1)} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) [H.Normal] {ℓ : ℕ} [Fact ℓ.Prime]
    {r : ℕ} (ρ : G →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ) (k : ℕ) [NeZero (ℓ ^ k)] {g : G}
    (hg : g ∈ H) : (levelCoinvariantsModule H ρ hρ k).obj.obj.obj.ρ g = 1 :=
  End.ext
    (ModuleCat.hom_ext (LinearMap.ext fun v => levelCoinvariantsRepresentation_eq_of_mem H ρ k hg v))

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

include hs hQ in
/-- **`H²_c(U_k̄, ℱ_Q) ≅ Q` with `π_U^* = q · φ`, naturally in `Q`**, for a finite `ℤ/m`-module
`Q` with a continuous action of `π₁(U, x̄)` on which the geometric fundamental group acts
trivially, `m` invertible in `k̄` and `φ` lying over the inverse of the Frobenius of `k`. -/
theorem exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_trivial_natural
    (hm : IsUnit (m : kbar)) (hgi : GeometricallyIrreducible f) (φ : EtaleFundamentalGroup U.1 x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p q hcard (x.map f))⁻¹) :
    ∃ θ : (compactSupportSheafCohomology (ZMod m) f j kbar 2).obj
        ((lisseEtaleSheaf B U x (ZMod m)).obj Q) ≃+ Q.obj.obj.obj.V,
      (∀ t, θ (((compactSupportSheafFrobenius (ZMod m) f j kbar p q hcard 2).app
          ((lisseEtaleSheaf B U x (ZMod m)).obj Q)).hom t) =
        (p ^ q : ℕ) • (Q.obj.obj.obj.ρ φ).asHom.hom (θ t)) ∧
      ∀ (g : Q ⟶ Q) t, θ (((compactSupportSheafCohomology (ZMod m) f j kbar 2).map
          ((lisseEtaleSheaf B U x (ZMod m)).map g)).hom t) = g.hom.hom.hom.hom.hom (θ t) := by
  obtain ⟨u₀, _, h₀, hu₀⟩ := exists_isIso_twist_lisseEtaleSheaf_baseField_natural B U f kbar m p q
    hcard x hs Q hQ φ hφ
  exact exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_twist_natural B U f j
    kbar m p q hcard x hs Q hQ hm hgi φ u₀ h₀ hu₀

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

/-- **`H²_c(U_k̄, ℱ_{ρ,n+1}) ≅ ((ℤ/ℓ^{n+1})^r)_{π₁(U_k̄)}` with `π_U^* = q · ρ(φ)`, naturally**
in the endomorphisms of the level module which descend to the coinvariants, for a smooth
geometrically connected curve `U` over a finite field, `ρ` the integral model of `τ` and `φ` over
the inverse of the Frobenius of `k`. -/
theorem LAdicSheaf.exists_linearEquiv_compactSupportSheafCohomology_two_levelModule_natural
    (hℓ : ℓ ≠ p) (φ : EtaleFundamentalGroup U.1 x)
    (hφ : etaleFundamentalGroupMap f x φ = (finiteFieldFrobenius p q hcard (x.map f))⁻¹) (n : ℕ) :
    ∃ e : (compactSupportSheafCohomology (ZMod (ℓ ^ (n + 1))) f j kbar 2).obj
        ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).obj
          (levelModule.{u + 1, u + 1} (integralModel τ hτ) (continuous_integralModel τ hτ)
            (n + 1))) ≃ₗ[ZMod (ℓ ^ (n + 1))]
        levelCoinvariants (etaleFundamentalGroupMap f x).toMonoidHom.ker (integralModel τ hτ)
          (n + 1),
      (∀ t, e (((compactSupportSheafFrobenius (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard 2).app
          ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).obj
            (levelModule.{u + 1, u + 1} (integralModel τ hτ) (continuous_integralModel τ hτ)
              (n + 1)))).hom t) =
        ((p ^ q : ℕ) : ZMod (ℓ ^ (n + 1))) •
          levelCoinvariantsFrobenius (etaleFundamentalGroupMap f x).toMonoidHom.ker
            (integralModel τ hτ) φ (n + 1) (e t)) ∧
      ∀ (g : levelModule.{u + 1, u + 1} (integralModel τ hτ) (continuous_integralModel τ hτ)
            (n + 1) ⟶
          levelModule.{u + 1, u + 1} (integralModel τ hτ) (continuous_integralModel τ hτ) (n + 1))
        (g' : levelCoinvariantsModule (etaleFundamentalGroupMap f x).toMonoidHom.ker
            (integralModel τ hτ) (continuous_integralModel τ hτ) (n + 1) ⟶
          levelCoinvariantsModule (etaleFundamentalGroupMap f x).toMonoidHom.ker
            (integralModel τ hτ) (continuous_integralModel τ hτ) (n + 1)),
        g ≫ levelCoinvariantsQuotient (etaleFundamentalGroupMap f x).toMonoidHom.ker
            (integralModel τ hτ) (continuous_integralModel τ hτ) (n + 1) =
          levelCoinvariantsQuotient (etaleFundamentalGroupMap f x).toMonoidHom.ker
            (integralModel τ hτ) (continuous_integralModel τ hτ) (n + 1) ≫ g' →
        ∀ t, e (((compactSupportSheafCohomology (ZMod (ℓ ^ (n + 1))) f j kbar 2).map
            ((lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))).map g)).hom t) =
          (g'.hom.hom.hom.hom.hom (ULift.up (e t))).down := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsCurve k f := isCurve_of_smoothOfRelativeDimension_one_of_connectedSpace f
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := (Algebra.charP_iff k kbar p).1 inferInstance
  have := compactSpace_etaleFundamentalGroup U.1 x
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have hgi : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_connectedSpace_pullback_isAlgClosure kbar f ‹_›
  have hs : Function.Surjective (etaleFundamentalGroupMap f x) :=
    surjective_etaleFundamentalGroupMap_isAlgClosed k kbar f x
  obtain ⟨θ, hθ, hθn⟩ :=
    exists_addEquiv_compactSupportSheafCohomology_two_lisseEtaleSheaf_of_trivial_natural B U f j
      kbar (ℓ ^ (n + 1)) p q hcard x hs
      (levelCoinvariantsModule (etaleFundamentalGroupMap f x).toMonoidHom.ker
        (integralModel τ hτ) (continuous_integralModel τ hτ) (n + 1))
      (fun _ hg => levelCoinvariantsModule_ρ_eq_one_of_mem _ _ _ _ (MonoidHom.mem_ker.2 hg))
      (isUnit_natCast_pow_of_ne_charP hℓ _) hgi φ hφ
  have := LAdicSheaf.finite_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule
    B U ℓ f j kbar p x τ hτ hℓ n
  let T := compactSupportSheafCohomology (ZMod (ℓ ^ (n + 1))) f j kbar 2
  let L := lisseEtaleSheaf B U x (ZMod (ℓ ^ (n + 1)))
  let c := levelCoinvariantsQuotient (etaleFundamentalGroupMap f x).toMonoidHom.ker
    (integralModel τ hτ) (continuous_integralModel τ hτ) (n + 1)
  have hadd : ∀ a b, (θ ((T.map (L.map c)).hom (a + b))).down =
      (θ ((T.map (L.map c)).hom a)).down + (θ ((T.map (L.map c)).hom b)).down :=
    fun a b => by rw [map_add, map_add]; rfl
  let F := AddMonoidHom.mk' (fun t => (θ ((T.map (L.map c)).hom t)).down) hadd
  have hFs : Function.Surjective F := fun y => by
    obtain ⟨z, hz⟩ := θ.surjective (ULift.up y)
    obtain ⟨t, rfl⟩ := surjective_compactSupportSheafCohomology_two_lisseEtaleSheaf_map B U x f j
      kbar (ℓ ^ (n + 1)) (IsCurve.topologicalKrullDim_eq_one (f := f)).le c
      (surjective_levelCoinvariantsQuotient (etaleFundamentalGroupMap f x).toMonoidHom.ker
        (integralModel τ hτ) (continuous_integralModel τ hτ) (n + 1)) z
    exact ⟨t, congrArg ULift.down hz⟩
  refine ⟨LinearEquiv.ofBijective (F.toZModLinearMap (ℓ ^ (n + 1))) (hFs.bijective_of_nat_card_le
    (LAdicSheaf.natCard_compactSupportSheafCohomology_two_lisseEtaleSheaf_levelModule_le
      B U ℓ f j kbar p x τ hτ hℓ n)), fun t => ?_, fun g g' hgg t => ?_⟩
  · have hnat := congrArg (fun g => g.hom t)
      ((compactSupportSheafFrobenius (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard 2).naturality
        (L.map c))
    change (θ ((T.map (L.map c)).hom
      (((compactSupportSheafFrobenius (ZMod (ℓ ^ (n + 1))) f j kbar p q hcard 2).app
        (L.obj _)).hom t))).down = _
    rw [← ModuleCat.comp_apply, ← hnat, ModuleCat.comp_apply, hθ,
      ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (n + 1)))]
    rfl
  · have hT : T.map (L.map g) ≫ T.map (L.map c) = T.map (L.map c) ≫ T.map (L.map g') := by
      rw [← T.map_comp, ← T.map_comp, ← L.map_comp, ← L.map_comp, hgg]
    exact (congrArg (fun z => (θ z).down) (congrArg (fun φ => φ.hom t) hT)).trans
      (congrArg ULift.down (hθn g' ((T.map (L.map c)).hom t)))

end Levels

end Stacks.EtaleCohomology

end
