module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.UnderlyingTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkExactnessCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTower
public import StacksFrontier.Homology.Perfect.ZModPrimePowerBaseChange
public import StacksFrontier.CategoryTheory.Abelian.PowExactImage

/-!
# The levels of the sheaf of a representation are flat

Let `ρ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous. The `k`-th level of `ℱ_ρ` has, at every geometric
point, the stalk `(ℤ/ℓᵏ)^r` (`Stacks.EtaleCohomology.representationLevelStalkIso`), which is free
over `ℤ/ℓᵏ`. Exactness of abelian étale sheaves is checked on geometric stalks (Tag 03PU), so the
sequences `F --ℓ^(k-a)--> F --ℓ^a--> F` are exact: the levels of `ℱ_ρ` are pow-exact, i.e. flat
over `ℤ/ℓᵏ`, on both small étale sites. This is the flatness input of the tower of
[Tag 03V2](https://stacks.math.columbia.edu/tag/03V2) for `ℱ_ρ` itself, without passing to a
torsion-free model.

## Main results

* `Stacks.EtaleCohomology.powExact_representationLevelSheaf`
* `Stacks.EtaleCohomology.powExact_etaleLevel_representationLAdicSheaf`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
  Stacks.ConstantSheaf Stacks.ZModPrimePower Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] (x : GeometricPoint X.1)
  {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)

/-- The stalks of the abelian sheaf underlying the `k`-th level of `ℱ_ρ` are `(ℤ/ℓᵏ)^r`. -/
theorem nonempty_stalk_representationLevelAbelian_addEquiv (k : ℕ) (s : GeometricPoint X.1) :
    Nonempty ((sheafToPresheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1} ⋙
      etaleStalkPresheafFunctor B X.1 X.2 s AddCommGrpCat.{u + 1}).obj
        (representationLevelAbelian B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ k) ≃+
        (Fin r → ZMod (ℓ ^ k))) := by
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso X.1 s x
  exact ⟨((etaleStalkForget₂Iso B X.1 X.2 s (ZMod (ℓ ^ k)) _).symm ≪≫
    representationLevelStalkIso B X x ρ hρ t k).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift⟩

/-- The `m`-th level of `ℱ_ρ` is killed by `ℓ ^ m`. -/
private theorem nsmul_id_representationLevelSheaf_eq_zero (m : ℕ) :
    (ℓ ^ m) • 𝟙 (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ m) = 0 := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => ?_))
  ext y
  exact ZModModule.char_nsmul_eq_zero (ℓ ^ m) y

/-- **The `k`-th level of `ℱ_ρ` is pow-exact**, on the small étale site of Stacks 021B. -/
theorem powExact_representationLevelSheaf (k : ℕ) :
    PowExact ℓ (k + 1) (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ (k + 1)) := by
  have := underlyingLevelFunctor_additive B X ℓ k
  have := underlyingLevelFunctor_isLeftAdjoint B X ℓ k
  have := underlyingLevelFunctor_preservesKernels B X ℓ k
  have : (underlyingLevelFunctor B X ℓ k).Faithful := inferInstance
  have hX := nsmul_id_representationLevelSheaf_eq_zero B X x ρ hρ (k + 1)
  refine PowExact.of_map (underlyingLevelFunctor B X ℓ k) hX ?_
  have hA : (ℓ ^ (k + 1)) • 𝟙 ((underlyingLevelFunctor B X ℓ k).obj (representationLevelSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ (k + 1))) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hX, Functor.map_zero]
  refine powExact_of_exact hA fun a ha => ?_
  rw [exact_iff_etaleStalk_exact.{u, 0} B X.1 X.2]
  intro s Φ b
  obtain ⟨e⟩ := nonempty_stalk_representationLevelAbelian_addEquiv B X x ρ hρ (k + 1) s
  have hP : IsPowExact ℓ (k + 1) _ := IsPowExact.of_addEquiv e.symm
    (isPowExact_of_projective (p := ℓ) (m := k + 1) (Fin r → ZMod (ℓ ^ (k + 1))))
  have hkill : ∀ z : ((sheafToPresheaf (SmallEtale.topology B X.1 X.2) AddCommGrpCat.{u + 1} ⋙
      etaleStalkPresheafFunctor B X.1 X.2 s AddCommGrpCat.{u + 1}).obj
        (representationLevelAbelian B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ (k + 1))),
      (ℓ ^ (k + 1)) • z = 0 := fun z => e.injective (by
    rw [map_zero, ← ZModModule.char_nsmul_eq_zero (ℓ ^ (k + 1)) (e z)]
    exact map_nsmul e _ z)
  have : Φ.Additive := abelianEtaleStalkFunctor_additive.{u, u + 1} B X.1 X.2 s
  have hmap : ∀ (n : ℕ) z, (Φ.map (n • 𝟙 ((underlyingLevelFunctor B X ℓ k).obj
      (representationLevelSheaf B X x (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x)
        ρ hρ (k + 1))))).hom z = n • z := by
    intro n z
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  change (Φ.map ((ℓ ^ a) • 𝟙 _)).hom b = 0 ↔ ∃ y, (Φ.map ((ℓ ^ (k + 1 - a)) • 𝟙 _)).hom y = b
  simp only [hmap]
  refine ⟨hP a ha b, ?_⟩
  rintro ⟨y, rfl⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' ha]
  exact hkill y

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [IsNoetherian X.1]

/-- **The levels of `ℱ_ρ` are pow-exact on Mathlib's small étale site**: the flatness input of the
tower of `RΓ_c(X_k̄, ℱ_{ρ,n})`. -/
theorem powExact_etaleLevel_representationLAdicSheaf (n : ℕ) :
    PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ hρ) n) := by
  let E := SmallEtale.sheafEquiv B X.1 X.2 (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact PowExact.map E.functor (nsmul_id_representationLevelSheaf_eq_zero B X x ρ hρ (n + 1))
    (powExact_representationLevelSheaf B X x ρ hρ n)

end Stacks.EtaleCohomology

end
