module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusTwistIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyRootsExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedBelowDirectSums
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow

/-!
# The canonical geometric Frobenius is an automorphism of `RΓ_c(X_k̄, -)`

The canonical geometric Frobenius `π_X^*` of `RΓ_c(X_k̄, K) = RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` is
`RΓ(Spec k̄, R pr_*(-))` applied to the canonical morphism `C|_{Y_k̄} ⟶ Rπ̄_*(C|_{Y_k̄})`, followed
by `Rπ̄_* ⋙ R pr_* ≅ R pr_*`.  That morphism is the Frobenius base change twist, an isomorphism
(`Stacks.EtaleCohomology.isIso_frobeniusBaseChangeTwist`), followed by the comparison of `π̄_*`
with its derived functor, an isomorphism since `π̄_*` is exact (an equivalence: `π̄` is a universal
homeomorphism).  So `π_X^*` is an automorphism of `RΓ_c(X_k̄, K)`, hence of every `Hⁱ_c(X_k̄, K)`,
of `Hⁱ_c(X_k̄, F)` for an ℓ-adic sheaf `F`, and of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`.

In particular `0` is not an eigenvalue of `π_X^*` on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`: a Frobenius weight, the
absolute value `q ^ (w / 2)` of an eigenvalue, is the weight of a nonzero number.

## Main results

* `Stacks.EtaleCohomology.isIso_frobeniusRestrictionCohomologyEndo`.
* `Stacks.EtaleCohomology.isIso_canonicalCompactSupportFrobenius`.
* `Stacks.EtaleCohomology.LAdicSheaf.isIso_rationalGeometricCompactlySupportedFrobenius`.
* `Stacks.EtaleCohomology.ne_zero_of_isRoot_charpoly_map_of_isUnit`: an automorphism has no
  characteristic root `0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Endo

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The canonical morphism `C|_{Y_k̄} ⟶ Rπ̄_*(C|_{Y_k̄})` is an isomorphism. -/
public instance isIso_frobeniusRestrictionDerivedMap
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    IsIso (frobeniusRestrictionDerivedMap.{u, r} Λ Y kbar p q hcard C) := by
  have := etaleModuleDirectImage_isEquivalence_of_universalHomeomorphism Λ
    (geometricFrobeniusBaseChange Y kbar p q hcard)
  have h₁ : IsIso ((Functor.mapCochainComplexPlusDerivedUnit (etaleModuleDirectImage.{u, r} Λ
      (geometricFrobeniusBaseChange Y kbar p q hcard))).app
      ((etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C)) :=
    Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app _ _
      fun _ => Functor.rightAcyclic_of_exact _ _
  let e := (NatIso.mapHomologicalComplex
    (asIso (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard)) (ComplexShape.up ℤ)).app C.obj
  unfold frobeniusRestrictionDerivedMap
  refine IsIso.comp_isIso' ?_ h₁
  have : IsIso (ObjectProperty.homMk (P := CochainComplex.plus _)
      (X := (etaleModuleInverseImage.{u, r} Λ
        (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C)
      (Y := (etaleModuleDirectImage.{u, r} Λ
          (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
        ((etaleModuleInverseImage.{u, r} Λ
          (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj C))
      ((NatTrans.mapHomologicalComplex (frobeniusBaseChangeTwist.{u, r} Λ Y kbar p q hcard)
        (ComplexShape.up ℤ)).app C.obj)) :=
    ⟨⟨ObjectProperty.homMk e.inv, by apply ObjectProperty.hom_ext; exact e.hom_inv_id,
      by apply ObjectProperty.hom_ext; exact e.inv_hom_id⟩⟩
  exact Functor.map_isIso _ _

/-- **The canonical endomorphism of `RΓ(Y_k̄, C|_{Y_k̄})` induced by the geometric Frobenius is an
automorphism.** -/
public instance isIso_frobeniusRestrictionCohomologyEndo
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    IsIso (frobeniusRestrictionCohomologyEndo.{u, r} Λ Y kbar p q hcard C) := by
  unfold frobeniusRestrictionCohomologyEndo
  infer_instance

end Endo

section CompactSupport

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- **`π_X^*` is an automorphism of `RΓ_c(X_k̄, K)`.** -/
public instance isIso_canonicalCompactSupportFrobenius
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    IsIso (canonicalCompactSupportFrobenius.{u, r} Λ f j kbar p q hcard K) :=
  isIso_frobeniusRestrictionCohomologyEndo Λ _ kbar p q hcard _

/-- `π_X^*` is an automorphism of `RΓ_c(X_k̄, -)`, as a natural transformation. -/
public instance isIso_canonicalCompactSupportFrobeniusNatTrans :
    IsIso (canonicalCompactSupportFrobeniusNatTrans.{u, r} Λ f j kbar p q hcard) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
    fun K => isIso_canonicalCompactSupportFrobenius Λ f j kbar p q hcard K

/-- **`π_X^*` is an automorphism of `Hⁱ_c(X_k̄, K)`.** -/
public instance isIso_canonicalCompactSupportFrobeniusGroup
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) (i : ℤ) :
    IsIso (canonicalCompactSupportFrobeniusGroup.{u, r} Λ f j kbar p q hcard K i) := by
  unfold canonicalCompactSupportFrobeniusGroup
  infer_instance

end CompactSupport

/-! ### The ℓ-adic and rational limits -/

section LAdic

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  (F : LAdicSheaf B X ℓ) (i : ℤ)

/-- **`π_X^*` is an automorphism of `Hⁱ_c(X_k̄, F)`.** -/
public instance LAdicSheaf.isIso_geometricCompactlySupportedFrobenius :
    IsIso (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i) := by
  have : IsIso (LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ f j kbar F i
      (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun n => ?_
    induction n using Opposite.rec with
    | op n =>
      change IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).map
        (canonicalCompactSupportFrobenius.{u, 0} ℤ_[ℓ] f j kbar p q hcard
          ((padicCoefficientComplex B X ℓ).obj (LAdicSheaf.padicLevel B X ℓ F n))))
      infer_instance
  change IsIso (limMap _)
  infer_instance

/-- **`π_X^*` is an automorphism of `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`.** -/
public instance LAdicSheaf.isIso_rationalGeometricCompactlySupportedFrobenius :
    IsIso
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i) := by
  change IsIso ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (LAdicSheaf.geometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F i))
  infer_instance

end LAdic

/-! ### No characteristic root `0` -/

/-- **An automorphism has no characteristic root `0`**: the constant coefficient of its
characteristic polynomial is `± det`, a unit. -/
public theorem ne_zero_of_isRoot_charpoly_map_of_isUnit {K L : Type*} [Field K] [Field L]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ι : K →+* L)
    {g : Module.End K V} (hg : IsUnit g) {z : L} (hz : (g.charpoly.map ι).IsRoot z) : z ≠ 0 := by
  rintro rfl
  let := ι.toAlgebra
  rw [isRoot_charpoly_map_iff_hasEigenvalue_baseChange] at hz
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  obtain ⟨u, rfl⟩ := hg
  have h0 : (↑u : Module.End K V).baseChange L v = 0 := by
    rw [hv.apply_eq_smul, zero_smul]
  have h1 : (↑u⁻¹ : Module.End K V).baseChange L ((↑u : Module.End K V).baseChange L v) = v := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp,
      Units.inv_mul, LinearMap.baseChange_one, Module.End.one_apply]
  rw [h0, map_zero] at h1
  exact hv.2 h1.symm

end Stacks.EtaleCohomology

end
