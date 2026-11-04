module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.DescentSheafStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteCoefficientLFunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisTwistGroupRing
public import StacksFrontier.LinearAlgebra.Matrix.AdditiveFunctorCharSeries

/-!
# The local factors of a lisse sheaf through the twist functor

Let `C` be an étale Galois covering of `Z` with group `H` and `F` a sheaf on `Z` isomorphic to the
descent sheaf of a representation `ρ` of `H` on a free `Λ`-module `E`. Let
`Ψ = Hom_{ℤ/ℓ^M[H]}(E^∨, -)` be the twist functor, `O = ℤ/ℓ^M[H]` and `φ` the representation of
`ℤ/ℓ^M[H]` attached to `Ψ` and a basis of `Ψ(O) ≅ E`
(`Stacks.CharSeriesTraceDetection.functorRep`). At a closed point `x` of degree `d` with
Frobenius element `g_x`, the local factor `det(1 - π_x^* T ^ d | F_x̄)` of the L-function is
`det(1 - φ(g_x⁻¹) T ^ d)`: the stalk is `E` with Frobenius `ρ(g_x)`, and `Ψ(x ↦ x g_x⁻¹)`
corresponds to `ρ(g_x)` under `Ψ(O) ≅ E`. This is the determinant side of the key lemma of
[Stacks, Tag 03UZ] on a lisse stratum.

## Main results

* `Stacks.EtaleCohomology.finiteProjectiveLocalCharSeries_eq_det_functorRep`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius Stacks.CharSeriesTraceDetection

universe u

namespace Stacks.EtaleCohomology

variable (ℓ M : ℕ) [Fact ℓ.Prime] (H : Type) [Group H] [Fintype H] (Λ : Type) [CommRing Λ]
  [Algebra (ZMod (ℓ ^ M)) Λ] (E : Type (u + 1)) [AddCommGroup E] [Module Λ E]
  [Module (ZMod (ℓ ^ M)) E] [IsScalarTower (ZMod (ℓ ^ M)) Λ E] (ρ : Representation Λ H E)
  [Finite E]

/-- The rank one free module `O = ℤ/ℓ^M[H]` in the universe of the sheaves. -/
abbrev groupRingRankOne : ModuleCat.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H) :=
  ModuleCat.of (MonoidAlgebra (ZMod (ℓ ^ M)) H) (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ M)) H))

/-- The coordinate of `O`. -/
abbrev groupRingRankOneEquiv :
    MonoidAlgebra (ZMod (ℓ ^ M)) H ≃ₗ[MonoidAlgebra (ZMod (ℓ ^ M)) H] groupRingRankOne ℓ M H :=
  ULift.moduleEquiv.symm

/-- The basis of `Ψ(O) ≅ E` induced by a basis of `E`. -/
abbrev twistBasis {r : ℕ} (bE : E ≃ₗ[Λ] (Fin r → Λ)) :
    (twistFunctor (ZMod (ℓ ^ M)) H Λ E ρ).obj (groupRingRankOne ℓ M H) ≃ₗ[Λ] (Fin r → Λ) :=
  (twistFunctorGroupRingEquiv ℓ M H Λ E ρ).trans bE

attribute [local instance] moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]

omit [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint] in
/-- **The local factor of a lisse sheaf is that of the twisted Frobenius element.** -/
theorem finiteProjectiveLocalCharSeries_eq_det_functorRep (Z : B.Scheme)
    (FZ : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{u + 1} Λ))
    {k : Type u} [Field k] [Finite k] (fZ : Z.obj ⟶ Spec (.of k)) [LocallyOfFiniteType fZ]
    (hfin : ∀ s : GeometricPoint Z.obj,
      Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B Z Λ s).obj FZ))
    (hproj : ∀ s : GeometricPoint Z.obj,
      Module.Projective Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B Z Λ s).obj FZ))
    (C : EtaleGaloisCovering Z.obj H)
    (e : (SmallEtale.sheafEquiv B Z.obj Z.property (ModuleCat.{u + 1} Λ)).functor.obj FZ ≅
      C.descentSheaf.{u, 0, 0, 0} Λ E ρ)
    {r : ℕ} (bE : E ≃ₗ[Λ] (Fin r → Λ)) (x : closedPoints Z.obj)
    (a : (geometricPointAt Z.obj x.1).source ⟶ C.cover.left)
    (ha : a ≫ C.cover.hom = (geometricPointAt Z.obj x.1).hom) :
    haveI := finite_residueField fZ x.1 x.2
    finiteProjectiveLocalCharSeries B Z Λ FZ fZ hfin hproj x =
      (1 - (PowerSeries.X : PowerSeries Λ) ^ residueDegree fZ x.1 •
        (functorRep (twistFunctor (ZMod (ℓ ^ M)) H Λ E ρ) (groupRingRankOneEquiv ℓ M H)
          (twistBasis ℓ M H Λ E ρ bE)
          (MonoidAlgebra.single (C.pointElement a ha (frobeniusPointHom Z.obj x.1))⁻¹ 1)).map
            (PowerSeries.C (R := Λ))).det := by
  have := finite_residueField fZ x.1 x.2
  have : Module.Finite Λ E := Module.Finite.equiv bE.symm
  have : Module.Projective Λ E := Module.Projective.of_equiv bE.symm
  have := finite_sheafFiber_sheafEquiv B Z Λ (geometricPointAt Z.obj x.1) FZ (hfin _)
  have := projective_sheafFiber_sheafEquiv B Z Λ FZ (geometricPointAt Z.obj x.1) (hproj _)
  let Ψ := twistFunctor (ZMod (ℓ ^ M)) H Λ E ρ
  let Θ := twistFunctorGroupRingEquiv ℓ M H Λ E ρ
  have : Module.Finite Λ (Ψ.obj (groupRingRankOne ℓ M H)) := Module.Finite.equiv Θ.symm
  have : Module.Projective Λ (Ψ.obj (groupRingRankOne ℓ M H)) := Module.Projective.of_equiv Θ.symm
  set g := C.pointElement a ha (frobeniusPointHom Z.obj x.1)
  have hconj : Θ.conj (Ψ.map (rightMulHom (groupRingRankOneEquiv ℓ M H)
      (MonoidAlgebra.single g⁻¹ 1))).hom = ρ g := by
    ext y
    rw [LinearEquiv.conj_apply_apply, twistFunctorGroupRingEquiv_map_rightMulHom,
      LinearEquiv.apply_symm_apply]
  change ProjectiveDeterminant.charSeries
    (Stacks.Frobenius.frobeniusStalk (ModuleCat.{u + 1} Λ) Z.obj x.1
      ((SmallEtale.sheafEquiv B Z.obj Z.property (ModuleCat.{u + 1} Λ)).functor.obj FZ)).hom
    (residueDegree fZ x.1) = _
  rw [C.charSeries_frobeniusStalk_eq x.1 e a ha, ← hconj, ProjectiveDeterminant.charSeries_conj,
    charSeries_functor_map_rightMulHom]

end Stacks.EtaleCohomology
