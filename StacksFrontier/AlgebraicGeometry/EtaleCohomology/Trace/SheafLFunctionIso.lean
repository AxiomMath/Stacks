module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AdicLFunction

/-!
# The L-function of a sheaf only depends on its isomorphism class

An isomorphism of sheaves of `Λ`-modules identifies their stalks at the geometric point at a
closed point compatibly with the geometric Frobenius, so the local factors
`det(1 - π_x^* T ^ (deg x))` agree, and so do the L-functions.

## Main results

* `Stacks.EtaleCohomology.charPowerSeries_frobeniusStalkEnd_of_iso`
* `Stacks.EtaleCohomology.lFunctionOfSheaf_congr_iso`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u w r

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
  [IsLocalRing Λ] {k : Type u} [Field k] [Finite k] (f : X.obj ⟶ Spec (.of k))
  [LocallyOfFiniteType f]

/-- Isomorphic sheaves have the same local factors at the closed points. -/
public theorem charPowerSeries_frobeniusStalkEnd_of_iso
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)} (e : F ≅ G)
    (hfin : ∀ s : GeometricPoint X.obj,
      Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
    (hproj : ∀ s : GeometricPoint X.obj,
      Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
    (x : closedPoints X.obj) (d : ℕ) :
    charPowerSeries (frobeniusStalkEnd B X Λ F f x) d =
      charPowerSeries (frobeniusStalkEnd B X Λ G f x) d := by
  have := finite_residueField f x.1 x.2
  have := finite_sheafFiber_sheafEquiv B X Λ (geometricPointAt X.obj x.1) F (hfin _)
  have := projective_sheafFiber_sheafEquiv B X Λ F (geometricPointAt X.obj x.1) (hproj _)
  let L := (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).functor
  let Φ := (Scheme.pointSmallEtale (geometricPointAt X.obj x.1).hom).sheafFiber
    (A := ModuleCat.{w} Λ)
  let E := Φ.mapIso (L.mapIso e)
  have hG : frobeniusStalk (ModuleCat.{w} Λ) X.obj x.1 (L.obj G) =
      E.inv ≫ frobeniusStalk (ModuleCat.{w} Λ) X.obj x.1 (L.obj F) ≫ E.hom := by
    rw [← cancel_epi E.hom, Iso.hom_inv_id_assoc]
    exact frobeniusStalk_naturality (ModuleCat.{w} Λ) X.obj x.1 (L.map e.hom)
  have h : frobeniusStalkEnd B X Λ G f x =
      E.toLinearEquiv.conj (frobeniusStalkEnd B X Λ F f x) :=
    LinearMap.ext fun y => congrArg (fun g => g.hom y) hG
  rw [h, charPowerSeries_conj (chooseBasisFin Λ _).equivFun]

/-- **Isomorphic sheaves have the same L-function.** -/
public theorem lFunctionOfSheaf_congr_iso [QuasiCompact f]
    {F G : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ)} (e : F ≅ G)
    (hfinF : ∀ s : GeometricPoint X.obj,
      Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
    (hprojF : ∀ s : GeometricPoint X.obj,
      Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
    (hfinG : ∀ s : GeometricPoint X.obj,
      Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj G))
    (hprojG : ∀ s : GeometricPoint X.obj,
      Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj G)) :
    lFunctionOfSheaf B X Λ F f hfinF hprojF = lFunctionOfSheaf B X Λ G f hfinG hprojG := by
  refine FrobeniusMatrices.lFunction_congr _ fun x => ?_
  rw [FrobeniusMatrices.localFactor, FrobeniusMatrices.localFactor, localEulerFactor,
    localEulerFactor, ← charPowerSeries_frobeniusStalkEnd, ← charPowerSeries_frobeniusStalkEnd,
    charPowerSeries_frobeniusStalkEnd_of_iso B X Λ f e hfinF hprojF x]

end Stacks.EtaleCohomology

end
