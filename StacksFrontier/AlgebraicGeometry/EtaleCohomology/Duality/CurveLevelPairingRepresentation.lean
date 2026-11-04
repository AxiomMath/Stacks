module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveLevelPoincarePairingNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationDualFibres
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevelPowExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.InverseImageAlongMorphism

/-!
# The finite-level Poincaré pairing on a curve for the sheaf of a representation

Let `ρ₀ : π₁(X, x̄) → GL_r(ℤ_ℓ)` be continuous, `F = ℱ_{ρ₀}` and `F' = ℱ_{ρ₀^∨}` the ℓ-adic sheaves
of `ρ₀` and of its contragredient
(`Stacks.EtaleCohomology.representationLAdicSheaf`). For a compactification `j : X ⟶ X̄` over a
finite field `k`, an extension `k̄` of `k`, `Y = X̄_k̄` and `N = ℓⁿ⁺¹`, the two coefficient
hypotheses of the finite-level Poincaré duality on a curve
(`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_bounds`) that concern `F'` alone hold:

* `F'ₙ|_{X_k̄}` is lisse
  (`isFiniteTypeLocallyConstant_inverseImage_etaleLevel_representationLAdicSheaf`): the levels of
  `ℱ_{ρ₀^∨}` are lisse and inverse images of lisse sheaves are lisse;
* `(j_! F'ₙ)|_Y` has flat fibres at all points with separably closed residue field
  (`Stacks.EtaleCohomology.flat_sheafFiber_inverseImage_extensionByZero_representationLAdicSheaf`):
  the levels are flat (pow-exact) and `j_!` and inverse images preserve flat fibres.

So for `F = ℱ_{ρ₀}`, `F' = ℱ_{ρ₀^∨}` the level pairing
`Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing` is defined for every pairing
`μₙ : j_! Fₙ ⊗ j_! F'ₙ ⟶ ℤ/N`, and `Stacks.EtaleCohomology.LAdicSheaf.curveLevelPairing_bounds`
applies with only the perfectness of `μₙ` on the fibres over `X_k̄` and the local terms of `F` left
to check. This is the
specialisation of Poincaré duality on an affine curve to the sheaf of a representation, in the
purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category (the ℓ-adic compactly supported cohomology), which is therefore a local instance
here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleModuleDirectImage_preservesFiniteColimits_of_universalHomeomorphism

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [IsNoetherian X.1] [Fact ℓ.Prime] [ConnectedSpace X.1] (x : GeometricPoint X.1) {r : ℕ}
  (ρ₀ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀)
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **The levels of `ℱ_{ρ₀}` are lisse over `X_k̄`.** -/
theorem isFiniteTypeLocallyConstant_inverseImage_etaleLevel_representationLAdicSheaf (n : ℕ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod (ℓ ^ (n + 1)))
      (fieldBaseChange (Over.mk f) kbar).smallEtaleTopology
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (fieldBaseChangeProj (Over.mk f) kbar)).obj
        (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
          (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n)) :=
  lccModules_etaleModuleInverseImage _ (fieldBaseChangeProj (Over.mk f) kbar) _
    (isFiniteTypeLocallyConstant_etaleLevel_representationLAdicSheaf B X x ρ₀ hρ₀ n)

omit [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **`(j_! ℱ_{ρ₀,n})|_{X̄_k̄}` has flat fibres** at all points with separably closed residue
field. -/
theorem flat_sheafFiber_inverseImage_extensionByZero_representationLAdicSheaf (n : ℕ)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk j.toBase) kbar) :
    Module.Flat (ZMod (ℓ ^ (n + 1)))
      ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1))) j.immersion).obj
            (LAdicSheaf.etaleLevel B X ℓ (representationLAdicSheaf B X x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B X x) ρ₀ hρ₀) n)))) :=
  have : IsOpenImmersion j.immersion := j.property.1
  flat_sheafFiber_inverseImage_extensionByZero_of_powExact j.immersion
    (fieldBaseChangeProj (Over.mk j.toBase) kbar) _
    (powExact_etaleLevel_representationLAdicSheaf B X x ρ₀ hρ₀ n) Ω s

end Stacks.EtaleCohomology

end
