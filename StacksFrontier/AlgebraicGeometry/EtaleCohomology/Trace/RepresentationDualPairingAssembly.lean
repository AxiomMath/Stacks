module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationDualFibres

/-!
# The dual coefficients of `ℱ_ρ`, from the pairing of their levels

This file discharges `Stacks.EtaleCohomology.LAdicSheaf.RepresentationDualPairingInput`, the dual
coefficients input of the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH),
with `F' = ℱ_{ρ₀^∨}` (`Stacks.EtaleCohomology.LAdicSheaf.representationDualSheaf`), from the one
remaining statement about the pairing of the levels on Mathlib's small étale site,
`Stacks.EtaleCohomology.LAdicSheaf.RepresentationLevelPairingInput`: every other clause
(perfectness of `RΓ`, flatness, lisseness, weights, realizability) is proved.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.RepresentationLevelPairingInput`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.representationDualPairingInput_of_levelPairingInput`.

The statements consume objects defined in the standard model `HasDerivedCategory.standard` of the
derived category, which is therefore a local instance here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  Sheaf.monoidalCategory etaleModuleInverseImageSheafPullbackMonoidal
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

/-- The class of morphisms of étale sheaves of `Λ`-modules on `S` inverted by sheafification is
monoidal. -/
local instance (Λ : Type) [CommRing Λ] (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  isMonoidal_W_etaleModules (Λ := Λ) S

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The pairing of the levels of `ℱ_ρ` and `ℱ_{ρ₀^∨}`, perfect on the geometric fibres over
`X_k̄`** (input): for `X` proper over a field `k`, compactified by itself, an extension `k̄` of `k`
and `ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` continuous, there are pairings
`μₙ : (ℱ_ρ)ₙ ⊗ (ℱ_{ρ₀^∨})ₙ ⟶ ℤ/ℓⁿ⁺¹` of the levels read on Mathlib's small étale site whose
inverse images to `X_k̄` are perfect on the fibres at all points with separably closed residue
field. (On the site of Stacks 021B this pairing is
`Stacks.EtaleCohomology.representationLevelTensorPairing`, perfect on stalks by
`Stacks.EtaleCohomology.bijective_representationLevelStalkBilinear`.) -/
def LAdicSheaf.RepresentationLevelPairingInput : Prop :=
  ∀ (k : Type u) [Field k] (kbar : Type u) [Field kbar] [Algebra k kbar] (X : B.Scheme)
    [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k)) [IsProper f]
    (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ),
    ∃ μ : ∀ n, (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ
          (LAdicSheaf.representationSheaf B X x ρ hρ) n) ⊗
      (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
        (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ
          (LAdicSheaf.representationDualSheaf B X x ρ hρ) n) ⟶
      Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod (ℓ ^ (n + 1)))
        X.1.smallEtaleTopology,
      ∀ (n : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (.of Ω) ⟶ fieldBaseChange (Over.mk f) kbar),
        Function.Bijective (TensorProduct.curry (Functor.LaxMonoidal.μ
          (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
            (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))))
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (CompactificationOf.ofProper f).immersion).obj (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.representationSheaf B X x ρ hρ) n)))
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ (n + 1)))
              (CompactificationOf.ofProper f).immersion).obj
                (LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.representationDualSheaf B X x ρ hρ) n))) ≫
          (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
            (A := ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).map
            (inverseImageConstantPairing (fieldBaseChangeProj (Over.mk f) kbar) (ℓ ^ (n + 1))
              (μ n))).hom)

/-- **The dual coefficients of `ℱ_ρ`**
(`Stacks.EtaleCohomology.LAdicSheaf.RepresentationDualPairingInput`) with `F' = ℱ_{ρ₀^∨}`, given
the pairing of the levels: the levels of `ℱ_ρ` and `ℱ_{ρ₀^∨}` have perfect `RΓ` (Tag 03V3 at the
levels), those of `ℱ_{ρ₀^∨}` are flat, and lisse with flat fibres over `X_k̄`, `ℱ_{ρ₀^∨}` is
lisse, and the conclusions of Deligne's conjecture for `ρ^∨` make it pointwise `ι`-mixed of
weights `≤ 0` and `ι`-realizable. -/
theorem LAdicSheaf.representationDualPairingInput_of_levelPairingInput
    (hpair : LAdicSheaf.RepresentationLevelPairingInput B ℓ) :
    LAdicSheaf.RepresentationDualPairingInput B ℓ := by
  intro k _ _ kbar _ _ _ p q _ _ hcard hℓ X _ _ f _ _ _ _ d _ _ x r ρ hρ hD
  obtain ⟨μ, hμ⟩ := hpair k kbar X f x ρ hρ
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have : Algebra.IsAlgebraic k kbar := IsAlgClosure.isAlgebraic
  have := compactSpace_etaleFundamentalGroup X.1 x
  refine ⟨LAdicSheaf.representationDualSheaf B X x ρ hρ, μ, fun n => ?_,
    LAdicSheaf.powExact_etaleLevel_representationDualSheaf B X x ρ hρ, fun n => ?_, fun n => ?_,
    fun n Ω _ _ s => ?_, hμ, LAdicSheaf.representationDualSheaf_isLisse B X x ρ hρ,
    fun ι => ⟨?_, ?_⟩⟩
  · exact isPerfect_compactSupportFrobeniusCohomology_levelComplex_representationLAdicSheaf B X ℓ
      x (integralModel ρ hρ) (continuous_integralModel ρ hρ) f (CompactificationOf.ofProper f) kbar
      p q hcard hℓ n
  · exact isPerfect_compactSupportFrobeniusCohomology_levelComplex_representationLAdicSheaf B X ℓ
      x (contragredient (integralModel ρ hρ))
      (continuous_contragredient (continuous_integralModel ρ hρ)) f (CompactificationOf.ofProper f)
      kbar p q hcard hℓ n
  · exact isFiniteTypeLocallyConstant_inverseImage_extensionByZero_ofProper _ f kbar _
      (isFiniteTypeLocallyConstant_etaleLevel_representationLAdicSheaf B X x _ _ n)
  · exact flat_sheafFiber_inverseImage_extensionByZero_of_powExact
      (CompactificationOf.ofProper f).immersion (fieldBaseChangeProj (Over.mk f) kbar) _
      (LAdicSheaf.powExact_etaleLevel_representationDualSheaf B X x ρ hρ n) Ω s
  · exact LAdicSheaf.isPointwiseMixedOfWeightLE_representationDualSheaf B X x ρ hρ f (p ^ q) (hD ι)
  · exact LAdicSheaf.isIotaRealizable_representationDualSheaf B X x ρ hρ f (hD ι)

end Stacks.EtaleCohomology

end
