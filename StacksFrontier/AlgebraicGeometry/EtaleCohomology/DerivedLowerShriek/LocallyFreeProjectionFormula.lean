module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocallyFreeDual
public import StacksFrontier.CategoryTheory.Monoidal.RigidProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution

/-!
# The projection formula for `Rf_!` and a locally free sheaf on the base

Let `Λ` be a commutative ring, `f : X ⟶ Y` a morphism of schemes with a compactification
`j : X ⟶ X̄`, `f̄ : X̄ ⟶ Y`, and `N` a sheaf of `Λ`-modules on the small étale site of `Y` which is
étale-locally constant with value a finite free `Λ`-module. Then

`Rf_!(K ⊗ f⁻¹ N) ≅ Rf_! K ⊗ N`, naturally in `K ∈ D⁺(X_étale, Λ)`,

where `- ⊗ N` and `- ⊗ f⁻¹ N` are exact and act degreewise on `D⁺`.

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith`:
  `- ⊗ N` is additive and exact.
* `etaleModuleDirectImageProjectionIso`: `f_*(M ⊗ f⁻¹ N) ≅ f_* M ⊗ N`.
* `etaleModuleExtensionByZeroProjectionIso`: `j_!(M ⊗ j⁻¹ N) ≅ j_! M ⊗ N`.
* `derivedLowerShriekProjectionIso`: the projection formula for `Rf_!`.

## Implementation notes

`N` is dualizable (`Stacks.EtaleCohomology.etaleModuleDualExactPairing`), so on sheaves both
projection formulas are formal (`CategoryTheory.Adjunction.tensorRightProjectionIso` and
`CategoryTheory.Adjunction.tensorRightProjectionIsoOfMonoidalRight`): the inverse image is
monoidal, and for the open immersion `j` it is the right adjoint of `j_!`. Tensoring with the
dualizable `f̄⁻¹ N` carries injectives to injectives, so
`Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso` upgrades the formula for `f̄_*`
to `Rf̄_*`; `j_!` is exact, so it upgrades the one for `j_!` for free. Composing the two gives the
formula for `Rf_! = Rf̄_* ∘ j_!`. No properness and no torsion hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

variable {Λ : Type} [CommRing Λ]

/-- The category of `Λ`-modules in `Type (u + 1)` has limits of size `u + 1`. -/
local instance hasLimitsOfSize_moduleCat_locallyFreeProjectionFormula :
    HasLimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} Λ) :=
  ModuleCat.instHasLimitsOfSize.{u + 1, u + 1, 0}

/-- Sheafification on the slices of the small étale site, at the coefficient universe `u + 1`. -/
local instance hasWeakSheafify_smallEtale_over' {S : Scheme.{u}} (V : S.Etale) :
    HasWeakSheafify (S.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ) :=
  haveI := Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, u + 1}
    (S.smallEtaleTopology.over V) Λ
  inferInstance

/-! ### Sheaves with duals on both sides -/

section Dualizable

/-- Tensoring with an étale sheaf of modules having duals on both sides is additive and exact:
`- ⊗ X` is both a left and a right adjoint. -/
theorem additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_exactPairing
    {S : Scheme.{u}} (X X' : EtaleModules.{u, 0} Λ S) (h₁ : ExactPairing X X')
    (h₂ : ExactPairing X' X) :
    (MonoidalCategory.tensorRight X).Additive ∧
      PreservesFiniteLimits (MonoidalCategory.tensorRight X) ∧
      PreservesFiniteColimits (MonoidalCategory.tensorRight X) := by
  have hl : PreservesLimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X) :=
    (tensorRightAdjunction X' X).rightAdjoint_preservesLimits
  have hc : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X) :=
    (tensorRightAdjunction X X').leftAdjoint_preservesColimits
  exact ⟨Functor.additive_of_preserves_binary_products _,
    PreservesLimitsOfSize.preservesFiniteLimits _,
    PreservesColimitsOfSize.preservesFiniteColimits _⟩

attribute [local instance] Sheaf.braidedCategory

/-- The swapped exact pairing of an étale sheaf of modules and its dual. -/
abbrev etaleModuleDualExactPairingSwap {S : Scheme.{u}} (N : EtaleModules.{u, 0} Λ S)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ S.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N) :
    ExactPairing (etaleModuleDual N) N :=
  letI := etaleModuleDualExactPairing N hN
  BraidedCategory.exactPairing_swap N (etaleModuleDual N)

/-- **Tensoring with an étale-locally free sheaf of finite rank is additive and exact.** -/
theorem additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
    {S : Scheme.{u}} (N : EtaleModules.{u, 0} Λ S)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ S.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N) :
    (MonoidalCategory.tensorRight N).Additive ∧
      PreservesFiniteLimits (MonoidalCategory.tensorRight N) ∧
      PreservesFiniteColimits (MonoidalCategory.tensorRight N) :=
  additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_exactPairing N
    (etaleModuleDual N) (etaleModuleDualExactPairing N hN) (etaleModuleDualExactPairingSwap N hN)

end Dualizable

/-! ### The projection formulas on sheaves -/

section Sheaves

attribute [local instance] Sheaf.braidedCategory etaleModuleInverseImageSheafPullbackMonoidal

/-- The inverse image of the exact pairing between an étale-locally free sheaf of finite rank and
its dual. -/
abbrev etaleModuleInverseImageDualExactPairing {X S : Scheme.{u}} (g : X ⟶ S)
    (N : EtaleModules.{u, 0} Λ S)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ S.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N) :
    ExactPairing ((etaleModuleInverseImage.{u, 0} Λ g).obj N)
      ((etaleModuleInverseImage.{u, 0} Λ g).obj (etaleModuleDual N)) :=
  letI := etaleModuleDualExactPairing N hN
  ExactPairing.map (etaleModuleInverseImage.{u, 0} Λ g) N (etaleModuleDual N)

/-- Tensoring with the inverse image of an étale-locally free sheaf of finite rank is additive and
exact. -/
theorem additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_inverseImage
    {X S : Scheme.{u}} (g : X ⟶ S) (N : EtaleModules.{u, 0} Λ S)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ S.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N) :
    (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ g).obj N)).Additive ∧
      PreservesFiniteLimits
        (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ g).obj N)) ∧
      PreservesFiniteColimits
        (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ g).obj N)) :=
  let := etaleModuleInverseImageDualExactPairing g N hN
  additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_exactPairing _ _
    (etaleModuleInverseImageDualExactPairing g N hN) (BraidedCategory.exactPairing_swap _ _)

/-- **Tensoring with the inverse image of an étale-locally free sheaf of finite rank preserves
injective objects.** -/
theorem injective_tensorRight_inverseImage_obj {X S : Scheme.{u}} (g : X ⟶ S)
    (N : EtaleModules.{u, 0} Λ S)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ S.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N)
    (I : EtaleModules.{u, 0} Λ X) (hI : Injective I) :
    Injective ((MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ g).obj N)).obj I) :=
  let := etaleModuleInverseImageDualExactPairing g N hN
  (preservesInjectiveObjects_tensorRight_of_exactPairing _ _
    (etaleModuleInverseImageDualExactPairing g N hN)
    (BraidedCategory.exactPairing_swap _ _)).injective_obj hI

/-- **The projection formula for the direct image**, `g_*(M ⊗ g⁻¹ N) ≅ g_* M ⊗ N` naturally in
`M`, for an arbitrary morphism of schemes `g` and `N` étale-locally free of finite rank. -/
def etaleModuleDirectImageProjectionIso {X S : Scheme.{u}} (g : X ⟶ S)
    (N : EtaleModules.{u, 0} Λ S)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ S.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N) :
    MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ g).obj N) ⋙
        etaleModuleDirectImage.{u, 0} Λ g ≅
      etaleModuleDirectImage.{u, 0} Λ g ⋙ MonoidalCategory.tensorRight N :=
  letI := etaleModuleDualExactPairingSwap N hN
  (etaleModuleInverseImageAdj.{u, 0} Λ g).tensorRightProjectionIso N (etaleModuleDual N)

/-- **The projection formula for extension by zero**, `j_!(M ⊗ j⁻¹ N) ≅ j_! M ⊗ N` naturally in
`M`, for an étale morphism `j` and a dualizable `N`. -/
def etaleModuleExtensionByZeroProjectionIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (N D : EtaleModules.{u, 0} Λ X) [ExactPairing N D] :
    MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ j).obj N) ⋙
        etaleModuleExtensionByZero.{u, 0} Λ j ≅
      etaleModuleExtensionByZero.{u, 0} Λ j ⋙ MonoidalCategory.tensorRight N :=
  ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).ofNatIsoRight
    (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm).tensorRightProjectionIsoOfMonoidalRight
      N D

/-- Tensoring on the right with isomorphic objects gives isomorphic functors. -/
def tensorRightIsoOfIso {S : Scheme.{u}} {A B : EtaleModules.{u, 0} Λ S} (e : A ≅ B) :
    MonoidalCategory.tensorRight A ≅ MonoidalCategory.tensorRight B :=
  NatIso.ofComponents (fun M => whiskerLeftIso M e) (fun φ => (whisker_exchange φ e.hom).symm)

/-- The inverse image along `f = j ≫ f̄` is the inverse image along `f̄` followed by the one along
the open immersion `j` of the compactification. -/
def etaleModuleInverseImageCompactificationIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (N : EtaleModules.{u, 0} Λ Y) :
    (etaleModuleInverseImage.{u, 0} Λ f).obj N ≅
      (etaleModuleInverseImage.{u, 0} Λ j.immersion).obj
        ((etaleModuleInverseImage.{u, 0} Λ j.toBase).obj N) :=
  eqToIso (congrArg (fun h => (etaleModuleInverseImage.{u, 0} Λ h).obj N)
      (Over.w j.obj.hom).symm) ≪≫
    (etaleModuleInverseImageCompIso.{u, 0} Λ j.immersion j.toBase).app N

/-- The projection formula for the extension by zero along the open immersion of a
compactification, with the coefficient `f⁻¹ N` on the source. -/
def etaleModuleCompactificationExtensionByZeroProjectionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N) :
    MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ f).obj N) ⋙
        etaleModuleExtensionByZero.{u, 0} Λ j.immersion ≅
      etaleModuleExtensionByZero.{u, 0} Λ j.immersion ⋙
        MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ j.toBase).obj N) :=
  letI := etaleModuleInverseImageDualExactPairing j.toBase N hN
  Functor.isoWhiskerRight (tensorRightIsoOfIso (etaleModuleInverseImageCompactificationIso f j N))
      (etaleModuleExtensionByZero.{u, 0} Λ j.immersion) ≪≫
    etaleModuleExtensionByZeroProjectionIso j.immersion _
      ((etaleModuleInverseImage.{u, 0} Λ j.toBase).obj (etaleModuleDual N))

end Sheaves

/-! ### The projection formula for `Rf_!` -/

section StandardModel

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The projection formula for `Rf_!` and an étale-locally free sheaf of finite rank on the
base**: for `f : X ⟶ Y` with a compactification `j`, and `N` a sheaf of `Λ`-modules on `Y_étale`
which is étale-locally constant with value a finite free `Λ`-module,

`Rf_!(K ⊗ f⁻¹ N) ≅ Rf_! K ⊗ N`

naturally in `K ∈ D⁺(X_étale, Λ)`, the exact functors `- ⊗ f⁻¹ N` and `- ⊗ N` acting degreewise.
No properness beyond that of the compactification and no torsion hypothesis is used.

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard` of the derived category, and so does this isomorphism. -/
def derivedLowerShriekProjectionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (N : EtaleModules.{u, 0} Λ Y)
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E) N) :
    haveI := (additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_inverseImage
      f N hN).1
    haveI := (additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_inverseImage
      f N hN).2.1
    haveI := (additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_inverseImage
      f N hN).2.2
    haveI :=
      (additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
        N hN).1
    haveI :=
      (additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
        N hN).2.1
    haveI :=
      (additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
        N hN).2.2
    (MonoidalCategory.tensorRight
          ((etaleModuleInverseImage.{u, 0} Λ f).obj N)).mapDerivedCategoryPlus ⋙
        derivedLowerShriek.{u, 0} f j Λ ≅
      derivedLowerShriek.{u, 0} f j Λ ⋙
        (MonoidalCategory.tensorRight N).mapDerivedCategoryPlus :=
  have hf := additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_inverseImage f N hN
  have hg := additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_inverseImage
    j.toBase N hN
  have h :=
    additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith N hN
  haveI := hf.1; haveI := hf.2.1; haveI := hf.2.2
  haveI := hg.1; haveI := hg.2.1; haveI := hg.2.2
  haveI := h.1; haveI := h.2.1; haveI := h.2.2
  let jShriek := etaleModuleExtensionByZero.{u, 0} Λ j.immersion
  let gStar := etaleModuleDirectImage.{u, 0} Λ j.toBase
  let e₁ := Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso
    (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ f).obj N))
    (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ j.toBase).obj N))
    jShriek jShriek (etaleModuleCompactificationExtensionByZeroProjectionIso f j N hN)
    (fun _ _ => Functor.rightAcyclic_of_exact jShriek _)
  let e₂ := Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso
    (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ j.toBase).obj N))
    (MonoidalCategory.tensorRight N) gStar gStar
    (etaleModuleDirectImageProjectionIso j.toBase N hN)
    (fun I hI =>
      haveI := injective_tensorRight_inverseImage_obj j.toBase N hN I hI
      Functor.rightAcyclic_of_injective gStar _)
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e₁ gStar.rightDerivedFunctorPlus ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft jShriek.rightDerivedFunctorPlus e₂ ≪≫
    (Functor.associator _ _ _).symm

end StandardModel

end Stacks.EtaleCohomology
