module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.CohomologyAffineReduction.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QuasiCoherentPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison

/-!
# Exactness of pushforward along an affine morphism on quasi-coherent modules

Let `f : X ⟶ Y` be an affine morphism of schemes. Pushforward of quasi-coherent modules
`QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)` is then exact.

Left exactness holds for any quasi-compact and quasi-separated morphism: pushforward of all
modules is a right adjoint, and the inclusion of the quasi-coherent modules is exact and
reflects limits. Right exactness is where affineness enters: the higher direct images of a
quasi-coherent module along an affine morphism vanish, so every quasi-coherent module is
acyclic for pushforward, and Leray's acyclicity criterion turns a short exact sequence of
quasi-coherent modules into a short exact sequence after pushforward.

## Main results

* `AlgebraicGeometry.affinePushforwardPreservesFiniteLimits`: pushforward along an affine
  morphism preserves finite limits of quasi-coherent modules.
* `AlgebraicGeometry.rightAcyclic_pushforward_of_isQuasicoherent`: a quasi-coherent module is
  acyclic for pushforward along an affine morphism.
* `AlgebraicGeometry.affinePushforwardPreservesFiniteColimits`: pushforward along an affine
  morphism preserves finite colimits of quasi-coherent modules.

## Implementation notes

The category of `𝒪_X`-modules on a scheme has two definitionally equal but syntactically
distinct spellings, `AlgebraicGeometry.Scheme.Modules X` and
`SheafOfModules X.ringCatSheaf`; quasi-coherence is stated in the second and pushforward in the
first, so the object property is ascribed to `X.Modules` wherever the two meet and the
exactness instances of the inclusion are supplied as explicit arguments.

## References

* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 08D7.** Pushforward along an affine morphism preserves finite limits
of quasi-coherent modules. -/
@[stacks 08D7 "exactness, kernels"]
public instance affinePushforwardPreservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] : PreservesFiniteLimits (quasicoherentPushforward f) := by
  have h : PreservesFiniteLimits
      (quasicoherentPushforward f ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι) := by
    change PreservesFiniteLimits
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ Scheme.Modules.pushforward f)
    exact @comp_preservesFiniteLimits _ _ _ _ _ _
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι (Scheme.Modules.pushforward f)
      (Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits X)
      (Stacks.SchemeCohomology.pushforward_preservesFiniteLimits f)
  exact preservesFiniteLimits_of_reflects_of_preserves (quasicoherentPushforward f)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι

/-- Every quasi-coherent `𝒪_X`-module is acyclic for pushforward along an affine morphism, its
higher direct images vanishing by [Stacks, Tag 01XC]. -/
public theorem rightAcyclic_pushforward_of_isQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] (M : X.Modules) (hM : M.IsQuasicoherent) :
    letI : HasDerivedCategory X.Modules := HasDerivedCategory.standard _
    letI : HasDerivedCategory Y.Modules := HasDerivedCategory.standard _
    (Scheme.Modules.pushforward f).rightAcyclic M := by
  let : HasDerivedCategory X.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory Y.Modules := HasDerivedCategory.standard _
  let : EnoughInjectives X.Modules := IsGrothendieckAbelian.enoughInjectives
  let : M.IsQuasicoherent := hM
  exact ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (Scheme.Modules.pushforward f) M).2
      (Stacks.SchemeCohomology.pushforward_preservesFiniteLimits f)).2 fun i hi =>
      Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom f M i hi

/-- **Stacks Project, Tag 08D7.** Pushforward along an affine morphism preserves finite colimits
of quasi-coherent modules. -/
@[stacks 08D7 "exactness, cokernels"]
public instance affinePushforwardPreservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] : PreservesFiniteColimits (quasicoherentPushforward f) := by
  let P : ObjectProperty X.Modules := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let Q : ObjectProperty Y.Modules := SheafOfModules.isQuasicoherent Y.ringCatSheaf
  let F : P.FullSubcategory ⥤ Q.FullSubcategory := quasicoherentPushforward f
  let I : P.FullSubcategory ⥤ X.Modules := P.ι
  let J : Q.FullSubcategory ⥤ Y.Modules := Q.ι
  let G : X.Modules ⥤ Y.Modules := Scheme.Modules.pushforward f
  let : Abelian P.FullSubcategory := quasicoherentModules_abelian X
  let : Abelian Q.FullSubcategory := quasicoherentModules_abelian Y
  let : Preadditive P.FullSubcategory := Abelian.toPreadditive
  let : Preadditive Q.FullSubcategory := Abelian.toPreadditive
  let : HasDerivedCategory X.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory Y.Modules := HasDerivedCategory.standard _
  let : EnoughInjectives X.Modules := IsGrothendieckAbelian.enoughInjectives
  let : PreservesFiniteLimits G := Stacks.SchemeCohomology.pushforward_preservesFiniteLimits f
  let : G.Additive := G.additive_of_preserves_binary_products
  let : PreservesFiniteLimits I :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits X
  let : PreservesFiniteColimits I :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteColimits X
  let : PreservesFiniteLimits J :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteLimits Y
  let : PreservesFiniteColimits J :=
    Stacks.AlgebraicGeometry.QuasicoherentDerived.isQuasicoherent_ι_preservesFiniteColimits Y
  let : I.Additive := I.additive_of_preserves_binary_products
  let : J.Additive := J.additive_of_preserves_binary_products
  let : F.Additive := by
    constructor
    intro A B g h
    apply J.map_injective
    change G.map (I.map (g + h)) = G.map (I.map g) + G.map (I.map h)
    rw [Functor.map_add I, Functor.map_add G]
  have hAcyclic (M : P.FullSubcategory) : G.rightAcyclic (I.obj M) :=
    rightAcyclic_pushforward_of_isQuasicoherent f M.obj M.property
  have hShort : ∀ S : ShortComplex P.FullSubcategory, S.ShortExact → (S.map F).ShortExact :=
    fun S hS => CategoryTheory.ShortExact.reflects_shortExact_of_faithful J
      (show ((S.map F).map J).ShortExact from
        ((Functor.rightAcyclic_and_shortExact_map_of_shortExact G (S.map I)
          (hS.map_of_exact I)).1 (hAcyclic S.X₁) (hAcyclic S.X₃)).2)
  have hF := ((Functor.exact_tfae F).out 1 4).mp hShort
  exact hF.2

end AlgebraicGeometry

end
