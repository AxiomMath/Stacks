module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Adjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactModuleSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors

/-!
# Integral coefficients on the small étale site

Restriction of coefficients along the unique ring map `ℤ → Λ`, for sheaves of modules on the
small étale site of a scheme, in two equivalent spellings: sheaves of `ℤ`-modules and sheaves of
abelian groups.  This is the coefficient change through which the proof of [Stacks, Tag 0GL6]
passes: the commutation of `Rf_!` with a general restriction of coefficients `Λ₁ → Λ₂` is not
proved directly, but by comparing both sides with integral coefficients, which is
[Stacks, Tag 0D6J].

The abelian-group spelling is the one the source uses -- 0D6J argues about `K_ab` and
`Z_C` -- and it is also the one the library's derived machinery is pinned to, so it is the
endpoint here; the `ℤ`-module spelling is the middle layer through which it is built.

## Main definitions

* `Stacks.EtaleCohomology.EtaleIntModules`: sheaves of `ℤ`-modules on the small étale site, in
  the module universe that sheaves of `Λ`-modules use.
* `Stacks.EtaleCohomology.EtaleAbelianSheaves`: sheaves of abelian groups on it, in that same
  universe.
* `Stacks.EtaleCohomology.etaleIntCoefficientEquivalence`: the two agree.
* `Stacks.EtaleCohomology.etaleModuleForgetToInt` and
  `Stacks.EtaleCohomology.etaleModuleForgetToAbelian`: restriction of coefficients along
  `ℤ → Λ`, in the two spellings.
* `Stacks.EtaleCohomology.etaleIntModuleExtend`,
  `Stacks.EtaleCohomology.etaleAbelianSheafExtend`: their left adjoints, `Λ ⊗_ℤ -` sheafified.
* `Stacks.EtaleCohomology.etaleIntModuleExtendForgetAdj`,
  `Stacks.EtaleCohomology.etaleAbelianExtendForgetAdj`: the adjunctions.
* `Stacks.EtaleCohomology.etaleModuleDerivedForgetToInt`,
  `Stacks.EtaleCohomology.etaleModuleDerivedForgetToAbelian`: the induced functors on unbounded
  derived categories.

## Main results

* `Stacks.EtaleCohomology.etaleModuleForgetToAbelian_eq`: forgetting to abelian groups is
  forgetting to `ℤ`-modules followed by the equivalence, on the nose.
* the `hasSheafify`, `isGrothendieckAbelian` and `enoughInjectives` instances: both integral
  coefficient categories are as good as the `Λ`-linear one.
* `Stacks.EtaleCohomology.etaleModuleForgetToInt_additive`,
  `Stacks.EtaleCohomology.etaleModuleForgetToInt_preservesFiniteColimits` and their abelian
  counterparts: forgetting to integral coefficients is additive and exact.

## Implementation notes

**The equivalence is the identity on sections, and that is what makes this route cheap.**
`Stacks.EtaleCohomology.etaleIntCoefficientEquivalence` is `CategoryTheory.sheafCompose` of
`forget₂ (ModuleCat ℤ) AddCommGrpCat`, so the sections of a sheaf and of its image are the same
object.  Every hypothesis of the form `∀ V, Module.IsTorsionFree ℤ (F.obj.obj V)` -- which is
what the dévissage behind 0D6J runs on, through
`ModuleSheafCohomology.isTorsionFree_of_mono` and
`ModuleSheafCohomology.exists_isTorsionFree_epi` -- therefore carries between the two spellings
with no transport work at all.

**Why the abelian spelling is the endpoint.**  Two independent reasons, both about universes.
`ModuleCat.free R : Type u ⥤ ModuleCat.{u} R` ties the type, the ring and the module universe
together, so the free `ℤ`-module sheaf is not constructible at the module universe used here;
`AddCommGrpCat.free : Type u ⥤ AddCommGrpCat.{u}` has no such rigidity.  And the derived
machinery is already pinned to abelian groups:
`Stacks.Cohomology.DerivedLowerShriek.rightDerivedUnit_isIso_of_corepresentable` requires a
sections functor valued in `AddCommGrpCat`.  The generalisable lesson is to pick the coefficient
category whose free functor is polymorphic in the universe one needs, because the derived
machinery is usually pinned there too.

*A related note for whoever needs the corepresentation.*
`ModuleSheafCohomology.evaluationRepresentation` is stated for `[SmallCategory C]`, which the
small étale site is not -- it is large and only essentially small -- so the universe-freed
`Stacks.Cohomology.FreeYonedaUnivLE.evaluationRepresentation` is the one that applies, at its
free universe parameter taken to be the coefficient universe.

**Why everything here is built at the level of sheaves rather than of modules.**  The
module-level route fails on universes twice, and both equations are worth recording because the
choice looks arbitrary otherwise.  `PreservesFiniteColimits (forget₂ (ModuleCat.{w} Λ)
AddCommGrpCat.{w})` leaves the unifier stuck at `max r (w + 1) =?= max (r + 1) (?u + 1)`, and
composing the module-level adjunctions fails because `ModuleCat.restrictScalars.{w, 0, r}`
presents hom universe `w` where `CategoryTheory.Equivalence.comp` wants `max r w`.  At the level
of sheaves both disappear: the forgetful functor is a composite of a functor already known to be
exact with one half of an equivalence, and the adjunction is a composite of the equivalence's
adjunction with one already constructed.

*Why this is not an instance of the general restriction of coefficients.*
`Stacks.EtaleCohomology.etaleModuleRestrictScalarsUniv` is stated for two coefficient rings in one
universe `r`, which is the generality Tag 0GL6 is about and the generality
`Stacks.EtaleCohomology.EtaleModules` admits.  Integral coefficients do not fit it: `ℤ` lives in
`Type 0` while `Λ` lives in `Type r`, and `ModuleCat.restrictScalars` needs one module universe
on both sides.  Abstracting the general definition over two ring universes does
not work: Mathlib's adjointness instances for `ModuleCat.restrictScalars` are stated at module
universe `max u₂ w` for a coefficient ring in `Type u₂`, and with both ring universes abstract
the unifier is left with `max (max r₁ r₂) (u + 1) =?= max r₂ ?w`, which it cannot solve; writing
the module universe as `max r₂ w` to match that shape instead loses the `u + 1` that essential
smallness of the étale site needs.  With `ℤ` concretely in `Type 0` the same instances present
`max 0 w`, which is `w`, and there is nothing left to solve -- so the integral case is written
out concretely here, and no second copy of the general definition is made.

A related subtlety: the first universe argument of
`ModuleCat.extendRestrictScalarsAdj` and of `ModuleCat.restrictCoextendScalarsAdj` is not the
module universe but the `v` in `max v u₂`.  For `ℤ` in `Type 0` the two coincide; for a general
coefficient ring they do not.

Sheafifiability of integral coefficients is not found by instance search --
`Stacks.EtaleCohomology.etaleModules_hasSheafify` ties the module universe to the coefficient
ring's universe -- so it is established here from
`CategoryTheory.hasSheafifyEssentiallySmallSite`, exactly as that instance is.

## References

* [Stacks Project, Tag 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

section Category

variable (X : Scheme.{u})

/-- Sheaves of `ℤ`-modules on the small étale site of `X`, in the module universe that sheaves
of `Λ`-modules for a coefficient ring in `Type r` use.  The universe parameter `r` is carried
only to fix that module universe; the coefficient ring is `ℤ`. -/
abbrev EtaleIntModules :=
  Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} ℤ)

/-- Sheaves of abelian groups on the small étale site of `X`, in the same module universe. -/
abbrev EtaleAbelianSheaves :=
  Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}

/-- Integral-coefficient presheaves on the small étale site can be sheafified. -/
instance etaleIntModules_hasSheafify :
    HasSheafify X.smallEtaleTopology (ModuleCat.{max (u + 1) r} ℤ) :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) r} _ _

/-- Abelian-group-valued presheaves on the small étale site can be sheafified. -/
instance etaleAbelianSheaves_hasSheafify :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, max (u + 1) r} _ _

/-- Sheaves of `ℤ`-modules on the small étale site form a Grothendieck abelian category. -/
instance etaleIntModules_isGrothendieckAbelian :
    IsGrothendieckAbelian.{max (u + 1) r} (EtaleIntModules.{u, r} X) :=
  have : ∀ W : X.Etaleᵒᵖ,
      HasLimitsOfShape (StructuredArrow W (equivSmallModel.{max (u + 1) r} X.Etale).inverse.op)
        (ModuleCat.{max (u + 1) r} ℤ) := fun _ ↦ inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology _

/-- Sheaves of abelian groups on the small étale site form a Grothendieck abelian category. -/
instance etaleAbelianSheaves_isGrothendieckAbelian :
    IsGrothendieckAbelian.{max (u + 1) r} (EtaleAbelianSheaves.{u, r} X) :=
  have : ∀ W : X.Etaleᵒᵖ,
      HasLimitsOfShape (StructuredArrow W (equivSmallModel.{max (u + 1) r} X.Etale).inverse.op)
        AddCommGrpCat.{max (u + 1) r} := fun _ ↦ inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology _

/-- Sheaves of `ℤ`-modules on the small étale site have enough injectives. -/
instance etaleIntModules_enoughInjectives : EnoughInjectives (EtaleIntModules.{u, r} X) :=
  have := etaleIntModules_isGrothendieckAbelian.{u, r} X
  CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- Sheaves of abelian groups on the small étale site have enough injectives. -/
instance etaleAbelianSheaves_enoughInjectives :
    EnoughInjectives (EtaleAbelianSheaves.{u, r} X) :=
  have := etaleAbelianSheaves_isGrothendieckAbelian.{u, r} X
  CategoryTheory.IsGrothendieckAbelian.enoughInjectives

/-- **Abelian sheaves and sheaves of `ℤ`-modules on the small étale site agree.**  The
equivalence is `CategoryTheory.sheafCompose` of a forgetful functor, so it is the identity on
sections. -/
def etaleIntCoefficientEquivalence :
    EtaleAbelianSheaves.{u, r} X ≌ EtaleIntModules.{u, r} X :=
  Sheaf.coefficientEquivalence X.smallEtaleTopology
    AddCommGrpCat.moduleCatIntEquivalence.{max (u + 1) r}

end Category

section Forget

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- **Forgetting to integral coefficients.**  A sheaf of `Λ`-modules on the small étale site of
`X`, read as a sheaf of `ℤ`-modules.  The underlying sheaf is unchanged. -/
abbrev etaleModuleForgetToInt :
    EtaleModules.{u, r} Λ X ⥤ EtaleIntModules.{u, r} X :=
  sheafCompose X.smallEtaleTopology
    (ModuleCat.restrictScalars.{max (u + 1) r, 0, r} (Int.castRingHom Λ))

/-- Forgetting to integral coefficients preserves finite limits, being a right adjoint. -/
instance etaleModuleForgetToInt_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModuleForgetToInt.{u, r} Λ X) :=
  inferInstance

/-- Forgetting to integral coefficients is additive. -/
instance etaleModuleForgetToInt_additive :
    (etaleModuleForgetToInt.{u, r} Λ X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Forgetting to integral coefficients preserves finite colimits.  Restriction of scalars is a
left adjoint, hence preserves sheafification, and postcomposition with a
sheafification-preserving functor commutes with colimits of sheaves. -/
instance etaleModuleForgetToInt_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleForgetToInt.{u, r} Λ X) where
  preservesFiniteColimits _ _ _ :=
    haveI : X.smallEtaleTopology.PreservesSheafification
        (ModuleCat.restrictScalars.{max (u + 1) r, 0, r} (Int.castRingHom Λ)) :=
      Sheaf.preservesSheafification_of_adjunction _
        (ModuleCat.restrictCoextendScalarsAdj.{max (u + 1) r, 0, r} (Int.castRingHom Λ))
    Sheaf.preservesColimitsOfShape_sheafCompose X.smallEtaleTopology
      (ModuleCat.restrictScalars.{max (u + 1) r, 0, r} (Int.castRingHom Λ))

/-- **Extension to `Λ`-coefficients.**  The left adjoint of forgetting to integral
coefficients: tensor the sections with `Λ` over `ℤ`, then sheafify. -/
abbrev etaleIntModuleExtend :
    EtaleIntModules.{u, r} X ⥤ EtaleModules.{u, r} Λ X :=
  Sheaf.composeAndSheafify X.smallEtaleTopology
    (ModuleCat.extendScalars.{0, r, max (u + 1) r} (Int.castRingHom Λ))

/-- **Extension of coefficients is left adjoint to forgetting to integral coefficients.** -/
def etaleIntModuleExtendForgetAdj :
    etaleIntModuleExtend.{u, r} Λ X ⊣ etaleModuleForgetToInt.{u, r} Λ X :=
  Sheaf.adjunction X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{max (u + 1) r, 0, r} (Int.castRingHom Λ))

/-- **Forgetting to integral coefficients on unbounded derived categories.** -/
abbrev etaleModuleDerivedForgetToInt :
    DerivedCategory (EtaleModules.{u, r} Λ X) ⥤ DerivedCategory (EtaleIntModules.{u, r} X) :=
  (etaleModuleForgetToInt.{u, r} Λ X).mapDerivedCategory

/-! ### The abelian-group spelling -/

/-- **Forgetting to abelian groups.**  A sheaf of `Λ`-modules on the small étale site of `X`,
read as a sheaf of abelian groups. -/
abbrev etaleModuleForgetToAbelian :
    EtaleModules.{u, r} Λ X ⥤ EtaleAbelianSheaves.{u, r} X :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})

/-- **Forgetting to abelian groups is forgetting to `ℤ`-modules followed by the equivalence.**
This is an equality, not merely an isomorphism: `forget₂ (ModuleCat Λ) AddCommGrpCat` is
definitionally restriction of scalars along `ℤ → Λ` followed by
`forget₂ (ModuleCat ℤ) AddCommGrpCat`, and the latter is the inverse of the coefficient
equivalence. -/
theorem etaleModuleForgetToAbelian_eq :
    etaleModuleForgetToAbelian.{u, r} Λ X =
      etaleModuleForgetToInt.{u, r} Λ X ⋙
        (etaleIntCoefficientEquivalence.{u, r} X).inverse :=
  rfl

/-- Forgetting to abelian groups preserves finite limits. -/
instance etaleModuleForgetToAbelian_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModuleForgetToAbelian.{u, r} Λ X) :=
  inferInstanceAs (PreservesFiniteLimits (etaleModuleForgetToInt.{u, r} Λ X ⋙
    (etaleIntCoefficientEquivalence.{u, r} X).inverse))

/-- Forgetting to abelian groups is additive. -/
instance etaleModuleForgetToAbelian_additive :
    (etaleModuleForgetToAbelian.{u, r} Λ X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Forgetting to abelian groups preserves finite colimits. -/
instance etaleModuleForgetToAbelian_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleForgetToAbelian.{u, r} Λ X) :=
  inferInstanceAs (PreservesFiniteColimits (etaleModuleForgetToInt.{u, r} Λ X ⋙
    (etaleIntCoefficientEquivalence.{u, r} X).inverse))

/-- **Extension to `Λ`-coefficients from abelian groups**, the left adjoint of forgetting to
abelian groups. -/
abbrev etaleAbelianSheafExtend :
    EtaleAbelianSheaves.{u, r} X ⥤ EtaleModules.{u, r} Λ X :=
  (etaleIntCoefficientEquivalence.{u, r} X).functor ⋙ etaleIntModuleExtend.{u, r} Λ X

/-- **Extension of coefficients is left adjoint to forgetting to abelian groups.** -/
def etaleAbelianExtendForgetAdj :
    etaleAbelianSheafExtend.{u, r} Λ X ⊣ etaleModuleForgetToAbelian.{u, r} Λ X :=
  (etaleIntCoefficientEquivalence.{u, r} X).toAdjunction.comp
    (etaleIntModuleExtendForgetAdj.{u, r} Λ X)

/-- **Forgetting to abelian groups on unbounded derived categories.** -/
abbrev etaleModuleDerivedForgetToAbelian :
    DerivedCategory (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory (EtaleAbelianSheaves.{u, r} X) :=
  (etaleModuleForgetToAbelian.{u, r} Λ X).mapDerivedCategory

end Forget

end Stacks.EtaleCohomology

end
