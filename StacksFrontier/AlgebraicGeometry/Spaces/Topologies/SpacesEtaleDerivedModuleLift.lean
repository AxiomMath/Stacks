module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleQuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Topologies.GlobalPresentationComparison

/-!
# The derived transport from the small étale site to the spaces-étale site

Let `X` be an algebraic space over a scheme `S`. The transport
`ι : Mod(𝒪_{X_étale}) ⥤ Mod(𝒪_{X_{spaces,étale}})` of
`AlgebraicGeometry.Space.toSpacesEtaleModules` raises the universe of the module sections from `u`
to `u + 1` and then extends along the comparison of Stacks 03G1. It is the universe lift
`Stacks.SheafOfModules.moduleULift` followed by the equivalence of Stacks 03G1 at module universe
`u + 1`, hence exact, and so it induces a functor `ι : D(𝒪_{X_étale}) ⥤ D(𝒪_{X_{spaces,étale}})` on
derived categories. This functor commutes with cohomology sheaves, and it carries `D_QCoh` into
`D_QCoh` and reflects it.

It is not an equivalence onto `D_QCoh`: at the module universe `u + 1` quasi-coherent modules may
have sections which are not `u`-small.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleToSmallEtaleModulesEquivalence`: the equivalence of
  Stacks 03G1 at module universe `u + 1`, with functor
  `AlgebraicGeometry.Space.spacesEtaleToSmallEtaleModulesSpacesEtaleQuasicoherentWeakSerre`.
* `AlgebraicGeometry.Space.toSpacesEtaleDerivedModules`: the derived transport `ι`.

## Main results

* `AlgebraicGeometry.Space.toSpacesEtaleModules_eq`: `ι` is the universe lift followed by the
  inverse of that equivalence.
* `AlgebraicGeometry.Space.qcohDerived_iff_toSpacesEtaleDerivedModules_obj`: an object of
  `D(𝒪_{X_étale})` lies in `D_QCoh` exactly when its transport does.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
-- No global `HasDerivedCategory` instance applies to modules on the small étale or spaces-étale
-- sites, which are not `SmallCategory`; at low priority the standard model chooses nothing where
-- a global one exists.
attribute [local instance low] HasDerivedCategory.standard
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The universe lift of `𝒪_X`-modules on the small étale site of `X`, from sections in `Type u`
to sections in `Type (u + 1)`. -/
abbrev smallEtaleModuleULift : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u + 1} B S hS X.1 X.2 :=
  Stacks.SheafOfModules.moduleULift.{u + 1, u} _

/-- The equivalence of Stacks 03G1 between the `𝒪_X`-modules on `X_{spaces,étale}` and the
`𝒪_X`-modules on `X_étale`, both with sections in `Type (u + 1)`. -/
abbrev spacesEtaleToSmallEtaleModulesEquivalence :
    SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O) ≌
      Modules.{u, u + 1} B S hS X.1 X.2 :=
  (comparisonModuleEquivalence B S hS X).trans
    (Stacks.Modules.sheafRingULiftEquiv.{u + 1, u, u, 0, u + 1}
      (isSheaf_structureRingPresheaf_smallEtaleRingedSite_spacesEtaleQuasicoherentWeakSerre
        B S hS X)
      (isSheaf_structureRingPresheaf_forget B S hS X.1 X.2))

/-- **`ι` is the universe lift followed by the inverse of the equivalence of Stacks 03G1**, on
the nose: the lift of the coefficient ring sheaf changes neither the sections nor the maps. -/
theorem toSpacesEtaleModules_eq :
    toSpacesEtaleModules B S hS X =
      smallEtaleModuleULift B S hS X ⋙
        (spacesEtaleToSmallEtaleModulesEquivalence B S hS X).inverse :=
  rfl

/-- The universe lift of `𝒪_X`-modules on `X_étale` is additive. -/
instance : (smallEtaleModuleULift B S hS X).Additive :=
  inferInstanceAs (Stacks.SheafOfModules.moduleULift.{u + 1, u} _).Additive

/-- The universe lift of `𝒪_X`-modules on `X_étale` preserves finite limits. -/
instance : PreservesFiniteLimits (smallEtaleModuleULift B S hS X) :=
  Stacks.SheafOfModules.preservesFiniteLimits_moduleULift.{u + 1, u, u}

/-- The universe lift of `𝒪_X`-modules on `X_étale` preserves finite colimits. -/
instance : PreservesFiniteColimits (smallEtaleModuleULift B S hS X) :=
  Stacks.SheafOfModules.preservesFiniteColimits_moduleULift _

/-- The inverse of the equivalence of Stacks 03G1 is additive. -/
instance : (spacesEtaleToSmallEtaleModulesEquivalence B S hS X).inverse.Additive := by
  have : (spacesEtaleToSmallEtaleModulesEquivalence B S hS X).inverse.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  exact Functor.additive_of_preserves_binary_products _

/-- The transport `ι` of modules is additive. -/
instance : (toSpacesEtaleModules B S hS X).Additive :=
  inferInstanceAs (smallEtaleModuleULift B S hS X ⋙
    (spacesEtaleToSmallEtaleModulesEquivalence B S hS X).inverse).Additive

/-- The transport `ι` of modules preserves finite limits. -/
instance : PreservesFiniteLimits (toSpacesEtaleModules B S hS X) :=
  inferInstanceAs (PreservesFiniteLimits (smallEtaleModuleULift B S hS X ⋙
    (spacesEtaleToSmallEtaleModulesEquivalence B S hS X).inverse))

/-- The transport `ι` of modules preserves finite colimits. -/
instance : PreservesFiniteColimits (toSpacesEtaleModules B S hS X) :=
  inferInstanceAs (PreservesFiniteColimits (smallEtaleModuleULift B S hS X ⋙
    (spacesEtaleToSmallEtaleModulesEquivalence B S hS X).inverse))

/-- The standard model of the derived category of `𝒪_X`-modules on `X_{spaces,étale}`, the model
at which the derived pullbacks of Stacks 06YY between spaces-étale ringed topoi are built. It is
passed explicitly: a small-Hom model is a global instance for these modules. -/
abbrev spacesEtaleHasDerivedCategory :
    HasDerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) :=
  HasDerivedCategory.standard _

/-- **The derived transport `ι : D(𝒪_{X_étale}) ⥤ D(𝒪_{X_{spaces,étale}})`**, induced by the
exact functor `AlgebraicGeometry.Space.toSpacesEtaleModules`. -/
abbrev toSpacesEtaleDerivedModules :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      @DerivedCategory (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) _ _
        (spacesEtaleHasDerivedCategory B S hS X) :=
  letI := spacesEtaleHasDerivedCategory B S hS X
  (toSpacesEtaleModules B S hS X).mapDerivedCategory

/-- The cohomology sheaves of `ιK` are the transports of the cohomology sheaves of `K`. -/
abbrev toSpacesEtaleDerivedModulesHomologyIso (n : ℤ) :
    toSpacesEtaleDerivedModules B S hS X ⋙
        @DerivedCategory.homologyFunctor _ _ _ (spacesEtaleHasDerivedCategory B S hS X) n ≅
      DerivedCategory.homologyFunctor _ n ⋙ toSpacesEtaleModules B S hS X :=
  letI := spacesEtaleHasDerivedCategory B S hS X
  (toSpacesEtaleModules B S hS X).mapDerivedCategoryHomologyFunctorIso n

/-- **`ι` preserves and reflects `D_QCoh`**: an object of `D(𝒪_{X_étale})` has quasi-coherent
cohomology sheaves exactly when its transport to `X_{spaces,étale}` has. -/
theorem qcohDerived_iff_toSpacesEtaleDerivedModules_obj
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    QcohDerived B S hS X K ↔
      @DerivedCategoryB.derivedCategoryB _ _ _ (spacesEtaleHasDerivedCategory B S hS X)
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O))
        ((toSpacesEtaleDerivedModules B S hS X).obj K) := by
  let := spacesEtaleHasDerivedCategory B S hS X
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · have := h n
    exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((toSpacesEtaleDerivedModulesHomologyIso B S hS X n).app K).symm
      (isQuasicoherentOnSite_toSpacesEtaleModules B S hS X _)
  · have : ((toSpacesEtaleModules B S hS X).obj
        ((DerivedCategory.homologyFunctor _ n).obj K)).IsQuasicoherentOnSite :=
      SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((toSpacesEtaleDerivedModulesHomologyIso B S hS X n).app K) (h n)
    exact isQuasicoherentOnSite_of_toSpacesEtaleModules B S hS X _

end AlgebraicGeometry.Space

end
