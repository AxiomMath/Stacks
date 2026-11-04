module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactCocontinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProjectionPullback
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# `𝒪`-module coefficients: étale cohomology on the big and the small site agree

Let `B` be a big étale site and let `f : T ⟶ S` be a morphism of `B`.  This file is the
`𝒪`-module companion of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/Cohomology.lean`: for a complex
`M` of sheaves of `𝒪`-modules on the big étale site over `S`, cohomology over the object
`T ⟶ S` agrees with cohomology on the small étale site of `T` of `i_f^*M`.

This is Stacks 0DDH, part (6), computed on underlying complexes of abelian sheaves.

## The two inputs, and why nothing else is needed

`i_f^*` on `𝒪`-modules *is* restriction along the functor `V/T ↦ V/S` presenting `i_f`, with no
change-of-rings in between, because `i_f^{-1}𝒪 = 𝒪`.  Both facts are definitional here:

* `AlgebraicGeometry.smallEtaleModuleInverseImageRing_eq` — `i_f^{-1}𝒪 = 𝒪` as sheaves of rings
  on the small étale site of `T`, by `rfl`.  (It is the `RingCat`-valued form of
  `AlgebraicGeometry.smallEtaleToBig_structureSheaf`, which is stated for the `CommRingCat`-valued
  structure sheaves of the two ringed sites.)
* `AlgebraicGeometry.smallEtaleModuleRestriction_comp_toSheaf` — forgetting the module structure
  turns `i_f^*` into the abelian `i_f^{-1}`, again by `rfl`.

So the comparison is the abelian comparison
`AlgebraicGeometry.bigSmallEtaleCohomologyIso` (Stacks 0DDH, part (5)) read through the
forgetful functor `SheafOfModules.toSheaf`, and nothing about module coefficients has to be
proved a second time.

## Cohomology of a module complex

In the source, `H^n_étale(T, M)` for `M` in `D(𝒪)` is `H^n` of the right derived functor of
sections on the derived category of modules. The comparison here is the one on underlying
complexes of abelian sheaves: both sides below are `RΓ` of the image of the coefficient object
under `SheafOfModules.toSheaf`. The two agree by Stacks 0D6J, and the statement with `RΓ` taken in
`D(𝒪)` is `AlgebraicGeometry.bigSmallEtaleModuleSectionsCohomologyIso` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/ModuleSectionsCohomology.lean`,
which is deduced from this one by
`Stacks.Cohomology.ForgetModuleUnivLE.derivedForgetIso` on the two sites.

Parts (2) and (4) of Stacks 0DDH are not here, and the reason is not the structure map: `π_S^♯`
is the identity too (`AlgebraicGeometry.smallEtalePiStructureSharp_eq_id`). It is the direction.
`π_S^*` is the *left* adjoint of restriction — the module lower shriek of Stacks 0797 along the
small étale inclusion — and that is neither left exact
(`Stacks.SheafOfModules.lowerShriek_not_preservesFiniteLimits`) nor compatible with forgetting
the module structure (`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic`, whose
counterexample functor is fully faithful, final, continuous and cocontinuous with the identity
structure map, which is the shape of the small étale inclusion). So `Lπ_S^*` is a genuine left
derived functor, the underlying abelian complex of `Lπ_S^*K` is not `π_S^{-1}` of the underlying
abelian complex of `K`, and parts (2) and (4) do not follow from the abelian parts (1) and (3)
the way part (6) follows from part (5).

Part (2) is proved from part (6) at the identity morphism of `S`, in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/ModuleProjectionPullback.lean`,
where `π_S^*` and `Lπ_S^*` are built at this file's module universe; part (4) is proved from
part (6) at a general `f` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ComparingBigSmall/DerivedModulePullback.lean`,
where the identity `Lf_small^* ≅ i_f^* ∘ Lπ_S^*` is established.

## Main definitions

* `AlgebraicGeometry.smallEtaleModuleRestriction` — `i_f^*` on sheaves of `𝒪`-modules.

## Main results

* `AlgebraicGeometry.bigSmallEtaleModuleCohomologyIso` — Stacks 0DDH, part (6), on underlying
  abelian complexes:
  `H^n_étale(T, M) = H^n(T_étale, i_f^*M)`.

## References

* [Stacks Project, Tag 0DDH](https://stacks.math.columbia.edu/tag/0DDH)
* [Stacks Project, Tag 0DD8](https://stacks.math.columbia.edu/tag/0DD8)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- **`i_f^{-1}𝒪 = 𝒪`, at the sheaves of rings the module apparatus reads.** Restricting the
structure sheaf of the big étale site over `S` along the functor `V/T ↦ V/S` presenting `i_f`
returns the structure sheaf of the small étale site of `T`.

This is `AlgebraicGeometry.smallEtaleToBig_structureSheaf` at `RingCat` instead of
`CommRingCat`: both structure sheaves are global functions on the underlying scheme, and the
functor presenting `i_f` composed with the underlying-scheme functor of the big site over `S` is
the underlying-scheme functor of the small site of `T`.

This declaration carries no Stacks attribute: the clause of Stacks 070R that it states is
already registered, on `AlgebraicGeometry.smallEtaleToBig_structureSheaf`, and this is that same
statement about the `RingCat`-valued structure sheaves rather than a further clause of the tag. -/
public theorem smallEtaleModuleInverseImageRing_eq :
    Stacks.SheafOfModules.inverseImageRing
        (SmallEtale.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property)
        (smallEtaleToBigEtaleFunctor B T S f)
        (BigEtaleOver.structureSheaf B S.obj S.property) =
      SmallEtale.structureSheaf B T.obj T.property :=
  rfl

/-- **`i_f^*` on sheaves of `𝒪`-modules.** A sheaf of `𝒪`-modules on the big étale site over `S`
is restricted along the functor `V/T ↦ V/S` presenting `i_f` and read as a sheaf of modules over
the structure sheaf of the small étale site of `T`, which is legitimate by
`AlgebraicGeometry.smallEtaleModuleInverseImageRing_eq`. -/
public abbrev smallEtaleModuleRestriction :
    SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property) ⥤
      SheafOfModules.{u + 1} (SmallEtale.structureSheaf B T.obj T.property) :=
  Stacks.SheafOfModules.inverseImage.{u + 1}
    (SmallEtale.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)
    (smallEtaleToBigEtaleFunctor B T S f)
    (BigEtaleOver.structureSheaf B S.obj S.property)

/-- **Forgetting the module structure turns `i_f^*` into the abelian `i_f^{-1}`.** Both are
restriction along the functor presenting `i_f` on the underlying presheaves, so the square
commutes on the nose. -/
public theorem smallEtaleModuleRestriction_comp_toSheaf :
    smallEtaleModuleRestriction B T S f ⋙
        SheafOfModules.toSheaf.{u + 1} (SmallEtale.structureSheaf B T.obj T.property) =
      SheafOfModules.toSheaf.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property) ⋙
        smallEtaleRestriction B T S f :=
  rfl

/-- `i_f^*` on `𝒪`-modules is additive: on underlying presheaves it is restriction along the
functor presenting `i_f`. This is `SheafOfModules.pushforward_additive` at the spelling
`Stacks.SheafOfModules.inverseImage`, which instance search does not unfold. -/
public instance smallEtaleModuleRestriction_additive :
    (smallEtaleModuleRestriction B T S f).Additive where
  map_add := rfl

/-- `i_f^*` on `𝒪`-modules preserves finite limits, being the direct image of sheaves of modules
along a continuous functor (Stacks 04BD (2), left exact half). As for additivity the instance has
to be named, instance search not unfolding `Stacks.SheafOfModules.inverseImage`. -/
public instance smallEtaleModuleRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (smallEtaleModuleRestriction B T S f) :=
  SheafOfModules.preservesFiniteLimits_pushforward.{u + 1}
    (Stacks.SheafOfModules.structureMap
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property)
      (smallEtaleToBigEtaleFunctor B T S f)
      (BigEtaleOver.structureSheaf B S.obj S.property))

section Exactness

/-- Forgetting the module structure preserves finite colimits, on the big étale site over `S`. -/
public instance bigEtaleToSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1}
      (BigEtaleOver.structureSheaf B S.obj S.property)) :=
  Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{u + 1} _

/-- Forgetting the module structure preserves finite colimits, on the small étale site of `T`. -/
public instance smallEtaleToSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1}
      (SmallEtale.structureSheaf B T.obj T.property)) :=
  Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{u + 1} _

/-- `i_f^*` on `𝒪`-modules preserves finite colimits: the functor presenting `i_f` is
cocontinuous, hence almost cocontinuous, which is the hypothesis under which the direct image of
sheaves of modules is right exact (Stacks 04BD (2)). -/
public instance smallEtaleModuleRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (smallEtaleModuleRestriction B T S f) :=
  open Stacks.SheafOfModules.PushforwardRightExact in
  preservesFiniteColimits_pushforward_of_isAlmostCocontinuous
    (smallEtaleToBigEtaleFunctor B T S f) _
    (isAlmostCocontinuous_of_isCocontinuous (smallEtaleToBigEtaleFunctor B T S f)
      (SmallEtale.topology B T.obj T.property)
      (BigEtaleOver.topology B S.obj S.property))

end Exactness

section Comparison

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

/-- **Stacks 0DDH, part (6), on underlying abelian complexes.** Let `f : T ⟶ S` be a morphism
of a big étale site and let `M` be
an unbounded complex of sheaves of `𝒪`-modules on the big étale site over `S`. Cohomology over
the object `T ⟶ S` of the big étale site of `S` agrees with cohomology on the small étale site of
`T` of `i_f^*M`, naturally in `M`:
`H^n_étale(T, M) = H^n(T_étale, i_f^*M)`.

Both sides are `RΓ` of abelian sheaves applied after `SheafOfModules.toSheaf`; the statement with
`RΓ` taken in `D(𝒪)`, as in the source, is
`AlgebraicGeometry.bigSmallEtaleModuleSectionsCohomologyIso`.

The proof is part (5), `AlgebraicGeometry.bigSmallEtaleCohomologyIso`, read through
`SheafOfModules.toSheaf`: the derived functor of the exact abelian `i_f^{-1}` is the functor it
induces on derived categories, and that composed with forgetting the module structure is what
`i_f^*` induces, by `AlgebraicGeometry.smallEtaleModuleRestriction_comp_toSheaf`. -/
public def bigSmallEtaleModuleCohomologyIso :
    (SheafOfModules.toSheaf.{u + 1}
          (BigEtaleOver.structureSheaf B S.obj S.property)).mapDerivedCategory ⋙
        (((bigEtaleSections B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
              (ComplexShape.up ℤ))) ≅
      (smallEtaleModuleRestriction B T S f).mapDerivedCategory ⋙
        ((SheafOfModules.toSheaf.{u + 1}
            (SmallEtale.structureSheaf B T.obj T.property)).mapDerivedCategory ⋙
          (((Sheaf.Γ (SmallEtale.topology B T.obj T.property) Ab.{u + 1}).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
              (HomotopyCategory.quasiIso
                (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1})
                (ComplexShape.up ℤ)))) := by
  let : IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1}) :=
    bigEtaleSheaf_isGrothendieckAbelian B S
  let : IsGrothendieckAbelian.{u + 1, u + 1, u + 2}
      (Sheaf (SmallEtale.topology B T.obj T.property) Ab.{u + 1}) :=
    smallEtaleSheaf_isGrothendieckAbelian B T
  have hR : ((smallEtaleRestriction B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
            (ComplexShape.up ℤ)) ≅
      (smallEtaleRestriction B T S f).mapDerivedCategory :=
    Functor.rightDerivedUnique _ _
      (((smallEtaleRestriction B T S f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
            (ComplexShape.up ℤ)))
      (smallEtaleRestriction B T S f).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (Sheaf (BigEtaleOver.topology B S.obj S.property) Ab.{u + 1})
        (ComplexShape.up ℤ))
  exact Functor.isoWhiskerLeft _ (bigSmallEtaleCohomologyIso B T S f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _ hR ≪≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
        Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
          (eqToIso (smallEtaleModuleRestriction_comp_toSheaf B T S f).symm) ≪≫
        Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _

end Comparison

end AlgebraicGeometry

end
