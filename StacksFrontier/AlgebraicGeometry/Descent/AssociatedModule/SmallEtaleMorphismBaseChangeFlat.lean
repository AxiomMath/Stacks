module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison

/-!
# The small étale pullback along a flat morphism is left exact on associated modules

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site, let `r` be the underlying
morphism of schemes and let `ε_a : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` be the morphism of ringed
sites of **Stacks 070R (2)**.  **Stacks 03LC (1)**, proved as
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso`, identifies the two composites

`(r^*𝓕)^a ≅ ε_a^*(𝓕^a)`

naturally in the `𝒪_Y`-module `𝓕`.  When `r` is flat both functors on the left are left exact —
`AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat` for the pullback of
`𝒪`-modules along a flat morphism of schemes, and the exactness assertion of **Stacks 08H8** for
the associated-module functor — so the composite on the right is left exact too.

This is the one place where flatness of `r` is spent.  The pullback `ε_a^*` by itself is only a
left adjoint, hence only right exact; what the identification buys is left exactness of its
restriction along `𝓕 ↦ 𝓕^a`, and by **Stacks 03DX (2)** every quasi-coherent module on
`Y_étale` is of that form, so this is left exactness of `ε_a^*` on quasi-coherent modules.

## Main results

* `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule_comp_pullback`: for `r`
  flat, `𝓕 ↦ ε_a^*(𝓕^a)` is left exact.
* `AlgebraicGeometry.SmallEtale.isLimit_map_pullback_of_isLimit_map_associatedModule`: a limit
  cone in the `𝒪_Y`-modules whose image under `𝓕 ↦ 𝓕^a` is the cone at hand stays a limit after
  `ε_a^*`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **The small étale pullback along a flat morphism is left exact on associated modules.**
For `r : X ⟶ Y` flat, the composite `𝓕 ↦ ε_a^*(𝓕^a)` of the associated-module functor of `Y`
with the pullback of sheaves of modules along `ε_a` preserves finite limits.

By **Stacks 03LC (1)** that composite is `𝓕 ↦ (r^*𝓕)^a`, and both of its factors are left
exact: the pullback of `𝒪`-modules along a flat morphism of schemes, and the associated-module
functor of `X` by the exactness assertion of **Stacks 08H8**. -/
theorem preservesFiniteLimits_associatedModule_comp_pullback [Flat (schemeHom B a)] :
    PreservesFiniteLimits (associatedModule B Y.obj Y.property ⋙
      SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)) :=
  let : PreservesFiniteLimits (Scheme.Modules.pullback (schemeHom B a)) :=
    preservesFiniteLimits_modulesPullback_of_flat (schemeHom B a)
  let : PreservesFiniteLimits (associatedModule B X.obj X.property) :=
    preservesFiniteLimits_associatedModule B X.obj X.property
  let : PreservesFiniteLimits (Scheme.Modules.pullback (schemeHom B a) ⋙
      associatedModule B X.obj X.property) := comp_preservesFiniteLimits _ _
  preservesFiniteLimits_of_natIso (associatedModuleBaseChangeIso B a)

/-- A finite limit cone of `𝒪_Y`-modules stays a limit cone after `𝓕 ↦ ε_a^*(𝓕^a)`, for `r`
flat.  This is `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule_comp_pullback`
read at one cone. -/
def isLimit_map_pullback_of_isLimit_map_associatedModule [Flat (schemeHom B a)]
    {J : Type} [SmallCategory J] [FinCategory J] {K : J ⥤ Y.obj.Modules} {c : Cone K}
    (hc : IsLimit c) :
    IsLimit (((associatedModule B Y.obj Y.property ⋙
      SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).mapCone c)) :=
  letI := preservesFiniteLimits_associatedModule_comp_pullback B a
  isLimitOfPreserves _ hc

/-- `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule_comp_pullback` at the
retyping `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`, whose source carries the
category instance of `SheafOfModules.{u} Y.ringCatSheaf` in which the quasi-coherent modules
are a full subcategory. -/
theorem preservesFiniteLimits_associatedModuleOfSheaf_comp_pullback [Flat (schemeHom B a)] :
    PreservesFiniteLimits (associatedModuleOfSheaf B Y.obj Y.property ⋙
      SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)) :=
  have h : PreservesFiniteLimits (associatedModule B Y.obj Y.property ⋙
      SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)) :=
    preservesFiniteLimits_associatedModule_comp_pullback B a
  h

/-- **The pullback of sheaves of modules along `ε_a` is left exact on quasi-coherent modules,
for `r : X ⟶ Y` flat.**

By **Stacks 03DX (2)** the functor `𝓕 ↦ 𝓕^a` is an equivalence `QCoh(𝒪_Y) ⥤ QCoh(Y_étale, 𝒪)`,
so `QCoh(Y_étale, 𝒪) ⥤ Mod(X_étale, 𝒪)` is, up to that equivalence, the composite of the
inclusion `QCoh(𝒪_Y) ⥤ Mod(𝒪_Y)` — left exact because quasi-coherence on a scheme is a weak
Serre class — with `𝓕 ↦ ε_a^*(𝓕^a)`, which is left exact by
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule_comp_pullback`. -/
theorem preservesFiniteLimits_ι_qcohOnSite_comp_pullback [Flat (schemeHom B a)] :
    PreservesFiniteLimits ((qcohOnSite B Y.obj Y.property).ι ⋙
      SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)) := by
  let := isEquivalence_associatedModuleQcohOnSite' B Y.obj Y.property
  let := preservesFiniteLimits_associatedModuleOfSheaf_comp_pullback B a
  let : PreservesFiniteLimits
      ((associatedModuleQcohOnSite B Y.obj Y.property).asEquivalence.functor ⋙
        ((qcohOnSite B Y.obj Y.property).ι ⋙
          SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a))) :=
    comp_preservesFiniteLimits (SheafOfModules.isQuasicoherent Y.obj.ringCatSheaf).ι
      (associatedModuleOfSheaf B Y.obj Y.property ⋙
        SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a))
  let : PreservesFiniteLimits
      ((associatedModuleQcohOnSite B Y.obj Y.property).asEquivalence.inverse ⋙
        (associatedModuleQcohOnSite B Y.obj Y.property).asEquivalence.functor ⋙
          ((qcohOnSite B Y.obj Y.property).ι ⋙
            SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a))) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso
    ((associatedModuleQcohOnSite B Y.obj Y.property).asEquivalence.invFunIdAssoc
      ((qcohOnSite B Y.obj Y.property).ι ⋙
        SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)))

end AlgebraicGeometry.SmallEtale

end
