module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceKernelIdealFirstMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeTransport
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageCotangentComplex

/-!
# The first arrow of the conormal sequence, read at both ends: the derivation

The first arrow of the conormal sequence is, at both ends of the comparison that Stacks 05ZB's
own proof needs, the adjoint transpose of **one and the same recipe**: restrict to the ideal
sheaf the universal derivation of the ambient object followed by the unit of the
pullback–pushforward adjunction, that is, `f ↦ 1 ⊗ d f`.

* Spaces-side the transpose is `AlgebraicGeometry.Space.kernelIdealUnitDifferential`, whose
  sections action is `AlgebraicGeometry.Space.kernelIdealUnitDifferential_val_app_apply`.
* Scheme-side it is `Stacks.ConormalSequenceRight.conormalDifferentialTranspose`, whose sections
  action is `Stacks.ConormalSequenceRight.conormalDifferentialTranspose_val_app`.

Those two value formulas are written in different vocabularies: the spaces-side one names the
constant `AlgebraicGeometry.Space.pullbackUnitDerivation`, the scheme-side one writes the unit
and the open-immersion comparison out.  **This file states and proves their agreement through
`AlgebraicGeometry.Space.schemeDifferentialsIso`**, and pins each transpose by its value formula
so that a comparison of the two arrows is reduced to a comparison of the two values.

## The agreement

For a morphism `α : U ⟶ V` of schemes of the big fppf site over `S` and a morphism
`φ : X' ⟶ yoneda.obj U` of algebraic spaces,
`AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_schemeDifferentialsIso` says that the
spaces-side derivation `d_{yoneda U/yoneda V}` followed by the unit of `φ^* ⊣ φ_*`, read through
`φ_*φ^*` of `AlgebraicGeometry.Space.schemeDifferentialsIso`, **is** the transported scheme-side
derivation followed by that same unit.  Restricted to the kernel ideal sheaf of `φ` that becomes
`AlgebraicGeometry.Space.kernelIdealUnitDifferential_val_app_apply_schemeDifferentialsIso`,
which reads the spaces-side value formula in exactly the shape the scheme-side one is written
in: the unit of a pullback–pushforward adjunction applied to the universal differential of the
section.

Only two inputs are used, and both are already proved:
`AlgebraicGeometry.Space.postcomp_schemeDifferentialsHom` — the comparison isomorphism of
Stacks 04CS carries the spaces-side universal derivation to the transported scheme-side one —
and the naturality of the unit, which is what moves the comparison past it.

## What this leaves for the join

The agreement above is between the spaces-side transpose and the **transported small-étale**
scheme-side one, `AlgebraicGeometry.Space.transportedUniversalDerivation`.  Two further
identifications are needed before it meets
`Stacks.ConormalSequenceRight.conormalDifferentialTranspose` itself, and neither belongs here:

* from the small étale site of the scheme down to its Zariski site, which is
  `AlgebraicGeometry.SmallEtale.differentialsIso` with
  `AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_hom` for the compatibility with the
  universal derivations, and the correspondence of the two units, which is
  `AlgebraicGeometry.SmallEtale.unit_associatedModuleBaseChange` and
  `AlgebraicGeometry.Space.unit_representedModulePullback`;
* the identification of the *sources* — the defining ideal sheaf of the closed factor against
  the kernel ideal sheaf of `φ` — which is proved, as
  `AlgebraicGeometry.Space.chartZariskiIdealSheaf_selfChart_kernelIdealSheaf_eq_definingIdealOfHom`
  of `StacksFrontier/AlgebraicGeometry/Spaces/RepresentedZariskiDefiningIdeal.lean`: the Zariski
  restriction of the kernel ideal sheaf of the represented morphism *is*
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.definingIdealOfHom` of the underlying morphism of
  schemes, with no hypothesis on it, which is the sheaf of ideals
  `Stacks.ConormalSequenceRight.conormalDifferentialTranspose` is a morphism out of;
* the open-immersion factor
  `Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso`, which moves the scheme-side
  target from the coborder neighbourhood to the ambient scheme.

The two pinning statements below are what make that join a check on values rather than a
manipulation of transposes.

## Main results

* `AlgebraicGeometry.Space.submoduleDerivationHom_comp` and
  `Stacks.ConormalSequenceRight.idealDerivationHom_comp`: at both ends, moving the target of an
  ideal-restricted derivation along a morphism of modules moves the derivation along it.  This
  is what turns an identification of targets into an identification of transposes.
* `AlgebraicGeometry.Space.eq_submoduleDerivationHom_of_val_app_apply`,
  `AlgebraicGeometry.Space.eq_kernelIdealUnitDifferential_of_val_app_apply` and
  `Stacks.ConormalSequenceRight.eq_conormalDifferentialTranspose_of_val_app`: **each transpose
  is the unique morphism out of the ideal sheaf with its value formula.**
* `AlgebraicGeometry.Space.submoduleTranspose_eq_kernelConormalFirstMap_of_val_app_apply`:
  **the spaces-side first arrow is pinned on sections of the ideal sheaf**, the mirror of
  `Stacks.ConormalSequenceRight.conormalDifferential_unique`.  Since the arrow is *definitionally*
  the transpose of its adjoint form, no new construction is needed.
* `AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_map_map` and
  `AlgebraicGeometry.Space.kernelIdealUnitDifferential_val_app_apply_map_map`: **the derivation,
  and then the transpose's value formula, read through an arbitrary comparison of the sheaves of
  differentials compatible with the universal derivations.**  This is the general form, and it
  is what lets the comparison be composed: the join needs the composite isomorphism of
  `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`, not only the first factor.
* `AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_schemeDifferentialsIso` and
  `AlgebraicGeometry.Space.kernelIdealUnitDifferential_val_app_apply_schemeDifferentialsIso`:
  **the derivation, and then the transpose, read at both ends through
  `AlgebraicGeometry.Space.schemeDifferentialsIso`**, which is that general form at the
  comparison isomorphism of Stacks 04CS.

## Implementation notes

Every statement below is an instance of moving a derivation's target, so the engine is
`PresheafOfModules.Derivation.postcomp_postcomp` — a derivation postcomposed with two morphisms
in turn is the derivation postcomposed with their composite.  It is **not** restated here: it
already exists, in `StacksFrontier/Cotangent/SheavesOfRings/InverseImageCotangentComplex.lean`,
and that module is imported for it — twenty-one further modules in the closure.  (An earlier
version of this file declared it again; a build of the whole library reported
`environment already contains 'PresheafOfModules.Derivation.postcomp_postcomp'`, which a build
of this module's closure alone does not see.)

The morphism of algebraic spaces is a variable throughout, for the reason the implementation
notes of `AlgebraicGeometry.Space.pullbackUnitDerivation` record: at a concrete morphism of
small étale ringed topoi the coefficient module of that derivation does not elaborate against
the one the adjunction writes through the composite functor.

## References

* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB), whose proof the
  comparison of the two arrows serves.
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA) and
  [Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ), the conormal sequence at the two ends.
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the spaces-level
  adjunction the spaces-side transposition is taken along.
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the
  two sheaves of differentials, through which the agreement is read.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the universal
  derivation and its universal property.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Ideal

variable {X : AlgebraicSpaces B S hS}

/-- **Moving the target of an ideal-restricted derivation.**  The restriction of a derivation `D`
to a sheaf of ideals, followed by a morphism `ψ` of `𝒪_X`-modules, is the restriction of `D`
postcomposed with `ψ`.

This is what turns an identification of the targets of the two first arrows into an
identification of the two arrows: on either side the arrow is built by restricting a derivation,
and the identification is absorbed into the derivation. -/
theorem submoduleDerivationHom_comp
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {φ : A ⟶ (smallEtaleRingedTopos B S hS X).O}
    (N N' : Modules.{u, u} B S hS X.1 X.2) (D : PresheafOfModulesOfCommRing.Derivation' N.val φ.hom)
    (hann : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (a : ToType ((structureRingSheaf B S hS X).obj.obj U)),
      a ∈ I.obj U →
        letI : Module ((structureRingSheaf B S hS X).obj.obj U) (N.val.obj U) :=
          (N.val.obj U).isModule
        ∀ m : N.val.obj U, a • m = 0)
    (ψ : N ⟶ N')
    (hann' : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (a : ToType ((structureRingSheaf B S hS X).obj.obj U)),
      a ∈ I.obj U →
        letI : Module ((structureRingSheaf B S hS X).obj.obj U) (N'.val.obj U) :=
          (N'.val.obj U).isModule
        ∀ m : N'.val.obj U, a • m = 0) :
    submoduleDerivationHom B S hS I N D hann ≫ ψ =
      submoduleDerivationHom B S hS I N' (D.postcomp ψ.val) hann' := by
  ext U x
  rfl

/-- **The restriction of a derivation to a sheaf of ideals is the only morphism with its value
formula.**  A morphism of `𝒪_X`-modules out of the ideal sheaf whose value on a local section is
the value of `D` on that section, read in `𝒪_X`, is
`AlgebraicGeometry.Space.submoduleDerivationHom`.

The content is that a morphism of sheaves of modules is determined by its values on sections;
the value formula of `AlgebraicGeometry.Space.submoduleDerivationHom` itself is
`AlgebraicGeometry.Space.conormalSequenceIdealHom_val_app_apply` at a general ideal, and holds
by `rfl`. -/
theorem eq_submoduleDerivationHom_of_val_app_apply
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {φ : A ⟶ (smallEtaleRingedTopos B S hS X).O}
    (N : Modules.{u, u} B S hS X.1 X.2) (D : PresheafOfModulesOfCommRing.Derivation' N.val φ.hom)
    (hann : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (a : ToType ((structureRingSheaf B S hS X).obj.obj U)),
      a ∈ I.obj U →
        letI : Module ((structureRingSheaf B S hS X).obj.obj U) (N.val.obj U) :=
          (N.val.obj U).isModule
        ∀ m : N.val.obj U, a • m = 0)
    (u : I.toSheafOfModules ⟶ N)
    (hu : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : I.toSheafOfModules.val.obj U),
      (ModuleCat.Hom.hom (u.val.app U)) x = D.d x.1) :
    u = submoduleDerivationHom B S hS I N D hann := by
  ext U x
  exact hu U x

end Ideal

section KernelIdeal

variable {X Y Bb : AlgebraicSpaces B S hS}

/-- **The adjoint form of the first arrow of Stacks 05ZA is the only morphism with its value
formula.**  A morphism of `𝒪_Y`-modules `𝓘_f ⟶ f_*f^*Ω_{Y/B}` carrying a local section `a` of
the kernel ideal sheaf to `d_{Y/B}(a)` followed by the unit of `f^* ⊣ f_*` is
`AlgebraicGeometry.Space.kernelIdealUnitDifferential`.

With `AlgebraicGeometry.Space.kernelIdealUnitDifferential_val_app_apply` this is the spaces-side
half of the pinning the comparison of the two first arrows consumes: the scheme-side half is
`Stacks.ConormalSequenceRight.eq_conormalDifferentialTranspose_of_val_app`. -/
theorem eq_kernelIdealUnitDifferential_of_val_app_apply (f : X ⟶ Y) (g : Y ⟶ Bb)
    (u : (kernelIdealSheaf B S hS f).toSheafOfModules ⟶
      (modulePushforward B S hS f).obj
        ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)))
    (hu : ∀ (U : (SmallEtale B S hS Y.1)ᵒᵖ)
      (x : (kernelIdealSheaf B S hS f).toSheafOfModules.val.obj U),
      (ModuleCat.Hom.hom (u.val.app U)) x = (pullbackUnitDerivation B S hS f g).d x.1) :
    u = kernelIdealUnitDifferential B S hS f g :=
  eq_submoduleDerivationHom_of_val_app_apply B S hS (kernelIdealSheaf B S hS f) _
    (pullbackUnitDerivation B S hS f g)
    (fun U a ha m ↦ kernelIdealAt_smul_modulePushforward_eq_zero B S hS f _ U a ha m) u hu

/-- **The first arrow of Stacks 05ZA at the kernel ideal sheaf is pinned on sections of that
ideal sheaf.**  The transpose along the adjunction of Stacks 03LU of *any* morphism
`u : 𝓘_f ⟶ f_*f^*Ω_{Y/B}` carrying a local section `a` of the kernel ideal sheaf to `d_{Y/B}(a)`
followed by the unit of `f^* ⊣ f_*` is `AlgebraicGeometry.Space.kernelConormalFirstMap`.

This is the spaces-side mirror of `Stacks.ConormalSequenceRight.conormalDifferential_unique`, and
it is the form a comparison of the two first arrows consumes: the scheme-side transpose, read on
the spaces side, is such a `u` as soon as its value formula is checked, and the arrow
identification then follows with no manipulation of transposes.

It is stated through `AlgebraicGeometry.Space.submoduleTranspose` and **not** through the hom-set
bijection written out.  That is not a presentation choice: the implementation notes of
`AlgebraicGeometry.Space.submoduleTranspose` record that writing the transposition out does not
fit in the default heartbeat budget, and the same holds here — both a `rfl` identifying
`kernelConormalFirstMap` with the written-out transpose and the same statement phrased with
`CategoryTheory.Adjunction.homEquiv` in the hypothesis exhaust the budget in this module, while
this phrasing is a `congrArg` and costs nothing. -/
theorem submoduleTranspose_eq_kernelConormalFirstMap_of_val_app_apply (f : X ⟶ Y) (g : Y ⟶ Bb)
    (u : (kernelIdealSheaf B S hS f).toSheafOfModules ⟶
      (modulePushforward B S hS f).obj
        ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)))
    (hu : ∀ (U : (SmallEtale B S hS Y.1)ᵒᵖ)
      (x : (kernelIdealSheaf B S hS f).toSheafOfModules.val.obj U),
      (ModuleCat.Hom.hom (u.val.app U)) x = (pullbackUnitDerivation B S hS f g).d x.1) :
    submoduleTranspose B S hS f (kernelIdealSheaf B S hS f)
        ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)) u =
      kernelConormalFirstMap B S hS f g :=
  congrArg (submoduleTranspose B S hS f (kernelIdealSheaf B S hS f)
      ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS g)))
    (eq_kernelIdealUnitDifferential_of_val_app_apply B S hS f g u hu)

end KernelIdeal

section Comparison

variable {X Y Bb : AlgebraicSpaces B S hS}

/-- **The derivation of the first arrow read through any comparison of the differentials.**  Let
`f : X ⟶ Y` be a morphism of algebraic spaces, `g : Y ⟶ Bb` a structure morphism, and let
`Φ : Ω_{Y/Bb} ⟶ N` carry the universal derivation `d_{Y/Bb}` to a derivation `E` of `𝒪_Y` with
values in `N`.  Then `d_{Y/Bb}` followed by the unit of `f^* ⊣ f_*`
(`AlgebraicGeometry.Space.pullbackUnitDerivation`), read through `f_*f^*Φ`, is `E` followed by
that same unit.

So a comparison of the sheaves of differentials compatible with the universal derivations is
automatically compatible with the derivation that induces the first arrow of Stacks 05ZA: the
only thing used beyond `Φ`'s own compatibility is the naturality of the unit, which is what
carries `Φ` past it.

This is the general form;
`AlgebraicGeometry.Space.pullbackUnitDerivation_postcomp_schemeDifferentialsIso` is the instance
at the comparison isomorphism of Stacks 04CS, and the instance at the composite
isomorphism of `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison` — which lands on
the associated module of the Zariski `Ω_{U/V}`, the sheaf
`Stacks.ConormalSequenceRight.conormalDifferentialTranspose` is written over — is this lemma at
that composite, whose compatibility with the universal derivations is
`AlgebraicGeometry.Space.postcomp_schemeDifferentialsHom` followed by
`AlgebraicGeometry.SmallEtale.postcomp_differentialsIso_hom`. -/
theorem pullbackUnitDerivation_postcomp_map_map (f : X ⟶ Y) (g : Y ⟶ Bb)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (Φ : sheafOfDifferentials B S hS g ⟶ N)
    (E : PresheafOfModulesOfCommRing.Derivation' N.val (structureSharpInverseImage B S hS g).hom)
    (hΦ : (universalDerivation B S hS g).postcomp Φ.val = E) :
    (pullbackUnitDerivation B S hS f g).postcomp
        ((modulePushforward B S hS f).map ((modulePullback B S hS f).map Φ)).val =
      E.postcomp ((modulePullbackAdjunction B S hS f).unit.app N).val := by
  have hnat : (modulePullbackAdjunction B S hS f).unit.app (sheafOfDifferentials B S hS g) ≫
        (modulePushforward B S hS f).map ((modulePullback B S hS f).map Φ) =
      Φ ≫ (modulePullbackAdjunction B S hS f).unit.app N :=
    ((modulePullbackAdjunction B S hS f).unit.naturality Φ).symm
  have hnat' : ((modulePullbackAdjunction B S hS f).unit.app
          (sheafOfDifferentials B S hS g)).val ≫
        ((modulePushforward B S hS f).map ((modulePullback B S hS f).map Φ)).val =
      Φ.val ≫ ((modulePullbackAdjunction B S hS f).unit.app N).val :=
    congrArg SheafOfModules.Hom.val hnat
  refine Eq.trans (PresheafOfModules.Derivation.postcomp_postcomp
    (universalDerivation B S hS g)
    ((modulePullbackAdjunction B S hS f).unit.app (sheafOfDifferentials B S hS g)).val
    ((modulePushforward B S hS f).map ((modulePullback B S hS f).map Φ)).val) ?_
  refine Eq.trans (congrArg
    (fun w ↦ (universalDerivation B S hS g).postcomp w) hnat') ?_
  refine Eq.trans (PresheafOfModules.Derivation.postcomp_postcomp
    (universalDerivation B S hS g) Φ.val
    ((modulePullbackAdjunction B S hS f).unit.app N).val).symm ?_
  exact congrArg (fun D ↦ PresheafOfModulesOfCommRing.Derivation.postcomp D
    ((modulePullbackAdjunction B S hS f).unit.app N).val) hΦ

/-- **The two value formulas of the first arrow agree through any such comparison.**  Read
through `f_*f^*Φ`, the value of `AlgebraicGeometry.Space.kernelIdealUnitDifferential` on a local
section `a` of the kernel ideal sheaf of `f` is the unit of `f^* ⊣ f_*` applied to `E a`.

That is the shape `Stacks.ConormalSequenceRight.conormalDifferentialTranspose_val_app` is
written in — the unit of a pullback–pushforward adjunction applied to the universal differential
of the section — so this is the agreement of the two value formulas, parametrized by the
comparison of the differentials. -/
theorem kernelIdealUnitDifferential_val_app_apply_map_map (f : X ⟶ Y) (g : Y ⟶ Bb)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (Φ : sheafOfDifferentials B S hS g ⟶ N)
    (E : PresheafOfModulesOfCommRing.Derivation' N.val (structureSharpInverseImage B S hS g).hom)
    (hΦ : (universalDerivation B S hS g).postcomp Φ.val = E)
    (W : (SmallEtale B S hS Y.1)ᵒᵖ)
    (x : (kernelIdealSheaf B S hS f).toSheafOfModules.val.obj W) :
    (ModuleCat.Hom.hom (((modulePushforward B S hS f).map
          ((modulePullback B S hS f).map Φ)).val.app W))
        ((ModuleCat.Hom.hom ((kernelIdealUnitDifferential B S hS f g).val.app W)) x) =
      (ModuleCat.Hom.hom (((modulePullbackAdjunction B S hS f).unit.app N).val.app W))
        (E.d x.1) :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    (pullbackUnitDerivation_postcomp_map_map B S hS f g N Φ E hΦ) x.1

end Comparison

section SchemeComparison

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable {U V : BigFppfOver B S hS} {X' : AlgebraicSpaces B S hS}

/-- **The derivation read at both ends, through the comparison isomorphism of Stacks 04CS.**
For a morphism `α : U ⟶ V` of schemes of the big fppf site over `S` and a morphism
`φ : X' ⟶ yoneda.obj U` of algebraic spaces, the spaces-side universal derivation followed by
the unit of `φ^* ⊣ φ_*` (`AlgebraicGeometry.Space.pullbackUnitDerivation`), read through
`φ_*φ^*` of `AlgebraicGeometry.Space.schemeDifferentialsIso`, is the transported scheme-side
universal derivation followed by that same unit.

Two inputs: `AlgebraicGeometry.Space.postcomp_schemeDifferentialsHom`, which is the
compatibility of the comparison isomorphism with the universal derivations, and the naturality
of the unit, which is what carries the comparison past it. -/
theorem pullbackUnitDerivation_postcomp_schemeDifferentialsIso (α : U ⟶ V)
    (φ : X' ⟶ schemeSpace U) :
    (pullbackUnitDerivation B S hS φ (schemeSpaceMap α)).postcomp
        ((modulePushforward B S hS φ).map
          ((modulePullback B S hS φ).map (schemeDifferentialsIso B S hS α).hom)).val =
      (transportedUniversalDerivation B S hS α).postcomp
        ((modulePullbackAdjunction B S hS φ).unit.app
          (transportedDifferentials B S hS α)).val :=
  pullbackUnitDerivation_postcomp_map_map B S hS φ (schemeSpaceMap α)
    (transportedDifferentials B S hS α) (schemeDifferentialsIso B S hS α).hom
    (transportedUniversalDerivation B S hS α) (postcomp_schemeDifferentialsHom B S hS α)

/-- **The two value formulas of the first arrow agree, through the comparison isomorphism of
Stacks 04CS.**  Read through `φ_*φ^*` of `AlgebraicGeometry.Space.schemeDifferentialsIso`, the
value of `AlgebraicGeometry.Space.kernelIdealUnitDifferential` on a local section `a` of the
kernel ideal sheaf of `φ` is the unit of `φ^* ⊣ φ_*` applied to the transported scheme-side
universal differential of `a`.

That is the shape `Stacks.ConormalSequenceRight.conormalDifferentialTranspose_val_app` is
written in — the unit of a pullback–pushforward adjunction applied to the universal differential
of the section — so this is the agreement of the two value formulas, with the remaining
identifications named in the module docstring. -/
theorem kernelIdealUnitDifferential_val_app_apply_schemeDifferentialsIso (α : U ⟶ V)
    (φ : X' ⟶ schemeSpace U) (W : (SmallEtale B S hS (schemeSpace U).1)ᵒᵖ)
    (x : (kernelIdealSheaf B S hS φ).toSheafOfModules.val.obj W) :
    (ModuleCat.Hom.hom
        (((modulePushforward B S hS φ).map
          ((modulePullback B S hS φ).map
            (schemeDifferentialsIso B S hS α).hom)).val.app W))
        ((ModuleCat.Hom.hom
          ((kernelIdealUnitDifferential B S hS φ (schemeSpaceMap α)).val.app W)) x) =
      (ModuleCat.Hom.hom
          (((modulePullbackAdjunction B S hS φ).unit.app
            (transportedDifferentials B S hS α)).val.app W))
        ((transportedUniversalDerivation B S hS α).d x.1) :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    (pullbackUnitDerivation_postcomp_schemeDifferentialsIso B S hS α φ) x.1

end SchemeComparison

end AlgebraicGeometry.Space

open AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.ConormalSequenceRight

variable {Z W S : Scheme.{u}}

/-- **Moving the target of an ideal-restricted derivation, scheme-side.**  The restriction of a
derivation `D` to the defining ideal sheaf of `j`, followed by a morphism `ψ` of
`𝒪_W`-modules, is the restriction of `D` postcomposed with `ψ`.

This is the scheme-side `AlgebraicGeometry.Space.submoduleDerivationHom_comp`. -/
theorem idealDerivationHom_comp (j : Z ⟶ W) (q : W ⟶ S) (F F' : Z.Modules)
    (D : AlgebraicGeometry.SheafOfModules.SheafDerivation (inverseImageStructureMap q)
      ((Scheme.Modules.pushforward j).obj F))
    (ψ : (Scheme.Modules.pushforward j).obj F ⟶ (Scheme.Modules.pushforward j).obj F') :
    idealDerivationHom j q F D ≫ ψ =
      idealDerivationHom j q F' (D.postcomp ψ.val) := by
  ext V f
  rfl

/-- **The restriction of a derivation to the defining ideal sheaf is the only morphism with its
value formula.**  A morphism of `𝒪_W`-modules out of the defining ideal sheaf of `j` whose value
on a local section is the value of `D` on that section is
`Stacks.ConormalSequenceRight.idealDerivationHom`.

The value formula of `idealDerivationHom` itself is
`Stacks.ConormalSequenceRight.idealDerivationHom_val_app`. -/
theorem eq_idealDerivationHom_of_val_app (j : Z ⟶ W) (q : W ⟶ S) (F : Z.Modules)
    (D : AlgebraicGeometry.SheafOfModules.SheafDerivation (inverseImageStructureMap q)
      ((Scheme.Modules.pushforward j).obj F))
    (u : ((definingIdealOfHom j).toSheafOfModules : W.Modules) ⟶
      (Scheme.Modules.pushforward j).obj F)
    (hu : ∀ (V : (Opens W)ᵒᵖ) (f : (definingIdealOfHom j).toSheafOfModules.val.obj V),
      (u.val.app V).hom f = D.d f.1) :
    u = idealDerivationHom j q F D := by
  ext V f
  exact hu V f

variable {X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)

/-- **The transpose of the first arrow of Stacks 01UZ is the only morphism with its value
formula.**  A morphism of `𝒪_W`-modules `ℐ ⟶ j_*(i^*Ω_{X/S})` out of the defining ideal sheaf of
the closed factor carrying a section `f` to `1 ⊗ d f` is
`Stacks.ConormalSequenceRight.conormalDifferentialTranspose`.

With `Stacks.ConormalSequenceRight.conormalDifferentialTranspose_val_app` this is the
scheme-side half of the pinning the comparison of the two first arrows consumes; the spaces-side
half is `AlgebraicGeometry.Space.eq_kernelIdealUnitDifferential_of_val_app_apply`. -/
theorem eq_conormalDifferentialTranspose_of_val_app
    (u : ((definingIdeal i).toSheafOfModules : (i.coborderRange.toScheme).Modules) ⟶
      (Scheme.Modules.pushforward i.liftCoborder).obj
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)))
    (hu : ∀ (V : (Opens i.coborderRange.toScheme)ᵒᵖ)
      (f : (definingIdeal i).toSheafOfModules.val.obj V),
      (u.val.app V).hom f =
        (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
              (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p)) ≫
            (Scheme.Modules.pushforward i.liftCoborder).map
              (coborderPullbackDifferentialsIso i p).hom).val.app V).hom
          ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d f.1)) :
    u = conormalDifferentialTranspose i p :=
  eq_idealDerivationHom_of_val_app i.liftCoborder (i.coborderRange.ι ≫ p) _
    (conormalDerivation i p) u hu

end Stacks.ConormalSequenceRight

end
