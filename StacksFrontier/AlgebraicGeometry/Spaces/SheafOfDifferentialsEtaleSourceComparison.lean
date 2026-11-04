module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMapEtale

/-!
# The étale-source localization is the comparison map of Stacks 04CX

Let `a : U ⟶ X` be an *étale* morphism of algebraic spaces over a scheme `S` and let
`f : X ⟶ Y` be any morphism.  Stacks 04CU identifies `a^*Ω_{X/Y}` with `Ω_{U/Y}`, and
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso` is that
identification.  This file proves that its forward map is the comparison map of Stacks 04CX
for the triangle `U ⟶ X ⟶ Y`, which is the form in which the comparison maps are hypothesized
throughout this development:

`AlgebraicGeometry.Space.IsSheafOfDifferentialsMap B S hS a f (a ≫ f) _`.

Because the comparison map of a square is unique
(`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`), **any** morphism with that
property is therefore an isomorphism when `a` is étale.  That is the clause of Stacks 04CU
which consumers of the comparison map previously had to assume as an `IsIso` hypothesis.

## Main results

* `modulePullbackAdjunction_homEquiv_val_app_eq_pullbackAdjPushforwardModules`: the two
  spellings of the adjoint transpose of Stacks 03D7 agree on sections.
* `AlgebraicGeometry.Space.differentialsHomEquiv_etaleSourceAdjEquiv_localizationHom`: the
  `Y`-derivation of `𝒪_X` attached to the étale-source comparison by the first two of the four
  bijections of `AlgebraicGeometry.Space.derivationEtalePullbackEquiv` is the transposition of
  the universal derivation `d_{U/Y}`.
* `AlgebraicGeometry.Space.derivationSheafHom_etaleSourceRingDataEquiv_symm_eq_comp` and
  `AlgebraicGeometry.Space.pushforwardUniversalDerivationHom_eq_homEquiv`: the two halves of
  the identification of that transposition with the composite `a_*d_{U/Y} ∘ a♯` of
  Stacks 04CX.
* `AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom`
  (`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsMapEtale.lean`): the forward map of
  the étale-source localization has the characterizing property of Stacks 04CX; it is
  registered for Stacks 04CU here.
* `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isEtale`: **the comparison
  map of Stacks 04CX for a triangle over `Y` whose upper edge is étale is an isomorphism.**

## Implementation notes

The characterizing property of Stacks 04CX is stated through
`AlgebraicGeometry.Space.modulePullbackAdjunction`, whose right adjoint is
`AlgebraicGeometry.Space.modulePushforward`, while the corepresentation
`AlgebraicGeometry.Space.derivationEtalePullbackEquiv` that produces the étale-source
localization is stated through the untransported
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`, whose right adjoint is
`Stacks.Sheaves.RingedToposModules.pushforwardModules`.  The two adjunctions differ by
`AlgebraicGeometry.Space.modulePushforwardIso`, which is the identity on sections
(`AlgebraicGeometry.Space.modulePullbackAdjunction_unit_val_app`); so the two adjoint
transposes of one morphism agree on sections.  That is the only plumbing step.

The mathematical step is the identification of the transposed universal derivation.  Both of
the two remaining bijections of `derivationEtalePullbackEquiv` are inverted explicitly: the
transposition of derivations is the hom-set bijection of `a^{-1} ⊣ a_*` on the underlying
sheaves of sets
(`Stacks.Sheaves.RingedToposModules.derivationSheafHom_inverseImageDerivationEquiv`), and the
transport along the ring data composes a derivation with the sections of the clause
`a^{-1}𝒪_X = 𝒪_U` of Stacks 03LV, whose forward map is the inverse-image form of the structure
map of `a` (`AlgebraicGeometry.Space.etaleInverseImageStructureSheafIso_hom`).  So the
transpose of `d_{U/Y}` is `a♯` followed by the direct image of `d_{U/Y}`, by
`AlgebraicGeometry.Space.homEquiv_structureSharpInverseImageSet`, which is the two forms of
the structure map being adjunct.

*The heartbeat budget is per declaration.*  Each step below is its own declaration even where
a reader would write one chain: the steps that read a composite of morphisms of sheaves of
modules on a section, and the step that reads a transported derivation on a section, each
force the elaborator to unfold the small étale ringed topos of an algebraic space down to its
`Category` instance, which is affordable once per declaration and not in a chain.  This is the
pattern of `StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSpellingBridge.lean`.

## References

* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), étale localization of
  the sheaf of differentials.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of
  a commutative square and its uniqueness.
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV), the clause
  `a^{-1}𝒪_X = 𝒪_U` for an étale `a`.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the two forms of the
  structure map and their adjunction.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules (pushforwardModules pullbackAdjPushforwardModules
  inverseImageDerivationEquiv derivationSheafHom
  derivationSheafHom_inverseImageDerivationEquiv)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U : AlgebraicSpaces B S hS}

/-! ### The two spellings of the adjoint transpose -/

/-- The two spellings of the direct image of a morphism of sheaves of modules agree on
sections: both are the direct image of the morphism of underlying sheaves of sets, and the two
restrictions of scalars do not change it. -/
theorem modulePushforward_map_val_app_eq_pushforwardModules (a : U ⟶ X)
    {C C' : Modules.{u, u} B S hS U.1 U.2}
    (θ : C ⟶ C') (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (y : ((modulePushforward B S hS a).obj C).val.obj V) :
    (((modulePushforward B S hS a).map θ).val.app V).hom y =
      (((pushforwardModules
        (smallEtaleRingedToposModulesHom B S hS a)).map θ).val.app V).hom y :=
  rfl

/-- The adjoint transpose of an adjunction with left adjoint the module pullback, read on a
section: the unit followed by the direct image of the morphism.  Stated for an arbitrary right
adjoint, so that the two spellings of the direct image of Stacks 03LU are both instances. -/
private theorem adjunction_homEquiv_val_app_eq (a : U ⟶ X)
    {G : Modules.{u, u} B S hS U.1 U.2 ⥤ Modules.{u, u} B S hS X.1 X.2}
    (adj : modulePullback B S hS a ⊣ G) (M : Modules.{u, u} B S hS X.1 X.2)
    {C : Modules.{u, u} B S hS U.1 U.2} (θ : (modulePullback B S hS a).obj M ⟶ C)
    (V : (SmallEtale B S hS X.1)ᵒᵖ) (x : M.val.obj V) :
    ((adj.homEquiv M C θ).val.app V).hom x =
      ((G.map θ).val.app V).hom (((adj.unit.app M).val.app V).hom x) := by
  have hu : adj.homEquiv M C θ = adj.unit.app M ≫ G.map θ := by
    simp only [Adjunction.homEquiv_unit]
  exact (congrArg (fun m : M ⟶ G.obj C ↦ (m.val.app V).hom x) hu).trans
    (Stacks.Sheaves.RingedToposModules.comp_val_app_apply _ _ V x)

/-- **The two spellings of the adjoint transpose of Stacks 03D7 agree on sections.**  The
adjunction `AlgebraicGeometry.Space.modulePullbackAdjunction` is the untransported
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` transported along
`AlgebraicGeometry.Space.modulePushforwardIso`, and that comparison is the identity on
sections. -/
theorem modulePullbackAdjunction_homEquiv_val_app_eq_pullbackAdjPushforwardModules (a : U ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) {C : Modules.{u, u} B S hS U.1 U.2}
    (θ : (modulePullback B S hS a).obj M ⟶ C) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : M.val.obj V) :
    (((modulePullbackAdjunction B S hS a).homEquiv M C θ).val.app V).hom x =
      (((pullbackAdjPushforwardModules
          (smallEtaleRingedToposModulesHom B S hS a)).homEquiv M C θ).val.app V).hom x :=
  (adjunction_homEquiv_val_app_eq B S hS a (modulePullbackAdjunction B S hS a) M θ V x).trans
    (((congrArg (fun y ↦ (((modulePushforward B S hS a).map θ).val.app V).hom y)
        (modulePullbackAdjunction_unit_val_app B S hS a M V x)).trans
      (modulePushforward_map_val_app_eq_pushforwardModules B S hS a θ V _)).trans
    (adjunction_homEquiv_val_app_eq B S hS a
      (pullbackAdjPushforwardModules (smallEtaleRingedToposModulesHom B S hS a)) M θ V x).symm)

/-! ### The transposed universal derivation -/

/-- **The transport along the ring data, on underlying sheaves of sets.**  Reading a
`Y`-derivation `D` of `𝒪_U` as an `a^{-1}f^{-1}𝒪_Y`-derivation of `a^{-1}𝒪_X` composes it with
the clause `a^{-1}𝒪_X = 𝒪_U` of Stacks 03LV, whose forward map is the inverse-image form
`a♯ : a^{-1}𝒪_X ⟶ 𝒪_U` of the structure map of `a`. -/
theorem derivationSheafHom_etaleSourceRingDataEquiv_symm_eq_comp (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    derivationSheafHom
        ((smallEtaleInverseImageRing B S hS a).map (structureSharpInverseImage B S hS f))
        ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        ((etaleSourceRingDataEquiv B S hS a ha f
            (sheafOfDifferentials B S hS (a ≫ f))).symm
          (universalDerivation B S hS (a ≫ f))) =
      structureSharpInverseImageSet B S hS a ≫ universalDerivationHom B S hS (a ≫ f) :=
  CategoryTheory.Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- **The composite `a_*d_{U/Y} ∘ a♯` of Stacks 04CX is the adjoint transpose of `d_{U/Y}`.**
This is `AlgebraicGeometry.Space.homEquiv_structureSharpInverseImageSet`, the two forms of the
structure map being adjunct, followed by naturality of the transposition. -/
theorem pushforwardUniversalDerivationHom_eq_homEquiv (a : U ⟶ X) (p : U ⟶ Y) :
    pushforwardUniversalDerivationHom B S hS a p =
      (smallEtaleRingedToposHom B S hS a).toToposHom.adj.homEquiv _ _
        (structureSharpInverseImageSet B S hS a ≫ universalDerivationHom B S hS p) := by
  rw [Adjunction.homEquiv_naturality_right, homEquiv_structureSharpInverseImageSet]
  rfl

/-- The `Y`-derivation attached to the étale-source comparison map by the first two of the four
bijections of `AlgebraicGeometry.Space.derivationEtalePullbackEquiv` is the transposition of
the universal derivation `d_{U/Y}` read through the ring data.

This is the defining property of the comparison map,
`AlgebraicGeometry.Space.derivationEtalePullbackEquiv_etaleSourceLocalizationHom`, with the
last two of the four bijections undone. -/
theorem differentialsHomEquiv_etaleSourceAdjEquiv_localizationHom (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    differentialsHomEquiv B S hS f
        ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        (etaleSourceAdjEquiv B S hS a f (sheafOfDifferentials B S hS (a ≫ f))
          (etaleSourceLocalizationHom B S hS a ha f)) =
      inverseImageDerivationEquiv (smallEtaleRingedToposHom B S hS a).toToposHom
        (structureSharpInverseImage B S hS f)
        ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        ((etaleSourceRingDataEquiv B S hS a ha f
            (sheafOfDifferentials B S hS (a ≫ f))).symm
          (universalDerivation B S hS (a ≫ f))) := by
  have h0 : etaleSourceRingDataEquiv B S hS a ha f (sheafOfDifferentials B S hS (a ≫ f))
      (etaleSourceTransposeEquiv B S hS a f (sheafOfDifferentials B S hS (a ≫ f))
        (differentialsHomEquiv B S hS f
          ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
          (etaleSourceAdjEquiv B S hS a f (sheafOfDifferentials B S hS (a ≫ f))
            (etaleSourceLocalizationHom B S hS a ha f)))) =
      universalDerivation B S hS (a ≫ f) :=
    (derivationEtalePullbackEquiv_apply B S hS a ha f (sheafOfDifferentials B S hS (a ≫ f))
        (etaleSourceLocalizationHom B S hS a ha f)).symm.trans
      (derivationEtalePullbackEquiv_etaleSourceLocalizationHom B S hS a ha f)
  exact (Equiv.apply_symm_apply (inverseImageDerivationEquiv
        (smallEtaleRingedToposHom B S hS a).toToposHom (structureSharpInverseImage B S hS f)
        ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f))))
      _).symm.trans
    (congrArg (fun z ↦ inverseImageDerivationEquiv
        (smallEtaleRingedToposHom B S hS a).toToposHom (structureSharpInverseImage B S hS f)
        ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f))) z)
      ((Equiv.eq_symm_apply _).mpr h0))

/-- The first of the two remaining bijections undone, under `derivationSheafHom`: this is
`AlgebraicGeometry.Space.differentialsHomEquiv_etaleSourceAdjEquiv_localizationHom` read on the
underlying sheaves of sets. -/
private theorem derivationSheafHom_congr_localizationHom (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    derivationSheafHom (structureSharpInverseImage B S hS f)
        ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        (differentialsHomEquiv B S hS f
          ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
          (etaleSourceAdjEquiv B S hS a f (sheafOfDifferentials B S hS (a ≫ f))
            (etaleSourceLocalizationHom B S hS a ha f))) =
      derivationSheafHom (structureSharpInverseImage B S hS f)
        ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        (inverseImageDerivationEquiv (smallEtaleRingedToposHom B S hS a).toToposHom
          (structureSharpInverseImage B S hS f)
          ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
          ((etaleSourceRingDataEquiv B S hS a ha f
              (sheafOfDifferentials B S hS (a ≫ f))).symm
            (universalDerivation B S hS (a ≫ f)))) :=
  congrArg (fun z ↦ derivationSheafHom (structureSharpInverseImage B S hS f)
      ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f))) z)
    (differentialsHomEquiv_etaleSourceAdjEquiv_localizationHom B S hS a ha f)

/-- The transposition of derivations undone: the sheaf-of-sets morphism of a transposed
derivation is the adjoint transpose of the sheaf-of-sets morphism of the derivation.  This is
`Stacks.Sheaves.RingedToposModules.derivationSheafHom_inverseImageDerivationEquiv` at the
transported universal derivation. -/
private theorem derivationSheafHom_inverseImageDerivation_localization (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    derivationSheafHom (structureSharpInverseImage B S hS f)
        ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        (inverseImageDerivationEquiv (smallEtaleRingedToposHom B S hS a).toToposHom
          (structureSharpInverseImage B S hS f)
          ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
          ((etaleSourceRingDataEquiv B S hS a ha f
              (sheafOfDifferentials B S hS (a ≫ f))).symm
            (universalDerivation B S hS (a ≫ f)))) =
      (smallEtaleRingedToposHom B S hS a).toToposHom.adj.homEquiv _ _
        (derivationSheafHom
          ((smallEtaleRingedToposHom B S hS a).toToposHom.inverseImageRing.map
            (structureSharpInverseImage B S hS f))
          ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
          ((etaleSourceRingDataEquiv B S hS a ha f
              (sheafOfDifferentials B S hS (a ≫ f))).symm
            (universalDerivation B S hS (a ≫ f)))) :=
  derivationSheafHom_inverseImageDerivationEquiv
    (smallEtaleRingedToposHom B S hS a).toToposHom (structureSharpInverseImage B S hS f)
    ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
    ((etaleSourceRingDataEquiv B S hS a ha f (sheafOfDifferentials B S hS (a ≫ f))).symm
      (universalDerivation B S hS (a ≫ f)))

/-- The transport along the ring data undone, under the adjoint transpose: this is
`AlgebraicGeometry.Space.derivationSheafHom_etaleSourceRingDataEquiv_symm_eq_comp` transposed. -/
private theorem homEquiv_derivationSheafHom_etaleSourceRingDataEquiv_symm_eq_comp (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS a).toToposHom.adj.homEquiv _ _
        (derivationSheafHom
          ((smallEtaleRingedToposHom B S hS a).toToposHom.inverseImageRing.map
            (structureSharpInverseImage B S hS f))
          ((etaleSourceRestrictScalars B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
          ((etaleSourceRingDataEquiv B S hS a ha f
              (sheafOfDifferentials B S hS (a ≫ f))).symm
            (universalDerivation B S hS (a ≫ f)))) =
      (smallEtaleRingedToposHom B S hS a).toToposHom.adj.homEquiv _ _
        (structureSharpInverseImageSet B S hS a ≫ universalDerivationHom B S hS (a ≫ f)) :=
  (Equiv.apply_eq_iff_eq _).mpr
    (derivationSheafHom_etaleSourceRingDataEquiv_symm_eq_comp B S hS a ha f)

/-- The three steps above chained: the sheaf-of-sets morphism of the `Y`-derivation attached to
the étale-source comparison is the adjoint transpose of `a♯` followed by `d_{U/Y}`. -/
private theorem derivationSheafHom_localizationHom_eq_homEquiv (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) :
    derivationSheafHom (structureSharpInverseImage B S hS f)
        ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
        (differentialsHomEquiv B S hS f
          ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
          (etaleSourceAdjEquiv B S hS a f (sheafOfDifferentials B S hS (a ≫ f))
            (etaleSourceLocalizationHom B S hS a ha f))) =
      (smallEtaleRingedToposHom B S hS a).toToposHom.adj.homEquiv _ _
        (structureSharpInverseImageSet B S hS a ≫ universalDerivationHom B S hS (a ≫ f)) :=
  (derivationSheafHom_congr_localizationHom B S hS a ha f).trans
    ((derivationSheafHom_inverseImageDerivation_localization B S hS a ha f).trans
      (homEquiv_derivationSheafHom_etaleSourceRingDataEquiv_symm_eq_comp B S hS a ha f))

/-- The left-hand side of the characterizing property of Stacks 04CX for the étale-source
comparison map, read as a local section of the `Y`-derivation of the first two bijections. -/
private theorem homEquiv_universalDerivation_eq_derivationSheafHom (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : (structureRingSheaf B S hS X).obj.obj V) :
    (((modulePullbackAdjunction B S hS a).homEquiv (sheafOfDifferentials B S hS f)
          (sheafOfDifferentials B S hS (a ≫ f))
          (etaleSourceLocalizationHom B S hS a ha f)).val.app V).hom
        ((universalDerivation B S hS f).d t) =
      (derivationSheafHom (structureSharpInverseImage B S hS f)
          ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
          (differentialsHomEquiv B S hS f
            ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
            (etaleSourceAdjEquiv B S hS a f (sheafOfDifferentials B S hS (a ≫ f))
              (etaleSourceLocalizationHom B S hS a ha f)))).hom.app V t :=
  modulePullbackAdjunction_homEquiv_val_app_eq_pullbackAdjPushforwardModules B S hS a
    (sheafOfDifferentials B S hS f) (etaleSourceLocalizationHom B S hS a ha f) V
    ((universalDerivation B S hS f).d t)

/-- The right-hand side of the characterizing property of Stacks 04CX reached: the two steps of
the identification, on a local section. -/
private theorem derivationSheafHom_eq_pushforwardUniversalDerivationHom (a : U ⟶ X)
    (ha : IsEtale B S hS a.hom) (f : X ⟶ Y) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (t : (structureRingSheaf B S hS X).obj.obj V) :
    (derivationSheafHom (structureSharpInverseImage B S hS f)
          ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
          (differentialsHomEquiv B S hS f
            ((etaleSourcePushforward B S hS a).obj (sheafOfDifferentials B S hS (a ≫ f)))
            (etaleSourceAdjEquiv B S hS a f (sheafOfDifferentials B S hS (a ≫ f))
              (etaleSourceLocalizationHom B S hS a ha f)))).hom.app V t =
      (pushforwardUniversalDerivationHom B S hS a (a ≫ f)).hom.app V t :=
  (congrArg (fun m ↦ m.hom.app V t)
    (derivationSheafHom_localizationHom_eq_homEquiv B S hS a ha f)).trans
    (congrArg (fun m ↦ m.hom.app V t)
      (pushforwardUniversalDerivationHom_eq_homEquiv B S hS a (a ≫ f)).symm)

/-! ### Stacks 04CU: the comparison map of an étale triangle is an isomorphism -/

/- The forward map of the étale-source localization `a^*Ω_{X/Y} ≅ Ω_{U/Y}` is the comparison
map of Stacks 04CX for the triangle `U ⟶ X ⟶ Y`; by
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap` it is the only morphism with that
property.  The statement is
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom`. -/
add_to_stacks 04CU "the étale-source identification is the comparison map of 04CX"
  AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom

/-- **Stacks 04CU: the comparison map of a triangle over `Y` whose upper edge is étale is an
isomorphism.**  Let `a : U ⟶ X` be étale, let `f : X ⟶ Y`, and let `q : U ⟶ Y` be the
composite.  Any morphism `c : a^*Ω_{X/Y} ⟶ Ω_{U/Y}` with the characterizing property of
Stacks 04CX is an isomorphism.

By `AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap` there is at most one such `c`, and
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_etaleSourceLocalizationHom` exhibits one
which is the forward map of
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso`. -/
@[stacks 04CU "the comparison map of an étale triangle over the base is an isomorphism"]
theorem isIso_of_isSheafOfDifferentialsMap_of_isEtale (a : U ⟶ X) (ha : IsEtale B S hS a.hom)
    (f : X ⟶ Y) (q : U ⟶ Y) (haq : a ≫ f = q)
    {c : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶
      sheafOfDifferentials B S hS q}
    (hc : IsSheafOfDifferentialsMap B S hS a f q c) : IsIso c := by
  subst haq
  rw [eq_of_isSheafOfDifferentialsMap B S hS a f (a ≫ f) hc
    (isSheafOfDifferentialsMap_etaleSourceLocalizationHom B S hS a ha f)]
  exact (sheafOfDifferentialsEtaleSourceLocalizationIso B S hS a ha f).isIso_hom

end AlgebraicGeometry.Space

end
