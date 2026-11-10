module

public import StacksFrontier.AlgebraicGeometry.ModuleStalkTensor.Basic

/-!
# Invertibility of a morphism of algebra sheaves, from its underlying module morphism

A morphism `φ : A ⟶ B` of sheaves of commutative `𝒪_X`-algebras on a scheme `X` induces a
morphism of the underlying `𝒪_X`-modules: the map on sections is the same, and it is
`𝒪_X`-linear because `φ` is a ring map carrying the structure morphism of `A` to that of `B`.

**This file builds that morphism and shows that `φ` is invertible as soon as it is.**  The
point is that the available local criteria for invertibility — invertibility is local on an open
cover (`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`), and on an affine
scheme a morphism of quasi-coherent modules invertible on global sections is invertible
(`isIso_of_isIso_moduleSpecΓ`) — are stated for *modules* on a scheme, and nothing in the
development transports them to sheaves of rings or to algebra sheaves.

## Main definitions

* `Stacks.AlgebraPullbackQcoh.unitToRestrictScalarsObjUnit`: for a morphism `ρ : R ⟶ R'` of
  sheaves of rings on a site, the morphism `unit R ⟶ (restrictScalars ρ).obj (unit R')` which
  is `ρ` on sections.  This is `CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` with
  restriction of scalars in place of a direct image; the two constructions are identical, the
  direct image of a presheaf of modules and restriction of scalars having the same sections.
* `Stacks.AlgebraPullbackQcoh.ringMap`: `φ` read as a morphism of the underlying sheaves of
  not necessarily commutative rings.
* `Stacks.AlgebraPullbackQcoh.moduleMap`: **the morphism of underlying `𝒪_X`-modules.**

## Main results

* `Stacks.AlgebraPullbackQcoh.smul_underlyingModule`: the scalar action on the underlying
  module of an algebra sheaf is multiplication by the image of the scalar under the structure
  morphism, on the nose.
* `Stacks.AlgebraPullbackQcoh.structureMap_comp_ringMap` and `ringMap_structureMap_app`: a
  morphism of algebra sheaves carries the structure morphism of its source to that of its
  target, as sheaves of rings and on sections.
* `Stacks.AlgebraPullbackQcoh.moduleMap_val_app_apply`: the underlying module morphism is `φ`
  on sections, by `rfl`.
* `Stacks.AlgebraPullbackQcoh.isIso_of_isIso_moduleMap`: **the criterion.**  If the underlying
  module morphism is invertible then so is `φ`.
* `Stacks.AlgebraPullbackQcoh.isIso_of_isIso_restrict_moduleMap`: the criterion in the form a
  local argument consumes — it is enough that the underlying module morphism be invertible
  after restriction to each member of an open cover.

## Route

`moduleMap φ` is built by hand rather than as a composite of
`unitToRestrictScalarsObjUnit` with restriction of scalars.  Both are possible, but the
composite lands in restriction of scalars along `structureMap A ≫ ringMap φ`, which is
`structureMap B` only propositionally, so that route needs a transport along an equality of
sheaf morphisms and the resulting sections formula is no longer `rfl`.  Built directly, the
morphism is `φ` on sections definitionally, which is what every consumer needs.
`unitToRestrictScalarsObjUnit` is kept because it is the general statement behind the
construction and is absent from Mathlib.

The criterion runs through sections, not through stalks: invertibility of the module morphism
gives invertibility of the underlying morphism of presheaves of abelian groups, hence
bijectivity of each component, hence — the two morphisms having the same components as
functions — invertibility of each component of `φ` in `CommRingCat`, and so of `φ` itself,
because `CategoryTheory.sheafToPresheaf` is fully faithful and
`CategoryTheory.Under.forget` reflects isomorphisms.

## What is not done

**No clause of [Stacks, Tag 01SA] is proved here, and no project tag attribute is attached.**
Tag 01SA is registered as a single unqualified tag on a nine-field structure; seven of its nine
fields have content, the two open ones being its base-change isomorphism `baseChangeIso` and the
identification `baseChangeIso_canonical` of that isomorphism.

This file is the first of the three things those two fields need.  The other two are not
started: the sections of `Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHom` over an affine
open of `T` lying over an affine open of `S`, identified with a tensor product of rings — for
which `Stacks.AlgebraicGeometry.SectionsColimit.sectionsPullbackIso` is the input on the
pullback side and `AlgebraicGeometry.pullbackSpecIso` on the fibre-product side — and then the
naturality of `baseChangeAlgebraHom` in the scheme over `S` and its assembly into an
isomorphism of functors.

Nothing here assumes quasi-coherence, affineness, Noetherian, finiteness or flatness: `X`,
`A`, `B` and `φ` are arbitrary.  The quasi-coherence hypotheses enter only where a consumer
applies `isIso_of_isIso_moduleSpecΓ` on an affine member of the cover.

## Transparency gotchas

* In the scalar-compatibility proof of `moduleMap` the multiplication cannot be written with a
  type ascription on the section: the element produced by `ext` has the underlying group of a
  restriction of scalars as its type, the multiplication notation elaborates that type before
  the ascription takes effect, and no `HMul` instance is found.  The remedy is
  `smul_underlyingModule`, a separate lemma whose section argument is declared at the sections
  of the sheaf of rings, so the multiplication elaborates there and the main proof only
  composes equalities.
* `CategoryTheory.Functor.map_isIso` and `CategoryTheory.isIso_of_reflects_iso` both want their
  `IsIso` hypothesis at the functor's own spelling of the morphism.  `IsIso φ.right` and
  `IsIso ((Under.forget X.sheaf).map φ)` are definitionally equal and instance search does not
  identify them, so each is introduced by a `have` at the spelling the next step asks for.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

universe v₁ u₁ u

namespace Stacks.AlgebraPullbackQcoh

section Unit

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}}

/-- **The morphism `unit R ⟶ (restrictScalars ρ).obj (unit R')` attached to a morphism
`ρ : R ⟶ R'` of sheaves of rings.**  On sections it is `ρ`; it is linear because `ρ` is
multiplicative and the scalars act by multiplication on both sides.  This is
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit` with restriction of scalars in place
of a direct image. -/
def unitToRestrictScalarsObjUnit (ρ : R ⟶ R') :
    SheafOfModules.unit R ⟶
      (SheafOfModules.restrictScalars.{u} ρ).obj (SheafOfModules.unit R') where
  val.app U := ModuleCat.homMk ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map (ρ.hom.app U))
    (fun r => by
      ext m
      exact ((ρ.hom.app U).hom.map_mul _ _).symm)
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom (ρ.hom.naturality f) _

end Unit

section AlgebraSheaf

open Stacks.RelativeSpec

variable {X : Scheme.{u}}

/-- **The scalar action on the underlying module of an algebra sheaf.**  A section `r` of the
structure sheaf acts on a section `a` of `E` by multiplication by the image of `r` under the
structure morphism of `E`, on the nose. -/
lemma smul_underlyingModule (E : AlgebraSheaf X) (U : (Opens X)ᵒᵖ)
    (r : X.ringCatSheaf.obj.obj U) (a : (AlgebraSheaf.ringSheaf E).obj.obj U) :
    AddCommGrpCat.Hom.hom (((AlgebraSheaf.underlyingModule E).val.obj U).smul r).asHom a =
      ((AlgebraSheaf.structureMap E).hom.app U) r * a := rfl

variable {A B : AlgebraSheaf X} (φ : A ⟶ B)

/-- A morphism of algebra sheaves, read as a morphism of the underlying sheaves of not
necessarily commutative rings — the category sheaves of modules are taken over. -/
def ringMap : AlgebraSheaf.ringSheaf A ⟶ AlgebraSheaf.ringSheaf B :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map φ.right

/-- **A morphism of algebra sheaves carries the structure morphism of its source to the
structure morphism of its target.**  This is the commuting triangle of the `Under` category,
pushed through `CategoryTheory.sheafCompose`. -/
lemma structureMap_comp_ringMap :
    AlgebraSheaf.structureMap A ≫ ringMap φ = AlgebraSheaf.structureMap B :=
  ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map_comp A.hom φ.right).symm.trans
    (congrArg (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map (Under.w φ))

/-- `Stacks.AlgebraPullbackQcoh.structureMap_comp_ringMap` on sections over an open. -/
lemma ringMap_structureMap_app (U : (Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj U) :
    ((ringMap φ).hom.app U) (((AlgebraSheaf.structureMap A).hom.app U) r) =
      ((AlgebraSheaf.structureMap B).hom.app U) r :=
  ConcreteCategory.congr_hom
    (congrArg (fun ψ : X.ringCatSheaf ⟶ AlgebraSheaf.ringSheaf B => ψ.hom.app U)
      (structureMap_comp_ringMap φ)) r

/-- **The morphism of underlying `𝒪_X`-modules induced by a morphism of algebra sheaves.**  On
sections it is the morphism itself; linearity over the structure sheaf is multiplicativity
together with `ringMap_structureMap_app`. -/
def moduleMap : AlgebraSheaf.underlyingModule A ⟶ AlgebraSheaf.underlyingModule B where
  val.app U := ModuleCat.homMk ((forget₂ RingCat.{u} AddCommGrpCat.{u}).map
      ((ringMap φ).hom.app U)) (fun r => by
    ext a
    exact ((smul_underlyingModule B U r ((ringMap φ).hom.app U a)).trans
        ((congrArg (fun y => y * ((ringMap φ).hom.app U) a)
            (ringMap_structureMap_app φ U r).symm).trans
          (map_mul ((ringMap φ).hom.app U).hom _ _).symm)).trans
      (congrArg ((ringMap φ).hom.app U) (smul_underlyingModule A U r a).symm))
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom ((ringMap φ).hom.naturality f) _

/-- The underlying module morphism is the morphism of algebra sheaves on sections. -/
lemma moduleMap_val_app_apply (U : (Opens X)ᵒᵖ) (a : (AlgebraSheaf.ringSheaf A).obj.obj U) :
    (moduleMap φ).val.app U a = (ringMap φ).hom.app U a := rfl

/-- **A morphism of algebra sheaves whose underlying module morphism is invertible is
invertible.**  Invertibility of the module morphism makes each of its components bijective;
those components are the components of the morphism of algebra sheaves as functions, so each
of the latter is an isomorphism of commutative rings, and `φ` is an isomorphism because
`CategoryTheory.sheafToPresheaf` is fully faithful and `CategoryTheory.Under.forget` reflects
isomorphisms. -/
theorem isIso_of_isIso_moduleMap (h : IsIso (moduleMap φ)) : IsIso φ := by
  have := h
  have hpre : IsIso ((Scheme.Modules.toPresheaf X).map (moduleMap φ)) := Functor.map_isIso _ _
  have hb : ∀ U : (Opens X)ᵒᵖ, Function.Bijective ((φ.right.hom.app U).hom) := fun U =>
    ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.toPresheaf X).map (moduleMap φ)).app U)
  have happ : ∀ U : (Opens X)ᵒᵖ, IsIso (φ.right.hom.app U) := fun U =>
    (ConcreteCategory.isIso_iff_bijective _).2 (hb U)
  have hhom : IsIso φ.right.hom := NatIso.isIso_of_isIso_app _
  have hmap : IsIso ((sheafToPresheaf (Opens.grothendieckTopology (X : Type u))
    CommRingCat.{u}).map φ.right) := hhom
  have hright : IsIso φ.right :=
    (fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology (X : Type u))
      CommRingCat.{u}).isIso_of_isIso_map φ.right
  have hforget : IsIso ((Under.forget X.sheaf).map φ) := hright
  exact isIso_of_reflects_iso φ (Under.forget X.sheaf)

/-- **The criterion in local form.**  A morphism of algebra sheaves is invertible as soon as
its underlying module morphism becomes invertible after restriction to each member of an open
cover of `X`.  This is the shape an argument over an affine cover consumes: on an affine
member, invertibility of a morphism of quasi-coherent modules is detected on global sections
by `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ`. -/
theorem isIso_of_isIso_restrict_moduleMap {I : Type*} (U : I → X.Opens)
    (hU : TopologicalSpace.IsOpenCover U)
    (h : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map (moduleMap φ))) : IsIso φ :=
  isIso_of_isIso_moduleMap φ
    (Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict (moduleMap φ) U hU h)

end AlgebraSheaf

end Stacks.AlgebraPullbackQcoh

end
