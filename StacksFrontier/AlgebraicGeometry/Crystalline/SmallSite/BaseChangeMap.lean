module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactCocontinuous
public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelTower
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleCohomology

/-!
# The pullback of a module along change of divided power base, for `g` an open immersion

Let `(S, I, γ) ⟶ (S', I', γ')` be a morphism of divided power schemes over `ℤ_{(p)}` and let
`g : X ⟶ X'` be a compatible morphism of the schemes over the closed fibres, so that we are in
the situation of [Stacks, Tag 07MJ].  Write `A = Γ(S, 𝒪_S)` and `A' = Γ(S', 𝒪_{S'})`.
[Stacks, Tag 07MS] constructs, for a sheaf of `𝒪_{X'/S'}`-modules `F'` with pullback `F`, a
canonical *base change map*, and reads it on global sections as the map

`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)`

of `D(A)`, which is the map labelled (07MT) and the subject of [Stacks, Tag 07MU].

This file builds, **for `g` an open immersion**, the pullback `F` of `F'` on the small
crystalline site by restriction along change of divided power base, together with its exactness
and the comparison of the two scalar actions; the map (07MT) at that generality is built in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMapConstruction.lean`.  The tag
itself, for an arbitrary `g`, is
`...SmallSite.crisSheafBaseChangeMap` and its global-sections form
`...SmallSite.crisGlobalBaseChangeMap` (`SmallSite/BaseChangeMapGlobal07MS.lean`), with
`F = ...SmallSite.crisModuleInverseImage F'`; the pullback here agrees with that one by
`...SmallSite.crisModuleInverseImageIsoSmallChangeBase`.

## The two scalar rings, and which one acts where

The `A`-action on `Γ(Cris(X/S), F)` and the `A'`-action on `Γ(Cris(X'/S'), F')` come from
*different* structure morphisms: an element acts on the sections over an object `(U, T, δ)` by
pullback along that object's own structure morphism `T ⟶ S`, respectively `T ⟶ S'`, which is
`Crystalline.GlobalCrystallineSituation.SmallSite.baseRingHom`.  The two are related because
change of divided power base replaces the structure morphism `T ⟶ S` of an object by
`T ⟶ S ⟶ S'`, by `Crystalline.GlobalCrystallineSituation.changeBase_obj_toBase`.  Applying
`Γ(-, 𝒪)` to that factorization gives `baseRingHom_baseChangeRingHom_val`, which says the two
actions are matched by the ring map

`baseChangeRingHom : A' ⟶ A`

induced by `f : S ⟶ S'`.  So `A'` acts on the source of the base change map and `A` on its
target, and any comparison between them is a morphism over two rings, never over one.

## Generality: open immersions only

Change of divided power base does not restrict to the small crystalline sites for a general
`g : X ⟶ X'`: an object `(U, T, δ)` of `Cris(X/S)` has `U ⟶ X` an open immersion, and composing
with `g` destroys that.  So `Crystalline.GlobalCrystallineSituation.smallChangeBase` carries
`[IsOpenImmersion g]`
(`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Functoriality.lean:224`), and so does
everything in this file.  This is the generality of [Stacks, Tag 07KL], *not* that of
[Stacks, Tag 07MJ]; in particular it does not cover the hypothesis `X = X' ×_{S'₀} S₀` of
[Stacks, Tag 07MU](4).  The general small-site functoriality goes through the big site instead,
`Crystalline.GlobalCrystallineSituation.crisMorphism`
(`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/ToposFunctoriality.lean:139`), whose
inverse image involves the lower shriek.  A module-level pullback with coefficients on the big
site now exists, `...SmallSite.crisModulePullback` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeIsomorphism.lean`, with no
hypothesis on `g`, agreeing with the open-immersion version above by `rfl` wherever that one
applies.

This passage used to add that the lower shriek "has no identity comparison of structure sheaves",
which is false: the comparison *is* the identity, by `...SmallSite.ι_op_comp_crisRing` of
`SmallSite/CrisDirectImage.lean`, which holds by `rfl`.  What carries a *small-site* `F'` there
is the module-level `i_!` of [Stacks, Tag 07IJ], and that is now built, as
`...SmallSite.moduleLowerShriek` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LowerShriekModules.lean`, together with the
composite `...SmallSite.crisModuleInverseImage : ModuleSheaf S' ⥤ ModuleSheaf S`, which has no
hypothesis on `g`.  The sheafification `Stacks.SheafOfModules.lowerShriek` asks for is of
`AddCommGrpCat.{u + 1}`-valued presheaves on the big site, not of `ModuleCat`-valued ones, and
the chapter has it, as `...SmallSite.instHasSheafifyBigAddCommGrpCat`.

## Main definitions

* `smallChangeBaseStructureHom` — the comparison of structure sheaves on the small sites under
  change of divided power base.  It is the identity: restriction along change of base carries
  `𝒪_{X'/S'}` to `𝒪_{X/S}` on the nose.
* `smallChangeBaseModulePullback` — **the pullback `F` of a sheaf `F'` of `𝒪_{X'/S'}`-modules**,
  as a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)`, for `g` an open immersion.  It is the
  restriction itself, not a sheafification of it, which rests on continuity of change of base.
* `baseChangeRingHom` — the ring map `A' ⟶ A` induced by `f : S ⟶ S'`.

## Main results

* `smallChangeBaseModulePullback_obj_val_obj` — the pullback's sections over `(U, T, δ)` are the
  sections of `F'` over the image object, so the construction is pinned down pointwise and is not
  vacuous.
* `smallChangeBaseModulePullback_preservesFiniteLimits` and
  `smallChangeBaseModulePullback_preservesFiniteColimits` — **the pullback is exact**.  The first
  holds because the pullback is a direct image, hence a right adjoint; the second because change
  of divided power base is *co*continuous as well as continuous, so restriction commutes with
  sheafification.  Exactness is what would let the pullback act on bounded below derived
  categories, and so is the structural prerequisite for the derived base change map.
* `baseRingHom_baseChangeRingHom_val` — **the two scalar actions are matched by
  `baseChangeRingHom`**, the content of the "two scalar rings" section above.
* `baseChangeRingHom_id` — when `S = S'` the ring map `A' ⟶ A` is the identity.
* `smallChangeBaseGlobalSectionsTrans` and `baseChangeGlobalSectionsTrans` — **the comparison on
  global sections**, over the section ring of `𝒪_{X'/S'}` and then over `baseChangeRingHom`.
  The second is the underived base change map, the input the derived (07MT) is built from.

## What is and is not proved

What is proved, for `g` an open immersion, is that `F'` has a pullback `F` computed by
restriction; that this pullback is exact; that the `A`- and `A'`-actions are matched by
`baseChangeRingHom`; and that the comparison on global sections exists as a natural
transformation semilinear over that ring map.  No `@[stacks 07MS]` attribute is placed here: the
tag is registered at its own generality, an arbitrary `g`, in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMapGeneral.lean`.

**The comparison on global sections is constructed**, as `baseChangeGlobalSectionsTrans` below:
the natural transformation

`baseModuleGlobalSections S' ⟶ smallChangeBaseModulePullback ⋙ baseModuleGlobalSections S ⋙
ModuleCat.restrictScalars (baseChangeRingHom f)`

that the base change map derives from (07MT).  Its construction meets a `restrictScalars`
instance diamond: the source
`(baseModuleGlobalSections S').obj F'` carries its `A'`-module structure through
`ModuleCat.restrictScalars (baseRingHom S')`, and a raw `LinearMap` semilinear over
`baseChangeRingHom` makes elaboration oscillate between `ModuleCat.isModule` of the restricted
object and `Module.compHom _ (baseRingHom S')`, which are definitionally but not syntactically
equal.  The diamond is **circumvented, not fought**: the comparison is first built over the
*single* ring `Γ(Cris(X'/S'), 𝒪_{X'/S'})`, where no semilinearity over two base rings is
involved — `smallChangeBaseSectionsMap` on sections, `smallChangeBaseGlobalSectionsTrans` as a
natural transformation — and the change of base rings is then made by whiskering with
`smallChangeBaseRestrictScalarsIso`, the comparison of the two factorizations of the `A'`-action
supplied by `smallChangeBaseSectionRingHom_comp_baseRingHom`.  Mathlib's
`SheafOfModules.pushforwardSections`
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean`) is the
underlying function and `baseRingHom_baseChangeRingHom_val` its semilinearity.

The base change map itself is not constructed *here*.  The derived part — the five steps below,
each a declaration of the library — is assembled in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/BaseChangeMapConstruction.lean`, which
produces `...SmallSite.baseChangeMap07MT`, a term of `...SmallSite.BaseChangeMap07MT`, at the
generality of this file: `g` an open immersion.  That is [Stacks, Tag 07KL] and not
[Stacks, Tag 07MJ], so it does **not** cover the `X = X' ×_{S'₀} S₀` of [Stacks, Tag 07MU](4),
and no 07MU tag is placed anywhere.  The five steps are:

1. `Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans`
   (`StacksFrontier/Homology/DerivedIndexing/Basic.lean:604`) derives it to
   `RΓ_{S'} ⟶ R(pullback ⋙ Γ_S ⋙ res)`.
2. `Stacks.DerivedIndexing.rightDerivedPlusCompTrans`
   (`StacksFrontier/Homology/DerivedIndexing/Composite.lean:273`), the canonical map of
   [Stacks, Tag 05T2], splits that.  It is only a *map*, and is used as one; its being an
   isomorphism is the Leray comparison [Stacks, Tag 07MU] is about, and is not assumed.
3. `CategoryTheory.Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`
   (`StacksFrontier/Algebra/Homology/DerivedCategory/BaseChangeBoundedBelow.lean:81`) replaces the
   derived functor of the exact pullback by `Functor.mapDerivedCategoryPlus`
   (`StacksFrontier/Algebra/Homology/DerivedCategory/ExactFunctorBoundedBelow.lean:78`); this is
   what the exactness results above are for.
4. `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic`
   (`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlusComparisons.lean:145`)
   handles `Γ_S` against the exact restriction of scalars, its acyclicity hypothesis being free
   by `CategoryTheory.Functor.rightAcyclic_of_exact`.
5. The passage to the shape (07MT) is the adjunction
   `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction`
   (`StacksFrontier/Homology/Tor/DerivedChangeOfRingsAdjunction.lean:86`, [Stacks, Tag 0GMT]),
   against the derived tensor product
   `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`
   (`StacksFrontier/Homology/Tor/DerivedExtensionScalars.lean:1242`), which supplies
   `- ⊗^L_{A'} A : D(Mod_{A'}) ⥤ D(Mod_A)` in exactly the universes this chapter uses.  It is
   assembled at this chapter's functor as
   `Crystalline.GlobalCrystallineSituation.SmallSite.derivedBaseChangeTensorAdjunction` of
   `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusSemilinearAction.lean`.

No part of [Stacks, Tag 07MU] is stated here, and 07MU is not tagged.  Neither is 07MT.

## References

* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}

/-! ### The pullback of a module along change of divided power base -/

section Pullback

variable [IsOpenImmersion g]

/-- **Restriction along change of divided power base carries `𝒪_{X'/S'}` to `𝒪_{X/S}` on the
nose**, so the comparison morphism of the structure sheaves of the two small crystalline sites is
the identity.

Change of base leaves the ambient divided power scheme of an object untouched and the structure
sheaf of the small site sends an object to the ring of global sections of that scheme, so
`(smallChangeBase S S' f g h).op ⋙ SmallSite.crisRing S'` is `SmallSite.crisRing S` definitionally;
this is that equality read on sheaves.  Continuity of change of base,
`Crystalline.GlobalCrystallineSituation.smallChangeBase_isContinuous`, is what makes the
restriction a sheaf and hence makes the target of this map well formed. -/
def smallChangeBaseStructureHom (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    structureSheaf S ⟶
      ((smallChangeBase S S' f g h).sheafPushforwardContinuous RingCat.{u}
        (smallTopology S) (smallTopology S')).obj (structureSheaf S') :=
  ⟨𝟙 _⟩

/-- The pullback `F` of a sheaf `F'` of `𝒪_{X'/S'}`-modules along change of divided power base,
as a sheaf of `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)`, for `g` an open
immersion.  It agrees with the general pullback `...SmallSite.crisModuleInverseImage` of
[Stacks, Tag 07MS] by `...SmallSite.crisModuleInverseImageIsoSmallChangeBase`.

Its sections over an object `(U, T, δ)` of `Cris(X/S)` are the sections of `F'` over the image of
`(U, T, δ)` under change of base — the same ambient scheme `T`, with `U ⟶ X ⟶ X'` and
`T ⟶ S ⟶ S'` as its structure maps.  No tensor product is needed, because the comparison of
structure sheaves is the identity `smallChangeBaseStructureHom`; and this is the restriction
itself rather than a sheafification of it, because change of base is continuous. -/
noncomputable def smallChangeBaseModulePullback (S S' : GlobalCrystallineSituation.{u})
    (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    ModuleSheaf S' ⥤ ModuleSheaf S :=
  SheafOfModules.pushforward (smallChangeBaseStructureHom S S' f g h)

/-- The sections of the pullback `F` over an object `(U, T, δ)` of `Cris(X/S)` are the sections of
`F'` over the image of `(U, T, δ)` under change of divided power base. -/
theorem smallChangeBaseModulePullback_obj_val_obj (F' : ModuleSheaf S')
    (A : (CrystallineThickening S)ᵒᵖ) :
    (((smallChangeBaseModulePullback S S' f g h).obj F').val.obj A : Type (u + 1)) =
      (F'.val.obj (op ((smallChangeBase S S' f g h).obj A.unop)) : Type (u + 1)) :=
  rfl

/-- The pullback of modules along change of divided power base is additive: it acts on sections
by restriction, which is additive on the nose. -/
instance smallChangeBaseModulePullback_additive :
    (smallChangeBaseModulePullback S S' f g h).Additive where
  map_add := by intros; rfl

/-- **The pullback preserves finite limits.**  It is a direct image of sheaves of modules along a
continuous functor, hence a right adjoint; this is the left exact half of [Stacks, Tag 04BD](2),
`SheafOfModules.preservesFiniteLimits_pushforward`. -/
instance smallChangeBaseModulePullback_preservesFiniteLimits :
    PreservesFiniteLimits (smallChangeBaseModulePullback S S' f g h) :=
  SheafOfModules.preservesFiniteLimits_pushforward _

/-- **The pullback preserves finite colimits**, because change of divided power base is
*co*continuous as well as continuous
(`Crystalline.GlobalCrystallineSituation.smallChangeBase_isCocontinuous`), so restriction
commutes with sheafification.  This is the right exact half of [Stacks, Tag 04BD](2),
`SheafOfModules.exactFunctor_pushforward_of_isCocontinuous`.

Together with the previous instance this says the pullback is *exact*, which is what lets it be
extended to the bounded below derived categories by
`CategoryTheory.Functor.mapDerivedCategoryPlus` and is the reason the derived base change map
below exists. -/
instance smallChangeBaseModulePullback_preservesFiniteColimits :
    PreservesFiniteColimits (smallChangeBaseModulePullback S S' f g h) :=
  (SheafOfModules.exactFunctor_pushforward_of_isCocontinuous (smallChangeBase S S' f g h)
    (smallChangeBaseStructureHom S S' f g h)).2

end Pullback

/-! ### The ring map `A' ⟶ A` -/

/-- **The ring map `A' = Γ(S', 𝒪_{S'}) ⟶ A = Γ(S, 𝒪_S)`** induced by the morphism of divided
power bases `f : S ⟶ S'`.  This is the ring map the base change map of [Stacks, Tag 07MS] is
semilinear over, and the one along which `- ⊗_{A'} A` is taken. -/
def baseChangeRingHom (f : S.S ⟶ S'.S) : Γ(S'.S.scheme, ⊤) →+* Γ(S.S.scheme, ⊤) :=
  (Scheme.Γ.map f.hom.op).hom

/-- The ring map `baseChangeRingHom f` sends a global section `a` of `𝒪_{S'}` to its image under
the map on global sections induced by `f`. -/
@[simp]
theorem baseChangeRingHom_apply (f : S.S ⟶ S'.S) (a : Γ(S'.S.scheme, ⊤)) :
    baseChangeRingHom f a = (Scheme.Γ.map f.hom.op).hom a := rfl

/-- **When the base does not change, the ring map `A' ⟶ A` is the identity.**  This is what keeps
the base change map below from being vacuous: along `f = 𝟙` it is a map of `A`-modules over the
identity of `A`. -/
@[simp]
theorem baseChangeRingHom_id (S : GlobalCrystallineSituation.{u}) :
    baseChangeRingHom (S := S) (S' := S) (𝟙 S.S) = RingHom.id Γ(S.S.scheme, ⊤) := by
  ext a
  simp [baseChangeRingHom, DividedPowerScheme.Hom.id_hom]

/-! ### Matching the two scalar actions -/

section Scalars

variable [IsOpenImmersion g]

/-- The scalar through which an element `a` of `A'` acts on the sections of the pullback `F` over
an object `A` of `Cris(X/S)` is the one through which it acts on the sections of `F'` over the
image of `A`: both are the pullback of `a` along `T ⟶ S ⟶ S'`.

This is the whole of the scalar bookkeeping of the base change map: it is the semilinearity of
the comparison on global sections over `baseChangeRingHom`, stated at the level of the scalars so
that it is available independently of how that comparison is packaged.  It is
`Crystalline.GlobalCrystallineSituation.changeBase_obj_toBase`
— change of base replaces the structure morphism `T ⟶ S` by `T ⟶ S ⟶ S'` — read through
`Γ(-, 𝒪)`. -/
theorem baseRingHom_baseChangeRingHom_val (a : Γ(S'.S.scheme, ⊤))
    (A : (CrystallineThickening S)ᵒᵖ) :
    (baseRingHom S (baseChangeRingHom f a)).val A =
      (baseRingHom S' a).val (op ((smallChangeBase S S' f g h).obj A.unop)) := by
  rw [baseRingHom_apply_val, baseRingHom_apply_val, baseChangeRingHom_apply]
  change (Scheme.Γ.map A.unop.obj.toBase.hom.op).hom ((Scheme.Γ.map f.hom.op).hom a) =
    (Scheme.Γ.map (A.unop.obj.toBase ≫ f).hom.op).hom a
  rw [DividedPowerScheme.Hom.comp_hom, op_comp, Functor.map_comp]
  rfl

/-- The restriction of a compatible family of sections of `𝒪_{X'/S'}` along change of divided
power base, as a ring map `Γ(Cris(X'/S'), 𝒪_{X'/S'}) ⟶ Γ(Cris(X/S), 𝒪_{X/S})`. -/
noncomputable def smallChangeBaseSectionRingHom (S S' : GlobalCrystallineSituation.{u})
    (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    ↥(crystallineSectionRing S') →+* ↥(crystallineSectionRing S) where
  toFun a := ⟨fun A => a.val (op ((smallChangeBase S S' f g h).obj A.unop)),
    fun k => a.property ((smallChangeBase S S' f g h).op.map k)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The two factorizations of the `A'`-action on the sections of the pullback agree. -/
theorem smallChangeBaseSectionRingHom_comp_baseRingHom :
    (smallChangeBaseSectionRingHom S S' f g h).comp (baseRingHom S') =
      (baseRingHom S).comp (baseChangeRingHom f) :=
  RingHom.ext fun a => Subtype.ext <| funext fun A =>
    (baseRingHom_baseChangeRingHom_val a A).symm

/-- The comparison on global sections, as a map semilinear over the restriction of compatible
sections of the structure sheaf. -/
noncomputable def smallChangeBaseSectionsMap (F' : ModuleSheaf S') :
    (moduleGlobalSections S').obj F' →ₛₗ[smallChangeBaseSectionRingHom S S' f g h]
      (moduleGlobalSections S).obj ((smallChangeBaseModulePullback S S' f g h).obj F') where
  toFun s := SheafOfModules.pushforwardSections (smallChangeBaseStructureHom S S' f g h) s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The comparison on global sections as a natural transformation over the single ring
`Γ(Cris(X'/S'), 𝒪_{X'/S'})`. -/
noncomputable def smallChangeBaseGlobalSectionsTrans (S S' : GlobalCrystallineSituation.{u})
    (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    moduleGlobalSections S' ⟶
      smallChangeBaseModulePullback S S' f g h ⋙ moduleGlobalSections S ⋙
        ModuleCat.restrictScalars (smallChangeBaseSectionRingHom S S' f g h) where
  app F' := ModuleCat.semilinearMapAddEquiv _ _ _ (smallChangeBaseSectionsMap F')
  naturality F' G' k := by
    ext s
    rfl

/-- The comparison of the two factorizations of the `A'`-action, as an isomorphism of
restriction-of-scalars functors. -/
noncomputable def smallChangeBaseRestrictScalarsIso (S S' : GlobalCrystallineSituation.{u})
    (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    ModuleCat.restrictScalars.{u + 1} (smallChangeBaseSectionRingHom S S' f g h) ⋙
        ModuleCat.restrictScalars (baseRingHom S') ≅
      ModuleCat.restrictScalars (baseRingHom S) ⋙
        ModuleCat.restrictScalars (baseChangeRingHom f) :=
  (ModuleCat.restrictScalarsComp (baseRingHom S')
        (smallChangeBaseSectionRingHom S S' f g h)).symm ≪≫
    ModuleCat.restrictScalarsCongr smallChangeBaseSectionRingHom_comp_baseRingHom ≪≫
    ModuleCat.restrictScalarsComp (baseChangeRingHom f) (baseRingHom S)

/-- **The base change map on global sections**, as a natural transformation semilinear over
`baseChangeRingHom`. -/
noncomputable def baseChangeGlobalSectionsTrans (S S' : GlobalCrystallineSituation.{u})
    (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    baseModuleGlobalSections S' ⟶
      smallChangeBaseModulePullback S S' f g h ⋙ baseModuleGlobalSections S ⋙
        ModuleCat.restrictScalars (baseChangeRingHom f) :=
  Functor.whiskerRight (smallChangeBaseGlobalSectionsTrans S S' f g h)
      (ModuleCat.restrictScalars (baseRingHom S')) ≫
    Functor.whiskerLeft (smallChangeBaseModulePullback S S' f g h ⋙ moduleGlobalSections S)
      (smallChangeBaseRestrictScalarsIso S S' f g h).hom

end Scalars

end Crystalline.GlobalCrystallineSituation.SmallSite

end
