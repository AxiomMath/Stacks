module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlueDescentDatumViaUnprimed

/-!
# The two spellings of `𝒢|_{X i}` in Stacks 03DX (1): `objRestrict` and `restrFun`

The gluing step of Stacks 03DX (1) speaks of the restriction of a module on `(Sch/S)_fppf` to a
member `T` of a covering family of the final object in **two different spellings**, and no lemma
in the library connected them.

* `AlgebraicGeometry.BigFppfOver.objRestrict` restricts to the localization at `T` and then
  reindexes along the equivalence of Stacks 06WI, landing in modules on the big fppf site of the
  scheme of `T`.  This is the spelling in which Stacks 03DV is available:
  `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`, the local step
  `…exists_isQuasicoherent_iso_associatedModule_objRestrict`, and the transition isomorphisms
  `AlgebraicGeometry.BigFppfOver.transitionIso` all speak of it.
* `restrFun` of the internal hom restricts the underlying presheaf of modules to the slice
  `(Sch/S)_fppf / T` and nothing else.  This is the spelling in which Stacks 03EM is available:
  `AlgebraicGeometry.BigFppfOver.exists_iso_of_isCompatible` and hence
  `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_memberProd` consume and
  return local isomorphisms in it.

**This file is the bridge.**  The two differ by exactly one thing — the reindexing of Stacks
06WI, which is an *equivalence* of categories of sheaves of modules
(`Stacks.SheafOfModules.reindexEquivalence` at `AlgebraicGeometry.BigFppfOver.objEquiv`) and in
particular fully faithful.  Restriction to the slice, `SheafOfModules.overFunctor`, is `restrFun`
on the nose, and `AlgebraicGeometry.BigFppfOver.objRestrict` is restriction to the slice followed
by that equivalence.  So an isomorphism of `objRestrict`-restrictions has a *unique* preimage
under the equivalence, and that preimage read on underlying presheaves of modules is an
isomorphism in the `restrFun` spelling.

With the bridge in place, `AlgebraicGeometry.BigFppfOver`
`.essImage_associatedModuleQcoh_of_forall_objRestrict` is the Stacks 03EM step of Stacks 03DX (1)
**stated in the spelling Stacks 03DV supplies**: a quasi-coherent `𝓕` on `S` together with
isomorphisms `𝓕^a|_{(Sch/X_i)_fppf} ≅ 𝒢|_{(Sch/X_i)_fppf}` whose preimages agree over the fibre
products exhibits `𝒢` in the essential image.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.objRestrictEquivalence`: the reindexing of Stacks 06WI as an
  equivalence of categories of sheaves of modules, whose functor is
  `AlgebraicGeometry.BigFppfOver.objRestrictFunctor` on the nose.
* `AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso`: **the bridge.**  An isomorphism of the
  `objRestrict`-restrictions of two modules on `(Sch/S)_fppf` is the image of a unique
  isomorphism of their restrictions to the slice at `T`.
* `AlgebraicGeometry.BigFppfOver.objRestrictRestrFunIso`: that preimage read in the `restrFun`
  spelling.

## Main results

* `homRestr_app_eq`: the sections of the relocalization of an internal-hom section — the
  component of `homRestr O F G g α` over an object `A` of the slice at the source is the
  component of `α` over its image in the slice at the target.  Stated at an arbitrary site, which
  is what makes it usable at the structure sheaf of the big fppf site.
* `AlgebraicGeometry.BigFppfOver.restrFun_obj_eq_over_val` and
  `AlgebraicGeometry.BigFppfOver.restrFun_map_eq_over_map_val`: **`restrFun` is
  `SheafOfModules.overFunctor` on underlying presheaves of modules**, on objects and on
  morphisms, by `rfl`.
* `AlgebraicGeometry.BigFppfOver.objRestrict_eq_overFunctor_comp`: **`objRestrict` is restriction
  to the slice followed by the reindexing**, by `rfl`.
* `AlgebraicGeometry.BigFppfOver.objRestrictFunctor_map_objRestrictPreimageIso`: the bridge is a
  section of `AlgebraicGeometry.BigFppfOver.objRestrictFunctor`, which is what says it changes
  the isomorphism in no way.
* `AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso_injective`: the bridge is injective, the
  reindexing being faithful; so an identity between two local isomorphisms in the `restrFun`
  spelling is an identity between them in the `objRestrict` spelling and conversely.
* `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_objRestrict`: **the
  Stacks 03EM step of Stacks 03DX (1) in the `objRestrict` spelling**, unconditionally.
* `AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_of_forall_objRestrict`: the shape
  in which `AlgebraicGeometry.BigFppfOver.AssociatedModuleRefinedDatum` — and hence, through
  `AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff`, the descent datum of Stacks
  03DX (1) — is reduced to the production of such a family out of the effectivity of
  `AlgebraicGeometry.BigFppfOver.memberHypercoverQcohDatum`.

## Implementation notes

Nothing here carries a `stacks` attribute: `AlgebraicGeometry.BigFppfOver`
`.essImage_associatedModuleQcoh_of_forall_objRestrict` is one paragraph of the proof of a clause
of Stacks 03DX, not the clause.

Every identification below is a `rfl`, and the reason the bridge is nevertheless a file and not a
line is the *cost* of those `rfl`s at the concrete structure sheaf of the big fppf site.  Three
of them go through: `restrFun` against `SheafOfModules.overFunctor` on objects and on morphisms,
and `objRestrict` against the composite.  The fourth — `homRestr` against
`SheafOfModules.overMap`, which is the same statement one slice down — does **not**: the two
morphisms of sheaves of rings that present the two relocalizations, `CategoryTheory.eqToHom` of
`ORestr_reloc` and the inverse of `CategoryTheory.Sheaf.pushforwardOverMapIso`, are
definitionally equal but comparing them at this structure sheaf exceeds the heartbeat budget,
whether the comparison is made on the functors, on one module, or section by section after
`PresheafOfModules.hom_ext`.  So the agreement of a family of local isomorphisms is stated with
`homRestr` itself — the form
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_memberProd` asks for — and
`homRestr_app_eq`, proved at an arbitrary site where there is nothing to unfold, is what reduces
it to a statement about sections.

`AlgebraicGeometry.BigFppfOver.objRestrictEquivalence` is literally
`Stacks.SheafOfModules.reindexEquivalence`, whose functor is the pushforward along the identity
morphism of sheaves of rings; `AlgebraicGeometry.BigFppfOver.objRestrictFunctor` is that same
pushforward, so `objRestrictEquivalence_functor` is a `rfl` and no transport is incurred anywhere
below.  The instances the equivalence needs — continuity of both directions of
`AlgebraicGeometry.BigFppfOver.objEquiv` — are the ones
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/MemberLocalStep.lean` declares.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
-/

@[expose] public section

open CategoryTheory

universe t v₁ u₁ u w

/-! ### The sections of a relocalized internal-hom section -/

section InternalHom

variable {C : Type u₁} [Category.{v₁} C] (O : Cᵒᵖ ⥤ CommRingCat.{t})

/-- **The components of a relocalized internal-hom section.**  For `g : V ⟶ U` an arrow of the
site and `α : F|_U ⟶ G|_U` a section of the internal hom over `U`, the component of its
relocalization `homRestr O F G g α : F|_V ⟶ G|_V` over an object `A` of the slice `C/V` is the
component of `α` over the image of `A` in the slice `C/U`.

This is the whole content of `homRestr`: the relocalization is restriction along
`CategoryTheory.Over.map g`, which is reindexing, and the two transports along
`reloc_restr_obj` are transports along `rfl`.  It is stated at an arbitrary site because that is
where it costs nothing — at a concrete structure sheaf the two sides are still definitionally
equal, but the elaborator has to unfold the two morphisms of sheaves of rings presenting the two
relocalizations in order to see it. -/
public theorem homRestr_app_eq {V U : C} (g : V ⟶ U)
    {F G : PresheafOfModules.{w} (Oforget O)}
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) (A : (Over V)ᵒᵖ) :
    (homRestr O F G g α).app A = α.app (Opposite.op ((Over.map g).obj A.unop)) := rfl

/-- **Two relocalized internal-hom sections agree as soon as their components do.**  This is
`homRestr_app_eq` read as a criterion: an identity between the relocalizations of two sections
along two arrows out of one object of the site is an identity between the components of the two
sections at the images of each object of the slice. -/
public theorem homRestr_eq_homRestr_of_app {V U U' : C} (g : V ⟶ U) (g' : V ⟶ U')
    {F G : PresheafOfModules.{w} (Oforget O)}
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G)
    (α' : (restrFun O U').obj F ⟶ (restrFun O U').obj G)
    (h : ∀ A : (Over V)ᵒᵖ, α.app (Opposite.op ((Over.map g).obj A.unop)) =
      α'.app (Opposite.op ((Over.map g').obj A.unop))) :
    homRestr O F G g α = homRestr O F G g' α' :=
  PresheafOfModules.hom_ext fun A =>
    (homRestr_app_eq O g α A).trans ((h A).trans (homRestr_app_eq O g' α' A).symm)

end InternalHom

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### `restrFun` is restriction to the slice -/

/-- **The `restrFun` of Stacks 03EM is `SheafOfModules.overFunctor` on underlying presheaves of
modules.**  Both are the pushforward of presheaves of modules along the identity morphism of
`(Over.forget T).op ⋙ 𝒪`, so the restriction of a sheaf of modules to the localization of the
big fppf site of `S` at `T` *is*, on underlying presheaves, its relocalization in the sense of
the internal hom. -/
public theorem restrFun_obj_eq_over_val (T : BigFppfOver B S hS)
    (M : SheafOfModules.{u} (structureSheaf B S hS)) :
    (restrFun (commStructurePresheaf B S hS) T).obj M.val = (M.over T).val := rfl

/-- **The same identification on morphisms**: the relocalization of a global morphism of sheaves
of modules is its restriction to the localization at `T`, on underlying presheaves. -/
public theorem restrFun_map_eq_over_map_val (T : BigFppfOver B S hS)
    {M N : SheafOfModules.{u} (structureSheaf B S hS)} (φ : M ⟶ N) :
    (restrFun (commStructurePresheaf B S hS) T).map φ.val = (φ.over T).val := rfl

/-- **Restriction to the big fppf site of the scheme of `T` is restriction to the localization at
`T` followed by the reindexing of Stacks 06WI**, as an equality of functors.  This is the
definition of `AlgebraicGeometry.BigFppfOver.objRestrict` read back; it is recorded because it is
what makes `AlgebraicGeometry.BigFppfOver.objRestrictFunctor` the only difference between the two
spellings of the restriction. -/
public theorem objRestrict_eq_overFunctor_comp (T : BigFppfOver B S hS) :
    objRestrict B S hS T =
      SheafOfModules.overFunctor.{u} (structureSheaf B S hS) T ⋙ objRestrictFunctor B S hS T :=
  rfl

/-! ### The reindexing of Stacks 06WI as an equivalence -/

/-- **The reindexing of Stacks 06WI is an equivalence of categories of sheaves of modules.**  The
equivalence of sites `AlgebraicGeometry.BigFppfOver.objEquiv` between the big fppf site of the
scheme of `T` and the localization of the big fppf site of `S` at `T` carries the structure sheaf
of the one to the structure sheaf of the other on the nose
(`AlgebraicGeometry.BigFppfOver.reindexRing_objEquiv`), so
`Stacks.SheafOfModules.reindexEquivalence` applies with the identity as its comparison of
structure sheaves. -/
public noncomputable def objRestrictEquivalence (T : BigFppfOver B S hS) :
    SheafOfModules.{u} ((structureSheaf B S hS).over T) ≌
      SheafOfModules.{u} (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  Stacks.SheafOfModules.reindexEquivalence
    (J' := topology B (objScheme B S hS T) (contains_objScheme B S hS T))
    (objEquiv B S hS T) ((structureSheaf B S hS).over T)

/-- **The functor of that equivalence is `AlgebraicGeometry.BigFppfOver.objRestrictFunctor`** on
the nose: both are the pushforward of sheaves of modules along the identity morphism of the
transported structure sheaf. -/
public theorem objRestrictEquivalence_functor (T : BigFppfOver B S hS) :
    (objRestrictEquivalence B S hS T).functor = objRestrictFunctor B S hS T := rfl

/-- **The reindexing of Stacks 06WI is fully faithful**, being the functor of an equivalence. -/
public noncomputable def objRestrictFunctorFullyFaithful (T : BigFppfOver B S hS) :
    (objRestrictFunctor B S hS T).FullyFaithful :=
  (objRestrictEquivalence B S hS T).fullyFaithfulFunctor

/-! ### The bridge -/

/-- **The bridge between the two spellings of a local isomorphism of Stacks 03DX (1).**  An
isomorphism of the restrictions of two modules on `(Sch/S)_fppf` to the big fppf site of the
scheme of `T` — the spelling Stacks 03DV supplies — is the image under the reindexing of Stacks
06WI of a unique isomorphism of their restrictions to the localization at `T` — the spelling
Stacks 03EM consumes.  This is that preimage.

It exists because `AlgebraicGeometry.BigFppfOver.objRestrict` is restriction to the localization
followed by the reindexing (`objRestrict_eq_overFunctor_comp`) and the reindexing is fully
faithful (`objRestrictFunctorFullyFaithful`). -/
public noncomputable def objRestrictPreimageIso {T : BigFppfOver B S hS}
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) :
    M.over T ≅ N.over T :=
  (objRestrictFunctorFullyFaithful B S hS T).preimageIso θ

/-- **The bridge changes the isomorphism in no way**: the image of
`AlgebraicGeometry.BigFppfOver.objRestrictPreimageIso` under the reindexing of Stacks 06WI is the
isomorphism it was formed from. -/
public theorem objRestrictFunctor_map_objRestrictPreimageIso {T : BigFppfOver B S hS}
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) :
    (objRestrictFunctor B S hS T).map (objRestrictPreimageIso B S hS θ).hom = θ.hom :=
  (objRestrictFunctorFullyFaithful B S hS T).map_preimage _

/-- **The bridge is injective.**  The reindexing of Stacks 06WI is faithful, so two local
isomorphisms in the `objRestrict` spelling with the same preimage are equal; an identity between
local isomorphisms may therefore be checked on either side of the bridge. -/
public theorem objRestrictPreimageIso_injective {T : BigFppfOver B S hS}
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    {θ θ' : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N}
    (h : objRestrictPreimageIso B S hS θ = objRestrictPreimageIso B S hS θ') : θ = θ' :=
  Iso.ext ((objRestrictFunctor_map_objRestrictPreimageIso B S hS θ).symm.trans
    ((congrArg (fun k : M.over T ≅ N.over T =>
      (objRestrictFunctor B S hS T).map k.hom) h).trans
      (objRestrictFunctor_map_objRestrictPreimageIso B S hS θ')))

/-- **The bridge, read in the `restrFun` spelling.**  The preimage of a local isomorphism under
the reindexing of Stacks 06WI, read on underlying presheaves of modules, is an isomorphism
`M|_T ≅ N|_T` in the relocalization spelling of the internal hom — which is the spelling
`AlgebraicGeometry.BigFppfOver.exists_iso_of_isCompatible`, Stacks 03EM at the big fppf site,
consumes. -/
public noncomputable def objRestrictRestrFunIso {T : BigFppfOver B S hS}
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) :
    (restrFun (commStructurePresheaf B S hS) T).obj M.val ≅
      (restrFun (commStructurePresheaf B S hS) T).obj N.val :=
  (SheafOfModules.forget _).mapIso (objRestrictPreimageIso B S hS θ)

/-- The underlying morphism of `AlgebraicGeometry.BigFppfOver.objRestrictRestrFunIso` is the
underlying morphism of the preimage. -/
public theorem objRestrictRestrFunIso_hom {T : BigFppfOver B S hS}
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N) :
    (objRestrictRestrFunIso B S hS θ).hom = (objRestrictPreimageIso B S hS θ).hom.val := rfl

/-- **The agreement of two local isomorphisms across the bridge, checked on sections.**  Let
`Z` be an object of `(Sch/S)_fppf` mapping to two objects `T` and `T'` by `g` and `g'`, and let
`θ` and `θ'` be isomorphisms of the restrictions of `M` and `N` to the big fppf sites of the
schemes of `T` and of `T'`.  Their relocalizations to `Z` agree as soon as the components of
their preimages agree at the images of each object of the slice at `Z`.

This is `homRestr_eq_homRestr_of_app` at the structure sheaf of the big fppf site, and it is the
form in which the agreement that
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_objRestrict` asks for is
reachable: the relocalization itself cannot be rewritten at this structure sheaf — see the
implementation notes — but each of its components can, the general lemma having nothing to
unfold. -/
public theorem homRestr_objRestrictPreimageIso_eq_of_app
    {Z T T' : BigFppfOver B S hS} (g : Z ⟶ T) (g' : Z ⟶ T')
    {M N : SheafOfModules.{u} (structureSheaf B S hS)}
    (θ : (objRestrict B S hS T).obj M ≅ (objRestrict B S hS T).obj N)
    (θ' : (objRestrict B S hS T').obj M ≅ (objRestrict B S hS T').obj N)
    (h : ∀ A : (Over Z)ᵒᵖ,
      (objRestrictPreimageIso B S hS θ).hom.val.app
          (Opposite.op ((Over.map g).obj A.unop)) =
        (objRestrictPreimageIso B S hS θ').hom.val.app
          (Opposite.op ((Over.map g').obj A.unop))) :
    homRestr (commStructurePresheaf B S hS) M.val N.val g
        (objRestrictPreimageIso B S hS θ).hom.val =
      homRestr (commStructurePresheaf B S hS) M.val N.val g'
        (objRestrictPreimageIso B S hS θ').hom.val :=
  homRestr_eq_homRestr_of_app (commStructurePresheaf B S hS) g g' _ _ h

/-! ### The Stacks 03EM step in the `objRestrict` spelling -/

/-- **The Stacks 03EM step of Stacks 03DX (1), with the local isomorphisms given in the spelling
Stacks 03DV supplies**, unconditionally.  A quasi-coherent `𝒪_S`-module `𝓕` together with
isomorphisms

    `𝓕^a|_{(Sch/X_i)_fppf} ≅ 𝒢|_{(Sch/X_i)_fppf}`

on a family of objects covering the final object of `(Sch/S)_fppf`, whose preimages under the
reindexing of Stacks 06WI agree over the fibre products `X i ×_S X j`, exhibits `𝒢` in the
essential image of `𝓕 ↦ 𝓕^a`.

This is `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_forall_memberProd` with
its local isomorphisms moved across the bridge: the family it asks for is the family of
underlying morphisms of the preimages, and the agreement it asks for is the agreement of those
same morphisms, because `AlgebraicGeometry.BigFppfOver.objRestrictRestrFunIso_hom` is a `rfl`. -/
public theorem essImage_associatedModuleQcoh_of_forall_objRestrict
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {I : Type w}
    (X : I → BigFppfOver B S hS) (hX : (topology B S hS).CoversTop X) (𝓕 : S.Modules)
    (h𝓕 : 𝓕.IsQuasicoherent)
    (θ : ∀ i, (objRestrict B S hS (X i)).obj ((associatedModule B S hS).obj 𝓕) ≅
      (objRestrict B S hS (X i)).obj G)
    (hθ : ∀ i j, homRestr (commStructurePresheaf B S hS)
          ((associatedModule B S hS).obj 𝓕).val G.val (memberProdFst B S hS X i j)
          (objRestrictPreimageIso B S hS (θ i)).hom.val =
        homRestr (commStructurePresheaf B S hS) ((associatedModule B S hS).obj 𝓕).val G.val
          (memberProdSnd B S hS X i j) (objRestrictPreimageIso B S hS (θ j)).hom.val) :
    (associatedModuleQcoh B S hS).essImage G :=
  essImage_associatedModuleQcoh_of_forall_memberProd B S hS G X hX 𝓕 h𝓕
    (fun i => objRestrictRestrFunIso B S hS (θ i)) hθ

/-- **The one-family descent datum of Stacks 03DX (1) is reduced to the production of a
compatible family of local isomorphisms in the `objRestrict` spelling.**  Given, for every family
`Y` of objects of `(Sch/S)_fppf` covering the final object whose structure morphisms are an fpqc
covering family of `S` and on whose members the restriction of `𝒢` is an associated module, a
quasi-coherent `𝓕` on `S` and isomorphisms `𝓕^a|_{(Sch/X_j)_fppf} ≅ 𝒢|_{(Sch/X_j)_fppf}` whose
preimages agree over the fibre products, `AlgebraicGeometry.BigFppfOver`
`.AssociatedModuleRefinedDatum` holds — and with it, by
`AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff`, the descent datum of
Stacks 03DX (1).

The covering family and the datum that the conclusion asks for are irrelevant here: the local
isomorphisms are produced *before* any appeal to effectivity, so the singleton family of the
identity of `S` and the canonical datum of `𝓕` are handed over and their effectivity is
discarded.  This is the shape in which a construction of the local isomorphisms out of the
effectivity of `AlgebraicGeometry.BigFppfOver.memberHypercoverQcohDatum` discharges the
residue. -/
public theorem associatedModuleRefinedDatum_of_forall_objRestrict
    (h : ∀ (G : SheafOfModules.{u} (structureSheaf B S hS)) (J : Type (u + 1))
      (Y : J → BigFppfOver B S hS), (topology B S hS).CoversTop Y →
      (objHypercover B S hS Y).presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S →
      (∀ j, HasLocalAssociatedModule B S hS G (Y j)) →
      ∃ (𝓕 : S.Modules) (_ : 𝓕.IsQuasicoherent)
        (θ : ∀ j, (objRestrict B S hS (Y j)).obj ((associatedModule B S hS).obj 𝓕) ≅
          (objRestrict B S hS (Y j)).obj G),
        ∀ j₁ j₂, homRestr (commStructurePresheaf B S hS)
              ((associatedModule B S hS).obj 𝓕).val G.val (memberProdFst B S hS Y j₁ j₂)
              (objRestrictPreimageIso B S hS (θ j₁)).hom.val =
            homRestr (commStructurePresheaf B S hS) ((associatedModule B S hS).obj 𝓕).val G.val
              (memberProdSnd B S hS Y j₁ j₂) (objRestrictPreimageIso B S hS (θ j₂)).hom.val) :
    AssociatedModuleRefinedDatum B S hS := by
  intro G J Y hY hfpqc hlocal
  obtain ⟨𝓕, h𝓕, θ, hθ⟩ := h G J Y hY hfpqc hlocal
  refine ⟨PreZeroHypercover.singleton.{u + 1} (𝟙 S), ?_,
    (canonicalDescentFunctor _).obj ⟨𝓕, h𝓕⟩, fun _ => ?_⟩
  · rw [PreZeroHypercover.presieve₀_singleton]
    exact Scheme.Hom.singleton_mem_fpqcPrecoverage (𝟙 S)
  · exact essImage_associatedModuleQcoh_of_forall_objRestrict B S hS G Y hY 𝓕 h𝓕 θ hθ

end AlgebraicGeometry.BigFppfOver

end
