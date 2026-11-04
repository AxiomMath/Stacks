module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.DenseSubsiteMorphism

/-!
# Reindexing along an equivalence of ringed sites is compatible with the tensor product

Let `e : C' ≌ C` be an equivalence of categories which is an equivalence of sites for topologies
`J'` on `C'` and `J` on `C`, and let `𝒪` be a sheaf of commutative rings on `(C, J)`.
`Stacks.SheafOfModules.reindexEquivalence` is the induced equivalence of the categories of sheaves
of modules; its functor is `CategoryTheory.SheafOfModules.pushforward` along `e.functor` with the
*identity* structure map, the structure sheaf on `C'` being the transported one.  This file proves
that it carries the tensor product sheaf of Stacks 01CA to the tensor product sheaf:

`(𝓕 ⊗_𝒪 𝓖)|_{C'} ≅ 𝓕|_{C'} ⊗_{𝒪|_{C'}} 𝓖|_{C'}`,

with no hypothesis on `𝓕` or `𝓖`.  The two sheafifications are formed on different sites, so this
is not a formal consequence of the presheaf-level statement.

## What it is

It is **Stacks 03EL** at the morphism of ringed sites presented by `e.inverse`, read across an
identification of the reindexing with a pullback of modules.  Reindexing is a *direct image*, so
its compatibility with the tensor product is not the generic one of a direct image — a direct
image is only lax monoidal.  The point is that for an equivalence of sites the direct image along
`e.functor` is also a *left* adjoint, namely of the direct image along `e.inverse`, and the
pullback of modules along `e.inverse` is a left adjoint of that same functor; so the two are
identified by `CategoryTheory.Adjunction.leftAdjointUniq`, after which 03EL applies verbatim.

The chain is:

* `Stacks.SheafOfModules.reindexRingedSiteHom` is `e.inverse` as an
  `AlgebraicGeometry.RingedSite.HomGeneral` from the reindexed ringed site to the given one.  Its
  site condition is `IsMorphismOfSites.ofIsDenseSubsite` — either direction of an equivalence of
  sites is a morphism of sites — and its structure map is
  `Stacks.SheafOfModules.reindexBackSharpComm`, the counit of `e` read on the structure sheaf,
  which is `Stacks.SheafOfModules.reindexBackSharp` with commutativity not yet forgotten.
* `Stacks.SheafOfModules.pullbackModulesReindexIso` identifies the pullback of sheaves of modules
  along the attached morphism of ringed topoi with the functor of `reindexEquivalence`.  It
  composes `AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral`, which passes
  from the four-field presentation of the geometric morphism to the site-presented one, with
  uniqueness of left adjoints for the site-presented pullback and the reindexing.
* `Stacks.SheafOfModules.reindexTensorIso` is `Stacks.SheafOfModules.pullbackTensorIso` read
  across that identification.

## Main definitions

* `Stacks.SheafOfModules.reindexCommRing`: the structure sheaf of commutative rings transported
  along `e`.
* `Stacks.SheafOfModules.reindexBackSharpComm`: the structure map of the inverse equivalence, on
  sheaves of commutative rings.
* `Stacks.SheafOfModules.reindexRingedSiteHom`: the reindexing as a morphism of ringed sites at
  independent universes.
* `Stacks.SheafOfModules.pullbackModulesReindexIso`: the pullback of modules along it is the
  functor of `Stacks.SheafOfModules.reindexEquivalence`.
* `Stacks.SheafOfModules.reindexTensorIso`: **the compatibility of the reindexing with the tensor
  product sheaf.**

## Implementation notes

Both tensor products are written at the bifunctor spelling
`Stacks.SheafOfModules.Tensor.sheafTensor`, which is the one Stacks 03EL is stated
with and the one the body produces.  A consumer whose tensor product is spelled differently —
`Stacks.SheafOfModules.Tensor.sheafTensor`, say — should bridge to it with a
separate `rfl` lemma rather than ask for the comparison at that spelling directly: a declared
result type at the consumer's spelling forces the elaborator to check the whole composite against
it and that exhausts the heartbeat budget at `whnf`.  This is the split recorded in the
implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DenseSubsiteSheafTensor.lean` and used again in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleAssociatedModuleMonoidal.lean`.

The two sites share their object and morphism universes, because
`Stacks.SheafOfModules.reindexEquivalence` does; nothing else here needs them to agree.

No `@[stacks]` attribute is claimed.  Stacks 03EL is registered on
`Stacks.SheafOfModules.pullbackTensorIso`, which proves it for an arbitrary morphism of ringed
topoi, and this instantiates it at one morphism; the clauses of Stacks 03CH and 00X1 used are
already covered by `IsMorphismOfSites.ofIsDenseSubsite`.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03CH](https://stacks.math.columbia.edu/tag/03CH)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (O : Sheaf J CommRingCat.{w})

/-- The structure sheaf of commutative rings transported along an equivalence of sites
`e : C' ≌ C`, that is, the direct image of `𝒪` under `e.functor`.

This is `Stacks.SheafOfModules.reindexRing` with commutativity not yet forgotten; forgetting it
commutes with the direct image on the nose, so the sheaf of rings underlying this one *is*
`reindexRing J' e` of the sheaf of rings underlying `𝒪`. -/
abbrev reindexCommRing : Sheaf J' CommRingCat.{w} :=
  (e.functor.sheafPushforwardContinuous CommRingCat.{w} J' J).obj O

/-- The given site, with its structure sheaf, as a ringed site. -/
abbrev siteRingedSite (J : GrothendieckTopology C) (O : Sheaf J CommRingCat.{w}) :
    AlgebraicGeometry.RingedSite.{u, v, w} where
  C := C
  J := J
  O := O

/-- The reindexed site, with the transported structure sheaf, as a ringed site. -/
abbrev reindexRingedSite : AlgebraicGeometry.RingedSite.{u, v, w} where
  C := C'
  J := J'
  O := reindexCommRing J' e O

/-- The structure map of the inverse of an equivalence of ringed sites, on sheaves of
*commutative* rings: the counit of `e` identifies `𝒪` with the direct image under `e.inverse` of
the transported structure sheaf.

This is the formula of `Stacks.SheafOfModules.reindexBackSharp`, taken before commutativity is
forgotten. -/
def reindexBackSharpComm :
    O ⟶ (e.inverse.sheafPushforwardContinuous CommRingCat.{w} J J').obj
      (reindexCommRing J' e O) :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op e.counit) O.obj)

variable [hmos : _root_.IsMorphismOfSites.{w} e.inverse J J']

/-- **Reindexing along an equivalence of sites, as a morphism of ringed sites** at independent
object universes.  The functor is `e.inverse`, which is a morphism of sites by
`IsMorphismOfSites.ofIsDenseSubsite`, and the structure map is
`Stacks.SheafOfModules.reindexBackSharpComm`. -/
def reindexRingedSiteHom :
    AlgebraicGeometry.RingedSite.HomGeneral (reindexRingedSite J' e O) (siteRingedSite J O) where
  u := e.inverse
  isMorphismOfSites := hmos
  fsharp := reindexBackSharpComm J' e O

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The underlying functor of `Stacks.SheafOfModules.reindexRingedSiteHom` is `e.inverse`. -/
@[simp]
theorem reindexRingedSiteHom_u : (reindexRingedSiteHom J' e O).u = e.inverse := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The structure map of `Stacks.SheafOfModules.reindexRingedSiteHom` is
`Stacks.SheafOfModules.reindexBackSharpComm`. -/
@[simp]
theorem reindexRingedSiteHom_fsharp :
    (reindexRingedSiteHom J' e O).fsharp = reindexBackSharpComm J' e O := rfl

section Pullback

variable [J.HasSheafCompose (forget RingCat.{w})] [J'.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [J'.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C] [LocallySmall.{w} C']

/-- The reindexing, in the shape of morphism of ringed topoi that the pullback of modules of
Stacks 03D6 and the comparison of Stacks 03EL consume. -/
abbrev reindexRingedToposModulesHom :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (reindexRingedSite J' e O).toRingedTopos (siteRingedSite J O).toRingedTopos :=
  (reindexRingedSiteHom J' e O).toRingedToposHom.toRingedToposModulesHom

/-- **The pullback of sheaves of modules along the reindexing is the functor of the reindexing
equivalence.**

The site-presented pullback is `CategoryTheory.SheafOfModules.pullback` of
`Stacks.SheafOfModules.reindexBackSharp`, so it is a left adjoint of the direct image along
`e.inverse`; and so is the functor of `Stacks.SheafOfModules.reindexEquivalence`, whose inverse
*is* that direct image.  Uniqueness of left adjoints identifies the two, and
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackModulesToposIsoGeneral` passes from the
four-field presentation of the geometric morphism to the site-presented one. -/
def pullbackModulesReindexIso :
    (reindexRingedToposModulesHom J' e O).pullbackModules ≅
      (reindexEquivalence.{w, w, u, v, u, v} e
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor :=
  (reindexRingedSiteHom J' e O).pullbackModulesToposIsoGeneral ≪≫
    Adjunction.leftAdjointUniq
      (reindexRingedSiteHom J' e O).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
      (reindexEquivalence.{w, w, u, v, u, v} e
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).toAdjunction

/-- **Reindexing along an equivalence of ringed sites carries the tensor product sheaf to the
tensor product sheaf.**  For sheaves of `𝒪`-modules `𝓕` and `𝓖` on `(C, J)`,

`(𝓕 ⊗_𝒪 𝓖)|_{C'} ≅ 𝓕|_{C'} ⊗_{𝒪|_{C'}} 𝓖|_{C'}`

on `(C', J')`, with no hypothesis on `𝓕` or `𝓖`.

This is Stacks 03EL, `Stacks.SheafOfModules.pullbackTensorIso`, at the morphism of ringed topoi
attached to `e.inverse`, read across
`Stacks.SheafOfModules.pullbackModulesReindexIso`.  Both tensor products are written at the
bifunctor spelling Stacks 03EL uses. -/
def reindexTensorIso (M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (reindexEquivalence.{w, w, u, v, u, v} e (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj M).obj N) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (reindexCommRing J' e O)).obj
        ((reindexEquivalence.{w, w, u, v, u, v} e
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor.obj M)).obj
        ((reindexEquivalence.{w, w, u, v, u, v} e
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).functor.obj N) :=
  (pullbackModulesReindexIso J' e O).symm.app _ ≪≫
    (Stacks.SheafOfModules.pullbackTensorIso
      (reindexRingedToposModulesHom J' e O)).app (M, N) ≪≫
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} (reindexCommRing J' e O)).mapIso
      ((pullbackModulesReindexIso J' e O).app M)).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        (reindexCommRing J' e O)).obj _).mapIso
        ((pullbackModulesReindexIso J' e O).app N))

end Pullback

end Stacks.SheafOfModules

end
