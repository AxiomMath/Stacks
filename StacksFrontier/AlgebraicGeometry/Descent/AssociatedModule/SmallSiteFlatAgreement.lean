module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFlatAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallFlatSiteFlatAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallFlatSiteQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiLocalTypesComparison
import StacksCore.Tactic.StacksAttribute

/-!
# Flatness across the equivalences `QCoh(𝒪_S) ≌ QCoh(S_τ, 𝒪)` of the small sites

Let `S` be a scheme.  Descent, Proposition 03DX (2) makes `𝓕 ↦ 𝓕^a` an equivalence of
categories `QCoh(𝒪_S) ≌ QCoh(S_τ, 𝒪)` for the small sites `S_Zar` and `S_étale`, and the library
extends it to the small sites `S_τ` for `τ ∈ {smooth, syntomic, fppf}`.  Descent, Lemma 05VG
says that these equivalences have the property

    `𝓕` is flat  ⇔  `𝓕^a` is flat as an `𝒪`-module,

flatness being that of Modules on Sites, Definition 03ER (3): `𝓖 ↦ 𝓖 ⊗_𝒪 𝓕` is an exact
endofunctor of `Mod(𝒪)`, which is `Stacks.SheafOfModules.IsFlat` (definitionally the same
predicate as `AlgebraicGeometry.SheafOfModules.IsFlat`).  It is used on both sides: on the left
for `𝓕` on the ringed site `S.zariskiRingedSite` of the opens of `S` with `𝒪_S`, on the right for
`𝓕^a` on the small site with its structure sheaf.  This file states that clause in the source's
own form, for an object `𝓕` of `QCoh(𝒪_S)` and its image under the functor of the equivalence of
03DX on each small site.

No equivalence of ringed topoi, and no other comparison, is a hypothesis of any statement here:
the only data are the scheme `S`, a big site containing it, the kind `κ` of small flat site where
there is one, and `𝓕`.

* On `S_Zar` the comparison `S_Zar → (S, 𝒪_S)` of Remark 03FH *is* an equivalence of ringed
  topoi, and that is proved, not assumed: its direct image is an equivalence because the opens of
  `S` form a dense subsite of `S_Zar`, and its structure map is invertible because every
  restriction map of `𝒪` along an open immersion is.  Flatness then transfers in both directions
  by Stacks 05VD applied to the morphism and to its inverse.
* On `S_étale` the comparison is not an equivalence of topoi.  The `only if` half is Stacks 05VD;
  the `if` half holds because the pullback `ε^*` of modules is exact and detects zero objects
  (Stacks 08H8), so it preserves and reflects monomorphisms, and such a pullback reflects
  flatness through the tensor identity of Stacks 03EL.
* On `S_τ` for `τ ∈ {smooth, syntomic, fppf}` both halves run through the equational criterion
  of Stacks 08FC: restriction from the big site keeps local factorizations of relations, and
  conversely such factorizations over flat covers descend to the stalks of `𝓕` along faithfully
  flat local homomorphisms.

## Main results

* `AlgebraicGeometry.SmallZariski.isFlat_iff_associatedModuleEquivalence`: Descent, Lemma 05VG
  for 03ER (3) at the equivalence `QCoh(𝒪_S) ≌ QCoh(S_Zar, 𝒪)`.
* `AlgebraicGeometry.SmallEtale.isFlat_iff_associatedModuleEquivalence`: the same at
  `QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)`.
* `AlgebraicGeometry.SmallFlatSite.isFlat_iff_associatedModuleEquivalence`: the same at
  `QCoh(𝒪_S) ≌ QCoh(S_τ, 𝒪)` for every `τ ∈ {smooth, syntomic, fppf}`.

## Implementation notes

The functor of each equivalence sends `𝓕` to an object of the full subcategory of
quasi-coherent `𝒪`-modules whose underlying module is `𝓕^a` itself, so each statement is read
off the corresponding statement for the associated-module functor on all `𝒪_S`-modules:
`AlgebraicGeometry.SmallZariski.isFlat_iff_associatedModule`,
`AlgebraicGeometry.SmallEtale.isFlat_associatedModule_iff` and
`AlgebraicGeometry.SmallFlatSite.isFlat_associatedModule_iff`.  The first two hold for every
`𝒪_S`-module; quasi-coherence, the source's hypothesis, enters only through the domain of the
equivalence.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3), at the equivalence
`QCoh(𝒪_S) ≌ QCoh(S_Zar, 𝒪)` of Descent, Proposition 03DX (2).**  A quasi-coherent
`𝒪_S`-module `𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on `S_Zar`.

There is no hypothesis beyond `𝓕`: the comparison `S_Zar → (S, 𝒪_S)` is proved to be an
equivalence of ringed topoi
(`AlgebraicGeometry.SmallZariski.isEquivalence_pushforward_toOpensRingedToposHom`,
`AlgebraicGeometry.SmallZariski.isIso_fSharp_toOpensRingedToposHom`), and
`AlgebraicGeometry.SmallZariski.isFlat_iff_associatedModule` transfers flatness across it. -/
@[stacks 05VG "flat (03ER (3)), small site S_Zar, at the equivalence QCoh(𝒪_S) ≌ QCoh(S_Zar, 𝒪) \
of 03DX (2) itself, with no hypothesis"]
theorem isFlat_iff_associatedModuleEquivalence
    (𝓕 : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕.obj ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := (smallZariskiRingedSite B S hS).O)
        ((associatedModuleEquivalence B S hS).functor.obj 𝓕).obj :=
  isFlat_iff_associatedModule B S hS 𝓕.obj

end SmallZariski

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3), at the equivalence
`QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪)` of Descent, Proposition 03DX (2).**  A quasi-coherent
`𝒪_S`-module `𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on `S_étale`.

There is no hypothesis beyond `𝓕`, and no equivalence of ringed topoi is involved: the
comparison `S_étale → S_Zar` is not one.  The proof is
`AlgebraicGeometry.SmallEtale.isFlat_associatedModule_iff` — Stacks 05VD for the `only if` half,
and for the `if` half the reflection of flatness by a pullback of modules which preserves and
reflects monomorphisms, both of which hold at `ε` by Stacks 08H8. -/
@[stacks 05VG "flat (03ER (3)), small site S_étale, at the equivalence \
QCoh(𝒪_S) ≌ QCoh(S_étale, 𝒪) of 03DX (2) itself, with no hypothesis"]
theorem isFlat_iff_associatedModuleEquivalence
    (𝓕 : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕.obj ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := (smallEtaleRingedSite B S hS).O)
        ((associatedModuleEquivalence' B S hS).functor.obj 𝓕).obj :=
  isFlat_associatedModule_iff B S hS 𝓕.obj

end SmallEtale

namespace SmallFlatSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (κ : FlatSiteKind)

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03ER (3), at the equivalence
`QCoh(𝒪_S) ≌ QCoh(S_τ, 𝒪)` of the small site `S_τ`, for every `τ ∈ {smooth, syntomic, fppf}`.**
A quasi-coherent `𝒪_S`-module `𝓕` is flat if and only if `𝓕^a` is flat as an `𝒪`-module on
`S_τ`.

There is no hypothesis beyond `𝓕`, and no equivalence of ringed topoi is involved.  The proof is
`AlgebraicGeometry.SmallFlatSite.isFlat_associatedModule_iff`, both of whose halves are the
equational criterion of Stacks 08FC. -/
@[stacks 05VG "flat (03ER (3)), small site S_τ for every τ ∈ {smooth, syntomic, fppf}, at the \
equivalence QCoh(𝒪_S) ≌ QCoh(S_τ, 𝒪) of 03DX itself, with no hypothesis"]
theorem isFlat_iff_associatedModuleEquivalence
    (𝓕 : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) :
    Stacks.SheafOfModules.IsFlat.{u, u, u, u} (O := S.zariskiRingedSite.O) 𝓕.obj ↔
      Stacks.SheafOfModules.IsFlat.{u, u + 1, u, u} (O := (ringedSite B S hS κ).O)
        ((associatedModuleEquivalence B S hS κ).functor.obj 𝓕).obj :=
  have : 𝓕.obj.IsQuasicoherent := 𝓕.property
  isFlat_associatedModule_iff B S hS κ 𝓕.obj

end SmallFlatSite

end AlgebraicGeometry

end
