module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFiniteLocallyFreeComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EssSurjectivityFpqcRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalTypesComparison
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjRestrictRestrFunBridge
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ObjectFunctoriality
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.Fpqc
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0GNE (3), the parenthetical: finite local freeness agrees at the five big sites

Descent, Lemma 0GNE (3) states that the internal hom of two quasi-coherent `𝒪`-modules on
`(Sch/S)_fppf`, the second of them finite locally free, is computed by the same sheaf whichever
of the five topologies is used; and it remarks, parenthetically, that *being* finite locally
free does not depend on the topology either — a quasi-coherent `𝒪`-module on `(Sch/S)_fppf` is
finite locally free for the fppf topology if and only if it is so for the étale topology, if and
only if for the Zariski topology.  **This file proves that parenthetical, at all five
topologies.**

The parenthetical is Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2), read across
a change of topology.  Its two directions are of entirely different natures, and only one
carries mathematics.

**The direction with no mathematics in it** is from the *coarser* topology to the finer one, and
it is proved here for an arbitrary pair of topologies `K ≤ J` on an arbitrary category, with no
quasi-coherence hypothesis at all:
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_comparisonPushforward`.  A covering family
for `K` is one for `J`, and finite freeness of a restriction transfers because
`Stacks.SheafOfModules.comparisonPushforward` — "read a `J`-sheaf of modules for `K`", which
changes neither the underlying presheaf of modules nor the morphisms — is **fully faithful**, so
it *reflects* a colimiting cofan of copies of the structure sheaf
(`Stacks.Sheaves.GlobalTypeComparison.isColimitCofanOfMap`, which needs no colimit preservation
whatsoever).  Nothing else is used; in particular no sheafification and no descent.

**The direction that carries the mathematics** is from fppf to the coarser topologies: an fppf
covering family trivializing `𝓕` is *not* an étale or Zariski covering family, so the covering
has to be descended, and the descent is Stacks 05B2.  The route is the source's own: write
`𝓕 = 𝓗ᵃ` and compare both sides with "`𝓗` finite locally free on `S`".

## The five-topology comparison, as an equivalence

The core statement is `BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_iff`:
for a quasi-coherent `𝒪_S`-module `𝓗` and any `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`,

    `𝓗` is finite locally free on `S_Zar`  ↔  `𝓗ᵃ` is finite locally free on `(Sch/S)_τ`.

Its `only if` half is
`BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_of_isFiniteLocallyFreeOnSite`,
valid at every `τ`.  The `if` half is proved here, in two steps:

* at `τ = fppf`, `AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_of_associatedModule`;
* at the four coarser `τ`, by carrying the verdict up to fppf with the monotonicity above,
  through `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso` — the key to
  Stacks 0GNE, which identifies `𝓗ᵃ` on `(Sch/S)_τ` with `𝓗ᵃ` on `(Sch/S)_fppf` read for the
  coarser topology.

So the monotonicity is what confines the hard work to a single topology, and the only place
where the `τ`-analogue of Stacks 03DV functorial in an arbitrary object is needed is `τ = fppf`,
where `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` supplies it.

## The descent step at `τ = fppf`, in detail

`𝓗ᵃ` finite locally free on `(Sch/S)_fppf` gives, by Stacks 03DN
(`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree`), a family
`X : I → (Sch/S)_fppf` covering the final object on whose members the restriction of `𝓗ᵃ` is
finite free.  The members of such a family are arbitrary schemes over `S`, so their structure
morphisms need not even be flat; `AlgebraicGeometry.BigFppfOver.exists_coversTop_fpqc_refinement`
refines it, unconditionally, to a family `Y` whose structure morphisms *are* an fpqc covering
family of `S`, each member mapping into a member of `X`.  Finite freeness survives that
refinement because it is inherited along any arrow of the site
(`Stacks.SheafOfModules.exists_isColimitCofan_over_of_le`).  On each `Y j`, with `X_j` its
scheme and `f_j : X_j ⟶ S` its structure morphism,

* `AlgebraicGeometry.BigFppfOver.isFiniteFree_objRestrict` moves finite freeness from the
  localization `(Sch/S)_fppf / Y j` to the big fppf site of `X_j`, along the reindexing of
  Stacks 06WI, which is an equivalence;
* `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso` — Stacks 03DV functorial in
  the object — rewrites the result as `(f_j^*𝓗)ᵃ`;
* `AlgebraicGeometry.BigFppfOver.isFiniteFree_iff_baseAssociatedModule`, 05VG for Modules on
  Sites 03DE (2) at the big site, is an *iff*, so it reflects finite freeness: `f_j^*𝓗` is
  finite free on `X_j`.

A finite free module is finite locally free in the local-generators sense of Stacks 01C6 (2)
(`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteFree`), which is the form
Stacks 05B2 consumes, and 05B2 descends the conclusion to `S`; Stacks 03DN's comparison of the
two forms, `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree`, returns it
to the covering-family form of 03DL (2).

## Main results

* `Stacks.SheafOfModules.isFiniteFree_of_comparisonPushforward` and
  `…isFiniteLocallyFreeOnSite_of_comparisonPushforward`: finite freeness and finite local
  freeness for a coarser topology imply the same for a finer one, for an arbitrary pair of
  topologies on one category and with no further hypothesis.
* `AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteFree`: a finite free sheaf of
  modules on a site is finite locally free in the sense of Stacks 01C6 (2).
* `AlgebraicGeometry.BigFppfOver.isFiniteFree_objRestrict` and
  `…isFiniteFree_pullback_of_isFiniteFree_over`: the two transports of finite freeness that the
  descent step runs on.
* `AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_of_associatedModule`: **the descent
  direction of 05VG for 03DL (2) at the big fppf site** — if `𝓗ᵃ` is finite locally free on
  `(Sch/S)_fppf` then `𝓗` is finite locally free on `S`.
* `AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_iff`:
  **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2), at the big site `(Sch/S)_τ`
  for every `τ`, as an equivalence.**
* `AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_restrictTopology_iff`:
  **Descent, Lemma 0GNE (3), the parenthetical** — a quasi-coherent `𝒪`-module on
  `(Sch/S)_fppf` is finite locally free there if and only if its reading on `(Sch/S)_τ` is
  finite locally free, for every one of the five topologies, in particular for the étale and
  the Zariski topology that the source names.

## Implementation notes

The argument rests on three ingredients:

1. the `τ`-analogue of Stacks 03DV functorial in an arbitrary object, needed at `τ = fppf`
   only — the monotonicity of item 3 does the rest;
2. the stability of finite freeness under restriction along an arrow `Z ⟶ Y` of the site,
   `Stacks.SheafOfModules.exists_isColimitCofan_over_of_le`, not only along the iterated slice;
3. the monotonicity along `Stacks.SheafOfModules.comparisonPushforward`, which is *not* the
   transfer of finite freeness along the left adjoint `Stacks.SheafOfModules.comparisonPullback`:
   that would prove the statement about a sheafified module, whereas what is wanted is about the
   module itself, and the full faithfulness of `comparisonPushforward` gives it directly, with no
   adjunction and no counit.

Only the equality of the two slice readings of one module is used in item 3, and that holds by
`rfl`: `CategoryTheory.Sheaf.over` and `SheafOfModules.overFunctor` restrict the underlying
presheaves and leave only the sheaf condition — a proposition — to differ.

The index universe of the covering family of Stacks 03DN at the big site is `u + 1`, the
universe of the site's objects, and so is the index universe of the fpqc covering family of `S`
produced from it, which is why Stacks 05B2 is applied at an index universe above the schemes';
`AlgebraicGeometry.isFiniteLocallyFree_of_pullback_fpqcCover` is stated at an arbitrary index
universe and so admits it.

## References

* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w u₁

namespace Stacks.SheafOfModules

/-- **Finite local freeness depends only on the isomorphism class.**  The same covering family
serves, the restriction of an isomorphism to each member being an isomorphism. -/
public theorem isFiniteLocallyFreeOnSite_of_iso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {M N : _root_.SheafOfModules.{w} R} (e : M ≅ N)
    (h : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite N) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite M := by
  intro U
  obtain ⟨I, V, f, hcov, hfree⟩ := h U
  exact ⟨I, V, f, hcov, fun i => Stacks.SheafOfModules.isFiniteFree_of_iso
    ((_root_.SheafOfModules.overFunctor R (V i)).mapIso e).symm (hfree i)⟩

section OfLe

variable {C : Type u} [Category.{v} C] {J K : GrothendieckTopology C} (h : K ≤ J)
  (R : Sheaf J RingCat.{w})

include h in
/-- Passing to the slice topologies preserves an inequality of Grothendieck topologies: the
covering sieves of `J.over U` are read off those of `J` by `Sieve.overEquiv`. -/
public theorem over_le_over_of_le (U : C) : K.over U ≤ J.over U := by
  intro Y T hT
  rw [GrothendieckTopology.mem_over_iff] at hT ⊢
  exact h _ hT

/-- Reading the structure sheaf of the finer topology for a coarser one returns the structure
sheaf of the coarser one: neither the underlying presheaf of modules nor the coefficient
presheaf of rings changes, and the two sheaf conditions are propositions. -/
public noncomputable def comparisonPushforwardUnitIso :
    (comparisonPushforward.{u, v, w, w} h R).obj (_root_.SheafOfModules.unit R) ≅
      _root_.SheafOfModules.unit (ringOfLe h R) :=
  Iso.refl _

/-- **Finite freeness is reflected by reading a sheaf of modules for a coarser topology.**  If
the reading of `M` for `K` is a coproduct of finitely many copies of the structure sheaf, then so
is `M` itself.

No colimit preservation is used: `Stacks.SheafOfModules.comparisonPushforward` is fully faithful,
so `Stacks.Sheaves.GlobalTypeComparison.isColimitCofanOfMap` lifts the cofan's legs to `M` and
reflects the colimit. -/
public theorem isFiniteFree_of_comparisonPushforward (M : _root_.SheafOfModules.{w} R)
    (hM : _root_.SheafOfModules.IsFiniteFree (ringOfLe h R)
      ((comparisonPushforward.{u, v, w, w} h R).obj M)) :
    _root_.SheafOfModules.IsFiniteFree R M := by
  have hff := comparisonPushforwardFullyFaithful.{u, v, w, w} h R
  have := hff.full
  have := hff.faithful
  rw [_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit] at hM ⊢
  obtain ⟨n, κ, ⟨hc⟩⟩ := hM
  exact ⟨n, _, ⟨Stacks.Sheaves.GlobalTypeComparison.isColimitCofanOfMap
    (comparisonPushforward.{u, v, w, w} h R) (comparisonPushforwardUnitIso h R) κ hc⟩⟩

/-- **Finite local freeness for a coarser topology implies finite local freeness for a finer
one.**  For `K ≤ J` two topologies on one category and `M` a sheaf of modules for `J`: if the
reading of `M` for `K` is finite locally free on `(C, K)`, then `M` is finite locally free on
`(C, J)`.

Both ingredients are free of hypotheses.  A `K`-covering family of an object is a `J`-covering
family of it, since `K ≤ J`; and the restriction of `M` to a member is finite free as soon as the
restriction of its reading is, by
`Stacks.SheafOfModules.isFiniteFree_of_comparisonPushforward` at the slice topologies
(`Stacks.SheafOfModules.over_le_over_of_le`).  The two readings of the restriction are literally
the same sheaf of modules: restriction to a slice site changes only the underlying presheaf's
index category, not the sheaf condition being asserted. -/
public theorem isFiniteLocallyFreeOnSite_of_comparisonPushforward
    (M : _root_.SheafOfModules.{w} R)
    (hM : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite
      ((comparisonPushforward.{u, v, w, w} h R).obj M)) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite M := by
  intro U
  obtain ⟨I, V, f, hcov, hfree⟩ := hM U
  exact ⟨I, V, f, h _ hcov, fun i => isFiniteFree_of_comparisonPushforward
    (over_le_over_of_le h (V i)) (R.over (V i)) (M.over (V i)) (hfree i)⟩

end OfLe

end Stacks.SheafOfModules

namespace AlgebraicGeometry.SheafOfModules

/-- **A finite free sheaf of modules is finite locally free in the local-generators form of
Stacks 01C6 (2).**  A colimiting cofan of `n` copies of the structure sheaf identifies the module
with the free module on `ULift (Fin n)`, which is finite locally free of rank `n` by
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free`.

This is the form in which Stacks 05B2 receives its hypothesis, whereas 05VG for Modules on Sites
03DE (2) delivers the global finite freeness `SheafOfModules.IsFiniteFree`; the two forms are not
comparable in general — a finite locally free module need not be finite free — and only this
implication is wanted. -/
public theorem isFiniteLocallyFree_of_isFiniteFree {C : Type u₁} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}] [HasBinaryProducts C]
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : _root_.SheafOfModules.{u} R)
    (h : _root_.SheafOfModules.IsFiniteFree R F) :
    IsFiniteLocallyFree.{u, v, u₁} F := by
  rw [_root_.SheafOfModules.isFiniteFree_iff_exists_isColimit] at h
  obtain ⟨n, ι, ⟨hc⟩⟩ := h
  have e : F ≅ _root_.SheafOfModules.free (R := R) (ULift.{u} (Fin n)) :=
    hc.coconePointUniqueUpToIso (Stacks.Sheaves.QcohTypeComparison.isColimitFreeCofanFin n)
  have : IsFiniteLocallyFreeOfRank.{u, v, u₁} F n :=
    IsFiniteLocallyFreeOfRank.of_iso e.symm (isFiniteLocallyFreeOfRank_free.{u, v, u₁} n)
  exact IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F n

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The reindexing of Stacks 06WI carries the structure sheaf of the localization of
`(Sch/S)_fppf` at `T` to the structure sheaf of the big fppf site of the scheme of `T`: both
send an object to the global functions of its underlying scheme, which is
`AlgebraicGeometry.BigFppfOver.reindexRing_objEquiv`. -/
public noncomputable def objRestrictFunctorUnitIso (T : BigFppfOver B S hS) :
    (objRestrictFunctor B S hS T).obj
        (SheafOfModules.unit ((structureSheaf B S hS).over T)) ≅
      SheafOfModules.unit
        (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T)) :=
  Iso.refl _

/-- **Finite freeness of the restriction of `𝒢` to the localization at `T` is finite freeness of
its restriction to the big fppf site of the scheme of `T`.**  The two are the same ringed site in
two spellings, and the reindexing of Stacks 06WI between them is an equivalence
(`AlgebraicGeometry.BigFppfOver.objRestrictEquivalence`), so
`Stacks.SheafOfModules.isColimitCofanTransport` carries a colimiting cofan of copies of the
structure sheaf across it. -/
public theorem isFiniteFree_objRestrict (T : BigFppfOver B S hS)
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (h : SheafOfModules.IsFiniteFree ((structureSheaf B S hS).over T) (G.over T)) :
    SheafOfModules.IsFiniteFree
      (structureSheaf B (objScheme B S hS T) (contains_objScheme B S hS T))
      ((objRestrict B S hS T).obj G) := by
  rw [SheafOfModules.isFiniteFree_iff_exists_isColimit] at h ⊢
  obtain ⟨n, ι, ⟨hc⟩⟩ := h
  exact ⟨n, _, ⟨Stacks.SheafOfModules.isColimitCofanTransport
    (objRestrictEquivalence B S hS T) (objRestrictFunctorUnitIso B S hS T) (Iso.refl _) ι hc⟩⟩

/-- **The pullback of `𝓗` along the structure morphism of `T` is finite free as soon as the
restriction of `𝓗ᵃ` to the localization at `T` is.**

Three steps: the spelling change
`AlgebraicGeometry.BigFppfOver.isFiniteFree_objRestrict`; then Stacks 03DV functorial in the
object, `AlgebraicGeometry.BigFppfOver.associatedModuleObjRestrictNatIso`, which rewrites
`(𝓗ᵃ)|_{(Sch/X)_fppf}` as `(f^*𝓗)ᵃ`; then
`AlgebraicGeometry.BigFppfOver.isFiniteFree_iff_baseAssociatedModule`, which is 05VG for Modules
on Sites 03DE (2) at the big site and is an *iff*, so it reflects finite freeness down to `X`.
The pullback is quasi-coherent by Stacks 01BG. -/
public theorem isFiniteFree_pullback_of_isFiniteFree_over (T : BigFppfOver B S hS)
    (𝓗 : S.Modules) [h𝓗 : 𝓗.IsQuasicoherent]
    (h : SheafOfModules.IsFiniteFree ((structureSheaf B S hS).over T)
      (((associatedModule B S hS).obj 𝓗).over T)) :
    SheafOfModules.IsFiniteFree (objScheme B S hS T).ringCatSheaf
      ((Scheme.Modules.pullback (objHom B S hS T)).obj 𝓗) :=
  (isFiniteFree_iff_baseAssociatedModule B (objScheme B S hS T)
      (contains_objScheme B S hS T) .fppf
    ⟨(Scheme.Modules.pullback (objHom B S hS T)).obj 𝓗,
      Stacks.Modules.isQuasicoherent_pullback _ 𝓗 h𝓗⟩).2
    (Stacks.SheafOfModules.isFiniteFree_of_iso
      ((associatedModuleObjRestrictNatIso B S hS T).app 𝓗).symm
      (isFiniteFree_objRestrict B S hS T ((associatedModule B S hS).obj 𝓗) h))

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2): the descent direction, at
the big fppf site.**  If the associated module `𝓗ᵃ` of a quasi-coherent `𝒪_S`-module is finite
locally free as an `𝒪`-module on `(Sch/S)_fppf`, then `𝓗` is finite locally free on the small
Zariski site of `S`.

This is the half of the clause that carries the mathematics, and it is the source's own argument.
Stacks 03DN produces a family covering the final object of `(Sch/S)_fppf` trivializing `𝓗ᵃ`; its
members are arbitrary schemes over `S`, so
`AlgebraicGeometry.BigFppfOver.exists_coversTop_fpqc_refinement` refines it to one whose
structure morphisms are an fpqc covering family of `S`, and finite freeness follows the
refinement because it is inherited along every arrow of the site
(`Stacks.SheafOfModules.exists_isColimitCofan_over_of_le`).  On each member,
`AlgebraicGeometry.BigFppfOver.isFiniteFree_pullback_of_isFiniteFree_over` turns the verdict into
finite freeness of the pullback of `𝓗`, hence into finite local freeness in the local-generators
form that Stacks 05B2 consumes; 05B2 descends it to `S`, and Stacks 03DN's comparison of the two
forms returns it to the covering-family form of Stacks 03DL (2). -/
public theorem isFiniteLocallyFreeOnSite_of_associatedModule (𝓗 : S.Modules)
    [h𝓗 : 𝓗.IsQuasicoherent]
    (h : SheafOfModules.IsFiniteLocallyFreeOnSite ((associatedModule B S hS).obj 𝓗)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (R := S.ringCatSheaf) 𝓗 := by
  classical
  obtain ⟨I, X, hX, hfree⟩ :=
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteFree
      (baseRingedSite B S hS .fppf) ((associatedModule B S hS).obj 𝓗)).1 h
  obtain ⟨I', Y, hY, hfpqc, hre⟩ := exists_coversTop_fpqc_refinement B S hS X hX
  let 𝒰 : S.Cover.{u + 1} Scheme.fpqcPrecoverage := ⟨objHypercover B S hS Y, hfpqc⟩
  have key : ∀ j, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (𝒰.f j)).obj 𝓗) := by
    intro j
    obtain ⟨i, ⟨g⟩⟩ := hre j
    exact AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteFree _
      (isFiniteFree_pullback_of_isFiniteFree_over B S hS (Y j) 𝓗
        ((SheafOfModules.isFiniteFree_iff_exists_isColimit _ _).2
          (Stacks.SheafOfModules.exists_isColimitCofan_over_of_le
            ((associatedModule B S hS).obj 𝓗) g (hfree i))))
  exact Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree 𝓗
    (isFiniteLocallyFree_of_pullback_fpqcCover 𝓗 𝒰 key)

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (2), on the big site, as an
equivalence.**  A quasi-coherent `𝒪_S`-module `𝓗` is finite locally free on the small Zariski
site of `S` if and only if `𝓗ᵃ` is finite locally free as an `𝒪`-module on `(Sch/S)_τ`, for
every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.

The `only if` half is
`BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_of_isFiniteLocallyFreeOnSite`,
valid at every `τ`.  The `if` half is proved at `τ = fppf` by
`AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_of_associatedModule`, and carried to the
four coarser topologies by the monotonicity
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_comparisonPushforward` through the key to
Stacks 0GNE, `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso`, which exhibits
`𝓗ᵃ` on `(Sch/S)_τ` as `𝓗ᵃ` on `(Sch/S)_fppf` read for the coarser topology.

This is clause 03DL (2) of 05VG at the **big** site `(Sch/S)_τ`, at every `τ`; the small sites
`S_τ` for `τ ∈ {Zariski, étale}`, which Stacks 03DU (4) also treats, are not covered. -/
@[stacks 05VG "finite locally free (03DL (2)), big site (Sch/S)_τ at every τ, at the \
comparison functor of 03DX itself"]
public theorem isFiniteLocallyFreeOnSite_baseAssociatedModule_iff (τ : SiteKind) (𝓗 : S.Modules)
    [h𝓗 : 𝓗.IsQuasicoherent] :
    SheafOfModules.IsFiniteLocallyFreeOnSite (R := S.ringCatSheaf) 𝓗 ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite ((baseAssociatedModule B S hS τ).obj 𝓗) := by
  refine ⟨isFiniteLocallyFreeOnSite_baseAssociatedModule_of_isFiniteLocallyFreeOnSite
    B S hS τ 𝓗, fun h => ?_⟩
  exact isFiniteLocallyFreeOnSite_of_associatedModule B S hS 𝓗
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_comparisonPushforward
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS)
      ((associatedModule B S hS).obj 𝓗)
      (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_iso
        (restrictTopologyAssociatedModuleIso B S hS τ 𝓗) h))

/-- **Descent, Lemma 0GNE (3), the parenthetical.**  A quasi-coherent `𝒪`-module `𝓕` on the big
fppf site of `S` is finite locally free there if and only if its reading as an `𝒪`-module on
`(Sch/S)_τ` is finite locally free, for every one of the five topologies — in particular for the
étale and the Zariski topology, which are the two the source names alongside fppf.

The source's proof is run unchanged: `𝓕 = 𝓗ᵃ` by the essential surjectivity half of Descent,
Proposition 03DX (1) at `τ = fppf`
(`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_isQuasicoherentOnSite`), and
both sides are then compared with "`𝓗` is finite locally free on `S`" by
`AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_baseAssociatedModule_iff`, the reading
on `(Sch/S)_τ` of `𝓗ᵃ` being `𝓗ᵃ` computed on `(Sch/S)_τ` by
`AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso`.

The `if` half needs no quasi-coherence and no reduction at all: it is
`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_comparisonPushforward`, valid for an
arbitrary module and an arbitrary pair of topologies.  Quasi-coherence is used only for the
`only if` half, and it is the hypothesis the source's clause carries. -/
@[stacks 0GNE "part (3), the parenthetical: finite local freeness agrees at τ = fppf, étale \
and Zariski"]
public theorem isFiniteLocallyFreeOnSite_restrictTopology_iff (τ : SiteKind)
    (𝓕 : SheafOfModules.{u} (structureSheaf B S hS))
    (h𝓕 : SheafOfModules.IsQuasicoherentOnSite.{u + 1, u, u, u} 𝓕) :
    SheafOfModules.IsFiniteLocallyFreeOnSite 𝓕 ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite ((restrictTopology B S hS τ).obj 𝓕) := by
  obtain ⟨⟨𝓗, h𝓗⟩, ⟨e⟩⟩ :=
    essImage_associatedModuleQcoh_of_isQuasicoherentOnSite B S hS 𝓕 h𝓕
  have : 𝓗.IsQuasicoherent := h𝓗
  refine ⟨fun hF => ?_, fun hF =>
    Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_comparisonPushforward
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS) 𝓕 hF⟩
  exact Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_iso
    ((restrictTopology B S hS τ).mapIso e.symm ≪≫
      restrictTopologyAssociatedModuleIso B S hS τ 𝓗)
    ((isFiniteLocallyFreeOnSite_baseAssociatedModule_iff B S hS τ 𝓗).1
      ((isFiniteLocallyFreeOnSite_baseAssociatedModule_iff B S hS .fppf 𝓗).2
        (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_iso e hF)))

end AlgebraicGeometry.BigFppfOver

end
