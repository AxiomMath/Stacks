module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitOpenPullback

/-!
# Restriction to an open subscheme is the transition functor of Tag 0EXE

Let `p` be a prime, let `X` be a scheme in characteristic `p` and let `V ⊆ X` be an open. There are
two functors from `colim_F 𝒪_X`-modules to `colim_F 𝒪_V`-modules built in this development, and
until now nothing connected them:

* `AlgebraicGeometry.frobeniusColimitVectorBundlesPullback p V.ι` and its module-level form
  `CategoryTheory.SheafOfModules.pullback (AlgebraicGeometry.frobeniusColimitStructureSheafHom p
  V.ι …)` — extension of scalars along the canonical morphism of Frobenius colimits. This is the
  transition functor of [Stacks, Tag 0EXE], and it is what the square comparison
  `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso`, its pasting law, the cube coherence
  and the free case of full faithfulness all speak;
* `AlgebraicGeometry.frobeniusColimitModuleRestrict` — slice restriction to `Opens(X)/V` followed
  by `AlgebraicGeometry.frobeniusColimitModuleOpenEquiv`. This is what the freeness transport
  `AlgebraicGeometry.exists_cover_free_frobeniusColimitModuleRestrict` delivers.

`AlgebraicGeometry.frobeniusColimitSiteRestrictIsoPullback` identifies the *first* of these with
pushforward along the open-image functor of `V.ι`. This file supplies the remaining step — that
that pushforward is the *second* — and then carries the trivialising cover across, so that a
finite locally free `colim_F 𝒪_X`-module is free over `colim_F 𝒪_{V}` on each member of an open
cover **in the transition-functor spelling**.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitModuleRestrictIsoSiteRestrict`: restriction to the open
  subscheme, in its slice-site presentation, is pushforward along the open-image functor.
* `AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback`: **restriction to an open
  subscheme is the transition functor of [Stacks, Tag 0EXE] along the open immersion**, with both
  sides written as named functors.
* `AlgebraicGeometry.frobeniusColimitPullbackObjFreeOfIso`: a module trivialised over `V` on the
  slice site is carried by the transition functor to a free `colim_F 𝒪_V`-module.

## Main results

* `AlgebraicGeometry.exists_cover_free_frobeniusColimitPullback`: **a finite locally free
  `colim_F 𝒪_X`-module is carried to a free module by the transition functor of each member of
  some open cover of `X`.**

## Implementation notes

Both functors are composites of `CategoryTheory.SheafOfModules.pushforward`, whose
pseudofunctoriality `CategoryTheory.SheafOfModules.pushforwardComp` is an `Iso.refl`, so the
identification carries no mathematical content: `frobeniusColimitModuleRestrict` is
`overFunctor ⋙ sheafOfModulesEquivOver ⋙ restrictScalars`, and `overFunctor` is a pushforward by
definition, `TopologicalSpace.Opens.sheafOfModulesEquivOver` is a
`CategoryTheory.SheafOfModules.pushforwardPushforwardEquivalence`, and restriction of scalars
along a morphism of sheaves of rings on a fixed site is pushforward along the identity functor of
that site. What makes the identification awkward is purely syntactic, and in two ways, each of
which needs its own remedy.

First, the composite site functor
`(TopologicalSpace.Opens.overEquivalence V).symm.functor ⋙ CategoryTheory.Over.forget V` is
definitionally but not syntactically the open-image functor of `V.ι`, and its continuity is
therefore *not* found by instance search; it has to be supplied by hand, from the continuity of
the two factors, exactly as `AlgebraicGeometry.SheafOfModules.overFunctorIsoSiteRestrict` does
for the structure sheaf of a ringed space. Second — and this is the part that no choice of
statement avoids — checking the resulting term against the *declared* type of a `def` exhausts
the whnf budget, because that comparison unfolds the Frobenius colimit on both sides at once.
Supplying the composition as `CategoryTheory.Iso.trans` through `apply`, which unifies at
reducible transparency and postpones the residual constraints, closes it immediately where
`exact` on the same term does not.

Note that the first of the two steps is available at an arbitrary sheaf of rings, and as an
equality rather than an isomorphism: `Stacks.DerivedGlueing.overFunctor_comp_sliceToSubspace`
(`StacksFrontier/Topology/Sheaves/Cohomology/DerivedCategory/SelfExtOnACollectionOfOpens.lean`) says
that slice restriction followed by the passage to the open-subspace model *is* pushforward along
the open-image functor, by `rfl`. What that statement does not cover is the change of the sheaf of
rings along `AlgebraicGeometry.frobeniusColimitRingSheafRestrictIso`, which is the third factor
here.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p) (V : X.Opens)
  (hV : IsInCharacteristic V.toScheme p)

/-- **Restriction of a `colim_F 𝒪_X`-module to the open subscheme `V`, presented through the
slice site, is pushforward along the open-image functor of `V.ι`.**

Both sides are composites of `CategoryTheory.SheafOfModules.pushforward`, so this is
`CategoryTheory.SheafOfModules.pushforwardComp` together with the identification of the two
structure morphisms, for which `CategoryTheory.SheafOfModules.pushforwardCongr` asks only an
equality of morphisms of sheaves of rings. The continuity of the composite site functor is
supplied by hand because the composite is definitionally, not syntactically, the open-image
functor. -/
noncomputable def frobeniusColimitModuleRestrictIsoSiteRestrict :
    frobeniusColimitModuleRestrict X p hX V hV ≅ frobeniusColimitSiteRestrict X p hX V hV := by
  let H : Topology.IsOpenEmbedding (TopCat.Hom.hom V.ι.base) := Scheme.Hom.isOpenEmbedding V.ι
  letI : H.isOpenMap.functor.IsContinuous
      (Opens.grothendieckTopology (V.toScheme : TopCat))
      (Opens.grothendieckTopology (X : TopCat)) := H.functor_isContinuous
  haveI : ((Opens.overEquivalence V).symm.functor).IsContinuous
      (Opens.grothendieckTopology ↥V)
      ((Opens.grothendieckTopology (X : TopCat)).over V) := inferInstance
  haveI : (Over.forget V).IsContinuous
      ((Opens.grothendieckTopology (X : TopCat)).over V)
      (Opens.grothendieckTopology (X : TopCat)) := inferInstance
  haveI : ((Opens.overEquivalence V).symm.functor ⋙ Over.forget V).IsContinuous
      (Opens.grothendieckTopology ↥V)
      (Opens.grothendieckTopology (X : TopCat)) :=
    Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology (X : TopCat)).over V) _
  apply Iso.trans (_root_.SheafOfModules.pushforwardComp _ _)
  exact _root_.SheafOfModules.pushforwardCongr (by ext W x; rfl)

/-- **Restriction to an open subscheme is the transition functor of [Stacks, Tag 0EXE] along the
open immersion.**

This is the identification the trivialising-cover argument for [Stacks, Tag 0EXD] needs: the two
halves of that argument speak different functors —
`AlgebraicGeometry.exists_cover_free_frobeniusColimitModuleRestrict` delivers a trivialisation in
terms of `AlgebraicGeometry.frobeniusColimitModuleRestrict`, while the free case of full
faithfulness, the square comparison and the cube coherence are all stated for the transition
functor — and this says they are the same functor.

It is `AlgebraicGeometry.frobeniusColimitSiteRestrictIsoPullback`, which is the content, composed
with `AlgebraicGeometry.frobeniusColimitModuleRestrictIsoSiteRestrict`, which is bookkeeping. -/
noncomputable def frobeniusColimitModuleRestrictIsoPullback :
    frobeniusColimitModuleRestrict X p hX V hV ≅
      _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p V.ι hV hX) :=
  frobeniusColimitModuleRestrictIsoSiteRestrict X p hX V hV ≪≫
    frobeniusColimitSiteRestrictIsoPullback X p hX V hV

/-- **A module trivialised over `V` on the slice site is carried to a free module by the
transition functor of `V.ι`.**

This is `AlgebraicGeometry.frobeniusColimitModuleRestrictObjFreeOfIso` read through
`AlgebraicGeometry.frobeniusColimitModuleRestrictIsoPullback`, so that the conclusion is about the
transition functor of [Stacks, Tag 0EXE] rather than about the slice-site restriction. -/
noncomputable def frobeniusColimitPullbackObjFreeOfIso
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) (I : Type u)
    (e : M.over V ≅ _root_.SheafOfModules.free I) :
    (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p V.ι hV hX)).obj M ≅
      _root_.SheafOfModules.free (R := frobeniusColimitRingSheaf V.toScheme p hV) I :=
  ((frobeniusColimitModuleRestrictIsoPullback X p hX V hV).app M).symm ≪≫
    frobeniusColimitModuleRestrictObjFreeOfIso X p hX V hV M I e

/-- **A finite locally free `colim_F 𝒪_X`-module is carried to a free module by the transition
functor of each member of an open cover of `X`.**

This is `AlgebraicGeometry.exists_cover_free_frobeniusColimitModuleRestrict` in the spelling the
trivialising-cover argument for [Stacks, Tag 0EXD] consumes: the transition functor of
[Stacks, Tag 0EXE] along the open immersion `(V i).ι`, which is what the square comparison and
the free case of full faithfulness are stated for.

The characteristic of each member is supplied by
`AlgebraicGeometry.isInCharacteristic_toScheme`, so no hypothesis beyond that of `X` is needed. -/
theorem exists_cover_free_frobeniusColimitPullback
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX))
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    ∃ (I : Type u) (W : I → X.Opens) (K : I → Type u), (⨆ i, W i = ⊤) ∧
      (∀ i, Finite (K i)) ∧ ∀ i, Nonempty
        ((_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p (W i).ι
            (isInCharacteristic_toScheme hX (W i)) hX)).obj M ≅
          _root_.SheafOfModules.free (K i)) := by
  obtain ⟨q, hfree, hfin⟩ := h.exists_isFiniteLocallyFreeData
  refine ⟨q.I, q.X, fun i => (q.generators i).I,
    (Opens.coversTop_iff _ q.X).mp q.coversTop, fun i => (hfin.isFiniteType i).finite,
    fun i => ⟨?_⟩⟩
  have : IsIso (q.generators i).π := hfree.isIso i
  exact frobeniusColimitPullbackObjFreeOfIso X p hX (q.X i)
    (isInCharacteristic_toScheme hX (q.X i)) M _ (asIso (q.generators i).π).symm

end AlgebraicGeometry

end
