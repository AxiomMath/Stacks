module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackCyclesInput
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionAcyclicityInput
public import StacksFrontier.Homology.CyclesShortComplex

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

/-!
# Degreewise pullback carries an acyclic K-flat complex with flat terms to an acyclic complex

Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of ringed topoi and let `K` be a complex of
`O`-modules which is K-flat, has flat terms, and is acyclic.  Then `f^*K` is acyclic.

This is the statement that both Tag 07A6 and Tag 06YY were waiting on at the topos level.  The
ringed-*space* analogue is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.acyclic_pullback_of_kFlat_of_acyclic`,
proved by testing acyclicity at the stalks; a topos has no
points, so that route is unavailable here and the source's splicing argument is used instead.

## Main results

* `Stacks.Sheaves.RingedToposDerivedPullback.acyclic_pullbackComplex_of_isFlat_cycles`: degreewise
  pullback carries an acyclic complex **with flat cycles** to an acyclic complex.  This is the
  whole of the mathematics, and it needs Stacks 0G6R and nothing else — neither K-flatness nor
  flatness of the terms appears.
* `Stacks.Sheaves.RingedToposDerivedPullback.acyclic_pullbackComplex_of_kFlat_of_acyclic`: the same
  for an acyclic K-flat complex with flat terms, the cycles hypothesis being discharged by
  Tag 0G7C (`Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`).
* `pullbackInvertsQuasiIso_isKFlat_of_pullbackPreservesShortExact`: the exactness half of
  Tag 07A6's resolving datum, in the spelling
  `f.u.IsMorphismOfSites Y.J X.J →
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso f IsKFlat`
  that `derivedPullbackPushforwardAdjunctionOfKFlat`,
  `pullbackOnHomotopy_hasLeftDerivedFunctor_of_kFlat` and Tag 06YY's parameter `hinv` all
  consume.

## Implementation notes

*The argument.*  An acyclic complex splices out of its cycles sequences
`0 ⟶ Z^n ⟶ K^n ⟶ Z^{n+1} ⟶ 0`, which are short exact exactly because `K` is acyclic
(`HomologicalComplex.cyclesShortComplex_shortExact`).  Their third terms are the cycles, which
are flat, so Stacks 0G6R keeps each of them short exact after pulling back.  A complex whose
cycles sequences stay short exact under a functor has acyclic image under that functor
(`CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact`), which is the conclusion.
None of this needs `f^*` to be exact, and none of it needs the pulled-back complex to be
K-flat.

*Why Stacks 0G6R is the only input, and why Stacks 05VD is not needed.*  The flatness that
0G6R asks of the third term of each sequence is flatness of `K.cycles (n + 1)`, which Tag 0G7C
supplies **unconditionally** (`Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`).
So no module is ever required to have flat pullback, and `PullbackPreservesIsFlat`
(Stacks 05VD) — which `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex` and all
of its corollaries carry — does not occur in this file.  This is the opposite of the situation for
the *K-flatness* of `f^*K`: there
`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_acyclic` avoids 0G6R and
needs 05VD, because its route is through the canonical truncations, where no kernel sequence
arises.  The two halves of Tag 0G7E's conclusion, on an acyclic complex, therefore need one Stacks
input each, and they are different ones.

*Why the truncation route was not taken.*
`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex_of_isFlat_cycles`
reads the acyclic case through `CochainComplex.truncLE`, so that route was weighed here too and
**not** built: `K` is the sequential colimit of its canonical truncations, `f^*` preserves that
colimit degreewise, and homology commutes with filtered colimits, so it would suffice that
`f^*(τ_{≤n}K)` be acyclic for each `n`.  But `τ_{≤n}K` is a *bounded above* acyclic complex with
flat terms and flat cycles, and the only argument for acyclicity of its pullback is again the
splicing of its cycles sequences — boundedness buys nothing, because the splice is degreewise
and has no induction in it.  So that route needs 0G6R as well, and additionally the colimit and
truncation bookkeeping, on top of the splice below.  That is a comparison of the two routes'
inputs, not a compiled comparison; only the splice was built.

*Tagging.*  Nothing in this file is tagged.  It is infrastructure feeding Tags 07A6 and 06YY,
every declaration carries `PullbackPreservesShortExact` — a `Prop` hypothesis that no
declaration in either library concludes — and none of the six clauses of the statement of
Tag 06YY is the assertion proved here.

*The tensor instances are not taken as binders.*
`Stacks.Sheaves.DerivedPullback.KFlatPullback.CyclesIsFlat` and
`Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat` carry
`[(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]`,
`[∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]` and the `HasMapBifunctor`
family as explicit instance binders.  However, at `RingedTopos.{u, u, u}` all three
*synthesize* — `Stacks.SheafOfModules.Tensor.sheafTensor_additive`,
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive` and
`Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor` are instances — so this file states its
results without them and the call to `cyclesIsFlat` fills them by search.  The same is true of the
Stacks 06YY development, which states `CochainComplex.KFlatBifunctor.KFlat` with no
such binder.  (At a ringed *space* they have to be seated by hand, as the Stacks 079W
development does, because there the site's object and morphism universes
coincide and the general instances present search with a stuck `max ?u ?v =?= u`.)

*Universes.*  `RingedTopos.{u, u, u}`, inherited from
`Stacks.Sheaves.DerivedPullback.KFlatPullback` and
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction`, which record the three independent
forcings of that narrowing; nothing is decided here.

## References

* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 0G7C](https://stacks.math.columbia.edu/tag/0G7C)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Sheaves.RingedToposDerivedPullback

attribute [local instance] HasDerivedCategory.standard

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Degreewise pullback carries an acyclic complex with flat cycles to an acyclic complex.**

The cycles sequences `0 ⟶ Z^n ⟶ K^n ⟶ Z^{n+1} ⟶ 0` of an acyclic complex are short exact, and
their third terms are flat by hypothesis, so Stacks 0G6R keeps each of them short exact after
pulling back; a complex whose cycles sequences stay short exact has acyclic image.

Stacks 05VD does not appear: the only flatness the argument consumes is the flatness of the
cycles, which is a hypothesis here and is discharged by Tag 0G7C in
`acyclic_pullbackComplex_of_kFlat_of_acyclic` below. -/
theorem acyclic_pullbackComplex_of_isFlat_cycles
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hex : Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesShortExact f)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hKac : K.Acyclic)
    (hcyc : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (K.cycles n)) :
    ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K).Acyclic :=
  CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact f.pullbackTopos K
    fun _ j hij ↦ hex hmos _
      (HomologicalComplex.cyclesShortComplex_shortExact K hij (hKac j)) (hcyc j)

section KFlat

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Degreewise pullback carries an acyclic K-flat complex with flat terms to an acyclic
complex.**  This is the statement the source's proof of Tag 06YY obtains from Tags 0G7C and
0G6R, and the one `derivedPullbackPushforwardAdjunctionOfAcyclic` consumes.

The three hypotheses on `K` enter only through Tag 0G7C
(`Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`): an acyclic K-flat complex with flat
terms has flat cycles, and flat cycles are all that `acyclic_pullbackComplex_of_isFlat_cycles`
needs. -/
theorem acyclic_pullbackComplex_of_kFlat_of_acyclic
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hex : Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesShortExact f)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hKac : K.Acyclic) :
    ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K).Acyclic :=
  acyclic_pullbackComplex_of_isFlat_cycles f hmos hex K hKac
    (Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat Y K hKac
      ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K).2 hK) hflat)

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The exactness half of Tag 07A6's resolving datum, from Stacks 0G6R alone.**  Degreewise
pullback carries a quasi-isomorphism between K-flat complexes of `O`-modules with flat terms to
an isomorphism of `D(O')`.

This is stated in the form `f.u.IsMorphismOfSites Y.J X.J → PullbackInvertsQuasiIso f IsKFlat`
that `pullbackOnHomotopy_hasLeftDerivedFunctor_of_kFlat` and
`DerivedPullbackPushforwardAdjunction.derivedPullbackPushforwardAdjunctionOfKFlat` take, so that
supplying it gives the derived pullback, the adjunction of Tag 07A6 and its two factorization
identities; it is also the parameter `hinv` of `StacksDraft.Ch21.Sec18.Tag06YY`, hence of every
conclusion of Tag 06YY.

The reduction of that input to the acyclicity statement above is
`pullbackInvertsQuasiIso_isKFlat_of_acyclic_pullbackComplex`; everything in it is
formal, by way of the mapping-cone triangle. -/
theorem pullbackInvertsQuasiIso_isKFlat_of_pullbackPreservesShortExact
    (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hex : Stacks.Sheaves.DerivedPullback.KFlatPullback.PullbackPreservesShortExact f) :
    f.u.IsMorphismOfSites Y.J X.J →
      Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso f
        (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)) :=
  fun hmos ↦
    pullbackInvertsQuasiIso_isKFlat_of_acyclic_pullbackComplex f
    fun K hK hflat hKac ↦
      acyclic_pullbackComplex_of_kFlat_of_acyclic f hmos hex K hK hflat hKac

end KFlat

end Stacks.Sheaves.RingedToposDerivedPullback

end

end
