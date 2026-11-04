module

public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentInternalHomOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentTensorProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# Coherence of the sheaf-hom of modules on an algebraic space

The sheaf-hom `𝓗om_{𝒪_F}(M, N)` of two coherent `𝒪_F`-modules on an algebraic space `F` is
coherent.  This is the sheaf-hom clause of Stacks 07UE, whose tensor-product clause is
`AlgebraicGeometry.Space.isCoherent_tensorModule` of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentTensorProduct`.  Both clauses together, for one
algebraic space and one pair of coherent modules, are
`AlgebraicGeometry.Space.isCoherent_tensorModule_and_smallEtaleInternalHomSmall`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleInternalHomSmall`: **the internal Hom `𝓗om_{𝒪_F}(M, N)` of
  two `𝒪_F`-modules, at the module universe `u` of the schemes.**
* `AlgebraicGeometry.Space.smallEtaleInternalHomSmallIso`: its universe lift is
  `AlgebraicGeometry.Space.smallEtaleInternalHom`, so it is that internal Hom read in a smaller
  universe and not a second construction.

## Main results

* `AlgebraicGeometry.Space.isCoherentOnSite_smallEtaleInternalHom`: the internal Hom of two
  modules coherent on the small étale ringed site of an algebraic space is coherent on that
  site.
* `AlgebraicGeometry.Space.isCoherent_smallEtaleInternalHomSmall`: **the sheaf-hom clause of
  Stacks 07UE** — the internal Hom of two coherent `𝒪_F`-modules is coherent.
* `AlgebraicGeometry.Space.isCoherent_tensorModule_and_smallEtaleInternalHomSmall`:
  **Stacks 07UE**, both clauses at once.

## Implementation notes

**The route.**  Coherence of the internal Hom is `Stacks 01CQ(2)` and holds on an arbitrary
ringed site, by `AlgebraicGeometry.RingedSite.isCoherentOnSite_internalHomSheaf` of
`StacksFrontier.AlgebraicGeometry.Topologies.CoherentInternalHomOnSite`; the statements below are
that theorem read at the small étale ringed site of `F`, together with the descent of the module
universe described next.  The source's own proof goes the other way — through Stacks 07UB to the
case of schemes, Cohomology of Schemes Lemma 30.9.4, which is Stacks 01Y2, proved at
ringed-space generality in `StacksFrontier.AlgebraicGeometry.TensorHomCoherent.Basic`.  That route
would pass through the restriction of a module to an étale chart, which in this development is
restriction to the slice of the small étale site; identifying that slice with the small étale
site of the chart additionally requires matching the two structure sheaves.  Proving the
site-level statement instead avoids the comparison entirely, and it is also what the source
itself proves for a ringed space.

**The module universe.**
`AlgebraicGeometry.Space.smallEtaleInternalHom` of two modules at the module universe `u` of the
schemes lands at `u + 1`: a section over an étale chart `U` is a morphism of modules on the
slice of the small étale site at `U`, and that site has its objects in `Type (u + 1)`.  At `u + 1`
the implication `Stacks 03DL(8) ⟹ 03DL(6)` — coherent implies quasi-coherent, which
`AlgebraicGeometry.Space.isCoherent_of_isCoherentOnSite` needs — is not available, since
`SheafOfModules.isQuasicoherentOnSite_of_isCoherentOnSite` builds its presentations out of global
sections of the structure sheaf and so pins the module universe to the ring universe.

The `u + 1` is, however, an artefact of the construction and not of the sheaf.  The
small étale site of an algebraic space is essentially `u`-small
(`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`, which rests on the cardinal cutoff of
the big fppf site), hence so is each of its slices, hence those `Hom`-sets are `u`-small and the
internal Hom descends to the module universe `u`.  That descent is
`AlgebraicGeometry.RingedSite.internalHomSheafSmall`, and
`AlgebraicGeometry.Space.smallEtaleInternalHomSmallIso` identifies its universe lift with
`AlgebraicGeometry.Space.smallEtaleInternalHom` — so the two are the same internal Hom.  At the
module universe `u` the implication above applies, and `AlgebraicGeometry.Space.IsCoherent` — the
coherence predicate of Stacks 07UA, the same one the tensor clause concludes — is reached.

**No local Noetherianity hypothesis, on either clause.**  The source states Stacks 07UE for a
locally Noetherian algebraic space, because it deduces it from the case of schemes through
Stacks 07UB, and that is where local Noetherianity enters.  Neither clause needs it: the tensor
clause is the coherent clause of Stacks 03L6, which holds on an arbitrary ringed site, and the
sheaf-hom clause is Stacks 01CQ(2), which likewise does.  The source says as much for a ringed
space in the comments on Lemma 30.9.4.  So the three statements below are stronger than the
source's.

## References

* [Stacks Project, Tag 07UE](https://stacks.math.columbia.edu/tag/07UE)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The small étale site of an algebraic space is essentially small at the universe of its
schemes, in the spelling the ringed site uses for its underlying category.  This is
`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`; instance search does not unfold the
projection `AlgebraicGeometry.RingedSite.C`, so the instance is restated here. -/
instance instEssentiallySmallSmallEtaleRingedSite :
    EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C :=
  SmallEtale.instEssentiallySmall B S hS F

/-- **The internal Hom of two coherent `𝒪_F`-modules is coherent on the small étale ringed site
of an algebraic space.**

This is `AlgebraicGeometry.RingedSite.isCoherentOnSite_internalHomSheaf`, Stacks 01CQ(2) on an
arbitrary ringed site, read at the small étale ringed site of `F`:
`AlgebraicGeometry.Space.smallEtaleInternalHom` *is*
`AlgebraicGeometry.RingedSite.internalHomSheaf` of that site, by `rfl`.

No local Noetherianity hypothesis is needed; see the module documentation. -/
theorem isCoherentOnSite_smallEtaleInternalHom (M N : Modules.{u, u} B S hS F hF)
    (hM : SheafOfModules.IsCoherentOnSite M) (hN : SheafOfModules.IsCoherentOnSite N) :
    SheafOfModules.IsCoherentOnSite (smallEtaleInternalHom B S hS F hF M N) :=
  RingedSite.isCoherentOnSite_internalHomSheaf
    (X := smallEtaleRingedSite B S hS F hF) M N hM hN

/-- **The internal Hom `𝓗om_{𝒪_F}(M, N)` of two `𝒪_F`-modules on an algebraic space, at the
module universe of the schemes.**

`AlgebraicGeometry.Space.smallEtaleInternalHom` has its sections in `u + 1`, a section over an
étale chart `U` being a morphism of modules on the slice of the small étale site at `U`, whose
objects lie in `Type (u + 1)`.  The small étale site of an algebraic space is nevertheless
essentially `u`-small, so those `Hom`-sets are `u`-small and the whole sheaf descends to the
module universe `u`.  That is what this is: `AlgebraicGeometry.Space.smallEtaleInternalHomSmallIso`
identifies its universe lift with `AlgebraicGeometry.Space.smallEtaleInternalHom`, so it is that
internal Hom and not a second construction. -/
def smallEtaleInternalHomSmall (M N : Modules.{u, u} B S hS F hF) :
    Modules.{u, u} B S hS F hF :=
  RingedSite.internalHomSheafSmall (smallEtaleRingedSite B S hS F hF) M N

/-- **The universe lift of `AlgebraicGeometry.Space.smallEtaleInternalHomSmall` is
`AlgebraicGeometry.Space.smallEtaleInternalHom`**: the two are the same internal Hom, read in
two universes. -/
def smallEtaleInternalHomSmallIso (M N : Modules.{u, u} B S hS F hF) :
    (Stacks.SheafOfModules.moduleULift.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)).obj
      (smallEtaleInternalHomSmall B S hS F hF M N) ≅
      smallEtaleInternalHom B S hS F hF M N :=
  RingedSite.internalHomSheafSmallIso (smallEtaleRingedSite B S hS F hF) M N

/-- The module-universe-`u` model of the internal Hom of two coherent `𝒪_F`-modules is coherent
on the small étale ringed site: its universe lift is, and coherence descends along a universe
lift of the sections. -/
theorem isCoherentOnSite_smallEtaleInternalHomSmall (M N : Modules.{u, u} B S hS F hF)
    (hM : SheafOfModules.IsCoherentOnSite M) (hN : SheafOfModules.IsCoherentOnSite N) :
    SheafOfModules.IsCoherentOnSite (smallEtaleInternalHomSmall B S hS F hF M N) :=
  Stacks.SheafOfModules.isCoherentOnSite_of_moduleULift
    (Stacks.SheafOfModules.isCoherentOnSite_of_iso
      (smallEtaleInternalHomSmallIso B S hS F hF M N).symm
      (isCoherentOnSite_smallEtaleInternalHom B S hS F hF M N hM hN))

/-- **Stacks 07UE, the sheaf-hom clause.**  The internal Hom `𝓗om_{𝒪_F}(M, N)` of two coherent
`𝒪_F`-modules on an algebraic space is coherent. -/
@[stacks 07UE "internal Hom"]
theorem isCoherent_smallEtaleInternalHomSmall (M N : Modules.{u, u} B S hS F hF)
    [IsCoherent B S hS F hF M] [IsCoherent B S hS F hF N] :
    IsCoherent B S hS F hF (smallEtaleInternalHomSmall B S hS F hF M N) :=
  let : SheafOfModules.IsCoherentOnSite (smallEtaleInternalHomSmall B S hS F hF M N) :=
    isCoherentOnSite_smallEtaleInternalHomSmall B S hS F hF M N inferInstance inferInstance
  isCoherent_of_isCoherentOnSite B S hS F hF (smallEtaleInternalHomSmall B S hS F hF M N)

/-- **Stacks 07UE.**  Let `F` be an algebraic space over a scheme `S` and let `M`, `N` be
coherent `𝒪_F`-modules.  Then `M ⊗_{𝒪_F} N` and `𝓗om_{𝒪_F}(M, N)` are coherent. -/
@[stacks 07UE]
theorem isCoherent_tensorModule_and_smallEtaleInternalHomSmall
    (M N : Modules.{u, u} B S hS F hF)
    [IsCoherent B S hS F hF M] [IsCoherent B S hS F hF N] :
    IsCoherent B S hS F hF (tensorModule B S hS F hF M N) ∧
      IsCoherent B S hS F hF (smallEtaleInternalHomSmall B S hS F hF M N) :=
  ⟨isCoherent_tensorModule B S hS F hF M N,
    isCoherent_smallEtaleInternalHomSmall B S hS F hF M N⟩

end AlgebraicGeometry.Space

end
