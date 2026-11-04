module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiSpaceFunctors
public import StacksFrontier.Topology.Sheaves.OpenEqualityLocus

/-!
# The open locus where two sections of a small Zariski sheaf agree

Let `S` be a scheme in a big Zariski site `B` and let `F` be a sheaf of sets on the small
Zariski site of `S`. Two global sections of `F`, presented as morphisms out of a sheaf assumed
terminal, agree on a largest open subscheme of `S`: there is an open `W ⊆ S` such that for a
morphism `f : T ⟶ S` of `B` the two sections have the same inverse image along the induced
morphism of small Zariski topoi exactly when the image of `T` lies in `W`.

This is the Zariski analogue of Stacks 09XM, which the source states for the small étale site
only, so nothing here carries that tag. It is obtained from the topological statement
`Stacks.OpenEqLocus.sheafPullback_map_eq_iff` by transporting along the identification of
sheaves on the small Zariski site of `S` with sheaves on the space of `S` (Stacks 020X), under
which small-site base change becomes the inverse image of sheaves on spaces (Stacks 0211).

## Main definitions

* `AlgebraicGeometry.smallZariskiSitePullback` — inverse image of sheaves of sets along small
  Zariski base change.
* `AlgebraicGeometry.zariskiOpenEqLocus` — the largest open of `S` on which the two sections
  agree.

## Main results

* `AlgebraicGeometry.smallZariskiPullback_map_eq_iff` — the universal property of the locus: the
  two sections agree after inverse image along `f` exactly when the image of `T` lies in it.
* `AlgebraicGeometry.eq_iff_zariskiOpenEqLocus_eq_top` — the locus is everything exactly when
  the two sections agree.

## Implementation notes

The transport is through `AlgebraicGeometry.smallZariskiPullbackIso`, which compares the two
inverse-image functors over the sheaf comparison `AlgebraicGeometry.smallZariskiSheafEquiv`. The
comparison is an equivalence of categories, so it is faithful and carries a terminal sheaf to a
terminal sheaf; those two facts are all that the transport needs, beyond the natural
isomorphism.

## References

* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
* [Stacks Project, Tag 0211](https://stacks.math.columbia.edu/tag/0211)
* [Stacks Project, Tag 09XM](https://stacks.math.columbia.edu/tag/09XM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.OpenEqLocus

universe u

namespace AlgebraicGeometry

/-- Inverse image of sheaves of sets along small Zariski base change along `f : T ⟶ S`, that is
`f_small⁻¹` on the small Zariski topoi. -/
public abbrev smallZariskiSitePullback (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S) :
    Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1)) ⥤
      Sheaf (SmallZariski.topology B T.obj T.property) (Type (u + 1)) :=
  (smallZariskiBaseChange B f).sheafPullback (Type (u + 1))
    (SmallZariski.topology B S.obj S.property) (SmallZariski.topology B T.obj T.property)

variable (B : BigZariskiSite.{u}) (S : B.Schemes)
  {A F : Sheaf (SmallZariski.topology B S.obj S.property) (Type (u + 1))}

/-- **The open locus, the Zariski analogue of Stacks 09XM.** The largest open subscheme of `S`
on which two global sections of a sheaf on the small Zariski site of `S` agree: the locus of the
corresponding sections of the corresponding sheaf on the space of `S`.

The source states 09XM for the small étale site only, so this carries no tag. -/
public def zariskiOpenEqLocus (s t : A ⟶ F) : Opens S.obj.carrier :=
  eqLocus ((smallZariskiSheafEquiv B S.obj S.property).functor.map s)
    ((smallZariskiSheafEquiv B S.obj S.property).functor.map t)

/-- **The universal property of the open locus, the Zariski analogue of Stacks 09XM.** Two
global sections of a sheaf on the small Zariski site of `S` agree after inverse image along
`f : T ⟶ S` exactly when the image of `T` lies in their open equality locus.

The source states 09XM for the small étale site only, so this carries no tag. -/
public theorem smallZariskiPullback_map_eq_iff {T : B.Schemes} (f : T ⟶ S)
    (hA : IsTerminal A) (s t : A ⟶ F) :
    (smallZariskiSitePullback B f).map s = (smallZariskiSitePullback B f).map t ↔
      ∀ x : (B.inclusion.obj T).carrier,
        (B.inclusion.map f).base x ∈ zariskiOpenEqLocus B S s t := by
  have : (smallZariskiBaseChange B f).IsContinuous
      (SmallZariski.topology B S.obj S.property)
      (SmallZariski.topology B T.obj T.property) :=
    (smallZariskiBaseChange_isMorphismOfSites B f).toIsContinuous
  have hA' : IsTerminal ((smallZariskiSheafEquiv B S.obj S.property).functor.obj A) :=
    IsTerminal.isTerminalObj (smallZariskiSheafEquiv B S.obj S.property).functor A hA
  have hstep : (smallZariskiSitePullback B f).map s = (smallZariskiSitePullback B f).map t ↔
      (opensPullback (B.inclusion.map f).base).map
          ((smallZariskiSheafEquiv B S.obj S.property).functor.map s) =
        (opensPullback (B.inclusion.map f).base).map
          ((smallZariskiSheafEquiv B S.obj S.property).functor.map t) :=
    ⟨fun h => (map_eq_iff_of_natIso (smallZariskiPullbackIso B f)).mpr
      (show ((smallZariskiSitePullback B f) ⋙
          (smallZariskiSheafEquiv B T.obj T.property).functor).map s = _ from
        congrArg (smallZariskiSheafEquiv B T.obj T.property).functor.map h),
     fun h => (smallZariskiSheafEquiv B T.obj T.property).functor.map_injective
      ((map_eq_iff_of_natIso (smallZariskiPullbackIso B f)).mp h)⟩
  rw [hstep, sheafPullback_map_eq_iff (B.inclusion.map f).base
    ((smallZariskiSheafEquiv B S.obj S.property).functor.map s)
    ((smallZariskiSheafEquiv B S.obj S.property).functor.map t) hA']
  refine ⟨fun h x => ?_, fun h => top_le_iff.mp fun x _ => h x⟩
  show x ∈ (Opens.map (B.inclusion.map f).base).obj (zariskiOpenEqLocus B S s t)
  rw [zariskiOpenEqLocus, h]
  trivial

/-- **The equality locus is everything exactly when the two sections agree.** -/
public theorem eq_iff_zariskiOpenEqLocus_eq_top (hA : IsTerminal A) (s t : A ⟶ F) :
    s = t ↔ zariskiOpenEqLocus B S s t = ⊤ := by
  have hA' : IsTerminal ((smallZariskiSheafEquiv B S.obj S.property).functor.obj A) :=
    IsTerminal.isTerminalObj (smallZariskiSheafEquiv B S.obj S.property).functor A hA
  rw [zariskiOpenEqLocus, ← eq_iff_eqLocus_eq_top hA'
    ((smallZariskiSheafEquiv B S.obj S.property).functor.map s)
    ((smallZariskiSheafEquiv B S.obj S.property).functor.map t)]
  exact ⟨congrArg _,
    fun h => (smallZariskiSheafEquiv B S.obj S.property).functor.map_injective h⟩

end AlgebraicGeometry

end
