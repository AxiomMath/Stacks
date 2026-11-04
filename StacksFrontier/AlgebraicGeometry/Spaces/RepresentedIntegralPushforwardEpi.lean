module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardBoundedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange

/-!
# Stacks 04C2, part (1), for a morphism of representable algebraic spaces

Let `B` be a big fppf site containing a scheme `S` and let `g : T' ⟶ T` be a morphism of the big
fppf category over `S` whose underlying morphism of schemes is integral.  Part (1) of
Stacks 04C2 for the represented morphism of algebraic spaces is proved here: the direct image
of sheaves of sets along the morphism of small étale topoi of Stacks 03G2, part (3), carries
surjections to surjections.

The proof transports the statement on the small étale site of the *scheme* `T`, which is proved
as `AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_pushforward_preservesEpimorphisms`, along
the identification of the small étale site of a representable algebraic space with that of the
representing scheme.  The compatibility of that identification with base change is
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso`, and the two identifications are
equivalences of sites, so they cancel.

## Main results

* `AlgebraicGeometry.Space.representedSmallBaseChange_pushforward_preservesEpimorphisms`:
  restriction of sheaves of sets along chart base change carries surjections to surjections.
* `AlgebraicGeometry.Space.representedSmallEtalePushforward_preservesEpimorphisms` is the same
  statement for the direct image of the morphism of small étale topoi, which is what Stacks
  04C2, part (1) asserts.

## Implementation notes

**What this does not give.**  The hypothesis `hscheme` of
`AlgebraicGeometry.Space.smallEtalePushforward_preservesEpimorphisms` quantifies over an
*arbitrary* algebraic space source, so it is not discharged by these theorems: passing from an
arbitrary source to a representable one needs that an integral morphism of algebraic spaces is
relatively representable, which is the implication Stacks 03ZQ, condition (2) implies condition
(1), and that implication is not available — see
`AlgebraicGeometry.Space.isIntegralHom_iff_representable_iff`, which records that it is exactly
what the repository's form of Stacks 03ZQ leaves out.  Consequently **no declaration here
carries a `@[stacks 0A4K]` attribute**: the general integral case of Stacks 0A4K still rests on
that implication.

**The two identifications are equivalences, not merely dense subsite inclusions.**
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` is an equivalence of categories and
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_topology` matches the two topologies,
so its inverse is a dense subsite inclusion and restriction of sheaves along its functor is the
inverse half of `CategoryTheory.Equivalence.sheafCongr`.  That is how the equivalence on the
left of the comparison square is cancelled, by the same assembly as in
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_pushforward_preservesEpimorphisms`.

**Universes.**  The objects of all four sites live in `Type (u + 1)`, which is the universe of
the sheaves of sets throughout; both inputs are stated there.

## References

* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The inverse of an equivalence is a dense subsite inclusion for the topology on the source
and the topology it induces on the target. -/
private theorem isDenseSubsite_inverse_of_inducedTopology_eq {C D : Type*} [Category C]
    [Category D] (e : C ≌ D) (K : GrothendieckTopology D) (J : GrothendieckTopology C)
    (h : e.functor.inducedTopology K = J) : e.inverse.IsDenseSubsite K J := by
  rw [← h]
  exact inferInstanceAs (e.symm.functor.IsDenseSubsite K (e.symm.inverse.inducedTopology K))

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

include hg

/-- **Stacks 04C2, part (1), for chart base change along a morphism of representable algebraic
spaces.** For `g : T' ⟶ T` with integral underlying morphism of schemes, restriction of sheaves
of sets along base change of étale scheme charts carries surjections to surjections.

The same statement on the small étale site of the scheme `T` is
`AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_pushforward_preservesEpimorphisms`, and
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` identifies the two base changes
through the equivalences of
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`; restriction along those
equivalences is an equivalence of sheaf categories, so it cancels. -/
theorem representedSmallBaseChange_pushforward_preservesEpimorphisms
    (hint : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map g)) :
    letI := isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS g) hg
    ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).sheafPushforwardContinuous
      (Type (u + 1)) (SmallEtale.topology B S hS (yoneda.obj T))
      (SmallEtale.topology B S hS (yoneda.obj T'))).PreservesEpimorphisms := by
  have := isContinuous_smallBaseChange B S hS (representedSpaceMap B S hS g) hg
  set A := Type (u + 1) with hA
  set E := associatedBigEtaleSite B with hE
  set φ := representedSpaceMap B S hS g with hφ
  set e' := representedSmallEtaleEquivalence B S hS T' with he'
  set e'' := representedSmallEtaleEquivalence B S hS T with he''
  set L := smallBaseChange B S hS φ hg with hLdef
  set R := _root_.AlgebraicGeometry.smallEtaleBaseChange E g.left with hRdef
  set J := SmallEtale.topology B S hS (yoneda.obj T) with hJ
  set J' := SmallEtale.topology B S hS (yoneda.obj T') with hJ'
  set K := _root_.AlgebraicGeometry.SmallEtale.topology E
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property with hK
  set K' := _root_.AlgebraicGeometry.SmallEtale.topology E
    ((BigFppfOver.toScheme B S hS).obj T') T'.left.property with hK'
  -- the two identifications are dense subsite inclusions, hence equivalences on sheaves
  have hds : e''.inverse.IsDenseSubsite K J :=
    isDenseSubsite_inverse_of_inducedTopology_eq e'' K J
      (representedSmallEtaleEquivalence_topology B S hS T)
  have hds' : e'.inverse.IsDenseSubsite K' J' :=
    isDenseSubsite_inverse_of_inducedTopology_eq e' K' J'
      (representedSmallEtaleEquivalence_topology B S hS T')
  have hR : R.IsContinuous K K' :=
    _root_.AlgebraicGeometry.smallEtaleBaseChange_isContinuous E g.left
  have hLe' : (L ⋙ e'.functor).IsContinuous J K' := Functor.isContinuous_comp _ _ J J' K'
  have he''R : (e''.functor ⋙ R).IsContinuous J K' := Functor.isContinuous_comp _ _ J K K'
  -- the comparison of the direct images, from the comparison of the base changes
  have hiso :
      e'.functor.sheafPushforwardContinuous A J' K' ⋙ L.sheafPushforwardContinuous A J J' ≅
        R.sheafPushforwardContinuous A K K' ⋙ e''.functor.sheafPushforwardContinuous A J K :=
    Functor.sheafPushforwardContinuousComp' (F := L) (G := e'.functor) (Iso.refl _) A J J' K' ≪≫
      Functor.sheafPushforwardContinuousIso
        (representedSmallEtaleBaseChangeIso B S hS g hg) A J K' ≪≫
      (Functor.sheafPushforwardContinuousComp' (F := e''.functor) (G := R)
        (Iso.refl _) A J K K').symm
  -- the right-hand composite preserves epimorphisms
  have hintE : _root_.AlgebraicGeometry.IsIntegralHom (E.inclusion.map g.left) := hint
  have hRepi : (R.sheafPushforwardContinuous A K K').PreservesEpimorphisms :=
    _root_.AlgebraicGeometry.SmallEtale.smallEtaleBaseChange_pushforward_preservesEpimorphisms
      E g.left
  have hrhs := _root_.AlgebraicGeometry.SmallEtale.preservesEpimorphisms_comp
    (R.sheafPushforwardContinuous A K K')
    (e''.functor.sheafPushforwardContinuous A J K) hRepi inferInstance
  have hlhs := Functor.PreservesEpimorphisms.of_iso hiso.symm
  -- cancel the equivalence on the left
  have hequiv : (e'.functor.sheafPushforwardContinuous A J' K').IsEquivalence :=
    inferInstanceAs (Equivalence.sheafCongr J' K' e' A).inverse.IsEquivalence
  let eq' := (e'.functor.sheafPushforwardContinuous A J' K').asEquivalence
  have hcancel := _root_.AlgebraicGeometry.SmallEtale.preservesEpimorphisms_comp eq'.inverse
    (eq'.functor ⋙ L.sheafPushforwardContinuous A J J') inferInstance hlhs
  exact Functor.PreservesEpimorphisms.of_iso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eq'.counitIso _ ≪≫ Functor.leftUnitor _)

/-- **Stacks 04C2, part (1), for a morphism of representable algebraic spaces.** For
`g : T' ⟶ T` in the big fppf category over `S` with integral underlying morphism of schemes,
the small étale direct image of sheaves of sets along the represented morphism of algebraic
spaces carries surjections to surjections.

By Stacks 03G2, part (4), that direct image is restriction along base change of étale scheme
charts, which is
`AlgebraicGeometry.Space.representedSmallBaseChange_pushforward_preservesEpimorphisms`. -/
theorem representedSmallEtalePushforward_preservesEpimorphisms
    (hint : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map g)) :
    Functor.PreservesEpimorphisms
      (smallToposMorphism B S hS (representedSpaceMap B S hS g)).pushforward := by
  have := (smallBaseChange_isMorphismOfSites B S hS
    (representedSpaceMap B S hS g) hg).toIsContinuous
  have hL : Functor.PreservesEpimorphisms
      ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg).sheafPushforwardContinuous
        (Type (u + 1)) (SmallEtale.topology B S hS (yoneda.obj T))
        (SmallEtale.topology B S hS (yoneda.obj T'))) :=
    representedSmallBaseChange_pushforward_preservesEpimorphisms B S hS g hg hint
  exact Functor.PreservesEpimorphisms.of_iso
    (smallBaseChange_topos B S hS (representedSpaceMap B S hS g) hg).symm

end AlgebraicGeometry.Space

end
