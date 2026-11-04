module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# The higher direct images transported along isomorphisms of source and target

Let `g : W ⟶ T` and `g' : W' ⟶ T'` be morphisms of schemes and let `a : W ≅ W'`, `b : T ≅ T'`
be isomorphisms making the square commute, `a.hom ≫ g' = g ≫ b.hom`.  This file transports the
higher direct images along `g` to the higher direct images along `g'`: the comparison

`b_* (R^p g_* G) ≅ R^p g'_* (a_* G)`

and, over locally Noetherian targets, the resulting equivalence of the two coherence statements.

The library has this transport for the underived pushforward —
`AlgebraicGeometry.Scheme.Modules.pushforwardComp`, `pushforwardCongr`, `pushforwardId` — and
that is all the input needed, because for an isomorphism `e` those three isomorphisms exhibit
`Scheme.Modules.pushforward e.hom` as an *equivalence* of categories
(`Stacks.AlgebraicGeometry.OpenBaseChange.pushforwardEquivalence`), and an equivalence is exact
and preserves injective objects.  So each leg of the square is a case of a comparison already in
the library:

* the target leg `b` is postcomposition by an exact functor, which commutes with right derived
  functors: `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`;
* the source leg `a` is precomposition by an exact functor preserving injectives, which also
  commutes with right derived functors because it carries an injective resolution to an
  injective resolution: `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`.

## Main definitions

* `Stacks.AlgebraicGeometry.DerivedPushforward.rightDerivedTransportIso` — the comparison
  displayed above, as an isomorphism of functors.
* `…DerivedPushforward.restrictInvIsoPushforward` — restriction along `e.inv` is pushforward
  along `e.hom`.

## Main results

* `…DerivedPushforward.pushforward_isEquivalence`: pushforward along an isomorphism of schemes
  is an equivalence of the categories of modules.
* `…DerivedPushforward.isCoherent_rightDerived_of_transport` and
  `…DerivedPushforward.isCoherent_rightDerived_transport`: over a locally Noetherian target,
  coherence of `R^p g_* G` and coherence of `R^p g'_* (a_* G)` imply one another.
* `…DerivedPushforward.isCoherent_rightDerived_transport_iff`: the two together.

## Implementation notes

Coherence is moved across the target isomorphism by
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`, which is
[Stacks, Tag 01Y6]: an isomorphism is a finite morphism, so the direct image of a coherent module
along it is coherent over a locally Noetherian target.  No separate transport of coherence is
needed.

Both the natural isomorphism and its value at an object are recorded.  The value is not a
convenience: `((F ⋙ G).obj M).IsCoherent` and `(G.obj (F.obj M)).IsCoherent` are definitionally
equal but not syntactically equal, and instance resolution for `IsCoherent` sees only the latter.

## References

* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.OpenBaseChange
open Stacks.Cohomology.CompositeRightDerived

universe u

namespace Stacks.AlgebraicGeometry.DerivedPushforward

/-! ### Pushforward along an isomorphism of schemes -/

variable {X Y : Scheme.{u}}

/-- **Pushforward along an isomorphism of schemes is an equivalence** of the categories of
sheaves of modules.  This is what supplies the exactness and the preservation of injective
objects that the two derived comparisons below need. -/
noncomputable instance pushforward_isEquivalence (e : X ≅ Y) :
    (Scheme.Modules.pushforward e.hom).IsEquivalence :=
  inferInstanceAs ((pushforwardEquivalence e).functor).IsEquivalence

/-- **Restriction along `e.inv` is pushforward along `e.hom`**, for an isomorphism `e`.  It is
`Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv` at `e.symm`, the
isomorphism `e.symm` having `e.inv` for its forward map and `e.hom` for its inverse. -/
noncomputable def restrictInvIsoPushforward (e : X ≅ Y) :
    Scheme.Modules.restrictFunctor e.inv ≅ Scheme.Modules.pushforward e.hom :=
  restrictFunctorIsoPushforwardInv e.symm

/-- Pushing forward along an isomorphism and then along its inverse is the identity. -/
noncomputable def pushforwardInvPushforwardIso (e : X ≅ Y) :
    Scheme.Modules.pushforward e.hom ⋙ Scheme.Modules.pushforward e.inv ≅ 𝟭 X.Modules :=
  Scheme.Modules.pushforwardComp e.hom e.inv ≪≫
    Scheme.Modules.pushforwardCongr e.hom_inv_id ≪≫ Scheme.Modules.pushforwardId X

/-- `pushforwardInvPushforwardIso` at a sheaf of modules, written with the two pushforwards
applied in turn. -/
noncomputable def pushforwardInvPushforwardObjIso (e : X ≅ Y) (M : X.Modules) :
    (Scheme.Modules.pushforward e.inv).obj ((Scheme.Modules.pushforward e.hom).obj M) ≅ M :=
  (pushforwardInvPushforwardIso e).app M

/-! ### The transport of the higher direct images -/

variable {W T W' T' : Scheme.{u}}

/-- **The higher direct images transported along isomorphisms of source and target.** For a
commuting square `a.hom ≫ g' = g ≫ b.hom` with `a : W ≅ W'` and `b : T ≅ T'` isomorphisms,
pushing `R^p g_*` forward along `b` is `R^p g'_*` of the pushforward along `a`.

Both sides are compared to `R^p (g ≫ b.hom)_* = R^p (a.hom ≫ g')_*`.  On the target side
`Scheme.Modules.pushforward b.hom` is exact, so
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` applies to
`AlgebraicGeometry.Scheme.Modules.pushforwardComp`; on the source side
`Scheme.Modules.pushforward a.hom` is exact and preserves injective objects, so
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` applies.  The square itself
enters only through `AlgebraicGeometry.Scheme.Modules.pushforwardCongr`. -/
noncomputable def rightDerivedTransportIso (g : W ⟶ T) (g' : W' ⟶ T') (a : W ≅ W') (b : T ≅ T')
    (h : a.hom ≫ g' = g ≫ b.hom) (p : ℕ) :
    (Scheme.Modules.pushforward g).rightDerived p ⋙ Scheme.Modules.pushforward b.hom ≅
      Scheme.Modules.pushforward a.hom ⋙ (Scheme.Modules.pushforward g').rightDerived p :=
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (Scheme.Modules.pushforward g)
      (Scheme.Modules.pushforward b.hom) (Scheme.Modules.pushforward (g ≫ b.hom))
      (Scheme.Modules.pushforwardComp g b.hom) p ≪≫
    Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (Scheme.Modules.pushforwardCongr h.symm) p ≪≫
    Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (Scheme.Modules.pushforwardComp a.hom g').symm p ≪≫
    compRightDerivedNatIso (Scheme.Modules.pushforward a.hom) (Scheme.Modules.pushforward g') p

/-- `rightDerivedTransportIso` at a sheaf of modules, with the functors applied in turn. -/
noncomputable def rightDerivedTransportObjIso (g : W ⟶ T) (g' : W' ⟶ T') (a : W ≅ W')
    (b : T ≅ T') (h : a.hom ≫ g' = g ≫ b.hom) (p : ℕ) (G : W.Modules) :
    (Scheme.Modules.pushforward b.hom).obj
        (((Scheme.Modules.pushforward g).rightDerived p).obj G) ≅
      ((Scheme.Modules.pushforward g').rightDerived p).obj
        ((Scheme.Modules.pushforward a.hom).obj G) :=
  (rightDerivedTransportIso g g' a b h p).app G

/-! ### Coherence across the transport -/

/-- **Coherence of a higher direct image descends along the transport.** If `R^p g'_* (a_* G)` is
coherent then so is `R^p g_* G`, the target `T` being locally Noetherian.

Push the hypothesis forward along `b.inv`, which is an isomorphism and hence a finite morphism,
so [Stacks, Tag 01Y6] keeps it coherent; `rightDerivedTransportObjIso` identifies the result with
`R^p g_* G`. -/
theorem isCoherent_rightDerived_of_transport (g : W ⟶ T) (g' : W' ⟶ T') (a : W ≅ W')
    (b : T ≅ T') (h : a.hom ≫ g' = g ≫ b.hom) (p : ℕ) (G : W.Modules) [IsLocallyNoetherian T]
    (hG : (((Scheme.Modules.pushforward g').rightDerived p).obj
      ((Scheme.Modules.pushforward a.hom).obj G)).IsCoherent) :
    (((Scheme.Modules.pushforward g).rightDerived p).obj G).IsCoherent := by
  have h1 : ((Scheme.Modules.pushforward b.inv).obj
      (((Scheme.Modules.pushforward g').rightDerived p).obj
        ((Scheme.Modules.pushforward a.hom).obj G))).IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite b.inv _
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    ((pushforwardInvPushforwardObjIso b
        (((Scheme.Modules.pushforward g).rightDerived p).obj G)).symm ≪≫
      (Scheme.Modules.pushforward b.inv).mapIso (rightDerivedTransportObjIso g g' a b h p G))

/-- **Coherence of a higher direct image survives the transport.** If `R^p g_* G` is coherent
then so is `R^p g'_* (a_* G)`, the target `T'` being locally Noetherian.

The same argument along `b.hom` instead of `b.inv`. -/
theorem isCoherent_rightDerived_transport (g : W ⟶ T) (g' : W' ⟶ T') (a : W ≅ W') (b : T ≅ T')
    (h : a.hom ≫ g' = g ≫ b.hom) (p : ℕ) (G : W.Modules) [IsLocallyNoetherian T']
    (hG : (((Scheme.Modules.pushforward g).rightDerived p).obj G).IsCoherent) :
    (((Scheme.Modules.pushforward g').rightDerived p).obj
      ((Scheme.Modules.pushforward a.hom).obj G)).IsCoherent := by
  have h1 : ((Scheme.Modules.pushforward b.hom).obj
      (((Scheme.Modules.pushforward g).rightDerived p).obj G)).IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite b.hom _
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    (rightDerivedTransportObjIso g g' a b h p G).symm

/-- **Coherence of a higher direct image is invariant under the transport**, both targets being
locally Noetherian. -/
theorem isCoherent_rightDerived_transport_iff (g : W ⟶ T) (g' : W' ⟶ T') (a : W ≅ W')
    (b : T ≅ T') (h : a.hom ≫ g' = g ≫ b.hom) (p : ℕ) (G : W.Modules) [IsLocallyNoetherian T]
    [IsLocallyNoetherian T'] :
    (((Scheme.Modules.pushforward g).rightDerived p).obj G).IsCoherent ↔
      (((Scheme.Modules.pushforward g').rightDerived p).obj
        ((Scheme.Modules.pushforward a.hom).obj G)).IsCoherent :=
  ⟨isCoherent_rightDerived_transport g g' a b h p G,
    isCoherent_rightDerived_of_transport g g' a b h p G⟩

end Stacks.AlgebraicGeometry.DerivedPushforward

end
