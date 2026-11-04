module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AlgebraSiteCartesianBase
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Fibre products in the algebra site of a chosen big site

`Stacks.Adequate.algebraSite` is the opposite of the category of `A`-algebras whose spectrum
belongs to a chosen big site.  To apply the cartesian-sheaf criteria to the module-valued
functors living on it, that category has to have fibre products, and its spectrum functor has
to carry them to fibre products of schemes.

Both come from one computation: a fibre product in `Stacks.Adequate.algebraSite` is a pushout
`B' ⊗_D C'` of the underlying algebras, and the spectrum of a pushout of commutative rings is
the fibre product of the spectra.  The algebras of the site are closed under such a pushout
precisely because the spectrum of the pushout is that fibre product, which the site contains.

## Main results

* `Stacks.Adequate.hasPullbacks_algebraSite` — the algebra site has fibre products.
* `Stacks.Adequate.preservesLimitsOfShape_algebraSiteScheme` — its spectrum functor carries
  them to fibre products of schemes.
* `Stacks.Adequate.isPushout_algebraSiteRings_of_isPullback` — a fibre-product square of the
  algebra site is a pushout, that is a tensor-product, square of commutative rings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

/-! ### Pushouts of the algebras of a site -/

section Algebras

variable {A : Type u} [CommRing A] (Q : ObjectProperty Scheme.{u})

/-- The forgetful functor from the commutative `A`-algebras to the commutative rings preserves
pushouts: it is the identification of `CommAlgCat A` with the commutative rings under `A`
followed by the forgetful functor of that coslice, and the latter creates the connected
colimits, `WalkingSpan` being connected. -/
private instance preservesColimitsOfShape_walkingSpan_forget₂ :
    PreservesColimitsOfShape WalkingSpan (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}) :=
  inferInstanceAs (PreservesColimitsOfShape WalkingSpan
    ((commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙ Under.forget (CommRingCat.of A)))

variable [Q.IsClosedUnderIsomorphisms]

/-- Belonging to the chosen category of schemes after taking spectra is invariant under
isomorphism of algebras, because isomorphic algebras have isomorphic spectra. -/
public instance isClosedUnderIsomorphisms_algebraInSite :
    (AdequateFunctor.algebraInSite.{u, u} A Q).IsClosedUnderIsomorphisms where
  of_iso {_X _Y} e hX :=
    (Q.prop_iff_of_iso
      (Scheme.Spec.mapIso ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).mapIso e).op).symm).mp hX

variable [Q.IsClosedUnderLimitsOfShape WalkingCospan]

omit [Q.IsClosedUnderIsomorphisms] in
/-- **The algebras of a site are closed under pushouts.** The spectrum of a pushout square of
commutative rings is a fibre-product square of schemes, by
`AlgebraicGeometry.isPullback_SpecMap_of_isPushout`; so if the three spectra of a pushout
square of `A`-algebras belong to a category of schemes closed under fibre products, so does
the spectrum of the pushout. -/
public theorem algebraInSite_of_isPushout {X Y Z W : CommAlgCat.{u} A}
    {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ W} {inr : Y ⟶ W} (h : IsPushout f g inl inr)
    (hZ : AdequateFunctor.algebraInSite.{u, u} A Q Z)
    (hX : AdequateFunctor.algebraInSite.{u, u} A Q X)
    (hY : AdequateFunctor.algebraInSite.{u, u} A Q Y) :
    AdequateFunctor.algebraInSite.{u, u} A Q W := by
  have hring := h.map (forget₂ (CommAlgCat.{u} A) CommRingCat.{u})
  have hpull := AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _ hring
  refine Q.prop_of_isLimit hpull.isLimit ?_
  intro j
  match j with
  | none => exact hZ
  | some WalkingPair.left => exact hX
  | some WalkingPair.right => exact hY

/-- The algebras of a site are closed under colimits of shape `WalkingSpan`: an arbitrary such
colimit is the pushout of the two legs of the span, which
`Stacks.Adequate.algebraInSite_of_isPushout` handles. -/
public instance isClosedUnderColimitsOfShape_algebraInSite :
    (AdequateFunctor.algebraInSite.{u, u} A Q).IsClosedUnderColimitsOfShape WalkingSpan := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  refine ((AdequateFunctor.algebraInSite.{u, u} A Q).prop_iff_of_iso
    (HasColimit.isoOfNatIso (diagramIsoSpan F))).mpr ?_
  exact algebraInSite_of_isPushout Q (IsPushout.of_hasPushout _ _)
    (hF WalkingSpan.zero) (hF WalkingSpan.left) (hF WalkingSpan.right)

/-- The algebras of a site have pushouts, formed as pushouts of the underlying algebras. -/
public instance hasPushouts_algebrasInSite :
    HasPushouts (AdequateFunctor.AlgebrasInSite.{u, u} A Q) := inferInstance

end Algebras

/-! ### Fibre products in the algebra site -/

section Site

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- **The algebra site of a chosen big site has fibre products.**  A fibre product there is a
pushout `B' ⊗_D C'` of the underlying algebras, which is again an algebra of the site because
its spectrum is the fibre product of the spectra. -/
public instance hasPullbacks_algebraSite : HasPullbacks (algebraSite B) := inferInstance

/-- **A fibre-product square of the algebra site is a pushout square of commutative rings.**
A fibre product of the algebra site is a pushout of the algebras of the site; the inclusion of
the algebras of the site into all `A`-algebras creates these pushouts, and the forgetful functor
to the commutative rings preserves them. -/
public theorem isPushout_algebraSiteRings_of_isPullback
    {X Y Z P : algebraSite B} {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback fst snd a b) :
    IsPushout ((algebraSiteRings B).map a.op) ((algebraSiteRings B).map b.op)
      ((algebraSiteRings B).map fst.op) ((algebraSiteRings B).map snd.op) :=
  h.unop.flip.map
    (AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff) ⋙
      forget₂ (CommAlgCat.{u} (A : Type u)) CommRingCat.{u})

/-- The spectrum functor of the algebra site carries a fibre-product square to a fibre-product
square of schemes: on the nose, the square is `Spec` of the pushout square of commutative rings
of `Stacks.Adequate.isPushout_algebraSiteRings_of_isPullback`. -/
public theorem isPullback_algebraSiteScheme_of_isPullback
    {X Y Z P : algebraSite B} {fst : P ⟶ X} {snd : P ⟶ Y} {a : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback fst snd a b) :
    IsPullback ((algebraSiteScheme B).map fst) ((algebraSiteScheme B).map snd)
      ((algebraSiteScheme B).map a) ((algebraSiteScheme B).map b) :=
  AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_algebraSiteRings_of_isPullback B h)

/-- **The spectrum functor of the algebra site preserves fibre products.** Every fibre-product
square of the site is carried to a fibre-product square of schemes by
`Stacks.Adequate.isPullback_algebraSiteScheme_of_isPullback`. -/
public instance preservesLimitsOfShape_algebraSiteScheme :
    PreservesLimitsOfShape WalkingCospan (algebraSiteScheme B) := by
  refine Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback ?_
  intro X Y Z a b _
  exact ⟨_, _, _, IsPullback.of_hasPullback a b,
    isPullback_algebraSiteScheme_of_isPullback B (IsPullback.of_hasPullback a b)⟩

end Site

end Stacks.Adequate

end
