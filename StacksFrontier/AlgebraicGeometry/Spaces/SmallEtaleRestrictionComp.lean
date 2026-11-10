module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRestrictionComp
public import StacksFrontier.CategoryTheory.Adjunction.TransportEquivalence
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# Restriction along a composite of étale morphisms, and Stacks 03LQ

Let `k : X ⟶ Y` and `l : Y ⟶ Z` be étale morphisms of algebraic spaces over a scheme `S`.
Stacks 03LQ identifies the small étale inverse image of an étale morphism `h` with restriction
of sheaves along the postcomposition functor `j_h` of Stacks 03LP, and Stacks 03G2, part (3),
identifies the inverse image of a composite with the composite of the inverse images.  Both
identifications are comparisons of two left adjoints of one functor, and the compatibility
between them — the *bridge* — is

`(k ≫ l)⁻¹ ≅ l⁻¹ ⋙ k⁻¹ ≅ j_l^* ⋙ k⁻¹ ≅ j_l^* ⋙ j_k^* = j_{k ≫ l}^*`,

the composite being the comparison of Stacks 03LQ for `k ≫ l`.  Note that the restriction side
carries no comparison isomorphism at all: `AlgebraicGeometry.Space.smallEtalePostcomp_comp` is
an *equality* of functors of sites, so `j_l^* ⋙ j_k^*` and `j_{k ≫ l}^*` are the same functor.

This file proves the bridge, by the general hexagon
`CategoryTheory.Adjunction.leftAdjointUniq_hom_comp_whisker`: the comparison of two systems of
left adjoints is compatible with composition as soon as the second system's adjunction for the
composite is the composite of its adjunctions, read through the composition isomorphism of the
right adjoints.  Here the two systems are the inverse images, with the adjunctions
`CategoryTheory.MorphismOfTopoi.adj` of Stacks 03G2, part (3), and the restrictions along
postcomposition, with the adjunctions
`AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward`; the shared right adjoint of
each pair is the small étale direct image, which is what makes the hexagon applicable at all.

## Main definitions

* `AlgebraicGeometry.Space.smallToposMorphism_inverseImageUniq`: the comparison of the small
  étale inverse image of an étale morphism with restriction along postcomposition, taken as the
  canonical comparison of two left adjoints of the small étale direct image.

## Main results

* `AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward_comp`: **`hcomp`**, the
  restriction adjunction of a composite is the composite of the restriction adjunctions, read
  through `AlgebraicGeometry.Space.smallToposMorphism_comp`; and
  `AlgebraicGeometry.Space.conjugateEquiv_smallEtalePostcompAdjunctionPushforward`, the same
  in the mate form the spaces-étale statement already proved in
  `StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRestrictionComp` takes.
* `AlgebraicGeometry.Space.smallToposMorphism_inverseImageUniq_comp`: **the bridge** for that
  comparison.
* `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_eq_uniq`: the comparison of
  Stacks 03LQ *is* that canonical comparison.
* `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_comp`: the bridge for the
  comparison `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` of Stacks 03LQ.
* `AlgebraicGeometry.Space.whiskerRight_spacesEtalePostcompSheafComp_inv`: the composition
  comparison of spaces-étale postcomposition restricts to the identity on the étale scheme
  charts — the absorption that the transport of `hcomp` has to perform.

## Implementation notes

The one input of the hexagon is

`hcomp`: `AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward` for `k ≫ l` is the
composite of the ones for `k` and for `l`, with its right adjoint read through
`AlgebraicGeometry.Space.smallToposMorphism_comp`.  Both sides are adjunctions with the *same*
left adjoint and the *same* right adjoint, so this is a unit-and-counit identity.  It says that
the direct-image composition comparison of Stacks 03G2, part (3), is the comparison that
strictness of the Stacks 03LP restriction tower already supplies.

The whole of this statement is already proved on the *spaces-étale* topoi.
`AlgebraicGeometry.Space.conjugateEquiv_spacesEtalePostcompSheafComp` is `hcomp` there, in the
mate form of
`AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward_comp`, and
`AlgebraicGeometry.Space.spacesToposMorphism_inverseImageIso_comp` is the bridge there.  What
this file adds is therefore not the content but its transport along the comparison
equivalences of Stacks 03G1 — and that transport is not formal, for one reason worth
recording: the
composition comparison of postcomposition is *not* strict on the spaces-étale sites, where
`AlgebraicGeometry.Space.spacesEtalePostcompComp` is a `CategoryTheory.Over.mapComp`, whereas
on the small étale sites it is, `AlgebraicGeometry.Space.smallEtalePostcomp_comp` being an
equality.  So the transport has to absorb an `Over.mapComp` into the comparison square
`AlgebraicGeometry.Space.smallEtalePostcompComparisonSquare`.

That absorption is
`AlgebraicGeometry.Space.whiskerRight_spacesEtalePostcompSheafComp_inv`: the spaces-étale
composition comparison becomes the identity once restricted to the étale scheme charts,
because `CategoryTheory.Over.mapComp` is the identity on underlying objects.  With it, and
with the calculus of
`StacksFrontier.CategoryTheory.Adjunction.TransportEquivalence`, the transport of `hcomp` reduces
to a single equation between two natural transformations
`(eZ.inverse ⋙ j_{k≫l}^*) ⋙ eX.functor ⟶ ((eZ.inverse ⋙ j_l^*) ⋙ eY.functor) ⋙
((eY.inverse ⋙ j_k^*) ⋙ eX.functor)`
— writing `e_•` for the Stacks 03G1 equivalences and `j^*` for restriction along spaces-étale
postcomposition.  The two transformations are

* the one the small side produces: the retyping
  `AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward_eq_ofNatIsoLeft` of the
  composite, i.e. `ιL_{k≫l}` followed by the inverse of the horizontal composite of `ιL_l` and
  `ιL_k`, where `ιL_f` is the `CategoryTheory.Iso.inverseCompIso` appearing in that lemma; and
* the one the spaces side produces:
  `(spacesEtalePostcompSheafComp k l).inv` followed by the unit of `e_Y` whiskered into the
  middle, the whole restricted to the charts.

They agree — this is
`AlgebraicGeometry.Space.inverseCompIso_smallEtalePostcompComparisonSquare_comp` — because the
two `e_Z`-counits in the first cancel against each other, `j_l^* ⋙ j_k^*` and `j_{k≫l}^*`
being the *same* functor after restriction to the charts, so that what is left is the
`e_Y`-counit, which is the `e_Y`-unit read through the triangle identity.  Granted that
equation the rest is formal, and is `CategoryTheory.conjugateEquiv_transport_comp_ofNatIsoLeft`:
peel the two outer equivalences with `CategoryTheory.conjugateEquiv_conj`, cancel the inserted
`e_Y.functor ⋙ e_Y.inverse` with `CategoryTheory.conjugateEquiv_comp_equivalence`, split off
`j_k^*` with `CategoryTheory.conjugateEquiv_whiskerRight`, and finish with
`AlgebraicGeometry.Space.conjugateEquiv_spacesEtalePostcompSheafComp`; the answer that comes
out is `AlgebraicGeometry.Space.smallToposMorphism_comp` written out, its first factor being
`MorphismOfTopoi.transport_comp_pushforward` and its second the whiskered
`AlgebraicGeometry.Space.spacesBaseChange_pushforward_comp`.

The second input, that
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` is the canonical comparison of
the two left adjoints, is no longer a hypothesis: it is
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_eq_uniq`.  That comparison is
*built* as the transport along the comparison equivalences of Stacks 03G1 of the corresponding
comparison on the spaces-étale topoi, which is a
`CategoryTheory.Adjunction.leftAdjointUniq`, and
`AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward` is the transport of the
spaces-étale adjunction by the same assembly; so the statement is that the transport of a
comparison of left adjoints is the comparison of the transported left adjoints.  Conjugation
by the equivalences is handled by `CategoryTheory.leftAdjointUniq_transport`, and what it does
not cover is the pair of retypings `CategoryTheory.Adjunction.ofNatIsoLeft` and
`CategoryTheory.Adjunction.ofNatIsoRight` by which that adjunction presents its two adjoints.
Both retypings turn out to be identities for a reason of its own: the one on the right is the
cancellation of an equivalence against its own unit
(`AlgebraicGeometry.Space.smallToposMorphism_comparison_inverseCompIso`), and the one on the
left is the identity because the Stacks 03G1 square for postcomposition is strict
(`AlgebraicGeometry.Space.smallEtalePostcompComparisonSquare_eq_refl`) — a sheaf restricted to
the charts of `X` along postcomposition is literally the sheaf restricted along the composite
functor of sites.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LS](https://stacks.math.columbia.edu/tag/03LS)
-/

@[expose] public noncomputable section

open CategoryTheory

/-! ### A general fact about equivalences

`CategoryTheory.inverseCompIso_unitIso` is a statement about an arbitrary equivalence and
belongs with `CategoryTheory.Iso.inverseCompIso`; it is here only to keep that file
untouched. -/

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- **Cancelling an equivalence against its own unit is the identity.**  The isomorphism
`e.inverse ⋙ K ≅ K'` extracted from the unit comparison `K ≅ e.functor ⋙ (e.inverse ⋙ K)` is
the identity of `e.inverse ⋙ K`, by the triangle identity
`CategoryTheory.Equivalence.unit_inverse_comp`. -/
theorem inverseCompIso_unitIso (e : C ≌ D) (K : C ⥤ E) :
    Iso.inverseCompIso (G := e)
        (Functor.isoWhiskerRight e.unitIso.symm K ≪≫ K.leftUnitor).symm =
      Iso.refl (e.inverse ⋙ K) := by
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  simp [Iso.inverseCompIso_hom_app, Functor.comp_map, ← Functor.map_comp,
    Equivalence.unit_inverse_comp]

end CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- The comparison of the small étale inverse image of an étale morphism with restriction of
sheaves along the postcomposition functor of Stacks 03LP, taken as the canonical comparison of
two left adjoints of the small étale direct image.

`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` is the comparison Stacks 03LQ
supplies; this one is the comparison the adjunctions force, and it is the one for which the
compatibility with composition is formal. -/
def smallToposMorphism_inverseImageUniq (h : X ⟶ Y) (hh : IsEtale B S hS h.hom) :
    (smallToposMorphism B S hS h).inverseImage ≅
      (smallEtalePostcomp B S hS h hh).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1) :=
  Adjunction.leftAdjointUniq (smallToposMorphism B S hS h).adj
    (smallEtalePostcompAdjunctionPushforward B S hS h hh)

/-! ### Stacks 03LQ is the canonical comparison of the two left adjoints -/

/-- **The comparison square of Stacks 03G1 for postcomposition is the identity.**  Restricting
a sheaf on the spaces-étale site of `Y` to the étale charts of `X` is literally the same
functor whether the restriction to charts or the restriction along postcomposition is taken
first, and the comparison
`AlgebraicGeometry.Space.smallEtalePostcompComparisonSquare` between the two is the identity:
the two composites of functors of sites agree on the nose by
`AlgebraicGeometry.Space.comparisonFunctor_smallEtalePostcomp`, so the only thing the
comparison does to a section is to transport it along an identity. -/
theorem smallEtalePostcompComparisonSquare_eq_refl (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    smallEtalePostcompComparisonSquare B S hS f hf = Iso.refl _ := by
  refine Iso.ext ?_
  ext M U : 5
  exact M.obj.map_id _

/-- **The comparison square of Stacks 03G1 for postcomposition is strict on morphisms.**
Restricting a morphism of sheaves on the spaces-étale site of `Y` to the étale charts of `X` is
the same functor whether the restriction to charts or the restriction along postcomposition is
taken first — not merely up to the comparison
`AlgebraicGeometry.Space.smallEtalePostcompComparisonSquare`, but on the nose, because the two
composites of functors of sites agree by
`AlgebraicGeometry.Space.comparisonFunctor_smallEtalePostcomp`. -/
theorem comparisonFunctor_smallEtalePostcomp_map (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    {A A' : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1))} (g : A ⟶ A') :
    ((smallEtalePostcomp B S hS f hf).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)).map
        ((smallEtaleToposEquiv B S hS Y).functor.map g) =
      (smallEtaleToposEquiv B S hS X).functor.map
        (((spacesEtalePostcomp B S hS f hf).sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).map g) := by
  ext U x
  rfl

/-- The isomorphism of right adjoints through which
`AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward` presents the small étale
direct image is the identity: the small étale direct image *is* the conjugate of the
spaces-étale one, and `AlgebraicGeometry.Space.smallToposMorphism_comparison` is the unit
comparison that cancels against it. -/
theorem smallToposMorphism_comparison_inverseCompIso (f : X ⟶ Y) :
    Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS X)
        (smallToposMorphism_comparison B S hS f).symm =
      Iso.refl _ :=
  inverseCompIso_unitIso _ _

/-- `AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward` is the conjugate of the
spaces-étale restriction adjunction by the comparison equivalences of Stacks 03G1, retyped on
the left only: the retyping on the right that its definition performs is the identity, by
`AlgebraicGeometry.Space.smallToposMorphism_comparison_inverseCompIso`. -/
theorem smallEtalePostcompAdjunctionPushforward_eq_ofNatIsoLeft (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    smallEtalePostcompAdjunctionPushforward B S hS f hf =
      (((smallEtaleToposEquiv B S hS Y).symm.toAdjunction.comp
          (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) f hf)).comp
        (smallEtaleToposEquiv B S hS X).toAdjunction).ofNatIsoLeft
          (Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS Y)
            (smallEtalePostcompComparisonSquare B S hS f hf).symm) :=
  (congrArg (fun e => ((((smallEtaleToposEquiv B S hS Y).symm.toAdjunction.comp
            (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) f hf)).comp
          (smallEtaleToposEquiv B S hS X).toAdjunction).ofNatIsoLeft
            (Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS Y)
              (smallEtalePostcompComparisonSquare B S hS f hf).symm)).ofNatIsoRight e)
      (smallToposMorphism_comparison_inverseCompIso B S hS f)).trans
    (Adjunction.ofNatIsoRight_refl _)

/-- The canonical comparison
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageUniq` of the two left adjoints is the
conjugate by the comparison equivalences of Stacks 03G1 of the spaces-étale one, before the
retyping of the left adjoint. -/
theorem smallToposMorphism_inverseImageUniq_eq_transport (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    Adjunction.leftAdjointUniq (smallToposMorphism B S hS f).adj
        (((smallEtaleToposEquiv B S hS Y).symm.toAdjunction.comp
            (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) f hf)).comp
          (smallEtaleToposEquiv B S hS X).toAdjunction) =
      Functor.isoWhiskerLeft (smallEtaleToposEquiv B S hS Y).inverse
        (Functor.isoWhiskerRight (spacesToposMorphism_inverseImageIso B S hS f hf)
          (smallEtaleToposEquiv B S hS X).functor) :=
  leftAdjointUniq_transport _ _ _ _

/-- The comparison `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` Stacks 03LQ
supplies, with the identity comparison square of
`AlgebraicGeometry.Space.smallEtalePostcompComparisonSquare_eq_refl` substituted: it is the
conjugate of the spaces-étale comparison, followed by the retyping of the left adjoint. -/
theorem smallToposMorphism_inverseImageIso_eq_transport (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    smallToposMorphism_inverseImageIso B S hS f hf =
      Functor.isoWhiskerLeft (smallEtaleToposEquiv B S hS Y).inverse
          (Functor.isoWhiskerRight (spacesToposMorphism_inverseImageIso B S hS f hf)
            (smallEtaleToposEquiv B S hS X).functor) ≪≫
        Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS Y)
          (smallEtalePostcompComparisonSquare B S hS f hf).symm := by
  rw [smallEtalePostcompComparisonSquare_eq_refl]
  rfl

/-- **The hypothesis `hθ`: the comparison of Stacks 03LQ is the canonical comparison of the
two left adjoints of the small étale direct image.**

Both sides are assembled from the same spaces-étale data: the Stacks 03LQ comparison is the
transport along the comparison equivalences of Stacks 03G1 of the spaces-étale comparison,
which is itself a `CategoryTheory.Adjunction.leftAdjointUniq`, and
`AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward` is the transport of the
spaces-étale adjunction by the same assembly.  `CategoryTheory.leftAdjointUniq_transport`
says that conjugating by the equivalences only whiskers the comparison, and the two retypings
by which that adjunction presents its adjoints are accounted for by
`AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward_eq_ofNatIsoLeft` and
`CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoLeft`. -/
theorem smallToposMorphism_inverseImageIso_eq_uniq (f : X ⟶ Y) (hf : IsEtale B S hS f.hom) :
    smallToposMorphism_inverseImageIso B S hS f hf =
      smallToposMorphism_inverseImageUniq B S hS f hf :=
  (smallToposMorphism_inverseImageIso_eq_transport B S hS f hf).trans
    ((congrArg (fun i => i ≪≫ Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS Y)
          (smallEtalePostcompComparisonSquare B S hS f hf).symm)
        (smallToposMorphism_inverseImageUniq_eq_transport B S hS f hf).symm).trans
      ((Adjunction.leftAdjointUniq_ofNatIsoLeft (smallToposMorphism B S hS f).adj _ _).symm.trans
        (congrArg (fun a => Adjunction.leftAdjointUniq (smallToposMorphism B S hS f).adj a)
          (smallEtalePostcompAdjunctionPushforward_eq_ofNatIsoLeft B S hS f hf).symm)))

/-! ### The absorption of the spaces-étale composition comparison -/

/-- **The composition comparison of spaces-étale postcomposition disappears on the charts.**

On the spaces-étale sites postcomposition does *not* compose strictly: the comparison
`AlgebraicGeometry.Space.spacesEtalePostcompComp` is a `CategoryTheory.Over.mapComp`.  On the
small étale sites it does, `AlgebraicGeometry.Space.smallEtalePostcomp_comp` being an
equality.  The two are compatible for the following reason: `CategoryTheory.Over.mapComp` is
the *identity* on underlying objects, so restricting
`AlgebraicGeometry.Space.spacesEtalePostcompSheafComp` along the comparison functor of
Stacks 03G1 — that is, evaluating it on the étale scheme charts — gives the identity.

This is the absorption that any transport of a statement about *composites* from the
spaces-étale topoi to the small étale ones has to perform. -/
theorem whiskerRight_spacesEtalePostcompSheafComp_inv (k : X ⟶ Y) (l : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (hl : IsEtale B S hS l.hom) :
    Functor.whiskerRight (spacesEtalePostcompSheafComp B S hS k hk l hl).inv
        (smallEtaleToposEquiv B S hS X).functor = 𝟙 _ := by
  ext M U : 5
  exact M.obj.map_id _

/-- `AlgebraicGeometry.Space.whiskerRight_spacesEtalePostcompSheafComp_inv` whiskered on the
other side as well, which is the form in which the transport of a composite meets it. -/
theorem whiskerRight_whiskerLeft_spacesEtalePostcompSheafComp_inv (k : X ⟶ Y) (l : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (hl : IsEtale B S hS l.hom) :
    Functor.whiskerRight
        (Functor.whiskerLeft (smallEtaleToposEquiv B S hS Z).inverse
          (spacesEtalePostcompSheafComp B S hS k hk l hl).inv)
        (smallEtaleToposEquiv B S hS X).functor = 𝟙 _ := by
  ext M U : 5
  exact ((smallEtaleToposEquiv B S hS Z).inverse.obj M).obj.map_id _

/-- **The retyping of the left adjoints, on the small side, is the spaces-étale composition
comparison followed by the unit of the comparison equivalence of `Y`.**

On the left: the comparison square of Stacks 03G1 for `k ≫ l`, read through
`CategoryTheory.Iso.inverseCompIso` as an isomorphism of the transported left adjoint with
restriction along small étale postcomposition, then — through the identity, which is the whole
content of the strictness of the Stacks 03LP tower: restriction along the composite *is* the
composite of the restrictions — the inverse of the horizontal composite of the same two
comparisons for `l` and for `k`.  On the right: the spaces-étale composition comparison
`AlgebraicGeometry.Space.spacesEtalePostcompSheafComp`, restricted to the charts, followed by
the unit of the comparison equivalence of `Y` inserted in the middle.

This is the one statement that the transport of the composition compatibility from the
spaces-étale topoi to the small étale ones is not formal about, and it holds for three
reasons: the spaces-étale comparison contributes nothing, by
`AlgebraicGeometry.Space.whiskerRight_whiskerLeft_spacesEtalePostcompSheafComp_inv`; the two
counits of the comparison equivalence of `Z` that the left side produces cancel against each
other; and the remaining counit of the comparison equivalence of `Y` is its unit, by the
triangle identity `CategoryTheory.Equivalence.counitInv_app_functor`. -/
theorem inverseCompIso_smallEtalePostcompComparisonSquare_comp (k : X ⟶ Y) (l : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (hl : IsEtale B S hS l.hom)
    (hkl : IsEtale B S hS (k ≫ l).hom) :
    (Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS Z)
          (smallEtalePostcompComparisonSquare B S hS (k ≫ l) hkl).symm).hom ≫
        𝟙 ((smallEtalePostcomp B S hS (k ≫ l) hkl).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1)) ≫
          (Functor.isoWhiskerLeft
              (((smallEtaleToposEquiv B S hS Z).inverse ⋙
                  (spacesEtalePostcomp B S hS l hl).sheafPushforwardContinuous (Type (u + 1))
                    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Z)) ⋙
                (smallEtaleToposEquiv B S hS Y).functor)
              (Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS Y)
                (smallEtalePostcompComparisonSquare B S hS k hk).symm) ≪≫
            Functor.isoWhiskerRight
              (Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS Z)
                (smallEtalePostcompComparisonSquare B S hS l hl).symm)
              ((smallEtalePostcomp B S hS k hk).sheafPushforwardContinuous (Type (u + 1))
                (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1))).inv =
      Functor.whiskerRight
          (Functor.whiskerLeft (smallEtaleToposEquiv B S hS Z).inverse
            (spacesEtalePostcompSheafComp B S hS k hk l hl).inv)
          (smallEtaleToposEquiv B S hS X).functor ≫
        Functor.whiskerLeft
          ((smallEtaleToposEquiv B S hS Z).inverse ⋙
            (spacesEtalePostcomp B S hS l hl).sheafPushforwardContinuous (Type (u + 1))
              (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Z))
          (Functor.whiskerRight (smallEtaleToposEquiv B S hS Y).unit
            ((spacesEtalePostcomp B S hS k hk).sheafPushforwardContinuous (Type (u + 1))
                (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
              (smallEtaleToposEquiv B S hS X).functor)) := by
  ext M : 2
  have h0 : (smallEtaleToposEquiv B S hS X).functor.map
      ((spacesEtalePostcompSheafComp B S hS k hk l hl).inv.app
        ((smallEtaleToposEquiv B S hS Z).inverse.obj M)) = 𝟙 _ :=
    NatTrans.congr_app
      (whiskerRight_whiskerLeft_spacesEtalePostcompSheafComp_inv B S hS k l hk hl) M
  change (Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS Z)
          (smallEtalePostcompComparisonSquare B S hS (k ≫ l) hkl).symm).hom.app M ≫
      ((smallEtalePostcomp B S hS k hk).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)).map
          ((Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS Z)
            (smallEtalePostcompComparisonSquare B S hS l hl).symm).inv.app M) ≫
        (Iso.inverseCompIso (G := smallEtaleToposEquiv B S hS Y)
            (smallEtalePostcompComparisonSquare B S hS k hk).symm).inv.app
          ((smallEtaleToposEquiv B S hS Y).functor.obj
            (((spacesEtalePostcomp B S hS l hl).sheafPushforwardContinuous (Type (u + 1))
                (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Z)).obj
              ((smallEtaleToposEquiv B S hS Z).inverse.obj M))) =
    (smallEtaleToposEquiv B S hS X).functor.map
        ((spacesEtalePostcompSheafComp B S hS k hk l hl).inv.app
          ((smallEtaleToposEquiv B S hS Z).inverse.obj M)) ≫
      (smallEtaleToposEquiv B S hS X).functor.map
        (((spacesEtalePostcomp B S hS k hk).sheafPushforwardContinuous (Type (u + 1))
              (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)).map
          ((smallEtaleToposEquiv B S hS Y).unit.app
            (((spacesEtalePostcomp B S hS l hl).sheafPushforwardContinuous (Type (u + 1))
                (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Z)).obj
              ((smallEtaleToposEquiv B S hS Z).inverse.obj M))))
  rw [h0]
  refine Eq.trans ?_ (Category.id_comp _).symm
  simp only [smallEtalePostcompComparisonSquare_eq_refl]
  change ((smallEtalePostcomp B S hS k hk).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)).map
        (((smallEtalePostcomp B S hS l hl).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Z.1)).map
          ((smallEtaleToposEquiv B S hS Z).counitIso.hom.app M)) ≫
      ((smallEtalePostcomp B S hS k hk).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)).map
          (((smallEtalePostcomp B S hS l hl).sheafPushforwardContinuous (Type (u + 1))
              (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Z.1)).map
            ((smallEtaleToposEquiv B S hS Z).counitIso.inv.app M)) ≫
        ((smallEtalePostcomp B S hS k hk).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)).map
          ((smallEtaleToposEquiv B S hS Y).counitIso.inv.app
            ((smallEtaleToposEquiv B S hS Y).functor.obj
              (((spacesEtalePostcomp B S hS l hl).sheafPushforwardContinuous (Type (u + 1))
                  (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Z)).obj
                ((smallEtaleToposEquiv B S hS Z).inverse.obj M)))) = _
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Equivalence.counitInv_app_functor]
  exact comparisonFunctor_smallEtalePostcomp_map B S hS k hk _

/-- **The direct-image composition comparison of Stacks 03G2, part (3), is the comparison the
Stacks 03LP tower supplies**, in *mate* form: the mate of the identity of the left adjoint
shared by the two adjunctions is
`AlgebraicGeometry.Space.smallToposMorphism_comp`.

This is the transport along the comparison equivalences of Stacks 03G1 of
`AlgebraicGeometry.Space.conjugateEquiv_spacesEtalePostcompSheafComp`, the same statement on
the spaces-étale topoi.  The transport is
`CategoryTheory.conjugateEquiv_transport_comp_ofNatIsoLeft`, whose one non-formal input is
`AlgebraicGeometry.Space.inverseCompIso_smallEtalePostcompComparisonSquare_comp`. -/
theorem conjugateEquiv_smallEtalePostcompAdjunctionPushforward (k : X ⟶ Y) (l : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (hl : IsEtale B S hS l.hom)
    (hkl : IsEtale B S hS (k ≫ l).hom) :
    conjugateEquiv
        ((smallEtalePostcompAdjunctionPushforward B S hS l hl).comp
          (smallEtalePostcompAdjunctionPushforward B S hS k hk))
        (smallEtalePostcompAdjunctionPushforward B S hS (k ≫ l) hkl)
        (𝟙 ((smallEtalePostcomp B S hS (k ≫ l) hkl).sheafPushforwardContinuous (Type (u + 1))
          (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Z.1))) =
      (smallToposMorphism_comp B S hS k l).hom := by
  rw [smallEtalePostcompAdjunctionPushforward_eq_ofNatIsoLeft B S hS k hk,
    smallEtalePostcompAdjunctionPushforward_eq_ofNatIsoLeft B S hS l hl,
    smallEtalePostcompAdjunctionPushforward_eq_ofNatIsoLeft B S hS (k ≫ l) hkl]
  refine Eq.trans (conjugateEquiv_transport_comp_ofNatIsoLeft
    (smallEtaleToposEquiv B S hS X) (smallEtaleToposEquiv B S hS Y)
      (smallEtaleToposEquiv B S hS Z)
    (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) k hk)
    (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) l hl)
    (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) (k ≫ l) hkl)
    (spacesEtalePostcompSheafComp B S hS k hk l hl).inv _ _ _ _
    (inverseCompIso_smallEtalePostcompComparisonSquare_comp B S hS k l hk hl hkl)) ?_
  rw [conjugateEquiv_spacesEtalePostcompSheafComp B S hS k hk l hl]
  rfl

/-- **The hypothesis `hcomp`**: the restriction adjunction of Stacks 03LP for a composite is
the composite of the restriction adjunctions, read through
`AlgebraicGeometry.Space.smallToposMorphism_comp`.

Both sides are adjunctions with the same left and the same right adjoint, so this is a unit
identity, and `CategoryTheory.Adjunction.eq_ofNatIsoRight_of_conjugateEquiv_id` turns it into
the mate identity
`AlgebraicGeometry.Space.conjugateEquiv_smallEtalePostcompAdjunctionPushforward`. -/
theorem smallEtalePostcompAdjunctionPushforward_comp (k : X ⟶ Y) (l : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (hl : IsEtale B S hS l.hom)
    (hkl : IsEtale B S hS (k ≫ l).hom) :
    smallEtalePostcompAdjunctionPushforward B S hS (k ≫ l) hkl =
      ((smallEtalePostcompAdjunctionPushforward B S hS l hl).comp
        (smallEtalePostcompAdjunctionPushforward B S hS k hk)).ofNatIsoRight
          (smallToposMorphism_comp B S hS k l) :=
  Adjunction.eq_ofNatIsoRight_of_conjugateEquiv_id _ _ _
    (conjugateEquiv_smallEtalePostcompAdjunctionPushforward B S hS k l hk hl hkl)

/-- **The bridge between Stacks 03LQ and Stacks 03G2, part (3)**, for the canonical comparison
of two left adjoints: the inverse-image composition isomorphism of a composite of two étale
morphisms, followed by the two comparisons with restriction along postcomposition, is the
comparison for the composite.  Nothing is inserted on the restriction side, because
postcomposition composes strictly.

This is the hexagon
`CategoryTheory.Adjunction.leftAdjointUniq_hom_comp_whisker` at the two systems of adjunctions,
`AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage` being by definition the
comparison of left adjoints induced by
`AlgebraicGeometry.Space.smallToposMorphism_comp`, with
`AlgebraicGeometry.Space.smallEtalePostcompAdjunctionPushforward_comp` for its hypothesis. -/
theorem smallToposMorphism_inverseImageUniq_comp (k : X ⟶ Y) (l : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (hl : IsEtale B S hS l.hom)
    (hkl : IsEtale B S hS (k ≫ l).hom) :
    (smallToposMorphism_comp_inverseImage B S hS k l).hom ≫
        Functor.whiskerRight (smallToposMorphism_inverseImageUniq B S hS l hl).hom
          (smallToposMorphism B S hS k).inverseImage ≫
        Functor.whiskerLeft
          ((smallEtalePostcomp B S hS l hl).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Z.1))
          (smallToposMorphism_inverseImageUniq B S hS k hk).hom =
      (smallToposMorphism_inverseImageUniq B S hS (k ≫ l) hkl).hom :=
  Adjunction.leftAdjointUniq_hom_comp_whisker _ _ _ _ _ _ _
    (smallEtalePostcompAdjunctionPushforward_comp B S hS k l hk hl hkl)

/-- **The bridge between Stacks 03LQ and Stacks 03G2, part (3)**, for the comparison
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` that Stacks 03LQ supplies.

This is `AlgebraicGeometry.Space.smallToposMorphism_inverseImageUniq_comp` together with
`AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso_eq_uniq`, which identifies that
comparison with the canonical one. -/
theorem smallToposMorphism_inverseImageIso_comp (k : X ⟶ Y) (l : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom) (hl : IsEtale B S hS l.hom)
    (hkl : IsEtale B S hS (k ≫ l).hom) :
    (smallToposMorphism_comp_inverseImage B S hS k l).hom ≫
        Functor.whiskerRight (smallToposMorphism_inverseImageIso B S hS l hl).hom
          (smallToposMorphism B S hS k).inverseImage ≫
        Functor.whiskerLeft
          ((smallEtalePostcomp B S hS l hl).sheafPushforwardContinuous (Type (u + 1))
            (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Z.1))
          (smallToposMorphism_inverseImageIso B S hS k hk).hom =
      (smallToposMorphism_inverseImageIso B S hS (k ≫ l) hkl).hom := by
  rw [smallToposMorphism_inverseImageIso_eq_uniq B S hS k hk,
    smallToposMorphism_inverseImageIso_eq_uniq B S hS l hl,
    smallToposMorphism_inverseImageIso_eq_uniq B S hS (k ≫ l) hkl]
  exact smallToposMorphism_inverseImageUniq_comp B S hS k l hk hl hkl

end AlgebraicGeometry.Space

end
