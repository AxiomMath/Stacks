module

public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.GroupoidRestriction

/-!
# Composing two successive restrictions on quotient sheaves

Let `G` be a groupoid scheme with scheme of objects `U`, let `g₁ : U₁ ⟶ U` be a morphism and
`H₁` a restriction of `G` along it, and let `g' : U' ⟶ U₁` be a morphism and `H'` a restriction
of `H₁.groupoid` along it.  Writing `g : U' ⟶ U` for the composite, this file shows that the
map `U'/R|_{U'} ⟶ U/R` of quotient sheaves is an isomorphism as soon as the two maps
`U₁/R|_{U₁} ⟶ U/R` and `U'/(R|_{U₁})|_{U'} ⟶ U₁/R|_{U₁}` of the two stages are.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isIso_restrictionQuotientMap_of_comp`: the map of quotient
  sheaves induced by the restriction along a composite is an isomorphism when the two stages
  induce isomorphisms.
* `AlgebraicGeometry.GroupoidScheme.isIso_restrictionQuotientMap_of_comp_reach`: the same
  conclusion from local surjectivity of the two stages' reach maps.

## Implementation notes

Two successive restrictions do not visibly collapse to one: the restriction of `G` along the
composite `g` has arrow scheme `U' ×_{g, U, t} R ×_{s, U, g} U'`, while the restriction of
`H₁.groupoid` along `g'` has arrow scheme `U' ×_{g', U₁, t₁} R₁ ×_{s₁, U₁, g'} U'` for the
arrow scheme `R₁` of `H₁.groupoid`, and a restriction is moreover given abstractly, by its
structure maps together with equalities identifying them with the displayed fibre products.
Neither is the criterion of Stacks 02VH applicable to `g` in one step: the reach map of the
composite is the reach map of the first stage precomposed with a base change of `g'`, so it is
not a covering even when both stages' reach maps are.

What makes the composition go through without any comparison of arrow schemes is that
injectivity of the map of quotient sheaves is unconditional, by Stacks 045Z and hence
`AlgebraicGeometry.GroupoidScheme.mono_restrictionQuotientMap`, so only surjectivity has to be
transported.  The projection onto a quotient sheaf is locally surjective, so the composite of
the two stages' maps witnesses that the projection onto `U/R`, precomposed with the functor of
points of `U'`, is locally surjective; since the two stages' object maps compose to the object
map of the restriction along `g` up to the canonical identification of the two schemes of
objects with `U'`, that is exactly a factorization through the map of quotient sheaves of the
composite, which therefore is locally surjective and so an epimorphism.

## References

* [Stacks Project, Tag 045Z](https://stacks.math.columbia.edu/tag/045Z)
* [Stacks Project, Tag 02VH](https://stacks.math.columbia.edu/tag/02VH)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u v w

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- The map of quotient sheaves induced by a restriction commutes with the projections onto the
quotient sheaves, over the map on schemes of objects. -/
private theorem toQuotientSheaf_comp_restrictionQuotientMap
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects) (H : Restriction G g) :
    toQuotientSheaf J F (groupoidPreRelation H.groupoid) ≫
        (restrictionQuotientMap J F G g H).hom =
      F.op.whiskerLeft (yoneda.map H.hom.mapObjects) ≫
        toQuotientSheaf J F (groupoidPreRelation G) := by
  have hs : H.hom.mapArrows ≫ (groupoidPreRelation G).source =
      (groupoidPreRelation H.groupoid).source ≫ H.hom.mapObjects := by
    simpa [groupoidPreRelation, PreRelation.source] using H.hom.map_source
  have ht : H.hom.mapArrows ≫ (groupoidPreRelation G).target =
      (groupoidPreRelation H.groupoid).target ≫ H.hom.mapObjects := by
    simpa [groupoidPreRelation, PreRelation.target] using H.hom.map_target
  exact toQuotientSheaf_comp_quotientSheafMap J F (groupoidPreRelation H.groupoid)
    (groupoidPreRelation G) H.hom.mapArrows H.hom.mapObjects hs ht

/-- **Composing two successive restrictions on quotient sheaves.** Let `H₁` be a restriction of
`G` along `g₁ : U₁ ⟶ U` and `H'` a restriction of `H₁.groupoid` along `g' : U' ⟶ U₁`, and let
`g : U' ⟶ U` be the composite of `g'` with the map on objects of `H₁`. If the two stages induce
isomorphisms of quotient sheaves, then so does the restriction of `G` along `g`.

This is the step of the proof of **Stacks 0489** which passes to the quotient twice and composes
the two resulting isomorphisms; the conclusion is about the restriction along the single
morphism `U' ⟶ U` that the statement of that tag names. -/
theorem isIso_restrictionQuotientMap_of_comp
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    (G : GroupoidScheme S) {U₁ : Over S} (g₁ : U₁ ⟶ G.objects) (H₁ : Restriction G g₁)
    {U' : Over S} (g' : U' ⟶ H₁.groupoid.objects) (H' : Restriction H₁.groupoid g')
    (g : U' ⟶ G.objects) (hg : g = g' ≫ H₁.hom.mapObjects) (H : Restriction G g)
    (h₁ : IsIso (restrictionQuotientMap J F G g₁ H₁))
    (h' : IsIso (restrictionQuotientMap J F H₁.groupoid g' H')) :
    IsIso (restrictionQuotientMap J F G g H) := by
  have _ := h₁
  have _ := h'
  -- the two schemes of objects are both `U'`, canonically
  have hobj : H'.groupoid.objects = H.groupoid.objects :=
    H'.objects_eq.trans H.objects_eq.symm
  -- the two stages' maps on objects compose to the map on objects of the restriction along `g`
  have hmap : eqToHom hobj ≫ H.hom.mapObjects =
      H'.hom.mapObjects ≫ H₁.hom.mapObjects :=
    calc eqToHom hobj ≫ H.hom.mapObjects
        = eqToHom hobj ≫ eqToHom H.objects_eq ≫ g := by rw [H.mapObjects_eq]
      _ = eqToHom H'.objects_eq ≫ g := by rw [← Category.assoc, eqToHom_trans]
      _ = eqToHom H'.objects_eq ≫ g' ≫ H₁.hom.mapObjects := by rw [hg]
      _ = H'.hom.mapObjects ≫ H₁.hom.mapObjects := by
          rw [H'.mapObjects_eq, Category.assoc]
  -- the same, whiskered into the functors of points
  have hwl : F.op.whiskerLeft (yoneda.map H'.hom.mapObjects) ≫
        F.op.whiskerLeft (yoneda.map H₁.hom.mapObjects) =
      F.op.whiskerLeft (yoneda.map (eqToHom hobj)) ≫
        F.op.whiskerLeft (yoneda.map H.hom.mapObjects) := by
    rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp, ← Functor.map_comp,
      ← Functor.map_comp, hmap]
  have hwl' : F.op.whiskerLeft (yoneda.map H'.hom.mapObjects) ≫
        F.op.whiskerLeft (yoneda.map H₁.hom.mapObjects) ≫
          toQuotientSheaf J F (groupoidPreRelation G) =
      F.op.whiskerLeft (yoneda.map (eqToHom hobj)) ≫
        F.op.whiskerLeft (yoneda.map H.hom.mapObjects) ≫
          toQuotientSheaf J F (groupoidPreRelation G) := by
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ toQuotientSheaf J F (groupoidPreRelation G)) hwl
  -- the composite of the two stages' maps of quotient sheaves, read on the projections
  have key : toQuotientSheaf J F (groupoidPreRelation H'.groupoid) ≫
        (restrictionQuotientMap J F H₁.groupoid g' H' ≫
          restrictionQuotientMap J F G g₁ H₁).hom =
      F.op.whiskerLeft (yoneda.map (eqToHom hobj)) ≫
        toQuotientSheaf J F (groupoidPreRelation H.groupoid) ≫
          (restrictionQuotientMap J F G g H).hom :=
    calc toQuotientSheaf J F (groupoidPreRelation H'.groupoid) ≫
          (restrictionQuotientMap J F H₁.groupoid g' H' ≫
            restrictionQuotientMap J F G g₁ H₁).hom
        = (toQuotientSheaf J F (groupoidPreRelation H'.groupoid) ≫
            (restrictionQuotientMap J F H₁.groupoid g' H').hom) ≫
            (restrictionQuotientMap J F G g₁ H₁).hom :=
          (Category.assoc _ _ _).symm
      _ = (F.op.whiskerLeft (yoneda.map H'.hom.mapObjects) ≫
            toQuotientSheaf J F (groupoidPreRelation H₁.groupoid)) ≫
            (restrictionQuotientMap J F G g₁ H₁).hom :=
          congrArg (fun k => k ≫ (restrictionQuotientMap J F G g₁ H₁).hom)
            (toQuotientSheaf_comp_restrictionQuotientMap J F H₁.groupoid g' H')
      _ = F.op.whiskerLeft (yoneda.map H'.hom.mapObjects) ≫
            toQuotientSheaf J F (groupoidPreRelation H₁.groupoid) ≫
              (restrictionQuotientMap J F G g₁ H₁).hom := Category.assoc _ _ _
      _ = F.op.whiskerLeft (yoneda.map H'.hom.mapObjects) ≫
            F.op.whiskerLeft (yoneda.map H₁.hom.mapObjects) ≫
              toQuotientSheaf J F (groupoidPreRelation G) :=
          congrArg (fun k => F.op.whiskerLeft (yoneda.map H'.hom.mapObjects) ≫ k)
            (toQuotientSheaf_comp_restrictionQuotientMap J F G g₁ H₁)
      _ = F.op.whiskerLeft (yoneda.map (eqToHom hobj)) ≫
            F.op.whiskerLeft (yoneda.map H.hom.mapObjects) ≫
              toQuotientSheaf J F (groupoidPreRelation G) := hwl'
      _ = F.op.whiskerLeft (yoneda.map (eqToHom hobj)) ≫
            toQuotientSheaf J F (groupoidPreRelation H.groupoid) ≫
              (restrictionQuotientMap J F G g H).hom :=
          congrArg (fun k => F.op.whiskerLeft (yoneda.map (eqToHom hobj)) ≫ k)
            (toQuotientSheaf_comp_restrictionQuotientMap J F G g H).symm
  -- the left-hand side of `key` is locally surjective, being a projection followed by an
  -- isomorphism
  have _ : Presheaf.IsLocallySurjective J
      (toQuotientSheaf J F (groupoidPreRelation H'.groupoid)) :=
    isLocallySurjective_toQuotientSheaf J F _
  have _ : Presheaf.IsLocallySurjective J
      ((restrictionQuotientMap J F H₁.groupoid g' H' ≫
        restrictionQuotientMap J F G g₁ H₁).hom) :=
    inferInstanceAs (Sheaf.IsLocallySurjective (restrictionQuotientMap J F H₁.groupoid g' H' ≫
      restrictionQuotientMap J F G g₁ H₁))
  have hlhs : Presheaf.IsLocallySurjective J
      (toQuotientSheaf J F (groupoidPreRelation H'.groupoid) ≫
        (restrictionQuotientMap J F H₁.groupoid g' H' ≫
          restrictionQuotientMap J F G g₁ H₁).hom) := inferInstance
  -- hence so is the map of quotient sheaves of the composite, after the projection
  have hmid : Presheaf.IsLocallySurjective J
      (toQuotientSheaf J F (groupoidPreRelation H.groupoid) ≫
        (restrictionQuotientMap J F G g H).hom) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J key.symm
  have hiso : Presheaf.IsLocallySurjective J ((restrictionQuotientMap J F G g H).hom) :=
    Presheaf.isLocallySurjective_of_isLocallySurjective J
      (toQuotientSheaf J F (groupoidPreRelation H.groupoid)) _
  have _ : Epi (restrictionQuotientMap J F G g H) :=
    (Sheaf.isLocallySurjective_iff_epi (restrictionQuotientMap J F G g H)).mp hiso
  have _ : Mono (restrictionQuotientMap J F G g H) := mono_restrictionQuotientMap J F G g H
  exact isIso_of_mono_of_epi (restrictionQuotientMap J F G g H)

/-- **Composing two successive restrictions on quotient sheaves, from the reach maps.** If the
reach map of the first stage and the reach map of the second stage are both locally surjective
after sheafification, then the restriction of `G` along the composite induces an isomorphism of
quotient sheaves.

In the proof of **Stacks 0489** the two reach maps are fppf coverings — the first by Step 1 and
the second by Steps 2 and 3 — and this is how the two applications of Stacks 02VH in that proof
combine into the single isomorphism its statement asks for. -/
theorem isIso_restrictionQuotientMap_of_comp_reach
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S)
    (G : GroupoidScheme S) {U₁ : Over S} (g₁ : U₁ ⟶ G.objects) (H₁ : Restriction G g₁)
    {U' : Over S} (g' : U' ⟶ H₁.groupoid.objects) (H' : Restriction H₁.groupoid g')
    (g : U' ⟶ G.objects) (hg : g = g' ≫ H₁.hom.mapObjects) (H : Restriction G g)
    (hreach₁ : Sheaf.IsLocallySurjective ((presheafToSheaf J (Type u)).map
      (F.op.whiskerLeft (yoneda.map (restrictionReachMap G g₁)))))
    (hreach' : Sheaf.IsLocallySurjective ((presheafToSheaf J (Type u)).map
      (F.op.whiskerLeft (yoneda.map (restrictionReachMap H₁.groupoid g'))))) :
    IsIso (restrictionQuotientMap J F G g H) :=
  isIso_restrictionQuotientMap_of_comp J F G g₁ H₁ g' H' g hg H
    (isIso_restrictionQuotientMap_of_reach J F G g₁ H₁ hreach₁)
    (isIso_restrictionQuotientMap_of_reach J F H₁.groupoid g' H' hreach')

end AlgebraicGeometry.GroupoidScheme

end
