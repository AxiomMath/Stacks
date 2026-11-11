module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentedPointRestrictionProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatQuotientStackAlgebraic

/-!
# A quotient stack is algebraic exactly when a restriction is flat and finitely presented

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site. **Stacks 06PJ** states that the quotient stack `[U/R]` is an
algebraic stack if and only if there is a morphism `g : U' ⟶ U` of algebraic spaces over `S` such
that

1. the saturation map `U' ×_{g, U, t} R ⟶ R ⟶ U` is a surjection of fppf sheaves, and
2. the source and target of the restriction of `(U, R, s, t, c)` along `g` are flat and locally of
   finite presentation.

This file proves both implications.

## Main results

* `AlgebraicGeometry.Stack.prop_restrictionSource_of_schemePresentationHom`: every relative
  property of the 1-morphism `𝒮_V ⟶ [U/R]` presented by `g` is a property of the source
  `R' ⟶ U'` of the restriction along `g`, as soon as the saturation map of `g` is a surjection of
  fppf sheaves.
* `AlgebraicGeometry.Stack.exists_restrictionAlong_of_isAlgebraicStack`: the converse
  implication of Stacks 06PJ.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_isAlgebraicStack_restrict`: if the
  quotient stack of the restriction along `g` is algebraic, so is `[U/R]`.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_restrictionAlong_of_flat`: the
  forward implication of Stacks 06PJ.
* `AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_iff_restrictionAlong`: Stacks 06PJ.

The forward implication for a groupoid exhibited as a restriction by an arbitrary morphism of
groupoids, rather than the canonical restriction of Stacks 044B, is
`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStack_of_restriction` in
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.GroupoidPresentationQuotientAlgebraic`.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 046S](https://stacks.math.columbia.edu/tag/046S)
* [Stacks Project, Tag 046T](https://stacks.math.columbia.edu/tag/046T)
* [Stacks Project, Tag 04M9](https://stacks.math.columbia.edu/tag/04M9)
* [Stacks Project, Tag 06FI](https://stacks.math.columbia.edu/tag/06FI)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w t

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **The saturation map of the canonical restriction is that of `g`.** The object map of the
morphism `(U', R', s', t', c') ⟶ (U, R, s, t, c)` of the canonical restriction along `g` is `g`
precomposed with the transport attached to the identification of the object space of the
restriction with `U'`, so its saturation map is a surjection of fppf sheaves as soon as that of
`g` is. -/
theorem isLocallySurjective_saturation_restrict
    (G : GroupoidInAlgebraicSpaces C S hS B) {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hsat : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source).hom)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd (ObjectProperty.homMk
        (GroupoidInAlgebraicSpaces.restrict G g).hom.toGroupoidHom.mapObjects :
          (GroupoidInAlgebraicSpaces.restrict G g).groupoid.objects ⟶ G.objects)
        G.target ≫ G.source).hom) := by
  have hmo : (ObjectProperty.homMk
      (GroupoidInAlgebraicSpaces.restrict G g).hom.toGroupoidHom.mapObjects :
      (GroupoidInAlgebraicSpaces.restrict G g).groupoid.objects ⟶ G.objects) =
      eqToHom (GroupoidInAlgebraicSpaces.restrict G g).objects_eq ≫ g :=
    ObjectProperty.hom_ext _ (GroupoidInAlgebraicSpaces.restrict G g).mapObjects_eq
  rw [hmo]
  let a := (eqToHom (GroupoidInAlgebraicSpaces.restrict G g).objects_eq).hom
  have e : pullback.snd (a ≫ g.hom) G.target.hom ≫ G.source.hom =
      pullback.map (a ≫ g.hom) G.target.hom g.hom G.target.hom a (𝟙 _) (𝟙 _) (by simp)
        (by simp) ≫ pullback.snd g.hom G.target.hom ≫ G.source.hom := by
    simp
  have : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (pullback.snd g.hom G.target.hom ≫ G.source.hom) := hsat
  change Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
    (pullback.snd (a ≫ g.hom) G.target.hom ≫ G.source.hom)
  rw [e]
  infer_instance

/-- **Every relative property of a presented point is a property of the source of the restriction
along it.** Let `P` be a property of morphisms of algebraic spaces over `S` stable under base
change and local on the target for the fppf precoverage, let `g : U' ⟶ U` be a morphism out of the
algebraic space of a scheme `V` of the site whose saturation map `U' ×_{g, U, t} R ⟶ R ⟶ U` is a
surjection of fppf sheaves, and suppose the presentation 1-morphism `𝒮_V ⟶ [U/R]` of Stacks 026O
at `g` satisfies the condition of Stacks 03YK at `P`. Then the source `R' ⟶ U'` of the restriction
of `(U, R, s, t, c)` along `g` has `P`. -/
theorem prop_restrictionSource_of_schemePresentationHom
    (P : MorphismProperty (AlgebraicSpaces C S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, max u t} C S hS)]
    (G : GroupoidInAlgebraicSpaces C S hS B) (V : BigFppfOver C S hS)
    (g : schemeSpace V ⟶ G.objects)
    (hsat : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source).hom))
    (hP : ChartRelativeProperty C S hS P (schemePresentationHom g.hom)) :
    P (GroupoidInAlgebraicSpaces.restrictionSource G g) := by
  obtain ⟨e⟩ := (quotientStackMap_isEquivalenceOver_iff
    (GroupoidInAlgebraicSpaces.restrict G g).hom).mpr
      ⟨isPullback_mapArrows_of_evaluation_fullyFaithful _ (fun T =>
        ((GroupoidInAlgebraicSpaces.restrict G g).evaluation_fullyFaithful T).some),
        isLocallySurjective_saturation_restrict G g hsat⟩
  have hk : Functor.IsEquivalence
      (quotientStackMap (GroupoidInAlgebraicSpaces.restrict G g).hom).toFunctor :=
    Functor.IsEquivalence.mk' e.inv e.unitIso.symm e.counitIso
  have hcomp : (eqToHom (GroupoidInAlgebraicSpaces.restrict G g).objects_eq.symm).hom ≫
      (GroupoidInAlgebraicSpaces.restrict G g).hom.toGroupoidHom.mapObjects = g.hom := by
    have h1 : (eqToHom (GroupoidInAlgebraicSpaces.restrict G g).objects_eq.symm :
          schemeSpace V ⟶
            (GroupoidInAlgebraicSpaces.restrict G g).groupoid.objects) ≫
        (eqToHom (GroupoidInAlgebraicSpaces.restrict G g).objects_eq ≫ g) = g := by
      rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    exact (congrArg (fun m =>
      (eqToHom (GroupoidInAlgebraicSpaces.restrict G g).objects_eq.symm).hom ≫ m)
        (GroupoidInAlgebraicSpaces.restrict G g).mapObjects_eq).trans
      (congrArg (fun k : schemeSpace V ⟶ G.objects => k.hom) h1)
  have hH : ChartRelativeProperty C S hS P
      (schemePresentationHom (G := (GroupoidInAlgebraicSpaces.restrict G g).groupoid)
        (eqToHom (GroupoidInAlgebraicSpaces.restrict G g).objects_eq.symm).hom) :=
    chartRelativeProperty_of_comp_equivalence P _
      (quotientStackMap (GroupoidInAlgebraicSpaces.restrict G g).hom) hk <|
      chartRelativeProperty_congr_twoIso P
      ((eqToIso (congrArg (fun k : yoneda.obj V ⟶ G.objects.obj =>
          schemePresentationHom (G := G) k) hcomp)).symm ≪≫
        schemePresentationHomQuotientStackMapIso (GroupoidInAlgebraicSpaces.restrict G g).hom
          (eqToHom (GroupoidInAlgebraicSpaces.restrict G g).objects_eq.symm).hom) hP
  have hsrc : P (GroupoidInAlgebraicSpaces.restrict G g).groupoid.source :=
    prop_source_of_relativeProperty_quotientStackProjectionHom.{u, t} P _
      (relativeProperty_quotientStackProjectionHom_of_schemePresentationHom P
        (GroupoidInAlgebraicSpaces.restrict G g).objects_eq hH)
  simpa only [(GroupoidInAlgebraicSpaces.restrict G g).source_eq, P.cancel_left_of_respectsIso,
    P.cancel_right_of_respectsIso] using hsrc

/-- **The converse implication of Stacks 06PJ.** If the quotient stack `[U/R]` of a groupoid in
algebraic spaces over `B` is an algebraic stack, then there is a morphism `g : U' ⟶ U` of
algebraic spaces over `S` whose saturation map `U' ×_{g, U, t} R ⟶ R ⟶ U` is a surjection of fppf
sheaves and whose restriction `(U', R', s', t', c')` has flat, locally finitely presented source
and target. -/
theorem exists_restrictionAlong_of_isAlgebraicStack
    (G : GroupoidInAlgebraicSpaces C S hS B)
    (h𝒳 : IsAlgebraicStack.{u, w} C S hS (quotientStack G)) :
    ∃ (U' : AlgebraicSpaces C S hS) (g : U' ⟶ G.objects),
      Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
        ((GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source).hom) ∧
      Space.IsFlat C S hS (GroupoidInAlgebraicSpaces.restrictionSource G g).hom ∧
      Space.IsFlat C S hS (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom ∧
      Space.IsLocallyOfFinitePresentation C S hS
        (GroupoidInAlgebraicSpaces.restrictionSource G g).hom ∧
      Space.IsLocallyOfFinitePresentation C S hS
        (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom := by
  obtain ⟨W, V, b, f, g, hf, hAtlas, hbFlat, hbLfp, _hbSurj, ⟨eIso⟩, hsat⟩ :=
    exists_presented_point_locallySurjective_saturation G h𝒳
  let : MorphismProperty.IsStableUnderComposition
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom) :=
    GroupoidInAlgebraicSpaces.isLocallyOfFinitePresentation_isStableUnderComposition C S hS
  have hchartFlat : ChartRelativeProperty C S hS
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom) f := by
    intro T y hy F hF he A A' a a' k ha ha' hw
    have := (hAtlas T y hy F hF he).2 A A' a a' k ha ha' hw
    infer_instance
  have hchartLfp : ChartRelativeProperty C S hS
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom) f := by
    intro T y hy F hF he A A' a a' k ha ha' hw
    have := (hAtlas T y hy F hF he).2 A A' a a' k ha ha' hw
    infer_instance
  have hsrcFlat : Space.IsFlat C S hS
      (GroupoidInAlgebraicSpaces.restrictionSource G g).hom :=
    prop_restrictionSource_of_schemePresentationHom.{u, u}
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom)
      G V g hsat
      (chartRelativeProperty_schemePresentationHom.{u, u}
        (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom)
        f hf hchartFlat b (Space.isFlat_yoneda_map C S hS b hbFlat) g.hom eIso)
  have hsrcLfp : Space.IsLocallyOfFinitePresentation C S hS
      (GroupoidInAlgebraicSpaces.restrictionSource G g).hom :=
    prop_restrictionSource_of_schemePresentationHom.{u, u}
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom)
      G V g hsat
      (chartRelativeProperty_schemePresentationHom.{u, u}
        (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
          Space.IsLocallyOfFinitePresentation C S hS k.hom)
        f hf hchartLfp b
        (Space.isLocallyOfFinitePresentation_yoneda_map C S hS b hbLfp) g.hom eIso)
  let : MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨Space.representedAlgebraicSpace C S hS V, g, hsat, hsrcFlat,
    restrictionTarget_property_of_restrictionSource C S hS
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom)
      G g hsrcFlat,
    hsrcLfp,
    restrictionTarget_property_of_restrictionSource C S hS
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom)
      G g hsrcLfp⟩

/-- **The quotient stack of a groupoid is algebraic as soon as that of a restriction with locally
surjective saturation is.** Let `g : U' ⟶ U` be a morphism of algebraic spaces whose saturation
map `U' ×_{g, U, t} R ⟶ R ⟶ U` is a surjection of fppf sheaves. If the quotient stack `[U'/R']`
of the restriction `(U', R', s', t', c')` of `(U, R, s, t, c)` along `g` is an algebraic stack,
then so is `[U/R]`. -/
theorem isAlgebraicStack_quotientStack_of_isAlgebraicStack_restrict
    (G : GroupoidInAlgebraicSpaces C S hS B) {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hsat : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source).hom))
    (h : IsAlgebraicStack.{u, w} C S hS
      (quotientStack (GroupoidInAlgebraicSpaces.restrict G g).groupoid)) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) := by
  obtain ⟨E⟩ := (quotientStackMap_isEquivalenceOver_iff
    (GroupoidInAlgebraicSpaces.restrict G g).hom).mpr
      ⟨isPullback_mapArrows_of_evaluation_fullyFaithful _ (fun T =>
        ((GroupoidInAlgebraicSpaces.restrict G g).evaluation_fullyFaithful T).some),
        isLocallySurjective_saturation_restrict G g hsat⟩
  exact (isAlgebraicStack_iff_of_equivalence C S hS
    (StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
      (quotientStackMap (GroupoidInAlgebraicSpaces.restrict G g).hom).w E).toBasedEquivalence).mp h

/-- **The forward implication of Stacks 06PJ.** Let `g : U' ⟶ U` be a morphism of algebraic
spaces whose saturation map `U' ×_{g, U, t} R ⟶ R ⟶ U` is a surjection of fppf sheaves and whose
restriction `(U', R', s', t', c')` has flat, locally finitely presented source and target. Then
`[U/R]` is an algebraic stack. -/
theorem isAlgebraicStack_quotientStack_of_restrictionAlong_of_flat
    (G : GroupoidInAlgebraicSpaces C S hS B) {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (hsat : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      ((GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source).hom))
    (hsource : Space.IsFlat C S hS (GroupoidInAlgebraicSpaces.restrictionSource G g).hom)
    (htarget : Space.IsFlat C S hS (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom)
    (hsourceFP : Space.IsLocallyOfFinitePresentation C S hS
      (GroupoidInAlgebraicSpaces.restrictionSource G g).hom)
    (htargetFP : Space.IsLocallyOfFinitePresentation C S hS
      (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) := by
  have hflat := Space.isFlat_isStableUnderBaseChange C S hS
  have hfp := Space.isLocallyOfFinitePresentation_isStableUnderBaseChange C S hS
  let : MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let : MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hs : ∀ (Q : MorphismProperty (AlgebraicSpaces C S hS)) [Q.RespectsIso],
      Q (GroupoidInAlgebraicSpaces.restrictionSource G g) →
        Q (GroupoidInAlgebraicSpaces.restrict G g).groupoid.source := fun Q _ h => by
    rw [(GroupoidInAlgebraicSpaces.restrict G g).source_eq]
    exact MorphismProperty.RespectsIso.precomp Q _ _
      (MorphismProperty.RespectsIso.postcomp Q _ _ h)
  have ht : ∀ (Q : MorphismProperty (AlgebraicSpaces C S hS)) [Q.RespectsIso],
      Q (GroupoidInAlgebraicSpaces.restrictionTarget G g) →
        Q (GroupoidInAlgebraicSpaces.restrict G g).groupoid.target := fun Q _ h => by
    rw [(GroupoidInAlgebraicSpaces.restrict G g).target_eq]
    exact MorphismProperty.RespectsIso.precomp Q _ _
      (MorphismProperty.RespectsIso.postcomp Q _ _ h)
  exact isAlgebraicStack_quotientStack_of_isAlgebraicStack_restrict.{u, w} G g hsat
    (isAlgebraicStack_quotientStack_of_flat _
      (hs (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom) hsource)
      (ht (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) => Space.IsFlat C S hS k.hom) htarget)
      (hs (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom) hsourceFP)
      (ht (fun ⦃X Y : AlgebraicSpaces C S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation C S hS k.hom) htargetFP))

/-- Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B`. The
quotient stack `[U/R]` is an algebraic stack if and only if there is a morphism `g : U' ⟶ U` of
algebraic spaces over `S` such that

1. the saturation map `U' ×_{g, U, t} R ⟶ R ⟶ U` is a surjection of fppf sheaves, and
2. the source and target of the restriction of `(U, R, s, t, c)` along `g` are flat and locally of
   finite presentation. -/
@[stacks 06PJ]
theorem isAlgebraicStack_quotientStack_iff_restrictionAlong
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsAlgebraicStack.{u, w} C S hS (quotientStack G) ↔
      ∃ (U' : AlgebraicSpaces C S hS) (g : U' ⟶ G.objects),
        Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
          ((GroupoidInAlgebraicSpaces.fiberProductSnd g G.target ≫ G.source).hom) ∧
        Space.IsFlat C S hS (GroupoidInAlgebraicSpaces.restrictionSource G g).hom ∧
        Space.IsFlat C S hS (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom ∧
        Space.IsLocallyOfFinitePresentation C S hS
          (GroupoidInAlgebraicSpaces.restrictionSource G g).hom ∧
        Space.IsLocallyOfFinitePresentation C S hS
          (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom where
  mp h𝒳 := exists_restrictionAlong_of_isAlgebraicStack.{u, w} G h𝒳
  mpr := fun ⟨_, g, hsat, hsource, htarget, hsourceFP, htargetFP⟩ =>
    isAlgebraicStack_quotientStack_of_restrictionAlong_of_flat G g hsat hsource htarget
      hsourceFP htargetFP

end AlgebraicGeometry.Stack

end
