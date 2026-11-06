module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation

/-!
# The relative Hom functor of a relocalized situation

Let `h : W ⟶ S` be a morphism of a big fppf site and `Λ` the lower-shriek extension of
algebraic spaces over `W` to algebraic spaces over `S`.  For a situation `s` of Stacks 08JT over
`W` — a morphism `f : X ⟶ B` of algebraic spaces over `W` and two quasi-coherent `𝒪_X`-modules —
the relocalized situation `s.relocalize h` over `S` is `Λ f : Λ X ⟶ Λ B` with the images of the
two modules under `Mod(𝒪_X) ≌ Mod(𝒪_{Λ X})`.  Its relative Hom functor, restricted to the test
schemes over `Λ B` coming from test schemes over `B`, is the relative Hom functor of `s`.

## Main definitions

* `AlgebraicGeometry.Space.relocalizeSchemesOver`: a test scheme over `B` as a test scheme over
  `Λ B`.
* `AlgebraicGeometry.Space.relocalizeOverBaseChangeFunctorIso`,
  `AlgebraicGeometry.Space.relocalizeTestBaseChangeIso`: base change commutes with `Λ`, because
  `Λ` preserves fibre products.
* `AlgebraicGeometry.Space.HomSituation.relocalize`: the relocalized situation.
* `AlgebraicGeometry.Space.HomSituation.homFunctorRelocalizeIso`: **the relative Hom functor of
  `s` is the restriction of that of `s.relocalize h`.**

## References

* [Stacks Project, Tag 08JT](https://stacks.math.columbia.edu/tag/08JT)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). Public, not private: the public statement of
`isPullback_relocalizeHom_fiberProduct` needs it, and a private instance is not usable there. -/
instance (priority := high) hasPullback_presheaf_relativeHomRelocalizeSituation
    {B : BigFppfSite.{u}} {W : Scheme.{u}} {hW : B.Contains W}
    {X Y Z : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- The comparison `h_{j U} ⟶ Λ h_U` of the algebraic space of a scheme over `W` viewed over `S`
with the extension of the algebraic space of the scheme. -/
def relocalizeSchemeSpaceIso (U : BigFppfOver B W hW) :
    (schemeSpaceFunctor B S hS).obj ((Over.map h).obj U) ≅
      relocalizeSpaceSE B W S hW hS h ((schemeSpaceFunctor B W hW).obj U) :=
  ObjectProperty.isoMk _ ((OverShriek.relocalizeYonedaIso h).app U).symm

/-- The forward direction of `AlgebraicGeometry.Space.relocalizeSchemeSpaceIso`. -/
abbrev relocalizeSchemeSpaceHom (U : BigFppfOver B W hW) :
    (schemeSpaceFunctor B S hS).obj ((Over.map h).obj U) ⟶
      relocalizeSpaceSE B W S hW hS h ((schemeSpaceFunctor B W hW).obj U) :=
  (relocalizeSchemeSpaceIso B W S hW hS h U).hom

/-- The comparison `h_{j U} ⟶ Λ h_U` is natural in the scheme `U` over `W`. -/
theorem relocalizeSchemeSpaceHom_naturality {U V : BigFppfOver B W hW} (g : U ⟶ V) :
    (schemeSpaceFunctor B S hS).map ((Over.map h).map g) ≫
        relocalizeSchemeSpaceHom B W S hW hS h V =
      relocalizeSchemeSpaceHom B W S hW hS h U ≫
        relocalizeHomSE B W S hW hS h ((schemeSpaceFunctor B W hW).map g) :=
  ObjectProperty.hom_ext _ ((OverShriek.relocalizeYonedaIso h).inv.naturality g)

/-- **The test schemes across relocalization**: a scheme `T` over `W` with a morphism to `Y` is
the scheme `T` over `S` with the morphism `h_T ⟶ Λ h_T ⟶ Λ Y`. -/
def relocalizeSchemesOver (Y : AlgebraicSpaces B W hW) :
    SchemesOver Y ⥤ SchemesOver (relocalizeSpaceSE B W S hW hS h Y) where
  obj T := CostructuredArrow.mk
    (relocalizeSchemeSpaceHom B W S hW hS h T.left ≫ relocalizeHomSE B W S hW hS h T.hom)
  map {T T'} g := CostructuredArrow.homMk ((Over.map h).map g.left) (by
    change (schemeSpaceFunctor B S hS).map ((Over.map h).map g.left) ≫
        relocalizeSchemeSpaceHom B W S hW hS h T'.left ≫ relocalizeHomSE B W S hW hS h T'.hom =
      relocalizeSchemeSpaceHom B W S hW hS h T.left ≫ relocalizeHomSE B W S hW hS h T.hom
    rw [← Category.assoc, relocalizeSchemeSpaceHom_naturality, Category.assoc,
      ← relocalizeHomSE_comp]
    exact congrArg (fun t => relocalizeSchemeSpaceHom B W S hW hS h T.left ≫
      relocalizeHomSE B W S hW hS h t) (CostructuredArrow.w g))
  map_id T := CostructuredArrow.hom_ext _ _ ((Over.map h).map_id _)
  map_comp f g := CostructuredArrow.hom_ext _ _ ((Over.map h).map_comp _ _)

/-- `Λ` carries fibre products of algebraic spaces over `W` to fibre products over `S`. -/
theorem isPullback_relocalizeHom_fiberProduct {X Y Z : AlgebraicSpaces B W hW} (f : X ⟶ Y)
    (g : Z ⟶ Y) :
    IsPullback
      (relocalizeHomSE B W S hW hS h (ObjectProperty.homMk (pullback.fst f.hom g.hom) :
        AlgebraicSpaces.fiberProduct B W hW f g ⟶ X))
      (relocalizeHomSE B W S hW hS h (ObjectProperty.homMk (pullback.snd f.hom g.hom) :
        AlgebraicSpaces.fiberProduct B W hW f g ⟶ Z))
      (relocalizeHomSE B W S hW hS h f) (relocalizeHomSE B W S hW hS h g) :=
  have hp := (AlgebraicSpaces.isPullback_hom B W hW
    (AlgebraicSpaces.isPullback_fiberProduct B W hW f g)).map
      (OverShriek.relocalizePresheafFunctor h)
  IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hp.w) hp

/-- `Λ` of a base change along an algebraic space over the target. -/
def relocalizeOverBaseChangeIso {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y) (V : Over Y) :
    relocalizeSpaceSE B W S hW hS h (overBaseChange f V) ≅
      overBaseChange (relocalizeHomSE B W S hW hS h f) ((relocalizeOver B W S hW hS h Y).obj V) :=
  (isPullback_relocalizeHom_fiberProduct B W S hW hS h f V.hom).isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS _ _)

/-- The isomorphism `relocalizeOverBaseChangeIso` followed by the projection of the base change
over `S` is `Λ` of the projection of the base change over `W`. -/
theorem relocalizeOverBaseChangeIso_hom_projection {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y)
    (V : Over Y) :
    (relocalizeOverBaseChangeIso B W S hW hS h f V).hom ≫
        overProjection (relocalizeHomSE B W S hW hS h f) ((relocalizeOver B W S hW hS h Y).obj V) =
      relocalizeHomSE B W S hW hS h (overProjection f V) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The isomorphism `relocalizeOverBaseChangeIso` followed by the inclusion of the base change
over `S` is `Λ` of the inclusion of the base change over `W`. -/
theorem relocalizeOverBaseChangeIso_hom_inclusion {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y)
    (V : Over Y) :
    (relocalizeOverBaseChangeIso B W S hW hS h f V).hom ≫
        overInclusion (relocalizeHomSE B W S hW hS h f) ((relocalizeOver B W S hW hS h Y).obj V) =
      relocalizeHomSE B W S hW hS h (overInclusion f V) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- **Base change commutes with relocalization**, naturally in the algebraic space over the
target. -/
def relocalizeOverBaseChangeFunctorIso {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y) :
    overBaseChangeFunctor f ⋙ relocalizeOver B W S hW hS h X ≅
      relocalizeOver B W S hW hS h Y ⋙
        overBaseChangeFunctor (relocalizeHomSE B W S hW hS h f) :=
  NatIso.ofComponents
    (fun V => Over.isoMk (relocalizeOverBaseChangeIso B W S hW hS h f V)
      (relocalizeOverBaseChangeIso_hom_projection B W S hW hS h f V))
    (fun {V V'} g => by
      refine Over.OverMorphism.ext (overBaseChange_hom_ext _ ?_ ?_)
      · change relocalizeHomSE B W S hW hS h (overBaseChangeMap f g) ≫
            (relocalizeOverBaseChangeIso B W S hW hS h f V').hom ≫
              overProjection (relocalizeHomSE B W S hW hS h f)
                ((relocalizeOver B W S hW hS h Y).obj V') =
          (relocalizeOverBaseChangeIso B W S hW hS h f V).hom ≫
            overBaseChangeMap (relocalizeHomSE B W S hW hS h f)
                ((relocalizeOver B W S hW hS h Y).map g) ≫
              overProjection (relocalizeHomSE B W S hW hS h f)
                ((relocalizeOver B W S hW hS h Y).obj V')
        rw [relocalizeOverBaseChangeIso_hom_projection, overBaseChangeMap_comp_projection,
          relocalizeOverBaseChangeIso_hom_projection, ← relocalizeHomSE_comp,
          overBaseChangeMap_comp_projection]
      · change relocalizeHomSE B W S hW hS h (overBaseChangeMap f g) ≫
            (relocalizeOverBaseChangeIso B W S hW hS h f V').hom ≫
              overInclusion (relocalizeHomSE B W S hW hS h f)
                ((relocalizeOver B W S hW hS h Y).obj V') =
          (relocalizeOverBaseChangeIso B W S hW hS h f V).hom ≫
            overBaseChangeMap (relocalizeHomSE B W S hW hS h f)
                ((relocalizeOver B W S hW hS h Y).map g) ≫
              overInclusion (relocalizeHomSE B W S hW hS h f)
                ((relocalizeOver B W S hW hS h Y).obj V')
        rw [relocalizeOverBaseChangeIso_hom_inclusion, overBaseChangeMap_comp_inclusion,
          ← Category.assoc, relocalizeOverBaseChangeIso_hom_inclusion, ← relocalizeHomSE_comp,
          ← relocalizeHomSE_comp, overBaseChangeMap_comp_inclusion])

/-- **The test schemes across relocalization, as algebraic spaces over the target.** -/
def relocalizeSchemesOverToOverIso (Y : AlgebraicSpaces B W hW) :
    schemesOverToOver Y ⋙ relocalizeOver B W S hW hS h Y ≅
      relocalizeSchemesOver B W S hW hS h Y ⋙
        schemesOverToOver (relocalizeSpaceSE B W S hW hS h Y) :=
  NatIso.ofComponents
    (fun T => Over.isoMk (relocalizeSchemeSpaceIso B W S hW hS h T.left).symm (by
      change (relocalizeSchemeSpaceIso B W S hW hS h T.left).inv ≫
          relocalizeSchemeSpaceHom B W S hW hS h T.left ≫ relocalizeHomSE B W S hW hS h T.hom =
        relocalizeHomSE B W S hW hS h T.hom
      rw [Iso.inv_hom_id_assoc]))
    (fun {T T'} g => by
      refine Over.OverMorphism.ext ?_
      change relocalizeHomSE B W S hW hS h ((schemeSpaceFunctor B W hW).map g.left) ≫
          (relocalizeSchemeSpaceIso B W S hW hS h T'.left).inv =
        (relocalizeSchemeSpaceIso B W S hW hS h T.left).inv ≫
          (schemeSpaceFunctor B S hS).map ((Over.map h).map g.left)
      rw [Iso.comp_inv_eq, Category.assoc, relocalizeSchemeSpaceHom_naturality,
        Iso.inv_hom_id_assoc])

/-- **Base change along the test schemes commutes with relocalization.** -/
def relocalizeTestBaseChangeIso {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y) :
    baseChangeOver f ⋙ relocalizeOver B W S hW hS h X ≅
      relocalizeSchemesOver B W S hW hS h Y ⋙
        baseChangeOver (relocalizeHomSE B W S hW hS h f) :=
  Functor.isoWhiskerLeft (schemesOverToOver Y)
      (relocalizeOverBaseChangeFunctorIso B W S hW hS h f) ≪≫
    Functor.isoWhiskerRight (relocalizeSchemesOverToOverIso B W S hW hS h Y)
      (overBaseChangeFunctor (relocalizeHomSE B W S hW hS h f))

/-- The projection `X_T ⟶ X` of the base change along a test scheme is relatively
representable: it is a base change of the morphism `h_T ⟶ Y` from a representable presheaf to an
algebraic space. -/
theorem relativelyRepresentable_baseChangeProjection_of_isAlgebraicSpace
    {X Y : AlgebraicSpaces B W hW} (f : X ⟶ Y) (T : SchemesOver Y) :
    yoneda.relativelyRepresentable (baseChangeProjection f T).hom :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    (AlgebraicSpaces.isPullback_hom B W hW
      (AlgebraicSpaces.isPullback_fiberProduct B W hW f T.hom)).flip
    (Functor.relativelyRepresentable.of_diag Y.2.diagonal_representable T.hom.hom)

namespace HomSituation

variable {B W S hW hS}

/-- **The relocalization of a situation of Stacks 08JT along `h : W ⟶ S`**: the lower-shriek
extensions of the source, the base and the morphism, and the images of the two modules under the
equivalence `Mod(𝒪_X) ≌ Mod(𝒪_{Λ X})`. -/
def relocalize (s : HomSituation B W hW) : HomSituation B S hS where
  X := relocalizeSpaceSE B W S hW hS h s.X
  base := relocalizeSpaceSE B W S hW hS h s.base
  f := relocalizeHomSE B W S hW hS h s.f
  F := (relocalizeModulesEquivalenceSE B W S hW hS h s.X.2
    (relocalizeSpaceSE B W S hW hS h s.X).2).functor.obj s.F
  G := (relocalizeModulesEquivalenceSE B W S hW hS h s.X.2
    (relocalizeSpaceSE B W S hW hS h s.X).2).functor.obj s.G
  quasicoherent_F := (isQuasicoherentOnSite_relocalizeModulesEquivalence_functor_iff B W S hW hS h
    s.X.2 _ s.F).2 s.quasicoherent_F
  quasicoherent_G := (isQuasicoherentOnSite_relocalizeModulesEquivalence_functor_iff B W S hW hS h
    s.X.2 _ s.G).2 s.quasicoherent_G

/-- **The relative Hom functor across relocalization.**  The relative Hom functor of a situation
over `W` is the relative Hom functor of its relocalization, restricted along the test schemes
over `Λ base` coming from test schemes over `base`. -/
def homFunctorRelocalizeIso (s : HomSituation B W hW) (hc : ModulePushforwardCoherence B W hW)
    (hc' : ModulePushforwardCoherence B S hS) :
    s.homFunctor hc ≅
      (relocalizeSchemesOver B W S hW hS h s.base).op ⋙ (s.relocalize h).homFunctor hc' :=
  relocalizeModuleHomOverIso B W S hW hS h (baseChangeOver s.f)
      (fun T => relativelyRepresentable_baseChangeProjection_of_isAlgebraicSpace B W hW s.f T)
      (fun g => relativelyRepresentable_baseChangeMap B W hW s.f g) hc hc' s.F s.G ≪≫
    Functor.isoWhiskerRight (NatIso.op (relocalizeTestBaseChangeIso B W S hW hS h s.f).symm)
      (moduleHomOver (X := relocalizeSpaceSE B W S hW hS h s.X) hc' (s.relocalize h).F
        (s.relocalize h).G)

end HomSituation

end AlgebraicGeometry.Space

end
