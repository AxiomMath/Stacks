module

public import StacksFrontier.AlgebraicGeometry.Recovery04IH.LocalizationMorphismsLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Recovery04IH.ToposRelocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.RelocalizedMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedTopoi.CompositionOfLocallyRingedMorphisms
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# The localized and relocalized morphisms of a locally ringed site or topos are locally ringed

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites given by a continuous functor
`u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`. Stacks 04J0 localizes `f` to
`(f', (f')♯) : (Sh(C/U), O_U) ⟶ (Sh(D/V), O'_V)` and Stacks 04J1 relocalizes it along a morphism
`c : U' ⟶ u(V)` to `(f_c, f_c♯) : (Sh(C/U'), O_{U'}) ⟶ (Sh(D/V), O'_V)`. Clauses (3) and (4) of
Stacks 04IH assert that both are locally ringed as soon as `f` is.

The same two clauses for a morphism of ringed *topoi* are clauses (7) and (8): Stacks 04IF
localizes `(f, f♯) : (Sh(C), O) ⟶ (Sh(D), O')` at a sheaf `G` on the target to
`(f', (f')♯) : (Sh(C)/f⁻¹G, O_{f⁻¹G}) ⟶ (Sh(D)/G, O'_G)`, and Stacks 04J8 relocalizes it along a
morphism `s : F ⟶ f⁻¹G` of sheaves on the source; both are locally ringed as soon as `f` is.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.fSharpSet_localizedRingedToposHom`: on underlying sheaves of
  sets the structure map of `f'` in inverse-image form is the structure map of `f` restricted to
  the slice, read through Stacks 03CF's clause (b).
* `AlgebraicGeometry.RingedSite.Hom.localizedRingedToposHom_isLocallyRinged`: **Stacks 04IH (3)**,
  the localized morphism of Stacks 04J0 is locally ringed.
* `AlgebraicGeometry.RingedSite.Hom.relocalized_isLocallyRinged`: **Stacks 04IH (4)**, the
  relocalized morphism of Stacks 04J1 is locally ringed.
* `AlgebraicGeometry.RingedToposHom.fSharpSet_localized`: on underlying sheaves of sets the
  structure map of the morphism of Stacks 04IF is `j_{f⁻¹G}⁻¹` of the structure map of `f`,
  preceded by 04IF's comparison of inverse images.
* `AlgebraicGeometry.RingedToposHom.localized_isLocallyRinged`: **Stacks 04IH (7)**, the
  localized morphism of Stacks 04IF is locally ringed.
* `AlgebraicGeometry.RingedToposHom.relocalized_isLocallyRinged`: **Stacks 04IH (8)**, the
  relocalized morphism of Stacks 04J8 is locally ringed.

## Implementation notes

Stacks defines a morphism of locally ringed *sites* to be one whose associated morphism of ringed
topoi is locally ringed, so both clauses are statements about
`AlgebraicGeometry.RingedToposHom.IsLocallyRinged`, applied to the associated morphisms of ringed
topoi `AlgebraicGeometry.RingedSite.Hom.ringedToposHom`,
`AlgebraicGeometry.RingedSite.Hom.localizedRingedToposHom` (which *is*
`(f.localized V).ringedToposHom`) and `AlgebraicGeometry.RingedSite.Hom.relocalized`. That is the
same reading under which clauses (1) and (2) are recorded in
`StacksFrontier/AlgebraicGeometry/Recovery04IH/LocalizationMorphismsLocallyRinged.lean`.

Clause (3) is the argument Stacks gives: the units square of `f'` is the image under `j_U^{-1}` of
the units square of `f`, and `j_U^{-1}` is exact. Three things make this work on the nose. The
units subsheaf and its inclusion restrict to a slice without any comparison map, because
restriction commutes with `CategoryTheory.sheafCompose` objectwise — the observation that already
does all the work in the file above. The bottom edges of the two squares are matched by Stacks
03CF's clause (b), `CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso`, and that
comparison is available with *computable components* because it is the Beck–Chevalley mate of
clause (d) (`CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso_hom`); the
identity it satisfies at a direct image,
`CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit`, is
exactly what turns the adjunct of `j_V^{-1}(f♯)` into the restriction of the adjunct of `f♯`.
Finally the left-hand square, whose two horizontal edges are components of clause (b), is
cartesian because they are isomorphisms.

Clause (4) is Stacks' "follows formally on combining (2) and (3)": `f_c` is by definition the
composite of `f'` with the relocalization morphism along `c`, so it is an instance of
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_comp`, Stacks 04IG.

Clause (7) is clause (3) for a general sheaf in place of `h_V^#`, and it runs along the same
three steps, with one difference. Over a site the two bottom edges of the units squares are
matched by a comparison of restrictions, Stacks 03CF's clause (b); for a general sheaf the
matching comparison is 04IF's comparison of inverse images
`AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso`, and that the two bottom edges
are matched by it is exactly the statement that 04IF's square is a square of *ringed* topoi,
`AlgebraicGeometry.RingedToposHom.localized_fSharpInverseImage_forget`. The other two steps are
unchanged: the units subsheaf of a localization and its inclusion are the inverse image of those
of the original ringed topos on the nose, which is the observation of the file above, and the
left-hand square of the pasting has both horizontal edges invertible.

Clause (8) is to clause (7) what clause (4) is to clause (3): Stacks 04J8 *defines* `f_s` to be
the morphism of 04IF composed with the relocalization morphism of 04J4 along `s`, so the clause
is `AlgebraicGeometry.RingedToposHom.isLocallyRinged_comp` applied to clause (7) and to
clause (6), `AlgebraicGeometry.RingedTopos.relocalizationMorphism_isLocallyRinged`.

Like the two files it rests on, nothing here assumes the hypotheses of Stacks 03EF: the continuity
of `u' = Over.post u` comes from `f.isMorphismOfSites` through
`CategoryTheory.Functor.isContinuous_overPost_of_isContinuous`, taken as a local instance.

## References

* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA)
* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04IG](https://stacks.math.columbia.edu/tag/04IG)
* [Stacks Project, Tag 04IH](https://stacks.math.columbia.edu/tag/04IH)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 04J1](https://stacks.math.columbia.edu/tag/04J1)
* [Stacks Project, Tag 04J8](https://stacks.math.columbia.edu/tag/04J8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

/-- Pasting a naturality square of isomorphisms to the left of the image of a pullback square
under a functor preserving pullbacks gives a pullback square. -/
private theorem isPullback_app_comp_map_of_isIso {C D E : Type*} [Category C] [Category D]
    [Category E] {H : C ⥤ D} {L : D ⥤ E} {K : C ⥤ E} (e : K ⟶ H ⋙ L) [PreservesLimitsOfShape
      WalkingCospan L] {A B : C} {P Q : D} {t : H.obj A ⟶ P} {j : P ⟶ Q} {s : H.obj B ⟶ Q}
    (i : A ⟶ B) [IsIso (e.app A)] [IsIso (e.app B)] (ht : IsPullback t (H.map i) j s) :
    IsPullback (e.app A ≫ L.map t) (K.map i) (L.map j) (e.app B ≫ L.map s) :=
  (IsPullback.of_horiz_isIso (CommSq.mk (e.naturality i).symm)).paste_horiz
    (CategoryTheory.Functor.map_isPullback L ht)

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Functor.isContinuous_overPost_of_isContinuous

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)

/-- The structure map of the localized morphism of Stacks 04J0, in inverse-image form on
underlying sheaves of sets: it is `j_U^{-1}` of the structure map of `f`, preceded by Stacks
03CF's clause (b).

Both sides are adjuncts of the same map: the left-hand side is the adjunct, under
`(f')^{-1} ⊣ f'_*`, of `j_V^{-1}(f♯)`, and clause (b) is the Beck–Chevalley mate of the strict
identity `f'_* j_U^{-1} = j_V^{-1} f_*` of clause (d). What carries one adjunct to the other is
naturality of the mate together with the identity it satisfies at a direct image. -/
theorem Hom.fSharpSet_localizedRingedToposHom (V : Y.C) :
    RingedToposHom.fSharpSet (f.localizedRingedToposHom V) =
      (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
            f.isMorphismOfSites).hom.app ((ringedTopos Y).forgetRing.obj Y.O) ≫
        (X.J.overPullback (Type u) (f.u.obj V)).map
          (RingedToposHom.fSharpSet f.ringedToposHom) := by
  -- The structure map of `f'` is the adjunct of `j_V^{-1}` of the structure map of `f`.
  have hLHS : RingedToposHom.fSharpSet (f.localizedRingedToposHom V) =
      (f.localizedRingedToposHom V).toToposHom.inverseImage.map
          ((Y.overMorphismOfTopoi V).inverseImage.map
            (RingedToposHom.forgetFSharp f.ringedToposHom)) ≫
        (f.localizedRingedToposHom V).toToposHom.adj.counit.app
          ((ringedTopos (X.over (f.u.obj V))).forgetRing.obj (X.over (f.u.obj V)).O) :=
    (congrArg
        (fun z => ((f.localizedRingedToposHom V).toToposHom.adj.homEquiv
          ((ringedTopos (Y.over V)).forgetRing.obj (Y.over V).O)
          ((ringedTopos (X.over (f.u.obj V))).forgetRing.obj (X.over (f.u.obj V)).O)).symm z)
        (f.forgetFSharp_localizedRingedToposHom V)).trans
      (Adjunction.homEquiv_counit _ _ _ _)
  -- The structure map of `f` is the adjunct of `f♯`.
  have hA : RingedToposHom.fSharpSet f.ringedToposHom =
      f.ringedToposHom.toToposHom.inverseImage.map
          (RingedToposHom.forgetFSharp f.ringedToposHom) ≫
        f.ringedToposHom.toToposHom.adj.counit.app ((ringedTopos X).forgetRing.obj X.O) :=
    Adjunction.homEquiv_counit _ _ _ _
  -- Naturality of clause (b) at the structure map of `f`.
  have hnat : (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
            f.isMorphismOfSites).hom.app ((ringedTopos Y).forgetRing.obj Y.O) ≫
        (X.J.overPullback (Type u) (f.u.obj V)).map
          (f.ringedToposHom.toToposHom.inverseImage.map
            (RingedToposHom.forgetFSharp f.ringedToposHom)) =
      (f.localizedRingedToposHom V).toToposHom.inverseImage.map
            ((Y.overMorphismOfTopoi V).inverseImage.map
              (RingedToposHom.forgetFSharp f.ringedToposHom)) ≫
          (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
            f.isMorphismOfSites).hom.app
            (f.ringedToposHom.toToposHom.pushforward.obj
              ((ringedTopos X).forgetRing.obj X.O)) :=
    ((SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
      f.isMorphismOfSites).hom.naturality
        (RingedToposHom.forgetFSharp f.ringedToposHom)).symm
  -- Clause (b) at a direct image, in terms of the two counits.
  have hcounit := SliceTopos.overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit
    Y.J X.J f.u V f.isMorphismOfSites ((ringedTopos X).forgetRing.obj X.O)
  refine hLHS.trans (Eq.symm ?_)
  refine Eq.trans (congrArg (fun z =>
    (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
          f.isMorphismOfSites).hom.app ((ringedTopos Y).forgetRing.obj Y.O) ≫
      (X.J.overPullback (Type u) (f.u.obj V)).map z) hA) ?_
  refine Eq.trans (congrArg (fun z =>
    (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
          f.isMorphismOfSites).hom.app ((ringedTopos Y).forgetRing.obj Y.O) ≫ z)
    ((X.J.overPullback (Type u) (f.u.obj V)).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫ (X.J.overPullback (Type u) (f.u.obj V)).map
    (f.ringedToposHom.toToposHom.adj.counit.app ((ringedTopos X).forgetRing.obj X.O))) hnat) ?_
  exact (Category.assoc _ _ _).trans (congrArg (fun z =>
    (f.localizedRingedToposHom V).toToposHom.inverseImage.map
      ((Y.overMorphismOfTopoi V).inverseImage.map
        (RingedToposHom.forgetFSharp f.ringedToposHom)) ≫ z) hcounit)

/-- **Stacks 04IH (3).** The localized morphism `(f', (f')♯)` of Stacks 04J0 is a morphism of
locally ringed sites as soon as `(f, f♯)` is: its units square is the image under the exact
functor `j_U^{-1}` of the units square of `f`, with the two bottom edges matched by Stacks 03CF's
clause (b).

The units subsheaf of a localization, and its inclusion, are the restrictions of those of the
original ringed site on the nose, so the only comparison entering is clause (b), whose two
components form a square of isomorphisms on the left of the pasting. -/
@[stacks 04IH "(3): the localized morphism `f'` of 04J0 is a morphism of locally ringed sites"]
theorem Hom.localizedRingedToposHom_isLocallyRinged (V : Y.C)
    (hf : f.ringedToposHom.IsLocallyRinged) :
    (f.localizedRingedToposHom V).IsLocallyRinged := by
  obtain ⟨t, ht⟩ := hf
  have := (X.overMorphismOfTopoi (f.u.obj V)).preservesFiniteLimits
  refine ⟨(SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
      f.isMorphismOfSites).hom.app (RingedTopos.units (ringedTopos Y)) ≫
    (X.J.overPullback (Type u) (f.u.obj V)).map t, ?_⟩
  rw [f.fSharpSet_localizedRingedToposHom V]
  exact isPullback_app_comp_map_of_isIso
    (SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V f.isMorphismOfSites).hom
    (RingedTopos.unitsι (ringedTopos Y)) ht

/-- **Stacks 04IH (4).** The relocalized morphism `(f_c, f_c♯)` of Stacks 04J1 is a morphism of
locally ringed topoi as soon as `(f, f♯)` is a morphism of locally ringed sites.

This is Stacks' "follows formally on combining (2) and (3)": `f_c` is by definition the localized
morphism of Stacks 04J0 composed with the relocalization morphism of Stacks 04IY along `c`, the
first locally ringed by clause (3) and the second by clause (2), and a composite of locally ringed
morphisms is locally ringed by Stacks 04IG. -/
@[stacks 04IH "(4): the relocalized morphism `f_c` of 04J1 is a morphism of locally ringed topoi"]
theorem Hom.relocalized_isLocallyRinged {U : X.C} {V : Y.C} (c : U ⟶ f.u.obj V)
    (hf : f.ringedToposHom.IsLocallyRinged) :
    (f.relocalized c).IsLocallyRinged :=
  RingedToposHom.isLocallyRinged_comp (f.localizedRingedToposHom V)
    (X.relocalizationRingedToposHom c)
    (f.localizedRingedToposHom_isLocallyRinged V hf)
    (X.relocalizationRingedToposHom_isLocallyRinged c)

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y) (G : Y.Topos)

/-- The structure map of the morphism of Stacks 04IF, in inverse-image form on underlying sheaves
of sets: it is `j_{f⁻¹G}⁻¹` of the structure map of `f`, preceded by 04IF's comparison of inverse
images.

This is `localized_fSharpInverseImage_forget` — the statement that the square of Stacks 04IF is a
square of ringed topoi — with the comparison of inverse images moved to the other side and both
structure maps read as adjuncts of their direct-image forms. -/
theorem fSharpSet_localized :
    fSharpSet (f.localized G) =
      (f.inverseImageCompLocalizationIso G).inv.app (Y.forgetRing.obj Y.O) ≫
        (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
          (fSharpSet f) :=
  have hL : fSharpSet (f.localized G) =
      (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
        (f.localized G).fSharpInverseImage :=
    (fSharpInverseImage_forget_homEquiv (f.localized G)).symm
  have key : (f.inverseImageCompLocalizationIso G).inv.app (Y.forgetRing.obj Y.O) ≫
        (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
          (X.forgetRing.map f.fSharpInverseImage) =
      (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).forgetRing.map
        (f.localized G).fSharpInverseImage :=
    (congrArg (fun z => (f.inverseImageCompLocalizationIso G).inv.app
          (Y.forgetRing.obj Y.O) ≫ z) (f.localized_fSharpInverseImage_forget G).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (X.localizedRingedTopos
              (f.toToposHom.inverseImage.obj G)).forgetRing.map
                (f.localized G).fSharpInverseImage)
            ((f.inverseImageCompLocalizationIso G).inv_hom_id_app
              (Y.forgetRing.obj Y.O))).trans (Category.id_comp _)))
  hL.trans (key.symm.trans
    (congrArg (fun z => (f.inverseImageCompLocalizationIso G).inv.app
        (Y.forgetRing.obj Y.O) ≫
      (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map z)
      (fSharpInverseImage_forget_homEquiv f)))

/-- **Stacks 04IH (7).** The localized morphism `(f', (f')♯)` of Stacks 04IF is a morphism of
locally ringed topoi as soon as `(f, f♯)` is: its units square is the image under the exact
functor `j_{f⁻¹G}⁻¹` of the units square of `f`, with the two bottom edges matched by 04IF's
comparison of inverse images.

The units subsheaf of a localization, and its inclusion, are the inverse image of those of the
original ringed topos on the nose, so the only comparison entering is 04IF's, whose two
components form a square of isomorphisms on the left of the pasting. -/
@[stacks 04IH "(7): the localized morphism `f'` of 04IF is a morphism of locally ringed topoi"]
theorem localized_isLocallyRinged (hf : f.IsLocallyRinged) :
    (f.localized G).IsLocallyRinged := by
  obtain ⟨t, ht⟩ := hf
  have := (X.localizationMorphism
    (f.toToposHom.inverseImage.obj G)).toToposHom.preservesFiniteLimits
  refine ⟨(f.inverseImageCompLocalizationIso G).inv.app (RingedTopos.units Y) ≫
    (X.localizationMorphism (f.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map t, ?_⟩
  rw [f.fSharpSet_localized G]
  exact isPullback_app_comp_map_of_isIso (f.inverseImageCompLocalizationIso G).inv
    (RingedTopos.unitsι Y) ht

/-- **Stacks 04IH (8).** The relocalized morphism `(f_s, f_s♯)` of Stacks 04J8 is a morphism of
locally ringed topoi as soon as `(f, f♯)` is.

Stacks 04J8 defines `f_s` as the morphism of 04IF composed with the relocalization morphism of
04J4 along `s`, the first locally ringed by clause (7) and the second by clause (6), and a
composite of locally ringed morphisms is locally ringed by Stacks 04IG. -/
@[stacks 04IH "(8): the relocalized morphism `f_s` of 04J8 is a morphism of locally ringed topoi"]
theorem relocalized_isLocallyRinged {F : X.Topos}
    (s : F ⟶ f.toToposHom.inverseImage.obj G) (hf : f.IsLocallyRinged) :
    (f.relocalized s).IsLocallyRinged :=
  isLocallyRinged_comp (f.localized G) (X.relocalizationMorphism s)
    (f.localized_isLocallyRinged G hf) (X.relocalizationMorphism_isLocallyRinged s)

end AlgebraicGeometry.RingedToposHom

end
