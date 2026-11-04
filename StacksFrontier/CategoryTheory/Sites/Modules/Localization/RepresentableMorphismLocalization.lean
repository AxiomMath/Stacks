module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposMorphismLocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedMorphism
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.LocalizationAndMorphismsOfTopoi

/-!
# Localizing a morphism of ringed sites at an object and localizing its ringed topos at the
associated sheaf

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites, given by a continuous functor
`u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`.  There are two ways to localize the
induced morphism of ringed topoi `f : (Sh(C), O) ⟶ (Sh(D), O')`.

* Stacks 04J0 localizes the morphism of *sites*, giving
  `(f', (f')♯) : (Sh(C/U), O_U) ⟶ (Sh(D/V), O'_V)` in a square with `j_U` and `j_V`.
* Stacks 04IF localizes the morphism of *ringed topoi* at the sheaf `G = h_V^#` on `D` and at
  `F = f^{-1}G` on `C`, giving `(Sh(C)/F, O_F) ⟶ (Sh(D)/G, O'_G)` in a square with `j_F`, `j_G`.

Stacks 04J7 says that these two squares agree via the identifications of Stacks 04J3 of the
localization of a ringed site at an object with the localization of its ringed topos at the
associated sheaf, `(j_F, j_F^♯) = (j_U, j_U^♯)` and `(j_G, j_G^♯) = (j_V, j_V^♯)`.  Since the
horizontal edges are identified by Stacks 04J3, the assertion is about the vertical edges, and
this file proves it in the three parts the source's proof splits into: the two `f'` have the same
inverse image, hence the same direct image, and the two `(f')^♯` are the same formula.

## Main definitions

* `AlgebraicGeometry.RingedSite.Hom.inverseImageRepresentableSheafIso`: Stacks 04D3's
  identification `F = f^{-1}h_V^# ≅ h_{u(V)}^#` of the two lower-left corners, written in the
  notation of Stacks 04J7.
* `AlgebraicGeometry.RingedSite.Hom.localizedSourceEquivalence`: the identification of the
  localization of the ringed topos at `F` with the localization at `h_U^#`, obtained from
  Stacks 04IE's slice identification and Stacks 04D3.
* `AlgebraicGeometry.RingedSite.Hom.sliceInverseImageIso`: Stacks 04IU packaged as an
  isomorphism of functors rather than as the equation of structure maps that it is stated as.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.localizedRepresentableInverseImageIso`: **Stacks 04J7** on
  inverse images.  Read through the identifications of Stacks 04J3 at `V` and at `U = u(V)`, and
  through Stacks 04D3 at the corner `F = f^{-1}h_V^#`, the inverse image of the localized
  morphism of ringed topoi of Stacks 04IF is the inverse image of the localized morphism of
  ringed sites of Stacks 04J0.
* `AlgebraicGeometry.RingedSite.Hom.localizedRepresentablePushforwardIso`: **Stacks 04J7** on
  direct images.  The two inverse images agree, so the two direct images agree by uniqueness of
  right adjoints.
* `AlgebraicGeometry.RingedSite.Hom.localizedRepresentable_forgetFSharp`: **Stacks 04J7** on
  structure maps.  Each of the two `(f')^♯` is the restriction `j^{-1}(f^♯)` of the structure map
  of `f` along its own localization morphism, which is what the source means by "the formulas
  defining `(f')^♯` agree".
* `AlgebraicGeometry.RingedToposHom.forgetFSharp_localized`: the half of that computation which
  belongs to Stacks 04IF, for an arbitrary morphism of ringed topoi and an arbitrary sheaf.

## Implementation notes

The source's proof is "for morphisms of topoi this is Sites, Lemma 7.31.2 (Stacks 04IU), and the
formulas defining `(f')^♯` in the proofs of the two lemmas agree".  Both halves are taken
literally here.

Stacks 04IU is formalized as `CategoryTheory.SliceTopos.underlyingIso_hom_app_comp_hom`, as the one
equation that is its content: the canonical isomorphism `j_{U!}(f')^{-1} ≅ f^{-1}j_{V!}` of the
proof of Stacks 03CF respects the structure maps to `h_U^#`, the right-hand one computed with
Stacks 04D3.  Feeding it to `CategoryTheory.Over.natIsoOfForgetIso` gives `sliceInverseImageIso`,
and the inverse-image half of Stacks 04J7 is that isomorphism transported across the two
equivalences of Stacks 04J3.  That transport is formal: the identification of Stacks 04J3 is
Stacks 00Y1's equivalence followed by Stacks 04IE's, the inverse image of Stacks 04IF's localized
morphism is `Over.post f^{-1}` read through Stacks 04IE's equivalence
(`AlgebraicGeometry.RingedToposHom.localizedInverseImageIso`), and the two occurrences of Stacks
04IE's equivalence at `G` cancel.  In particular no property of
`AlgebraicGeometry.RingedTopos.localizationEquivalence` beyond its being an equivalence is used,
which matters because that equivalence is a `Classical.choose`: the mathematical content of the
comparison is entirely in Stacks 04IU, and the choice cancels.

On the structure maps the source is even more economical, and so is this file.  Stacks 04J0's
`(f')^♯` is `j_V^{-1}(f^♯)` on the nose, because Stacks 03CF's clause (d) is a strict equality of
functors; that is recorded as
`AlgebraicGeometry.RingedSite.Hom.forgetFSharp_localizedRingedToposHom`.  Stacks 04IF's `(f')^♯`
is `j_G^{-1}(f^♯)` followed by the identification of its target `j_G^{-1}f_*O` with `f'_*O_F`,
which for a general sheaf `G` is a genuine isomorphism rather than an identity; that
identification is pinned as `AlgebraicGeometry.RingedToposHom.localizedStructureIso` and
`AlgebraicGeometry.RingedToposHom.forgetFSharp_localized` is the computation, whose content is
that the one remaining identification that the definition of
`AlgebraicGeometry.RingedToposHom.localized` inserts — of `O'_G` with `j_G^{-1}O'` — is the
identity on underlying sheaves of sets, so that the formula really is `j_G^{-1}` applied to `f^♯`.
So the two formulas are the same formula, which is the assertion.

Nothing here carries a hypothesis beyond the data of Stacks 04J7: a morphism of ringed sites
`(f, f♯)` — whose `u` is continuous and whose `f.isMorphismOfSites` is Stacks 00X1, both bundled
into `AlgebraicGeometry.RingedSite.Hom` — and an object `V` of the target site.  Stacks 03EF's
sufficient condition (the site `D` that `u` goes out of has all finite limits and `u` is left
exact) is strictly stronger than that, and is not assumed: `Over.post u` is continuous whenever
`u` is (`Functor.isContinuous_overPost_of_isContinuous`, the `local instance` above), so the
site-theoretic `f'` of Stacks 03CF, the diagram of Stacks 04J0 and Stacks 04IU all
exist in Stacks 03CF's own generality.  See the module docstrings of
`StacksFrontier/CategoryTheory/Sites/Modules/LocalizationRingedSites/LocalizedMorphism.lean` and
`StacksFrontier/CategoryTheory/Sites/SliceTopos/LocalizationAndMorphismsOfTopoi.lean`.

`AlgebraicGeometry.RingedToposHom.localizedStructureIso` and
`AlgebraicGeometry.RingedToposHom.forgetFSharp_localized` are stated for an arbitrary morphism of
ringed topoi and an arbitrary sheaf `G`, since nothing about `h_V^#` enters them; they belong to
Stacks 04IF and are placed here only because Stacks 04J7 is what needs them.

Universes follow Stacks 04J3 and Stacks 04IF: site objects, site morphisms and sections of the
structure sheaves are all taken in one universe `u`, which is what Stacks 0791 needs in order to
return a sheaf equivalence.

## References

* [Stacks Project, Tag 04J7](https://stacks.math.columbia.edu/tag/04J7)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04IU](https://stacks.math.columbia.edu/tag/04IU)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 04J3](https://stacks.math.columbia.edu/tag/04J3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

universe u

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y) (G : Y.Topos)

/-- **The identification that Stacks 04IF's formula for `(f')^♯` ends with.**  The source writes
```
  (f')^♯ : O'_G = j_G^{-1}O' --j_G^{-1}(f^♯)--> j_G^{-1}f_*O = f'_*j_F^{-1}O = f'_*O_F ,
```
and the last two equalities are canonical identifications of sheaves of commutative rings: the
comparison `j_G^{-1}f_* ≅ f'_*j_F^{-1}` of the two direct images, which Stacks 04IF supplies as
`localizedPushforwardCommRingIso`, followed by `f'_*` of the identification of `j_F^{-1}O` with
the localized structure sheaf `O_F`. -/
noncomputable def localizedStructureIso :
    (inverseImageCommRingFunctor (Y.localizationMorphism G).toToposHom).obj
        ((pushforwardCommRingFunctor f.toToposHom).obj X.O) ≅
      (pushforwardCommRingFunctor (localizedToposMorphism f G)).obj
        (X.localizedRingedTopos (f.toToposHom.inverseImage.obj G)).O :=
  ((localizedPushforwardCommRingIso f G).app X.O).symm ≪≫
    (pushforwardCommRingFunctor (localizedToposMorphism f G)).mapIso
      (X.localizationInverseImageCommRingIso (f.toToposHom.inverseImage.obj G))

/-- **Stacks 04IF**'s structure map, on underlying sheaves of sets: `(f')^♯` is the restriction
`j_G^{-1}(f^♯)` of the structure map of `f`, followed by the identification `localizedStructureIso`
of its target `j_G^{-1}f_*O` with `f'_*O_F`.  This is the first of the two adjoint descriptions
the source gives of `(f')^♯`, read off its definition.

The content of the computation is that the remaining identification that the definition of
`localized` inserts, the one of `O'_G` with `j_G^{-1}O'`, is the identity on underlying sheaves of
sets, so that the formula really is `j_G^{-1}` applied to `f^♯`. -/
theorem forgetFSharp_localized :
    forgetFSharp (localized f G) =
      (Y.localizationMorphism G).toToposHom.inverseImage.map (forgetFSharp f) ≫
        (Y.localizedRingedTopos G).forgetRing.map (localizedStructureIso f G).hom := by
  have hA : (Y.localizedRingedTopos G).forgetRing.map
      (Y.localizationInverseImageCommRingIso G).inv = 𝟙 _ := rfl
  have hB : (Y.localizedRingedTopos G).forgetRing.map
        ((inverseImageCommRingFunctor (Y.localizationMorphism G).toToposHom).map f.fSharp) =
      (Y.localizationMorphism G).toToposHom.inverseImage.map (forgetFSharp f) :=
    underlyingRingSheaf_map_pullbackCommRingSheafMap (Y.localizedRingedTopos G).J _ f.fSharp
  refine Eq.trans ((Y.localizedRingedTopos G).forgetRing.map_comp _ _) ?_
  refine Eq.trans (congrArg (fun z => z ≫ _) hA) ?_
  refine Eq.trans (Category.id_comp _) ?_
  refine Eq.trans ((Y.localizedRingedTopos G).forgetRing.map_comp _ _) ?_
  exact congrArg (fun z => z ≫ _) hB

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- The sheaf `F = f^{-1}h_V^#` of Stacks 04J7, at which Stacks 04IF localizes the source. -/
noncomputable abbrev Hom.inverseImageRepresentableSheaf : X.ringedTopos.Topos :=
  f.toposHom.inverseImage.obj (representableSheaf Y V)

/-- **Stacks 04D3** in the notation of Stacks 04J7: the identification `F = f^{-1}h_V^#` with
`h_{u(V)}^#` of the two lower-left corners of the two squares. -/
noncomputable abbrev Hom.inverseImageRepresentableSheafIso :
    f.inverseImageRepresentableSheaf V ≅ representableSheaf X (f.u.obj V) :=
  sheafPullbackSheafifyYonedaIso f.u Y.J X.J V

/-- **The identification of the two localizations of the source.** Stacks 04IF localizes the
ringed topos `(Sh(C), O)` at `F = f^{-1}h_V^#`, while Stacks 04J3 identifies `Sh(C/U)` with its
localization at `h_U^#`; Stacks 04D3's isomorphism `F ≅ h_U^#` identifies the two localizations,
through Stacks 04IE's identification of each with the corresponding slice topos. -/
noncomputable def Hom.localizedSourceEquivalence :
    (RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V)).Topos ≌
      (RingedTopos.localizedRingedTopos X.ringedTopos
        (representableSheaf X (f.u.obj V))).Topos :=
  (RingedTopos.localizationEquivalence X.ringedTopos (f.inverseImageRepresentableSheaf V)).trans
    ((Over.mapIso (f.inverseImageRepresentableSheafIso V)).trans
      (RingedTopos.localizationEquivalence X.ringedTopos
        (representableSheaf X (f.u.obj V))).symm)

/-- **Stacks 04IU as an isomorphism of functors.** Read through Stacks 00Y1's equivalences
`Sh(D/V) ≌ Sh(D)/h_V^#` and `Sh(C/U) ≌ Sh(C)/h_U^#` and through Stacks 04D3's identification of
the corner, the inverse image of the localized morphism of sites of Stacks 04J0 is
`Over.post f^{-1}`, the inverse image of the localized morphism of topoi of Stacks 04H1.

Stacks 04IU is formalized as the single equation that is its content — that the canonical isomorphism
`j_{U!}(f')^{-1} ≅ f^{-1}j_{V!}` of the proof of Stacks 03CF respects the structure maps to
`h_U^#` — and `CategoryTheory.Over.natIsoOfForgetIso` turns that equation, with the naturality
the underlying isomorphism already carries, into the isomorphism of functors. -/
noncomputable def Hom.sliceInverseImageIso :
    (f.localizedRingedToposHom V).toToposHom.inverseImage ⋙
        CategoryTheory.OverShriek.sheafFunctorToOver (U := f.u.obj V) X.J ≅
      CategoryTheory.OverShriek.sheafFunctorToOver (U := V) Y.J ⋙
        Over.post f.toposHom.inverseImage ⋙
          Over.map (f.inverseImageRepresentableSheafIso V).hom :=
  Over.natIsoOfForgetIso (CategoryTheory.SliceTopos.underlyingIso Y.J X.J f.u V)
    (CategoryTheory.SliceTopos.underlyingIso_hom_app_comp_hom f.isMorphismOfSites V)

/-- **Stacks 04IU, read through `Over.forget`.** The underlying map of a component of
`sliceInverseImageIso` is the corresponding component of Stacks 04IU's isomorphism of the
underlying sheaves.

`CategoryTheory.Over.natIsoOfForgetIso` builds its components with `Over.isoMk` out of the given
isomorphism of the composites with `Over.forget`, so this holds by `rfl`. Naming it is what makes
Stacks 04IU reachable from an equation in which `sliceInverseImageIso` appears: the two spellings
are definitionally equal but not syntactically, and no rewrite against the second form fires on
the first. -/
theorem Hom.left_sliceInverseImageIso_hom_app (G : Sheaf (Y.J.over V) (Type u)) :
    ((f.sliceInverseImageIso V).hom.app G).left =
      (CategoryTheory.SliceTopos.underlyingIso Y.J X.J f.u V).hom.app G :=
  rfl

/-- **Stacks 04IU through the lower shrieks.** The underlying map of a component of
`sliceInverseImageIso` is Stacks 00Y1's identification of the sheaf underlying `Φ_{u(V)}` with
`j_{u(V)!}`, followed by the comparison `j_{u(V)!}(f')^{-1} ≅ f^{-1}j_{V!}` of the proof of
Stacks 03CF, followed by `f^{-1}` of Stacks 00Y1's identification at `V`.

This is the form in which Stacks 04IU is consumed by an equation transposed across the lower
shriek: the middle factor `CategoryTheory.sheafPullbackOverPostIso` is exactly the one that
`CategoryTheory.SliceTopos.shriek_overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit`
produces from Stacks 03CF's clause (b), so after transposing both sides of such an equation the
two occurrences of Stacks 04IU and of clause (b) meet at the same morphism. -/
theorem Hom.left_sliceInverseImageIso_hom_app_eq (G : Sheaf (Y.J.over V) (Type u)) :
    ((f.sliceInverseImageIso V).hom.app G).left =
      (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app
          (((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
            (X.J.over (f.u.obj V))).obj G) ≫
        (CategoryTheory.sheafPullbackOverPostIso Y.J X.J f.u V (Type u)).hom.app G ≫
          (f.u.sheafPullback (Type u) Y.J X.J).map
            ((CategoryTheory.OverShriek.sheafFunctorToOverForgetIso Y.J).inv.app G) :=
  (f.left_sliceInverseImageIso_hom_app V G).trans
    (CategoryTheory.SliceTopos.underlyingIso_hom_app Y.J X.J f.u V G)

/-- The comparison of inverse images with values in the slice topos `Sh(C)/h_U^#`, before it is
carried into the localization of the ringed topos at `h_U^#` by Stacks 04IE.

Stacks 04IF's `localizedInverseImageIso` identifies the inverse image of its localized morphism,
read into the slice topos, with `Over.post f^{-1}`; the remaining occurrence of Stacks 04IE's
equivalence at `h_V^#` cancels against the one inside Stacks 04J3's identification at `V`, and
what is left is `sliceInverseImageIso`, which is Stacks 04IU. -/
noncomputable def Hom.localizedRepresentableSliceInverseImageIso :
    (Y.representableLocalizationEquivalence V).functor ⋙
        (RingedToposHom.localizedToposMorphism f.ringedToposHom
            (representableSheaf Y V)).inverseImage ⋙
          (RingedTopos.localizationEquivalence X.ringedTopos
            (f.inverseImageRepresentableSheaf V)).functor ⋙
            Over.map (f.inverseImageRepresentableSheafIso V).hom ≅
      (f.localizedRingedToposHom V).toToposHom.inverseImage ⋙
        CategoryTheory.OverShriek.sheafFunctorToOver (U := f.u.obj V) X.J :=
  Functor.isoWhiskerLeft _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (RingedToposHom.localizedInverseImageIso f.ringedToposHom (representableSheaf Y V))
          (Over.map (f.inverseImageRepresentableSheafIso V).hom)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (CategoryTheory.OverShriek.sheafFunctorToOver (U := V) Y.J)
          (RingedTopos.localizationEquivalence Y.ringedTopos
            (representableSheaf Y V)).counitIso ≪≫
        Functor.rightUnitor _)
      (Over.post f.toposHom.inverseImage ⋙
        Over.map (f.inverseImageRepresentableSheafIso V).hom) ≪≫
    Functor.associator _ _ _ ≪≫
    (f.sliceInverseImageIso V).symm

/-- **Stacks 04J7**, on inverse images.  Read through the identifications of Stacks 04J3 of
`Sh(D/V)` with the localization of the ringed topos at `h_V^#` and of `Sh(C/U)` with the
localization at `h_U^#`, and through Stacks 04D3's identification of `F = f^{-1}h_V^#` with
`h_U^#`, the inverse image of the morphism of ringed topoi that Stacks 04IF obtains by localizing
at `F` and `G = h_V^#` is the inverse image of the morphism of ringed topoi that Stacks 04J0
obtains by localizing the morphism of ringed sites at `V`. -/
@[stacks 04J7 "the two localized morphisms have the same inverse image, via the identifications
  of 04J3"]
noncomputable def Hom.localizedRepresentableInverseImageIso :
    (Y.representableLocalizationEquivalence V).functor ⋙
        (RingedToposHom.localizedToposMorphism f.ringedToposHom
            (representableSheaf Y V)).inverseImage ⋙
          (f.localizedSourceEquivalence V).functor ≅
      (f.localizedRingedToposHom V).toToposHom.inverseImage ⋙
        (X.representableLocalizationEquivalence (f.u.obj V)).functor :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (f.localizedRepresentableSliceInverseImageIso V)
      (RingedTopos.localizationEquivalence X.ringedTopos
        (representableSheaf X (f.u.obj V))).inverse ≪≫
    Functor.associator _ _ _

/-- **Stacks 04J7**, on direct images.  Read through the same identifications, the direct image
of Stacks 04IF's localized morphism is the direct image of Stacks 04J0's localized morphism.  The
two inverse images agree, so the two direct images agree by uniqueness of right adjoints. -/
@[stacks 04J7 "the two localized morphisms have the same direct image"]
noncomputable def Hom.localizedRepresentablePushforwardIso :
    ((f.localizedSourceEquivalence V).inverse ⋙
          (RingedToposHom.localizedToposMorphism f.ringedToposHom
            (representableSheaf Y V)).pushforward) ⋙
        (Y.representableLocalizationEquivalence V).inverse ≅
      (X.representableLocalizationEquivalence (f.u.obj V)).inverse ⋙
        (f.localizedRingedToposHom V).toToposHom.pushforward :=
  Adjunction.rightAdjointUniq
    (((Y.representableLocalizationEquivalence V).toAdjunction.comp
        ((RingedToposHom.localizedToposMorphism f.ringedToposHom
              (representableSheaf Y V)).adj.comp
          (f.localizedSourceEquivalence V).toAdjunction)).ofNatIsoLeft
      (f.localizedRepresentableInverseImageIso V))
    ((f.localizedRingedToposHom V).toToposHom.adj.comp
      (X.representableLocalizationEquivalence (f.u.obj V)).toAdjunction)

/-- **Stacks 04J7**, on structure maps: the two `(f')^♯` are the same formula, each being the
restriction `j^{-1}(f^♯)` of the structure map of `f` along its own localization morphism — along
`j_V` for Stacks 04J0 and along `j_G` for Stacks 04IF — and Stacks 04J3 identifies
`(j_G, j_G^♯)` with `(j_V, j_V^♯)`.

For Stacks 04J0 the restriction is the whole formula, because Stacks 03CF's clause (d) is a
strict equality of functors `f'_*j_U^{-1} = j_V^{-1}f_*`.  For Stacks 04IF, where `G` is an
arbitrary sheaf, that identity is only an isomorphism, and the formula is the restriction followed
by it; the identifications of sheaves of commutative rings that Stacks 04IF's definition inserts
contribute nothing, being the identity on underlying sheaves of sets. -/
@[stacks 04J7 "the two maps (f')^sharp agree, each being the restriction j^{-1}(f^sharp) of the
  structure map of f along its own localization morphism"]
theorem Hom.localizedRepresentable_forgetFSharp :
    AlgebraicGeometry.RingedToposHom.forgetFSharp (f.localizedRingedToposHom V) =
        (Y.overMorphismOfTopoi V).inverseImage.map
          (AlgebraicGeometry.RingedToposHom.forgetFSharp f.ringedToposHom) ∧
      AlgebraicGeometry.RingedToposHom.forgetFSharp
          (AlgebraicGeometry.RingedToposHom.localized f.ringedToposHom
            (representableSheaf Y V)) =
        (RingedTopos.localizationMorphism Y.ringedTopos
              (representableSheaf Y V)).toToposHom.inverseImage.map
            (AlgebraicGeometry.RingedToposHom.forgetFSharp f.ringedToposHom) ≫
          (RingedTopos.localizedRingedTopos Y.ringedTopos
              (representableSheaf Y V)).forgetRing.map
            (AlgebraicGeometry.RingedToposHom.localizedStructureIso f.ringedToposHom
              (representableSheaf Y V)).hom :=
  ⟨f.forgetFSharp_localizedRingedToposHom V,
    AlgebraicGeometry.RingedToposHom.forgetFSharp_localized f.ringedToposHom
      (representableSheaf Y V)⟩

end AlgebraicGeometry.RingedSite

end
