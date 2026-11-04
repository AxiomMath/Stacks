module

public import StacksFrontier.AlgebraicGeometry.Recovery04IH.LocalizedMorphismsLocallyRinged
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.ToposHomUnitsSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RelocalizedMorphismComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The two localized morphisms of Stacks 04J7 as morphisms *into one localized ringed topos*

Let `(f, f♯) : (C, O) ⟶ (D, O')` be a morphism of ringed sites given by a continuous functor
`u : D ⥤ C`, let `V` be an object of `D` and put `U = u(V)`, `G = h_V^#` and `F = f^{-1}G`.
Stacks 04J7 compares two squares:

* the square of Stacks 04J0, whose vertical edge is the localized morphism of *sites*
  `f' : (Sh(C/U), O_U) ⟶ (Sh(D/V), O'_V)`;
* the square of Stacks 04IF, whose vertical edge is the localized morphism of *ringed topoi*
  `f' : (Sh(C)/F, O_F) ⟶ (Sh(D)/G, O'_G)`.

`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RepresentableMorphismLocalization.lean`
compares the two vertical edges themselves: their inverse images agree, hence their direct
images, and the two `(f')^♯` are the same formula. Promoting that to a 2-isomorphism of
morphisms of ringed topoi — which is what a comparison of the two *squares* is pasted from —
requires the comparison to be read not between the two `f'` but between the two composites

```
  ι_V ∘ f'_{04J0}  and  f'_{04IF} ∘ compareMid ,
```

both morphisms of ringed topoi from `(Sh(C/U), O_U)` to the localization of `(Sh(D), O')` at
`G`, where `ι_V` and `compareMid` are the identifications of Stacks 04J3 at `V` and at the
middle corner. This file supplies the comparison of the inverse images of those two composites,
which is the datum that
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` consumes.

## Main definitions

* `CategoryTheory.Over.pullbackIsoMap`: base change along the inverse of an isomorphism is
  `CategoryTheory.Over.map` along the isomorphism.
* `AlgebraicGeometry.RingedSite.Hom.localizedSourceEquivalenceFunctorIso`: the identification
  of the two localizations of the source of Stacks 04J7 is the inverse image of the
  relocalization morphism of Stacks 04J4 along Stacks 04D3's isomorphism `h_U^# ⟶ F`.
* `AlgebraicGeometry.RingedSite.Hom.localizedRepresentableCompInverseImageIso`: **Stacks 04J7**
  on inverse images, between the two composites above rather than between the two `f'`.

## Main results

* `AlgebraicGeometry.RingedSite.Hom.forgetRing_representableComp_fSharpInverseImage` and
  `AlgebraicGeometry.RingedSite.Hom.forgetRing_localizedCompareMidComp_fSharpInverseImage`: the
  structure maps of the two composites, in inverse-image form and on underlying sheaves of sets,
  computed. Both end in `j_U^{-1}` applied to the structure map of `f`, which is what reduces
  the compatibility that the 2-isomorphism needs to an equation with no structure map in it.
* `AlgebraicGeometry.RingedSite.Hom.forgetRing_compareMid_fSharpInverseImage`: the structure map
  of the middle identification of Stacks 04J3 is that identification's own comparison of inverse
  images; the relocalization of Stacks 04J4 inside it contributes the identity.
* `AlgebraicGeometry.RingedToposHom.forgetRing_localized_fSharpInverseImage_eq`: Stacks 04IF's
  structure-map compatibility with the comparison moved to the other side, which is the form a
  composite of structure maps consumes.

## Implementation notes

**What the relocalization identification unblocks.** Stacks 04IF localizes the source ringed
topos at `F = f^{-1}h_V^#` while Stacks 04J3 presents `Sh(C/U)` as the localization at
`h_U^#`, so the two comparisons of Stacks 04J7 and of Stacks 04J9 have different sources, and
Stacks 04D3's isomorphism `e : F ≅ h_U^#` has to move one onto the other. There are two ways to
do that: `AlgebraicGeometry.RingedSite.Hom.localizedSourceEquivalence` moves it by base change
in the slice presentation, and `AlgebraicGeometry.RingedTopos.relocalizationMorphism e.inv`
moves it by the relocalization morphism of Stacks 04J4, which is what the morphisms of ringed
topoi in the comparison are built from.
`AlgebraicGeometry.RingedSite.Hom.localizedSourceEquivalenceFunctorIso` identifies the two, and
it is exactly Stacks 04J4's assertion that the inverse image of a relocalization is base
change, which is
`AlgebraicGeometry.RingedTopos.relocalizationInverseImageSliceIso`: base change along `e.inv`
is `CategoryTheory.Over.map e.hom` because `e` is invertible, and whiskering with the
equivalence of Stacks 04IE at `h_U^#` is cancelled by
`CategoryTheory.Functor.fullyFaithfulCancelRight`.

**Why the comparison is restated for the composites.** The comparison of the two `f'` is an
isomorphism of inverse-image functors read *through* the equivalences of Stacks 04J3, i.e. with
those equivalences whiskered onto it. A 2-isomorphism of morphisms of ringed topoi, on the other
hand, is an isomorphism of the inverse images of two morphisms with the *same source and
target*; the two composites above are such a pair, and the equivalences of Stacks 04J3 are
absorbed into them. The two statements carry the same information — the passage from one to the
other is the unit and the counit of the two equivalences — but only the second has the shape
that the calculus of 2-isomorphisms accepts.

**What is still owed for the 2-isomorphism, exactly.** Feeding
`localizedRepresentableCompInverseImageIso` to
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` needs one further equation: that the
comparison carries the inverse-image form of the structure map of `ι_V ∘ f'_{04J0}` to that of
`f'_{04IF} ∘ compareMid`. The two structure-map computations in this file evaluate both sides of
that equation, and both end in the same factor `j_U^{-1}(f^♯)`, so what is left of it is the
equation of the two factors in front, which mentions no structure map:
```
  localizedRepresentableCompInverseImageIso.hom.app O'_G ≫
      (f')⁻¹((representableLocalizationInverseImageIso Y V).hom.app O') ≫
        (overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V).hom.app O'
    = compareMid⁻¹((inverseImageCompLocalizationIso f h_V^#).inv.app O') ≫
        midInverseImageComparison.app (f⁻¹O') .
```
In words: this comparison, followed by the comparison of inverse images of Stacks 04J3 at `V`
and by Stacks 03CF's clause (b), is Stacks 04IF's comparison of inverse images followed by the
comparison of Stacks 04J3 at the middle corner, read at the sheaf `O'`. That it is sufficient is
not a guess: the two structure-map computations and three associativities derive the hypothesis
of `TwoIso.ofInverseImageIso` from it, and nothing else is needed. It is left out of this file
rather than stated with that equation as a hypothesis, which would be an assumption standing in
for the conclusion. Its conjugate is the compatibility of the two squares that
`AlgebraicGeometry.RingedSite.Hom.locSquareCompareSite` and
`AlgebraicGeometry.RingedSite.Hom.locSquareCompareTopos` are compared by, so one proof settles
both.

That equation is not formal. The comparison of this file is built from Stacks 04IU
(`CategoryTheory.SliceTopos.underlyingIso`, a statement about the lower shrieks) while the
right-hand side is built from Stacks 04IF's comparison, so relating them means transposing the
equation across the lower shriek of the localization at `U`, where
`CategoryTheory.SliceTopos.shriek_overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit`
describes the left-hand side and
`AlgebraicGeometry.RingedTopos.forget_localizationInverseImageIso_hom_app` with
`AlgebraicGeometry.RingedTopos.fibreTranspose` the right-hand one.

Universes follow Stacks 04J3 and Stacks 04IF: site objects, site morphisms and sections of the
structure sheaves are all taken in one universe `u`, which is what Stacks 0791 needs in order to
return a sheaf equivalence.

## References

* [Stacks Project, Tag 04J7](https://stacks.math.columbia.edu/tag/04J7)
* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04IF](https://stacks.math.columbia.edu/tag/04IF)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 04J3](https://stacks.math.columbia.edu/tag/04J3)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedToposHom

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- **Naturality against a composite, applied under the second factor.** For functors
`L : C₁ ⥤ C₂` and `M : C₂ ⥤ C₃`, a transformation `η : L ⋙ M ⟶ N`, a morphism `φ : A ⟶ B` of
`C₁` and a morphism `ψ : Z ⟶ L A` of `C₂`, applying `M` to `ψ ≫ L φ` and following by `η` at `B`
is `M ψ` followed by `η` at `A` and by `N φ`.

This is `Functor.map_comp`, associativity and `NatTrans.naturality` in one step. Stated with the
three functors abstract on purpose: in the composites it is used on, `L ⋙ M` and the source of
`η` are definitionally but not syntactically equal, and performing the three steps separately
there makes the elaborator check that identification once per step inside a `congrArg` motive,
which it cannot afford. -/
theorem map_comp_comp_naturality {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂}
    [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃] (L : C₁ ⥤ C₂) (M : C₂ ⥤ C₃)
    (N : C₁ ⥤ C₃) (η : L ⋙ M ⟶ N) {A B : C₁} (φ : A ⟶ B) {Z : C₂} (ψ : Z ⟶ L.obj A) :
    M.map (ψ ≫ L.map φ) ≫ η.app B = M.map ψ ≫ η.app A ≫ N.map φ :=
  Eq.trans (congrArg (fun z => z ≫ η.app B) (M.map_comp ψ (L.map φ)))
    (Eq.trans (Category.assoc (M.map ψ) (M.map (L.map φ)) (η.app B))
      (congrArg (fun z => M.map ψ ≫ z) (η.naturality φ)))

end Stacks.CategoryTheory

namespace CategoryTheory.Over

universe v' u'

variable {E : Type u'} [Category.{v'} E] [HasPullbacks E] {H K : E}

/-- **Base change along the inverse of an isomorphism is `Over.map` along the isomorphism.**
For `e : K ≅ H`, the functor `Over.map e.inv : Over H ⥤ Over K` is an equivalence with inverse
`Over.map e.hom`, and it is also left adjoint to `Over.pullback e.inv`; so the two right
adjoints agree by uniqueness. -/
noncomputable def pullbackIsoMap (e : K ≅ H) : Over.pullback e.inv ≅ Over.map e.hom :=
  Adjunction.rightAdjointUniq (Over.mapPullbackAdj e.inv) (Over.mapIso e.symm).toAdjunction

end CategoryTheory.Over

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp
  CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- The identification of the two localizations of the source, whiskered with the equivalence of
Stacks 04IE at `h_U^#`: both composites are the equivalence at `F` followed by base change along
Stacks 04D3's isomorphism, read as `CategoryTheory.Over.map`.

The left-hand side is `localizedSourceEquivalence` by definition, up to the counit of the
equivalence at `h_U^#`; the right-hand side is Stacks 04J4's comparison of the inverse image of
the relocalization with base change, composed with `CategoryTheory.Over.pullbackIsoMap`. -/
noncomputable def Hom.localizedSourceEquivalenceWhiskerIso :
    (f.localizedSourceEquivalence V).functor ⋙
        (RingedTopos.localizationEquivalence X.ringedTopos
          (representableSheaf X (f.u.obj V))).functor ≅
      (X.ringedTopos.relocalizationMorphism
            (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage ⋙
        (RingedTopos.localizationEquivalence X.ringedTopos
          (representableSheaf X (f.u.obj V))).functor :=
  (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (RingedTopos.localizationEquivalence X.ringedTopos
          (f.inverseImageRepresentableSheaf V)).functor
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (Over.map (f.inverseImageRepresentableSheafIso V).hom)
            (RingedTopos.localizationEquivalence X.ringedTopos
              (representableSheaf X (f.u.obj V))).counitIso ≪≫
          Functor.rightUnitor _)) ≪≫
    Functor.isoWhiskerLeft
      (RingedTopos.localizationEquivalence X.ringedTopos
        (f.inverseImageRepresentableSheaf V)).functor
      (Over.pullbackIsoMap (f.inverseImageRepresentableSheafIso V)).symm ≪≫
    (RingedTopos.relocalizationInverseImageSliceIso X.ringedTopos
      (f.inverseImageRepresentableSheafIso V).inv).symm

/-- **The two ways of moving the source of Stacks 04IF's localized morphism onto the source of
Stacks 04J0's agree.** Stacks 04IF localizes at `F = f^{-1}h_V^#` and Stacks 04J3 presents
`Sh(C/U)` as the localization at `h_U^#`; Stacks 04D3's isomorphism `e : F ≅ h_U^#` moves one
onto the other either by base change in the slice presentation, which is
`AlgebraicGeometry.RingedSite.Hom.localizedSourceEquivalence`, or by the relocalization morphism
of Stacks 04J4 along `e.inv`, which is what the morphisms of ringed topoi in the comparison of
Stacks 04J7 are built from. The two agree, by Stacks 04J4.

The equivalence of Stacks 04IE at `h_U^#` is fully faithful, so it may be cancelled from
`localizedSourceEquivalenceWhiskerIso`. -/
noncomputable def Hom.localizedSourceEquivalenceFunctorIso :
    (f.localizedSourceEquivalence V).functor ≅
      (X.ringedTopos.relocalizationMorphism
        (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage :=
  Functor.fullyFaithfulCancelRight
    (RingedTopos.localizationEquivalence X.ringedTopos
      (representableSheaf X (f.u.obj V))).functor
    (f.localizedSourceEquivalenceWhiskerIso V)

/-- **Stacks 04J7 on inverse images, between the two composites with the identifications of
Stacks 04J3.** The inverse image of `f'_{04IF} ∘ compareMid` is the inverse image of
`ι_V ∘ f'_{04J0}`, as functors from the localization of `(Sh(D), O')` at `h_V^#` to `Sh(C/U)`.

This is `AlgebraicGeometry.RingedSite.Hom.localizedRepresentableInverseImageIso`, which compares
the two `f'` with the equivalences of Stacks 04J3 whiskered onto it, read instead between the
two composites: the equivalence at `V` is absorbed by its counit, the equivalence at `U` by its
unit, and the identification of the two localizations of the source is turned into the inverse
image of the relocalization of Stacks 04J4 by
`localizedSourceEquivalenceFunctorIso`. It is the comparison that
`AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` consumes. -/
noncomputable def Hom.localizedRepresentableCompInverseImageIso :
    (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (f.ringedToposHom.localized (representableSheaf Y V))
        (f.compareMid V)).toToposHom.inverseImage ≅
      (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := ringedTopos (Y.over V))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (representableLocalizationRingedMorphism Y V)
        (f.localizedRingedToposHom V)).toToposHom.inverseImage :=
  Functor.isoWhiskerLeft
      (RingedToposHom.localizedToposMorphism f.ringedToposHom
        (representableSheaf Y V)).inverseImage
      (Functor.isoWhiskerRight (f.localizedSourceEquivalenceFunctorIso V).symm
        (X.representableLocalizationEquivalence (f.u.obj V)).inverse) ≪≫
    Functor.isoWhiskerRight
      ((Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (Y.representableLocalizationEquivalence V).counitIso.symm
          ((RingedToposHom.localizedToposMorphism f.ringedToposHom
              (representableSheaf Y V)).inverseImage ⋙
            (f.localizedSourceEquivalence V).functor) ≪≫
        Functor.isoWhiskerLeft (Y.representableLocalizationEquivalence V).inverse
          (f.localizedRepresentableInverseImageIso V))
      (X.representableLocalizationEquivalence (f.u.obj V)).inverse ≪≫
    Functor.isoWhiskerLeft
      ((Y.representableLocalizationEquivalence V).inverse ⋙
        (f.localizedRingedToposHom V).toToposHom.inverseImage)
      (X.representableLocalizationEquivalence (f.u.obj V)).unitIso.symm ≪≫
    Functor.rightUnitor _

end AlgebraicGeometry.RingedSite

/-! ### Comparisons of inverse images are atoms below this point

Every comparison appearing in the computations that follow is a composite of several whiskered
isomorphisms of functors between sheaf categories, and none of them is ever opened: they are
only ever passed from one equation to the next. Left reducible, a `congrArg` whose motive
mentions one of them sends the elaborator into the whole composite to check a type that two
definitional unfoldings would settle, which is what exhausts its budget here. The same
declaration is marked the same way, for the same reason, in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RelocalizedMorphismComparison.lean`. -/
attribute [local irreducible]
  AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso
  AlgebraicGeometry.RingedSite.representableLocalizationInverseImageIso
  AlgebraicGeometry.RingedSite.Hom.localizedRepresentableInverseImageIso
  AlgebraicGeometry.RingedSite.Hom.localizedRepresentableCompInverseImageIso
  CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso

namespace AlgebraicGeometry.RingedToposHom

variable {A B : RingedTopos.{u, u, u}} (g : RingedToposHom A B) (G : B.Topos)

/-- **Stacks 04IF's structure map in inverse-image form, read on the other side of the
comparison.** `localized_fSharpInverseImage_forget` states the compatibility as an equation
whose left-hand side begins with the comparison of inverse images; this is the same equation
with the comparison moved across, which is the form a composite of structure maps needs.

The two are related by `Iso.inv_hom_id_app` alone, written as an explicit term because the
pattern prints identically to the target subterm and no rewrite fires. -/
theorem forgetRing_localized_fSharpInverseImage_eq :
    (A.localizedRingedTopos (g.toToposHom.inverseImage.obj G)).forgetRing.map
        (g.localized G).fSharpInverseImage =
      (g.inverseImageCompLocalizationIso G).inv.app (B.forgetRing.obj B.O) ≫
        (A.localizationMorphism
            (g.toToposHom.inverseImage.obj G)).toToposHom.inverseImage.map
          (A.forgetRing.map g.fSharpInverseImage) :=
  Eq.trans (Category.id_comp _).symm
    (Eq.trans (congrArg (fun z => z ≫
          (A.localizedRingedTopos (g.toToposHom.inverseImage.obj G)).forgetRing.map
            (g.localized G).fSharpInverseImage)
        (Iso.inv_hom_id_app (g.inverseImageCompLocalizationIso G)
          (B.forgetRing.obj B.O)).symm)
      (Eq.trans (Category.assoc
          ((g.inverseImageCompLocalizationIso G).inv.app (B.forgetRing.obj B.O))
          ((g.inverseImageCompLocalizationIso G).hom.app (B.forgetRing.obj B.O))
          ((A.localizedRingedTopos (g.toToposHom.inverseImage.obj G)).forgetRing.map
            (g.localized G).fSharpInverseImage))
        (congrArg (fun z => (g.inverseImageCompLocalizationIso G).inv.app
            (B.forgetRing.obj B.O) ≫ z)
          (localized_fSharpInverseImage_forget g G))))

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp
  CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

/-! ### The structure maps of the two composites, in inverse-image form

The compatibility that `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` asks of
`localizedRepresentableCompInverseImageIso` is an equation between the inverse-image forms of
the structure maps of the two composites. The three computations below evaluate those two
structure maps completely, which is what turns that compatibility into an equation with no
structure map in it: both sides acquire the same last factor `j_U^{-1}(f^♯)`, and what is left
in front is a comparison of inverse images. -/

/-- **Stacks 04J3's structure map, in inverse-image form**: the structure map of the
identification of the localization of a ringed site at an object with the localization of its
ringed topos at the associated sheaf is, on underlying sheaves of sets, Stacks 04J3's comparison
of inverse images evaluated at `O`. -/
theorem forgetRing_representableLocalizationRingedMorphism_fSharpInverseImage
    (Z : RingedSite.{u, u, u}) (U : Z.C) :
    (ringedTopos (Z.over U)).forgetRing.map
        (representableLocalizationRingedMorphism Z U).fSharpInverseImage =
      (Z.representableLocalizationInverseImageIso U).hom.app
        ((ringedTopos Z).forgetRing.obj Z.O) := by
  rw [representableLocalizationRingedMorphism_fSharpInverseImage]
  exact representableLocalizationStructureSheafIso_hom_forget Z U

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- `compareMid` is the composite it is defined to be.

Giving the unfolding a name is load-bearing rather than cosmetic: a lemma about a composite,
applied to `compareMid` with the two factors left to unification, makes the elaborator search
for them under a definition whose instance arguments are large, and that search diverges. With
the equation named, the unfolding is a `congrArg` against a closed term. -/
theorem Hom.compareMid_eq :
    f.compareMid V =
      AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos
          (representableSheaf X (f.u.obj V)))
        (Z := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (X.ringedTopos.relocalizationMorphism (f.inverseImageRepresentableSheafIso V).inv)
        (representableLocalizationRingedMorphism X (f.u.obj V)) :=
  rfl

/-- `Hom.forgetRing_compareMid_fSharpInverseImage` for the composite that `compareMid` is. -/
theorem Hom.forgetRing_compareMidComp_fSharpInverseImage :
    (ringedTopos (X.over (f.u.obj V))).forgetRing.map
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
          (Y := RingedTopos.localizedRingedTopos X.ringedTopos
            (representableSheaf X (f.u.obj V)))
          (Z := RingedTopos.localizedRingedTopos X.ringedTopos
            (f.inverseImageRepresentableSheaf V))
          (X.ringedTopos.relocalizationMorphism (f.inverseImageRepresentableSheafIso V).inv)
          (representableLocalizationRingedMorphism X (f.u.obj V))).fSharpInverseImage =
      (X.representableLocalizationInverseImageIso (f.u.obj V)).hom.app
        ((ringedTopos X).forgetRing.obj X.O) := by
  refine Eq.trans (comp_fSharpInverseImage_forget
    (X := ringedTopos (X.over (f.u.obj V)))
    (Y := RingedTopos.localizedRingedTopos X.ringedTopos (representableSheaf X (f.u.obj V)))
    (Z := RingedTopos.localizedRingedTopos X.ringedTopos (f.inverseImageRepresentableSheaf V))
    (X.ringedTopos.relocalizationMorphism (f.inverseImageRepresentableSheafIso V).inv)
    (representableLocalizationRingedMorphism X (f.u.obj V))) ?_
  refine Eq.trans (congrArg (fun z =>
      (representableLocalizationRingedMorphism X (f.u.obj V)).toToposHom.inverseImage.map z ≫
        (ringedTopos (X.over (f.u.obj V))).forgetRing.map
          (representableLocalizationRingedMorphism X (f.u.obj V)).fSharpInverseImage)
    (forgetRing_relocalizationMorphism_fSharpInverseImage X.ringedTopos
      (f.inverseImageRepresentableSheafIso V).inv)) ?_
  refine Eq.trans (congrArg (fun z => z ≫
      (ringedTopos (X.over (f.u.obj V))).forgetRing.map
        (representableLocalizationRingedMorphism X (f.u.obj V)).fSharpInverseImage)
    ((representableLocalizationRingedMorphism X
      (f.u.obj V)).toToposHom.inverseImage.map_id _)) ?_
  exact (Category.id_comp _).trans
    (forgetRing_representableLocalizationRingedMorphism_fSharpInverseImage X (f.u.obj V))

/-- **The structure map of the middle identification, in inverse-image form**: it is Stacks
04J3's comparison of inverse images at `U`. The relocalization of Stacks 04J4 that `compareMid`
is composed with contributes the identity. -/
theorem Hom.forgetRing_compareMid_fSharpInverseImage :
    (ringedTopos (X.over (f.u.obj V))).forgetRing.map (f.compareMid V).fSharpInverseImage =
      (X.representableLocalizationInverseImageIso (f.u.obj V)).hom.app
        ((ringedTopos X).forgetRing.obj X.O) :=
  f.forgetRing_compareMidComp_fSharpInverseImage V

/-- **The inverse image of `j_F` followed by that of `compareMid` is the inverse image of
`j_{h_U^#}` followed by the equivalence of Stacks 04J3**, on the nose: the relocalization
triangle of Stacks 04J4 is a strict identity on inverse images
(`AlgebraicGeometry.RingedTopos.comp_inverseImage`), and the remaining factor of `compareMid` is
that equivalence.

Named for the same reason as `Hom.compareMid_eq`: the two spellings are definitionally equal but
not syntactically, so the naturality of Stacks 04J3's comparison has to be transported across
them by an explicit term. -/
theorem Hom.compareMid_inverseImage_map_localization_map {A B : X.ringedTopos.Topos}
    (φ : A ⟶ B) :
    (f.compareMid V).toToposHom.inverseImage.map
        ((X.ringedTopos.localizationMorphism
          (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage.map φ) =
      ((X.ringedTopos.localizationMorphism
            (representableSheaf X (f.u.obj V))).toToposHom.inverseImage ⋙
        (X.representableLocalizationEquivalence (f.u.obj V)).inverse).map φ :=
  rfl

/-- **The structure map of `ι_V ∘ f'_{04J0}`, in inverse-image form.** It is Stacks 04J3's
comparison at `V` restricted along `f'`, followed by Stacks 03CF's clause (b) at `O'`, followed
by `j_U^{-1}` of the structure map of `f`. -/
theorem Hom.forgetRing_representableComp_fSharpInverseImage :
    (ringedTopos (X.over (f.u.obj V))).forgetRing.map
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
          (Y := ringedTopos (Y.over V))
          (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
          (representableLocalizationRingedMorphism Y V)
          (f.localizedRingedToposHom V)).fSharpInverseImage =
      (f.localizedRingedToposHom V).toToposHom.inverseImage.map
          ((Y.representableLocalizationInverseImageIso V).hom.app
            ((ringedTopos Y).forgetRing.obj Y.O)) ≫
        (CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
              f.isMorphismOfSites).hom.app ((ringedTopos Y).forgetRing.obj Y.O) ≫
          (X.J.overPullback (Type u) (f.u.obj V)).map
            ((ringedTopos X).forgetRing.map f.ringedToposHom.fSharpInverseImage) := by
  refine Eq.trans (comp_fSharpInverseImage_forget
    (X := ringedTopos (X.over (f.u.obj V)))
    (Y := ringedTopos (Y.over V))
    (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
    (representableLocalizationRingedMorphism Y V) (f.localizedRingedToposHom V)) ?_
  refine Eq.trans (congrArg (fun z =>
      (f.localizedRingedToposHom V).toToposHom.inverseImage.map z ≫
        (ringedTopos (X.over (f.u.obj V))).forgetRing.map
          (f.localizedRingedToposHom V).fSharpInverseImage)
    (forgetRing_representableLocalizationRingedMorphism_fSharpInverseImage Y V)) ?_
  refine congrArg (fun z => (f.localizedRingedToposHom V).toToposHom.inverseImage.map
      ((Y.representableLocalizationInverseImageIso V).hom.app
        ((ringedTopos Y).forgetRing.obj Y.O)) ≫ z) ?_
  refine Eq.trans
    (forgetRing_map_fSharpInverseImage_eq_fSharpSet (f.localizedRingedToposHom V)) ?_
  refine Eq.trans (f.fSharpSet_localizedRingedToposHom V) ?_
  exact congrArg (fun z => (CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso
      Y.J X.J f.u V f.isMorphismOfSites).hom.app ((ringedTopos Y).forgetRing.obj Y.O) ≫
    (X.J.overPullback (Type u) (f.u.obj V)).map z)
    (forgetRing_map_fSharpInverseImage_eq_fSharpSet f.ringedToposHom).symm

/-- `AlgebraicGeometry.RingedToposHom.forgetRing_localized_fSharpInverseImage_eq` with the sheaf
`F` spelled as `Hom.inverseImageRepresentableSheaf`, the spelling every other statement about
Stacks 04J7 uses.

The two spellings differ in whether the inverse image is taken along the morphism of topoi of
`f` or along the morphism of ringed topoi it induces. They are definitionally equal, and the one
`:=` below is the only place that has to know it: performing the identification once, between
two closed terms, costs a single definitional check, whereas leaving it to be rediscovered
inside the unification of each later rewrite does not terminate within the elaborator's
budget. -/
theorem Hom.forgetRing_localizedRepresentable_fSharpInverseImage_eq :
    (RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V)).forgetRing.map
        (f.ringedToposHom.localized (representableSheaf Y V)).fSharpInverseImage =
      (f.ringedToposHom.inverseImageCompLocalizationIso (representableSheaf Y V)).inv.app
          ((ringedTopos Y).forgetRing.obj Y.O) ≫
        (X.ringedTopos.localizationMorphism
            (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage.map
          ((ringedTopos X).forgetRing.map f.ringedToposHom.fSharpInverseImage) :=
  AlgebraicGeometry.RingedToposHom.forgetRing_localized_fSharpInverseImage_eq
    f.ringedToposHom (representableSheaf Y V)

/-- **Stacks 04J3's comparison at `U`, typed as a transformation out of
`j_F^{-1} ⋙ compareMid^{-1}`.** This is the same transformation as
`representableLocalizationInverseImageIso`, at a source functor that is definitionally but not
syntactically the stated one; naming it is what lets a lemma about `L ⋙ M` be applied without
the elaborator having to discover that identification during unification. -/
noncomputable def Hom.midInverseImageComparison :
    (X.ringedTopos.localizationMorphism
          (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage ⋙
        (f.compareMid V).toToposHom.inverseImage ⟶
      X.J.overPullback (Type u) (f.u.obj V) :=
  (X.representableLocalizationInverseImageIso (f.u.obj V)).hom

/-- `midInverseImageComparison` has the components of Stacks 04J3's comparison. -/
theorem Hom.midInverseImageComparison_app (A : X.ringedTopos.Topos) :
    (f.midInverseImageComparison V).app A =
      (X.representableLocalizationInverseImageIso (f.u.obj V)).hom.app A :=
  rfl

/-- The value of `midInverseImageComparison` at `O` is the structure map of `compareMid` in
inverse-image form. This is `Hom.forgetRing_compareMid_fSharpInverseImage` with the two sides
exchanged, which is not redundant: the objects of the common type are read off whichever side
is written first, and only this orientation spells the source as
`(j_F^{-1} ⋙ compareMid^{-1}) O`, the spelling under which a composite with it is type-correct
without unfolding the structure sheaf of the localized ringed topos. -/
theorem Hom.midInverseImageComparison_app_structureSheaf :
    (f.midInverseImageComparison V).app ((ringedTopos X).forgetRing.obj X.O) =
      (ringedTopos (X.over (f.u.obj V))).forgetRing.map (f.compareMid V).fSharpInverseImage :=
  ((f.forgetRing_compareMid_fSharpInverseImage V).trans
    (f.midInverseImageComparison_app V ((ringedTopos X).forgetRing.obj X.O)).symm).symm

/-! From here on `compareMid` is an atom too. Everything about it that needs its definition —
its structure map, its inverse image on a restriction, and the retyped comparison above — is
already proved, and leaving it reducible makes the unifier compare two spellings of one sheaf
*underneath* its inverse image, where both have to be expanded, instead of at the top level,
where the comparison is the one the statements above already paid for. -/
attribute [local irreducible] AlgebraicGeometry.RingedSite.Hom.compareMid

/-- **The structure map of `f'_{04IF} ∘ compareMid`, in inverse-image form.** It is the inverse
of Stacks 04IF's comparison of inverse images at `O'`, restricted along `compareMid`, followed
by Stacks 04J3's comparison at `U` evaluated at `f^{-1}O'`, followed by `j_U^{-1}` of the
structure map of `f` — the same last factor as for `ι_V ∘ f'_{04J0}`.

The structure map of `f` is moved out in front by naturality of Stacks 04J3's comparison, and
the relocalization inside `compareMid` contributes the identity through
`Hom.forgetRing_compareMid_fSharpInverseImage`. -/
theorem Hom.forgetRing_localizedCompareMidComp_fSharpInverseImage :
    (ringedTopos (X.over (f.u.obj V))).forgetRing.map
        (AlgebraicGeometry.RingedToposHom.comp (X := ringedTopos (X.over (f.u.obj V)))
          (Y := RingedTopos.localizedRingedTopos X.ringedTopos
            (f.inverseImageRepresentableSheaf V))
          (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
          (f.ringedToposHom.localized (representableSheaf Y V))
          (f.compareMid V)).fSharpInverseImage =
      (f.compareMid V).toToposHom.inverseImage.map
          ((f.ringedToposHom.inverseImageCompLocalizationIso
            (representableSheaf Y V)).inv.app ((ringedTopos Y).forgetRing.obj Y.O)) ≫
        (f.midInverseImageComparison V).app
            ((ringedTopos X).forgetRing.obj
              ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
                f.ringedToposHom.toToposHom).obj Y.ringedTopos.O)) ≫
          (X.J.overPullback (Type u) (f.u.obj V)).map
            ((ringedTopos X).forgetRing.map f.ringedToposHom.fSharpInverseImage) := by
  -- The three ringed topoi are left to unification, and the two factors of the composite are
  -- rewritten together: every spelling of `F = f^{-1}h_V^#` written here is one more
  -- identification of the two spellings of that sheaf, and this declaration's budget affords
  -- the one its own statement already pays for.
  have h0 := comp_fSharpInverseImage_forget
    (f.ringedToposHom.localized (representableSheaf Y V)) (f.compareMid V)
  refine Eq.trans h0 ?_
  refine Eq.trans (congrArg₂ (fun a b => (f.compareMid V).toToposHom.inverseImage.map a ≫ b)
    (f.forgetRing_localizedRepresentable_fSharpInverseImage_eq V)
    (f.midInverseImageComparison_app_structureSheaf V).symm) ?_
  exact Stacks.CategoryTheory.map_comp_comp_naturality
    (X.ringedTopos.localizationMorphism
      (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage
    (f.compareMid V).toToposHom.inverseImage
    (X.J.overPullback (Type u) (f.u.obj V))
    (f.midInverseImageComparison V)
    ((ringedTopos X).forgetRing.map f.ringedToposHom.fSharpInverseImage)
    ((f.ringedToposHom.inverseImageCompLocalizationIso (representableSheaf Y V)).inv.app
      ((ringedTopos Y).forgetRing.obj Y.O))

end AlgebraicGeometry.RingedSite

end
