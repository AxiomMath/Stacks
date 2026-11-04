module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LiftAlongAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleIsoCongr
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Universal

/-!
# Stacks 0DEE: the affine étale site of an affine formal algebraic space is a category of charts

Let `S` be a scheme contained in a big fppf site `B` and let `X` be an affine formal algebraic
space over `S`. Stacks 0DEE asserts that `X_{affine, étale}` — which by Stacks 0DEA part (3) is
the affine étale site of the reduction `X_red` — is *equivalent* to the category `C` whose
objects are the morphisms `φ : U ⟶ X` of formal algebraic spaces with `U` an affine formal
algebraic space and `φ` representable by algebraic spaces and étale.

The category `C` and the comparison functor `(U ⟶ X) ↦ U ×_X X_red` are built in
`StacksFrontier/AlgebraicGeometry/FormalSpace/Affine/EtaleSite.lean`. This file proves that the
comparison functor is full, faithful and essentially surjective, assembles the equivalence, and
identifies the affine étale site of Stacks 0DEA part (3) with the category the comparison
functor takes values in.

## Main definitions

* `AlgebraicGeometry.FormalSpace.AffineReductionChart.toReduction`: the reduction datum of
  Stacks 0AIN carried by a reduction exhibited as an affine object of the site.
* `AlgebraicGeometry.FormalSpace.Reduction.affineEtaleIsoYonedaAffineReductionChart`: the
  identification of `X_{affine, étale}` with the affine étale site of the Yoneda presheaf of an
  object of the site exhibiting an affine reduction.
* `AlgebraicGeometry.FormalSpace.affineEtaleEquivalence`: **Stacks 0DEE**, the equivalence
  `X_{affine, étale} ≌ C` at an arbitrary reduction datum of `X`.

## Main results

* `AlgebraicGeometry.FormalSpace.faithful_affineEtaleComparison` and
  `AlgebraicGeometry.FormalSpace.full_affineEtaleComparison`: the comparison functor is fully
  faithful.
* `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_liftAlong_of_affine`: the
  dependent product that is the quasi-inverse on objects is an *affine* formal algebraic space.
* `AlgebraicGeometry.FormalSpace.essSurj_affineEtaleComparison`: the comparison functor is
  essentially surjective.
* `AlgebraicGeometry.FormalSpace.affineEtaleComparison_isEquivalence` and
  `AlgebraicGeometry.FormalSpace.reductionAffineEtaleComparison_isEquivalence`: the comparison
  functor is an equivalence.

## Full faithfulness

An object `φ : U ⟶ X` of `C` has `U ×_X h_V ⟶ U` for a representable thickening, `h_V ⟶ X`
being one and the property being stable under base change; and the structure morphism of an
object of `C` is representable by algebraic spaces and étale. So a morphism out of `U` into
another object of `C`, over `X`, is determined by — and can be prescribed along — its
restriction to `U ×_X h_V`, by
`AlgebraicGeometry.FormalSpace.existsUnique_hom_of_isRepresentableThickening`, the sheaf-level
general-thickening case of Stacks 05ZH. Uniqueness is faithfulness and existence is fullness;
that the morphism produced is carried to the given one is the uniqueness half of the universal
property of the chosen cartesian square,
`AlgebraicGeometry.FormalSpace.AffineEtaleBaseChange.lift_uniq`. This is the half of the
source's omitted "verification that the constructions are mutually inverse to each other" that
lives over the thickening.

## Essential surjectivity

An object of the affine étale site of `h_V` is, the Yoneda embedding being fully faithful, an
étale morphism `q : W ⟶ V` of the site with `W` affine. The quasi-inverse sends it to the
dependent product `U_{W, q}` of Stacks 0DEG — the sheaf of pairs `(a, b)` with `a : T ⟶ X` and
`b : T ×_{a, X} h_V ⟶ h_W` over `h_V`, constructed in
`StacksFrontier/AlgebraicGeometry/FormalSpace/SpacesEtaleQuasiInverse.lean` — rather than to the
colimit of a diagram of lifts along the stages of a presentation, which is how the source
writes it. The two agree, but the dependent product needs no assembly of the lifts and no
set-theoretic hypothesis: that `U_{W, q} ⟶ X` is representable by algebraic spaces and étale is
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_liftAlongBase`, and the set-theoretic
condition of Stacks 0AIS descends from `X` along that structure morphism, by
`SetTheoreticDescent.satisfiesSetTheoreticCondition_of_representable_over` (in the namespace
`AlgebraicGeometry.FormalSpace`).

What is new here, and what Stacks 0DEG does not need, is that `U_{W, q}` is an *affine* formal
algebraic space:
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_liftAlong_of_affine`. Its base
change to a stage `X_ν` of a presentation of `X` is an affine object of the site, by one
application of
`AlgebraicGeometry.FormalSpace.exists_affine_etale_iso_pullback_liftAlongBase` — the stage
`X_ν ×_X h_V` of the thickening is affine, being a closed subscheme of the affine `X_ν`, the
base change `W ×_V (X_ν ×_X h_V)` of `q` to it is affine and étale over it, and the dependent
product of an affine object along a thickening of objects of the site is affine — so Stacks
0GVM applies through
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_of_affine_stages`.

The equivalence holds for an arbitrary representable thickening `i : h_V ⟶ X` out of the sheaf
of an affine object of the site, not only for the inclusion of the reduction:
`AlgebraicGeometry.FormalSpace.affineEtaleComparison_isEquivalence`. That is the content of the
source's `X_{red, affine, étale} = X_{λ, affine, étale}`.

## The affine étale site of Stacks 0DEA and the one the comparison functor targets

The comparison functor takes values in `AlgebraicGeometry.Space.AffineEtale` of the *Yoneda
presheaf* of an object `V` of the site exhibiting the reduction, while `X_{affine, étale}` as
defined in Stacks 0DEA part (3) is `AlgebraicGeometry.Space.AffineEtale` of the presheaf of
points of the reduction *as an algebraic space*,
`AlgebraicGeometry.FormalSpace.Reduction.AffineEtale`. The two are identified here, so the
equivalence is stated with the library's own 0DEA site and nothing is left to the reader: the
two presheaves are isomorphic because both exhibit the reduction of `X` and a reduction is
unique up to canonical isomorphism
(`AlgebraicGeometry.FormalSpace.Reduction.objIsoYonedaAffineReductionChart`, out of
`AlgebraicGeometry.FormalSpace.Reduction.iso` and
`AlgebraicGeometry.FormalSpace.AffineReductionChart.toReduction`), and the affine étale site of
a presheaf depends on it only up to isomorphism
(`AlgebraicGeometry.Space.AffineEtale.congr`).

## References

* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
* [Stacks Project, Tag 0H01](https://stacks.math.columbia.edu/tag/0H01)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A representable thickening stays one after precomposition with an isomorphism: the property
is stable under base change, hence respects isomorphisms, and an isomorphism of fppf sheaves is
an isomorphism of the underlying presheaves. -/
theorem isRepresentableThickeningULift_iso_comp {Z Z' X : FppfSheaf B S hS} (e : Z' ≅ Z)
    {i : Z ⟶ X} (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (e.hom ≫ i).hom := by
  have _ : ((MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (uliftYoneda.{u + 1} (C := BigFppfOver B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange _).respectsIso
  have _ : IsIso (e.hom.hom) :=
    inferInstanceAs (IsIso ((sheafToPresheaf (BigFppfOver.topology B S hS)
      (Type (u + 1))).map e.hom))
  exact MorphismProperty.RespectsIso.precomp _ e.hom.hom _ hi

section FullyFaithful

variable {B S hS} {X : FppfSheaf B S hS} {V : BigFppfOver B S hS}
    {i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}

/-- The projection of a base change of a chart to the source of the chart is a representable
thickening, being a base change of one. -/
theorem AffineEtaleBaseChange.isRepresentableThickening_fst
    (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)
    {Y : AffineEtaleFormalCharts B S hS X} (dY : AffineEtaleBaseChange B S hS X V i Y) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS dY.fst.hom :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (dY.isPullback.flip.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hi

variable (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)

include hi in
/-- **The comparison functor of Stacks 0DEE is faithful.** -/
theorem faithful_affineEtaleComparison :
    (affineEtaleComparison B S hS hX V hV i).Faithful where
  map_injective {Y Z} f g hfg := by
    set dY := affineEtaleBaseChangeData B S hS hX V hV i Y
    set dZ := affineEtaleBaseChangeData B S hS hX V hV i Z
    have hlift : dY.lift dZ f = dY.lift dZ g :=
      congrArg (fun m : (affineEtaleComparison B S hS hX V hV i).obj Y ⟶
        (affineEtaleComparison B S hS hX V hV i).obj Z ↦ m.hom.hom.left) hfg
    have key : dY.fst ≫ f.hom.left = dY.fst ≫ g.hom.left := by
      rw [← dY.lift_fst dZ f, ← dY.lift_fst dZ g, hlift]
    have hw : (dY.fst ≫ f.hom.left) ≫ Z.obj.hom = dY.fst ≫ Y.obj.hom := by
      rw [Category.assoc, Over.w f.hom]
    exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext
      ((existsUnique_hom_of_isRepresentableThickening (dY.isRepresentableThickening_fst hi)
        Z.property.2 Y.obj.hom hw).unique ⟨Over.w f.hom, rfl⟩ ⟨Over.w g.hom, key.symm⟩))

include hi in
/-- **The comparison functor of Stacks 0DEE is full.** -/
theorem full_affineEtaleComparison :
    (affineEtaleComparison B S hS hX V hV i).Full where
  map_surjective {Y Z} φ := by
    set dY := affineEtaleBaseChangeData B S hS hX V hV i Y
    set dZ := affineEtaleBaseChangeData B S hS hX V hV i Z
    set m : dY.obj ⟶ dZ.obj := φ.hom.hom.left
    have hproj : m ≫ dZ.proj = dY.proj := by
      apply Yoneda.fullyFaithful.map_injective
      rw [Functor.map_comp]
      exact CostructuredArrow.w φ.hom.hom
    have hw : ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map m ≫ dZ.fst)
        ≫ Z.obj.hom = dY.fst ≫ Y.obj.hom := by
      rw [Category.assoc, dZ.isPullback.w, ← Category.assoc, ← Functor.map_comp, hproj,
        dY.isPullback.w]
    obtain ⟨fl, hfl⟩ := (existsUnique_hom_of_isRepresentableThickening
      (dY.isRepresentableThickening_fst hi) Z.property.2 Y.obj.hom hw).exists
    exact ⟨ObjectProperty.homMk (Over.homMk fl hfl.1), ObjectProperty.hom_ext _
      (ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
        (dY.lift_uniq dZ _ m hproj hfl.2.symm).symm))⟩

/-- **The comparison functor of Stacks 0DEE carries a chart to every object of the affine étale
site that represents the base change of that chart.** If the fibre product of `φ : U ⟶ X` with
`h_V` over `X` is represented, over `V`, by the object of the site underlying an affine étale
chart `Z` of `h_V`, then `Z` is in the essential image of the comparison functor.

The chosen base change of `φ` and the given one are two fibre products of the same pair of
morphisms, hence isomorphic over `V` as fppf sheaves, hence — the sheafified Yoneda embedding
being fully faithful, the big fppf site being subcanonical — isomorphic over `V` as objects of
the site. An isomorphism of charts over `V` is an isomorphism of the affine étale site. -/
theorem mem_essImage_affineEtaleComparison (Z : Space.AffineEtale B S hS (yoneda.obj V))
    (Y : AffineEtaleFormalCharts B S hS X) {q : Z.obj.obj.left ⟶ V}
    (hq : yoneda.map q = Z.obj.obj.hom)
    {s : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj Z.obj.obj.left ⟶
      Y.obj.left}
    (hs : IsPullback s ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q)
      Y.obj.hom i) :
    (affineEtaleComparison B S hS hX V hV i).essImage Z := by
  refine ⟨Y, ⟨?_⟩⟩
  set dY := affineEtaleBaseChangeData B S hS hX V hV i Y
  have hθ : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((sheafifiedYonedaFF B S hS).preimageIso
          (dY.isPullback.isoIsPullback _ _ hs)).hom
      = (dY.isPullback.isoIsPullback _ _ hs).hom :=
    (sheafifiedYonedaFF B S hS).map_preimage _
  have hcompat : ((sheafifiedYonedaFF B S hS).preimageIso
        (dY.isPullback.isoIsPullback _ _ hs)).hom ≫ q = dY.proj := by
    apply (sheafifiedYonedaFF B S hS).map_injective
    rw [Functor.map_comp, hθ]
    exact dY.isPullback.isoIsPullback_hom_snd _ _ hs
  have hw : yoneda.map ((sheafifiedYonedaFF B S hS).preimageIso
          (dY.isPullback.isoIsPullback _ _ hs)).hom ≫ Z.obj.obj.hom
      = yoneda.map dY.proj := by
    rw [← hq, ← Functor.map_comp, hcompat]
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (CostructuredArrow.isoMk _ hw))

end FullyFaithful

/-! ### The quasi-inverse is valued in affine formal algebraic spaces -/

/-- The universe lift of an étale morphism of the site is representable by algebraic spaces and
étale. -/
private theorem isRepresentableEtale_liftSheafMap_schemeSpaceMap {V W : BigFppfOver B S hS}
    (q : W ⟶ V) (hq : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    IsRepresentableEtale B S hS (liftSheafMap B S hS (schemeSpaceMap q)) :=
  isRepresentableEtale_liftSheafMap B S hS (schemeSpaceMap q)
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map q)).2
      ((Space.presheaf_yoneda_map_etale_iff B S hS q).2 hq))

attribute [local instance] sheaf_hasColimits

/-- **The dependent product of an affine scheme étale over an affine base along a representable
thickening of an affine formal algebraic space is an affine formal algebraic space.**

Let `X` be an affine formal algebraic space over `S`, let `i : h_V ⟶ X` be a representable
thickening out of the sheaf of an object `V` of the site with affine underlying scheme, and let
`q : W ⟶ V` be an étale morphism of the site with `W` affine. Then `U_{W, q}`, the dependent
product of Stacks 0DEG's construction — which for `i` the inclusion of the reduction is the
quasi-inverse of the comparison functor of Stacks 0DEE — is an *affine* formal algebraic space,
not merely a formal algebraic space.

The base change of `U_{W, q}` to a stage `X_ν` of a presentation of `X` is computed in one step
by `AlgebraicGeometry.FormalSpace.exists_affine_etale_iso_pullback_liftAlongBase`: the stage
`T_ν = X_ν ×_X h_V` of the thickening is an affine object of the site, the base change
`W ×_V T_ν` of `q` to it is an affine object étale over it, and the dependent product of that
along the thickening `T_ν ⟶ X_ν` of objects of the site is an affine object of the site.
Stacks 0GVM then applies, through
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_of_affine_stages`, the
set-theoretic condition of Stacks 0AIS descending from `X` along the representable structure
morphism.

This is where Stacks 0DEE differs from Stacks 0DEG: the latter needs only that the dependent
product is a formal algebraic space, and it covers the base change of its base by a *family* of
affine étale charts, so the members of the resulting atlas are affine formal algebraic spaces
while their coproduct is not. Here the base `W` is a single affine object of the site, and the
dependent product is affine on the nose. -/
theorem isAffineFormalAlgebraicSpace_liftAlong_of_affine
    {X : FppfSheaf B S hS} (hX : IsAffineFormalAlgebraicSpace B S hS X)
    {V W : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    {i : liftSheaf B S hS (schemeSpace V) ⟶ X}
    (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)
    {q : W ⟶ V} (hq : Etale ((BigFppfOver.toScheme B S hS).map q)) :
    IsAffineFormalAlgebraicSpace B S hS
      (liftAlong B S hS i (liftSheafMap B S hS (schemeSpaceMap q))) := by
  classical
  obtain ⟨hXset, Λ, pre, hne, hdir, D, hDthick, ⟨eX⟩⟩ := hX
  have eX' : X ≅ colimit (presentationDiagram D) := eX
  let _ : Preorder Λ := pre
  let _ : Nonempty Λ := hne
  let _ : IsDirected Λ (· ≤ ·) := hdir
  set p : liftSheaf B S hS (schemeSpace W) ⟶ liftSheaf B S hS (schemeSpace V) :=
    liftSheafMap B S hS (schemeSpaceMap q)
  have hpet : IsRepresentableEtale B S hS p :=
    isRepresentableEtale_liftSheafMap_schemeSpaceMap B S hS q hq
  -- the stages of the presentation of `X`, as objects of the site
  set Xs : Λ → BigFppfOver B S hS := fun ν ↦ (BigAffineFppf.inclusion B S hS).obj (D.obj ν)
  have hXsaff : ∀ ν, IsAffine ((BigFppfOver.toScheme B S hS).obj (Xs ν)) := fun ν ↦
    BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj ν)
  have εs : ∀ ν : Λ, liftSheaf B S hS (schemeSpace (Xs ν))
      ≅ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj (Xs ν) := fun ν ↦
    liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS (Xs ν)
  set σ : ∀ ν, liftSheaf B S hS (schemeSpace (Xs ν)) ⟶ X := fun ν ↦
    (εs ν).hom ≫ colimit.ι (presentationDiagram D) ν ≫ eX'.inv
  -- the stage of the thickening over each stage of `X`
  choose Ts kk jj hkkthick hTsq using
    fun ν ↦ exists_isPullback_point_of_isRepresentableThickening hi (σ ν)
  have hTsaff : ∀ ν, IsAffine ((BigFppfOver.toScheme B S hS).obj (Ts ν)) := by
    intro ν
    have _ := hXsaff ν
    have _ : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kk ν)) := (hkkthick ν).1
    exact isAffine_of_isAffineHom ((BigFppfOver.toScheme B S hS).map (kk ν))
  refine isAffineFormalAlgebraicSpace_of_affine_stages D hDthick eX' hXset
    (liftAlongBase B S hS i p)
    (isRepresentableEtale_liftAlongBase B S hS hi hpet).1 fun ν ↦ ?_
  -- the stage of the thickening is represented by a morphism of the site
  obtain ⟨π, hπ⟩ := exists_liftSheafMap_schemeSpaceMap_eq (jj ν)
  have hTsqν : IsPullback (liftSheafMap B S hS (schemeSpaceMap (kk ν)))
      (liftSheafMap B S hS (schemeSpaceMap π)) (σ ν) i := by
    rw [hπ]
    exact hTsq ν
  -- the base change of `q` to that stage is an affine object of the site étale over it
  have hsqA := (IsPullback.of_hasPullback q π).map (BigFppfOver.toScheme B S hS)
  have hAaff : IsAffine ((BigFppfOver.toScheme B S hS).obj (Limits.pullback q π)) := by
    have _ := hW
    have _ := hV
    have _ := hTsaff ν
    have _ : IsAffine (Limits.pullback ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map π)) := inferInstance
    exact IsAffine.of_isIso hsqA.isoPullback.hom
  have hAet : Etale ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd q π)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsqA hq
  obtain ⟨ε, hε⟩ := exists_iso_pullback_liftSheafMap q π
  obtain ⟨V', -, hV'aff, -, e, -⟩ :=
    exists_affine_etale_iso_pullback_liftAlongBase (hkkthick ν) hTsqν _ hAaff _ hAet ε hε
  -- the base change of the dependent product to the stage, read in the colimit presentation
  have hsw : IsPullback
      (pullback.snd (liftAlongBase B S hS i p) (σ ν) ≫ (εs ν).hom)
      (pullback.fst (liftAlongBase B S hS i p) (σ ν))
      (colimit.ι (presentationDiagram D) ν)
      (liftAlongBase B S hS i p ≫ eX'.hom) := by
    refine (IsPullback.of_hasPullback (liftAlongBase B S hS i p) (σ ν)).flip.of_iso
      (Iso.refl _) (εs ν) (Iso.refl _) eX'
      (by simp) (by simp) ?_ (by simp)
    change ((εs ν).hom ≫ colimit.ι (presentationDiagram D) ν ≫ eX'.inv) ≫ eX'.hom = _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ⟨V', hV'aff, ⟨e ≪≫ hsw.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)⟩⟩

/-! ### Essential surjectivity -/

section EssSurj

variable {B S hS} {X : FppfSheaf B S hS} {V : BigFppfOver B S hS}
    {i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)

include hi in
/-- **The comparison functor of Stacks 0DEE is essentially surjective.** Let `Z` be an affine
étale chart of `h_V`, that is — the Yoneda embedding being fully faithful — an étale morphism
`q : W ⟶ V` of the site with `W` affine. The dependent product `U_{W, q}` along `i` is an
affine formal algebraic space by
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_liftAlong_of_affine` and is
representable by algebraic spaces and étale over `X` by
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_liftAlongBase`, so it is an object of the
category of Stacks 0DEE; and its fibre product with `h_V` over `X` is `h_W`, by
`AlgebraicGeometry.FormalSpace.isPullback_liftAlongSection`, so the comparison functor carries
it to `Z`. -/
theorem essSurj_affineEtaleComparison :
    (affineEtaleComparison B S hS hX V hV i).EssSurj where
  mem_essImage Z := by
    classical
    -- the given chart, as an étale morphism of the site with affine source
    obtain ⟨q, hq⟩ : ∃ q : Z.obj.obj.left ⟶ V, yoneda.map q = Z.obj.obj.hom :=
      ⟨Yoneda.fullyFaithful.preimage Z.obj.obj.hom,
        Yoneda.fullyFaithful.map_preimage Z.obj.obj.hom⟩
    have hchart : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q) := by
      rw [hq]
      exact Z.obj.property
    have hqet : Etale ((BigFppfOver.toScheme B S hS).map q) :=
      (Space.presheaf_yoneda_map_etale_iff B S hS q).1 hchart
    -- the thickening and the chart, read through the universe lift of the represented space
    have hi' : Space.IsRepresentableThickeningULift.{u + 1} B S hS
        ((liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS V).hom ≫ i).hom :=
      isRepresentableThickeningULift_iso_comp B S hS
        (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS V) hi
    have hpet := isRepresentableEtale_liftSheafMap_schemeSpaceMap B S hS q hqet
    have hinj : ∀ T : BigFppfOver B S hS, Function.Injective
        (((liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS V).hom ≫ i).hom.app
          (Opposite.op T)) := fun T ↦
      (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
        (mono_of_isRepresentableThickeningULift B S hS hi') (Opposite.op T))
    -- the fibre product of the dependent product with `h_V` over `X` is `h_W`
    have hnat : liftSheafMap B S hS (schemeSpaceMap q) ≫
          (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS V).hom
        = (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS Z.obj.obj.left).hom
          ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q :=
      (yonedaSpaceCompLiftSheafFunctorIsoSheafifiedYoneda B S hS).hom.naturality q
    have hsec : IsPullback
        ((liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS Z.obj.obj.left).inv ≫
          liftAlongSection B S hS hinj (p := liftSheafMap B S hS (schemeSpaceMap q)))
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q)
        (liftAlongBase B S hS ((liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS V).hom ≫ i)
          (liftSheafMap B S hS (schemeSpaceMap q))) i :=
      (isPullback_liftAlongSection B S hS hinj
          (p := liftSheafMap B S hS (schemeSpaceMap q))).of_iso
        (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS Z.obj.obj.left) (Iso.refl _)
        (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS V) (Iso.refl _)
        ((Category.comp_id _).trans (Iso.hom_inv_id_assoc _ _).symm) hnat
        ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _)
    exact mem_essImage_affineEtaleComparison hX hV Z
      ⟨Over.mk (liftAlongBase B S hS
          ((liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS V).hom ≫ i)
          (liftSheafMap B S hS (schemeSpaceMap q))),
        isAffineFormalAlgebraicSpace_liftAlong_of_affine B S hS hX hV Z.property hi' hqet,
        isRepresentableEtale_liftAlongBase B S hS hi' hpet⟩ hq hsec

end EssSurj

/-! ### The equivalence -/

section Equivalence

variable {B S hS} {X : FppfSheaf B S hS} {V : BigFppfOver B S hS}
    {i : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X}

/-- **The comparison functor of Stacks 0DEE is an equivalence**, for an arbitrary object `V` of
the site with affine underlying scheme and an arbitrary *representable thickening* `i` out of
the sheaf it represents — not only for the inclusion of the reduction. That extra generality is
the content of the source's remark that `X_{red, affine, étale} = X_{λ, affine, étale}` for
every stage `X_λ` of a presentation. -/
theorem affineEtaleComparison_isEquivalence
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (hi : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom) :
    (affineEtaleComparison B S hS hX V hV i).IsEquivalence where
  faithful := faithful_affineEtaleComparison hX hV hi
  full := full_affineEtaleComparison hX hV hi
  essSurj := essSurj_affineEtaleComparison hX hV hi

/-- The reduction datum of Stacks 0AIN carried by a reduction exhibited as an affine object of
the site: the represented algebraic space, with the inclusion moved to the universe lift of
that space along `AlgebraicGeometry.FormalSpace.liftSheafYonedaSpaceIsoSheafifiedYoneda`. This
is what compares the affine étale site of the Yoneda presheaf of the object with the site
`X_{affine, étale}` of Stacks 0DEA, which is built from a
`AlgebraicGeometry.FormalSpace.Reduction`. -/
noncomputable def AffineReductionChart.toReduction (c : AffineReductionChart B S hS X) :
    Reduction B S hS X where
  space := schemeSpace c.obj
  inclusion := (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS c.obj).hom ≫ c.inclusion
  isReduction :=
    isReduction_comp_iso B S hS (liftSheafYonedaSpaceIsoSheafifiedYoneda B S hS c.obj)
      c.isReduction

/-- **The reduction underlying any reduction datum of `X` is the Yoneda presheaf of the object
of the site exhibiting an affine reduction.** Two reductions of one fppf sheaf are canonically
isomorphic, by `AlgebraicGeometry.FormalSpace.Reduction.iso`; applied to a given reduction
datum and to the one `AlgebraicGeometry.FormalSpace.AffineReductionChart.toReduction` carries,
that isomorphism of algebraic spaces is an isomorphism of their presheaves of points, and the
presheaf of points of the algebraic space of an object of the site is its Yoneda presheaf. -/
noncomputable def Reduction.objIsoYonedaAffineReductionChart (R : Reduction B S hS X)
    (c : AffineReductionChart B S hS X) : R.space.obj ≅ yoneda.obj c.obj :=
  (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u ↦
    IsAlgebraicSpace B S hS F)).mapIso (R.iso c.toReduction)

/-- **The affine étale site of `X` is the affine étale site of the Yoneda presheaf of an object
of the site exhibiting an affine reduction of `X`.**

This is the identification the source makes silently when it writes
`X_{affine, étale} = X_{red, affine, étale}` and then treats `X_{red}` as an affine scheme: the
site `X_{affine, étale}` of Stacks 0DEA part (3) is the affine étale site of the presheaf of
points of the reduction *as an algebraic space*, while the comparison functor of Stacks 0DEE is
built on the Yoneda presheaf of an object of the site representing that reduction. The two
presheaves are isomorphic, by
`AlgebraicGeometry.FormalSpace.Reduction.objIsoYonedaAffineReductionChart`, and the affine
étale site depends on its base presheaf only up to isomorphism, by
`AlgebraicGeometry.Space.AffineEtale.congr`. The identification is one of *sites*, not only of
categories: `AlgebraicGeometry.Space.AffineEtale.congr_isIsoOfSites` exhibits it as an
isomorphism of sites, whose
`CategoryTheory.Equivalence.IsIsoOfSites.functor_inducedTopology` matches the two affine étale
topologies, and `AlgebraicGeometry.Space.AffineEtale.congr_functor_comp_inclusion` says that
the chart, hence the object of the site, underlying an affine chart is unchanged. -/
noncomputable def Reduction.affineEtaleIsoYonedaAffineReductionChart (R : Reduction B S hS X)
    (c : AffineReductionChart B S hS X) :
    R.AffineEtale ≌ Space.AffineEtale B S hS (yoneda.obj c.obj) :=
  Space.AffineEtale.congr B S hS (R.objIsoYonedaAffineReductionChart c)

/-- **Stacks 0DEE.** Let `X` be an affine formal algebraic space over `S`. Then
`X_{affine, étale}` — the affine étale site of the reduction of `X`, in the sense of Stacks
0DEA part (3), at an arbitrary reduction datum — is equivalent to the category whose objects
are the morphisms `φ : U ⟶ X` of formal algebraic spaces such that

1. `U` is an affine formal algebraic space,
2. `φ` is representable by algebraic spaces and étale.

The functor is the source's, `(U ⟶ X) ↦ U ×_X X_red`: it is
`AlgebraicGeometry.FormalSpace.reductionAffineEtaleComparison`, read backwards and composed
with the identification of `X_{affine, étale}` with the affine étale site of the Yoneda
presheaf of the chosen affine reduction chart. Full faithfulness is
`AlgebraicGeometry.FormalSpace.full_affineEtaleComparison` and
`AlgebraicGeometry.FormalSpace.faithful_affineEtaleComparison`, both out of the unique
extension of a morphism along a representable thickening; essential surjectivity is
`AlgebraicGeometry.FormalSpace.essSurj_affineEtaleComparison`, whose quasi-inverse is the
dependent product `U_{W, q}` and whose affineness is
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_liftAlong_of_affine`. The source's
omitted "verification that the constructions are mutually inverse to each other" is therefore
supplied.

The reduction datum is a parameter, not a weakening: `X_{affine, étale}` is defined, in Stacks
0DEA, only for a formal algebraic space with a given reduction, and the datum exists for every
affine formal algebraic space by Stacks 0AIN — in the shape used here by
`AlgebraicGeometry.FormalSpace.nonempty_affineReductionChart`. -/
@[stacks 0DEE "the equivalence of `X_affine,étale` with the category of the morphisms \
satisfying (1) and (2); fullness, faithfulness and essential surjectivity are all proved, and \
the affine étale site of Stacks 0DEA(3) is identified with the one the comparison functor \
targets"]
noncomputable def affineEtaleEquivalence (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (R : Reduction B S hS X) : R.AffineEtale ≌ AffineEtaleFormalCharts B S hS X :=
  haveI := affineEtaleComparison_isEquivalence hX (affineReductionChart B S hS hX).isAffine
    (affineReductionChart B S hS hX).isReduction.isRepresentableThickening
  (R.affineEtaleIsoYonedaAffineReductionChart (affineReductionChart B S hS hX)).trans
    (affineEtaleComparison B S hS hX _ (affineReductionChart B S hS hX).isAffine
      (affineReductionChart B S hS hX).inclusion).asEquivalence.symm

/-- **Stacks 0DEE.** The comparison functor
`AlgebraicGeometry.FormalSpace.reductionAffineEtaleComparison` of Stacks 0DEE is an equivalence
of categories: it is full, faithful and essentially surjective. Its target is the affine étale
site of `X`, which is identified with the site `X_{affine, étale}` of Stacks 0DEA part (3) by
`AlgebraicGeometry.FormalSpace.Reduction.affineEtaleIsoYonedaAffineReductionChart`; the
resulting equivalence stated with that site is
`AlgebraicGeometry.FormalSpace.affineEtaleEquivalence`. -/
@[stacks 0DEE "the comparison functor is an equivalence: it is full, faithful and essentially \
surjective"]
theorem reductionAffineEtaleComparison_isEquivalence
    (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    (reductionAffineEtaleComparison' B S hS hX).IsEquivalence :=
  affineEtaleComparison_isEquivalence hX (affineReductionChart B S hS hX).isAffine
    (affineReductionChart B S hS hX).isReduction.isRepresentableThickening

end Equivalence

end AlgebraicGeometry.FormalSpace

end
