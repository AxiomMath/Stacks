module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSiteSpecDictionary
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineCanonicalFull
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingProperties
import all StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFullyFaithful

/-!
# Full faithfulness of the Beauville--Laszlo glueing functor, with its inputs proved (Stacks 0F9T)

`StacksFrontier/AlgebraicGeometry/Spaces/BeauvilleLaszloGlueingFullyFaithful.lean` proves that the
glueing functor of Stacks 0F9N is fully faithful on algebraic spaces which are glueable for
`(g, f)` and have affine diagonal, relative to two inputs: the equivalence of the affine case
(Stacks 0F9Q, as a term `E` of `BeauvilleLaszlo.Space.AffineGlueingEquivalenceSpec`) and Stacks
0F9R for the property "étale" (as the hypothesis `hEtale`). Both are theorems of this library.
This file proves the second in the form `hEtale` asks for and supplies both, so that the
statements registered here assume nothing beyond the source's hypotheses.

## Main results

* `BeauvilleLaszlo.Space.isEtale_iff_isEtale_glueingComponents`: **Stacks 0F9R for the property
  "étale"**, in the language of algebraic spaces: a morphism of affine algebraic spaces over
  `X = Spec R` with glueable target is étale if and only if its three base changes, the
  components of its image under the glueing functor of Stacks 0F9N, are étale.
* `beauvilleLaszloGlueingSpaces_map_surjective_of_isGlueable_of_isAffineHom_diag`:
  **Stacks 0F9T, fullness**, with no hypothesis beyond glueability and affineness of the
  diagonal of the target.
* `beauvilleLaszloGlueingSpaces_map_bijective_of_isGlueable_of_isAffineHom_diag`:
  **Stacks 0F9T**, full faithfulness.

## Implementation notes

The space-level statement of Stacks 0F9R for étale reduces to
`BeauvilleLaszlo.etale_iff_baseChange`, stated for a morphism of affine schemes over `Spec R`
and its base changes along `Over.pullback`. The reduction replaces the two spaces by spectra of
rings over `R` representing them (`AlgebraicGeometry.BigFppfOver.exists_specOver`), reads the
morphism in the site, and identifies each space-level base change with the scheme-level one:
base change of algebraic spaces is restriction of presheaves, which carries a representable
presheaf to the presheaf represented by the fibre product
(`CategoryTheory.OverShriek.restrictYonedaIso`), and both the site-level and the scheme-level
fibre products are base changes of the same morphism of schemes
(`CategoryTheory.OverShriek.isPullback_pullback_map`), the first preserved by the inclusion of
the size-cut full subcategory. Each identification is an isomorphism of arrows, so both
directions hold.

The private étale lemmas of the full-faithfulness file are reached by `import all`.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9R](https://stacks.math.columbia.edu/tag/0F9R)
* [Stacks Project, Tag 0F9T](https://stacks.math.columbia.edu/tag/0F9T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace BeauvilleLaszlo.Space

attribute [local instance] isEtale_respectsIso

/-! ### Étaleness of a morphism of affine glueable spaces and of its components -/

/-- **The base change of a morphism of representable spaces, read in the site.** The base
change along `j` of a morphism `p` of algebraic spaces is étale exactly when the base change
along `j` of the morphism `ψ` of the site representing `p` is étale as a morphism of schemes.

Base change of algebraic spaces is restriction of presheaves, and restriction carries the
presheaf represented by `T` to the one represented by the fibre product `T ×_X -`
(`CategoryTheory.OverShriek.restrictYonedaIso`), naturally in `T`; so the two morphisms are
isomorphic arrows, and étaleness of a morphism of representables is étaleness of the morphism
of schemes underneath. -/
private theorem etale_toScheme_pullback_map_iff_isEtale_baseChange (B : BigFppfSite.{u})
    (X T : Scheme.{u}) (hX : B.Contains X) (hT : B.Contains T) (j : B.obj hT ⟶ B.obj hX)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    {L V : AlgebraicSpaces B X hX} (p : L ⟶ V)
    (eL : L.1 ≅ yoneda.obj TL) (eV : V.1 ≅ yoneda.obj TV)
    (hψ : yoneda.map ψ = eL.inv ≫ p.hom ≫ eV.hom) :
    Etale ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ)) ↔
      AlgebraicGeometry.Space.IsEtale B T hT ((baseChange B T X hT hX j).map p).hom := by
  have key : (OverShriek.restrictYonedaIso j TL).inv ≫
        yoneda.map ((Over.pullback j).map ψ) =
      (OverShriek.relocalizeRestrict j).map (yoneda.map ψ) ≫
        (OverShriek.restrictYonedaIso j TV).inv := by
    rw [Iso.eq_comp_inv, Category.assoc, OverShriek.restrictYonedaIso_naturality,
      Iso.inv_hom_id_assoc]
  let e : Arrow.mk ((OverShriek.relocalizeRestrict j).map p.hom) ≅
      Arrow.mk (yoneda.map ((Over.pullback j).map ψ)) := by
    refine Arrow.isoMk
      ((OverShriek.relocalizeRestrict j).mapIso eL ≪≫ (OverShriek.restrictYonedaIso j TL).symm)
      ((OverShriek.relocalizeRestrict j).mapIso eV ≪≫ (OverShriek.restrictYonedaIso j TV).symm)
      ?_
    change ((OverShriek.relocalizeRestrict j).map eL.hom ≫
        (OverShriek.restrictYonedaIso j TL).inv) ≫ yoneda.map ((Over.pullback j).map ψ) =
      (OverShriek.relocalizeRestrict j).map p.hom ≫
        (OverShriek.relocalizeRestrict j).map eV.hom ≫
          (OverShriek.restrictYonedaIso j TV).inv
    rw [Category.assoc, key, hψ, ← Category.assoc, ← Functor.map_comp]
    simp
  exact ((AlgebraicGeometry.Space.presheaf_yoneda_map_etale_iff B T hT _).symm.trans
    (AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda B T hT _).symm).trans
    ⟨isEtale_of_arrowIso B T hT e.symm, isEtale_of_arrowIso B T hT e⟩

/-- **The two readings of one base change agree.** The base change of `ψ` along a morphism `j`
of the site and the base change of the morphism of schemes underneath along the morphism `ρ` of
schemes underneath `j` are isomorphic arrows, hence have the same étaleness.

Both are base changes of the same morphism of schemes
(`CategoryTheory.OverShriek.isPullback_pullback_map`), the first computed in the size-cut full
subcategory, which the inclusion into schemes preserves, and the second in schemes; the
comparison of the two fibre products of the target identifies the two cospans. -/
private theorem etale_overPullback_map_iff_etale_toScheme_pullback_map (B : BigFppfSite.{u})
    (X T : Scheme.{u}) (hX : B.Contains X) (hT : B.Contains T) (j : B.obj hT ⟶ B.obj hX)
    (ρ : T ⟶ X) (hρ : B.inclusion.map j = ρ)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    (h : Over.mk (B.inclusion.map TL.hom) ⟶ Over.mk (B.inclusion.map TV.hom))
    (hh : h.left = (BigFppfOver.toScheme B X hX).map ψ) :
    Etale ((Over.pullback ρ).map h).left ↔
      Etale ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ)) := by
  have hTVsq : IsPullback (B.inclusion.map (pullback.fst TV.hom j))
      (B.inclusion.map (pullback.snd TV.hom j)) (B.inclusion.map TV.hom) ρ := by
    rw [← hρ]
    exact (IsPullback.of_hasPullback TV.hom j).map B.inclusion
  let i₂ := hTVsq.isoIsPullback _ _
    (IsPullback.of_hasPullback (B.inclusion.map TV.hom) ρ)
  have hi₂ : i₂.hom ≫ pullback.fst (B.inclusion.map TV.hom) ρ =
      B.inclusion.map (pullback.fst TV.hom j) :=
    hTVsq.isoIsPullback_hom_fst _ _ _
  have sqA : IsPullback ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ))
      (B.inclusion.map (pullback.fst TL.hom j)) (B.inclusion.map (pullback.fst TV.hom j))
      ((BigFppfOver.toScheme B X hX).map ψ) :=
    (OverShriek.isPullback_pullback_map j ψ).map B.inclusion
  have sqB : IsPullback ((Over.pullback ρ).map h).left
      (pullback.fst (B.inclusion.map TL.hom) ρ)
      (pullback.fst (B.inclusion.map TV.hom) ρ) h.left :=
    OverShriek.isPullback_pullback_map ρ h
  have sqA' : IsPullback
      ((BigFppfOver.toScheme B T hT).map ((Over.pullback j).map ψ) ≫ i₂.hom)
      (B.inclusion.map (pullback.fst TL.hom j))
      (pullback.fst (B.inclusion.map TV.hom) ρ) h.left :=
    sqA.of_iso (Iso.refl _) i₂ (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simpa using hi₂.symm) (by simp [hh])
  exact (MorphismProperty.arrow_mk_iso_iff (@Etale.{u} : MorphismProperty Scheme.{u})
    (Arrow.isoMk (sqA'.isoIsPullback _ _ sqB) i₂ (sqA'.isoIsPullback_hom_fst _ _ _))).symm

/-- The two readings of a base change, composed: the scheme-level base change of `h` along `ρ`
is étale iff the space-level base change of `p` along `j` is. -/
private theorem etale_overPullback_map_iff_isEtale_baseChange (B : BigFppfSite.{u})
    (X T : Scheme.{u}) (hX : B.Contains X) (hT : B.Contains T) (j : B.obj hT ⟶ B.obj hX)
    (ρ : T ⟶ X) (hρ : B.inclusion.map j = ρ)
    {TL TV : BigFppfOver B X hX} (ψ : TL ⟶ TV)
    (h : Over.mk (B.inclusion.map TL.hom) ⟶ Over.mk (B.inclusion.map TV.hom))
    (hh : h.left = (BigFppfOver.toScheme B X hX).map ψ)
    {L V : AlgebraicSpaces B X hX} (p : L ⟶ V)
    (eL : L.1 ≅ yoneda.obj TL) (eV : V.1 ≅ yoneda.obj TV)
    (hψ : yoneda.map ψ = eL.inv ≫ p.hom ≫ eV.hom) :
    Etale ((Over.pullback ρ).map h).left ↔
      AlgebraicGeometry.Space.IsEtale B T hT ((baseChange B T X hT hX j).map p).hom :=
  (etale_overPullback_map_iff_etale_toScheme_pullback_map B X T hX hT j ρ hρ ψ h hh).trans
    (etale_toScheme_pullback_map_iff_isEtale_baseChange B X T hX hT j ψ p eL eV hψ)

/-- **Stacks 0F9R for the property "étale", in the language of algebraic spaces.** Let
`(g : R → R', f)` be a glueing pair. A morphism `p : L → V` of algebraic spaces over
`X = Spec R` with `L` and `V` affine and `V` glueable for `(g, f)` is étale if and only if its
three base changes to `U = Spec R_f`, `U' = Spec R'_{g f}` and `X' = Spec R'` — the three
components of its image under the glueing functor of Stacks 0F9N — are étale.

The statement in the language of affine schemes over `Spec R` is
`BeauvilleLaszlo.etale_iff_baseChange`, which this reduces to: `L` and `V` are replaced by the
spectra of rings over `R` representing them (`AlgebraicGeometry.BigFppfOver.exists_specOver`),
`p` is read as a morphism of the site, and the space-level base changes are identified with the
scheme-level ones. -/
theorem isEtale_iff_isEtale_glueingComponents
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    {L V : AlgebraicSpaces B (Spec (.of R)) hX} (p : L ⟶ V)
    (hLa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX L.1)
    (hVa : AlgebraicGeometry.Space.IsAffineSpace B (Spec (.of R)) hX V.1)
    (hVg : AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX V) :
    AlgebraicGeometry.Space.IsEtale B (Spec (.of R)) hX p.hom ↔
      (AlgebraicGeometry.Space.IsEtale B (Spec (.of (Localization.Away f))) hU
          ((baseChange B (Spec (.of (Localization.Away f))) (Spec (.of R)) hU hX
            (canJU f B hU hX)).map p).hom ∧
        AlgebraicGeometry.Space.IsEtale B (Spec (.of (Localization.Away (g f)))) hU'
          ((baseChange B (Spec (.of (Localization.Away (g f)))) (Spec (.of R)) hU' hX
            (canGU g f B hU' hU ≫ canJU f B hU hX)).map p).hom ∧
        AlgebraicGeometry.Space.IsEtale B (Spec (.of R')) hX'
          ((baseChange B (Spec (.of R')) (Spec (.of R)) hX' hX (canJX' g B hX' hX)).map
            p).hom) := by
  let : Algebra R R' := g.toAlgebra
  obtain ⟨TL, hTL, ⟨eL0⟩⟩ := hLa
  obtain ⟨A, hA, φA, ⟨eL1⟩⟩ := BigFppfOver.exists_specOver B hX TL hTL
  obtain ⟨TV, hTV, ⟨eV0⟩⟩ := hVa
  obtain ⟨C, hC, φC, ⟨eV1⟩⟩ := BigFppfOver.exists_specOver B hX TV hTV
  let : Algebra R A := φA.hom.toAlgebra
  let : Algebra R C := φC.hom.toAlgebra
  obtain ⟨eL, eV, ψ, hψ⟩ :
      ∃ (eL : L.1 ≅ yoneda.obj (BigFppfOver.specOver B hX hA φA))
        (eV : V.1 ≅ yoneda.obj (BigFppfOver.specOver B hX hC φC))
        (ψ : BigFppfOver.specOver B hX hA φA ⟶ BigFppfOver.specOver B hX hC φC),
        yoneda.map ψ = eL.inv ≫ p.hom ≫ eV.hom :=
    ⟨eL0 ≪≫ yoneda.mapIso eL1, eV0 ≪≫ yoneda.mapIso eV1,
      yoneda.preimage ((eL0 ≪≫ yoneda.mapIso eL1).inv ≫ p.hom ≫
        (eV0 ≪≫ yoneda.mapIso eV1).hom), yoneda.map_preimage _⟩
  have hCg : (_root_.BeauvilleLaszlo.beauvilleLaszloModuleSequence (S := R')
      (C : Type u) f).ShortExact :=
    (_root_.BeauvilleLaszlo.isGlueableFor_iff_beauvilleLaszloModuleSequence_shortExact _ f).1
      (isGlueableFor_of_isGlueableGlobalSections g f B hX (C : Type u) hC
        (hVg (BigFppfOver.specOver B hX hC φC) eV.inv
          (BigFppfOver.isAffine_toScheme_obj_specOver B hX hC φC)
          (AlgebraicGeometry.Space.isEtale_of_isIso B (Spec (.of R)) hX eV.inv)))
  let h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (A : Type u)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (C : Type u)))) :=
    Over.homMk ((BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ)
      (BigFppfOver.specOverHomMap_comp B hX hA hC φA φC ψ)
  have hh : h.left = (BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ := rfl
  have hspace : AlgebraicGeometry.Space.IsEtale B (Spec (.of R)) hX p.hom ↔
      Etale ((BigFppfOver.toScheme B (Spec (.of R)) hX).map ψ) := by
    have e : Arrow.mk p.hom ≅ Arrow.mk (yoneda.map ψ) := Arrow.isoMk eL eV (by simp [hψ])
    exact (Iff.intro (isEtale_of_arrowIso B (Spec (.of R)) hX e)
      (isEtale_of_arrowIso B (Spec (.of R)) hX e.symm)).trans
      ((AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda B (Spec (.of R)) hX _).trans
        (AlgebraicGeometry.Space.presheaf_yoneda_map_etale_iff B (Spec (.of R)) hX ψ))
  refine hspace.trans ?_
  rw [← hh]
  refine (_root_.BeauvilleLaszlo.etale_iff_baseChange f hglue hCg h).trans
    (and_congr ?_ (and_congr ?_ ?_))
  · exact etale_overPullback_map_iff_isEtale_baseChange B _ _ hX hU (canJU f B hU hX) _ rfl ψ h
      hh p eL eV hψ
  · refine etale_overPullback_map_iff_isEtale_baseChange B _ _ hX hU'
      (canGU g f B hU' hU ≫ canJU f B hU hX) _ ?_ ψ h hh p eL eV hψ
    rw [Functor.map_comp]
    change Spec.map (CommRingCat.ofHom (Localization.awayMap g f)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) = _
    rw [← Spec.map_comp]
    congr 1
    ext r
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    rfl
  · exact etale_overPullback_map_iff_isEtale_baseChange B _ _ hX hX' (canJX' g B hX' hX) _ rfl ψ
      h hh p eL eV hψ

/-! ### Full faithfulness -/

/-- **Stacks 0F9R for étale, in the form the fullness argument of Stacks 0F9T consumes.** Given
any equivalence `E` of Stacks 0F9Q whose forward functor is identified with the glueing functor
of Stacks 0F9N, a morphism of affine glueable spaces over `Spec R` is étale exactly when the
three components of its image under `E` are étale. The identification `E.functorIso` reduces
this to the components of the image under the glueing functor, which are the three base
changes, and that is `isEtale_iff_isEtale_glueingComponents`. -/
private theorem isEtale_iff_affineGlueingEquivalenceSpec_components
    {R R' : Type u} [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R)))
    (hcomm : canGU g f B hU' hU ≫ canJU f B hU hX = canGX' g f B hU' hX' ≫ canJX' g B hX' hX)
    (E : AffineGlueingEquivalenceSpec g f B _ _ _ hU' hU hX' hX _ _
      (beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _ hcomm).functor)
    (Y Z : (affineGlueableSpaces g f B hX).FullSubcategory) (h : Y ⟶ Z) :
    AlgebraicGeometry.Space.IsEtale B (Spec (.of R)) hX h.hom.hom ↔
      (AlgebraicGeometry.Space.IsEtale B _ hU
          ((overU B _ _ _ hU' hU hX' (canGU g f B hU' hU) (canGX' g f B hU' hX')).map
            ((ObjectProperty.ι _).map (E.equivalence.functor.map h))).hom ∧
        AlgebraicGeometry.Space.IsEtale B _ hU'
          ((overU' B _ _ _ hU' hU hX' (canGU g f B hU' hU) (canGX' g f B hU' hX')).map
            ((ObjectProperty.ι _).map (E.equivalence.functor.map h))).hom ∧
        AlgebraicGeometry.Space.IsEtale B _ hX'
          ((overX' B _ _ _ hU' hU hX' (canGU g f B hU' hU) (canGX' g f B hU' hX')).map
            ((ObjectProperty.ι _).map (E.equivalence.functor.map h))).hom) := by
  have tU : ∀ {T : Scheme.{u}} (hT : B.Contains T)
      (O : GlueingData B _ _ _ hU' hU hX' (canGU g f B hU' hU) (canGX' g f B hU' hX') ⥤
        AlgebraicSpaces B T hT),
      AlgebraicGeometry.Space.IsEtale B T hT
          (O.map ((ObjectProperty.ι _).map (E.equivalence.functor.map h))).hom ↔
        AlgebraicGeometry.Space.IsEtale B T hT
          (O.map ((beauvilleLaszloGlueingSpaces B _ _ _ _ hU' hU hX' hX _ _ _ _
            hcomm).functor.map h.hom)).hom := fun hT O ↦
    ⟨fun hh ↦ map_property_of_natIso (fun {V W} p ↦ AlgebraicGeometry.Space.IsEtale B _ hT p)
        (CategoryTheory.Functor.isoWhiskerRight E.functorIso.symm (O ⋙ ObjectProperty.ι _))
        h hh,
      fun hh ↦ map_property_of_natIso (fun {V W} p ↦ AlgebraicGeometry.Space.IsEtale B _ hT p)
        (CategoryTheory.Functor.isoWhiskerRight E.functorIso (O ⋙ ObjectProperty.ι _))
        h hh⟩
  exact (isEtale_iff_isEtale_glueingComponents g f hglue B hU' hU hX' hX h.hom Y.property.1
    Z.property.1 Z.property.2).trans
    (and_congr
      (tU hU (overU B _ _ _ hU' hU hX' (canGU g f B hU' hU) (canGX' g f B hU' hX'))).symm
      (and_congr
        (tU hU' (overU' B _ _ _ hU' hU hX' (canGU g f B hU' hU) (canGX' g f B hU' hX'))).symm
        (tU hX' (overX' B _ _ _ hU' hU hX' (canGU g f B hU' hU) (canGX' g f B hU' hX'))).symm))

/-- **Stacks 0F9T, fullness.** For a Beauville--Laszlo glueing pair `(g : R → R', f)`, a
morphism of glueing triples between the images of two algebraic spaces over `Spec R` which are
glueable for `(g, f)` comes from a morphism of algebraic spaces, provided the target has affine
diagonal.

Nothing beyond the glueing pair and these two conditions is assumed: the equivalence of the
affine case is `BeauvilleLaszlo.Space.affineGlueingEquivalence` (Stacks 0F9Q) and étaleness of a
morphism of affine glueable spaces in terms of its components is
`BeauvilleLaszlo.Space.isEtale_iff_isEtale_glueingComponents` (Stacks 0F9R for the property
"étale"); both are supplied to
`beauvilleLaszloGlueingSpaces_map_surjective_of_isGlueable_of_affineDiagonal`. -/
@[stacks 0F9T "fullness"]
theorem beauvilleLaszloGlueingSpaces_map_surjective_of_isGlueable_of_isAffineHom_diag
    (R R' : Type u) [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R))) :
    let U' : Scheme.{u} := Spec (.of (Localization.Away (g f)))
    let U : Scheme.{u} := Spec (.of (Localization.Away f))
    let X' : Scheme.{u} := Spec (.of R')
    let X : Scheme.{u} := Spec (.of R)
    let gU : B.obj hU' ⟶ B.obj hU :=
      ⟨Spec.map (CommRingCat.ofHom (Localization.awayMap g f))⟩
    let gX' : B.obj hU' ⟶ B.obj hX' :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (g f))))⟩
    let jU : B.obj hU ⟶ B.obj hX :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))⟩
    let jX' : B.obj hX' ⟶ B.obj hX := ⟨Spec.map (CommRingCat.ofHom g)⟩
    ∀ (hcomm : gU ≫ jU = gX' ≫ jX') (Y Z : AlgebraicSpaces B X hX),
      AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Y →
      AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Z →
      AlgebraicGeometry.Space.IsAffineHom B X hX (diag Z.1) →
      Function.Surjective (fun (φ : Y ⟶ Z) ↦
        (beauvilleLaszloGlueingSpaces
          B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).functor.map φ) := by
  intro U' U X' X gU gX' jU jX' hcomm Y Z hY hZ hdiag
  exact beauvilleLaszloGlueingSpaces_map_surjective_of_isGlueable_of_affineDiagonal
    R R' g f hglue B hU' hU hX' hX hcomm
    (affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue)
    (isEtale_iff_affineGlueingEquivalenceSpec_components g f hglue B hU' hU hX' hX hcomm
      (affineGlueingEquivalence g f B hU' hU hX' hX hcomm hglue))
    Y Z hY hZ hdiag

/-- **Stacks 0F9T.** For a Beauville--Laszlo glueing pair `(g : R → R', f)`, the glueing functor
of Stacks 0F9N is fully faithful on the full subcategory of algebraic spaces `Y/X` which are
glueable for `(g, f)` and have affine diagonal `Y → Y ×_X Y`: the map it induces on each hom-set
between two such objects is bijective.

Injectivity is Stacks 0F9S, which needs glueability alone; surjectivity needs affineness of the
diagonal of the target alone, and is
`beauvilleLaszloGlueingSpaces_map_surjective_of_isGlueable_of_isAffineHom_diag`. -/
@[stacks 0F9T]
theorem beauvilleLaszloGlueingSpaces_map_bijective_of_isGlueable_of_isAffineHom_diag
    (R R' : Type u) [CommRing R] [CommRing R'] (g : R →+* R') (f : R)
    (hglue : _root_.BeauvilleLaszlo.IsGlueingPair g f) (B : BigFppfSite.{u})
    (hU' : B.Contains (Spec (.of (Localization.Away (g f)))))
    (hU : B.Contains (Spec (.of (Localization.Away f))))
    (hX' : B.Contains (Spec (.of R'))) (hX : B.Contains (Spec (.of R))) :
    let U' : Scheme.{u} := Spec (.of (Localization.Away (g f)))
    let U : Scheme.{u} := Spec (.of (Localization.Away f))
    let X' : Scheme.{u} := Spec (.of R')
    let X : Scheme.{u} := Spec (.of R)
    let gU : B.obj hU' ⟶ B.obj hU :=
      ⟨Spec.map (CommRingCat.ofHom (Localization.awayMap g f))⟩
    let gX' : B.obj hU' ⟶ B.obj hX' :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away (g f))))⟩
    let jU : B.obj hU ⟶ B.obj hX :=
      ⟨Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f)))⟩
    let jX' : B.obj hX' ⟶ B.obj hX := ⟨Spec.map (CommRingCat.ofHom g)⟩
    ∀ (hcomm : gU ≫ jU = gX' ≫ jX') (Y Z : AlgebraicSpaces B X hX),
      AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Y →
      AlgebraicGeometry.Space.IsGlueableAlgebraicSpace g f B hX Z →
      AlgebraicGeometry.Space.IsAffineHom B X hX (diag Y.1) →
      AlgebraicGeometry.Space.IsAffineHom B X hX (diag Z.1) →
      Function.Bijective (fun (φ : Y ⟶ Z) ↦
        (beauvilleLaszloGlueingSpaces
          B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm).functor.map φ) := by
  intro U' U X' X gU gX' jU jX' hcomm Y Z hY hZ _ hdiagZ
  exact ⟨beauvilleLaszloGlueingSpaces_map_injective_of_isGlueable
      R R' g f hglue B hU' hU hX' hX hcomm Y Z hY hZ,
    beauvilleLaszloGlueingSpaces_map_surjective_of_isGlueable_of_isAffineHom_diag
      R R' g f hglue B hU' hU hX' hX hcomm Y Z hY hZ hdiagZ⟩

end BeauvilleLaszlo.Space

end
