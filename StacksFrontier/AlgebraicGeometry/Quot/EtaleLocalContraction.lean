module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocalContractionLimit
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessLocal
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksFrontier.AlgebraicGeometry.Quot.ExtendsFibreIsoNearPoint

/-!
# Contractions of a fibre of a family of curves extend étale locally (Stacks 0E7C)

Let `f : X ⟶ S` be a family of curves, `s ∈ S` a point and `h₀ : X_s ⟶ Y₀` a morphism to a proper
scheme over `κ(s)` with `h₀,*𝒪_{X_s} = 𝒪_{Y₀}` and `R¹h₀,*𝒪_{X_s} = 0`. Then there are an
elementary étale neighbourhood `(U, u) ⟶ (S, s)`, a family of curves `Y ⟶ U` and a morphism
`h : X_U ⟶ Y` over `U` whose fibre in `u` is isomorphic to `h₀` ([Stacks, Tag 0E7C]).

The proof is the source's, organised as follows.

* The question is local on `S`, so `S` may be replaced by an affine open neighbourhood `Spec A` of
  `s` (the conclusion is pushed forward along the open immersion,
  `AlgebraicGeometry.EtaleLocalContraction.HasEtaleLocalExtension.comp_etale`).
* Over an affine base the statement is
  `AlgebraicGeometry.EtaleLocalContraction.hasEtaleLocalExtension_of_affine`: the family and `h₀`
  descend to a base of finite type over `ℤ` and a residue field of it, where the Noetherian case
  `AlgebraicGeometry.EtaleLocalContraction.hasEtaleLocalExtension_of_isNoetherianRing` (the
  complete case by deformation theory, [Stacks, Tag 0E3X], followed by Artin approximation)
  applies.
* The étale neighbourhood is elementary because the point `Spec κ(s) ⟶ S` lifts to it
  (`AlgebraicGeometry.EtaleLocalContraction.isIso_residueFieldMap_of_isIso_comp`).

## Main results

* `AlgebraicGeometry.CurveFamily.exists_elementaryEtale_extension_of_fibre`: [Stacks, Tag 0E7C].
* `AlgebraicGeometry.EtaleLocalContraction.hasEtaleLocalExtension_of_residueFieldValuedPoint`:
  the same over an arbitrary object of the site, for a presheaf family.
* `AlgebraicGeometry.EtaleLocalContraction.exists_affineOpen_fromSpecResidueField`: the point
  `Spec κ(s) ⟶ S` factors through an affine open neighbourhood as the point of a prime.

## Conventions

The family `f : X ⟶ S` is an `AlgebraicGeometry.CurveFamily`. The point `s` is given by a
field-valued point `p` of `S` whose field is `κ(s)`: its morphism `Spec K ⟶ S` is the canonical
`Spec κ(s) ⟶ S` precomposed with an isomorphism `Spec K ≅ Spec κ(s)`. The fibre `X_s` is presented,
as in the rest of the chapter, by an object `V` of the site with a cartesian square over `p`, and
`h₀ : V ⟶ Y₀` is a morphism of schemes over `Spec K`; the two conditions on `h₀` are
`𝒪_{Y₀} ≅ h₀,*𝒪_V` and `R¹h₀,*𝒪_V = 0` (with `R¹` the first right derived functor of the direct
image). The conclusion presents the fibre of `Y` over the lift `ū : Spec K ⟶ U` of `p` by an object
`W` with `W ≅ Y₀` over `K`, and the fibre of `h` over `ū` by `a : V ⟶ W` with `a = h₀` through this
identification.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace EtaleLocalContraction

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **The conclusion of [Stacks, Tag 0E7C] pushes forward along an étale morphism of bases.** If it
holds for `f' : X' ⟶ T'` at `k'`, and `X'` is the base change of `f : X ⟶ T` along an étale
`j : T' ⟶ T`, it holds for `f` at `k' ≫ j`. -/
theorem HasEtaleLocalExtension.comp_etale {T T' K F : BigFppfOver B integerBase hZ}
    {X X' : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {f' : X' ⟶ yoneda.obj T'} {k' : K ⟶ T'}
    {tX : F ⟶ K} {iX' : yoneda.obj F ⟶ X'} {Y₀ : Scheme.{u}} {pY₀ : Y₀ ⟶ (𝒯).obj K}
    {h₀ : (𝒯).obj F ⟶ Y₀} (H : HasEtaleLocalExtension f' k' tX iX' pY₀ h₀) (j : T' ⟶ T)
    (hj : Etale ((𝒯).map j)) (f : X ⟶ yoneda.obj T) (q : X' ⟶ X)
    (sq : IsPullback q f' f (yoneda.map j)) :
    HasEtaleLocalExtension f (k' ≫ j) tX (iX' ≫ q) pY₀ h₀ := by
  obtain ⟨U, e, ū, he, hū, Y, XU, g, pXU, fXU, h, hY, hXU, hflg, hprg, hfpg, hdg, sqXU, hhg,
    iXU, G, tG, iG, φ, a, hiXU, hiXUp, hiG, hφ, hat, hcomp, ha⟩ := H
  have hej : Etale ((𝒯).map (e ≫ j)) := by
    rw [Functor.map_comp]
    infer_instance
  have sq' : IsPullback (pXU ≫ q) fXU f (yoneda.map (e ≫ j)) := by
    rw [Functor.map_comp]
    exact sqXU.paste_horiz sq
  exact ⟨U, e ≫ j, ū, hej, by rw [← Category.assoc, hū], Y, XU, g, pXU ≫ q, fXU, h, hY, hXU,
    hflg, hprg, hfpg, hdg, sq', hhg, iXU, G, tG, iG, φ, a, hiXU, by rw [← Category.assoc, hiXUp],
    hiG, hφ, hat, hcomp, ha⟩

/-- **A lift through a morphism of a point with invertible residue field map has invertible
residue field map**: if the residue field map of `f ≫ g` at `x` is invertible, so is that of `g`
at `f x` (the residue field map of `f` at `x`, a homomorphism of fields, is then surjective and
injective). -/
alias isIso_residueFieldMap_of_isIso_comp := AlgebraicGeometry.residueFieldMap_isIso_of_comp

/-- **A morphism with `𝒪_Y ≅ h_*𝒪_X` which is closed does not raise the dimension.** Such a
morphism is scheme-theoretically dominant, hence surjective. -/
theorem topologicalKrullDim_le_of_isIso_unitToPushforwardUnit {X Y : Scheme.{u}} (h : X ⟶ Y)
    [QuasiCompact h] (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h))
    (hclosed : IsClosedMap h) : topologicalKrullDim Y ≤ topologicalKrullDim X := by
  have := isSchemeTheoreticallyDominant_of_isIso_unitToPushforwardUnit h
  have hsurj : Function.Surjective h := by
    rw [← Set.range_eq_univ, ← (hclosed.isClosed_range).closure_eq]
    exact h.denseRange.closure_range
  exact Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap h
    h.continuous hsurj (Or.inl hclosed.specializingMap)

/-- **A fibre of a family of curves over a field has dimension at most one.** If a morphism
`t : V ⟶ Spec K` of the site (for a field `K`) is flat, proper, of finite presentation and of
relative dimension at most one as a morphism of algebraic spaces, the scheme `V` has dimension at
most one. -/
theorem topologicalKrullDim_le_one_of_field {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
    {V : BigFppfOver B integerBase hZ} (t : V ⟶ integerSiteObject B hZ hK)
    (hfl : Space.IsFlat B integerBase hZ (yoneda.map t))
    (hpr : Space.IsProper B integerBase hZ (yoneda.map t))
    (hfp : Space.IsFinitePresentation B integerBase hZ (yoneda.map t))
    (hd : Space.HasRelativeDimensionLE 1 B integerBase hZ (yoneda.map t)) :
    topologicalKrullDim ((𝒯).obj V) ≤ 1 := by
  obtain ⟨F', t', e, -, hdim⟩ := Space.exists_presentation_of_curveFamilyConditions_of_field hK
    (isAlgebraicSpace_yoneda B integerBase hZ V) (yoneda.map t) hfl hpr hfp hd
  let ε : F' ≅ V := Yoneda.fullyFaithful.preimageIso e
  rwa [← ((𝒯).mapIso ε).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]

/-- **The point `Spec κ(s) ⟶ S` factors through an affine open neighbourhood of `s`** as the
point of `Spec A` given by a prime `𝔭` and an isomorphism `κ(𝔭) ≅ κ(s)`. -/
theorem exists_affineOpen_fromSpecResidueField (S : Scheme.{u}) (s : S) :
    ∃ (W : S.Opens) (hW : IsAffineOpen W) (𝔭 : Ideal Γ(S, W)) (_ : 𝔭.IsPrime)
      (ψ : 𝔭.ResidueField ≃+* S.residueField s),
      s ∈ W ∧ S.fromSpecResidueField s =
        Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (algebraMap Γ(S, W) 𝔭.ResidueField))) ≫
          hW.fromSpec := by
  obtain ⟨W, hW, hsW, -⟩ := exists_isAffineOpen_mem_and_subset (x := s) (U := ⊤) trivial
  obtain ⟨x, hx⟩ : s ∈ Set.range hW.fromSpec := by rwa [hW.range_fromSpec]
  let e : CommRingCat.of x.asIdeal.ResidueField ≅ S.residueField s :=
    (Scheme.Spec.residueFieldIso _ x).symm ≪≫ (asIso (hW.fromSpec.residueFieldMap x)).symm ≪≫
      S.residueFieldCongr hx
  refine ⟨W, hW, x.asIdeal, inferInstance, e.commRingCatIsoToRingEquiv, hsW, ?_⟩
  have h₁ : CommRingCat.ofHom (e.commRingCatIsoToRingEquiv.toRingHom.comp
      (algebraMap Γ(S, W) x.asIdeal.ResidueField)) =
      CommRingCat.ofHom (algebraMap Γ(S, W) x.asIdeal.ResidueField) ≫ e.hom := rfl
  rw [h₁]
  simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv, Spec.map_comp, Category.assoc,
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField_assoc]
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField hW.fromSpec x,
    ← Spec.map_comp_assoc (hW.fromSpec.residueFieldMap x), IsIso.hom_inv_id, Spec.map_id,
    Category.id_comp, Scheme.residueFieldCongr_fromSpecResidueField]

/-- A morphism of schemes between objects of the site is a morphism of the site: it automatically
lies over the terminal base. -/
private def siteHomMk {F G : BigFppfOver B integerBase hZ} (f : F.left.1 ⟶ G.left.1) : F ⟶ G :=
  Over.homMk (ObjectProperty.homMk f) (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- The object of the site given by a field-valued point is the spectrum of its field over the
integers. -/
private def fieldValuedPointSiteObjectIso {G : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (p : Space.FieldValuedPoint B integerBase hZ G) :
    p.siteObject ≅ integerSiteObject B hZ p.contained where
  hom := siteHomMk (𝟙 _)
  inv := siteHomMk (𝟙 _)
  hom_inv_id := Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Category.id_comp _))
  inv_hom_id := Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Category.id_comp _))

/-- A morphism of the site which is proper as a morphism of algebraic spaces is proper as a
morphism of schemes. -/
private theorem isProper_map_of_isProper_yoneda_map {F G : BigFppfOver B integerBase hZ} (t : F ⟶ G)
    (ht : Space.IsProper B integerBase hZ (yoneda.map t)) : IsProper ((𝒯).map t) :=
  ((Space.presheaf_isProper_iff B integerBase hZ (yoneda.map t)
    (isAlgebraicSpace_yoneda B integerBase hZ F) (isAlgebraicSpace_yoneda B integerBase hZ G)
    (Functor.relativelyRepresentable.map _ _)).1 ht).property (𝟙 _) (𝟙 _) t
    (IsPullback.of_horiz_isIso ⟨by simp⟩)

/-- **A proper morphism over a proper base with `𝒪_Y ≅ h_*𝒪_X` does not raise the dimension.** -/
private theorem topologicalKrullDim_le_of_isIso_unitToPushforwardUnit_of_comp {X Y Z : Scheme.{u}}
    (h : X ⟶ Y) (q : Y ⟶ Z) [IsProper q] [IsProper (h ≫ q)]
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h)) :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  have : IsProper h := IsProper.of_comp h q
  topologicalKrullDim_le_of_isIso_unitToPushforwardUnit h h0 h.isClosedMap

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **[Stacks, Tag 0E7C] over an arbitrary base**, at the point `Spec κ(s) ⟶ T` of a point `s` of
an object `T` of the site. Let `f : X ⟶ T` be a family of curves whose fibre over `κ(s)` is
presented by `tX : F ⟶ Spec κ(s)`, and let `h₀ : F ⟶ Y₀` be a morphism over `κ(s)` to a proper
scheme with `𝒪_{Y₀} ≅ h₀,*𝒪_F` and `R¹h₀,*𝒪_F = 0`. Then the conclusion of the tag holds at the
point. The question is local on `T`: the point factors through an affine open neighbourhood of
`s`, over which this is `hasEtaleLocalExtension_of_affine`, and the conclusion is pushed forward
along the open immersion. The bounds `dim F ≤ 1` and `dim Y₀ ≤ 1` of the affine case come from the
family (`topologicalKrullDim_le_one_of_field`) and from `𝒪_{Y₀} ≅ h₀,*𝒪_F`
(`topologicalKrullDim_le_of_isIso_unitToPushforwardUnit`). -/
theorem hasEtaleLocalExtension_of_residueFieldValuedPoint (T : BigFppfOver B integerBase hZ)
    (s : T.left.1) {X : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B integerBase hZ X) (f : X ⟶ yoneda.obj T)
    (hfl : Space.IsFlat B integerBase hZ f) (hpr : Space.IsProper B integerBase hZ f)
    (hfp : Space.IsFinitePresentation B integerBase hZ f)
    (hd : Space.HasRelativeDimensionLE 1 B integerBase hZ f) {F : BigFppfOver B integerBase hZ}
    (tX : F ⟶ (CurveFamily.residueFieldValuedPoint B hZ T s).siteObject)
    (iX : yoneda.obj F ⟶ X)
    (hiX : IsPullback iX (yoneda.map tX) f
      (yoneda.map (CurveFamily.residueFieldValuedPoint B hZ T s).value))
    {Y₀ : Scheme.{u}}
    (pY₀ : Y₀ ⟶ (𝒯).obj (CurveFamily.residueFieldValuedPoint B hZ T s).siteObject)
    [IsProper pY₀] (h₀ : (𝒯).obj F ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = (𝒯).map tX)
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR1 : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit ((𝒯).obj F).ringCatSheaf))) :
    HasEtaleLocalExtension f (CurveFamily.residueFieldValuedPoint B hZ T s).value tX iX pY₀
      h₀ := by
  classical
  let p := CurveFamily.residueFieldValuedPoint B hZ T s
  obtain ⟨W, hW, 𝔭, h𝔭, ψ, -, hpt⟩ := exists_affineOpen_fromSpecResidueField ((𝒯).obj T) s
  -- the affine open neighbourhood as an object of the site, and the point over it
  have hA : B.Contains (Spec (.of Γ((𝒯).obj T, W))) :=
    B.contains_of_isOpenImmersion hW.fromSpec T.left.property
  let j : integerSiteObject B hZ hA ⟶ T := siteHomMk hW.fromSpec
  let mIso := fieldValuedPointSiteObjectIso p
  let kA := integerSiteMap B hZ p.contained hA
    (Spec.map (CommRingCat.ofHom (ψ.toRingHom.comp (algebraMap _ 𝔭.ResidueField))))
  have hkm : (CurveFamily.residueFieldValuedPoint B hZ T s).value = mIso.hom ≫ kA ≫ j :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ (hpt.trans (Category.id_comp _).symm))
  -- the base change of the family to the affine open
  have hFa := isAlgebraicSpace_yoneda B integerBase hZ F
  have hX' := isAlgebraicSpace_pullback B integerBase hZ f (yoneda.map j) hX
    (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ T)
  have sq := IsPullback.of_hasPullback f (yoneda.map j)
  obtain ⟨hfl', hpr', hfp', hd'⟩ :=
    Space.curveFamilyConditions_of_isPullback B integerBase hZ sq hX hX' hfl hpr hfp hd
  -- the fibre of the base change over the point of the affine open
  have hiX₂ : IsPullback iX (yoneda.map (tX ≫ mIso.hom)) f (yoneda.map (kA ≫ j)) :=
    IsPullback.of_iso hiX (Iso.refl _) (Iso.refl _) (yoneda.mapIso mIso) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp [hkm])
  let iX' : yoneda.obj F ⟶ pullback f (yoneda.map j) :=
    pullback.lift iX (yoneda.map (tX ≫ mIso.hom ≫ kA)) (by
      rw [hiX₂.w]; simp only [Functor.map_comp, Category.assoc])
  have hiX' : IsPullback iX' (yoneda.map (tX ≫ mIso.hom)) (pullback.snd f (yoneda.map j))
      (yoneda.map kA) :=
    IsPullback.of_right (by rwa [pullback.lift_fst, ← Functor.map_comp])
      (by rw [pullback.lift_snd, ← Functor.map_comp, Category.assoc]) sq
  -- the dimensions of `F` and `Y₀`
  obtain ⟨hflF, hprF, hfpF, hdF⟩ :=
    Space.curveFamilyConditions_of_isPullback B integerBase hZ hiX' hX' hFa hfl' hpr' hfp' hd'
  have hdimF : topologicalKrullDim ((𝒯).obj F) ≤ 1 :=
    topologicalKrullDim_le_one_of_field p.contained (tX ≫ mIso.hom) hflF hprF hfpF hdF
  have h𝒯t : (𝒯).map (tX ≫ mIso.hom) = (𝒯).map tX :=
    (Functor.map_comp _ _ _).trans (Category.comp_id _)
  have : IsProper (h₀ ≫ pY₀) := by
    rw [hh₀, ← h𝒯t]
    exact isProper_map_of_isProper_yoneda_map _ hprF
  have hdimY : topologicalKrullDim Y₀ ≤ 1 :=
    (topologicalKrullDim_le_of_isIso_unitToPushforwardUnit_of_comp h₀ pY₀ h0).trans hdimF
  -- the affine case, pushed forward along the open immersion
  have : IsProper (pY₀ : Y₀ ⟶ Spec (.of p.carrier)) := ‹IsProper pY₀›
  have hj : Etale ((𝒯).map j) := inferInstanceAs (Etale hW.fromSpec)
  have H' := (hasEtaleLocalExtension_of_affine (B := B) (hZ := hZ) Γ((𝒯).obj T, W) hA 𝔭
    p.carrier p.contained ψ hX' (pullback.snd f (yoneda.map j)) hfl' hpr' hfp' (tX ≫ mIso.hom)
    iX' hiX' hdimF pY₀ hdimY h₀ (by rwa [h𝒯t]) h0 hR1).comp_etale j hj f (pullback.fst _ _) sq
  rw [show iX' ≫ pullback.fst _ _ = iX from pullback.lift_fst _ _ _] at H'
  -- transport along the identification of the two spectra of `κ(s)`
  exact H'.baseChange f (𝟙 X) (𝟙 T) (IsPullback.of_horiz_isIso ⟨by simp⟩) p.value mIso.hom
    ((Category.comp_id _).trans hkm) tX iX hiX (𝟙 F) (by simp) (by simp) pY₀ (𝟙 Y₀)
    (IsPullback.of_horiz_isIso ⟨(Category.id_comp _).trans (Category.comp_id _).symm⟩) h₀ hh₀
    (by simp)

/-- **A factorisation of the point `Spec κ(s) ⟶ T` through a morphism is an elementary
neighbourhood**: if `ū ≫ e` is the point `Spec κ(s) ⟶ T` of `s`, the image `u` of the point of
`Spec κ(s)` in `U` lies over `s`, and `κ(s) ⟶ κ(u)` is an isomorphism. -/
theorem exists_isIso_residueFieldMap_of_comp_eq (T : BigFppfOver B integerBase hZ)
    (s : T.left.1) {U : BigFppfOver B integerBase hZ} (e : U ⟶ T)
    (ū : (CurveFamily.residueFieldValuedPoint B hZ T s).siteObject ⟶ U)
    (hū : ū ≫ e = (CurveFamily.residueFieldValuedPoint B hZ T s).value) :
    ∃ u : U.left.1, (𝒯).map e u = s ∧ IsIso (((𝒯).map e).residueFieldMap u) := by
  let pt : Spec (T.left.1.residueField s) := IsLocalRing.closedPoint (T.left.1.residueField s)
  have h𝒯 : (𝒯).map ū ≫ (𝒯).map e = T.left.1.fromSpecResidueField s := by
    rw [← Functor.map_comp, hū]
    rfl
  refine ⟨(𝒯).map ū pt, ?_, ?_⟩
  · change ((𝒯).map ū ≫ (𝒯).map e) pt = s
    rw [h𝒯]
    exact Scheme.fromSpecResidueField_apply _ _
  · refine isIso_residueFieldMap_of_isIso_comp ((𝒯).map ū) ((𝒯).map e) pt ?_
    rw [h𝒯]
    exact isIso_residueFieldMap_fromSpecResidueField _ s pt

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **[Stacks, Tag 0E7C].** Let `X` be a family of curves over a scheme `S` of the site, `s ∈ S`,
let `V` present the fibre of `X` over `κ(s)` (through `v : V ⟶ Spec κ(s)` and a cartesian
square `q`), and let `h₀ : V ⟶ Y₀` be a morphism over `κ(s)` to a proper scheme with
`𝒪_{Y₀} ≅ h₀,*𝒪_V` and `R¹h₀,*𝒪_V = 0`. Then there are an elementary étale neighbourhood
`e : (U, u) ⟶ (S, s)` (`e` étale, `e u = s`, `κ(s) ≅ κ(u)`, and the point `Spec κ(s) ⟶ S` lifts
to `ū : Spec κ(s) ⟶ U`), a family of curves `g : Y ⟶ U` (flat, proper, of finite presentation,
of relative dimension at most one) and a morphism `h : X_U ⟶ Y` over `U` from the base change
`X_U` of `X`, such that the fibre `tG : G ⟶ Spec κ(s)` of `Y` over `ū` is isomorphic to `Y₀` over
`κ(s)` and the fibre `a : V ⟶ G` of `h` over `ū` is `h₀` through this isomorphism. -/
theorem _root_.AlgebraicGeometry.CurveFamily.exists_elementaryEtale_extension_of_fibre
    (X : CurveFamily B hZ)
    (s : X.base.left.1) {V : BigFppfOver B integerBase hZ}
    (v : V ⟶ (CurveFamily.residueFieldValuedPoint B hZ X.base s).siteObject)
    (q : schemeSpace V ⟶ X.total)
    (hq : IsPullback q (schemeSpaceMap v) X.toBase
      (schemeSpaceMap (CurveFamily.residueFieldValuedPoint B hZ X.base s).value))
    {Y₀ : Scheme.{u}}
    (pY₀ : Y₀ ⟶ (𝒯).obj (CurveFamily.residueFieldValuedPoint B hZ X.base s).siteObject)
    [IsProper pY₀] (h₀ : (𝒯).obj V ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = (𝒯).map v)
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR1 : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit ((𝒯).obj V).ringCatSheaf))) :
    ∃ (U : BigFppfOver B integerBase hZ) (e : U ⟶ X.base)
      (ū : (CurveFamily.residueFieldValuedPoint B hZ X.base s).siteObject ⟶ U),
      Etale ((𝒯).map e) ∧ ū ≫ e = (CurveFamily.residueFieldValuedPoint B hZ X.base s).value ∧
      (∃ u : U.left.1, (𝒯).map e u = s ∧ IsIso (((𝒯).map e).residueFieldMap u)) ∧
      ∃ (Y XU : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) (g : Y ⟶ yoneda.obj U)
        (pXU : XU ⟶ X.total.obj) (fXU : XU ⟶ yoneda.obj U) (h : XU ⟶ Y),
        IsAlgebraicSpace B integerBase hZ Y ∧ IsAlgebraicSpace B integerBase hZ XU ∧
        Space.IsFlat B integerBase hZ g ∧ Space.IsProper B integerBase hZ g ∧
        Space.IsFinitePresentation B integerBase hZ g ∧
        Space.HasRelativeDimensionLE 1 B integerBase hZ g ∧
        IsPullback pXU fXU X.toBase.hom (yoneda.map e) ∧ h ≫ g = fXU ∧
        ∃ (iXU : yoneda.obj V ⟶ XU) (G : BigFppfOver B integerBase hZ)
          (tG : G ⟶ (CurveFamily.residueFieldValuedPoint B hZ X.base s).siteObject)
          (iG : yoneda.obj G ⟶ Y) (φ : (𝒯).obj G ≅ Y₀) (a : V ⟶ G),
          IsPullback iXU (yoneda.map v) fXU (yoneda.map ū) ∧ iXU ≫ pXU = q.hom ∧
          IsPullback iG (yoneda.map tG) g (yoneda.map ū) ∧ φ.hom ≫ pY₀ = (𝒯).map tG ∧
          a ≫ tG = v ∧ iXU ≫ h = yoneda.map a ≫ iG ∧ (𝒯).map a ≫ φ.hom = h₀ := by
  have hp : yonedaEquiv.symm (CurveFamily.residueFieldValuedPoint B hZ X.base s).value =
      yoneda.map (CurveFamily.residueFieldValuedPoint B hZ X.base s).value :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map _).symm
  have hiX := CurveFamily.isPullback_yoneda_of_isPullback_schemeSpace X.toBase _ hq
  rw [hp] at hiX
  obtain ⟨U, e, ū, he, hū, rest⟩ := hasEtaleLocalExtension_of_residueFieldValuedPoint X.base s
    X.total.property X.toBase.hom X.flat X.proper X.finitePresentation
    X.relativeDimensionLE v q.hom hiX pY₀ h₀ hh₀ h0 hR1
  exact ⟨U, e, ū, he, hū, exists_isIso_residueFieldMap_of_comp_eq X.base s e ū hū, rest⟩

end EtaleLocalContraction

end AlgebraicGeometry

end
