module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocallyProjectiveCurvesChartEquation
public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocallyProjectiveCurvesCommonNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionClosedFibreFieldDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatReadingHenselianNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PresheafPointTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseMorphism

/-!
# Families of curves are étale locally schemes (Stacks 0E6F, pointwise)

Let `X ⟶ S` be a family of curves and `s ∈ S`. Then there is an étale morphism `U ⟶ S` through
`s` such that `X ×_S U` is a scheme.

## Main definitions

* `AlgebraicGeometry.CurveFamily.residueFieldIntegerMap`: the residue-field point `Spec κ(s) ⟶ S`
  of the base of a family, as a morphism of the site.

## Main results

* `AlgebraicGeometry.CurveFamily.exists_isPullback_residueField`: the fibre `X_s` presented by a
  scheme of dimension at most one over `Spec κ(s)` (Stacks 0ADD).
* `AlgebraicGeometry.CurveFamily.exists_elementaryEtaleChart_of_mem_fibre`: an affine elementary
  étale chart of `X` at a point of the fibre.
* `AlgebraicGeometry.CurveFamily.exists_chartDivisor_of_fibre_equation`: a closed subscheme of
  such a chart, principal near its point, cutting out an effective Cartier divisor on the fibre.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- The residue-field point `Spec κ(s) ⟶ S` of the base of a family, from the spectrum of the
residue field read as a scheme over the integers. -/
def residueFieldIntegerMap (X : CurveFamily B hZ) (s : (𝒯).obj X.base) :
    integerSiteObject B hZ (B.residueField_spec_contains X.base.left.property s) ⟶ X.base :=
  Over.homMk (⟨X.base.left.1.fromSpecResidueField s⟩ :
      B.obj (B.residueField_spec_contains X.base.left.property s) ⟶ X.base.left) (by
    apply ObjectProperty.hom_ext
    exact specULiftZIsTerminal.hom_ext _ _)

/-- The morphism of schemes underlying `residueFieldIntegerMap X s` is `Spec κ(s) ⟶ S`. -/
theorem toScheme_map_residueFieldIntegerMap (X : CurveFamily B hZ) (s : (𝒯).obj X.base) :
    (𝒯).map (residueFieldIntegerMap X s) = ((𝒯).obj X.base).fromSpecResidueField s := rfl

/-- **The fibre of a family of curves is a scheme of dimension at most one** (Stacks 0ADD). The
base change of `X ⟶ S` along `Spec κ(s) ⟶ S` is presented by a scheme `V` of the site, of
dimension at most one. -/
theorem exists_isPullback_residueField (X : CurveFamily B hZ) (s : (𝒯).obj X.base) :
    ∃ (V : BigFppfOver B integerBase hZ)
      (v : V ⟶ integerSiteObject B hZ (B.residueField_spec_contains X.base.left.property s))
      (j : yoneda.obj V ⟶ X.total.obj),
      IsPullback j (yoneda.map v) X.toBase.hom (yoneda.map (residueFieldIntegerMap X s)) ∧
        topologicalKrullDim ((𝒯).obj V) ≤ 1 := by
  let r := residueFieldIntegerMap X s
  let P := pullback X.toBase.hom (yoneda.map r)
  have sq : IsPullback (pullback.fst X.toBase.hom (yoneda.map r))
      (pullback.snd X.toBase.hom (yoneda.map r)) X.toBase.hom (yoneda.map r) :=
    IsPullback.of_hasPullback _ _
  have hP : IsAlgebraicSpace B integerBase hZ P :=
    isAlgebraicSpace_pullback B integerBase hZ _ _ X.total.property
      (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
  have hflat : Space.IsFlat B integerBase hZ (pullback.snd X.toBase.hom (yoneda.map r)) :=
    Space.isFlat_of_isPullback_of_isAlgebraicSpace B integerBase hZ sq.flip X.total.property
      (isAlgebraicSpace_yoneda B integerBase hZ _) X.flat
  have hproper : Space.IsProper B integerBase hZ (pullback.snd X.toBase.hom (yoneda.map r)) :=
    Space.isProper_of_isPullback B integerBase hZ hP X.total.property
      (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
      sq X.proper
  have hfp : Space.IsFinitePresentation B integerBase hZ
      (pullback.snd X.toBase.hom (yoneda.map r)) :=
    Space.isFinitePresentation_of_isPullback B integerBase hZ hP X.total.property
      (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
      sq X.finitePresentation
  have hd : Space.HasRelativeDimensionLE 1 B integerBase hZ
      (pullback.snd X.toBase.hom (yoneda.map r)) := by
    intro x'
    obtain ⟨e, he, hrel⟩ := X.relativeDimensionLE
      (Space.pointsMap B integerBase hZ P (pullback.fst X.toBase.hom (yoneda.map r)) x')
    exact ⟨e, he, (Space.hasRelativeDimensionAt_iff_of_isPullback B integerBase hZ sq
      X.total.property (isAlgebraicSpace_yoneda B integerBase hZ _)
      (isAlgebraicSpace_yoneda B integerBase hZ _)
      (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
        X.finitePresentation.1) x' (e : ℕ∞)).1 hrel⟩
  obtain ⟨V, t, e, he, hdim⟩ := Space.exists_presentation_of_curveFamilyConditions_of_field
    (B.residueField_spec_contains X.base.left.property s) hP _ hflat hproper hfp hd
  exact ⟨V, t, e.hom ≫ pullback.fst X.toBase.hom (yoneda.map r),
    sq.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp [← he])
      (by simp) ((Category.comp_id _).trans (Category.id_comp _).symm), hdim⟩

/-- A morphism of the site whose underlying scheme morphism is a monomorphism is a monomorphism
of presheaves after applying Yoneda. -/
private theorem mono_yoneda_map_of_mono_map {U U' : BigFppfOver B integerBase hZ} (f : U ⟶ U')
    (h : Mono ((𝒯).map f)) : Mono (yoneda.map f) := by
  have := (𝒯).mono_of_mono_map h
  exact Functor.map_mono yoneda f

/-- **An affine elementary étale chart at a point of the fibre.** Let `V` present the fibre of a
family of curves `X ⟶ S` over `Spec κ(s)` and `x ∈ V`. There are an affine scheme `W` of the site,
an étale `e : W ⟶ X` and a point `w ∈ W` whose residue-field point is a monomorphism into `X`
(Stacks 0BBP), lying over the image of `x` in `|X|`, together with the composite `W ⟶ S`. -/
theorem exists_elementaryEtaleChart_of_mem_fibre (X : CurveFamily B hZ) (s : (𝒯).obj X.base)
    {V : BigFppfOver B integerBase hZ}
    (v : V ⟶ integerSiteObject B hZ (B.residueField_spec_contains X.base.left.property s))
    (j : yoneda.obj V ⟶ X.total.obj)
    (hsq : IsPullback j (yoneda.map v) X.toBase.hom (yoneda.map (residueFieldIntegerMap X s)))
    (x : (𝒯).obj V) :
    ∃ (W : BigFppfOver B integerBase hZ) (e : yoneda.obj W ⟶ X.total.obj) (w : W.left.1)
      (hw : B.Contains (Spec (.of (W.left.1.residueField w)))) (gW : W ⟶ X.base),
      (MorphismProperty.inverseImage @Etale (𝒯)).presheaf e ∧
      Mono (yoneda.map (Space.residueFieldMap B integerBase hZ W w hw) ≫ e) ∧
      e ≫ X.toBase.hom = yoneda.map gW ∧ IsAffine ((𝒯).obj W) ∧
      Space.pointsMap B integerBase hZ _ e (Space.presheafPoint B integerBase hZ W w hw) =
        Space.pointsMap B integerBase hZ _ j (Space.presheafPoint B integerBase hZ V x
          (B.residueField_spec_contains V.left.property x)) := by
  let fX : X.total.obj ⟶ yoneda.obj X.base := X.toBase.hom
  have hsq' : IsPullback j (yoneda.map v) fX (yoneda.map (residueFieldIntegerMap X s)) := hsq
  obtain ⟨S₁, hS₁, hsS₁, -⟩ := exists_isAffineOpen_mem_and_subset (X := (𝒯).obj X.base) (x := s)
    (U := ⊤) trivial
  have : IsAffine (S₁ : Scheme.{u}) := hS₁
  have hc : B.Contains (S₁ : Scheme.{u}) :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B S₁.ι X.base.left.property
  let U₁ : BigFppfOver B integerBase hZ :=
    BigFppfOver.siteObjectOver B integerBase hZ X.base hc S₁.ι
  let ι₁ : U₁ ⟶ X.base := BigFppfOver.siteMapOver B integerBase hZ X.base hc S₁.ι
  have hι₁ : (𝒯).map ι₁ = S₁.ι := rfl
  have : IsAffine ((𝒯).obj U₁) := hS₁
  let X₁ := pullback fX (yoneda.map ι₁)
  have sq₁ : IsPullback (pullback.fst fX (yoneda.map ι₁))
      (pullback.snd fX (yoneda.map ι₁)) fX (yoneda.map ι₁) :=
    IsPullback.of_hasPullback _ _
  have hX₁ : IsAlgebraicSpace B integerBase hZ X₁ :=
    isAlgebraicSpace_pullback B integerBase hZ _ _ X.total.property
      (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
  have hsep₁ : Space.IsSeparated B integerBase hZ (pullback.snd fX (yoneda.map ι₁)) :=
    Space.isSeparated_of_isPullback B integerBase hZ sq₁ X.proper.1
  have habs := Space.isAbsolutelySeparated_of_isSeparated_to_affine B integerBase hZ
    B.contains_terminal U₁ hS₁ _ hsep₁
  have hdec : Space.IsDecentSpace B integerBase hZ X₁ :=
    Space.isDecentSpace_of_isAbsolutelyQuasiSeparated B integerBase hZ X₁ hX₁
      (Space.isAbsolutelyQuasiSeparated_of_isAbsolutelySeparated B integerBase hZ
        B.contains_terminal X₁ habs)
  let r := residueFieldIntegerMap X s
  have hrange : Set.range ((𝒯).map r) ⊆ Set.range S₁.ι := by
    change Set.range (((𝒯).obj X.base).fromSpecResidueField s) ⊆ _
    rwa [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι, Set.singleton_subset_iff]
  let l : (𝒯).obj (integerSiteObject B hZ (B.residueField_spec_contains X.base.left.property s)) ⟶
      (S₁ : Scheme.{u}) := IsOpenImmersion.lift S₁.ι ((𝒯).map r) hrange
  have hl : l ≫ S₁.ι = (𝒯).map r := IsOpenImmersion.lift_fac S₁.ι ((𝒯).map r) hrange
  let r' : integerSiteObject B hZ (B.residueField_spec_contains X.base.left.property s) ⟶ U₁ :=
    Over.homMk (⟨l⟩ :
        B.obj (B.residueField_spec_contains X.base.left.property s) ⟶ U₁.left) (by
      apply ObjectProperty.hom_ext
      exact specULiftZIsTerminal.hom_ext _ _)
  have hr' : r' ≫ ι₁ = r := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hl
  let j₁ : yoneda.obj V ⟶ X₁ := pullback.lift j (yoneda.map (v ≫ r')) (by
    rw [Functor.map_comp, Category.assoc, ← Functor.map_comp, hr']
    exact hsq'.w)
  let p := Space.pointsMap B integerBase hZ _ j₁ (Space.presheafPoint B integerBase hZ V x
    (B.residueField_spec_contains V.left.property x))
  obtain ⟨E, hEaff, -, -⟩ :=
    Space.exists_affine_elementaryEtaleNeighborhood' B integerBase hZ hX₁ hdec p
  have hι₁et : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf (yoneda.map ι₁) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B integerBase hZ _ ι₁).2
      (inferInstance : Etale S₁.ι)
  have := MorphismProperty.relative_isStableUnderBaseChange
    (P := MorphismProperty.inverseImage @Etale (𝒯)) (F := yoneda)
  have hfst : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf
      (pullback.fst fX (yoneda.map ι₁)) :=
    MorphismProperty.of_isPullback sq₁.flip hι₁et
  let e := E.toSpace ≫ pullback.fst fX (yoneda.map ι₁)
  have he : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf e :=
    MorphismProperty.comp_mem _ _ _ (Space.ElementaryEtaleNeighborhood.presheaf_etale_toSpace
      B integerBase hZ hX₁ E) hfst
  have hmono : Mono (yoneda.map (Space.residueFieldMap B integerBase hZ E.scheme E.point
      E.residueField_contained) ≫ e) := by
    have := E.mono_residueField
    have : Mono (yoneda.map ι₁) := mono_yoneda_map_of_mono_map ι₁ (inferInstance : Mono S₁.ι)
    have : Mono (pullback.fst fX (yoneda.map ι₁)) := inferInstance
    rw [← Category.assoc]
    exact mono_comp _ _
  refine ⟨E.scheme, e, E.point, E.residueField_contained,
    Yoneda.fullyFaithful.preimage (e ≫ fX), he, hmono,
    (Yoneda.fullyFaithful.map_preimage _).symm, hEaff, ?_⟩
  simp only [e, Space.pointsMap_comp, Function.comp_apply, E.map_point, p]
  rw [← Function.comp_apply (f := Space.pointsMap B integerBase hZ _ _), ← Space.pointsMap_comp]
  simp only [j₁, pullback.lift_fst]

/-- A cartesian square over the residue-field point at `s` is one over the residue-field point at
any point equal to `s`. -/
theorem exists_isPullback_fromSpecResidueField_of_eq {P W S : Scheme.{u}} {a : P ⟶ W}
    {g : W ⟶ S} {s : S} {b : P ⟶ Spec (S.residueField s)}
    (sq : IsPullback a b g (S.fromSpecResidueField s)) {s' : S} (h : s = s') :
    ∃ b' : P ⟶ Spec (S.residueField s'), IsPullback a b' g (S.fromSpecResidueField s') := by
  subst h; exact ⟨b, sq⟩

open Stacks.Divisors in
/-- **The chart divisor at a point of the fibre.** Let `V` present the fibre of a family of curves
`X ⟶ S` over `Spec κ(s)`, `f` a nonzerodivisor on an affine open `A` of `V` vanishing at `x` with
zero locus `{x}` near `x`, and `(W, w)` an affine étale chart of `X` at the image of `x`, with
`gW : W ⟶ S`. Then there is a closed subscheme `Z ⊆ W` through `w`, principal near `w`, whose
fibre over `s` is an effective Cartier divisor near `w`, quasi-finite over `S` at its point over
`w`. -/
theorem exists_chartDivisor_of_fibre_equation (X : CurveFamily B hZ) (s : (𝒯).obj X.base)
    {V : BigFppfOver B integerBase hZ}
    (v : V ⟶ integerSiteObject B hZ (B.residueField_spec_contains X.base.left.property s))
    (j : yoneda.obj V ⟶ X.total.obj)
    (hsq : IsPullback j (yoneda.map v) X.toBase.hom (yoneda.map (residueFieldIntegerMap X s)))
    {A : ((𝒯).obj V).Opens} (hA : IsAffineOpen A) (f : Γ((𝒯).obj V, A)) (hf : _root_.IsRegular f)
    {x : (𝒯).obj V} (hxA : x ∈ A) (hx : x ∉ ((𝒯).obj V).basicOpen f) (O : ((𝒯).obj V).Opens)
    (hxO : x ∈ O) (hiso : ∀ y ∈ O, y ∈ A → y ∉ ((𝒯).obj V).basicOpen f → y = x)
    {W : BigFppfOver B integerBase hZ} (e : yoneda.obj W ⟶ X.total.obj) (w : W.left.1)
    (hw : B.Contains (Spec (.of (W.left.1.residueField w)))) (gW : W ⟶ X.base)
    (he : (MorphismProperty.inverseImage @Etale (𝒯)).presheaf e)
    (hgW : e ≫ X.toBase.hom = yoneda.map gW) [IsAffine ((𝒯).obj W)]
    [LocallyOfFiniteType ((𝒯).map gW)]
    (hpt : Space.pointsMap B integerBase hZ _ e (Space.presheafPoint B integerBase hZ W w hw) =
      Space.pointsMap B integerBase hZ _ j (Space.presheafPoint B integerBase hZ V x
        (B.residueField_spec_contains V.left.property x))) :
    ∃ Z : ((𝒯).obj W).IdealSheafData, w ∈ Z.support ∧
      (∃ V : ((𝒯).obj W).affineOpens, w ∈ (V : ((𝒯).obj W).Opens) ∧ (Z.ideal V).IsPrincipal) ∧
      (∃ V : (((𝒯).map gW).fiber ((𝒯).map gW w)).Opens, ((𝒯).map gW).asFiber w ∈ V ∧
        IsEffectiveCartierDivisor ((Z.comap (((𝒯).map gW).fiberι ((𝒯).map gW w))).comap V.ι)) ∧
      ∃ z : Z.subscheme, Z.subschemeι z = w ∧ (Z.subschemeι ≫ (𝒯).map gW).QuasiFiniteAt z := by
  let fX : X.total.obj ⟶ yoneda.obj X.base := X.toBase.hom
  let r := residueFieldIntegerMap X s
  have hsq' : IsPullback j (yoneda.map v) fX (yoneda.map r) := hsq
  have hgW' : e ≫ fX = yoneda.map gW := hgW
  let rel := he.rep
  let W' := rel.pullback j
  let fst' : W' ⟶ W := rel.fst' j
  let snd : W' ⟶ V := rel.snd j
  have sqWV : IsPullback (yoneda.map fst') (yoneda.map snd) e j := rel.isPullback' j
  have hsnd : Etale ((𝒯).map snd) := he.property_snd j
  have sq2 :
      IsPullback (yoneda.map fst') (yoneda.map (snd ≫ v)) (yoneda.map gW) (yoneda.map r) := by
    have := sqWV.paste_vert hsq'
    rwa [← Functor.map_comp, hgW'] at this
  have sq3 : IsPullback fst' (snd ≫ v) gW r :=
    IsPullback.of_map yoneda (Yoneda.fullyFaithful.map_injective (by
      simpa only [Functor.map_comp] using sq2.w)) sq2
  have sq4 : IsPullback ((𝒯).map fst') ((𝒯).map (snd ≫ v)) ((𝒯).map gW)
      (((𝒯).obj X.base).fromSpecResidueField s) := sq3.map (𝒯)
  have hpp : ∀ {T : BigFppfOver B integerBase hZ} (t t' : (𝒯).obj T),
      Space.presheafPoint B integerBase hZ T t (B.residueField_spec_contains T.left.property t) =
        Space.presheafPoint B integerBase hZ T t' (B.residueField_spec_contains T.left.property t')
        → t = t' := fun t t' h => by
    have := congrArg (Space.pointsToScheme B integerBase hZ _) h
    rwa [Space.pointsToScheme_presheafPoint, Space.pointsToScheme_presheafPoint] at this
  have hws : (𝒯).map gW w = s := by
    apply hpp
    have h1 := Space.pointsMap_presheafPoint B integerBase hZ W X.base gW w hw
      (B.residueField_spec_contains X.base.left.property _)
    have h2 := Space.pointsMap_presheafPoint B integerBase hZ V X.base (v ≫ r) x
      (B.residueField_spec_contains V.left.property x)
      (B.residueField_spec_contains X.base.left.property _)
    have hr : (𝒯).map (v ≫ r) x = s := by
      rw [Functor.map_comp, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    rw [← hgW', Space.pointsMap_comp, Function.comp_apply, hpt, ← Function.comp_apply
      (f := Space.pointsMap B integerBase hZ _ fX), ← Space.pointsMap_comp, hsq'.w,
      ← Functor.map_comp] at h1
    exact h1.symm.trans (h2.trans (by rw [show (v ≫ r).left.hom x = s from hr]))
  obtain ⟨b', sq5⟩ := exists_isPullback_fromSpecResidueField_of_eq sq4 hws.symm
  let Ψ : ((𝒯).map gW).fiber ((𝒯).map gW w) ⟶ (𝒯).obj W' := sq5.isoPullback.inv
  have : IsIso Ψ := inferInstanceAs (IsIso sq5.isoPullback.inv)
  have hΦ : Ψ ≫ (𝒯).map fst' = ((𝒯).map gW).fiberι ((𝒯).map gW w) :=
    sq5.isoPullback_inv_fst
  let h : ((𝒯).map gW).fiber ((𝒯).map gW w) ⟶ (𝒯).obj V := Ψ ≫ (𝒯).map snd
  have : Etale h := inferInstanceAs (Etale (Ψ ≫ (𝒯).map snd))
  have hjmono : Mono j := by
    have := mono_yoneda_map_of_mono_map r
      (inferInstance : Mono (((𝒯).obj X.base).fromSpecResidueField s))
    exact hsq'.mono_fst_of_mono
  have hhx : h (((𝒯).map gW).asFiber w) = x := by
    have hy' : (𝒯).map fst' (Ψ (((𝒯).map gW).asFiber w)) = w := by
      rw [← Scheme.Hom.comp_apply, hΦ, Scheme.Hom.fiberι_asFiber]
    apply hpp
    apply Space.pointsMap_injective_of_mono B integerBase hZ j
    have e1 := Space.pointsMap_presheafPoint B integerBase hZ W' V snd
      (Ψ (((𝒯).map gW).asFiber w)) (B.residueField_spec_contains W'.left.property _)
      (B.residueField_spec_contains V.left.property _)
    have e2 := Space.pointsMap_presheafPoint B integerBase hZ W' W fst'
      (Ψ (((𝒯).map gW).asFiber w)) (B.residueField_spec_contains W'.left.property _)
      (B.residueField_spec_contains W.left.property _)
    calc _ = Space.pointsMap B integerBase hZ _ j (Space.pointsMap B integerBase hZ _
          (yoneda.map snd) (Space.presheafPoint B integerBase hZ W'
            (Ψ (((𝒯).map gW).asFiber w)) (B.residueField_spec_contains W'.left.property _))) := by
          rw [e1]; rfl
      _ = Space.pointsMap B integerBase hZ _ e (Space.pointsMap B integerBase hZ _
          (yoneda.map fst') (Space.presheafPoint B integerBase hZ W'
            (Ψ (((𝒯).map gW).asFiber w)) (B.residueField_spec_contains W'.left.property _))) := by
          rw [← Function.comp_apply (f := Space.pointsMap B integerBase hZ _ j),
            ← Space.pointsMap_comp, ← sqWV.w, Space.pointsMap_comp, Function.comp_apply]
      _ = _ := by
          have hy'' : fst'.left.hom (Ψ (((𝒯).map gW).asFiber w)) = w := hy'
          rw [e2]; simp only [hy'']; exact hpt
  obtain ⟨N, hN, b, hyN, hb, hyb, O', hyO', hiso'⟩ :=
    exists_isRegular_isolated_of_flat_of_locallyQuasiFinite h hA f hf hxA hx O hxO hiso _ hhx
  exact exists_idealSheafData_quasiFiniteAt_of_fibre_equation ((𝒯).map gW) w hN b hyN hb hyb O'
    hyO' hiso'

end AlgebraicGeometry.CurveFamily

end
