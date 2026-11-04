module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyDivisorLift
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreDivisorFiniteLift
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafComapMap
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyChartDivisorDescends
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallySeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.RepresentableFibreProduct
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PresheafPointTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyContractionUniqueness
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback

/-!
# Lifting a divisor of a closed fibre supported in one point (towards Stacks 0E6F)

Let `X ⟶ S` be a family of curves over an affine scheme, `s ∈ S` a closed point with fibre `V`,
and `E ⊆ V` an effective Cartier divisor supported in at most one point `x`. Then over an
elementary étale neighbourhood of `s` there is a relative effective Cartier divisor of the base
changed family whose preimage in the fibre is `E`. This is
`AlgebraicGeometry.C1590Private.DivisorLiftAtClosedFibreLocal`.

## Main results

* `AlgebraicGeometry.C1590Private.divisorLiftAtClosedFibreLocal`: the one-point divisor lift.
* `AlgebraicGeometry.C1590Private.exists_chartDivisorDescends_input`: the front half, producing
  the input of `AlgebraicGeometry.C1590Private.chartDivisorDescends`.
* `AlgebraicGeometry.exists_residueField_iso_of_isClosedImmersion` and
  `AlgebraicGeometry.isIso_of_etale_of_bijective_of_isIso_residueFieldMap`: scheme-level inputs.

## Proof

Choose an affine elementary étale neighbourhood `N ⟶ X` of the image of `x` (Stacks 0BBP). The
fibre of `N` over `s` is `N ×_X V`; the closed subscheme `Z ⊆ N` cut out by the preimage of `E` in
it satisfies the hypotheses of
`AlgebraicGeometry.C1590Private.exists_elementary_finite_relativeEffectiveCartier`, which gives an
elementary étale neighbourhood `U` of `s` and a finite relative effective Cartier divisor `D` on
an open of `N ×_S U`. The morphism from `D` to the base change `X_U` is a closed immersion over the
fibre, hence over an open neighbourhood of the closed point (Stacks 05XA); its image is the lift.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 05XA](https://stacks.math.columbia.edu/tag/05XA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- **A closed immersion from the spectrum of a field is the residue field of its image.** If
`j : Spec K ⟶ S` is a closed immersion, the induced map from the residue field of its image point
to `K` is an isomorphism, through which `j` is `S.fromSpecResidueField`. -/
theorem exists_residueField_iso_of_isClosedImmersion {S : Scheme.{u}} {K : Type u} [Field K]
    (j : Spec (.of K) ⟶ S) [IsClosedImmersion j] :
    ∃ (y : S) (e : S.residueField y ≅ CommRingCat.of K), (∀ p, j p = y) ∧
      j = Spec.map e.hom ≫ S.fromSpecResidueField y := by
  set r := S.descResidueField (Scheme.stalkClosedPointTo j) with hr
  have hj : j = Spec.map r ≫ S.fromSpecResidueField _ :=
    ((Scheme.SpecToEquivOfField K S).left_inv j).symm
  have hsurj : Function.Surjective r := by
    have h1 : Function.Surjective (Scheme.stalkClosedPointTo j) := by
      have := j.stalkMap_surjective (IsLocalRing.closedPoint K)
      exact (ConcreteCategory.bijective_of_isIso
        (stalkClosedPointIso (CommRingCat.of K)).hom).2.comp this
    intro y
    obtain ⟨z, hz⟩ := h1 y
    refine ⟨S.residue _ z, ?_⟩
    rw [← hz, hr, ← CommRingCat.comp_apply, Scheme.residue_descResidueField]
  have hbij : Function.Bijective r := ⟨r.hom.injective, hsurj⟩
  refine ⟨_, (RingEquiv.ofBijective r.hom hbij).toCommRingCatIso, fun p => ?_, hj⟩
  congr 1
  exact Subsingleton.elim _ _

/-- **An étale morphism which is bijective with trivial residue field extensions is an
isomorphism.** It is universally injective (Stacks 01S4), hence an open immersion (Stacks 025G),
and surjective. -/
theorem isIso_of_etale_of_bijective_of_isIso_residueFieldMap {A B : Scheme.{u}} (f : A ⟶ B)
    [Etale f] (hbij : Function.Bijective f) (hres : ∀ a, IsIso (f.residueFieldMap a)) :
    IsIso f := by
  have hui : UniversallyInjective f := by
    have key : UniversallyInjective f ↔ (Function.Injective f ∧
        ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable) :=
      (tfae_universallyInjective (f := f)).out 1 3
    refine key.2 ⟨hbij.1, fun a => ?_⟩
    have hb := (ConcreteCategory.bijective_of_isIso (f.residueFieldMap a))
    algebraize [(f.residueFieldMap a).hom]
    exact ⟨⟨fun x => by
      obtain ⟨y, rfl⟩ := hb.2 x
      exact isIntegral_algebraMap⟩, fun x _ => hb.2 x⟩
  have := isOpenImmersion_of_etale_universallyInjective f
  have : Surjective f := ⟨hbij.2⟩
  exact (isIso_iff_isOpenImmersion_and_surjective f).2 ⟨inferInstance, inferInstance⟩

/-- **A point of a locally quasi-finite scheme over a closed point is closed.** -/
theorem isClosed_singleton_of_locallyQuasiFinite {U S : Scheme.{u}} (f : U ⟶ S)
    [LocallyQuasiFinite f] (x : U) (hs : IsClosed ({f x} : Set S)) : IsClosed ({x} : Set U) := by
  have hd := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have hc : IsClosed (f ⁻¹' {f x}) := hs.preimage f.continuous
  have himg := hc.isClosedEmbedding_subtypeVal.isClosedMap
    ({⟨x, rfl⟩} : Set (f ⁻¹' {f x})) (isClosed_discrete _)
  simpa using himg

namespace C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **An affine elementary étale chart of the total space of a family of curves over an affine
base** (Stacks 0BBP), with the scheme-level properties of the composite to the base: it is flat
and locally of finite presentation. The chart meets the given point only at the distinguished
point, and the residue-field point there is a monomorphism into the total space. -/
theorem exists_elementaryChart (X : CurveFamily B hZ)
    (hXaff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (ξ : Space.points B integerBase hZ X.total.obj) :
    ∃ (N : BigFppfOver B integerBase hZ) (c : yoneda.obj N ⟶ X.total.obj) (π' : N ⟶ X.base)
      (w : N.left.1) (hw : B.Contains (Spec (.of (N.left.1.residueField w)))),
      Space.IsEtale B integerBase hZ c ∧ yoneda.map π' = c ≫ X.toBase.hom ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj N) ∧
      Flat ((BigFppfOver.toScheme B integerBase hZ).map π') ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map π') ∧
      Space.pointsMap B integerBase hZ (yoneda.obj N) c
        (Space.presheafPoint B integerBase hZ N w hw) = ξ ∧
      (∀ y : Space.points B integerBase hZ (yoneda.obj N),
        Space.pointsMap B integerBase hZ (yoneda.obj N) c y = ξ →
          y = Space.presheafPoint B integerBase hZ N w hw) ∧
      Mono (yoneda.map (Space.residueFieldMap B integerBase hZ N w hw) ≫ c) := by
  have hsep := Space.isAbsolutelySeparated_of_isSeparated_to_affine B integerBase hZ
    B.contains_terminal X.base hXaff X.toBase.hom X.proper.1
  have hdec := Space.isDecentSpace_of_isAbsolutelyLocallySeparated B integerBase hZ
    B.contains_terminal X.total.property
    (Space.isAbsolutelyLocallySeparated_of_isAbsolutelySeparated B integerBase hZ
      B.contains_terminal _ hsep)
  obtain ⟨E₀, hNaff, huniq, -⟩ :=
    Space.exists_affine_elementaryEtaleNeighborhood' B integerBase hZ X.total.property hdec ξ
  have hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B integerBase hZ)).presheaf E₀.toSpace :=
    (Space.isEtale_iff_presheaf_of_yoneda B integerBase hZ E₀.toSpace).1 E₀.etale_toSpace
  let π' : E₀.scheme ⟶ X.base := yoneda.preimage (E₀.toSpace ≫ X.toBase.hom)
  have hπ' : yoneda.map π' = E₀.toSpace ≫ X.toBase.hom := yoneda.map_preimage _
  have hid := (Space.idEtaleChart B integerBase hZ X.base).2
  refine ⟨E₀.scheme, E₀.toSpace, π', E₀.point, E₀.residueField_contained, E₀.etale_toSpace, hπ',
    hNaff, X.flat _ _ _ _ π' hc hid ((Category.comp_id _).trans hπ'),
    X.finitePresentation.1 _ _ _ _ π' hc hid ((Category.comp_id _).trans hπ'), E₀.map_point,
    fun y hy => huniq y hy, E₀.mono_residueField⟩

/-- Two charts over the total space of a family of curves have a representable fibre product. -/
private theorem exists_isPullback_yoneda_map (X : CurveFamily B hZ)
    {N V : BigFppfOver B integerBase hZ} (c : yoneda.obj N ⟶ X.total.obj)
    (q : yoneda.obj V ⟶ X.total.obj) :
    ∃ (G : BigFppfOver B integerBase hZ) (gN : G ⟶ N) (gV : G ⟶ V),
      IsPullback (yoneda.map gN) (yoneda.map gV) c q := by
  have := Space.isRepresentable_pullback_yoneda B integerBase hZ X.total.property c q
  let e := (pullback c q).reprW
  refine ⟨_, yoneda.preimage (e.hom ≫ pullback.fst c q), yoneda.preimage (e.hom ≫ pullback.snd c q),
    IsPullback.of_iso_pullback ⟨?_⟩ e (by simp) (by simp)⟩
  simp only [Functor.map_preimage, Category.assoc, pullback.condition]

/-- The base change of an étale chart along a chart is étale as a morphism of schemes. -/
private theorem etale_map_of_isPullback_yoneda_map (X : CurveFamily B hZ)
    {N V G : BigFppfOver B integerBase hZ} {c : yoneda.obj N ⟶ X.total.obj}
    {q : yoneda.obj V ⟶ X.total.obj} {gN : G ⟶ N} {gV : G ⟶ V}
    (hpb : IsPullback (yoneda.map gN) (yoneda.map gV) c q) (hc : Space.IsEtale B integerBase hZ c) :
    Etale ((BigFppfOver.toScheme B integerBase hZ).map gV) :=
  (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B integerBase hZ @Etale gV).1
    ((Space.isEtale_iff_presheaf_of_yoneda B integerBase hZ _).1
      (Space.isEtale_of_isPullback_yoneda B integerBase hZ hpb hc))

/-- **The fibre of an étale chart over a closed fibre.** For an étale chart `c : N ⟶ X` of the
total space and the fibre `q : V ⟶ X` over a field-valued point `P` of the base, the fibre product
`N ×_X V` is a scheme `G₀` of the site; `G₀ ⟶ N` is a closed immersion when `P` is, `G₀ ⟶ V` is
étale, and `G₀ = N ×_S Spec K` as schemes. -/
theorem exists_fibreChart (X : CurveFamily B hZ)
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (hP : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    {N : BigFppfOver B integerBase hZ} (c : yoneda.obj N ⟶ X.total.obj) (π' : N ⟶ X.base)
    (hc : Space.IsEtale B integerBase hZ c) (hπ' : yoneda.map π' = c ≫ X.toBase.hom) :
    ∃ (G₀ : BigFppfOver B integerBase hZ) (gN : G₀ ⟶ N) (gV : G₀ ⟶ V),
      IsPullback (yoneda.map gN) (yoneda.map gV) c q ∧
      IsPullback ((BigFppfOver.toScheme B integerBase hZ).map gN)
        ((BigFppfOver.toScheme B integerBase hZ).map (gV ≫ v))
        ((BigFppfOver.toScheme B integerBase hZ).map π')
        ((BigFppfOver.toScheme B integerBase hZ).map P.value) ∧
      IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map gN) ∧
      Etale ((BigFppfOver.toScheme B integerBase hZ).map gV) := by
  obtain ⟨G₀, gN, gV, hpb⟩ := exists_isPullback_yoneda_map X c q
  let pv : P.siteObject ⟶ X.base := P.value
  have hPv : yonedaEquiv.symm P.value = yoneda.map pv := yonedaEquiv_symm_value P
  have hpb₂ : IsPullback (yoneda.map gN) (yoneda.map (gV ≫ v)) (yoneda.map π')
      (yoneda.map pv) := by
    rw [hπ', yoneda.map_comp, ← hPv]
    exact hpb.paste_vert hV
  have hw : gN ≫ π' = (gV ≫ v) ≫ pv := yoneda.map_injective (by
    simp only [Functor.map_comp]
    simpa only [Functor.map_comp, Category.assoc] using hpb₂.w)
  have hsite : IsPullback gN (gV ≫ v) π' pv := IsPullback.of_map yoneda hw hpb₂
  have hT := hsite.map (BigFppfOver.toScheme B integerBase hZ)
  exact ⟨_, gN, gV, hpb, hT, MorphismProperty.of_isPullback hT.flip hP,
    etale_map_of_isPullback_yoneda_map X hpb hc⟩

/-- **The point of the fibre chart over the support of the divisor.** Let `c : N ⟶ X` be an étale
chart whose residue-field point at `w` is a monomorphism into `X` and which meets the image of
`x ∈ V` only at `w`. Then `G₀ = N ×_X V` has a point `g₀` over `(w, x)`, it is the only point over
`x`, and `G₀ ⟶ V` induces an isomorphism of residue fields at `g₀`. -/
theorem exists_fibreChart_point (X : CurveFamily B hZ) {V N G₀ : BigFppfOver B integerBase hZ}
    (q : yoneda.obj V ⟶ X.total.obj) (c : yoneda.obj N ⟶ X.total.obj) (gN : G₀ ⟶ N)
    (gV : G₀ ⟶ V) (hpb : IsPullback (yoneda.map gN) (yoneda.map gV) c q)
    (hgN : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map gN))
    (x : V.left.1) (hx : B.Contains (Spec (.of (V.left.1.residueField x))))
    (w : N.left.1) (hw : B.Contains (Spec (.of (N.left.1.residueField w))))
    (hpt : Space.pointsMap B integerBase hZ (yoneda.obj N) c
      (Space.presheafPoint B integerBase hZ N w hw) =
      Space.pointsMap B integerBase hZ (yoneda.obj V) q
        (Space.presheafPoint B integerBase hZ V x hx))
    (huniq : ∀ y : Space.points B integerBase hZ (yoneda.obj N),
      Space.pointsMap B integerBase hZ (yoneda.obj N) c y =
        Space.pointsMap B integerBase hZ (yoneda.obj V) q
          (Space.presheafPoint B integerBase hZ V x hx) →
        y = Space.presheafPoint B integerBase hZ N w hw)
    (hmono : Mono (yoneda.map (Space.residueFieldMap B integerBase hZ N w hw) ≫ c)) :
    ∃ g₀ : (BigFppfOver.toScheme B integerBase hZ).obj G₀,
      (BigFppfOver.toScheme B integerBase hZ).map gN g₀ = w ∧
      (BigFppfOver.toScheme B integerBase hZ).map gV g₀ = x ∧
      IsIso (((BigFppfOver.toScheme B integerBase hZ).map gV).residueFieldMap g₀) ∧
      ∀ g, (BigFppfOver.toScheme B integerBase hZ).map gV g = x → g = g₀ := by
  set T := BigFppfOver.toScheme B integerBase hZ
  -- the two residue-field points of `ξ`
  let pw : Space.FieldValuedPoint B integerBase hZ X.total.obj :=
    ⟨N.left.1.residueField w, hw, N.left.1.fromSpecResidueField w ≫ N.hom.1,
      c.app _ (Space.residueFieldMap B integerBase hZ N w hw)⟩
  let px : Space.FieldValuedPoint B integerBase hZ X.total.obj :=
    ⟨V.left.1.residueField x, hx, V.left.1.fromSpecResidueField x ≫ V.hom.1,
      q.app _ (Space.residueFieldMap B integerBase hZ V x hx)⟩
  let rW : pw.siteObject ⟶ N := Space.residueFieldMap B integerBase hZ N w hw
  let rX : px.siteObject ⟶ V := Space.residueFieldMap B integerBase hZ V x hx
  have hsymm : ∀ {M : BigFppfOver B integerBase hZ} (d : yoneda.obj M ⟶ X.total.obj) (A : _)
      (r : A ⟶ M), yonedaEquiv.symm (d.app _ r) = yoneda.map r ≫ d := fun d A r => by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  have hpw : yonedaEquiv.symm pw.value = yoneda.map rW ≫ c := hsymm c _ _
  have hpx : yonedaEquiv.symm px.value = yoneda.map rX ≫ q := hsymm q _ _
  have : Mono (yonedaEquiv.symm pw.value) := by rw [hpw]; exact hmono
  obtain ⟨f, hf, -⟩ := Space.FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B integerBase
    hZ X.total.obj X.total.property pw px hpt
  have hf' : yoneda.map f ≫ yoneda.map rW ≫ c = yoneda.map rX ≫ q := by
    rw [← hpw, ← hpx, ← hf, yonedaEquiv_symm_naturality_left]
  -- the lift to `G₀`
  let ℓ := hpb.lift (yoneda.map (f ≫ rW)) (yoneda.map rX)
    (by rw [Functor.map_comp, Category.assoc, hf'])
  let ℓ' := yoneda.preimage ℓ
  have hℓV : ℓ' ≫ gV = rX := yoneda.map_injective (by simp [ℓ', ℓ])
  have hℓN : ℓ' ≫ gN = f ≫ rW := yoneda.map_injective (by simp [ℓ', ℓ])
  let pt : T.obj px.siteObject := IsLocalRing.closedPoint (V.left.1.residueField x)
  set g₀ := T.map ℓ' pt with hg₀
  have hg₀V : T.map gV g₀ = x := by
    rw [hg₀, ← Scheme.Hom.comp_apply, ← T.map_comp, hℓV]
    exact Scheme.fromSpecResidueField_apply x _
  have hg₀N : T.map gN g₀ = w := by
    rw [hg₀, ← Scheme.Hom.comp_apply, ← T.map_comp, hℓN, T.map_comp, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply w _
  -- every point of `G₀` over `x` lies over `w`
  have hover : ∀ g, T.map gV g = x → T.map gN g = w := by
    intro g hg
    have hg' : B.Contains (Spec (.of ((T.obj G₀).residueField g))) :=
      B.residueField_spec_contains G₀.left.2 g
    have h1 := Space.pointsMap_presheafPoint B integerBase hZ G₀ N gN g hg'
      (B.residueField_spec_contains N.left.2 _)
    have h2 := Space.pointsMap_presheafPoint B integerBase hZ G₀ V gV g hg'
      (B.residueField_spec_contains V.left.2 _)
    have hcomm := congrFun (congrArg (Space.pointsMap B integerBase hZ (yoneda.obj G₀)) hpb.w)
      (Space.presheafPoint B integerBase hZ G₀ g hg')
    simp only [Space.pointsMap_comp, Function.comp_apply, h1, h2] at hcomm
    have hgV : gV.left.1 g = x := hg
    have hcongr : ∀ (y : V.left.1) (hy : B.Contains (Spec (.of (V.left.1.residueField y)))),
        y = x → Space.presheafPoint B integerBase hZ V y hy =
          Space.presheafPoint B integerBase hZ V x hx := by
      rintro y _ rfl; rfl
    have h3 := huniq _ (by rw [hcomm, hcongr _ _ hgV])
    have := congrArg (Space.pointsToScheme B integerBase hZ N) h3
    simp only [Space.pointsToScheme_presheafPoint] at this
    exact this
  refine ⟨g₀, hg₀N, hg₀V, ?_, fun g hg => ?_⟩
  · have hcomp : IsIso ((T.map ℓ' ≫ T.map gV).residueFieldMap pt) := by
      rw [← T.map_comp, hℓV]
      exact isIso_residueFieldMap_fromSpecResidueField _ _ _
    rw [Scheme.residueFieldMap_comp] at hcomp
    have hbij := (ConcreteCategory.isIso_iff_bijective _).1 hcomp
    have hbinj : Function.Injective ((T.map ℓ').residueFieldMap pt) := RingHom.injective _
    change IsIso ((T.map gV).residueFieldMap (T.map ℓ' pt))
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨RingHom.injective _, fun z => ?_⟩
    obtain ⟨y, hy⟩ := hbij.2 ((T.map ℓ').residueFieldMap pt z)
    refine ⟨y, hbinj ?_⟩
    rw [← hy]
    rfl
  · exact hgN.isClosedEmbedding.injective ((hover g hg).trans (hg₀N.symm.trans rfl))

/-- **The pushed-forward divisor satisfies the hypotheses of the finite lift.** Let `π : N ⟶ S`
be flat and locally of finite presentation, `j : Spec K ⟶ S` a closed immersion, and
`G₀ = N ×_S Spec K` with `gN : G₀ ⟶ N` (a closed immersion) and `gV : G₀ ⟶ V` étale. Let `E ⊆ V`
be an effective Cartier divisor supported at `x`, and `g₀` the only point of `G₀` over `x`, lying
over `w`. Then `Z = (E ×_V G₀)` read in `N` contains `w`, has an effective Cartier fibre over
`π w`, has `w` as its only point, and is cut out on `G₀` by the preimage of `E`. -/
theorem fibreDivisor_hypotheses {N G₀ V S : Scheme.{u}} (π : N ⟶ S) [Flat π]
    (gN : G₀ ⟶ N) [IsClosedImmersion gN] (gV : G₀ ⟶ V) [Etale gV] {K : Type u} [Field K]
    (j : Spec (.of K) ⟶ S) [IsClosedImmersion j] (vK : V ⟶ Spec (.of K))
    (hT : IsPullback gN (gV ≫ vK) π j) (E : V.IdealSheafData)
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E) (x : V) (hx : (E.support : Set V) = {x})
    (w : N) (g₀ : G₀) (hg₀N : gN g₀ = w) (hg₀V : gV g₀ = x) (huniq : ∀ g, gV g = x → g = g₀) :
    ((E.comap gV).map gN).comap gN = E.comap gV ∧ w ∈ ((E.comap gV).map gN).support ∧
      (∃ O : (π.fiber (π w)).Opens, π.asFiber w ∈ O ∧ Stacks.Divisors.IsEffectiveCartierDivisor
        ((((E.comap gV).map gN).comap (π.fiberι (π w))).comap O.ι)) ∧
      ∃ O₀ : N.Opens, w ∈ O₀ ∧ ∀ y ∈ O₀, y ∈ ((E.comap gV).map gN).support → π y = π w →
        y = w := by
  set Z := (E.comap gV).map gN with hZdef
  have hZc : Z.comap gN = E.comap gV := Scheme.IdealSheafData.comap_map_of_isClosedImmersion _ _
  have hsupp : (Z.support : Set N) = gN '' ((E.comap gV).support : Set G₀) := by
    rw [hZdef, Scheme.IdealSheafData.support_map, TopologicalSpace.Closeds.coe_closure]
    exact (gN.isClosedEmbedding.isClosedMap _ (E.comap gV).support.isClosed).closure_eq
  have hmem : ∀ y, y ∈ Z.support ↔ y = w := by
    intro y
    change y ∈ (Z.support : Set N) ↔ _
    rw [hsupp]
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hg' : gV g ∈ (E.support : Set V) := by
        simpa [Scheme.IdealSheafData.support_comap] using hg
      rw [hx] at hg'
      rw [huniq g hg', hg₀N]
    · rintro rfl
      refine ⟨g₀, ?_, hg₀N⟩
      show g₀ ∈ ((E.comap gV).support : Set G₀)
      rw [Scheme.IdealSheafData.support_comap]
      simp only [TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage, hg₀V, hx,
        Set.mem_singleton_iff]
  refine ⟨hZc, (hmem w).2 rfl, ⟨⊤, trivial, ?_⟩, ⊤, trivial, fun y _ hy _ => (hmem y).1 hy⟩
  -- the fibre of `π` over `π w` is `G₀`
  obtain ⟨y, e, hjy, he⟩ := exists_residueField_iso_of_isClosedImmersion j
  have hs : π w = y := by
    rw [← hg₀N, ← Scheme.Hom.comp_apply, hT.w, Scheme.Hom.comp_apply, hjy]
  let θ : Spec (S.residueField (π w)) ⟶ Spec (.of K) :=
    Spec.map (S.residueFieldCongr hs).inv ≫ Spec.map e.inv
  have hej : Spec.map e.inv ≫ j = S.fromSpecResidueField y := by
    rw [he, ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  have hθ : θ ≫ j = S.fromSpecResidueField (π w) := by
    simp only [θ, Category.assoc, hej]
    exact S.residueFieldCongr_fromSpecResidueField hs.symm
  have hbig := IsPullback.of_hasPullback π (S.fromSpecResidueField (π w))
  let φ := hT.lift (π.fiberι (π w)) (π.fiberToSpecResidueField (π w) ≫ θ)
    (by rw [Category.assoc, hθ]; exact pullback.condition)
  have hφN : φ ≫ gN = π.fiberι (π w) := hT.lift_fst _ _ _
  have hφV : φ ≫ gV ≫ vK = π.fiberToSpecResidueField (π w) ≫ θ := hT.lift_snd _ _ _
  have hleft : IsPullback φ (π.fiberToSpecResidueField (π w)) (gV ≫ vK) θ :=
    IsPullback.of_right (by rwa [hφN, hθ]) hφV hT
  have : IsIso θ := by simp only [θ]; infer_instance
  have : IsIso φ := hleft.isIso_fst_of_isIso
  have heq : (Z.comap (π.fiberι (π w))).comap (⊤ : (π.fiber (π w)).Opens).ι =
      E.comap ((⊤ : (π.fiber (π w)).Opens).ι ≫ φ ≫ gV) := by
    rw [← hφN, Scheme.IdealSheafData.comap_comp, hZc, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, Category.assoc]
  rw [heq]
  exact Stacks.Divisors.isPullbackDefined_of_flat _ E hE

/-- A scheme contained in the site, read as an object of the site over `Spec ℤ`. -/
def siteObjectOf (W : Scheme.{u}) (hW : B.Contains W) : BigFppfOver B integerBase hZ :=
  Over.mk (ObjectProperty.homMk (specULiftZIsTerminal.from W) : B.obj hW ⟶ B.obj hZ)

/-- **The input of `ChartDivisorDescends` at a divisor supported in one point.** -/
theorem exists_chartDivisorDescends_input (X : CurveFamily B hZ)
    (hXaff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (hP : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (E : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData)
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E) (x : V.left.1)
    (hx : (E.support : Set ((BigFppfOver.toScheme B integerBase hZ).obj V)) = {x}) :
    ∃ (Y : CurveFamily B hZ) (φ : Y ⟶ X) (t : P.siteObject ⟶ Y.base)
      (q' : yoneda.obj V ⟶ Y.total.obj),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ∧ t ≫ φ.baseMap = P.value ∧
      IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map t) ∧
      IsPullback q' (yoneda.map v) Y.toBase.hom (yoneda.map t) ∧ q' ≫ φ.totalMap.hom = q ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Y.base) ∧
      ∃ (O : BigFppfOver B integerBase hZ) (c : yoneda.obj O ⟶ Y.total.obj) (b : O ⟶ Y.base)
        (D : ((BigFppfOver.toScheme B integerBase hZ).obj O).IdealSheafData)
        (G : BigFppfOver B integerBase hZ) (gO : G ⟶ O) (gV : G ⟶ V),
        Space.IsEtale B integerBase hZ c ∧ yoneda.map b = c ≫ Y.toBase.hom ∧
        Stacks.Divisors.IsRelativeEffectiveCartierDivisor
          ((BigFppfOver.toScheme B integerBase hZ).map b) D ∧
        IsFinite (D.subschemeι ≫ (BigFppfOver.toScheme B integerBase hZ).map b) ∧
        IsPullback (yoneda.map gO) (yoneda.map gV) c q' ∧
        D.comap ((BigFppfOver.toScheme B integerBase hZ).map gO) =
          E.comap ((BigFppfOver.toScheme B integerBase hZ).map gV) ∧
        IsClosedImmersion ((E.comap ((BigFppfOver.toScheme B integerBase hZ).map gV)).subschemeι ≫
          (BigFppfOver.toScheme B integerBase hZ).map gV) ∧
        ((E.comap ((BigFppfOver.toScheme B integerBase hZ).map gV)).subschemeι ≫
          (BigFppfOver.toScheme B integerBase hZ).map gV).ker = E := by
  have hκx : B.Contains (Spec (.of (V.left.1.residueField x))) :=
    B.residueField_spec_contains V.left.2 x
  obtain ⟨N, c, π', w, hκw, hc, hπ', hNaff, hflat, hlfp, hcw, huniqN, hmono⟩ :=
    exists_elementaryChart X hXaff (Space.pointsMap B integerBase hZ _ q
      (Space.presheafPoint B integerBase hZ V x hκx))
  obtain ⟨G₀, gN, gV, hpb, hTsq, hgN, hgV⟩ := exists_fibreChart X P hP v q hV c π' hc hπ'
  obtain ⟨g₀, hg₀N, hg₀V, hg₀res, hg₀uniq⟩ := exists_fibreChart_point X q c gN gV hpb hgN x hκx w
    hκw hcw (fun y hy => huniqN y hy) hmono
  have := hflat; have := hlfp; have := hgN; have := hgV
  obtain ⟨hZc, hwZ, hfibZ, hisolZ⟩ := fibreDivisor_hypotheses
    ((BigFppfOver.toScheme B integerBase hZ).map π')
    ((BigFppfOver.toScheme B integerBase hZ).map gN)
    ((BigFppfOver.toScheme B integerBase hZ).map gV)
    ((BigFppfOver.toScheme B integerBase hZ).map P.value)
    ((BigFppfOver.toScheme B integerBase hZ).map v) hTsq E hE x hx w g₀ hg₀N hg₀V hg₀uniq
  obtain ⟨U, hel, hUaff, O', a, b, hab, hopen, D, hrel, hfin, hfibD, ⟨d₀, hd₀u, hd₀w, hd₀res⟩,
    hDuniq⟩ := exists_elementary_finite_relativeEffectiveCartier
      ((BigFppfOver.toScheme B integerBase hZ).map π') w _ hwZ hfibZ hisolZ
  -- the neighbourhood `U` as an object of the site
  have : QuasiCompact U.toBase := by
    have := hUaff; have := hXaff; infer_instance
  have hcU : B.Contains U.scheme :=
    Space.contains_of_locallyOfFiniteType_of_quasiCompact B integerBase hZ (Y₀ := X.base) U.toBase
  let Ũ : BigFppfOver B integerBase hZ := siteObjectOf U.scheme hcU
  let φU : Ũ ⟶ X.base := homOfToScheme U.toBase
  let u₀ : (BigFppfOver.toScheme B integerBase hZ).obj Ũ := U.point
  have : Etale ((BigFppfOver.toScheme B integerBase hZ).map φU) := U.etale_toBase
  -- the base change `Y` of the family to `Ũ`
  have hfib := AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap φU)
  let Y := X.ofIsPullback B hZ φU _ _ hfib
  let φ : Y ⟶ X := X.homOfIsPullback B hZ φU _ _ hfib
  have hpres := AlgebraicSpaces.isPullback_hom B integerBase hZ hfib
  -- the residue point of `U`, lying over that of `S`
  obtain ⟨y, e, hjy, he⟩ :=
    exists_residueField_iso_of_isClosedImmersion
      ((BigFppfOver.toScheme B integerBase hZ).map P.value)
  have hs : (BigFppfOver.toScheme B integerBase hZ).map π' w = y := by
    rw [← hg₀N, ← Scheme.Hom.comp_apply, hTsq.w, Scheme.Hom.comp_apply, hjy]
  have hUu : (BigFppfOver.toScheme B integerBase hZ).map φU u₀ = y := U.map_point.trans hs
  have : IsIso (((BigFppfOver.toScheme B integerBase hZ).map φU).residueFieldMap u₀) :=
    (EtaleNeighborhood.isElementary_iff U).1 hel
  let e₁ : ((BigFppfOver.toScheme B integerBase hZ).obj Ũ).residueField u₀ ⟶
      CommRingCat.of P.carrier :=
    inv (((BigFppfOver.toScheme B integerBase hZ).map φU).residueFieldMap u₀) ≫
      (((BigFppfOver.toScheme B integerBase hZ).obj X.base).residueFieldCongr hUu).hom ≫ e.hom
  let t₀ : Spec (.of P.carrier) ⟶ (BigFppfOver.toScheme B integerBase hZ).obj Ũ :=
    Spec.map e₁ ≫ ((BigFppfOver.toScheme B integerBase hZ).obj Ũ).fromSpecResidueField u₀
  have : IsIso (Spec.map e₁) := by simp only [e₁]; infer_instance
  have ht₀ : t₀ ≫ (BigFppfOver.toScheme B integerBase hZ).map φU =
      (BigFppfOver.toScheme B integerBase hZ).map P.value := by
    simp only [t₀, Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    rw [← Category.assoc, ← Spec.map_comp]
    simp only [e₁, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc,
      Scheme.residueFieldCongr_fromSpecResidueField]
    exact he.symm
  let t : P.siteObject ⟶ Ũ := homOfToScheme t₀
  have ht : t ≫ φU = P.value := hom_ext_of_toScheme (by rwa [Functor.map_comp])
  have htci : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map t) := by
    change IsClosedImmersion t₀
    have hyc : IsClosed ({(BigFppfOver.toScheme B integerBase hZ).map φU u₀} : Set _) := by
      rw [hUu]
      have := ((BigFppfOver.toScheme B integerBase hZ).map P.value).isClosedEmbedding.isClosed_range
      convert this using 1
      ext z; simp only [Set.mem_singleton_iff, Set.mem_range]
      exact ⟨fun h => ⟨IsLocalRing.closedPoint _, (hjy _).trans h.symm⟩, fun ⟨p, hp⟩ => hp ▸ hjy p⟩
    have := isClosed_singleton_iff_isClosedImmersion.1 (isClosed_singleton_of_locallyQuasiFinite
      ((BigFppfOver.toScheme B integerBase hZ).map φU) u₀ hyc)
    exact inferInstanceAs (IsClosedImmersion (Spec.map e₁ ≫ _))
  -- the fibre of `Y` at the lifted point
  have hPv : yonedaEquiv.symm P.value = yoneda.map (P.value : P.siteObject ⟶ X.base) :=
    yonedaEquiv_symm_value P
  have hφU : (schemeSpaceMap φU).hom = yoneda.map φU := schemeSpaceMap_hom φU
  have e1 : yoneda.map t ≫ (schemeSpaceMap φU).hom = yonedaEquiv.symm P.value := by
    change yoneda.map t ≫ yoneda.map φU = _
    rw [← Functor.map_comp, ht, hPv]
  have hvt : yoneda.map (v ≫ t) ≫ (schemeSpaceMap φU).hom =
      yoneda.map v ≫ yonedaEquiv.symm P.value :=
    (congrArg (· ≫ (schemeSpaceMap φU).hom) (Functor.map_comp yoneda v t)).trans
      ((Category.assoc _ _ _).trans (congrArg (yoneda.map v ≫ ·) e1))
  let q' : yoneda.obj V ⟶ Y.total.obj :=
    pullback.lift q (yoneda.map (v ≫ t)) (hV.w.trans hvt.symm)
  have hq'fst : q' ≫ pullback.fst _ _ = q := pullback.lift_fst _ _ _
  have hq'snd : q' ≫ pullback.snd _ _ = yoneda.map (v ≫ t) := pullback.lift_snd _ _ _
  have hbig : IsPullback (q' ≫ pullback.fst X.toBase.hom (schemeSpaceMap φU).hom) (yoneda.map v)
      X.toBase.hom (yoneda.map t ≫ (schemeSpaceMap φU).hom) := by
    rw [hq'fst, e1]; exact hV
  have hq'pb : IsPullback q' (yoneda.map v) (pullback.snd X.toBase.hom (schemeSpaceMap φU).hom)
      (yoneda.map t) :=
    IsPullback.of_right hbig (hq'snd.trans (Functor.map_comp yoneda v t))
      (IsPullback.of_hasPullback _ _)
  refine ⟨Y, φ, t, q', show Etale U.toBase from inferInstance, ht, htci, hq'pb, hq'fst,
    show IsAffine U.scheme from hUaff, ?_⟩
  -- the chart `O'` as an object of the site, étale over `Y`
  have : QuasiCompact (pullback.fst ((BigFppfOver.toScheme B integerBase hZ).map π') U.toBase) :=
    inferInstance
  have hcP : B.Contains (pullback ((BigFppfOver.toScheme B integerBase hZ).map π') U.toBase) :=
    Space.contains_of_locallyOfFiniteType_of_quasiCompact B integerBase hZ (Y₀ := N)
      (pullback.fst _ _)
  have hcO : B.Contains O' := BigFppfSite.contains_of_mono B (pullback.lift a b hab) hcP
  let Õ : BigFppfOver B integerBase hZ := siteObjectOf O' hcO
  let aO : Õ ⟶ N := homOfToScheme a
  let bO : Õ ⟶ Ũ := homOfToScheme b
  have habO : aO ≫ π' = bO ≫ φU := hom_ext_of_toScheme (by
    rw [Functor.map_comp, Functor.map_comp]; exact hab)
  let PN := pullback π' φU
  have hPNsq := IsPullback.of_hasPullback π' φU
  let ι : Õ ⟶ PN := pullback.lift aO bO habO
  have hιopen : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map ι) := by
    have hTsq' := hPNsq.map (BigFppfOver.toScheme B integerBase hZ)
    have hab' : a ≫ (BigFppfOver.toScheme B integerBase hZ).map π' =
        b ≫ (BigFppfOver.toScheme B integerBase hZ).map φU := hab
    have hopen' : IsOpenImmersion (pullback.lift a b hab') := hopen
    have hfac : (BigFppfOver.toScheme B integerBase hZ).map ι ≫ hTsq'.isoPullback.hom =
        pullback.lift a b hab' := by
      apply pullback.hom_ext
      · rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Functor.map_comp, pullback.lift_fst]
        exact (pullback.lift_fst a b hab').symm
      · rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Functor.map_comp, pullback.lift_snd]
        exact (pullback.lift_snd a b hab').symm
    have h3 : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map ι ≫
        hTsq'.isoPullback.hom) := by rwa [hfac]
    have h4 : IsOpenImmersion (((BigFppfOver.toScheme B integerBase hZ).map ι ≫
        hTsq'.isoPullback.hom) ≫ hTsq'.isoPullback.inv) := inferInstance
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h4
  have hcomm : (yoneda.map (pullback.fst π' φU) ≫ c) ≫ X.toBase.hom =
      yoneda.map (pullback.snd π' φU) ≫ (schemeSpaceMap φU).hom := by
    rw [Category.assoc, ← hπ', hφU]
    exact (Functor.map_comp yoneda _ _).symm.trans
      ((congrArg yoneda.map pullback.condition).trans (Functor.map_comp yoneda _ _))
  let cP : yoneda.obj PN ⟶ Y.total.obj :=
    pullback.lift (yoneda.map (pullback.fst π' φU) ≫ c) (yoneda.map (pullback.snd π' φU)) hcomm
  have h1 : cP ≫ pullback.snd X.toBase.hom (schemeSpaceMap φU).hom =
      yoneda.map (pullback.snd π' φU) := pullback.lift_snd _ _ _
  have hs : IsPullback (cP ≫ pullback.snd X.toBase.hom (schemeSpaceMap φU).hom)
      (yoneda.map (pullback.fst π' φU)) (schemeSpaceMap φU).hom (c ≫ X.toBase.hom) := by
    rw [h1, ← hπ']
    exact (hPNsq.map yoneda).flip
  have hcPsq : IsPullback cP (yoneda.map (pullback.fst π' φU))
      (pullback.fst X.toBase.hom (schemeSpaceMap φU).hom) c :=
    IsPullback.of_right hs (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback X.toBase.hom (schemeSpaceMap φU).hom).flip
  have hcPet : Space.IsEtale B integerBase hZ cP :=
    Space.isEtale_of_isPullback_yoneda B integerBase hZ hcPsq.flip hc
  let c' : yoneda.obj Õ ⟶ Y.total.obj := yoneda.map ι ≫ cP
  have hc'et : Space.IsEtale B integerBase hZ c' :=
    Space.isEtale_yoneda_map_comp B integerBase hZ cP ι inferInstance hcPet
  have hc'snd : c' ≫ pullback.snd X.toBase.hom (schemeSpaceMap φU).hom = yoneda.map bO :=
    ((Category.assoc _ _ _).trans (congrArg (yoneda.map ι ≫ ·) h1)).trans
      ((Functor.map_comp yoneda ι _).symm.trans (congrArg yoneda.map (pullback.lift_snd _ _ _)))
  have hc'fst : c' ≫ pullback.fst X.toBase.hom (schemeSpaceMap φU).hom = yoneda.map aO ≫ c :=
    ((Category.assoc _ _ _).trans (congrArg (yoneda.map ι ≫ ·) (pullback.lift_fst _ _ _))).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) ((Functor.map_comp yoneda ι _).symm.trans
        (congrArg yoneda.map (pullback.lift_fst _ _ _)))))
  -- the fibre `G = Õ ×_Y V` of the chart
  obtain ⟨G, gO, gV', hGpb⟩ := exists_isPullback_yoneda_map Y c' q'
  have hkcomm : yoneda.map (gO ≫ aO) ≫ c = yoneda.map gV' ≫ q :=
    (by rw [Functor.map_comp, Category.assoc] :
      yoneda.map (gO ≫ aO) ≫ c = yoneda.map gO ≫ (yoneda.map aO ≫ c)).trans <|
    (congrArg (yoneda.map gO ≫ ·) hc'fst.symm).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ pullback.fst X.toBase.hom (schemeSpaceMap φU).hom) hGpb.w).trans <|
    (Category.assoc _ _ _).trans (congrArg (yoneda.map gV' ≫ ·) hq'fst)
  let k : G ⟶ G₀ := yoneda.preimage (hpb.lift _ _ hkcomm)
  have hkN : k ≫ gN = gO ≫ aO := yoneda.map_injective (by simp [k])
  have hkV : k ≫ gV = gV' := yoneda.map_injective (by simp [k])
  have hGU : gO ≫ bO = gV' ≫ v ≫ t := yoneda.map_injective <|
    (Functor.map_comp yoneda gO bO).trans <| (congrArg (yoneda.map gO ≫ ·) hc'snd.symm).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ pullback.snd X.toBase.hom (schemeSpaceMap φU).hom) hGpb.w).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (yoneda.map gV' ≫ ·) hq'snd).trans <|
    (Functor.map_comp yoneda gV' (v ≫ t)).symm
  let D' : ((BigFppfOver.toScheme B integerBase hZ).obj Õ).IdealSheafData := D
  have hrel' : Stacks.Divisors.IsRelativeEffectiveCartierDivisor
      ((BigFppfOver.toScheme B integerBase hZ).map bO) D' := hrel
  have hfin' : IsFinite (D'.subschemeι ≫ (BigFppfOver.toScheme B integerBase hZ).map bO) := hfin
  have hfibD' : ((((E.comap ((BigFppfOver.toScheme B integerBase hZ).map gV)).map
      ((BigFppfOver.toScheme B integerBase hZ).map gN)).comap
        ((BigFppfOver.toScheme B integerBase hZ).map aO)).comap
          (((BigFppfOver.toScheme B integerBase hZ).map bO).fiberι u₀)) =
      D'.comap (((BigFppfOver.toScheme B integerBase hZ).map bO).fiberι u₀) := hfibD
  have hgOa : (BigFppfOver.toScheme B integerBase hZ).map gO ≫
      (BigFppfOver.toScheme B integerBase hZ).map aO =
      (BigFppfOver.toScheme B integerBase hZ).map k ≫
        (BigFppfOver.toScheme B integerBase hZ).map gN := by
    rw [← Functor.map_comp, ← hkN, Functor.map_comp]
  have hcomapEq : D'.comap ((BigFppfOver.toScheme B integerBase hZ).map gO) =
      E.comap ((BigFppfOver.toScheme B integerBase hZ).map gV') := by
    have hψcomm : (BigFppfOver.toScheme B integerBase hZ).map gO ≫
        (BigFppfOver.toScheme B integerBase hZ).map bO =
        ((BigFppfOver.toScheme B integerBase hZ).map gV' ≫
          (BigFppfOver.toScheme B integerBase hZ).map v ≫ Spec.map e₁) ≫
          ((BigFppfOver.toScheme B integerBase hZ).obj Ũ).fromSpecResidueField u₀ := by
      have h := congrArg (BigFppfOver.toScheme B integerBase hZ).map hGU
      simp only [Functor.map_comp] at h
      refine h.trans ?_
      simp only [Category.assoc]
      rfl
    let ψ : (BigFppfOver.toScheme B integerBase hZ).obj G ⟶
        ((BigFppfOver.toScheme B integerBase hZ).map bO).fiber u₀ :=
      pullback.lift _ _ hψcomm
    have hψ : ψ ≫ ((BigFppfOver.toScheme B integerBase hZ).map bO).fiberι u₀ =
        (BigFppfOver.toScheme B integerBase hZ).map gO :=
      pullback.lift_fst _ _ _
    rw [← hψ, Scheme.IdealSheafData.comap_comp, ← hfibD', ← Scheme.IdealSheafData.comap_comp, hψ,
      ← Scheme.IdealSheafData.comap_comp, hgOa, Scheme.IdealSheafData.comap_comp, hZc,
      ← Scheme.IdealSheafData.comap_comp, ← Functor.map_comp, hkV]
  -- `G` is the fibre of the chart over the lifted point
  have hGsite : IsPullback gO (gV' ≫ v) bO t := by
    have h := hGpb.paste_vert hq'pb
    rw [hc'snd, ← Functor.map_comp] at h
    exact IsPullback.of_map yoneda (yoneda.map_injective (by
      rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]; exact h.w)) h
  have hGT := hGsite.map (BigFppfOver.toScheme B integerBase hZ)
  have : Mono ((BigFppfOver.toScheme B integerBase hZ).map t) := by
    change Mono t₀
    infer_instance
  have : Mono ((BigFppfOver.toScheme B integerBase hZ).map gO) := hGT.mono_fst_of_mono
  -- the point of `D` over `u₀`
  have hpt : ∀ g, (BigFppfOver.toScheme B integerBase hZ).map (gO ≫ bO) g = u₀ := by
    intro g
    rw [hGU, Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply u₀ _
  have hDpt : ∀ g, g ∈ (E.comap ((BigFppfOver.toScheme B integerBase hZ).map gV')).support →
      (BigFppfOver.toScheme B integerBase hZ).map gO g = D.subschemeι d₀ := by
    intro g hg
    rw [← hcomapEq, Scheme.IdealSheafData.support_comap] at hg
    obtain ⟨d, hd⟩ := exists_subschemeι_eq D hg
    have hdu : b (D.subschemeι d) = U.point := by
      rw [hd]; have := hpt g; rw [Functor.map_comp, Scheme.Hom.comp_apply] at this; exact this
    rw [← hd, hDuniq d d₀ hdu hd₀u]
  have hGinj : Function.Injective ((BigFppfOver.toScheme B integerBase hZ).map gO) :=
    ((BigFppfOver.toScheme B integerBase hZ).map gO).injective
  have : Etale ((BigFppfOver.toScheme B integerBase hZ).map gV') :=
    etale_map_of_isPullback_yoneda_map Y hGpb hc'et
  set gT := (BigFppfOver.toScheme B integerBase hZ).map gV' with hgT
  let m : (E.comap gT).subscheme ⟶ E.subscheme :=
    (E.comapIso gT).hom ≫ pullback.snd gT E.subschemeι
  have hm : (E.comap gT).subschemeι ≫ gT = m ≫ E.subschemeι := by
    simp only [m, Category.assoc, ← pullback.condition,
      Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  have hEpt : ∀ p : E.subscheme, E.subschemeι p = x := by
    intro p
    have : E.subschemeι p ∈ (E.support : Set _) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨p, rfl⟩
    rw [hx] at this; exact this
  have hGx : ∀ p : (E.comap gT).subscheme,
      (E.comap gT).subschemeι p ∈ (E.comap gT).support := by
    intro p
    change (E.comap gT).subschemeι p ∈ ((E.comap gT).support : Set _)
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨p, rfl⟩
  have hmIso : IsIso m := by
    refine isIso_of_etale_of_bijective_of_isIso_residueFieldMap m ⟨fun p p' _ => ?_, fun z => ?_⟩
      (fun p => ?_)
    · exact (E.comap gT).subschemeι.isEmbedding.injective
        (hGinj ((hDpt _ (hGx p)).trans (hDpt _ (hGx p')).symm))
    · -- `E` has one point and the preimage is nonempty
      have hd₀O : b (D.subschemeι d₀) =
          (BigFppfOver.toScheme B integerBase hZ).map t (IsLocalRing.closedPoint P.carrier) := by
        rw [hd₀u]; exact (Scheme.fromSpecResidueField_apply u₀ _).symm
      obtain ⟨z₀, hz₀, -⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := (BigFppfOver.toScheme B integerBase hZ).map bO)
        (g := (BigFppfOver.toScheme B integerBase hZ).map t) (D.subschemeι d₀)
        (IsLocalRing.closedPoint P.carrier) hd₀O
      set g := hGT.isoPullback.inv z₀ with hg
      have hgO : (BigFppfOver.toScheme B integerBase hZ).map gO g = D.subschemeι d₀ := by
        rw [hg, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
        exact hz₀
      have hgE : g ∈ (E.comap gT).support := by
        rw [← hcomapEq, Scheme.IdealSheafData.support_comap]
        change (BigFppfOver.toScheme B integerBase hZ).map gO g ∈ (D'.support : Set _)
        rw [hgO, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨d₀, rfl⟩
      obtain ⟨p, hp⟩ := exists_subschemeι_eq _ hgE
      refine ⟨p, E.subschemeι.isEmbedding.injective ?_⟩
      rw [hEpt, hEpt]
    · -- trivial residue extension
      set g := (E.comap gT).subschemeι p with hgdef
      have hgO : (BigFppfOver.toScheme B integerBase hZ).map gO g = D.subschemeι d₀ :=
        hDpt g (hGx p)
      have hgx : gT g = x := by
        have := congrArg (fun f => f p) hm
        simp only [Scheme.Hom.comp_apply] at this
        rw [← hgdef] at this
        rw [this, hEpt]
      have hkg : (BigFppfOver.toScheme B integerBase hZ).map k g = g₀ := hg₀uniq _ (by
        rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hkV]; exact hgx)
      -- the residue field map of `gO` at `g`
      have htres :
          ∀ y, IsIso (((BigFppfOver.toScheme B integerBase hZ).map t).residueFieldMap y) := by
        intro y
        change IsIso ((Spec.map e₁ ≫
          ((BigFppfOver.toScheme B integerBase hZ).obj Ũ).fromSpecResidueField u₀).residueFieldMap
            y)
        rw [Scheme.residueFieldMap_comp]
        exact IsIso.comp_isIso' (isIso_residueFieldMap_fromSpecResidueField _ u₀ _) inferInstance
      have hgOres : IsIso (((BigFppfOver.toScheme B integerBase hZ).map gO).residueFieldMap g) := by
        have h1 := pullback_snd_residueFieldMap_isIso
          ((BigFppfOver.toScheme B integerBase hZ).map t)
          ((BigFppfOver.toScheme B integerBase hZ).map bO)
          (hGT.flip.isoPullback.hom g) (htres _)
        have h2 : hGT.flip.isoPullback.hom ≫
            pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map t)
              ((BigFppfOver.toScheme B integerBase hZ).map bO) =
            (BigFppfOver.toScheme B integerBase hZ).map gO := IsPullback.isoPullback_hom_snd _
        have h3 : IsIso ((hGT.flip.isoPullback.hom ≫
            pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map t)
              ((BigFppfOver.toScheme B integerBase hZ).map bO)).residueFieldMap g) := by
          rw [Scheme.residueFieldMap_comp]; exact IsIso.comp_isIso' h1 inferInstance
        rwa [h2] at h3
      have haO : IsIso (((BigFppfOver.toScheme B integerBase hZ).map aO).residueFieldMap
          ((BigFppfOver.toScheme B integerBase hZ).map gO g)) := by
        rw [hgO]; exact hd₀res
      have hcomp1 : IsIso (((BigFppfOver.toScheme B integerBase hZ).map gO ≫
          (BigFppfOver.toScheme B integerBase hZ).map aO).residueFieldMap g) := by
        rw [Scheme.residueFieldMap_comp]; exact IsIso.comp_isIso' haO hgOres
      have hk : IsIso (((BigFppfOver.toScheme B integerBase hZ).map k).residueFieldMap g) := by
        rw [hgOa, Scheme.residueFieldMap_comp] at hcomp1
        exact (@isIso_comp_left_iff _ _ _ _ _ _ _
          (residueFieldMap_isIso_of_isClosedImmersion
            ((BigFppfOver.toScheme B integerBase hZ).map gN)
            ((BigFppfOver.toScheme B integerBase hZ).map k g))).1 hcomp1
      have hV : IsIso (((BigFppfOver.toScheme B integerBase hZ).map gV).residueFieldMap
          ((BigFppfOver.toScheme B integerBase hZ).map k g)) := by
        rw [hkg]; exact hg₀res
      have hgTres : IsIso (gT.residueFieldMap g) := by
        have h6 : gT = (BigFppfOver.toScheme B integerBase hZ).map k ≫
            (BigFppfOver.toScheme B integerBase hZ).map gV := by
          rw [hgT, ← Functor.map_comp, hkV]
        rw [h6, Scheme.residueFieldMap_comp]
        exact IsIso.comp_isIso' hV hk
      have h5 : IsIso (((E.comap gT).subschemeι ≫ gT).residueFieldMap p) := by
        rw [Scheme.residueFieldMap_comp]; exact IsIso.comp_isIso' hgTres inferInstance
      rw [hm, Scheme.residueFieldMap_comp] at h5
      exact (@isIso_comp_left_iff _ _ _ _ _ _ _
        (residueFieldMap_isIso_of_isClosedImmersion E.subschemeι (m p))).1 h5
  have := hmIso
  refine ⟨Õ, c', bO, D', _, gO, gV', hc'et, hc'snd.symm, hrel', hfin', hGpb, hcomapEq, ?_, ?_⟩
  · rw [hm]; infer_instance
  · rw [hm, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- **The lift of a divisor of the closed fibre supported in one point** (the one-point case of
`AlgebraicGeometry.C1590Private.DivisorLiftAtClosedFibreLocal`): the front half
`AlgebraicGeometry.C1590Private.exists_chartDivisorDescends_input` followed by
`AlgebraicGeometry.C1590Private.chartDivisorDescends`. -/
theorem exists_divisorLift_of_support_eq_singleton (X : CurveFamily B hZ)
    (hXaff : IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj X.base))
    (P : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (hP : IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map P.value))
    (V : BigFppfOver B integerBase hZ) (v : V ⟶ P.siteObject) (q : yoneda.obj V ⟶ X.total.obj)
    (hV : IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm P.value))
    (E : ((BigFppfOver.toScheme B integerBase hZ).obj V).IdealSheafData)
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E)
    (hsupp : ∃ x, (E.support : Set ((BigFppfOver.toScheme B integerBase hZ).obj V)) = {x}) :
    ∃ (Y : CurveFamily B hZ) (φ : Y ⟶ X) (t : P.siteObject ⟶ Y.base)
      (q' : yoneda.obj V ⟶ Y.total.obj) (D : Space.ClosedSubspaces B integerBase hZ Y.total.obj),
      Etale ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ∧ t ≫ φ.baseMap = P.value ∧
      IsClosedImmersion ((BigFppfOver.toScheme B integerBase hZ).map t) ∧
      IsPullback q' (yoneda.map v) Y.toBase.hom (yoneda.map t) ∧ q' ≫ φ.totalMap.hom = q ∧
      IsAffine ((BigFppfOver.toScheme B integerBase hZ).obj Y.base) ∧
      Space.IsRelativeEffectiveCartierDivisor B integerBase hZ Y.toBase D ∧
      D.1.preimage q' = (Space.closedSubspaceOfIdeal V E).1 := by
  obtain ⟨x, hx⟩ := hsupp
  obtain ⟨Y, φ, t, q', hφ, ht, htci, hq'pb, hq'q, hYaff, O, c, b, D, G, gO, gV, hc, hb, hrel, hfin,
    hG, hcomap, hci, hker⟩ := exists_chartDivisorDescends_input X hXaff P hP V v q hV E hE x hx
  let PY : Space.FieldValuedPoint B integerBase hZ (schemeSpace Y.base).obj :=
    ⟨P.carrier, P.contained, P.toBase, t⟩
  have hq'Y : IsPullback q' (yoneda.map v) Y.toBase.hom (yonedaEquiv.symm PY.value) := by
    rw [yonedaEquiv_symm_value PY]; exact hq'pb
  obtain ⟨Y', φ', t', q'', D', hφ', ht', ht'ci, hq''pb, hq''q, hY'aff, hrel', hpre⟩ :=
    chartDivisorDescends B hZ Y PY htci V v q' hq'Y E O c hc b hb D hrel hfin G gO gV hG hcomap
      hci hker
  refine ⟨Y', φ' ≫ φ, t', q'', D', ?_, ?_, ht'ci, hq''pb, ?_, hY'aff, hrel', hpre⟩
  · change Etale ((BigFppfOver.toScheme B integerBase hZ).map (φ'.baseMap ≫ φ.baseMap))
    rw [Functor.map_comp]; infer_instance
  · change t' ≫ φ'.baseMap ≫ φ.baseMap = P.value
    rw [← Category.assoc]
    exact (congrArg (· ≫ φ.baseMap) ht').trans ht
  · change q'' ≫ (φ'.totalMap ≫ φ.totalMap).hom = q
    exact ((congrArg (q'' ≫ ·) (InducedCategory.comp_hom _ _)).trans
      (Category.assoc _ _ _).symm).trans ((congrArg (· ≫ φ.totalMap.hom) hq''q).trans hq'q)

/-- **The lift of a divisor of the closed fibre supported in one point** (P2a towards Stacks 0E6F):
`AlgebraicGeometry.C1590Private.DivisorLiftAtClosedFibreLocal`, proved by
`AlgebraicGeometry.C1590Private.exists_divisorLift_of_support_eq_singleton`. -/
theorem divisorLiftAtClosedFibreLocal : DivisorLiftAtClosedFibreLocal B hZ :=
  fun X hXaff P hP V v q hV E hE hsupp =>
    exists_divisorLift_of_support_eq_singleton X hXaff P hP V v q hV E hE hsupp

end C1590Private

end AlgebraicGeometry

end
