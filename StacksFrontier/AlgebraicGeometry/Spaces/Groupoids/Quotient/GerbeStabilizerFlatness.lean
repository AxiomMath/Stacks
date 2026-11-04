module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSingletonCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PointwiseFibreFullFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.FlatStabilizerQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The stabilizer of a groupoid whose arrows cover the related pairs is flat

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces whose source map is flat and locally of
finite presentation, and let `q : U ⟶ Z` be a morphism to an algebraic space, constant on arrows,
such that `(s, t) : R ⟶ U ×_Z U` is a surjection of fppf sheaves. This is the situation of a
groupoid presenting a gerbe over the algebraic space `Z`. Then the stabilizer of the groupoid is
flat and locally of finite presentation over `U`: for every point `a` of `U` over a scheme `T`,
the presheaf of arrows from `a` to `a` is flat and locally of finite presentation over `T`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isFlat_stabilizer_of_isLocallySurjective`: the
  stabilizer is flat and locally of finite presentation at every scheme-valued point.
* `AlgebraicGeometry.Stack.isLocallySurjective_of_isGerbeOver_restrictedMorphism`: for a quotient
  stack `[U/R]` which is a gerbe over an algebraic space `Y`, the map `(s, t) : R ⟶ U ×_Y U` is a
  surjection of fppf sheaves.

## References

* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06PJ](https://stacks.math.columbia.edu/tag/06PJ)
* [Stacks Project, Tag 06PL](https://stacks.math.columbia.edu/tag/06PL)
* [Stacks Project, Tag 06QJ](https://stacks.math.columbia.edu/tag/06QJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A property of scheme morphisms read on étale charts passes to base changes between algebraic
spaces**, when it is étale local on the source and target and stable under base change: for a
cartesian square of presheaves all of whose corners are algebraic spaces, if the property holds
on every étale chart of `f` then it holds on every étale chart of its base change `p`. -/
theorem holdsOnEveryEtaleChart_of_isPullback_of_isAlgebraicSpace
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange]
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y}
    {f : X ⟶ Y} (sq : IsPullback p q g f) (hW : IsAlgebraicSpace B S hS W)
    (hX : IsAlgebraicSpace B S hS X) (hZ : IsAlgebraicSpace B S hS Z)
    (hY : IsAlgebraicSpace B S hS Y) (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P p := by
  have := holdsOnEveryEtaleChart_isStableUnderBaseChange B S hS P hP
  let Wo : AlgebraicSpaces B S hS := ⟨W, hW⟩
  let Xo : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Zo : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let Yo : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  have sq' : IsPullback (ObjectProperty.homMk q : Wo ⟶ Xo) (ObjectProperty.homMk p : Wo ⟶ Zo)
      (ObjectProperty.homMk f : Xo ⟶ Yo) (ObjectProperty.homMk g : Zo ⟶ Yo) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι (fun F => IsAlgebraicSpace B S hS F)) sq.flip
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) => HoldsOnEveryEtaleChart B S hS P k.hom)
    sq' hf

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- For points `a` over `T` and `a' = h ≫ a` over `T'` of the object space, the presheaf of
arrows from `a'` to itself is the base change along `h : T' ⟶ T` of the presheaf of arrows from
`a` to itself. -/
lemma isPullback_arrowsBetween_comp {T T' : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (a : T ⟶ G.objects.obj) (h : T' ⟶ T) (a' : T' ⟶ G.objects.obj) (ha : h ≫ a = a') :
    ∃ k : arrowsBetween G a' a' ⟶ arrowsBetween G a a,
      IsPullback k (pullback.fst _ _) (pullback.fst _ _) h := by
  subst ha
  refine ⟨pullback.lift (pullback.fst _ _ ≫ h) (pullback.snd _ _) ?_,
    IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback (prod.lift a a) (prod.lift G.target.hom G.source.hom)).flip⟩
  · rw [Category.assoc, ← pullback.condition]
    apply prod.hom_ext <;> simp
  · rw [pullback.lift_snd,
      show h ≫ prod.lift a a = prod.lift (h ≫ a) (h ≫ a) by apply prod.hom_ext <;> simp]
    exact (IsPullback.of_hasPullback _ _).flip

/-- Translating a stabilizer element `g` of `w` by an arrow `σ : w ⟶ b` and back:
`σ⁻¹ ∘ (σ ∘ g) = g`. -/
lemma groupoidCompose_inverse_compose {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (σ g : T ⟶ G.arrows.obj) (hg : σ ≫ G.source.hom = g ≫ G.target.hom)
    (hinv : (σ ≫ groupoidInverse G) ≫ G.source.hom =
      groupoidCompose G σ g hg ≫ G.target.hom) :
    groupoidCompose G (σ ≫ groupoidInverse G) (groupoidCompose G σ g hg) hinv = g := by
  have wab : (σ ≫ groupoidInverse G) ≫ G.source.hom = σ ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_source]
  have wL : groupoidCompose G (σ ≫ groupoidInverse G) σ wab ≫ G.source.hom =
      g ≫ G.target.hom := by
    rw [groupoidCompose_source, hg]
  rw [← groupoidCompose_assoc G (σ ≫ groupoidInverse G) σ g wab hg wL hinv]
  have hid : identityAfterSource G σ = identityAfterTarget G g := by
    simp only [identityAfterSource, identityAfterTarget]
    rw [← Category.assoc, hg, Category.assoc]
  rw [groupoidCompose_congr G wL (identityAfterTarget_composable G g)
    ((groupoidCompose_inverseRight G σ).trans hid) rfl]
  exact groupoidCompose_leftIdentity G g

/-- The presheaf of arrows from `a` to itself, for a point `a` over an algebraic space, is an
algebraic space. -/
private lemma isAlgebraicSpace_arrowsBetween {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace C S hS T) (a : T ⟶ G.objects.obj) :
    IsAlgebraicSpace C S hS (arrowsBetween G a a) :=
  isAlgebraicSpace_pullback C S hS _ _ hT G.arrows.property
    (isAlgebraicSpace_prod C S hS G.objects.property G.objects.property)

/-- Flatness and local finite presentation pass to base changes between algebraic spaces. -/
private lemma isFlat_and_isLocallyOfFinitePresentation_of_isPullback
    {W X Z Y : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y}
    {f : X ⟶ Y} (sq : IsPullback p q g f) (hW : IsAlgebraicSpace C S hS W)
    (hX : IsAlgebraicSpace C S hS X) (hZ : IsAlgebraicSpace C S hS Z)
    (hY : IsAlgebraicSpace C S hS Y)
    (hf : Space.IsFlat C S hS f ∧ Space.IsLocallyOfFinitePresentation C S hS f) :
    Space.IsFlat C S hS p ∧ Space.IsLocallyOfFinitePresentation C S hS p :=
  ⟨holdsOnEveryEtaleChart_of_isPullback_of_isAlgebraicSpace C S hS _
      Flat.isEtaleLocalOnSourceAndTarget sq hW hX hZ hY hf.1,
    holdsOnEveryEtaleChart_of_isPullback_of_isAlgebraicSpace C S hS _
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget sq hW hX hZ hY hf.2⟩

/-- **Fppf descent of the flatness of the stabilizer.** If `w : V ⟶ U` is surjective, flat and
locally of finite presentation and the stabilizer of `w` is flat and locally of finite
presentation over `V`, so is the stabilizer of the identity of `U` over `U`. -/
lemma isFlat_stabilizer_id_of_fppf {V : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace C S hS V) (w : V ⟶ G.objects.obj)
    (hwF : Space.IsFlat C S hS w) (hwL : Space.IsLocallyOfFinitePresentation C S hS w)
    (hwS : Space.IsSurjective C S hS w)
    (hmF : Space.IsFlat C S hS
      (pullback.fst (prod.lift w w) (prod.lift G.target.hom G.source.hom)))
    (hmL : Space.IsLocallyOfFinitePresentation C S hS
      (pullback.fst (prod.lift w w) (prod.lift G.target.hom G.source.hom))) :
    Space.IsFlat C S hS (pullback.fst (prod.lift (𝟙 G.objects.obj) (𝟙 G.objects.obj))
        (prod.lift G.target.hom G.source.hom)) ∧
      Space.IsLocallyOfFinitePresentation C S hS
        (pullback.fst (prod.lift (𝟙 G.objects.obj) (𝟙 G.objects.obj))
          (prod.lift G.target.hom G.source.hom)) := by
  have hU := G.objects.property
  have hR := G.arrows.property
  obtain ⟨k, hk⟩ := isPullback_arrowsBetween_comp G (𝟙 G.objects.obj) w w (Category.comp_id w)
  let Mo : AlgebraicSpaces C S hS := ⟨_, isAlgebraicSpace_arrowsBetween G hV w⟩
  let No : AlgebraicSpaces C S hS := ⟨_, isAlgebraicSpace_arrowsBetween G hU (𝟙 _)⟩
  let Vo : AlgebraicSpaces C S hS := ⟨V, hV⟩
  let Uo : AlgebraicSpaces C S hS := ⟨G.objects.obj, hU⟩
  have hsq : IsPullback (ObjectProperty.homMk k : Mo ⟶ No)
      (ObjectProperty.homMk (pullback.fst _ _) : Mo ⟶ Vo)
      (ObjectProperty.homMk (pullback.fst _ _) : No ⟶ Uo) (ObjectProperty.homMk w : Vo ⟶ Uo) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι (fun F => IsAlgebraicSpace C S hS F)) hk
  have : (flatProperty C S hS).IsLocalAtTarget (Topology.fppf.precoverage.{u, 0} C S hS) :=
    (isFlat_isLocalAtTarget_fpqc C S hS).of_le (fppfPrecoverage_le_fpqcPrecoverage C S hS)
  have : (locallyOfFinitePresentationProperty C S hS).IsLocalAtTarget
      (Topology.fppf.precoverage.{u, 0} C S hS) :=
    (isLocallyOfFinitePresentation_isLocalAtTarget_fpqc C S hS).of_le
      (fppfPrecoverage_le_fpqcPrecoverage C S hS)
  exact ⟨prop_of_isPullback_of_fppf.{u, 0} C S hS (flatProperty C S hS) hsq hwS hwF hwL hmF,
    prop_of_isPullback_of_fppf.{u, 0} C S hS (locallyOfFinitePresentationProperty C S hS) hsq
      hwS hwF hwL hmL⟩

/-- **The stabilizer of a groupoid whose arrows cover the related pairs is flat.** Let `q : U ⟶ Z`
be a morphism from the object space to an algebraic space identifying the source and the target
of every arrow, such that `(s, t) : R ⟶ U ×_Z U` is a surjection of fppf sheaves, and let the
source map be flat and locally of finite presentation. Then the presheaf of arrows from the
identity of `U` to itself is flat and locally of finite presentation over `U`. -/
theorem isFlat_stabilizer_id_of_isLocallySurjective {Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace C S hS Z) (q : G.objects.obj ⟶ Z)
    (hq : G.source.hom ≫ q = G.target.hom ≫ q)
    (hπ : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (pullback.lift G.source.hom G.target.hom hq))
    (hsF : Space.IsFlat C S hS G.source.hom)
    (hsL : Space.IsLocallyOfFinitePresentation C S hS G.source.hom) :
    Space.IsFlat C S hS (pullback.fst (prod.lift (𝟙 G.objects.obj) (𝟙 G.objects.obj))
        (prod.lift G.target.hom G.source.hom)) ∧
      Space.IsLocallyOfFinitePresentation C S hS
        (pullback.fst (prod.lift (𝟙 G.objects.obj) (𝟙 G.objects.obj))
          (prod.lift G.target.hom G.source.hom)) := by
  have hU := G.objects.property
  have hR := G.arrows.property
  let π := pullback.lift G.source.hom G.target.hom hq
  have hR' : IsAlgebraicSpace C S hS (pullback q q) :=
    isAlgebraicSpace_pullback C S hS q q hU hU hZ
  have hπ₁ : π ≫ pullback.fst q q = G.source.hom := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ pullback.snd q q = G.target.hom := pullback.lift_snd _ _ _
  have hp₁F : Space.IsFlat C S hS (pullback.fst q q) :=
    isFlat_of_comp_of_locallySurjective C S hS hR hR' hU π _ (by rwa [hπ₁]) hπ
  have hp₁L : Space.IsLocallyOfFinitePresentation C S hS (pullback.fst q q) :=
    isLocallyOfFinitePresentation_of_comp_of_locallySurjective C S hS hR hR' hU π _
      (by rwa [hπ₁]) hπ
  have hp₁S : Space.IsSurjective C S hS (pullback.fst q q) := by
    let δ : G.objects.obj ⟶ pullback q q := pullback.lift (𝟙 _) (𝟙 _) rfl
    have hδ : δ ≫ pullback.fst q q = 𝟙 _ := pullback.lift_fst _ _ _
    intro x
    refine ⟨pointsMap C S hS _ δ x, ?_⟩
    rw [← pointsMap_comp_apply, hδ, pointsMap_id]
    rfl
  obtain ⟨U₀, e, hes, hee⟩ := hR'.exists_atlas
  obtain ⟨V₀, f, hfF, hfL, hfS, r, hr⟩ := exists_single_fppf_lift_of_isLocallySurjective C S hS
    hR.isSheaf hR'.isSheaf π hπ U₀ (yonedaEquiv e)
  let v : yoneda.obj V₀ ⟶ pullback q q := yoneda.map f ≫ e
  let σ : yoneda.obj V₀ ⟶ G.arrows.obj := yonedaEquiv.symm r
  have hσ : σ ≫ π = v := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    simp only [σ, Equiv.apply_symm_apply, v]
    rw [hr, ← yonedaEquiv_naturality]
  have hV := isAlgebraicSpace_yoneda C S hS V₀
  have hU₀ := isAlgebraicSpace_yoneda C S hS U₀
  have heEt : IsEtale C S hS e := isEtale_of_presheaf_etale C S hS hee
  have hvF : Space.IsFlat C S hS v :=
    isFlat_comp C S hS hV hU₀ hR' _ _
      (holdsOnEveryEtaleChart_yoneda_map C S hS Flat.isEtaleLocalOnSourceAndTarget f hfF)
      (isFlat_of_isEtale C S hS heEt)
  have hvL : Space.IsLocallyOfFinitePresentation C S hS v :=
    isLocallyOfFinitePresentation_comp C S hS hV hU₀ hR' _ _
      (holdsOnEveryEtaleChart_yoneda_map C S hS
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget f hfL)
      (isLocallyOfFinitePresentation_of_isEtale C S hS heEt)
  have := Space.inverseImage_isStableUnderBaseChange C S hS
    (inferInstance : MorphismProperty.IsStableUnderBaseChange (@Surjective.{u}))
  have hvS : Space.IsSurjective C S hS v :=
    isSurjective_comp C S hS
      (isSurjective_of_presheafSurjective C S hS _ (MorphismProperty.relative_map hfS))
      (isSurjective_of_presheafSurjective C S hS e hes)
  let w : yoneda.obj V₀ ⟶ G.objects.obj := σ ≫ G.source.hom
  let b : yoneda.obj V₀ ⟶ G.objects.obj := σ ≫ G.target.hom
  have hvw : v ≫ pullback.fst q q = w := by rw [← hσ, Category.assoc, hπ₁]
  have hvb : v ≫ pullback.snd q q = b := by rw [← hσ, Category.assoc, hπ₂]
  let Y := pullback w G.source.hom
  let yF : Y ⟶ yoneda.obj V₀ := pullback.fst w G.source.hom
  let yS : Y ⟶ G.arrows.obj := pullback.snd w G.source.hom
  have hYw : yF ≫ w = yS ≫ G.source.hom := pullback.condition
  have hY : IsAlgebraicSpace C S hS Y := isAlgebraicSpace_pullback C S hS w G.source.hom hV hR hU
  obtain ⟨hyF, hyL⟩ := isFlat_and_isLocallyOfFinitePresentation_of_isPullback
    (IsPullback.of_hasPullback w G.source.hom) hY hR hV hU ⟨hsF, hsL⟩
  have hcondY : (yF ≫ w) ≫ q = (yS ≫ G.target.hom) ≫ q := by
    rw [hYw, Category.assoc, Category.assoc, hq]
  let y' : Y ⟶ pullback q q := pullback.lift (yF ≫ w) (yS ≫ G.target.hom) hcondY
  have hy'₁ : y' ≫ pullback.fst q q = yF ≫ w := pullback.lift_fst _ _ _
  have hy'₂ : y' ≫ pullback.snd q q = yS ≫ G.target.hom := pullback.lift_snd _ _ _
  let Zs := pullback y' v
  let zF : Zs ⟶ Y := pullback.fst y' v
  let zS : Zs ⟶ yoneda.obj V₀ := pullback.snd y' v
  have hZv : zF ≫ y' = zS ≫ v := pullback.condition
  have hZs : IsAlgebraicSpace C S hS Zs := isAlgebraicSpace_pullback C S hS y' v hY hV hR'
  obtain ⟨hzF, hzL⟩ := isFlat_and_isLocallyOfFinitePresentation_of_isPullback
    (IsPullback.of_hasPullback y' v) hZs hV hY hR' ⟨hvF, hvL⟩
  have hcF : Space.IsFlat C S hS (zF ≫ yF) := isFlat_comp C S hS hZs hY hV zF yF hzF hyF
  have hcL : Space.IsLocallyOfFinitePresentation C S hS (zF ≫ yF) :=
    isLocallyOfFinitePresentation_comp C S hS hZs hY hV zF yF hzL hyL
  have hz₁ : zF ≫ yF ≫ w = zS ≫ w := by
    simpa only [Category.assoc, hy'₁, hvw] using congrArg (· ≫ pullback.fst q q) hZv
  have hz₂ : zF ≫ yS ≫ G.target.hom = zS ≫ b := by
    simpa only [Category.assoc, hy'₂, hvb] using congrArg (· ≫ pullback.snd q q) hZv
  let σ₁ : Zs ⟶ G.arrows.obj := zS ≫ σ
  let ρ : Zs ⟶ G.arrows.obj := zF ≫ yS
  have w₀ : (σ₁ ≫ groupoidInverse G) ≫ G.source.hom = ρ ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_source]
    change zS ≫ σ ≫ G.target.hom = (zF ≫ yS) ≫ G.target.hom
    rw [Category.assoc, hz₂]
  let gψ := groupoidCompose G (σ₁ ≫ groupoidInverse G) ρ w₀
  have hgψt : gψ ≫ G.target.hom = zF ≫ yF ≫ w := by
    rw [groupoidCompose_target, Category.assoc, groupoidInverse_target, hz₁]
    rfl
  have hgψs : gψ ≫ G.source.hom = zF ≫ yF ≫ w := by
    rw [groupoidCompose_source]
    change (zF ≫ yS) ≫ G.source.hom = _
    rw [Category.assoc, ← hYw]
  let M := arrowsBetween G w w
  let mF : M ⟶ yoneda.obj V₀ := pullback.fst (prod.lift w w) (prod.lift G.target.hom G.source.hom)
  let mS : M ⟶ G.arrows.obj := pullback.snd (prod.lift w w) (prod.lift G.target.hom G.source.hom)
  have hmt : mS ≫ G.target.hom = mF ≫ w := arrowsBetween_target w w
  have hms : mS ≫ G.source.hom = mF ≫ w := arrowsBetween_source w w
  let ψ : Zs ⟶ M := pullback.lift (zF ≫ yF) gψ (by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, hgψt]
    · simp only [Category.assoc, prod.lift_snd, hgψs])
  have hψF : ψ ≫ mF = zF ≫ yF := pullback.lift_fst _ _ _
  have hψS : ψ ≫ mS = gψ := pullback.lift_snd _ _ _
  let σ₀ : M ⟶ G.arrows.obj := mF ≫ σ
  have wχ : σ₀ ≫ G.source.hom = mS ≫ G.target.hom := by
    rw [hmt]; rfl
  let ρχ := groupoidCompose G σ₀ mS wχ
  let yχ : M ⟶ Y := pullback.lift mF ρχ (by
    rw [groupoidCompose_source, hms])
  have hyχF : yχ ≫ yF = mF := pullback.lift_fst _ _ _
  have hyχS : yχ ≫ yS = ρχ := pullback.lift_snd _ _ _
  let χ : M ⟶ Zs := pullback.lift yχ mF (by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hy'₁, hvw, ← Category.assoc, hyχF]
    · rw [Category.assoc, Category.assoc, hy'₂, hvb, ← Category.assoc, hyχS,
        groupoidCompose_target]
      rfl)
  have hχF : χ ≫ zF = yχ := pullback.lift_fst _ _ _
  have hχS : χ ≫ zS = mF := pullback.lift_snd _ _ _
  have hχψ : χ ≫ ψ = 𝟙 M := by
    apply pullback.hom_ext
    · rw [Category.assoc, hψF, ← Category.assoc, hχF, hyχF, Category.id_comp]
    · rw [Category.assoc, hψS, Category.id_comp, groupoidCompose_pre]
      have h₁ : χ ≫ σ₁ ≫ groupoidInverse G = σ₀ ≫ groupoidInverse G := by
        change χ ≫ (zS ≫ σ) ≫ groupoidInverse G = (mF ≫ σ) ≫ groupoidInverse G
        rw [← Category.assoc, ← Category.assoc, hχS]
      have h₂ : χ ≫ ρ = ρχ := by
        change χ ≫ zF ≫ yS = ρχ
        rw [← Category.assoc, hχF, hyχS]
      have hinv : (σ₀ ≫ groupoidInverse G) ≫ G.source.hom = ρχ ≫ G.target.hom := by
        rw [Category.assoc, groupoidInverse_source, groupoidCompose_target]
      rw [groupoidCompose_congr G _ hinv h₁ h₂]
      exact groupoidCompose_inverse_compose G σ₀ mS wχ hinv
  have hψls : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) ψ :=
    Presheaf.isLocallySurjective_of_surjective _ ψ fun X m =>
      ⟨χ.app X m, congrArg (fun f => f.app X m) hχψ⟩
  have hM := isAlgebraicSpace_arrowsBetween G hV w
  have hmF : Space.IsFlat C S hS mF :=
    isFlat_of_comp_of_locallySurjective C S hS hZs hM hV ψ mF (by rw [hψF]; exact hcF) hψls
  have hmL : Space.IsLocallyOfFinitePresentation C S hS mF :=
    isLocallyOfFinitePresentation_of_comp_of_locallySurjective C S hS hZs hM hV ψ mF
      (by rw [hψF]; exact hcL) hψls
  have hwF : Space.IsFlat C S hS w := by
    rw [← hvw]; exact isFlat_comp C S hS hV hR' hU _ _ hvF hp₁F
  have hwL : Space.IsLocallyOfFinitePresentation C S hS w := by
    rw [← hvw]; exact isLocallyOfFinitePresentation_comp C S hS hV hR' hU _ _ hvL hp₁L
  have hwS : Space.IsSurjective C S hS w := by
    rw [← hvw]; exact isSurjective_comp C S hS hvS hp₁S
  exact isFlat_stabilizer_id_of_fppf G hV w hwF hwL hwS hmF hmL

/-- **The stabilizer of a groupoid whose arrows cover the related pairs is flat, at every point.**
Under the hypotheses of `isFlat_stabilizer_id_of_isLocallySurjective`, for every point `a` of the
object space over a scheme `T` the presheaf of arrows from `a` to `a` is flat and locally of
finite presentation over `T`. -/
theorem isFlat_stabilizer_of_isLocallySurjective {Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace C S hS Z) (q : G.objects.obj ⟶ Z)
    (hq : G.source.hom ≫ q = G.target.hom ≫ q)
    (hπ : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (pullback.lift G.source.hom G.target.hom hq))
    (hsF : Space.IsFlat C S hS G.source.hom)
    (hsL : Space.IsLocallyOfFinitePresentation C S hS G.source.hom)
    (T : BigFppfOver C S hS) (a : yoneda.obj T ⟶ G.objects.obj) :
    Space.IsFlat C S hS (pullback.fst (prod.lift a a) (prod.lift G.target.hom G.source.hom)) ∧
      Space.IsLocallyOfFinitePresentation C S hS
        (pullback.fst (prod.lift a a) (prod.lift G.target.hom G.source.hom)) := by
  have hU := G.objects.property
  have hT := isAlgebraicSpace_yoneda C S hS T
  obtain ⟨k, hk⟩ := isPullback_arrowsBetween_comp G (𝟙 G.objects.obj) a a (Category.comp_id a)
  exact isFlat_and_isLocallyOfFinitePresentation_of_isPullback hk.flip
    (isAlgebraicSpace_arrowsBetween G hT a) (isAlgebraicSpace_arrowsBetween G hU _) hT hU
    (isFlat_stabilizer_id_of_isLocallySurjective G hZ q hq hπ hsF hsL)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

namespace AlgebraicGeometry.Stack

open GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)

/-- **For a quotient stack which is a gerbe over an algebraic space `Y`, the arrows cover the
related pairs.** Let `Φ : [U/R] ⟶ Y` make `[U/R]` a gerbe over an algebraic space `Y`, and let
`ψ : U ⟶ Y` be its restriction along the projection (Stacks 0DUH). Then `(s, t) : R ⟶ U ×_Y U`
is a surjection of fppf sheaves. -/
theorem isLocallySurjective_of_isGerbeOver_restrictedMorphism {Y : AlgebraicSpaces C S hS}
    (Φ : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val)
    (hΦ : IsGerbeOver (BigFppfOver.topology C S hS) (fibredCategory C S hS Y.obj).val.p
      Φ.toFunctor)
    (hq : G.source.hom ≫ (restrictedMorphism G Φ).hom =
      G.target.hom ≫ (restrictedMorphism G Φ).hom) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (pullback.lift G.source.hom G.target.hom hq) := by
  let ψ := (restrictedMorphism G Φ).hom
  let r := (fibredCategory C S hS Y.obj).val.p
  let p := (quotientStack G).p
  have hp : p.IsFiberedInGroupoids := isFiberedInGroupoids_quotientStack G
  have hΦw : Φ.toFunctor ⋙ r = p := Φ.w
  have hspec := restrictedMorphism_spec G Φ
  have himage : ∀ (T : BigFppfOver C S hS) (a : G.objects.obj.obj (op T)),
      Φ.obj ((quotientStackProjection G).obj ⟨T, Discrete.mk a⟩) =
        ⟨T, Discrete.mk (ψ.app (op T) a)⟩ := by
    intro T a
    have h := congrArg (fun K => K.obj (⟨T, Discrete.mk a⟩ :
      (fibredCategory C S hS G.objects.obj).val.obj)) hspec
    exact h.trans (associatedMap_obj C S hS ψ _)
  let κ : ∀ {T V : BigFppfOver C S hS} (i : V ⟶ T) (a : G.objects.obj.obj (op T)),
      (quotientStackProjection G).obj ⟨V, Discrete.mk (G.objects.obj.map i.op a)⟩ ⟶
        (quotientStackProjection G).obj ⟨T, Discrete.mk a⟩ :=
    fun i a => (quotientStackProjection G).map ⟨i, eqToHom rfl⟩
  have hκ : ∀ {T V : BigFppfOver C S hS} (i : V ⟶ T) (a : G.objects.obj.obj (op T)),
      p.IsHomLift i (κ i a) := by
    intro T V i a
    let φ : (⟨V, Discrete.mk (G.objects.obj.map i.op a)⟩ :
        (fibredCategory C S hS G.objects.obj).val.obj) ⟶ ⟨T, Discrete.mk a⟩ := ⟨i, eqToHom rfl⟩
    have h : (fibredCategory C S hS G.objects.obj).val.p.IsHomLift i φ :=
      IsHomLift.map (fibredCategory C S hS G.objects.obj).val.p φ
    exact Functor.isHomLift_map_of_comp_eq (quotientStackProjection G).w i φ
  let lift := pullback.lift G.source.hom G.target.hom hq
  refine ⟨?_⟩
  intro T x
  let a := (pullback.fst ψ ψ).app (op T) x
  let b := (pullback.snd ψ ψ).app (op T) x
  have hab : ψ.app (op T) a = ψ.app (op T) b := by
    simpa [a, b] using congrArg (fun f => f.app (op T) x) (pullback.condition (f := ψ) (g := ψ))
  let za := (quotientStackProjection G).obj ⟨T, Discrete.mk a⟩
  let zb := (quotientStackProjection G).obj ⟨T, Discrete.mk b⟩
  have hzab : Φ.obj za = Φ.obj zb :=
    (himage T a).trans ((congrArg (fun y => (⟨T, Discrete.mk y⟩ :
      (fibredCategory C S hS Y.obj).val.obj)) hab).trans (himage T b).symm)
  have hrT : r.obj (Φ.obj za) = T := by rw [himage T a]; rfl
  obtain ⟨Rs, hRs, hloc⟩ :=
    hΦ.locally_full (eqToHom hzab) (IsHomLift.eqToHom_domain_lift_id hzab hrT)
  refine (BigFppfOver.topology C S hS).superset_covering ?_ hRs
  intro V i hi
  obtain ⟨x₁, x₁', ξ, ξ', α, hξ, hξ', hα, -⟩ := hloc i hi
  have hξp : p.IsHomLift i ξ := hΦw ▸ hξ
  have hξ'p : p.IsHomLift i ξ' := hΦw ▸ hξ'
  have hαp : p.IsHomLift (𝟙 V) α := hΦw ▸ hα
  let a' := G.objects.obj.map i.op a
  let b' := G.objects.obj.map i.op b
  have := hκ i a
  have := hκ i b
  have : p.IsStronglyCartesian i ξ := hp.isStronglyCartesian_homLift i ξ
  have : p.IsStronglyCartesian i (κ i b) := hp.isStronglyCartesian_homLift i (κ i b)
  let φ := Functor.IsCartesian.map p i ξ (κ i a)
  let l := φ ≫ α ≫ ξ'
  have hl : p.IsHomLift i l := by
    simpa using (inferInstance : p.IsHomLift (𝟙 V ≫ 𝟙 V ≫ i) l)
  let β := Functor.IsCartesian.map p i (κ i b) l
  let βf :
      (pointwiseToQuotientStackFiber G V).obj a' ⟶ (pointwiseToQuotientStackFiber G V).obj b' :=
    ⟨β, Functor.IsCartesian.map_isHomLift p i (κ i b) l⟩
  obtain ⟨hff⟩ := fullyFaithful_pointwiseToQuotientStackFiber G V
  let rr := G.toGroupoidInFunctors.evaluationArrowEquiv (op V) a' b' (hff.preimage βf)
  refine ⟨rr.1, ?_⟩
  have hmor : yonedaEquiv.symm (lift.app (op V) rr.1) =
      yonedaEquiv.symm ((pullback ψ ψ).map i.op x) := by
    rw [← yonedaEquiv_symm_naturality_right V lift rr.1, yonedaEquiv_symm_map]
    apply pullback.hom_ext
    · simp only [Category.assoc, lift, pullback.lift_fst]
      rw [yonedaEquiv_symm_naturality_right V G.source.hom rr.1,
        yonedaEquiv_symm_naturality_right T (pullback.fst _ _) x, Quiver.Hom.unop_op,
        yonedaEquiv_symm_naturality_left]
      exact congrArg yonedaEquiv.symm rr.2.1
    · simp only [Category.assoc, lift, pullback.lift_snd]
      rw [yonedaEquiv_symm_naturality_right V G.target.hom rr.1,
        yonedaEquiv_symm_naturality_right T (pullback.snd _ _) x, Quiver.Hom.unop_op,
        yonedaEquiv_symm_naturality_left]
      exact congrArg yonedaEquiv.symm rr.2.2
  exact yonedaEquiv.symm.injective hmor

end AlgebraicGeometry.Stack

end
