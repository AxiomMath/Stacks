module

public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The relative dimension at a point is unchanged by base change

For a cartesian square of algebraic spaces over `S` with `f` locally of finite type, the relative
dimension of the base change `f'` at a point `x'` of its source is the relative dimension of `f` at
the image of `x'`.

## Main results

* `AlgebraicGeometry.Space.hasRelativeDimensionAt_comp_iff`: the relative dimension of `g ≫ f` at a
  point is the relative dimension of `f` at its image, for `g` étale after every representable base
  change.
* `AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_of_isPullback'`: the relative dimension of
  the base change of `f` at a point is the relative dimension of `f` at its image.

## References

* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The relative dimension along a relatively étale morphism into the source -/

/-- The relative dimension at a point is unchanged by a precomposition with a morphism which is
étale after every representable base change: the relative dimension of `g ≫ f` at `x` is the
relative dimension of `f` at the image of `x`. -/
theorem hasRelativeDimensionAt_comp_iff (d : ℕ∞)
    {E F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : E ⟶ F) (f : F ⟶ G)
    (hg : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hE : IsAlgebraicSpace B S hS E) (hG : IsAlgebraicSpace B S hS G)
    (x : points B S hS E) :
    HasRelativeDimensionAt d B S hS (g ≫ f) x ↔
      HasRelativeDimensionAt d B S hS f (pointsMap B S hS E g x) := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  refine ⟨fun hd ↦ ?_, hasRelativeDimensionAt_comp B S hS d g f hg x⟩
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hE hG (g ≫ f) x
  refine (hasRelativeDimensionAt_iff_of_chart B S hS d f _
    { U := c.U
      V := c.V
      a := c.a ≫ g
      b := c.b
      h := c.h
      a_etale := MorphismProperty.comp_mem _ c.a g c.a_etale hg
      b_etale := c.b_etale
      comm := by rw [c.comm, Category.assoc]
      representative := c.representative
      point := c.point
      maps_to := by rw [pointsMap_comp_apply, c.maps_to] }).mpr ?_
  exact (hasRelativeDimensionAt_iff_of_chart B S hS d (g ≫ f) x c).mp hd

/-! ### The chart of the base-changed source -/

/-- The morphism of presheaves induced on a chart square of a base change is étale, resp.
surjective, after every representable base change.

The square `sq` exhibits `p : W ⟶ Z` as the base change of `f : X ⟶ Y` along `g : Z ⟶ Y`; `aU` is a
chart of `X` sitting over the chart `bV` of `Y` through `h`, the chart `bV'` of `Z` factors through
a chart `dZ` of `Z` by `δ` and sits over `bV` through `φ` in a *cartesian* square, and `U'` sits
over `V'` and `U` in a cartesian square of the site. Then the induced morphism `a''` from
`yoneda.obj U'` to `W` has every property `Q` of morphisms of the site which is tested after every
representable base change, is stable under composition, and holds for `aU` and for `dZ`. -/
private theorem presheaf_of_chartSquare_isPullback
    {Q : MorphismProperty (BigFppfOver B S hS)}
    (hQcomp : (Q.presheaf).IsStableUnderComposition)
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    {U V V' D U' : BigFppfOver B S hS}
    {aU : yoneda.obj U ⟶ X} {bV : yoneda.obj V ⟶ Y} {dZ : yoneda.obj D ⟶ Z}
    {bV' : yoneda.obj V' ⟶ Z} {a'' : yoneda.obj U' ⟶ W}
    {h : U ⟶ V} {φ : V' ⟶ V} {δ : V' ⟶ D} {h' : U' ⟶ V'} {ψ : U' ⟶ U}
    (hcommU : aU ≫ f = yoneda.map h ≫ bV)
    (sqV' : IsPullback (yoneda.map φ) (yoneda.map δ) bV (dZ ≫ g))
    (hbV' : yoneda.map δ ≫ dZ = bV')
    (sqSite : IsPullback h' ψ φ h)
    (ha''p : a'' ≫ p = yoneda.map h' ≫ bV')
    (ha''q : a'' ≫ q = yoneda.map ψ ≫ aU)
    (haU : Q.presheaf aU) (hdZ : Q.presheaf dZ) :
    Q.presheaf a'' := by
  have hcomp := hQcomp
  have sqM : IsPullback (pullback.fst bV g) (pullback.snd bV g) bV g :=
    IsPullback.of_hasPullback bV g
  have hκc : yoneda.map φ ≫ bV = bV' ≫ g := by
    rw [← hbV', Category.assoc]
    exact sqV'.w
  have hκ1 : sqM.lift (yoneda.map φ) bV' hκc ≫ pullback.fst bV g = yoneda.map φ :=
    sqM.lift_fst _ _ _
  have hκ2 : sqM.lift (yoneda.map φ) bV' hκc ≫ pullback.snd bV g = bV' :=
    sqM.lift_snd _ _ _
  have sqκ : IsPullback (yoneda.map δ) (sqM.lift (yoneda.map φ) bV' hκc) dZ
      (pullback.snd bV g) := by
    refine IsPullback.of_bot ?_ ?_ sqM.flip
    · rw [hκ1]
      exact sqV'.flip
    · rw [hκ2, hbV']
  have hκQ : Q.presheaf (sqM.lift (yoneda.map φ) bV' hκc) :=
    presheaf_of_isPullback B S hS sqκ hdZ
  have sqR : IsPullback (pullback.fst aU q) (pullback.snd aU q) aU q :=
    IsPullback.of_hasPullback aU q
  have hr₂Q : Q.presheaf (pullback.snd aU q) := presheaf_of_isPullback B S hS sqR haU
  have hϖc : (pullback.fst aU q ≫ yoneda.map h) ≫ bV = (pullback.snd aU q ≫ p) ≫ g := by
    rw [Category.assoc, ← hcommU, ← Category.assoc, sqR.w, Category.assoc, Category.assoc,
      ← sq.w]
  have hϖ1 : sqM.lift (pullback.fst aU q ≫ yoneda.map h) (pullback.snd aU q ≫ p) hϖc ≫
      pullback.fst bV g = pullback.fst aU q ≫ yoneda.map h := sqM.lift_fst _ _ _
  have hϖ2 : sqM.lift (pullback.fst aU q ≫ yoneda.map h) (pullback.snd aU q ≫ p) hϖc ≫
      pullback.snd bV g = pullback.snd aU q ≫ p := sqM.lift_snd _ _ _
  have sqRM : IsPullback (pullback.fst aU q)
      (sqM.lift (pullback.fst aU q ≫ yoneda.map h) (pullback.snd aU q ≫ p) hϖc)
      (yoneda.map h) (pullback.fst bV g) := by
    refine IsPullback.of_bot ?_ hϖ1.symm sqM
    rw [hϖ2, ← hcommU]
    exact sqR.paste_vert sq.flip
  have hρc : yoneda.map ψ ≫ aU = a'' ≫ q := ha''q.symm
  have hρ1 : sqR.lift (yoneda.map ψ) a'' hρc ≫ pullback.fst aU q = yoneda.map ψ :=
    sqR.lift_fst _ _ _
  have hρ2 : sqR.lift (yoneda.map ψ) a'' hρc ≫ pullback.snd aU q = a'' :=
    sqR.lift_snd _ _ _
  have hρϖ : sqR.lift (yoneda.map ψ) a'' hρc ≫
      sqM.lift (pullback.fst aU q ≫ yoneda.map h) (pullback.snd aU q ≫ p) hϖc =
      yoneda.map h' ≫ sqM.lift (yoneda.map φ) bV' hκc := by
    refine sqM.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hϖ1, hκ1, ← Category.assoc, hρ1, ← Functor.map_comp,
        ← Functor.map_comp, sqSite.w]
    · rw [Category.assoc, Category.assoc, hϖ2, hκ2, ← Category.assoc, hρ2, ha''p]
  have sqρ : IsPullback (sqR.lift (yoneda.map ψ) a'' hρc) (yoneda.map h')
      (sqM.lift (pullback.fst aU q ≫ yoneda.map h) (pullback.snd aU q ≫ p) hϖc)
      (sqM.lift (yoneda.map φ) bV' hκc) := by
    refine IsPullback.of_right ?_ hρϖ sqRM
    rw [hρ1, hκ1]
    exact (sqSite.map yoneda).flip
  have hρQ : Q.presheaf (sqR.lift (yoneda.map ψ) a'' hρc) :=
    presheaf_of_isPullback B S hS sqρ.flip hκQ
  rw [← hρ2]
  exact MorphismProperty.comp_mem _ _ _ hρQ hr₂Q

/-! ### Part (1) of Tag 04NS -/

/-- In a cartesian square of algebraic spaces over `S` with `f` locally of finite type, the
relative dimension of the base change of `f` at a point of its source is the relative dimension of
`f` at the image of that point.

The square is the one with `p` over `f` and `q` over `g`, so `p : W ⟶ Z` is the base change of
`f : X ⟶ Y` and `q : W ⟶ X` is the projection. Only `X`, `Y` and `Z` are assumed to be algebraic
spaces. -/
@[stacks 04NS "part (1)"]
theorem hasRelativeDimensionAt_iff_of_isPullback' (d : ℕ∞)
    {W X Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hf : IsLocallyOfFiniteType B S hS f)
    (x' : points B S hS W) :
    HasRelativeDimensionAt d B S hS p x' ↔
      HasRelativeDimensionAt d B S hS f (pointsMap B S hS W q x') := by
  classical
  have hEtaleMul := isMultiplicative_presheaf_etale B S hS
  have hEtaleComp : MorphismProperty.IsStableUnderComposition
      ((MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) := hEtaleMul.toIsStableUnderComposition
  have hSurjComp : MorphismProperty.IsStableUnderComposition
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have hSurjInv : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
  have hSurjPre : MorphismProperty.IsStableUnderComposition
      ((MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) := inferInstance
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  obtain ⟨V, bV, hbVs, hbVe⟩ := hY.exists_atlas
  obtain ⟨T₀, cT, hcTs, hcTe⟩ := hX.exists_atlas
  obtain ⟨D, dZ, hdZs, hdZe⟩ := hZ.exists_atlas
  set U := hbVe.rep.pullback (cT ≫ f) with hUdef
  set σ := hbVe.rep.snd (cT ≫ f) with hσdef
  have sqU : IsPullback (hbVe.rep.fst (cT ≫ f)) (yoneda.map σ) bV (cT ≫ f) :=
    hbVe.rep.isPullback (cT ≫ f)
  set h : U ⟶ V := yoneda.preimage (hbVe.rep.fst (cT ≫ f)) with hhdef
  have hmaph : yoneda.map h = hbVe.rep.fst (cT ≫ f) := yoneda.map_preimage _
  set aU : yoneda.obj U ⟶ X := yoneda.map σ ≫ cT with haUdef
  have hcommU : aU ≫ f = yoneda.map h ≫ bV := by
    rw [hmaph, haUdef, Category.assoc]
    exact sqU.w.symm
  set V' := hbVe.rep.pullback (dZ ≫ g) with hV'def
  set δ := hbVe.rep.snd (dZ ≫ g) with hδdef
  set φ : V' ⟶ V := yoneda.preimage (hbVe.rep.fst (dZ ≫ g)) with hφdef
  have hmapφ : yoneda.map φ = hbVe.rep.fst (dZ ≫ g) := yoneda.map_preimage _
  have sqV' : IsPullback (yoneda.map φ) (yoneda.map δ) bV (dZ ≫ g) := by
    rw [hmapφ]
    exact hbVe.rep.isPullback (dZ ≫ g)
  set bV' : yoneda.obj V' ⟶ Z := yoneda.map δ ≫ dZ with hbV'def
  have hδe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map δ) :=
    presheaf_of_isPullback B S hS sqV' hbVe
  have hbV'e : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf bV' :=
    MorphismProperty.comp_mem _ _ _ hδe hdZe
  set U' : BigFppfOver B S hS := Limits.pullback φ h with hU'def
  set h' : U' ⟶ V' := pullback.fst φ h with hh'def
  set ψ : U' ⟶ U := pullback.snd φ h with hψdef
  have sqSite : IsPullback h' ψ φ h := IsPullback.of_hasPullback φ h
  have hcomm'' : (yoneda.map h' ≫ bV') ≫ g = (yoneda.map ψ ≫ aU) ≫ f := by
    simp only [hbV'def, Category.assoc, hcommU]
    rw [← sqV'.w, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, sqSite.w]
  set a'' := sq.lift (yoneda.map h' ≫ bV') (yoneda.map ψ ≫ aU) hcomm'' with ha''def
  have ha''p : a'' ≫ p = yoneda.map h' ≫ bV' := sq.lift_fst _ _ _
  have ha''q : a'' ≫ q = yoneda.map ψ ≫ aU := sq.lift_snd _ _ _
  have hchart : ∀ Q : MorphismProperty (BigFppfOver B S hS), Q.presheaf.IsStableUnderComposition →
      Q.presheaf bV → Q.presheaf cT → Q.presheaf dZ → Q.presheaf aU ∧ Q.presheaf a'' :=
    fun Q hQ hbV hcT hdZ ↦ by
      have haU : Q.presheaf aU :=
        MorphismProperty.comp_mem _ _ _ (presheaf_of_isPullback B S hS sqU hbV) hcT
      exact ⟨haU, presheaf_of_chartSquare_isPullback B S hS hQ sq hcommU sqV' rfl sqSite
        ha''p ha''q haU hdZ⟩
  obtain ⟨haUe, ha''e⟩ := hchart _ hEtaleComp hbVe hcTe hdZe
  obtain ⟨-, ha''s⟩ := hchart _ hSurjPre hbVs hcTs hdZs
  obtain ⟨u₀, hu₀⟩ := isSurjective_of_presheafSurjective B S hS a'' ha''s x'
  set u' := pointsEquivScheme B S hS U' u₀ with hu'def
  have hback : (pointsEquivScheme B S hS U').symm u' = u₀ := by
    rw [hu'def, Equiv.symm_apply_apply]
  have hψpt : (pointsEquivScheme B S hS U).symm
      ((BigFppfOver.toScheme B S hS).map ψ u') =
      pointsMap B S hS (yoneda.obj U') (yoneda.map ψ) u₀ := by
    refine (pointsEquivScheme B S hS U).injective ?_
    rw [Equiv.apply_symm_apply]
    exact (pointsToScheme_pointsMap_yoneda B S hS ψ u₀).symm
  have hkey : pointsMap B S hS (yoneda.obj U) aU
      ((pointsEquivScheme B S hS U).symm ((BigFppfOver.toScheme B S hS).map ψ u')) =
      pointsMap B S hS W q x' := by
    rw [hψpt, ← pointsMap_comp_apply, ← ha''q, pointsMap_comp_apply, hu₀]
  have hleft : pointsMap B S hS (yoneda.obj U') a''
      ((pointsEquivScheme B S hS U').symm u') = x' := by
    rwa [hback]
  have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
    hf U V aU bV h haUe hbVe hcommU.symm
  have hdim := topologicalKrullDimAt_fiber_eq_of_isPullback
    (sqSite.map (BigFppfOver.toScheme B S hS)).flip u'
  rw [← hkey, ← hleft,
    hasRelativeDimensionAt_pointsMap_iff B S hS d p U' V' a'' bV' h' ha''e hbV'e ha''p.symm u',
    hasRelativeDimensionAt_pointsMap_iff B S hS d f U V aU bV h haUe hbVe hcommU.symm
      ((BigFppfOver.toScheme B S hS).map ψ u'),
    hdim]

end AlgebraicGeometry.Space

end
