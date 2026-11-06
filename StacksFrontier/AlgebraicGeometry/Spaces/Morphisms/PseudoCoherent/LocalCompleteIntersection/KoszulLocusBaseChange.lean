module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.KoszulLocusChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints

/-!
# Base change of the Koszul open subspace

For a commutative triangle `f : X ⟶ Y`, `p : X ⟶ Z`, `q : Y ⟶ Z` of algebraic spaces over a
scheme `S` with `p` and `q` flat and locally of finite presentation, and an arbitrary morphism
`Z' ⟶ Z`, the Koszul locus of the base change `f'` of `f` is the inverse image of the Koszul
locus of `f` under the projection `X' ⟶ X`. Equivalently, the open subspace `U(f')` of Tag 06CA
is the inverse image of `U(f)`.

## Main results

* `AlgebraicGeometry.Space.setOf_koszulAt_pullbackMap`: the identity of Koszul loci as sets of
  points.
* `AlgebraicGeometry.Space.koszulOpenSubspace_pullbackMap`: **Stacks 06CA, part (2)**, the
  identity of the open subspaces themselves.

## Implementation notes

The reduction of the second part of Tag 06CA to the identity of point sets is
`AlgebraicGeometry.Space.koszulOpenSubspace_eq_preimage_of_setOf_koszulAt_eq`, which needs no
hypothesis at all; the content is the identity of point sets, and that is proved here.

The proof is the four-chart construction of the source. A surjective étale chart `W ⟶ Z` of the
common target is chosen first, and the two pullbacks `X ×_Z W` and `Y ×_Z W` are formed; the
remaining two charts are taken of those, so that the chart `U` of `X ×_Z W` and the chart `V` of
`Y ×_Z W` come with morphisms `U ⟶ V ⟶ W` of the site. A surjective étale chart `W' ⟶ Z'`
lifting `W ⟶ Z` is chosen last, and the primed charts are the fibre products `U' = U ×_W W'` and
`V' = V ×_W W'` taken in the site.

Taking the charts of the pullbacks rather than of `X` and `Y` themselves is what makes the
primed charts étale over `X'` and `Y'`: the morphism `yoneda U' ⟶ (X ×_Z W) ×_W W'` is the base
change of `yoneda U ⟶ X ×_Z W` along `yoneda W' ⟶ yoneda W`, hence surjective étale, and
`(X ×_Z W) ×_W W' = X' ×_{Z'} W' ⟶ X'` is the base change of the surjective étale `W' ⟶ Z'`.
Taking the chart of `X` directly would instead require cancelling an étale morphism, which is
not available for a relatively representable property of morphisms of presheaves.

By construction `U' ⟶ U` and `V' ⟶ V` form a cartesian square over `U ⟶ V` in the site, and the
functor to schemes preserves it, so the square of schemes is cartesian; this is the step the
source records as "by construction the diagram is cartesian (in the category of schemes)". The
morphisms `U ⟶ W` and `V ⟶ W` of schemes are flat and locally of finite presentation because
they sit in chart squares of `p` and of `q`, so Tag 06B8 applies to that square in the form
`AlgebraicGeometry.koszulAt_iff_of_isPullback`.

Both sides of the identity are then read on these charts with
`AlgebraicGeometry.Space.koszulAt_iff_koszulAt_chart`: one field-valued point of `yoneda U'`
representing the given point of `|X'|` serves as the pointed-chart datum on the primed side, and
its image along `U' ⟶ U` serves on the unprimed side, the two selected scheme points
corresponding under `U' ⟶ U` because the field of definition is unchanged.

The Koszul property of morphisms of schemes has to be étale local on the source, which is Stacks
069P restricted to étale coverings; it is a statement about morphisms of schemes alone. The tag
`AlgebraicGeometry.Space.koszulOpenSubspace_pullbackMap` discharges it, while the auxiliary
`AlgebraicGeometry.Space.setOf_koszulAt_pullbackMap` keeps it as the hypothesis `hsrc`.

## References

* [Stacks Project, Tag 06CA](https://stacks.math.columbia.edu/tag/06CA)
* [Stacks Project, Tag 06B8](https://stacks.math.columbia.edu/tag/06B8)
* [Stacks Project, Tag 06C4](https://stacks.math.columbia.edu/tag/06C4)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 069P](https://stacks.math.columbia.edu/tag/069P)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

-- Lean v4.35.0: `HasLimit (cospan _ _)` in presheaf categories exceeds the default budget.
set_option synthInstance.maxHeartbeats 200000

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The relative property on morphisms of presheaves induced by a property of morphisms of
schemes stable under base change is again stable under base change. -/
private theorem presheaf_inverseImage_isStableUnderBaseChange (P : MorphismProperty Scheme.{u})
    (hP : P.IsStableUnderBaseChange) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange := by
  have _ : (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS hP
  exact MorphismProperty.relative_isStableUnderBaseChange _

/-- The relative property on morphisms of presheaves induced by a property of morphisms of
schemes stable under composition is again stable under composition. -/
private theorem presheaf_inverseImage_isStableUnderComposition (P : MorphismProperty Scheme.{u})
    (hP : P.IsStableUnderComposition) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition := by
  have _ : (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS hP
  exact MorphismProperty.relative_isStableUnderComposition _

/-- A morphism of schemes whose composite with a second morphism is locally of finite
presentation is locally of finite type. -/
private theorem locallyOfFiniteType_of_comp_eq_of_lfp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    {k : X ⟶ Z} (hk : g ≫ h = k)
    (hlfp : _root_.AlgebraicGeometry.LocallyOfFinitePresentation k) :
    _root_.AlgebraicGeometry.LocallyOfFiniteType g := by
  have : _root_.AlgebraicGeometry.LocallyOfFinitePresentation (g ≫ h) := by rw [hk]; exact hlfp
  have : _root_.AlgebraicGeometry.LocallyOfFiniteType (g ≫ h) := by
    rw [hk]
    have := hlfp
    infer_instance
  exact _root_.AlgebraicGeometry.locallyOfFiniteType_of_comp g h

set_option maxHeartbeats 1000000 in
/-- **The Koszul locus commutes with base change.** In a commutative triangle of algebraic
spaces over `S` with `p : X ⟶ Z` and `q : Y ⟶ Z` flat and locally of finite presentation, the
set of points at which the base change of `f : X ⟶ Y` along an arbitrary `z : Z' ⟶ Z` is Koszul
is the inverse image of the set of points at which `f` is Koszul.

This is the content of the second part of Tag 06CA; the passage from it to the equality of open
subspaces is `AlgebraicGeometry.Space.koszulOpenSubspace_eq_preimage_of_setOf_koszulAt_eq`. -/
theorem setOf_koszulAt_pullbackMap
    (hsrc : MorphismProperty.IsLocalAtSource
      (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
        MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage)
    {X Y Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hZ' : IsAlgebraicSpace B S hS Z')
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hpq : f ≫ q = p)
    (hp : IsFlat B S hS p) (hplfp : IsLocallyOfFinitePresentation B S hS p)
    (hq : IsFlat B S hS q) (hqlfp : IsLocallyOfFinitePresentation B S hS q)
    (z : Z' ⟶ Z) :
    {x' : points B S hS (pullback p z) |
        KoszulAt B S hS (pullback.map p z q z f (𝟙 _) (𝟙 _)
          (by simpa only [Category.comp_id] using hpq.symm) (by simp)) x'} =
      pointsMap B S hS (pullback p z) (pullback.fst p z) ⁻¹'
        {x : points B S hS X | KoszulAt B S hS f x} := by
  classical
  set T := BigFppfOver.toScheme B S hS with hT
  set E := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf with hE
  set R := (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) T).presheaf with hR
  have _ : E.IsStableUnderBaseChange := presheaf_inverseImage_isStableUnderBaseChange B S hS _
    _root_.AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  have _ : R.IsStableUnderBaseChange :=
    presheaf_inverseImage_isStableUnderBaseChange B S hS _ inferInstance
  have _ : E.IsStableUnderComposition := presheaf_inverseImage_isStableUnderComposition B S hS _
    _root_.AlgebraicGeometry.etale_isStableUnderComposition.{u}
  have _ : R.IsStableUnderComposition := presheaf_inverseImage_isStableUnderComposition B S hS _
    _root_.AlgebraicGeometry.surjective_isStableUnderComposition.{u}
  -- The chart `W ⟶ Z` of the common target, and the two pullbacks over it.
  obtain ⟨W, w, hwR, hwE⟩ := hZ.exists_atlas
  set XW := pullback p w with hXWdef
  set pX : XW ⟶ X := pullback.fst p w with hpXdef
  set pW : XW ⟶ yoneda.obj W := pullback.snd p w with hpWdef
  have sqXW : IsPullback pX pW p w := IsPullback.of_hasPullback p w
  set YW := pullback q w with hYWdef
  set qY : YW ⟶ Y := pullback.fst q w with hqYdef
  set qW : YW ⟶ yoneda.obj W := pullback.snd q w with hqWdef
  have sqYW : IsPullback qY qW q w := IsPullback.of_hasPullback q w
  have hWalg : IsAlgebraicSpace B S hS (yoneda.obj W) := isAlgebraicSpace_yoneda B S hS W
  have hXW : IsAlgebraicSpace B S hS XW := isAlgebraicSpace_pullback B S hS p w hX hWalg hZ
  have hYW : IsAlgebraicSpace B S hS YW := isAlgebraicSpace_pullback B S hS q w hY hWalg hZ
  have hpXE : E pX := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqXW.flip hwE
  have hqYE : E qY := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqYW.flip hwE
  set fW : XW ⟶ YW := sqYW.lift (pX ≫ f) pW (by rw [Category.assoc, hpq]; exact sqXW.w)
    with hfWdef
  have hfWY : fW ≫ qY = pX ≫ f := sqYW.lift_fst _ _ _
  have hfWW : fW ≫ qW = pW := sqYW.lift_snd _ _ _
  -- The chart `V ⟶ Y ×_Z W` and the chart `U ⟶ X ×_Z W` above it.
  obtain ⟨V, v, hvR, hvE⟩ := hYW.exists_atlas
  obtain ⟨β, hβ⟩ : ∃ β : V ⟶ W, yoneda.map β = v ≫ qW :=
    ⟨yoneda.preimage (v ≫ qW), by simp⟩
  obtain ⟨U, u, α, hucomm, huR, huE⟩ :=
    exists_surjective_etale_presentation_lift B S hS hXW hYW fW V v hvR hvE
  -- The chart `W' ⟶ Z'` lifting `W ⟶ Z`.
  obtain ⟨W', w', γ, hw'comm, hw'R, hw'E⟩ :=
    exists_surjective_etale_presentation_lift B S hS hZ' hZ z W w hwR hwE
  have hupW : u ≫ pW = yoneda.map (α ≫ β) := by
    rw [← hfWW, ← Category.assoc, hucomm, Category.assoc, ← hβ, ← Functor.map_comp]
  -- The primed charts, as fibre products in the site.
  set U' := pullback (α ≫ β) γ with hU'def
  set uU : U' ⟶ U := pullback.fst (α ≫ β) γ with huUdef
  set uW : U' ⟶ W' := pullback.snd (α ≫ β) γ with huWdef
  have sqUsite : IsPullback uU uW (α ≫ β) γ := IsPullback.of_hasPullback _ _
  set V' := pullback β γ with hV'def
  set vV : V' ⟶ V := pullback.fst β γ with hvVdef
  set vW : V' ⟶ W' := pullback.snd β γ with hvWdef
  have sqVsite : IsPullback vV vW β γ := IsPullback.of_hasPullback _ _
  set α' : U' ⟶ V' := sqVsite.lift (uU ≫ α) uW (by rw [Category.assoc]; exact sqUsite.w)
    with hα'def
  have hα'V : α' ≫ vV = uU ≫ α := sqVsite.lift_fst _ _ _
  have hα'W : α' ≫ vW = uW := sqVsite.lift_snd _ _ _
  have sqUV : IsPullback uU α' α vV :=
    IsPullback.of_bot (by rw [hα'W]; exact sqUsite) hα'V.symm sqVsite
  -- The chart of `X'` and the chart of `Y'`.
  set X2 := pullback pW (yoneda.map γ) with hX2def
  set ρX : X2 ⟶ XW := pullback.fst pW (yoneda.map γ) with hρXdef
  set σX : X2 ⟶ yoneda.obj W' := pullback.snd pW (yoneda.map γ) with hσXdef
  have sqX2 : IsPullback ρX σX pW (yoneda.map γ) := IsPullback.of_hasPullback _ _
  set Y2 := pullback qW (yoneda.map γ) with hY2def
  set ρY : Y2 ⟶ YW := pullback.fst qW (yoneda.map γ) with hρYdef
  set σY : Y2 ⟶ yoneda.obj W' := pullback.snd qW (yoneda.map γ) with hσYdef
  have sqY2 : IsPullback ρY σY qW (yoneda.map γ) := IsPullback.of_hasPullback _ _
  set u2 : yoneda.obj U' ⟶ X2 := sqX2.lift (yoneda.map uU ≫ u) (yoneda.map uW) (by
    rw [Category.assoc, hupW, ← Functor.map_comp, ← Functor.map_comp, sqUsite.w]) with hu2def
  have hu2a : u2 ≫ ρX = yoneda.map uU ≫ u := sqX2.lift_fst _ _ _
  have hu2b : u2 ≫ σX = yoneda.map uW := sqX2.lift_snd _ _ _
  set v2 : yoneda.obj V' ⟶ Y2 := sqY2.lift (yoneda.map vV ≫ v) (yoneda.map vW) (by
    rw [Category.assoc, ← hβ, ← Functor.map_comp, ← Functor.map_comp, sqVsite.w]) with hv2def
  have hv2a : v2 ≫ ρY = yoneda.map vV ≫ v := sqY2.lift_fst _ _ _
  have hv2b : v2 ≫ σY = yoneda.map vW := sqY2.lift_snd _ _ _
  have sqU2 : IsPullback (yoneda.map uU) u2 u ρX :=
    IsPullback.of_bot (by rw [hu2b, hupW]; exact sqUsite.map yoneda) hu2a.symm sqX2
  have sqV2 : IsPullback (yoneda.map vV) v2 v ρY :=
    IsPullback.of_bot (by rw [hv2b, ← hβ]; exact sqVsite.map yoneda) hv2a.symm sqY2
  have hu2E : E u2 := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqU2 huE
  have hu2R : R u2 := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqU2 huR
  have hv2E : E v2 := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqV2 hvE
  -- The projections of the base changes onto `X'` and `Y'`.
  set X' := pullback p z with hX'def
  set pr : X' ⟶ X := pullback.fst p z with hprdef
  set pz : X' ⟶ Z' := pullback.snd p z with hpzdef
  have sqX' : IsPullback pr pz p z := IsPullback.of_hasPullback p z
  set Y' := pullback q z with hY'def
  set prY : Y' ⟶ Y := pullback.fst q z with hprYdef
  set qz : Y' ⟶ Z' := pullback.snd q z with hqzdef
  have sqY' : IsPullback prY qz q z := IsPullback.of_hasPullback q z
  have hX2X : IsPullback (ρX ≫ pX) σX p (yoneda.map γ ≫ w) := sqX2.paste_horiz sqXW
  have hY2Y : IsPullback (ρY ≫ qY) σY q (yoneda.map γ ≫ w) := sqY2.paste_horiz sqYW
  set ρ' : X2 ⟶ X' := sqX'.lift (ρX ≫ pX) (σX ≫ w') (by
    simp only [Category.assoc]; rw [hw'comm]
    simpa only [Category.assoc] using hX2X.w) with hρ'def
  have hρ'a : ρ' ≫ pr = ρX ≫ pX := sqX'.lift_fst _ _ _
  have hρ'b : ρ' ≫ pz = σX ≫ w' := sqX'.lift_snd _ _ _
  set ρ'Y : Y2 ⟶ Y' := sqY'.lift (ρY ≫ qY) (σY ≫ w') (by
    simp only [Category.assoc]; rw [hw'comm]
    simpa only [Category.assoc] using hY2Y.w) with hρ'Ydef
  have hρ'Ya : ρ'Y ≫ prY = ρY ≫ qY := sqY'.lift_fst _ _ _
  have hρ'Yb : ρ'Y ≫ qz = σY ≫ w' := sqY'.lift_snd _ _ _
  have sqρ' : IsPullback ρ' σX pz w' :=
    IsPullback.of_right (by rw [hρ'a, hw'comm]; exact hX2X) hρ'b sqX'
  have sqρ'Y : IsPullback ρ'Y σY qz w' :=
    IsPullback.of_right (by rw [hρ'Ya, hw'comm]; exact hY2Y) hρ'Yb sqY'
  have hρ'E : E ρ' := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqρ'.flip hw'E
  have hρ'R : R ρ' := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqρ'.flip hw'R
  have hρ'YE : E ρ'Y := MorphismProperty.IsStableUnderBaseChange.of_isPullback sqρ'Y.flip hw'E
  set u' : yoneda.obj U' ⟶ X' := u2 ≫ ρ' with hu'def
  set v' : yoneda.obj V' ⟶ Y' := v2 ≫ ρ'Y with hv'def
  have hu'E : E u' := MorphismProperty.comp_mem E _ _ hu2E hρ'E
  have hu'R : R u' := MorphismProperty.comp_mem R _ _ hu2R hρ'R
  have hv'E : E v' := MorphismProperty.comp_mem E _ _ hv2E hρ'YE
  -- The base change of `f`.
  set f' : X' ⟶ Y' := pullback.map p z q z f (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id] using hpq.symm) (by simp) with hf'def
  have hf'a : f' ≫ prY = pr ≫ f := by rw [hf'def, hprYdef, pullback.lift_fst]
  have hf'b : f' ≫ qz = pz := by
    rw [hf'def, hqzdef, pullback.lift_snd, Category.comp_id]
  -- The chart squares.
  have hchartU : yoneda.map α ≫ (v ≫ qY) = (u ≫ pX) ≫ f := by
    have h1 : (u ≫ fW) ≫ qY = (yoneda.map α ≫ v) ≫ qY := by rw [hucomm]
    simp only [Category.assoc, hfWY] at h1 ⊢
    exact h1.symm
  have e1 : v2 ≫ ρ'Y ≫ prY = yoneda.map vV ≫ v ≫ qY := by
    rw [hρ'Ya, ← Category.assoc, hv2a, Category.assoc]
  have e2 : u2 ≫ ρ' ≫ pr = yoneda.map uU ≫ u ≫ pX := by
    rw [hρ'a, ← Category.assoc, hu2a, Category.assoc]
  have e3 : v2 ≫ ρ'Y ≫ qz = yoneda.map vW ≫ w' := by
    rw [hρ'Yb, ← Category.assoc, hv2b]
  have e4 : u2 ≫ ρ' ≫ pz = yoneda.map uW ≫ w' := by
    rw [hρ'b, ← Category.assoc, hu2b]
  have e2f : u2 ≫ ρ' ≫ pr ≫ f = yoneda.map uU ≫ u ≫ pX ≫ f := by
    simpa only [Category.assoc] using congrArg (fun k => k ≫ f) e2
  have hu'pr : u' ≫ pr = yoneda.map uU ≫ (u ≫ pX) := by
    rw [hu'def, Category.assoc, e2]
  have hcomm' : yoneda.map α' ≫ v' = u' ≫ f' := by
    refine sqY'.hom_ext ?_ ?_
    · calc (yoneda.map α' ≫ v') ≫ prY
          = yoneda.map α' ≫ v2 ≫ ρ'Y ≫ prY := by
            rw [hv'def]; simp only [Category.assoc]
        _ = yoneda.map (α' ≫ vV) ≫ v ≫ qY := by
            rw [e1, Functor.map_comp]; simp only [Category.assoc]
        _ = yoneda.map uU ≫ u ≫ pX ≫ f := by
            rw [hα'V, Functor.map_comp, Category.assoc, hchartU]
            simp only [Category.assoc]
        _ = (u' ≫ f') ≫ prY := by
            rw [hu'def]
            simp only [Category.assoc]
            rw [hf'a, e2f]
    · calc (yoneda.map α' ≫ v') ≫ qz
          = yoneda.map α' ≫ v2 ≫ ρ'Y ≫ qz := by
            rw [hv'def]; simp only [Category.assoc]
        _ = yoneda.map (α' ≫ vW) ≫ w' := by
            rw [e3, Functor.map_comp]; simp only [Category.assoc]
        _ = yoneda.map uW ≫ w' := by rw [hα'W]
        _ = (u' ≫ f') ≫ qz := by
            rw [hu'def]
            simp only [Category.assoc]
            rw [hf'b, e4]
  -- Flatness and local finite presentation of the chart morphisms to `W`.
  have hEuPX : E (u ≫ pX) := MorphismProperty.comp_mem E _ _ huE hpXE
  have hEvQY : E (v ≫ qY) := MorphismProperty.comp_mem E _ _ hvE hqYE
  have hchartP : yoneda.map (α ≫ β) ≫ w = (u ≫ pX) ≫ p := by
    rw [← hupW, Category.assoc, Category.assoc, sqXW.w]
  have hchartQ : yoneda.map β ≫ w = (v ≫ qY) ≫ q := by
    rw [hβ, Category.assoc, Category.assoc, sqYW.w]
  have hflatU : _root_.AlgebraicGeometry.Flat (T.map (α ≫ β)) :=
    hp U W (u ≫ pX) w (α ≫ β) hEuPX hwE hchartP
  have hflatV : _root_.AlgebraicGeometry.Flat (T.map β) := hq V W (v ≫ qY) w β hEvQY hwE hchartQ
  have hlfpU : _root_.AlgebraicGeometry.LocallyOfFinitePresentation (T.map (α ≫ β)) :=
    hplfp U W (u ≫ pX) w (α ≫ β) hEuPX hwE hchartP
  have hlfpV : _root_.AlgebraicGeometry.LocallyOfFinitePresentation (T.map β) :=
    hqlfp V W (v ≫ qY) w β hEvQY hwE hchartQ
  -- The cartesian square of schemes.
  have sqUT : IsPullback (T.map uU) (T.map uW) (T.map (α ≫ β)) (T.map γ) := sqUsite.map T
  have sqVT : IsPullback (T.map vV) (T.map vW) (T.map β) (T.map γ) := sqVsite.map T
  have _ := hflatU
  have _ := hflatV
  have _ := hlfpU
  have _ := hlfpV
  have hTαβ : T.map α ≫ T.map β = T.map (α ≫ β) := (T.map_comp α β).symm
  have hlftα : _root_.AlgebraicGeometry.LocallyOfFiniteType (T.map α) :=
    locallyOfFiniteType_of_comp_eq_of_lfp (T.map α) (T.map β) hTαβ hlfpU
  have hlfpuW : _root_.AlgebraicGeometry.LocallyOfFinitePresentation (T.map uW) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) sqUT inferInstance
  have hlfpvW : _root_.AlgebraicGeometry.LocallyOfFinitePresentation (T.map vW) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @_root_.AlgebraicGeometry.LocallyOfFinitePresentation.{u}) sqVT inferInstance
  have hlftα' : _root_.AlgebraicGeometry.LocallyOfFiniteType (T.map α') :=
    locallyOfFiniteType_of_comp_eq_of_lfp (T.map α') (T.map vW)
      (by rw [← T.map_comp, hα'W]) hlfpuW
  -- Algebraicity of the base-changed spaces.
  have hX'alg : IsAlgebraicSpace B S hS X' := isAlgebraicSpace_pullback B S hS p z hX hZ' hZ
  have hY'alg : IsAlgebraicSpace B S hS Y' := isAlgebraicSpace_pullback B S hS q z hY hZ' hZ
  -- The pointwise comparison.
  have hu'surj : Function.Surjective (pointsMap B S hS (yoneda.obj U') u') :=
    surjective_pointsMap_of_presheaf_surjective B S hS u' hu'R
  ext x'
  obtain ⟨x0, hx0⟩ := hu'surj x'
  obtain ⟨pt, hpt⟩ := Quot.exists_rep x0
  set c' : EtaleChartAtPoint B S hS f' x' :=
    { U := U', V := V', a := u', b := v', h := α', a_etale := hu'E, b_etale := hv'E
      comm := hcomm'
      representative := pt
      point := IsLocalRing.closedPoint pt.carrier
      maps_to := by rw [show pt.class B S hS (yoneda.obj U') = x0 from hpt]; exact hx0 } with hc'
  set c : EtaleChartAtPoint B S hS f (pointsMap B S hS X' pr x') :=
    { U := U, V := V, a := u ≫ pX, b := v ≫ qY, h := α, a_etale := hEuPX, b_etale := hEvQY
      comm := hchartU
      representative := FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map uU) pt
      point := IsLocalRing.closedPoint pt.carrier
      maps_to := by
        rw [show (FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map uU) pt).class B S hS
            (yoneda.obj U) =
          pointsMap B S hS (yoneda.obj U') (yoneda.map uU) (pt.class B S hS (yoneda.obj U'))
          from rfl, show pt.class B S hS (yoneda.obj U') = x0 from hpt,
          ← Function.comp_apply (f := pointsMap B S hS (yoneda.obj U) (u ≫ pX)),
          ← pointsMap_comp, ← hu'pr, pointsMap_comp, Function.comp_apply, hx0] } with hc
  have hsrcpt : c.sourcePoint B S hS = (T.map uU).base (c'.sourcePoint B S hS) := by
    show (T.map (pt.value ≫ uU)).base (IsLocalRing.closedPoint pt.carrier) =
      (T.map uU).base ((T.map pt.value).base (IsLocalRing.closedPoint pt.carrier))
    rw [T.map_comp]
    rfl
  show KoszulAt B S hS f' x' ↔ KoszulAt B S hS f (pointsMap B S hS X' pr x')
  rw [koszulAt_iff_koszulAt_chart B S hS hsrc hX'alg hY'alg f' x' c' hlftα',
    koszulAt_iff_koszulAt_chart B S hS hsrc hX hY f _ c hlftα,
    show c'.h = α' from rfl, show c.h = α from rfl, hsrcpt]
  exact _root_.AlgebraicGeometry.koszulAt_iff_of_isPullback (T.map α) (T.map (α ≫ β)) (T.map β)
    hTαβ (T.map γ) (T.map α') sqUT sqVT (by rw [← T.map_comp, ← T.map_comp, hα'V])
    (by rw [← T.map_comp, hα'W]) _

/-- **Stacks 06CA, part (2).** The open subspace `U(f')` of the Koszul points of the base change
`f'` of `f` along an arbitrary `Z' ⟶ Z` is the inverse image of `U(f)` under the projection
`X' ⟶ X`.

The one input from the theory of schemes is that the Koszul property of morphisms of schemes is
local on the source for the étale topology — Stacks 069P restricted to étale coverings. -/
@[stacks 06CA "part (2): base change of the Koszul open subspace"]
theorem koszulOpenSubspace_pullbackMap
    {X Y Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hZ' : IsAlgebraicSpace B S hS Z')
    (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hpq : f ≫ q = p)
    (hp : IsFlat B S hS p) (hplfp : IsLocallyOfFinitePresentation B S hS p)
    (hq : IsFlat B S hS q) (hqlfp : IsLocallyOfFinitePresentation B S hS q)
    (z : Z' ⟶ Z) :
    koszulOpenSubspace B S hS (pullback p z)
        (pullback.map p z q z f (𝟙 _) (𝟙 _)
          (by simpa only [Category.comp_id] using hpq.symm) (by simp)) =
      (koszulOpenSubspace B S hS X f).preimage (pullback.fst p z) :=
  koszulOpenSubspace_eq_preimage_of_setOf_koszulAt_eq B S hS f _ (pullback.fst p z)
    (setOf_koszulAt_pullbackMap B S hS
      _root_.AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale
      hX hY hZ hZ' f p q hpq hp hplfp hq hqlfp z)

end AlgebraicGeometry.Space

end
