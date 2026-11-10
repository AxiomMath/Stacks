module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFiniteAffineChart
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleLocalTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryChartFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenChartCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackWeaklyAssociated

/-!
# A finite affine chart diagram at a point with finite fibre, trivializing an invertible module

Let `g : Z ⟶ Y` be a proper morphism of decent algebraic spaces over `S`, let `η ∈ |Y|` have
finite fibre, and let `ℒ` be an invertible `𝒪_Y`-module. This file refines
`AlgebraicGeometry.Space.exists_finite_affine_chartDiagram`: the cartesian square of affine
étale charts of `g` with finite vertical morphism, whose target chart has exactly one point `e`
over `η` with `Spec κ(e) ⟶ Y` a monomorphism, can be chosen so that moreover `ℒ` is free over
the target chart.

The square of `AlgebraicGeometry.Space.exists_finite_affine_chartDiagram` is restricted to a
basic open `D(h)` of its target chart containing `e` over which `ℒ` is free
(`AlgebraicGeometry.Space.exists_basicOpen_freeGenerator`) and to the preimage of `D(h)` in its
source chart. Restricting to an open and its preimage keeps the square cartesian
(`AlgebraicGeometry.Space.isPullback_openSubHomOfRestrict`), the charts affine and the vertical
morphism finite; `e` stays the only point over `η`, and its residue field does not change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The point of `X` under a point of the open restriction `openChart U O` of an étale chart `U`
is the point under its image in `U`. -/
theorem chartSchemeToPoints_openChart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B S hS X)
    (O : ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj U)).Opens)
    (x : chartScheme (openChart B S hS X U O)) :
    chartSchemeToPoints B S hS X (openChart B S hS X U O) x =
      chartSchemeToPoints B S hS X U (O.ι.base x) := by
  let d' : ChartDiagram B S hS X X (𝟙 X) :=
    { U := openChart B S hS X U O
      V := U
      g := openSubHom _ O
      comm := Category.comp_id _ }
  have hx : ((BigFppfOver.toScheme B S hS).map d'.g).base x = O.ι.base x := by
    change ((BigFppfOver.toScheme B S hS).map (openSubHom _ O)).base x = _
    rw [toScheme_map_openSubHom]
    rfl
  rw [← hx, chartSchemeToPoints_map_chartDiagram B S hS d' x, pointsMap_id]
  rfl

/-- If the field-valued point of `X` at the image in `U` of a point `x` of the open restriction
`openChart U O` is a monomorphism, then so is the field-valued point at `x`. -/
theorem mono_fieldMorphism_openChart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : SmallEtale B S hS X)
    (O : ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X).obj U)).Opens)
    (x : chartScheme (openChart B S hS X U O))
    (hmono : Mono (fieldMorphism B S hS X (chartSchemeFieldValuedPoint B S hS X U (O.ι.base x)))) :
    Mono (fieldMorphism B S hS X
      (chartSchemeFieldValuedPoint B S hS X (openChart B S hS X U O) x)) := by
  let d' : ChartDiagram B S hS X X (𝟙 X) :=
    { U := openChart B S hS X U O
      V := U
      g := openSubHom _ O
      comm := Category.comp_id _ }
  have hx : ((BigFppfOver.toScheme B S hS).map d'.g).base x = O.ι.base x := by
    change ((BigFppfOver.toScheme B S hS).map (openSubHom _ O)).base x = _
    rw [toScheme_map_openSubHom]
    rfl
  obtain ⟨k, hk, -, hk₂⟩ := exists_siteHom_chartSchemeFieldValuedPoint B S hS d' x
  have hm : Mono (fieldMorphism B S hS X (chartSchemeFieldValuedPoint B S hS X U
      (((BigFppfOver.toScheme B S hS).map d'.g).base x))) := by
    rw [hx]
    exact hmono
  have hkmono : Mono k := by
    have : Mono ((BigFppfOver.toScheme B S hS).map k) := by
      change Mono (B.inclusion.map k.left)
      rw [hk]
      have : _root_.AlgebraicGeometry.IsOpenImmersion
          ((BigFppfOver.toScheme B S hS).map d'.g) := by
        change _root_.AlgebraicGeometry.IsOpenImmersion
          ((BigFppfOver.toScheme B S hS).map (openSubHom _ O))
        rw [toScheme_map_openSubHom]
        exact Scheme.Opens.instIsOpenImmersionι _
      rw [CommRingCat.ofHom_hom]
      exact (inferInstance : Mono (Spec.map
        (Scheme.Hom.residueFieldMap ((BigFppfOver.toScheme B S hS).map d'.g) x)))
    exact (BigFppfOver.toScheme B S hS).mono_of_mono_map this
  rw [← Category.comp_id (fieldMorphism B S hS X _), ← hk₂]
  infer_instance

/-- **A finite affine chart diagram at a point with finite fibre, over which a given invertible
module is free.** -/
theorem exists_finite_affine_chartDiagram_free {Z Y : AlgebraicSpaces B S hS}
    (hZdec : IsDecentSpace B S hS Z.1) (hYdec : IsDecentSpace B S hS Y.1)
    (g : Z ⟶ Y) (hg : IsProper B S hS g.hom) (η : points B S hS Y.1)
    (hfin : {z : points B S hS Z.1 | pointsMap B S hS Z.1 g.hom z = η}.Finite)
    (L : Modules.{u, u} B S hS Y.1 Y.2) (hL : IsInvertibleModule (B := B) Y L) :
    ∃ (d : ChartDiagram B S hS Z.1 Y.1 g.hom) (e : chartScheme d.V),
      IsPullback d.U.1.hom (yoneda.map d.g) g.hom d.V.1.hom ∧
      IsAffine (chartScheme d.V) ∧ IsAffine (chartScheme d.U) ∧
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map d.g) ∧
      chartSchemeToPoints B S hS Y.1 d.V e = η ∧
      (∀ e' : chartScheme d.V, chartSchemeToPoints B S hS Y.1 d.V e' = η → e' = e) ∧
      Mono (fieldMorphism B S hS Y.1 (chartSchemeFieldValuedPoint B S hS Y.1 d.V e)) ∧
      ∃ eM : (W : SmallEtale B S hS Y.1) → (W ⟶ d.V) → L.val.obj (op W),
        (∀ (W W' : SmallEtale B S hS Y.1) (k : W ⟶ d.V) (h : W' ⟶ W),
          (L.val.map h.op).hom (eM W k) = eM W' (h ≫ k)) ∧
        ∀ (W : SmallEtale B S hS Y.1) (k : W ⟶ d.V),
          Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W ↦ r • eM W k := by
  obtain ⟨d₀, e₀, hpb₀, hV₀, hU₀, hfin₀, he₀, huniq₀, hmono₀⟩ :=
    exists_finite_affine_chartDiagram B S hS hZdec hYdec g hg η hfin
  obtain ⟨h, heh, eM, hcompat, hbij⟩ := exists_basicOpen_freeGenerator B S hS Y L hL d₀.V hV₀ e₀
  let O := (chartScheme d₀.V).basicOpen h
  let O' := (BigFppfOver.toScheme B S hS).map d₀.g ⁻¹ᵁ O
  have hsq := isPullback_openSubHomOfRestrict d₀.g O
  let d : ChartDiagram B S hS Z.1 Y.1 g.hom :=
    { U := openChart B S hS Z.1 d₀.U O'
      V := openChart B S hS Y.1 d₀.V O
      g := openSubHomOfRestrict d₀.g O
      comm := by
        change (yoneda.map (openSubHom _ O') ≫ d₀.U.1.hom) ≫ g.hom =
          yoneda.map (openSubHomOfRestrict d₀.g O) ≫ (yoneda.map (openSubHom _ O) ≫ d₀.V.1.hom)
        rw [Category.assoc, d₀.comm, ← Category.assoc, ← Functor.map_comp, hsq.w,
          Functor.map_comp, Category.assoc] }
  have hpb : IsPullback d.U.1.hom (yoneda.map d.g) g.hom d.V.1.hom :=
    (hsq.map yoneda).paste_horiz hpb₀
  have hpts : ∀ x : chartScheme d.V,
      chartSchemeToPoints B S hS Y.1 d.V x = chartSchemeToPoints B S hS Y.1 d₀.V (O.ι.base x) :=
    chartSchemeToPoints_openChart B S hS d₀.V O
  let e : chartScheme d.V := ⟨e₀, heh⟩
  refine ⟨d, e, hpb, isAffine_chartScheme_openChart_basicOpen B S hS Y.1 d₀.V hV₀ h, ?_, ?_,
    ?_, ?_, mono_fieldMorphism_openChart B S hS d₀.V O e hmono₀, ⟨eM, hcompat, hbij⟩⟩
  · have hO' : O' = (chartScheme d₀.U).basicOpen
        (((BigFppfOver.toScheme B S hS).map d₀.g).appTop h) := Scheme.preimage_basicOpen _ _
    exact (show IsAffineOpen O' from hO' ▸ (isAffineOpen_top _).basicOpen _)
  · change _root_.AlgebraicGeometry.IsFinite (B.inclusion.map (openSubSchemeHomOfRestrict d₀.g O))
    rw [inclusion_map_openSubSchemeHomOfRestrict]
    have key : ∀ {X' Y' : Scheme.{u}} (f : X' ⟶ Y') [_root_.AlgebraicGeometry.IsFinite f]
        (U : Y'.Opens), _root_.AlgebraicGeometry.IsFinite (f ∣_ U) := fun _ _ => inferInstance
    exact @key _ _ _ hfin₀ O
  · exact (hpts e).trans he₀
  · intro e' he'
    rw [hpts] at he'
    exact Subtype.ext (huniq₀ _ he')

end AlgebraicGeometry.Space

end
