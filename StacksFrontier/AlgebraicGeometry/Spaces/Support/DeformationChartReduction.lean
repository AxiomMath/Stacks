module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Diagram
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.DeformationDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Reducing a flat deformation of algebraic spaces to diagrams of schemes

A flat deformation diagram of algebraic spaces admits compatible surjective étale scheme
charts of all six of its corners: a chart of the ambient base lifts to a chart of the ambient
target and then to a chart of the ambient source, and each of the three thickenings pulls back
along the corresponding chart to a thickening of schemes. The resulting diagram of schemes is a
flat deformation diagram of schemes, so a property of morphisms which is étale local on source
and target is invariant under the deformation of algebraic spaces as soon as it is invariant
under every flat deformation of schemes.

## Main results

* `AlgebraicGeometry.Space.exists_thickening_chart_pullback`: a thickening of algebraic spaces
  pulls back along a scheme chart of the ambient space to a thickening of schemes.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_scheme_diagrams`: the scheme-level
  invariance implies the algebraic-space-level invariance.

## Implementation notes

The chart condition on a morphism of algebraic spaces is
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ; the proof passes to the
equivalent one-chart condition
`AlgebraicGeometry.Space.HoldsOnSurjectiveEtaleChart` through
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart`, which is where étale
locality of the property is used. The charts themselves come from
`AlgebraicGeometry.Space.exists_surjective_etale_presentation_lift` (Stacks 02X1) applied
twice, and the thickenings of the unprimed corners from
`exists_thickening_chart_pullback` below, which is the representability of the thickening
inclusion together with surjectivity of its map on points.

Both pasting arguments identifying the charts of the unprimed corners as fibre products run in
the presheaf category and are transported to the site by faithfulness of Yoneda, so no
fibre-product object in the site has to be chosen.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

/-- A thickening of algebraic spaces pulls back along any scheme chart of the ambient space to
a thickening of schemes: the inclusion is representable with closed-immersion base changes, and
it is surjective on points, hence its base changes are surjective. -/
theorem exists_thickening_chart_pullback (T : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : T.Contains S) {X X' : AlgebraicSpaces T S hS} (i : X ⟶ X') [Mono i.hom]
    (hi : IsThickening T S hS X' (Subfunctor.range i.hom))
    (U : BigFppfOver T S hS) (q : yoneda.obj U ⟶ X'.1) :
    ∃ (U₀ : BigFppfOver T S hS) (j : U₀ ⟶ U) (p : yoneda.obj U₀ ⟶ X.1),
      IsPullback p (yoneda.map j) i.hom q ∧
        Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme T S hS).map j) := by
  have hpoints : Function.Surjective (pointsMap T S hS X.1 i.hom) := by
    intro x
    obtain ⟨y, hy⟩ := hi.2 x
    let t := Subfunctor.toRange i.hom
    have : IsIso t := inferInstance
    let z := pointsMap T S hS (Subfunctor.range i.hom).toFunctor (inv t) y
    have hz : pointsMap T S hS X.1 t z = y := by
      have h := congrFun (pointsMap_comp T S hS
        (F := (Subfunctor.range i.hom).toFunctor) (inv t) t) y
      simp only [Function.comp_apply] at h
      rw [show z = pointsMap T S hS (Subfunctor.range i.hom).toFunctor (inv t) y from rfl,
        ← h, IsIso.inv_hom_id, pointsMap_id]
      rfl
    refine ⟨z, ?_⟩
    calc
      pointsMap T S hS X.1 i.hom z =
          pointsMap T S hS X.1 (t ≫ (Subfunctor.range i.hom).ι) z :=
        congrArg (fun k => pointsMap T S hS X.1 k z) (Subfunctor.toRange_ι i.hom).symm
      _ = pointsMap T S hS (Subfunctor.range i.hom).toFunctor (Subfunctor.range i.hom).ι
            (pointsMap T S hS X.1 t z) := by
          have h := congrFun (pointsMap_comp T S hS (F := X.1) t
            (Subfunctor.range i.hom).ι) z
          simpa only [Function.comp_apply] using h
      _ = pointsMap T S hS (Subfunctor.range i.hom).toFunctor
            (Subfunctor.range i.hom).ι y := by rw [hz]
      _ = x := hy
  let Pclosed := MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme T S hS))
  have hiClosed : Pclosed i.hom := by
    rw [← Subfunctor.toRange_ι i.hom]
    exact MorphismProperty.RespectsIso.precomp Pclosed
      (Subfunctor.toRange i.hom) (Subfunctor.range i.hom).ι hi.1.2
  have hirep : yoneda.relativelyRepresentable i.hom := by
    rw [← Subfunctor.toRange_ι i.hom]
    exact MorphismProperty.comp_mem yoneda.relativelyRepresentable
      (Subfunctor.toRange i.hom) (Subfunctor.range i.hom).ι
      (Functor.relativelyRepresentable.of_isIso yoneda (Subfunctor.toRange i.hom))
      hi.1.2.rep
  have hsurj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme T S hS)).presheaf i.hom :=
    (surjective_iff_pointsMap_surjective T S hS X.property X'.property i.hom hirep).2 hpoints
  refine ⟨hirep.pullback q, hirep.snd q, hirep.fst q, hirep.isPullback q,
    hiClosed.property q (hirep.fst q) (hirep.snd q) (hirep.isPullback q),
    (hsurj.property q (hirep.fst q) (hirep.snd q) (hirep.isPullback q)).surj⟩

/-- Two compatible charts of the primed corners, which pull back to charts of the unprimed ones
along the thickenings, are joined by a morphism of charts of the unprimed corners. -/
private theorem exists_chart_lift {C : Type (u + 1)} [Category.{u} C] {X Y X' Y' : Cᵒᵖ ⥤ Type u}
    {W₀ V₀ W' V' : C} (pX : yoneda.obj W₀ ⟶ X) (pY : yoneda.obj V₀ ⟶ Y)
    (qX : yoneda.obj W' ⟶ X') (qY : yoneda.obj V' ⟶ Y') (jX : W₀ ⟶ W') (jY : V₀ ⟶ V')
    (β : W' ⟶ V') (iX : X ⟶ X') (iY : Y ⟶ Y') (f : X ⟶ Y) (f' : X' ⟶ Y')
    (hpbX : IsPullback pX (yoneda.map jX) iX qX) (hpbY : IsPullback pY (yoneda.map jY) iY qY)
    (hcomm : iX ≫ f' = f ≫ iY) (hβ : qX ≫ f' = yoneda.map β ≫ qY) :
    ∃ f₀ : W₀ ⟶ V₀, yoneda.map f₀ ≫ pY = pX ≫ f ∧ f₀ ≫ jY = jX ≫ β := by
  have hw : pX ≫ f ≫ iY = yoneda.map (jX ≫ β) ≫ qY := by
    rw [← hcomm, ← Category.assoc, hpbX.w, Category.assoc, hβ, Functor.map_comp, Category.assoc]
  refine ⟨yoneda.preimage (hpbY.lift (pX ≫ f) (yoneda.map (jX ≫ β)) hw), ?_, ?_⟩
  · rw [yoneda.map_preimage]
    exact hpbY.lift_fst _ _ _
  · apply yoneda.map_injective
    rw [yoneda.map_comp, yoneda.map_preimage]
    simpa only [Category.assoc, ← Functor.map_comp] using hpbY.lift_snd _ _ hw

/-- A square of charts of the primed corners which is cartesian over the thickening of the base,
together with a compatible morphism of charts of the unprimed corners, gives a pullback square
of charts. -/
private theorem isPullback_chart_of_paste {C : Type (u + 1)} [Category.{u} C]
    {Y B Y' B' : Cᵒᵖ ⥤ Type u} {V₀ V' U₀ U' : C} (pY : yoneda.obj V₀ ⟶ Y) (pB : yoneda.obj U₀ ⟶ B)
    (qY : yoneda.obj V' ⟶ Y') (qB : yoneda.obj U' ⟶ B') (iY : Y ⟶ Y') (iB : B ⟶ B')
    (g : Y ⟶ B) (g' : Y' ⟶ B') (jY : V₀ ⟶ V') (jB : U₀ ⟶ U') (g₀ : V₀ ⟶ U₀) (α : V' ⟶ U')
    (hpbY : IsPullback pY (yoneda.map jY) iY qY) (hpbB : IsPullback pB (yoneda.map jB) iB qB)
    (hout : IsPullback iY g g' iB) (hg : yoneda.map g₀ ≫ pB = pY ≫ g)
    (hα : qY ≫ g' = yoneda.map α ≫ qB) (hcomm : g₀ ≫ jB = jY ≫ α) : IsPullback jY g₀ α jB := by
  apply IsPullback.of_map_of_faithful yoneda
  have h := hpbY.flip.paste_vert hout
  rw [← hg, hα] at h
  exact h.of_bot (by rw [← Functor.map_comp, ← Functor.map_comp, hcomm]) hpbB.flip

/-- An étale-local property of morphisms of schemes is invariant under a flat deformation of
algebraic spaces as soon as it is invariant under every flat deformation of schemes. -/
theorem holdsOnEveryEtaleChart_iff_of_scheme_diagrams (T : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : T.Contains S) (D : FlatDeformationDiagram T S hS) (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hSchemes : ∀ E : Stacks.Thickenings.FlatDeformationDiagram.{u}, P E.f ↔ P E.f') :
    HoldsOnEveryEtaleChart T S hS P D.f.hom ↔ HoldsOnEveryEtaleChart T S hS P D.f'.hom := by
  let Tscheme := BigFppfOver.toScheme T S hS
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      Tscheme).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange T S hS inferInstance
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      Tscheme).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange T S hS inferInstance
  have : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      Tscheme).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      Tscheme).presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  obtain ⟨U', qB', hqB'surj, hqB'etale⟩ := D.B'.property.exists_atlas
  obtain ⟨V', qY', α, hqYcomm, hqYsurj, hqYetale⟩ :=
    exists_surjective_etale_presentation_lift T S hS D.Y'.property D.B'.property D.g'.hom
      U' qB' hqB'surj hqB'etale
  obtain ⟨W', qX', β, hqXcomm, hqXsurj, hqXetale⟩ :=
    exists_surjective_etale_presentation_lift T S hS D.X'.property D.Y'.property D.f'.hom
      V' qY' hqYsurj hqYetale
  have := D.iB_mono
  obtain ⟨U₀, jB, pB, hpbB, hBthick⟩ :=
    exists_thickening_chart_pullback T S hS D.iB D.iB_thickening U' qB'
  have := D.iY_mono
  obtain ⟨V₀, jY, pY, hpbY, hYthick⟩ :=
    exists_thickening_chart_pullback T S hS D.iY D.iY_thickening V' qY'
  have := D.iX_mono
  obtain ⟨W₀, jX, pX, hpbX, hXthick⟩ :=
    exists_thickening_chart_pullback T S hS D.iX D.iX_thickening W' qX'
  have hqY₀surj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf pY :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbY.flip hqYsurj
  have hqY₀etale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf pY :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbY.flip hqYetale
  have hqX₀surj : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf pX :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbX.flip hqXsurj
  have hqX₀etale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Tscheme).presheaf pX :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbX.flip hqXetale
  -- The charts of the unprimed corners, compatible with the charts of the primed ones.
  obtain ⟨g₀, hg₀pB, hg₀jB⟩ := exists_chart_lift pY pB qY' qB' jY jB α D.iY.hom D.iB.hom D.g.hom
    D.g'.hom hpbY hpbB (congrArg (fun k => k.hom) D.comm_g) hqYcomm
  obtain ⟨f₀, hf₀pY, hf₀jY⟩ := exists_chart_lift pX pY qX' qY' jX jY β D.iX.hom D.iY.hom D.f.hom
    D.f'.hom hpbX hpbY (congrArg (fun k => k.hom) D.comm_f) hqXcomm
  have hf₀g₀pB : yoneda.map (f₀ ≫ g₀) ≫ pB = pX ≫ D.f.hom ≫ D.g.hom := by
    rw [Functor.map_comp, Category.assoc, hg₀pB, ← Category.assoc, hf₀pY, Category.assoc]
  have hβaQ : yoneda.map (β ≫ α) ≫ qB' = qX' ≫ D.f'.hom ≫ D.g'.hom := by
    rw [Functor.map_comp, Category.assoc, ← hqYcomm, ← Category.assoc, ← hqXcomm, Category.assoc]
  have hpbYchartSite : IsPullback jY g₀ α jB :=
    isPullback_chart_of_paste pY pB qY' qB' D.iY.hom D.iB.hom D.g.hom D.g'.hom jY jB g₀ α hpbY hpbB
      (AlgebraicSpaces.isPullback_hom T S hS D.isPullback_Y) hg₀pB hqYcomm hg₀jB
  have hpbXchartSite : IsPullback jX (f₀ ≫ g₀) (β ≫ α) jB :=
    isPullback_chart_of_paste pX pB qX' qB' D.iX.hom D.iB.hom (D.f.hom ≫ D.g.hom)
      (D.f'.hom ≫ D.g'.hom) jX jB (f₀ ≫ g₀) (β ≫ α) hpbX hpbB
      (AlgebraicSpaces.isPullback_hom T S hS D.isPullback_X) hf₀g₀pB hβaQ.symm
      (by rw [Category.assoc, hg₀jB, ← Category.assoc, hf₀jY, Category.assoc])
  -- The finiteness and flatness hypotheses, read on the charts.
  have hqY'finiteType : LocallyOfFiniteType (Tscheme.map α) :=
    D.finiteType_Y' V' U' qY' qB' α hqYetale hqB'etale hqYcomm.symm
  have hqX'flat : Flat (Tscheme.map (β ≫ α)) :=
    D.flat_X' W' U' qX' qB' (β ≫ α) hqXetale hqB'etale hβaQ
  have hqX'finitePresentation : LocallyOfFinitePresentation (Tscheme.map (β ≫ α)) :=
    D.finitePresentation_X' W' U' qX' qB' (β ≫ α) hqXetale hqB'etale hβaQ
  -- The resulting flat deformation diagram of schemes.
  let E : Stacks.Thickenings.FlatDeformationDiagram.{u} :=
    { X := Tscheme.obj W₀
      X' := Tscheme.obj W'
      Y := Tscheme.obj V₀
      Y' := Tscheme.obj V'
      S := Tscheme.obj U₀
      S' := Tscheme.obj U'
      iX := Tscheme.map jX
      iY := Tscheme.map jY
      iS := Tscheme.map jB
      f := Tscheme.map f₀
      f' := Tscheme.map β
      g := Tscheme.map g₀
      g' := Tscheme.map α
      iX_thickening := hXthick
      iY_thickening := hYthick
      iS_thickening := hBthick
      comm_f := by simpa only [Functor.map_comp] using congrArg Tscheme.map hf₀jY.symm
      comm_g := by simpa only [Functor.map_comp] using congrArg Tscheme.map hg₀jB.symm
      isPullback_X := hpbXchartSite.map Tscheme
      isPullback_Y := hpbYchartSite.map Tscheme
      finiteType_Y' := hqY'finiteType
      flat_X' := hqX'flat
      finitePresentation_X' := hqX'finitePresentation }
  constructor
  · intro hAll
    rw [holdsOnEveryEtaleChart_iff_surjectiveChart T S hS P hP D.X'.property D.Y'.property
      D.f'.hom]
    have hPE : P E.f := by
      exact hAll W₀ V₀ pX pY f₀ hqX₀etale hqY₀etale hf₀pY
    exact ⟨W', V', qX', qY', β, hqXetale, hqYetale, hqXsurj, hqXcomm.symm,
      (hSchemes E).mp hPE⟩
  · intro hAll'
    rw [holdsOnEveryEtaleChart_iff_surjectiveChart T S hS P hP D.X.property D.Y.property
      D.f.hom]
    have hPE' : P E.f' := hAll' W' V' qX' qY' β hqXetale hqYetale hqXcomm.symm
    refine ⟨W₀, V₀, pX, pY, f₀, hqX₀etale, hqY₀etale, hqX₀surj, hf₀pY, (hSchemes E).mpr hPE'⟩

end AlgebraicGeometry.Space

end
