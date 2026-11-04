module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct

/-!
# Flat base change of an every-etale-chart property

A property of morphisms of schemes which is etale local on the source and target and stable
under base change along a flat morphism induces, via `HoldsOnEveryEtaleChart`, a property of
morphisms of algebraic spaces which is again stable under base change along a flat morphism.

This is the flat-base-change form of Stacks 0AMM, and it is the common engine behind flat base
change for pseudo-coherence (Stacks 06BY), for perfection (Stacks 06C3) and for the Koszul
property (Stacks 06C7); those three modules share it.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_isPullback_of_isFlat`

## Tags

algebraic space, etale chart, flat base change
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The flat-base-change form of Stacks 0AMM. Let `P` be a property of morphisms of schemes which
is étale local on the source and target and stable under base change along a flat morphism. Then
the induced every-étale-chart property of morphisms of algebraic spaces over `S` is stable under
base change along a flat morphism of algebraic spaces: in a cartesian square with `g : Y ⟶ Z`
carrying the property and `f : X ⟶ Z` flat, the base change `g' : Y' ⟶ X` of `g` carries it. -/
public theorem holdsOnEveryEtaleChart_of_isPullback_of_isFlat
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    (hbc : ∀ {A A' C : Scheme.{u}} (a : A ⟶ C) (c : A' ⟶ C), Flat c → P a →
      P (Limits.pullback.snd a c))
    {X Y Y' Z : AlgebraicSpaces B S hS} {f : X ⟶ Z} {g : Y ⟶ Z} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hflat : IsFlat B S hS f.hom)
    (hf : HoldsOnEveryEtaleChart B S hS P g.hom) :
    HoldsOnEveryEtaleChart B S hS P g'.hom := by
  let T := BigFppfOver.toScheme B S hS
  let QEtale : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T
  let QSurjective : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) T
  let E := QEtale.presheaf
  let R := QSurjective.presheaf
  have : QEtale.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  have : QSurjective.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have : QEtale.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have : QSurjective.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition.{u}
  have : E.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange QEtale
  have : R.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange QSurjective
  have : E.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition QEtale
  have : R.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition QSurjective
  obtain ⟨V, b, hbSurj, hbEtale⟩ := Z.property.exists_atlas
  obtain ⟨U, a, h, hab, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS Y.property Z.property g.hom V b
      hbSurj hbEtale
  have hPchart : P (T.map h) := hf U V a b h haEtale hbEtale hab.symm
  obtain ⟨D, d, hdSurj, hdEtale⟩ := X.property.exists_atlas
  let rObj := hbEtale.rep.pullback (d ≫ f.hom)
  let rV : rObj ⟶ V := hbEtale.rep.fst' (d ≫ f.hom)
  let rD : rObj ⟶ D := hbEtale.rep.snd (d ≫ f.hom)
  have hrD_etale : AlgebraicGeometry.Etale (T.map rD) :=
    hbEtale.property (d ≫ f.hom) (yoneda.map rV) rD
      (hbEtale.rep.isPullback' (d ≫ f.hom))
  let H := Limits.pullback h rV
  let hU : H ⟶ U := Limits.pullback.fst h rV
  let hR : H ⟶ rObj := Limits.pullback.snd h rV
  have hpbH : IsPullback (yoneda.map hU) (yoneda.map hR) (yoneda.map h) (yoneda.map rV) :=
    (IsPullback.of_hasPullback h rV).map yoneda
  have hpbR : IsPullback (yoneda.map rV) (yoneda.map rD) b (d ≫ f.hom) :=
    hbEtale.rep.isPullback' (d ≫ f.hom)
  have hpbOuter : IsPullback (yoneda.map hU)
      (yoneda.map (hR ≫ rD)) (a ≫ g.hom) (d ≫ f.hom) := by
    simpa only [Functor.map_comp, ← hab] using hpbH.paste_vert hpbR
  let Yc := AlgebraicSpaces.fiberProduct B S hS f g
  let fC : Yc ⟶ Y := ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom)
  let gC : Yc ⟶ X := ObjectProperty.homMk (Limits.pullback.fst f.hom g.hom)
  have hsq : IsPullback fC.hom gC.hom g.hom f.hom :=
    (IsPullback.of_hasPullback f.hom g.hom).flip
  have hpbC : IsPullback fC gC g f := (AlgebraicSpaces.isPullback_fiberProduct B S hS f g).flip
  let e : Y' ≅ Yc := sq.isoIsPullback _ _ hpbC
  have he : e.hom ≫ gC = g' := sq.isoIsPullback_hom_snd _ _ hpbC
  let J := Limits.pullback gC.hom d
  let jYc := Limits.pullback.fst gC.hom d
  let jD := Limits.pullback.snd gC.hom d
  have hpbJ : IsPullback jYc jD gC.hom d := IsPullback.of_hasPullback gC.hom d
  have hpbJY : IsPullback (jYc ≫ fC.hom) jD g.hom (d ≫ f.hom) := hpbJ.paste_horiz hsq
  let j : yoneda.obj H ⟶ J := hpbJY.lift (yoneda.map hU ≫ a)
    (yoneda.map (hR ≫ rD)) (by simpa only [Category.assoc] using hpbOuter.w)
  have hpbHJ : IsPullback (yoneda.map hU) j a (jYc ≫ fC.hom) := by
    simpa [j] using hpbOuter.of_bot' hpbJY
  have hjD : j ≫ jD = yoneda.map (hR ≫ rD) := hpbJY.lift_snd _ _ _
  have hbEtale' : E (yoneda.map rD ≫ d) :=
    MorphismProperty.comp_mem E _ _ (MorphismProperty.relative_map (F := yoneda) hrD_etale) hdEtale
  have hflatrV : Flat (T.map rV) :=
    hflat rObj V (yoneda.map rD ≫ d) b rV hbEtale' hbEtale
      (by simpa only [Category.assoc] using hpbR.w)
  have hPbase : P (T.map hR) := by
    have hpbT : IsPullback (T.map hU) (T.map hR) (T.map h) (T.map rV) :=
      (IsPullback.of_hasPullback h rV).map T
    have hcan : P (Limits.pullback.snd (T.map h) (T.map rV)) := hbc _ _ hflatrV hPchart
    rw [← hpbT.isoPullback_hom_snd]
    exact hP.precomp.precomp _ inferInstance _ hcan
  have hcommC : j ≫ jYc ≫ gC.hom = yoneda.map hR ≫ (yoneda.map rD ≫ d) := by
    rw [hpbJ.w, reassoc_of% hjD]
    simp only [Functor.map_comp, Category.assoc]
  let c : yoneda.obj H ⟶ Y'.obj := (j ≫ jYc) ≫ e.inv.hom
  have hcomp : ∀ W : MorphismProperty _, W.IsStableUnderBaseChange → W.IsStableUnderComposition →
      W a → W d → W c := fun W _ _ ha hd ↦ MorphismProperty.RespectsIso.postcomp W e.inv.hom _
    (MorphismProperty.comp_mem W j jYc
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbHJ ha)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hpbJ.flip hd))
  have hc' : E c := hcomp E inferInstance inferInstance haEtale hdEtale
  have hs' : R c := hcomp R inferInstance inferInstance haSurj hdSurj
  have heInv : e.inv ≫ g' = gC := by
    rw [← he, Iso.inv_hom_id_assoc]
  have heInvHom : e.inv.hom ≫ g'.hom = gC.hom := by
    simpa only [ObjectProperty.FullSubcategory.comp_hom] using congrArg (fun q => q.hom) heInv
  have hcomm : c ≫ g'.hom = yoneda.map hR ≫ (yoneda.map rD ≫ d) := by
    dsimp [c]
    rw [Category.assoc, heInvHom]
    exact hcommC
  exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP Y'.property X.property
    g'.hom).mpr ⟨H, rObj, c, yoneda.map rD ≫ d, hR, hc', hbEtale', hs', hcomm.symm, hPbase⟩

end Space

end AlgebraicGeometry

end
