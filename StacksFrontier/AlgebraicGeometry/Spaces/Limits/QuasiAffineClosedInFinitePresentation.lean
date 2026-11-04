module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae

/-!
# A quasi-affine morphism of finite type is closed in one of finite presentation

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type and quasi-affine, with `Y` quasi-compact and quasi-separated.  Then `X` is a closed
subspace of an algebraic space of finite presentation over `Y`.  This file proves it for a target
represented by an object of the site.

## Main results

* `AlgebraicGeometry.Space.exists_isFinitePresentation_isClosedImmersion_of_isQuasiAffineHom`: a
  locally finite type quasi-affine morphism to a representable quasi-compact quasi-separated target
  is a closed immersion into an algebraic space of finite presentation over that target.
* `AlgebraicGeometry.Space.exists_finitePresentation_isClosedImmersion_site`: the same
  factorization for a morphism of the site, taken inside the site.
* `AlgebraicGeometry.Space.isFinitePresentation_yoneda_map`: a morphism of the site of finite
  presentation represents a morphism of algebraic spaces of finite presentation.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG)
* [Stacks Project, Tag 0871](https://stacks.math.columbia.edu/tag/0871)
* [Stacks Project, Tag 03WM](https://stacks.math.columbia.edu/tag/03WM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The factorization inside the site -/

/-- A morphism of the big fppf site of `S` which is locally of finite type, with quasi-compact
and quasi-separated source and quasi-separated target, factors as a closed immersion followed by
a morphism of finite presentation whose intermediate object is again an object of the site. -/
theorem exists_finitePresentation_isClosedImmersion_site {W Z : BigFppfOver B S hS} (k : W ⟶ Z)
    (hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k))
    (hWqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj W))
    (hWqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj W))
    (hZqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Z)) :
    ∃ (Z' : BigFppfOver B S hS) (p : Z' ⟶ Z) (i : W ⟶ Z'),
      FinitePresentation ((BigFppfOver.toScheme B S hS).map p) ∧
        _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
          i ≫ p = k := by
  have := hft
  have := hWqc
  have := hWqs
  have := hZqs
  obtain ⟨T, p, i, hp, hi, hcomp⟩ :=
    exists_finitePresentation_closedImmersion ((BigFppfOver.toScheme B S hS).map k)
  have hpfp : LocallyOfFinitePresentation p := FinitePresentation.locallyOfFinitePresentation hp
  have hpft : LocallyOfFiniteType p := inferInstance
  have hpqc : QuasiCompact p := FinitePresentation.quasiCompact hp
  have hsize : T.size < B.cutoff :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p Z.left.property
  let L : B.Schemes := B.obj hsize
  let str : B.inclusion.obj L ⟶ B.inclusion.obj (B.obj hS) := p ≫ B.inclusion.map Z.hom
  let Z' : BigFppfOver B S hS := Over.mk (B.inclusion.preimage str)
  let pL : L ⟶ Z.left :=
    B.inclusion.preimage (show B.inclusion.obj L ⟶ B.inclusion.obj Z.left from p)
  let iL : W.left ⟶ L :=
    B.inclusion.preimage (show B.inclusion.obj W.left ⟶ B.inclusion.obj L from i)
  have hpL : B.inclusion.map pL = p := B.inclusion.map_preimage _
  have hiL : B.inclusion.map iL = i := B.inclusion.map_preimage _
  have hstr : B.inclusion.map Z'.hom = p ≫ B.inclusion.map Z.hom :=
    B.inclusion.map_preimage _
  have hwp : pL ≫ Z.hom = Z'.hom := B.inclusion.map_injective <| by
    rw [B.inclusion.map_comp, hpL, hstr]
  have hwi : iL ≫ Z'.hom = W.hom := B.inclusion.map_injective <| by
    rw [B.inclusion.map_comp, hiL, hstr, ← Category.assoc, hcomp]
    exact (B.inclusion.map_comp _ _).symm.trans (congrArg _ (Over.w k))
  refine ⟨Z', Over.homMk pL hwp, Over.homMk iL hwi, ?_, ?_, ?_⟩
  · rwa [← hpL] at hp
  · rwa [← hiL] at hi
  · exact Over.OverMorphism.ext <| B.inclusion.map_injective <| by
      simp only [Over.comp_left, Over.homMk_left, B.inclusion.map_comp, hiL, hpL]
      exact hcomp

/-! ### Finite presentation of a represented morphism -/

/-- A morphism of the big fppf site of `S` of finite presentation represents a morphism of
algebraic spaces of finite presentation in the sense of Stacks 03XP, part (3). -/
theorem isFinitePresentation_yoneda_map {a b : BigFppfOver B S hS} (p : a ⟶ b)
    (hp : FinitePresentation ((BigFppfOver.toScheme B S hS).map p)) :
    IsFinitePresentation B S hS (yoneda.map p) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget p).2
      (FinitePresentation.locallyOfFinitePresentation hp)
  · exact isQuasiCompact_of_presheaf_quasiCompact B S hS
      ((presheaf_yoneda_map_iff B S hS
        (P := @AlgebraicGeometry.QuasiCompact.{u}) inferInstance p).2
        (FinitePresentation.quasiCompact hp))
  · exact (isQuasiSeparated_yoneda_map_iff B S hS p).2 (FinitePresentation.quasiSeparated hp)

/-! ### Stacks 0871 over a representable target -/

/-- A quasi-affine morphism of algebraic spaces over `S` with representable target has
representable source, and the morphism of schemes underlying it is quasi-affine. -/
theorem exists_iso_yoneda_of_isQuasiAffineHom {Z : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj Z)
    (hX : IsAlgebraicSpace B S hS X) (hqa : IsQuasiAffineHom B S hS f) :
    ∃ (W : BigFppfOver B S hS) (k : W ⟶ Z) (e : yoneda.obj W ≅ X),
      e.hom ≫ f = yoneda.map k ∧
        _root_.AlgebraicGeometry.IsQuasiAffineHom ((BigFppfOver.toScheme B S hS).map k) := by
  have hpre := presheaf_isQuasiAffineHom_of_isQuasiAffineHom_of_isAlgebraicSpace B S hS hX
    (isAlgebraicSpace_yoneda B S hS Z) hqa
  have hpb := hpre.rep.isPullback (𝟙 (yoneda.obj Z))
  have hstd : IsPullback (𝟙 X) f f (𝟙 (yoneda.obj Z)) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨_, hpre.rep.snd (𝟙 (yoneda.obj Z)), hpb.isoIsPullback _ _ hstd,
    hpb.isoIsPullback_hom_snd _ _ hstd, hpre.property_snd (𝟙 (yoneda.obj Z))⟩

/-- A morphism of algebraic spaces over `S` which is locally of finite type and quasi-affine,
whose target is the functor of points of a quasi-compact, quasi-separated scheme of the site, is a
closed immersion into an algebraic space of finite presentation over that target. -/
@[stacks 0871 "for a target represented by a quasi-compact quasi-separated object of the \
site; a general algebraic-space target needs the unproved direction of 086S and Stacks 0870"]
theorem exists_isFinitePresentation_isClosedImmersion_of_isQuasiAffineHom
    {Z : BigFppfOver B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj Z)
    (hX : IsAlgebraicSpace B S hS X)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hqa : IsQuasiAffineHom B S hS f)
    (hZqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj Z))
    (hZqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj Z)) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ yoneda.obj Z) (i : X ⟶ X'),
      IsAlgebraicSpace B S hS X' ∧ IsFinitePresentation B S hS f' ∧
        IsClosedImmersion B S hS i ∧ i ≫ f' = f := by
  have := hZqc
  have := hZqs
  obtain ⟨W, k, e, hek, hkqa⟩ := exists_iso_yoneda_of_isQuasiAffineHom B S hS f hX hqa
  have := hkqa
  have hkqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map k) := inferInstance
  have hkqs : QuasiSeparated ((BigFppfOver.toScheme B S hS).map k) := inferInstance
  have _hri : MorphismProperty.RespectsIso (@IsLocallyOfFiniteType B S hS) :=
    holdsOnEveryEtaleChart_respectsIso_presheaf B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
  have hftk : IsLocallyOfFiniteType B S hS (yoneda.map k) :=
    hek ▸ MorphismProperty.RespectsIso.precomp _ e.hom f hft
  have hftks : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget k).1 hftk
  have hWqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) :=
    QuasiCompact.compactSpace_of_compactSpace ((BigFppfOver.toScheme B S hS).map k)
  have hWqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj W) :=
    quasiSeparatedSpace_of_quasiSeparated ((BigFppfOver.toScheme B S hS).map k)
  obtain ⟨Z', p, i, hp, hi, hcomp⟩ :=
    exists_finitePresentation_isClosedImmersion_site B S hS k hftks hWqc hWqs hZqs
  refine ⟨yoneda.obj Z', yoneda.map p, e.inv ≫ yoneda.map i,
    isAlgebraicSpace_yoneda B S hS Z', isFinitePresentation_yoneda_map B S hS p hp, ?_, ?_⟩
  · exact MorphismProperty.RespectsIso.precomp _ e.inv (yoneda.map i)
      ((presheaf_yoneda_map_iff B S hS
        (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}) inferInstance i).2 hi)
  · rw [Category.assoc, ← yoneda.map_comp, hcomp, ← hek, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Space

end
