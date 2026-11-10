module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.ModuleFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FpqcCoverings

/-!
# The Koszul property of morphisms of algebraic spaces is fpqc local on the base

Let `S` be a scheme contained in a big fppf site `B`. The property of being a local complete
intersection morphism of algebraic spaces over `S` is local on the base for the fpqc topology of
**Stacks 03YH**: a morphism is Koszul exactly when its base changes along the members of an fpqc
covering of its target are. This is **Stacks 0CHM**.

## Main results

* `AlgebraicGeometry.Space.isLocalCompleteIntersection_isLocalAtTarget_fpqc`: **Stacks 0CHM**.

## Implementation notes

The argument is the source's. One direction is flat base change, **Stacks 06C7**, the members of
an fpqc covering being flat. For the other, the covering `{Yᵢ ⟶ Y}` is first replaced by a
refinement whose members are schemes of the site, **Stacks 0419**; the refining morphisms
`eᵢ : h_{Tᵢ} ⟶ Yᵢ` are the étale atlases of the members, so the base change of `f` along
`eᵢ ≫ gᵢ` is the base change along `eᵢ` — a flat one — of its base change along `gᵢ`, and
Stacks 06C7 carries the hypothesis over to the refinement. That is the reading of the source's
"we may replace the covering by a refinement (again because flat base change preserves the
property of being a local complete intersection morphism)", and it is why Stacks 0419 is used in
the form that records relative étaleness of the refining morphisms.

The Koszul property of a morphism of algebraic spaces is the every-chart condition of
**Stacks 03MJ** at the Koszul property of morphisms of schemes, so what has to be shown is that
the scheme morphism `h : U ⟶ V` of an arbitrary commuting square of étale charts `a` of `X` and
`b` of `Y` is Koszul. The chart `b` is relatively representable, so the refined covering pulls
back along it to a family `{V ×_Y Tᵢ ⟶ V}` of morphisms of schemes of the site, which is an fpqc
covering of the scheme `V` by `AlgebraicGeometry.Space.fpqc_of_yoneda_refinements`: its members
are flat by the chart condition for flatness, and over an affine scheme-valued point of `V` the
refinement clause of **Stacks 03MQ** for the refined covering supplies the required finite affine
family. By the case of schemes, **Stacks 069N**, it therefore suffices that each base change of
`h` along a member of that family is Koszul. That base change is the scheme morphism of a
commuting square of étale charts of `X ×_Y Yᵢ ⟶ Yᵢ`: the chart of the target is
`h_{V ×_Y Tᵢ} ⟶ h_{Tᵢ} ⟶ Yᵢ` and the chart of the source is the base change of `a`, étale
because `U ×_V (V ×_Y Tᵢ) = U ×_Y Tᵢ` is a fibre product over `Y`. So the hypothesis at `i`
applies, and no locality on the source is needed.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 0419](https://stacks.math.columbia.edu/tag/0419)
* [Stacks Project, Tag 069N](https://stacks.math.columbia.edu/tag/069N)
* [Stacks Project, Tag 06C7](https://stacks.math.columbia.edu/tag/06C7)
* [Stacks Project, Tag 0CHM](https://stacks.math.columbia.edu/tag/0CHM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site over `S` is slow
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_lciFpqcLocalAtTarget :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_lciFpqcLocalAtTarget
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The base change along `w` of the scheme morphism `h` of a commuting square of étale charts
`a`, `b` of `f : X ⟶ Y` is Koszul, when `w` is the first projection of a square identifying it
with a morphism `yoneda.obj T ⟶ Y'.obj ⟶ Y.obj` through a relatively étale `ei` and the base
change of `f` along `gi : Y' ⟶ Y` is Koszul.

Indeed that base change of `h` is the scheme morphism of a commuting square of étale charts of
`pullback.snd f.hom gi.hom`, the chart of the source being the base change of `a` and the chart
of the target being `yoneda.map sm ≫ ei`, so the hypothesis at `gi` applies. -/
private theorem isLocalCompleteIntersectionMorphism_pullback_snd_of_etaleCharts
    {X Y Y' : AlgebraicSpaces B S hS} {T U V V' : BigFppfOver B S hS} (f : X ⟶ Y) (gi : Y' ⟶ Y)
    (ei : yoneda.obj T ⟶ Y'.obj) (a : yoneda.obj U ⟶ X.obj) (b : yoneda.obj V ⟶ Y.obj)
    (h : U ⟶ V) (w : V' ⟶ V) (sm : V' ⟶ T)
    (hsq : IsPullback (yoneda.map w) (yoneda.map sm) b (ei ≫ gi.hom))
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hei : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ei)
    (hsm : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map sm))
    (hh : yoneda.map h ≫ b = a ≫ f.hom)
    (hf : IsLocalCompleteIntersection B S hS (pullback.snd f.hom gi.hom)) :
    IsLocalCompleteIntersectionMorphism
      (pullback.snd ((BigFppfOver.toScheme B S hS).map h)
        ((BigFppfOver.toScheme B S hS).map w)) := by
  let F := BigFppfOver.toScheme B S hS
  let E : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F
  let _ : PreservesLimitsOfShape WalkingCospan F := by
    dsimp [F, BigFppfOver.toScheme, BigFppfOver.forget]
    infer_instance
  let _ : E.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  let _ : E.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange E
  let _ : E.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  let _ : E.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition E
  let P : MorphismProperty Scheme.{u} := @IsLocalCompleteIntersectionMorphism.{u}
  -- The base change, as a morphism of schemes of the site.
  let H := Limits.pullback h w
  let r : H ⟶ U := pullback.fst h w
  let t : H ⟶ V' := pullback.snd h w
  have outer : IsPullback (yoneda.map r) (yoneda.map t ≫ yoneda.map sm)
      (a ≫ f.hom) (ei ≫ gi.hom) := by
    rw [← hh]
    exact ((IsPullback.of_hasPullback h w).map yoneda).paste_vert hsq
  -- It is the scheme morphism of a commuting square of étale charts of the base change of `f`.
  let α : yoneda.obj H ⟶ Limits.pullback f.hom gi.hom :=
    outer.isoPullback.hom ≫
      pullback.map (a ≫ f.hom) (ei ≫ gi.hom) f.hom gi.hom a ei (𝟙 _) (by simp) (by simp)
  let β : yoneda.obj V' ⟶ Y'.obj := yoneda.map sm ≫ ei
  have hα : E.presheaf α :=
    MorphismProperty.RespectsIso.precomp E.presheaf outer.isoPullback.hom _
      (MorphismProperty.pullbackMap (P := E.presheaf) ha hei rfl rfl)
  have hβ : E.presheaf β := MorphismProperty.comp_mem _ _ _ hsm hei
  have hcomm : yoneda.map t ≫ β = α ≫ pullback.snd f.hom gi.hom := by
    simp only [α, β, Category.assoc, pullback.map, pullback.lift_snd]
    simp only [← Category.assoc, outer.isoPullback_hom_snd]
  have ht : P (F.map t) := hf H V' α β t hα hβ hcomm
  let sq := (IsPullback.of_hasPullback h w).map F
  apply (P.cancel_left_of_respectsIso sq.isoPullback.hom (pullback.snd _ _)).mp
  simpa only [sq.isoPullback_hom_snd] using ht

/-- Descent of the Koszul property along an fpqc covering of the target: a morphism of algebraic
spaces over `S` whose base change along every member of an fpqc covering of its target is Koszul
is itself Koszul.

This is the substantial half of Stacks 0CHM; see the module docstring for the argument. -/
private theorem isLocalCompleteIntersection_of_isFpqcCovering
    {I : Type v} {X Y : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
    (f : X ⟶ Y) (g : ∀ i, Yi i ⟶ Y)
    (hcover : IsFpqcCovering B S hS fun i => (g i).hom)
    (hf : ∀ i, IsLocalCompleteIntersection B S hS (pullback.snd f.hom (g i).hom)) :
    IsLocalCompleteIntersection B S hS f.hom := by
  classical
  let F := BigFppfOver.toScheme B S hS
  let A := BigAffineFppf.inclusion B S hS
  let E : MorphismProperty (BigFppfOver B S hS) :=
    MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) F
  let _ : E.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  obtain ⟨T, e, he, hc⟩ := exists_fpqc_scheme_refinement B S hS Y.property
    (fun i => (Yi i).property) (fun i => (g i).hom) hcover
  intro U V a b h ha hb hh
  -- The refined covering, as a family of morphisms into the target.
  let d (i : I) : yoneda.obj (T i) ⟶ Y.obj := e i ≫ (g i).hom
  -- Its pullback along the chart `b`, a family of morphisms of schemes of the site.
  let W : PreZeroHypercover.{v} V :=
    { I₀ := I
      X i := hb.rep.pullback (d i)
      f i := hb.rep.fst' (d i) }
  let s (i : I) : W.X i ⟶ T i := hb.rep.snd (d i)
  have hs (i : I) : E (s i) := hb.property_snd (d i)
  have hs' (i : I) : E.presheaf (yoneda.map (s i)) := MorphismProperty.relative_map (hs i)
  have hwflat (i : I) : Flat (F.map (W.f i)) :=
    hc.1 i (W.X i) V (yoneda.map (s i)) b (W.f i) (hs' i) hb (hb.rep.isPullback' (d i)).w
  have hwcover : (W.map F).presieve₀ ∈ Scheme.fpqcPrecoverage (F.obj V) := by
    apply fpqc_of_yoneda_refinements B S hS W hwflat
    intro Z k
    obtain ⟨R, hfin, hcov, hfac⟩ := hc.2 Z (yoneda.map k ≫ b)
    refine ⟨R, hfin, hcov, fun j => ?_⟩
    obtain ⟨i, q, hq⟩ := hfac j
    have heq : yoneda.map (A.map (R.f j) ≫ k) ≫ b = yoneda.map (yoneda.preimage q) ≫ d i := by
      change q ≫ d i = yoneda.map (A.map (R.f j)) ≫ yoneda.map k ≫ b at hq
      simpa only [Functor.map_comp, Functor.map_preimage, Category.assoc] using hq.symm
    exact ⟨i, hb.rep.lift' (A.map (R.f j) ≫ k) (yoneda.preimage q) heq, hb.rep.lift'_fst _ _ _⟩
  -- By the case of schemes it is enough to check the base changes along that family.
  let P : MorphismProperty Scheme.{u} := @IsLocalCompleteIntersectionMorphism.{u}
  apply (isLocalCompleteIntersectionMorphism_isLocalAtTarget_fpqc :
    P.IsLocalAtTarget Scheme.fpqcPrecoverage).of_forall_pullbackSnd hwcover
  intro Z k _ hk
  change Presieve.ofArrows (fun i : I => F.obj (W.X i)) (fun i : I => F.map (W.f i)) k at hk
  obtain ⟨i, hZ, hk'⟩ := Presieve.ofArrows_surj (fun i : I => F.map (W.f i)) k hk
  cases hZ
  simp only [eqToHom_refl, Category.id_comp] at hk'
  subst k
  -- Its base change along the member at `i` is the scheme morphism of a square of étale charts
  -- of the base change of `f` along `g i`.
  exact isLocalCompleteIntersectionMorphism_pullback_snd_of_etaleCharts B S hS f (g i) (e i)
    a b h (W.f i) (s i) (hb.rep.isPullback' (d i)) ha (he i) (hs' i) hh (hf i)

/-- **Stacks 0CHM.** The property of being a local complete intersection morphism of algebraic
spaces over `S` is local on the base for the fpqc topology of Stacks 03YH: a morphism is Koszul
exactly when its base changes along the members of an fpqc covering of its target are. -/
@[stacks 0CHM]
theorem isLocalCompleteIntersection_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) =>
        IsLocalCompleteIntersection B S hS f.hom)
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun _ _ f => IsLocalCompleteIntersection B S hS f.hom
  let _ : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso B S hS _
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff (P := Q) ?_
  intro X Y f R hR
  have key {Z : AlgebraicSpaces B S hS} (g : Z ⟶ Y) [HasPullback f g] :
      Q (pullback.snd f g) ↔ IsLocalCompleteIntersection B S hS (pullback.snd f.hom g.hom) := by
    have hfib := AlgebraicSpaces.isPullback_fiberProduct B S hS f g
    rw [← Q.cancel_left_of_respectsIso hfib.isoPullback.hom (pullback.snd f g),
      hfib.isoPullback_hom_snd]
    exact Iff.rfl
  obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
  obtain ⟨-, -, hfpqc⟩ := hcover
  constructor
  · intro hf U g _ hg
    obtain ⟨i⟩ := hg
    exact (key (gi i)).2 (isLocalCompleteIntersection_pullback_snd B S hS f (gi i) (hfpqc.1 i) hf)
  · intro hall
    refine isLocalCompleteIntersection_of_isFpqcCovering B S hS Yi f gi hfpqc fun i => ?_
    let _ : HasPullback f (gi i) :=
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f (gi i)).hasPullback
    exact (key (gi i)).1 (hall (gi i) (Presieve.ofArrows.mk i))

end AlgebraicGeometry.Space

end
