module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Descent of proper support along an fpqc covering of the base

Let

```
X i ⟶ X
 ↓     ↓ f
Y i ⟶ Y
```

be cartesian squares of algebraic spaces over a scheme `S`, indexed by an fpqc covering
`{Y i ⟶ Y}`, with `f` locally of finite type.  This file proves:

* a closed subset `T` of the points of `X` is proper over `Y` as soon as its inverse image in
  every `X i` is proper over `Y i`;
* a quasi-coherent `𝒪_X`-module of finite type has support proper over `Y` as soon as every
  inverse image to `X i` has support proper over `Y i`.

## Main results

* `AlgebraicGeometry.Space.isProperOver_of_isFpqcCovering`: properness over the base of a
  closed subset descends along an fpqc covering of the base.
* `AlgebraicGeometry.Space.hasProperSupport_of_isFpqcCovering`: proper support of a finite type
  quasi-coherent module descends along an fpqc covering of the base.

## References

* [Stacks Project, Tag 09TT](https://stacks.math.columbia.edu/tag/09TT)
* [Stacks Project, Tag 0422](https://stacks.math.columbia.edu/tag/0422)
* [Stacks Project, Tag 0CZC](https://stacks.math.columbia.edu/tag/0CZC)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Properness over the base of a closed subset depends on the subset only. -/
theorem isProperOver_of_eq_set {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) {s t : Set (points B S hS X)} (hst : s = t)
    (hs : IsClosed s) (ht : IsClosed t) (h : IsProperOver B S hS hX hY f hf s hs) :
    IsProperOver B S hS hX hY f hf t ht := by
  subst hst
  exact h

/-- **Properness over the base of a closed subset descends along an fpqc covering of the
base.** -/
theorem isProperOver_of_isFpqcCovering {I : Type v} {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    {X' Y' : I → AlgebraicSpaces B S hS} {g' : ∀ i, X' i ⟶ X} {f' : ∀ i, X' i ⟶ Y' i}
    {g : ∀ i, Y' i ⟶ Y} (sq : ∀ i, IsPullback (g' i) (f' i) f (g i))
    (hg : IsFpqcCovering B S hS fun i => (g i).hom)
    (T : Set (points B S hS X.1)) (hT : IsClosed T)
    (h : ∀ i, IsProperOver B S hS (X' i).property (Y' i).property (f' i).hom
      ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback (sq i) hf)
      (pointsMap B S hS (X' i).1 (g' i).hom ⁻¹' T)
      (isClosed_preimage_pointsMap B S hS (X' i).property X.property (g' i).hom hT)) :
    IsProperOver B S hS X.property Y.property f.hom hf T hT := by
  set Z := reducedClosedSubspace B S hS X.1 X.property T hT
  have hZcl : IsClosedSubspace B S hS Z :=
    isClosedSubspace_reducedClosedSubspace_of_closedImmersionDescent B S hS X.1 X.property T hT
      (isEffectiveDescentAlongSurjectiveEtale_isClosedImmersion B S hS)
  let Zs : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZcl.1⟩
  let ι : Zs ⟶ X := ObjectProperty.homMk Z.ι
  have hcov : Presieve.ofArrows Y' g ∈ Topology.precoverage.{u, v} .fpqc B S hS Y :=
    ⟨I, Y', g, rfl, Y.property, fun i => (Y' i).property, hg⟩
  show properProperty B S hS (ι ≫ f)
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
    (P := properProperty B S hS) (K := Topology.precoverage.{u, v} .fpqc B S hS) hcov ?_
  intro U u _ hu
  obtain ⟨i⟩ := hu
  set Q := Z.preimage (g' i).hom
  have hQcl : IsClosedSubspace B S hS Q :=
    isClosedSubspace_preimage B S hS (g' i).hom Z X.property (X' i).property hZcl
  have hQrange : Set.range (pointsMap B S hS Q.toFunctor Q.ι) =
      pointsMap B S hS (X' i).1 (g' i).hom ⁻¹' T := by
    rw [range_pointsMap_ι_preimage B S hS (X' i).property X.property (g' i).hom Z hZcl.1,
      range_pointsMap_ι_reducedClosedSubspace]
  have hf' := (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback (sq i) hf
  have hTi := isClosed_preimage_pointsMap B S hS (X' i).property X.property (g' i).hom hT
  have hQproper : IsProper B S hS (Q.ι ≫ (f' i).hom) :=
    (exists_isProper_closedSubspace_iff_forall B S hS (X' i).property (Y' i).property
      (f' i).hom hf' _ hTi).1
      ((isProper_reducedClosedSubspace_iff_exists B S hS (X' i).property (Y' i).property
        (f' i).hom hf' _ _).1 (h i)) Q hQcl hQrange
  let Qs : AlgebraicSpaces B S hS := ⟨Q.toFunctor, hQcl.1⟩
  have hsqQ : IsPullback (Z.fromPreimage (g' i).hom) Q.ι Z.ι (g' i).hom :=
    Subfunctor.isPullback_preimage (g' i).hom Z
  have hpull : IsPullback
      (ObjectProperty.homMk (Z.fromPreimage (g' i).hom) : Qs ⟶ Zs)
      (ObjectProperty.homMk Q.ι : Qs ⟶ X' i) ι (g' i) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F)) hsqQ
  have hpaste := hpull.paste_vert (sq i)
  have : (properProperty B S hS).IsLocalAtTarget (Topology.precoverage.{u, v} .fpqc B S hS) :=
    proper_isLocalAtTarget_fpqc B S hS
  have key₂ : properProperty B S hS
      (hpaste.isoPullback.hom ≫ pullback.snd (ι ≫ f) (g i)) := by
    rw [hpaste.isoPullback_hom_snd]
    exact hQproper
  exact (MorphismProperty.cancel_left_of_respectsIso (properProperty B S hS)
    hpaste.isoPullback.hom _).mp key₂

/-- **Proper support of a module descends along an fpqc covering of the base.**  A
quasi-coherent `𝒪_X`-module of finite type whose inverse images to the members of the base
change of an fpqc covering of `Y` have support proper over the members has support proper over
`Y`. -/
theorem hasProperSupport_of_isFpqcCovering {I : Type v} {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    {X' Y' : I → AlgebraicSpaces B S hS} {g' : ∀ i, X' i ⟶ X} {f' : ∀ i, X' i ⟶ Y' i}
    {g : ∀ i, Y' i ⟶ Y} (sq : ∀ i, IsPullback (g' i) (f' i) f (g i))
    (hg : IsFpqcCovering B S hS fun i => (g i).hom)
    (G : Modules.{u, u} B S hS X.1 X.2) (hqc : G.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite G)
    (h : ∀ i, HasProperSupport B S hS (X' i).property (Y' i).property (f' i).hom
      ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback (sq i) hf)
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS (g' i)).obj G))) :
    HasProperSupport B S hS X.property Y.property f.hom hf ((SheafOfModules.toSheaf _).obj G) := by
  have hcl : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G)) :=
    let := hft
    isClosed_supportOfSheaf_of_isFiniteTypeOnSite B S hS X.1 X.property G
  refine ⟨hcl, isProperOver_of_isFpqcCovering B S hS f hf sq hg _ hcl fun i => ?_⟩
  obtain ⟨hcl', hi⟩ := h i
  exact isProperOver_of_eq_set B S hS _ _ _ _
    (supportOfSheaf_modulePullback_eq B S hS (g' i) G hqc hft) hcl' _ hi

end AlgebraicGeometry.Space

end
