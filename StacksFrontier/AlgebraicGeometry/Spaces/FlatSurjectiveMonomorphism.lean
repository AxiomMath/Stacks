module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
import StacksFrontier.AlgebraicGeometry.Spaces.Immersions

/-!
# Quasi-compact flat surjective monomorphisms of algebraic spaces

A quasi-compact, flat and surjective morphism of algebraic spaces over `S` is a one-member
fpqc covering of its target, and if it is in addition a monomorphism it is an isomorphism.
The second statement is **Stacks 0B8C**.

## Main results

* `AlgebraicGeometry.Space.isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective`: a
  quasi-compact flat surjective morphism of algebraic spaces is an fpqc covering.
* `AlgebraicGeometry.Space.isIso_of_mono_of_isQuasiCompact_of_isFlat_of_isSurjective`:
  **Stacks 0B8C**.

## Implementation notes

The fpqc condition of Stacks 03MQ asks, over every affine scheme-valued point `T ⟶ Y`, for a
finite affine family covering `T` in the fpqc precoverage of schemes and refining the given
family. Quasi-compactness of `f` makes the fibre product `X ×_Y T` a quasi-compact algebraic
space, so by Stacks 03H6 it has a surjective étale cover by a single affine scheme `U` of the
site; the induced morphism `U ⟶ T` is flat because flatness is stable under base change and
étale morphisms are flat, it is surjective on points because both of its factors are, and it is
quasi-compact because its source and target are affine. A flat surjective quasi-compact morphism
of schemes is a one-member fpqc covering, which is the required refinement.

Given that, Tag 0B8C needs no descent argument of its own: being an open immersion is local on
the base for the fpqc topology (Stacks 041X), and the base change of a monomorphism along itself
is an isomorphism, hence an open immersion. So `f` is an open immersion, and an open immersion
which is surjective is an isomorphism (Stacks 03MD).

## References

* [Stacks Project, Tag 0B8C](https://stacks.math.columbia.edu/tag/0B8C)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A quasi-compact, flat and surjective morphism of algebraic spaces over `S` is an fpqc
covering of its target in the sense of Stacks 03MQ, as a family with any nonempty index
type. -/
theorem isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {I : Type v} [Nonempty I]
    (hqc : IsQuasiCompact B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) :
    IsFpqcCovering B S hS (fun _ : I ↦ f.hom) := by
  classical
  refine ⟨fun _ ↦ hflat, fun T h ↦ ?_⟩
  let G := BigFppfOver.toScheme B S hS
  let V : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj T
  have hVaff : IsAffine (G.obj V) := T.property
  have hVsp := isAlgebraicSpace_yoneda B S hS V
  let TY : AlgebraicSpaces B S hS := ⟨yoneda.obj V, hVsp⟩
  let g : TY ⟶ Y := ObjectProperty.homMk h
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS g f
  have hZ : IsAlgebraicSpace B S hS (pullback h f.hom) :=
    isAlgebraicSpace_pullback B S hS h f.hom hVsp X.property Y.property
  have hZqc : IsQuasiCompactSpace B S hS (pullback h f.hom) :=
    hqc (yoneda.obj V) hVsp
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS V hVaff) h
  obtain ⟨U, a, hUaff, haSurj, haEt⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (pullback h f.hom) hZ).mp hZqc
  have _ := isFlat_isStableUnderBaseChange B S hS
  have hpFlat : IsFlat B S hS (pullback.fst h f.hom) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) ↦ IsFlat B S hS k.hom) sq.flip hflat
  have hpSurj : IsSurjective B S hS (pullback.fst h f.hom) :=
    isSurjective_of_isPullback B S hS sq.flip hsurj
  have haEt' : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) G).presheaf a :=
    (isEtale_iff_presheaf_of_yoneda B S hS a).1 haEt
  let b : U ⟶ V := yoneda.preimage (a ≫ pullback.fst h f.hom)
  have hb : yoneda.map b = a ≫ pullback.fst h f.hom := yoneda.map_preimage _
  have hid : ∀ W : BigFppfOver B S hS, (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      G).presheaf (𝟙 (yoneda.obj W)) := fun W ↦
    (isEtale_iff_presheaf_of_yoneda B S hS (𝟙 (yoneda.obj W))).1 fun _ _ hφ ↦ by simpa using hφ
  have hbFlat : Flat (G.map b) := by
    have hfl : IsFlat B S hS (yoneda.map b) := hb ▸ isFlat_comp_of_etale_chart B S hS hZ
      hVsp a haEt' (pullback.fst h f.hom) hpFlat
    exact hfl U V (𝟙 _) (𝟙 _) b (hid U) (hid V) (by simp)
  have hbSurjP : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) G).presheaf
      (yoneda.map b) := by
    refine (presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj V)
      hVsp U (yoneda.map b)).2 ?_
    rw [hb]
    intro z
    obtain ⟨y, hy⟩ := hpSurj z
    obtain ⟨x, hx⟩ := isSurjective_of_presheafSurjective B S hS a haSurj y
    refine ⟨x, ?_⟩
    rw [pointsMap_comp]
    simp only [Function.comp_apply, hx, hy]
  have hbSurj : Surjective (G.map b) :=
    MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) G)
      (F := yoneda) (f := b) hbSurjP
  have _ : IsAffine (G.obj U) := hUaff
  let W : BigAffineFppf B S hS := ⟨U, hUaff⟩
  let bb : W ⟶ T := ObjectProperty.homMk b
  refine ⟨PreZeroHypercover.singleton bb, inferInstance, ?_, fun _ ↦ ?_⟩
  · rw [PreZeroHypercover.presieve₀_singleton, Presieve.map_singleton]
    exact Scheme.Hom.singleton_mem_fpqcPrecoverage (G.map b)
  · refine ⟨Classical.arbitrary I, a ≫ pullback.snd h f.hom, ?_⟩
    change (a ≫ pullback.snd h f.hom) ≫ f.hom = yoneda.map b ≫ h
    rw [hb, Category.assoc, Category.assoc, pullback.condition]

/-- **Stacks 0B8C.** A quasi-compact, flat and surjective monomorphism of algebraic spaces
over `S` is an isomorphism. -/
@[stacks 0B8C]
theorem isIso_of_mono_of_isQuasiCompact_of_isFlat_of_isSurjective
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f]
    (hqc : IsQuasiCompact B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) :
    IsIso f := by
  have hR : Presieve.ofArrows (fun _ : PUnit.{u + 1} ↦ X) (fun _ ↦ f) ∈
      (Topology.precoverage.{u, u} .fpqc B S hS) Y :=
    ⟨PUnit.{u + 1}, fun _ ↦ X, fun _ ↦ f, rfl, Y.property, fun _ ↦ X.property,
      isFpqcCovering_of_isQuasiCompact_of_isFlat_of_isSurjective B S hS f hqc hflat hsurj⟩
  have hoi : IsOpenImmersion B S hS f.hom := by
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := openImmersionProperty B S hS)
      (K := Topology.precoverage.{u, u} .fpqc B S hS) hR ?_
    intro Z k _ hk
    obtain ⟨-⟩ := hk
    have hiso : IsIso (pullback.snd f f) := (IsPullback.of_hasPullback f f).flip.isIso_fst_of_mono
    have _ : IsIso (pullback.snd f f).hom := (ObjectProperty.isIso_hom_iff _).2 hiso
    exact MorphismProperty.presheaf_of_isIso _ _
  exact (ObjectProperty.isIso_hom_iff f).mp
    (isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS f.hom hoi
      (presheafSurjective_of_isSurjective B S hS f.hom hoi.rep hsurj))

end AlgebraicGeometry.Space

end
