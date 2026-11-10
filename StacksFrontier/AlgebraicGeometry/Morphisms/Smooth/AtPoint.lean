module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.Defs
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness of a morphism at a point

A morphism of schemes is smooth at a point when its restriction to some open neighbourhood of
that point is smooth. This is equivalent to the morphism being given, near the point, by a smooth
homomorphism between the rings of sections of affine open neighbourhoods, and — over any
prescribed affine neighbourhood of the image — by a standard smooth one.

## Main definitions

* `InfinitesimalLifting.SmoothAt` expresses that a morphism of schemes is smooth at a specified
  point.

## Main results

* `InfinitesimalLifting.smoothAt_iff_exists_affine` characterizes smoothness at a point by affine
  neighbourhoods and the induced smooth ring homomorphism.
* `InfinitesimalLifting.smoothAt_iff_exists_affine_isStandardSmooth` characterizes smoothness at a
  point by a standard smooth restriction over any prescribed affine neighbourhood of the image.
* `InfinitesimalLifting.smooth_iff_forall_smoothAt` and
  `InfinitesimalLifting.smooth_of_forall_smoothAt` globalize smoothness at every point to
  smoothness of the morphism.

## Implementation notes

The existing predicate `InfinitesimalLifting.SmoothAt` uses an arbitrary open neighbourhood on
which the restricted morphism is smooth. The two characterizations prove that this intrinsic form
is equivalent to the affine-open formulations, and their forward and reverse implications are the
introduction and elimination API for the affine witnesses.

Membership of the point in the inverse image of the chosen target open is the scheme-theoretic
expression of that open being a neighbourhood of its image, and the restricted morphism is
expressed by `AlgebraicGeometry.Scheme.Hom.resLE`.

The passage between a morphism restricted to an open subscheme and the map it induces on sections
is mediated by `AlgebraicGeometry.Scheme.Hom.resLE_appLE`. It is applied with its opens given
explicitly, so that the rewrite is a syntactic match rather than a definitional unfolding;
likewise the identification of the restriction of an inclusion with a presheaf restriction map is
isolated in `InfinitesimalLifting.isIso_ι_appLE`. This keeps both equivalences free of any
dependence on relaxed elaborator transparency.

The globalization goes through locality of smoothness on the source, which for a property coming
from a ring homomorphism property is
`AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`. That instance is supplied
explicitly rather than by inference: its ring homomorphism property is an instance-implicit
argument that instance resolution cannot determine from the goal alone.

## References

* [Stacks Project, Tag 01V5](https://stacks.math.columbia.edu/tag/01V5)
* [Stacks Project, Tag 01V7](https://stacks.math.columbia.edu/tag/01V7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace InfinitesimalLifting

add_to_stacks 01V5 "smooth_at_point" InfinitesimalLifting.SmoothAt

/-- Smoothness at a point is equivalent to the existence of affine open neighbourhoods of the
point and of its image on whose rings of sections the induced homomorphism is smooth. -/
public theorem smoothAt_iff_exists_affine {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    InfinitesimalLifting.SmoothAt f x ↔
      ∃ (U : X.Opens) (V : S.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V)
        (_ : x ∈ U) (hUV : U ≤ f ⁻¹ᵁ V), (f.appLE V U hUV).hom.Smooth := by
  constructor
  · rintro ⟨W, hxW, hf⟩
    obtain ⟨V, hV, U, hU, hxU, hUV, -⟩ :=
      AlgebraicGeometry.Smooth.exists_isStandardSmooth (f.resLE ⊤ W le_top) ⟨x, hxW⟩
    have hs := (f.resLE ⊤ W le_top).smooth_appLE hV hU hUV
    rw [Scheme.Hom.resLE_appLE f (U := ⊤) (V := W) le_top V U hUV] at hs
    exact ⟨W.ι ''ᵁ U, (⊤ : S.Opens).ι ''ᵁ V, hU.image_of_isOpenImmersion _,
      hV.image_of_isOpenImmersion _, by simpa using W.mem_ι_image_iff.mpr hxU,
      (Scheme.Hom.le_resLE_preimage_iff f le_top V U).mp hUV, hs⟩
  · rintro ⟨U, V, hU, hV, hxU, hUV, hs⟩
    have : IsAffine U.toScheme := hU
    have : IsAffine V.toScheme := hV
    have hg : Smooth (f.resLE V U hUV) :=
      (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).2
        ((RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
          (arrowResLEAppIso f V U hUV)).mpr hs)
    refine ⟨U, hxU, ?_⟩
    rw [← f.resLE_map hUV le_top]
    infer_instance

/-- The restriction of an open immersion to a smaller open of its source, read on sections, is an
isomorphism onto the corresponding presheaf restriction. -/
public lemma isIso_ι_appLE {X : Scheme.{u}} {W : X.Opens} (A : W.toScheme.Opens) :
    IsIso (W.ι.appLE (W.ι ''ᵁ A) A (W.ι.preimage_image_eq A).ge) :=
  inferInstanceAs (IsIso (W.ι.app _ ≫
    W.toScheme.presheaf.map (eqToHom (W.ι.preimage_image_eq A).symm).op))

/-- If `f` restricted to an open `W` of its source is smooth, so is the composite `W.ι ≫ f`. -/
private lemma smooth_ι_comp_of_smooth_resLE {X S : Scheme.{u}} (f : X ⟶ S) (W : X.Opens)
    (h : Smooth (f.resLE ⊤ W le_top)) : Smooth (W.ι ≫ f) := by
  rw [show W.ι ≫ f = f.resLE ⊤ W le_top ≫ (⊤ : S.Opens).ι from (f.resLE_comp_ι le_top).symm]
  infer_instance

/-- A morphism smooth at a point is smooth on the rings of sections of some affine open
neighbourhood of the point lying over a prescribed affine open neighbourhood of its image. -/
private lemma exists_isAffineOpen_smooth_appLE_of_smoothAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (V : S.Opens)
    (hV : IsAffineOpen V) (hxV : x ∈ f ⁻¹ᵁ V) (hf : InfinitesimalLifting.SmoothAt f x) :
    ∃ (A : X.Opens) (_ : IsAffineOpen A) (_ : x ∈ A) (hAV : A ≤ f ⁻¹ᵁ V),
      (f.appLE V A hAV).hom.Smooth := by
  obtain ⟨W, hxW, hfW⟩ := hf
  let g := W.ι ≫ f
  have : Smooth g := smooth_ι_comp_of_smooth_resLE f W hfW
  let xW : W.toScheme := ⟨x, hxW⟩
  have hxWV : xW ∈ g ⁻¹ᵁ V := by
    change f x ∈ V
    exact hxV
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAV⟩ :=
    W.toScheme.isBasis_affineOpens.exists_subset_of_mem_open hxWV
      (V.isOpen.preimage g.continuous)
  have hA'V : W.ι ''ᵁ A ≤ f ⁻¹ᵁ V := by
    intro y hy
    change y ∈ W.ι.base '' A at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa [g] using hAV hz
  refine ⟨W.ι ''ᵁ A, hA.image_of_isOpenImmersion _,
    by simpa [xW] using W.mem_ι_image_iff.mpr hxA, hA'V, ?_⟩
  have hs := g.smooth_appLE hV hA hAV
  have := isIso_ι_appLE A
  rw [← RingHom.Smooth.propertyIsLocal.respectsIso.cancel_right_isIso
    (f.appLE V (W.ι ''ᵁ A) hA'V) (W.ι.appLE (W.ι ''ᵁ A) A (W.ι.preimage_image_eq A).ge),
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  dsimp [g] at hs
  convert hs using 1

/-- Smoothness at a point is equivalent to standard smoothness on a suitable affine
neighbourhood lying over any prescribed affine neighbourhood of the image point. -/
@[stacks 01V7]
public lemma smoothAt_iff_exists_affine_isStandardSmooth
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (V : S.Opens)
    (hV : IsAffineOpen V) (hxV : x ∈ f ⁻¹ᵁ V) :
    InfinitesimalLifting.SmoothAt f x ↔
      ∃ (U : X.Opens) (hU : IsAffineOpen U) (_ : x ∈ U)
        (hUV : U ≤ f ⁻¹ᵁ V),
        @AlgebraicGeometry.IsStandardSmooth
          U.toScheme V.toScheme hU hV (f.resLE V U hUV) := by
  constructor
  · intro hf
    obtain ⟨A', hA', hxA', hA'V, hsmooth⟩ :=
      exists_isAffineOpen_smooth_appLE_of_smoothAt f x V hV hxV hf
    algebraize [(f.appLE V A' hA'V).hom]
    have : Algebra.IsSmoothAt Γ(S, V) (hA'.primeIdealOf ⟨x, hxA'⟩).asIdeal :=
      inferInstance
    obtain ⟨r, hr, hrstd⟩ :=
      Algebra.IsSmoothAt.exists_notMem_isStandardSmooth Γ(S, V)
        (hA'.primeIdealOf ⟨x, hxA'⟩).asIdeal
    let U : X.Opens := X.basicOpen r
    have hU : IsAffineOpen U := hA'.basicOpen r
    have hxU : x ∈ U := by
      change x ∈ X.basicOpen r
      have hp : hA'.isoSpec.hom ⟨x, hxA'⟩ ∈ PrimeSpectrum.basicOpen r := hr
      rw [← hA'.fromSpec_preimage_basicOpen] at hp
      change hA'.fromSpec (hA'.isoSpec.hom ⟨x, hxA'⟩) ∈ X.basicOpen r at hp
      have heq : hA'.fromSpec (hA'.isoSpec.hom ⟨x, hxA'⟩) = x := by
        change (hA'.isoSpec.hom ≫ hA'.fromSpec) ⟨x, hxA'⟩ = x
        rw [hA'.isoSpec_hom_fromSpec]
        rfl
      rwa [heq] at hp
    have hUV : U ≤ f ⁻¹ᵁ V := (X.basicOpen_le r).trans hA'V
    refine ⟨U, hU, hxU, hUV, ?_⟩
    have : IsLocalization.Away r Γ(X, U) := hA'.isLocalization_basicOpen r
    let : Algebra Γ(X, A') Γ(X, U) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    have happ : f.appLE V U hUV =
        f.appLE V A' hA'V ≫ X.presheaf.map (homOfLE (X.basicOpen_le r)).op := by
      rw [← f.appLE_map hA'V (homOfLE (X.basicOpen_le r)).op]
    apply (RingHom.isStandardSmooth_respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f V U hUV)).mpr
    algebraize [(f.appLE V U hUV).hom]
    have : IsScalarTower Γ(S, V) Γ(X, A') Γ(X, U) :=
      IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom happ)
    have : Algebra.IsStandardSmooth Γ(S, V) (Localization.Away r) := hrstd
    exact Algebra.IsStandardSmooth.of_algEquiv
      ((IsLocalization.algEquiv (.powers r) (Localization.Away r) Γ(X, U)).restrictScalars
        Γ(S, V))
  · rintro ⟨U, hU, hxU, hUV, hs⟩
    exact (smoothAt_iff_exists_affine f x).2
      ⟨U, V, hU, hV, hxU, hUV,
        (RingHom.isStandardSmooth_respectsIso.arrow_mk_iso_iff
          (arrowResLEAppIso f V U hUV)).mp hs |>.smooth⟩

/-- **A morphism of schemes is smooth if and only if it is smooth at every point of its source.**
The neighbourhoods witnessing smoothness at the individual points cover the source, and
smoothness is local on the source. -/
@[ega "IV 17.3.7" "partial"]
public theorem smooth_iff_forall_smoothAt {X S : Scheme.{u}} (f : X ⟶ S) :
    Smooth f ↔ ∀ x : X, InfinitesimalLifting.SmoothAt f x := by
  refine ⟨fun hf x => @smoothAt_of_smooth X S f hf x, fun hf => ?_⟩
  choose U hxU hU using hf
  have : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth.{u}) U ?_ fun x => ?_
  · exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  · exact smooth_ι_comp_of_smooth_resLE f (U x) (hU x)

/-- A morphism of schemes smooth at every point of its source is smooth. -/
public theorem smooth_of_forall_smoothAt {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : ∀ x : X, InfinitesimalLifting.SmoothAt f x) : Smooth f :=
  (smooth_iff_forall_smoothAt f).2 hf

end InfinitesimalLifting
