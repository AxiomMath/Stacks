module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedGenericFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Section
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Stability of the locus `X⁰` under generalization over a discrete valuation ring

Let `R` be a discrete valuation ring with closed point `0` and generic point `η`, and let
`f : X ⟶ Spec R` be flat and of finite presentation with a specified section `s`, as in
Situation 055L. If the fibre `X_0` is reduced and a point `x` of `X_0` lies in the locus `X⁰`,
then every generalization of `x` lies in `X⁰` as well.

This is the discrete valuation ring case of the stability of `X⁰` under generalization, the
third and last step of the proof of Stacks Tag 055Q.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_mem_connected_open`: if a connected
  open subscheme `W` contains `s(0)`, then every point of `W` in the generic fibre lies in
  `X⁰`. This is where Stacks Tag 055J is applied.
* `AlgebraicGeometry.ConnectedAlongSection.mem_locus_of_specializes_over_dvr`: the discrete
  valuation ring case of the stability of `X⁰` under generalization.

## Implementation notes

The open subscheme used in the second result is the connected component, inside
`X \ (X_0 \ X⁰_0)`, of the point `s(0)`; it is open because `X` is a Noetherian space, and its
closed fibre is contained in the connected component `X⁰_0`, hence connected. Stacks Tag 055J
then makes its generic fibre connected, and the image of that generic fibre in `X_η` is a
connected subset containing the point selected by the section, so it lies in `X⁰_η`.

The sectioned morphism is presented by its data `X`, `f`, `s` rather than by a term of
`AlgebraicGeometry.ConnectedAlongSection`, because the target has to be literally `Spec R`;
this follows
`AlgebraicGeometry.ConnectedAlongSection.isLocallyConstructible_locus_over_spec`. The closed
and the generic point of `Spec R` are taken as variables pinned by an equation rather than
written out, because the written-out forms live in `PrimeSpectrum R` and are therefore not
recognized by `rewrite`, which works at `instances` transparency, as points of the scheme
`Spec R`.

## References

* [Stacks Project, Tag 055J](https://stacks.math.columbia.edu/tag/055J)
* [Stacks Project, Tag 055L](https://stacks.math.columbia.edu/tag/055L)
* [Stacks Project, Tag 055Q](https://stacks.math.columbia.edu/tag/055Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProperGeomConnected (isOpen_connectedComponent_of_finite
  finite_connectedComponents_of_noetherianSpace)

universe u

namespace AlgebraicGeometry

/-- The map from a scheme-theoretic fibre to the source is injective. -/
theorem Scheme.Hom.fiberι_injective {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    Function.Injective (f.fiberι y) := by
  intro a b h
  refine (f.fiberHomeo y).injective (Subtype.ext ?_)
  rw [f.fiberHomeo_apply, f.fiberHomeo_apply, h]

/-- The image in the source of a closed subset of the fibre over a closed point is closed. -/
theorem Scheme.Hom.isClosed_image_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (hy : IsClosed ({y} : Set Y)) {A : Set (f.fiber y)} (hA : IsClosed A) :
    IsClosed (f.fiberι y '' A) := by
  have himg : f.fiberι y '' A = Subtype.val '' (f.fiberHomeo y '' A) := by
    rw [Set.image_image]
    exact Set.image_congr' fun a => (f.fiberHomeo_apply y a).symm
  rw [himg]
  exact (hy.preimage f.continuous).isClosedMap_subtype_val _ ((f.fiberHomeo y).isClosedMap _ hA)

/-- In a Noetherian space, the connected component of a point inside an open set is open. -/
theorem isOpen_connectedComponentIn_of_noetherianSpace {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] {U : Set α} (hU : IsOpen U) {a : α} (ha : a ∈ U) :
    IsOpen (connectedComponentIn U a) := by
  rw [connectedComponentIn_eq_image ha]
  have : Finite (ConnectedComponents U) := finite_connectedComponents_of_noetherianSpace
  exact hU.isOpenMap_subtype_val _ (isOpen_connectedComponent_of_finite _)

namespace ConnectedAlongSection

/-- A point specializing to `a` lies in the connected component of `a`, the closure of a point
being connected. -/
private theorem mem_connectedComponent_of_specializes {α : Type*} [TopologicalSpace α]
    {a b : α} (h : b ⤳ a) : b ∈ connectedComponent a :=
  isConnected_singleton.closure.isPreconnected.subset_connectedComponent
    (specializes_iff_mem_closure.mp h) (subset_closure rfl)

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **Stacks Project, Tag 055J** with the two points of `Spec R` taken as variables. -/
private theorem connectedSpace_fiber_generic {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [ConnectedSpace X]
    {σ η : ↥(Spec (CommRingCat.of R))} (hσ : σ = IsLocalRing.closedPoint R)
    (hη : η = (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) (hred : IsReduced (f.fiber σ)) :
    ConnectedSpace (f.fiber η) := by
  subst hσ hη
  exact connectedSpace_fiber_bot_of_isReduced_fiber_closedPoint f

/-- The generic point of `Spec R` specializes to the closed point. -/
private theorem specializes_of_eq {σ η : ↥(Spec (CommRingCat.of R))}
    (hσ : σ = IsLocalRing.closedPoint R)
    (hη : η = (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) : η ⤳ σ := by
  subst hσ hη
  exact IsLocalRing.specializes_closedPoint _

/-- The generic point of `Spec R` is not the closed point, `R` not being a field. -/
private theorem ne_of_eq {σ η : ↥(Spec (CommRingCat.of R))}
    (hσ : σ = IsLocalRing.closedPoint R)
    (hη : η = (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) : η ≠ σ := by
  subst hσ hη
  exact fun h => IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal h).symm

/-- The closed point of `Spec R` is a closed point. -/
private theorem isClosed_singleton_of_eq {σ : ↥(Spec (CommRingCat.of R))}
    (hσ : σ = IsLocalRing.closedPoint R) : IsClosed ({σ} : Set ↥(Spec (CommRingCat.of R))) := by
  subst hσ
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
    (IsLocalRing.maximalIdeal.isMaximal R)

/-- **The application of Stacks Tag 055J.** Let `f : X ⟶ Spec R` be flat with a section `s`,
where `R` is a discrete valuation ring whose closed fibre is reduced. If `W` is a connected
open subscheme of `X` containing the value of the section at the closed point `σ`, then every
point of `W` lying in the fibre over the generic point `η` belongs to the locus `X⁰`. -/
theorem mem_locus_of_mem_connected_open {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (s : Spec (CommRingCat.of R) ⟶ X) (hsec : s ≫ f = 𝟙 (Spec (CommRingCat.of R))) [Flat f]
    {σ η : ↥(Spec (CommRingCat.of R))} (hσ : σ = IsLocalRing.closedPoint R)
    (hη : η = (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) (hred : IsReduced (f.fiber σ))
    (W : X.Opens) (hWconn : ConnectedSpace W.toScheme) (hsW : s σ ∈ W)
    {x' : X} (hx'W : x' ∈ W) (hx' : f x' = η) :
    x' ∈ (⟨X, Spec (CommRingCat.of R), f, s, hsec⟩ : ConnectedAlongSection.{u}).locus := by
  let D : ConnectedAlongSection.{u} := ⟨X, Spec (CommRingCat.of R), f, s, hsec⟩
  have hfs : ∀ y, f (s y) = y := by
    intro y
    rw [← Scheme.Hom.comp_apply, hsec]
    rfl
  have : ConnectedSpace ((W.ι ≫ f).fiber η) :=
    connectedSpace_fiber_generic (W.ι ≫ f) hσ hη (isReduced_fiber_comp W.ι f σ)
  let ρ : (W.ι ≫ f).fiber η ⟶ f.fiber η :=
    pullback.lift ((W.ι ≫ f).fiberι η ≫ W.ι) ((W.ι ≫ f).fiberToSpecResidueField η) (by
      rw [Category.assoc]
      exact (W.ι ≫ f).fiber_fac η)
  have hρfst : ρ ≫ f.fiberι η = (W.ι ≫ f).fiberι η ≫ W.ι := pullback.lift_fst _ _ _
  have hρ : ∀ z, f.fiberι η (ρ z) = W.ι ((W.ι ≫ f).fiberι η z) := fun z => by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun m : (W.ι ≫ f).fiber η ⟶ X => m z) hρfst
  have hpoint : ∀ w : W.toScheme, f (W.ι w) = η →
      ∃ z, f.fiberι η (ρ z) = W.ι w := by
    intro w hw
    refine ⟨((W.ι ≫ f).fiberHomeo η).symm ⟨w, by
      rwa [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply]⟩, ?_⟩
    rw [hρ, (W.ι ≫ f).fiberι_fiberHomeo_symm]
  obtain ⟨z₀, hz₀⟩ :=
    hpoint ⟨s η, ((specializes_of_eq hσ hη).map s.continuous).mem_open W.isOpen hsW⟩ (hfs _)
  obtain ⟨z₁, hz₁⟩ := hpoint ⟨x', hx'W⟩ hx'
  have hrange : Set.range ρ ⊆ D.fiberComponent η := by
    change Set.range ρ ⊆ connectedComponent (D.sectionPoint η)
    exact (isConnected_range ρ.continuous).isPreconnected.subset_connectedComponent
      ⟨z₀, f.fiberι_injective _ (hz₀.trans (D.fiberι_sectionPoint η).symm)⟩
  exact (D.mem_locus x').mpr ⟨η, ρ z₁, hrange ⟨z₁, rfl⟩, hz₁⟩

/-- **The discrete valuation ring case of Stacks Tag 055Q.** Let `f : X ⟶ Spec R` be flat and
of finite presentation with a section `s`, where `R` is a discrete valuation ring whose fibre
over the closed point `σ` is reduced. If a point `x` over `σ` lies in the locus `X⁰`, then so
does every point over the generic point `η` which specializes to `x`. -/
theorem mem_locus_of_specializes_over_dvr {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (s : Spec (CommRingCat.of R) ⟶ X) (hsec : s ≫ f = 𝟙 (Spec (CommRingCat.of R)))
    (hfp : FinitePresentation f) [Flat f]
    {σ η : ↥(Spec (CommRingCat.of R))} (hσ : σ = IsLocalRing.closedPoint R)
    (hη : η = (⟨⊥, inferInstance⟩ : PrimeSpectrum R)) (hred : IsReduced (f.fiber σ))
    {x x' : X} (hx0 : f x = σ) (hx'0 : f x' = η)
    (hx : x ∈ (⟨X, Spec (CommRingCat.of R), f, s, hsec⟩ : ConnectedAlongSection.{u}).locus)
    (hspec : x' ⤳ x) :
    x' ∈ (⟨X, Spec (CommRingCat.of R), f, s, hsec⟩ : ConnectedAlongSection.{u}).locus := by
  let D : ConnectedAlongSection.{u} := ⟨X, Spec (CommRingCat.of R), f, s, hsec⟩
  have : LocallyOfFinitePresentation f := hfp.1
  have : QuasiCompact f := hfp.2.1
  have : QuasiSeparated f := hfp.2.2
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  have : NoetherianSpace (f.fiber σ) :=
    (noetherianSpace_iff_of_homeomorph (f.fiberHomeo σ)).mpr inferInstance
  have : Finite (ConnectedComponents (f.fiber σ)) :=
    finite_connectedComponents_of_noetherianSpace
  have hA0 : IsOpen (D.fiberComponent σ) := by
    change IsOpen (connectedComponent (D.sectionPoint σ))
    exact isOpen_connectedComponent_of_finite _
  have hC : IsClosed (f.fiberι σ '' (D.fiberComponent σ)ᶜ) :=
    f.isClosed_image_fiberι (isClosed_singleton_of_eq hσ) hA0.isClosed_compl
  have hsub : f.fiberι σ '' D.fiberComponent σ ⊆ (f.fiberι σ '' (D.fiberComponent σ)ᶜ)ᶜ := by
    rintro - ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact hb (f.fiberι_injective _ hab ▸ ha)
  have hxL : x ∈ f.fiberι σ '' D.fiberComponent σ := by
    obtain ⟨y, z, hz, hzx⟩ := (D.mem_locus x).mp hx
    obtain rfl : y = σ := (hzx ▸ D.f.apply_fiberι y z : f x = y).symm.trans hx0
    exact ⟨z, hz, hzx⟩
  have hsL : s σ ∈ f.fiberι σ '' D.fiberComponent σ :=
    ⟨D.sectionPoint σ, D.sectionPoint_mem_fiberComponent σ, D.fiberι_sectionPoint σ⟩
  have hx'C : x' ∈ (f.fiberι σ '' (D.fiberComponent σ)ᶜ)ᶜ := by
    rintro ⟨a, -, rfl⟩
    exact ne_of_eq hσ hη (hx'0.symm.trans (f.apply_fiberι σ a))
  have hLW : f.fiberι σ '' D.fiberComponent σ ⊆
      connectedComponentIn (f.fiberι σ '' (D.fiberComponent σ)ᶜ)ᶜ (s σ) :=
    (isConnected_connectedComponent.image _ (f.fiberι σ).continuous.continuousOn
      ).isPreconnected.subset_connectedComponentIn hsL hsub
  have hx'W : x' ∈ connectedComponentIn (f.fiberι σ '' (D.fiberComponent σ)ᶜ)ᶜ (s σ) := by
    rw [connectedComponentIn_eq (hLW hxL), connectedComponentIn_eq_image (hsub hxL)]
    exact ⟨⟨x', hx'C⟩, mem_connectedComponent_of_specializes
      ((subtype_specializes_iff _ _).mpr hspec), rfl⟩
  exact mem_locus_of_mem_connected_open f s hsec hσ hη hred
    ⟨_, isOpen_connectedComponentIn_of_noetherianSpace hC.isOpen_compl (hsub hsL)⟩
    (isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr (hsub hsL)))
    (mem_connectedComponentIn (hsub hsL)) hx'W hx'0

end ConnectedAlongSection

end AlgebraicGeometry

end
