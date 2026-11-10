module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpec

/-!
# The cone projection on an affine chart

Let `A` and `B` be nonnegatively graded rings, `c : ConeData 𝒜 ℬ` cone data, and let
`π : L = Proj B ⟶ P = Proj A` be the cone projection, the morphism induced by the graded ring
homomorphism `ψ : A → B`. For `f` homogeneous of positive degree the standard open `D₊(ψ f)` is
the inverse image of `D₊(f)`, and both are affine: `D₊(f) = Spec A_{(f)}` and
`D₊(ψ f) = Spec B_{(ψ f)}` for the degree-zero localizations. This file shows that on those
charts `π` is `Spec` of the map `A_{(f)} ⟶ B_{(ψ f)}` of degree-zero localizations.

This is the analogue, for the cone projection, of Mathlib's
`AlgebraicGeometry.Proj.awayι_comp_map`, which does not apply here because `ψ` need not carry
the irrelevant ideal of `A` onto one generating that of `B` — only its radical, as the
implementation notes of `StacksFrontier/AlgebraicGeometry/Constructions/ProjAndSpec.lean` explain.

## Main results

* `Stacks.AlgebraicGeometry.ProjAndSpec.awayι_comp_pi`: **on the affine chart
  `Spec B_{(ψ f)}` of `L` the cone projection is `Spec` of
  `HomogeneousLocalization.Away.map ψ f`.**
* `Stacks.AlgebraicGeometry.ProjAndSpec.awayToSection_comp_pi_appLE`: **on functions over
  `D₊(f)` the cone projection is that same map of degree-zero localizations**, read through the
  identifications `A_{(f)} = Γ(P, D₊(f))` and `B_{(ψ f)} = Γ(L, D₊(ψ f))`. This is what says
  which `A_{(f)}`-algebra the functions on the part of `L` over `D₊(f)` form, and so what the
  scalar multiplication is in any comparison of `π_* 𝒪_L` with a sheaf of `𝒪_P`-modules over a
  standard open.
* `Stacks.AlgebraicGeometry.ProjChartSections.awayToSection_comp_awayι_appLE`: the same
  bookkeeping for the chart of `Proj A` itself, which the previous statement is proved from:
  reading the sections of `𝒪_P` over `D₊(f)` on the chart `Spec A_{(f)}` inverts
  `AlgebraicGeometry.Proj.awayToSection`.

## Implementation notes

`appLE_congr_hom` transports `appLE` along an equality of morphisms: the equality cannot be
rewritten inside `appLE` directly, because the inequality of opens that `appLE` carries mentions
the morphism.

## References

* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjTwistChain Stacks.AlgebraicGeometry.RelativeProj

universe u w

namespace Stacks.AlgebraicGeometry.ProjAndSpec

variable {A B : Type u} {σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (c : ConeData 𝒜 ℬ) {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d)

/-- **On the affine chart `Spec B_{(ψ f)}` of `L` the cone projection is `Spec` of the map
`A_{(f)} ⟶ B_{(ψ f)}` of degree-zero localizations.** The chart of `L` is carried by the
inclusion of `D₊(ψ f)`, on which the cone projection is the local morphism attached to `f`, and
that local morphism is by construction the one of the degree-zero localizations. -/
@[stacks 0EKG "the cone projection on an affine chart is Spec of the map of degree-zero \
localizations"]
theorem awayι_comp_pi :
    Proj.awayι ℬ (c.psi f) (c.psi.map_mem hf) hd ≫ pi c =
      Spec.map (CommRingCat.ofHom (Away.map c.psi f)) ≫ Proj.awayι 𝒜 f hf hd := by
  rw [pi, Proj.awayι, Category.assoc, ι_mapHomOfTop 𝒜 ℬ c.psi _ hd hf, mapAwayHom,
    ← Proj.basicOpenIsoSpec_hom ℬ _ _ hd, Iso.inv_hom_id_assoc]
  exact c.psi.map_mem hf

end Stacks.AlgebraicGeometry.ProjAndSpec

namespace Stacks.AlgebraicGeometry.ProjChartSections

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {f : A}

/-- The chart `Spec A_{(f)} ⟶ Proj A` has the standard open `D₊(f)` for inverse image of
`D₊(f)`: it is an isomorphism onto that open. -/
theorem awayι_preimage_basicOpen_self (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Proj.awayι 𝒜 f hf hd ⁻¹ᵁ Proj.basicOpen 𝒜 f = ⊤ := by
  rw [Proj.awayι, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self,
    Scheme.Hom.preimage_top]

/-- Restriction along the inclusion of an open, read as a map of sections over that open, is the
canonical identification of the sections of the open subscheme over `⊤`. -/
theorem ι_appLE_top {X : Scheme.{u}} (U : X.Opens) :
    U.ι.appLE U ⊤ (by simp) = U.topIso.inv := by
  rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  rfl

/-- Over the top open of both schemes, `appLE` is the map on global sections. -/
theorem appLE_top_top {X Y : Scheme.{u}} (g : X ⟶ Y) (e : (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤) :
    g.appLE ⊤ ⊤ e = g.appTop := by
  have h : X.presheaf.map (homOfLE e).op = CategoryStruct.id Γ(X, ⊤) := by
    change X.presheaf.map (CategoryStruct.id (Opposite.op (⊤ : X.Opens))) = _
    exact X.presheaf.map_id _
  rw [Scheme.Hom.appLE, h]
  exact Category.comp_id _

/-- On the chart `Spec A_{(f)}` the sections of `𝒪_P` over `D₊(f)` are read by the inverse of
the identification `AlgebraicGeometry.Proj.awayToSection` of `A_{(f)}` with those sections. -/
theorem awayToSection_comp_awayι_appLE (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Proj.awayToSection 𝒜 f ≫ (Proj.awayι 𝒜 f hf hd).appLE (Proj.basicOpen 𝒜 f) ⊤
        (awayι_preimage_basicOpen_self 𝒜 hf hd).ge =
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 f))).inv := by
  have hsplit : (Proj.awayι 𝒜 f hf hd).appLE (Proj.basicOpen 𝒜 f) ⊤
        (awayι_preimage_basicOpen_self 𝒜 hf hd).ge =
      (Proj.basicOpen 𝒜 f).ι.appLE (Proj.basicOpen 𝒜 f) ⊤ (by simp) ≫
        ((Proj.basicOpenIsoSpec 𝒜 f hf hd).inv).appLE ⊤ ⊤ (by simp) :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have hhom : ((Proj.basicOpenIsoSpec 𝒜 f hf hd).hom).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 f))).hom ≫
        Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv := by
    rw [Proj.basicOpenIsoSpec_hom]
    exact Proj.basicOpenToSpec_app_top 𝒜 f
  have hcancel : ((Proj.basicOpenIsoSpec 𝒜 f hf hd).hom).appTop ≫
      ((Proj.basicOpenIsoSpec 𝒜 f hf hd).inv).appTop = CategoryStruct.id _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id, Scheme.Hom.id_appTop]
  have hinvapp : ((Proj.basicOpenIsoSpec 𝒜 f hf hd).inv).appLE ⊤ ⊤ (by simp) =
      ((Proj.basicOpenIsoSpec 𝒜 f hf hd).inv).appTop := appLE_top_top _ _
  rw [hsplit, hinvapp, ι_appLE_top, ← Category.assoc,
    show Proj.awayToSection 𝒜 f ≫ (Proj.basicOpen 𝒜 f).topIso.inv =
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 f))).inv ≫
        ((Proj.basicOpenIsoSpec 𝒜 f hf hd).hom).appTop from by
      rw [hhom, Iso.inv_hom_id_assoc],
    Category.assoc, hcancel, Category.comp_id]

/-- Two equal morphisms have the same maps on sections. -/
theorem appLE_congr_hom {X Y : Scheme.{u}} {g₁ g₂ : X ⟶ Y} (h : g₁ = g₂) (U : Y.Opens)
    (V : X.Opens) (e₁ : V ≤ g₁ ⁻¹ᵁ U) (e₂ : V ≤ g₂ ⁻¹ᵁ U) :
    g₁.appLE U V e₁ = g₂.appLE U V e₂ := by
  subst h
  rfl

end Stacks.AlgebraicGeometry.ProjChartSections

namespace Stacks.AlgebraicGeometry.ProjAndSpec

open Stacks.AlgebraicGeometry.ProjChartSections

variable {A B : Type u} {σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (c : ConeData 𝒜 ℬ) {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d)

/-- **The cone projection acts on functions over a standard open by the map of degree-zero
localizations.** Through the identifications `A_{(f)} = Γ(P, D₊(f))` and
`B_{(ψ f)} = Γ(L, D₊(ψ f))` of [Stacks, Tag 01M6], the pullback of functions along `π` is
`HomogeneousLocalization.Away.map ψ f`. This is the module-theoretic content of the chart
description `Stacks.AlgebraicGeometry.ProjAndSpec.awayι_comp_pi`: it says which
`A_{(f)}`-algebra the functions on the part of `L` over `D₊(f)` form. -/
@[stacks 0EKG "the cone projection on functions over a standard open is the map of degree-zero \
localizations"]
theorem awayToSection_comp_pi_appLE :
    Proj.awayToSection 𝒜 f ≫ (pi c).appLE (Proj.basicOpen 𝒜 f)
        (Proj.basicOpen ℬ (c.psi f)) (pi_preimage_basicOpen c f d hf hd).ge =
      CommRingCat.ofHom (Away.map c.psi f) ≫ Proj.awayToSection ℬ (c.psi f) := by
  have hψf : c.psi f ∈ ℬ d := c.psi.map_mem hf
  have hpre1 : (Proj.awayι ℬ (c.psi f) hψf hd ≫ pi c) ⁻¹ᵁ Proj.basicOpen 𝒜 f = ⊤ := by
    rw [Scheme.Hom.comp_preimage, pi_preimage_basicOpen c f d hf hd,
      awayι_preimage_basicOpen_self ℬ hψf hd]
  have hpre2 : (Spec.map (CommRingCat.ofHom (Away.map c.psi f)) ≫
      Proj.awayι 𝒜 f hf hd) ⁻¹ᵁ Proj.basicOpen 𝒜 f = ⊤ := by
    rwa [← awayι_comp_pi c hd hf]
  have hchart : (Proj.awayι ℬ (c.psi f) hψf hd ≫ pi c).appLE
        (Proj.basicOpen 𝒜 f) ⊤ hpre1.ge =
      (Spec.map (CommRingCat.ofHom (Away.map c.psi f)) ≫ Proj.awayι 𝒜 f hf hd).appLE
        (Proj.basicOpen 𝒜 f) ⊤ hpre2.ge :=
    appLE_congr_hom (awayι_comp_pi c hd hf) _ _ _ _
  have hsplit1 : (pi c).appLE (Proj.basicOpen 𝒜 f) (Proj.basicOpen ℬ (c.psi f))
        (pi_preimage_basicOpen c f d hf hd).ge ≫
      (Proj.awayι ℬ (c.psi f) hψf hd).appLE (Proj.basicOpen ℬ (c.psi f)) ⊤
        (awayι_preimage_basicOpen_self ℬ hψf hd).ge =
      (Proj.awayι ℬ (c.psi f) hψf hd ≫ pi c).appLE (Proj.basicOpen 𝒜 f) ⊤ hpre1.ge :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have hsplit2 : (Proj.awayι 𝒜 f hf hd).appLE (Proj.basicOpen 𝒜 f) ⊤
        (awayι_preimage_basicOpen_self 𝒜 hf hd).ge ≫
      (Spec.map (CommRingCat.ofHom (Away.map c.psi f))).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom (Away.map c.psi f)) ≫ Proj.awayι 𝒜 f hf hd).appLE
        (Proj.basicOpen 𝒜 f) ⊤ hpre2.ge :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have hαval : Proj.awayToSection ℬ (c.psi f) ≫
      (Proj.awayι ℬ (c.psi f) hψf hd).appLE (Proj.basicOpen ℬ (c.psi f)) ⊤
        (awayι_preimage_basicOpen_self ℬ hψf hd).ge =
      (Scheme.ΓSpecIso (CommRingCat.of (Away ℬ (c.psi f)))).inv :=
    awayToSection_comp_awayι_appLE ℬ hψf hd
  have hαiso : IsIso ((Proj.awayι ℬ (c.psi f) hψf hd).appLE (Proj.basicOpen ℬ (c.psi f)) ⊤
      (awayι_preimage_basicOpen_self ℬ hψf hd).ge) := by
    rw [show (Proj.awayι ℬ (c.psi f) hψf hd).appLE (Proj.basicOpen ℬ (c.psi f)) ⊤
        (awayι_preimage_basicOpen_self ℬ hψf hd).ge =
        (Proj.basicOpenIsoAway ℬ (c.psi f) hψf hd).inv ≫
          (Scheme.ΓSpecIso (CommRingCat.of (Away ℬ (c.psi f)))).inv from by
      rw [← hαval, ← Proj.basicOpenIsoAway_hom ℬ (c.psi f) hψf hd, Iso.inv_hom_id_assoc]]
    infer_instance
  have hγ : (Spec.map (CommRingCat.ofHom (Away.map c.psi f))).appLE ⊤ ⊤ (by simp) =
      (Spec.map (CommRingCat.ofHom (Away.map c.psi f))).appTop :=
    appLE_top_top _ _
  rw [← cancel_mono ((Proj.awayι ℬ (c.psi f) hψf hd).appLE (Proj.basicOpen ℬ (c.psi f)) ⊤
      (awayι_preimage_basicOpen_self ℬ hψf hd).ge),
    Category.assoc, Category.assoc, hαval, hsplit1, hchart, ← hsplit2, ← Category.assoc,
    awayToSection_comp_awayι_appLE 𝒜 hf hd, hγ, Iso.inv_comp_eq,
    ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end Stacks.AlgebraicGeometry.ProjAndSpec

end
