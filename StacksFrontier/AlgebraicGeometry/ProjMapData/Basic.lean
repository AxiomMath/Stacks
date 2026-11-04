module

public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.MY

/-!
# Tag 01MY part (2): the induced morphism on standard opens, and its uniqueness

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings and let
`U(ψ) = ⋃_{d > 0} ⋃_{f ∈ 𝒜 d} D₊(ψ f) ⊆ Proj ℬ` be the open on which it induces a morphism
to `Proj 𝒜`, built as `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`. This file proves the
two assertions of Tag 01MY that concern that morphism alone:

* on each standard open `D₊(ψ f)` of the domain, the morphism is the one induced by the map
  `𝒜_{(f)} → ℬ_{(ψ f)}` of degree-zero homogeneous localizations, read as a square of
  structure-sheaf sections;
* that square, together with the identification of inverse images of standard opens, pins the
  morphism down uniquely.

Both are obtained from one reduction, `awayToSection_appLE_iff`: for a morphism
`p : U(ψ) ⟶ Proj 𝒜` whose inverse image of `D₊(f)` contains `W = U(ψ).ι ⁻¹ᵁ D₊(ψ f)`, the
square of degree-zero localizations over `W` holds precisely when `p` restricted along `W.ι`
agrees with the affine morphism `mapAwayHom` attached to `f`. The reduction is a chain of
cancellations: `W` is an affine open of `U(ψ)`, so `W.toSpecΓ` is an isomorphism, and `Spec` is
faithful, which turns the equality of ring maps into an equality of morphisms into
`Spec 𝒜_{(f)}`; composing with the open immersion `Proj.awayι` turns that into an equality of
morphisms into `Proj 𝒜`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistChain.awayToSection_appLE_iff`: the reduction just
  described.
* `Stacks.AlgebraicGeometry.ProjTwistChain.awayToSection_comp_appLE_mapHom`: Tag 01MY part (2),
  the localization square for `mapHom`. This is the analogue, with no hypothesis on `ψ`, of
  Mathlib's `AlgebraicGeometry.Proj.awayToSection_comp_appLE`, which is stated for
  `AlgebraicGeometry.Proj.map` and therefore assumes `ℬ₊ ≤ 𝒜₊.map ψ`.
* `Stacks.AlgebraicGeometry.ProjTwistChain.eq_mapHom`: uniqueness of the morphism characterized
  by Tag 01MY part (2).

## Implementation notes

Tag 01MY is a statement about a *triple* `(U(ψ), r_ψ, θ)`, where `θ` is a map of `ℤ`-graded
`𝒪_{U(ψ)}`-algebras `r_ψ^*(⨁_d 𝒪_X(d)) → ⨁_d 𝒪_{U(ψ)}(d)`. Only the `r_ψ` half is proved here,
and it is proved *off the bundle*: the statements below are about `mapHom` directly rather than
about the `hom` field of a record that also carries `θ`. This is the seam the source itself
uses — its proof opens "Clearly condition (2) uniquely determines the morphism of schemes and
the open subset `U(ψ)`", and only then determines `θ`. Nothing is weakened by the split:
the two statements below quantify over exactly the data the source's condition (2) quantifies
over, with the hypotheses the source states, and neither mentions `θ`.

The `θ` half is not proved, and two of the source's clauses about it cannot presently be
stated in this library at all. Writing down the compatibility of `θ` with the multiplication
`𝒪(a) ⊗ 𝒪(b) → 𝒪(a + b)` needs the comparison isomorphism between the pullback of a tensor
product of module sheaves and the tensor product of the pullbacks (Tag 01CD); no declaration
in this library provides it. The remaining clauses — the degree-`d` global-section square and
the unit law — are stateable, via
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections` and
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`.

This file previously recorded `θ` itself as blocked, on the ground that `mapHom` is produced by
gluing over the cover `D₊(ψ f)`, so its action on sections over a general open is pinned down
only up to the local identifications and the source's pointwise formula is unavailable as a
formula for a morphism out of the pullback. **That was wrong and is withdrawn.** The pointwise
formula over an arbitrary open is `Stacks.AlgebraicGeometry.ProjTwistCompare.val_app`
(`StacksFrontier/AlgebraicGeometry/ProjTwistCompare/SectionValue.lean:189`), derived from the
standard-open square proved below without unwinding the gluing and without computing a stalk
map; the base map it rests on is `.mapHom_base_asHomogeneousIdeal` (`StacksFrontier/AlgebraicGeometry/ProjTwistCompare/BaseMap.lean:164`), which
is Mathlib's `ProjectiveSpectrum.comapFun` without that file's hypothesis on the irrelevant
ideals. So `θ` is assembly — the presheaf-of-modules morphism, its naturality, and two
adjunction steps — and what remains genuinely absent is Tag 01CD, which blocks the
multiplication clauses rather than `θ`.

A record bundling `r_ψ` with a family of twist maps and *no* axiom relating them would not fix
this. Such a record is inhabited by taking every twist map to be zero, and the two assertions
proved here never mention the twist maps, so they would hold of that witness while saying
nothing about `θ`. The witness is refuted by the source, though, not merely uninformative: the
degree-`d` global-section clause applied to `1 ∈ 𝒜 0` would force the global section of
`𝒪_{U(ψ)}(0)` attached to `1` to vanish. So the source's clauses do pin the triple down; they
are simply not all available yet, which is why the morphism is stated here on its own.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization TopologicalSpace CategoryTheory
open Stacks.AlgebraicGeometry.ProjShared

namespace Stacks.AlgebraicGeometry.ProjTwistChain

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The standard open `D₊(ψ f)`, read as an open of the domain of definition `U(ψ)`, is an
affine open. -/
public theorem isAffineOpen_preimage_basicOpen (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) :
    IsAffineOpen ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)) :=
  (Proj.isAffineOpen_basicOpen ℬ (ψ f) (mem_of_mem 𝒜 ℬ ψ hf) hd).preimage_of_isOpenImmersion
    _ (by rw [Scheme.Opens.opensRange_ι]; exact basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The inclusion of `D₊(ψ f)` into `U(ψ)` restricted from the inclusion of `U(ψ)` into
`Proj ℬ`, followed by the comparison with `D₊(ψ f)` itself, is the inclusion of
`U(ψ).ι ⁻¹ᵁ D₊(ψ f)`. -/
public theorem resLE_ι_comp_homOfLE (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) :
    Scheme.Hom.resLE (mapDomain 𝒜 ℬ ψ).ι (Proj.basicOpen ℬ (ψ f))
        ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)) le_rfl ≫
      (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf) =
      ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)).ι := by
  rw [← cancel_mono (mapDomain 𝒜 ℬ ψ).ι, Category.assoc, Scheme.homOfLE_ι,
    Scheme.Hom.resLE_comp_ι]

/-- Composing the comparison `Proj 𝒜 |_{D₊(f)} ⟶ Spec 𝒜_{(f)}` with the open immersion
`Spec 𝒜_{(f)} ⟶ Proj 𝒜` gives the inclusion of `D₊(f)`. -/
public theorem basicOpenToSpec_comp_awayι {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    Proj.basicOpenToSpec 𝒜 f ≫ Proj.awayι 𝒜 f hf hd = (Proj.basicOpen 𝒜 f).ι := by
  rw [← Proj.basicOpenIsoSpec_hom 𝒜 f hf hd, Proj.awayι, Iso.hom_inv_id_assoc]

/-- The square of degree-zero homogeneous localizations attached to `f` holds for a morphism
`p : U(ψ) ⟶ Proj 𝒜` exactly when `p`, restricted to `D₊(ψ f)`, is the affine morphism
`mapAwayHom` induced by `𝒜_{(f)} → ℬ_{(ψ f)}`.

This is the reduction behind both assertions of Tag 01MY part (2). -/
public theorem awayToSection_appLE_iff (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) (p : (mapDomain 𝒜 ℬ ψ).toScheme ⟶ AlgebraicGeometry.Proj 𝒜)
    (e : (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f) ≤ p ⁻¹ᵁ Proj.basicOpen 𝒜 f) :
    (Proj.awayToSection 𝒜 f ≫ Scheme.Hom.appLE p (Proj.basicOpen 𝒜 f)
        ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)) e =
      CommRingCat.ofHom (Away.map ψ f) ≫ Proj.awayToSection ℬ (ψ f) ≫
        Scheme.Hom.appLE (mapDomain 𝒜 ℬ ψ).ι (Proj.basicOpen ℬ (ψ f))
          ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)) le_rfl) ↔
    ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)).ι ≫ p =
      Scheme.Hom.resLE (mapDomain 𝒜 ℬ ψ).ι (Proj.basicOpen ℬ (ψ f))
        ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)) le_rfl ≫
          mapAwayHom 𝒜 ℬ ψ hd hf := by
  rw [← Spec.map_inj, ← cancel_epi
    (isAffineOpen_preimage_basicOpen 𝒜 ℬ ψ hd hf).isoSpec.hom, IsAffineOpen.isoSpec_hom]
  simp only [Spec.map_comp, Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  rw [show (Proj.basicOpen 𝒜 f).toSpecΓ ≫ Spec.map (Proj.awayToSection 𝒜 f) =
      Proj.basicOpenToSpec 𝒜 f from rfl,
    ← Category.assoc (Proj.basicOpen ℬ (ψ f)).toSpecΓ,
    show (Proj.basicOpen ℬ (ψ f)).toSpecΓ ≫ Spec.map (Proj.awayToSection ℬ (ψ f)) =
      Proj.basicOpenToSpec ℬ (ψ f) from rfl,
    ← cancel_mono (Proj.awayι 𝒜 f hf hd)]
  simp only [Category.assoc, basicOpenToSpec_comp_awayι 𝒜 hd hf,
    show Proj.basicOpenToSpec ℬ (ψ f) ≫ Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫
      Proj.awayι 𝒜 f hf hd = mapAwayHom 𝒜 ℬ ψ hd hf from rfl]
  rw [Scheme.Hom.resLE_comp_ι]

/-- **Stacks 01MY (2)**: on the standard open `D₊(ψ f)` of the domain of definition, the
morphism induced by `ψ` is the one induced by the map `𝒜_{(f)} → ℬ_{(ψ f)}` of degree-zero
homogeneous localizations.

With no hypothesis on `ψ`; compare `AlgebraicGeometry.Proj.awayToSection_comp_appLE`, which
states this for `AlgebraicGeometry.Proj.map` and so assumes `ℬ₊ ≤ 𝒜₊.map ψ`. -/
@[stacks 01MY "part (2), localization map on standard opens"]
public theorem awayToSection_comp_appLE_mapHom (ψ : 𝒜 →+*ᵍ ℬ) (f : A) (d : ℕ) (hf : f ∈ 𝒜 d)
    (hd : 0 < d) :
    Proj.awayToSection 𝒜 f ≫
      Scheme.Hom.appLE (mapHom 𝒜 ℬ ψ) (Proj.basicOpen 𝒜 f)
        ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f))
        (by rw [mapHom_preimage_basicOpen 𝒜 ℬ ψ f d hf hd]) =
    CommRingCat.ofHom (Away.map ψ f) ≫
      Proj.awayToSection ℬ (ψ f) ≫
        Scheme.Hom.appLE (mapDomain 𝒜 ℬ ψ).ι (Proj.basicOpen ℬ (ψ f))
          ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)) le_rfl :=
  (awayToSection_appLE_iff 𝒜 ℬ ψ hd hf _ _).mpr (by
    rw [← resLE_ι_comp_homOfLE 𝒜 ℬ ψ hd hf, Category.assoc, homOfLE_mapHom])

/-- **Stacks 01MY (2), uniqueness**: a morphism out of the domain of definition that has the
inverse images of standard opens of Tag 01MY (2), and that on each of them is induced by the
corresponding map of degree-zero homogeneous localizations, is `mapHom`. -/
@[stacks 01MY "uniqueness of the scheme morphism"]
public theorem eq_mapHom (ψ : 𝒜 →+*ᵍ ℬ)
    (p : (mapDomain 𝒜 ℬ ψ).toScheme ⟶ AlgebraicGeometry.Proj 𝒜)
    (hopen : ∀ (f : A) (d : ℕ), f ∈ 𝒜 d → 0 < d →
      p ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f =
        (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen ℬ (ψ f))
    (hlocal : ∀ (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d),
      Proj.awayToSection 𝒜 f ≫
        Scheme.Hom.appLE p (Proj.basicOpen 𝒜 f)
          ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f))
          (by rw [hopen f d hf hd]) =
      CommRingCat.ofHom (Away.map ψ f) ≫
        Proj.awayToSection ℬ (ψ f) ≫
          Scheme.Hom.appLE (mapDomain 𝒜 ℬ ψ).ι (Proj.basicOpen ℬ (ψ f))
            ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)) le_rfl) :
    p = mapHom 𝒜 ℬ ψ := by
  refine mapDomain_hom_ext 𝒜 ℬ ψ p (mapHom 𝒜 ℬ ψ) fun d hd f hf => ?_
  have hsub : Set.range ((AlgebraicGeometry.Proj ℬ).homOfLE
        (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf)).base ⊆
      Set.range ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)).ι.base := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
      Scheme.opensRange_homOfLE, Scheme.Opens.opensRange_ι]
  have hι := AlgebraicGeometry.IsOpenImmersion.lift_fac
    ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)).ι
    ((AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf)) hsub
  have hp := (awayToSection_appLE_iff 𝒜 ℬ ψ hd hf p _).mp (hlocal f d hf hd)
  have hq := (awayToSection_appLE_iff 𝒜 ℬ ψ hd hf (mapHom 𝒜 ℬ ψ) _).mp
    (awayToSection_comp_appLE_mapHom 𝒜 ℬ ψ f d hf hd)
  rw [← hι, Category.assoc, Category.assoc, hp, hq]

end Stacks.AlgebraicGeometry.ProjTwistChain

end
