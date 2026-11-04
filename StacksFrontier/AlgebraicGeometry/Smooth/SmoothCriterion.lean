module

public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import StacksFrontier.Algebra.Module.FinitePresentation.Transport
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite presentation of `a^*Ω_{X/S}` over an arbitrary affine, and rigidity of lifts

This file supplies the two inputs that the correction step (II) of the infinitesimal lifting
criterion [Stacks Project, Tag 02H6] needs and that the chart-local development of
`StacksFrontier.AlgebraicGeometry.Smooth.CotangentFinitePresentation` does not give.

The first is **global** finite presentation. For `a : T ⟶ X` a morphism from an affine scheme and
`f : X ⟶ S` locally of finite presentation, the lemma
`Stacks.Smooth.finitePresentation_pullbackCotangentSheaf` computes `Γ(a^*Ω_{X/S}, ⊤)` only when
`a` maps the whole of `T` into a single affine chart `W` of `X` lying over an affine open `V` of
`S`. A general `a` does not, and the Čech argument of Tag 02H6 runs on one global
`Γ(T, ⊤)`-module and its localizations, so it needs
`Module.FinitePresentation Γ(T, ⊤) Γ(a^*Ω_{X/S}, ⊤)` with no hypothesis on `a` at all. That is
`Stacks.Smooth.finitePresentation_pullbackCotangentSheaf_of_isAffine`.

The second is the **rigidity of the underlying map of a lift**: along a thickening — and a
first-order thickening is a thickening, so surjective on points — the underlying continuous map
of a solution of a lifting problem is determined by the problem. Consequently two solutions have
the same preimages, so if one of them maps an open into an affine chart then so does the other.
This is what lets the chart-based difference `Stacks.Smooth.liftDiffDerivation` be formed on the
overlap of two charts of a covering of the thickening, where the two local solutions a priori
live in different charts.

## Main definitions

* `AlgebraicGeometry.sectionsLinearEquivOfIso` (imported): an isomorphism of sheaves of modules
  induces a linear equivalence on sections over any open.
* `Stacks.Smooth.restrictPullbackCotangentSheafIso`: for `U` an open of `T`, the restriction of
  `a^*Ω_{X/S}` to `U` is `(U.ι ≫ a)^*Ω_{X/S}`.

## Main results

* `Stacks.Smooth.finitePresentation_pullbackCotangentSheaf_isAffineOpen`: the sections of
  `a^*Ω_{X/S}` over an affine open `U` of `T` with `U ≤ a ⁻¹ᵁ W`, for `W` an affine chart over an
  affine open of `S`, are a finitely presented `Γ(T, U)`-module. Here `T` need not be affine.
* `Stacks.Smooth.finitePresentation_pullbackCotangentSheaf_of_isAffine`: for `T` affine, `f`
  locally of finite presentation and `a : T ⟶ X` **arbitrary**, `Γ(a^*Ω_{X/S}, ⊤)` is a finitely
  presented `Γ(T, ⊤)`-module.
* `Stacks.Smooth.base_apply_eq_of_lift` and `Stacks.Smooth.preimage_eq_of_lift`: two solutions of
  one lifting problem along a morphism which is surjective on points have the same underlying map,
  hence the same preimages.
* `Stacks.Smooth.le_preimage_of_lift`: hence an open mapped into `W` by one solution is mapped
  into `W` by every other.

## Implementation notes

The passage from an affine open `U` of `T` to the affine scheme `U` is the only real content of
the first half. Restriction of a sheaf of modules along an open immersion `j` satisfies
`Γ(M.restrict j, V) = Γ(M, j ''ᵁ V)` on the nose — Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is `Iso.refl` — but the two sides carry
*different* module structures: the left-hand side over `Γ(Y, V)` and the right-hand side over
`Γ(Z, j ''ᵁ V)`, and they differ by the ring isomorphism
`(AlgebraicGeometry.Scheme.Hom.appIso j V).inv`, as recorded by
`AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom`. They are therefore *not*
interchangeable for typeclass resolution, and a `Module.FinitePresentation` proved for one does not
apply to the other; `finitePresentation_of_ringEquiv` transports it across the ring isomorphism.
With `j = U.ι` and `V = ⊤` the statement obtained is about the open `U.ι ''ᵁ ⊤`, which is `U` by
`AlgebraicGeometry.Scheme.Opens.ι_image_top`; the rewriting along that equality is the last step,
and it is legitimate because both the ring and the module in the conclusion depend on the open
only.

Globalization is `Module.FinitePresentation.of_localizationSpan'` for the set of those global
sections `c` of `T` whose basic open `T.basicOpen c` is mapped by `a` into some affine chart.
Those `c` generate the unit ideal because their basic opens cover `T`: around each point one
chooses an affine open of `S` containing the image, an affine open of `X` inside its preimage
containing the point's image, and then a basic open inside the preimage of the latter
(`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`). The localization hypotheses are exactly
the lemma `Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'`, which is available
with no hypothesis on `a` because `a^*Ω_{X/S}` is quasi-coherent, and the finite presentation
hypothesis at each member is the first half.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 01V3](https://stacks.math.columbia.edu/tag/01V3)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.Smooth

/-! ### Finite presentation of the sections of `a^*Ω_{X/S}` -/

variable {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) {V : S.Opens} {W : X.Opens}

/-- **The restriction of `a^*Ω_{X/S}` to an open is the pullback along the restricted
morphism.** For `U` an open of `T` the sheaf `(a^*Ω_{X/S})|_U` is `(U.ι ≫ a)^*Ω_{X/S}`, by the
compatibility of pullback with composition and the identification of restriction along an open
immersion with pullback. -/
noncomputable def restrictPullbackCotangentSheafIso (U : T.Opens) :
    (pullbackCotangentSheaf f a).restrict U.ι ≅ pullbackCotangentSheaf f (U.ι ≫ a) :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp U.ι a).app (cotangentSheaf f)

/-- **The sections of `a^*Ω_{X/S}` over an affine open inside a chart are finitely presented.**
Let `f : X ⟶ S` be a morphism of schemes, let `V` be an affine open of `S` and `W` an affine open
of `X` with `W ≤ f ⁻¹ᵁ V` such that `Γ(S, V) ⟶ Γ(X, W)` is of finite presentation, and let
`a : T ⟶ X` be a morphism of schemes. Then for every affine open `U` of `T` with
`U ≤ a ⁻¹ᵁ W` the sections `Γ(a^*Ω_{X/S}, U)` are a finitely presented `Γ(T, U)`-module.

No affineness is assumed on `T`: the statement is obtained from
`Stacks.Smooth.finitePresentation_pullbackCotangentSheaf` applied to the affine scheme `U` and the
morphism `U.ι ≫ a`, transported along `Stacks.Smooth.restrictPullbackCotangentSheafIso` and the
ring isomorphism comparing the `Γ(U, ⊤)`- and `Γ(T, U)`-module structures on the sections. -/
@[sga "3 III 0.6" "partial"]
theorem finitePresentation_pullbackCotangentSheaf_isAffineOpen {U : T.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W)
    (hfp : (f.appLE V W hWV).hom.FinitePresentation) :
    Module.FinitePresentation Γ(T, U) Γ(pullbackCotangentSheaf f a, U) := by
  have key : Module.FinitePresentation Γ(T, U.ι ''ᵁ ⊤)
      Γ(pullbackCotangentSheaf f a, U.ι ''ᵁ ⊤) := by
    have hUa : IsAffine (U : Scheme.{u}) := hU
    have hUW' : (⊤ : U.toScheme.Opens) ≤ (U.ι ≫ a) ⁻¹ᵁ W := by
      intro x _
      show a.base (U.ι.base x) ∈ W
      exact hUW x.2
    refine finitePresentation_of_ringEquiv Γ(U.toScheme, (⊤ : U.toScheme.Opens))
      Γ(T, U.ι ''ᵁ (⊤ : U.toScheme.Opens))
      ((U.ι.appIso (⊤ : U.toScheme.Opens)).symm).commRingCatIsoToRingEquiv _ _
      (Scheme.Modules.restrictAppIso U.ι (pullbackCotangentSheaf f a)
        ⊤).addCommGroupIsoToAddEquiv
      (fun r x ↦ Scheme.Modules.smul_restrictAppIso_hom_apply U.ι (pullbackCotangentSheaf f a)
        ⊤ r x)
      ((LinearEquiv.finitePresentation_iff (AlgebraicGeometry.sectionsLinearEquivOfIso
          (restrictPullbackCotangentSheafIso f a U).symm ⊤)).mp
        (finitePresentation_pullbackCotangentSheaf f (U.ι ≫ a) hV hW hWV hUW' hfp))
  exact U.ι_image_top ▸ key

/-- **The global sections of `a^*Ω_{X/S}` are finitely presented, for an arbitrary `a`.** Let
`f : X ⟶ S` be locally of finite presentation, let `T` be an affine scheme and let `a : T ⟶ X` be
any morphism. Then `Γ(a^*Ω_{X/S}, ⊤)` is a finitely presented `Γ(T, ⊤)`-module.

This is the statement that the Čech step (II) of [Stacks Project, Tag 02H6] consumes: it is what
makes `Module.FinitePresentation.isLocalizedModule_map` available, hence what makes the groups of
chart-local differences of two lifts the localizations of one global `Γ(T, ⊤)`-module.

Finite presentation of a module is local on the base
(`Module.FinitePresentation.of_localizationSpan'`), the localizations of `Γ(a^*Ω_{X/S}, ⊤)` at the
basic opens of `T` are its sections there
(`Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'`, which needs no hypothesis on
`a`), and on a basic open small enough to be carried by `a` into a single affine chart the sections
are finitely presented by
`Stacks.Smooth.finitePresentation_pullbackCotangentSheaf_isAffineOpen`. Such basic opens cover
`T`. -/
@[sga "3 III 0.6" "special case"]
theorem finitePresentation_pullbackCotangentSheaf_of_isAffine [IsAffine T]
    [LocallyOfFinitePresentation f] :
    Module.FinitePresentation Γ(T, ⊤) Γ(pullbackCotangentSheaf f a, (⊤ : T.Opens)) := by
  classical
  set P : Γ(T, (⊤ : T.Opens)) → Prop := fun c ↦ ∃ (V : S.Opens) (W : X.Opens),
    IsAffineOpen V ∧ IsAffineOpen W ∧ W ≤ f ⁻¹ᵁ V ∧ T.basicOpen c ≤ a ⁻¹ᵁ W
  have hcov : ⨆ c : {c // P c}, T.basicOpen (c : Γ(T, (⊤ : T.Opens))) = ⊤ := by
    refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨V, hV, hxV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (Opens.mem_top (f.base (a.base x)))
    obtain ⟨W, hW, hxW, hWV⟩ :=
      exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ V) (x := a.base x) hxV
    obtain ⟨c, hc₁, hc₂⟩ :=
      (isAffineOpen_top T).exists_basicOpen_le (V := a ⁻¹ᵁ W) ⟨x, hxW⟩ trivial
    exact Opens.mem_iSup.mpr ⟨⟨c, V, W, hV, hW, hWV, hc₁⟩, hc₂⟩
  have hspan : Ideal.span {c | P c} = ⊤ :=
    ((isAffineOpen_top T).iSup_basicOpen_eq_self_iff (s := {c | P c})).mp hcov
  have : ∀ g : {c | P c}, IsLocalization.Away (g : Γ(T, (⊤ : T.Opens)))
      Γ(T, T.basicOpen (g : Γ(T, (⊤ : T.Opens)))) :=
    fun g ↦ (isAffineOpen_top T).isLocalization_basicOpen _
  let : ∀ g : {c | P c}, Module Γ(T, (⊤ : T.Opens))
      Γ(pullbackCotangentSheaf f a, T.basicOpen (g : Γ(T, (⊤ : T.Opens)))) :=
    fun g ↦ moduleOfLE (pullbackCotangentSheaf f a) (T.basicOpen_le _)
  have : ∀ g : {c | P c}, IsScalarTower Γ(T, (⊤ : T.Opens))
      Γ(T, T.basicOpen (g : Γ(T, (⊤ : T.Opens))))
      Γ(pullbackCotangentSheaf f a, T.basicOpen (g : Γ(T, (⊤ : T.Opens)))) :=
    fun g ↦ isScalarTowerOfLE (pullbackCotangentSheaf f a) (T.basicOpen_le _)
  have : ∀ g : {c | P c}, IsLocalizedModule (Submonoid.powers (g : Γ(T, (⊤ : T.Opens))))
      (restrictₗ (pullbackCotangentSheaf f a) (T.basicOpen_le (g : Γ(T, (⊤ : T.Opens))))) :=
    fun g ↦ isLocalizedModule_restrictₗ_pullbackCotangentSheaf' f a _
  refine Module.FinitePresentation.of_localizationSpan' {c | P c} hspan
    (Rₚ := fun g ↦ Γ(T, T.basicOpen (g : Γ(T, (⊤ : T.Opens)))))
    (Mₚ := fun g ↦ Γ(pullbackCotangentSheaf f a, T.basicOpen (g : Γ(T, (⊤ : T.Opens)))))
    (fun g ↦ restrictₗ (pullbackCotangentSheaf f a) (T.basicOpen_le _)) fun g ↦ ?_
  obtain ⟨V', W', hV', hW', hWV', hUW'⟩ := g.2
  exact finitePresentation_pullbackCotangentSheaf_isAffineOpen f a
    ((isAffineOpen_top T).basicOpen _) hV' hW' hWV' hUW'
    (f.finitePresentation_appLE hV' hW' hWV')

/-! ### Rigidity of the underlying map of a lift -/

section Rigidity

variable {X T T' : Scheme.{u}} {i : T ⟶ T'} {a : T ⟶ X} {b₁ b₂ : T' ⟶ X}

/-- **The underlying map of a solution of a lifting problem is determined.** If `i` is surjective
on points and `b₁`, `b₂` both restrict along `i` to `a`, then `b₁` and `b₂` have the same
underlying map. In particular this applies to a thickening, which is surjective on points by
`Stacks.Thickenings.IsThickening`. -/
theorem base_apply_eq_of_lift (hi : Function.Surjective i.base) (h₁ : i ≫ b₁ = a)
    (h₂ : i ≫ b₂ = a) (t : T') : b₁.base t = b₂.base t := by
  obtain ⟨t₀, rfl⟩ := hi t
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h₁, h₂]

/-- **Two solutions of one lifting problem have the same preimages.** -/
theorem preimage_eq_of_lift (hi : Function.Surjective i.base) (h₁ : i ≫ b₁ = a)
    (h₂ : i ≫ b₂ = a) (W : X.Opens) : b₁ ⁻¹ᵁ W = b₂ ⁻¹ᵁ W :=
  Opens.ext (Set.ext fun t ↦ by
    show b₁.base t ∈ W ↔ b₂.base t ∈ W
    rw [base_apply_eq_of_lift hi h₁ h₂ t])

/-- **An open carried into a chart by one solution is carried into it by every other.** This is
what allows the chart-local difference `Stacks.Smooth.liftDiffDerivation` of two solutions of one
lifting problem to be formed on the overlap of two members of a covering of the thickening, where
the two solutions were produced in different charts. -/
theorem le_preimage_of_lift (hi : Function.Surjective i.base) (h₁ : i ≫ b₁ = a)
    (h₂ : i ≫ b₂ = a) {W : X.Opens} {V' : T'.Opens} (hb₁ : V' ≤ b₁ ⁻¹ᵁ W) : V' ≤ b₂ ⁻¹ᵁ W :=
  preimage_eq_of_lift hi h₁ h₂ W ▸ hb₁

end Rigidity

end Stacks.Smooth

end
