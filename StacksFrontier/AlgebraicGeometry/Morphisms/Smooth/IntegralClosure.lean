module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.IntegralClosureAlgebra
public import StacksFrontier.RingTheory.IntegralClosure.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# Integral closure and pullback along a smooth morphism

Let `g : Y ⟶ S` be a smooth morphism of schemes, let `𝒜` be a quasi-coherent sheaf of
`𝒪_S`-algebras and let `𝒜' ⊆ 𝒜` be the integral closure of `𝒪_S` in `𝒜`. Forming the integral
closure commutes with pullback: the integral closure of `𝒪_Y` in `g^*𝒜` is `g^*𝒜'`.

A quasi-coherent `𝒪_S`-algebra is `f_*𝒪_X` for an affine morphism `f : X ⟶ S`, and more generally
`f_*𝒪_X` is quasi-coherent for `f` quasi-compact and quasi-separated. In that presentation the
pullback `g^*(f_*𝒪_X)` is the pushforward of the structure sheaf of `X ×_S Y`, and the assertion
is tested on an affine open `V ⊆ Y` lying over an affine open `U ⊆ S`, where it becomes the
statement that
```
Γ(Y, V) ⊗_{Γ(S, U)} integralClosure Γ(S, U) Γ(X, f⁻¹U) → integralClosure Γ(Y, V) Γ(X ×_S Y, q⁻¹V)
```
is bijective, `q : X ×_S Y ⟶ Y` being the projection. This is proved here.

Two inputs carry it. The first is the identification of the sections of the pullback,
`sectionsBaseChangeEquiv`, which needs only flatness of `g`: for `f` quasi-compact and
quasi-separated the comparison map `Γ(Y, V) ⊗_{Γ(S, U)} Γ(X, f⁻¹U) → Γ(X ×_S Y, q⁻¹V)` is an
isomorphism. The second is the affine statement that integral closure commutes with smooth base
change, Stacks 03GG, applied to the smooth ring map `Γ(S, U) → Γ(Y, V)` cut out by `g` on the two
affine opens.

## Main results

* `Stacks.IntegralClosure.SmoothPullback.sectionsBaseChangeEquiv`: for `f` quasi-compact and
  quasi-separated and `g` flat, the sections of the structure sheaf of `X ×_S Y` over `q⁻¹V` are
  `Γ(Y, V) ⊗_{Γ(S, U)} Γ(X, f⁻¹U)`.
* `Stacks.IntegralClosure.SmoothPullback.bijective_toIntegralClosure_sections`: for `g` smooth the
  canonical map from `Γ(Y, V) ⊗_{Γ(S, U)} integralClosure Γ(S, U) Γ(X, f⁻¹U)` to the integral
  closure of `Γ(Y, V)` in `Γ(X ×_S Y, q⁻¹V)` is bijective.
* `Stacks.IntegralClosure.SmoothPullback.range_integralClosureAlgebraι_app_pullback`: the same
  assertion read off the integral-closure subalgebra itself, as an equality of its sections over
  `V` with the image of the base change of its sections over `U`.

## Implementation notes

The quasi-coherent algebra is presented as `f_*𝒪_X`, so that the sections of its pullback are the
sections of the structure sheaf of a fibre product and the comparison map is the one supplied by
`AlgebraicGeometry.pushoutSection`; the integral closure of `𝒪_S` in `𝒜` then has sections
`integralClosure Γ(S, U) Γ(X, f⁻¹U)` over an affine open, and the equality of subsheaves asserted
by the source is the bijectivity, over every such pair of affine opens, of the canonical map out
of the base change of those sections. The equivalence is pinned by its values on the two tensor
factors, `sectionsBaseChangeEquiv_tmul_one` and `sectionsBaseChangeEquiv_one_tmul`, which
determine it.

The subsheaf `𝒜'` is `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.integralClosureAlgebra`, the
sheaf of sections whose germs are everywhere integral over the local rings; over an affine open its
sections are the integral closure of the rings, which is what turns the comparison above into a
statement about that subsheaf. For `f` affine this is recorded in
`range_integralClosureAlgebraι_app_pullback`, where the pullback `g^*𝒜` is presented as
`f_*𝒪_{X ×_S Y}` rather than through the extension-of-scalars functor on algebra sheaves.

The algebra structures are the ones cut out by the morphisms on sections, introduced as local
instances in the statements: `Γ(S, U) → Γ(X, f⁻¹U)` by `f`, `Γ(S, U) → Γ(Y, V)` by `g` and
`Γ(Y, V) → Γ(X ×_S Y, q⁻¹V)` by the projection `q`.

## References

* [Stacks Project, Tag 081K](https://stacks.math.columbia.edu/tag/081K)
* [Stacks Project, Tag 03GG](https://stacks.math.columbia.edu/tag/03GG)
* [Stacks Project, Tag 035F](https://stacks.math.columbia.edu/tag/035F)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
open Stacks.AffineAlgebraEquivalence AlgebraicGeometry.Scheme.QuasicoherentAlgebra

universe u

namespace Stacks.IntegralClosure.SmoothPullback

variable {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The sections of the structure sheaf of `X ×_S Y` over the preimage of an affine open
`V ⊆ Y` lying over an affine open `U ⊆ S` are `Γ(Y, V) ⊗_{Γ(S, U)} Γ(X, f⁻¹U)`, provided `f` is
quasi-compact and quasi-separated and `g` is flat. -/
public noncomputable def sectionsBaseChangeEquiv [QuasiCompact f] [QuasiSeparated f] [Flat g]
    {U : S.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U) :
    letI := (f.app U).hom.toAlgebra
    letI := (g.appLE U V hVU).hom.toAlgebra
    letI := ((pullback.snd f g).app V).hom.toAlgebra
    Γ(Y, V) ⊗[Γ(S, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, V)]
      Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) := by
  letI := (f.app U).hom.toAlgebra
  letI := (g.appLE U V hVU).hom.toAlgebra
  letI := ((pullback.snd f g).app V).hom.toAlgebra
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    (by simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV
    (f.isCompact_preimage hU.isCompact) (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let e₀ := (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ hiso :)
  exact
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          (pullback.snd f g).app V r
        congr 2
        simp only [AlgHom.toRingHom_eq_coe, pushoutSection, Iso.trans_hom, pushout.congrHom_hom,
          asIso_hom, IsPushout.inr_isoPushout_hom_assoc, pushout.inr_desc_assoc, Category.id_comp,
          Scheme.Hom.app_eq_appLE, e₀]
        exact pushout.inr_desc _ _ _ }

/-- On the left tensor factor the identification of `sectionsBaseChangeEquiv` is the map on
sections induced by the projection `X ×_S Y ⟶ Y`. -/
public theorem sectionsBaseChangeEquiv_tmul_one [QuasiCompact f] [QuasiSeparated f] [Flat g]
    {U : S.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U) :
    letI := (f.app U).hom.toAlgebra
    letI := (g.appLE U V hVU).hom.toAlgebra
    letI := ((pullback.snd f g).app V).hom.toAlgebra
    ∀ s : Γ(Y, V), sectionsBaseChangeEquiv f g hU hV hVU (s ⊗ₜ 1) =
      ((pullback.snd f g).app V).hom s := by
  let := (f.app U).hom.toAlgebra
  let := (g.appLE U V hVU).hom.toAlgebra
  let := ((pullback.snd f g).app V).hom.toAlgebra
  intro s
  simpa [RingHom.algebraMap_toAlgebra] using (sectionsBaseChangeEquiv f g hU hV hVU).commutes s

/-- On the right tensor factor the identification of `sectionsBaseChangeEquiv` is the map on
sections induced by the projection `X ×_S Y ⟶ X`. -/
public theorem sectionsBaseChangeEquiv_one_tmul [QuasiCompact f] [QuasiSeparated f] [Flat g]
    {U : S.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U)
    (hle : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U) :
    letI := (f.app U).hom.toAlgebra
    letI := (g.appLE U V hVU).hom.toAlgebra
    letI := ((pullback.snd f g).app V).hom.toAlgebra
    ∀ b : Γ(X, f ⁻¹ᵁ U), sectionsBaseChangeEquiv f g hU hV hVU (1 ⊗ₜ b) =
      ((pullback.fst f g).appLE (f ⁻¹ᵁ U) (pullback.snd f g ⁻¹ᵁ V) hle).hom b := by
  let := (f.app U).hom.toAlgebra
  let := (g.appLE U V hVU).hom.toAlgebra
  let := ((pullback.snd f g).app V).hom.toAlgebra
  intro b
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    (by simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV
    (f.isCompact_preimage hU.isCompact) (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  change ((CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ hiso :)).hom.hom (1 ⊗ₜ b) = _
  rw [show (1 : Γ(Y, V)) ⊗ₜ[Γ(S, U)] b =
    (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := Γ(S, U)) (A := Γ(Y, V))).toRingHom).hom b from
      (Algebra.TensorProduct.includeRight_apply b).symm]
  rw [← CommRingCat.comp_apply]
  congr 2
  simp only [AlgHom.toRingHom_eq_coe, pushoutSection, Iso.trans_hom, pushout.congrHom_hom,
    asIso_hom, IsPushout.inl_isoPushout_hom_assoc, pushout.inl_desc_assoc, Category.id_comp]
  exact pushout.inl_desc _ _ _

/-- **Stacks Project, Tag 081K**, over a pair of affine opens. Let `g : Y ⟶ S` be a smooth
morphism, let `𝒜 = f_*𝒪_X` be a quasi-coherent sheaf of `𝒪_S`-algebras and let `𝒜'` be the
integral closure of `𝒪_S` in `𝒜`. Over an affine open `V ⊆ Y` lying over an affine open
`U ⊆ S`, the canonical map from `𝒜'(U) ⊗_{Γ(S, U)} Γ(Y, V)` to the integral closure of `Γ(Y, V)`
in `(g^*𝒜)(V) = Γ(X ×_S Y, q⁻¹V)` is bijective. -/
@[stacks 081K "affine-open comparison map. The equality of subsheaves is asserted over a pair of
affine opens `V ⊆ Y`, `U ⊆ S` with `V ⊆ g⁻¹U`, as bijectivity of the canonical map out of the base
change of the sections of the integral closure, the quasi-coherent algebra being presented as
`f_*𝒪_X` for `f` quasi-compact and quasi-separated. The identification of the sections of the
pullback is `sectionsBaseChangeEquiv`, pinned by `sectionsBaseChangeEquiv_tmul_one` and
`sectionsBaseChangeEquiv_one_tmul`. The same assertion in terms of the integral-closure
subalgebra itself is `range_integralClosureAlgebraι_app_pullback`. The sheaf-level equality is
not asserted here. See the module docstring.",
  ega "IV 18.12.15",
  ega "IV 6.14.5" "smooth, affine opens"]
public theorem bijective_toIntegralClosure_sections [QuasiCompact f] [QuasiSeparated f] [Smooth g]
    {U : S.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U) :
    letI := (f.app U).hom.toAlgebra
    letI := (g.appLE U V hVU).hom.toAlgebra
    letI := ((pullback.snd f g).app V).hom.toAlgebra
    Function.Bijective
      ((sectionsBaseChangeEquiv f g hU hV hVU).mapIntegralClosure.toAlgHom.comp
        (TensorProduct.toIntegralClosure Γ(S, U) Γ(Y, V) Γ(X, f ⁻¹ᵁ U))) := by
  let := (f.app U).hom.toAlgebra
  let := (g.appLE U V hVU).hom.toAlgebra
  let := ((pullback.snd f g).app V).hom.toAlgebra
  have : Algebra.Smooth Γ(S, U) Γ(Y, V) := (g.smooth_appLE hU hV hVU).toAlgebra
  exact (sectionsBaseChangeEquiv f g hU hV hVU).mapIntegralClosure.bijective.comp
    TensorProduct.toIntegralClosure_bijective_of_smooth

/-- **Stacks Project, Tag 081K**, over a pair of affine opens and in terms of the integral-closure
subalgebra itself. For `g` smooth and `𝒜 = f_*𝒪_X` with `f` affine, the sections over `V` of the
integral closure of `𝒪_Y` in `g^*𝒜` are the image of `Γ(Y, V) ⊗_{Γ(S, U)} 𝒜'(U)`. -/
@[stacks 081K "affine sections of the integral-closure subalgebra. Both sides are read over a
pair of affine opens `V ⊆ Y`, `U ⊆ S` with `V ⊆ g⁻¹U`: the left is the sections of the
integral-closure subalgebra of Stacks 035F in the pullback, the right the image of the base
change of `𝒜'(U)`, which is the sections of that subalgebra over `U` by
`AlgebraicGeometry.Scheme.QuasicoherentAlgebra.range_integralClosureAlgebraι_app_of_isAffineOpen`.
The pullback is presented as `f_*𝒪_{X ×_S Y}`, not as `algebraPullback g`; the two agree by
`Stacks.AffineAlgebraEquivalence.isIso_baseChangeAlgebraHom`, whose sections over an open are not
computed in this repository, so the sheaf-level equality is not asserted here. See the module
docstring.", ega "IV 18.12.15", ega "IV 6.14.5" "smooth, affine opens"]
public theorem range_integralClosureAlgebraι_app_pullback [IsAffineHom f] [Smooth g]
    {U : S.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ g ⁻¹ᵁ U) :
    haveI := IsSeparated.of_isAffineHom f
    haveI : IsAffineHom (pullback.snd f g) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f g) ‹IsAffineHom f›
    letI := (f.app U).hom.toAlgebra
    letI := (g.appLE U V hVU).hom.toAlgebra
    letI := ((pullback.snd f g).app V).hom.toAlgebra
    Set.range ((integralClosureAlgebraι
        (pushforwardAlgebra (pullback.snd f g))).right.hom.app (op V)) =
      Set.range ((sectionsBaseChangeEquiv f g hU hV hVU).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id Γ(Y, V) Γ(Y, V))
          (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)).val)) := by
  have := IsSeparated.of_isAffineHom f
  have : IsAffineHom (pullback.snd f g) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f g) ‹IsAffineHom f›
  let := (f.app U).hom.toAlgebra
  let := (g.appLE U V hVU).hom.toAlgebra
  let := ((pullback.snd f g).app V).hom.toAlgebra
  have : (underlyingModule (pushforwardAlgebra (pullback.snd f g))).IsQuasicoherent :=
    isQuasicoherent_pushforwardAlgebra _
  rw [range_integralClosureAlgebraι_app_of_isAffineOpen _ V hV]
  ext z
  refine ⟨fun hz ↦ ((bijective_toIntegralClosure_sections f g hU hV hVU).surjective
    ⟨z, hz⟩).imp fun x hx ↦ congrArg Subtype.val hx, ?_⟩
  rintro ⟨x, rfl⟩
  exact ((sectionsBaseChangeEquiv f g hU hV hVU).mapIntegralClosure
    (TensorProduct.toIntegralClosure Γ(S, U) Γ(Y, V) Γ(X, f ⁻¹ᵁ U) x)).2

end Stacks.IntegralClosure.SmoothPullback

end
