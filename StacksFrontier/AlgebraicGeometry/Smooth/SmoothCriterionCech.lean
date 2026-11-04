module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentRestrictNatural

/-!
# The chart-local difference of two lifts as a linear map out of the sections of `a^*Ω_{X/S}`

Let `f : X ⟶ S` be a morphism of schemes, let `i : T ⟶ T'` be a first-order thickening and let
`a : T ⟶ X`, `h : T' ⟶ S` present a lifting problem for `f`. Step (II) of the proof of the
infinitesimal lifting criterion [Stacks Project, Tag 02H6] compares the local solutions produced
by step (I) over the members of a covering of `T'`. On an overlap the two solutions differ by a
derivation, `Stacks.Smooth.liftDiffDerivation`, but that derivation depends on the affine chart
`(V, W)` of `f` in which it is formed, so the differences cannot be assembled into a Čech cochain
until they have been read inside one chart-independent group.

This file performs that reading over an affine open of the thickening. For `U'` an affine open of
`T'` the difference of two solutions of the restricted lifting problem is exhibited as the unique
`Γ(T, i ⁻¹ᵁ U')`-linear map

`Γ(a^*Ω_{X/S}, i ⁻¹ᵁ U') ⟶ 𝒞_{T_{U'}/T'_{U'}}`

inducing it, where `𝒞` denotes the conormal module of the restricted thickening. Both the source
and the target are now modules of sections attached to the *original* data `a` and `i`, over the
sections of `𝒪_T` on an open of `T`, so both localize: the source by
`Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'` and the target by
`Stacks.Smooth.isLocalizedModule_conormalRestrict`.

## Main results

* `Stacks.Smooth.existsUnique_linearMap_liftDiffDerivation`: the chart-local difference of two
  solutions of the restricted lifting problem over an affine open `U'` of `T'` is induced by
  exactly one `Γ(T, i ⁻¹ᵁ U')`-linear map out of `Γ(a^*Ω_{X/S}, i ⁻¹ᵁ U')`.

## Implementation notes

Everything is an application of `Stacks.Smooth.existsUnique_linearMap_of_leibniz_opensTop`. The
three hypotheses it asks for are exactly the three axioms of
`Stacks.Smooth.liftDiffDerivation`: additivity is `map_add`, the vanishing on the sections coming
from `Γ(S, V)` is `Derivation.map_algebraMap` for the algebra structure
`Stacks.Smooth.algebraAppLE`, and the Leibniz rule is `Derivation.leibniz` — the module structure
`Stacks.Smooth.moduleOfAppLE` being restriction of scalars along
`AlgebraicGeometry.Scheme.Hom.appLE`, the displayed equation and the derivation's own Leibniz
rule are the same statement by `rfl`.

The one thing that is *not* automatic is the ring over which the conormal module is a module.
`Stacks.Smooth.thickeningKerModule` produces a module over the global sections
`Γ(i ⁻¹ᵁ U', ⊤)` of the affine scheme cut out by the restricted thickening, whereas the source
`Γ(a^*Ω_{X/S}, i ⁻¹ᵁ U')` is a module over `Γ(T, i ⁻¹ᵁ U')`. Those two rings are isomorphic by
`AlgebraicGeometry.Scheme.Opens.topIso` but not identical, and
`Stacks.Smooth.moduleOfTopIso` is the restriction of scalars that bridges them; it is built into
the statement of `Stacks.Smooth.existsUnique_linearMap_of_leibniz_opensTop`.

What remains for the unrestricted [Stacks Project, Tag 02H6] is the Čech argument itself. Its
inputs are now all available: the linear map produced here is an element of the `Γ(T, ⊤)`-module
of `Γ(T, ⊤)`-linear maps `Γ(a^*Ω_{X/S}, ⊤) ⟶ 𝒞_{T/T'}` localized away from the section cutting
out `U'`, by `Module.FinitePresentation.isLocalizedModule_mapExtendScalars` together with
`Stacks.Smooth.finitePresentation_pullbackCotangentSheaf_of_isAffine`,
`Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'` and
`Stacks.Smooth.isLocalizedModule_conormalRestrict`; the cocycle identity is
`Stacks.Smooth.liftDiffDerivation_add`, formed in a single chart on each triple overlap by
`Stacks.Smooth.le_preimage_of_lift`; `Stacks.RingTheory.CechAcyclicity.cech_exact` at `p = 0`
produces the 0-cochain; `Stacks.Smooth.exists_lift_of_derivation` corrects the local solutions;
`Stacks.Smooth.eq_of_liftDiffDerivation_eq_zero` shows the corrected solutions agree; and
`Stacks.Smooth.exists_lift_of_isOpenCover` glues them.

## References

* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Smooth

/-- **The chart-local difference of two lifts, as a linear map out of the sections of
`a^*Ω_{X/S}`.** Let `f : X ⟶ S` be a morphism of schemes, let `V` be an affine open of `S` and
`W` an affine open of `X` with `W ≤ f ⁻¹ᵁ V`, let `i : T ⟶ T'` be a first-order thickening and
let `a : T ⟶ X`, `h : T' ⟶ S` present a lifting problem for `f`. Let `U'` be an affine open of
`T'` whose preimage in `T` is affine, and let `b₁`, `b₂` be two solutions of the lifting problem
restricted to `U'`, both mapping into `W`. Then there is exactly one `Γ(T, i ⁻¹ᵁ U')`-linear map

`Γ(a^*Ω_{X/S}, i ⁻¹ᵁ U') ⟶ RingHom.ker (i ∣_ U').appTop`

sending the pullback of the universal differential of a section of `𝒪_X` over `W` to the
difference of the two solutions at that section.

The left-hand side mentions no chart, so this is the chart-independent reading of
`Stacks.Smooth.liftDiffDerivation` that step (II) of [Stacks Project, Tag 02H6] needs in order to
assemble the differences of the local solutions into a Čech cochain. -/
theorem existsUnique_linearMap_liftDiffDerivation {X S T T' : Scheme.{u}} (f : X ⟶ S)
    {V : S.Opens} {W : X.Opens} {U' : T'.Opens} {i : T ⟶ T'} {a : T ⟶ X} {h : T' ⟶ S}
    (hi : Thickenings.IsFirstOrderThickening i) [IsAffine (U' : Scheme.{u})]
    (hU : IsAffineOpen (i ⁻¹ᵁ U')) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) (hUW : i ⁻¹ᵁ U' ≤ a ⁻¹ᵁ W)
    (hUWt : (⊤ : ((i ⁻¹ᵁ U' : T.Opens) : Scheme.{u}).Opens) ≤ ((i ⁻¹ᵁ U').ι ≫ a) ⁻¹ᵁ W)
    (hV' : (⊤ : (U' : Scheme.{u}).Opens) ≤ (U'.ι ≫ h) ⁻¹ᵁ V)
    (hcomm : ((i ⁻¹ᵁ U').ι ≫ a) ≫ f = (i ∣_ U') ≫ (U'.ι ≫ h))
    {b₁ b₂ : (U' : Scheme.{u}) ⟶ X} (hb₁f : b₁ ≫ f = U'.ι ≫ h) (hb₂f : b₂ ≫ f = U'.ι ≫ h)
    (hb₁a : (i ∣_ U') ≫ b₁ = (i ⁻¹ᵁ U').ι ≫ a) (hb₂a : (i ∣_ U') ≫ b₂ = (i ⁻¹ᵁ U').ι ≫ a)
    (hb₁ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W)
    (hb₂ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W) :
    letI := algebraAppLE f hWV
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
    letI := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUWt (RingHom.ker (i ∣_ U').appTop.hom)
    letI := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt (RingHom.ker (i ∣_ U').appTop.hom)
    letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt
      (RingHom.ker (i ∣_ U').appTop.hom)
    letI := moduleOfTopIso (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
    ∃! θ : Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ U') →ₗ[Γ(T, i ⁻¹ᵁ U')]
        RingHom.ker (i ∣_ U').appTop.hom,
      ∀ b : Γ(X, W), θ (pullbackD f a W hUW b) =
        liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi U') hWV hUWt hV'
          hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ b := by
  let := algebraAppLE f hWV
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
  let := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUWt (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt (RingHom.ker (i ∣_ U').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt
    (RingHom.ker (i ∣_ U').appTop.hom)
  set δ := liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi U') hWV hUWt hV'
    hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂
  exact existsUnique_linearMap_of_leibniz_opensTop f a hU hV hW hWV hUW hUWt
    (RingHom.ker (i ∣_ U').appTop.hom) (fun b ↦ δ b) (fun x y ↦ map_add δ x y)
    (fun r ↦ by
      rw [← RingHom.algebraMap_toAlgebra (f.appLE V W hWV).hom]
      exact δ.map_algebraMap r)
    (fun x y ↦ δ.leibniz x y)

end Stacks.Smooth

end
