module

public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothCriterionCech
public import StacksFrontier.RingTheory.CechAcyclicity

/-!
# Assembling the chart-local differences of lifts into a Čech cochain

Let `f : X ⟶ S` be a morphism of schemes locally of finite presentation, let `i : T ⟶ T'` be a
first-order thickening with `T'` affine and let `a : T ⟶ X`, `h : T' ⟶ S` present a lifting
problem for `f`. Step (II) of the proof of the infinitesimal lifting criterion
[Stacks Project, Tag 02H6] compares the local solutions of step (I) over the members of a
standard covering `T' = ⋃ D(g j)` of the thickening. On an overlap `D(c)` the difference of two
solutions is, by `Stacks.Smooth.existsUnique_linearMap_liftDiffDerivation`, a
`Γ(T, i ⁻¹ᵁ D(c))`-linear map

`Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(c)) ⟶ 𝒞_{T_c/T'_c}`,

and this file exhibits the family of those modules, as `c` varies, as the family of
localizations of the single `Γ(T, ⊤)`-module

`N = Γ(a^*Ω_{X/S}, ⊤) →ₗ[Γ(T, ⊤)] 𝒞_{T/T'}`

that the Čech complex `Stacks.RingTheory.CechAcyclicity.CechTerm` of `N` is built from, together
with the identification of the Čech restriction maps
`Stacks.RingTheory.CechAcyclicity.resAway` with restriction of sections.

## Main definitions

* `Stacks.Smooth.conormalResOpens` is the restriction map `𝒞_{T/T'} ⟶ 𝒞_{T_{U'}/T'_{U'}}` of
  conormal modules attached to an affine open `U'` of `T'`, generalizing
  `Stacks.Smooth.conormalRestrict` from a basic open to an arbitrary affine open.
* `Stacks.Smooth.conormalResLE` is the restriction map of conormal modules attached to an
  inclusion `U'' ≤ U'` of affine opens of `T'`.
* `Stacks.Smooth.homCompare` is the canonical comparison map between two localizations, at the
  powers of `b` and of a multiple `b'` of `b`, of a module `P →ₗ[A] C` of linear maps.

## Main results

* `Stacks.Smooth.isScalarTower_moduleOfTopIso`: the two restrictions of scalars
  `Stacks.Smooth.moduleOfOpensAppTop` and `Stacks.Smooth.moduleOfTopIso` of a module over
  `Γ(U, ⊤)` form a scalar tower over the restriction map `Γ(Y, ⊤) ⟶ Γ(Y, U)`.
* `Stacks.Smooth.hom_ext_pullbackD`: a `Γ(T, U)`-linear map out of `Γ(a^*Ω_{X/S}, U)` is
  determined by the derivation it induces in a single affine chart.
* `Stacks.Smooth.pullbackD_shrink`: the pullback of a universal differential is unchanged when
  the chart is shrunk, so a solution of the corepresentability problem for a chart is one for
  every smaller chart.
* `Stacks.Smooth.conormalResLE_comp_conormalResOpens`: the conormal restriction maps compose.
* `Stacks.Smooth.homCompare_apply`: the abstract comparison of two localizations of a module of
  linear maps is computed by any pair of restriction maps compatible with the four localization
  maps. This is the only property of the comparison that the Čech step uses.
* `Stacks.Smooth.homCompare_iso`: transported along the canonical isomorphisms with
  `Stacks.RingTheory.CechAcyclicity.AwayLoc`, that comparison map *is*
  `Stacks.RingTheory.CechAcyclicity.resAway`.
* `Stacks.Smooth.isLocalizedModule_homLoc_basicOpen`: **the coefficient input of the Čech step.**
  The module of `Γ(T, i ⁻¹ᵁ D(c))`-linear maps `Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(c)) ⟶ 𝒞_{T_c/T'_c}` is the
  localization of `N` away from the image of `c`.
* `Stacks.Smooth.homCompare_restrictₗ`: the comparison map between two of those localizations is
  restriction of sections on both sides.

## Implementation notes

The three localization inputs are available:
`Stacks.Smooth.finitePresentation_pullbackCotangentSheaf_of_isAffine` makes
`Module.FinitePresentation.isLocalizedModule_mapExtendScalars` apply,
`Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'` localizes
`Γ(a^*Ω_{X/S}, ⊤)` and `Stacks.Smooth.isLocalizedModule_conormalRestrict` localizes the conormal
module. Two bookkeeping steps are needed to put them in one shape. First, the two sides speak of
different opens of `T`: the sheaf side of `T.basicOpen (i.appTop c)` and the conormal side of
`i ⁻¹ᵁ T'.basicOpen c`. These are the same open by
`Stacks.Smooth.preimage_basicOpen_appTop`, and everything is stated for the latter — the shape in
which the difference of two lifts actually arises — with the two localization hypotheses
transported by a `rintro O rfl` on that equality of opens
(`Stacks.Smooth.isLocalization_preimage_basicOpen` and
`Stacks.Smooth.isLocalizedModule_restrictₗ_preimage_basicOpen`). Second, the conormal module
carries its `Γ(T, ⊤)`-action through `Stacks.Smooth.moduleOfOpensAppTop` and its
`Γ(T, i ⁻¹ᵁ D(c))`-action through `Stacks.Smooth.moduleOfTopIso`; that these form a scalar tower
is `Stacks.Smooth.isScalarTower_moduleOfTopIso`, which rests on the comparison
`Stacks.Smooth.map_comp_topIso_inv` of `AlgebraicGeometry.Scheme.Opens.topIso` with
`AlgebraicGeometry.Scheme.Opens.ι` on global sections.

The comparison of two of these localizations is treated abstractly, because the geometric
description of the map is not needed: `Stacks.Smooth.homCompare` is defined as
`IsLocalizedModule.lift`, and `Stacks.Smooth.homCompare_apply` shows that it is computed by *any*
pair of restriction maps compatible with the localization maps. The pair that occurs is
restriction of sections of `a^*Ω_{X/S}` (`Stacks.Smooth.restrictₗ_restrictₗ`) and
`Stacks.Smooth.conormalResLE` (`Stacks.Smooth.conormalResLE_comp_conormalResOpens`); the proof
of `Stacks.Smooth.homCompare_apply` clears the denominator of `θ` and compares the two
`Γ(T, ⊤)`-linear maps out of the localization `Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(c))` by
`IsLocalizedModule.ext`. Because `Stacks.Smooth.conormalResLE` is restriction of sections of
`𝒪_{T'}` along `AlgebraicGeometry.Scheme.homOfLE`, its compatibility with
`Stacks.Smooth.conormalResOpens` is `AlgebraicGeometry.Scheme.homOfLE_ι` on global sections — no
comparison of a basic open of a basic open with a basic open of `T'` is needed anywhere.

### How the unrestricted Tag 02H6 was completed

**Tag 02H6 is now proved and tagged**, as
`Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth` in
`StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag`. The account below was
written while it was still open; it is kept because it names, in order, the inputs the
assembly consumes, which is the clearest description of how this file is used.

The Čech cocycle itself is **not** constructed here, and the implication
`Smooth f → Stacks.Smooth.FormallySmoothScheme f` is still open. With the present file the
remaining obstruction is a single statement, which is *not* an instance of the localization
bookkeeping above:

> **Chart independence.** For `U` an affine open of `T` and two solutions of one lifting problem
> over `U` mapping into two affine charts `W` and `W₂` of `X` at once, the linear map
> `Γ(a^*Ω_{X/S}, U) ⟶ 𝒞` produced by
> `Stacks.Smooth.existsUnique_linearMap_liftDiffDerivation` from the chart `W` is the one
> produced from the chart `W₂`.

It is needed because the Čech differential of the family of pairwise differences compares, at a
triple overlap `D(g j) ⊓ D(g k) ⊓ D(g l)`, three differences formed in the charts attached to
`j`, `j` and `k`: the two formed in the chart of `j` combine by the cocycle identity
`Stacks.Smooth.liftDiffDerivation_add`, and what is left over is exactly the comparison of the
chart of `j` with the chart of `k` for one and the same pair of solutions. No choice of covering
avoids this, since the Čech condition quantifies over unordered triples.

Two of the three ingredients of a proof are in this file. The comparison of the chart `W` with a
smaller affine chart `W₃ ≤ W` is immediate from `Stacks.Smooth.pullbackD_shrink` and
`Stacks.Smooth.hom_ext_pullbackD`: the solution for `W₃` satisfies the defining equation for `W`
as well, hence equals the solution for `W` by uniqueness, so two charts admitting a common
affine refinement containing the image give the same map. Shrinking `U` so that such a
refinement exists is possible, and `Stacks.Smooth.homCompare_restrictₗ` identifies the
restriction of the map for `W` over `U` with the map for `W` over the smaller open. The missing
ingredient is the separatedness statement that closes the local-to-global step: that the
restriction maps `Stacks.Smooth.conormalResLE` of the conormal module to the members of a
basic-open covering of `U` are jointly injective.

## References

* [Stacks Project, Tag 01EO](https://stacks.math.columbia.edu/tag/01EO)
* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/
@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.Smooth

/-! ### Restriction of scalars along the inclusion of an open subscheme -/

/-- **The sections of `𝒪_Y` on an open, read on the open subscheme.** Restricting a global
section of `𝒪_Y` to an open `U` and then transporting it along
`AlgebraicGeometry.Scheme.Opens.topIso` is the same as taking its image under the inclusion
`U.ι` on global sections. -/
theorem map_comp_topIso_inv {Y : Scheme.{u}} (U : Y.Opens) :
    Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ U.topIso.inv = U.ι.appTop := by
  rw [← opens_ι_appLE_top (W := U), Scheme.Hom.map_appLE]
  exact appLE_top_top U.ι

/-- The `Γ(Y, ⊤)`-action of `Stacks.Smooth.moduleOfOpensAppTop` on a `Γ(U, ⊤)`-module is the
restriction of its `Γ(Y, U)`-action of `Stacks.Smooth.moduleOfTopIso`: the two restrictions of
scalars form a scalar tower over the restriction map `Γ(Y, ⊤) ⟶ Γ(Y, U)`. -/
theorem isScalarTower_moduleOfTopIso {Y : Scheme.{u}} (U : Y.Opens) (M : Type*) [AddCommGroup M]
    [Module Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)) M] :
    letI := algebraOfLE Y (le_top : U ≤ ⊤)
    letI := moduleOfOpensAppTop U M
    letI := moduleOfTopIso U M
    IsScalarTower Γ(Y, (⊤ : Y.Opens)) Γ(Y, U) M := by
  let := algebraOfLE Y (le_top : U ≤ ⊤)
  let := moduleOfOpensAppTop U M
  let := moduleOfTopIso U M
  refine IsScalarTower.of_algebraMap_smul fun r m ↦ ?_
  change U.topIso.inv.hom ((Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom r) • m
    = U.ι.appTop.hom r • m
  rw [← CommRingCat.comp_apply, map_comp_topIso_inv U]

/-! ### Restriction of sections through nested opens -/

/-- **Restriction of sections composes.** This is the compatibility of the restriction maps on
sections of a sheaf of modules with the three nested opens `U' ≤ U ≤ V`, stated for
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ`. It is the hypothesis `hσ` of
`Stacks.Smooth.homCompare_apply` on the side of `a^*Ω_{X/S}`. -/
theorem restrictₗ_restrictₗ {Y : Scheme.{u}} (M : Y.Modules) {U' U V : Y.Opens} (h : U ≤ V)
    (h' : U' ≤ U) (y : Γ(M, V)) :
    letI := moduleOfLE M h
    letI := moduleOfLE M h'
    letI := moduleOfLE M (h'.trans h)
    restrictₗ M h' (restrictₗ M h y) = restrictₗ M (h'.trans h) y := by
  let := moduleOfLE M h
  let := moduleOfLE M h'
  let := moduleOfLE M (h'.trans h)
  change (M.presheaf.map (homOfLE h').op) ((M.presheaf.map (homOfLE h).op) y)
    = (M.presheaf.map (homOfLE (h'.trans h)).op) y
  rw [← Functor.map_comp_apply]
  rfl

/-- The scalar tower `Γ(Y, V) → Γ(Y, U) → Γ(M, U')` for nested opens `U' ≤ U ≤ V`: the two
restrictions of scalars of the sections of a sheaf of modules are compatible. -/
theorem isScalarTowerOfLE_of_le {Y : Scheme.{u}} (M : Y.Modules) {U' U V : Y.Opens} (h : U ≤ V)
    (h' : U' ≤ U) :
    letI := algebraOfLE Y h
    letI := moduleOfLE M h'
    letI := moduleOfLE M (h'.trans h)
    IsScalarTower Γ(Y, V) Γ(Y, U) Γ(M, U') := by
  let := algebraOfLE Y h
  let := moduleOfLE M h'
  let := moduleOfLE M (h'.trans h)
  refine IsScalarTower.of_algebraMap_smul fun r m ↦ ?_
  change ((Y.presheaf.map (homOfLE h').op).hom ((Y.presheaf.map (homOfLE h).op).hom r)) • m
    = ((Y.presheaf.map (homOfLE (h'.trans h)).op).hom r) • m
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-! ### Shrinking the chart -/

/-- **The pullback of a universal differential does not change when the chart is shrunk.** Let
`W₃ ≤ W` be opens of `X` and let `U` be an open of `T` carried by `a` into `W₃`. Then the
pullback along `a` of the universal differential of a section `b` of `𝒪_X` over `W`, read over
`U`, is the pullback of the universal differential of the restriction of `b` to `W₃`.

This is `Stacks.Smooth.pullbackD_map` with the two restrictions of sections composed, and it is
what lets a solution of the corepresentability problem for a chart be read as a solution for any
smaller chart. -/
theorem pullbackD_shrink {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) {W W₃ : X.Opens}
    {U : T.Opens} (hW₃W : W₃ ≤ W) (hUW : U ≤ a ⁻¹ᵁ W) (hUW₃ : U ≤ a ⁻¹ᵁ W₃) (b : Γ(X, W)) :
    pullbackD f a W₃ hUW₃ ((X.presheaf.map (homOfLE hW₃W).op).hom b) = pullbackD f a W hUW b := by
  rw [← map_pullbackD f a W₃ (le_refl (a ⁻¹ᵁ W₃)) hUW₃ hUW₃, pullbackD_map f a hW₃W b,
    ← map_pullbackD f a W (le_refl (a ⁻¹ᵁ W)) hUW hUW, ← Functor.map_comp_apply]
  rfl

/-- **A linear map out of the sections of `a^*Ω_{X/S}` is determined by the derivation it
induces in one chart.** Let `V` be an affine open of `S` and `W` an affine open of `X` with
`W ≤ f ⁻¹ᵁ V`, let `U` be an affine open of `T` carried by `a` into `W` and let `M` be a
`Γ(T, U)`-module. Two `Γ(T, U)`-linear maps `Γ(a^*Ω_{X/S}, U) ⟶ M` agreeing on the pullbacks of
the universal differentials of the sections of `𝒪_X` over `W` are equal.

This is the uniqueness clause of
`Stacks.Smooth.existsUnique_linearMap_of_leibniz_isAffineOpen`, read as an extensionality
principle: the family `b ↦ θ₁ (pullbackD f a W hUW b)` satisfies the three derivation axioms
because `Stacks.Smooth.pullbackD` does, by `Stacks.Smooth.pullbackD_appLE` and
`Stacks.Smooth.pullbackD_mul'`. -/
theorem hom_ext_pullbackD {X S T : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X) {V : S.Opens}
    {W : X.Opens} {U : T.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) (hUW : U ≤ a ⁻¹ᵁ W) (M : Type u) [AddCommGroup M] [Module Γ(T, U) M]
    {θ₁ θ₂ : Γ(pullbackCotangentSheaf f a, U) →ₗ[Γ(T, U)] M}
    (h : ∀ b : Γ(X, W), θ₁ (pullbackD f a W hUW b) = θ₂ (pullbackD f a W hUW b)) :
    θ₁ = θ₂ := by
  obtain ⟨θ, -, huniq⟩ := existsUnique_linearMap_of_leibniz_isAffineOpen f a hU hV hW hWV hUW M
    (fun b ↦ θ₁ (pullbackD f a W hUW b)) (fun x y ↦ by rw [map_add, map_add])
    (fun r ↦ by rw [pullbackD_appLE f a W hWV hUW r, map_zero])
    (fun x y ↦ by rw [pullbackD_mul' f a W hUW x y, map_add, map_smul, map_smul])
  exact (huniq θ₁ fun b ↦ rfl).trans (huniq θ₂ fun b ↦ (h b).symm).symm

/-! ### Comparison of two localizations of a module of linear maps -/

section Abstract

open Stacks.RingTheory.CechAcyclicity in
/-- A power of a divisor of `b'` acts invertibly on any module on which `b'` acts invertibly. -/
theorem isUnit_algebraMap_powers_of_dvd {A : Type u} [CommRing A] {b b' : A} (hbb' : b ∣ b')
    {N : Type*} [AddCommGroup N] [Module A N]
    (hb' : IsUnit (algebraMap A (Module.End A N) b')) (s : Submonoid.powers b) :
    IsUnit (algebraMap A (Module.End A N) (s : A)) := by
  obtain ⟨k, hk⟩ := s.2
  rw [← hk, map_pow]
  exact (isUnit_algebraMap_of_dvd hbb' hb').pow k

/-- A power of a divisor of `b'` acts invertibly on any localization of a module at the powers
of `b'`. -/
private theorem isUnit_algebraMap_powers_of_isLocalizedModule {A : Type u} [CommRing A]
    {b b' : A} (hbb' : b ∣ b') {N N' : Type*} [AddCommGroup N] [Module A N] [AddCommGroup N']
    [Module A N'] (g : N →ₗ[A] N') [IsLocalizedModule (Submonoid.powers b') g]
    (s : Submonoid.powers b) : IsUnit (algebraMap A (Module.End A N') (s : A)) :=
  isUnit_algebraMap_powers_of_dvd hbb'
    (IsLocalizedModule.map_units g (⟨b', Submonoid.mem_powers b'⟩ : Submonoid.powers b')) s

variable {A : Type u} [CommRing A] {P C P₁ C₁ P₂ C₂ R₁ R₂ : Type u}
  [AddCommGroup P] [Module A P] [AddCommGroup C] [Module A C]
  [AddCommGroup P₁] [Module A P₁] [AddCommGroup C₁] [Module A C₁]
  [AddCommGroup P₂] [Module A P₂] [AddCommGroup C₂] [Module A C₂]
  [CommRing R₁] [Algebra A R₁] [CommRing R₂] [Algebra A R₂]
  [Module R₁ P₁] [Module R₁ C₁] [IsScalarTower A R₁ P₁] [IsScalarTower A R₁ C₁]
  [Module R₂ P₂] [Module R₂ C₂] [IsScalarTower A R₂ P₂] [IsScalarTower A R₂ C₂]
  {b b' : A} [IsLocalization (Submonoid.powers b) R₁] [IsLocalization (Submonoid.powers b') R₂]
  (p₁ : P →ₗ[A] P₁) (c₁ : C →ₗ[A] C₁) (p₂ : P →ₗ[A] P₂) (c₂ : C →ₗ[A] C₂)
  [IsLocalizedModule (Submonoid.powers b) p₁] [IsLocalizedModule (Submonoid.powers b) c₁]
  [IsLocalizedModule (Submonoid.powers b') p₂] [IsLocalizedModule (Submonoid.powers b') c₂]
  [Module.FinitePresentation A P]

omit [Module.FinitePresentation A P] in
/-- The localization of a module of linear maps, evaluated on an element coming from the source
module. This is the defining property of `IsLocalizedModule.mapExtendScalars`, with the
`extendScalars` wrapper removed. -/
theorem mapExtendScalars_apply_localizationMap (θ : P →ₗ[A] C) (y : P) :
    IsLocalizedModule.mapExtendScalars (Submonoid.powers b) p₁ c₁ R₁ θ (p₁ y) = c₁ (θ y) :=
  IsLocalizedModule.map_apply _ p₁ c₁ θ y

/-- **The comparison map between two localizations of a module of linear maps.** For `b ∣ b'`,
the canonical `A`-linear map from the localization at the powers of `b` of `P →ₗ[A] C` to its
localization at the powers of `b'`, both read through
`IsLocalizedModule.mapExtendScalars`. -/
noncomputable def homCompare (hbb' : b ∣ b') : (P₁ →ₗ[R₁] C₁) →ₗ[A] (P₂ →ₗ[R₂] C₂) :=
  IsLocalizedModule.lift (Submonoid.powers b)
    (IsLocalizedModule.mapExtendScalars (Submonoid.powers b) p₁ c₁ R₁)
    (IsLocalizedModule.mapExtendScalars (Submonoid.powers b') p₂ c₂ R₂)
    (isUnit_algebraMap_powers_of_dvd hbb'
      (IsLocalizedModule.map_units
        (IsLocalizedModule.mapExtendScalars (Submonoid.powers b') p₂ c₂ R₂)
        (⟨b', Submonoid.mem_powers b'⟩ : Submonoid.powers b')))

/-- `Stacks.Smooth.homCompare` is compatible with the two localization maps. -/
theorem homCompare_mapExtendScalars (hbb' : b ∣ b') (θ : P →ₗ[A] C) :
    homCompare p₁ c₁ p₂ c₂ hbb'
        (IsLocalizedModule.mapExtendScalars (Submonoid.powers b) p₁ c₁ R₁ θ)
      = IsLocalizedModule.mapExtendScalars (Submonoid.powers b') p₂ c₂ R₂ θ :=
  IsLocalizedModule.lift_apply _ _ _ _ θ

/-- **The comparison map is computed by the restriction maps.** Let `σ : P₁ ⟶ P₂` and
`ρ : C₁ ⟶ C₂` be `A`-linear maps compatible with the four localization maps. Then for every
`R₁`-linear map `θ : P₁ ⟶ C₁`, the comparison `Stacks.Smooth.homCompare` of `θ`, evaluated at
`σ x`, is `ρ` of `θ` evaluated at `x`.

This is what reads the abstract comparison of two localizations of a module of linear maps as
the geometric restriction of sections, and it is the only property of the comparison that the
Čech step of [Stacks Project, Tag 02H6] uses. -/
theorem homCompare_apply (hbb' : b ∣ b') (σ : P₁ →ₗ[A] P₂) (hσ : ∀ y : P, σ (p₁ y) = p₂ y)
    (ρ : C₁ →ₗ[A] C₂) (hρ : ∀ z : C, ρ (c₁ z) = c₂ z) (θ : P₁ →ₗ[R₁] C₁) (x : P₁) :
    homCompare (R₂ := R₂) p₁ c₁ p₂ c₂ hbb' θ (σ x) = ρ (θ x) := by
  have hunit := isUnit_algebraMap_powers_of_isLocalizedModule hbb' c₂
  have key : ∀ ν : P →ₗ[A] C, ∀ z : P₁,
      IsLocalizedModule.mapExtendScalars (Submonoid.powers b') p₂ c₂ R₂ ν (σ z)
        = ρ (IsLocalizedModule.mapExtendScalars (Submonoid.powers b) p₁ c₁ R₁ ν z) := by
    intro ν
    have h : ((IsLocalizedModule.mapExtendScalars (Submonoid.powers b') p₂ c₂ R₂
          ν).restrictScalars A).comp σ
        = ρ.comp ((IsLocalizedModule.mapExtendScalars (Submonoid.powers b) p₁ c₁ R₁
          ν).restrictScalars A) := by
      refine IsLocalizedModule.ext (Submonoid.powers b) p₁ hunit (LinearMap.ext fun y ↦ ?_)
      change IsLocalizedModule.mapExtendScalars (Submonoid.powers b') p₂ c₂ R₂ ν (σ (p₁ y))
        = ρ (IsLocalizedModule.mapExtendScalars (Submonoid.powers b) p₁ c₁ R₁ ν (p₁ y))
      rw [hσ y, mapExtendScalars_apply_localizationMap, mapExtendScalars_apply_localizationMap,
        hρ]
    exact fun z ↦ LinearMap.congr_fun h z
  obtain ⟨⟨ν, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers b)
    (IsLocalizedModule.mapExtendScalars (Submonoid.powers b) p₁ c₁ R₁) θ
  rw [Submonoid.smul_def] at hs
  have e₁ : (s : A) • homCompare (R₂ := R₂) p₁ c₁ p₂ c₂ hbb' θ
      = IsLocalizedModule.mapExtendScalars (Submonoid.powers b') p₂ c₂ R₂ ν := by
    rw [← map_smul, hs, homCompare_mapExtendScalars]
  have hL := congrArg (fun φ : P₂ →ₗ[R₂] C₂ ↦ φ (σ x)) e₁
  have hR := congrArg (fun φ : P₁ →ₗ[R₁] C₁ ↦ φ x) hs
  change (s : A) • homCompare (R₂ := R₂) p₁ c₁ p₂ c₂ hbb' θ (σ x)
    = IsLocalizedModule.mapExtendScalars (Submonoid.powers b') p₂ c₂ R₂ ν (σ x) at hL
  change (s : A) • θ x
    = IsLocalizedModule.mapExtendScalars (Submonoid.powers b) p₁ c₁ R₁ ν x at hR
  refine ((Module.End.isUnit_iff _).mp (hunit s)).1 ?_
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, hL, key ν x, ← hR, map_smul]


/-- **The abstract comparison map is the Čech restriction map.** Transported along the canonical
isomorphisms with `Stacks.RingTheory.CechAcyclicity.AwayLoc`, the comparison map
`Stacks.Smooth.homCompare` is `Stacks.RingTheory.CechAcyclicity.resAway`. -/
theorem homCompare_iso (hbb' : b ∣ b')
    (z : Stacks.RingTheory.CechAcyclicity.AwayLoc (P →ₗ[A] C) b) :
    homCompare p₁ c₁ p₂ c₂ hbb'
        (IsLocalizedModule.iso (Submonoid.powers b)
          (IsLocalizedModule.mapExtendScalars (Submonoid.powers b) p₁ c₁ R₁) z)
      = IsLocalizedModule.iso (Submonoid.powers b')
          (IsLocalizedModule.mapExtendScalars (Submonoid.powers b') p₂ c₂ R₂)
          (Stacks.RingTheory.CechAcyclicity.resAway (P →ₗ[A] C) hbb' z) := by
  have hunit := isUnit_algebraMap_powers_of_isLocalizedModule hbb'
    (IsLocalizedModule.mapExtendScalars (Submonoid.powers b') p₂ c₂ R₂)
  have h : (homCompare p₁ c₁ p₂ c₂ hbb').comp
        (IsLocalizedModule.iso (Submonoid.powers b)
          (IsLocalizedModule.mapExtendScalars (Submonoid.powers b) p₁ c₁ R₁)).toLinearMap
      = (IsLocalizedModule.iso (Submonoid.powers b')
          (IsLocalizedModule.mapExtendScalars (Submonoid.powers b')
            p₂ c₂ R₂)).toLinearMap.comp
          (Stacks.RingTheory.CechAcyclicity.resAway (P →ₗ[A] C) hbb') := by
    refine IsLocalizedModule.ext (Submonoid.powers b)
      (LocalizedModule.mkLinearMap (Submonoid.powers b) (P →ₗ[A] C)) hunit
      (LinearMap.ext fun ν ↦ ?_)
    change homCompare p₁ c₁ p₂ c₂ hbb'
        (IsLocalizedModule.iso (Submonoid.powers b)
          (IsLocalizedModule.mapExtendScalars (Submonoid.powers b) p₁ c₁ R₁)
          (LocalizedModule.mk ν 1))
      = IsLocalizedModule.iso (Submonoid.powers b')
          (IsLocalizedModule.mapExtendScalars (Submonoid.powers b') p₂ c₂ R₂)
          (Stacks.RingTheory.CechAcyclicity.resAway (P →ₗ[A] C) hbb' (LocalizedModule.mk ν 1))
    rw [IsLocalizedModule.iso_mk_one, homCompare_mapExtendScalars,
      Stacks.RingTheory.CechAcyclicity.resAway_mk_one, IsLocalizedModule.iso_mk_one]
  exact LinearMap.congr_fun h z

end Abstract

/-! ### The conormal module of a thickening restricted to an open -/

section Conormal

variable {T T' : Scheme.{u}} [IsAffine T'] {i : T ⟶ T'}
  (hi : Thickenings.IsFirstOrderThickening i)

include hi

omit [IsAffine T'] in
/-- The closed subscheme of a thickening restricted to an affine open of the ambient scheme is
affine, being a closed subscheme of that affine open. -/
theorem isAffine_preimage_of_isAffine (U' : T'.Opens) [IsAffine (U' : Scheme.{u})] :
    IsAffine ((i ⁻¹ᵁ U' : T.Opens) : Scheme.{u}) :=
  have : IsClosedImmersion (i ∣_ U') := (isFirstOrderThickening_morphismRestrict hi U').1
  (IsClosedImmersion.isAffine_surjective_of_isAffine (i ∣_ U')).1

omit [IsAffine T'] in
/-- The action of `Γ(T, ⊤)` on the conormal module of the thickening restricted to an affine open
`U'` of `T'` is multiplication by the restriction to `U'` of any preimage of the scalar in
`Γ(T', ⊤)`. This is `Stacks.Smooth.coe_smul_conormal_basicOpen` for an arbitrary affine open in
place of a basic open. -/
theorem coe_smul_conormalOpens (U' : T'.Opens) [IsAffine (U' : Scheme.{u})]
    {r : Γ(T', (⊤ : T'.Opens))} {c : Γ(T, (⊤ : T.Opens))} (hr : i.appTop.hom r = c)
    (y : RingHom.ker (i ∣_ U').appTop.hom) :
    letI := isAffine_preimage_of_isAffine hi U'
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
    ((c • y : RingHom.ker (i ∣_ U').appTop.hom) : Γ((U' : Scheme.{u}),
        (⊤ : (U' : Scheme.{u}).Opens)))
      = U'.ι.appTop.hom r * (y : Γ((U' : Scheme.{u}), (⊤ : (U' : Scheme.{u}).Opens))) := by
  let := isAffine_preimage_of_isAffine hi U'
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
  let := moduleOfOpensAppTop (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
  rw [← hr, moduleOfOpensAppTop_smul, ← appTop_morphismRestrict_comm i U' r,
    thickeningKerModule_smul (isFirstOrderThickening_morphismRestrict hi U'),
    Submodule.coe_smul, smul_eq_mul]

/-- **The restriction map of conormal modules attached to an open.** For `i : T ⟶ T'` a
first-order thickening with `T'` affine and `U'` an affine open of `T'`, restriction of sections
of `𝒪_{T'}` carries the conormal module of `i` into the conormal module of `i ∣_ U'`,
`Γ(T, ⊤)`-linearly.

This is `Stacks.Smooth.conormalRestrict` for an arbitrary affine open in place of a basic
open. -/
noncomputable def conormalResOpens (U' : T'.Opens) [IsAffine (U' : Scheme.{u})] :
    letI := isAffine_preimage_of_isAffine hi U'
    letI := thickeningKerModule hi
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
    RingHom.ker i.appTop.hom →ₗ[Γ(T, (⊤ : T.Opens))] RingHom.ker (i ∣_ U').appTop.hom :=
  letI := isAffine_preimage_of_isAffine hi U'
  letI := thickeningKerModule hi
  letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
  letI := moduleOfOpensAppTop (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
  { toFun := fun x ↦ ⟨U'.ι.appTop.hom (x : Γ(T', (⊤ : T'.Opens))), by
      rw [RingHom.mem_ker, appTop_morphismRestrict_comm i U', RingHom.mem_ker.mp x.2, map_zero]⟩
    map_add' := fun x y ↦ Subtype.ext (by
      simp only [Submodule.coe_add]
      exact map_add _ _ _)
    map_smul' := fun c x ↦ Subtype.ext (by
      obtain ⟨r, hr⟩ := surjective_appTop_of_isFirstOrderThickening hi c
      rw [RingHom.id_apply, coe_smul_conormalOpens hi U' hr]
      change U'.ι.appTop.hom ((c • x : RingHom.ker i.appTop.hom) : Γ(T', (⊤ : T'.Opens))) = _
      rw [coe_smul_conormal hi hr, map_mul]) }

/-- The value of `Stacks.Smooth.conormalResOpens` is the restriction of the section. -/
theorem conormalResOpens_apply (U' : T'.Opens) [IsAffine (U' : Scheme.{u})]
    (x : RingHom.ker i.appTop.hom) :
    ((conormalResOpens hi U' x : RingHom.ker (i ∣_ U').appTop.hom) :
        Γ((U' : Scheme.{u}), (⊤ : (U' : Scheme.{u}).Opens)))
      = U'.ι.appTop.hom (x : Γ(T', (⊤ : T'.Opens))) :=
  rfl

/-- `Stacks.Smooth.conormalResOpens` at a basic open is
`Stacks.Smooth.conormalRestrict`. -/
theorem conormalResOpens_basicOpen (g : Γ(T', (⊤ : T'.Opens))) :
    letI : IsAffine ((T'.basicOpen g : T'.Opens) : Scheme.{u}) :=
      (isAffine_basicOpen_of_isFirstOrderThickening hi g).1
    conormalResOpens hi (T'.basicOpen g) = conormalRestrict hi g :=
  rfl

/-- **The restriction map of conormal modules attached to an inclusion of opens.** For
`U'' ≤ U'` affine opens of `T'`, restriction of sections of `𝒪_{T'}` carries the conormal module
of `i ∣_ U'` into the conormal module of `i ∣_ U''`, `Γ(T, ⊤)`-linearly. -/
noncomputable def conormalResLE {U' U'' : T'.Opens} [IsAffine (U' : Scheme.{u})]
    [IsAffine (U'' : Scheme.{u})] (h : U'' ≤ U') :
    letI := isAffine_preimage_of_isAffine hi U'
    letI := isAffine_preimage_of_isAffine hi U''
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U'')
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ U'') (RingHom.ker (i ∣_ U'').appTop.hom)
    RingHom.ker (i ∣_ U').appTop.hom →ₗ[Γ(T, (⊤ : T.Opens))]
      RingHom.ker (i ∣_ U'').appTop.hom :=
  letI := isAffine_preimage_of_isAffine hi U'
  letI := isAffine_preimage_of_isAffine hi U''
  letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
  letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U'')
  letI := moduleOfOpensAppTop (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
  letI := moduleOfOpensAppTop (i ⁻¹ᵁ U'') (RingHom.ker (i ∣_ U'').appTop.hom)
  { toFun := fun y ↦ ⟨(T'.homOfLE h).appTop.hom
      (y : Γ((U' : Scheme.{u}), (⊤ : (U' : Scheme.{u}).Opens))), by
      have hsq : (T'.homOfLE h).appTop ≫ (i ∣_ U'').appTop
          = (i ∣_ U').appTop ≫ (T.homOfLE (show i ⁻¹ᵁ U'' ≤ i ⁻¹ᵁ U'
            from fun _ hx ↦ h hx)).appTop := by
        rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, morphismRestrict_comp_homOfLE i h]
      rw [RingHom.mem_ker, ← CommRingCat.comp_apply, hsq, CommRingCat.comp_apply,
        RingHom.mem_ker.mp y.2, map_zero]⟩
    map_add' := fun x y ↦ Subtype.ext (by
      simp only [Submodule.coe_add]
      exact map_add _ _ _)
    map_smul' := fun c y ↦ Subtype.ext (by
      obtain ⟨r, hr⟩ := surjective_appTop_of_isFirstOrderThickening hi c
      rw [RingHom.id_apply, coe_smul_conormalOpens hi U'' hr]
      change (T'.homOfLE h).appTop.hom
        ((c • y : RingHom.ker (i ∣_ U').appTop.hom) : Γ((U' : Scheme.{u}), ⊤)) = _
      rw [coe_smul_conormalOpens hi U' hr, map_mul, ← CommRingCat.comp_apply,
        ← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]) }

/-- The value of `Stacks.Smooth.conormalResLE` is the restriction of the section. -/
theorem conormalResLE_apply {U' U'' : T'.Opens} [IsAffine (U' : Scheme.{u})]
    [IsAffine (U'' : Scheme.{u})] (h : U'' ≤ U')
    (y : RingHom.ker (i ∣_ U').appTop.hom) :
    ((conormalResLE hi h y : RingHom.ker (i ∣_ U'').appTop.hom) :
        Γ((U'' : Scheme.{u}), (⊤ : (U'' : Scheme.{u}).Opens)))
      = (T'.homOfLE h).appTop.hom (y : Γ((U' : Scheme.{u}), (⊤ : (U' : Scheme.{u}).Opens))) :=
  rfl

/-- **The conormal restriction maps compose.** Restricting the conormal module of `i` to an
affine open `U'` and then to a smaller affine open `U''` is restricting it to `U''`. -/
theorem conormalResLE_comp_conormalResOpens {U' U'' : T'.Opens} [IsAffine (U' : Scheme.{u})]
    [IsAffine (U'' : Scheme.{u})] (h : U'' ≤ U') (x : RingHom.ker i.appTop.hom) :
    conormalResLE hi h (conormalResOpens hi U' x) = conormalResOpens hi U'' x :=
  Subtype.ext (by
    rw [conormalResLE_apply, conormalResOpens_apply, conormalResOpens_apply,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι])

end Conormal

/-! ### The module of linear maps `Γ(a^*Ω_{X/S}, -) ⟶ 𝒞` localizes -/

section HomLocalization

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) (a : T ⟶ X)

/-- **The sections of `𝒪_T` over the closed subscheme of a basic open are a localization.** For
`i : T ⟶ T'` a morphism with `T` affine and `c` a global section of `T'`, the restriction map
`Γ(T, ⊤) ⟶ Γ(T, i ⁻¹ᵁ T'.basicOpen c)` exhibits its target as the localization of its source away
from the image of `c`. This is
`AlgebraicGeometry.isLocalization_away_of_isAffine` read on `i ⁻¹ᵁ T'.basicOpen c`, which is a
basic open of `T` by `Stacks.Smooth.preimage_basicOpen_appTop`. -/
theorem isLocalization_preimage_basicOpen [IsAffine T] (i : T ⟶ T')
    (c : Γ(T', (⊤ : T'.Opens))) :
    letI := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    IsLocalization.Away (i.appTop.hom c) Γ(T, i ⁻¹ᵁ T'.basicOpen c) := by
  have key : ∀ O : T.Opens, O = T.basicOpen (i.appTop.hom c) →
      let := algebraOfLE T (le_top : O ≤ ⊤)
      IsLocalization.Away (i.appTop.hom c) Γ(T, O) := by
    rintro O rfl
    exact AlgebraicGeometry.isLocalization_away_of_isAffine (i.appTop.hom c)
  exact key _ (Scheme.preimage_basicOpen_top i c)

/-- **The sections of `a^*Ω_{X/S}` over the closed subscheme of a basic open are a
localization.** This is `Stacks.Smooth.isLocalizedModule_restrictₗ_pullbackCotangentSheaf'` read
on `i ⁻¹ᵁ T'.basicOpen c`. -/
theorem isLocalizedModule_restrictₗ_preimage_basicOpen [IsAffine T] (i : T ⟶ T')
    (c : Γ(T', (⊤ : T'.Opens))) :
    letI := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    IsLocalizedModule.Away (i.appTop.hom c)
      (restrictₗ (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)) := by
  have key : ∀ O : T.Opens, O = T.basicOpen (i.appTop.hom c) →
      let := moduleOfLE (pullbackCotangentSheaf f a) (le_top : O ≤ ⊤)
      IsLocalizedModule.Away (i.appTop.hom c)
        (restrictₗ (pullbackCotangentSheaf f a) (le_top : O ≤ ⊤)) := by
    rintro O rfl
    exact isLocalizedModule_restrictₗ_pullbackCotangentSheaf' f a (i.appTop.hom c)
  exact key _ (Scheme.preimage_basicOpen_top i c)

variable [IsAffine T'] {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i)

/-- `Stacks.Smooth.conormalResOpens` at a basic open is a localization map; this is
`Stacks.Smooth.isLocalizedModule_conormalRestrict`. -/
theorem isLocalizedModule_conormalResOpens_basicOpen (c : Γ(T', (⊤ : T'.Opens))) :
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffine_basicOpen_of_isFirstOrderThickening hi c).1
    letI := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
    letI := thickeningKerModule hi
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    IsLocalizedModule.Away (i.appTop.hom c) (conormalResOpens hi (T'.basicOpen c)) :=
  isLocalizedModule_conormalRestrict hi c

/-- **The module of linear maps out of the sections of `a^*Ω_{X/S}` localizes.** Let
`f : X ⟶ S` be locally of finite presentation, let `i : T ⟶ T'` be a first-order thickening with
`T'` affine, let `a : T ⟶ X` be an arbitrary morphism and let `c` be a global section of `T'`.
Then the module of `Γ(T, i ⁻¹ᵁ D(c))`-linear maps

`Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(c)) ⟶ 𝒞_{T_c/T'_c}`

is the localization, away from the image of `c`, of the module of `Γ(T, ⊤)`-linear maps
`Γ(a^*Ω_{X/S}, ⊤) ⟶ 𝒞_{T/T'}`, through `IsLocalizedModule.mapExtendScalars`.

This is the coefficient input of the Čech step (II) of [Stacks Project, Tag 02H6]. The three
ingredients are `Stacks.Smooth.finitePresentation_pullbackCotangentSheaf_of_isAffine`, which
makes `Module.FinitePresentation.isLocalizedModule_mapExtendScalars` apply,
`Stacks.Smooth.isLocalizedModule_restrictₗ_preimage_basicOpen` on the side of `a^*Ω_{X/S}` and
`Stacks.Smooth.isLocalizedModule_conormalResOpens_basicOpen` on the side of the conormal
module. -/
theorem isLocalizedModule_homLoc_basicOpen [LocallyOfFinitePresentation f]
    (c : Γ(T', (⊤ : T'.Opens))) :
    haveI : IsClosedImmersion i := hi.1
    haveI : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffine_basicOpen_of_isFirstOrderThickening hi c).1
    letI := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
    letI := thickeningKerModule hi
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    letI := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := isScalarTowerOfLE (pullbackCotangentSheaf f a)
      (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    letI := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := isLocalization_preimage_basicOpen i c
    letI := isLocalizedModule_restrictₗ_preimage_basicOpen f a i c
    letI := isLocalizedModule_conormalResOpens_basicOpen hi c
    IsLocalizedModule.Away (i.appTop.hom c)
      (IsLocalizedModule.mapExtendScalars (Submonoid.powers (i.appTop.hom c))
        (restrictₗ (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤))
        (conormalResOpens hi (T'.basicOpen c)) Γ(T, i ⁻¹ᵁ T'.basicOpen c)) := by
  have hci : IsClosedImmersion i := hi.1
  have hTa : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  let : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
    (isAffine_basicOpen_of_isFirstOrderThickening hi c).1
  let := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
  let := thickeningKerModule hi
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isScalarTowerOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isLocalization_preimage_basicOpen i c
  let := isLocalizedModule_restrictₗ_preimage_basicOpen f a i c
  let := isLocalizedModule_conormalResOpens_basicOpen hi c
  have := finitePresentation_pullbackCotangentSheaf_of_isAffine f a
  infer_instance

/-- **The Čech restriction map of the module of linear maps is restriction of sections.** Let
`f : X ⟶ S` be locally of finite presentation, let `i : T ⟶ T'` be a first-order thickening with
`T'` affine, let `a : T ⟶ X` be arbitrary and let `c`, `c'` be global sections of `T'` with
`D(c') ≤ D(c)`. Then the abstract comparison `Stacks.Smooth.homCompare` of the two localizations
of the module of `Γ(T, ⊤)`-linear maps `Γ(a^*Ω_{X/S}, ⊤) ⟶ 𝒞_{T/T'}` is computed by restriction
of sections on both sides: it carries `θ` to the map `x ↦ 𝒞-restriction of θ` applied to the
restriction of `x`.

Together with `Stacks.Smooth.homCompare_iso` this identifies
`Stacks.RingTheory.CechAcyclicity.resAway` on the Čech term with restriction of sections, which
is the compatibility that step (II) of [Stacks Project, Tag 02H6] needs in order to read the
chart-local differences of lifts as a Čech cochain. -/
theorem homCompare_restrictₗ [LocallyOfFinitePresentation f] (c c' : Γ(T', (⊤ : T'.Opens)))
    (hcc' : T'.basicOpen c' ≤ T'.basicOpen c) (hd : i.appTop.hom c ∣ i.appTop.hom c') :
    haveI : IsClosedImmersion i := hi.1
    haveI : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffine_basicOpen_of_isFirstOrderThickening hi c).1
    letI : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
      (isAffine_basicOpen_of_isFirstOrderThickening hi c').1
    letI := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
    letI := isAffine_preimage_of_isAffine hi (T'.basicOpen c')
    letI := thickeningKerModule hi
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c'))
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c')
      (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
    letI := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    letI := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤)
    letI := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    letI := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤)
    letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c')
      (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
    letI := isScalarTowerOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    letI := isScalarTowerOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤)
    letI := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c')
      (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
    letI := isLocalization_preimage_basicOpen i c
    letI := isLocalization_preimage_basicOpen i c'
    letI := isLocalizedModule_restrictₗ_preimage_basicOpen f a i c
    letI := isLocalizedModule_restrictₗ_preimage_basicOpen f a i c'
    letI := isLocalizedModule_conormalResOpens_basicOpen hi c
    letI := isLocalizedModule_conormalResOpens_basicOpen hi c'
    haveI := finitePresentation_pullbackCotangentSheaf_of_isAffine f a
    letI := moduleOfLE (pullbackCotangentSheaf f a)
      (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx)
    letI := isScalarTowerOfLE_of_le (pullbackCotangentSheaf f a)
      (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
      (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx)
    ∀ (θ : Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c) →ₗ[Γ(T, i ⁻¹ᵁ T'.basicOpen c)]
        RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      (x : Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c)),
      homCompare (R₂ := Γ(T, i ⁻¹ᵁ T'.basicOpen c'))
          (restrictₗ (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤))
          (conormalResOpens hi (T'.basicOpen c))
          (restrictₗ (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤))
          (conormalResOpens hi (T'.basicOpen c')) hd θ
          (restrictₗ (pullbackCotangentSheaf f a)
            (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx) x)
        = conormalResLE hi hcc' (θ x) := by
  have hci : IsClosedImmersion i := hi.1
  have hTa : IsAffine T := (IsClosedImmersion.isAffine_surjective_of_isAffine i).1
  let : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
    (isAffine_basicOpen_of_isFirstOrderThickening hi c).1
  let : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
    (isAffine_basicOpen_of_isFirstOrderThickening hi c').1
  let := isAffine_preimage_of_isAffine hi (T'.basicOpen c)
  let := isAffine_preimage_of_isAffine hi (T'.basicOpen c')
  let := thickeningKerModule hi
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c'))
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfOpensAppTop (i ⁻¹ᵁ T'.basicOpen c')
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := moduleOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤)
  let := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := algebraOfLE T (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c')
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := isScalarTowerOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
  let := isScalarTowerOfLE (pullbackCotangentSheaf f a) (le_top : i ⁻¹ᵁ T'.basicOpen c' ≤ ⊤)
  let := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isScalarTower_moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c')
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := isLocalization_preimage_basicOpen i c
  let := isLocalization_preimage_basicOpen i c'
  let := isLocalizedModule_restrictₗ_preimage_basicOpen f a i c
  let := isLocalizedModule_restrictₗ_preimage_basicOpen f a i c'
  let := isLocalizedModule_conormalResOpens_basicOpen hi c
  let := isLocalizedModule_conormalResOpens_basicOpen hi c'
  have := finitePresentation_pullbackCotangentSheaf_of_isAffine f a
  let := moduleOfLE (pullbackCotangentSheaf f a)
    (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx)
  let := isScalarTowerOfLE_of_le (pullbackCotangentSheaf f a)
    (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤)
    (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from fun _ hx ↦ hcc' hx)
  intro θ x
  exact homCompare_apply (R₂ := Γ(T, i ⁻¹ᵁ T'.basicOpen c')) _ _ _ _ hd
    ((restrictₗ (pullbackCotangentSheaf f a)
      (show i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c from
        fun _ hx ↦ hcc' hx)).restrictScalars Γ(T, (⊤ : T.Opens)))
    (fun y ↦ restrictₗ_restrictₗ (pullbackCotangentSheaf f a)
      (le_top : i ⁻¹ᵁ T'.basicOpen c ≤ ⊤) _ y)
    (conormalResLE hi hcc') (fun z ↦ conormalResLE_comp_conormalResOpens hi hcc' z) θ x

end HomLocalization

end Stacks.Smooth

end
