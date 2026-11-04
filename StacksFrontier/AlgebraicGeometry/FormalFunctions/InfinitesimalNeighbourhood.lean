module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Infinitesimal neighbourhoods of a fibre

Let `f : X ⟶ Y` be a morphism of schemes and let `y` be a point of `Y`. Writing
`𝒪_{Y,y}` for the local ring of `Y` at `y` and `𝔪_y` for its maximal ideal, the `n`-th
*infinitesimal neighbourhood of the fibre `X_y`* is the fibre product

`X_n = Spec (𝒪_{Y,y}/𝔪_y ^ n) ×_Y X`,

and a sheaf of modules `ℱ` on `X` restricts to `ℱ_n = i_n ^* ℱ` on it, where
`i_n : X_n ⟶ X` is the projection. This file constructs that system: the base schemes
`Spec (𝒪_{Y,y}/𝔪_y ^ n)` and their canonical morphisms `c_n` to `Y`, the fibre products `X_n`
with their two projections `i_n` and `f_n`, the restricted modules `ℱ_n`, the transition
morphisms `X_n ⟶ X_m` for `n ≤ m`, and the properties of all of these that are needed to speak
about cohomology on `X_n`: `f_n` is proper when `f` is and `X_n` is locally Noetherian when `Y`
is (both by instance search), and `ℱ_n` is coherent when `ℱ` is.

This is the geometric setup of the theorem on formal functions in the form
[Stacks, Tag 02OD]. The conclusion of that tag — the identification
`(R ᵖ f_* ℱ)_y ^∧ ≅ lim_n H ᵖ (X_n, ℱ_n)` in every degree — is proved in
`StacksFrontier/AlgebraicGeometry/FormalFunctions/CompletionStalkLimit.lean`, which is where the
tag is registered; see the implementation notes below.

## Main definitions

* `Stacks.FormalFunctions.stalkQuotient`: the ring `𝒪_{Y,y}/𝔪_y ^ n`.
* `Stacks.FormalFunctions.infinitesimalBase`: the canonical morphism
  `c_n : Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Y`.
* `Stacks.FormalFunctions.baseTransition`: the closed immersion
  `Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ m)` for `n ≤ m`.
* `Stacks.FormalFunctions.infinitesimalNeighbourhood`: the scheme `X_n`, with its projections
  `Stacks.FormalFunctions.infinitesimalι` (`i_n`) and
  `Stacks.FormalFunctions.infinitesimalStructure` (`f_n`).
* `Stacks.FormalFunctions.infinitesimalModule`: the module `ℱ_n = i_n ^* ℱ`.
* `Stacks.FormalFunctions.infinitesimalTransition`: the morphism `X_n ⟶ X_m` for `n ≤ m`.
* `Stacks.FormalFunctions.infinitesimalDiagram`: the whole system as a functor `ℕ ⥤ Scheme`,
  together with `Stacks.FormalFunctions.infinitesimalCocone`, the cocone on it given by the
  projections `i_n` to `X`.
* `Stacks.FormalFunctions.fiberIsoInfinitesimalNeighbourhoodOne`: the identification
  `X_y ≅ X_1` of the scheme-theoretic fibre with the first neighbourhood.

## Main results

* `Stacks.FormalFunctions.isPreimmersion_infinitesimalBase`: `c_n` is a preimmersion.
* `Stacks.FormalFunctions.isNoetherianRing_stalkQuotient`: `𝒪_{Y,y}/𝔪_y ^ n` is Noetherian
  when `Y` is locally Noetherian; hence, by instance search, `X_n` is locally Noetherian when `f`
  is locally of finite type.
* `Stacks.FormalFunctions.isPullback_infinitesimalTransition`: `X_n` is the base change of `X_m`
  along `Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ m)`, so
  `Stacks.FormalFunctions.isClosedImmersion_infinitesimalTransition` holds: `X_n` is a closed
  subscheme of `X_m`.
* `Stacks.FormalFunctions.isCoherent_infinitesimalModule`: `ℱ_n` is coherent when `ℱ` is and `Y`
  is locally Noetherian.
* `Stacks.FormalFunctions.infinitesimalModuleTransitionIso`: `ℱ_n` is the restriction of `ℱ_m`
  along `X_n ⟶ X_m`, so the modules in the system are compatible.
* `Stacks.FormalFunctions.isPullback_fiberToInfinitesimalNeighbourhoodOne`: `X_1 = X_y`, the
  statement that the system starts at the fibre.

## Implementation notes

The morphism `c_n` is the composite of the closed immersion
`Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec 𝒪_{Y,y}` with Mathlib's `AlgebraicGeometry.Scheme.fromSpecStalk`,
which is the canonical morphism `Spec 𝒪_{Y,y} ⟶ Y` of [Stacks, Tag 01J7]. It is a preimmersion,
not in general a closed immersion: that happens when `Y` is the spectrum of a local ring with
closed point `y`, which is the situation the source reduces to. What *is* a closed immersion for
every `Y` is each transition morphism `X_n ⟶ X_m`, since it is a base change of
`Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ m)`, and that is the content of
`isPullback_infinitesimalTransition`.

Indices start at `n = 0`, where `𝔪_y ^ 0 = 𝒪_{Y,y}`, so `𝒪_{Y,y}/𝔪_y ^ 0` is the zero ring and
`X_0` is empty. The source indexes from `n = 1`, where `X_1 = X_y` is the fibre. Nothing below
needs `n ≥ 1`, so no such hypothesis is imposed; a statement about the limit over `n` is
unaffected by the extra initial term, since the system is cofinal in either indexing.

**What this file does not contain.** The conclusion of [Stacks, Tag 02OD] needs three inputs,
none of them proved here. In degree `p = 0` only the first of them is absent from this
library:

* the theorem on formal functions itself, [Stacks, Tag 02OC]: for `A` Noetherian, `I ⊆ A` an
  ideal, `f` proper and `ℱ` coherent, `H ᵖ (X, ℱ) ^∧ ≅ lim_n H ᵖ (X, ℱ/I ⁿ ℱ)`. This is the one
  genuine blocker at `p = 0`;
* flat base change for higher direct images, [Stacks, Tag 02KH], which is what identifies
  `(R ᵖ f_* ℱ)_y` with `H ᵖ` of the base change along `Spec 𝒪_{Y,y} ⟶ Y`. Part (1) of that tag
  **at `p = 0`** is proved unconditionally, as
  `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat` of
  `FlatBaseChangeCohomology/AffineDegreeZero/Modules.lean`, and it instantiates at exactly the
  morphism wanted here: flatness of the stalk inclusion is unconditional, as
  `AlgebraicGeometry.flat_fromSpecStalk` of `Pullback/StalkFromSpecStalk.lean`, and `[IsProper f]`
  supplies the quasi-compactness and quasi-separatedness. Only the positive-degree case is
  missing, which matters because `p = 0` is the degree [Stacks, Tag 0G7X] reads this chain in;
* the invariance of cohomology under pushforward along the closed immersion `i_n`, the
  combination of [Stacks, Tag 01Y6] with the Leray spectral sequence, which is what identifies
  `H ᵖ (X_n, ℱ_n)` with `H ᵖ (X, ℱ/𝔪_y ⁿ ℱ)`. At `p = 0` no Leray sequence is needed, since
  global sections along a closed immersion agree, leaving only the identification of `i_{n*}ℱ_n`
  with `ℱ/𝔪_y ⁿ ℱ`, and **that identification is proved**. It is [Stacks, Tag 0EL1], proved for
  an arbitrary closed immersion presented by its ideal sheaf as
  `Stacks.Algebraization.idealQuotientPushforwardIso` of
  `FormalGeometry/CompletionFullyFaithful/SectionsComplete.lean`, and instantiated at the fibre
  product `X ×_{Spec A} Spec (A/I ⁿ)` of the source's own diagram as
  `Stacks.Cohomology.FormalFunctions.pushforwardPullbackBaseIdealIso` of
  `FormalFunctionsTheorem/IdealPowerQuotientSubscheme.lean`. The quotient there is by the `n`-th
  power of `I · 𝒪_X`, which is the shape [Stacks, Tag 02OC] uses, and the affine base is the one
  reached once the second bullet's reduction has replaced `Y` by `Spec 𝒪_{Y,y}`.

Over a general `Y` the morphism `i_n` is *not* a closed immersion, since `c_n` is only a
preimmersion (see above), so the identification cannot be stated at `infinitesimalι` below
without that reduction; the reduction is the flat-base-change bullet, not this one.

The `@[stacks 02OD]` attributes below therefore register the setup paragraph of the tag only --
the neighbourhoods, the sheaves restricted to them, and the identification of `X_1` with the
fibre -- and no part of its conclusion.

## References

* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.FormalFunctions

variable {X Y : Scheme.{u}}

/-! ### The base of the system -/

/-- The maximal ideal `𝔪_y` of the local ring `𝒪_{Y,y}` of a scheme `Y` at a point `y`. -/
public abbrev stalkMaximalIdeal (y : Y) : Ideal (Y.presheaf.stalk y) :=
  IsLocalRing.maximalIdeal (Y.presheaf.stalk y)

/-- The ring `𝒪_{Y,y}/𝔪_y ^ n`, the `n`-th infinitesimal neighbourhood of a point `y` of a
scheme `Y` read as a ring. For `n = 1` this is the residue field at `y`. -/
public abbrev stalkQuotient (y : Y) (n : ℕ) : CommRingCat.{u} :=
  .of (Y.presheaf.stalk y ⧸ stalkMaximalIdeal y ^ n)

/-- The quotient map `𝒪_{Y,y} ⟶ 𝒪_{Y,y}/𝔪_y ^ n`. -/
public abbrev toStalkQuotient (y : Y) (n : ℕ) : Y.presheaf.stalk y ⟶ stalkQuotient y n :=
  CommRingCat.ofHom (Ideal.Quotient.mk (stalkMaximalIdeal y ^ n))

/-- `𝒪_{Y,y}/𝔪_y ^ n` is a Noetherian ring when `Y` is locally Noetherian, as a quotient of the
Noetherian local ring `𝒪_{Y,y}`. -/
public instance isNoetherianRing_stalkQuotient [IsLocallyNoetherian Y] (y : Y) (n : ℕ) :
    IsNoetherianRing (stalkQuotient y n) :=
  Ideal.Quotient.isNoetherianRing _

/-- The quotient map `𝒪_{Y,y} ⟶ 𝒪_{Y,y}/𝔪_y ^ n` induces a closed immersion on spectra, being
surjective. -/
public instance isClosedImmersion_specMap_toStalkQuotient (y : Y) (n : ℕ) :
    IsClosedImmersion (Spec.map (toStalkQuotient y n)) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The surjection `𝒪_{Y,y}/𝔪_y ^ m ⟶ 𝒪_{Y,y}/𝔪_y ^ n` for `n ≤ m`, induced by the inclusion
`𝔪_y ^ m ⊆ 𝔪_y ^ n`. -/
public abbrev stalkQuotientFactor (y : Y) {n m : ℕ} (h : n ≤ m) :
    stalkQuotient y m ⟶ stalkQuotient y n :=
  CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := stalkMaximalIdeal y) h))

/-- The canonical morphism `c_n : Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Y`: the quotient map on spectra,
followed by the canonical morphism `Spec 𝒪_{Y,y} ⟶ Y` of [Stacks, Tag 01J7]. -/
public def infinitesimalBase (y : Y) (n : ℕ) : Spec (stalkQuotient y n) ⟶ Y :=
  Spec.map (toStalkQuotient y n) ≫ Y.fromSpecStalk y

/-- `c_n` is a preimmersion: it is a closed immersion followed by the preimmersion
`Spec 𝒪_{Y,y} ⟶ Y`. It is not a closed immersion for general `Y`. -/
public instance isPreimmersion_infinitesimalBase (y : Y) (n : ℕ) :
    IsPreimmersion (infinitesimalBase y n) :=
  inferInstanceAs (IsPreimmersion (Spec.map (toStalkQuotient y n) ≫ Y.fromSpecStalk y))

/-- The transition morphism `Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ m)` for `n ≤ m`,
induced by the surjection `𝒪_{Y,y}/𝔪_y ^ m ⟶ 𝒪_{Y,y}/𝔪_y ^ n`. -/
public def baseTransition (y : Y) {n m : ℕ} (h : n ≤ m) :
    Spec (stalkQuotient y n) ⟶ Spec (stalkQuotient y m) :=
  Spec.map (stalkQuotientFactor y h)

/-- The transition morphism `Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ m)` is a closed
immersion, being induced by a surjection of rings. -/
public instance isClosedImmersion_baseTransition (y : Y) {n m : ℕ} (h : n ≤ m) :
    IsClosedImmersion (baseTransition y h) :=
  IsClosedImmersion.spec_of_surjective (stalkQuotientFactor y h)
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (I := stalkMaximalIdeal y) h))

/-- The quotient map to `𝒪_{Y,y}/𝔪_y ^ m` followed by the surjection onto `𝒪_{Y,y}/𝔪_y ^ n` is
the quotient map to `𝒪_{Y,y}/𝔪_y ^ n`. -/
@[simp]
public theorem toStalkQuotient_comp_stalkQuotientFactor (y : Y) {n m : ℕ} (h : n ≤ m) :
    toStalkQuotient y m ≫ stalkQuotientFactor y h = toStalkQuotient y n :=
  congrArg CommRingCat.ofHom
    (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (I := stalkMaximalIdeal y) h))

/-- The surjection `𝒪_{Y,y}/𝔪_y ^ n ⟶ 𝒪_{Y,y}/𝔪_y ^ n` attached to `n ≤ n` is the identity. -/
@[simp]
public theorem stalkQuotientFactor_refl (y : Y) (n : ℕ) :
    stalkQuotientFactor y (le_refl n) = 𝟙 (stalkQuotient y n) :=
  (congrArg CommRingCat.ofHom
    (Ideal.Quotient.factor_eq (S := stalkMaximalIdeal y ^ n))).trans CommRingCat.ofHom_id

/-- The surjections between the rings `𝒪_{Y,y}/𝔪_y ^ n` compose: for `n ≤ m ≤ k` the composite
`𝒪_{Y,y}/𝔪_y ^ k ⟶ 𝒪_{Y,y}/𝔪_y ^ m ⟶ 𝒪_{Y,y}/𝔪_y ^ n` is the surjection for `n ≤ k`. -/
@[simp]
public theorem stalkQuotientFactor_comp (y : Y) {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) :
    stalkQuotientFactor y h₂ ≫ stalkQuotientFactor y h₁ =
      stalkQuotientFactor y (h₁.trans h₂) :=
  congrArg CommRingCat.ofHom
    (Ideal.Quotient.factor_comp (Ideal.pow_le_pow_right (I := stalkMaximalIdeal y) h₂)
      (Ideal.pow_le_pow_right (I := stalkMaximalIdeal y) h₁))

/-- The transition morphisms of the base are compatible with the canonical morphisms to `Y`:
`Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ m)` followed by `c_m` is `c_n`. -/
@[simp]
public theorem baseTransition_comp_infinitesimalBase (y : Y) {n m : ℕ} (h : n ≤ m) :
    baseTransition y h ≫ infinitesimalBase y m = infinitesimalBase y n := by
  rw [infinitesimalBase, infinitesimalBase, baseTransition, ← Category.assoc, ← Spec.map_comp,
    toStalkQuotient_comp_stalkQuotientFactor]

/-- The transition morphism of the base attached to `n ≤ n` is the identity. -/
@[simp]
public theorem baseTransition_refl (y : Y) (n : ℕ) : baseTransition y (le_refl n) = 𝟙 _ := by
  rw [baseTransition, stalkQuotientFactor_refl, Spec.map_id]

/-- The transition morphisms of the base compose: for `n ≤ m ≤ k` the composite of the
transitions for `n ≤ m` and `m ≤ k` is the transition for `n ≤ k`. -/
@[simp]
public theorem baseTransition_comp (y : Y) {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k) :
    baseTransition y h₁ ≫ baseTransition y h₂ = baseTransition y (h₁.trans h₂) := by
  rw [baseTransition, baseTransition, baseTransition, ← Spec.map_comp,
    stalkQuotientFactor_comp]

/-! ### The infinitesimal neighbourhoods and their modules -/

/-- The `n`-th infinitesimal neighbourhood `X_n = Spec (𝒪_{Y,y}/𝔪_y ^ n) ×_Y X` of the fibre of
`f : X ⟶ Y` over `y`. -/
@[stacks 02OD "the infinitesimal neighbourhoods X_n = X ×_Y Spec(𝒪_{Y,y}/𝔪ⁿ) of the fibre, \
  the setup paragraph of the tag. The conclusion -- that the completed stalk of R^p f_* ℱ at \
  y is the limit of the H^p(X_n, ℱ_n) -- is NOT asserted here: see the implementation notes \
  for its three inputs and which of them are now available"]
public abbrev infinitesimalNeighbourhood (f : X ⟶ Y) (y : Y) (n : ℕ) : Scheme.{u} :=
  pullback f (infinitesimalBase y n)

/-- The projection `i_n : X_n ⟶ X`. -/
public abbrev infinitesimalι (f : X ⟶ Y) (y : Y) (n : ℕ) :
    infinitesimalNeighbourhood f y n ⟶ X :=
  pullback.fst f (infinitesimalBase y n)

/-- The projection `f_n : X_n ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ n)`, the structure morphism of `X_n` over
the `n`-th infinitesimal neighbourhood of `y` in `Y`. -/
public abbrev infinitesimalStructure (f : X ⟶ Y) (y : Y) (n : ℕ) :
    infinitesimalNeighbourhood f y n ⟶ Spec (stalkQuotient y n) :=
  pullback.snd f (infinitesimalBase y n)

/-- The defining square of `X_n`: `i_n ≫ f = f_n ≫ c_n`. -/
public theorem infinitesimalι_comp (f : X ⟶ Y) (y : Y) (n : ℕ) :
    infinitesimalι f y n ≫ f = infinitesimalStructure f y n ≫ infinitesimalBase y n :=
  pullback.condition

/-- The restriction `ℱ_n = i_n ^* ℱ` of a sheaf of modules `ℱ` on `X` to the `n`-th
infinitesimal neighbourhood of the fibre. -/
public abbrev infinitesimalModule (f : X ⟶ Y) (F : X.Modules) (y : Y) (n : ℕ) :
    (infinitesimalNeighbourhood f y n).Modules :=
  (Scheme.Modules.pullback (infinitesimalι f y n)).obj F

/-- `ℱ_n` is quasi-coherent when `ℱ` is, by [Stacks, Tag 01BG]. -/
public instance isQuasicoherent_infinitesimalModule (f : X ⟶ Y) (F : X.Modules)
    [F.IsQuasicoherent] (y : Y) (n : ℕ) : (infinitesimalModule f F y n).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ F

/-- `ℱ_n` is coherent when `ℱ` is and `Y` is locally Noetherian, by [Stacks, Tag 0EBF] applied
to the locally Noetherian scheme `X_n`. -/
public instance isCoherent_infinitesimalModule (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (y : Y) (n : ℕ) :
    (infinitesimalModule f F y n).IsCoherent :=
  isCoherent_pullback _ F

/-! ### The transition morphisms -/

/-- The transition morphism `X_n ⟶ X_m` for `n ≤ m`, induced on fibre products by
`baseTransition`. -/
public def infinitesimalTransition (f : X ⟶ Y) (y : Y) {n m : ℕ} (h : n ≤ m) :
    infinitesimalNeighbourhood f y n ⟶ infinitesimalNeighbourhood f y m :=
  pullback.lift (infinitesimalι f y n) (infinitesimalStructure f y n ≫ baseTransition y h)
    (by rw [infinitesimalι_comp, Category.assoc, baseTransition_comp_infinitesimalBase])

/-- The transition morphism `X_n ⟶ X_m` commutes with the projections to `X`:
followed by `i_m` it is `i_n`. -/
@[reassoc (attr := simp)]
public theorem infinitesimalTransition_ι (f : X ⟶ Y) (y : Y) {n m : ℕ} (h : n ≤ m) :
    infinitesimalTransition f y h ≫ infinitesimalι f y m = infinitesimalι f y n :=
  pullback.lift_fst _ _ _

/-- The transition morphism `X_n ⟶ X_m` lies over the transition morphism of the base:
followed by `f_m` it is `f_n` followed by `Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ m)`. -/
@[reassoc (attr := simp)]
public theorem infinitesimalTransition_structure (f : X ⟶ Y) (y : Y) {n m : ℕ} (h : n ≤ m) :
    infinitesimalTransition f y h ≫ infinitesimalStructure f y m =
      infinitesimalStructure f y n ≫ baseTransition y h :=
  pullback.lift_snd _ _ _

/-- The transition morphism `X_n ⟶ X_n` attached to `n ≤ n` is the identity. -/
@[simp]
public theorem infinitesimalTransition_refl (f : X ⟶ Y) (y : Y) (n : ℕ) :
    infinitesimalTransition f y (le_refl n) = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · simp

/-- The transition morphisms of the infinitesimal neighbourhoods compose: for `n ≤ m ≤ k` the
composite `X_n ⟶ X_m ⟶ X_k` is the transition morphism `X_n ⟶ X_k`. -/
@[simp]
public theorem infinitesimalTransition_comp (f : X ⟶ Y) (y : Y) {n m k : ℕ} (h₁ : n ≤ m)
    (h₂ : m ≤ k) :
    infinitesimalTransition f y h₁ ≫ infinitesimalTransition f y h₂ =
      infinitesimalTransition f y (h₁.trans h₂) := by
  refine pullback.hom_ext ?_ ?_
  · simp
  · rw [Category.assoc, infinitesimalTransition_structure, infinitesimalTransition_structure_assoc,
      baseTransition_comp, infinitesimalTransition_structure]

/-- Pasting: a square over `f` and `b ≫ g` induces a pullback square over `b` and the pullback
of `f` along `g`, given any comparison map `t` into that pullback. -/
private theorem isPullback_of_lift_pullback {B B' P : Scheme.{u}} (f : X ⟶ Y) (g : B ⟶ Y)
    (b : B' ⟶ B) (i : P ⟶ X) (s : P ⟶ B') (hP : IsPullback i s f (b ≫ g))
    (t : P ⟶ pullback f g) (ht₁ : t ≫ pullback.fst f g = i) (ht₂ : t ≫ pullback.snd f g = s ≫ b) :
    IsPullback t s (pullback.snd f g) b :=
  IsPullback.of_right (by rwa [ht₁]) ht₂ (IsPullback.of_hasPullback f g)

/-- **`X_n` is the base change of `X_m` along `Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ m)`.**
This is the pasting of the defining square of `X_n` out of the defining square of `X_m` and the
square relating the two transition morphisms. -/
public theorem isPullback_infinitesimalTransition (f : X ⟶ Y) (y : Y) {n m : ℕ} (h : n ≤ m) :
    IsPullback (infinitesimalTransition f y h) (infinitesimalStructure f y n)
      (infinitesimalStructure f y m) (baseTransition y h) := by
  refine isPullback_of_lift_pullback f _ _ _ _ ?_ _ (infinitesimalTransition_ι f y h)
    (infinitesimalTransition_structure f y h)
  rw [baseTransition_comp_infinitesimalBase]
  exact IsPullback.of_hasPullback _ _

/-- `X_n` is a closed subscheme of `X_m` for `n ≤ m`: the transition morphism is a closed
immersion, being a base change of the closed immersion
`Spec (𝒪_{Y,y}/𝔪_y ^ n) ⟶ Spec (𝒪_{Y,y}/𝔪_y ^ m)`. -/
public instance isClosedImmersion_infinitesimalTransition (f : X ⟶ Y) (y : Y) {n m : ℕ}
    (h : n ≤ m) : IsClosedImmersion (infinitesimalTransition f y h) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_infinitesimalTransition f y h).flip inferInstance

/-- `ℱ_n` is the restriction of `ℱ_m` along the transition morphism `X_n ⟶ X_m`. This is the
compatibility that makes the modules `ℱ_n` a system over the system of schemes `X_n`. -/
public def infinitesimalModuleTransitionIso (f : X ⟶ Y) (F : X.Modules) (y : Y) {n m : ℕ}
    (h : n ≤ m) :
    (Scheme.Modules.pullback (infinitesimalTransition f y h)).obj (infinitesimalModule f F y m) ≅
      infinitesimalModule f F y n :=
  (Scheme.Modules.pullbackComp (infinitesimalTransition f y h) (infinitesimalι f y m)).app F ≪≫
    (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f y h)).app F

/-! ### The first neighbourhood is the fibre -/

/-- `𝔪_y ^ 1 = 𝔪_y`, so `𝒪_{Y,y}/𝔪_y ^ 1` is the residue field `κ(y)` of `Y` at `y`. -/
public def stalkQuotientOneIso (y : Y) : stalkQuotient y 1 ≅ Y.residueField y :=
  (Ideal.quotEquivOfEq (pow_one (stalkMaximalIdeal y))).toCommRingCatIso

/-- The quotient map `𝒪_{Y,y} ⟶ 𝒪_{Y,y}/𝔪_y ^ 1` followed by the identification with `κ(y)` is
the residue map `𝒪_{Y,y} ⟶ κ(y)`. -/
@[simp]
public theorem toStalkQuotient_comp_stalkQuotientOneIso (y : Y) :
    toStalkQuotient y 1 ≫ (stalkQuotientOneIso y).hom = Y.residue y := by
  ext x
  exact Ideal.quotEquivOfEq_mk (pow_one (stalkMaximalIdeal y)) x

/-- Under the identification `𝒪_{Y,y}/𝔪_y ^ 1 ≅ κ(y)`, the morphism `c_1` is the canonical
morphism `Spec κ(y) ⟶ Y`. -/
@[simp]
public theorem specMap_stalkQuotientOneIso_comp_infinitesimalBase (y : Y) :
    Spec.map (stalkQuotientOneIso y).hom ≫ infinitesimalBase y 1 = Y.fromSpecResidueField y := by
  rw [infinitesimalBase, ← Category.assoc, ← Spec.map_comp,
    toStalkQuotient_comp_stalkQuotientOneIso, Scheme.fromSpecResidueField]

/-- The canonical morphism from the scheme-theoretic fibre `X_y` to the first infinitesimal
neighbourhood `X_1`, induced by the identification `𝒪_{Y,y}/𝔪_y ^ 1 ≅ κ(y)` on the base. -/
public def fiberToInfinitesimalNeighbourhoodOne (f : X ⟶ Y) (y : Y) :
    f.fiber y ⟶ infinitesimalNeighbourhood f y 1 :=
  pullback.lift (f.fiberι y)
    (f.fiberToSpecResidueField y ≫ Spec.map (stalkQuotientOneIso y).hom)
    (by rw [Category.assoc, specMap_stalkQuotientOneIso_comp_infinitesimalBase,
      Scheme.Hom.fiber_fac])

/-- `X_y` is the base change of `X_1` along the isomorphism `Spec κ(y) ≅ Spec (𝒪_{Y,y}/𝔪_y ^ 1)`,
by the same pasting argument as `isPullback_infinitesimalTransition`. -/
public theorem isPullback_fiberToInfinitesimalNeighbourhoodOne (f : X ⟶ Y) (y : Y) :
    IsPullback (fiberToInfinitesimalNeighbourhoodOne f y) (f.fiberToSpecResidueField y)
      (infinitesimalStructure f y 1) (Spec.map (stalkQuotientOneIso y).hom) := by
  refine isPullback_of_lift_pullback f _ _ _ _ ?_ _ (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _)
  rw [specMap_stalkQuotientOneIso_comp_infinitesimalBase]
  exact IsPullback.of_hasPullback _ _

/-- The canonical morphism `X_y ⟶ X_1` is an isomorphism, being a base change of the
isomorphism `Spec κ(y) ≅ Spec (𝒪_{Y,y}/𝔪_y ^ 1)`. -/
public instance isIso_fiberToInfinitesimalNeighbourhoodOne (f : X ⟶ Y) (y : Y) :
    IsIso (fiberToInfinitesimalNeighbourhoodOne f y) :=
  (isPullback_fiberToInfinitesimalNeighbourhoodOne f y).isIso_fst_of_isIso

/-- **`X_1` is the fibre `X_y`.** The first infinitesimal neighbourhood of the fibre is the
scheme-theoretic fibre `f.fiber y = X ×_Y Spec κ(y)` of `f` at `y`, which is how
[Stacks, Tag 02OD] describes the start of the system. -/
public def fiberIsoInfinitesimalNeighbourhoodOne (f : X ⟶ Y) (y : Y) :
    f.fiber y ≅ infinitesimalNeighbourhood f y 1 :=
  asIso (fiberToInfinitesimalNeighbourhoodOne f y)

/-! ### The system as a diagram -/

/-- The system of infinitesimal neighbourhoods of the fibre as a functor `ℕ ⥤ Scheme`: the
object at `n` is `X_n` and the morphism attached to `n ≤ m` is the closed immersion
`X_n ⟶ X_m`. -/
public def infinitesimalDiagram (f : X ⟶ Y) (y : Y) : ℕ ⥤ Scheme.{u} where
  obj n := infinitesimalNeighbourhood f y n
  map h := infinitesimalTransition f y (leOfHom h)
  map_id n := infinitesimalTransition_refl f y n
  map_comp _ _ := (infinitesimalTransition_comp f y _ _).symm

/-- The projections `i_n : X_n ⟶ X` assemble into a cocone on the system of infinitesimal
neighbourhoods with vertex `X`. -/
public def infinitesimalCocone (f : X ⟶ Y) (y : Y) : Cocone (infinitesimalDiagram f y) where
  pt := X
  ι :=
    { app n := infinitesimalι f y n
      naturality _ _ h := by
        simp [infinitesimalDiagram] }

/-- The leg of the cocone of infinitesimal neighbourhoods at `n` is the projection
`i_n : X_n ⟶ X`. -/
@[simp]
public theorem infinitesimalCocone_ι_app (f : X ⟶ Y) (y : Y) (n : ℕ) :
    (infinitesimalCocone f y).ι.app n = infinitesimalι f y n :=
  rfl

end Stacks.FormalFunctions

end

end
