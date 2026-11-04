module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.OfScheme
public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalSheaf
public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening
public import Mathlib.Topology.Homeomorph.Lemmas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The conormal sheaf of a first-order thickening is its defining ideal

Let `i : X ⟶ X'` be a closed immersion of schemes with defining ideal sheaf `ℐ`. The conormal
sheaf of [Stacks Project, Tag 01R1] part (3) is `𝒞_{X/X'} = i^* ℐ`, and its pushforward along `i`
is `ℐ/ℐ²`; the canonical map `ℐ ⟶ i_* 𝒞_{X/X'}` is the unit of `i^* ⊣ i_*` at `ℐ`, which is
`Stacks.Immersion.canonicalConormalQuotientMap`. When `i` is a **first-order thickening** — that
is, `ℐ² = 0` — that quotient map is an isomorphism, so `i_* 𝒞_{X/X'}` *is* the ideal `ℐ` and
therefore sits inside `𝒪_{X'}`.

This file constructs that inclusion

`Stacks.Thickenings.firstOrderConormalSheafι : i_* 𝒞_{X/X'} ⟶ 𝒪_{X'}`

and proves it is a monomorphism. It is the subsheaf inclusion `𝒞_{X/X'} ⊆ 𝒪_{X'}` that the
statement of [Stacks Project, Tag 04FG] uses, before the pushforward along `a : X ⟶ Y` that puts
it on `Y`; on global sections over an affine `X'` it is the inclusion of
`RingHom.ker i.appTop.hom` used by `Stacks.Thickenings.mapDifferenceDerivation`.

The other half of the comparison the source needs — the identification of the conormal sheaf
`Stacks.Thickenings.immersionConormalSheaf i` of [Stacks Project, Tag 01R2], which is built from
the factorization of `i` over `AlgebraicGeometry.Scheme.Hom.coborderRange`, with the conormal
sheaf `Stacks.Thickenings.schemeConormalSheaf i` built from the defining ideal sheaf of `i`
itself — is **already in the library**: it is `Stacks.Immersion.conormalSheafSelfIso`, available
for every immersion and not only for a closed one. This file consumes it to produce the inclusion
out of `Stacks.Thickenings.immersionConormalSheaf i` as well; see the implementation notes for
the in-tree notes that said the identification was unavailable.

## Main definitions

* `Stacks.Thickenings.firstOrderConormalIso` is the quotient map `ℐ ⟶ i_* 𝒞_{X/X'}` of
  [Stacks Project, Tag 01R3] part (1), as an isomorphism, for a first-order thickening.
* `Stacks.Thickenings.firstOrderConormalSheafι` is the inclusion `i_* 𝒞_{X/X'} ⟶ 𝒪_{X'}`.
* `Stacks.Thickenings.firstOrderImmersionConormalSheafι` is the same inclusion with its source
  written as the conormal sheaf of [Stacks Project, Tag 01R2],
  `i_* 𝒞_{X/X'} ⟶ 𝒪_{X'}` for `𝒞_{X/X'} = Stacks.Thickenings.immersionConormalSheaf i`.

## Main results

* `Stacks.Thickenings.ker_app_sq_eq_bot`: a closed immersion with square-zero defining ideal
  sheaf has `RingHom.ker (i.app U) ^ 2 = ⊥` over **every** open `U`, not only over an affine
  one. This is the only non-formal step: the hypothesis `i.ker ^ 2 = ⊥` is a condition on affine
  opens, and the extension to an arbitrary open is a sheaf argument.
* `Stacks.Thickenings.mul_eq_zero_of_app_eq_zero_of_ker_sq_eq_bot`: the sectionwise reading of the
  same fact — two
  sections over a common open which die on the closed subscheme have vanishing product.
* `Stacks.Thickenings.isFirstOrderThickening_toShHom`: a first-order thickening of schemes
  underlies a first-order thickening of ringed spaces in the sense of
  `AlgebraicGeometry.RingedSpaceThickening.IsFirstOrderThickening`.
* `Stacks.Thickenings.isIso_unit_app_idealSheaf`: for a first-order thickening of schemes the
  quotient map `ℐ ⟶ i_* 𝒞_{X/X'}` is an isomorphism.
* `Stacks.Thickenings.unit_comp_firstOrderConormalSheafι` and
  `Stacks.Thickenings.canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι` pin
  the two inclusions down: composed with the quotient map they are the inclusion `ℐ ⟶ 𝒪_{X'}` of
  the defining ideal sheaf. A bundled morphism whose type does not mention its characterisation
  asserts nothing by itself.
* `Stacks.Thickenings.mono_firstOrderConormalSheafι` and
  `Stacks.Thickenings.mono_firstOrderImmersionConormalSheafι`: both are monomorphisms, which is
  what makes "inclusion" the right word.
* `Stacks.Thickenings.isIso_canonicalConormalQuotientMap`: for a first-order thickening the
  quotient map is an isomorphism also in the factorization-free spelling
  `Stacks.Immersion.canonicalConormalQuotientMap`, which is the form in which it can be
  cancelled against `Stacks.Immersion.canonicalConormalQuotientMap_comp_pushforward_homEquiv`.
* `Stacks.Thickenings.app_firstOrderImmersionConormalSheafι_eq_zero` and
  `Stacks.Thickenings.app_firstOrderImmersionConormalSheafι_smul`: the inclusion read on
  sections lands in the kernel of `i^♯` and is `𝒪_{X'}`-linear.

## Implementation notes

The invertibility of the quotient map is not proved here: it is
`AlgebraicGeometry.RingedSpaceThickening.isIso_unit_app_idealSheaf`, which deduces it from the
essential-image criterion of [Stacks Project, Tag 08KS] for a thickening of **ringed spaces**.
What this file supplies is the bridge from the scheme-level hypothesis to that ringed-space one.
Three of the four conditions of
`AlgebraicGeometry.RingedSpaceThickening.IsFirstOrderThickening` are immediate: the underlying
map of a first-order thickening is a surjective closed embedding, hence a homeomorphism; the
surjectivity of the comorphism is `Stacks.ClosedImmersion.epi_structureSheafModuleHom`; and local
nilpotence follows from square-zero with no shrinking of the open at all.

The fourth is `Stacks.Thickenings.ker_app_sq_eq_bot`. The scheme-level hypothesis
`i.ker ^ 2 = ⊥` is an equality of `AlgebraicGeometry.Scheme.IdealSheafData`, so by
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow` it says that the square of
`RingHom.ker (i.app V)` vanishes for every **affine** open `V`
(`AlgebraicGeometry.Scheme.Hom.ker_apply`, available because a closed immersion is quasi-compact).
The ringed-space condition quantifies over every open. The two are reconciled by the sheaf
condition: for `a, b` in the kernel over an arbitrary `U`, every point of `U` has an affine
neighbourhood `V ≤ U` (`AlgebraicGeometry.Scheme.isBasis_affineOpens`), the restrictions of `a`
and `b` lie in the kernel over `V` by naturality of `i.app`, their product vanishes there, and
`TopCat.Presheaf.IsSheaf.section_ext` concludes `a * b = 0`.

The inclusion is `(firstOrderConormalIso).inv ≫ Stacks.ClosedImmersion.idealSheafι`, so it is a
composite of two monomorphisms and the pinning lemma is the inverse-cancellation of an
isomorphism; nothing beyond that is claimed about it.

`Stacks.Thickenings.ker_app_sq_eq_bot` is stated in ideal-power form because that is the form the
ringed-space condition consumes, and
`Stacks.Thickenings.mul_eq_zero_of_app_eq_zero_of_ker_sq_eq_bot` is its
sectionwise reading, which is the form every other consumer wants. The two together are the single
home of the square-zero-over-an-arbitrary-open fact: this file sits low enough in the import order
(it needs only the defining ideal sheaf of a closed immersion, nothing about square-zero
extensions or about affineness) that the files proving [Stacks Project, Tag 05YV] and
[Stacks Project, Tag 06AD] both import it for that lemma instead of reproving it.

## Partial coverage

**No `@[stacks]` attribute is placed by this file.** What it proves is the subsheaf inclusion
`𝒞_{X/X'} ⊆ 𝒪_{X'}` that the statement of [Stacks Project, Tag 04FG] uses, not any clause of
that tag. Two files carry that attribute for the unrestricted tag, and each reads the conormal
sheaf as the defining ideal of `i` through `Stacks.Thickenings.firstOrderConormalIso`, the
isomorphism this file builds:
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDerivationGlobal.lean`, which uses
`Stacks.Thickenings.firstOrderConormalSheafι` directly, and
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDerivationSheaf.lean`, whose
`Stacks.Thickenings.firstOrderImmersionConormalSheafι_differenceDerivation_d` states it with the
reading `Stacks.Thickenings.firstOrderImmersionConormalSheafι` through the conormal sheaf of
[Stacks Project, Tag 01R2]. The note that used to stand here named two further pieces as missing
before the unrestricted statement could be made — the identification of sheaves on a first-order
thickening `X'` of `X` with sheaves on `X`, and the compatibility of module pushforward along `a`
with it — and both turned out to be needless: the inclusion built here reads a conormal section
over `a⁻¹j⁻¹V` as a section of `𝒪_{X'}` over `(a')⁻¹V` directly. Likewise nothing of
[Stacks Project, Tag 04F7] beyond what
`Stacks.Thickenings.universalConormalSheafMap` already had is proved: the identification that
tag still owed is `Stacks.Immersion.conormalSheafSelfIso`, which this file only cites.

The hypotheses carried are exactly `AlgebraicGeometry.IsClosedImmersion i` and `i.ker ^ 2 = ⊥`,
i.e. the two halves of `Stacks.Thickenings.IsFirstOrderThickening`. For a closed immersion that
is *not* first order the inclusion does not exist: `i_* 𝒞_{X/X'}` is `ℐ/ℐ²`, which receives the
quotient map `Stacks.Immersion.canonicalConormalQuotientMap` from `ℐ` but admits no canonical map
to `𝒪_{X'}`. Nothing here is stated for a general closed immersion, and the square-zero
hypothesis is not removable.

Three in-tree notes stated that the identification of the two conormal sheaves of a closed
immersion was unavailable, and all three are stale — `Stacks.Immersion.conormalSheafSelfIso`
postdates them. They are corrected in place: the implementation notes of
`StacksFrontier/AlgebraicGeometry/Thickenings/UniversalConormalSheaf.lean`, those of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDerivation.lean` and those of
`StacksFrontier/AlgebraicGeometry/Conormal/FirstOrderThickening.lean`.

## References

* [Stacks Project, Tag 01R1](https://stacks.math.columbia.edu/tag/01R1)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 08KZ](https://stacks.math.columbia.edu/tag/08KZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction 
open Stacks.Thickenings

universe u

namespace Stacks.Thickenings

variable {X X' : Scheme.{u}} (i : X ⟶ X')

/-! ### Square-zero over an arbitrary open -/

/-- **The defining ideal of a first-order thickening is square-zero over every open.** The
hypothesis `i.ker ^ 2 = ⊥` is an equality of `AlgebraicGeometry.Scheme.IdealSheafData`, hence a
statement about affine opens; this is the same statement over an arbitrary open `U`.

Every point of `U` has an affine neighbourhood `V ≤ U`, the restrictions to `V` of two sections
of the kernel over `U` are again in the kernel, and there their product vanishes, so the product
vanishes over `U` by the sheaf condition. -/
theorem ker_app_sq_eq_bot [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
    (U : X'.Opens) : RingHom.ker (i.app U).hom ^ 2 = ⊥ := by
  rw [pow_two]
  refine le_antisymm (Ideal.mul_le.mpr fun a ha b hb => Ideal.mem_bot.mpr ?_) bot_le
  refine TopCat.Presheaf.IsSheaf.section_ext (F := X'.presheaf) X'.sheaf.property
    (U := op U) (s := a * b) (t := 0) ?_
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  refine ⟨V, hVU, hxV, ?_⟩
  have hres : ∀ c : Γ(X', U), c ∈ RingHom.ker (i.app U).hom →
      (X'.presheaf.map (homOfLE hVU).op).hom c ∈ RingHom.ker (i.app V).hom := by
    intro c hc
    have hnat := Scheme.Hom.naturality i (U := V) (U' := U) (homOfLE hVU).op
    have h2 := congrArg (fun g : Γ(X', U) ⟶ Γ(X, i ⁻¹ᵁ V) => g.hom c) hnat
    simp only [CommRingCat.comp_apply] at h2
    have hc0 : (i.app U).hom c = 0 := hc
    have h3 : (i.app V).hom ((X'.presheaf.map (homOfLE hVU).op).hom c) = 0 := by
      rw [h2, hc0, map_zero]
    exact h3
  have hker : RingHom.ker (i.app V).hom = i.ker.ideal ⟨V, hV⟩ :=
    (Scheme.Hom.ker_apply i ⟨V, hV⟩).symm
  have hsq2 : i.ker.ideal ⟨V, hV⟩ ^ 2 = ⊥ :=
    congrArg (fun K : Scheme.IdealSheafData X' => K.ideal ⟨V, hV⟩) hsq
  have hzero : (X'.presheaf.map (homOfLE hVU).op).hom a *
      (X'.presheaf.map (homOfLE hVU).op).hom b = 0 := by
    have hm : (X'.presheaf.map (homOfLE hVU).op).hom a *
        (X'.presheaf.map (homOfLE hVU).op).hom b ∈
          i.ker.ideal ⟨V, hV⟩ * i.ker.ideal ⟨V, hV⟩ :=
      Ideal.mul_mem_mul (hker ▸ hres a ha) (hker ▸ hres b hb)
    rw [← pow_two, hsq2] at hm
    exact Ideal.mem_bot.mp hm
  rw [map_mul, map_zero]
  exact hzero

/-- **Two sections dying on the closed subscheme of a first-order thickening have vanishing
product**, over an arbitrary open. This is the sectionwise reading of
`Stacks.Thickenings.ker_app_sq_eq_bot`, and the arbitrary-open form of
`Stacks.Thickenings.mul_eq_zero_of_mem_ker_appTop`, which is stated over `⊤` for an affine
ambient scheme. -/
theorem mul_eq_zero_of_app_eq_zero_of_ker_sq_eq_bot [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) (U : X'.Opens) (a b : Γ(X', U))
    (ha : i.app U a = 0) (hb : i.app U b = 0) :
    a * b = 0 := by
  have hm : a * b ∈ RingHom.ker (i.app U).hom ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul (RingHom.mem_ker.mpr ha) (RingHom.mem_ker.mpr hb)
  rw [ker_app_sq_eq_bot i hsq U] at hm
  exact Ideal.mem_bot.mp hm

/-! ### The underlying thickening of ringed spaces -/

/-- The kernel of the structure-sheaf map of a closed immersion with square-zero defining ideal
sheaf is locally nilpotent: a kernel section squares to zero already on the open it is given on,
by `Stacks.Thickenings.mul_eq_zero_of_app_eq_zero_of_ker_sq_eq_bot`, so no shrinking is needed. -/
theorem hasLocallyNilpotentKernel_toShHom [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) :
    RingedSpaceThickening.HasLocallyNilpotentKernel i.toLRSHom.toShHom := by
  intro U a ha x hx
  refine ⟨U, le_rfl, hx, 2, ?_⟩
  have hmem : a ∈ RingHom.ker (i.app U).hom := ha
  have h2 : a * a = 0 :=
    mul_eq_zero_of_app_eq_zero_of_ker_sq_eq_bot i hsq U a a (RingHom.mem_ker.mp hmem)
      (RingHom.mem_ker.mp hmem)
  have hone : (structureSheafRing X'.toSheafedSpace).obj.map
      (homOfLE (le_refl U)).op a = a := by
    rw [show (homOfLE (le_refl U)) = 𝟙 U from rfl, op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [hone, pow_two]
  exact h2

/-- **A first-order thickening of schemes underlies a first-order thickening of ringed spaces.**
The underlying map is a surjective closed embedding, hence a homeomorphism; the comorphism is an
epimorphism of sheaves of modules by `Stacks.ClosedImmersion.epi_structureSheafModuleHom`; local
nilpotence is `Stacks.Thickenings.hasLocallyNilpotentKernel_toShHom`; and the square-zero
condition over an arbitrary open is `Stacks.Thickenings.ker_app_sq_eq_bot`.

This is the hypothesis that `AlgebraicGeometry.RingedSpaceThickening.isIso_unit_app_idealSheaf`
consumes. -/
@[ega "IV 16.5.14" "partial"]
theorem isFirstOrderThickening_toShHom [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) :
    RingedSpaceThickening.IsFirstOrderThickening i.toLRSHom.toShHom := by
  refine ⟨⟨?_, Stacks.ClosedImmersion.epi_structureSheafModuleHom i,
    hasLocallyNilpotentKernel_toShHom i hsq⟩, fun U => ker_app_sq_eq_bot i hsq U⟩
  have hs : Function.Surjective i :=
    (Stacks.Thickenings.isThickening_of_ker_pow_eq_bot i inferInstance
      (n := 1) (by simpa using hsq)).2
  rw [TopCat.isIso_iff_isHomeomorph]
  exact isHomeomorph_iff_isEmbedding_surjective.2
    ⟨(AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding i).isEmbedding, hs⟩

/-! ### The conormal sheaf of a first-order thickening is the defining ideal -/

/-- **The quotient map `ℐ ⟶ i_* 𝒞_{X/X'}` of a first-order thickening is an isomorphism.** The
map is the unit of `i^* ⊣ i_*` at the defining ideal sheaf, which is what
`Stacks.Immersion.canonicalConormalQuotientMap` is built from; for a square-zero ideal
`ℐ/ℐ² = ℐ`, so it is invertible.

This is `AlgebraicGeometry.RingedSpaceThickening.isIso_unit_app_idealSheaf` — a consequence of
the essential-image criterion of [Stacks Project, Tag 08KS] — transported along
`Stacks.Thickenings.isFirstOrderThickening_toShHom`. -/
theorem isIso_unit_app_idealSheaf [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) :
    IsIso ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)) :=
  RingedSpaceThickening.isIso_unit_app_idealSheaf i.toLRSHom.toShHom
    (isFirstOrderThickening_toShHom i hsq)

/-- **The defining ideal sheaf of a first-order thickening is its pushed-forward conormal
sheaf**, `ℐ ≅ i_* 𝒞_{X/X'}`. The underlying morphism is the quotient map of
[Stacks Project, Tag 01R3] part (1), the unit of `i^* ⊣ i_*` at `ℐ`; it is an isomorphism by
`Stacks.Thickenings.isIso_unit_app_idealSheaf`. -/
def firstOrderConormalIso [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) :
    Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom ≅
      (modulePushforward i.toLRSHom.toShHom).obj (schemeConormalSheaf i) :=
  let := isIso_unit_app_idealSheaf i hsq
  asIso ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
    (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom))

/-- The underlying morphism of `Stacks.Thickenings.firstOrderConormalIso` is the unit of
`i^* ⊣ i_*` at the defining ideal sheaf. -/
@[simp]
theorem firstOrderConormalIso_hom [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) :
    (firstOrderConormalIso i hsq).hom =
      (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) :=
  rfl

/-- **The inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` of the conormal sheaf of a first-order thickening into
the structure sheaf of the ambient scheme**, read on `X'` — that is, the conormal sheaf pushed
forward along `i`, which for a thickening is no loss of information since `i` is a homeomorphism.

It is `Stacks.Thickenings.firstOrderConormalIso` inverted, followed by the inclusion
`Stacks.ClosedImmersion.idealSheafι` of the defining ideal sheaf into `𝒪_{X'}`. It is pinned by
`Stacks.Thickenings.unit_comp_firstOrderConormalSheafι` and is a monomorphism by
`Stacks.Thickenings.mono_firstOrderConormalSheafι`.

This is the subsheaf inclusion `𝒞_{X/X'} ⊆ 𝒪_{X'}` appearing in [Stacks Project, Tag 04FG]. -/
def firstOrderConormalSheafι [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) :
    (modulePushforward i.toLRSHom.toShHom).obj (schemeConormalSheaf i) ⟶
      SheafOfModules.unit
        (structureSheafRing X'.toLocallyRingedSpace.toRingedSpace) :=
  (firstOrderConormalIso i hsq).inv ≫ Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom

/-- **The characterising property of `Stacks.Thickenings.firstOrderConormalSheafι`.** Precomposed
with the quotient map `ℐ ⟶ i_* 𝒞_{X/X'}` — the unit of `i^* ⊣ i_*` at `ℐ` — it is the inclusion
`ℐ ⟶ 𝒪_{X'}` of the defining ideal sheaf.

Since that quotient map is an isomorphism, this determines the inclusion uniquely. -/
@[simp]
theorem unit_comp_firstOrderConormalSheafι [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) :
    (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
          (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) ≫
        firstOrderConormalSheafι i hsq =
      Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom := by
  rw [← firstOrderConormalIso_hom i hsq]
  exact (firstOrderConormalIso i hsq).hom_inv_id_assoc _

/-- **The inclusion of the conormal sheaf of a first-order thickening is a monomorphism**, so it
really does exhibit `𝒞_{X/X'}` as a subsheaf of `𝒪_{X'}`: it is an isomorphism followed by the
inclusion of a kernel. -/
theorem mono_firstOrderConormalSheafι [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) : Mono (firstOrderConormalSheafι i hsq) := by
  have : Mono (Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom) :=
    inferInstanceAs (Mono (kernel.ι (structureSheafModuleHom i.toLRSHom.toShHom)))
  exact mono_comp (firstOrderConormalIso i hsq).inv _

/-! ### The same inclusion for the conormal sheaf of Tag 01R2 -/

/-- **The inclusion `𝒞_{X/X'} ⟶ 𝒪_{X'}` with its source the conormal sheaf of
[Stacks Project, Tag 01R2].** `Stacks.Thickenings.immersionConormalSheaf i` is built from the
factorization of `i` over `AlgebraicGeometry.Scheme.Hom.coborderRange`;
`Stacks.Immersion.conormalSheafSelfIso` identifies it with
`Stacks.Thickenings.schemeConormalSheaf i`, built from the defining ideal sheaf of `i` itself,
and this is `Stacks.Thickenings.firstOrderConormalSheafι` read through that identification. -/
def firstOrderImmersionConormalSheafι [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) :
    (modulePushforward i.toLRSHom.toShHom).obj (immersionConormalSheaf i) ⟶
      SheafOfModules.unit
        (structureSheafRing X'.toLocallyRingedSpace.toRingedSpace) :=
  (modulePushforward i.toLRSHom.toShHom).map (Stacks.Immersion.conormalSheafSelfIso i).inv ≫
    firstOrderConormalSheafι i hsq

/-- The quotient map `canonicalConormalQuotientMap` is the unit of `i^* ⊣ i_*` at the defining
ideal sheaf followed by the pushforward of `conormalSheafSelfIso`. -/
private theorem canonicalConormalQuotientMap_eq [AlgebraicGeometry.IsClosedImmersion i] :
    Stacks.Immersion.canonicalConormalQuotientMap i =
      (modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
          (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) ≫
        (modulePushforward i.toLRSHom.toShHom).map
          (Stacks.Immersion.conormalSheafSelfIso i).hom := rfl

/-- **The characterising property of `Stacks.Thickenings.firstOrderImmersionConormalSheafι`.**
Precomposed with the quotient map `ℐ ⟶ i_* 𝒞_{X/X'}` of
`Stacks.Immersion.canonicalConormalQuotientMap` — the unit of `i^* ⊣ i_*` at `ℐ` followed by the
pushforward of `Stacks.Immersion.conormalSheafSelfIso` — it is the inclusion `ℐ ⟶ 𝒪_{X'}` of the
defining ideal sheaf. -/
@[simp]
theorem canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι
    [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) :
    Stacks.Immersion.canonicalConormalQuotientMap i ≫ firstOrderImmersionConormalSheafι i hsq =
      Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom := by
  have hdef : firstOrderImmersionConormalSheafι i hsq =
      (modulePushforward i.toLRSHom.toShHom).map
          (Stacks.Immersion.conormalSheafSelfIso i).inv ≫
        firstOrderConormalSheafι i hsq := rfl
  rw [canonicalConormalQuotientMap_eq, hdef, Category.assoc,
    ← Category.assoc ((modulePushforward i.toLRSHom.toShHom).map _), ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    unit_comp_firstOrderConormalSheafι]

/-- `Stacks.Thickenings.firstOrderImmersionConormalSheafι` is a monomorphism: it is the
pushforward of an isomorphism followed by
`Stacks.Thickenings.firstOrderConormalSheafι`, itself a monomorphism. -/
theorem mono_firstOrderImmersionConormalSheafι [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) : Mono (firstOrderImmersionConormalSheafι i hsq) := by
  have := mono_firstOrderConormalSheafι i hsq
  exact mono_comp ((modulePushforward i.toLRSHom.toShHom).map
    (Stacks.Immersion.conormalSheafSelfIso i).inv) _

/-- **The quotient map `ℐ ⟶ i_* 𝒞_{X/X'}` of [Stacks Project, Tag 01R3] is an isomorphism for a
first-order thickening**, in the factorization-free spelling
`Stacks.Immersion.canonicalConormalQuotientMap`. That map is the unit of `i^* ⊣ i_*` at `ℐ`,
invertible by `Stacks.Thickenings.isIso_unit_app_idealSheaf`, followed by the pushforward of the
isomorphism `Stacks.Immersion.conormalSheafSelfIso`. -/
theorem isIso_canonicalConormalQuotientMap [AlgebraicGeometry.IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) : IsIso (Stacks.Immersion.canonicalConormalQuotientMap i) := by
  have := isIso_unit_app_idealSheaf i hsq
  rw [canonicalConormalQuotientMap_eq]
  infer_instance

/-! ### The inclusion on sections lands in the defining ideal -/

/-- **A section of the conormal sheaf of a first-order thickening is killed by the comorphism of
`i`.** The inclusion `Stacks.Thickenings.firstOrderImmersionConormalSheafι` factors through the
inclusion of the defining ideal sheaf, whose sections over `V` are exactly the kernel of
`Γ(X', V) ⟶ Γ(X, i⁻¹V)` by `Stacks.ClosedImmersion.range_idealSheafι_val_app`. -/
theorem app_firstOrderImmersionConormalSheafι_eq_zero
    [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) (V : X'.Opens)
    (m : ((modulePushforward i.toLRSHom.toShHom).obj (immersionConormalSheaf i)).val.obj
      (op V)) :
    (i.app V).hom ((firstOrderImmersionConormalSheafι i hsq).val.app (op V) m) = 0 := by
  have hmem : (firstOrderImmersionConormalSheafι i hsq).val.app (op V) m ∈
      LinearMap.range
        ((Stacks.ClosedImmersion.idealSheafι i.toLRSHom.toShHom).val.app (op V)).hom :=
    ⟨(((modulePushforward i.toLRSHom.toShHom).map
        (Stacks.Immersion.conormalSheafSelfIso i).inv ≫
      (firstOrderConormalIso i hsq).inv)).val.app (op V) m, rfl⟩
  rw [Stacks.ClosedImmersion.range_idealSheafι_val_app] at hmem
  exact RingHom.mem_ker.mp hmem

/-- **`Stacks.Thickenings.firstOrderImmersionConormalSheafι` is `𝒪_{X'}`-linear on sections.**
The scalars of the pushed-forward conormal sheaf over `V` are `Γ(X', V)` acting through `i^♯`,
and the action on the structure sheaf is multiplication, so this is its `map_smul`. -/
theorem app_firstOrderImmersionConormalSheafι_smul
    [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥) (V : X'.Opens)
    (ρ : Γ(X', V))
    (m : ((modulePushforward i.toLRSHom.toShHom).obj (immersionConormalSheaf i)).val.obj
      (op V)) :
    (firstOrderImmersionConormalSheafι i hsq).val.app (op V) (ρ • m) =
      ρ • (firstOrderImmersionConormalSheafι i hsq).val.app (op V) m :=
  map_smul ((firstOrderImmersionConormalSheafι i hsq).val.app (op V)).hom ρ m

end Stacks.Thickenings

end
