module

public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.VanishingToConnected
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.ModelTransportVanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRing
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality

/-!
# `Γ(X, 𝒪_X) = A` on the blowup of a regular local surface, and the first inequality of Tag 0AGT

Let `(A, 𝔪)` be a regular local ring of dimension two and let `b : X ⟶ Spec A` be the blowup of
`Spec A` in `𝔪`. This file supplies the two things the first inequality of [Stacks, Tag 0AGT]
clause (3) was waiting on:

* **`Γ(X, 𝒪_X) = A`**: the structure morphism of the blowup induces an isomorphism on global
  functions. This is the input recorded as missing in the docstring of
  `Stacks.Blowup.Colength.surjective_appTop_comap_ofIdealTop_blowUp`, which starts the surjection
  of clause (3) at `Γ(X, 𝒪_X)` rather than at `A`.
* **the non-strict first inequality**
  `length_A Γ(X, 𝒪_X/I·𝒪_X) ≤ length_A (A/I)`, for any ideal `I` of `A`.

## Main results

* `AlgebraicGeometry.isIso_appTop_blowUpToBase_maximalIdeal` — **`Γ(X, 𝒪_X) = A`.** For `A` a
  regular local ring with `ringKrullDim A = 2`, the map of global functions along the blowup at
  the closed point is an isomorphism of rings.
* `AlgebraicGeometry.surjective_appTop_blowUpToBase_maximalIdeal` — the same read as a surjection
  of functions, which is the form the length argument consumes.
* `Stacks.Divisors.length_globalSections_subscheme_le_of_surjective` — **the length inequality,
  in general and on variables.** For `f : X ⟶ Y` with `Y` affine, `J` an ideal of `Γ(Y, 𝒪_Y)` and
  `Z ⊆ X` the closed subscheme cut out by the inverse image `J·𝒪_X`: if `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`
  and `Γ(X, 𝒪_X) ⟶ Γ(Z, 𝒪_Z)` are both surjective then
  `length Γ(Z, 𝒪_Z) ≤ length (Γ(Y, 𝒪_Y)/J)` over `Γ(Y, 𝒪_Y)`.
* `Stacks.Blowup.Colength.length_globalSections_comap_ofIdealTop_blowUp_le` — **the first
  inequality of [Stacks, Tag 0AGT] clause (3), without the strictness**, obtained by discharging
  both hypotheses of the previous result on the blowup of a regular local surface.

## Why `Γ(X, 𝒪_X) = A` is not new mathematics here

It is two existing results composed. `AlgebraicGeometry.IsModification.isIso_appTop` says that a
*modification* of the spectrum of a normal domain — a proper birational morphism with integral
source, [Stacks, Tag 0AAZ] — has no new global functions, and
`AlgebraicGeometry.isModification_blowUpToBase_maximalIdeal` says the blowup of a
two-dimensional local Noetherian domain at its maximal ideal is one. A regular local ring is a
normal domain (`AlgebraicGeometry.isNormalDomain_of_isRegularLocalRing`), which supplies the
remaining hypothesis and, with it, `IsDomain` and `IsNoetherianRing`.

The general statement and its instance at this blowup are in the library, outside the `Blowup/`
and `ResolutionOfSurfaces/` trees, under `appTop` names that do not mention a blowup.

## Implementation notes

**The sections of `𝒪_X/J·𝒪_X` are read on the closed subscheme, and the quotient map is a ring
map.** The third term of [Stacks, Tag 0C6K] is `i_*𝒪_Z` for `i : Z ⟶ X` the inclusion, and
sections of a direct image over the whole target are the sections of the source, so the
component of `Stacks.IdealSheafSequence.divisorQuotientMap` over `⊤` *is* the ring map
`Scheme.Hom.appTop` of `i` — by `rfl`, which is
`Stacks.AmpleSectionConnected.secF_map_divisorQuotientMap_apply`. The whole first inequality is
therefore a statement about a composite of two surjective ring maps
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X) ⟶ Γ(Z, 𝒪_Z)` and needs no module-level bookkeeping.

**That the composite kills `J`** is the unit of the adjunction between inverse and direct image
of ideal sheaves: `Scheme.IdealSheafData.le_map_comap` gives
`J·𝒪_Y ≤ (J·𝒪_X).map f`, the right-hand side is by definition the kernel ideal sheaf of
`i ≫ f`, and `Scheme.Hom.ideal_ker_le` evaluates that kernel at the affine open `⊤` of `Y`. No
quasi-compactness is needed: only the easy half of `Scheme.Hom.ker_apply` is used.

**The length is taken over `Γ(Y, 𝒪_Y)`.** For `Y = Spec A` that ring is `A` under the canonical
identification `AlgebraicGeometry.Scheme.ΓSpecIso`, which is the spelling in which the ideal of
the source's statement already lives in this development (see
`Stacks.Blowup.Colength.surjective_appTop_comap_ofIdealTop_blowUp`). The module structure on the
sections of the subscheme is restriction of scalars along the composite ring map, written with
`Module.compHom` as elsewhere in this development
(`AlgebraicGeometry.length_globalSections_eq_sum_length_stalk`).

The blowup, its structure morphism and `Spec` are written with their `AlgebraicGeometry.`
prefixes throughout: the namespace `Stacks.Blowup` carries a second blowup
`Stacks.Blowup.blowUp` with its own `blowUpToBase` and `exceptionalIdeal`, and inside
`Stacks.Blowup.Colength` the bare names resolve to those.

## What the *strict* inequality still waits on

One thing, and it is the only one left. The source's chain is

`length_A(A/I) ≥ length_A Γ(X, 𝒪_X/I·𝒪_X) > length_A Γ(X, E^d/I·𝒪_X) = length_A Γ(X, 𝒪_X/ℐ')`.

This file supplies the first step. The second step's content — that the global sections of
`E^d/I·𝒪_X` are a *proper* subgroup of those of `𝒪_X/I·𝒪_X` — is
`Stacks.Blowup.Colength.notMem_range_residualSections`; turning it into a strict inequality of
lengths needs that subgroup to be a submodule over the base ring and the ambient module to have
finite length, the latter from `𝔪ⁿ ⊆ I` through the inequality proved here. The third step,
`Γ(X, E^d/I·𝒪_X) = Γ(X, 𝒪_X/ℐ')`, is untouched; its ingredients are recorded in the module
docstring of `StacksFrontier/AlgebraicGeometry/Blowup/Colength/StrictColength.lean`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AAZ](https://stacks.math.columbia.edu/tag/0AAZ)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **`Γ(X, 𝒪_X) = A` for the blowup of a regular local surface at its closed point.** For
`(A, 𝔪)` a regular local ring with `ringKrullDim A = 2` and `b : X ⟶ Spec A` the blowup of
`Spec A` in `𝔪`, the ring map `b^♯ : Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)` is an isomorphism.

The blowup is a modification of `Spec A` — proper, birational, with integral source, by
`AlgebraicGeometry.isModification_blowUpToBase_maximalIdeal` — and a modification of the
spectrum of a normal domain has no new global functions, by
`AlgebraicGeometry.IsModification.isIso_appTop`. A regular local ring is a normal domain. -/
public theorem isIso_appTop_blowUpToBase_maximalIdeal (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    IsIso ((AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        (IsLocalRing.maximalIdeal A)))).appTop) :=
  let := isNormalDomain_of_isRegularLocalRing A
  (isModification_blowUpToBase_maximalIdeal A hdim).isIso_appTop

/-- **Every global function on the blowup of a regular local surface comes from the base.** The
function form of `AlgebraicGeometry.isIso_appTop_blowUpToBase_maximalIdeal`: an isomorphism of
`CommRingCat` is bijective on elements. -/
public theorem surjective_appTop_blowUpToBase_maximalIdeal (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    Function.Surjective ((AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        (IsLocalRing.maximalIdeal A)))).appTop).hom :=
  have := isIso_appTop_blowUpToBase_maximalIdeal A hdim
  (ConcreteCategory.bijective_of_isIso _).2

end AlgebraicGeometry

namespace Stacks.Divisors

/-- **The colength of the inverse image of an ideal is at most the colength of the ideal.** Let
`f : X ⟶ Y` be a morphism of schemes with `Y` affine, let `J` be an ideal of `Γ(Y, 𝒪_Y)` and let
`Z ⊆ X` be the closed subscheme cut out by the inverse-image ideal sheaf `J·𝒪_X`. If `f` induces
a surjection on global functions and so does the inclusion `Z ⟶ X`, then

`length Γ(Z, 𝒪_Z) ≤ length (Γ(Y, 𝒪_Y)/J)`

over `Γ(Y, 𝒪_Y)`, the sections of `𝒪_Z` carrying the module structure restricted along the
composite ring map.

Both surjectivity hypotheses are genuinely needed and neither is automatic: the first is
`Γ(X, 𝒪_X) = Γ(Y, 𝒪_Y)`, the second is the vanishing of `H¹(X, J·𝒪_X)`.

Stated on variables `f`, `J` so that the unifier never meets a blowup written out as a relative
`Proj`; see the implementation notes of the module. -/
public theorem length_globalSections_subscheme_le_of_surjective {Y : Scheme.{u}} [IsAffine Y]
    (J : Ideal Γ(Y, ⊤)) {X : Scheme.{u}} (f : X ⟶ Y)
    (hf : Function.Surjective (f.appTop).hom)
    (hZ : Function.Surjective
      (((Scheme.IdealSheafData.ofIdealTop J).comap f).subschemeι.appTop).hom) :
    letI : Module ↑Γ(Y, ⊤) ↑Γ(((Scheme.IdealSheafData.ofIdealTop J).comap f).subscheme, ⊤) :=
      Module.compHom _
        ((((Scheme.IdealSheafData.ofIdealTop J).comap f).subschemeι ≫ f).appTop).hom
    Module.length ↑Γ(Y, ⊤)
        ↑Γ(((Scheme.IdealSheafData.ofIdealTop J).comap f).subscheme, ⊤) ≤
      Module.length ↑Γ(Y, ⊤) (↑Γ(Y, ⊤) ⧸ J) := by
  set D := (Scheme.IdealSheafData.ofIdealTop J).comap f with hD
  set φ := ((D.subschemeι ≫ f).appTop).hom with hφ
  let : Module ↑Γ(Y, ⊤) ↑Γ(D.subscheme, ⊤) := Module.compHom _ φ
  have hφsurj : Function.Surjective φ := by
    rw [hφ, Scheme.Hom.appTop, Scheme.Hom.comp_app]
    exact hZ.comp hf
  have hker : J ≤ RingHom.ker φ := by
    intro x hx
    have h1 := Scheme.IdealSheafData.le_map_comap
      (J := Scheme.IdealSheafData.ofIdealTop J) (f := f) ⟨⊤, isAffineOpen_top Y⟩
    have h2 := Scheme.Hom.ideal_ker_le (D.subschemeι ≫ f) ⟨⊤, isAffineOpen_top Y⟩
    refine h2 (h1 ?_)
    simpa [Scheme.IdealSheafData.ofIdealTop_ideal] using hx
  let ψ : ↑Γ(Y, ⊤) →ₗ[↑Γ(Y, ⊤)] ↑Γ(D.subscheme, ⊤) :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun r x => φ.map_mul r x }
  exact Module.length_le_of_surjective (J.liftQ ψ hker) fun z =>
    (hφsurj z).elim fun r hr => ⟨J.mkQ r, hr⟩

end Stacks.Divisors

namespace Stacks.Blowup.Colength

/-- **The first inequality of [Stacks, Tag 0AGT] clause (3), without the strictness.** For
`(A, 𝔪)` a regular local ring with `ringKrullDim A = 2`, `b : X ⟶ Spec A` the blowup of `Spec A`
in `𝔪`, `I` an ideal of `Γ(Spec A, 𝒪)` and `Z ⊆ X` the closed subscheme cut out by `I·𝒪_X`,

`length Γ(X, 𝒪_X/I·𝒪_X) ≤ length (Γ(Spec A, 𝒪)/I)`.

Unconditional beyond the two hypotheses the source already grants on `A`; in particular the
source's `𝔪ⁿ ⊆ I ⊆ 𝔪` is not used, so the bound holds for every ideal.

The two inputs of `Stacks.Divisors.length_globalSections_subscheme_le_of_surjective` are
`AlgebraicGeometry.surjective_appTop_blowUpToBase_maximalIdeal` — `Γ(X, 𝒪_X) = A` — and
`Stacks.Blowup.Colength.surjective_appTop_comap_ofIdealTop_blowUp`, which is the vanishing
`H¹(X, I·𝒪_X) = 0` read on sections. The source's strict inequality needs this bound together
with `Stacks.Blowup.Colength.notMem_range_residualSections`; see the module docstring. -/
public theorem length_globalSections_comap_ofIdealTop_blowUp_le (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2)
    (I : Ideal Γ(Spec (CommRingCat.of A), ⊤)) :
    letI : Module ↑Γ(Spec (CommRingCat.of A), ⊤)
        ↑Γ(((Scheme.IdealSheafData.ofIdealTop I).comap
          (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
            (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
              (IsLocalRing.maximalIdeal A))))).subscheme, ⊤) :=
      Module.compHom _ ((((Scheme.IdealSheafData.ofIdealTop I).comap
        (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
            (IsLocalRing.maximalIdeal A))))).subschemeι ≫
        AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
            (IsLocalRing.maximalIdeal A)))).appTop).hom
    Module.length ↑Γ(Spec (CommRingCat.of A), ⊤)
        ↑Γ(((Scheme.IdealSheafData.ofIdealTop I).comap
          (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
            (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
              (IsLocalRing.maximalIdeal A))))).subscheme, ⊤) ≤
      Module.length ↑Γ(Spec (CommRingCat.of A), ⊤)
        (↑Γ(Spec (CommRingCat.of A), ⊤) ⧸ I) :=
  Stacks.Divisors.length_globalSections_subscheme_le_of_surjective I _
    (AlgebraicGeometry.surjective_appTop_blowUpToBase_maximalIdeal A hdim)
    (surjective_appTop_comap_ofIdealTop_blowUp A hdim I)

end Stacks.Blowup.Colength

end
