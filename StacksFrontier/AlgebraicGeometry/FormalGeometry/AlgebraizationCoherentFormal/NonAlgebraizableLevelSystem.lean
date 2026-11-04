module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableLevelEpi
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.NonAlgebraizableLevelSubscheme
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.QuotientFromAffineKernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated

/-!
# The system `(𝓛ₙ)` of the non-algebraizable example is coherent and annihilated

For `A = k[x,y][[t]]`, `I = (t)` and `U` the punctured spectrum of `A`, the family `(𝓛ₙ)` of
[Stacks, Tag 0EHE] is available as a diagram `ℕᵒᵖ ⥤ U.Modules`
(`Stacks.Algebraization.NonAlgebraizableExample.levelSystem`) whose transition maps are
epimorphisms. Membership of that diagram in `Coh(U, I𝒪_U)` is reduced by
`Stacks.Algebraization.isCoherentAdicSystem_of_basis_ker` to four pieces of affine-local data: a
basis `S` of affine opens, coherence of each term, annihilation of the `n`-th term by
`(I𝒪_U) ^ (n + 1)`, and a computation of the kernel of each transition map over the members of
`S`. This file supplies the first three; the kernel computation is
`Stacks.Algebraization.NonAlgebraizableExample.ker_app_levelSystem_map_succ`, in the module
`NonAlgebraizableLevelKernel` of this directory, where the four are assembled.

The whole content is that the level scheme over `U` *is* the closed subscheme of `U` cut out by
`(I𝒪_U) ^ n`, in kernel-ideal form:
`Stacks.Algebraization.NonAlgebraizableExample.ker_levelStructureMap`. Coherence is then the
direct image of a coherent module along a finite morphism ([Stacks, Tag 01Y6]) and annihilation
is the direct image along a closed immersion being killed by the ideal cutting it out
([Stacks, Tag 08KS]); neither needs the two-chart description of `𝓛ₙ`.

## Main definitions

* `Stacks.Algebraization.NonAlgebraizableExample.ambientBasicAffineOpens` — the family `S` of
  affine opens of `U` used as a basis: the basic opens `D(hg)` of `Spec(A)` with `g` one of
  `x`, `y`, `t`.

## Main results

* `Stacks.Algebraization.NonAlgebraizableExample.isClosedImmersion_levelStructureMap` — the
  structure map `Spec(A/tⁿA) ∩ U ⟶ U` is a closed immersion.
* `Stacks.Algebraization.NonAlgebraizableExample.ker_levelStructureMap` — its kernel ideal sheaf
  is `(I𝒪_U) ^ n`, so the level scheme over `U` is the `n`-th infinitesimal neighbourhood.
* `Stacks.Algebraization.NonAlgebraizableExample.isCoherent_levelSystem_obj` — the terms of the
  system are coherent. This is the hypothesis `hcoh` of
  `Stacks.Algebraization.isCoherentAdicSystem_of_basis_ker`.
* `Stacks.Algebraization.NonAlgebraizableExample.idealPowerMultiple_levelSystem_obj_eq_bot` — the
  `n`-th term is annihilated by `(I𝒪_U) ^ (n + 1)`. This is the hypothesis `hann`.
* `Stacks.Algebraization.NonAlgebraizableExample.exists_mem_ambientBasicAffineOpens` — the family
  `S` is a basis of the topology of `U`. This is the hypothesis `hS`.

## Implementation notes

`ker_levelStructureMap` is read off
`Stacks.Algebraization.NonAlgebraizableExample.exists_subschemeIso_levelOpen`, which identifies
the subscheme of `(I𝒪_U) ^ n` with the punctured spectrum of `A/tⁿA` *compatibly with the two
morphisms to `U`*: the kernel ideal sheaf of a morphism is unchanged by precomposition with an
isomorphism (`AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso`) and the kernel of a
`subschemeι` is the ideal it was cut out by
(`AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι`). No ideal is computed on an affine
open along the way.

Coherence is stated at the root `SheafOfModules.IsCoherent`, which is the class
`Stacks.Coherent.IsCoherentAdicSystem` asks for — the name `SheafOfModules.IsCoherent` written
inside a `Stacks` namespace resolves to it, not to `Stacks.SheafOfModules.IsCoherent`, and the
spelling is made explicit here so that the two are not confused. `𝓛ₙ` is coherent because it is
invertible on a locally Noetherian scheme
(`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible`, [Stacks, Tag 01XZ]),
and its direct image is coherent by [Stacks, Tag 01Y6]
(`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`, a
closed immersion being finite); both are at that class, so no bridge is needed. Invertibility is
passed with `@` because `Stacks.Ample.IsInvertibleModule` presents the structure sheaf as
`Scheme.presheaf` where `isCoherent_of_isInvertible` presents it as `Scheme.sheaf.obj`; the two
are definitionally equal but neither instance is found from the other.

Annihilation goes through `Stacks.ClosedImmersion.AnnihilatedByKer`: a direct image along a
closed immersion is killed by the kernel of the comorphism, which is the essential-image
description of [Stacks, Tag 08KS]
(`Stacks.ClosedImmersion.pushforward_essImage_iff`), and
`Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal` turns that into the affine-open condition
`Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_affine_sections_annihilated` consumes. The
exponent matches on the nose: the `n`-th term of `levelSystem` is `𝓛ₙ₊₁`, annihilated by
`(I𝒪_U) ^ (n + 1)`, which is the shifted indexing `levelSystem` was chosen for.

The members of `S` are indexed by a *pair* `(h, g)` rather than by a single element: `D(h)` alone
need not lie in `U`, so the basis is obtained by cutting a given `D(h)` down with one of the three
opens `D(x)`, `D(y)`, `D(t)` that cover `U`, and `D(hg)` is affine because it is a basic open of
`Spec(A)` contained in `U`. The third variable is needed here exactly as it is for
`Stacks.Algebraization.NonAlgebraizableExample.epi_levelTransitionOnOpen`: the punctured spectrum
of `A` is not covered by `D(x) ∪ D(y)`.

## What is not proved here

Nothing of membership in `Coh(U, I𝒪_U)` is left open: the kernel computation and the assembly of
the four inputs are in the module `NonAlgebraizableLevelKernel` of this directory, which also
proves the resulting object invertible.
`Stacks.Algebraization.NonAlgebraizableExample.HasNonAlgebraizableInvertibleObject` is still
untagged, its non-algebraizability clause being independent of everything here.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization.NonAlgebraizableExample

variable (k : Type u) [Field k]

/-! ### The level scheme over `U` is the infinitesimal neighbourhood -/

/-- The structure map `Spec(A/tⁿA) ∩ U ⟶ U` is a closed immersion: it is the restriction of the
closed immersion `Spec(A/tⁿA) ⟶ Spec(A)` to `U` and its whole preimage. -/
public instance isClosedImmersion_levelStructureMap (m : ℕ) :
    IsClosedImmersion (levelStructureMap k m) :=
  Scheme.Hom.isClosedImmersion_resLE (levelToAmbient k m) (preimage_U_levelToAmbient k m)

/-- **Stacks Project, Tag 0EHE (the level scheme over `U` is cut out by `(I𝒪_U)ⁿ`).** The kernel
ideal sheaf of the structure map `Spec(A/tⁿA) ∩ U ⟶ U` is the `n`-th power of `I𝒪_U`.

This is `Stacks.Algebraization.NonAlgebraizableExample.exists_subschemeIso_levelOpen` read as an
equality of ideal sheaves: that identification is compatible with the two morphisms to `U`, and a
kernel ideal sheaf does not change when the morphism is precomposed with an isomorphism. -/
@[stacks 0EHE "the kernel ideal sheaf of Spec(A/t^n A) ∩ U → U is (I O_U)^n"]
public theorem ker_levelStructureMap (m : ℕ) :
    (levelStructureMap k m).ker = idealOnOpen (situation k) ^ m := by
  obtain ⟨e, he⟩ := exists_subschemeIso_levelOpen k m
  rw [← Scheme.IdealSheafData.ker_subschemeι (idealOnOpen (situation k) ^ m), ← he,
    Scheme.Hom.ker_comp_of_isIso]

/-! ### The terms of the system are coherent -/

/-- **Stacks Project, Tag 0EHE (`𝓛ₙ` is coherent on `U`).** The module `𝓛ₙ`, read on the
punctured spectrum `U` of `A`, is coherent: it is invertible upstairs, hence coherent there by
[Stacks, Tag 01XZ], and its direct image along the closed immersion
`Spec(A/tⁿA) ∩ U ⟶ U` — a finite morphism — is coherent by [Stacks, Tag 01Y6]. -/
@[stacks 0EHE "L_n, pushed forward to U, is a coherent module"]
public theorem isCoherent_levelModuleOnOpen (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (m : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} (levelModuleOnOpen k a φ m) :=
  have : _root_.SheafOfModules.IsCoherent (levelModule k a φ m) :=
    @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible
      (levelOpen k m).toScheme _ (levelModule k a φ m) (isInvertibleModule_levelModule k a φ m)
  Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
    (levelStructureMap k m) (levelModule k a φ m)

/-- **Stacks Project, Tag 0EHE (the system has coherent terms).** Every term of the system
`(𝓛ₙ)` is a coherent module on `U`. This is the hypothesis `hcoh` of
`Stacks.Algebraization.isCoherentAdicSystem_of_basis_ker`. -/
@[stacks 0EHE "the terms of the system (L_n) are coherent"]
public theorem isCoherent_levelSystem_obj (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (n : ℕ) :
    _root_.SheafOfModules.IsCoherent.{u} ((levelSystem k a φ).obj (op n)) :=
  isCoherent_levelModuleOnOpen k a φ (n + 1)

/-! ### The terms of the system are annihilated by the ideal powers -/

/-- The direct image of `𝓛ₙ` along the closed immersion `Spec(A/tⁿA) ∩ U ⟶ U` is killed by the
kernel of the comorphism of that immersion: it lies in the essential image of the direct-image
functor, which [Stacks, Tag 08KS] describes by exactly that annihilation. -/
public theorem annihilatedByKer_levelModuleOnOpen (a : ℕ → PlaneRing k) (φ : ℕ → ℕ) (m : ℕ) :
    Stacks.ClosedImmersion.AnnihilatedByKer (levelStructureMap k m)
      (levelModuleOnOpen k a φ m) :=
  (Stacks.ClosedImmersion.pushforward_essImage_iff (levelStructureMap k m)
    (levelModuleOnOpen k a φ m)).mp
      ((Scheme.Modules.pushforward (levelStructureMap k m)).obj_mem_essImage
        (levelModule k a φ m))

/-- **Stacks Project, Tag 0EHE (`𝓛ₙ` is annihilated by `(I𝒪_U)ⁿ`).** The module `𝓛ₙ`, read on
`U`, is annihilated by the `n`-th power of `I𝒪_U`: that power is the kernel ideal sheaf of the
closed immersion `Spec(A/tⁿA) ∩ U ⟶ U` by
`Stacks.Algebraization.NonAlgebraizableExample.ker_levelStructureMap`, and the kernel of a closed
immersion kills every direct image along it. -/
@[stacks 0EHE "L_n, pushed forward to U, is annihilated by (I O_U)^n"]
public theorem idealPowerMultiple_levelModuleOnOpen_eq_bot (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (m : ℕ) :
    idealPowerMultiple (idealOnOpen (situation k)) m (levelModuleOnOpen k a φ m) = ⊥ := by
  rw [idealPowerMultiple_eq_bot_iff_affine_sections_annihilated]
  intro W r hr x
  refine (Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal (levelStructureMap k m)
    (levelModuleOnOpen k a φ m)).mp (annihilatedByKer_levelModuleOnOpen k a φ m) W r ?_ x
  rw [ker_levelStructureMap, Scheme.IdealSheafData.ideal_pow]
  simpa using hr

/-- **Stacks Project, Tag 0EHE (the system is annihilated by the successive ideal powers).** The
`n`-th term of the system `(𝓛ₙ)` is annihilated by the `(n + 1)`-st power of `I𝒪_U`. This is the
hypothesis `hann` of `Stacks.Algebraization.isCoherentAdicSystem_of_basis_ker`; the exponent
matches because the `n`-th term of the system is `𝓛ₙ₊₁`. -/
@[stacks 0EHE "the n-th term of the system (L_n) is annihilated by (I O_U)^(n+1)"]
public theorem idealPowerMultiple_levelSystem_obj_eq_bot (a : ℕ → PlaneRing k) (φ : ℕ → ℕ)
    (n : ℕ) :
    idealPowerMultiple (idealOnOpen (situation k)) (n + 1) ((levelSystem k a φ).obj (op n)) = ⊥ :=
  idealPowerMultiple_levelModuleOnOpen_eq_bot k a φ (n + 1)

/-! ### The basis of affine opens -/

/-- A basic open `D(r)` of `Spec(A)` which lies in the punctured spectrum `U` is an affine open
of `U`, being the preimage of an affine open of `Spec(A)` along the open immersion `U ⟶ Spec(A)`,
whose range contains it. -/
public theorem isAffineOpen_ambientBasicOpen (r : AmbientRing k)
    (hr : PrimeSpectrum.basicOpen r ≤ (situation k).U) :
    IsAffineOpen (ambientBasicOpen k r) :=
  (IsAffineOpen.Spec_basicOpen r).preimage_of_isOpenImmersion (situation k).U.ι
    (hr.trans (Scheme.Opens.opensRange_ι (situation k).U).ge)

/-- **Stacks Project, Tag 0EHE (the family of affine opens the kernel computation runs on).** The
affine opens `D(hg)` of `U`, for `h` an element of `A` and `g` one of the three variables `x`,
`y`, `t`. Over each of them the module `𝓛ₙ` is trivialized — for `g = x` or `g = y` because
`D(hg)` lies in a chart, for `g = t` because its preimage upstairs is empty — and they form a
basis of the topology of `U`. -/
@[stacks 0EHE "the family of affine opens D(hg) of U, for g one of x, y, t"]
public def ambientBasicAffineOpens : Set (situation k).U.toScheme.affineOpens :=
  {V | ∃ h g : AmbientRing k, g ∈ ({xVar k, yVar k, tVar k} : Set (AmbientRing k)) ∧
    (V : (situation k).U.toScheme.Opens) = ambientBasicOpen k (h * g)}

/-- **Stacks Project, Tag 0EHE (those affine opens are a basis).** Every point of every open `W`
of the punctured spectrum `U` of `A` has one of the affine opens `D(hg)` around it inside `W`:
the basic opens `D(h)` of `Spec(A)` are a basis of `U`, and `D(h)` is cut down into `U` by
whichever of `D(x)`, `D(y)`, `D(t)` contains the point. This is the hypothesis `hS` of
`Stacks.Algebraization.isCoherentAdicSystem_of_basis_ker`. -/
@[stacks 0EHE "the affine opens D(hg) are a basis of the topology of U"]
public theorem exists_mem_ambientBasicAffineOpens
    (W : (situation k).U.toScheme.Opens) (x : (situation k).U.toScheme) (hx : x ∈ W) :
    ∃ V ∈ ambientBasicAffineOpens k, x ∈ (V : (situation k).U.toScheme.Opens) ∧
      (V : (situation k).U.toScheme.Opens) ≤ W := by
  obtain ⟨h, hxh, hhW⟩ := exists_ambientBasicOpen_nbhd k hx
  have main : ∀ g : AmbientRing k, g ∈ ({xVar k, yVar k, tVar k} : Set (AmbientRing k)) →
      (x.val : (situation k).X) ∈ PrimeSpectrum.basicOpen g →
      ∃ V ∈ ambientBasicAffineOpens k, x ∈ (V : (situation k).U.toScheme.Opens) ∧
        (V : (situation k).U.toScheme.Opens) ≤ W := by
    intro g hg hxg
    refine ⟨⟨ambientBasicOpen k (h * g), isAffineOpen_ambientBasicOpen k (h * g)
        ((PrimeSpectrum.basicOpen_mul_le_right h g).trans (basicOpen_le_U k hg))⟩,
      ⟨h, g, hg, rfl⟩, mem_ambientBasicOpen_mul k hxh hxg, ?_⟩
    exact ((situation k).U.ι.preimage_mono
      (PrimeSpectrum.basicOpen_mul_le_left h g)).trans hhW
  rcases exists_mem_basicOpen_of_mem_U k x.val x.2 with hc | hc | hc
  · exact main (xVar k) (Set.mem_insert _ _) hc
  · exact main (yVar k) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) hc
  · exact main (tVar k) (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)) hc

end Stacks.Algebraization.NonAlgebraizableExample

end
