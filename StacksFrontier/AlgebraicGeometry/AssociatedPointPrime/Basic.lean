module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import StacksFrontier.RingTheory.AssociatedPrime.Spellings
public import StacksFrontier.AlgebraicGeometry.EmbeddedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Associated points against associated primes

Let `X` be a locally Noetherian scheme, `F` a quasi-coherent `𝒪_X`-module, `U` an affine open of
`X` and `x ∈ U`. Writing `A = Γ(X, U)` and `M = Γ(F, U)`, the point `x` of `U` corresponds to a
prime `p ⊆ A`. This file proves that `x` is an associated point of `F` exactly when `p` is an
associated prime of the `A`-module `M`. Equivalently, under the identification of `U` with
`Spec A`, the associated points of `F` lying in `U` are exactly the associated primes of
`Γ(F, U)`: the *spectrum characterisation* of associated points.

## Imported machinery

The stalk-side machinery this file runs on is not declared here: the `Γ(X, U)`-module structure
on the stalk `F_x`, the germ at `x` as a `Γ(X, U)`-linear map `Γ(F, U) → F_x`, and the
presentation of the stalk as a localization of `Γ(F, U)` are
`Stacks.ModuleStalkSpecialization.sectionsStalkModule`,
`Stacks.ModuleStalkSpecialization.germₗ` and
`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ` of
`StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization`. The first three are
re-exported into this namespace, so the bare names stay available to the files that open it.

## Main results

* `isAssociatedPoint_of_mem_associatedPrimes` and `mem_associatedPrimes_of_isAssociatedPoint`:
  the two implications of the bridge, and `isAssociatedPoint_iff_mem_associatedPrimes`, the
  resulting equivalence.
* `associatedPrimes_eq_image_associatedPoints`: the set form — the associated primes of
  `Γ(F, U)` are the images of the associated points of `F` lying in `U`.
* `isSchemeAssociatedPoint_iff_mem_associatedPrimes`: the specialization to the structure sheaf,
  which is the shape in which `Stacks.AlgebraicGeometry.EmbeddedPoints` is written.

## Route

The direction "associated prime of the sections ⟹ associated point" is the argument already
carried out inside `Stacks.AlgebraicGeometry.AssociatedPointsMono.injective_app_of_isAffineOpen`,
factored out here: an element of `Γ(F, U)` whose annihilator is the prime of `x` has, by
`colon_germ_eq`, a germ at `x` whose annihilator is the maximal ideal of `𝒪_{X,x}`. Noetherianity
of `Γ(X, U)` is used only to strip the radical from Mathlib's definition of an associated prime.

The converse is not an element chase: the annihilator in `Γ(X, U)` of a section produced from an
element of the stalk is in general only *saturated* to the prime of `x`, not equal to it, so a
different element of `Γ(F, U)` has to be produced. The correct tool is the behaviour of associated
primes under localization, which Mathlib has as
`Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule`
(Stacks tag 0310) over a Noetherian ring. Applying it needs the stalk to be presented as a
localized module, which is `Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`; that file
checks the three conditions and needs no Noetherian hypothesis.

## Implementation notes

Neither `Module (X.presheaf.stalk x) (F.presheaf.stalk x)` nor the `Γ(X, U)`-module structure
obtained from it by restriction of scalars is found by instance search, because the latter cannot
unfold `AlgebraicGeometry.Scheme.Modules.presheaf`. They are supplied as the definitions
`Stacks.AlgebraicGeometry.AssociatedPointsMono.stalkModule` and
`Stacks.ModuleStalkSpecialization.sectionsStalkModule`, to be introduced with `let`. For the same
reason the two scalar actions on the stalk have to be related by the explicit lemma
`smul_stalk_eq` rather than by `rfl` inside an elaboration problem.

## References

* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
* [Stacks Project, Tag 0310](https://stacks.math.columbia.edu/tag/0310)
* [Stacks Project, Tag 05AK](https://stacks.math.columbia.edu/tag/05AK)
* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.AssociatedPointsMono
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.AssociatedPointPrime

variable {X : Scheme.{u}}

/-! ### The stalk as a module over the sections of the structure sheaf -/

-- The module structure on the stalk, the linear germ map and the localization statement were
-- duplicated here; the surviving copies are in
-- `StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization` (namespace
-- `Stacks.ModuleStalkSpecialization`), which holds the better-factored proofs. Old -> new:
--   `sectionsStalkModule`     -> `Stacks.ModuleStalkSpecialization.sectionsStalkModule`
--   `germ_smul_eq`            -> `Stacks.ModuleStalkSpecialization.germ_smul`
--   `germₗ`                   -> `Stacks.ModuleStalkSpecialization.germₗ`
--   `isScalarTower_stalk`     -> `Stacks.ModuleStalkSpecialization.isScalarTower_sectionsStalk`
--   `isLocalizedModule_germₗ` -> `Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`
-- `germₗ_apply`, `germ_restrict`, `germ_restrict_ring` and `germ_smul_restrict` had no
-- counterpart in that file and no user outside the deleted `isLocalizedModule_germₗ` proof, so
-- they went with it.

export Stacks.ModuleStalkSpecialization (sectionsStalkModule germₗ isLocalizedModule_germₗ)

/-- The action of `Γ(X, U)` on a stalk is the action of `𝒪_{X,x}` through the germ map. -/
theorem smul_stalk_eq (F : X.Modules) {U : X.Opens} {x : X} (hx : x ∈ U) (r : Γ(X, U))
    (z : F.presheaf.stalk x) :
    letI := stalkModule F x
    letI := sectionsStalkModule F hx
    r • z = (X.presheaf.germ U x hx) r • z := rfl

/-! ### The bridge -/

/-- **An associated prime of the sections over an affine open is an associated point.** This is
the implication already present inside
`Stacks.AlgebraicGeometry.AssociatedPointsMono.injective_app_of_isAffineOpen`, stated on its
own. -/
theorem isAssociatedPoint_of_mem_associatedPrimes [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (h : (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U)) :
    IsAssociatedPoint F x := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at h
  obtain ⟨-, k, hk⟩ := h
  have hcol : (⊥ : Submodule Γ(X, U) Γ(F, U)).colon (Submodule.span Γ(X, U) {k})
      = (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [Submodule.colon_span, ← hk]
  let := stalkModule F x
  exact ⟨inferInstance, _, colon_germ_eq F hU x hx k hcol⟩

/-- **An associated point of a quasi-coherent module on a locally Noetherian scheme gives an
associated prime of the sections over any affine open containing it.**

The route is the behaviour of associated primes under localization, Mathlib's
`Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule`,
applied to the presentation of the stalk as a localized module given by
`isLocalizedModule_germₗ`; the maximal ideal of `𝒪_{X,x}` contracts to the prime of `x`. -/
theorem mem_associatedPrimes_of_isAssociatedPoint [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (h : IsAssociatedPoint F x) :
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := stalkModule F x
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let := sectionsStalkModule F hx
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  have htower := Stacks.ModuleStalkSpecialization.isScalarTower_sectionsStalk F hx
  have hlm := isLocalizedModule_germₗ F hU hx
  have hmem : IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
      associatedPrimes (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    Stacks.RingTheory.AssociatedPrimeStacks.isAssociatedPrime_of_isAssociatedPrimeStacks h
  have key : (Ideal.comap (algebraMap Γ(X, U) (X.presheaf.stalk x))) ⁻¹'
      (associatedPrimes Γ(X, U) Γ(F, U))
        = associatedPrimes (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
      (S := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (R' := X.presheaf.stalk x)
      (f := germₗ F hx)
  rw [← key] at hmem
  have hcomap : Ideal.comap (algebraMap Γ(X, U) (X.presheaf.stalk x))
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) = (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  rwa [Set.mem_preimage, hcomap] at hmem

/-- **Associated points are associated primes.** On a locally Noetherian scheme, a point `x` of
an affine open `U` is an associated point of a quasi-coherent module `F` exactly when the prime
of `x` in `Γ(X, U)` is an associated prime of the `Γ(X, U)`-module `Γ(F, U)`. -/
theorem isAssociatedPoint_iff_mem_associatedPrimes [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    IsAssociatedPoint F x ↔
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) :=
  ⟨mem_associatedPrimes_of_isAssociatedPoint F hU hx,
    isAssociatedPoint_of_mem_associatedPrimes F hU hx⟩

/-- **The spectrum characterisation of associated points.** Under the identification of an affine
open `U` with `Spec Γ(X, U)`, the associated primes of `Γ(F, U)` are exactly the points of `U`
associated to `F`. -/
theorem associatedPrimes_eq_image_associatedPoints [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    associatedPrimes Γ(X, U) Γ(F, U)
      = (fun y : U => (hU.primeIdealOf y).asIdeal) '' {y : U | (y : X) ∈ associatedPoints F} := by
  ext q
  refine ⟨fun hq => ?_, ?_⟩
  · have hqp : q.IsPrime := hq.1
    set u : U := hU.isoSpec.inv ⟨q, hqp⟩ with hu
    have hpq : hU.primeIdealOf u = ⟨q, hqp⟩ := primeIdealOf_isoSpec_inv hU _
    have hqu : (hU.primeIdealOf ⟨(u : X), u.2⟩).asIdeal = q :=
      congrArg PrimeSpectrum.asIdeal hpq
    refine ⟨u, isAssociatedPoint_of_mem_associatedPrimes F hU u.2 ?_, hqu⟩
    rw [hqu]
    exact hq
  · rintro ⟨y, hy, rfl⟩
    exact mem_associatedPrimes_of_isAssociatedPoint F hU y.2 hy

/-- **The structure-sheaf case.** A point of an affine open is an associated point of a scheme —
in the sense of `Stacks.AlgebraicGeometry.EmbeddedPoints.IsSchemeAssociatedPoint`, which is the
notion the no-embedded-points predicate of Tag 05AK is built from — exactly when the prime of that
point is an associated prime of the ring of functions on the open.

The structure sheaf is passed as a module `F` together with the hypothesis that it *is* the unit
module, because neither `(SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent` nor
`Module Γ(X, U) Γ(SheafOfModules.unit X.ringCatSheaf, U)` is found by instance search. -/
@[ega "IV 3.1.2" "special case"]
theorem isSchemeAssociatedPoint_iff_mem_associatedPrimes [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsQuasicoherent] (hF : F = SheafOfModules.unit X.ringCatSheaf)
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    EmbeddedPoints.IsSchemeAssociatedPoint X x ↔
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) := by
  subst hF
  exact isAssociatedPoint_iff_mem_associatedPrimes _ hU hx

end Stacks.AlgebraicGeometry.AssociatedPointPrime

end
