module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.Depth.SemilinearEquivCohenMacaulay

/-!
# The stalk of a quasi-coherent module as a localization, semilinearly

Let `X` be a scheme, `U ⊆ X` an affine open, `x ∈ U` and `ℱ` a quasi-coherent `𝒪_X`-module.  Two
known facts present the stalk at `x` as a localization of the sections over `U`:
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk` says the local ring `𝒪_{X,x}` is a
localization of `Γ(X, U)` at the prime `𝔭` of `x`, and
`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ` says the stalk `ℱ_x` is the
localization of `Γ(ℱ, U)` at the same prime.

Both are `IsLocalization`/`IsLocalizedModule` *properties* of the germ maps.  What a consumer
that wants to move a statement about `Γ(ℱ, U)_𝔭` over `Γ(X, U)_𝔭` to a statement about `ℱ_x`
over `𝒪_{X,x}` needs instead are the two *isomorphisms* those properties determine, together
with the compatibility between them — and that compatibility is not linearity: `ℱ_x` is a module
over `𝒪_{X,x}` while `Γ(ℱ, U)_𝔭` is a module over `Γ(X, U)_𝔭`, so all that can relate them is an
additive isomorphism semilinear over the ring isomorphism.  That is exactly the data
`Module.isMaximalCohenMacaulay_of_semilinearEquiv` consumes, and this file writes it down.

## Main definitions

* `Stacks.ModuleStalkSpecialization.stalkRingEquiv`: the ring isomorphism
  `𝒪_{X,x} ≃+* Γ(X, U)_𝔭`.
* `Stacks.ModuleStalkSpecialization.stalkLinearEquiv`: the `Γ(X, U)`-linear isomorphism
  `ℱ_x ≃ₗ Γ(ℱ, U)_𝔭`.

## Main results

* `Stacks.ModuleStalkSpecialization.stalkRingEquiv_algebraMap`: the ring isomorphism carries the
  germ of a section to its image in the localization.
* `Stacks.ModuleStalkSpecialization.stalkLinearEquiv_smul`: **the module isomorphism is
  semilinear over the ring isomorphism**, for the action of the whole local ring `𝒪_{X,x}` and
  not merely of `Γ(X, U)`.
* `Stacks.ModuleStalkSpecialization.isMaximalCohenMacaulay_stalk`: hence maximal
  Cohen–Macaulayness ([Stacks, Tag 00NF]) passes from `Γ(ℱ, U)_𝔭` to `ℱ_x`.
* `Stacks.ModuleStalkSpecialization.min_supportDim_le_depth_stalk`: and therefore so does the
  inequality of Serre's condition `(S_k)` at `x`, for every `k` — the form
  `AlgebraicGeometry.SheafHasPropertySk` is stated in.

## Implementation notes

**Why the semilinearity needs a proof at all.** `IsLocalizedModule.iso` is `Γ(X, U)`-linear, so
`f (r • m) = r • f m` holds for `r : Γ(X, U)` by construction; the statement wanted is the same
for `a : 𝒪_{X,x}`, and the ring isomorphism has to appear.  Writing `a = r/s` with `s ∉ 𝔭`,
multiplying through by the germ of `s` turns both sides into `Γ(X, U)`-scalar actions — on the
left by the scalar tower `Γ(X, U) → 𝒪_{X,x} → ℱ_x`
(`Stacks.ModuleStalkSpecialization.isScalarTower_sectionsStalk`) and on the right because the
ring isomorphism is one of `Γ(X, U)`-algebras — after which `Γ(X, U)`-linearity closes the goal.
The germ of `s` is invertible in both localizations, so the multiplication can be cancelled.

**The module structures are `letI` binders**, as everywhere in
`StacksFrontier/AlgebraicGeometry/Scheme/Points/ModuleStalkSpecialization.lean`: instance search
cannot produce `Module 𝒪_{X,x} ℱ_x` in the `Scheme.Modules.presheaf` spelling.
`Stacks.ModuleStalkSpecialization.stalkModule` is Mathlib's instance named explicitly, which is
the same structure `AlgebraicGeometry.SheafHasPropertySk` is stated over, so the last result
above feeds that predicate directly.

**What this does not do.** It says nothing about which modules are maximal Cohen–Macaulay: the
hypothesis of the last two results is maximal Cohen–Macaulayness over `Γ(X, U)_𝔭`.  For the
dualizing module of [Stacks, Tag 0AWT] that hypothesis is supplied in
`StacksFrontier/AlgebraicGeometry/Duality/CohenMacaulayDualizingModule.lean`, out of
`Dualizing.isMaximalCohenMacaulay_homology_of_concentrated`, which is the normalizing-shift
question this file deliberately does not address.  See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/CohenMacaulayLocus.lean`.

## References

* [Stacks Project, Tag 00NF](https://stacks.math.columbia.edu/tag/00NF)
* [Stacks Project, Tag 0341](https://stacks.math.columbia.edu/tag/0341)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.ModuleStalkSpecialization

variable {X : Scheme.{u}}

/-- The local ring at a point of an affine open, as a localization of the sections. -/
def stalkRingEquiv {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    letI := (X.presheaf.germ U x hx).hom.toAlgebra
    X.presheaf.stalk x ≃+*
      Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
  letI := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (X.presheaf.stalk x)
    (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)).toRingEquiv

/-- The stalk of a quasi-coherent module at a point of an affine open, as a localized module. -/
def stalkLinearEquiv (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    letI := sectionsStalkModule F hx
    F.presheaf.stalk x ≃ₗ[Γ(X, U)]
      LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U) :=
  letI := sectionsStalkModule F hx
  haveI := isLocalizedModule_germₗ F hU hx
  (IsLocalizedModule.iso (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (germₗ F hx)).symm

/-- The comparison carries the germ of a section of the structure sheaf to the image of that
section in the localization. -/
theorem stalkRingEquiv_algebraMap {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    letI := (X.presheaf.germ U x hx).hom.toAlgebra
    ∀ r : Γ(X, U), stalkRingEquiv hU hx (algebraMap Γ(X, U) (X.presheaf.stalk x) r) =
      algebraMap Γ(X, U) (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) r := by
  let := (X.presheaf.germ U x hx).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  intro r
  exact (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (X.presheaf.stalk x)
    (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)).commutes r

/-- **The stalk comparison is semilinear over the ring comparison.** -/
theorem stalkLinearEquiv_smul (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    letI := (X.presheaf.germ U x hx).hom.toAlgebra
    letI := stalkModule F x
    letI := sectionsStalkModule F hx
    ∀ (a : X.presheaf.stalk x) (m : F.presheaf.stalk x),
      stalkLinearEquiv F hU hx (a • m) =
        stalkRingEquiv hU hx a • stalkLinearEquiv F hU hx m := by
  let := (X.presheaf.germ U x hx).hom.toAlgebra
  let := stalkModule F x
  let := sectionsStalkModule F hx
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have := isLocalizedModule_germₗ F hU hx
  have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    isScalarTower_sectionsStalk F hx
  intro a m
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl a
  have hunit : IsUnit (algebraMap Γ(X, U)
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) (s : Γ(X, U))) :=
    IsLocalization.map_units _ s
  have hA : (algebraMap Γ(X, U) (X.presheaf.stalk x) (s : Γ(X, U))) *
      IsLocalization.mk' (X.presheaf.stalk x) r s =
      algebraMap Γ(X, U) (X.presheaf.stalk x) r := IsLocalization.mk'_spec' _ r s
  have hmul : ((s : Γ(X, U)) • (IsLocalization.mk' (X.presheaf.stalk x) r s • m))
      = ((r : Γ(X, U)) • m) := by
    rw [← IsScalarTower.algebraMap_smul (X.presheaf.stalk x) (s : Γ(X, U)), smul_smul, hA,
      IsScalarTower.algebraMap_smul]
  have hB : (algebraMap Γ(X, U)
        (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) (s : Γ(X, U))) *
      stalkRingEquiv hU hx (IsLocalization.mk' (X.presheaf.stalk x) r s) =
      algebraMap Γ(X, U) (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) r := by
    rw [← stalkRingEquiv_algebraMap hU hx (s : Γ(X, U)), ← map_mul, hA,
      stalkRingEquiv_algebraMap]
  refine hunit.smul_left_cancel.mp ?_
  rw [IsScalarTower.algebraMap_smul, ← LinearEquiv.map_smul, hmul, LinearEquiv.map_smul,
    smul_smul, hB, IsScalarTower.algebraMap_smul]

/-- **Maximal Cohen–Macaulayness transports from the sections to the stalk.** -/
theorem isMaximalCohenMacaulay_stalk (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (h : Module.IsMaximalCohenMacaulay
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
      (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U))) :
    letI := stalkModule F x
    Module.IsMaximalCohenMacaulay (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  let := (X.presheaf.germ U x hx).hom.toAlgebra
  let := stalkModule F x
  let := sectionsStalkModule F hx
  exact Module.isMaximalCohenMacaulay_of_semilinearEquiv (stalkRingEquiv hU hx).symm
    (stalkLinearEquiv F hU hx).toAddEquiv.symm
    (Module.symm_smul_of_semilinearEquiv (stalkRingEquiv hU hx)
      (stalkLinearEquiv F hU hx).toAddEquiv (stalkLinearEquiv_smul F hU hx)) h

/-- **Serre's condition `(S_k)` at `x`, for every `k`**, from maximal Cohen–Macaulayness of the
localized sections.  This is the inequality `AlgebraicGeometry.SheafHasPropertySk` asks for at
the point `x`, and it is stated over the same stalk module structure. -/
theorem min_supportDim_le_depth_stalk (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (h : Module.IsMaximalCohenMacaulay
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
      (LocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl Γ(F, U))) (k : ℕ) :
    letI := stalkModule F x
    min (k : WithBot ℕ∞) (Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x)) ≤
      (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (F.presheaf.stalk x) : WithBot ℕ∞) :=
  let := stalkModule F x
  Module.min_supportDim_le_depth_of_isMaximalCohenMacaulay
    (isMaximalCohenMacaulay_stalk F hU hx h) k

end Stacks.ModuleStalkSpecialization

end
