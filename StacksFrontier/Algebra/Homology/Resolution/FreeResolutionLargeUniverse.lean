module

public import StacksFrontier.Algebra.Homology.Resolution.Existence

@[expose] public section

/-!
# Free resolutions of modules in a universe above the ring's

Let `R` be a commutative ring in a universe `u` and let `M` be an `R`-module whose carrier lies
in a universe `max u v` independent of `u`. Covering `M` by the free module `M →₀ R`, then
covering the kernel of that surjection, and iterating, produces an exact complex
`... → F₂ → F₁ → F₀ → M → 0` of free `R`-modules.

## Main definitions

* `FreeResolutionLargeUniverse.Layer`: one stage of the construction — a module, a free cover of
  it, and the covering surjection.
* `FreeResolutionLargeUniverse.coverLayer`: the canonical free cover of a module.
* `FreeResolutionLargeUniverse.layers`: the stages obtained by iterating the construction on the
  kernel of the previous surjection.
* `FreeResolutionLargeUniverse.buildResolution`: the resolution datum assembled from the stages.

## Main results

* `exists_free_resolution_largeUniverse`: every module whose carrier lies in a universe above the
  ring's admits an exact complex of free modules.

## Implementation notes

This is the counterpart, for a module carrier in a universe `max u v` above the ring's universe
`u`, of the construction in `StacksFrontier.Algebra.Homology.Resolution.Existence`, whose stages
carry their module in the ring's own universe. The two constructions are the same formulas at
different universe levels and a later pass can collapse them into one; the resolution datum
`FreeResolutionData` they both produce is already stated at an independent universe and is
shared rather than duplicated.
-/

universe u v

namespace FreeResolutionLargeUniverse

/-- One stage of a free resolution of a module in a universe above the ring's: a module `K`, a
free cover `F` of it, and a surjection `π : F ↠ K`. -/
structure Layer (R : Type u) [CommRing R] where
  /-- The module to be covered at this stage (a syzygy module). -/
  K : Type (max u v)
  [acgK : AddCommGroup K]
  [modK : Module R K]
  /-- The free cover of `K`. -/
  F : Type (max u v)
  [acgF : AddCommGroup F]
  [modF : Module R F]
  [freeF : Module.Free R F]
  /-- The covering surjection. -/
  π : F →ₗ[R] K
  /-- The cover is surjective. -/
  hπ : Function.Surjective π

attribute [instance] Layer.acgK Layer.modK Layer.acgF Layer.modF Layer.freeF

variable {R : Type u} [CommRing R]

/-- Cover an arbitrary module `K` by the free module `K →₀ R` via the canonical surjection. -/
noncomputable def coverLayer (K : Type (max u v)) [AddCommGroup K] [Module R K] :
    Layer.{u, v} R where
  K := K
  F := K →₀ R
  π := Finsupp.linearCombination R (id : K → K)
  hπ := Finsupp.linearCombination_id_surjective R K

/-- The next stage: cover the kernel of the current surjection. -/
noncomputable def nextLayer (L : Layer.{u, v} R) : Layer.{u, v} R :=
  coverLayer (R := R) (LinearMap.ker L.π)

/-- The sequence of stages obtained by iterating `nextLayer` from a starting stage. -/
noncomputable def layers (L0 : Layer.{u, v} R) : ℕ → Layer.{u, v} R
  | 0 => L0
  | (n + 1) => nextLayer (layers L0 n)

/-- The differential `d n : F (n + 1) → F n`: cover `ker (πₙ)` and include it back into `Fₙ`.
This typechecks because `(layers L0 (n + 1)).K` is definitionally `LinearMap.ker (layers L0 n).π`.
-/
noncomputable def dd (L0 : Layer.{u, v} R) (n : ℕ) :
    (layers L0 (n + 1)).F →ₗ[R] (layers L0 n).F :=
  (LinearMap.ker (layers L0 n).π).subtype.comp (layers L0 (n + 1)).π

set_option backward.isDefEq.respectTransparency false in
-- The rewrite by `LinearMap.range_comp` needs the module structure on the kernel of `πₙ` and the
-- one carried by the next stage to be identified at implicit transparency.
/-- The image of `dd L0 n` is exactly `ker (πₙ)`: it is the image under the inclusion of
`ker (πₙ)` of the whole of `Fₙ₊₁`, because `πₙ₊₁` is surjective onto `ker (πₙ)`. -/
theorem dd_range (L0 : Layer.{u, v} R) (n : ℕ) :
    LinearMap.range (dd L0 n) = LinearMap.ker (layers L0 n).π := by
  rw [dd, LinearMap.range_comp, LinearMap.range_eq_top.mpr (layers L0 (n + 1)).hπ,
    Submodule.map_top, Submodule.range_subtype]

set_option backward.isDefEq.respectTransparency false in
-- The rewrite by `LinearMap.ker_comp` needs the module structure on the kernel of `πₙ` and the
-- one carried by the next stage to be identified at implicit transparency.
/-- The kernel of `dd L0 n` is exactly `ker (πₙ₊₁)`, the inclusion of `ker (πₙ)` being
injective. -/
theorem dd_ker (L0 : Layer.{u, v} R) (n : ℕ) :
    LinearMap.ker (dd L0 n) = LinearMap.ker (layers L0 (n + 1)).π := by
  rw [dd, LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _),
    Submodule.comap_bot]

/-- Assemble the stages into a resolution datum for `L0.K`. -/
noncomputable def buildResolution (L0 : Layer.{u, v} R) : FreeResolutionData R L0.K where
  F n := (layers L0 n).F
  instAddCommGroup n := (layers L0 n).acgF
  instModule n := (layers L0 n).modF
  d n := dd L0 n
  ε := (layers L0 0).π

/-- The assembled complex of stages is exact. -/
theorem buildResolution_isExact (L0 : Layer.{u, v} R) : (buildResolution L0).IsExact := by
  refine ⟨(layers L0 0).hπ, ?_, ?_⟩
  · change LinearMap.range (dd L0 0) = LinearMap.ker (layers L0 0).π
    exact dd_range L0 0
  · intro n
    change LinearMap.range (dd L0 (n + 1)) = LinearMap.ker (dd L0 n)
    rw [dd_range L0 (n + 1), dd_ker L0 n]

/-- Every term of the assembled complex is free. -/
theorem buildResolution_isFree (L0 : Layer.{u, v} R) : (buildResolution L0).IsFree :=
  fun n => (layers L0 n).freeF

end FreeResolutionLargeUniverse

open FreeResolutionLargeUniverse in
/-- For a commutative ring `R` in a universe `u` and an `R`-module `M` whose carrier lies in a
universe `max u v` above it, there is an exact complex of `R`-modules
`... → F₂ → F₁ → F₀ → M → 0` in which every `Fᵢ` is free. -/
theorem exists_free_resolution_largeUniverse
    (R : Type u) [CommRing R] (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    ∃ P : FreeResolutionData R M, P.IsExact ∧ P.IsFree :=
  ⟨buildResolution (coverLayer.{u, v} (R := R) M),
    buildResolution_isExact _, buildResolution_isFree _⟩

end
