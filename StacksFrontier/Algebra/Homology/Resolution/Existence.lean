module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.TotallySplit
public import StacksCore.Tactic.StacksAttribute

/-!
# Resolutions by free and by finite free modules

Let `R` be a commutative ring (with unit) and let `M` be an `R`-module.

A *complex* of `R`-modules
  `... → F₂ →[d₂] F₁ →[d₁] F₀ →[d₀=ε] M → 0`
is a sequence of `R`-modules and `R`-linear maps such that the composition of any
two consecutive maps is zero.

Such a complex is *exact* (a *free resolution* when all `Fᵢ` are free) if:
  - the augmentation `ε : F₀ → M` is surjective (exactness at `M`), and
  - `im(d_{n+1}) = ker(d_n)` at every `Fₙ`.

A module is *free* if it has a basis (`Module.Free`); *finite free* if it is in
addition finitely generated.  A ring is *Noetherian* (`IsNoetherianRing`) if every
ideal is finitely generated; a module is *finite* (`Module.Finite`) if it is
finitely generated.

## Main definitions

* `FreeResolutionData`: an augmented chain complex `... → F 1 → F 0 → M → 0` of `R`-modules.

## Main results

* `exists_free_resolution`: every `R`-module `M` admits an exact complex with all terms free.
* `exists_finite_free_resolution`: if `R` is Noetherian and `M` is finite, then `M` admits an
  exact complex with all terms finite free.

## References

* [Stacks Project, Tag 00LP](https://stacks.math.columbia.edu/tag/00LP)
-/

@[expose] public section
universe u v

/-- A resolution datum for an `R`-module `M`: a family of `R`-modules `F n`,
differentials `d n : F (n+1) →ₗ F n`, and an augmentation `ε : F 0 →ₗ M`.

This packages the data of an augmented chain complex
`... → F 2 → F 1 → F 0 → M → 0`, with `d 0 : F 1 → F 0` the first differential
and `ε : F 0 → M` the augmentation. -/
structure FreeResolutionData (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] where
  /-- The modules of the resolution. -/
  F : ℕ → Type v
  /-- Each `F n` is an additive commutative group. -/
  instAddCommGroup : ∀ n, AddCommGroup (F n)
  /-- Each `F n` is an `R`-module. -/
  instModule : ∀ n, Module R (F n)
  /-- The differentials `d n : F (n+1) → F n`. -/
  d : ∀ n, F (n + 1) →ₗ[R] F n
  /-- The augmentation `ε : F 0 → M`. -/
  ε : F 0 →ₗ[R] M

attribute [instance] FreeResolutionData.instAddCommGroup FreeResolutionData.instModule

namespace FreeResolutionData

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- The *complex* condition: the composition of any two consecutive maps is zero,
i.e. `ε ∘ d 0 = 0` and `d n ∘ d (n+1) = 0` for all `n`. -/
def IsComplex (P : FreeResolutionData R M) : Prop :=
  P.ε.comp (P.d 0) = 0 ∧ ∀ n, (P.d n).comp (P.d (n + 1)) = 0

/-- *Exactness* of the complex: the augmentation `ε` is surjective (exactness at
`M`), `im(d 0) = ker ε` (exactness at `F 0`), and `im(d (n+1)) = ker (d n)` for all
`n` (exactness at `F (n+1)`). -/
@[ega "IV 2.1.10"]
def IsExact (P : FreeResolutionData R M) : Prop :=
  Function.Surjective P.ε ∧
  LinearMap.range (P.d 0) = LinearMap.ker P.ε ∧
  ∀ n, LinearMap.range (P.d (n + 1)) = LinearMap.ker (P.d n)

/-- Every module in the resolution is free. -/
def IsFree (P : FreeResolutionData R M) : Prop :=
  ∀ n, Module.Free R (P.F n)

/-- Every module in the resolution is finite (finitely generated). -/
def IsFinite (P : FreeResolutionData R M) : Prop :=
  ∀ n, Module.Finite R (P.F n)

/-- Every module in the resolution is *finite free*: free and finitely generated
(equivalently, isomorphic to `Rⁿ` for some `n : ℕ`). -/
def IsFiniteFree (P : FreeResolutionData R M) : Prop :=
  ∀ n, Module.Free R (P.F n) ∧ Module.Finite R (P.F n)

end FreeResolutionData

/-! ## Construction of free resolutions

We build a resolution by repeatedly covering a module with a free module and then
covering the kernel of that cover.  A single "layer" packages a module `K`, a free
cover `F`, and a surjection `π : F ↠ K`. -/

namespace FreeResolutionConstruction

/-- One layer of a free resolution: a module `K`, a free cover `F`, and a
surjection `π : F ↠ K`. -/
structure Layer (R : Type u) [CommRing R] where
  /-- The module to be covered at this layer (a syzygy module). -/
  K : Type u
  [acgK : AddCommGroup K]
  [modK : Module R K]
  /-- The free cover of `K`. -/
  F : Type u
  [acgF : AddCommGroup F]
  [modF : Module R F]
  [freeF : Module.Free R F]
  /-- The covering surjection. -/
  π : F →ₗ[R] K
  /-- The cover is surjective. -/
  hπ : Function.Surjective π

attribute [instance] Layer.acgK Layer.modK Layer.acgF Layer.modF Layer.freeF

variable {R : Type u} [CommRing R]

/-- Cover an arbitrary module `K` by the free module `K →₀ R` via the canonical
surjection. -/
noncomputable def coverLayer (K : Type u) [AddCommGroup K] [Module R K] : Layer R where
  K := K
  F := K →₀ R
  π := Finsupp.linearCombination R (id : K → K)
  hπ := Finsupp.linearCombination_id_surjective R K

/-- The next layer: cover the kernel of the current surjection. -/
noncomputable def nextLayer (L : Layer R) : Layer R :=
  coverLayer (R := R) (LinearMap.ker L.π)

/-- The sequence of layers obtained by iterating `nextLayer` from a starting layer. -/
noncomputable def layers (L0 : Layer R) : ℕ → Layer R
  | 0 => L0
  | (n + 1) => nextLayer (layers L0 n)

/-- The differential `d n : F (n+1) → F n`: the cover of `ker (πₙ)` followed by its inclusion
into `Fₙ`. -/
noncomputable def dd (L0 : Layer R) (n : ℕ) :
    (layers L0 (n + 1)).F →ₗ[R] (layers L0 n).F :=
  (LinearMap.ker (layers L0 n).π).subtype.comp (layers L0 (n + 1)).π

-- needed: `dd_range`'s `rw [LinearMap.range_comp]` requires `(layers L0 n).modK` and the
-- `Submodule.module` instance on `↥(ker πₙ)` to be defeq at `implicit` transparency
set_option backward.isDefEq.respectTransparency false in
/-- The image of `dd L0 n` is exactly `ker (πₙ)`. -/
theorem dd_range (L0 : Layer R) (n : ℕ) :
    LinearMap.range (dd L0 n) = LinearMap.ker (layers L0 n).π := by
  rw [dd, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (layers L0 (n + 1)).hπ), Submodule.range_subtype]

-- needed: `dd_ker`'s `rw [LinearMap.ker_comp]` requires `(layers L0 n).modK` and the
-- `Submodule.module` instance on `↥(ker πₙ)` to be defeq at `implicit` transparency
set_option backward.isDefEq.respectTransparency false in
/-- The kernel of `dd L0 n` is exactly `ker (πₙ₊₁)`. -/
theorem dd_ker (L0 : Layer R) (n : ℕ) :
    LinearMap.ker (dd L0 n) = LinearMap.ker (layers L0 (n + 1)).π := by
  exact LinearMap.ker_comp_of_ker_eq_bot _ (Submodule.ker_subtype _)

/-- Assemble the layers into a `FreeResolutionData` of `L0.K`. -/
noncomputable def buildResolution (L0 : Layer R) : FreeResolutionData R L0.K where
  F n := (layers L0 n).F
  instAddCommGroup n := (layers L0 n).acgF
  instModule n := (layers L0 n).modF
  d n := dd L0 n
  ε := (layers L0 0).π

/-- The assembled complex of layers is exact. -/
theorem buildResolution_isExact (L0 : Layer R) : (buildResolution L0).IsExact := by
  exact ⟨(layers L0 0).hπ, dd_range L0 0,
    fun n => (dd_range L0 (n + 1)).trans (dd_ker L0 n).symm⟩

/-- Every term of the assembled complex is free. -/
theorem buildResolution_isFree (L0 : Layer R) : (buildResolution L0).IsFree :=
  fun n => (layers L0 n).freeF

/-! ### Finite layers (Noetherian finite case) -/

/-- One layer of a *finite free* resolution: like `Layer`, but `K` is finite and the
free cover `F` is finite free. -/
structure FinLayer (R : Type u) [CommRing R] where
  /-- The finite module to be covered at this layer. -/
  K : Type u
  [acgK : AddCommGroup K]
  [modK : Module R K]
  [finK : Module.Finite R K]
  /-- The finite free cover of `K`. -/
  F : Type u
  [acgF : AddCommGroup F]
  [modF : Module R F]
  [freeF : Module.Free R F]
  [finF : Module.Finite R F]
  /-- The covering surjection. -/
  π : F →ₗ[R] K
  /-- The cover is surjective. -/
  hπ : Function.Surjective π

attribute [instance] FinLayer.acgK FinLayer.modK FinLayer.finK
  FinLayer.acgF FinLayer.modF FinLayer.freeF FinLayer.finF

variable [IsNoetherianRing R]

/-- Cover a finite module `K` by a finite free module `Fin n → R`. -/
noncomputable def coverFinLayer (K : Type u) [AddCommGroup K] [Module R K]
    [Module.Finite R K] : FinLayer R :=
  let h := Module.Finite.exists_fin' R K
  { K := K
    F := Fin h.choose → R
    π := h.choose_spec.choose
    hπ := h.choose_spec.choose_spec }

/-- The next finite layer: cover the kernel of the current surjection, a finite module since
`R` is Noetherian. -/
noncomputable def nextFinLayer (L : FinLayer R) : FinLayer R :=
  coverFinLayer (R := R) (LinearMap.ker L.π)

/-- The sequence of finite layers obtained by iterating `nextFinLayer`. -/
noncomputable def finLayers (L0 : FinLayer R) : ℕ → FinLayer R
  | 0 => L0
  | (n + 1) => nextFinLayer (finLayers L0 n)

/-- The differential `d n : F (n+1) → F n` in the finite case. -/
noncomputable def ddF (L0 : FinLayer R) (n : ℕ) :
    (finLayers L0 (n + 1)).F →ₗ[R] (finLayers L0 n).F :=
  (LinearMap.ker (finLayers L0 n).π).subtype.comp (finLayers L0 (n + 1)).π

-- needed: `ddF_range`'s `rw [LinearMap.range_comp]` requires `(finLayers L0 n).modK` and the
-- `Submodule.module` instance on `↥(ker πₙ)` to be defeq at `implicit` transparency
set_option backward.isDefEq.respectTransparency false in
/-- The image of `ddF L0 n` is exactly `ker (πₙ)`. -/
theorem ddF_range (L0 : FinLayer R) (n : ℕ) :
    LinearMap.range (ddF L0 n) = LinearMap.ker (finLayers L0 n).π := by
  rw [ddF, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (finLayers L0 (n + 1)).hπ), Submodule.range_subtype]

-- needed: `ddF_ker`'s `rw [LinearMap.ker_comp]` requires `(finLayers L0 n).modK` and the
-- `Submodule.module` instance on `↥(ker πₙ)` to be defeq at `implicit` transparency
set_option backward.isDefEq.respectTransparency false in
/-- The kernel of `ddF L0 n` is exactly `ker (πₙ₊₁)`. -/
theorem ddF_ker (L0 : FinLayer R) (n : ℕ) :
    LinearMap.ker (ddF L0 n) = LinearMap.ker (finLayers L0 (n + 1)).π := by
  exact LinearMap.ker_comp_of_ker_eq_bot _ (Submodule.ker_subtype _)

/-- Assemble the finite layers into a `FreeResolutionData` of `L0.K`. -/
noncomputable def buildFinResolution (L0 : FinLayer R) : FreeResolutionData R L0.K where
  F n := (finLayers L0 n).F
  instAddCommGroup n := (finLayers L0 n).acgF
  instModule n := (finLayers L0 n).modF
  d n := ddF L0 n
  ε := (finLayers L0 0).π

/-- The assembled complex of finite layers is exact. -/
theorem buildFinResolution_isExact (L0 : FinLayer R) :
    (buildFinResolution L0).IsExact := by
  exact ⟨(finLayers L0 0).hπ, ddF_range L0 0,
    fun n => (ddF_range L0 (n + 1)).trans (ddF_ker L0 n).symm⟩

/-- Every term of the assembled complex of finite layers is finite free. -/
theorem buildFinResolution_isFiniteFree (L0 : FinLayer R) :
    (buildFinResolution L0).IsFiniteFree :=
  fun n => ⟨(finLayers L0 n).freeF, (finLayers L0 n).finF⟩

end FreeResolutionConstruction

open FreeResolutionConstruction in
/-- **(Existence of a free resolution.)** For any commutative ring `R` and any
`R`-module `M`, there exists an exact complex of `R`-modules
`... → F₂ → F₁ → F₀ → M → 0` in which every `Fᵢ` is free. -/
@[stacks 00LP "(1)"]
theorem exists_free_resolution
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] :
    ∃ P : FreeResolutionData R M, P.IsExact ∧ P.IsFree :=
  ⟨buildResolution (coverLayer (R := R) M),
    buildResolution_isExact _, buildResolution_isFree _⟩

open FreeResolutionConstruction in
/-- **(Finite free resolution in the Noetherian finite case.)** If `R` is a Noetherian
commutative ring and `M` is a finite `R`-module, then there exists an exact complex of
`R`-modules `... → F₂ → F₁ → F₀ → M → 0` in which every `Fᵢ` is finite free. -/
@[stacks 00LP "(2)",
  ega "0 11.9.2" "special case",
  ega "IV 12.3.2" "(i), special case",
  sga "2 VIII 1.2" "partial",
  sga "4 IX 2.3" "partial",
  sga "6 VI 1.6" "partial"]
theorem exists_finite_free_resolution
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ P : FreeResolutionData R M, P.IsExact ∧ P.IsFiniteFree :=
  ⟨buildFinResolution (coverFinLayer (R := R) M),
    buildFinResolution_isExact _, buildFinResolution_isFiniteFree _⟩
