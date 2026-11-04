module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.Homology.TorAmplitude.Defs
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Flat.UniversallyInjectiveLocalize
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degreewise flatness chase of a bounded below complex

This file is the module-theoretic half of the proof of [stacks 0E2F] (2).  Given the bounded
below complex `E^•` of `R`-flat finitely presented `B`-modules produced by [stacks 0E1U], the
source argues degree by degree: it puts `Q^n = Coker(E^{n-1} → E^n)`, knows
`H^n(E^• ⊗_R κ(𝔭)) = 0` for every prime `𝔭` of `R` (the Noetherian case of the clause read at
the residue fields), chases diagrams to see that `Q^n ⊗_R κ(𝔭) → E^{n+1} ⊗_R κ(𝔭)` is injective,
applies [stacks 00ME] at each prime of `B` to conclude that `Q^n` is `R`-flat and
`Q^n → E^{n+1}` is `R`-universally injective, and reads off `H^n(E^• ⊗_R R') = 0` for *every*
ring map `R → R'`.

This is the bounded below mirror of [stacks 0653],
`StacksDraft.TorAmplitude.cokernel_flat_of_torAmplitude`.  The two statements have the same
conclusion — a cokernel of the complex is `R`-flat — but they cannot share a proof.  0653 is
stated for a complex bounded *above*, where a complex of flats is K-flat ([stacks 064K],
`CochainComplex.KFlat.kFlat_of_flat`) and therefore computes the derived tensor product, so that
derived Tor amplitude gives termwise exactness after tensoring with *every* module.  A bounded
below complex of `R`-flat modules is not K-flat, the filtration that would reduce it to the
bounded case running the wrong way, and no derived hypothesis is available; the source instead
tests only against the residue fields `κ(𝔭)` and pays for that with the local criterion
[stacks 00ME], which is why finiteness over `B` and Noetherianness of `B` appear here and not in
0653.

## Main results

* `StacksDraft.DegreewiseChase.exact_iff_injective_of_isCokernel` — the diagram chase: a
  three-term complex `M₀ → M₁ → M₂` is exact at `M₁` exactly when the induced map out of the
  cokernel of `M₀ → M₁` is injective.  This is the step the source calls "chasing diagrams",
  and it is also what turns flatness of the cokernel back into the vanishing of cohomology.
* `StacksDraft.DegreewiseChase.exact_rTensor_iff_injective_rTensor` — the same equivalence after
  tensoring with an arbitrary `R`-module `N`, which is the form in which the chase both consumes
  its hypothesis (at `N = κ(𝔭)`) and delivers its conclusion (at `N = R'`).
* `StacksDraft.DegreewiseChase.exact_rTensor_of_flat_quotient` — if the cokernel `Q` of
  `M₀ → M₁` injects into `M₂` with `R`-flat quotient, then `M₀ ⊗ N → M₁ ⊗ N → M₂ ⊗ N` is exact
  at `M₁ ⊗ N` for *every* `R`-module `N`.
* `StacksDraft.DegreewiseChase.injective_rTensor_quotient_iff_le_comap` and
  `StacksDraft.DegreewiseChase.injective_mapQ_iff_injective_rTensor_quotient` — the fibre
  `Q/𝔪Q → M₂/𝔪M₂` of a map is injective exactly when the map becomes injective after
  `⊗_R R/𝔪`; this is the translation between the form [stacks 00ME] is stated in and the form
  the chase produces.
* `StacksDraft.DegreewiseChase.injective_and_flat_of_injective_rTensor_residue` —
  [stacks 00ME] run at a three-term complex over a local base: the whole conclusion of one
  degree of the chase, over a local ring.
* `StacksDraft.DegreewiseChase.flat_of_injective_rTensor_residueField` and
  `StacksDraft.DegreewiseChase.injective_rTensor_of_injective_rTensor_residueField` — the chase
  globalised over an arbitrary base: from the residue-field test at every prime of `R`, the
  cokernel is `R`-flat and injects universally into the next term.
* `StacksDraft.DegreewiseChase.flat_cokernel_and_exact_rTensor_of_exact_rTensor_residueField` —
  the two previous results assembled into the statement the source's argument proves at each
  degree: exactness after `⊗_R κ(𝔭)` at every prime goes in, flatness of the cokernel and
  exactness after `⊗_R N` for every `N` come out.  **This is the bounded below mirror of
  [stacks 0653].**
* `StacksDraft.DegreewiseChase.exactAt_tensorModuleRight_iff_exact_rTensor` and
  `StacksDraft.DegreewiseChase.isZero_homology_tensorModuleRight_iff_exact_rTensor` — the bridge
  to a complex: the cohomology of `K ⊗_R M` vanishes in degree `n` exactly when the three-term
  piece `K^{n-1} ⊗ M → K^n ⊗ M → K^{n+1} ⊗ M` is exact in the middle, so that a
  `CochainComplex (ModuleCat R) ℤ` may be fed to the results above one degree at a time.
* `StacksDraft.DegreewiseChase.flat_ker_of_flat_cokernel` and
  `StacksDraft.DegreewiseChase.injective_and_exact_rTensor_ker_of_flat_cokernel` — the source's
  degree-zero step, which the degrees `n ≠ 0` feed: `Z^0 = Ker(E^0 → E^1)` is `R`-flat and
  `Z^0 ⊗_R R' = Ker(E^0 ⊗_R R' → E^1 ⊗_R R')` for every `R → R'`, once `Q^1` is `R`-flat.  With
  right exactness of the tensor product this is what makes
  `H^0(E^• ⊗_R R') = H^0(E^•) ⊗_R R'`.

## Implementation notes

The cokernel is not formed; it is *given*, as a surjection `c : M₁ →ₗ[S] Q` with
`Function.Exact f c`.  Every consumer has some presentation of it to hand — a categorical
`cokernel`, a `Submodule.mkQ`, or the localisation of one of those — and the abstract form
applies to all of them without transport.

The residue field `κ(𝔭)` is spelled `Localization.AtPrime 𝔭 ⧸ IsLocalRing.maximalIdeal _`
rather than `IsLocalRing.ResidueField (Localization.AtPrime 𝔭)`, which is a `def` wrapping that
quotient: the quotient is the form in which [stacks 00ME] and `LinearMap.ker_tensorProductMk`
read it, and no instance has to be transported across the wrapper.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
* [Stacks Project, Tag 00ME](https://stacks.math.columbia.edu/tag/00ME)
* [Stacks Project, Tag 00HM](https://stacks.math.columbia.edu/tag/00HM)
-/

@[expose] public section

open scoped TensorProduct

universe v

namespace StacksDraft.DegreewiseChase

/-! ### Chasing diagrams -/

section Chase

variable {R : Type*} [CommRing R]
  {M₀ M₁ M₂ Q : Type*} [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup Q]
  [Module R M₀] [Module R M₁] [Module R M₂] [Module R Q]

/-- **The diagram chase of [stacks 0E2F] (2).**  Let `M₀ →[f] M₁ →[g] M₂` be a three-term
complex and let `c : M₁ → Q` present `Q` as the cokernel of `f`, so that `u : Q → M₂` is the
map induced by `g`.  Then the complex is exact at `M₁` if and only if `u` is injective.

The source uses this twice: once forwards, to turn the vanishing `H^n(E^• ⊗_R κ(𝔭)) = 0` into
injectivity of `Q^n ⊗_R κ(𝔭) → E^{n+1} ⊗_R κ(𝔭)`, and once backwards, to turn universal
injectivity of `Q^n → E^{n+1}` into the vanishing of `H^n(E^• ⊗_R R')`. -/
theorem exact_iff_injective_of_isCokernel
    {f : M₀ →ₗ[R] M₁} {g : M₁ →ₗ[R] M₂} {c : M₁ →ₗ[R] Q} {u : Q →ₗ[R] M₂}
    (hc : Function.Surjective c) (hfc : Function.Exact f c) (hu : u ∘ₗ c = g) :
    Function.Exact f g ↔ Function.Injective u := by
  constructor
  · intro h
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := hc x
    obtain ⟨z, rfl⟩ := (h y).mp (by rwa [← hu])
    exact hfc.apply_apply_eq_zero z
  · intro h y
    constructor
    · intro hgy
      refine (hfc y).mp (h ?_)
      rwa [map_zero, ← LinearMap.comp_apply, hu]
    · rintro ⟨z, rfl⟩
      rw [← hu, LinearMap.comp_apply, hfc.apply_apply_eq_zero z, map_zero]

/-- If `u : Q → M₂` is injective with `R`-flat cokernel `w : M₂ → W`, then `u ⊗ id_N` is injective
for every `R`-module `N` ([stacks 00HL]). -/
private theorem injective_rTensor_of_flat_quotient
    {Q M₂ W : Type*} [AddCommGroup Q] [AddCommGroup M₂] [AddCommGroup W]
    [Module R Q] [Module R M₂] [Module R W] [Module.Flat R W]
    {u : Q →ₗ[R] M₂} (huinj : Function.Injective u)
    {w : M₂ →ₗ[R] W} (hw : Function.Surjective w) (huw : Function.Exact u w)
    (N : Type*) [AddCommGroup N] [Module R N] :
    Function.Injective (LinearMap.rTensor N u) :=
  (LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp (flat_tor_zero (N := N) u w huinj huw hw).1

/-- **"In particular `H^n(E^• ⊗_R R') = 0` for any ring map `R → R'`."**  Let
`M₀ →[f] M₁ →[g] M₂` be a three-term complex, let `c : M₁ → Q` present `Q` as the cokernel of
`f`, let `u : Q → M₂` be the induced map and suppose `u` is injective with `R`-flat cokernel.
Then `M₀ ⊗ N → M₁ ⊗ N → M₂ ⊗ N` is exact at `M₁ ⊗ N` for every `R`-module `N`.

Tensoring is right exact, so `c ⊗ id` presents `Q ⊗ N` as the cokernel of `f ⊗ id`; flatness of
the cokernel of `u` makes `u ⊗ id` injective ([stacks 00HL]); and
`StacksDraft.DegreewiseChase.exact_iff_injective_of_isCokernel` reads that back as exactness. -/
@[ega "0 6.1.2" "more general"]
theorem exact_rTensor_of_flat_quotient
    {f : M₀ →ₗ[R] M₁} {g : M₁ →ₗ[R] M₂} {c : M₁ →ₗ[R] Q} {u : Q →ₗ[R] M₂}
    (hc : Function.Surjective c) (hfc : Function.Exact f c) (hu : u ∘ₗ c = g)
    (huinj : Function.Injective u)
    {W : Type*} [AddCommGroup W] [Module R W] [Module.Flat R W]
    (w : M₂ →ₗ[R] W) (hw : Function.Surjective w) (huw : Function.Exact u w)
    (N : Type*) [AddCommGroup N] [Module R N] :
    Function.Exact (LinearMap.rTensor N f) (LinearMap.rTensor N g) := by
  refine (exact_iff_injective_of_isCokernel (u := LinearMap.rTensor N u)
    (LinearMap.rTensor_surjective N hc) (_root_.rTensor_exact N hfc hc) ?_).mpr ?_
  · rw [← LinearMap.rTensor_comp, hu]
  · exact injective_rTensor_of_flat_quotient huinj hw huw N

/-- **The chase after a base change.**
`StacksDraft.DegreewiseChase.exact_iff_injective_of_isCokernel` applied to the complex tensored
with an arbitrary `R`-module `N`: tensoring is right exact, so
`c ⊗ id_N` still presents `Q ⊗ N` as the cokernel of `f ⊗ id_N`, and exactness of
`M₀ ⊗ N → M₁ ⊗ N → M₂ ⊗ N` at the middle is injectivity of `u ⊗ id_N`.

This is the equivalence the source uses in both directions: at `N = κ(𝔭)` to extract the
hypothesis of [stacks 00ME], and at `N = R'` to read off `H^n(E^• ⊗_R R') = 0`. -/
theorem exact_rTensor_iff_injective_rTensor
    {f : M₀ →ₗ[R] M₁} {g : M₁ →ₗ[R] M₂} {c : M₁ →ₗ[R] Q} {u : Q →ₗ[R] M₂}
    (hc : Function.Surjective c) (hfc : Function.Exact f c) (hu : u ∘ₗ c = g)
    (N : Type*) [AddCommGroup N] [Module R N] :
    Function.Exact (LinearMap.rTensor N f) (LinearMap.rTensor N g) ↔
      Function.Injective (LinearMap.rTensor N u) :=
  exact_iff_injective_of_isCokernel (LinearMap.rTensor_surjective N hc)
    (_root_.rTensor_exact N hfc hc) (by rw [← LinearMap.rTensor_comp, hu])

/-- The cokernel `Q` itself is `R`-flat once `M₂` and the quotient `W = M₂/u(Q)` are: this is
the second half of [stacks 00HM] at the short exact sequence `0 → Q → M₂ → W → 0`. -/
theorem flat_of_flat_quotient
    {u : Q →ₗ[R] M₂} (huinj : Function.Injective u) [Module.Flat R M₂]
    {W : Type*} [AddCommGroup W] [Module R W] [Module.Flat R W]
    (w : M₂ →ₗ[R] W) (hw : Function.Surjective w) (huw : Function.Exact u w) :
    Module.Flat R Q :=
  flat_of_flat_of_flat_quotient u w huinj huw hw

/-! ### The degree-zero step: the kernel -/

section Kernel

variable {W : Type*} [AddCommGroup W] [Module R W]

/-- The inclusion of the image of `g` is exact with any `w` that is exact with `g`. -/
private theorem exact_subtype_range {g : M₁ →ₗ[R] M₂} {w : M₂ →ₗ[R] W}
    (hgw : Function.Exact g w) : Function.Exact (LinearMap.range g).subtype w := by
  rw [LinearMap.exact_iff, Submodule.range_subtype]
  exact LinearMap.exact_iff.mp hgw

/-- Corestricting `g` to its range keeps it exact with any `z` that is exact with `g`. -/
private theorem exact_rangeRestrict {Z : Type*} [AddCommGroup Z] [Module R Z]
    {z : Z →ₗ[R] M₁} {g : M₁ →ₗ[R] M₂} (hzg : Function.Exact z g) :
    Function.Exact z g.rangeRestrict := by
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict]
  exact LinearMap.exact_iff.mp hzg

/-- The image `I = Im(g) = Ker(w)` is `R`-flat when `M₁` and the cokernel `W` are: the second
half of [stacks 00HM] at `0 → I → M₁ → W → 0`. -/
private theorem flat_range_of_flat_cokernel (g : M₁ →ₗ[R] M₂) {w : M₂ →ₗ[R] W}
    (hgw : Function.Exact g w) (hw : Function.Surjective w)
    [Module.Flat R M₂] [Module.Flat R W] :
    Module.Flat R (LinearMap.range g) :=
  flat_of_flat_of_flat_quotient (LinearMap.range g).subtype w
    Subtype.val_injective (exact_subtype_range hgw) hw

/-- **"`Z^0` is `R`-flat", the degree-zero step of the chase of [stacks 0E2F] (2).**  Let
`Z →[z] M₁ →[g] M₂ →[w] W` be exact, with `z` injective and `w` surjective — so `Z = Ker(g)` and
`W = Coker(g)` — and let `M₁`, `M₂` and `W` be `R`-flat.  Then `Z` is `R`-flat.

In the source `Z = Z^0 = Ker(E^0 → E^1)` and `W = Q^1 = Coker(E^0 → E^1)`, whose flatness is the
output of the chase at degree `1`; the four-term exact sequence
`0 → Z^0 → E^0 → E^1 → Q^1 → 0` is broken at the image, which is flat by
[stacks 00HM] because `E^1` and `Q^1` are, and then `Z^0` is flat by [stacks 00HM] again. -/
theorem flat_ker_of_flat_cokernel {Z : Type*} [AddCommGroup Z] [Module R Z]
    {z : Z →ₗ[R] M₁} {g : M₁ →ₗ[R] M₂} {w : M₂ →ₗ[R] W}
    (hz : Function.Injective z) (hzg : Function.Exact z g)
    (hgw : Function.Exact g w) (hw : Function.Surjective w)
    [Module.Flat R M₁] [Module.Flat R M₂] [Module.Flat R W] :
    Module.Flat R Z := by
  have := flat_range_of_flat_cokernel g hgw hw
  exact flat_of_flat_of_flat_quotient z g.rangeRestrict hz (exact_rangeRestrict hzg)
    g.surjective_rangeRestrict

/-- **"`Z^0 ⊗_R R' = Ker(E^0 ⊗_R R' → E^1 ⊗_R R')` for all `R → R'`".**  In the situation of
`StacksDraft.DegreewiseChase.flat_ker_of_flat_cokernel`, `z ⊗ id_N` is injective with image the
kernel of `g ⊗ id_N`, for every `R`-module `N`.

This is what turns the degree-zero cohomology of the tensored complex into a tensor product:
`H^0(E^• ⊗_R R')` is the cokernel of `E^{-1} ⊗ R' → Z^0 ⊗ R'`, which by right exactness of the
tensor product is `H^0(E^•) ⊗_R R'`. -/
theorem injective_and_exact_rTensor_ker_of_flat_cokernel {Z : Type*} [AddCommGroup Z]
    [Module R Z] {z : Z →ₗ[R] M₁} {g : M₁ →ₗ[R] M₂} {w : M₂ →ₗ[R] W}
    (hz : Function.Injective z) (hzg : Function.Exact z g)
    (hgw : Function.Exact g w) (hw : Function.Surjective w)
    [Module.Flat R M₂] [Module.Flat R W]
    (N : Type*) [AddCommGroup N] [Module R N] :
    Function.Injective (LinearMap.rTensor N z) ∧
      Function.Exact (LinearMap.rTensor N z) (LinearMap.rTensor N g) := by
  have hI := flat_range_of_flat_cokernel g hgw hw
  obtain ⟨h1, h2, -⟩ :=
    flat_tor_zero (N := N) z g.rangeRestrict hz (exact_rangeRestrict hzg)
      g.surjective_rangeRestrict
  have hsub : Function.Injective (LinearMap.rTensor N (LinearMap.range g).subtype) :=
    injective_rTensor_of_flat_quotient Subtype.val_injective hw (exact_subtype_range hgw) N
  have h2' : Function.Exact (LinearMap.rTensor N z) (LinearMap.rTensor N g.rangeRestrict) :=
    (LinearMap.rTensor_exact_iff_lTensor_exact N).mpr h2
  have hgfac : (LinearMap.range g).subtype ∘ₗ g.rangeRestrict = g :=
    LinearMap.subtype_comp_codRestrict g g.range (LinearMap.mem_range_self g)
  refine ⟨(LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp h1, ?_⟩
  rw [LinearMap.exact_iff] at h2' ⊢
  rw [← h2', ← hgfac, LinearMap.rTensor_comp]
  exact LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hsub)

end Kernel

end Chase

/-! ### The fibre of a map, as a tensor product -/

section Fibre

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]

/-- **The fibre test, in the two forms the chase and [stacks 00ME] use.**  For an ideal `I` of
`R` and a map `u : M → N`, the map `u ⊗ id_{R/I}` is injective if and only if
`u⁻¹(I·N) ⊆ I·M`, which is injectivity of the induced map `M/IM → N/IN` of fibres
(`StacksDraft.DegreewiseChase.injective_mapQ_iff_injective_rTensor_quotient`). -/
theorem injective_rTensor_quotient_iff_le_comap (u : M →ₗ[R] N) (I : Ideal R) :
    Function.Injective (LinearMap.rTensor (R ⧸ I) u) ↔
      (I • (⊤ : Submodule R N)).comap u ≤ I • (⊤ : Submodule R M) := by
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · rw [← LinearMap.ker_tensorProductMk (I := I) (Q := M), LinearMap.mem_ker]
    refine h ?_
    rwa [map_zero, show (LinearMap.lTensor (R ⧸ I) u) (TensorProduct.mk R (R ⧸ I) M 1 x)
        = TensorProduct.mk R (R ⧸ I) N 1 (u x) from by simp, ← LinearMap.mem_ker,
      LinearMap.ker_tensorProductMk]
  · rw [injective_iff_map_eq_zero]
    intro z hz
    have hsurj : Function.Surjective (TensorProduct.mk R (R ⧸ I) M 1) := by
      rw [← TensorProduct.quotTensorEquivQuotSMul_symm_comp_mkQ]
      exact (TensorProduct.quotTensorEquivQuotSMul M I).symm.surjective.comp
        (Submodule.mkQ_surjective _)
    obtain ⟨y, rfl⟩ := hsurj z
    rw [show (LinearMap.lTensor (R ⧸ I) u) (TensorProduct.mk R (R ⧸ I) M 1 y)
        = TensorProduct.mk R (R ⧸ I) N 1 (u y) from by simp, ← LinearMap.mem_ker,
      LinearMap.ker_tensorProductMk] at hz
    rw [← LinearMap.mem_ker, LinearMap.ker_tensorProductMk]
    exact h hz

/-- The fibre form of `StacksDraft.DegreewiseChase.injective_rTensor_quotient_iff_le_comap`:
`u ⊗ id_{R/I}` is injective exactly when the induced map `M/IM → N/IN` on fibres is, which is
the hypothesis of [stacks 00ME]. -/
theorem injective_mapQ_iff_injective_rTensor_quotient (u : M →ₗ[R] N) (I : Ideal R) :
    Function.Injective ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) u
        (Submodule.smul_top_le_comap_smul_top I u)) ↔
      Function.Injective (LinearMap.rTensor (R ⧸ I) u) := by
  rw [injective_rTensor_quotient_iff_le_comap,
    Stacks.Flatness.FibreNonZeroDivisor.mapQ_injective_iff]

end Fibre

/-! ### [Stacks 00ME] at a three-term complex over a local base -/

section LocalCase

open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
  {Q M₂ : Type*} [AddCommGroup Q] [Module R Q]
  [AddCommGroup M₂] [Module R M₂] [Module.Flat R M₂]

/-- **One degree of the chase, over a local base.**  Let `R → S` be a local homomorphism of
local rings with `S` Noetherian, let `M₂` be a flat `R`-module, let `Q` be a finite `S`-module
and let `u : Q → M₂` be `R`-linear.  If `u ⊗ id_{κ(R)}` is injective then `u` is injective,
`M₂/u(Q)` is `R`-flat and `Q` is `R`-flat.

This is [stacks 00ME] with its hypothesis read as the chase produces it — injectivity after
tensoring with the residue field, rather than injectivity of the induced map of fibres — plus
the flatness of `Q` itself, which the source also records and which is the second half of
[stacks 00HM] at `0 → Q → M₂ → M₂/u(Q) → 0`. -/
theorem injective_and_flat_of_injective_rTensor_residue (S : Type*) [CommRing S] [IsLocalRing S]
    [Algebra R S] [IsLocalHom (algebraMap R S)] [IsNoetherianRing S]
    [Module S Q] [IsScalarTower R S Q] [Module.Finite S Q] (u : Q →ₗ[R] M₂)
    (hu : Function.Injective (LinearMap.rTensor (R ⧸ maximalIdeal R) u)) :
    Function.Injective u ∧ Module.Flat R (M₂ ⧸ LinearMap.range u) ∧ Module.Flat R Q := by
  obtain ⟨hinj, hflat⟩ :=
    Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing
      (S := S) u ((injective_mapQ_iff_injective_rTensor_quotient u (maximalIdeal R)).mpr hu)
  exact ⟨hinj, hflat, flat_of_flat_quotient hinj (LinearMap.range u).mkQ
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range u)⟩

end LocalCase

/-! ### The chase globalised: the bounded below mirror of [stacks 0653] -/

/-- The residue field `κ(𝔭)` at a prime of `R`, as the quotient of `R_𝔭` by its maximal ideal.
This is the test module the source's chase uses.

It is the same field as `Ideal.ResidueField 𝔭` and as the library's `ResidueFieldAtPrime R 𝔭`,
which are `IsLocalRing.ResidueField (Localization.AtPrime 𝔭)`; the quotient is spelled out
because `LinearMap.ker_tensorProductMk` and [stacks 00ME] read the test module as `R_𝔭 ⧸ I` for
an ideal `I`, and `IsLocalRing.ResidueField` is a plain `def` across which the module instances
would have to be transported. -/
@[ega "0 21.9.8", ega "I 1.1.1"]
abbrev ResidueFieldAt (R : Type*) [CommRing R] (p : Ideal R) [p.IsPrime] : Type _ :=
  Localization.AtPrime p ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime p)

section Global

open IsLocalRing Stacks.UniversalInjectivity Stacks.UniversalInjectivity.LocalizationCriteria

universe t

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing S]
  {Q M₂ : Type*}
  [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q] [Module.Finite S Q]
  [AddCommGroup M₂] [Module R M₂] [Module S M₂] [IsScalarTower R S M₂] [Module.Flat R M₂]

omit [IsNoetherianRing S] [Module.Finite S Q] [Module.Flat R M₂] in
/-- The residue-field test survives localisation at a prime `𝔮` of `S` and the change of base
ring from `R` to `R_𝔭`, `𝔭 = 𝔮 ∩ R`.  Localisation of modules is exact, which carries the
injectivity over
(`Stacks.UniversalInjectivity.LocalizationCriteria.localizedMapR_rTensor_injective`), and
tensoring two `R_𝔭`-modules over `R` or over `R_𝔭` gives the same thing
(`IsLocalization.moduleTensorEquiv`). -/
private theorem injective_rTensor_residue_localizedMapRp (u : Q →ₗ[S] M₂)
    (q : Ideal S) [q.IsPrime]
    (hres : Function.Injective
      (LinearMap.rTensor (ResidueFieldAt R (q.under R)) (u.restrictScalars R))) :
    Function.Injective
      (LinearMap.rTensor (ResidueFieldAt R (q.under R)) (localizedMapRp (R := R) u q)) := by
  set e₁ := IsLocalization.moduleTensorEquiv (q.under R).primeCompl
    (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl Q)
    (ResidueFieldAt R (q.under R))
  set e₂ := IsLocalization.moduleTensorEquiv (q.under R).primeCompl
    (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl M₂)
    (ResidueFieldAt R (q.under R))
  have nat : (e₂ : _ → _) ∘ (LinearMap.rTensor (ResidueFieldAt R (q.under R))
        (localizedMapRp (R := R) u q)) =
      (LinearMap.rTensor (ResidueFieldAt R (q.under R)) (localizedMapR (R := R) u q)) ∘ e₁ := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x k => rfl
    | add a b ha hb =>
      simp only [Function.comp_apply, map_add] at ha hb ⊢
      rw [ha, hb]
  refine Function.Injective.of_comp (f := (e₂ : _ → _)) ?_
  rw [nat]
  exact (localizedMapR_rTensor_injective (R := R) u q _ hres).comp e₁.injective

/-- The per-prime output of the chase: at every prime `𝔮` of `S`, [stacks 00ME] applies to the
localised map over the local ring `R_𝔭`, `𝔭 = 𝔮 ∩ R`. -/
private theorem localized_injective_and_flat (u : Q →ₗ[S] M₂)
    (hres : ∀ (p : Ideal R) [p.IsPrime], Function.Injective
      (LinearMap.rTensor (ResidueFieldAt R p) (u.restrictScalars R)))
    (q : Ideal S) [q.IsPrime] :
    Function.Injective (localizedMapRp (R := R) u q) ∧
      Module.Flat (Localization.AtPrime (q.under R))
        (LocalizedModule q.primeCompl M₂ ⧸ LinearMap.range (localizedMapRp (R := R) u q)) ∧
      Module.Flat (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl Q) := by
  have : Module.Flat (Localization.AtPrime (q.under R)) (LocalizedModule q.primeCompl M₂) :=
    flat_localizedModule_atPrime q
  exact injective_and_flat_of_injective_rTensor_residue (Localization.AtPrime q)
    (localizedMapRp (R := R) u q)
    (injective_rTensor_residue_localizedMapRp u q (hres (q.under R)))

/-- **The cokernel is flat: the bounded below mirror of [stacks 0653], in its bare form.**  Let
`R → S` be a ring map with `S` Noetherian, let `M₂` be an `S`-module flat over `R`, let `Q` be a
finite `S`-module and let `u : Q → M₂` be `S`-linear.  If `u ⊗ id_{κ(𝔭)}` is injective for every
prime `𝔭` of `R`, then `Q` is flat over `R`.

Flatness over `R` of an `S`-module is local on `S` (`Module.flat_of_isLocalized_maximal`), and at
each prime of `S` it is [stacks 00ME] over `R_𝔭`. -/
theorem flat_of_injective_rTensor_residueField (u : Q →ₗ[S] M₂)
    (hres : ∀ (p : Ideal R) [p.IsPrime], Function.Injective
      (LinearMap.rTensor (ResidueFieldAt R p) (u.restrictScalars R))) :
    Module.Flat R Q := by
  refine Module.flat_of_isLocalized_maximal S Q (fun P _ => LocalizedModule P.primeCompl Q)
    (fun P _ => LocalizedModule.mkLinearMap P.primeCompl Q) ?_
  intro P _
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime (P.under R))
    (P.under R).primeCompl _).mp (localized_injective_and_flat u hres P).2.2

/-- **The map is universally injective: the other half of the mirror of [stacks 0653].**  In the
situation of `StacksDraft.DegreewiseChase.flat_of_injective_rTensor_residueField`, `u ⊗ id_N` is
injective for *every* `R`-module `N`, which is the source's "`Q^n → E^{n+1}` is `R`-universally
injective".

Universal injectivity is local on `S` by [stacks 05CL],
`Stacks.UniversalInjectivity.LocalizationCriteria.universallyInjective_of_localizedMapRp`, and at
each prime of `S` it follows from [stacks 00ME] through [stacks 00HL]: the quotient
`M₂_𝔮/u(Q_𝔮)` is `R_𝔭`-flat, so the sequence stays exact after every tensor product. -/
theorem injective_rTensor_of_injective_rTensor_residueField (u : Q →ₗ[S] M₂)
    (hres : ∀ (p : Ideal R) [p.IsPrime], Function.Injective
      (LinearMap.rTensor (ResidueFieldAt R p) (u.restrictScalars R)))
    (N : Type t) [AddCommGroup N] [Module R N] :
    Function.Injective (LinearMap.rTensor N (u.restrictScalars R)) := by
  have hglobal : UniversallyInjective.{t} (u.restrictScalars R) := by
    refine universallyInjective_of_localizedMapRp u ?_
    intro q _ N' _ _
    obtain ⟨hinj, _, -⟩ := localized_injective_and_flat u hres q
    exact injective_rTensor_of_flat_quotient hinj (Submodule.mkQ_surjective _)
      (LinearMap.exact_map_mkQ_range _) N'
  exact hglobal N

/-- **The bounded below mirror of [stacks 0653].**  Let `R → S` be a ring map with `S`
Noetherian and let `M₀ →[f] M₁ →[g] M₂` be a three-term complex of `S`-modules with `M₂` flat
over `R`, presented with its cokernel `c : M₁ → Q` and the induced `u : Q → M₂`, and with `Q`
finite over `S`.  If the complex stays exact at `M₁` after `⊗_R κ(𝔭)` for every prime `𝔭` of
`R`, then `Q` is `R`-flat and the complex stays exact at `M₁` after `⊗_R N` for **every**
`R`-module `N`.

This is the statement the source's degree-by-degree argument for [stacks 0E2F] (2) proves at
each degree `n ≠ 0` of the bounded below complex `E^•` of [stacks 0E1U], with `M₀ = E^{n-1}`,
`M₁ = E^n`, `M₂ = E^{n+1}`, `Q = Q^n` and `S = A ⊗_R A`: the vanishing
`H^n(E^• ⊗_R κ(𝔭)) = 0` goes in and `H^n(E^• ⊗_R R') = 0` for every `R → R'` comes out,
together with the `R`-flatness of `Q^n`.

It is the mirror of [stacks 0653] for a complex bounded below rather than above, and the two
proofs have nothing in common.  0653 tests against *every* module (which a bounded above
complex of flats may be assumed to do, being K-flat, so that derived Tor amplitude suffices) and
uses exactness one degree *below* the cokernel it concludes about; here only the residue fields
are available as test modules and the gap is bridged by the local criterion [stacks 00ME], which
reads exactness at the same degree and is what makes the finiteness of `Q` over the Noetherian
`S` indispensable. -/
theorem flat_cokernel_and_exact_rTensor_of_exact_rTensor_residueField
    {M₀ M₁ : Type*} [AddCommGroup M₀] [Module R M₀] [Module S M₀] [IsScalarTower R S M₀]
    [AddCommGroup M₁] [Module R M₁] [Module S M₁] [IsScalarTower R S M₁]
    {f : M₀ →ₗ[S] M₁} {g : M₁ →ₗ[S] M₂} {c : M₁ →ₗ[S] Q} {u : Q →ₗ[S] M₂}
    (hc : Function.Surjective c) (hfc : Function.Exact f c) (hu : u ∘ₗ c = g)
    (hres : ∀ (p : Ideal R) [p.IsPrime],
      Function.Exact (LinearMap.rTensor (ResidueFieldAt R p) (f.restrictScalars R))
        (LinearMap.rTensor (ResidueFieldAt R p) (g.restrictScalars R))) :
    Module.Flat R Q ∧ ∀ (N : Type t) [AddCommGroup N] [Module R N],
      Function.Exact (LinearMap.rTensor N (f.restrictScalars R))
        (LinearMap.rTensor N (g.restrictScalars R)) := by
  have hc' : Function.Surjective (c.restrictScalars R) := hc
  have hfc' : Function.Exact (f.restrictScalars R) (c.restrictScalars R) := hfc
  have hu' : (u.restrictScalars R) ∘ₗ (c.restrictScalars R) = g.restrictScalars R :=
    LinearMap.ext fun x => LinearMap.congr_fun hu x
  have hkey : ∀ (p : Ideal R) [p.IsPrime], Function.Injective
      (LinearMap.rTensor (ResidueFieldAt R p) (u.restrictScalars R)) :=
    fun p _ => (exact_rTensor_iff_injective_rTensor hc' hfc' hu' _).mp (hres p)
  exact ⟨flat_of_injective_rTensor_residueField u hkey,
    fun N _ _ => (exact_rTensor_iff_injective_rTensor hc' hfc' hu' N).mpr
      (injective_rTensor_of_injective_rTensor_residueField u hkey N)⟩

end Global

/-! ### The bridge to a complex -/

section ComplexBridge

open CategoryTheory CategoryTheory.Limits StacksDraft.TorAmplitude

/-- **The three-term piece of a termwise tensor product complex.**  For a cochain complex `K` of
`R`-modules and an `R`-module `M`, the complex `K ⊗_R M` is exact in degree `n` exactly when
`K^{n-1} ⊗ M → K^n ⊗ M → K^{n+1} ⊗ M` is exact in the middle as a sequence of linear maps.

This is the translation between the cohomology of a `CochainComplex (ModuleCat R) ℤ` and the
three-term statements of this file, so that a complex may be fed to the chase one degree at a
time. -/
theorem exactAt_tensorModuleRight_iff_exact_rTensor {R : Type*} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (M : ModuleCat.{v} R) (n : ℤ) :
    (((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt n ↔
      Function.Exact (LinearMap.rTensor M (K.d (n - 1) n).hom)
        (LinearMap.rTensor M (K.d n (n + 1)).hom) := by
  have hprev : (ComplexShape.up ℤ).prev n = n - 1 := by simp [CochainComplex.prev]
  have hnext : (ComplexShape.up ℤ).next n = n + 1 := by simp [CochainComplex.next]
  rw [HomologicalComplex.exactAt_iff, ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  show Function.Exact (LinearMap.rTensor M (K.d ((ComplexShape.up ℤ).prev n) n).hom)
      (LinearMap.rTensor M (K.d n ((ComplexShape.up ℤ).next n)).hom) ↔ _
  rw [hprev, hnext]

/-- The cohomology of `K ⊗_R M` vanishes in degree `n` exactly when
`K^{n-1} ⊗ M → K^n ⊗ M → K^{n+1} ⊗ M` is exact in the middle. -/
theorem isZero_homology_tensorModuleRight_iff_exact_rTensor {R : Type*} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (M : ModuleCat.{v} R) (n : ℤ) :
    IsZero ((((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n)
      ↔ Function.Exact (LinearMap.rTensor M (K.d (n - 1) n).hom)
        (LinearMap.rTensor M (K.d n (n + 1)).hom) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    exactAt_tensorModuleRight_iff_exact_rTensor]

end ComplexBridge

end StacksDraft.DegreewiseChase

end
