module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Length
public import StacksFrontier.RingTheory.Dualizing.ExtFiniteLengthBound
public import StacksFrontier.RingTheory.Dualizing.ExtRegularElement
public import StacksFrontier.RingTheory.Dualizing.ExtShortExact
public import StacksFrontier.RingTheory.Dualizing.ExtVanishingRange
public import StacksFrontier.RingTheory.Length.SmulPowQuotient

/-!
# Kollár's length bound for the cokernel of a map of depth-two modules

Let `(A, 𝔪)` be a Noetherian local ring carrying a normalized dualizing complex `ω_A^•`, let
`f ∈ A`, and let `ρ : M → N` be a map of finite `A`-modules with

* `f` a nonzerodivisor on `M` and `ker ρ = fM`,
* `depth_𝔪(M) ≥ 2` and `depth_𝔪(N) ≥ 2`,
* `N / ρ(M)` of finite length.

Write `E = Ext_A^{-2}(M, ω_A^•)` and `B = Ext_A^{-2}(N, ω_A^•)`. This file proves that the
cokernel of `ρ` is no longer than the cokernel of the dual of any map `ν : N → V` that `ρ`
annihilates in the derived sense, i.e. for which `ν ∘ ρ` factors through a module `W` whose
own `Ext^{-2}` into `ω_A^•` vanishes:

`length_A(N / ρ(M)) ≤ length_A(B / Ext^{-2}(ν)(Ext_A^{-2}(V, ω_A^•)))`.

The argument is the chain of identifications that makes up the proof of Stacks tag 0F2B.
Put `Q = N / ρ(M)` and `M/fM` for the quotient of `M` by `f`. Since `ker ρ = fM`, the map `ρ`
factors as an injection `ι : M/fM ↪ N`, so that

`0 → M/fM → N → Q → 0`

is short exact. Now:

* `Q` has finite length, so its dual Ext vanishes in every nonzero degree; `N` has depth at
  least two, so its dual Ext vanishes in degrees `-1` and `0`; and `M` has depth at least two,
  so its dual Ext vanishes in degree `-1`. (All of this is the vanishing range of tag 0DWZ.)
* The vanishing of `Ext^{-2}(Q)` and `Ext^{-1}(Q)` makes `Ext^{-2}(ι)` bijective.
* The vanishing of `Ext^{-1}(N)` and `Ext^{0}(N)` makes the connecting map
  `Ext^{-1}(M/fM) → Ext^{0}(Q)` bijective.
* `length(Q) ≤ length(Ext^0(Q, ω_A^•))`, so `length(Q) ≤ length(Ext^{-1}(M/fM, ω_A^•))`.
* The long exact Ext sequence of `0 → M →^f M → M/fM → 0`, cut down by the vanishing of
  `Ext^{-1}(M)`, identifies `Ext^{-1}(M/fM, ω_A^•)` with `E / fE`; and for `E` of finite length
  `E / fE` has the same length as the `f`-torsion `ker(f · : E → E)`, which the same long exact
  sequence identifies with the image of `Ext^{-2}` of the quotient map `M → M/fM`.
* That image is the image of `Ext^{-2}(ρ)`, because `ρ` is the quotient map followed by `ι` and
  `Ext^{-2}(ι)` is surjective.
* Finally `Ext^{-2}(ρ) ∘ Ext^{-2}(ν) = Ext^{-2}(c) ∘ Ext^{-2}(τ)` vanishes, the middle group
  `Ext_A^{-2}(W, ω_A^•)` being zero, so `Ext^{-2}(ρ)` factors through `B / im Ext^{-2}(ν)` and
  its image is no longer than that quotient.

## Main results

* `Module.length_range_le_length_quotient_range` — if `im h ⊆ ker g` then the image of `g` is no
  longer than the cokernel of `h`.
* `Dualizing.surjective_extConnecting_of_subsingleton` — the connecting map of the sequence
  `0 → M →^f M → M/fM → 0` out of degree `i` is surjective once `Ext^{i+1}(M)` vanishes.
* `Dualizing.length_moduleExtInto_quotSMulTop_eq_length_quotient_smul` — under the same vanishing,
  `Ext^{i+1}(M/fM, K)` and `Ext^i(M, K) / f · Ext^i(M, K)` have the same length.
* `Dualizing.objExtPrecomp_comp_objExtPrecomp_eq_zero_of_subsingleton` — a composite of two
  precomposition maps through a module with vanishing Ext is zero.
* `Dualizing.range_objExtPrecomp_comp_of_surjective` — precomposing with a surjective
  precomposition map does not change the image.
* `Dualizing.length_quotient_range_le_length_quotient_range_objExtPrecomp` — the length bound.

## Implementation notes

The connecting maps of `StacksFrontier.RingTheory.Dualizing.ExtRegularElement` and of
`StacksFrontier.RingTheory.Dualizing.ExtShortExact` go from degree `i` to degree `i + 1`, and the
bijectivity criteria of the latter take their two vanishing hypotheses in degrees `i` and
`i + 1`. The degrees used here are `-2` and `-1`, so the hypotheses are needed at `-2 + 1` and
`-1 + 1`; those are rewritten to `-1` and `0` rather than being left for the caller, which is why
several `have`s in the main proof differ from the lemmas they quote only by a degree
normalization.

`Dualizing.quotientExtEmbedding` already provides the injection
`Ext^i(M, K) / f · Ext^i(M, K) ↪ Ext^{i+1}(M/fM, K)` together with the specification of its
values, so the only new input for
`Dualizing.length_moduleExtInto_quotSMulTop_eq_length_quotient_smul` is the surjectivity of the
connecting map, which is `Dualizing.surjective_extConnecting_of_subsingleton`.

`Module.length_range_le_length_quotient_range` is a statement about lengths of modules with no
Ext in it; it is kept here because this is its only consumer. The equality of the `f`-torsion and
the `f`-cotorsion of a finite-length module that it is paired with is
`Module.length_ker_lsmul_eq_length_quotient_smul` in
`StacksFrontier/RingTheory/Length/SmulPowQuotient.lean`.

The short exact sequence is built with `ModuleCat.shortComplexOfCompEqZero` and
`ModuleCat.shortComplex_shortExact`, as in
`StacksFrontier/RingTheory/Dualizing/ExtFiniteLengthBound.lean`; its objects are then
`ModuleCat.of A _` and the Ext groups attached to them are `Dualizing.objExtInto`, which is
`Dualizing.moduleExtInto` on those objects by definition, so nothing has to be transported.

## References

* [Stacks Project, Lemma 0F2B](https://stacks.math.columbia.edu/tag/0F2B)
* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
* [Stacks Project, Lemma 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
-/

@[expose] public section

open CategoryTheory

open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe v u

/-- **The image of a map is no longer than the cokernel of anything it kills.** If
`h : D →ₗ[A] B` has image inside the kernel of `g : B →ₗ[A] C`, then `g` factors through
`B ⧸ range h` without changing its image, so the image of `g` is a quotient of `B ⧸ range h`
and hence no longer. -/
theorem Module.length_range_le_length_quotient_range {A : Type*} [CommRing A]
    {B C D : Type*} [AddCommGroup B] [Module A B] [AddCommGroup C] [Module A C]
    [AddCommGroup D] [Module A D] (g : B →ₗ[A] C) (h : D →ₗ[A] B)
    (hle : LinearMap.range h ≤ LinearMap.ker g) :
    Module.length A ↥(LinearMap.range g) ≤ Module.length A (B ⧸ LinearMap.range h) := by
  have hrange : LinearMap.range ((LinearMap.range h).liftQ g hle) = LinearMap.range g :=
    Submodule.range_liftQ _ g hle
  rw [← hrange]
  exact Module.length_le_of_surjective ((LinearMap.range h).liftQ g hle).rangeRestrict
    (LinearMap.surjective_rangeRestrict _)

namespace Dualizing

variable {A : Type u} [CommRing A]

/-- **Surjectivity of the connecting map across a regular element.** In the long exact Ext
sequence of `0 → M →^f M → M/fM → 0` the connecting map out of degree `i` is followed by the
map induced by the quotient `M → M/fM` in degree `i + 1`; if `Ext^{i+1}(M, K)` vanishes, the
latter is zero and exactness makes the connecting map surjective. -/
theorem surjective_extConnecting_of_subsingleton (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (i : ℤ)
    (h : Subsingleton (moduleExtInto M K (i + 1))) :
    Function.Surjective (extConnecting M K f hreg i) :=
  fun y => (exact_extConnecting_extFromQuotient M K f hreg i y).mp (h.elim _ 0)

/-- **The Ext of a quotient by a regular element is the quotient of the Ext.** If
`Ext^{i+1}(M, K)` vanishes then the connecting map of `0 → M →^f M → M/fM → 0` induces an
isomorphism `Ext^i(M, K) / f · Ext^i(M, K) ≅ Ext^{i+1}(M/fM, K)`, so the two have the same
length. Injectivity of the induced map is `Dualizing.quotientExtEmbedding` and surjectivity is
`Dualizing.surjective_extConnecting_of_subsingleton`. -/
theorem length_moduleExtInto_quotSMulTop_eq_length_quotient_smul (M : Type v) [AddCommGroup M]
    [Module A M] (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f)
    (i : ℤ) (h : Subsingleton (moduleExtInto M K (i + 1))) :
    Module.length A (moduleExtInto (QuotSMulTop f M) K (i + 1)) =
      Module.length A
        (moduleExtInto M K i ⧸ (f • (⊤ : Submodule A (moduleExtInto M K i)))) := by
  obtain ⟨j, hinj, hspec⟩ := quotientExtEmbedding M K f hreg i
  have hsurj : Function.Surjective j := by
    intro y
    obtain ⟨x, hx⟩ := surjective_extConnecting_of_subsingleton M K f hreg i h y
    exact ⟨_, (hspec x).trans hx⟩
  exact ((LinearEquiv.ofBijective j ⟨hinj, hsurj⟩).length_eq).symm

/-- **Precomposition through a module with vanishing Ext is zero.** For morphisms `φ : M ⟶ N`
and `ψ : N ⟶ P` of `A`-modules, the composite of the two induced maps on Ext in degree `i`
passes through `Ext^i(N, K)`, so it vanishes as soon as that group does. -/
theorem objExtPrecomp_comp_objExtPrecomp_eq_zero_of_subsingleton {M N P : ModuleCat.{v} A}
    (φ : M ⟶ N) (ψ : N ⟶ P) (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ)
    (h : Subsingleton (objExtInto N K i)) :
    (objExtPrecomp φ K i).comp (objExtPrecomp ψ K i) = 0 := by
  ext x
  rw [LinearMap.comp_apply, h.elim (objExtPrecomp ψ K i x) 0, map_zero, LinearMap.zero_apply]

/-- **A surjective precomposition map can be cancelled from an image.** For `φ : M ⟶ N` and
`ψ : N ⟶ P`, the map induced by `φ ≫ ψ` on Ext is the one induced by `φ` composed with the one
induced by `ψ`; when the latter is surjective the two have the same image. -/
theorem range_objExtPrecomp_comp_of_surjective {M N P : ModuleCat.{v} A} (φ : M ⟶ N) (ψ : N ⟶ P)
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ)
    (h : Function.Surjective (objExtPrecomp ψ K i)) :
    LinearMap.range (objExtPrecomp (φ ≫ ψ) K i) = LinearMap.range (objExtPrecomp φ K i) := by
  rw [objExtPrecomp_comp, LinearMap.range_comp, LinearMap.range_eq_top.mpr h, Submodule.map_top]

/-- **Kollár's length bound.** Let `(A, 𝔪)` be a Noetherian local ring with normalized dualizing
complex `ω`, let `f : A`, and let `ρ : M →ₗ[A] N` be a map of finite `A`-modules such that `f`
is a nonzerodivisor on `M`, the kernel of `ρ` is `fM`, both `M` and `N` have depth at least two,
and `N ⧸ ρ(M)` has finite length. Suppose moreover that `Ext_A^{-2}(M, ω)` has finite length and
that `ν : N →ₗ[A] V` is a map for which `ν ∘ ρ` factors as `c ∘ τ` through a module `W` with
`Ext_A^{-2}(W, ω) = 0`. Then

`length_A(N ⧸ ρ(M)) ≤ length_A(Ext_A^{-2}(N, ω) ⧸ im Ext_A^{-2}(ν))`.

The proof is the chain of identifications described in the module documentation: the finite-length
quotient is bounded by its own dual `Ext^0`, which the short exact sequence
`0 → M/fM → N → N/ρ(M) → 0` identifies with `Ext^{-1}(M/fM, ω)`, which the sequence
`0 → M →^f M → M/fM → 0` identifies with the cokernel of `f` on `Ext^{-2}(M, ω)`, hence (finite
length) with the `f`-torsion of `Ext^{-2}(M, ω)`, hence with the image of `Ext^{-2}(ρ)`; and that
image is no longer than the asserted quotient because `Ext^{-2}(ρ)` kills the image of
`Ext^{-2}(ν)`. -/
theorem length_quotient_range_le_length_quotient_range_objExtPrecomp
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (f : A)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hMreg : IsSMulRegular M f)
    (hdM : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) M)
    (hExtM : IsFiniteLength A (Dualizing.moduleExtInto M ω (-2)))
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (hdN : 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A) N)
    (ρ : M →ₗ[A] N) (hker : LinearMap.ker ρ = f • (⊤ : Submodule A M))
    (hQ : IsFiniteLength A (N ⧸ LinearMap.range ρ))
    {V W : Type u} [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W]
    (ν : N →ₗ[A] V) (τ : M →ₗ[A] W) (c : W →ₗ[A] V)
    (hW : Subsingleton (Dualizing.moduleExtInto W ω (-2)))
    (hfact : ν ∘ₗ ρ = c ∘ₗ τ) :
    Module.length A (N ⧸ LinearMap.range ρ) ≤
      Module.length A (Dualizing.moduleExtInto N ω (-2) ⧸
        LinearMap.range (Dualizing.objExtPrecomp (ModuleCat.ofHom ν) ω (-2))) := by
  -- Step 0: `ρ` factors through an injection `ι : M/fM ↪ N` with the same image.
  set ι : QuotSMulTop f M →ₗ[A] N := (f • (⊤ : Submodule A M)).liftQ ρ hker.ge with hιdef
  have hιinj : Function.Injective ι := by
    rw [hιdef, ← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ ρ hker.ge hker.le
  have hρfact : ρ = ι ∘ₗ (f • (⊤ : Submodule A M)).mkQ := by
    rw [hιdef]
    exact (Submodule.liftQ_mkQ _ ρ hker.ge).symm
  have hιrange : LinearMap.range ι = LinearMap.range ρ := by
    rw [hρfact, LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top]
  -- Step 1: the short exact sequence `0 → M/fM → N → N/ρ(M) → 0`.
  have hcomp : (LinearMap.range ρ).mkQ ∘ₗ ι = 0 :=
    LinearMap.range_le_ker_iff.mp (by rw [Submodule.ker_mkQ]; exact hιrange.le)
  have hexact : Function.Exact ι (LinearMap.range ρ).mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, hιrange]
  have hS : (ModuleCat.shortComplexOfCompEqZero ι (LinearMap.range ρ).mkQ hcomp).ShortExact :=
    ModuleCat.shortComplex_shortExact _ hexact hιinj (Submodule.mkQ_surjective _)
  -- Step 2: the vanishing of the neighbouring Ext groups.
  have hQm2 : Subsingleton (moduleExtInto (N ⧸ LinearMap.range ρ) ω (-2)) :=
    subsingleton_moduleExtInto_of_ne_zero_of_isFiniteLength hQ ω hω (-2) (by norm_num)
  have hQm1 : Subsingleton (moduleExtInto (N ⧸ LinearMap.range ρ) ω ((-2 : ℤ) + 1)) := by
    rw [show (-2 : ℤ) + 1 = -1 by norm_num]
    exact subsingleton_moduleExtInto_of_ne_zero_of_isFiniteLength hQ ω hω (-1) (by norm_num)
  have hNm1 : Subsingleton (moduleExtInto N ω (-1)) := by
    have h := subsingleton_moduleExtInto_of_lt_depth_bound (M := N) ω hω 2
      (by exact_mod_cast hdN) 1 (by norm_num)
    rwa [Nat.cast_one] at h
  have hN0 : Subsingleton (moduleExtInto N ω ((-1 : ℤ) + 1)) := by
    rw [show (-1 : ℤ) + 1 = 0 by norm_num]
    have h := subsingleton_moduleExtInto_of_lt_depth_bound (M := N) ω hω 2
      (by exact_mod_cast hdN) 0 (by norm_num)
    rwa [Nat.cast_zero, neg_zero] at h
  have hMm1 : Subsingleton (moduleExtInto M ω ((-2 : ℤ) + 1)) := by
    rw [show (-2 : ℤ) + 1 = -1 by norm_num]
    have h := subsingleton_moduleExtInto_of_lt_depth_bound (M := M) ω hω 2
      (by exact_mod_cast hdM) 1 (by norm_num)
    rwa [Nat.cast_one] at h
  -- Step 3: `Ext^{-2}(ι)` is bijective.
  have h3 : Function.Bijective (objExtPrecomp (ModuleCat.ofHom ι) ω (-2)) :=
    bijective_objExtPrecomp_f_of_subsingleton_third hS ω (-2) hQm2 hQm1
  -- Steps 4 and 5: the connecting map `Ext^{-1}(M/fM) → Ext^0(N/ρ(M))` is bijective.
  have h5 : Module.length A (moduleExtInto (QuotSMulTop f M) ω (-1)) =
      Module.length A (moduleExtInto (N ⧸ LinearMap.range ρ) ω 0) := by
    have h := (LinearEquiv.ofBijective (extSESConnecting hS ω (-1))
      (bijective_extSESConnecting_of_subsingleton_second hS ω (-1) hNm1 hN0)).length_eq
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  -- Step 6: `Ext^{-1}(M/fM, ω)` is the cokernel of `f` on `Ext^{-2}(M, ω)`.
  have h6 : Module.length A (moduleExtInto (QuotSMulTop f M) ω (-1)) =
      Module.length A (moduleExtInto M ω (-2) ⧸
        (f • (⊤ : Submodule A (moduleExtInto M ω (-2))))) := by
    have h := length_moduleExtInto_quotSMulTop_eq_length_quotient_smul M ω f hMreg (-2) hMm1
    rwa [show (-2 : ℤ) + 1 = -1 by norm_num] at h
  -- Step 7: for a module of finite length the `f`-cotorsion and the `f`-torsion agree.
  have h7 : Module.length A ↥(LinearMap.ker (LinearMap.lsmul A (moduleExtInto M ω (-2)) f)) =
      Module.length A (moduleExtInto M ω (-2) ⧸
        (f • (⊤ : Submodule A (moduleExtInto M ω (-2))))) :=
    Module.length_ker_lsmul_eq_length_quotient_smul hExtM f
  -- Step 8: that torsion is the image of `Ext^{-2}` of the quotient map `M → M/fM`.
  have h8 : LinearMap.ker (LinearMap.lsmul A (moduleExtInto M ω (-2)) f) =
      LinearMap.range (extFromQuotient M ω f (-2)) :=
    LinearMap.exact_iff.mp (exact_extFromQuotient_lsmul M ω f hMreg (-2))
  -- Step 9: that image is the image of `Ext^{-2}(ρ)`.
  have hρofHom : ModuleCat.ofHom ρ =
      ModuleCat.ofHom (f • (⊤ : Submodule A M)).mkQ ≫ ModuleCat.ofHom ι := by
    rw [← ModuleCat.ofHom_comp, ← hρfact]
  have h9 : LinearMap.range (objExtPrecomp (ModuleCat.ofHom ρ) ω (-2)) =
      LinearMap.range (extFromQuotient M ω f (-2)) := by
    rw [extFromQuotient_eq_objExtPrecomp, hρofHom]
    exact range_objExtPrecomp_comp_of_surjective _ _ ω (-2) h3.surjective
  -- Step 10: `Ext^{-2}(ρ)` kills the image of `Ext^{-2}(ν)`.
  have h10 : LinearMap.range (objExtPrecomp (ModuleCat.ofHom ν) ω (-2)) ≤
      LinearMap.ker (objExtPrecomp (ModuleCat.ofHom ρ) ω (-2)) := by
    rw [LinearMap.range_le_ker_iff, ← objExtPrecomp_comp, ← ModuleCat.ofHom_comp, hfact,
      ModuleCat.ofHom_comp, objExtPrecomp_comp]
    exact objExtPrecomp_comp_objExtPrecomp_eq_zero_of_subsingleton _ _ ω (-2) hW
  -- The chain.
  calc Module.length A (N ⧸ LinearMap.range ρ)
      ≤ Module.length A (moduleExtInto (N ⧸ LinearMap.range ρ) ω 0) :=
        length_le_length_moduleExtInto_zero hQ ω hω
    _ = Module.length A (moduleExtInto M ω (-2) ⧸
          (f • (⊤ : Submodule A (moduleExtInto M ω (-2))))) := by rw [← h5, h6]
    _ = Module.length A ↥(LinearMap.ker (LinearMap.lsmul A (moduleExtInto M ω (-2)) f)) := h7.symm
    _ = Module.length A ↥(LinearMap.range (objExtPrecomp (ModuleCat.ofHom ρ) ω (-2))) := by
          rw [h8, ← h9]
    _ ≤ Module.length A (moduleExtInto N ω (-2) ⧸
          LinearMap.range (objExtPrecomp (ModuleCat.ofHom ν) ω (-2))) :=
        Module.length_range_le_length_quotient_range _ _ h10

end Dualizing

end
