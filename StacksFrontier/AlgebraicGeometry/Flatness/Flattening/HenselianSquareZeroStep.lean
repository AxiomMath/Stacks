module

public import Mathlib.RingTheory.Flat.Tensor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.LocalCriteria
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# The square-zero step in the proof of Stacks 0AT3

The second paragraph of the proof of Stacks 0AT3 runs as follows.  In Situation 0AT0 with `A`
henselian, Stacks 05PG produces a finitely generated ideal `I ⊆ A` such that `N/IN` is flat
over `A/I` and such that `N/I²N` is *not* flat over `A/I²` unless `I = 0`.  The first paragraph
of that proof, applied over `A/I`, gives that `u mod I : N/IN → M/IM` is `A/I`-universally
injective.  The source then chases the diagram

```
0 → M ⊗_A I/I² → M/I²M → M/IM → 0
    N ⊗_A I/I² → N/I²N → N/IN → 0
```

to conclude that the lower left arrow is injective, and deduces from Algebra 10.99.8 that
`N/I²N` is flat over `A/I²` — a contradiction unless `I = 0`.

This file proves that implication, in the intrinsic form in which the ring `A/I²` and its
square-zero ideal `I/I²` are the data: **if `J ⊆ S` is an ideal with `J² = 0`, `M` is a flat
`S`-module, `u : N → M` is `S`-linear, `N/JN` is flat over `S/J`, and `N/JN → M/JM` is
universally injective, then `N` is flat over `S`.**  Instantiated at `S = A/I²` and `J = I/I²`
this is exactly the step above, with the conclusion `N/I²N` flat over `A/I²`.

The chase is shorter than the source's, because no exactness of either row is needed.  Only the
commuting square

```
J ⊗_S N  →  S ⊗_S N
   ↓            ↓
J ⊗_S M  →  S ⊗_S M
```

is used: the bottom map is injective because `M` is flat, the left map is injective because `J`
is annihilated by `J`, so tensoring with `J` does not distinguish `N` from `N/JN` and the left
map is `id_J ⊗ (u mod J)`.  Hence the top map is injective, which is the hypothesis of the
square-zero local criterion of flatness (`flat_of_sq_zero_local_criterion`, the `J² = 0` case of
Algebra 10.99.8).

## Main results

* `Stacks.SquareZeroInjectivity.lTensor_mkQ_injective`: tensoring with a module annihilated by
  `J` does not see `J • ⊤`.
* `Stacks.SquareZeroInjectivity.injective_lTensor_of_injective_lTensor_mapQ`: consequently
  `id_X ⊗ u` is injective as soon as `id_X ⊗ (u mod J)` is, for `X` annihilated by `J`.
* `AlgebraicGeometry.flat_of_sqZero_of_universallyInjective_mapQ`: the implication above, i.e.
  the second paragraph of the proof of Stacks 0AT3 with the two conclusions of Stacks 05PG
  removed.
* `AlgebraicGeometry.flat_of_sqZero_of_universallyInjectivePoly`: the same, with the hypothesis
  phrased by `UniversallyInjectivePoly`, which is what the first paragraph concludes.

## Implementation notes

Reduction modulo `J` is the quotient by `J • (⊤ : Submodule S ·)` and the induced map is the
canonical `Submodule.mapQ` of `u`, as everywhere else in this development; universal injectivity
is spelled out as injectivity of every `LinearMap.rTensor Q`, with `Q` ranging over the modules
in the universe of `S`, which is the universe the test module `↥J` actually used lives in.

No tag is registered here.  Stacks 0AT3 has three conclusions and its proof needs Stacks 05PG
(Theorem 38.24.1), which is proved nowhere in this repository; see the module docstring of
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.HenselianColimitFreeStep` for the state of the
first paragraph.

## References

* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0AT3](https://stacks.math.columbia.edu/tag/0AT3)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open TensorProduct

universe u v w w'

namespace Stacks.SquareZeroInjectivity

variable {S : Type u} [CommRing S]

/-! ### Tensoring with a module annihilated by the ideal -/

/-- An element of `J` acts as zero on a module annihilated by `J`. -/
private theorem smul_eq_zero_of_smul_top_eq_bot {X : Type v} [AddCommGroup X] [Module S X]
    {J : Ideal S} (hX : J • (⊤ : Submodule S X) = ⊥) {j : S} (hj : j ∈ J) (x : X) :
    j • x = 0 := by
  have hmem : j • x ∈ J • (⊤ : Submodule S X) := Submodule.smul_mem_smul hj Submodule.mem_top
  rw [hX, Submodule.mem_bot] at hmem
  exact hmem

/-- A pure tensor whose right factor lies in `J • ⊤` vanishes, as soon as the left factor lives
in a module annihilated by `J`. -/
private theorem tmul_eq_zero_of_mem_smul_top {X : Type v} [AddCommGroup X] [Module S X]
    {J : Ideal S} (hX : J • (⊤ : Submodule S X) = ⊥) {P : Type w} [AddCommGroup P] [Module S P]
    (x : X) {y : P} (hy : y ∈ J • (⊤ : Submodule S P)) :
    x ⊗ₜ[S] y = (0 : X ⊗[S] P) := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro j hj n _
    rw [← TensorProduct.smul_tmul, smul_eq_zero_of_smul_top_eq_bot hX hj x,
      TensorProduct.zero_tmul]
  · intro a b ha hb
    rw [TensorProduct.tmul_add, ha, hb, add_zero]

/-- **Tensoring with a module annihilated by `J` kills `J • ⊤`.** -/
theorem lTensor_subtype_eq_zero {X : Type v} [AddCommGroup X] [Module S X]
    (J : Ideal S) (hX : J • (⊤ : Submodule S X) = ⊥) (P : Type w) [AddCommGroup P]
    [Module S P] :
    LinearMap.lTensor X (J • (⊤ : Submodule S P)).subtype = 0 := by
  apply TensorProduct.ext'
  intro x y
  simpa using tmul_eq_zero_of_mem_smul_top hX x y.2

/-- **Tensoring with a module annihilated by `J` does not see `J • ⊤`.** The map
`X ⊗ P → X ⊗ (P ⧸ J • ⊤)` is injective when `J` annihilates `X`; since it is also surjective it
is an isomorphism, which is the statement `X ⊗_S P = X ⊗_{S/J} (P/JP)` used in the source. -/
theorem lTensor_mkQ_injective {X : Type v} [AddCommGroup X] [Module S X]
    (J : Ideal S) (hX : J • (⊤ : Submodule S X) = ⊥) {P : Type w} [AddCommGroup P]
    [Module S P] :
    Function.Injective (LinearMap.lTensor X (J • (⊤ : Submodule S P)).mkQ) := by
  have hex : Function.Exact (LinearMap.lTensor X (J • (⊤ : Submodule S P)).subtype)
      (LinearMap.lTensor X (J • (⊤ : Submodule S P)).mkQ) :=
    lTensor_exact X (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
  intro z₁ z₂ h
  rw [← sub_eq_zero] at h ⊢
  rw [← map_sub] at h
  obtain ⟨y, hy⟩ := (hex _).mp h
  rw [← hy, lTensor_subtype_eq_zero J hX P, LinearMap.zero_apply]

/-- If `g' ∘ f' = g ∘ f` with `f'` and `g'` injective, then `f` is injective. -/
private theorem injective_of_comp_eq_comp {R : Type*} [CommRing R]
    {A : Type*} [AddCommGroup A] [Module R A] {B : Type*} [AddCommGroup B] [Module R B]
    {A' : Type*} [AddCommGroup A'] [Module R A'] {B' : Type*} [AddCommGroup B'] [Module R B']
    {f : A →ₗ[R] B} {g : B →ₗ[R] B'} {f' : A →ₗ[R] A'} {g' : A' →ₗ[R] B'}
    (hsq : g'.comp f' = g.comp f) (hf' : Function.Injective f') (hg' : Function.Injective g') :
    Function.Injective f := by
  have hcomp : Function.Injective (g ∘ f) := by
    rw [← LinearMap.coe_comp, ← hsq, LinearMap.coe_comp]
    exact hg'.comp hf'
  exact hcomp.of_comp

/-- **Reduction modulo `J` does not change injectivity after tensoring with a `J`-killed
module.** -/
theorem injective_lTensor_of_injective_lTensor_mapQ {X : Type v} [AddCommGroup X] [Module S X]
    (J : Ideal S) (hX : J • (⊤ : Submodule S X) = ⊥)
    {P : Type w} [AddCommGroup P] [Module S P] {Q : Type w'} [AddCommGroup Q] [Module S Q]
    (f : P →ₗ[S] Q)
    (h : Function.Injective (LinearMap.lTensor X
      (Submodule.mapQ (J • (⊤ : Submodule S P)) (J • (⊤ : Submodule S Q)) f
        (Submodule.smul_top_le_comap_smul_top J f)))) :
    Function.Injective (LinearMap.lTensor X f) := by
  refine injective_of_comp_eq_comp
      (g := LinearMap.lTensor X (J • (⊤ : Submodule S Q)).mkQ) ?_ (lTensor_mkQ_injective J hX) h
  rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, Submodule.mapQ_mkQ]

/-- Injectivity of `id_X ⊗ f` follows from injectivity of `f ⊗ id_X`, by commutativity of the
tensor product. -/
theorem injective_lTensor_of_injective_rTensor {R : Type*} [CommRing R]
    {X : Type*} [AddCommGroup X] [Module R X] {P : Type*} [AddCommGroup P] [Module R P]
    {Q : Type*} [AddCommGroup Q] [Module R Q] (f : P →ₗ[R] Q)
    (h : Function.Injective (LinearMap.rTensor X f)) :
    Function.Injective (LinearMap.lTensor X f) := by
  have hsq : (TensorProduct.comm R X Q).toLinearMap.comp (LinearMap.lTensor X f)
      = (LinearMap.rTensor X f).comp (TensorProduct.comm R X P).toLinearMap := by
    apply TensorProduct.ext'
    intro x p
    simp
  exact injective_of_comp_eq_comp hsq.symm (TensorProduct.comm R X P).injective h

/-! ### The diagram chase -/

/-- A square-zero ideal annihilates itself. -/
theorem smul_top_self_eq_bot {J : Ideal S} (hJ : J ^ 2 = ⊥) :
    J • (⊤ : Submodule S (↥J)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro j hj k _
  rw [Submodule.mem_bot]
  apply Subtype.ext
  have hmem : j * (k : S) ∈ J ^ 2 := by
    rw [pow_two]; exact Ideal.mul_mem_mul hj k.2
  rw [hJ, Submodule.mem_bot] at hmem
  simpa [smul_eq_mul] using hmem

/-- **The diagram chase of the second paragraph of the proof of Stacks 0AT3.** For `J ⊆ S` an
ideal with `J² = 0`, `M` a flat `S`-module and `u : N → M` an `S`-linear map whose reduction
modulo `J` stays injective after tensoring with `↥J`, the multiplication `J ⊗_S N → S ⊗_S N` is
injective.

The square

```
J ⊗_S N  →  S ⊗_S N
   ↓            ↓
J ⊗_S M  →  S ⊗_S M
```

commutes (both composites are `TensorProduct.map J.subtype u`); the bottom map is injective
because `M` is flat, and the left map is injective by hypothesis. -/
@[sga "3 III 4.13" "partial"]
theorem rTensor_subtype_injective_of_injective_lTensor_mapQ
    {M : Type v} [AddCommGroup M] [Module S M] [Module.Flat S M]
    {N : Type w} [AddCommGroup N] [Module S N]
    (J : Ideal S) (hJ : J ^ 2 = ⊥) (u : N →ₗ[S] M)
    (hui : Function.Injective (LinearMap.lTensor (↥J)
      (Submodule.mapQ (J • (⊤ : Submodule S N)) (J • (⊤ : Submodule S M)) u
        (Submodule.smul_top_le_comap_smul_top J u)))) :
    Function.Injective (LinearMap.rTensor N J.subtype) := by
  have hvert : Function.Injective (LinearMap.lTensor (↥J) u) :=
    injective_lTensor_of_injective_lTensor_mapQ J (smul_top_self_eq_bot hJ) u hui
  have hM : Function.Injective (LinearMap.rTensor M J.subtype) :=
    (Module.Flat.iff_rTensor_injective' (R := S) (M := M)).mp inferInstance J
  refine injective_of_comp_eq_comp (g := LinearMap.lTensor S u) ?_ hvert hM
  rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]

end Stacks.SquareZeroInjectivity

namespace AlgebraicGeometry

open Stacks.SquareZeroInjectivity

/-- **The second paragraph of the proof of Stacks 0AT3, with the two conclusions of Stacks 05PG
removed from it.** Let `J ⊆ S` be an ideal with `J² = 0`, let `M` be a flat `S`-module, let
`u : N → M` be an `S`-linear map, and suppose that `N/JN` is flat over `S/J` and that
`u mod J : N/JN → M/JM` is universally injective. Then `N` is flat over `S`.

Instantiated at `S = A/I²` and `J = I/I²` for the ideal `I ⊆ A` of Stacks 05PG this is the step
of the source's proof that produces the contradiction: `N/I²N` is then flat over `A/I²`, whereas
Stacks 05PG says this forces `I = 0`, whence `N = N/IN` is flat over `A`.

The proof is the source's diagram chase
(`rTensor_subtype_injective_of_injective_lTensor_mapQ`) feeding the square-zero case of
Algebra 10.99.8 (`flat_of_sq_zero_local_criterion`). Only the value of the universal injectivity
hypothesis at the test module `↥J` is used, which is the source's `N/JN ⊗ J → M/JM ⊗ J`. -/
theorem flat_of_sqZero_of_universallyInjective_mapQ
    {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M] [Module.Flat S M]
    {N : Type w} [AddCommGroup N] [Module S N]
    (J : Ideal S) (hJ : J ^ 2 = ⊥) (u : N →ₗ[S] M)
    (hquot : Module.Flat (S ⧸ J) (N ⧸ J • (⊤ : Submodule S N)))
    (hui : ∀ (Q : Type u) [AddCommGroup Q] [Module S Q], Function.Injective
      (LinearMap.rTensor Q (Submodule.mapQ (J • (⊤ : Submodule S N))
        (J • (⊤ : Submodule S M)) u (Submodule.smul_top_le_comap_smul_top J u)))) :
    Module.Flat S N := by
  refine flat_of_sq_zero_local_criterion J hJ hquot ?_
  have hgoal : (TensorProduct.lift ((LinearMap.lsmul S N).comp J.subtype))
      = (TensorProduct.lid S N).toLinearMap.comp (LinearMap.rTensor N J.subtype) := by
    apply TensorProduct.ext'
    intro j n
    simp
  rw [hgoal, LinearMap.coe_comp]
  refine (TensorProduct.lid S N).injective.comp ?_
  exact rTensor_subtype_injective_of_injective_lTensor_mapQ J hJ u
    (injective_lTensor_of_injective_rTensor _ (hui (↥J)))

/-- **The same step, with its universal injectivity hypothesis in the shape the first paragraph
of the proof of Stacks 0AT3 produces.** The predicate is `UniversallyInjectivePoly`, which is
what `AlgebraicGeometry.universallyInjective_of_colimit_free` concludes; here its test modules
range over the universe of `S`, which is where the module `↥J` the proof uses lives. -/
theorem flat_of_sqZero_of_universallyInjectivePoly
    {S : Type u} [CommRing S] {M : Type v} [AddCommGroup M] [Module S M] [Module.Flat S M]
    {N : Type w} [AddCommGroup N] [Module S N]
    (J : Ideal S) (hJ : J ^ 2 = ⊥) (u : N →ₗ[S] M)
    (hquot : Module.Flat (S ⧸ J) (N ⧸ J • (⊤ : Submodule S N)))
    (hui : UniversallyInjectivePoly.{u, u}
      (Submodule.mapQ (J • (⊤ : Submodule S N)) (J • (⊤ : Submodule S M)) u
        (Submodule.smul_top_le_comap_smul_top J u))) :
    Module.Flat S N :=
  flat_of_sqZero_of_universallyInjective_mapQ J hJ u hquot hui

end AlgebraicGeometry

end
