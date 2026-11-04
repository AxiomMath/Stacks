module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

/-!
# Termwise Tor amplitude and flatness of a cokernel

Let `R` be a commutative ring and let `K` be a cochain complex of `R`-modules, modelled as a
term of `CochainComplex (ModuleCat R) ℤ` with cohomological indexing. This file introduces the
*termwise* Tor-amplitude condition on `K`: for every `R`-module `M` and every integer
`i ∉ [a, b]`, the cohomology `H^i(K ⊗ M)` of the complex obtained by tensoring `K` with `M` in
each degree vanishes.

This condition is **not** the Tor-amplitude condition of Stacks 0652, which is about the
derived tensor product `K ⊗^L M[0]` in `D(R)`. It is an auxiliary condition: it mentions only
the termwise tensor product complex, it assumes nothing about boundedness of `K`, and it is
stated with the ring and the modules in one shared universe. What it is for is the flat-cokernel
argument below, which needs no more than this.

The derived-category statement of Stacks 0653 — a *bounded above* complex of flat modules whose
image in `D(R)` has derived Tor amplitude in `[a, b]` has flat `Coker(d_K^{a-1})` — is obtained
by feeding this file's `cokernel_flat_of_termwise_torAmplitude` the comparison between derived
and termwise Tor amplitude. That comparison and the tagged theorem live in
`StacksFrontier.Homology.TorAmplitude.DerivedComparison`.

## Main definitions

* `StacksDraft.TorAmplitude.Termwise.tensorComplex`: the termwise tensor product complex `K ⊗ M`,
  with terms `K^n ⊗ M`
  and differentials `d_K^n ⊗ id`.
* `StacksDraft.TorAmplitude.Termwise.IsComplexOfFlats`: every term of `K` is a flat `R`-module.
* `StacksDraft.TorAmplitude.Termwise.HasTorAmplitudeIn`: the termwise Tor-amplitude condition
  described above.

## Main results

* `StacksDraft.TorAmplitude.Termwise.cokernel_flat_of_termwise_torAmplitude`: a complex of flat
  modules satisfying the
  termwise condition for `[a, b]` has flat `Coker(d_K^{a-1}) = K^a / Im(d_K^{a-1})`, modelled by
  the categorical `cokernel (K.d (a - 1) a)`.
* `StacksDraft.TorAmplitude.Termwise.flat_quotient_of_rTensor_subtype_injective`: a submodule `Z`
  of a flat module `D`
  such that `Z ⊗ M → D ⊗ M` is injective for every `M` has flat quotient `D ⧸ Z`.
* `StacksDraft.TorAmplitude.Termwise.rTensor_range_subtype_injective_of_exact`: middle exactness of
  a tensored
  two-step complex makes `range g ⊗ M → B ⊗ M` injective.

## Implementation notes

The upper bound `b` does not enter the conclusion of the flat-cokernel argument; only the lower
bound `a` is used. The condition is stated with both `a` and `b` to match the source.

## References

* [Stacks Project, Tag 00M5](https://stacks.math.columbia.edu/tag/00M5)
* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
-/

open CategoryTheory MonoidalCategory Limits

namespace StacksDraft.TorAmplitude.Termwise

variable {R : Type*} [CommRing R]

/-- The termwise derived tensor product of a bounded above complex of flat modules
`K` with a module `M`: the complex with terms `K^n ⊗ M` and differentials
`d_K^n ⊗ id`. For a bounded above complex of flat modules this represents
`K ⊗^L M`. -/
noncomputable def tensorComplex (K : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) :
    CochainComplex (ModuleCat R) ℤ :=
  ((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The `n`-th term of the termwise tensor product complex is `K^n ⊗ M`. -/
@[simp] theorem tensorComplex_X (K : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (n : ℤ) :
    (tensorComplex K M).X n = K.X n ⊗ M := rfl

/-- The differentials of the termwise tensor product complex are `d_K^n ⊗ id`. -/
@[simp] theorem tensorComplex_d (K : CochainComplex (ModuleCat R) ℤ) (M : ModuleCat R) (i j : ℤ) :
    (tensorComplex K M).d i j = K.d i j ▷ M := rfl

/-- A cochain complex `K` is a *complex of flat `R`-modules* if `K^n` is a flat
`R`-module for every `n`. -/
def IsComplexOfFlats (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  ∀ n : ℤ, Module.Flat R (K.X n)

/-- The *termwise* Tor-amplitude condition: `H^i(K ⊗ M) = 0` for every `R`-module `M` and every
integer `i ∉ [a, b]` (i.e. `i < a` or `b < i`), where `K ⊗ M` is the termwise tensor product
complex `tensorComplex K M`.

This is an auxiliary condition and not the derived Tor amplitude of Stacks 0652: no derived
tensor product occurs, and `K` is not assumed bounded above. For a bounded above complex of flat
modules the two agree, because then `tensorComplex K M` represents `K ⊗^L M[0]`; see
`StacksFrontier.Homology.TorAmplitude.DerivedComparison`. -/
def HasTorAmplitudeIn (K : CochainComplex (ModuleCat R) ℤ) (a b : ℤ) : Prop :=
  ∀ (M : ModuleCat R) (i : ℤ), (i < a ∨ b < i) → IsZero ((tensorComplex K M).homology i)

/-!
## Proof outline (Tor-free formalization)

The classical Stacks proof says: the condition at `i = a - 1` gives `H^{a-1}(K ⊗ M) = 0` for
all `M`, i.e. `Tor₁^R(C, M) = 0` for all `M`, where `C = Coker(d^{a-1})`; hence `C` is flat by
Tag 00M5. **Mathlib has no usable `Tor` API** (`Module.Tor` does not exist; `flat ↔ Tor` is an
explicit TODO). So we reformulate the whole argument in terms of injectivity of tensored maps.

Write `g := d_K^{a-1} : K^{a-1} → K^a`, `f := d_K^{a-2} : K^{a-2} → K^{a-1}`,
`Z := range g ⊆ K^a`, and `C := K^a / Z ≅ Coker(g)`. All `K^n` are flat. The
argument has three substantive steps:

* **S1 (extract middle-exactness).** From `htor` at `i = a-1` (`a-1 < a`) and
  `exactAt_iff_isZero_homology`, the short complex of `tensorComplex K M` at
  `a-1` is exact, i.e. for every `M`,
  `Function.Exact (rTensor M f.hom) (rTensor M g.hom)`
  (the maps `K^{a-2}⊗M → K^{a-1}⊗M → K^a⊗M`).

* **S3 (`Z⊗M → K^a⊗M` is injective).** Factor `g.hom = Z.subtype ∘ g'` with
  `g' : K^{a-1} ↠ Z` surjective (`g' = g.hom.rangeRestrict`). Then
  `rTensor M g.hom = rTensor M Z.subtype ∘ rTensor M g'` and `rTensor M g'` is
  surjective. If `ξ ∈ Z⊗M` has `rTensor M Z.subtype ξ = 0`, lift `ξ = rTensor M g' η`;
  then `rTensor M g.hom η = 0`, so by S1 `η ∈ ker(rTensor M g.hom) = range(rTensor M f.hom)`,
  say `η = rTensor M f.hom θ`; hence `ξ = rTensor M (g' ∘ f.hom) θ = 0` because
  `g' ∘ f.hom = 0` (since `Z.subtype` is injective and `Z.subtype ∘ g' ∘ f.hom = g.hom ∘ f.hom =
  0`).
  So `rTensor M Z.subtype` is injective. (Only uses S1 and surjectivity of `g'`;
  flatness of `K^{a-1}` is not needed here.)

* **S4 (flat from S3).** `C` is flat iff for every injection `α : N ↪ N'`,
  `lTensor C α` (equiv. `rTensor`) is injective
  (`Module.Flat.iff_lTensor_preserves_injective_linearMap`). Given such `α`,
  apply the four-lemma `lTensor_injective_of_exact_of_exact_of_rTensor_injective`
  to the two right-exact rows `Z → K^a → C → 0` and `N → N' → coker α → 0`:
  its hypotheses are (i) `rTensor (coker α) Z.subtype` injective — this is S3 at
  `M = coker α`; and (ii) `lTensor K^a α` injective — true since `K^a` is flat.
  The conclusion is `lTensor C α` injective. Hence `C` is flat.

* **Bridge.** `cokernel (K.d (a-1) a) ≅ ModuleCat.of R (K^a / range g.hom)` via
  `ModuleCat.cokernelIsoRangeQuotient`; transport flatness with
  `Module.Flat.of_linearEquiv`.
-/

/-- **Step S3.** SANITY CHECK PASSED (a complete proof was found by the checker).
Let `f : A →ₗ B`, `g : B →ₗ D` with `g ∘ f = 0`, and let
`g' : B →ₗ range g` be the surjection `g.rangeRestrict` (so `g = (range g).subtype ∘ g'`).
If for the module `M` the tensored sequence
`A⊗M → B⊗M → D⊗M` is exact in the middle (`Function.Exact (rTensor M f) (rTensor M g)`),
then `rTensor M ((range g).subtype) : (range g)⊗M → B⊗M` is injective. -/
theorem rTensor_range_subtype_injective_of_exact
    {A B D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [Module R A] [Module R B] [Module R D]
    (f : A →ₗ[R] B) (g : B →ₗ[R] D) (hfg : g ∘ₗ f = 0)
    (M : Type*) [AddCommGroup M] [Module R M]
    (hexact : Function.Exact (LinearMap.rTensor M f) (LinearMap.rTensor M g)) :
    Function.Injective (LinearMap.rTensor M (LinearMap.range g).subtype) := by
  set g' : B →ₗ[R] LinearMap.range g := g.rangeRestrict
  have hgcomp : (LinearMap.range g).subtype ∘ₗ g' = g :=
    LinearMap.subtype_comp_codRestrict g g.range (LinearMap.mem_range_self g)
  have hg'f : g' ∘ₗ f = 0 :=
    LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun hfg x)
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  obtain ⟨η, rfl⟩ := LinearMap.rTensor_surjective M g.surjective_rangeRestrict ξ
  have hg0 : LinearMap.rTensor M g η = 0 := by
    rw [← hgcomp, LinearMap.rTensor_comp]
    exact hξ
  obtain ⟨θ, hθ⟩ := (hexact η).mp hg0
  rw [← hθ, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hg'f]
  simp

/-- **Step S4.** SANITY CHECK PASSED. Let `Z` be a submodule of a flat module `D`, and
suppose that for *every* module `M` the inclusion `Z ↪ D` induces an injection
`Z⊗M → D⊗M` (`rTensor M Z.subtype` injective). Then `D ⧸ Z` is flat. This is the
Tor-free form of: from the SES `0 → Z → D → D/Z → 0` with `D` flat, `D/Z` is flat iff
`Z⊗M → D⊗M` is injective for all `M` (Stacks Tag 00M5).

Note: `hinj` is quantified over `M : Type (max u w)`. In Lean a hypothesis
`∀ (M : Type*), …` introduces a *single fixed* universe parameter, which cannot be
applied at the universe `max u w` that the flatness criterion's test module
`N' ⧸ range α` lives in. We therefore pin `hinj`'s universe to exactly `max u w`
(`u`, `w` = universes of `R`, `D`), which requires the explicit universe binder
`{u, w}`. -/
theorem flat_quotient_of_rTensor_subtype_injective.{u, w}
    {R : Type u} [CommRing R] {D : Type w} [AddCommGroup D] [Module R D]
    (Z : Submodule R D) [Module.Flat R D]
    (hinj : ∀ (M : Type (max u w)) [AddCommGroup M] [Module R M],
      Function.Injective (LinearMap.rTensor M Z.subtype)) :
    Module.Flat R (D ⧸ Z) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ α hα
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (LinearMap.exact_subtype_mkQ Z)
    (Submodule.mkQ_surjective Z)
    (LinearMap.exact_map_mkQ_range α)
    (Submodule.mkQ_surjective (LinearMap.range α))
    (hinj (N' ⧸ LinearMap.range α))
    (Module.Flat.lTensor_preserves_injective_linearMap α hα)

/-- The flat-cokernel argument from the *termwise* Tor-amplitude condition. Let `a b : ℤ` and
let `K` be a cochain complex of flat `R`-modules such that `H^i(K ⊗ M) = 0` for every
`R`-module `M` and every `i ∉ [a, b]`. Then `Coker(d_K^(a-1)) = K^a / Im(d_K^(a-1))` is a flat
`R`-module.

This is an auxiliary statement, not Stacks 0653: the hypothesis is the termwise condition
`HasTorAmplitudeIn` rather than derived Tor amplitude in `D(R)`, `K` is not assumed bounded
above, and the ring and the modules share a universe. Only the lower bound `a` is used. For the
derived-category form of the statement, at independent ring and module universes, see
`StacksDraft.TorAmplitude.cokernel_flat_of_torAmplitude_of_comparisonFunctor` in
`StacksFrontier.Homology.TorAmplitude.DerivedComparison`, which supplies a hypothesis of this shape
from derived Tor amplitude. -/
theorem cokernel_flat_of_termwise_torAmplitude
    (K : CochainComplex (ModuleCat R) ℤ) (a b : ℤ)
    (hflat : IsComplexOfFlats K)
    (htor : HasTorAmplitudeIn K a b) :
    Module.Flat R (cokernel (K.d (a - 1) a) : ModuleCat R) := by
  -- Abbreviations: `g := (K.d (a-1) a).hom`, `f := (K.d (a-2) (a-1)).hom`.
  set g : (K.X (a - 1) : Type _) →ₗ[R] (K.X a : Type _) := (K.d (a - 1) a).hom with hg
  -- `K^a` is flat (from `hflat`).
  have hKa : Module.Flat R (K.X a : Type _) := hflat a
  -- S1: for every module `M`, the tensored sequence is exact in the middle, i.e.
  -- `Function.Exact (rTensor M (K.d (a-2) (a-1)).hom) (rTensor M g)`.
  -- From `htor _ (a-1) (Or.inl (by omega))`, `exactAt_iff_isZero_homology`,
  -- `HomologicalComplex.exactAt_iff`, the `shortComplexFunctor` accessors
  -- (`prev (a-1) = a-2`, `next (a-1) = a`), `Functor.mapHomologicalComplex_obj_d`,
  -- `ModuleCat.hom_whiskerRight` (= `rTensor`), and
  -- `ShortExact.moduleCat_exact_iff_function_exact`.
  -- (S1 is a definitional/categorical unfolding of the hypothesis `htor`.)
  -- S3 ⟹ for every `M`, `rTensor M (range g).subtype` is injective.
  -- (Apply `rTensor_range_subtype_injective_of_exact` with the S1 exactness and
  --  `(K.d (a-1) a).hom ∘ₗ (K.d (a-2) (a-1)).hom = 0`, i.e.
  --  `(K.d (a-2) (a-1) ≫ K.d (a-1) a).hom = 0` from `K.d_comp_d` + `ModuleCat.hom_zero`.)
  have hinj : ∀ (M : Type _) [AddCommGroup M] [Module R M],
      Function.Injective (LinearMap.rTensor M (LinearMap.range g).subtype) := by
    intro M _ _
    have hexactAt : (tensorComplex K (ModuleCat.of R M)).ExactAt (a - 1) :=
      (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
        (htor (ModuleCat.of R M) (a - 1) (Or.inl (by omega)))
    rw [HomologicalComplex.exactAt_iff,
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hexactAt
    -- `hexactAt : Function.Exact (hom S.f) (hom S.g)` where
    -- `S.f = (tensorComplex K M).d (prev (a-1)) (a-1)` and
    -- `S.g = (tensorComplex K M).d (a-1) (next (a-1))`, and the underlying linear
    -- maps are the corresponding `rTensor`s (definitionally).
    have key : Function.Exact
        (LinearMap.rTensor M (K.d ((ComplexShape.up ℤ).prev (a - 1)) (a - 1)).hom)
        (LinearMap.rTensor M (K.d (a - 1) ((ComplexShape.up ℤ).next (a - 1))).hom) := hexactAt
    rw [show ((ComplexShape.up ℤ).next (a - 1)) = a by simp [CochainComplex.next]] at key
    exact rTensor_range_subtype_injective_of_exact
      (K.d ((ComplexShape.up ℤ).prev (a - 1)) (a - 1)).hom g
      (by rw [hg, ← ModuleCat.hom_comp, K.d_comp_d, ModuleCat.hom_zero]) M key
  -- S4 ⟹ `(K.X a) ⧸ range g` is flat.
  have hflatQ : Module.Flat R ((K.X a : Type _) ⧸ LinearMap.range g) :=
    flat_quotient_of_rTensor_subtype_injective (LinearMap.range g) hinj
  -- Bridge: `cokernel (K.d (a-1) a) ≅ ModuleCat.of R ((K.X a) ⧸ range g)`,
  -- transport flatness via `Module.Flat.of_linearEquiv` /
  -- `ModuleCat.cokernelIsoRangeQuotient` (its `toLinearEquiv`).
  exact Module.Flat.of_linearEquiv
    (ModuleCat.cokernelIsoRangeQuotient (K.d (a - 1) a)).toLinearEquiv

end StacksDraft.TorAmplitude.Termwise
