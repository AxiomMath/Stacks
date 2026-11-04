module

public import StacksFrontier.RingTheory.Coherent.Basic
public import StacksFrontier.RingTheory.Module.FinitePresentation.TensorProductPi

@[expose] public section

universe u

/-!
# Chase's theorem: coherence and products of flat modules

Let `R` be a commutative ring. Flatness of a module is preserved by direct sums, but not in
general by direct products: the product `∏ Q α` of flat `R`-modules can fail to be flat, and
already the product `R^A = ∀ _ : A, R` of copies of `R` can. Chase's theorem says that the rings
over which this never happens are exactly the coherent ones, and that a single family of test
modules suffices to detect them: the free modules `R^A`.

The mechanism is the description of flatness by finitely generated ideals: `M` is flat if and only
if `↥I ⊗[R] M → R ⊗[R] M` is injective for every finitely generated ideal `I` of `R`
(`Module.Flat.iff_rTensor_injective`, Stacks 00HD). And the canonical comparison map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is bijective for every family `(Q α)` exactly when `M` is
finitely presented (`Module.FinitePresentation.tfae_piRightHom_bijective`, Stacks 059K), and
surjective for every family exactly when `M` is finitely generated
(`Module.Finite.tfae_piRightHom_surjective`, Stacks 059J).

So let `R` be coherent, let `(Q α)` be flat and let `I` be a finitely generated ideal. Coherence
makes `↥I` finitely presented, so the comparison map for `↥I` is injective, and naturality of the
comparison map in its left factor identifies `↥I ⊗[R] ∏ Q α → R ⊗[R] ∏ Q α`, followed by the
comparison map for `R`, with the product of the maps `↥I ⊗[R] Q α → R ⊗[R] Q α`, each injective by
flatness of `Q α`; hence the first map is injective and `∏ Q α` is flat. Taking every `Q α` to be
`R` gives the flatness of `R^A`. Conversely, if every `R^A` is flat and `I` is a finitely generated
ideal, then `↥I ⊗[R] R^A → ↥I^A` is surjective by finite generation of `I` and Stacks 059J, and
injective by the same naturality square, whose bottom row `R ⊗[R] R^A → R^A` is bijective because
`R` is finitely presented over itself; so it is bijective for every `A` and `↥I` is finitely
presented by Stacks 059K.

## Main results

* `IsCoherentRing.tfae_flat_pi`: for a commutative ring `R` the following are equivalent: `R` is
  coherent; every product of flat `R`-modules is flat; the module `R^A` is flat for every set `A`.
* `TensorProduct.piRightHom_rTensor_apply`, `TensorProduct.piScalarRightHom_rTensor_apply`:
  naturality of the two comparison maps in the left tensor factor.

## Implementation notes

Coherence is `IsCoherentRing` (Definition 05CV), coherence of `R` as a module over itself; the
equivalent form used in the proof, that every finitely generated ideal of `R` is finitely
presented, is the remark following that definition and not restated here (it is
`isCoherentRing_iff_forall_fg_ideal_finitePresentation`).

The source's product `∏_{α ∈ A} Q α` is the Lean product `∀ α, Q α`, and its `R^A` is the special
case `∀ _ : A, R`, written `A → R`; no comparison map has to be pinned, since both items assert
flatness of an honestly constructed module rather than a property of a map.

The source quantifies over families of `R`-modules in every universe, which no single Lean
statement can do. The index types and the members of the family range over `Type u`, the universe
of `R`, and this is the sharp choice, exactly as in Propositions 059J and 059K, whose items are
then citable at the same universe: the implication from coherence holds for families in any
universe; the implication from item 2 to item 3 needs `R` itself among the available test modules;
and the converse needs index sets of the cardinality of a finitely generated ideal `I` of `R` and
of the kernel of a surjection `R^n → I`, both of which `Type u` provides. No smallness hypothesis
on `R` is therefore imposed. A family of modules in a larger universe `Type w` is reached by
applying the statement to the ring `ULift.{w} R`, over which flatness of a module is flatness
over `R`.

The equivalence is stated as a `List.TFAE`, as the source states it, in the source's order, so
that `(IsCoherentRing.tfae_flat_pi R).out 1 3` is the source's `(1) ↔ (3)` — `List.TFAE.out`
numbers the items from `1`, as the source does — and each item quantifies over its own test data.
The flatness of the members of the family is an explicit hypothesis of item 2 rather than an
instance binder, so that item 2 reads as the implication the source states and can be applied to a
flatness proof that is not an instance; this is the shape of the right-hand side of
`Module.Flat.directSum_iff`, the direct sum counterpart, which holds over every ring.

Naturality of `TensorProduct.piRightHom` and of `TensorProduct.piScalarRightHom` in the left
tensor factor is not in Mathlib; it is proved here in the applied form the two flatness arguments
consume. Both citations of Stacks 059J and 059K are at test universe `v := u`, the universe of
`R`, where `Small.{u} R` is `small_self` and the modules tested, `↥I` for an ideal `I` of `R` and
`R` itself, are available.

Faithfulness. (1) There is no hypothesis to be dead: the only datum is a commutative ring `R`,
used by all three items, and nothing is assumed of it — no coherence, no Noetherian hypothesis, no
smallness — the test data of items 2 and 3 being quantified inside those items. (2) The scalars
and the base are the source's: coherence, flatness and the products are all over `R`, with no
localization and no base change. (3) The source names no canonical map: the content is flatness of
the modules `∀ α, Q α` and `A → R`, which are pinned as the `Pi` module structure over `R`.
(4) The instantiation is not degenerate and both directions have content: for `R = ℤ`, coherent by
Lemma 05CY, all three items hold, and `ℤ^A` is even free; for the non-coherent ring
`R = k[x, y₁, y₂, …] / (x y₁, x y₂, …)`, where the finitely generated ideal `(x)` is not finitely
presented, all three fail, so item 3 exhibits a set `A` with `R^A` not flat even though `R` itself
is flat over `R` and every finite product `R^n` is free. Item 3 holds automatically for finite `A`,
where `R^A` is free, so it is the infinite sets that carry the theorem.

## References

* [StacksProject 05CZ](https://stacks.math.columbia.edu/tag/05CZ)
* [Chase, *Direct products of modules*, Theorem 2.1]
-/

namespace TensorProduct

section Naturality

open Function LinearMap

variable {R : Type*} [CommRing R] {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁]
  [AddCommGroup N₂] [Module R N₂]

/-- `TensorProduct.piRightHom` is natural in the left tensor factor. -/
lemma piRightHom_rTensor_apply {A : Type*} (Q : A → Type*) [∀ α, AddCommGroup (Q α)]
    [∀ α, Module R (Q α)] (h : N₁ →ₗ[R] N₂) (x : N₁ ⊗[R] (∀ α, Q α)) (α : A) :
    piRightHom R R N₂ Q (rTensor (∀ α, Q α) h x) α = rTensor (Q α) h (piRightHom R R N₁ Q x α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul n q => simp
  | add x y hx hy => simp [hx, hy]

/-- `TensorProduct.piScalarRightHom` is natural in the left tensor factor. -/
lemma piScalarRightHom_rTensor_apply (A : Type*) (h : N₁ →ₗ[R] N₂)
    (x : N₁ ⊗[R] (A → R)) (α : A) :
    piScalarRightHom R R N₂ A (rTensor (A → R) h x) α = h (piScalarRightHom R R N₁ A x α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul n q => simp
  | add x y hx hy => simp [hx, hy]

end Naturality

end TensorProduct

section Chase

open Function LinearMap TensorProduct

/-- **Stacks 05CZ** (Chase's theorem). Let `R` be a commutative ring. The following are
equivalent: (1) `R` is coherent; (2) any product of flat `R`-modules is flat; (3) for every set
`A` the module `R^A` is flat. -/
@[stacks 05CZ "Test data in the universe of `R`. See the module docstring."]
theorem IsCoherentRing.tfae_flat_pi (R : Type u) [CommRing R] :
    List.TFAE
      [IsCoherentRing R,
        ∀ (A : Type u) (Q : A → Type u) [∀ α, AddCommGroup (Q α)] [∀ α, Module R (Q α)],
          (∀ α, Module.Flat R (Q α)) → Module.Flat R (∀ α, Q α),
        ∀ A : Type u, Module.Flat R (A → R)] := by
  tfae_have 1 → 2 := by
    intro hR A Q _ _ hQ
    rw [Module.Flat.iff_rTensor_injective]
    intro I hI
    have hfp : Module.FinitePresentation R ↥I :=
      hR.isCoherent.fg_submodule_finitePresentation I hI
    have h12 := ((Module.FinitePresentation.tfae_piRightHom_bijective R ↥I).out 1 2).mp hfp
    have hbij : Bijective (piRightHom R R ↥I Q) := h12 A Q
    intro x y hxy
    refine hbij.injective (funext fun α => ?_)
    refine (Module.Flat.iff_rTensor_injective.mp (hQ α) hI) ?_
    rw [← piRightHom_rTensor_apply, ← piRightHom_rTensor_apply, hxy]
  tfae_have 2 → 3 := fun h A => h A (fun _ => R) fun _ => inferInstance
  tfae_have 3 → 1 := by
    intro h
    refine ⟨⟨inferInstance, ?_⟩⟩
    intro I hI
    have hfin : Module.Finite R ↥I := Module.Finite.iff_fg.mpr hI
    have hsurj := ((Module.Finite.tfae_piRightHom_surjective R ↥I).out 1 4).mp hfin
    have hself : Module.FinitePresentation R R := inferInstance
    have hbijR := ((Module.FinitePresentation.tfae_piRightHom_bijective R R).out 1 4).mp hself
    refine ((Module.FinitePresentation.tfae_piRightHom_bijective R ↥I).out 4 1).mp fun A => ?_
    refine ⟨fun x y hxy => ?_, hsurj A⟩
    refine (Module.Flat.iff_rTensor_injective.mp (h A) hI) ?_
    have hR : Bijective (piScalarRightHom R R R A) := hbijR A
    refine hR.injective (funext fun α => ?_)
    rw [piScalarRightHom_rTensor_apply, piScalarRightHom_rTensor_apply, hxy]
  tfae_finish

end Chase

end
