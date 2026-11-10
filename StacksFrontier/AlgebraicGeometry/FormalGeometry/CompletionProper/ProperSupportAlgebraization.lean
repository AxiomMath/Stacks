module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardCoherent.StalkProduct
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.Devissage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DevissageStep
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ProperSupportAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ProperSerreClass
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.FormalGeometry.ProperSerreClass

/-!
# The Noetherian induction behind the hypothesis `hSupp` of Stacks 088E

Let `A` be a Noetherian ring complete with respect to `I` and let `f : X ⟶ Spec A` be separated,
locally of finite type and quasi-compact. The hypothesis `hSupp` of
`Stacks.Algebraization.isEquivalence_completionFunctorProperOver` asks that a coherent `𝓘`-adic
system whose first term has support proper over `A` be annihilated by the ideal sheaf of a closed
subscheme proper over `A`;
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/ProperSupportAnnihilation.lean`
shows that this is equivalent to properness of the subscheme cut out by one canonical ideal sheaf.

This file carries the **shape of the source's proof** of that statement: it is a Noetherian
induction over the quasi-coherent ideal sheaves of `X`, exactly as the proof of Stacks 088C is,
and its inductive step consumes the comparison map of Stacks 088B through the two Serre
subcategories of [Stacks, Tag 0CYV]. Both halves are proved here unconditionally, as are the
coherence and the proper support of the direct image that the step feeds on. Two binders are
left: [Stacks, Tag 088B] at the hypotheses the source states it with, and the transport of a
coherent adic system to the projective compactification of a Chow modification.

## The source's argument, and where it differs from a descent

The proof of [Stacks, Tag 088E] considers the family

  `Ξ = { 𝒦 ⊆ 𝒪_X quasi-coherent : every system with proper support killed by 𝒦 has a proper
         annihilator }`,

and wants `⊥ ∈ Ξ`. `X` being Noetherian, it suffices to prove `K ∈ Ξ` knowing every strictly
larger ideal sheaf is in `Ξ`. At such a `K` the source applies Chow's lemma to get a proper
surjective `π : Y ⟶ X`, an isomorphism over a dense open `U ⊆ X`, and an open immersion of `Y`
into a `Y'` projective over `A`; pushes the system forward to `Y'`, where its support is proper
and the projective case of Grothendieck existence algebraizes it; concludes by completeness of `A`
that the algebraization does not escape `j(Y)`; and feeds the resulting coherent module
`ℋ = π_*(𝓕'|_Y)` on `X` to [Stacks, Tag 088B], obtaining

  `α : (𝓕_n) ⟶ ℋ ^∧`  with `Ker(α_n)`, `Coker(α_n)` annihilated by `𝒦 ᵗ`,

`𝒦` cutting out `X ∖ U`. `Supp(ℋ)` is proper over `A`, so `ℋ ^∧` has a proper annihilator; the
*kernel* of `α` is killed by `𝒦 ᵗ` and, being a subobject of `(𝓕_n)`, also by `K`, hence by the
join `K ⊔ 𝒦 ᵗ`, which is strictly larger than `K`, so the induction hypothesis applies to it; and
a Serre subcategory containing both the kernel and the target contains `(𝓕_n)`.

**The induction is not an optional packaging of a descent.** It is tempting to try to descend the
annihilator of the algebraization along `π` directly, and that fails for a reason this file makes
precise. The annihilator `J` of `ℋ` does satisfy `V(J) ⊆ π(Supp 𝓕'|_Y)`, proper over `A`, and for
`a` a section of `J` and `s` a section of `𝓕_n` one gets `a · α_n(s) = 0`, hence `a · s ∈ Ker(α_n)`
and so `𝒦 ᵗ · J · 𝓕_n = 0`. But `V(𝒦 ᵗ · J) = (X ∖ U) ∪ V(J)` and the complement of a dense open
is not proper over `A`, so the ideal sheaf produced that way is not admissible. There is no
route around this: the kernel of `𝓕_n ⟶ π_*π^*𝓕_n` is genuinely nonzero, supported on `X ∖ U`,
and only the induction hypothesis can absorb it.

## Main results

* `Stacks.Algebraization.hasProperAnnihilator_iff` — the predicate
  `Stacks.Coherent.HasProperAnnihilator` of [Stacks, Tag 0CYV] is the conclusion of `hSupp`.
* `Stacks.Algebraization.IsSystemAnnihilatedBy.sup` and
  `Stacks.Algebraization.isSystemAnnihilatedBy_of_mono` — annihilation by a join, and annihilation
  of a subobject of a coherent adic system. Unconditional.
* `Stacks.Algebraization.isSystemAnnihilatedBy_pow_kernel` — **the kernel step.** If the levelwise
  kernels of a morphism of coherent adic systems are annihilated by `𝒦 ᵗ`, then so is every term
  of its kernel *in* `Coh(X, 𝓘)`. Unconditional, and the place where the fact that a monomorphism
  of coherent adic systems is not levelwise injective has to be faced.
* `Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_completionFunctor_obj` — the
  completion of a coherent module whose support is proper over the base has a proper annihilator,
  namely the annihilator ideal sheaf of the module. Unconditional.
* `Stacks.Algebraization.hasProperSupport_properPushforwardCoherent` — the direct image along a
  proper morphism of a module with support proper over the base has support proper over the base.
  Unconditional, and the one place [Stacks, Tag 02O5] is consumed.
* `Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_of_comparison` — **the inductive
  step, from the comparison map.** Unconditional.
* `Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_of_devissage` — **the Noetherian
  induction.** Unconditional.
* `Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_chowComparison` — the properness
  statement behind `hSupp`, from the single binder `hChow`, the Chow step of the source, **in its
  repaired disjunctive form**.
* `Stacks.Algebraization.hSupp_of_chowComparison` — the same in the shape of the binder `hSupp` of
  `Stacks.Algebraization.isEquivalence_completionFunctorProperOver`.
* `Stacks.Algebraization.IsDirectImageComparison` — [Stacks, Tag 088B] at the hypotheses the
  source states it with, and
  `Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_of_isDirectImageComparison`:
  it gives the library's `Stacks.Algebraization.IsProperDirectImageComparison` at the source's own
  isomorphism hypothesis.
* `Stacks.Algebraization.isEquivalence_completionFunctor_of_isDirectImageComparison` —
  [Stacks, Tag 088C] for a proper morphism from that hypothesis alone, which is what
  `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProperDirectImageComparison` does
  from the library's spelling: nothing downstream of 088B needs more than the source's hypothesis.
* `Stacks.Algebraization.chowComparison_of_isDirectImageComparison` and
  `Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport` — `hChow`, and hence the
  properness statement behind `hSupp`, from 088B together with the transport of the system to the
  compactification, the transport binder `hTransport` again being disjunctive.
* `Stacks.Algebraization.exists_isSystemAnnihilatedBy_top_isProper_systemAnnihilatorIdeal` — the
  witness of the refutation below: a coherent adic system killed by `⊤` whose support is proper
  over `A` and which **already has a proper annihilator**, so that it discharges the degenerate
  disjunct of each repaired binder. Unconditional.
* `Stacks.Algebraization.ChowComparisonDefective`,
  `Stacks.Algebraization.TransportDefective` and the refutations
  `Stacks.Algebraization.not_chowComparisonDefective`,
  `Stacks.Algebraization.not_transportDefective` — the pre-repair forms of the two binders,
  restated locally and **refuted**, so that the account below is kernel-checked.

## Why the library's spelling of Stacks 088B is not the one this needs

The source applies 088B **over the base `X`**, which in Stacks 088E is separated and of finite
type over `A` and *not proper* over `A`; the lemma's own hypotheses ask only that the base be a
Noetherian scheme and that `π` be proper. This library's
`Stacks.Algebraization.IsProperDirectImageComparison` is 088B with its base morphism
`f : X ⟶ Spec A` **assumed proper**, as is the general-base
`Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage` from
which it is cut: properness of the base is what discharges that statement's binder `hff`, full
faithfulness of completion upstairs, through
`Stacks.Algebraization.fullyFaithful_completionFunctor_comap_of_isProper`. Neither
`IsProperDirectImageComparison A I` nor `hff` can therefore be instantiated at the point Stacks
088E uses 088B — `Y` there is quasi-projective over `A`, not proper over it — so the binder below
is `Stacks.Algebraization.IsDirectImageComparison`, which is the same statement with the
properness of the base deleted and the source's hypothesis on `π` kept, and which serves every
consumer of the library's spelling
(`Stacks.Algebraization.isEquivalence_completionFunctor_of_isDirectImageComparison`). The source
needs no such hypothesis: its reduction is to an affine base, over which full faithfulness comes
from the formal functions theorem for `π`.

## Implementation notes: the refuted form of `IsDirectImageComparison`, and the repair

`Stacks.Algebraization.IsDirectImageComparison` was first stated with the source's hypothesis on
`π` replaced by its *consequence*

`hc : ∀ 𝒜, (𝓖 ≅ 𝒜 ^∧) → IsIso ((𝒜 ⟶ π_*π^*𝒜) |_{X ∖ V(𝒦)})`,

the form `Stacks.Algebraization.IsProperDirectImageComparison` carries. **That form is false**;
the refutation is
`Stacks.Algebraization.essImage_of_isDirectImageComparison`
(`CompletionProper/DirectImageComparisonGeneral.lean`), which derives from it that a coherent adic
system whose pullback along *some* proper morphism is a completion is itself a completion.

The defect is that `hc` quantifies over the algebraizations of `(𝓖_n)` and is therefore **vacuous
whenever `(𝓖_n)` has none** — which, at a general base with no completeness anywhere, is the
normal state of affairs and is exactly the difficulty 088B is about. Read at `𝒦 = ⊤`: then
`V(𝒦) = ∅`, so `hc` asks for nothing, while `IsKernelCokernelAnnihilatedByPower ⊤ α` forces the
levelwise kernels and cokernels to have empty support ([Stacks, Tag 01Y9],
`AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset`) hence to vanish, so `α` is a
levelwise isomorphism and `(𝓖_n) ≅ (π_*𝓕) ^∧`. Taking `π = 𝓙.subschemeι`, along which `𝓙` pulls
back to `⊥` so that every pullback system is constant and hence a completion, that algebraizes
*every* coherent adic system on *every* Noetherian scheme: unrestricted Grothendieck existence,
with no completeness of anything. It is refuted by the counterexample of
`CompletionCriteria/AffineExistenceDescent.lean` — a finite `B ^∧`-module at the local ring of a
node which is not the base change of a finite `B`-module.

**`Stacks.Algebraization.IsProperDirectImageComparison` is not affected and is not changed.**
There the base `X` is proper over a complete `A`, so every object of `Coh(X, 𝓘)` is a completion
by Stacks 088C and `hc` always has content; the substitution is harmless precisely because of the
properness that the definition below deletes, which is why the defect surfaces only at a general
base. A binder phrased through `hc` cannot travel with that deletion.

The repair is to ask the source's hypothesis itself, `IsIso (π ∣_ 𝒦.support.compl)`, which implies
`hc` by
`Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit` — the
implication `Stacks.Algebraization.chowComparison_of_isDirectImageComparison` was already using,
and the one every consumer of `IsProperDirectImageComparison` in this library supplies its `hc`
from. So no consumer loses anything, and
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isDirectImageComparison` recovers the
whole of Stacks 088C for a proper morphism from the repaired form. What the repair does cost is
the bare implication `IsDirectImageComparison → IsProperDirectImageComparison`: `hc` being the
weaker hypothesis, the `hc` form is the *stronger* statement, and the implication runs the other
way. In its place
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_of_isDirectImageComparison`
records the specialization to a proper base morphism at the source's hypothesis.

## Implementation notes: the refuted join clause, and the repair

The binders `hChow` and `hTransport` below were first stated with the join clause

`hpow : ∀ e, K < K ⊔ 𝒦 ᵉ⁺¹`

asked of **every** quasi-coherent ideal sheaf `K` of `X` and every coherent adic system with
proper support killed by `K`. **In that form they are false**, and the refutation is
machine-checked at the end of this file: `Stacks.Algebraization.not_chowComparisonDefective` and
`Stacks.Algebraization.not_transportDefective` refute the locally restated pre-repair forms
`Stacks.Algebraization.ChowComparisonDefective` and `Stacks.Algebraization.TransportDefective`.

Read them at `K = ⊤` and at the **zero** system. It is a coherent adic system; it is killed by
`⊤`, every ideal sheaf killing it; and its support is empty, hence proper over `A` — both facts
come from the zero object of `Coh(X, 𝓘)`, through [Stacks, Tag 0CYV] part (1)
(`Stacks.Coherent.isSerreClass_hasProperSupport`), whose Serre subcategory contains it. The
hypotheses of the binder are therefore met, while its conclusion demands
`∀ e, ⊤ < ⊤ ⊔ 𝒦 ᵉ⁺¹`, i.e. `⊤ < ⊤` (`AlgebraicGeometry.Scheme.IdealSheafData.ideal_top` and the
`OrderTop` of that lattice). The same reading refutes the binder `hJoin` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_join`, which isolates the clause.

**The defect is a transplanted hypothesis, not a missing lemma.** The source of
[Stacks, Tag 088E] runs Chow's lemma not on `X` but on `V(K)`, so that the dense open it produces
meets `V(K)`; the clause then holds because `𝒦 ᵉ⁺¹ ≤ K` would force `V(K) ⊆ X ∖ U`. At `K = ⊤`
there is no `V(K)` to run it on, and there the source has nothing to prove. Carrying the clause
over to `X` kept the inductive step and dropped the base case. Compare
`Stacks.IdealSheafData.lt_map_subschemeι_pow_succ`
(`StacksFrontier/AlgebraicGeometry/Scheme/SubschemeIdealJoin.lean`), which is the clause as the
replaced induction can actually consume it — at the *inverse images* `(𝒦₀ ᵉ⁺¹).map K.subschemeι`
of powers computed in `V(K)`, out of `𝒦₀.support ≠ ⊤` alone.

**The repair is a disjunction**, the one
`Stacks.Algebraization.IsDirectImageComparison` was given above: *either* the system already has
a proper annihilator — `IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f)`, which by
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_iff` is the whole of what is wanted
of the system and leaves nothing to do — *or* the Chow data with the join clause exists. No
conclusion is weakened: a disjunction is the weaker *hypothesis*, so each theorem below is
strictly stronger than before, and `hpow` remains the only form the inductive step
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_of_comparison` consumes — it is
unchanged. What the repair costs is that a supplier of the binder must now say which disjunct it
is in; the degenerate one is reachable, which is the content of
`Stacks.Algebraization.exists_isSystemAnnihilatedBy_top_isProper_systemAnnihilatorIdeal`: at the
very witness that refutes the old form, the repaired form is satisfied outright.

## What the transport binder is, and what of it this library already has

`hTransport` asks, at every quasi-coherent ideal sheaf `K` and every system with proper support
killed by `K`, either for a proper annihilator of the system already — the degenerate disjunct of
the repair above — or for a proper `π : Y ⟶ X`, an open `U` over which `π` is an isomorphism and
whose complement cuts out an ideal sheaf no power of which lies below `K`, and a coherent
`𝒪_Y`-module `G` with support proper over `A` together with the source's isomorphism
`β : π^*(𝓕_n) ≅ G ^∧`.
Every geometric ingredient of it is in this library:
`Stacks.Algebraization.exists_isOpenImmersion_isProjectiveMorphism_denseChowModification`
(Chow's lemma with a projective compactification, unconditional),
`Stacks.Algebraization.isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds` (the projective
case of Grothendieck existence, unconditional),
`Stacks.Algebraization.supp_subset_of_mem_zeroLocus_imp_mem` (the escape of the support, which is
where completeness of `A` is consumed) and
`AlgebraicGeometry.isClosedImmersion_subschemeι_vanishingIdeal_comp` (the coherence of `j_*` of a
sheaf with proper support). What is missing is the functor pushing a coherent adic system on `Y`
forward along the open immersion `j : Y ⟶ Y'`, without which the system cannot be presented on the
compactification and `β` cannot be produced; and the source's replacement of `X` by `V(K)` before
the Chow step, which is what makes the join condition on `K` available.

## References

* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0CYV](https://stacks.math.columbia.edu/tag/0CYV)
* [Stacks Project, Tag 02OM](https://stacks.math.columbia.edu/tag/02OM)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent

/-! ### The conclusion of `hSupp` is the Serre class of Stacks 0CYV -/

/-- The conclusion of the hypothesis `hSupp` of Stacks 088E — that some closed subscheme proper
over the base has its ideal sheaf annihilating every term of the system — is membership in the
Serre subcategory `Stacks.Coherent.HasProperAnnihilator` of [Stacks, Tag 0CYV]. The two are the
same statement, `Stacks.Algebraization.IsSystemAnnihilatedBy` being annihilation of every term. -/
public theorem hasProperAnnihilator_iff {X S : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ S)
    [LocallyOfFiniteType f] (ℐ : X.IdealSheafData) (𝓕 : CoherentAdicSystems ℐ) :
    HasProperAnnihilator f ℐ 𝓕 ↔
      ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧ IsSystemAnnihilatedBy J 𝓕.obj :=
  Iff.rfl

/-! ### Annihilation by a join, and annihilation of a subobject -/

/-- **Annihilation by two ideal sheaves is annihilation by their join.** The sections of `𝒥 ⊔ 𝒦`
over an affine open are sums of a section of `𝒥` and a section of `𝒦`
(`AlgebraicGeometry.Scheme.IdealSheafData.ideal_sup`), and each of the two summands kills every
section of every term.

This is what makes the family the source's induction runs over the family of *joins* `K ⊔ 𝒦 ᵉ⁺¹`
rather than the family of powers `𝒦 ᵉ⁺¹`: a subobject of a system killed by `K` is killed by `K`,
so a subobject killed in addition by `𝒦 ᵉ⁺¹` is killed by the join, which is where the induction
hypothesis lives. -/
public theorem IsSystemAnnihilatedBy.sup {X : Scheme.{u}} {J K : X.IdealSheafData}
    {F : ℕᵒᵖ ⥤ X.Modules} (hJ : IsSystemAnnihilatedBy J F) (hK : IsSystemAnnihilatedBy K F) :
    IsSystemAnnihilatedBy (J ⊔ K) F := by
  intro n
  have hJf := (idealPowerMultiple_eq_bot_iff_affine_sections_annihilated J 1
    (F.obj (op n))).1 (hJ n)
  have hKf := (idealPowerMultiple_eq_bot_iff_affine_sections_annihilated K 1
    (F.obj (op n))).1 (hK n)
  rw [idealPowerMultiple_eq_bot_iff_affine_sections_annihilated]
  intro U r hr x
  rw [pow_one] at hr
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hr
  rw [add_smul, hJf U a (by rwa [pow_one]), hKf U b (by rwa [pow_one]), add_zero]

/-- A system with a monomorphism into another is annihilated by `L` once the levelwise kernels of
the cokernel projection are, since each term is an epimorphic image of such a kernel. -/
private theorem isSystemAnnihilatedBy_of_kernel_cokernel_app {X : Scheme.{u}} [IsNoetherian X]
    {ℐ : X.IdealSheafData} (L : X.IdealSheafData) {𝓐 𝓑 : CoherentAdicSystems ℐ} (i : 𝓐 ⟶ 𝓑)
    [Mono i]
    (h : ∀ m : ℕ, idealPowerMultiple L 1 (kernel ((cokernel.π i).hom.app (op m))) = ⊥) :
    IsSystemAnnihilatedBy L 𝓐.obj := by
  intro n
  have hT : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    ⟨ShortComplex.exact_cokernel i⟩
  obtain ⟨m, e, he⟩ := exists_epi_kernel_app ℐ _ hT n
  have := he
  exact Stacks.Coherent.idealPowerMultiple_eq_bot_of_epi L e (h m)

/-- **Annihilation of a coherent adic system by an ideal sheaf passes to subobjects.** A
monomorphism of coherent adic systems is not levelwise injective, so this is not immediate: the
terms of the subobject are reached through `Stacks.Coherent.exists_epi_kernel_app`, as quotients
of levelwise kernels of the cokernel projection, and those are subsheaves of the terms of the
ambient system.

The same argument appears inside the `CategoryTheory.ObjectProperty.IsClosedUnderSubobjects`
clause of `Stacks.Coherent.isSerreClass_hasProperAnnihilator`, where it is applied to the ideal
sheaf of a closed subscheme proper over the base; this is the statement at a bare ideal sheaf,
which is what the induction over ideal sheaves consumes. -/
public theorem isSystemAnnihilatedBy_of_mono {X : Scheme.{u}} [IsNoetherian X]
    (ℐ L : X.IdealSheafData) {𝓐 𝓑 : CoherentAdicSystems ℐ} (i : 𝓐 ⟶ 𝓑) [Mono i]
    (h : IsSystemAnnihilatedBy L 𝓑.obj) : IsSystemAnnihilatedBy L 𝓐.obj :=
  isSystemAnnihilatedBy_of_kernel_cokernel_app L i fun m =>
    Stacks.Coherent.idealPowerMultiple_eq_bot_of_mono L
      (kernel.ι ((cokernel.π i).hom.app (op m))) (h m)

/-! ### Annihilation by one ideal sheaf, out of annihilation by a power -/

/-- Annihilation of a sheaf of modules by `𝒦 ᵗ` is annihilation by the single ideal sheaf
`𝒦 ᵗ`, which is the form the family `Ξ` of the source's induction is indexed by. -/
private theorem idealPowerMultiple_pow_one_eq_bot {X : Scheme.{u}} {K : X.IdealSheafData} {t : ℕ}
    {M : X.Modules} (h : idealPowerMultiple K t M = ⊥) :
    idealPowerMultiple (K ^ t) 1 M = ⊥ :=
  le_antisymm ((idealPowerMultiple_le_of_pow_le (pow_one (K ^ t)).le M).trans h.le) bot_le

/-! ### The kernel of a morphism of coherent adic systems -/

/-- **The kernel step of the source's induction.** Let `α` be a morphism of coherent adic systems
whose *levelwise* kernels are annihilated by a power `𝒦 ᵗ` of a quasi-coherent ideal sheaf. Then
every term of the kernel of `α` taken *in* `Coh(X, 𝓘)` is annihilated by `𝒦 ᵗ`, so the kernel is
killed by the single ideal sheaf `𝒦 ᵗ`.

This is not a formality: a monomorphism of coherent adic systems need not be levelwise injective,
so the terms of the kernel are not subsheaves of the terms of the source. They are reached, by
`Stacks.Coherent.exists_epi_kernel_app`, as quotients of levelwise kernels of the cokernel
projection of `Ker(α) ⟶ (𝓕_n)` at a possibly higher level; and such a levelwise kernel embeds in
the levelwise kernel of `α` at that level because `α` factors through that cokernel projection.
Annihilation then passes down the mono and up the epi. -/
public theorem isSystemAnnihilatedBy_pow_kernel {X : Scheme.{u}} [IsNoetherian X]
    (ℐ K : X.IdealSheafData) {𝓕 𝓗 : CoherentAdicSystems ℐ} (α : 𝓕 ⟶ 𝓗) {t : ℕ}
    (hα : ∀ n : ℕ, idealPowerMultiple K t (kernel (α.hom.app (op n))) = ⊥) :
    IsSystemAnnihilatedBy (K ^ t) (kernel α).obj := by
  refine isSystemAnnihilatedBy_of_kernel_cokernel_app (K ^ t) (kernel.ι α) fun m => ?_
  -- the levelwise kernel of the cokernel projection embeds in the levelwise kernel of `α`
  have hz : kernel.ι ((cokernel.π (kernel.ι α)).hom.app (op m)) ≫ α.hom.app (op m) = 0 := by
    have hfac : (cokernel.π (kernel.ι α)).hom.app (op m) ≫
        (cokernel.desc (kernel.ι α) α (kernel.condition α)).hom.app (op m) = α.hom.app (op m) :=
      congrArg (fun z : 𝓕 ⟶ 𝓗 => z.hom.app (op m)) (cokernel.π_desc _ _ _)
    rw [← hfac, ← Category.assoc, kernel.condition, zero_comp]
  have : Mono (kernel.lift (α.hom.app (op m))
      (kernel.ι ((cokernel.π (kernel.ι α)).hom.app (op m))) hz) :=
    mono_of_mono_fac (kernel.lift_ι _ _ _)
  exact Stacks.Coherent.idealPowerMultiple_eq_bot_of_mono (K ^ t)
    (kernel.lift (α.hom.app (op m))
      (kernel.ι ((cokernel.π (kernel.ι α)).hom.app (op m))) hz)
    (idealPowerMultiple_pow_one_eq_bot (hα m))

/-! ### The completion of a module with proper support -/

/-- **The target of the comparison map has a proper annihilator.** The completion along `𝓘` of a
coherent module `ℋ` whose support is proper over the base is annihilated by the annihilator ideal
sheaf of `ℋ`, whose closed subscheme is the scheme-theoretic support of `ℋ` and is therefore
proper over the base.

Each term of the completion is a quotient of `ℋ`, so an ideal sheaf killing `ℋ` kills it; the
annihilator ideal sheaf kills `ℋ` by `Stacks.Algebraization`
`.le_annihilatorIdeal_iff_idealPowerMultiple_one_eq_bot`, and its closed subset is the support of
`ℋ` by [Stacks, Tag 02OM] (`AlgebraicGeometry.supp_eq_support_annihilatorIdeal`), on which
properness of a closed subset does not depend on the subscheme structure chosen
([Stacks, Tag 0CYL]). -/
public theorem exists_isProper_isSystemAnnihilatedBy_completionFunctor_obj {X S : Scheme.{u}}
    [IsLocallyNoetherian X] (f : X ⟶ S) [LocallyOfFiniteType f] (ℐ : X.IdealSheafData)
    (ℋ : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
    (hℋ : HasProperSupport f ℋ.obj) :
    ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
      IsSystemAnnihilatedBy J ((completionFunctor X ℐ).obj ℋ).obj := by
  have : _root_.SheafOfModules.IsCoherent.{u} ℋ.obj := ℋ.property
  obtain ⟨Z, hZ, hZp⟩ := hℋ
  refine ⟨annihilatorIdeal ℋ.obj, ?_, fun n => ?_⟩
  · have hle : (annihilatorIdeal ℋ.obj).support ≤ Z := by
      refine le_of_eq (TopologicalSpace.Closeds.ext ?_)
      exact (hZ.trans (supp_eq_support_annihilatorIdeal ℋ.obj)).symm
    exact (exists_isProper_iff_forall_isProper f _).1
      ((isProperOver_iff_exists_isProper f _).1 (isProperOver_of_le f hle hZp)) _ rfl
  · have := epi_completionProjection X ℐ ℋ n
    exact Stacks.Coherent.idealPowerMultiple_eq_bot_of_epi _ (completionProjection X ℐ ℋ n)
      ((le_annihilatorIdeal_iff_idealPowerMultiple_one_eq_bot ℋ.obj _).1 le_rfl)

/-! ### The proper direct image of a module with proper support -/

/-- **The direct image along a proper morphism of a coherent module whose support is proper over
the base again has support proper over the base.** This is the step "if `Z₀` is the
scheme-theoretic support of `ℋ = π_*𝓕` then `Z₀ ⊆ π(Z')` set-theoretically, hence `Z₀` is proper
over `A`" of the proof of [Stacks, Tag 088E], `Z'` being the support of `𝓕`.

The support of a direct image along a closed morphism is contained in the image of the support
(`Stacks.Chow.supp_pushforward_subset_image`), the image of a closed subset proper over the base
is closed and proper over the base ([Stacks, Tag 0CYQ],
`AlgebraicGeometry.isProperOver_closedImage`), and a closed subset of such is again proper over
the base ([Stacks, Tag 0CYN]). Coherence of the direct image is [Stacks, Tag 02O5],
`Stacks.Algebraization.properPushforwardCoherent`. -/
public theorem hasProperSupport_properPushforwardCoherent {Y X S : Scheme.{u}}
    [IsNoetherian Y] [IsNoetherian X] (π : Y ⟶ X) [IsProper π] (f : X ⟶ S)
    [LocallyOfFiniteType f]
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (hG : HasProperSupport (π ≫ f) G.obj) :
    HasProperSupport f (properPushforwardCoherent π G).obj := by
  have : _root_.SheafOfModules.IsCoherent.{u} G.obj := G.property
  have : G.obj.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType (M := G.obj)
  have : _root_.SheafOfModules.IsCoherent.{u} (properPushforwardCoherent π G).obj :=
    (properPushforwardCoherent π G).property
  have : (properPushforwardCoherent π G).obj.IsFiniteType :=
    _root_.SheafOfModules.IsCoherent.isFiniteType (M := (properPushforwardCoherent π G).obj)
  obtain ⟨Z, hZ, hZp⟩ := hG
  refine ⟨⟨_root_.SheafOfModules.supp (properPushforwardCoherent π G).obj,
    _root_.SheafOfModules.isClosed_supp _⟩, rfl,
    isProperOver_of_le f ?_ (isProperOver_closedImage π f Z hZp)⟩
  change _root_.SheafOfModules.supp (properPushforwardCoherent π G).obj ⊆
    π.base '' (Z : Set Y)
  rw [hZ]
  exact Stacks.Chow.supp_pushforward_subset_image π G.obj
    (_root_.SheafOfModules.isClosed_supp G.obj)

/-! ### The inductive step, from the comparison map of Stacks 088B -/

/-- **The inductive step of the proof of Stacks 088E.** Let `K` be the quasi-coherent ideal sheaf
being inducted on and suppose given

* `hpow`, that every join `K ⊔ 𝒦 ᵉ⁺¹` with a power of a quasi-coherent ideal sheaf `𝒦` is
  strictly larger than `K`, equivalently that no power of `𝒦` lies below `K` — on the subscheme
  of `K`, where the source does its Chow step, `K` is `⊥` and this says that no power of `𝒦`
  vanishes, which holds because `𝒦` cuts out the complement of a dense open. The family of joins,
  rather than of powers, is the family the source's induction is consumed at, because the ideal
  sheaves of the Chow step are ideal sheaves of `V(K)`; and
* `hInd`, the induction hypothesis: every coherent `𝓘`-adic system whose first term has support
  proper over the base and which is killed by an ideal sheaf strictly larger than `K` is
  annihilated by the ideal sheaf of a closed subscheme proper over the base.

Then a system with proper support admitting the comparison data of [Stacks, Tag 088B] — a
coherent module `ℋ` with support proper over the base and a morphism `α : (𝓕_n) ⟶ ℋ ^∧` whose
levelwise kernels and cokernels are annihilated by a power of `𝒦` — is annihilated by the ideal
sheaf of a closed subscheme proper over the base.

The proof is the source's last paragraph. The target `ℋ ^∧` is annihilated by a proper ideal
sheaf, `Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_completionFunctor_obj`. The
kernel of `α` in `Coh(X, 𝓘)` is killed by `𝒦 ᵗ` by
`Stacks.Algebraization.isSystemAnnihilatedBy_pow_kernel`, is killed by `K` as a subobject of
`(𝓕_n)` (`Stacks.Algebraization.isSystemAnnihilatedBy_of_mono`) and hence by the join
(`Stacks.Algebraization.IsSystemAnnihilatedBy.sup`), and has support proper over the base,
properness of the support cutting out a Serre subcategory ([Stacks, Tag 0CYV], part (1)); so
`hInd` applies to it at `K ⊔ 𝒦 ᵗ`. Since `0 ⟶ Ker(α) ⟶ (𝓕_n) ⟶ ℋ ^∧` is exact and a common
proper annihilator also cuts out a Serre subcategory ([Stacks, Tag 0CYV], part (2)), the middle
term is in it. Only the kernel of `α` is used; the cokernel bound of 088B is not needed for this
statement. -/
public theorem exists_isProper_isSystemAnnihilatedBy_of_comparison {X S : Scheme.{u}}
    [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (ℐ K 𝒦 : X.IdealSheafData) (hpow : ∀ e : ℕ, K < K ⊔ 𝒦 ^ (e + 1))
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ K' : X.IdealSheafData, K < K' →
        ∀ 𝓖 : CoherentAdicSystems ℐ, IsSystemAnnihilatedBy K' 𝓖.obj →
          HasProperSupport f (𝓖.obj.obj (op 0)) →
            ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
              IsSystemAnnihilatedBy J 𝓖.obj) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ (𝓕 : CoherentAdicSystems ℐ), IsSystemAnnihilatedBy K 𝓕.obj →
      HasProperSupport f (𝓕.obj.obj (op 0)) →
      ∀ (ℋ : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf),
        HasProperSupport f ℋ.obj →
          ∀ α : 𝓕.obj ⟶ ((completionFunctor X ℐ).obj ℋ).obj,
            IsKernelCokernelAnnihilatedByPower 𝒦 α →
              ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
                IsSystemAnnihilatedBy J 𝓕.obj := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { }
  intro 𝓕 hK h𝓕 ℋ hℋ α hα
  have hSA : (HasProperAnnihilator f ℐ).IsSerreClass := isSerreClass_hasProperAnnihilator f ℐ
  have hSS : ObjectProperty.IsSerreClass (C := CoherentAdicSystems ℐ)
      (fun F => HasProperSupport f (F.obj.obj (op 0))) := isSerreClass_hasProperSupport f ℐ
  obtain ⟨t, ht, hkc⟩ := hα
  set α' : 𝓕 ⟶ (completionFunctor X ℐ).obj ℋ := ObjectProperty.homMk α with hα'
  have hkerann : IsSystemAnnihilatedBy (K ⊔ 𝒦 ^ t) (kernel α').obj :=
    (isSystemAnnihilatedBy_of_mono ℐ K (kernel.ι α') hK).sup
      (isSystemAnnihilatedBy_pow_kernel ℐ 𝒦 α' fun n => (hkc n).1)
  have hkersupp : HasProperSupport f ((kernel α').obj.obj (op 0)) :=
    ObjectProperty.prop_of_mono (fun F : CoherentAdicSystems ℐ =>
      HasProperSupport f (F.obj.obj (op 0))) (kernel.ι α') h𝓕
  obtain ⟨e, rfl⟩ : ∃ e : ℕ, t = e + 1 := ⟨t - 1, by omega⟩
  have hkerS : HasProperAnnihilator f ℐ (kernel α') :=
    hInd (K ⊔ 𝒦 ^ (e + 1)) (hpow e) (kernel α') hkerann hkersupp
  exact (HasProperAnnihilator f ℐ).prop_X₂_of_exact (ShortComplex.exact_kernel α') hkerS
    (exists_isProper_isSystemAnnihilatedBy_completionFunctor_obj f ℐ ℋ hℋ)

/-! ### The Noetherian induction -/

/-- **The Noetherian induction of the proof of Stacks 088E.** Let `X` be a scheme of finite type
over a Noetherian base and `𝓘` a quasi-coherent ideal sheaf on it. Suppose that for every
quasi-coherent ideal sheaf `K` the inductive step holds: if every coherent `𝓘`-adic system with
proper support killed by an ideal sheaf strictly larger than `K` is annihilated by the ideal sheaf
of a closed subscheme proper over the base, then so is every coherent `𝓘`-adic system with proper
support killed by `K`. Then *every* coherent `𝓘`-adic system whose first term has support proper
over the base is annihilated by the ideal sheaf of a closed subscheme proper over the base — which
is the conclusion of the hypothesis `hSupp` of Stacks 088E.

This is well-founded induction along the strict-superset relation on `X.IdealSheafData`, which is
well-founded by `AlgebraicGeometry.Scheme.IdealSheafData.wellFoundedGT_of_isNoetherian`, read at
the zero ideal sheaf, which kills every system by
`Stacks.Algebraization.isSystemAnnihilatedBy_bot`. The source runs the same induction in
contrapositive form, choosing an ideal sheaf maximal outside the family `Ξ`. -/
public theorem exists_isProper_isSystemAnnihilatedBy_of_devissage {X S : Scheme.{u}}
    [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (ℐ : X.IdealSheafData)
    (hDev : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ K : X.IdealSheafData,
        (∀ K' : X.IdealSheafData, K < K' →
            ∀ 𝓖 : CoherentAdicSystems ℐ, IsSystemAnnihilatedBy K' 𝓖.obj →
              HasProperSupport f (𝓖.obj.obj (op 0)) →
                ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
                  IsSystemAnnihilatedBy J 𝓖.obj) →
          ∀ 𝓕 : CoherentAdicSystems ℐ, IsSystemAnnihilatedBy K 𝓕.obj →
            HasProperSupport f (𝓕.obj.obj (op 0)) →
              ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
                IsSystemAnnihilatedBy J 𝓕.obj) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓕 : CoherentAdicSystems ℐ, HasProperSupport f (𝓕.obj.obj (op 0)) →
      ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧ IsSystemAnnihilatedBy J 𝓕.obj := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { }
  let : WellFoundedGT X.IdealSheafData :=
    AlgebraicGeometry.Scheme.IdealSheafData.wellFoundedGT_of_isNoetherian X
  have key : ∀ K : X.IdealSheafData, ∀ 𝓕 : CoherentAdicSystems ℐ,
      IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
        ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
          IsSystemAnnihilatedBy J 𝓕.obj := by
    intro K
    induction K using WellFoundedGT.induction with
    | ind K ih => exact hDev K ih
  exact fun 𝓕 h => key ⊥ 𝓕 (isSystemAnnihilatedBy_bot 𝓕.obj) h

/-! ### The properness statement behind `hSupp`, from the Chow step -/

/-- **The properness statement behind `hSupp`, reduced to the Chow step of Stacks 088E.** Let `A`
be Noetherian and complete with respect to `I` and let `f : X ⟶ Spec A` be separated, locally of
finite type and quasi-compact. Suppose `hChow`: at every quasi-coherent ideal sheaf `K` of `X`,
every coherent `𝓘`-adic system with support proper over `A` killed by `K` **either already has a
proper annihilator** — the closed subscheme of
`Stacks.Algebraization.systemAnnihilatorIdeal` being proper over `A`, which by
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_iff` is the whole of what is wanted
of that system — *or* admits the comparison data of [Stacks, Tag 088B]: an ideal sheaf `𝒦` no
power of which lies below `K`, a coherent module `ℋ` with support proper over `A`, and a morphism
`(𝓕_n) ⟶ ℋ ^∧` whose levelwise kernels and cokernels are annihilated by a power of `𝒦`. Then the
closed subscheme cut out by `Stacks.Algebraization.systemAnnihilatorIdeal` is proper over `A` for
every coherent `𝓘`-adic system whose first term has support proper over `A`.

**The disjunction is the repair of a refutable hypothesis, and is not optional.** Asking the
comparison data at *every* `K` is false at `K = ⊤`, where the join clause reads `⊤ < ⊤`; see the
module docstring and `Stacks.Algebraization.not_chowComparisonDefective`. The degenerate disjunct
is the base case the source has and the transplanted clause lost: it costs the induction nothing,
since it is literally the conclusion wanted of the system at that stage.

Everything besides `hChow` is proved: the Noetherian induction is
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_of_devissage`, its step is
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_of_comparison` — which consumes the
join clause unchanged, the repair being confined to the binder — and the passage from the
existential to properness of the one canonical ideal sheaf is
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_iff`, which shows the existential
carries no content and which is also what turns the degenerate disjunct into the goal of the
inductive step. Completeness of `A` is consumed inside `hChow` and nowhere else, which is the
source's own accounting; see the module docstring for the state of its ingredients. -/
public theorem isProper_systemAnnihilatorIdeal_of_chowComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hChow : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ (K : X.IdealSheafData) (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)),
        IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
          IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f) ∨
            ∃ 𝒦 : X.IdealSheafData, (∀ e : ℕ, K < K ⊔ 𝒦 ^ (e + 1)) ∧
              ∃ ℋ : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
                HasProperSupport f ℋ.obj ∧
                  ∃ α : 𝓕.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj ℋ).obj,
                    IsKernelCokernelAnnihilatedByPower 𝒦 α) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I f),
      HasProperSupport f (𝓖.obj.obj (op 0)) →
        IsProper ((systemAnnihilatorIdeal 𝓖).subschemeι ≫ f) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro 𝓖 h𝓖
  refine (exists_isProper_isSystemAnnihilatedBy_iff f 𝓖).1 ?_
  refine exists_isProper_isSystemAnnihilatedBy_of_devissage f (baseIdealSheaf A I f)
    (fun K hInd 𝓕 hK h𝓕 => ?_) 𝓖 h𝓖
  rcases hChow K 𝓕 hK h𝓕 with hdone | ⟨𝒦, hpow, ℋ, hℋ, α, hα⟩
  · -- the degenerate disjunct: the canonical annihilator of this system is already proper
    exact (exists_isProper_isSystemAnnihilatedBy_iff f 𝓕).2 hdone
  · exact exists_isProper_isSystemAnnihilatedBy_of_comparison f (baseIdealSheaf A I f) K 𝒦 hpow
      hInd 𝓕 hK h𝓕 ℋ hℋ α hα

/-- **The hypothesis `hSupp` of Stacks 088E, from the Chow step.** The previous theorem read
through `Stacks.Algebraization.hSupp_of_isProper_systemAnnihilatorIdeal`: this is verbatim the
binder `hSupp` of `Stacks.Algebraization.isEquivalence_completionFunctorProperOver`, proved from
`hChow` alone — `hChow` in the repaired disjunctive form of the previous theorem, the form asking
the comparison data at every `K` being refutable; see the module docstring. -/
public theorem hSupp_of_chowComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hChow : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ (K : X.IdealSheafData) (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)),
        IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
          IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f) ∨
            ∃ 𝒦 : X.IdealSheafData, (∀ e : ℕ, K < K ⊔ 𝒦 ^ (e + 1)) ∧
              ∃ ℋ : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
                HasProperSupport f ℋ.obj ∧
                  ∃ α : 𝓕.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj ℋ).obj,
                    IsKernelCokernelAnnihilatedByPower 𝒦 α) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I f),
      HasProperSupport f (𝓖.obj.obj (op 0)) →
        ∃ J : X.IdealSheafData, IsProper (J.subschemeι ≫ f) ∧
          IsSystemAnnihilatedBy J 𝓖.obj :=
  hSupp_of_isProper_systemAnnihilatorIdeal A I f
    (isProper_systemAnnihilatorIdeal_of_chowComparison A I f hChow)

/-! ### Stacks 088B at a base that need not be proper over the affine base -/

/-- **[Stacks, Tag 088B], at the hypotheses the source states it with.** Let `X` be a Noetherian
scheme, let `𝓙, 𝒦 ⊆ 𝒪_X` be quasi-coherent sheaves of ideals, let `π : Y ⟶ X` be proper with `Y`
Noetherian and set `ℐ = π^{-1}𝓙 𝒪_Y`. Given a coherent `𝒪_Y`-module `𝓕`, an object `(𝓖_n)` of
`Coh(X, 𝓙)`, the source's isomorphism `β : π^*(𝓖_n) ≅ 𝓕 ^∧` in `Coh(Y, ℐ)` and the source's
hypothesis that `π` **is an isomorphism over** `X ∖ V(𝒦)`, there is a morphism
`α : (𝓖_n) ⟶ (π_*𝓕) ^∧` whose levelwise kernels and cokernels are annihilated by a power of `𝒦`.

This is `Stacks.Algebraization.IsProperDirectImageComparison` with its base `Spec A` replaced by
an arbitrary Noetherian scheme, its `baseIdealSheaf A I f` by an arbitrary quasi-coherent ideal
sheaf, and its hypothesis `[IsProper f]` on the base morphism deleted — equivalently, it is
`Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage` with
*both* of its binders `halg` and `hff` deleted. The deletion of `[IsProper f]` is not cosmetic and
is not optional here: the proof of [Stacks, Tag 088E] applies 088B over its own `X`, which is
separated and of finite type over `A` and not proper over `A`, so neither
`IsProperDirectImageComparison A I` nor the `hff` of the general-base statement — which is
discharged only by properness over `A`, through
`Stacks.Algebraization.fullyFaithful_completionFunctor_comap_of_isProper` — is available at the
point of use. The source needs none of them: its reduction is to an *affine base*, over which
full faithfulness comes from the formal functions theorem for `π`.

**The isomorphism binder is the source's own hypothesis and is not interchangeable with its
consequence.** `IsProperDirectImageComparison` asks instead for

`hc : ∀ 𝒜, (𝓖 ≅ 𝒜 ^∧) → IsIso ((𝒜 ⟶ π_*π^*𝒜) |_{X ∖ V(𝒦)})`,

the restriction of the adjunction unit at every algebraization of `(𝓖_n)`, which `IsIso (π ∣_
𝒦.support.compl)` implies by
`Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit`. Over a base
that is proper over a complete `A` the two are equally strong, every object of `Coh(X, 𝓘)` being a
completion there; with the properness of the base deleted they are not, and the `hc` form is
**false** — see the module docstring. -/
public def IsDirectImageComparison : Prop :=
  ∀ {Y X : Scheme.{u}} [IsNoetherian Y] [IsNoetherian X]
    (π : Y ⟶ X) [IsProper π] (𝓙 𝒦 : X.IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
    (𝓖 : CoherentAdicSystems 𝓙),
    ((coherentAdicPullback π 𝓙).obj 𝓖 ≅ (completionFunctor Y (𝓙.comap π)).obj 𝓕) →
      IsIso (π ∣_ 𝒦.support.compl) →
        ∃ α : 𝓖.obj ⟶ ((completionFunctor X 𝓙).obj (properPushforwardCoherent π 𝓕)).obj,
          IsKernelCokernelAnnihilatedByPower 𝒦 α

/-- **Stacks 088B at a general base, read at a base morphism proper over `Spec A`.** Instantiating
`Stacks.Algebraization.IsDirectImageComparison` at a base morphism `f : X ⟶ Spec A` that happens
to be proper and at the base ideal sheaf of `f` gives
`Stacks.Algebraization.IsProperDirectImageComparison A I` with its binder `hc` replaced by the
source's own hypothesis that `π` is an isomorphism over `X ∖ V(𝒦)`, with nothing left to
discharge.

It is *not* `IsProperDirectImageComparison A I` itself, and cannot be: `hc` is the weaker
hypothesis of the two, so a statement carrying `hc` is the stronger statement, and the
implication runs the other way. That asymmetry is harmless — every consumer of
`IsProperDirectImageComparison` in this library supplies its `hc` out of
`IsIso (π ∣_ 𝒦.support.compl)` through
`Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit`, so this form
serves each of them;
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isDirectImageComparison` carries that out
and recovers the whole of [Stacks, Tag 088C] from the hypothesis below. See the module docstring
for why the `hc` form cannot travel with the deletion of `[IsProper f]`. -/
public theorem exists_isKernelCokernelAnnihilatedByPower_of_isDirectImageComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (h : IsDirectImageComparison.{u})
    {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X]
    (f : X ⟶ Spec (.of A)) (π : X' ⟶ X) [IsProper π] [IsProper f]
    (𝒦 : X.IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (𝓖 : CoherentAdicSystems (baseIdealSheaf A I f))
    (β : (coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓖 ≅
      (completionFunctor X' ((baseIdealSheaf A I f).comap π)).obj 𝓕)
    (hπ : IsIso (π ∣_ 𝒦.support.compl)) :
    ∃ α : 𝓖.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsKernelCokernelAnnihilatedByPower 𝒦 α :=
  h π (baseIdealSheaf A I f) 𝒦 𝓕 𝓖 β hπ

/-! ### Stacks 088C for a proper morphism, from Stacks 088B at a general base -/

/-- If `π` is an isomorphism over an open `U`, it is one over the complement of the support of the
vanishing ideal sheaf of `Uᶜ`, which is `U`. -/
private theorem isIso_restrict_support_compl_vanishingIdeal {Y X : Scheme.{u}} (π : Y ⟶ X)
    (U : X.Opens) (h : IsIso (π ∣_ U)) :
    IsIso (π ∣_ (Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)).support.compl) := by
  have h1 : (Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)).support =
      (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X) :=
    TopologicalSpace.Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  rwa [h1, show (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X).compl = U from
    TopologicalSpace.Opens.ext (compl_compl _)]

/-- **The comparison of Stacks 088A at the Chow data, from Stacks 088B at a general base.** This
is `Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_vanishingIdealCompl` with its
binder `Stacks.Algebraization.IsProperDirectImageComparison A I` replaced by
`Stacks.Algebraization.IsDirectImageComparison`: the proof there supplies the `hc` of
`IsProperDirectImageComparison` from `IsIso (π ∣_ U)` and from nothing else, so the repaired
binder serves it unchanged, the identification of `U` with the complement of the support of the
vanishing ideal of `Y ∖ U` now being handed straight to the hypothesis instead of through
`Stacks.Algebraization.isIso_restrictFunctor_map_pullbackPushforwardAdjunction_unit`. -/
public theorem exists_isKernelCokernelAnnihilatedByPower_vanishingIdeal_of_isDirectImageComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (h088B : IsDirectImageComparison.{u})
    {Y X' : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [IsProper g] (π : X' ⟶ Y) [IsProper π]
    (U : Y.Opens) (hproj : AlgebraicGeometry.IsProjectiveMorphism (π ≫ g))
    (hiso : IsIso (π ∣_ U)) :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
    ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I g),
      ∃ (H : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf)
        (α : 𝓖.obj ⟶ ((completionFunctor Y (baseIdealSheaf A I g)).obj H).obj),
        IsKernelCokernelAnnihilatedByPower
          (Scheme.IdealSheafData.vanishingIdeal
            (⟨(U : Set Y)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds Y)) α := by
  let _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  let _ : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  let _ : IsNoetherian Y := { }
  have _ : IsProper (π ≫ g) := isProper_of_isProjectiveMorphism (π ≫ g) hproj
  let _ : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (π ≫ g)
  let _ : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (π ≫ g)
  let _ : IsNoetherian X' := { }
  -- the projective case of Grothendieck existence on the modification
  have hEq : (completionFunctor X' ((baseIdealSheaf A I g).comap π)).IsEquivalence := by
    rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I g π]
    exact isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds A I (π ≫ g) hproj
  intro 𝓖
  -- the source's `β`: the algebraization upstairs of the termwise pullback of the system
  obtain ⟨𝓕, ⟨e⟩⟩ : (completionFunctor X' ((baseIdealSheaf A I g).comap π)).essImage
      ((coherentAdicPullback π (baseIdealSheaf A I g)).obj 𝓖) :=
    Functor.EssSurj.mem_essImage _ _
  exact ⟨properPushforwardCoherent π 𝓕,
    h088B π (baseIdealSheaf A I g) _ 𝓕 𝓖 e.symm
      (isIso_restrict_support_compl_vanishingIdeal π U hiso)⟩

/-- **[Stacks, Tag 088C] for a proper morphism, with Stacks 088B at a general base as the only
hypothesis.** Let `A` be a Noetherian ring complete with respect to an ideal `I`, let
`f : X ⟶ Spec A` be proper and set `𝓘 = I · 𝒪_X`. Granted
`Stacks.Algebraization.IsDirectImageComparison` — Stacks 088B at the hypotheses the source states
it with, and nothing else — the completion functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` of Stacks 0880 is an
equivalence.

This is `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProperDirectImageComparison`
with its binder replaced by the repaired one, and it is the reason the repair costs no consumer
anything: the dévissage of Stacks 088C reaches 088B only through
`Stacks.Algebraization.essImage_completionFunctor_of_devissageChowSubscheme`, at Chow data where
`π` *is* an isomorphism over the dense open, so the source's hypothesis is available there and
`hc` was never needed in its own right. Full faithfulness (Stacks 0883), the Noetherian induction
and its base case are proved unconditionally in
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`.

No tag attribute is attached: Stacks 088C is registered on
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`. -/
public theorem isEquivalence_completionFunctor_of_isDirectImageComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    (h088B : IsDirectImageComparison.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence := by
  refine isEquivalence_completionFunctor_of_devissage A I f
    (fun H => isIso_globalSectionsToLimit_of_isProper A I f H) fun K hInd => ?_
  refine essImage_completionFunctor_of_devissageChowSubscheme A I f K hInd ?_
  intro X' π U hπ _ hproj _ hisoU
  have _ := hπ
  rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I f K.subschemeι]
  exact exists_isKernelCokernelAnnihilatedByPower_vanishingIdeal_of_isDirectImageComparison
    A I h088B (K.subschemeι ≫ f) π U hproj hisoU

/-! ### The Chow step, from Stacks 088B and the transport of the system -/

/-- **The comparison data of the inductive step, from Stacks 088B and the transport of the
system.** Suppose given `h088B`, [Stacks, Tag 088B] at the hypotheses the source states it with,
and `hTransport`: at every quasi-coherent ideal sheaf `K` and every coherent `𝓘`-adic system with
support proper over `A` killed by `K`, **either a proper annihilator of the system already** —
properness over `A` of the closed subscheme of
`Stacks.Algebraization.systemAnnihilatorIdeal` — *or* a proper `π : Y ⟶ X`, an open `U ⊆ X` over
which `π` is an isomorphism and whose closed complement cuts out an ideal sheaf no power of which
lies below `K`, and a coherent `𝒪_Y`-module `G` with support proper over `A` together with the
source's isomorphism `β : π^*(𝓕_n) ≅ G ^∧`. Then the binder `hChow` of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_chowComparison` holds, in its matching
disjunctive form: the degenerate disjunct is carried across unchanged, and only the geometric one
goes through 088B.

The disjunction repairs a hypothesis which, asked of every `K`, is refutable at `K = ⊤`; see the
module docstring and `Stacks.Algebraization.not_transportDefective`.

The module `ℋ` is the proper direct image `π_*G`, coherent by [Stacks, Tag 02O5] and with support
proper over `A` by
`Stacks.Algebraization.hasProperSupport_properPushforwardCoherent`; the isomorphism hypothesis of
088B is the `IsIso (π ∣_ U)` that `hTransport` supplies, read through the identification of `U`
with the complement of the support of the vanishing ideal sheaf of `X ∖ U`.

`hTransport` is what the compactification of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ProperSupportCompactification`
is for: Chow's lemma produces `π` and `U`, the projective case of Grothendieck existence
algebraizes the system pushed to `Y'`, and completeness of `A` keeps the support of that
algebraization inside `j(Y)`, which is what makes it restrict to the `G` above. What is not in
this library is the functor pushing a coherent adic system on `Y` forward to `Y'` along the open
immersion `j`, without which `β` cannot be produced. -/
public theorem chowComparison_of_isDirectImageComparison
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f]
    (h088B : IsDirectImageComparison.{u})
    (hTransport : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      letI : IsNoetherian X := { }
      ∀ (K : X.IdealSheafData) (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)),
        IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
          IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f) ∨
            ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (_ : IsProper π) (_ : IsNoetherian Y) (U : X.Opens),
              IsIso (π ∣_ U) ∧
                (∀ e : ℕ, K < K ⊔ (Scheme.IdealSheafData.vanishingIdeal
                    (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)) ^ (e + 1)) ∧
                  ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
                    HasProperSupport (π ≫ f) G.obj ∧
                      Nonempty ((coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓕 ≅
                        (completionFunctor Y ((baseIdealSheaf A I f).comap π)).obj G)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
    letI : IsNoetherian X := { }
    ∀ (K : X.IdealSheafData) (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)),
      IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
        IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f) ∨
          ∃ 𝒦 : X.IdealSheafData, (∀ e : ℕ, K < K ⊔ 𝒦 ^ (e + 1)) ∧
            ∃ ℋ : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
              HasProperSupport f ℋ.obj ∧
                ∃ α : 𝓕.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj ℋ).obj,
                  IsKernelCokernelAnnihilatedByPower 𝒦 α := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { }
  intro K 𝓕 hK h𝓕
  rcases hTransport K 𝓕 hK h𝓕 with hdone | ⟨Y, π, hπ, hY, U, hiso, hpow, G, hG, ⟨β⟩⟩
  · -- the degenerate disjunct is the same statement on both sides
    exact Or.inl hdone
  have := hπ
  have := hY
  refine Or.inr ⟨_, hpow, properPushforwardCoherent π G,
    hasProperSupport_properPushforwardCoherent π f G hG, ?_⟩
  exact h088B π (baseIdealSheaf A I f) _ G 𝓕 β
    (isIso_restrict_support_compl_vanishingIdeal π U hiso)

/-- **The properness statement behind `hSupp`, from Stacks 088B and the transport of the
system.** The composite of
`Stacks.Algebraization.chowComparison_of_isDirectImageComparison` with
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_chowComparison`: the two binders left
are [Stacks, Tag 088B] at the hypotheses the source states it with, and the transport of a
coherent adic system to the projective compactification — the latter in the repaired disjunctive
form, which also carries the source's base case. Everything else — the Noetherian
induction, its inductive step through the two Serre subcategories of [Stacks, Tag 0CYV], the
coherence and proper support of the direct image, the condition `hc` of 088B, and the reduction of
the existential to the canonical ideal sheaf — is proved.

See the module docstring for why the transport binder cannot ask the Chow data at every `K`:
`Stacks.Algebraization.not_transportDefective` refutes that form outright. -/
public theorem isProper_systemAnnihilatorIdeal_of_transport
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (h088B : IsDirectImageComparison.{u})
    (hTransport : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      letI : IsNoetherian X := { }
      ∀ (K : X.IdealSheafData) (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)),
        IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
          IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f) ∨
            ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (_ : IsProper π) (_ : IsNoetherian Y) (U : X.Opens),
              IsIso (π ∣_ U) ∧
                (∀ e : ℕ, K < K ⊔ (Scheme.IdealSheafData.vanishingIdeal
                    (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)) ^ (e + 1)) ∧
                  ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
                    HasProperSupport (π ≫ f) G.obj ∧
                      Nonempty ((coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓕 ≅
                        (completionFunctor Y ((baseIdealSheaf A I f).comap π)).obj G)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓖 : CoherentAdicSystems (baseIdealSheaf A I f),
      HasProperSupport f (𝓖.obj.obj (op 0)) →
        IsProper ((systemAnnihilatorIdeal 𝓖).subschemeι ≫ f) :=
  isProper_systemAnnihilatorIdeal_of_chowComparison A I f
    (chowComparison_of_isDirectImageComparison A I f h088B hTransport)

/-! ### The pre-repair form of the two binders is false as stated -/

/-- The sections of a zero sheaf of modules over any open vanish: its identity is the zero
morphism, and the component of a morphism of sheaves of modules at an open acts on sections. -/
private theorem sections_eq_zero_of_isZero {X : Scheme.{u}} {M : X.Modules} (hM : IsZero M)
    (U : X.Opensᵒᵖ) (x : M.val.obj U) : x = 0 := by
  have hid := (IsZero.iff_id_eq_zero M).mp hM
  have happ := congrArg (fun g : M ⟶ M => g.val.app U x) hid
  rw [show ((𝟙 M : M ⟶ M).val.app U) = 𝟙 _ from rfl,
    show ((0 : M ⟶ M).val.app U) = 0 from rfl] at happ
  simpa using happ

/-- **A zero inverse system is killed by every quasi-coherent ideal sheaf**, in particular by `⊤`.
Each of its terms is a zero object (`CategoryTheory.Functor.isZero_iff`), so every section over
every affine open vanishes and is annihilated by anything at all. -/
private theorem isSystemAnnihilatedBy_of_isZero {X : Scheme.{u}} (K : X.IdealSheafData)
    {F : ℕᵒᵖ ⥤ X.Modules} (hF : IsZero F) : IsSystemAnnihilatedBy K F := by
  intro n
  rw [idealPowerMultiple_eq_bot_iff_affine_smul_top]
  intro U
  rw [Submodule.eq_bot_iff]
  intro x _
  exact sections_eq_zero_of_isZero (F.isZero_iff.1 hF (op n)) (op U.1) x

/-- **The witness that refutes the pre-repair binders and satisfies the repaired ones.** Let `A`
be Noetherian and `f : X ⟶ Spec A` locally of finite type and quasi-compact. There is a coherent
`𝓘`-adic system which is annihilated by the unit ideal sheaf `⊤`, whose first term has support
proper over `A`, and whose canonical annihilator `Stacks.Algebraization.systemAnnihilatorIdeal`
already cuts out a closed subscheme proper over `A` — so it meets the hypotheses of the binders
`hChow` and `hTransport` at `K = ⊤` while discharging their degenerate disjunct outright.

It is a zero object of `Coh(X, 𝓘)`, and all three clauses come from the two Serre subcategories of
[Stacks, Tag 0CYV]: a Serre class contains a zero object
(`CategoryTheory.ObjectProperty.ContainsZero`), which for
`Stacks.Algebraization.HasProperSupport` of the first term
(`Stacks.Coherent.isSerreClass_hasProperSupport`) is the proper support and for
`Stacks.Coherent.HasProperAnnihilator`
(`Stacks.Coherent.isSerreClass_hasProperAnnihilator`) is the proper annihilator, read through
`Stacks.Algebraization.exists_isProper_isSystemAnnihilatedBy_iff`. Annihilation by `⊤` is
the vanishing of every section of every term. No completeness of `A` and no
separatedness of `f` is used. -/
public theorem exists_isSystemAnnihilatedBy_top_isProper_systemAnnihilatorIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∃ 𝓕 : CoherentAdicSystems (baseIdealSheaf A I f),
      IsSystemAnnihilatedBy ⊤ 𝓕.obj ∧ HasProperSupport f (𝓕.obj.obj (op 0)) ∧
        IsProper ((systemAnnihilatorIdeal 𝓕).subschemeι ≫ f) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { }
  have hSS : ObjectProperty.IsSerreClass (C := CoherentAdicSystems (baseIdealSheaf A I f))
      (fun F => HasProperSupport f (F.obj.obj (op 0))) :=
    isSerreClass_hasProperSupport f (baseIdealSheaf A I f)
  have hSA : (HasProperAnnihilator f (baseIdealSheaf A I f)).IsSerreClass :=
    isSerreClass_hasProperAnnihilator f (baseIdealSheaf A I f)
  obtain ⟨𝓕, h0, hsupp⟩ := ObjectProperty.exists_prop_of_containsZero
    (fun F : CoherentAdicSystems (baseIdealSheaf A I f) => HasProperSupport f (F.obj.obj (op 0)))
  refine ⟨𝓕, isSystemAnnihilatedBy_of_isZero ⊤
    ((isZero_coherentAdicSystems_iff _ 𝓕).1 h0), hsupp, ?_⟩
  exact (exists_isProper_isSystemAnnihilatedBy_iff f 𝓕).1
    ((HasProperAnnihilator f (baseIdealSheaf A I f)).prop_of_isZero h0)

/-- **The pre-repair form of the binder `hChow`** of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_chowComparison`, which asked the
comparison data of [Stacks, Tag 088B] — with the join clause `∀ e, K < K ⊔ 𝒦 ᵉ⁺¹` — at *every*
quasi-coherent ideal sheaf `K` and every coherent adic system with proper support killed by `K`,
with no degenerate disjunct.

The live binder has since been **repaired** and is disjunctive. The defective form is restated
here solely so that its refutation,
`Stacks.Algebraization.not_chowComparisonDefective`, stays machine-checked; nothing in the library
depends on it. -/
public def ChowComparisonDefective (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] : Prop :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  ∀ (K : X.IdealSheafData) (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)),
    IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
      ∃ 𝒦 : X.IdealSheafData, (∀ e : ℕ, K < K ⊔ 𝒦 ^ (e + 1)) ∧
        ∃ ℋ : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
          HasProperSupport f ℋ.obj ∧
            ∃ α : 𝓕.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj ℋ).obj,
              IsKernelCokernelAnnihilatedByPower 𝒦 α

/-- **The pre-repair form of the binder `hTransport`** of
`Stacks.Algebraization.isProper_systemAnnihilatorIdeal_of_transport` and
`Stacks.Algebraization.chowComparison_of_isDirectImageComparison`: the Chow data with the join
clause asked at every `K`, with no degenerate disjunct. Restated for the sake of
`Stacks.Algebraization.not_transportDefective`; nothing depends on it. -/
public def TransportDefective (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f] : Prop :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : IsNoetherian X := { }
  ∀ (K : X.IdealSheafData) (𝓕 : CoherentAdicSystems (baseIdealSheaf A I f)),
    IsSystemAnnihilatedBy K 𝓕.obj → HasProperSupport f (𝓕.obj.obj (op 0)) →
      ∃ (Y : Scheme.{u}) (π : Y ⟶ X) (_ : IsProper π) (_ : IsNoetherian Y) (U : X.Opens),
        IsIso (π ∣_ U) ∧
          (∀ e : ℕ, K < K ⊔ (Scheme.IdealSheafData.vanishingIdeal
              (⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds X)) ^ (e + 1)) ∧
            ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules Y.ringCatSheaf,
              HasProperSupport (π ≫ f) G.obj ∧
                Nonempty ((coherentAdicPullback π (baseIdealSheaf A I f)).obj 𝓕 ≅
                  (completionFunctor Y ((baseIdealSheaf A I f).comap π)).obj G)

/-- **The pre-repair form of `hChow` is false.** Read it at `K = ⊤` and at the zero system of
`Stacks.Algebraization.exists_isSystemAnnihilatedBy_top_isProper_systemAnnihilatorIdeal`: the
hypotheses are met — the system is annihilated by `⊤` and its support is empty, hence proper over
`A` — while the conclusion demands an ideal sheaf `𝒦` with `⊤ < ⊤ ⊔ 𝒦 ᵉ⁺¹`, and
`⊤ ⊔ 𝒦 ᵉ⁺¹ = ⊤`.

The hypothesis is not merely unproved: it is refuted, for every `A`, `I` and `f`, with no
nonemptiness and no completeness anywhere. Nothing is lost by repairing it, because at this very
witness the repaired binder's degenerate disjunct holds; see the module docstring. -/
public theorem not_chowComparisonDefective
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f] :
    ¬ ChowComparisonDefective A I f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro h
  obtain ⟨𝓕, hann, hsupp, -⟩ :=
    exists_isSystemAnnihilatedBy_top_isProper_systemAnnihilatorIdeal A I f
  obtain ⟨𝒦, hpow, -⟩ := h ⊤ 𝓕 hann hsupp
  exact absurd (hpow 0) (by rw [top_sup_eq]; exact lt_irrefl _)

/-- **The pre-repair form of `hTransport` is false**, by the same reading as
`Stacks.Algebraization.not_chowComparisonDefective`: the join clause on the ideal sheaf cutting
out the complement of the Chow open is `⊤ < ⊤` at `K = ⊤`, where the zero system meets every
hypothesis. The geometric clauses of the binder are not reached; it is the clause on the lattice
of ideal sheaves alone that fails, which is why the repair is the degenerate disjunct and not a
change to the Chow data. -/
public theorem not_transportDefective
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f] :
    ¬ TransportDefective A I f := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { }
  intro h
  obtain ⟨𝓕, hann, hsupp, -⟩ :=
    exists_isSystemAnnihilatedBy_top_isProper_systemAnnihilatorIdeal A I f
  obtain ⟨Y, π, hπ, hY, U, hiso, hpow, -⟩ := h ⊤ 𝓕 hann hsupp
  exact absurd (hpow 0) (by rw [top_sup_eq]; exact lt_irrefl _)

end Stacks.Algebraization

end
