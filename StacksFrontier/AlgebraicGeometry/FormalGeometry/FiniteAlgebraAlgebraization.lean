module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.AlgebraSheafFiniteCoherent
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicThickeningCoherentSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicThickeningUnwinding
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafIsomorphism

/-!
# The residual statements behind the algebra hypothesis of Stacks 09ZT

`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization A I f` is the single input behind the `halg`
hypotheses of Stacks 09ZT, 0A42 and 0899
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/FiniteAlgebraization.lean`). It reduces to
**Grothendieck existence for coherent modules with support proper over the base** — the
equivalence asserted by Stacks 088F, carried by
`AlgebraicGeometry.adicThickeningCompletionFunctor` — together with further residuals. This file
states the residuals; the reduction itself is
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_systemTransport` in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AdicAlgebraStructureProof.lean`,
and the account of the reduction's six steps is in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AdicAlgebraTransport.lean`.

The reduction is not in this file because one of the residuals stated here,
`AlgebraicGeometry.AlgebraSheafProperSupportBridge`, is **no longer a residual**: it is proved, as
`AlgebraicGeometry.algebraSheafProperSupportBridge`, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AlgebraSheafSupport.lean`, and
that file imports this one in order to state it. A reduction that discharges the bridge must
therefore sit downstream of the proof rather than beside the statement.

## The residuals, and why each is a hypothesis

* **Grothendieck existence for coherent modules** —
  `(adicThickeningCompletionFunctor A I f).IsEquivalence`. This is Stacks 088F read through the
  unwinding of `StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicThickeningUnwinding.lean`; the
  module docstring of `AdicThickeningCoherentSystem` records that the one missing input for it is
  Stacks 088E itself, whose carrier
  `Stacks.Algebraization.isEquivalence_completionFunctorProperOver` still takes two named inputs.
  This is the hypothesis the reduction is *for*.

* **The module underlying an algebra pullback.** For `g : T ⟶ S` and a **quasi-coherent** algebra
  sheaf `E` on `S`, `underlyingModule ((algebraPullback g).obj E) ≅
  (Scheme.Modules.pullback g).obj (underlyingModule E)`. This is exactly the hypothesis of
  `Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_underlyingModuleIso`, whose
  file records it as missing: `algebraPullback` is a pushout of sheaves of rings, and Mathlib at
  this pin has no lemma computing the module underlying such a pushout
  (`Stacks.ModuleStalkTensor.comparison` goes one way only, with no `IsIso`, and
  `Stacks.SheafOfModules.AlgebraPushout.underlyingModulePushoutIso` is itself conditional). It is
  needed in the reduction because the transition isomorphisms of the given system are
  isomorphisms of *algebra* sheaves while the systems of Stacks 088F are systems of *modules*.

  The quasi-coherence hypothesis on `E` is **not optional**. The carrier it is meant to feed takes
  `[A.IsQuasicoherent]`, so a form of this statement quantifying over an arbitrary algebra sheaf
  would be strictly stronger than anything the library could ever supply, and discharging it
  would be impossible on principle rather than merely blocked at this pin.

* **The algebra structure on a module algebraization.** A module algebraization of the underlying
  modules of a system of algebra sheaves is the underlying module of an algebra sheaf algebraizing
  the system. This is the one step of the source's recipe that is not module theory: see the
  implementation notes. Its hypothesis list is **coherence of the module, properness of its
  support, the compatibility of the identification with the transitions, and the Stacks 088F
  equivalence**; see the two refutations below for why all four are needed. The live form of this
  residual is `AlgebraicGeometry.AdicAlgebraStructureSystemTransport` in
  `StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AdicAlgebraStructureProof.lean`.
  `AlgebraicGeometry.AdicAlgebraStructureTransport`, stated here, is the form without the fourth
  hypothesis, and it is **false**; it is kept only because the refutation below is stated against
  it.

* **`AlgebraicGeometry.AlgebraSheafProperSupportBridge`** — stated here, and **proved**: for a
  finite quasi-coherent algebra sheaf, properness of the relative spectrum over the base and
  properness of the support of the underlying module over the base are the same condition. This
  is the identification the module docstring of `FiniteAlgebraization` points at when it says
  that for a finite algebra sheaf "the relative spectrum is finite over the base with image the
  support, so the two readings agree". The proof is
  `AlgebraicGeometry.isProper_relativeSpecToBase_comp_iff_hasProperSupport`; the definition is
  kept because that file is phrased against it.

## Why the arbitrary-module form of `AdicAlgebraStructureTransport` is false

An earlier form of `AdicAlgebraStructureTransport` asked for the algebra structure on an
**arbitrary** `N : X.Modules` — no coherence, no proper support, no equivalence in scope — and
that form is false, which made the reduction that consumes it vacuous. Take `A = ℤ_p`, `I = (p)`,
`X = Spec ℤ_p` and `f = 𝟙`; let `N` be the quasi-coherent sheaf of `M = ℚ_p / ℤ_p`, and let `B n`
be the terminal (zero-ring) algebra sheaf on `adicBaseChange ℤ_p (p) f n`, whose underlying module
is a zero object. The hypothesis holds: `M` is `p`-divisible, so the pullback of `N` to
`Spec (ℤ_p / p ⁿ⁺¹)` is `M / p ⁿ⁺¹ M = 0`, isomorphic to `underlyingModule (B n)` for every `n`.
The conclusion cannot hold. `Stacks.RelativeSpec.AlgebraSheaf.underlyingModule C` is
`SheafOfModules.restrictScalars (structureMap C)` applied to `SheafOfModules.unit (ringSheaf C)`,
so over every open it is the additive group of the commutative ring `C(U)`; hence
`underlyingModule C ≅ N` would force a unital
commutative ring structure on `Γ(N, ⊤) ≅ ℚ_p / ℤ_p`; but in a unital ring whose additive group is
`ℚ_p / ℤ_p` the element `1` has finite additive order `n`, whence `n • x = (n • 1) * x = 0` for
every `x`, so the ring is bounded `n`-torsion — and `ℚ_p / ℤ_p` has elements of order `p ᵏ` for
every `k`. The degenerate escape is closed as well: `IsAdicComplete ⊤ A` forces `A = 0`. Every
hypothesis of this counterexample lies inside those of the reduction — `A` is Noetherian and
`I`-adically complete and `f` is separated of finite type — so it refutes the binder in the form
the reduction used it.

Coherence is what rules it out: `ℚ_p / ℤ_p` is not a finite `ℤ_p`-module. The root cause of the
false form was that `N` was arbitrary, with no coherence, no proper support and no 088F
equivalence in scope, so the descent of the multiplications below had nothing to run on.

## Why `AdicAlgebraStructureTransport` as stated below is false as well

Adding coherence, proper support and the equivalence repaired the counterexample above but left a
second defect, of **quantifier shape**, and the form stated below — the one with those three
hypotheses — is false for it. The hypothesis relates `𝒩` to each `B n` *separately*, by an
isomorphism of modules `𝒩|_{Xₙ} ≅ underlyingModule (B n)` chosen independently for each `n`, with
nothing tying the choice at `n + 1` to the choice at `n`. The conclusion, on the other hand, asks
for a single algebra sheaf `C` on `X` with `(algebraPullback vₙ).obj C ≅ B n` for every `n`, and
that forces the `(B n)` to be a **cartesian** system of algebra sheaves: the transitions
`iₙ : Xₙ ⟶ Xₙ₊₁` satisfy `iₙ ≫ vₙ₊₁ = vₙ`, so pseudofunctoriality of `algebraPullback` turns such
a `C` into isomorphisms `(algebraPullback iₙ).obj (B (n + 1)) ≅ B n`. Those are exactly the
hypothesis `hBtrans` of `AlgebraicGeometry.AdicFiniteAlgebraAlgebraization`, and they are not
among the transport's hypotheses — nor are they a consequence of them, because the algebra
structure on a sheaf of modules is not determined by the module.

A family witnessing the gap, inside the hypotheses of the reduction: let `k` be a field,
`A = k⟦t⟧` — Noetherian and `t`-adically complete — `I = (t)`, `X = Spec A` and `f = 𝟙`, which is
proper, separated and of finite type, so `Xₙ = Spec (A / tⁿ⁺¹)`. Take `𝒩 = 𝒪_X ⊕ 𝒪_X`, free of
rank two, hence coherent with support `X`, which is proper over `A` because `f` is. Take

* `B n = (A / tⁿ⁺¹)[x] / (x²)` for `n ≥ 1`, and
* `B 0 = (A / t) × (A / t) = k × k`.

Every `B n` is a finite quasi-coherent algebra sheaf whose underlying module is free of rank two
over `𝒪_{Xₙ}`, so `𝒩|_{Xₙ} ≅ underlyingModule (B n)` for every `n` and the module hypothesis
holds. But `(algebraPullback i₀).obj (B 1) = (A / t²)[x] / (x²) ⊗_{A/t²} A/t = k[x] / (x²)` is not
isomorphic to `k × k`: one is local with a nonzero nilpotent, the other is reduced with two
idempotents. So no `C` can satisfy the conclusion, and the transport fails at this `A`, `I`, `f`.
The antecedent `(adicThickeningCompletionFunctor A I f).IsEquivalence` is Grothendieck existence
for the identity of a complete affine base, which is what Stacks 088E asserts, so the implication
is not vacuous. (The degenerate variant `A = k`, `I = ⊥`, where every `Xₙ` is `Spec k` and `vₙ` is
an isomorphism, refutes it in the same way with no `t` in sight.)

The two halves of that argument are formalized in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AdicAlgebraStructureProof.lean`:
`AlgebraicGeometry.nonempty_algebraTransition_of_algebraPullback_iso` is the engine that turns the
conclusion into the transitions, and
`AlgebraicGeometry.not_adicAlgebraStructureTransport_of_not_algebraTransition` turns any single
incompatible family into `¬ AdicAlgebraStructureTransport A I f`. It is stated as an implication
from the incompatibility of two concrete finite algebras because what cannot be discharged in this
library is the *antecedent*: a closed `¬ AdicAlgebraStructureTransport A I f` would have to prove
Stacks 088E first.

The repair hands the transport the data the source's argument actually runs on, and which the one
call site actually has: an isomorphism **of systems** — a morphism of
`AlgebraicGeometry.AdicCoherentModuleSystem`, hence compatible with the transitions — in place of
the family of unrelated isomorphisms. That is
`AlgebraicGeometry.AdicAlgebraStructureSystemTransport`, and
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_systemTransport` runs the reduction off it
to the same conclusion, so the chain to the `halg` hypotheses of Stacks 09ZT, 0A42 and 0899 is
unaffected. Coherence and proper support are not weakened by the repair: they are the two
components of the `Stacks.Algebraization.CoherentModulesProperOver f` the repaired binder takes.

## Implementation notes

**The algebra structure is not a map of sheaves of rings that full faithfulness can move.** An
object of `Stacks.RelativeSpec.AlgebraSheaf X = Under X.sheaf` is a sheaf of commutative rings
together with a map from `𝒪_X`, so algebraizing the system `(B n)` asks for a *new sheaf of
rings* whose module of sections is the prescribed `𝒩`; full faithfulness of a functor on modules
moves morphisms, not ring structures. The source's argument is therefore the one the docstring of
`FiniteAlgebraization` describes: the multiplications `ℳₙ ⊗ ℳₙ ⟶ ℳₙ`
(`Stacks.RelativeSpec.AlgebraSheaf.multiplication`) form a morphism of systems out of the system
`(ℳₙ ⊗ ℳₙ)`, and full faithfulness produces `𝒩 ⊗ 𝒩 ⟶ 𝒩` from it. That is what makes coherence
and proper support of `𝒩` indispensable: they are what puts `𝒩` and its tensor square in
`Stacks.Algebraization.CoherentModulesProperOver f`, the domain on which the 088F equivalence is
full and faithful.

The inputs that argument needs are in these states in this library:

* the monoidal comparison is **available and unconditional** — `g^*(ℱ ⊗ 𝒢) ≅ g^*ℱ ⊗ g^*𝒢` is
  `Stacks.RingedSpace.comparisonBifunctorIso` (Stacks 01CD), with the full `Functor.Monoidal`
  structure on the pullback in
  `Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`;
* the constructor turning a sheaf of modules with an associative, commutative, unital
  multiplication into an object of `Under X.sheaf` is **available**:
  `Stacks.FundamentalGroup.algebraSheafOfModule`, its data structure
  `Stacks.FundamentalGroup.ModuleAlgebraData` and the identification
  `Stacks.FundamentalGroup.algebraSheafOfModuleIso` of its underlying module with the prescribed
  one are
  `StacksFrontier/AlgebraicGeometry/FundamentalGroup/RestrictionEquivalenceOfCompletion.lean`
  lines 1364-1498, with quasi-coherence of the result in
  `Stacks.FundamentalGroup.algebraSheafOfModule_isQuasicoherent` (private there). The step from
  that data to the repaired binder is discharged:
  `AlgebraicGeometry.adicAlgebraStructureSystemTransport_of_moduleAlgebraData` in
  `CompletionProper/AdicAlgebraStructureSystemProof.lean` (under
  `StacksFrontier/AlgebraicGeometry/FormalGeometry/`);
* the full faithfulness of the completion functor in the asymmetric form the descent of the
  *unit* needs is **no longer missing**.
  `Stacks.FundamentalGroup.ModuleAlgebraData.unit` is a map `𝒪_X ⟶ 𝒩`, and `𝒪_X` has full
  support, so it is an object of `Stacks.Algebraization.CoherentModulesProperOver f` only when
  `f` is proper; the 088F equivalence of `adicThickeningCompletionFunctor` is an equivalence of
  that category, so it moves morphisms whose *source* already has proper support and says nothing
  about `Hom (𝒪_X, 𝒩) ≅ lim Hom (𝒪_{Xₙ}, ℳₙ) = lim Γ (Xₙ, ℳₙ)`. The asymmetric comparison
  supplies that bijection, placing no condition on the source, and over a Noetherian
  `I`-adically complete base — which is what the reduction has — it is **unconditional**:
  `Stacks.Algebraization.bijective_completionFunctor_map_unit_of_hasProperSupport_complete` of
  `StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/SheafHomQuotient.lean`, resting
  on `Stacks.Algebraization.isIso_globalSectionsToLimit_of_hasProperSupport`, which is the
  degree-zero theorem on formal functions for a coherent sheaf of proper support — Stacks 087U,
  i.e. Stacks 02OC in degree zero — proved there. (The general-`I` form,
  `Stacks.Algebraization.bijective_completionFunctor_map_unit_of_hasProperSupport` of
  `StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AsymmetricFormalFunctions.lean`,
  still carries that as a binder.) What is **missing** is only
  the comparison of the two pictures on hom-sets out of `𝒪_X`: those statements are about
  `Stacks.Algebraization.completionFunctor X ℐ`, while the systems of this file's reduction are
  those of `adicThickeningCompletionFunctor`, and the bridge between them is at object level only
  (`AlgebraicGeometry.adicThickeningCompletionPushforwardIso`).

**Why the bridge residual is stated at an arbitrary base.** It quantifies over an arbitrary
`g : T ⟶ S` and an arbitrary algebra sheaf rather than over the adic vocabulary, so that
discharging it is a statement about algebra sheaves and the relative spectrum with no adic
hypotheses — which is what it is, and it is now discharged in that generality.

**Quasi-coherence is an explicit argument throughout**, as in
`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization` itself and for the reason recorded in
`StacksFrontier/AlgebraicGeometry/AlgebraSheafFiniteCoherent.lean`: `Scheme.Modules` is a plain
`def` for `SheafOfModules _`, so instance search does not see through it and the finiteness and
coherence predicates are passed positionally.

## References

* [Stacks Project, Tag 09ZT](https://stacks.math.columbia.edu/tag/09ZT)
* [Stacks Project, Tag 088E](https://stacks.math.columbia.edu/tag/088E)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence
open Stacks.RelativeSpec (AlgebraSheaf)

universe u

namespace AlgebraicGeometry

open Stacks.Algebraization (HasProperSupport)

/-! ### Components of an isomorphism of systems -/

/-- **The `n`-th component of an isomorphism of systems of Stacks 088F.** A morphism of systems is
a family of morphisms of modules, and composition and the identity are computed componentwise, so
an isomorphism of systems is componentwise an isomorphism. -/
public def AdicCoherentModuleSystem.isoApp {A : Type u} [CommRing A] {I : Ideal A}
    {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} [LocallyOfFiniteType f]
    {F G : AdicCoherentModuleSystem A I f} (e : F ≅ G) (n : ℕ) :
    F.obj n ≅ G.obj n where
  hom := e.hom.app n
  inv := e.inv.app n
  hom_inv_id := congrArg (fun h : F ⟶ F => h.app n) e.hom_inv_id
  inv_hom_id := congrArg (fun h : G ⟶ G => h.app n) e.inv_hom_id

/-! ### The residuals -/

/-- **For a finite quasi-coherent algebra sheaf, properness of the relative spectrum over the base
and properness of the support of the underlying module over the base are the same condition.**

This is the identification between the two readings of the properness clauses of Grothendieck
existence: Stacks 088F states them through the support of a coherent module, while
`AlgebraicGeometry.AdicFiniteAlgebraAlgebraization` states them through the relative spectrum.
For a finite algebra sheaf the relative spectrum is finite over the base
(`Stacks.AffineAlgebraEquivalence.isFinite_relativeSpecToBase`), hence universally closed with
image the support of the underlying module, which is what makes the two agree.

It is **no longer a hypothesis**: it is proved, as
`AlgebraicGeometry.algebraSheafProperSupportBridge`, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AlgebraSheafSupport.lean`, through
the support computation `SheafOfModules.supp (underlyingModule E) =
Set.range (relativeSpecToBase E).base` that this definition used to record as missing. It is kept
as a definition because that file states its theorem against it, and because the reduction
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_systemTransport` — which discharges it
rather than taking it — reads more plainly for naming the condition. -/
public def AlgebraSheafProperSupportBridge : Prop :=
  ∀ {T S : Scheme.{u}} (g : T ⟶ S) [LocallyOfFiniteType g] (E : AlgebraSheaf T)
    (hqc : AlgebraSheaf.IsQuasicoherent E), AlgebraSheaf.IsFinite E →
      (IsProper (@relativeSpecToBase _ E hqc ≫ g) ↔
        HasProperSupport g (AlgebraSheaf.underlyingModule E))

/-- **The algebra structure on a module algebraization, in a form that is FALSE.** This
definition is retired: it is kept only as the subject of the refutation
`AlgebraicGeometry.not_adicAlgebraStructureTransport_of_not_algebraTransition`, and no theorem of
this library takes it as a hypothesis any more. The live form of the residual is
`AlgebraicGeometry.AdicAlgebraStructureSystemTransport`, and the reduction run off it is
`AlgebraicGeometry.adicFiniteAlgebraAlgebraization_of_systemTransport`, both in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/AdicAlgebraStructureProof.lean`.

What it asserts: given a system `(B n)` of algebra sheaves on the adic thickenings, the
equivalence of Stacks 088F, and a **coherent** `𝒪_X`-module `𝒩` **with support proper over the
base** whose restriction to every thickening is isomorphic to the module underlying `B n`, the
module `𝒩` carries an algebra structure realizing the system: there is an algebra sheaf `C` on `X`
with `underlyingModule C ≅ 𝒩` and `(algebraPullback vₙ).obj C ≅ B n` for every `n`.

**Why it is false**: the restriction isomorphisms are chosen independently at each `n`, while the
conclusion forces the `(B n)` to be a cartesian system of algebra sheaves, which the underlying
modules cannot see. See "Why `AdicAlgebraStructureTransport` as stated below is false as well" in
the module docstring for the defect and for the counterexample over `A = k⟦t⟧` with
`B 1 = (A/t²)[x]/(x²)` and `B 0 = k × k`. The repair adds the transitions and replaces the family
of isomorphisms by an isomorphism of systems; it keeps coherence and proper support, which the
earlier refutation in the module docstring shows are indispensable.

This is the step of the proof of Stacks 09ZT that is not module theory — an object of
`Stacks.RelativeSpec.AlgebraSheaf X = Under X.sheaf` is a sheaf of commutative *rings*, and
nothing about a module produces one. The source transports the multiplications
`Stacks.RelativeSpec.AlgebraSheaf.multiplication` of the `B n` across the module equivalence; see
the implementation notes of this file for the inputs that needs and for where the library keeps
them. -/
public def AdicAlgebraStructureTransport (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] : Prop :=
  (adicThickeningCompletionFunctor A I f).IsEquivalence →
  ∀ (B : ∀ n : ℕ, AlgebraSheaf (adicBaseChange A I f n)) (N : X.Modules),
    _root_.SheafOfModules.IsCoherent.{u} N → HasProperSupport f N →
    (∀ n, Nonempty ((Scheme.Modules.pullback (pullback.fst f (adicThickeningι A I n))).obj N ≅
      AlgebraSheaf.underlyingModule (B n))) →
    ∃ C : AlgebraSheaf X, Nonempty (AlgebraSheaf.underlyingModule C ≅ N) ∧
      ∀ n, Nonempty ((algebraPullback (pullback.fst f (adicThickeningι A I n))).obj C ≅ B n)

end AlgebraicGeometry

end
