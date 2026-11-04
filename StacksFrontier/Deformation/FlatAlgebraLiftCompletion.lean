module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.Deformation.FlatAlgebraLift
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.AdicCompletion.LiftToComplete
public import StacksFrontier.RingTheory.AdicCompletion.MapOfPowLe
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.Quotient
public import StacksFrontier.RingTheory.Localization.Idempotent
public import StacksFrontier.RingTheory.Smoothing.LiftingAlongSurjections

/-!
# Deformations of completions

Let `A' → A` be a surjection of Noetherian rings with nilpotent kernel, let `B` be a finite
type flat `A`-algebra and let `𝔟 ⊆ B` be an ideal such that `A → B_h` is syntomic for every
`h ∈ 𝔟`. Stacks 0DZ3 says that `B` has a flat lift to `A'` if and only if its `𝔟`-adic
completion does. This file proves its two implications assuming Stacks 0DZ2; the equivalence
itself, without that assumption, is
`Deformation.hasFlatAlgebraLift_iff_hasFlatAlgebraLift_adicCompletion` of
`StacksFrontier.Deformation.FlatAlgebraLiftCompletionNilpotent`.

The proof is the source's. Choose a surjection `P = A[x_1, …, x_n] → B`, let `P'` be the
polynomial algebra over `A'` and let `𝔭' ⊆ P'` be the preimage of `𝔟`. Flat algebra lifts of
`B` to `A'` are the same thing as `A'`-flat `P'`-module lifts of `B`, because a lift is a
quotient of `P'` by Nakayama; likewise over the `𝔭'`-adic completion `Q'` of `P'`, whose base
change `Q = P ⊗_{P'} Q'` presents the completion of `B`. The map `P' → Q'` is flat and induces
`P'/𝔭' = Q'/𝔭'Q'`, so the two module-lifting problems are compared by Stacks 0DZ2, whose local
liftability hypothesis is supplied by Stacks 07M8: `B_h` is syntomic over `A`, hence has a flat
lift, which the comparison turns into a module lift over `(P')_g`.

## Main definitions

* `Deformation.FlatModuleLiftBaseChangeStatement`: the statement of Stacks 0DZ2, as the source
  states it.
* `Deformation.FlatModuleLiftBaseChangeStatementFaithful`: the same, with the source's
  `Module.Flat A P` written out as well, so that nothing of the source is left implicit. It is
  equivalent to the previous one, because that hypothesis is redundant.

## Main results

* `Deformation.flat_of_surjective_of_ker_eq_map`: the lower horizontal arrow of a cartesian
  square is flat when the upper one is; this is why `Module.Flat A P` is redundant.
* `Deformation.flatModuleLiftBaseChangeStatement_of_faithful`,
  `Deformation.flatModuleLiftBaseChangeStatementFaithful_of_statement`: the two statements of
  Stacks 0DZ2 above are equivalent.
* `Deformation.hasFlatAlgebraLift_of_syntomic`: a syntomic algebra has a flat lift, which is
  Stacks 07M8 read as a lifting statement.
* `Deformation.exists_algEquiv_tensorBaseChange`: the base change of a `P'`-algebra along
  `A' → A` agrees with its base change along `P' → P`.
* `Deformation.bijective_quotientMap_adicCompletion`: `P'/I' = (P')^∧/I'(P')^∧`.
* `Deformation.hasFlatAlgebraLift_adicCompletion_of_hasFlatAlgebraLift`: the implication from
  `B` to its completion, assuming Stacks 0DZ2.
* `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion`: the implication from
  the completion back to `B`, assuming Stacks 0DZ2.
* **Stacks 0DZ3**, the equivalence, is
  `Deformation.hasFlatAlgebraLift_iff_hasFlatAlgebraLift_adicCompletion` of
  `StacksFrontier.Deformation.FlatAlgebraLiftCompletionNilpotent`, which does not assume 0DZ2.

## Implementation notes

**`h0DZ2` IS FALSE, so this file's conditional theorems are vacuous.**
`Deformation.FlatModuleLiftBaseChangeStatement` — Stacks 0DZ2 at the source's hypotheses,
restricted to a finite module — is refuted by
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement` of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutation`, a term of type
`¬ FlatModuleLiftBaseChangeStatement.{0}` whose counterexample module is
finite and cyclic, so the finiteness restriction does not save it. The same statement at an
arbitrary universe is refuted by
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement_ulift` of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutationUniverse`, which instantiates 0DZ2
at the `ULift`s of the counterexample's six rings; so the vacuity of the theorems below holds at
their own universe parameter `u` and not merely at `u = 0`. Everything below that takes
`h0DZ2` as a hypothesis is therefore vacuously true and establishes nothing. The `_of_sqZero`
variants are not the repair, because Stacks 0DZ3 (Lemma 93.12.3) says `nilpotent kernel`. What
is left open is the route through the consumers: there `M` comes from a syntomic `B_h`, where
the higher `Ext` carrying the obstruction vanishes, so the obstruction cannot arise — extra
vanishing that 0DZ2's own hypotheses do not supply. Settling those three tags by that route is
not done here.

**The defect is the source's, not this file's rendering of it.** The obvious objection to the
previous paragraph is that `FlatModuleLiftBaseChangeStatement` might be stronger than Stacks
0DZ2 — that a hypothesis of the source was dropped and the counterexample exploits its absence.
One hypothesis *is* absent: the source's "flat horizontal arrows" covers `A → P` as well as
`A' → P'`, `P' → Q'` and `P → Q`, and only the last three are written out below.
`Deformation.FlatModuleLiftBaseChangeStatementFaithful` restores it, and
`Deformation.flat_of_surjective_of_ker_eq_map` shows it is redundant: `P` is `A ⊗_{A'} P'` by
the left-hand cartesian square, so it is `A`-flat because `P'` is `A'`-flat. The two statements
are therefore equivalent, by
`Deformation.flatModuleLiftBaseChangeStatement_of_faithful` and
`Deformation.flatModuleLiftBaseChangeStatementFaithful_of_statement`, and the refutation
transports: `Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatementFaithful`
of `StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutationFaithful`. Nothing else of the
source is missing below — `Module.Flat A' Q'` is carried and is the composite of two arrows the
source does assume, nilpotence of `ker(P' → P)` and `ker(Q' → Q)` is implied by nilpotence of
`ker(A' → A)`, and `Module.Finite P M` is an *addition*, which the source's own proof uses and
its statement omits. So **Stacks 0DZ2, Lemma 93.12.2, is false as stated**; the step that fails
is its `details omitted` induction from `Iⁿ = 0` to `I² = 0`, and the diagnosis is in the module
documentation of `StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutationFaithful`.

**The hypothesis `h0DZ2`.** `FlatModuleLiftBaseChangeStatement` is Stacks 0DZ2 written out,
restricted to a finite module, which is all the proof below uses: two cartesian squares of
Noetherian rings with flat horizontal maps and surjective vertical maps with nilpotent kernels,
an ideal `J'` of `P'` with `P'/J' = Q'/J'Q'`, and a `P`-module `M` finite over `P` and flat
over `A` whose localization `M_g` has an `A'`-flat `(P')_g`-module lift for every `g ∈ J'`. The
cartesian condition is carried by the kernel identities `ker(P' → P) = ker(A' → A) · P'` and
`ker(Q' → Q) = ker(A' → A) · Q'` together with the scalar towers, which is the form the proof
of 0DZ3 produces and consumes. It is assumed here and not derived from the proved forms of
0DZ2. Those are `StacksFrontier.Deformation.FlatModuleLiftBaseChange`, which demands that the
obstruction morphism of `M` be `J`-power torsion, and
`StacksFrontier.Deformation.FlatModuleLiftLocalization`, which carries the tag and does assume the
source's local liftability — so the torsion gap is closed. What still separates the proved form
from `FlatModuleLiftBaseChangeStatement` is that it assumes the kernel of `A' → A` square-zero
rather than nilpotent, the dévissage between the two being left to the reader by the source,
and that it states `P` and `Q` as the literal base changes `P' ⊗_{A'} A` and `Q' ⊗_{A'} A`
rather than as abstract rings carrying the kernel identities, so a transport along
`P ≅ A ⊗_{A'} P'` is still owed.

**The syntomic hypothesis.** It is stated as syntomy of `A → B_h` for every `h ∈ 𝔟`, which is
the affine reading of "`Spec(B) → Spec(A)` is syntomic on the complement of `V(𝔟)`": that
complement is covered by the opens `D(h)`, `h ∈ 𝔟`, and syntomy is local on the source. This
is also the form Stacks 07M8 consumes.

**The second implication.** It is the same comparison read backwards, and what it needs is a
lift of the presentation along `Q'`. Let `C` be the completion of `B` and let `C'` be a flat
algebra lift of `C` to `A'`. The reduction `C' → C` is a surjection with nilpotent finitely
generated kernel, so `C'` is complete along that kernel and therefore Noetherian; the preimage
`c'` of `𝔟C` then makes `C'` adically complete by Stacks 0DYC, after transporting
`IsAdicComplete` across `C'/ker(C' → C) ≅ C`. The presentation `P' → C` lifts to `C'` by formal
smoothness and `AdicCompletion.exists_algHom_of_isAdicComplete` extends it to `Q' → C'`; the
extension agrees with the structure map of `C` over `Q'` because the two maps out of `Q'` agree
on `P'` and `C` is `𝔟C`-adically Hausdorff
(`AdicCompletion.algHom_ext_of_isHausdorff`).

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DZ3](https://stacks.math.columbia.edu/tag/0DZ3)
* [Stacks Project, Tag 07M8](https://stacks.math.columbia.edu/tag/07M8)
* [Stacks Project, Tag 0DYC](https://stacks.math.columbia.edu/tag/0DYC)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

/-- **Stacks 0DZ2 with the source's hypotheses, for a finite module.** For two cartesian
squares of Noetherian rings `A' → P' → Q'` over `A → P → Q` with flat horizontal maps and
surjective vertical maps with nilpotent kernels, an ideal `J'` of `P'` with
`P'/J' = Q'/J'Q'`, and a `P`-module `M` finite
over `P` and flat over `A` whose localization `M_g` has an `A'`-flat `(P')_g`-module lift for
every `g ∈ J'`: `M` has an `A'`-flat `P'`-module lift if and only if `Q ⊗_P M` has an
`A'`-flat `Q'`-module lift.

**This statement is FALSE, at every universe.**
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement` of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutation` proves
`¬ FlatModuleLiftBaseChangeStatement.{0}` outright, and
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement_ulift` of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutationUniverse` proves
`¬ FlatModuleLiftBaseChangeStatement.{u}` for a universe parameter `u`, by instantiating this
definition at the `ULift`s of the counterexample's rings. The counterexample — the
Artin–Schreier obstruction on the nodal cubic, with a finite cyclic `M`, so that the finiteness
restriction added here does not save the statement — is set out in the module documentation of
the first of those two files and is not repeated here. Every theorem below that takes this
statement as a hypothesis is therefore vacuous. It is kept because it is the exact shape those
proofs consume, and because naming the false statement is how the defect stays visible.

The cartesian condition is carried by the identities `ker(P' → P) = ker(A' → A) · P'` and
`ker(Q' → Q) = ker(A' → A) · Q'` together with the scalar towers, which is what the proof of
Stacks 0DZ3 produces and consumes. -/
def FlatModuleLiftBaseChangeStatement : Prop :=
  ∀ (A' A P' P Q' Q : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing Q'] [CommRing Q]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q'] [IsNoetherianRing Q]
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra A' P] [Algebra A' Q]
    [Algebra A P] [Algebra A Q] [Algebra P' P] [Algebra P' Q'] [Algebra P' Q]
    [Algebra P Q] [Algebra Q' Q]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' P' Q']
    [IsScalarTower A' Q' Q] [IsScalarTower A P Q] [IsScalarTower P' P Q]
    [IsScalarTower P' Q' Q],
    Function.Surjective (algebraMap A' A) →
    IsNilpotent (RingHom.ker (algebraMap A' A)) →
    Function.Surjective (algebraMap P' P) →
    RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P') →
    Function.Surjective (algebraMap Q' Q) →
    RingHom.ker (algebraMap Q' Q) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') →
    Module.Flat A' P' → Module.Flat A' Q' → Module.Flat P' Q' → Module.Flat P Q →
    ∀ (J' : Ideal P'),
      Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q')) (algebraMap P' Q')
        Ideal.le_comap_map) →
    ∀ (M : Type u) [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower A P M]
      [Module.Finite P M] [Module.Flat A M] (N : Type u) [AddCommGroup N] [Module Q N],
      Nonempty ((Q ⊗[P] M) ≃ₗ[Q] N) →
      (∀ g ∈ J',
        letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
          (Localization.awayMap (algebraMap P' P) g).toAlgebra
        ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
          (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
          Module.Flat A' L ∧ Nonempty
            ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
              ≃ₗ[Localization.Away (algebraMap P' P g)]
                (Localization.Away (algebraMap P' P g) ⊗[P] M))) →
      ((∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
          (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
          Nonempty ((P ⊗[P'] M') ≃ₗ[P] M)) ↔
        (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
          (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
          Nonempty ((Q ⊗[Q'] N') ≃ₗ[Q] N)))


/-! ### `Module.Flat A P` is a consequence of the cartesian square, not an extra hypothesis -/

/-- **The lower horizontal arrow of a cartesian square inherits flatness from the upper one.**
For a surjection `A' → A` with kernel `I` and a surjection `P' → P` over it whose kernel is
`I · P'` — which is exactly the statement that `A → P` is the base change of `A' → P'`, by the
isomorphism `A ⊗_{A'} P' ≅ P` built in the proof — flatness of `P'` over `A'` gives flatness of
`P` over `A`.

This is why the hypothesis `Module.Flat A P` of Stacks 0DZ2 — part of its "flat horizontal
arrows", the horizontal arrows being `A' → P'`, `P' → Q'`, `A → P` and `P → Q` — is *redundant*
in the presence of the lemma's other hypotheses, and why omitting it from
`Deformation.FlatModuleLiftBaseChangeStatement` did not strengthen that statement. The two
statements are in fact equivalent; see
`Deformation.flatModuleLiftBaseChangeStatement_of_faithful` and
`Deformation.flatModuleLiftBaseChangeStatementFaithful_of_statement`. -/
theorem flat_of_surjective_of_ker_eq_map
    (A' A P' P : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A P] [Algebra P' P]
    [IsScalarTower A' A P] [IsScalarTower A' P' P]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hflat : Module.Flat A' P') :
    Module.Flat A P := by
  have := hflat
  have : Module.Flat A (A ⊗[A'] P') := Module.Flat.baseChange A' A P'
  set f : (A ⊗[A'] P') →ₐ[A] P :=
    AlgHom.liftEquiv A' A P' P (IsScalarTower.toAlgHom A' P' P) with hf
  have hcomp : ∀ p : P', f ((1 : A) ⊗ₜ[A'] p) = algebraMap P' P p := by
    intro p
    rw [hf, AlgHom.liftEquiv_tmul, one_smul]
    rfl
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨p, rfl⟩ := hsurjP y
    exact ⟨(1 : A) ⊗ₜ[A'] p, hcomp p⟩
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨p, rfl⟩ := surjective_includeRight A' A P' hsurjA y
    have hp : algebraMap P' P p = 0 := (hcomp p).symm.trans hy
    have hmem : p ∈ RingHom.ker (algebraMap P' P) := hp
    rw [hkerP, ← ker_includeRight A' A P' hsurjA, RingHom.mem_ker] at hmem
    exact hmem
  exact Module.Flat.of_linearEquiv (AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.toLinearEquiv


/-! ### Stacks 0DZ2 with every hypothesis of the source written out -/

/-- **Stacks 0DZ2 with every hypothesis of the source written out, for a finite module.**

This is `Deformation.FlatModuleLiftBaseChangeStatement` with the one hypothesis of the source
that statement does not carry — `Module.Flat A P` — restored, so that a clause-by-clause reading
against the source leaves nothing over. The source reads:

> Consider a commutative diagram of Noetherian rings `A' → P' → Q'` over `A → P → Q` with
> cartesian squares, with flat horizontal arrows, and with surjective vertical arrows whose
> kernels are nilpotent. Let `J' ⊆ P'` be an ideal such that `P'/J' = Q'/J'Q'`. Let `M` be an
> `A`-flat `P`-module. Assume for all `g ∈ J'` there exists an `A'`-flat `(P')_g`-module lifting
> `M_g`. Then the following are equivalent: (1) `M` has an `A'`-flat lift to a `P'`-module, and
> (2) `M ⊗_P Q` has an `A'`-flat lift to a `Q'`-module.

Clause by clause, and why each hypothesis below is there:

* **Noetherian rings**: the six `IsNoetherianRing` instances. The source's proof uses `P`
  Noetherian at Stacks 0A6A; the other five are stated by the source and carried here.
* **Commutative diagram**: the seven `IsScalarTower` instances. They pin down every composite:
  `A' → P' → P = A' → A → P`, `A' → P' → Q'`, `A' → Q' → Q`, `A → P → Q`, `P' → P → Q` and
  `P' → Q' → Q`.
* **Cartesian squares**: `hsurjP` with `hkerP` say that `A ⊗_{A'} P' → P` is an isomorphism,
  and `hsurjQ` with `hkerQ` that `P ⊗_{P'} Q' → Q` is — note `(I · P') · Q' = I · Q'`, so the
  right-hand square's kernel condition is stated against the same `I = ker(A' → A)`. The
  equivalence of the two renderings is the content of
  `Deformation.flat_of_surjective_of_ker_eq_map`, whose proof builds the isomorphism.
* **Surjective vertical arrows with nilpotent kernels**: `hsurjA`, `hnilA`, `hsurjP`, `hsurjQ`.
  Nilpotence is asked only of `ker(A' → A)`; the other two kernels are `I · P'` and `I · Q'` and
  are nilpotent for free (`Deformation.isNilpotent_ideal_map`), so nothing is dropped.
* **Flat horizontal arrows**: the horizontal arrows of the diagram are `A' → P'`, `P' → Q'`,
  `A → P` and `P → Q`, so the source asks for `Module.Flat A' P'`, `Module.Flat P' Q'`,
  **`Module.Flat A P`** and `Module.Flat P Q`. `Module.Flat A' Q'` is carried too, as
  `FlatModuleLiftBaseChangeStatement` carries it; it is the composite of the first two and adds
  no strength.
* **`P'/J' = Q'/J'Q'`**: `hquot`, the bijectivity of the natural `P'/J' → Q'/J'Q'`.
* **`M` an `A`-flat `P`-module**: `Module P M`, `Module A M`, `IsScalarTower A P M` and
  `Module.Flat A M`.
* **`Module.Finite P M`**: *added*, not in the source's statement. The source's own proof needs
  it — "here we use that `P` is Noetherian and `M` finite", at Stacks 0A6A — and the step is
  false without it, as the clause on the `_of_isNilpotent_ker` form of
  `Deformation.exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift`
  records. Adding a hypothesis makes this statement *weaker* than the source's, so a refutation
  of it refutes the source a fortiori.
* **Local liftability**: for `g ∈ J'`, an `A'`-flat `(P')_g`-module `L` with
  `P_ḡ ⊗_{(P')_g} L ≅ P_ḡ ⊗_P M = M_ḡ`. That left-hand side is `L ⊗_{A'} A`, by the localized
  cartesian square, so this is the source's "lifting `M_g`".

**The one encoding choice that is not a literal reading** is the universe: every ring and module
here lives in `Type u`, including the lifts `M'`, `N'` and `L` the existentials produce, whereas
the source places no bound on a lift. For a lift of a *finite* `M` the restriction is vacuous —
`M'` is generated over `P'` by any lift of a generating set of `M`, by Nakayama against the
nilpotent `ker(P' → P)` — but that argument is not part of this statement. The refutation does
not lean on it either: its negative half,
`Deformation.Examples.ArtinSchreier.not_lift_of_tensorEquiv`, is polymorphic in the lift's
universe and so rules out a lift in *any* universe.

**This statement is FALSE**, at every universe, by
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatementFaithful_ulift` of
`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutationFaithful`. Since the added
`Module.Flat A P` is redundant the two statements are equivalent, so this is no new mathematics
beyond `Deformation.FlatModuleLiftBaseChangeStatement`'s refutation; what it settles is that the
refutation is a refutation of the source and not of a mis-rendering of it. -/
def FlatModuleLiftBaseChangeStatementFaithful : Prop :=
  ∀ (A' A P' P Q' Q : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing Q'] [CommRing Q]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q'] [IsNoetherianRing Q]
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra A' P] [Algebra A' Q]
    [Algebra A P] [Algebra A Q] [Algebra P' P] [Algebra P' Q'] [Algebra P' Q]
    [Algebra P Q] [Algebra Q' Q]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' P' Q']
    [IsScalarTower A' Q' Q] [IsScalarTower A P Q] [IsScalarTower P' P Q]
    [IsScalarTower P' Q' Q],
    Function.Surjective (algebraMap A' A) →
    IsNilpotent (RingHom.ker (algebraMap A' A)) →
    Function.Surjective (algebraMap P' P) →
    RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P') →
    Function.Surjective (algebraMap Q' Q) →
    RingHom.ker (algebraMap Q' Q) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') →
    Module.Flat A' P' → Module.Flat A' Q' → Module.Flat P' Q' → Module.Flat P Q →
    Module.Flat A P →
    ∀ (J' : Ideal P'),
      Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q')) (algebraMap P' Q')
        Ideal.le_comap_map) →
    ∀ (M : Type u) [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower A P M]
      [Module.Finite P M] [Module.Flat A M] (N : Type u) [AddCommGroup N] [Module Q N],
      Nonempty ((Q ⊗[P] M) ≃ₗ[Q] N) →
      (∀ g ∈ J',
        letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
          (Localization.awayMap (algebraMap P' P) g).toAlgebra
        ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
          (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
          Module.Flat A' L ∧ Nonempty
            ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
              ≃ₗ[Localization.Away (algebraMap P' P g)]
                (Localization.Away (algebraMap P' P g) ⊗[P] M))) →
      ((∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
          (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
          Nonempty ((P ⊗[P'] M') ≃ₗ[P] M)) ↔
        (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
          (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
          Nonempty ((Q ⊗[Q'] N') ≃ₗ[Q] N)))

/-- **The faithful statement implies the one the rest of this file consumes.** The only
difference between them is the hypothesis `Module.Flat A P`, which
`Deformation.flat_of_surjective_of_ker_eq_map` supplies from the cartesian square and
`Module.Flat A' P'`. -/
theorem flatModuleLiftBaseChangeStatement_of_faithful
    (h : FlatModuleLiftBaseChangeStatementFaithful.{u}) :
    FlatModuleLiftBaseChangeStatement.{u} := by
  intro A' A P' P Q' Q
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _
  intro _ _ _ _ _ _ _
  intro hsurjA hnilA hsurjP hkerP hsurjQ hkerQ hfAP' hfAQ' hfPQ' hfPQ
  exact h A' A P' P Q' Q hsurjA hnilA hsurjP hkerP hsurjQ hkerQ hfAP' hfAQ' hfPQ' hfPQ
    (flat_of_surjective_of_ker_eq_map A' A P' P hsurjA hsurjP hkerP hfAP')

/-- **The converse**, which is the trivial direction: the faithful statement has one hypothesis
more, so it follows by forgetting it. With
`Deformation.flatModuleLiftBaseChangeStatement_of_faithful` this makes the two statements
equivalent, which is the precise sense in which omitting `Module.Flat A P` from
`Deformation.FlatModuleLiftBaseChangeStatement` was harmless. -/
theorem flatModuleLiftBaseChangeStatementFaithful_of_statement
    (h : FlatModuleLiftBaseChangeStatement.{u}) :
    FlatModuleLiftBaseChangeStatementFaithful.{u} := by
  intro A' A P' P Q' Q
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _
  intro _ _ _ _ _ _ _ _ _ _ _ _
  intro _ _ _ _ _ _ _
  intro hsurjA hnilA hsurjP hkerP hsurjQ hkerQ hfAP' hfAQ' hfPQ' hfPQ _hfAP
  exact h A' A P' P Q' Q hsurjA hnilA hsurjP hkerP hsurjQ hkerQ hfAP' hfAQ' hfPQ' hfPQ


/-! ### The two base changes of an algebra over the upper left corner -/

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- In `S ⊗[R] T` the images of `r : R` through `S` and through `T` agree. -/
private theorem algebraMap_tensorProduct_comm (R S T : Type u) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] (r : R) :
    algebraMap S (S ⊗[R] T) (algebraMap R S r) = algebraMap T (S ⊗[R] T) (algebraMap R T r) := by
  rw [← IsScalarTower.algebraMap_apply R S, ← IsScalarTower.algebraMap_apply R T]

/-- The scalar tower `A' → Q' → P ⊗_{P'} Q'` over the upper left corner. -/
private theorem isScalarTower_tensorProduct_right (A' P' P Q' : Type u) [CommRing A']
    [CommRing P'] [CommRing P] [CommRing Q'] [Algebra A' P'] [Algebra A' P] [Algebra A' Q']
    [Algebra P' P] [Algebra P' Q'] [IsScalarTower A' P' P] [IsScalarTower A' P' Q'] :
    IsScalarTower A' Q' (P ⊗[P'] Q') :=
  IsScalarTower.of_algebraMap_eq fun a' => by
    rw [IsScalarTower.algebraMap_apply A' P (P ⊗[P'] Q'), IsScalarTower.algebraMap_apply A' P' P,
      IsScalarTower.algebraMap_apply A' P' Q']
    exact algebraMap_tensorProduct_comm P' P Q' _

/-- The kernel of `Q' → P ⊗_{P'} Q'` is `ker(A' → A) · Q'` when `ker(P' → P) = ker(A' → A) · P'`. -/
private theorem ker_includeRight_eq_map_of_ker_eq_map (A' A P' P Q' : Type u) [CommRing A']
    [CommRing A] [CommRing P'] [CommRing P] [CommRing Q'] [Algebra A' A] [Algebra A' P']
    [Algebra A' P] [Algebra A' Q'] [Algebra P' P] [Algebra P' Q'] [IsScalarTower A' P' P]
    [IsScalarTower A' P' Q'] (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P')) :
    RingHom.ker (algebraMap Q' (P ⊗[P'] Q')) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') := by
  have h := ker_includeRight P' P Q' hsurjP
  rw [hkerP, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
  exact h

/-- Let `A' → A` be a surjection with kernel `K` and let `P' → P` be a surjection over it with
kernel `K · P'`. For a `P'`-algebra `Q'`, the base change of `Q'` along `A' → A` agrees with its
base change along `P' → P`: both are the quotient of `Q'` by `K · Q'`. -/
theorem exists_algEquiv_tensorBaseChange
    (A' A P' P Q' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' Q'] [Algebra A P]
    [Algebra P' P] [Algebra P' Q'] [IsScalarTower A' A P] [IsScalarTower A' P' P]
    [IsScalarTower A' P' Q'] [Algebra A (P ⊗[P'] Q')]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hAPQ : ∀ a : A, algebraMap A (P ⊗[P'] Q') a =
      algebraMap P (P ⊗[P'] Q') (algebraMap A P a)) :
    ∃ e : (A ⊗[A'] Q') ≃ₐ[A] (P ⊗[P'] Q'),
      ∀ x : Q', e (1 ⊗ₜ[A'] x) = algebraMap Q' (P ⊗[P'] Q') x := by
  have hs1 : Function.Surjective (algebraMap Q' (A ⊗[A'] Q')) :=
    surjective_includeRight A' A Q' hsurjA
  have hs2 : Function.Surjective (algebraMap Q' (P ⊗[P'] Q')) :=
    surjective_includeRight P' P Q' hsurjP
  have hk1 : RingHom.ker (algebraMap Q' (A ⊗[A'] Q')) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') :=
    ker_includeRight A' A Q' hsurjA
  have hk2 := ker_includeRight_eq_map_of_ker_eq_map A' A P' P Q' hsurjP hkerP
  have heq : RingHom.ker (algebraMap Q' (A ⊗[A'] Q')) =
      RingHom.ker (algebraMap Q' (P ⊗[P'] Q')) := by rw [hk1, hk2]
  set r1 := RingHom.quotientKerEquivOfSurjective hs1 with hr1
  set r2 := RingHom.quotientKerEquivOfSurjective hs2 with hr2
  set e : (A ⊗[A'] Q') ≃+* (P ⊗[P'] Q') :=
    r1.symm.trans ((Ideal.quotEquivOfEq heq).trans r2) with hedef
  have hcompat : ∀ x : Q', e (algebraMap Q' (A ⊗[A'] Q') x) =
      algebraMap Q' (P ⊗[P'] Q') x := by
    intro x
    have h1 : r1 (Ideal.Quotient.mk _ x) = algebraMap Q' (A ⊗[A'] Q') x := rfl
    have h2 : r2 (Ideal.Quotient.mk _ x) = algebraMap Q' (P ⊗[P'] Q') x := rfl
    rw [hedef, ← h1, RingEquiv.trans_apply, RingEquiv.symm_apply_apply,
      RingEquiv.trans_apply, show (Ideal.quotEquivOfEq heq) (Ideal.Quotient.mk _ x) =
        Ideal.Quotient.mk _ x from rfl, h2]
  refine ⟨AlgEquiv.ofRingEquiv (f := e) ?_, fun x => hcompat x⟩
  intro a
  obtain ⟨a', rfl⟩ := hsurjA a
  rw [algebraMap_tensorProduct_comm A' A Q', hcompat, hAPQ, IsScalarTower.algebraMap_apply A' P' Q',
    ← IsScalarTower.algebraMap_apply A' A P, IsScalarTower.algebraMap_apply A' P' P]
  exact (algebraMap_tensorProduct_comm P' P Q' _).symm

/-! ### The reduction of an adic completion -/

/-- For a Noetherian ring `P'` and an ideal `I'`, the canonical map `P'/I' → (P')^∧/I'(P')^∧`
is bijective: surjective because every element of the completion agrees with one of `P'` modulo
`I'`, and injective because `I'(P')^∧` is the kernel of the projection to `P'/I'`. -/
theorem bijective_quotientMap_adicCompletion {P' : Type u} [CommRing P'] [IsNoetherianRing P']
    (I' : Ideal P') :
    Function.Bijective (Ideal.quotientMap
      (I'.map (algebraMap P' (AdicCompletion I' P'))) (algebraMap P' (AdicCompletion I' P'))
      Ideal.le_comap_map) := by
  have hfg : I'.FG := IsNoetherian.noetherian I'
  have hmem : ∀ x : P', algebraMap P' (AdicCompletion I' P') x ∈
      I'.map (algebraMap P' (AdicCompletion I' P')) ↔ x ∈ I' := by
    intro x
    have hof : ∀ y : P', algebraMap P' (AdicCompletion I' P') y = AdicCompletion.of I' P' y :=
      fun _ => rfl
    have h1 : ∀ y : AdicCompletion I' P', y ∈ I'.map (algebraMap P' (AdicCompletion I' P')) ↔
        y ∈ I' ^ 1 • (⊤ : Submodule P' (AdicCompletion I' P')) := by
      intro y
      rw [pow_one, Ideal.smul_top_eq_map I', Submodule.restrictScalars_mem]
    have h2 : I' ^ 1 • (⊤ : Submodule P' (AdicCompletion I' P')) =
        LinearMap.ker (AdicCompletion.eval I' P' 1) :=
      AdicCompletion.pow_smul_top_eq_ker_eval hfg
    constructor
    · intro hx
      have hx' : algebraMap P' (AdicCompletion I' P') x ∈
          LinearMap.ker (AdicCompletion.eval I' P' 1) := by
        rw [← h2]
        exact (h1 _).mp hx
      rw [LinearMap.mem_ker, hof, AdicCompletion.eval_of, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, pow_one, Ideal.smul_eq_mul, Ideal.mul_top] at hx'
      exact hx'
    · intro hx
      exact Ideal.mem_map_of_mem _ hx
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, hmem] at hx
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hx
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, hp⟩ := AdicCompletion.exists_sub_mem_map_pow I' hfg 1 w
    refine ⟨Ideal.Quotient.mk I' p, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    rw [pow_one] at hp
    have hneg := Submodule.neg_mem _ hp
    rwa [neg_sub] at hneg

/-- **Stacks 07M8 as a flat lift.** A syntomic `A`-algebra has a flat lift to `A'` along any
surjection `A' → A`: the syntomic lift of Stacks 07M8 is flat, being syntomic. -/
theorem hasFlatAlgebraLift_of_syntomic (A' A A₀ : Type u) [CommRing A'] [CommRing A]
    [CommRing A₀] [Algebra A' A] [Algebra A A₀]
    (hsurjA : Function.Surjective (algebraMap A' A)) (hsyn : Algebra.Syntomic A A₀) :
    HasFlatAlgebraLift A' A A₀ := by
  obtain ⟨D, hDring, aD, hDsyn, e, he⟩ :=
    Stacks.Smoothing.exists_syntomic_lift_of_surjective A' A A₀ hsurjA hsyn
  let : CommRing D := hDring
  let : Algebra A' D := aD
  let : Algebra.Syntomic A' D := hDsyn
  have hflat : Module.Flat A' D := Algebra.Syntomic.flat
  have hker : RingHom.ker (algebraMap D (A ⊗[A'] D)) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' D) :=
    ker_includeRight A' A D hsurjA
  set r1 : (D ⧸ RingHom.ker (algebraMap D (A ⊗[A'] D))) ≃+* (A ⊗[A'] D) :=
    RingHom.quotientKerEquivOfSurjective (surjective_includeRight A' A D hsurjA) with hr1
  set r2 : (D ⧸ (RingHom.ker (algebraMap A' A)).map (algebraMap A' D)) ≃+* (A ⊗[A'] D) :=
    (Ideal.quotEquivOfEq hker.symm).trans r1 with hr2
  have hr2mk : ∀ d : D, r2 (Ideal.Quotient.mk _ d) = algebraMap D (A ⊗[A'] D) d := by
    intro d
    rw [hr2, RingEquiv.trans_apply,
      show (Ideal.quotEquivOfEq hker.symm) (Ideal.Quotient.mk _ d) =
        Ideal.Quotient.mk _ d from rfl]
    rfl
  refine ⟨D, inferInstance, inferInstance, hflat,
    ⟨AlgEquiv.ofRingEquiv (f := r2.symm.trans e.symm) ?_⟩⟩
  intro a
  obtain ⟨a', rfl⟩ := hsurjA a
  rw [RingEquiv.trans_apply, algebraMap_tensorProduct_comm A' A D, ← hr2mk, r2.symm_apply_apply,
    RingEquiv.symm_apply_eq]
  exact (he a').symm
/-- **The local liftability hypothesis of Stacks 0DZ2, in the situation of Stacks 0DZ3.** If
`A → B_h` is syntomic for every `h` in an ideal `𝔟` of `B`, then for every `g` in the preimage
of `𝔟` the localization of `B` at the image of `g` has an `A'`-flat module lift over the
localization of `P'` at `g`: it is a syntomic `A`-algebra, so Stacks 07M8 gives it a flat
algebra lift, which the first implication of the comparison turns into a module lift. -/
public theorem exists_flatModuleLift_localization_of_syntomic (A' A P' P B : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B]
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B]
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [Algebra.FormallySmooth A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h))
    (g : P') (hg : g ∈ Ideal.comap (algebraMap P' B) b) :
    letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
      (Localization.awayMap (algebraMap P' P) g).toAlgebra
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
      (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
      Module.Flat A' L ∧ Nonempty
        ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
          ≃ₗ[Localization.Away (algebraMap P' P g)]
            (Localization.Away (algebraMap P' P g) ⊗[P] B)) := by
  let : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
    (Localization.awayMap (algebraMap P' P) g).toAlgebra
  have hsurjPg : Function.Surjective
      (algebraMap (Localization.Away g) (Localization.Away (algebraMap P' P g))) :=
    IsLocalization.map_surjective_of_surjective (Submonoid.powers g)
      (Localization.Away g) (Localization.Away (algebraMap P' P g)) hsurjP
  have hkerPg : RingHom.ker
      (algebraMap (Localization.Away g) (Localization.Away (algebraMap P' P g))) =
      (RingHom.ker (algebraMap A' A)).map
        (algebraMap A' (Localization.Away g)) := by
    have h := IsLocalization.Away.ker_map (A := P') (C := P) g
    rw [hkerP, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
    exact h
  -- `Pg ⊗[P] B` is the localization of `B` at the image of `g`
  have hbg : algebraMap P B (algebraMap P' P g) = algebraMap P' B g :=
    (IsScalarTower.algebraMap_apply P' P B g).symm
  have : IsLocalization.Away (algebraMap P' B g)
      (Localization.Away (algebraMap P' P g) ⊗[P] B) := by
    rw [← hbg]
    exact IsLocalization.Away.tensorRight (algebraMap P' P g)
      (Localization.Away (algebraMap P' P g))
  have eBh : (Localization.Away (algebraMap P' P g) ⊗[P] B) ≃ₐ[B]
      Localization.Away (algebraMap P' B g) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap P' B g)) _ _
  -- the towers at `g`
  have hABh : ∀ a : A, algebraMap A (Localization.Away (algebraMap P' P g) ⊗[P] B) a =
      algebraMap B (Localization.Away (algebraMap P' P g) ⊗[P] B) (algebraMap A B a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A (Localization.Away (algebraMap P' P g))
        (Localization.Away (algebraMap P' P g) ⊗[P] B),
      IsScalarTower.algebraMap_apply A P (Localization.Away (algebraMap P' P g)),
      IsScalarTower.algebraMap_apply A P B]
    exact algebraMap_tensorProduct_comm P (Localization.Away (algebraMap P' P g)) B _
  have : IsScalarTower A B (Localization.Away (algebraMap P' P g) ⊗[P] B) :=
    IsScalarTower.of_algebraMap_eq hABh
  have hlift : HasFlatAlgebraLift A' A (Localization.Away (algebraMap P' P g) ⊗[P] B) := by
    rw [hasFlatAlgebraLift_congr (A' := A') (eBh.restrictScalars A)]
    exact hasFlatAlgebraLift_of_syntomic A' A _ hsurjA (hsyn _ hg)
  -- the module lift over the localized presentation
  have hA'Pg : ∀ a' : A', algebraMap A' (Localization.Away (algebraMap P' P g)) a' =
      algebraMap (Localization.Away g) (Localization.Away (algebraMap P' P g))
        (algebraMap A' (Localization.Away g) a') := by
    have hmap : ∀ x : P',
        algebraMap (Localization.Away g) (Localization.Away (algebraMap P' P g))
          (algebraMap P' (Localization.Away g) x) =
        algebraMap P (Localization.Away (algebraMap P' P g)) (algebraMap P' P x) := by
      intro x
      exact RingHom.congr_fun (IsLocalization.map_comp
        (M := Submonoid.powers g) (S := Localization.Away g)
        (g := algebraMap P' P) (T := Submonoid.powers (algebraMap P' P g))
        (Q := Localization.Away (algebraMap P' P g))
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _))) x
    intro a'
    rw [IsScalarTower.algebraMap_apply A' P' (Localization.Away g), hmap,
      ← IsScalarTower.algebraMap_apply A' P' P,
      ← IsScalarTower.algebraMap_apply A' P (Localization.Away (algebraMap P' P g))]
  have : IsScalarTower A' (Localization.Away g)
      (Localization.Away (algebraMap P' P g)) := IsScalarTower.of_algebraMap_eq hA'Pg
  have : IsScalarTower A' (Localization.Away (algebraMap P' P g))
      (Localization.Away (algebraMap P' P g) ⊗[P] B) :=
    IsScalarTower.to₁₃₄ A' A (Localization.Away (algebraMap P' P g))
      (Localization.Away (algebraMap P' P g) ⊗[P] B)
  have : IsScalarTower A' (Localization.Away g)
      (Localization.Away (algebraMap P' P g) ⊗[P] B) :=
    IsScalarTower.to₁₂₄ A' (Localization.Away g) (Localization.Away (algebraMap P' P g))
      (Localization.Away (algebraMap P' P g) ⊗[P] B)
  exact exists_flatModuleLift_of_hasFlatAlgebraLift hsurjA hnilA hsurjPg hkerPg hlift
/-- The chain of isomorphisms identifying `(P ⊗_{P'} (P')^∧) ⊗_P B` with the completion of
`B`. -/
private theorem exists_ringEquiv_tensorAdicCompletion
    (A P' P B : Type u) [CommRing A] [CommRing P'] [CommRing P] [CommRing B]
    [IsNoetherianRing P'] [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B]
    [Algebra P B] [IsScalarTower A P B] [IsScalarTower P' P B] [Module.Finite P' B]
    (I' : Ideal P') :
    ∃ e : ((P ⊗[P'] AdicCompletion I' P') ⊗[P] B) ≃+*
        AdicCompletion (I'.map (algebraMap P' B)) B,
      ∀ p : P, e ((p ⊗ₜ[P'] (1 : AdicCompletion I' P')) ⊗ₜ[P] (1 : B)) =
        AdicCompletion.of (I'.map (algebraMap P' B)) B (algebraMap P B p) := by
  have hc4 : ∀ d : B, ofTensorProductAlgEquiv I' B ((1 : AdicCompletion I' P') ⊗ₜ[P'] d) =
      AdicCompletion.of (I'.map (algebraMap P' B)) B d := by
    intro d
    refine AdicCompletion.ext_evalₐ fun n => ?_
    have h := ofTensorProductLinearEquiv_tmul_eval I' B (1 : AdicCompletion I' P') d n
    rw [show ofTensorProductAlgEquiv I' B ((1 : AdicCompletion I' P') ⊗ₜ[P'] d) =
      ofTensorProductLinearEquiv I' B ((1 : AdicCompletion I' P') ⊗ₜ[P'] d) from
        Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply _ _ _ _, h]
    simp
  refine ⟨(Algebra.TensorProduct.comm P (P ⊗[P'] AdicCompletion I' P') B).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange P' P B B
        (AdicCompletion I' P')).toRingEquiv.trans
      ((Algebra.TensorProduct.comm P' B (AdicCompletion I' P')).toRingEquiv.trans
        (ofTensorProductAlgEquiv I' B).toRingEquiv)), fun p => ?_⟩
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply, RingEquiv.trans_apply]
  simp only [AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul]
  rw [Algebra.smul_def, mul_one]
  exact hc4 (algebraMap P B p)
/-- The assembly of the first implication of Stacks 0DZ3 out of Stacks 0DZ2 and the two
presentations. `B` is presented by `P` over `P'`; its base change `C` to `Q = P ⊗_{P'} Q'` is
presented by `Q` over `Q'`; and the two module-lifting problems are compared by Stacks 0DZ2. -/
public theorem hasFlatAlgebraLift_imp_baseChange_of_presentation
    (h0DZ2 : FlatModuleLiftBaseChangeStatement.{u})
    (A' A P' P B Q' : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q']
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q']
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q']
    [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Flat A B] [Module.Flat P' Q']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (J' : Ideal P')
    (hquot : Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q'))
      (algebraMap P' Q') Ideal.le_comap_map))
    (hloc : ∀ g ∈ J',
      letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
        (Localization.awayMap (algebraMap P' P) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away (algebraMap P' P g)]
              (Localization.Away (algebraMap P' P g) ⊗[P] B)))
    (C : Type u) [CommRing C] [Algebra A' C] [Algebra A C] [IsScalarTower A' A C]
    (e : (((P ⊗[P'] Q') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B))) :
    HasFlatAlgebraLift A' A B → HasFlatAlgebraLift A' A C := by
  have hsurjQ : Function.Surjective (algebraMap Q' (P ⊗[P'] Q')) :=
    surjective_includeRight P' P Q' hsurjP
  have hkerQ := ker_includeRight_eq_map_of_ker_eq_map A' A P' P Q' hsurjP hkerP
  have hnilQ : IsNilpotent (RingHom.ker (algebraMap Q' (P ⊗[P'] Q'))) := by
    rw [hkerQ]
    exact isNilpotent_ideal_map hnilA _
  have hnoethQ : IsNoetherianRing (P ⊗[P'] Q') :=
    isNoetherianRing_of_surjective Q' (P ⊗[P'] Q') (algebraMap Q' (P ⊗[P'] Q')) hsurjQ
  have hflatA'Q' : Module.Flat A' Q' := Module.Flat.trans A' P' Q'
  -- the scalar tower that is not canonical
  have := isScalarTower_tensorProduct_right A' P' P Q'
  -- the comparison of the two base changes of `Q'`
  obtain ⟨eQQ, heQQ⟩ := exists_algEquiv_tensorBaseChange A' A P' P Q' hsurjA hsurjP hkerP
    (fun a => IsScalarTower.algebraMap_apply A P (P ⊗[P'] Q') a)
  -- the presentation of the base change of `B`
  have hfinPB : Module.Finite P B :=
    Module.Finite.of_surjective (Algebra.linearMap P B) hsurjB
  let : Algebra (P ⊗[P'] Q') C :=
    (e.toRingHom.comp (algebraMap (P ⊗[P'] Q') ((P ⊗[P'] Q') ⊗[P] B))).toAlgebra
  let : Algebra Q' C :=
    ((algebraMap (P ⊗[P'] Q') C).comp (algebraMap Q' (P ⊗[P'] Q'))).toAlgebra
  have : IsScalarTower Q' (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq hAe
  have : IsScalarTower A' (P ⊗[P'] Q') C := IsScalarTower.to₁₃₄ A' A (P ⊗[P'] Q') C
  have : IsScalarTower A' Q' C := IsScalarTower.to₁₂₄ A' Q' (P ⊗[P'] Q') C
  have hsurjC : Function.Surjective (algebraMap (P ⊗[P'] Q') C) :=
    e.surjective.comp (surjective_tmul_one P B hsurjB (P ⊗[P'] Q'))
  have eC : (((P ⊗[P'] Q') ⊗[P] B)) ≃ₗ[P ⊗[P'] Q'] C :=
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)).toLinearEquiv
  intro hB
  refine hasFlatAlgebraLift_of_exists_flatModuleLift hsurjQ hnilQ hsurjC eQQ heQQ ?_
  exact (h0DZ2 A' A P' P Q' (P ⊗[P'] Q') hsurjA hnilA hsurjP hkerP hsurjQ hkerQ
    inferInstance hflatA'Q' inferInstance inferInstance J' hquot B C ⟨eC⟩ hloc).mp
      (exists_flatModuleLift_of_hasFlatAlgebraLift hsurjA hnilA hsurjP hkerP hB)

/-- The assembly of the second implication of Stacks 0DZ3 out of Stacks 0DZ2 and the two
presentations. A flat algebra lift of `C` along which the structure map of `C` lifts to `Q'` is
an `A'`-flat `Q'`-module lift of `C`; Stacks 0DZ2 turns it into an `A'`-flat `P'`-module lift
of `B`, which is a flat algebra lift of `B` by Nakayama. -/
public theorem hasFlatAlgebraLift_of_baseChange_of_presentation
    (h0DZ2 : FlatModuleLiftBaseChangeStatement.{u})
    (A' A P' P B Q' C : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing Q']
    [CommRing C]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' Q']
    [Algebra A P] [Algebra A B] [Algebra P' P] [Algebra P' B] [Algebra P B] [Algebra P' Q']
    [Algebra A' C] [Algebra A C] [Algebra Q' C]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' P' Q'] [IsScalarTower A' A C]
    [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Flat A B] [Module.Flat P' Q']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (ePP : (A ⊗[A'] P') ≃ₐ[A] P)
    (hePP : ∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' P x)
    (J' : Ideal P')
    (hquot : Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q'))
      (algebraMap P' Q') Ideal.le_comap_map))
    (hloc : ∀ g ∈ J',
      letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
        (Localization.awayMap (algebraMap P' P) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away (algebraMap P' P g)]
              (Localization.Away (algebraMap P' P g) ⊗[P] B)))
    (e : (((P ⊗[P'] Q') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] Q') a) ⊗ₜ[P] (1 : B)))
    (hQe : ∀ x : Q', algebraMap Q' C x = e (((1 : P) ⊗ₜ[P'] x) ⊗ₜ[P] (1 : B)))
    (hlift : ∀ (C' : Type u) (_ : CommRing C') (_ : Algebra A' C')
      (eC : (A ⊗[A'] C') ≃ₐ[A] C), ∃ g : Q' →ₐ[A'] C',
        ∀ x : Q', eC (1 ⊗ₜ[A'] (g x)) = algebraMap Q' C x) :
    HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B := by
  have hsurjQ : Function.Surjective (algebraMap Q' (P ⊗[P'] Q')) :=
    surjective_includeRight P' P Q' hsurjP
  have hkerQ := ker_includeRight_eq_map_of_ker_eq_map A' A P' P Q' hsurjP hkerP
  have hnilP : IsNilpotent (RingHom.ker (algebraMap P' P)) := by
    rw [hkerP]
    exact isNilpotent_ideal_map hnilA _
  have hnoethQ : IsNoetherianRing (P ⊗[P'] Q') :=
    isNoetherianRing_of_surjective Q' (P ⊗[P'] Q') (algebraMap Q' (P ⊗[P'] Q')) hsurjQ
  have hflatA'Q' : Module.Flat A' Q' := Module.Flat.trans A' P' Q'
  have := isScalarTower_tensorProduct_right A' P' P Q'
  have hfinPB : Module.Finite P B :=
    Module.Finite.of_surjective (Algebra.linearMap P B) hsurjB
  -- the presentation of `C` over `Q = P ⊗_{P'} Q'`
  let : Algebra (P ⊗[P'] Q') C :=
    (e.toRingHom.comp (algebraMap (P ⊗[P'] Q') ((P ⊗[P'] Q') ⊗[P] B))).toAlgebra
  have hQ2 : ∀ x : Q', algebraMap Q' C x =
      algebraMap (P ⊗[P'] Q') C (algebraMap Q' (P ⊗[P'] Q') x) := by
    intro x
    rw [hQe x]
    rfl
  have : IsScalarTower Q' (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq hQ2
  have : IsScalarTower A (P ⊗[P'] Q') C := IsScalarTower.of_algebraMap_eq hAe
  have eC : (((P ⊗[P'] Q') ⊗[P] B)) ≃ₗ[P ⊗[P'] Q'] C :=
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)).toLinearEquiv
  rintro ⟨C', _, _, hflatC', ⟨eCa⟩⟩
  obtain ⟨g, hg⟩ := hlift C' inferInstance inferInstance eCa
  refine hasFlatAlgebraLift_of_exists_flatModuleLift hsurjP hnilP hsurjB ePP hePP ?_
  exact (h0DZ2 A' A P' P Q' (P ⊗[P'] Q') hsurjA hnilA hsurjP hkerP hsurjQ hkerQ
    inferInstance hflatA'Q' inferInstance inferInstance J' hquot B C ⟨eC⟩ hloc).mpr
      (exists_flatModuleLift_of_algebraLift hsurjA hsurjQ hkerQ C' hflatC' eCa g hg)

/-! ### Lifting a presentation to a flat algebra lift of a complete algebra -/

/-- **Stacks 0DYC at a flat algebra lift.** Let `C` be `c`-adically complete and let `C'` be a
flat lift of `C` to `A'`. The reduction `C' → C` is a surjection with nilpotent kernel, so `C'`
is `c'`-adically complete for the preimage `c'` of `c` and a formally smooth presentation
`P' → C` carrying an ideal `J'` into `c` lifts to an `A'`-algebra map `(P')^∧ → C'`. -/
private theorem exists_algHom_adicCompletion_of_algebraLift
    (A' A P' C C' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing C] [CommRing C']
    [IsNoetherianRing A'] [IsNoetherianRing P'] [IsNoetherianRing C]
    [Algebra A' A] [Algebra A' P'] [Algebra A' C] [Algebra A' C'] [Algebra A C] [Algebra P' C]
    [IsScalarTower A' A C] [IsScalarTower A' P' C] [Algebra.FormallySmooth A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (J' : Ideal P') (c : Ideal C) (hc : IsAdicComplete c C)
    (hJc : ∀ g ∈ J', algebraMap P' C g ∈ c)
    [Algebra (AdicCompletion J' P') C] [IsScalarTower A' (AdicCompletion J' P') C]
    (hQC : ∀ x : P', algebraMap (AdicCompletion J' P') C
      (algebraMap P' (AdicCompletion J' P') x) = algebraMap P' C x)
    (eC : (A ⊗[A'] C') ≃ₐ[A] C) :
    ∃ g : AdicCompletion J' P' →ₐ[A'] C', ∀ x : AdicCompletion J' P',
      eC (1 ⊗ₜ[A'] (g x)) = algebraMap (AdicCompletion J' P') C x := by
  have hhaus : IsHausdorff c C := hc.toIsHausdorff
  -- the reduction of the lift, a surjection with nilpotent finitely generated kernel
  set rho : C' →ₐ[A'] C :=
    (eC.restrictScalars A').toAlgHom.comp Algebra.TensorProduct.includeRight with hrhodef
  have hrhoapp : ∀ y : C', rho y = eC (1 ⊗ₜ[A'] y) := fun _ => rfl
  have hrhosurj : Function.Surjective rho :=
    (eC.restrictScalars A').surjective.comp (surjective_includeRight A' A C' hsurjA)
  have hrhoker : RingHom.ker rho = (RingHom.ker (algebraMap A' A)).map (algebraMap A' C') :=
    ker_comp_includeRight C C' hsurjA (eC.restrictScalars A')
  have hrhonil : IsNilpotent (RingHom.ker rho) := by
    rw [hrhoker]
    exact isNilpotent_ideal_map hnilA _
  have hrhofg : (RingHom.ker rho).FG := by
    rw [hrhoker]
    exact Ideal.FG.map (IsNoetherian.noetherian (RingHom.ker (algebraMap A' A))) _
  -- `C'` is Noetherian, being a nilpotent thickening of the Noetherian ring `C`
  have hkercomplete : IsAdicComplete (RingHom.ker rho) C' :=
    IsAdicComplete.of_isNilpotent _ hrhonil
  set eρ : (C' ⧸ RingHom.ker rho) ≃ₐ[A'] C :=
    Ideal.quotientKerAlgEquivOfSurjective hrhosurj with heρdef
  have hquotnoeth : IsNoetherianRing (C' ⧸ RingHom.ker rho) :=
    isNoetherianRing_of_ringEquiv C eρ.symm.toRingEquiv
  have hC'noeth : IsNoetherianRing C' :=
    noetherian_of_isAdicComplete_fg C' (RingHom.ker rho) hrhofg hkercomplete hquotnoeth
  -- and `C'` is complete along the preimage of `c`, by Stacks 0DYC
  set c' : Ideal C' := Ideal.comap rho.toRingHom c with hc'def
  have hmapc : Ideal.map eρ.toRingEquiv (c'.map (algebraMap C' (C' ⧸ RingHom.ker rho)))
      = c := by
    have hcomp : eρ.toRingEquiv.toRingHom.comp
        (algebraMap C' (C' ⧸ RingHom.ker rho)) = rho.toRingHom :=
      RingHom.ext fun x => Ideal.quotientKerAlgEquivOfSurjective_mk hrhosurj x
    show Ideal.map eρ.toRingEquiv.toRingHom
      (c'.map (algebraMap C' (C' ⧸ RingHom.ker rho))) = c
    rw [Ideal.map_map, hcomp]
    exact Ideal.map_comap_of_surjective rho.toRingHom hrhosurj c
  have hc'quotmap : IsAdicComplete (c'.map (algebraMap C' (C' ⧸ RingHom.ker rho)))
      (C' ⧸ RingHom.ker rho) := by
    refine (IsAdicComplete.congr_ringEquiv _ eρ.toRingEquiv).mp ?_
    rw [hmapc]
    exact hc
  have hc'quot : IsAdicComplete c' (C' ⧸ RingHom.ker rho) :=
    (IsAdicComplete.map_algebraMap_iff c' (C' ⧸ RingHom.ker rho)).mp hc'quotmap
  have hc'complete : IsAdicComplete c' C' :=
    IsAdicComplete.of_quotient (RingHom.ker rho) c' hc'quot
  -- the lift of the presentation, extended across the completion
  set η₀ : P' →ₐ[A'] C' := Algebra.FormallySmooth.liftOfSurjective
    (IsScalarTower.toAlgHom A' P' C) rho hrhosurj hrhonil with hη₀def
  have hη₀ : ∀ x : P', rho (η₀ x) = algebraMap P' C x := fun x =>
    Algebra.FormallySmooth.liftOfSurjective_apply _ rho hrhosurj hrhonil x
  have hJc' : J'.map η₀ ≤ c' := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    refine Ideal.mem_comap.mpr ?_
    rw [hc'def, Ideal.mem_comap]
    show rho (η₀ x) ∈ c
    rw [hη₀ x]
    exact hJc x hx
  obtain ⟨η, hη⟩ :=
    AdicCompletion.exists_algHom_of_isAdicComplete (A := A') J' c' η₀ hJc'
  refine ⟨η, fun x => ?_⟩
  have hext : rho.comp η = IsScalarTower.toAlgHom A' (AdicCompletion J' P') C := by
    refine AdicCompletion.algHom_ext_of_isHausdorff J' (IsNoetherian.noetherian J') c _ _
      (fun p => ?_) (fun p hp => ?_)
    · show rho (η (AdicCompletion.of J' P' p)) =
        algebraMap (AdicCompletion J' P') C (AdicCompletion.of J' P' p)
      rw [hη p, hη₀ p, ← hQC p]
      rfl
    · show rho (η (AdicCompletion.of J' P' p)) ∈ c
      rw [hη p, hη₀ p]
      exact hJc p hp
  rw [← hrhoapp]
  exact AlgHom.congr_fun hext x

/-- The second implication of Stacks 0DZ3 for the completed presentation: the lifting
hypothesis of `Deformation.hasFlatAlgebraLift_of_baseChange_of_presentation` is supplied by
Stacks 0DYC when `Q'` is the `J'`-adic completion of `P'` and `J'` lands in the ideal of
completeness of `C`. -/
private theorem hasFlatAlgebraLift_of_adicCompletion_of_presentation
    (h0DZ2 : FlatModuleLiftBaseChangeStatement.{u})
    (A' A P' P B C : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing B] [CommRing C]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing C]
    [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' B] [Algebra A' C]
    [Algebra A P] [Algebra A B] [Algebra A C] [Algebra P' P] [Algebra P' B] [Algebra P B]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
    [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
    [IsScalarTower A' A C]
    [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Flat A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjB : Function.Surjective (algebraMap P B))
    (ePP : (A ⊗[A'] P') ≃ₐ[A] P)
    (hePP : ∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' P x)
    (J' : Ideal P') [Module.Flat P' (AdicCompletion J' P')]
    [IsNoetherianRing (AdicCompletion J' P')]
    (hloc : ∀ g ∈ J',
      letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
        (Localization.awayMap (algebraMap P' P) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away (algebraMap P' P g)]
              (Localization.Away (algebraMap P' P g) ⊗[P] B)))
    (c : Ideal C) (hc : IsAdicComplete c C)
    (e : (((P ⊗[P'] AdicCompletion J' P') ⊗[P] B)) ≃+* C)
    (hAe : ∀ a : A, algebraMap A C a =
      e ((algebraMap A (P ⊗[P'] AdicCompletion J' P') a) ⊗ₜ[P] (1 : B)))
    (hJc : ∀ g ∈ J', e (((algebraMap P' P g) ⊗ₜ[P']
      (1 : AdicCompletion J' P')) ⊗ₜ[P] (1 : B)) ∈ c) :
    HasFlatAlgebraLift A' A C → HasFlatAlgebraLift A' A B := by
  -- the algebra structures on `C` over the completed presentation
  let : Algebra (P ⊗[P'] AdicCompletion J' P') C :=
    (e.toRingHom.comp (algebraMap (P ⊗[P'] AdicCompletion J' P')
      ((P ⊗[P'] AdicCompletion J' P') ⊗[P] B))).toAlgebra
  let : Algebra (AdicCompletion J' P') C :=
    ((algebraMap (P ⊗[P'] AdicCompletion J' P') C).comp
      (algebraMap (AdicCompletion J' P') (P ⊗[P'] AdicCompletion J' P'))).toAlgebra
  let : Algebra P' C := ((algebraMap (AdicCompletion J' P') C).comp
    (algebraMap P' (AdicCompletion J' P'))).toAlgebra
  have := isScalarTower_tensorProduct_right A' P' P (AdicCompletion J' P')
  have : IsScalarTower (AdicCompletion J' P') (P ⊗[P'] AdicCompletion J' P') C :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A (P ⊗[P'] AdicCompletion J' P') C :=
    IsScalarTower.of_algebraMap_eq hAe
  have : IsScalarTower A' (P ⊗[P'] AdicCompletion J' P') C :=
    IsScalarTower.to₁₃₄ A' A (P ⊗[P'] AdicCompletion J' P') C
  have : IsScalarTower A' (AdicCompletion J' P') C :=
    IsScalarTower.to₁₂₄ A' (AdicCompletion J' P') (P ⊗[P'] AdicCompletion J' P') C
  have : IsScalarTower P' (AdicCompletion J' P') C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' P' C := IsScalarTower.to₁₂₄ A' P' (AdicCompletion J' P') C
  -- the image of `J'` in `C` lies in the ideal of completeness
  have hJcC : ∀ g ∈ J', algebraMap P' C g ∈ c := by
    intro g hg
    have hval : algebraMap P' C g =
        e (((algebraMap P' P g) ⊗ₜ[P'] (1 : AdicCompletion J' P')) ⊗ₜ[P] (1 : B)) :=
      congrArg (fun y => e (y ⊗ₜ[P] 1)) (algebraMap_tensorProduct_comm P' P _ g).symm
    rw [hval]
    exact hJc g hg
  refine hasFlatAlgebraLift_of_baseChange_of_presentation h0DZ2 A' A P' P B
    (AdicCompletion J' P') C hsurjA hnilA hsurjP hkerP hsurjB ePP hePP J'
    (bijective_quotientMap_adicCompletion J') hloc e hAe (fun _ => rfl)
    (fun C' _ _ eCa => ?_)
  exact exists_algHom_adicCompletion_of_algebraLift A' A P' C C' hsurjA hnilA J' c hc hJcC
    (fun _ => rfl) eCa

/-! ### Stacks 0DZ3 -/

/-- Every finite type `A`-algebra `B` is presented by a polynomial algebra `P` over `A`, which is
the base change of the polynomial algebra `P'` over `A'` along a surjection `A' → A`. -/
private theorem exists_polynomial_presentation (A' A B : Type u) [CommRing A'] [CommRing A]
    [CommRing B] [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    [Algebra.FiniteType A B] (hsurjA : Function.Surjective (algebraMap A' A)) (R : Prop)
    (k : ∀ (P' P : Type u) [CommRing P'] [CommRing P] [IsNoetherianRing P'] [IsNoetherianRing P]
      [Algebra A' P'] [Algebra A' P] [Algebra A P] [Algebra P' P] [Algebra A' B] [Algebra P' B]
      [Algebra P B] [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' A B]
      [IsScalarTower A' P' B] [IsScalarTower A P B] [IsScalarTower P' P B]
      [Algebra.FormallySmooth A' P'] [Module.Flat A' P'] [Module.Finite P' B],
      Function.Surjective (algebraMap P' P) →
      RingHom.ker (algebraMap P' P) =
        (RingHom.ker (algebraMap A' A)).map (algebraMap A' P') →
      Function.Surjective (algebraMap P B) → Function.Surjective (algebraMap P' B) →
      ∀ ePP : (A ⊗[A'] P') ≃ₐ[A] P, (∀ x : P', ePP (1 ⊗ₜ[A'] x) = algebraMap P' P x) → R) :
    R := by
  classical
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType A B)
  let : Algebra (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) :=
    (MvPolynomial.map (algebraMap A' A)).toAlgebra
  have hsurjP : Function.Surjective
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A)) :=
    MvPolynomial.map_surjective _ hsurjA
  have hkerP : RingHom.ker
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A)) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' (MvPolynomial (Fin n) A')) :=
    MvPolynomial.ker_map (algebraMap A' A)
  have : IsScalarTower A' (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) := by
    refine IsScalarTower.of_algebraMap_eq fun a' => ?_
    show MvPolynomial.C (algebraMap A' A a') =
      MvPolynomial.map (algebraMap A' A) (MvPolynomial.C a')
    rw [MvPolynomial.map_C]
  let : Algebra (MvPolynomial (Fin n) A) B := f.toRingHom.toAlgebra
  have : IsScalarTower A (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have hsurjB : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) B) := hf
  let : Algebra (MvPolynomial (Fin n) A') B :=
    ((algebraMap (MvPolynomial (Fin n) A) B).comp
      (algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A))).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A' (MvPolynomial (Fin n) A) B :=
    IsScalarTower.to₁₃₄ A' A (MvPolynomial (Fin n) A) B
  have : IsScalarTower A' (MvPolynomial (Fin n) A') B :=
    IsScalarTower.to₁₂₄ A' (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) B
  have hsurjPB : Function.Surjective (algebraMap (MvPolynomial (Fin n) A') B) :=
    hsurjB.comp hsurjP
  have hfinP'B : Module.Finite (MvPolynomial (Fin n) A') B :=
    Module.Finite.of_surjective (Algebra.linearMap (MvPolynomial (Fin n) A') B) hsurjPB
  have hePP : ∀ x : MvPolynomial (Fin n) A',
      MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A ((1 : A) ⊗ₜ[A'] x) =
        algebraMap (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) x := by
    intro x
    rw [← MvPolynomial.algebraTensorAlgEquiv_symm_map (σ := Fin n) A' A x,
      AlgEquiv.apply_symm_apply]
    rfl
  exact k (MvPolynomial (Fin n) A') (MvPolynomial (Fin n) A) hsurjP hkerP hsurjB hsurjPB
    (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A' A) hePP

/-- **The first implication of Stacks 0DZ3.** A flat lift of `B` to `A'` gives one of the
`𝔟`-adic completion of `B`: the completion of the polynomial presentation `P'` presents the
completion of `B`, and Stacks 0DZ2 transports the module lift from `P'` to it. -/
theorem hasFlatAlgebraLift_adicCompletion_of_hasFlatAlgebraLift
    (h0DZ2 : FlatModuleLiftBaseChangeStatement.{u})
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h)) :
    HasFlatAlgebraLift A' A B → HasFlatAlgebraLift A' A (AdicCompletion b B) := by
  refine exists_polynomial_presentation A' A B hsurjA _ ?_
  intro P' P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsurjP hkerP hsurjB hsurjPB ePP hePP
  set I' : Ideal P' := Ideal.comap (algebraMap P' B) b
  have hb : I'.map (algebraMap P' B) = b := Ideal.map_comap_of_surjective _ hsurjPB b
  obtain ⟨e, he⟩ := exists_ringEquiv_tensorAdicCompletion A P' P B I'
  rw [← hb]
  refine hasFlatAlgebraLift_imp_baseChange_of_presentation h0DZ2 A' A P' P B
    (AdicCompletion I' P') hsurjA hnilA hsurjP hkerP hsurjB I'
    (bijective_quotientMap_adicCompletion I')
    (fun g hg => exists_flatModuleLift_localization_of_syntomic A' A P' P B hsurjA hnilA hsurjP
      hkerP b hsyn g hg)
    (AdicCompletion (I'.map (algebraMap P' B)) B) e (fun a => ?_)
  show algebraMap A _ a = e (((algebraMap A P a) ⊗ₜ[P'] (1 : AdicCompletion I' P'))
    ⊗ₜ[P] (1 : B))
  rw [he (algebraMap A P a), ← IsScalarTower.algebraMap_apply A P B]
  rfl

/-- **The second implication of Stacks 0DZ3.** A flat lift of the `𝔟`-adic completion of `B` to
`A'` gives one of `B`: a flat algebra lift of the completion is an `A'`-flat module lift over
the completed presentation `Q'`, and Stacks 0DZ2 transports that lift back to `P'`. -/
theorem hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion
    (h0DZ2 : FlatModuleLiftBaseChangeStatement.{u})
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h)) :
    HasFlatAlgebraLift A' A (AdicCompletion b B) → HasFlatAlgebraLift A' A B := by
  refine exists_polynomial_presentation A' A B hsurjA _ ?_
  intro P' P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsurjP hkerP hsurjB hsurjPB ePP hePP
  set I' : Ideal P' := Ideal.comap (algebraMap P' B) b
  have hb : I'.map (algebraMap P' B) = b := Ideal.map_comap_of_surjective _ hsurjPB b
  have hnoethB : IsNoetherianRing B :=
    isNoetherianRing_of_surjective P B (algebraMap P B) hsurjB
  -- the completed presentation, written at the ideal `𝔟` itself
  obtain ⟨e, he⟩ : ∃ e : ((P ⊗[P'] AdicCompletion I' P') ⊗[P] B) ≃+* AdicCompletion b B,
      ∀ p : P, e ((p ⊗ₜ[P'] (1 : AdicCompletion I' P')) ⊗ₜ[P] (1 : B)) =
        AdicCompletion.of b B (algebraMap P B p) := by
    rw [← hb]
    exact exists_ringEquiv_tensorAdicCompletion A P' P B I'
  -- the completion of `B` is Noetherian and complete along the extension of `𝔟`
  have hbfg : b.FG := IsNoetherian.noetherian b
  have hbquot : IsNoetherianRing (B ⧸ b) :=
    isNoetherianRing_of_surjective B (B ⧸ b) (Ideal.Quotient.mk b)
      Ideal.Quotient.mk_surjective
  have hCnoeth : IsNoetherianRing (AdicCompletion b B) :=
    (completion_noetherian B b hbquot hbfg).1
  have hCcomplete : IsAdicComplete (b.map (algebraMap B (AdicCompletion b B)))
      (AdicCompletion b B) := (completion_noetherian B b hbquot hbfg).2
  -- the image of `𝔭'` in the completion of `B` lies in the ideal of completeness
  have hJc : ∀ g ∈ I', e (((algebraMap P' P g) ⊗ₜ[P'] (1 : AdicCompletion I' P'))
      ⊗ₜ[P] (1 : B)) ∈ b.map (algebraMap B (AdicCompletion b B)) := by
    intro g hg
    rw [he (algebraMap P' P g), ← IsScalarTower.algebraMap_apply P' P B g]
    exact Ideal.mem_map_of_mem _ hg
  refine hasFlatAlgebraLift_of_adicCompletion_of_presentation h0DZ2 A' A P' P B
    (AdicCompletion b B) hsurjA hnilA hsurjP hkerP hsurjB ePP hePP I'
    (fun g hg => exists_flatModuleLift_localization_of_syntomic A' A P' P B hsurjA hnilA hsurjP
      hkerP b hsyn g hg)
    (b.map (algebraMap B (AdicCompletion b B))) hCcomplete e (fun a => ?_) hJc
  show algebraMap A _ a = e (((algebraMap A P a) ⊗ₜ[P'] (1 : AdicCompletion I' P'))
    ⊗ₜ[P] (1 : B))
  rw [he (algebraMap A P a), ← IsScalarTower.algebraMap_apply A P B]
  rfl

end Deformation

end
