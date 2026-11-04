module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Rat.Star
import Mathlib.LinearAlgebra.FreeProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Algebra.MittagLeffler.DirectSum
import StacksFrontier.Algebra.MittagLeffler.TensorProductPi

/-!
# Finitely presented, free and projective modules are Mittag-Leffler
-/

@[expose] public section

universe u v

/-!
# Finitely presented, free and projective modules are Mittag-Leffler

Let `R` be a commutative ring. An `R`-module `M` is *Mittag-Leffler* (Definition 059F) in the
intrinsic form 059E (1) when every map `f : P → M` from a finitely presented `R`-module dominates
and is dominated by some map `g : P → Q` into a finitely presented `R`-module, that is
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`. This file proves the first three examples
of Example 059R: a finitely generated module is Mittag-Leffler if and only if it is finitely
presented, and a projective module — in particular a free one — is Mittag-Leffler.

A finitely presented `M` is Mittag-Leffler for a trivial reason in this spelling: `Q = M` and
`g = f` witness the condition, the two kernels then being the same submodule. For the converse,
let `M` be finitely generated. Proposition 059M reads the Mittag-Leffler property off injectivity
of the comparison map `M ⊗ (∏_α Q α) → ∏_α (M ⊗ Q α)` for all families `(Q α)`, Proposition 059J
reads finite generation off its surjectivity, and Proposition 059K reads finite presentation off
its bijectivity. So for a finitely generated `M` the comparison maps are surjective, and the
Mittag-Leffler property upgrades them to bijections; that is finite presentation.

The second and third items rest on one lemma: the Mittag-Leffler property passes to a *retract*.
If `p ∘ i = id_M` and `f : P → M`, then `f` and `i ∘ f` have literally the same tensored kernels —
one inclusion because `(i ∘ f) ⊗ id_N` factors through `f ⊗ id_N`, the other because `i ⊗ id_N` is
injective, having `p ⊗ id_N` as a left inverse — so a witness for `i ∘ f` in a Mittag-Leffler `F`
is a witness for `f`. A direct sum of copies of `R` is Mittag-Leffler by Proposition 059P, each
summand being finitely presented, which is the free case; and the free module on the underlying set
of `M` surjects onto `M`, a surjection that splits when `M` is projective, exhibiting `M` as a
retract of a free module. This is the source's argument for free modules (condition (1) of 059E
holds with `Q` a free summand) merged with its deduction of the projective case from Proposition
059P.

## Main results

* `Stacks.MittagLeffler.OfProjective.solution`: Example 059R (1) and (3) — a finitely generated
module is Mittag-Leffler if and only if it is finitely presented, and a projective module is
  Mittag-Leffler.
* `Stacks.MittagLeffler.OfProjective.isMittagLeffler_of_comp_eq_id`: the lemma the last two items
rest on, that the Mittag-Leffler property passes to a retract.

## Implementation notes

The Mittag-Leffler condition of 059E (1) is written `Module.IsMittagLefflerKerEq R M`: the
single-universe spelling in which domination of `f : P →ₗ[R] M` by `g : P →ₗ[R] Q` is equality of
the kernels of `f.rTensor N` and `g.rTensor N`. Being an `abbrev`, it unifies with the condition
spelled out in 059M and 059P.

The free module of which a projective `M : Type v` is a retract must itself live in `Type v`,
where the quantifiers of condition (1) sit, whereas `M →₀ R` lands in `Type (max u v)`. It is
taken to be `⨁ (_ : M), Shrink.{v} R`, a direct sum of copies of `R` moved into `Type v` by
`Shrink`, available because `R` is `v`-small; this is the device of 05CN, 05CP and 05CQ, and taking
a `DirectSum` rather than a `Finsupp` is what lets Proposition 059P apply on the nose. The
splitting is `Module.projective_lifting_property` against the identity of `M`, so the summand
decomposition of the source's "direct summand of a free module" is produced by projectivity rather
than assumed. The identification of `Shrink.{v} R` with `R` is taken as `Shrink.algEquiv`, whose
`R`-module structure on `Shrink.{v} R` is the one coming from `Algebra R R` that instance search
finds, rather than as `Shrink.linearEquiv`, which carries the transported structure
`Shrink.instModule` and so does not compose with a map out of `⨁ (_ : M), Shrink.{v} R`.

The two lemmas behind the retract step are stated under their minimal hypotheses and for arbitrary
universes, since neither needs the Mittag-Leffler condition or a `v`-small ring:
`Stacks.MittagLeffler.OfProjective.ker_rTensor_comp_left_eq` compares the tensored kernels of `f`
and `i ∘ f` for any
`i` with `i ⊗ id_N` injective, and
`Stacks.MittagLeffler.OfProjective.injective_rTensor_of_comp_eq_id` says that a
split injection is universally injective, which is item (1) of Lemma 058J for a split sequence.

## References

* [StacksProject 059R](https://stacks.math.columbia.edu/tag/059R)
* [StacksProject 059E](https://stacks.math.columbia.edu/tag/059E)
-/

namespace Stacks.MittagLeffler.OfProjective

open scoped DirectSum

/-! ### The Mittag-Leffler property passes to a retract -/

section Retract

variable {R : Type u} [CommRing R]

/-- A split injection is universally injective: if `p ∘ i = id`, then `i ⊗ id_N` is injective for
every `R`-module `N`, with left inverse `p ⊗ id_N`. This is item (1) of Lemma 058J for a split
short exact sequence. -/
private theorem injective_rTensor_of_comp_eq_id {M F : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F] {i : M →ₗ[R] F} {p : F →ₗ[R] M} (hpi : p ∘ₗ i = LinearMap.id)
    (N : Type*) [AddCommGroup N] [Module R N] : Function.Injective (i.rTensor N) :=
  LinearMap.injective_of_comp_eq_id _ (p.rTensor N) <| by
    rw [← LinearMap.rTensor_comp, hpi, LinearMap.rTensor_id]

/-- Composing with a universally injective map does not change the tensored kernels: if
`i ⊗ id_N` is injective, then `Ker((i ∘ f) ⊗ id_N) = Ker(f ⊗ id_N)`. -/
private theorem ker_rTensor_comp_left_eq {M F P : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F] [AddCommGroup P] [Module R P] (i : M →ₗ[R] F) (f : P →ₗ[R] M)
    (N : Type*) [AddCommGroup N] [Module R N] (hi : Function.Injective (i.rTensor N)) :
    LinearMap.ker ((i ∘ₗ f).rTensor N) = LinearMap.ker (f.rTensor N) := by
  rw [LinearMap.rTensor_comp]
  exact LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hi)

/-- The Mittag-Leffler property passes to a retract: if `p ∘ i = id_M` and `F` is Mittag-Leffler,
then so is `M`. A witness for `i ∘ f` is a witness for `f`, the two having the same tensored
kernels. -/
private theorem isMittagLeffler_of_comp_eq_id {M F : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F] {i : M →ₗ[R] F} {p : F →ₗ[R] M} (hpi : p ∘ₗ i = LinearMap.id)
    (hF : _root_.Module.IsMittagLefflerKerEq R F) :
    _root_.Module.IsMittagLefflerKerEq R M := by
  intro P _ _ _ f
  obtain ⟨Q, _, _, _, g, hg⟩ := hF P (i ∘ₗ f)
  exact ⟨Q, inferInstance, inferInstance, inferInstance, g, fun N _ _ =>
    (ker_rTensor_comp_left_eq i f N (injective_rTensor_of_comp_eq_id hpi N)).symm.trans (hg N)⟩

end Retract

/-! ### The three examples -/

/-- A finitely presented module is Mittag-Leffler: in the spelling 059E (1) the condition holds
with `Q = M` and `g = f`. This is the first sentence of Example 059R (1). -/
private theorem isMittagLeffler_of_finitePresentation (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    _root_.Module.IsMittagLefflerKerEq R M :=
  fun _ _ _ _ f => ⟨M, inferInstance, inferInstance, inferInstance, f, fun _ _ _ => rfl⟩

section Small

variable (R : Type u) [CommRing R] [Small.{v} R]

/-- **Example 059R (1).** A finitely generated `R`-module is Mittag-Leffler if and only if it is
finitely presented: the comparison maps `M ⊗ (∏_α Q α) → ∏_α (M ⊗ Q α)` are surjective by 059J,
injective exactly when `M` is Mittag-Leffler by 059M, and bijective exactly when `M` is finitely
presented by 059K. -/
private theorem isMittagLeffler_iff_finitePresentation (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    _root_.Module.IsMittagLefflerKerEq R M ↔ Module.FinitePresentation R M := by
  refine ⟨fun hML => ?_, fun _ => isMittagLeffler_of_finitePresentation R M⟩
  have hinj := (Module.mittagLeffler_iff_piRightHom_injective R M).mp hML
  have hsurj := ((Module.Finite.tfae_piRightHom_surjective R M).out 1 2).mp ‹Module.Finite R M›
  have hbij := (Module.FinitePresentation.tfae_piRightHom_bijective R M).out 2 1
  exact hbij.mp fun A Q _ _ => ⟨hinj A Q, hsurj A Q⟩

/-- **Example 059R (2).** A free module is Mittag-Leffler: a direct sum of copies of `R` is
Mittag-Leffler by 059P, `R` being finitely presented over itself. The copies are `Shrink.{v} R`,
`R` moved into the universe where the condition's quantifiers sit. -/
private theorem isMittagLeffler_directSum_shrink (ι : Type v) :
    _root_.Module.IsMittagLefflerKerEq R (⨁ _ : ι, Shrink.{v} R) :=
  have : Module.FinitePresentation R (Shrink.{v} R) :=
    Module.finitePresentation_of_projective R _
  (Module.mittagLeffler_directSum_iff R _).mpr fun _ =>
    isMittagLeffler_of_finitePresentation R (Shrink.{v} R)

/-- Every `R`-module `M` is a quotient of the free module on its underlying set: the direct sum of
copies of `R` indexed by `M` surjects onto `M`, the generator at `m` going to `m`. -/
private theorem exists_surjective_directSum_shrink (M : Type v) [AddCommGroup M] [Module R M] :
    ∃ q : (⨁ _ : M, Shrink.{v} R) →ₗ[R] M, Function.Surjective q := by
  classical
  refine ⟨DirectSum.toModule R M M fun m =>
    LinearMap.toSpanSingleton R M m ∘ₗ (Shrink.algEquiv R R).toLinearEquiv.toLinearMap,
    fun m => ⟨DirectSum.lof R M _ m ((Shrink.algEquiv R R).symm 1),
      (DirectSum.toModule_lof R m _).trans ?_⟩⟩
  simp

/-- **Example 059R (3).** A projective `R`-module is Mittag-Leffler: it is a retract of the free
module on its underlying set, which is Mittag-Leffler by Example 059R (2), the surjection from
that free module splitting by projectivity. -/
private theorem isMittagLeffler_of_projective (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Projective R M] : _root_.Module.IsMittagLefflerKerEq R M := by
  obtain ⟨q, hq⟩ := exists_surjective_directSum_shrink R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
  exact isMittagLeffler_of_comp_eq_id hs (isMittagLeffler_directSum_shrink R M)

end Small

/-- **Stacks 059R.** Let `R` be a commutative ring and `M` an `R`-module. Then (1) if `M` is
finitely generated, `M` is Mittag-Leffler if and only if `M` is finitely presented, and (2) if `M`
is projective, in particular if `M` is free, then `M` is Mittag-Leffler. -/
public theorem solution (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M]
    [Module R M] :
    (Module.Finite R M →
        ((∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
            (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
              (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
                [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
          Module.FinitePresentation R M)) ∧
      (Module.Projective R M →
        ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
          (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
            (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
              [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :=
  ⟨fun _ => isMittagLeffler_iff_finitePresentation R M, fun _ => isMittagLeffler_of_projective R M⟩

end Stacks.MittagLeffler.OfProjective

/-!
# Examples of Mittag-Leffler modules: finitely presented, free and projective modules

Let `R` be a commutative ring. An `R`-module `M` is *Mittag-Leffler* when every map `f : P → M`
from a finitely presented `R`-module dominates and is dominated by a map `g : P → Q` into a
finitely presented `R`-module, that is `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`;
this is condition (1) of Proposition 059E, the one of its five conditions that mentions `M` alone,
and it is Definition 059F.

This file states the first three examples of the class:

* a finitely generated module is Mittag-Leffler if and only if it is finitely presented; in
  particular every finitely presented module is Mittag-Leffler;
* a free module is Mittag-Leffler;
* a projective module is Mittag-Leffler.

The first is the combination of Propositions 059J, 059K and 059M: the comparison map
`M ⊗[R] (∏ Q α) → ∏ (M ⊗[R] Q α)` is surjective exactly when `M` is finitely generated (059J),
bijective exactly when `M` is finitely presented (059K), and injective exactly when `M` is
Mittag-Leffler (059M), so for a finitely generated `M` the Mittag-Leffler property upgrades
surjectivity to bijectivity and back. The second holds because a map from a finitely generated
module into a free module lands in a finite free direct summand, which is finitely presented and
through which the map factors, so condition (1) of Proposition 059E holds with `Q` that summand.
The third follows from the second and Proposition 059P, a direct sum being Mittag-Leffler exactly
when each of its summands is: a projective module is one summand of a free module.

## Main results

* `Module.mittagLeffler_iff_finitePresentation`: a finitely generated module is Mittag-Leffler if
  and only if it is finitely presented. This is item (1).
* `Module.mittagLeffler_of_projective`: a projective module is Mittag-Leffler. This is
  items (2) and (3).
* `Module.mittagLeffler_iff_finitePresentation_and_mittagLeffler_of_projective`: the two together,
  over one module and with the finiteness and the projectivity as antecedents. This is the
  example as the source states it, and the two results above are its two halves.

## Implementation notes

Departures from the source's form, none of them weakening it.

*The Mittag-Leffler property is spelled out.* The condition is written inline in the intrinsic
form 059E (1), the spelling of Propositions 059M, 059N, 059P and Lemma 05CQ, in each statement of
the file; `CategoryTheory.Functor.IsMittagLeffler` is the condition on an inverse system, that is
condition (4) of 059E for the dual systems, and does not apply to a module on its own. It is
byte-identical to the left-hand side of 059M, so that proposition applies to it without a bridge.

*Three items, two independent statements.* Items (1) and (3) are statements about one module `M`
that share no hypothesis beyond the ring and the module, so each is stated separately, over its
own hypothesis alone and with that hypothesis an instance hypothesis where instance inference will
find it: `Module.mittagLeffler_iff_finitePresentation` assumes `Module.Finite R M` and
`Module.mittagLeffler_of_projective` assumes `Module.Projective R M`.
Assuming both hypotheses of one statement would make item (3) say no more than item (1), a
finitely generated projective module being finitely presented
(`Module.finitePresentation_of_projective`); it is the separation that keeps item (3) the stronger
statement. The example as the source states it — the two implications over one module, with the
two hypotheses as antecedents — is
`Module.mittagLeffler_iff_finitePresentation_and_mittagLeffler_of_projective`, of which the two
are the halves.

The two items the source states but does not state independently are consequences of these by
instance inference rather than statements of their own: item (2), that a free module is
Mittag-Leffler, is `Module.mittagLeffler_of_projective` with `Module.Projective.of_free` supplying
the instance, and the first sentence of item (1), that a finitely presented module is
Mittag-Leffler, is the direction `←` of `Module.mittagLeffler_iff_finitePresentation` with
`instFiniteOfFinitePresentation` supplying the instance.

*Projectivity rather than "a direct summand of a free module".* `Module.Projective` is `Mathlib`'s
spelling of the source's hypothesis, and the summand decomposition the proof needs is
`Module.Projective.of_lifting_property` unfolded, not part of the statement. The statement is not
generalized to "a direct summand of a direct sum of finitely presented modules is Mittag-Leffler",
which is also true and which the same proof gives from 059P and 059N (1); that is a statement the
source makes nowhere in this section, and it needs an edge to 059N that the example does not have.

*Universes.* The module `M` and the modules `P`, `Q`, `N` of the Mittag-Leffler condition live in
`Type v`, with `R : Type u` assumed `Small.{v}`, the convention of 059K, 059M, 059N, 059P and
05CQ, through which the proof passes. This is not a weakening: `Small.{v} R` is automatic when
`v = max u v`, in particular whenever `R` and `M` share a universe, so the single-universe form is
the instance `v := max u v`. It is also what makes the `Type v` quantifiers the source's
quantifiers over all modules, domination being testable on the finitely presented modules of
`Type v` alone (Lemma 059C).

Faithfulness. (1) No hypothesis is dead: `Module.Finite R M` is used by the direction `→` of
`Module.mittagLeffler_iff_finitePresentation`, which fails without it — a free module of infinite
rank is Mittag-Leffler and not finitely presented — and `Module.Projective R M` is used by
`Module.mittagLeffler_of_projective`, which fails without it, since `ℚ` is not a Mittag-Leffler
`ℤ`-module (Example 059I); `Small.{v} R` is used as described above. (2) The scalars and the base
are the source's: one commutative ring `R` throughout, `M`, `P`, `Q` and `N` are `R`-modules, `f`
and `g` are `R`-linear, finite generation, finite presentation and projectivity are over `R`, and
every tensor product is `⊗[R]`; nothing is localized or base changed. (3) The maps of the
Mittag-Leffler condition are pinned, not merely asserted to exist: `f ⊗ id_N` is `f.rTensor N`,
built from `f` itself, and likewise `g.rTensor N`, and only the finitely presented module `Q` and
the map `g` are existentially quantified, as they are in 059E (1); the source names no other map.
(4) The instantiation is not degenerate and no statement is vacuous: for `R = ℤ` and `M = ℤ` all
of them hold with both sides of the equivalence true, `M` being finitely presented and projective;
the direction `→` of the equivalence has content, for `R = ℤ[x₁, x₂, …]` and `M = R ⧸ (x₁, x₂, …)`
the module `M` is finitely generated and not finitely presented, so it is not Mittag-Leffler; and
`Module.mittagLeffler_of_projective` says strictly more than the equivalence, for `R = ℤ` and
`M = ⨁ (_ : ℕ), ℤ` the module `M` is projective and Mittag-Leffler but not finitely presented.

## References

* [StacksProject 059R](https://stacks.math.columbia.edu/tag/059R)
-/



@[expose] public section

/-- **Stacks 059R.** Let `R` be a commutative ring and `M` an `R`-module. Then (1) if `M` is
finitely generated, `M` is Mittag-Leffler if and only if `M` is finitely presented — in particular
every finitely presented module is Mittag-Leffler — and (2) if `M` is projective, in particular if
`M` is free, then `M` is Mittag-Leffler. Being Mittag-Leffler is spelled out in the intrinsic form
059E (1): every map `f : P → M` from a finitely presented module dominates and is dominated by a
map `g : P → Q` into a finitely presented module, domination meaning
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`.

This is the example as the source states it, over one module. The two items are independent of
each other and each is stated separately, over its own hypothesis alone, as
`Module.mittagLeffler_iff_finitePresentation` and `Module.mittagLeffler_of_projective`. -/
@[stacks 059R "Items (1) and (3) together, over one module and with the two hypotheses as
antecedents; the forms to cite are the two halves. Mittag-Leffler is spelled out inline as
condition (1) of 059E, as in 059M, 059N and 059P. Test data in the universe of `M`, whence
`Small.{v} R`. See the module docstring."]
public theorem Module.mittagLeffler_iff_finitePresentation_and_mittagLeffler_of_projective
    (R : Type u) [CommRing R] [Small.{v} R] (M : Type v) [AddCommGroup M] [Module R M] :
    (Module.Finite R M →
        ((∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
            (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
              (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
                [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
          Module.FinitePresentation R M)) ∧
      (Module.Projective R M →
        ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
          (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
            (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
              [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :=
  Stacks.MittagLeffler.OfProjective.solution R M

/-- **Stacks 059R, item (1).** Let `R` be a commutative ring and `M` a finitely generated
`R`-module. Then `M` is Mittag-Leffler if and only if `M` is finitely presented; in particular
every finitely presented module is Mittag-Leffler, finite presentation implying finite generation.
Being Mittag-Leffler is spelled out in the intrinsic form
059E (1): every map `f : P → M` from a finitely presented module dominates and is dominated by a
map `g : P → Q` into a finitely presented module, domination meaning
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`. -/
@[stacks 059R "Item (1), with the finite generation an instance hypothesis; `finitely presented
implies Mittag-Leffler` is the direction `←`, via `instFiniteOfFinitePresentation`."]
public theorem Module.mittagLeffler_iff_finitePresentation (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      Module.FinitePresentation R M :=
  (Module.mittagLeffler_iff_finitePresentation_and_mittagLeffler_of_projective R M).1 inferInstance

/-- **Stacks 059R, items (2) and (3).** Let `R` be a commutative ring and `M` a projective
`R`-module, in particular a free one, `Module.Projective.of_free` being an instance. Then `M` is
Mittag-Leffler, spelled out in the intrinsic form 059E (1): every map `f : P → M` from a finitely
presented module dominates and is dominated by a map `g : P → Q` into a finitely presented module,
domination meaning `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`. -/
@[stacks 059R "Items (2) and (3), with the projectivity an instance hypothesis; item (2), a free
module, is this statement via `Module.Projective.of_free`."]
public theorem Module.mittagLeffler_of_projective (R : Type u) [CommRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Projective R M] :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
        (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
          (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) :=
  (Module.mittagLeffler_iff_finitePresentation_and_mittagLeffler_of_projective R M).2 inferInstance

end

end

/-!
# `ℚ` is not Mittag-Leffler

For a ring `R`, an `R`-module `M`, and a family `(Q_n)` of `R`-modules, there is
a canonical comparison map
  `c : M ⊗_R (∏_n Q_n) → ∏_n (M ⊗_R Q_n)`,
characterized on simple tensors by `c (m ⊗ (q_n)) = (m ⊗ q_n)`.

The two examples below (with `R = Z`, `M = Q`) show that `c` is in general
neither injective nor surjective.

* Statement 1: with `Q_n = Z/nZ`, the map `c` is not injective. Indeed the
  target `∏_n (Q ⊗ Z/nZ)` is the zero module (each `Q ⊗ Z/nZ = 0`), while the
  source `Q ⊗ (∏_n Z/nZ)` is nonzero.

* Statement 2: with `Q_n = Z`, identifying `Q ⊗ Z ≅ Q`, the map `c` is not
  surjective. Its image consists precisely of those sequences `(x_n) ∈ ∏_n Q`
  admitting a common denominator (a nonzero integer `m` with `x_n = a_n / m` for
  all `n`); e.g. the sequence `(1/n)_{n ≥ 1}` is not in the image.

## Indexing convention

The family is indexed by positive integers `n ≥ 1`. We index by `n : ℕ` and use
the modulus `n + 1`, so the moduli range over `1, 2, 3, …`. Including the term
`Z/1Z = 0` is harmless. (Indexing by `ℕ` directly with `ZMod n` would be wrong
for Statement 1 since `ZMod 0 = ℤ` and `Q ⊗ ℤ ≠ 0`.)
-/

@[expose] public section

open TensorProduct

/-- The canonical comparison map `c : M ⊗_R (∏_n Q_n) → ∏_n (M ⊗_R Q_n)`.
This is exactly `TensorProduct.piRightHom`, the unique `R`-linear map whose
composition with the `k`-th projection equals `id_M ⊗ pr_k`, given on simple
tensors by `m ⊗ (q_n) ↦ (m ⊗ q_n)`. We record it here specialized to the
present setting `R = S = ℤ`, `M = ℚ`. -/
noncomputable abbrev tensorPiComparison (Q : ℕ → Type) [∀ n, AddCommMonoid (Q n)]
    [∀ n, Module ℤ (Q n)] :
    ℚ ⊗[ℤ] (∀ n, Q n) →ₗ[ℤ] ∀ n, ℚ ⊗[ℤ] Q n :=
  TensorProduct.piRightHom ℤ ℤ ℚ Q

/-- The defining property on simple tensors: `c (m ⊗ q) n = m ⊗ q n`. -/
theorem comparisonMap_tmul (Q : ℕ → Type) [∀ n, AddCommMonoid (Q n)]
    [∀ n, Module ℤ (Q n)] (m : ℚ) (q : ∀ n, Q n) :
    tensorPiComparison Q (m ⊗ₜ[ℤ] q) = fun n => m ⊗ₜ[ℤ] q n :=
  TensorProduct.piRightHom_tmul ℤ ℤ ℚ Q m q

/-- For Statement 2, the comparison map composed with the canonical
isomorphisms `ℚ ⊗_ℤ ℤ ≅ ℚ` on each factor, giving a map into `∏_n ℚ`. Since
`TensorProduct.rid` is a linear isomorphism, surjectivity of this composite is
equivalent to surjectivity of `tensorPiComparison`. -/
noncomputable abbrev comparisonMapQ : (ℚ ⊗[ℤ] (∀ _ : ℕ, ℤ)) →ₗ[ℤ] (∀ _ : ℕ, ℚ) :=
  LinearMap.pi fun n =>
    (TensorProduct.rid ℤ ℚ).toLinearMap ∘ₗ (LinearMap.proj n) ∘ₗ
      (tensorPiComparison (fun _ : ℕ => ℤ))

-- needed: `comparisonMapQ_tmul`'s `rw [comparisonMap_tmul]` needs the `Pi.module` and
-- `AddCommGroup.toIntModule` instances on `ℕ → ℚ ⊗[ℤ] ℤ` to be defeq at `implicit`
-- transparency
set_option backward.isDefEq.respectTransparency false in
/-- `comparisonMapQ` on a simple tensor `x ⊗ b` is the sequence `n ↦ (b n) • x`,
i.e. `n ↦ x * (b n)`, matching the identification `ℚ ⊗ ℤ ≅ ℚ`, `x ⊗ a ↦ a x`. -/
theorem comparisonMapQ_tmul (x : ℚ) (b : ∀ _ : ℕ, ℤ) :
    comparisonMapQ (x ⊗ₜ[ℤ] b) = fun n => (b n : ℚ) * x := by
  ext n
  simp only [comparisonMapQ, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe]
  rw [comparisonMap_tmul]
  change (TensorProduct.rid ℤ ℚ) (x ⊗ₜ[ℤ] b n) = (b n : ℚ) * x
  rw [TensorProduct.rid_tmul]
  simp [mul_comm]

/-- A simple tensor `q ⊗ z` in `ℚ ⊗ ZMod (k+1)` is zero. -/
theorem rat_tmul_zmod_zero (k : ℕ) (q : ℚ) (z : ZMod (k + 1)) :
    q ⊗ₜ[ℤ] z = (0 : ℚ ⊗[ℤ] ZMod (k + 1)) := by
  have hq : q = ((k + 1 : ℤ)) • (q / (k + 1)) := by
    rw [zsmul_eq_mul]
    push_cast
    field_simp
  rw [hq, TensorProduct.smul_tmul]
  have hz : ((k + 1 : ℤ)) • z = 0 := by
    rw [zsmul_eq_mul, show ((k + 1 : ℤ) : ZMod (k + 1)) = 0 by
      exact_mod_cast ZMod.natCast_self (k + 1), zero_mul]
  rw [hz, TensorProduct.tmul_zero]

/-- `ℚ ⊗ ZMod (k+1)` is subsingleton. -/
theorem rat_tmul_zmod_subsingleton (k : ℕ) :
    Subsingleton (ℚ ⊗[ℤ] ZMod (k + 1)) := by
  rw [subsingleton_iff_forall_eq 0]
  intro y
  induction y using TensorProduct.induction_on with
  | zero => rfl
  | tmul q z => exact rat_tmul_zmod_zero k q z
  | add a b ha hb => rw [ha, hb, add_zero]

/-- **Statement 1, part 1.** The target `∏_n (Q ⊗_Z Z/(n+1)Z)` is the zero
module, since `Q ⊗_Z Z/(n+1)Z = 0` for every `n`. -/
theorem target_subsingleton :
    Subsingleton (∀ n : ℕ, ℚ ⊗[ℤ] ZMod (n + 1)) :=
  ⟨fun a b => funext fun n => (rat_tmul_zmod_subsingleton n).elim (a n) (b n)⟩

/-- The element `x = (1,1,1,…)` of `∏_n ZMod (n+1)` is not torsion. -/
theorem one_seq_not_torsion (a : ℤ) (ha : a • (fun n : ℕ => (1 : ZMod (n + 1))) = 0) :
    a = 0 := by
  -- look at component n = a.natAbs, where the modulus is a.natAbs + 1 > |a|
  set n := a.natAbs
  have key : ((a : ZMod (n + 1))) = 0 := by simpa using congrFun ha n
  have hdvd : ((n : ℤ) + 1) ∣ a := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd a (n + 1)).mp (by exact_mod_cast key)
  -- but |a| = n < n + 1, contradiction with divisibility by something larger
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by omega)

/-- **Statement 1, part 2.** The source `Q ⊗_Z (∏_n Z/(n+1)Z)` is nonzero. -/
theorem source_nontrivial :
    Nontrivial (ℚ ⊗[ℤ] (∀ n : ℕ, ZMod (n + 1))) := by
  -- e : ℤ →ₗ ∏ ZMod(n+1), 1 ↦ (1, 1, 1, ...)
  let e : ℤ →ₗ[ℤ] (∀ n : ℕ, ZMod (n + 1)) :=
    LinearMap.toSpanSingleton ℤ _ fun n => (1 : ZMod (n + 1))
  have he_inj : Function.Injective e := by
    intro a b hab
    simp only [e, LinearMap.toSpanSingleton_apply] at hab
    exact sub_eq_zero.mp (one_seq_not_torsion (a - b) (by rw [sub_smul, hab, sub_self]))
  -- ℚ ⊗ ℤ is nontrivial
  have : Nontrivial (ℚ ⊗[ℤ] ℤ) := (TensorProduct.rid ℤ ℚ).toEquiv.nontrivial
  exact (Module.Flat.lTensor_preserves_injective_linearMap e he_inj).nontrivial

/-- **Statement 1 (the comparison map need not be injective).**
With `Q_n = Z/(n+1)Z`, the canonical map
`c : Q ⊗_Z (∏_n Z/(n+1)Z) → ∏_n (Q ⊗_Z Z/(n+1)Z)` is not injective. -/
@[stacks 059I "(1)"]
theorem comparisonMap_not_injective :
    ¬ Function.Injective (tensorPiComparison (fun n : ℕ => ZMod (n + 1))) := by
  intro hinj
  obtain ⟨u, v, huv⟩ := source_nontrivial
  exact huv (hinj (target_subsingleton.elim _ _))

/-- Scalar identity: `(c : ℚ) * (1/m) ⊗ b = (1/m) ⊗ (c • b)`. -/
theorem tmul_intCast_smul (m c : ℤ) (b : ∀ _ : ℕ, ℤ) :
    ((c : ℚ) * (1 / (m : ℚ))) ⊗ₜ[ℤ] b
      = (1 / (m : ℚ)) ⊗ₜ[ℤ] (c • b : ∀ _ : ℕ, ℤ) := by
  rw [← zsmul_eq_mul, TensorProduct.smul_tmul]

/-- Rewriting `(1/m₁) ⊗ b` over the denominator `m₁ * m₂`. -/
theorem one_div_tmul_eq_one_div_mul_tmul_smul {m₁ m₂ : ℤ} (hm₂ : m₂ ≠ 0)
    (b : ∀ _ : ℕ, ℤ) :
    (1 / (m₁ : ℚ)) ⊗ₜ[ℤ] b = (1 / ((m₁ * m₂ : ℤ) : ℚ)) ⊗ₜ[ℤ] (m₂ • b : ∀ _ : ℕ, ℤ) := by
  have hm₂' : (m₂ : ℚ) ≠ 0 := by exact_mod_cast hm₂
  rw [show (1 / (m₁ : ℚ)) = (m₂ : ℚ) * (1 / ((m₁ * m₂ : ℤ) : ℚ)) by
    push_cast
    field_simp, tmul_intCast_smul]

/-- Every element of `ℚ ⊗ (∀ ℤ)` is a single simple tensor `(1/m) ⊗ b` with
`m ≠ 0`. -/
theorem exists_common_denom (t : ℚ ⊗[ℤ] (∀ _ : ℕ, ℤ)) :
    ∃ (m : ℤ) (b : ∀ _ : ℕ, ℤ), m ≠ 0 ∧ t = (1 / (m : ℚ)) ⊗ₜ[ℤ] b := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul x b =>
    refine ⟨x.den, x.num • b, by exact_mod_cast x.den_nz, ?_⟩
    -- x = num / den, so x ⊗ b = (num/den) ⊗ b = (1/den) ⊗ (num • b)
    rw [← tmul_intCast_smul, mul_one_div, Int.cast_natCast, Rat.num_div_den]
  | add s t hs ht =>
    obtain ⟨m₁, b₁, hm₁, hs⟩ := hs
    obtain ⟨m₂, b₂, hm₂, ht⟩ := ht
    refine ⟨m₁ * m₂, m₂ • b₁ + m₁ • b₂, mul_ne_zero hm₁ hm₂, ?_⟩
    -- (1/m₁) ⊗ b₁ + (1/m₂) ⊗ b₂ = (1/(m₁m₂)) ⊗ (m₂•b₁ + m₁•b₂)
    rw [hs, ht, one_div_tmul_eq_one_div_mul_tmul_smul hm₂ b₁,
      one_div_tmul_eq_one_div_mul_tmul_smul hm₁ b₂, mul_comm m₂ m₁, ← TensorProduct.tmul_add]

/-- **Statement 2, image characterization.** A sequence `x : ℕ → ℚ` lies in the
image of `c` (here `comparisonMapQ`) if and only if it admits a common
denominator: there is a nonzero integer `m` and integers `a_n` with
`x_n = a_n / m` for all `n`. -/
theorem range_comparisonMapQ (x : ∀ _ : ℕ, ℚ) :
    x ∈ Set.range comparisonMapQ ↔
      ∃ m : ℤ, m ≠ 0 ∧ ∀ n, ∃ a : ℤ, x n = (a : ℚ) / (m : ℚ) := by
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨m, b, hm, rfl⟩ := exists_common_denom t
    exact ⟨m, hm, fun n => ⟨b n, by
      rw [comparisonMapQ_tmul]
      exact mul_one_div _ _⟩⟩
  · rintro ⟨m, hm, hax⟩
    choose a ha using hax
    refine ⟨(1 / (m : ℚ)) ⊗ₜ[ℤ] a, ?_⟩
    rw [comparisonMapQ_tmul]
    funext n
    rw [ha n, mul_one_div]

/-- **Statement 2, explicit witness.** The sequence `(1/(n+1))_{n}` is not in
the image of `c`, since it has no common denominator. -/
theorem oneDiv_not_in_range :
    (fun n : ℕ => (1 : ℚ) / (n + 1)) ∉ Set.range comparisonMapQ := by
  rw [range_comparisonMapQ]
  rintro ⟨m, hm, h⟩
  -- evaluate at n = m.natAbs
  set n := m.natAbs
  obtain ⟨a, ha⟩ := h n
  -- ha : 1/(n+1) = a/m, hence m = a*(n+1)
  have key : (m : ℚ) = (a : ℚ) * ((n : ℚ) + 1) := by
    field_simp at ha
    linarith
  have keyZ : m = a * ((n : ℤ) + 1) := by exact_mod_cast key
  exact hm (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Dvd.intro_left a keyZ.symm) (by omega))

/-- **Statement 2 (the comparison map need not be surjective).**
With `Q_n = Z` and the identification `Q ⊗_Z Z ≅ Q`, the canonical map
`c : Q ⊗_Z (∏_n Z) → ∏_n Q` is not surjective. -/
@[stacks 059I "(2)"]
theorem comparisonMap_not_surjective :
    ¬ Function.Surjective comparisonMapQ :=
  fun hsurj => oneDiv_not_in_range (hsurj _)

end
