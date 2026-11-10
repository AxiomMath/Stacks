module

public import StacksFrontier.Algebra.MittagLeffler.TensorProduct
public import StacksFrontier.Algebra.MittagLeffler.TensorProductPi

@[expose] public section

universe u v w t

/-!
# Mittag-Leffler modules descend along a finitely presented ring map

Let `R → S` be a ring map with `S` finitely presented as an `R`-module and let `M` be an
`S`-module. If `M` is Mittag-Leffler over `S`, in the intrinsic form 059E (1) — every map `f` from
a finitely presented module into `M` dominates and is dominated by a map `g` into a finitely
presented module — then `M` is Mittag-Leffler over `R`.

The source writes `M = colim M_i` as a directed colimit of finitely presented `S`-modules, notes
that the `M_i` are finitely presented over `R` as well (Lemma 0564), and observes that the
factorizations exhibiting the Mittag-Leffler condition are maps of `R`-modules as they stand. The
route taken here is the same idea read off the intrinsic form: a map `f : P → M` of `R`-modules
with `P` finitely presented over `R` factors as `P → S ⊗[R] P → M` with the second map `S`-linear
and `S ⊗[R] P` finitely presented over `S`, so the `g : S ⊗[R] P → Q` supplied by the hypothesis
composes with the first map to a map `P → Q` of `R`-modules, and `Q` is finitely presented over
`R` by 0564. Both dominations then transfer from `S` to `R` at once, because for an `S`-module `X`
and an `R`-module `N` the base-change cancellation `X ⊗[S] (S ⊗[R] N) ≃ X ⊗[R] N` identifies
`f ⊗ id_{S ⊗[R] N}` with `f ⊗ id_N`; taking `N` to a test `S`-module this way is what replaces the
source's remark that the maps of the system are already maps of `R`-modules.

## Main results

* `Stacks.MittagLeffler.ScalarRestriction.solution`: a Mittag-Leffler module over `S` is
  Mittag-Leffler over `R`, for `S` finitely presented as an `R`-module.

## Implementation notes

Domination is a containment of kernels, hence an additive matter, so the transfer of a domination
along an identification of tensor products is isolated once and for all in `ker_le_ker_of_comm`: a
commuting pair of squares whose vertical maps are additive isomorphisms carries a domination to a
domination, and the two rows may be linear over different rings, which is what lets a domination
over `S` be read as one over `R`. Both identifications used are natural in the module the maps go
out of. For the base-change cancellation that naturality is `rTensor_cancelBaseChange_apply`, the
`rTensor` counterpart of Mathlib's
`TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange`, which Mathlib does not have.

The half of 0564 that is used is `Module.FinitePresentation.trans`: a finitely presented module
over `S` is finitely presented over `R`. The `R`-module structure on the module `Q` produced by
the hypothesis is the restriction of scalars `Module.compHom Q (algebraMap R S)`, which is the
`Module R Q` witness handed back in the conclusion's existential.

Two constructions live in a universe larger than `Type v`, where the quantifiers of both
conditions sit, and are shrunk back into it: the base change `S ⊗[R] P` and, in the transfer of
domination, the test module `S ⊗[R] N`. Both are `v`-small because `S` is a finite module over the
`v`-small ring `R`, so `Shrink` and `Shrink.linearEquiv` move them into `Type v` without changing
the mathematics. Smallness of `S` is all that the two lemmas doing this need, so it is what they
assume.

## References

* [StacksProject 05CQ](https://stacks.math.columbia.edu/tag/05CQ)
* [StacksProject 059E](https://stacks.math.columbia.edu/tag/059E)
* [StacksProject 0564](https://stacks.math.columbia.edu/tag/0564)
-/

namespace Stacks.MittagLeffler.ScalarRestriction


open TensorProduct

/-- Tensoring on the right with an isomorphism `e` is natural: it carries `f ⊗ id` to `f ⊗ id`. -/
private theorem rTensor_lTensor_comm {S : Type w} [CommSemiring S] {X Y T T' : Type*}
    [AddCommMonoid X] [Module S X] [AddCommMonoid Y] [Module S Y] [AddCommMonoid T] [Module S T]
    [AddCommMonoid T'] [Module S T'] (f : X →ₗ[S] Y) (e : T' ≃ₗ[S] T) (x : X ⊗[S] T') :
    f.rTensor T (LinearEquiv.lTensor X e x) = LinearEquiv.lTensor Y e (f.rTensor T' x) := by
  have h : LinearMap.rTensor T f ∘ₗ LinearMap.lTensor X e.toLinearMap
      = LinearMap.lTensor Y e.toLinearMap ∘ₗ LinearMap.rTensor T' f := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  exact congr($h x)

/-- Domination of maps out of a module in `Type v` may be tested against every `v`-small module
once it is known against the modules of `Type v` itself: a `v`-small `T` is `S`-linearly
isomorphic to `Shrink.{v} T`, and tensoring with that isomorphism is natural. -/
private theorem ker_rTensor_le_of_small {S : Type w} [CommRing S] {X Y Z : Type v}
    [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y] [AddCommGroup Z] [Module S Z]
    (f : X →ₗ[S] Y) (g : X →ₗ[S] Z)
    (h : ∀ (N : Type v) [AddCommGroup N] [Module S N],
      LinearMap.ker (f.rTensor N) ≤ LinearMap.ker (g.rTensor N))
    (T : Type t) [AddCommGroup T] [Module S T] [Small.{v} T] :
    LinearMap.ker (f.rTensor T) ≤ LinearMap.ker (g.rTensor T) :=
  Stacks.MittagLeffler.TensorProductStable.ker_le_ker_of_comm
    (LinearEquiv.lTensor X (Shrink.linearEquiv S T))
    (LinearEquiv.lTensor Y (Shrink.linearEquiv S T))
    (LinearEquiv.lTensor Z (Shrink.linearEquiv S T))
    (rTensor_lTensor_comm f (Shrink.linearEquiv S T))
    (rTensor_lTensor_comm g (Shrink.linearEquiv S T)) (h (Shrink.{v} T))

section Naturality

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Type*} [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
  [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]

/-- Base-change cancellation `X ⊗[S] (S ⊗[R] N) ≃ X ⊗[R] N` is natural in the `S`-module `X`:
it carries `f ⊗ id_{S ⊗[R] N}` to `f ⊗ id_N`. The `lTensor` counterpart is Mathlib's
`TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange`. -/
private theorem rTensor_cancelBaseChange_apply (N : Type v) [AddCommGroup N] [Module R N]
    (f : X →ₗ[S] Y) (x : X ⊗[S] (S ⊗[R] N)) :
    (f.restrictScalars R).rTensor N (AlgebraTensorModule.cancelBaseChange R S S X N x) =
      AlgebraTensorModule.cancelBaseChange R S S Y N (f.rTensor (S ⊗[R] N) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a y =>
    induction y using TensorProduct.inductionOn with
    | tmul s n => simp
    | add u v hu hv => simp [tmul_add, hu, hv]
  | add x y hx hy => simp [hx, hy]

end Naturality

section RestrictScalars

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S] [Small.{v} S]
  {X Y Z : Type v} [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
  [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]
  [AddCommGroup Z] [Module R Z] [Module S Z] [IsScalarTower R S Z]
  (f : X →ₗ[S] Y) (g : X →ₗ[S] Z)

/-- Domination of `S`-linear maps between modules of `Type v` survives restriction of scalars to
`R`, for `S` a `v`-small ring: an `R`-module test object `N` is fed into the `S`-linear condition
as the `S`-module `S ⊗[R] N`, and base-change cancellation turns the resulting containment into
the containment over `R`. -/
private theorem ker_rTensor_restrictScalars_le
    (h : ∀ (N : Type v) [AddCommGroup N] [Module S N],
      LinearMap.ker (f.rTensor N) ≤ LinearMap.ker (g.rTensor N))
    (N : Type v) [AddCommGroup N] [Module R N] :
    LinearMap.ker ((f.restrictScalars R).rTensor N) ≤
      LinearMap.ker ((g.restrictScalars R).rTensor N) :=
  Stacks.MittagLeffler.TensorProductStable.ker_le_ker_of_comm
    (AlgebraTensorModule.cancelBaseChange R S S X N)
    (AlgebraTensorModule.cancelBaseChange R S S Y N)
    (AlgebraTensorModule.cancelBaseChange R S S Z N)
    (rTensor_cancelBaseChange_apply N f) (rTensor_cancelBaseChange_apply N g)
    (ker_rTensor_le_of_small f g h (S ⊗[R] N))

/-- Mutual domination of `S`-linear maps between modules of `Type v` survives restriction of
scalars to `R`, for `S` a `v`-small ring. -/
private theorem ker_rTensor_restrictScalars_eq
    (h : ∀ (N : Type v) [AddCommGroup N] [Module S N],
      LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N))
    (N : Type v) [AddCommGroup N] [Module R N] :
    LinearMap.ker ((f.restrictScalars R).rTensor N) =
      LinearMap.ker ((g.restrictScalars R).rTensor N) :=
  le_antisymm (ker_rTensor_restrictScalars_le f g (fun N' _ _ => (h N').le) N)
    (ker_rTensor_restrictScalars_le g f (fun N' _ _ => (h N').ge) N)

end RestrictScalars

/-- Every map `f : P → M` of `R`-modules from a finitely presented `P` into an `S`-module `M`
factors as an `R`-linear map into a finitely presented `S`-module followed by an `S`-linear map:
take the base change `S ⊗[R] P`, shrunk into the universe of `P`. -/
private theorem exists_baseChange_factorization {R : Type u} {S : Type w} {M : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [Small.{v} S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] (P : Type v) [AddCommGroup P] [Module R P]
    [Module.FinitePresentation R P] (f : P →ₗ[R] M) :
    ∃ (PS : Type v) (_ : AddCommGroup PS) (_ : Module R PS) (_ : Module S PS)
      (_ : IsScalarTower R S PS) (_ : Module.FinitePresentation S PS) (ι : P →ₗ[R] PS)
      (fS : PS →ₗ[S] M), f = (fS.restrictScalars R) ∘ₗ ι := by
  have hts : IsScalarTower R S (Shrink.{v} (S ⊗[R] P)) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      apply (Shrink.linearEquiv S (S ⊗[R] P)).injective
      simp [algebraMap_smul]
  have hfp : Module.FinitePresentation S (Shrink.{v} (S ⊗[R] P)) :=
    (LinearEquiv.finitePresentation_iff (Shrink.linearEquiv S (S ⊗[R] P))).mpr inferInstance
  exact ⟨Shrink.{v} (S ⊗[R] P), inferInstance, inferInstance, inferInstance, hts, hfp,
    (Shrink.linearEquiv R (S ⊗[R] P)).symm.toLinearMap ∘ₗ TensorProduct.mk R S P 1,
    (LinearMap.liftBaseChange S f) ∘ₗ (Shrink.linearEquiv S (S ⊗[R] P)).toLinearMap,
    by ext p; simp⟩

public theorem solution {R : Type u} {S : Type w} {M : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Small.{v} R] [Module.FinitePresentation R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M]
    (hM : ∀ (P : Type v) [AddCommGroup P] [Module S P] [Module.FinitePresentation S P]
      (f : P →ₗ[S] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module S Q)
        (_ : Module.FinitePresentation S Q) (g : P →ₗ[S] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module S N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  intro P _ _ _ f
  have : Small.{v} S := Module.Finite.small R S
  -- Factor `f` through the base change of `P`, a finitely presented `S`-module, and apply the
  -- Mittag-Leffler condition over `S` to that factorization.
  obtain ⟨PS, _, _, _, _, _, ι, fS, hf⟩ := exists_baseChange_factorization (S := S) P f
  obtain ⟨Q, _, _, _, gS, hker⟩ := hM PS fS
  -- `Q` is finitely presented over `R` by 0564, for the restricted scalar action.
  let _ : Module R Q := Module.compHom Q (algebraMap R S)
  have : IsScalarTower R S Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine ⟨Q, inferInstance, inferInstance, .trans R Q S, (gS.restrictScalars R) ∘ₗ ι,
    fun N _ _ => ?_⟩
  -- Both dominations transfer from `S` to `R` at once, and `f` and `g` differ from `fS` and `gS`
  -- by the same map `ι`.
  rw [hf, LinearMap.rTensor_comp, LinearMap.rTensor_comp, LinearMap.ker_comp, LinearMap.ker_comp,
    ker_rTensor_restrictScalars_eq fS gS hker N]

end Stacks.MittagLeffler.ScalarRestriction

/-!
# Mittag-Leffler modules and restriction of scalars

An `R`-module `M` is *Mittag-Leffler* (Definition 059F) if the equivalent conditions of
Proposition 059E hold. Only one of the five is intrinsic to `M`, namely condition (1), and it is
the one used here: for every finitely presented `R`-module `P` and every module map `f : P → M`
there are a finitely presented `R`-module `Q` and a module map `g : P → Q` such that `f` and `g`
dominate each other, i.e. `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every `R`-module `N`.

The Mittag-Leffler condition sees the base ring, so it is a genuine question how it behaves under
restriction of scalars along a ring map `R → S`. It descends whenever `S` is finitely presented as
an `R`-module: the source's proof writes `M = colim M_i` as a directed colimit of finitely
presented `S`-modules, notes that the `M_i` are then finitely presented as `R`-modules
(Lemma 0564, which is `Module.FinitePresentation.trans` in Mathlib), and observes that the
factorizations `f_{ij} = h ∘ f_{ik}` of condition 059E (3) are maps of `R`-modules as they stand,
so that the same system exhibits `M` as a Mittag-Leffler `R`-module. It does not ascend: by
Remark 05CS a module over the ring of dual numbers `S = R ⊕ Rε` may be Mittag-Leffler over `R`
without being Mittag-Leffler over `S`.

## Main results

* `Module.mittagLeffler_trans`: a Mittag-Leffler module over `S` is Mittag-Leffler over `R`, for
  `S` finitely presented as an `R`-module.

## Implementation notes

Neither Mathlib nor this project has a predicate for a Mittag-Leffler module — Mathlib's
`CategoryTheory.Functor.IsMittagLeffler` is the Mittag-Leffler condition on an inverse *system*,
and 059F has no Lean form yet — so the condition is spelled out inline on both sides of the
implication, in the intrinsic form 059E (1), the two sides differing only in the ring. Mutual
domination is spelled out as equality of the kernels of the tensored maps, `f ⊗ id_N` being
`f.rTensor N`, as in 059D (`LinearMap.forall_ker_rTensor_le_iff_exists_eq_comp`).

The source's hypothesis is that `R → S` is a finite and finitely presented ring map; the
hypothesis here is `Module.FinitePresentation R S`, which the source's gives by
`Module.FinitePresentation.of_finite_of_finitePresentation` and which conversely gives
`Module.Finite R S`. This is what the proof uses, and it is all it uses: finite presentation of
`S` as an `R`-*algebra* enters the source only through Lemma 0564, whose own proof reduces it to
finite presentation of `S` as an `R`-module.

The modules `M`, `P`, `Q`, `N` live in one universe `Type v` and `R` is `v`-small, as in 059D.
For a `v`-small `R` every finitely presented `R`-module is isomorphic to one in `Type v`, so the
displayed quantifiers are the source's quantifiers over all finitely presented modules and all
test modules; smallness of `S` is not assumed because it follows, `S` being a quotient of `Rⁿ`.

Faithfulness. (1) Every hypothesis is used: the Mittag-Leffler hypothesis over `S` is the
conclusion's content, `Module.FinitePresentation R S` is what makes the `M_i` finitely presented
over `R` and cannot be dropped (over a non-coherent ring `R` a finitely presented `S`-module need
not even be finitely generated over `R`), the tower `IsScalarTower R S M` is what makes the two
conditions conditions on one module, and `Small.{v} R` is what makes the quantifier over
`P, N : Type v` the source's quantifier over all modules. (2) The scalars and the base are the
source's: the hypothesis quantifies over `S`-modules and `S`-linear maps and tensors over `S`, the
conclusion over `R`-modules and `R`-linear maps and tensors over `R`, and the `R`-module structure
on `M` is the one restricted from `S` along the tower. (3) The source names no canonical map: `Q`
and `g` are existentially quantified in 059E (1) itself, and what is canonical is pinned — the
maps whose kernels are compared are `f.rTensor N` and `g.rTensor N`, not arbitrary maps
`P ⊗ N → M ⊗ N` and `P ⊗ N → Q ⊗ N`. (4) The instantiation is not degenerate: the hypothesis is
satisfied whenever `M` is a finitely presented `S`-module, with `Q = M` and `g = f`, while the
conclusion is not satisfied by every module, since `ℚ` is not a Mittag-Leffler `ℤ`-module (it is
flat and countably generated but not projective, Theorem 059Z); and the implication is strict by
Remark 05CS, so it is not an instance of an equivalence.

## References

* [StacksProject 05CQ](https://stacks.math.columbia.edu/tag/05CQ)
-/


@[expose] public section

/-- **Stacks 05CQ.** Let `R → S` be a ring map with `S` finitely presented as an `R`-module (for
instance a finite and finitely presented ring map) and let `M` be an `S`-module. If `M` is
Mittag-Leffler over `S` then `M` is Mittag-Leffler over `R`. The Mittag-Leffler condition is
spelled out in the intrinsic form 059E (1): every map `f` from a finitely presented module into
`M` dominates and is dominated by a map `g` into a finitely presented module, domination meaning
containment of the kernels of the maps `· ⊗ id_N`. -/
@[stacks 05CQ "Mittag-Leffler is spelled out inline as condition (1) of 059E."]
public theorem Module.mittagLeffler_trans {R : Type u} {S : Type w} {M : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Small.{v} R] [Module.FinitePresentation R S] [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M]
    (hM : ∀ (P : Type v) [AddCommGroup P] [Module S P] [Module.FinitePresentation S P]
      (f : P →ₗ[S] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module S Q)
        (_ : Module.FinitePresentation S Q) (g : P →ₗ[S] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module S N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) :=
    by exact Stacks.MittagLeffler.ScalarRestriction.solution (S := S) hM

end

/-!
# Mittag-Leffler descends along a ring map for a flat Mittag-Leffler module

Let `R → S` be a ring map and let `M` be an `S`-module which is flat over `S`. This file proves
that `M` is Mittag-Leffler over `R` as soon as `S` is Mittag-Leffler over `R` and `M` is
Mittag-Leffler over `S`.

The proof is the source's. By Proposition 059M
(`Module.mittagLeffler_iff_piRightHom_injective`) being Mittag-Leffler is injectivity of the
comparison map `N ⊗ (∀ α, Q α) → ∀ α, N ⊗ Q α` for every family `(Q α)`, so it suffices to
factor the comparison map of `M` over `R` through maps that are injective for the stated reasons.
Read through the base change isomorphism `M ⊗[S] (S ⊗[R] N) ≅ M ⊗[R] N`, that map becomes
`M ⊗[S] (S ⊗[R] ∀ α, Q α) → M ⊗[S] (∀ α, S ⊗[R] Q α) → ∀ α, M ⊗[S] (S ⊗[R] Q α)`: the first is
`M ⊗[S] ·` applied to the comparison map of `S` over `R`, injective because that map is injective
and `M` is flat over `S`, and the second is the comparison map of `M` over `S` at the family
`(S ⊗[R] Q α)` of `S`-modules.

## Main results

* `Stacks.MittagLeffler.FlatTransitivity.solution`: the statement of
  `Module.mittagLeffler_trans_of_flat`.

## Implementation notes

The factorisation is `Stacks.MittagLeffler.FlatTransitivity.piRightHom_comp_cancelBaseChange`, an
identity of `S`-linear maps holding for any `S`-module `M`, with no flatness or finiteness
hypothesis: it is naturality of `TensorProduct.piRightHom` with respect to the base change
cancellation `TensorProduct.AlgebraTensorModule.cancelBaseChange`. Mathlib has the companion
`TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange`, which is the same square with a
single module in place of the product, but not this one.

The comparison map used in the factorisation is `TensorProduct.piRightHom R S M Q`, the `S`-linear
form, while Proposition 059M is stated with the `R`-linear form `TensorProduct.piRightHom R R M Q`.
The two have the same underlying function definitionally — `piRightHom` is the lift of
`piRightHomBil`, whose value does not mention the intermediate ring — so injectivity transfers
with no intervening lemma.

## References

* [StacksProject 05CT](https://stacks.math.columbia.edu/tag/05CT)
-/



@[expose] public section

namespace Stacks.MittagLeffler.FlatTransitivity

open TensorProduct

/-- The comparison map `M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` of an `S`-module `M`, read through
the base change isomorphisms `M ⊗[S] (S ⊗[R] N) ≅ M ⊗[R] N`, is `M ⊗[S] ·` applied to the
comparison map of `S` over `R` followed by the comparison map of `M` over `S` at the family
`(S ⊗[R] Q α)`. -/
private lemma piRightHom_comp_cancelBaseChange (R : Type u) (S : Type v) [CommRing R]
    [CommRing S] [Algebra R S] (M : Type v) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] {A : Type v} (Q : A → Type v) [∀ α, AddCommGroup (Q α)]
    [∀ α, Module R (Q α)] :
    piRightHom R S M Q ∘ₗ
        (AlgebraTensorModule.cancelBaseChange R S S M (∀ α, Q α)).toLinearMap =
      (LinearEquiv.piCongrRight fun α ↦
          AlgebraTensorModule.cancelBaseChange R S S M (Q α)).toLinearMap ∘ₗ
        piRightHom S S M (fun α ↦ S ⊗[R] Q α) ∘ₗ
          LinearMap.lTensor M (piRightHom R S S Q) := by
  ext m s q
  simp

public theorem solution {R : Type u} {S M : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Small.{v} R] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Flat S M]
    (hS : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] S), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N))
    (hM : ∀ (P : Type v) [AddCommGroup P] [Module S P] [Module.FinitePresentation S P]
      (f : P →ₗ[S] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module S Q)
        (_ : Module.FinitePresentation S Q) (g : P →ₗ[S] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module S N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  -- Both hypotheses and the conclusion are turned into interchange of `⊗` with products, 059M.
  have hSinj := (Module.mittagLeffler_iff_piRightHom_injective R S).mp hS
  have hMinj := (Module.mittagLeffler_iff_piRightHom_injective S M).mp hM
  refine (Module.mittagLeffler_iff_piRightHom_injective R M).mpr ?_
  intro A Q _ _
  -- The first map of the factorisation: `M ⊗[S] ·` on the comparison map of `S` over `R`.
  have h₁ : Function.Injective (LinearMap.lTensor M (piRightHom R S S Q)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (hSinj A Q)
  suffices h : Function.Injective (piRightHom R S M Q ∘ₗ
      (AlgebraTensorModule.cancelBaseChange R S S M (∀ α, Q α)).toLinearMap) by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe] at h
    exact h.of_comp_right (AlgebraTensorModule.cancelBaseChange R S S M (∀ α, Q α)).surjective
  rw [piRightHom_comp_cancelBaseChange]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe]
  -- The second map is the comparison map of `M` over `S` at the family `(S ⊗[R] Q α)`.
  exact ((LinearEquiv.piCongrRight fun α ↦
    AlgebraTensorModule.cancelBaseChange R S S M (Q α)).injective.comp
      (hMinj A fun α ↦ S ⊗[R] Q α)).comp h₁

end Stacks.MittagLeffler.FlatTransitivity

end

/-!
# Mittag-Leffler descends along a ring map for a flat Mittag-Leffler module

Let `R → S` be a ring map and let `M` be an `S`-module. An `R`-module is *Mittag-Leffler*
(Definition 059F) when the equivalent conditions of Proposition 059E hold; only condition (1)
of those is intrinsic to the module, and it is the one used here: every map `f : P → M` from a
finitely presented module dominates and is dominated by a map `g : P → Q` into a finitely
presented module, domination meaning `Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every test module `N`.

The property sees the base ring, so restriction of scalars along `R → S` is a genuine question.
This file states that it descends as soon as `S` is Mittag-Leffler over `R` and `M` is flat as
well as Mittag-Leffler over `S`. The source's proof reads the property off the characterization
of Proposition 059M — `M` is Mittag-Leffler over `R` exactly when the canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is injective for every family `(Q α)` of `R`-modules — and
factors that map, through the canonical isomorphism `M ⊗[R] Q = M ⊗[S] (S ⊗[R] Q)`, as
`M ⊗[S] (S ⊗[R] ∀ α, Q α) → M ⊗[S] (∀ α, S ⊗[R] Q α) → ∀ α, M ⊗[S] (S ⊗[R] Q α)`.
The first map is `M ⊗[S] ·` applied to the comparison map for `S` over `R`, injective because
that comparison map is injective (`S` being Mittag-Leffler over `R`) and `M` is flat over `S`;
the second is the comparison map for `M` over `S` at the family `(S ⊗[R] Q α)` of `S`-modules,
injective because `M` is Mittag-Leffler over `S`.

This complements Lemma 05CQ, which drops both hypotheses on `S` as an `R`-module in exchange for
`S` being finitely presented as one: here `S` may have infinite rank over `R`, as for `R = ℤ`
and `S = ℤ[X]`, and there `M` need not be flat. The property does not ascend in either setting:
by Remark 05CS a module over the ring of dual numbers may be Mittag-Leffler over `R` and not
over `S`.

## Main results

* `Module.mittagLeffler_trans_of_flat`: for a ring map `R → S` with `S` Mittag-Leffler as an
  `R`-module, a flat Mittag-Leffler `S`-module is Mittag-Leffler as an `R`-module.

## Implementation notes

Departures from the source's form, none of them weakening it.

*The Mittag-Leffler property is spelled out, three times.* Neither Mathlib nor this project has
a predicate for a Mittag-Leffler module — `CategoryTheory.Functor.IsMittagLeffler` is the
Mittag-Leffler condition on an inverse *system*, that is condition (4) of 059E for the dual
systems, and does not apply to a module on its own — so the condition is written inline in the
intrinsic form 059E (1), as in Propositions 059M and 05CQ and Lemmas 059N and 059P. The same
text appears three times, differing only in the ring: over `R` for `S`, over `S` for `M`, and
over `R` for `M`. Mutual domination is equality of the kernels of the tensored maps, `f ⊗ id_N`
being `f.rTensor N`, which is the form in which 059D
(`LinearMap.forall_ker_rTensor_le_iff_exists_eq_comp`) supplies it.

*Flatness is Mathlib's `Module.Flat S M`, an instance hypothesis*, so that flatness already
known to the instance graph — a free or projective `S`-module, a localization of `S` — costs no
argument at the call site.

*Universes.* `S` and `M` live in one universe `Type v`, and so do the finitely presented modules
`P`, `Q` and the test modules `N` of all three Mittag-Leffler conditions, as in 059D, 059E, 059M
and 05CQ. `Small.{v} R` is what makes those quantifiers the source's quantifiers over all
finitely presented modules and all test modules (Lemma 059C), and it is what lets 059M be
applied over `R`; `Small.{v} S`, needed to apply 059M over `S`, is automatic from `S : Type v`
by `small_self`. A ring in another universe `S : Type w` is reached by applying the statement at
`max v w` to `ULift` copies of `S` and `M`, which are isomorphic to them as a ring and as a
module. Unlike in 05CQ, where finite presentation of `S` over `R` makes `Small.{v} S` a
consequence of `Small.{v} R`, nothing here bounds the size of `S`, so keeping `S` and `M` in one
universe is what avoids a second smallness hypothesis in place of the source's silence about
universes.

Faithfulness. (1) No hypothesis is dead: `hS` cannot be dropped — for `R = ℤ` and `S = M = ℚ`
the module `M` is flat and Mittag-Leffler over `S`, being `S` itself, while `ℚ` is not a
Mittag-Leffler `ℤ`-module (Example 059I), which is also the failure of `hS`; `hM` cannot be
dropped — for `R = S = ℤ` and `M = ℚ` the ring `S` is free hence Mittag-Leffler over `R` and `M`
is flat, and the conclusion fails; `Module.Flat S M` is what makes the first of the two maps
above injective, and is the only place flatness of `M` over `S` enters; and the tower
`IsScalarTower R S M` is what makes the three conditions conditions on one module. (2) The
scalars and the base are the source's: `hS` quantifies over `R`-modules with `R`-linear maps and
`⊗[R]`, `hM` over `S`-modules with `S`-linear maps and `⊗[S]`, the conclusion over `R`-modules
with `R`-linear maps and `⊗[R]`; the `R`-module structure on `M` is the one restricted from `S`
along the tower and the `R`-module structure on `S` is the one from `Algebra R S`; nothing is
localized or base changed. (3) The source's statement names no map — `Q` and `g` are
existentially quantified in 059E (1) itself — and what is canonical is pinned: the maps whose
kernels are compared are `f.rTensor N` and `g.rTensor N`, built from the given `f` and the
produced `g`, not arbitrary maps `P ⊗ N → M ⊗ N`. (4) The instantiation is not degenerate: for
`R = ℤ` and `S = M = ℤ[X]` all three hypotheses hold and the conclusion is the non-trivial
assertion that `ℤ[X]` is Mittag-Leffler over `ℤ`, while the two instantiations above show that
the conclusion is not universally true, so the implication has content and is not an instance of
an equivalence.

## References

* [StacksProject 05CT](https://stacks.math.columbia.edu/tag/05CT)
-/



@[expose] public section

/-- **Stacks 05CT.** Let `R → S` be a ring map and let `M` be an `S`-module. If `S` is
Mittag-Leffler as an `R`-module, and `M` is flat and Mittag-Leffler as an `S`-module, then `M` is
Mittag-Leffler as an `R`-module. Being Mittag-Leffler is spelled out in the intrinsic form
059E (1): every map `f : P → M` from a finitely presented module dominates and is dominated by a
map `g : P → Q` into a finitely presented module, domination meaning
`Ker(f ⊗ id_N) = Ker(g ⊗ id_N)` for every test module `N`. -/
@[stacks 05CT "Mittag-Leffler is spelled out inline as condition (1) of 059E, as in 059M, 059N,
059P and 05CQ; flatness is `Module.Flat S M`. `S` and `M` share the universe of the test data,
whence the single `Small.{v} R`. See the module docstring."]
public theorem Module.mittagLeffler_trans_of_flat {R : Type u} {S M : Type v} [CommRing R]
    [CommRing S] [Algebra R S] [Small.{v} R] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] [Module.Flat S M]
    (hS : ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] S), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N))
    (hM : ∀ (P : Type v) [AddCommGroup P] [Module S P] [Module.FinitePresentation S P]
      (f : P →ₗ[S] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module S Q)
        (_ : Module.FinitePresentation S Q) (g : P →ₗ[S] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module S N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) :
    ∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) :=
    by exact Stacks.MittagLeffler.FlatTransitivity.solution (S := S) hS hM

end
