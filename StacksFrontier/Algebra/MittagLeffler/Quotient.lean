module

public import StacksFrontier.Algebra.MittagLeffler.RestrictScalars

@[expose] public section

universe u v w

/-!
# Mittag-Leffler modules over a quotient ring

Let `R` be a ring, let `S = R/I` for a finitely generated ideal `I` — presented here as an
`R`-algebra with surjective structure map which is finitely presented as an `R`-module — and let
`M` be an `S`-module. Then `M` is Mittag-Leffler over `R` if and only if it is Mittag-Leffler over
`S`, the condition being spelled out in the intrinsic form 059E (1).

The implication from `S` to `R` is Lemma 05CQ and needs no surjectivity. For the converse the
source writes `M = colim M_i` as a directed colimit of finitely presented `S`-modules, notes that
the `M_i` are finitely presented over `R` as well (Lemma 0564), and observes that
`Hom_R (M_i, N) = Hom_S (M_i, N)` for an `S`-module `N` because `R → S` is surjective, so that the
Mittag-Leffler condition 059E (4) on the inverse systems `(Hom_R (M_i, N))_i` gives the same
condition on `(Hom_S (M_i, N))_i`.

The route taken here is the same observation read off the intrinsic form. Surjectivity of `R → S`
says that `R → S` is an epimorphism of rings: the unit `X → S ⊗[R] X` of the base change is an
isomorphism for every `S`-module `X` (`unitBaseChange`). So a map `f : P → M` of `S`-modules is,
up to those isomorphisms, the base change `S ⊗[R] f_R` of its restriction of scalars, and the same
holds for the map `g : P → Q` of `R`-modules that the hypothesis produces once its target is
replaced by `S ⊗[R] Q`, a finitely presented `S`-module. Domination transfers because tensoring a
base change over `S` with an `S`-module `N` is tensoring over `R` with `N`:
`(S ⊗[R] X) ⊗[S] N ≃ X ⊗[R] N`, naturally in `X` (`ker_rTensor_baseChange_eq`). That natural
isomorphism is the intrinsic form of the source's `Hom_R (M_i, N) = Hom_S (M_i, N)`.

## Main results

* `Stacks.MittagLeffler.OverQuotientRing.solution`: an `S`-module is Mittag-Leffler over `R` if and
  only if it is Mittag-Leffler over `S`, for `S` a quotient of `R` by a finitely generated ideal.

## Implementation notes

The half of 0564 that is used is `Module.FinitePresentation.trans`: a finitely presented module
over `S` is finitely presented over `R`. It is applied to the module `P` of the `S`-side condition,
whose `R`-module structure is the restriction of scalars `Module.compHom P (algebraMap R S)`.

The base change `S ⊗[R] Q` lives in a universe larger than `Type v`, where the quantifiers of both
conditions sit, and is shrunk back into it; it is `v`-small because it is a finite module over the
`v`-small ring `R`, so `Shrink` and `Shrink.linearEquiv` move it into `Type v` without changing the
mathematics.

## References

* [StacksProject 05CR](https://stacks.math.columbia.edu/tag/05CR)
* [StacksProject 05CQ](https://stacks.math.columbia.edu/tag/05CQ)
* [StacksProject 059E](https://stacks.math.columbia.edu/tag/059E)
* [StacksProject 0564](https://stacks.math.columbia.edu/tag/0564)
-/

namespace Stacks.MittagLeffler.OverQuotientRing



open TensorProduct

/-- The unit `x ↦ 1 ⊗ x` of the base change along a *surjective* ring map `R → S` is an
isomorphism on every `S`-module: a surjection of rings is an epimorphism, so `S ⊗[R] -` is the
identity functor on `S`-modules. -/
private noncomputable def unitBaseChange {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    [Algebra R S] (hRS : Function.Surjective (algebraMap R S)) (X : Type*) [AddCommGroup X]
    [Module R X] [Module S X] [IsScalarTower R S X] : X ≃ₗ[S] S ⊗[R] X :=
  LinearEquiv.ofBijective (LinearMap.extendScalarsOfSurjective hRS (TensorProduct.mk R S X 1))
    ⟨Function.LeftInverse.injective
      (g := LinearMap.liftBaseChange S (LinearMap.id : X →ₗ[R] X)) fun x => by simp,
      TensorProduct.mk_surjective R X S hRS⟩

private theorem unitBaseChange_apply {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    [Algebra R S] (hRS : Function.Surjective (algebraMap R S)) (X : Type*) [AddCommGroup X]
    [Module R X] [Module S X] [IsScalarTower R S X] (x : X) :
    unitBaseChange hRS X x = 1 ⊗ₜ[R] x :=
  rfl

attribute [local simp] unitBaseChange_apply

/-- Tensoring an isomorphism with a fixed module is injective. -/
private theorem ker_rTensor_toLinearMap_eq_bot {S : Type w} [CommRing S] {C D : Type*}
    [AddCommGroup C] [Module S C] [AddCommGroup D] [Module S D] (θ : C ≃ₗ[S] D) (N : Type*)
    [AddCommGroup N] [Module S N] : LinearMap.ker (θ.toLinearMap.rTensor N) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  refine Function.LeftInverse.injective (g := θ.symm.toLinearMap.rTensor N) fun x => ?_
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  simp

/-- Two maps that agree up to isomorphisms of their source and target have, after tensoring with
`N`, kernels that correspond under the isomorphism of the sources. -/
private theorem ker_rTensor_eq_comap {S : Type w} [CommRing S] {A B C D : Type*} [AddCommGroup A]
    [Module S A] [AddCommGroup B] [Module S B] [AddCommGroup C] [Module S C] [AddCommGroup D]
    [Module S D] (e : A ≃ₗ[S] B) (θ : C ≃ₗ[S] D) (u : A →ₗ[S] C) (v : B →ₗ[S] D)
    (h : θ.toLinearMap ∘ₗ u = v ∘ₗ e.toLinearMap) (N : Type*) [AddCommGroup N] [Module S N] :
    LinearMap.ker (u.rTensor N) =
      Submodule.comap (e.toLinearMap.rTensor N) (LinearMap.ker (v.rTensor N)) := by
  have key : (θ.toLinearMap.rTensor N) ∘ₗ (u.rTensor N)
      = (v.rTensor N) ∘ₗ (e.toLinearMap.rTensor N) := by
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp, h]
  rw [← LinearMap.ker_comp, ← key, LinearMap.ker_comp, ker_rTensor_toLinearMap_eq_bot,
    Submodule.comap_bot]

/-- Tensoring the base change `S ⊗[R] X` with an `S`-module `N` over `S` is tensoring `X` with `N`
over `R`, naturally in `X`: the isomorphism `(S ⊗[R] X) ⊗[S] N ≃ X ⊗[R] N` carries
`(S ⊗[R] h) ⊗ id_N` to `h ⊗ id_N`. This is the intrinsic form of the identification
`Hom_R (X, N) = Hom_S (S ⊗[R] X, N)`. -/
private theorem rTensor_baseChange_comm_cancelBaseChange {R : Type u} {S : Type w} [CommRing R]
    [CommRing S] [Algebra R S] {X Y : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
    [Module R Y] {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (h : X →ₗ[R] Y) (z : (S ⊗[R] X) ⊗[S] N) :
    (TensorProduct.comm R N Y) (AlgebraTensorModule.cancelBaseChange R S S N Y
        (TensorProduct.comm S (S ⊗[R] Y) N ((h.baseChange S).rTensor N z)))
      = h.rTensor N ((TensorProduct.comm R N X) (AlgebraTensorModule.cancelBaseChange R S S N X
        (TensorProduct.comm S (S ⊗[R] X) N z))) := by
  induction z using TensorProduct.inductionOn with
  | tmul a n =>
      induction a using TensorProduct.inductionOn with
      | tmul s x => simp
      | add a b ha hb => simp only [add_tmul, map_add, ha, hb]
  | add a b ha hb => simp [ha, hb]

/-- The isomorphism `(S ⊗[R] X) ⊗[S] N ≃ X ⊗[R] N` detects zero. -/
private theorem comm_cancelBaseChange_eq_zero_iff {R : Type u} {S : Type w} [CommRing R]
    [CommRing S] [Algebra R S] {X : Type*} [AddCommGroup X] [Module R X] {N : Type*}
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (z : (S ⊗[R] X) ⊗[S] N) :
    (TensorProduct.comm R N X) (AlgebraTensorModule.cancelBaseChange R S S N X
        (TensorProduct.comm S (S ⊗[R] X) N z)) = 0 ↔ z = 0 := by
  rw [LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff, LinearEquiv.map_eq_zero_iff]

/-- Domination of maps of `R`-modules, tested against an `S`-module `N`, is domination of their
base changes to `S`, tested against `N` over `S`. -/
private theorem ker_rTensor_baseChange_eq {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    [Algebra R S] {X Y Z : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] (h₁ : X →ₗ[R] Y) (h₂ : X →ₗ[R] Z) (N : Type*) [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N]
    (hker : LinearMap.ker (h₁.rTensor N) = LinearMap.ker (h₂.rTensor N)) :
    LinearMap.ker ((h₁.baseChange S).rTensor N) = LinearMap.ker ((h₂.baseChange S).rTensor N) := by
  refine Submodule.ext fun z => ?_
  simp only [LinearMap.mem_ker]
  rw [← comm_cancelBaseChange_eq_zero_iff (S := S) ((h₁.baseChange S).rTensor N z),
    ← comm_cancelBaseChange_eq_zero_iff (S := S) ((h₂.baseChange S).rTensor N z),
    rTensor_baseChange_comm_cancelBaseChange h₁ z, rTensor_baseChange_comm_cancelBaseChange h₂ z]
  simpa only [LinearMap.mem_ker] using SetLike.ext_iff.mp hker _

/-- Let `R → S` be surjective with `S` finitely presented as an `R`-module, and let `M` be an
`S`-module. Then `M` is Mittag-Leffler over `R` if and only if it is Mittag-Leffler over `S`: every
map from a finitely presented module to `M` is dominated by a map to a finitely presented module,
over `R` exactly when over `S`. -/
public theorem solution {R : Type u} {S : Type w}
    {M : Type v} [CommRing R] [CommRing S] [Algebra R S] [Small.{v} R]
    [Module.FinitePresentation R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (hRS : Function.Surjective (algebraMap R S)) :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ (P : Type v) [AddCommGroup P] [Module S P] [Module.FinitePresentation S P]
        (f : P →ₗ[S] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module S Q)
          (_ : Module.FinitePresentation S Q) (g : P →ₗ[S] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module S N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  refine ⟨fun hM => ?_, fun hM => Module.mittagLeffler_trans hM⟩
  intro P _ _ _ f
  -- `P` is finitely presented over `R` as well, by 0564.
  let _ : Module R P := Module.compHom P (algebraMap R S)
  have : IsScalarTower R S P := IsScalarTower.of_algebraMap_smul fun r x => rfl
  have : Module.FinitePresentation R P := Module.FinitePresentation.trans R P S
  -- Feed the restriction of scalars of `f` to the Mittag-Leffler condition over `R`.
  obtain ⟨Q, _, _, _, g, hker⟩ := hM P (f.restrictScalars R)
  have : Small.{v} S := small_of_surjective hRS
  have : Small.{v} (S ⊗[R] Q) := Module.Finite.small R (S ⊗[R] Q)
  let eP := unitBaseChange hRS P
  let sh := Shrink.linearEquiv S (S ⊗[R] Q)
  -- The base change of `Q`, shrunk into `Type v`, is the finitely presented `S`-module wanted.
  refine ⟨Shrink.{v} (S ⊗[R] Q), inferInstance, inferInstance,
    (LinearEquiv.finitePresentation_iff (Shrink.linearEquiv S (S ⊗[R] Q))).mpr inferInstance,
    sh.symm.toLinearMap ∘ₗ (g.baseChange S) ∘ₗ eP.toLinearMap, fun N _ _ => ?_⟩
  let _ : Module R N := Module.compHom N (algebraMap R S)
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun r x => rfl
  -- Both maps are, up to isomorphism, base changes of maps of `R`-modules.
  have hf : (unitBaseChange hRS M).toLinearMap ∘ₗ f
      = ((f.restrictScalars R).baseChange S) ∘ₗ eP.toLinearMap := by
    ext p
    simp [eP]
  have hg : sh.toLinearMap ∘ₗ (sh.symm.toLinearMap ∘ₗ (g.baseChange S) ∘ₗ eP.toLinearMap)
      = (g.baseChange S) ∘ₗ eP.toLinearMap := by
    ext p
    simp [sh]
  -- So their dominations are the domination of `f.restrictScalars R` and `g`.
  rw [ker_rTensor_eq_comap eP (unitBaseChange hRS M) f _ hf N,
    ker_rTensor_eq_comap eP sh _ _ hg N,
    ker_rTensor_baseChange_eq (f.restrictScalars R) g N (hker N)]

end Stacks.MittagLeffler.OverQuotientRing

/-!
# Mittag-Leffler modules over a quotient ring

An `R`-module `M` is *Mittag-Leffler* (Definition 059F) when the equivalent conditions of
Proposition 059E hold for it. Only one of those five conditions is intrinsic to `M`, namely
condition (1), and it is the one used here: for every finitely presented `R`-module `P` and every
module map `f : P → M` there are a finitely presented `R`-module `Q` and a module map `g : P → Q`
such that `f` and `g` dominate each other, i.e. `Ker (f ⊗ id_N) = Ker (g ⊗ id_N)` for every
`R`-module `N`.

The Mittag-Leffler condition sees the base ring, so it is a genuine question how it behaves along a
ring map `R → S`. This file states Stacks 05CR: for a *surjective* `R → S` with finitely generated
kernel — that is, for `S = R/I` with `I` a finitely generated ideal — an `S`-module `M` is
Mittag-Leffler over `R` if and only if it is Mittag-Leffler over `S`. One implication is
Lemma 05CQ, which needs no surjectivity. For the other, the source writes `M = colim M i` as a
directed colimit of finitely presented `S`-modules; since `I` is finitely generated, `S` is finite
and finitely presented over `R`, so the `M i` are finitely presented as `R`-modules (Lemma 0564);
and since `R → S` is surjective, `Hom_R (M i, N) = Hom_S (M i, N)` for every `S`-module `N`, so the
Mittag-Leffler condition 059E (4) on the inverse systems `(Hom_R (M i, N)) i` gives the same
condition on `(Hom_S (M i, N)) i`, which is Mittag-Leffler over `S`.

Surjectivity is what makes this an equivalence rather than the one-way implication 05CQ: by
Remark 05CS a module over the ring of dual numbers `S = R ⊕ Rε`, a finite and finitely presented
`R`-algebra, may be Mittag-Leffler over `R` without being Mittag-Leffler over `S`.

## Main results

* `Module.mittagLeffler_restrictScalars_iff_of_surjective`: for `S` a quotient of `R` by a finitely
  generated ideal and `M` an `S`-module, `M` is Mittag-Leffler over `R` if and only if it is
  Mittag-Leffler over `S`.

## Implementation notes

Neither Mathlib nor this project has a predicate for a Mittag-Leffler module — Mathlib's
`CategoryTheory.Functor.IsMittagLeffler` is the Mittag-Leffler condition on an inverse *system*,
and 059F has no Lean form yet — so the condition is spelled out inline on both sides of the
equivalence, in the intrinsic form 059E (1), the two sides differing only in the ring, exactly as
in the companion statements 05CQ (`Module.mittagLeffler_trans`) and 05CN
(`Module.mittagLeffler_tensorProduct`). Mutual domination is spelled out as equality of the kernels
of the tensored maps, `f ⊗ id_N` being `f.rTensor N`, as in 059D
(`LinearMap.forall_ker_rTensor_le_iff_exists_eq_comp`).

The source's `S = R/I` with `I` a finitely generated ideal is stated abstractly, as an `R`-algebra
`S` whose structure map is surjective and which is finitely presented as an `R`-module. This is the
same hypothesis: for a surjection `R → S` with kernel `I` the module `S ≅ R/I` is finitely
presented over `R` precisely when `I` is finitely generated, and conversely every quotient `R/I`
is such an algebra. It costs no generality and it is the form the two ingredients consume —
Lemma 0564 (`Module.FinitePresentation.trans`) and Lemma 05CQ take `Module.FinitePresentation R S`,
and the identification `Hom_R (P, N) = Hom_S (P, N)` is Mathlib's
`LinearMap.extendScalarsOfSurjectiveEquiv`, which takes exactly `hRS`. Finiteness of `S` over `R`,
which the source also asks for, is automatic here, being implied by finite presentation.

The modules `M` and the quantified `P`, `Q`, `N` all live in one universe `Type v` and `R` is
`v`-small, as in 059D, 05CQ and 05CN. For a `v`-small `R` every finitely presented `R`-module is
isomorphic to one in `Type v`, so the left-hand quantifiers are the source's quantifiers over all
finitely presented `R`-modules and all test `R`-modules; the same holds on the right, `S` being
`v`-small as a quotient of `R`, so smallness of `S` is not assumed.

Faithfulness. (1) No hypothesis is dead: `Module.FinitePresentation R S` is what makes the `M i`
finitely presented over `R` and is used in both directions (it is 05CQ's hypothesis), while
surjectivity of `algebraMap R S` is what makes the left-to-right implication true at all, 05CS
exhibiting a finite and finitely presented `R`-algebra and a module over it that is Mittag-Leffler
over `R` but not over `S`; `Small.{v} R` is what makes the quantifiers over `P, Q, N : Type v` the
source's quantifiers over all modules; and `IsScalarTower R S M` is what makes the two conditions
conditions on one module. (2) The scalars and the base are the source's: the left-hand condition
quantifies over `R`-modules and `R`-linear maps and tensors over `R`, the right-hand one over
`S`-modules and `S`-linear maps and tensors over `S`, and the `R`-module structure on `M` is the
one restricted from `S` along the tower. (3) The source names no canonical map: `Q` and `g` are
existentially quantified in 059E (1) itself, and what is canonical is pinned — the maps whose
kernels are compared are `f.rTensor N` and `g.rTensor N`, not arbitrary maps `P ⊗ N → M ⊗ N` and
`P ⊗ N → Q ⊗ N`. (4) The instantiation is not degenerate: take `R = ℤ[X]` and `S = ℤ = R/(X)`,
whose defining ideal `(X)` is finitely generated and nonzero, so that the two rings really differ;
for `M = S` both sides hold, `S` being finitely presented over `S` and over `R`, while for `M = ℚ`
both fail, `ℚ` not being Mittag-Leffler over `ℤ` (flat and countably generated but not projective,
Theorem 059Z) and hence, by the equivalence, not over `ℤ[X]` either.

## References

* [StacksProject 05CR](https://stacks.math.columbia.edu/tag/05CR)
-/



@[expose] public section

/-- **Stacks 05CR.** Let `R` be a ring and let `S = R/I` for a finitely generated ideal `I`,
presented here as an `R`-algebra with surjective structure map which is finitely presented as an
`R`-module. Let `M` be an `S`-module. Then `M` is a Mittag-Leffler module over `R` if and only if
`M` is a Mittag-Leffler module over `S`. The Mittag-Leffler condition is spelled out in the
intrinsic form 059E (1): every map `f` from a finitely presented module into `M` dominates and is
dominated by a map `g` into a finitely presented module, domination meaning equality of the kernels
of the maps `· ⊗ id_N`. -/
@[stacks 05CR "Mittag-Leffler is spelled out inline as condition (1) of 059E; `S = R/I` with `I`
finitely generated is spelled abstractly as a surjective `algebraMap R S` with `S` finitely
presented as an `R`-module."]
public theorem Module.mittagLeffler_restrictScalars_iff_of_surjective {R : Type u} {S : Type w}
    {M : Type v} [CommRing R] [CommRing S] [Algebra R S] [Small.{v} R]
    [Module.FinitePresentation R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (hRS : Function.Surjective (algebraMap R S)) :
    (∀ (P : Type v) [AddCommGroup P] [Module R P] [Module.FinitePresentation R P]
      (f : P →ₗ[R] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q)
        (_ : Module.FinitePresentation R Q) (g : P →ₗ[R] Q), ∀ (N : Type v) [AddCommGroup N]
          [Module R N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N)) ↔
      ∀ (P : Type v) [AddCommGroup P] [Module S P] [Module.FinitePresentation S P]
        (f : P →ₗ[S] M), ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module S Q)
          (_ : Module.FinitePresentation S Q) (g : P →ₗ[S] Q), ∀ (N : Type v) [AddCommGroup N]
            [Module S N], LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) :=
  Stacks.MittagLeffler.OverQuotientRing.solution hRS

end
