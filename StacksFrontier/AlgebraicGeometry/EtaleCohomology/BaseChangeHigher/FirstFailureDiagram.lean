module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.FirstFailureFieldObstruction
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralBaseCriterion
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCoverCriterion
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageCyclicCoefficients
import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.AlgClosedField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normalized diagram at a first failure of étale base change

Let `f : X ⟶ S` be a morphism of schemes and `n` an integer, as in the condition `BC(f, n, q₀)`
of [Stacks, Tag 0F02]. Suppose `BC(f, n, q)` holds while `BC(f, n, q + 1)` fails. The source
produces a commutative diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  Spec K
```

with both squares cartesian, in which `S'` is affine, integral and normal with algebraically
closed function field, `K` is algebraically closed and `Spec K ⟶ S'` is dominant, and in which
`R^{q+1} h_*(ℤ/dℤ)` is nonzero for some `d ∣ n`. That is [Stacks, Tag 0F08].

The source's argument is a chain of improvements of one counterexample. [Stacks, Tag 0F07]
replaces an arbitrary base for the sheaf by the spectrum of a field; [Stacks, Tag 0F04], applied
to the integral surjective morphism `Spec K̄ ⟶ Spec K`, replaces that field by an algebraic
closure; over an algebraically closed field an `n`-torsion abelian étale sheaf is a
`ℤ/nℤ`-module, hence a direct sum of copies of `ℤ/dℤ` for divisors `d` of `n`, so the sheaf may
be taken constant; and [Stacks, Tag 0F05], applied to the normalization of `S'` in `Spec K̄`,
replaces `S'` by an affine integral normal scheme with algebraically closed function field over
which `K̄` is still dominant. Only then does the nonvanishing of `R^{q+1} h_*(ℤ/dℤ)` follow, from
the failure of base change together with injectivity of the base change map, which is part (1)
of [Stacks, Tag 0F03].

This file formalizes the chain and proves [Stacks, Tag 0F08] as
`normalFailureDiagram_of_not_baseChangeHolds`. Each step is a theorem:
[Stacks, Tag 0F07] is `Stacks.EtaleCohomology.exists_affine_field_not_isIso_higherBaseChangeMapAb`,
[Stacks, Tag 0F04] is
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_integralSurjective`, the normalization
of an affine scheme in the spectrum of an algebraically closed field is
`AlgebraicGeometry.exists_normalization_of_isAlgClosed`, [Stacks, Tag 0F05] is
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff_of_isIntegralHom`, part (1) of
[Stacks, Tag 0F03] is `Stacks.EtaleCohomology.mono_higherBaseChangeMapAb_app_of_annihilated`, and
the reduction to the constant coefficients `ℤ/dℤ` is
`Stacks.EtaleCohomology.isZero_rightDerived_pullback_of_forall_zmod`. As in the source's proof,
the base is normalized before the coefficients are made constant: once `R^{q+1} h_* e⁻¹F` is known
to be nonzero, the cyclic decomposition gives a divisor `d` with `R^{q+1} h_* e⁻¹(ℤ/dℤ)` nonzero.

## Main definitions

* `Stacks.EtaleCohomology.FirstFailureDiagram.constantZMod` — the constant abelian sheaf `ℤ/dℤ`
  on the small étale site of a scheme.
* `Stacks.EtaleCohomology.FirstFailureDiagram.FailureOver` — a failure of the base change map of
  [Stacks, Tag 0F02] in a fixed degree, over an arbitrary quasi-compact quasi-separated base for
  the sheaf.
* `Stacks.EtaleCohomology.FirstFailureDiagram.FieldFailure`,
  `Stacks.EtaleCohomology.FirstFailureDiagram.AlgClosedFailure`,
  `Stacks.EtaleCohomology.FirstFailureDiagram.ConstantFailure`,
  `Stacks.EtaleCohomology.FirstFailureDiagram.NormalConstantFailure` — the same failure with the
  base of the sheaf the spectrum of a field, of an algebraically closed field, with the sheaf
  constant with value `ℤ/dℤ` for some `d ∣ n`, and with `S'` affine integral normal with
  algebraically closed function field and `Spec K ⟶ S'` dominant. These are the four successive
  improvements of the source's counterexample.
* `Stacks.EtaleCohomology.FirstFailureDiagram.NormalFailureDiagram` — the conclusion of
  [Stacks, Tag 0F08]: the normalized diagram together with the nonvanishing of
  `R^{q+1} h_*(ℤ/dℤ)`.

## Main results

* `Stacks.EtaleCohomology.FirstFailureDiagram.isIso_of_mono_of_isZero` and
  `Stacks.EtaleCohomology.FirstFailureDiagram.not_isZero_of_mono_of_not_isIso` — a monomorphism
  into a zero object is an isomorphism, so a monomorphism that is not an isomorphism has a
  nonzero target. This is what converts a failure of base change into a nonvanishing statement.
* `Stacks.EtaleCohomology.FirstFailureDiagram.zsmul_constantZMod_eq_zero` — every section of
  the constant sheaf `ℤ/dℤ` is annihilated by any multiple of `d`. This discharges the torsion
  hypothesis of part (1) of [Stacks, Tag 0F03] at the sheaf the chain of improvements ends with.
* `Stacks.EtaleCohomology.FirstFailureDiagram.failureOver_of_not_baseChangeHolds` — a first
  failure of base change is a failure in degree exactly `q + 1`: `BC(f, n, q + 1)` fails in a
  single degree, and `BC(f, n, q)` forces that degree to be `q + 1`.
* `Stacks.EtaleCohomology.FirstFailureDiagram.normalFailureDiagram_of_normalConstantFailure` —
  the last step of the source's proof: the normalized counterexample forces
  `R^{q+1} h_*(ℤ/dℤ)` to be nonzero, given injectivity of the base change map.
* `Stacks.EtaleCohomology.FirstFailureDiagram.normalFailureDiagram_of_isAlgClosed` — the
  normalized diagram from a failure of base change over an algebraically closed field: the base
  is replaced by its normalization in `Spec K` ([Stacks, Tag 0F05]), the base change map is
  injective (part (1) of [Stacks, Tag 0F03]), and the coefficients are made constant.
* `Stacks.EtaleCohomology.FirstFailureDiagram.normalFailureDiagram_of_not_baseChangeHolds` —
  **[Stacks, Tag 0F08]**.

## Implementation notes

Degrees are indexed as elsewhere in this development: the running index is `q : ℕ`, the standing
hypothesis is `BC(f, n, q)` and the conclusion concerns degree `q + 1`. That is the source's
`q ≥ 1` together with its `BC(f, n, q - 1)`, written so that no subtraction on `ℤ` has to be
moved across the argument of `Stacks.EtaleCohomology.BaseChangeHolds`.

The source's `S'` is required to be affine, integral and normal with algebraically closed
function field. Affineness and integrality are Mathlib's `AlgebraicGeometry.IsAffine` and
`AlgebraicGeometry.IsIntegral`; normality of an integral affine scheme is normality of its ring
of global sections, which is `IsNormalDomain` of [Stacks, Tag 0309]; and the function field is
Mathlib's `AlgebraicGeometry.Scheme.functionField`, the stalk at the generic point, a field
because `S'` is integral.

The sheaf `ℤ/dℤ` of the source lives on `Y`; here it is the inverse image along `e` of the
constant sheaf `ℤ/dℤ` on `Spec K`, which is the shape the base change map of
[Stacks, Tag 0F02] takes its sheaves in. The value group is `ULift (ZMod d)`, the sections of an
étale sheaf in this development living one universe above the schemes.

Quasi-compactness and quasi-separatedness of `g : Spec K ⟶ S'`, which the diagrams of
[Stacks, Tag 0F02] require, are not carried in the predicates with a field base: they are
automatic, the spectrum of a field being compact and quasi-separated. They are carried in
`FailureOver`, whose base is arbitrary.

The torsion hypothesis that part (1) of [Stacks, Tag 0F03] needs is discharged, not assumed:
`zsmul_constantZMod_eq_zero` proves that every section of the constant sheaf `ℤ/dℤ` is
annihilated by `n` whenever `d ∣ n`. It is a statement about the sections of a sheafification,
and it is proved without describing them, by evaluating the endomorphism `n • 𝟙` of the sheaf,
which vanishes because the constant sheaf functor is additive and `n • 𝟙` already vanishes on
the value group.

## References

* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
* [Stacks Project, Tag 0F07](https://stacks.math.columbia.edu/tag/0F07)
* [Stacks Project, Tag 0F05](https://stacks.math.columbia.edu/tag/0F05)
* [Stacks Project, Tag 0F04](https://stacks.math.columbia.edu/tag/0F04)
* [Stacks Project, Tag 0F03](https://stacks.math.columbia.edu/tag/0F03)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.FirstFailureDiagram

/-- **A monomorphism into a zero object is an isomorphism.** Every morphism out of a zero
object is determined by its source, so a morphism into a zero object is epi; in a balanced
category a morphism that is both mono and epi is invertible. -/
public theorem isIso_of_mono_of_isZero {C : Type*} [Category* C] [Balanced C] {A B : C}
    (φ : A ⟶ B) [Mono φ] (hB : IsZero B) : IsIso φ :=
  have := hB.epi φ
  isIso_of_mono_of_epi φ

/-- **A monomorphism that is not an isomorphism has a nonzero target.** The contrapositive of
`isIso_of_mono_of_isZero`; this is what turns a failure of an injective base change map into a
nonvanishing statement about the higher direct image it maps into. -/
public theorem not_isZero_of_mono_of_not_isIso {C : Type*} [Category* C] [Balanced C] {A B : C}
    (φ : A ⟶ B) [Mono φ] (hφ : ¬ IsIso φ) : ¬ IsZero B :=
  fun hB => hφ (isIso_of_mono_of_isZero φ hB)

/-- **The constant abelian sheaf `ℤ/dℤ` on the small étale site of a scheme**: the sheafification
of the constant presheaf with value `ℤ/dℤ`, the value group lifted into the universe the sections
of an étale sheaf live in. -/
@[sga "7 XXII 2.0"]
public def constantZMod (Z : Scheme.{u}) (d : ℕ) : Sheaf (smallEtaleTopology Z) Ab.{u + 1} :=
  (constantSheaf (smallEtaleTopology Z) Ab.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod d)))

/-- **Every section of the constant sheaf `ℤ/dℤ` is annihilated by any multiple of `d`.**
Multiplication by `n` is zero on the value group `ℤ/dℤ` because `d ∣ n`; the constant sheaf
functor is additive, being the constant presheaf functor followed by sheafification, so it
carries that zero endomorphism to the endomorphism `n • 𝟙` of `constantZMod T d`, which is
therefore zero as well. Evaluating that vanishing endomorphism at an object of the small étale
site gives the statement on sections, no description of the sheafification being needed. -/
public theorem zsmul_constantZMod_eq_zero (T : Scheme.{u}) (d : ℕ) {n : ℤ} (hd : (d : ℤ) ∣ n)
    (U : T.Etale) (x : (constantZMod T d).obj.obj (op U)) : n • x = 0 := by
  have hM : n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))) = 0 := by
    obtain ⟨k, rfl⟩ := hd
    ext y
    simp
  have hF : n • 𝟙 (constantZMod T d) = 0 := by
    have h := congrArg (constantSheaf (smallEtaleTopology T) Ab.{u + 1}).map hM
    rwa [Functor.map_zsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
  have happ : n • 𝟙 ((constantZMod T d).obj.obj (op U)) = 0 :=
    congrArg (fun φ : constantZMod T d ⟶ constantZMod T d => φ.hom.app (op U)) hF
  simpa using congrArg (fun ψ => ψ x) happ

/-- **A failure of étale base change in degree `r` over an arbitrary base.** There are a
commutative diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  T
```

with both squares cartesian and `g` quasi-compact and quasi-separated, and an abelian sheaf `F`
on the small étale site of `T` annihilated by `n`, whose base change map
`(f')⁻¹ R^r g_* F ⟶ R^r h_* e⁻¹ F` is not an isomorphism. This is the negation of the degree-`r`
clause of `Stacks.EtaleCohomology.BaseChangeHolds`. -/
public def FailureOver {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (r : ℕ) : Prop :=
  ∃ (S' X' T Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_hp : IsPullback p f' f s) (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    (sq : IsPullback h e f' g) (_ : QuasiCompact g) (_ : QuasiSeparated g)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}),
    (∀ (U : T.Etale) (x : F.obj.obj (op U)), n • x = 0) ∧
      ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w r).app F)

/-- **A failure of étale base change in degree `r` over the spectrum of a field.** The base `T`
of `FailureOver` is `Spec K` for a field `K`. This is the conclusion of [Stacks, Tag 0F07]. -/
public def FieldFailure {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (r : ℕ) : Prop :=
  ∃ (S' X' Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_hp : IsPullback p f' f s) (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ S')
    (h : Y ⟶ X') (e : Y ⟶ Spec (.of K)) (sq : IsPullback h e f' g)
    (F : Sheaf (smallEtaleTopology (Spec (.of K))) Ab.{u + 1}),
    (∀ (U : (Spec (.of K)).Etale) (x : F.obj.obj (op U)), n • x = 0) ∧
      ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w r).app F)

/-- **A failure of étale base change in degree `r` over the spectrum of an algebraically closed
field.** The improvement of `FieldFailure` obtained from [Stacks, Tag 0F04] applied to the
integral surjective morphism `Spec K̄ ⟶ Spec K`. -/
public def AlgClosedFailure {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (r : ℕ) : Prop :=
  ∃ (S' X' Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_hp : IsPullback p f' f s) (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
    (g : Spec (.of K) ⟶ S') (h : Y ⟶ X') (e : Y ⟶ Spec (.of K))
    (sq : IsPullback h e f' g) (F : Sheaf (smallEtaleTopology (Spec (.of K))) Ab.{u + 1}),
    (∀ (U : (Spec (.of K)).Etale) (x : F.obj.obj (op U)), n • x = 0) ∧
      ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w r).app F)

/-- **A failure of étale base change in degree `r` with constant coefficients.** The improvement
of `AlgClosedFailure` in which the sheaf is the constant sheaf `ℤ/dℤ` for a divisor `d` of `n`:
over an algebraically closed field an abelian étale sheaf annihilated by `n` is a `ℤ/nℤ`-module,
so a direct sum of copies of such `ℤ/dℤ`, and the failure is visible on one summand. -/
public def ConstantFailure {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (r : ℕ) : Prop :=
  ∃ (S' X' Y : Scheme.{u}) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_hp : IsPullback p f' f s) (K : Type u) (_ : Field K) (_ : IsAlgClosed K)
    (g : Spec (.of K) ⟶ S') (h : Y ⟶ X') (e : Y ⟶ Spec (.of K))
    (sq : IsPullback h e f' g) (d : ℕ) (_ : (d : ℤ) ∣ n),
    ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w r).app (constantZMod (Spec (.of K)) d))

/-- **A failure of étale base change in degree `r` over a normalized base.** The improvement of
`ConstantFailure` in which `S'` is affine, integral and normal with algebraically closed function
field and `Spec K ⟶ S'` is dominant, obtained in the source by replacing `S'` by its
normalization in `Spec K` and invoking [Stacks, Tag 0F05]. Normality of the integral affine `S'`
is normality of its ring of global sections. -/
public def NormalConstantFailure {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (r : ℕ) : Prop :=
  ∃ (S' X' Y : Scheme.{u}) (_ : IsAffine S') (_ : IsIntegral S')
    (_ : IsNormalDomain Γ(S', ⊤)) (_ : IsAlgClosed S'.functionField)
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (_hp : IsPullback p f' f s)
    (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (g : Spec (.of K) ⟶ S')
    (_ : IsDominant g) (h : Y ⟶ X') (e : Y ⟶ Spec (.of K)) (sq : IsPullback h e f' g)
    (d : ℕ) (_ : (d : ℤ) ∣ n),
    ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w r).app (constantZMod (Spec (.of K)) d))

/-- **The conclusion of [Stacks, Tag 0F08].** There are a commutative diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  Spec K
```

with both squares cartesian, in which `S'` is affine, integral and normal with algebraically
closed function field, `K` is algebraically closed and `g : Spec K ⟶ S'` is dominant, and an
integer `d ∣ n` for which `R^r h_*(ℤ/dℤ)` is nonzero, the sheaf `ℤ/dℤ` on `Y` being the inverse
image along `e` of the constant sheaf `ℤ/dℤ` on `Spec K`. -/
public def NormalFailureDiagram {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (r : ℕ) : Prop :=
  ∃ (S' X' Y : Scheme.{u}) (_ : IsAffine S') (_ : IsIntegral S')
    (_ : IsNormalDomain Γ(S', ⊤)) (_ : IsAlgClosed S'.functionField)
    (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S') (_hp : IsPullback p f' f s)
    (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (g : Spec (.of K) ⟶ S')
    (_ : IsDominant g) (h : Y ⟶ X') (e : Y ⟶ Spec (.of K)) (_sq : IsPullback h e f' g)
    (d : ℕ) (_ : (d : ℤ) ∣ n),
    ¬ IsZero (((smallEtalePushforwardAb h).rightDerived r).obj
      ((smallEtalePullbackAb e).obj (constantZMod (Spec (.of K)) d)))

/-- **A first failure of étale base change is a failure in degree exactly `q + 1`.** If
`BC(f, n, q)` holds and `BC(f, n, q + 1)` fails, then some diagram of two cartesian squares with
quasi-compact quasi-separated `g` and some abelian sheaf annihilated by `n` have a base change
map in degree `q + 1` that is not an isomorphism: the failure of `BC(f, n, q + 1)` is a failure
in a single degree, and `BC(f, n, q)` forces that degree to be `q + 1`. This is the opening of
the source's proof of [Stacks, Tag 0F07], and the entry point of the chain of improvements
leading to [Stacks, Tag 0F08]. -/
public theorem failureOver_of_not_baseChangeHolds {X S : Scheme.{u}} (f : X ⟶ S) (n : ℤ)
    (q : ℕ) (hprev : BaseChangeHolds f n (q : ℤ))
    (hfail : ¬ BaseChangeHolds f n ((q : ℤ) + 1)) :
    FailureOver f n (q + 1) := by
  by_contra hcon
  refine hfail ?_
  intro S' X' T Y s p f' hp g h e sq hqc hqs F hF q' hq'
  rcases le_or_gt (q' : ℤ) (q : ℤ) with hle | hgt
  · exact hprev s p f' hp g h e sq F hF q' hle
  · obtain rfl : q' = q + 1 := by omega
    by_contra hni
    exact hcon ⟨S', X', T, Y, s, p, f', hp, g, h, e, sq, hqc, hqs, F, hF, hni⟩

/-- **The last step of the source's proof of [Stacks, Tag 0F08].** Given the normalized
counterexample `NormalConstantFailure` the chain of improvements ends with, and granted part (1)
of [Stacks, Tag 0F03] — injectivity of the base change map in degree `r` for an `n`-torsion
sheaf over a field-valued base, which in the source follows from `BC(f, n, r - 1)` — the higher
direct image `R^r h_*(ℤ/dℤ)` is nonzero. Indeed the base change map into it is injective and not
invertible, and a monomorphism into a zero object is invertible. -/
public theorem normalFailureDiagram_of_normalConstantFailure {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℤ) (r : ℕ)
    (h0F03 : ∀ {S' X' Y : Scheme.{u}} (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
      (_hp : IsPullback p f' f s) (K : Type u) (_ : Field K) (g : Spec (.of K) ⟶ S')
      (h : Y ⟶ X') (e : Y ⟶ Spec (.of K)) (sq : IsPullback h e f' g)
      (F : Sheaf (smallEtaleTopology (Spec (.of K))) Ab.{u + 1}),
      (∀ (U : (Spec (.of K)).Etale) (x : F.obj.obj (op U)), n • x = 0) →
        Mono ((higherBaseChangeMapAb f' g h e sq.w r).app F))
    (hfail : NormalConstantFailure f n r) :
    NormalFailureDiagram f n r := by
  obtain ⟨S', X', Y, haff, hint, hnorm, hfun, s, p, f', hp, K, hK, hKcl, g, hdom, h, e, sq,
    d, hd, hni⟩ := hfail
  have : Mono ((higherBaseChangeMapAb f' g h e sq.w r).app
      (constantZMod (Spec (.of K)) d)) :=
    h0F03 s p f' hp K hK g h e sq (constantZMod (Spec (.of K)) d)
      (zsmul_constantZMod_eq_zero (Spec (.of K)) d hd)
  exact ⟨S', X', Y, haff, hint, hnorm, hfun, s, p, f', hp, K, hK, hKcl, g, hdom, h, e, sq,
    d, hd, not_isZero_of_mono_of_not_isIso _ hni⟩

/-- **The normalized diagram from a failure of base change over an algebraically closed field.**
With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], assume `BC(f, n, q)`, and let

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  Spec K
```

be a diagram of two cartesian squares with `S'` affine and `K` algebraically closed, together
with an abelian sheaf `F` on `Spec K` annihilated by `n` whose base change map in degree `q + 1`
is not an isomorphism. Then the normalized diagram of `NormalFailureDiagram` exists in degree
`q + 1`.

The base `S'` is replaced by the normalization `S''` of `S'` in `Spec K`
(`AlgebraicGeometry.exists_normalization_of_isAlgClosed`), over which the failure persists by
[Stacks, Tag 0F05] (`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff_of_isIntegralHom`);
the base change map is then injective by part (1) of [Stacks, Tag 0F03]
(`Stacks.EtaleCohomology.mono_higherBaseChangeMapAb_app_of_annihilated`) and not invertible, so
`R^{q+1} h_* e⁻¹F ≠ 0`; and over the algebraically closed `K` the sheaf `F` is built from the
constant sheaves `ℤ/dℤ`, `d ∣ n`, so one of them has `R^{q+1} h_* e⁻¹(ℤ/dℤ) ≠ 0`
(`Stacks.EtaleCohomology.isZero_rightDerived_pullback_of_forall_zmod`). -/
public theorem normalFailureDiagram_of_isAlgClosed {X S S' X' Y : Scheme.{u}} (f : X ⟶ S)
    (n : ℤ) (q : ℕ) (hprev : BaseChangeHolds f n (q : ℤ)) [IsAffine S'] (s : S' ⟶ S)
    (p : X' ⟶ X) (f' : X' ⟶ S') (hp : IsPullback p f' f s) (K : Type u) [Field K]
    [IsAlgClosed K] (g : Spec (.of K) ⟶ S') (h : Y ⟶ X') (e : Y ⟶ Spec (.of K))
    (sq : IsPullback h e f' g) (F : Sheaf (smallEtaleTopology (Spec (.of K))) Ab.{u + 1})
    (hF : ∀ (U : (Spec (.of K)).Etale) (x : F.obj.obj (op U)), n • x = 0)
    (hfail : ¬ IsIso ((higherBaseChangeMapAb f' g h e sq.w (q + 1)).app F)) :
    NormalFailureDiagram f n (q + 1) := by
  -- Step 1 ([Stacks, Tag 0F05]): replace `S'` by the normalization of `S'` in `Spec K`.
  obtain ⟨S'', hS''a, hS''i, hS''n, hS''f, π₂, hπ₂, g'', hg'', rfl⟩ :=
    exists_normalization_of_isAlgClosed K g
  let π₂' : pullback f' π₂ ⟶ X' := pullback.fst f' π₂
  let f'' : pullback f' π₂ ⟶ S'' := pullback.snd f' π₂
  have sq₂ : IsPullback π₂' f'' f' π₂ := IsPullback.of_hasPullback f' π₂
  obtain ⟨h'', rfl, hh''⟩ : ∃ h'' : Y ⟶ pullback f' π₂, h'' ≫ π₂' = h ∧ h'' ≫ f'' = e ≫ g'' :=
    ⟨pullback.lift h (e ≫ g'') (by rw [Category.assoc, sq.w]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have sq₄ : IsPullback h'' e f'' g'' := IsPullback.of_right sq hh'' sq₂
  have hfail₂ : ¬ IsIso ((higherBaseChangeMapAb f'' g'' h'' e sq₄.w (q + 1)).app F) :=
    fun hiso ↦ hfail ((isIso_higherBaseChangeMapAb_app_iff_of_isIntegralHom f n (q + 1)
      (by omega) (fun s p f' hp g h e sq _ _ F hF k hk ↦ hprev s p f' hp g h e sq F hF k
        (by omega)) s p f' hp π₂ π₂' f'' sq₂ g'' h'' e sq₄ F hF).2 hiso)
  -- Step 2 (part (1) of [Stacks, Tag 0F03]): the target of the base change map is nonzero.
  have hp₂ : IsPullback (π₂' ≫ p) f'' f (π₂ ≫ s) := sq₂.paste_horiz hp
  have hmono : Mono ((higherBaseChangeMapAb f'' g'' h'' e sq₄.w (q + 1)).app F) :=
    mono_higherBaseChangeMapAb_app_of_annihilated f n q (π₂ ≫ s) (π₂' ≫ p) f'' g'' h'' e
      hprev hp₂ sq₄ hF
  -- Step 3: the coefficient sheaf may be taken to be `ℤ/dℤ` for some `d ∣ n`.
  have : QuasiCompact h'' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq₄.flip inferInstance
  have : QuasiSeparated h'' :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated) sq₄.flip inferInstance
  obtain ⟨d, hdn, hd⟩ : ∃ d : ℕ, (d : ℤ) ∣ n ∧ ¬ IsZero (((smallEtalePushforwardAb h'').rightDerived
      (q + 1)).obj ((smallEtalePullbackAb e).obj (constantZMod (Spec (.of K)) d))) := by
    by_contra! hcon
    exact not_isZero_of_mono_of_not_isIso _ hfail₂
      (isZero_rightDerived_pullback_of_forall_zmod K h'' e (q + 1) n hcon F hF)
  exact ⟨S'', pullback f' π₂, Y, hS''a, hS''i, hS''n, hS''f, π₂ ≫ s, π₂' ≫ p, f'', hp₂, K,
    inferInstance, inferInstance, g'', hg'', h'', e, sq₄, d, hdn, hd⟩

/-- **Stacks Project, Tag 0F08.** With `f : X ⟶ S` and `n` as in [Stacks, Tag 0F02], assume
`BC(f, n, q)` holds and `BC(f, n, q + 1)` does not (the source's `BC(f, n, q - 1)` and
`BC(f, n, q)` for `q ≥ 1`, indexed from `q + 1`). Then there are a commutative diagram

```
X  ←--  X'  ←-h-  Y
|f      |f'       |e
S  ←--  S'  ←-g-  Spec K
```

with both squares cartesian, in which `S'` is affine, integral and normal with algebraically
closed function field, `K` is algebraically closed and `g : Spec K ⟶ S'` is dominant, and an
integer `d ∣ n` for which `R^{q+1} h_*(ℤ/dℤ)` is nonzero; this is `NormalFailureDiagram`,
the sheaf `ℤ/dℤ` on `Y` being the inverse image along `e` of `constantZMod (Spec K) d`, the
constant sheaf `ℤ/dℤ` on `Spec K`. `BaseChangeHolds` is the condition `BC(f, n, q₀)` of
[Stacks, Tag 0F02].

The failure is first realised over the spectrum of a field `K` with `S'` affine by
[Stacks, Tag 0F07] (`Stacks.EtaleCohomology.exists_affine_field_not_isIso_higherBaseChangeMapAb`).
The field is replaced by an algebraic closure `K̄` by
[Stacks, Tag 0F04] (`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_integralSurjective`)
applied to the integral surjective `Spec K̄ ⟶ Spec K`, and the diagram is then normalized by
`normalFailureDiagram_of_isAlgClosed`. -/
@[stacks 0F08 "the base change condition BC(f, n, q) of 0F02 and its failure in degree q + 1, \
indexed as the source's BC(f, n, q - 1) and BC(f, n, q)"]
public theorem normalFailureDiagram_of_not_baseChangeHolds {X S : Scheme.{u}} (f : X ⟶ S)
    (n : ℤ) (q : ℕ) (hprev : BaseChangeHolds f n (q : ℤ))
    (hfail : ¬ BaseChangeHolds f n ((q : ℤ) + 1)) :
    NormalFailureDiagram f n (q + 1) := by
  -- [Stacks, Tag 0F07]: the failure over an affine `S'` and a field `K`.
  obtain ⟨S', X', Y, hS', s, p, f', hp, K, hK, g, h, e, sq, F, hF, hfail⟩ :=
    exists_affine_field_not_isIso_higherBaseChangeMapAb f n q hprev hfail
  -- [Stacks, Tag 0F04]: replace `K` by an algebraic closure `K̄`.
  let K₁ := AlgebraicClosure K
  let π : Spec (.of K₁) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K₁))
  have : IsIntegralHom π := by
    rw [IsIntegralHom.SpecMap_iff]
    exact Algebra.IsIntegral.isIntegral
  let π' : pullback e π ⟶ Y := pullback.fst e π
  let e₁ : pullback e π ⟶ Spec (.of K₁) := pullback.snd e π
  have sq₃ : IsPullback π' e₁ e π := IsPullback.of_hasPullback e π
  exact normalFailureDiagram_of_isAlgClosed f n q hprev s p f' hp K₁ (π ≫ g) (π' ≫ h) e₁
    (sq₃.paste_horiz sq) ((smallEtalePullbackAb π).obj F)
    (fun U x ↦ zsmul_eq_zero_of_additive (smallEtalePullbackAb π) F n
      (fun V z ↦ hF V.unop z) (op U) x)
    (fun hiso ↦ hfail (isIso_higherBaseChangeMapAb_app_of_integralSurjective f n q hprev s p f'
      hp g h e sq π π' e₁ sq₃ F hF hiso))

end Stacks.EtaleCohomology.FirstFailureDiagram

end
