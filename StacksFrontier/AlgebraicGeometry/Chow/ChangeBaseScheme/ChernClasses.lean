module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleExistence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProjectionFormula
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes under a change of the base scheme

Let `B` be a flat base change of Chow situations with dimension shift `c` — [Stacks, Tag 0FVG] —
let `X` be locally of finite type over `S`, let `ℰ` be a finite locally free `𝒪_X`-module of rank
`r` with base change `ℰ'` on `X' = X ×_S S'`. This file proves [Stacks, Tag 0FVN] for a projective
bundle datum `(π : P ⟶ X, M)` given abstractly: the square

  `CH_k(X) --g^*--> CH_{k+c}(X')`, `CH_{k-i}(X) --g^*--> CH_{k+c-i}(X')`

whose vertical arrows are `c_i(ℰ) ∩ -` and `c_i(ℰ') ∩ -` commutes for all `i`. The statement for
the Chern classes of the library, on the genuine projective bundle, is
`Stacks.Chow.baseChange_chowCohomologyCap_chernClassOfLocallyFree` in
`StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.GenuineChernClasses`, which uses the results
of this file.

## How the Chern classes enter

The cap product `c_i(ℰ) ∩ -` on Chow groups is `Stacks.Chow.chernCapOnChow`, obtained from the
characterization of [Stacks, Tag 02U6] rather than from [Stacks, Tag 02U5]: it is determined by
the projective bundle `π : P = 𝐏(ℰ) ⟶ X` of relative dimension `r - 1` together with the first
Chern class cap operator of its twist `𝒪_P(1)`, and writing it down at all needs the two halves
of [Stacks, Tag 02TX] for that bundle, which this repository carries as the hypotheses
`Stacks.Chow.ProjectiveBundleRelationInjective` and
`Stacks.Chow.ProjectiveBundleRelationSurjective`. Those hypotheses are therefore hypotheses of
the statement below, on each of the two base schemes: they are not extra assumptions on
[Stacks, Tag 0FVN] but the data and the facts that make `c_i(ℰ) ∩ -` exist.

What the base change needs beyond that is exactly what the source's proof uses, and both are
available here:

* the projective bundle of `ℰ'` is the base change of the projective bundle of `ℰ`, so the
  morphism over `X'` is `Stacks.Chow.baseChangeMorphism` of `π`, flat of relative dimension
  `r - 1` by [Stacks, Tag 0FVK], and the twist on it is the pullback of `𝒪_P(1)`;
* flat pullback commutes with base change ([Stacks, Tag 0FVK]) and capping with the first Chern
  class of an invertible module commutes with base change ([Stacks, Tag 0FVM],
  `Stacks.Chow.baseChange_firstChernClassCapChow_module`).

Together these carry each summand `c₁(𝒪_P(1))^i ∩ π^*(-)` of the relation of [Stacks, Tag 02U6]
across the base change, which is
`Stacks.Chow.baseChange_projectiveBundleChernTerm`; summing, the base change of a family
satisfying the relation satisfies the relation, and the uniqueness of [Stacks, Tag 02U6]
identifies it with the family of Chern classes on `X'`.

Unlike `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleFlatPullback`, which
carries the compatibility of the summands as the hypothesis
`Stacks.Chow.ChernTermsCompatibleWithFlatPullback` because [Stacks, Tag 02SS] on Chow groups is
not available, nothing of the kind is assumed here: the compatibility is proved.

## Main definitions

* `Stacks.Chow.chernCapIterate` — the `i`-fold cap product with the first Chern class of a cap
  operator, `A_{k+i}(X) ⟶ A_k(X)`, indexed by a natural number rather than by a list. This is
  `Stacks.Chow.iteratedChernCapOnChow` at a constant list with its degrees written without the
  length of that list, which is what makes the induction below readable.
* `Stacks.Chow.baseChangeChernFamily` — the base change of a family of Chow classes, read in the
  degrees of a family based at `k + c`.

## Main results

* `Stacks.Chow.iteratedChernCapOnChow_replicate_apply` — the two iterates agree.
* `Stacks.Chow.baseChangeChowPullback_chernCapIterate` — **[Stacks, Tag 0FVM], iterated**: the
  base change of an `i`-fold first Chern class cap of an invertible module is the `i`-fold cap of
  its base change.
* `Stacks.Chow.baseChange_projectiveBundleChernTerm` — **[Stacks, Tag 0FVK] and
  [Stacks, Tag 0FVM], assembled**: base change carries each summand of the relation of
  [Stacks, Tag 02U6] over `X` to the corresponding summand over `X'`.
* `Stacks.Chow.baseChange_projectiveBundleChernRelation` — the base change of a family satisfying
  the relation satisfies the relation.
* `Stacks.Chow.baseChange_isChernCapFamily` — the base change of a characterizing family is a
  characterizing family of the base change of the class.
* `Stacks.Chow.baseChange_chernCapOnChow` — **[Stacks, Tag 0FVN]**: the square of Chow groups
  commutes for every `i`.

## Implementation notes

The structure morphism of the bundle over `S` is written `π ≫ sX` rather than carried as an
independent morphism with a factorization, because that is the only thing the base change of the
bundle can be: `Stacks.Chow.baseChangeMorphism` produces a morphism out of
`(P ×_S S') = pullback (π ≫ sX) B.g`.

## References

* [Stacks Project, Tag 0FVN](https://stacks.math.columbia.edu/tag/0FVN)
* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVJ](https://stacks.math.columbia.edu/tag/0FVJ)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 0FVM](https://stacks.math.columbia.edu/tag/0FVM)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The iterated first Chern class cap with degrees indexed by a natural number -/

section Iterate

variable (C : ChowSituation.{u}) {Z : Scheme.{u}} (q : Z ⟶ C.S) [LocallyOfFiniteType q]

/-- **The `i`-fold cap product with the first Chern class of a cap operator**,
`A_{k+i}(X) ⟶ A_k(X)`. This is `Stacks.Chow.iteratedChernCapOnChow` at the constant list of
length `i`, with the degree of the source written `k + i` rather than
`k + (List.replicate i O).length`; the two agree by
`Stacks.Chow.iteratedChernCapOnChow_replicate_apply`. -/
def chernCapIterate (O : ChernCapOperator C q) :
    (i : ℕ) → (k : ℤ) → chowGroup C q (k + (i : ℤ)) →+ chowGroup C q k
  | 0, k => (chowGroupCast C q (show k + ((0 : ℕ) : ℤ) = k from by simp)).toAddMonoidHom
  | (i + 1), k =>
      ((O.capOnChow C q k).comp (chernCapIterate O i (k + 1))).comp
        (chowGroupCast C q
          (show k + ((i + 1 : ℕ) : ℤ) = k + 1 + (i : ℤ) from by push_cast; ring)).toAddMonoidHom

/-- The `0`-fold cap product is the transport along `k + 0 = k`. -/
theorem chernCapIterate_zero_apply (O : ChernCapOperator C q) (k : ℤ)
    (x : chowGroup C q (k + ((0 : ℕ) : ℤ))) :
    chernCapIterate C q O 0 k x =
      chowGroupCast C q (show k + ((0 : ℕ) : ℤ) = k from by simp) x :=
  rfl

/-- The `(i + 1)`-fold cap product is the `i`-fold one in degree `k + 1` followed by one cap
product with the first Chern class. -/
theorem chernCapIterate_succ_apply (O : ChernCapOperator C q) (i : ℕ) (k : ℤ)
    (x : chowGroup C q (k + ((i + 1 : ℕ) : ℤ))) :
    chernCapIterate C q O (i + 1) k x =
      O.capOnChow C q k (chernCapIterate C q O i (k + 1)
        (chowGroupCast C q
          (show k + ((i + 1 : ℕ) : ℤ) = k + 1 + (i : ℤ) from by push_cast; ring) x)) :=
  rfl

/-- The iterated cap product commutes with transport along an equality of base degrees. -/
theorem chernCapIterate_chowGroupCast (O : ChernCapOperator C q) (i : ℕ) {k l : ℤ} (h : k = l)
    (h' : k + (i : ℤ) = l + (i : ℤ)) (x : chowGroup C q (k + (i : ℤ))) :
    chowGroupCast C q h (chernCapIterate C q O i k x) =
      chernCapIterate C q O i l (chowGroupCast C q h' x) := by
  subst h
  rfl

/-- **The two iterated cap products agree.** -/
theorem iteratedChernCapOnChow_replicate_apply (O : ChernCapOperator C q) :
    ∀ (i : ℕ) (k : ℤ) (x : chowGroup C q (k + (i : ℤ)))
      (h : k + (i : ℤ) = k + ((List.replicate i O).length : ℤ)),
      iteratedChernCapOnChow C q (List.replicate i O) k (chowGroupCast C q h x) =
        chernCapIterate C q O i k x := by
  intro i
  induction i with
  | zero =>
    intro k x h
    rw [chernCapIterate_zero_apply]
    show chowGroupDegreeCast C q _ (AddMonoidHom.id (chowGroup C q k)) (chowGroupCast C q h x) = _
    rw [chowGroupDegreeCast_apply]
    simp only [AddMonoidHom.id_apply, chowGroupCast_chowGroupCast]
  | succ i ih =>
    intro k x h
    rw [chernCapIterate_succ_apply]
    show chowGroupDegreeCast C q _
      ((O.capOnChow C q k).comp (iteratedChernCapOnChow C q (List.replicate i O) (k + 1)))
        (chowGroupCast C q h x) = _
    rw [chowGroupDegreeCast_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    refine congrArg (O.capOnChow C q k) (Eq.trans (congrArg _ ?_) (ih (k + 1)
      (chowGroupCast C q
        (show k + ((i + 1 : ℕ) : ℤ) = k + 1 + (i : ℤ) from by push_cast; ring) x)
      (show k + 1 + (i : ℤ) = k + 1 + ((List.replicate i O).length : ℤ) from by simp)))
    simp only [chowGroupCast_chowGroupCast]

end Iterate

/-! ### A summand of the relation of Stacks 02U6 through the iterated cap product -/

section Term

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (twist : ChernCapOperator C sP)

/-- A summand of the relation of [Stacks, Tag 02U6], written with the iterated cap product of
`Stacks.Chow.chernCapIterate` in place of the one indexed by a list. -/
theorem projectiveBundleChernTerm_eq_chernCapIterate (k : ℤ) (i : ℕ) (hi : i ≤ r)
    (x : chowGroup C sX (k - ((r - i : ℕ) : ℤ))) :
    projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i hi x =
      chernCapIterate C sP twist i (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
        (chowGroupCast C sP
          (show k - ((r - i : ℕ) : ℤ) + ((r - 1 : ℕ) : ℤ) =
              k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + (i : ℤ) from by
            rw [Nat.cast_sub hi]; ring)
          (projectiveBundlePullback C sX sP π hsP r hπ hfac (k - ((r - i : ℕ) : ℤ)) x)) := by
  refine Eq.trans (congrArg (iteratedChernCapOnChow C sP (List.replicate i twist)
      (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))) ?_)
    (iteratedChernCapOnChow_replicate_apply C sP twist i _ _ (by simp))
  simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply,
    chowGroupCast_chowGroupCast]

/-- The flat pullback along the projection of the bundle commutes with transport along an
equality of degrees. -/
theorem projectiveBundlePullback_chowGroupCast {m n : ℤ} (h : m = n)
    (h' : m + ((r - 1 : ℕ) : ℤ) = n + ((r - 1 : ℕ) : ℤ)) (x : chowGroup C sX m) :
    projectiveBundlePullback C sX sP π hsP r hπ hfac n (chowGroupCast C sX h x) =
      chowGroupCast C sP h' (projectiveBundlePullback C sX sP π hsP r hπ hfac m x) := by
  subst h
  rfl

end Term

/-! ### Stacks 0FVM for the iterated cap product -/

variable (B : FlatBaseChangeSituation.{u})

/-- **[Stacks, Tag 0FVM] for the cap operator of an invertible module.** Base change commutes
with capping with the first Chern class of an invertible module, read on the cap operator
`Stacks.Chow.invertibleChernCap` that the iterated cap product consumes. -/
theorem baseChangeChowPullback_capOnChow_invertibleChernCap {P : Scheme.{u}}
    (sP : P ⟶ B.base.S) [LocallyOfFiniteType sP] (M : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]
    (k : ℤ) (y : chowGroup B.base sP (k + 1)) :
    baseChangeChowPullback B sP k
        ((invertibleChernCap B.base sP M).capOnChow B.base sP k y) =
      (invertibleChernCap B.baseChange (pullback.snd sP B.g)
            ((Scheme.Modules.pullback (pullback.fst sP B.g)).obj M)).capOnChow
          B.baseChange (pullback.snd sP B.g) (k + B.c)
        (chowGroupCast B.baseChange (pullback.snd sP B.g)
          (show k + 1 + B.c = k + B.c + 1 from by omega)
          (baseChangeChowPullback B sP (k + 1) y)) :=
  (baseChange_firstChernClassCapChow_module B sP M k y).symm

/-- Base change commutes with transport along an equality of degrees, with the transport on the
base-changed side taken along the induced equality. -/
private theorem baseChangeChowPullback_chowGroupCast_add {X : Scheme.{u}} (f : X ⟶ B.base.S)
    [LocallyOfFiniteType f] {i j : ℤ} (h : i = j) (x : chowGroup B.base f i) :
    baseChangeChowPullback B f j (chowGroupCast B.base f h x) =
      chowGroupCast B.baseChange (pullback.snd f B.g) (congrArg (· + B.c) h)
        (baseChangeChowPullback B f i x) :=
  baseChangeChowPullback_chowGroupCast B f h _ x

/-- **[Stacks, Tag 0FVM], iterated.** The base change of the `i`-fold cap product with the first
Chern class of an invertible module `M` on `P` is the `i`-fold cap product with the first Chern
class of the base change of `M`.

The induction is on `i`: the base case is that base change commutes with a transport of degrees,
and the step is `Stacks.Chow.baseChangeChowPullback_capOnChow_invertibleChernCap`, which is
[Stacks, Tag 0FVM]. -/
theorem baseChangeChowPullback_chernCapIterate {P : Scheme.{u}} (sP : P ⟶ B.base.S)
    [LocallyOfFiniteType sP] (M : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M] :
    ∀ (i : ℕ) (k : ℤ) (h : k + (i : ℤ) + B.c = k + B.c + (i : ℤ))
      (x : chowGroup B.base sP (k + (i : ℤ))),
      baseChangeChowPullback B sP k
          (chernCapIterate B.base sP (invertibleChernCap B.base sP M) i k x) =
        chernCapIterate B.baseChange (pullback.snd sP B.g)
            (invertibleChernCap B.baseChange (pullback.snd sP B.g)
              ((Scheme.Modules.pullback (pullback.fst sP B.g)).obj M)) i (k + B.c)
          (chowGroupCast B.baseChange (pullback.snd sP B.g) h
            (baseChangeChowPullback B sP (k + (i : ℤ)) x)) := by
  intro i
  induction i with
  | zero =>
    intro k h x
    rw [chernCapIterate_zero_apply, chernCapIterate_zero_apply]
    simp only [baseChangeChowPullback_chowGroupCast_add, chowGroupCast_chowGroupCast]
  | succ i ih =>
    intro k h x
    rw [chernCapIterate_succ_apply, chernCapIterate_succ_apply,
      baseChangeChowPullback_capOnChow_invertibleChernCap B sP M k,
      ih (k + 1) (show k + 1 + (i : ℤ) + B.c = k + 1 + B.c + (i : ℤ) from by omega)]
    refine congrArg _ ?_
    rw [chernCapIterate_chowGroupCast B.baseChange (pullback.snd sP B.g) _ i
      (show k + 1 + B.c = k + B.c + 1 from by omega)
      (show k + 1 + B.c + (i : ℤ) = k + B.c + 1 + (i : ℤ) from by omega)]
    refine congrArg _ ?_
    simp only [baseChangeChowPullback_chowGroupCast_add, chowGroupCast_chowGroupCast]

/-! ### The base change of the projective bundle -/

variable {X P : Scheme.{u}} (sX : X ⟶ B.base.S) [LocallyOfFiniteType sX]
  (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (r : ℕ)
  (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))

/-- The base change `P ×_S S' ⟶ X ×_S S'` of the projection of the bundle. -/
abbrev bundleBaseChangeMorphism :
    (pullback (π ≫ sX) B.g : Scheme.{u}) ⟶ (pullback sX B.g : Scheme.{u}) :=
  baseChangeMorphism B sX π

/-- The base change of the projection of the bundle is locally of finite type. -/
instance locallyOfFiniteType_bundleBaseChangeMorphism :
    LocallyOfFiniteType (bundleBaseChangeMorphism B sX π) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeMorphism B sX π)
    (P := @LocallyOfFiniteType) inferInstance

/-- The base change of the projection of the bundle is flat. -/
instance flat_bundleBaseChangeMorphism : Flat (bundleBaseChangeMorphism B sX π) :=
  MorphismProperty.of_isPullback (isPullback_baseChangeMorphism B sX π) (P := @Flat) inferInstance

omit [LocallyOfFiniteType sX] [Flat π] in
include hπ in
/-- **[Stacks, Tag 0FVK] for the projection of the bundle**: its base change is again flat of
relative dimension `r - 1`. -/
theorem relativeDimension_bundleBaseChangeMorphism :
    AlgebraicGeometry.RelativeDimension (bundleBaseChangeMorphism B sX π) (r - 1) :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_baseChangeMorphism B sX π) hπ

/-- [Stacks, Tag 02S1] for the base-changed projection, so that the flat pullback along it is
available in every degree. -/
theorem flatPullbackFactors_bundleBaseChangeMorphism (k : ℤ) :
    FlatPullbackFactorsThroughRationalEquivalence B.baseChange
      (pullback.snd (π ≫ sX) B.g) (pullback.snd sX B.g) (bundleBaseChangeMorphism B sX π)
      (baseChangeMorphism_comp_snd B sX π) (r - 1)
      (relativeDimension_bundleBaseChangeMorphism B sX π r hπ) k :=
  flatPullbackFactorsThroughRationalEquivalence_general B.baseChange
    (pullback.snd (π ≫ sX) B.g) (pullback.snd sX B.g) (bundleBaseChangeMorphism B sX π)
    (baseChangeMorphism_comp_snd B sX π) (r - 1)
    (relativeDimension_bundleBaseChangeMorphism B sX π r hπ) k

variable (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence B.base
    (π ≫ sX) sX π rfl (r - 1) hπ k)

/-- **[Stacks, Tag 0FVK] along the projection of the bundle**: base change commutes with the flat
pullback `π^*`. -/
theorem baseChange_projectiveBundlePullback (m : ℤ)
    (hidx : m + ((r - 1 : ℕ) : ℤ) + B.c = m + B.c + ((r - 1 : ℕ) : ℤ))
    (x : chowGroup B.base sX m) :
    chowGroupCast B.baseChange (pullback.snd (π ≫ sX) B.g) hidx
        (baseChangeChowPullback B (π ≫ sX) (m + ((r - 1 : ℕ) : ℤ))
          (projectiveBundlePullback B.base sX (π ≫ sX) π rfl r hπ hfac m x)) =
      projectiveBundlePullback B.baseChange (pullback.snd sX B.g)
        (pullback.snd (π ≫ sX) B.g) (bundleBaseChangeMorphism B sX π)
        (baseChangeMorphism_comp_snd B sX π) r
        (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
        (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ) (m + B.c)
        (baseChangeChowPullback B sX m x) :=
  baseChange_flatPullbackChow_apply B (π ≫ sX) sX π rfl (bundleBaseChangeMorphism B sX π)
    (baseChangeMorphism_comp_snd B sX π) (baseChangeMorphism_comp_fst B sX π).symm (r - 1) hπ
    (relativeDimension_bundleBaseChangeMorphism B sX π r hπ) m hidx x

/-! ### The summands of the relation of Stacks 02U6 under base change -/

variable (M : P.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]

/-- The twist of the base-changed bundle: the pullback of `𝒪_P(1)` to `P ×_S S'`. -/
abbrev bundleTwistBaseChange : (pullback (π ≫ sX) B.g : Scheme.{u}).Modules :=
  (Scheme.Modules.pullback (pullback.fst (π ≫ sX) B.g)).obj M

/-- **[Stacks, Tag 0FVK] and [Stacks, Tag 0FVM], assembled.** Base change carries the `i`-th
summand `c₁(𝒪_P(1))^i ∩ π^*(-)` of the relation of [Stacks, Tag 02U6] over `X` to the `i`-th
summand over `X'`, precomposed with base change.

This is the step that the flat-pullback analogue
`Stacks.Chow.ChernTermsCompatibleWithFlatPullback` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleFlatPullback` has to assume:
here `π^*` is carried across by [Stacks, Tag 0FVK]
(`Stacks.Chow.baseChange_projectiveBundlePullback`) and the `i` first Chern class caps by
[Stacks, Tag 0FVM] (`Stacks.Chow.baseChangeChowPullback_chernCapIterate`). -/
theorem baseChange_projectiveBundleChernTerm (k : ℤ) (i : ℕ) (hi : i ≤ r)
    (x : chowGroup B.base sX (k - ((r - i : ℕ) : ℤ))) :
    baseChangeChowPullback B (π ≫ sX) (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
        (projectiveBundleChernTerm B.base sX (π ≫ sX) π rfl r hπ hfac
          (invertibleChernCap B.base (π ≫ sX) M) k i hi x) =
      chowGroupCast B.baseChange (pullback.snd (π ≫ sX) B.g)
        (show k + B.c + ((r - 1 : ℕ) : ℤ) - (r : ℤ) =
            k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + B.c from by omega)
        (projectiveBundleChernTerm B.baseChange (pullback.snd sX B.g)
          (pullback.snd (π ≫ sX) B.g) (bundleBaseChangeMorphism B sX π)
          (baseChangeMorphism_comp_snd B sX π) r
          (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
          (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
          (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
            (bundleTwistBaseChange B sX π M)) (k + B.c) i hi
          (chowGroupCast B.baseChange (pullback.snd sX B.g)
            (show k - ((r - i : ℕ) : ℤ) + B.c = k + B.c - ((r - i : ℕ) : ℤ) from by omega)
            (baseChangeChowPullback B sX (k - ((r - i : ℕ) : ℤ)) x))) := by
  rw [projectiveBundleChernTerm_eq_chernCapIterate B.base sX (π ≫ sX) π rfl r hπ hfac
      (invertibleChernCap B.base (π ≫ sX) M) k i hi x,
    baseChangeChowPullback_chernCapIterate B (π ≫ sX) M i
      (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
      (show k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + (i : ℤ) + B.c =
        k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + B.c + (i : ℤ) from by omega),
    projectiveBundleChernTerm_eq_chernCapIterate B.baseChange (pullback.snd sX B.g)
      (pullback.snd (π ≫ sX) B.g) (bundleBaseChangeMorphism B sX π)
      (baseChangeMorphism_comp_snd B sX π) r
      (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
      (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
      (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
        (bundleTwistBaseChange B sX π M)) (k + B.c) i hi _,
    chernCapIterate_chowGroupCast B.baseChange (pullback.snd (π ≫ sX) B.g) _ i
      (show k + B.c + ((r - 1 : ℕ) : ℤ) - (r : ℤ) =
        k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + B.c from by omega)
      (show k + B.c + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + (i : ℤ) =
        k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + B.c + (i : ℤ) from by omega)]
  refine congrArg _ ?_
  rw [baseChangeChowPullback_chowGroupCast_add,
    projectiveBundlePullback_chowGroupCast B.baseChange (pullback.snd sX B.g)
      (pullback.snd (π ≫ sX) B.g) (bundleBaseChangeMorphism B sX π)
      (baseChangeMorphism_comp_snd B sX π) r
      (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
      (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
      (show k - ((r - i : ℕ) : ℤ) + B.c = k + B.c - ((r - i : ℕ) : ℤ) from by omega)
      (show k - ((r - i : ℕ) : ℤ) + B.c + ((r - 1 : ℕ) : ℤ) =
        k + B.c - ((r - i : ℕ) : ℤ) + ((r - 1 : ℕ) : ℤ) from by omega),
    ← baseChange_projectiveBundlePullback B sX π r hπ hfac (k - ((r - i : ℕ) : ℤ))
      (show k - ((r - i : ℕ) : ℤ) + ((r - 1 : ℕ) : ℤ) + B.c =
        k - ((r - i : ℕ) : ℤ) + B.c + ((r - 1 : ℕ) : ℤ) from by omega)]
  simp only [chowGroupCast_chowGroupCast]

/-! ### Stacks 0FVN -/

/-- The base change of a family of Chow classes on `X`, read in the degrees of a family on
`X' = X ×_S S'` based at `k + c`. -/
def baseChangeChernFamily (k : ℤ)
    (c : ∀ j : Fin (r + 1), chowGroup B.base sX (k - (j : ℤ))) (j : Fin (r + 1)) :
    chowGroup B.baseChange (pullback.snd sX B.g) (k + B.c - (j : ℤ)) :=
  chowGroupCast B.baseChange (pullback.snd sX B.g)
    (show k - (j : ℤ) + B.c = k + B.c - (j : ℤ) from by omega)
    (baseChangeChowPullback B sX (k - (j : ℤ)) (c j))

/-- **The base change of a family satisfying the relation of [Stacks, Tag 02U6] satisfies the
relation.** Apply the base-change map to the relation and use
`Stacks.Chow.baseChange_projectiveBundleChernTerm` on each summand; the passage from the summands
to the relation is the additivity of the base-change map. -/
theorem baseChange_projectiveBundleChernRelation (k : ℤ)
    (c : ∀ j : Fin (r + 1), chowGroup B.base sX (k - (j : ℤ)))
    (hc : ProjectiveBundleChernRelation B.base sX (π ≫ sX) π rfl r hπ hfac
      (invertibleChernCap B.base (π ≫ sX) M) k c) :
    ProjectiveBundleChernRelation B.baseChange (pullback.snd sX B.g)
      (pullback.snd (π ≫ sX) B.g) (bundleBaseChangeMorphism B sX π)
      (baseChangeMorphism_comp_snd B sX π) r
      (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
      (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
      (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
        (bundleTwistBaseChange B sX π M)) (k + B.c)
      (baseChangeChernFamily B sX r k c) := by
  have hrel : ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm B.base sX (π ≫ sX) π rfl r hπ hfac
        (invertibleChernCap B.base (π ≫ sX) M) k i.val (Nat.lt_succ_iff.mp i.isLt)
        (c ⟨r - i.val, by omega⟩) = 0 := hc
  show ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
    projectiveBundleChernTerm B.baseChange (pullback.snd sX B.g) (pullback.snd (π ≫ sX) B.g)
      (bundleBaseChangeMorphism B sX π) (baseChangeMorphism_comp_snd B sX π) r
      (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
      (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
      (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
        (bundleTwistBaseChange B sX π M)) (k + B.c) i.val (Nat.lt_succ_iff.mp i.isLt)
      (baseChangeChernFamily B sX r k c ⟨r - i.val, by omega⟩) = 0
  refine (chowGroupCast B.baseChange (pullback.snd (π ≫ sX) B.g)
    (show k + B.c + ((r - 1 : ℕ) : ℤ) - (r : ℤ) =
      k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + B.c from by omega)).injective ?_
  rw [map_zero, map_sum]
  have hsum := congrArg (baseChangeChowPullback B (π ≫ sX) (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))) hrel
  rw [map_sum, map_zero] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, map_zsmul, baseChange_projectiveBundleChernTerm B sX π r hπ hfac M k i.val
    (Nat.lt_succ_iff.mp i.isLt) (c ⟨r - i.val, by omega⟩)]
  rfl

/-- **The base change of a family characterizing the Chern classes of `α` characterizes the
Chern classes of `g^*α`.** -/
theorem baseChange_isChernCapFamily (k : ℤ) (α : chowGroup B.base sX k)
    (c : ∀ j : Fin (r + 1), chowGroup B.base sX (k - (j : ℤ)))
    (hc : IsChernCapFamily B.base sX (π ≫ sX) π rfl r hπ hfac
      (invertibleChernCap B.base (π ≫ sX) M) k α c) :
    IsChernCapFamily B.baseChange (pullback.snd sX B.g) (pullback.snd (π ≫ sX) B.g)
      (bundleBaseChangeMorphism B sX π) (baseChangeMorphism_comp_snd B sX π) r
      (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
      (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
      (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
        (bundleTwistBaseChange B sX π M)) (k + B.c)
      (baseChangeChowPullback B sX k α) (baseChangeChernFamily B sX r k c) := by
  refine ⟨?_, baseChange_projectiveBundleChernRelation B sX π r hπ hfac M k c hc.2⟩
  show chowGroupCast B.baseChange (pullback.snd sX B.g) _
      (chowGroupCast B.baseChange (pullback.snd sX B.g) _
        (baseChangeChowPullback B sX (k - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) : ℤ))
          (c ⟨0, Nat.zero_lt_succ r⟩))) =
    baseChangeChowPullback B sX k α
  rw [← hc.1]
  simp only [baseChangeChowPullback_chowGroupCast_add, chowGroupCast_chowGroupCast]

/-- **[Stacks, Tag 0FVN].** In the flat base-change situation of [Stacks, Tag 0FVG] let `X` be
locally of finite type over `S`, let `X' = X ×_S S'` be the base change by `S' ⟶ S`, and let `ℰ`
be a finite locally free `𝒪_X`-module of rank `r` with base change `ℰ'` on `X'`. Then the square

  `CH_k(X)     --g^*--> CH_{k+c}(X')`
  `    |c_i(ℰ) ∩ -              |c_i(ℰ') ∩ -`
  `CH_{k-i}(X) --g^*--> CH_{k+c-i}(X')`

of Chow groups commutes for all `i`.

The module `ℰ` enters through its projective bundle `π : P = 𝐏(ℰ) ⟶ X` and the twist `𝒪_P(1)`,
which is how `Stacks.Chow.chernCapOnChow` — the operation `c_i(ℰ) ∩ -` of [Stacks, Tag 02U6] —
is given: `π` flat of relative dimension `r - 1`, the invertible module `M = 𝒪_P(1)` on `P`, and
the two halves of [Stacks, Tag 02TX] for the bundle, which this repository carries as hypotheses
and without which the operation cannot be written down at all. On `X'` the bundle is the base
change `P ×_S S' ⟶ X'` of `π`, which is `𝐏(ℰ')`, and the twist is the pullback of `M`.

**Proof.** The family of Chern classes of `α` satisfies the relation of [Stacks, Tag 02U6] and
has `α` in degree `k`. Its base change satisfies the relation over `X'`, by
`Stacks.Chow.baseChange_projectiveBundleChernRelation` — whose summandwise content is
[Stacks, Tag 0FVK] for `π^*` and [Stacks, Tag 0FVM] for the first Chern class caps — and has
`g^*α` in degree `k + c`. So the uniqueness of [Stacks, Tag 02U6] identifies it with the family
of Chern classes of `g^*α`, which is the assertion. -/
theorem baseChange_chernCapOnChow
    (hinj : ProjectiveBundleRelationInjective B.base sX (π ≫ sX) π rfl r hπ hfac
      (invertibleChernCap B.base (π ≫ sX) M))
    (hsurj : ProjectiveBundleRelationSurjective B.base sX (π ≫ sX) π rfl r hπ hfac
      (invertibleChernCap B.base (π ≫ sX) M))
    (hinj' : ProjectiveBundleRelationInjective B.baseChange (pullback.snd sX B.g)
      (pullback.snd (π ≫ sX) B.g) (bundleBaseChangeMorphism B sX π)
      (baseChangeMorphism_comp_snd B sX π) r
      (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
      (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
      (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
        (bundleTwistBaseChange B sX π M)))
    (hsurj' : ProjectiveBundleRelationSurjective B.baseChange (pullback.snd sX B.g)
      (pullback.snd (π ≫ sX) B.g) (bundleBaseChangeMorphism B sX π)
      (baseChangeMorphism_comp_snd B sX π) r
      (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
      (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
      (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
        (bundleTwistBaseChange B sX π M)))
    (k : ℤ) (j : Fin (r + 1)) (α : chowGroup B.base sX k) :
    chernCapOnChow B.baseChange (pullback.snd sX B.g) (pullback.snd (π ≫ sX) B.g)
        (bundleBaseChangeMorphism B sX π) (baseChangeMorphism_comp_snd B sX π) r
        (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
        (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
        (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
          (bundleTwistBaseChange B sX π M)) hinj' hsurj' (k + B.c) j
        (baseChangeChowPullback B sX k α) =
      chowGroupCast B.baseChange (pullback.snd sX B.g)
        (show k - (j : ℤ) + B.c = k + B.c - (j : ℤ) from by omega)
        (baseChangeChowPullback B sX (k - (j : ℤ))
          (chernCapOnChow B.base sX (π ≫ sX) π rfl r hπ hfac
            (invertibleChernCap B.base (π ≫ sX) M) hinj hsurj k j α)) := by
  have heq := eq_projectiveBundleChernCapFamily B.baseChange (pullback.snd sX B.g)
    (pullback.snd (π ≫ sX) B.g) (bundleBaseChangeMorphism B sX π)
    (baseChangeMorphism_comp_snd B sX π) r
    (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
    (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
    (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
      (bundleTwistBaseChange B sX π M)) hinj' hsurj' (k + B.c)
    (baseChangeChowPullback B sX k α)
    (baseChange_isChernCapFamily B sX π r hπ hfac M k α
      (projectiveBundleChernCapFamily B.base sX (π ≫ sX) π rfl r hπ hfac
        (invertibleChernCap B.base (π ≫ sX) M) hsurj k α)
      (isChernCapFamily_projectiveBundleChernCapFamily B.base sX (π ≫ sX) π rfl r hπ hfac
        (invertibleChernCap B.base (π ≫ sX) M) hsurj k α))
  exact (congrFun heq j).symm

/-- **[Stacks, Tag 0FVN] for an arbitrary natural number `i`.** [Stacks, Tag 02U0] defines
`c_i(ℰ)` for `i = 0, …, r`, so `Stacks.Chow.baseChange_chernCapOnChow` already states the square
for every `i` at which the Chern class is defined. Reading `c_i(ℰ) ∩ -` as zero for `i > r`, the
usual convention, the square holds for every natural number `i`: above the rank both routes are
zero. -/
theorem baseChange_chernCapOnChowExt
    (hinj : ProjectiveBundleRelationInjective B.base sX (π ≫ sX) π rfl r hπ hfac
      (invertibleChernCap B.base (π ≫ sX) M))
    (hsurj : ProjectiveBundleRelationSurjective B.base sX (π ≫ sX) π rfl r hπ hfac
      (invertibleChernCap B.base (π ≫ sX) M))
    (hinj' : ProjectiveBundleRelationInjective B.baseChange (pullback.snd sX B.g)
      (pullback.snd (π ≫ sX) B.g) (bundleBaseChangeMorphism B sX π)
      (baseChangeMorphism_comp_snd B sX π) r
      (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
      (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
      (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
        (bundleTwistBaseChange B sX π M)))
    (hsurj' : ProjectiveBundleRelationSurjective B.baseChange (pullback.snd sX B.g)
      (pullback.snd (π ≫ sX) B.g) (bundleBaseChangeMorphism B sX π)
      (baseChangeMorphism_comp_snd B sX π) r
      (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
      (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
      (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
        (bundleTwistBaseChange B sX π M)))
    (k : ℤ) (i : ℕ) (α : chowGroup B.base sX k) :
    (if h : i ≤ r then
        chernCapOnChow B.baseChange (pullback.snd sX B.g) (pullback.snd (π ≫ sX) B.g)
          (bundleBaseChangeMorphism B sX π) (baseChangeMorphism_comp_snd B sX π) r
          (relativeDimension_bundleBaseChangeMorphism B sX π r hπ)
          (flatPullbackFactors_bundleBaseChangeMorphism B sX π r hπ)
          (invertibleChernCap B.baseChange (pullback.snd (π ≫ sX) B.g)
            (bundleTwistBaseChange B sX π M)) hinj' hsurj' (k + B.c)
          ⟨i, Nat.lt_succ_of_le h⟩ (baseChangeChowPullback B sX k α)
      else 0) =
      chowGroupCast B.baseChange (pullback.snd sX B.g)
        (show k - (i : ℤ) + B.c = k + B.c - (i : ℤ) from by omega)
        (baseChangeChowPullback B sX (k - (i : ℤ))
          (if h : i ≤ r then
              chernCapOnChow B.base sX (π ≫ sX) π rfl r hπ hfac
                (invertibleChernCap B.base (π ≫ sX) M) hinj hsurj k
                ⟨i, Nat.lt_succ_of_le h⟩ α
            else 0)) := by
  by_cases h : i ≤ r
  · rw [dif_pos h, dif_pos h]
    exact baseChange_chernCapOnChow B sX π r hπ hfac M hinj hsurj hinj' hsurj' k
      ⟨i, Nat.lt_succ_of_le h⟩ α
  · rw [dif_neg h, dif_neg h, map_zero, map_zero]

end Stacks.Chow

end
