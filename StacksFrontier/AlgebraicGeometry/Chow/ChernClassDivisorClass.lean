module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDominantPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.IntegralChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorOfInvertibleSheaf

/-!
# The first Chern class of an invertible module is its Weil divisor class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, integral and of delta-dimension `n`, and let `L` be an invertible
`𝒪_X`-module. [Stacks, Tag 02U2](https://stacks.math.columbia.edu/tag/02U2) says that the first
Chern class of `L` in the sense of [Stacks, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0) —
the class `c_1 ∈ A_{n-1}(X)` of the projective-bundle characterization — is the Weil divisor class
of `L` in the sense of [Stacks, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ).

The source proof is three lines. The rank of `L` is one, so the projective bundle of `L` is `X`
itself, with projection the identity and `O_{𝐏(L)}(1) = L`; substituting that into the relation
02U1 leaves

  `(-1)^1 c₁(L) ∩ c_0 + (-1)^0 c_1 = 0`,

and `c_0 = [X]` turns this into `c_1 = c₁(L) ∩ [X]`, which is the Weil divisor class.

This file is that computation. Both sides of the asserted equality are already in this library:
the left is `Stacks.Chow.chernClassCapFundamental` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.IntegralChernClass`, the right is
`Stacks.Chow.firstChernClassCapFundamental` of
`StacksFrontier.AlgebraicGeometry.Chow.DivisorOfInvertibleSheaf`.

## Main results

* `Stacks.Chow.flatPullbackChow_id` — flat pullback along the identity of `X` is the identity of
  `A_k(X)`, up to the transport `A_k(X) = A_{k+0}(X)`. This is what makes the relation 02U1
  readable on `X` itself.
* `Stacks.Chow.firstChernClassCapOfInvertible_fundamentalCycle_eq_firstChernClassCapFundamental` —
  the cap product of Stacks 02SO of an invertible module, evaluated at the fundamental cycle of an
  integral scheme, **is** the Weil divisor class of Stacks 02SJ (2).
* `Stacks.Chow.chernClassCapFundamental_one_eq_firstChernClassCapFundamental` — **Stacks 02U2**.

## Implementation notes

### What the statement carries, and why

`Stacks.Chow.chernClassCapFundamental` is parameterised by the projective bundle on which the
relation 02U1 is read: a morphism `π : P ⟶ X`, flat of relative dimension `r - 1` whose flat
pullback factors through rational equivalence, a `Stacks.Chow.ChernCapOperator` on `P` standing
for `c₁(O_P(1)) ∩ -`, and a `Stacks.Chow.ChernClassFundamentalFamily` — the family of clause (1)
of Stacks 02U0, as a datum. The reasons are recorded in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation`: neither Stacks
01O4 (so not `O_P(1)`) nor Stacks 02TX is available there.

Accordingly Stacks 02U2 is stated at `r = 1` with the bundle instantiated the way the source
instantiates it: `P = X`, `π = 𝟙 X`, and `O_{𝐏(L)}(1) = L`. The twist operator is therefore not a
parameter but the operator of `L` itself, `Stacks.Chow.invertibleChernCapOperator`, whose
component rule is `Stacks.Chow.firstChernComponentCycleRule` of `L` and whose only argument is
Stacks 02TI for `L` in every degree, supplied by
`Stacks.Chow.firstChernClassCap_factors` from
`Stacks.Chow.firstChernCapFactorsEverywhere`.

What remains carried is the family of clause (1) of Stacks 02U0, as a datum `D`, exactly as
`Stacks.Chow.chernClassCapFundamental` takes it; its existence is
`Stacks.Chow.exists_isChernClassFundamentalFamily`, which needs the surjectivity half of
Stacks 02TX.

The datum `D` concerns the *inputs* that define the first Chern class, not the classes
the conclusion compares: nothing below assumes that the two classes agree anywhere, nor that any
comparison map is an isomorphism. The two remaining parameters of the bundle — that `𝟙 X` is flat
of relative dimension `1 - 1 = 0`, and that its flat pullback factors through rational
equivalence — are *proved* here, as `Stacks.Chow.relativeDimension_identity` and
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_id`, so they are not hypotheses.

### Why the divisor class needs no section

`Stacks.Chow.firstChernClassCapFundamental` quantifies over no meromorphic section: on an integral
scheme an invertible module has a regular meromorphic section with nonzero generic value, and the
class of its divisor cycle is independent of the choice. So the right-hand side of Stacks 02U2 is
unconditional, and the comparison with the cap product of Stacks 02SO goes through
`Stacks.Chow.firstChernClassCapFundamental_eq` and
`Stacks.Chow.firstChernClassCapOfInvertible_fundamentalCycle_eq_mk`, which both describe their
class through one and the same section.

### Transports along equalities of degrees

Each summand of the relation 02U1 lands in `A_{n + (r-1) - r}(P)`, which for `r = 1` is
`A_{n + 0 - 1}(X)` — the same integer as `n - 1` but not the same term. The private lemmas below
isolate the resulting transports: `Stacks.Chow.chowGroupCast` and
`Stacks.Chow.chowGroupDegreeCast` are substitutions along an equality of degrees, so each one is
discharged by `subst`, and the equalities themselves compose away by
`Stacks.Chow.chowGroupCast_chowGroupCast`.

## References

* [Stacks Project, Tag 02U2](https://stacks.math.columbia.edu/tag/02U2)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02U1](https://stacks.math.columbia.edu/tag/02U1)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### Transports along an equality of degrees -/

section Cast

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q]


/-- The transport along an equality of a degree with itself is the identity. -/
private theorem chowGroupCast_self {k : ℤ} (h : k = k) (x : chowGroup C q k) :
    chowGroupCast C q h x = x := rfl


/-- The class of the cycle of a closed subscheme, transported along an equality of degrees, is the
class of the cycle of that subscheme in the new degree. -/
private theorem chowGroupCast_mk_cycleAssociatedToClosedSubscheme {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {k l : ℤ} (h : k = l) :
    chowGroupCast C q h (QuotientAddGroup.mk' (rationalEquivalences C q k)
        (cycleAssociatedToClosedSubscheme C q i k)) =
      QuotientAddGroup.mk' (rationalEquivalences C q l)
        (cycleAssociatedToClosedSubscheme C q i l) := by
  subst h; rfl

/-- Capping with the empty list of first Chern class cap operators is the identity. -/
private theorem iteratedChernCapOnChow_nil_apply (k : ℤ)
    (x : chowGroup C q (k + ((0 : ℕ) : ℤ))) :
    iteratedChernCapOnChow C q [] k x =
      chowGroupCast C q (show k + ((0 : ℕ) : ℤ) = k from by simp) x := by
  simp only [iteratedChernCapOnChow]
  rw [chowGroupDegreeCast_apply]
  rfl

/-- Capping with a one-element list of first Chern class cap operators is that operator. -/
private theorem iteratedChernCapOnChow_singleton_apply (O : ChernCapOperator C q) (k : ℤ)
    (x : chowGroup C q (k + ((1 : ℕ) : ℤ))) :
    iteratedChernCapOnChow C q [O] k x =
      O.capOnChow C q k (chowGroupCast C q (show k + ((1 : ℕ) : ℤ) = k + 1 from by simp) x) := by
  simp only [iteratedChernCapOnChow]
  rw [chowGroupDegreeCast_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    chowGroupDegreeCast_apply, AddMonoidHom.id_apply, chowGroupCast_chowGroupCast]

end Cast

/-! ### Flat pullback along the identity -/

/-- The identity morphism of a scheme is flat of relative dimension zero: it is locally
quasi-finite, and relative dimension zero is exactly local quasi-finiteness. -/
theorem relativeDimension_identity (X : Scheme.{u}) :
    AlgebraicGeometry.RelativeDimension (𝟙 X) 0 :=
  (AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero (𝟙 X)).mp inferInstance

/-- **Stacks 02S1 along the identity.** Flat pullback of `k`-cycles along `𝟙 X` carries cycles
rationally equivalent to zero to cycles rationally equivalent to zero, so the flat pullback of
Stacks 0FVK along `𝟙 X` exists; this is the case of an isomorphism,
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_of_isIso`. -/
theorem flatPullbackFactorsThroughRationalEquivalence_id (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (k : ℤ) :
    FlatPullbackFactorsThroughRationalEquivalence C sX sX (𝟙 X) (Category.id_comp sX) 0
      (relativeDimension_identity X) k :=
  flatPullbackFactorsThroughRationalEquivalence_of_isIso C sX sX (𝟙 X) (Category.id_comp sX)
    (relativeDimension_identity X) k

/-- **Flat pullback along the identity is the identity.** On `A_k(X)` the flat pullback of Stacks
0FVK along `𝟙 X` is the identity map, up to the transport `A_k(X) = A_{k+0}(X)` of degrees.

On cycles this is `Stacks.Chow.cycleGroupRestrict_eq_flatPullback`, restriction along the identity
viewed as an open immersion: the coefficient of the pullback at a point is the coefficient of the
cycle at its image, and the image is the point. -/
theorem flatPullbackChow_id (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (k : ℤ) (α : chowGroup C sX k) :
    flatPullbackChow C sX sX (𝟙 X) (Category.id_comp sX) 0 (relativeDimension_identity X) k
        (flatPullbackFactorsThroughRationalEquivalence_id C sX k) α =
      chowGroupCast C sX (show k = k + ((0 : ℕ) : ℤ) from by simp) α := by
  have key : ∀ c : CycleGroup C sX k,
      flatPullbackChow C sX sX (𝟙 X) (Category.id_comp sX) 0 (relativeDimension_identity X) k
          (flatPullbackFactorsThroughRationalEquivalence_id C sX k)
          (QuotientAddGroup.mk' (rationalEquivalences C sX k) c) =
        chowGroupCast C sX (show k = k + ((0 : ℕ) : ℤ) from by simp)
          (QuotientAddGroup.mk' (rationalEquivalences C sX k) c) := by
    intro c
    rw [flatPullbackChow_mk, chowGroupCast_mk]
    refine congrArg _ (Subtype.ext ?_)
    rw [val_cycleGroup_cast, ← cycleGroupRestrict_eq_flatPullback C sX sX (𝟙 X)
      (Category.id_comp sX) (relativeDimension_identity X) k c]
    exact Function.locallyFinsuppWithin.ext fun z ↦ by simp
  induction α using QuotientAddGroup.induction_on with
  | H c => exact key c

/-! ### The two summands of the relation 02U1 at `r = 1` -/

section Relation

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (n : ℤ)
  (twist : ChernCapOperator C p)

/-- **The summand `i = 0` of the relation 02U1 at `r = 1` on the bundle `(X, 𝟙 X)`.** It is the
flat pullback of a class of degree `n - 1` along `𝟙 X`, capped with no first Chern class, hence
the identity up to the transport of degrees. -/
private theorem projectiveBundleChernTerm_id_zero
    (α : chowGroup C p (n - ((1 - 0 : ℕ) : ℤ))) :
    projectiveBundleChernTerm C p p (𝟙 X) (Category.id_comp p) 1
        (relativeDimension_identity X) (flatPullbackFactorsThroughRationalEquivalence_id C p)
        twist n 0 (by omega) α =
      chowGroupCast C p (show n - ((1 - 0 : ℕ) : ℤ) =
        n + ((1 - 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) from by norm_num) α := by
  simp only [projectiveBundleChernTerm, projectiveBundlePullback, AddMonoidHom.coe_comp,
    Function.comp_apply, AddEquiv.coe_toAddMonoidHom, List.replicate]
  rw [iteratedChernCapOnChow_nil_apply, chowGroupCast_chowGroupCast, flatPullbackChow_id,
    chowGroupCast_chowGroupCast]

/-- **The summand `i = 1` of the relation 02U1 at `r = 1` on the bundle `(X, 𝟙 X)`.** It is the
flat pullback of a class of degree `n` along `𝟙 X`, capped once with the first Chern class of the
twist, hence that cap product up to the transport of degrees. -/
private theorem projectiveBundleChernTerm_id_one
    (β : chowGroup C p (n - ((1 - 1 : ℕ) : ℤ))) :
    projectiveBundleChernTerm C p p (𝟙 X) (Category.id_comp p) 1
        (relativeDimension_identity X) (flatPullbackFactorsThroughRationalEquivalence_id C p)
        twist n 1 (by omega) β =
      twist.capOnChow C p (n + ((1 - 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
        (chowGroupCast C p (show n - ((1 - 1 : ℕ) : ℤ) =
          n + ((1 - 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) + 1 from by norm_num) β) := by
  simp only [projectiveBundleChernTerm, projectiveBundlePullback, AddMonoidHom.coe_comp,
    Function.comp_apply, AddEquiv.coe_toAddMonoidHom, List.replicate_one]
  rw [iteratedChernCapOnChow_singleton_apply, chowGroupCast_chowGroupCast, flatPullbackChow_id,
    chowGroupCast_chowGroupCast]

end Relation

/-! ### The cap product of Stacks 02SO on the fundamental cycle -/

section Divisor

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] (n : ℤ) (hn : schemeDeltaDimension C p = (n : EInt)) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The cap product of Stacks 02SO on the fundamental cycle is the Weil divisor class of
Stacks 02SJ (2).** On an integral scheme `X` of delta-dimension `n`, locally of finite type over
the base, the cap product `c₁(L) ∩ -` of `Stacks.Chow.firstChernClassCapOfInvertible`, evaluated
at the fundamental cycle `[X]`, is the class `c₁(L) ∩ [X] ∈ CH_{n-1}(X)` of
`Stacks.Chow.firstChernClassCapFundamental`.

The two were built from the same material and are compared through one section: an invertible
module on an integral scheme has a regular meromorphic section with nonzero generic value, and
both sides are the class of its divisor cycle, by
`Stacks.Chow.firstChernClassCapOfInvertible_fundamentalCycle_eq_mk` and
`Stacks.Chow.firstChernClassCapFundamental_eq` respectively. -/
theorem firstChernClassCapOfInvertible_fundamentalCycle_eq_firstChernClassCapFundamental :
    firstChernClassCapOfInvertible C p (n - 1) L
        (cycleAssociatedToClosedSubscheme C p (𝟙 X) (n - 1 + 1)) =
      firstChernClassCapFundamental C p n hn L := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨σ, hσ, hv⟩ := ChernCap42.exists_isRegularMeromorphicSection_of_isIntegral X L
  rw [firstChernClassCapFundamental_eq C p n hn L σ hσ,
    firstChernClassCapOfInvertible_fundamentalCycle_eq_mk C p hn L (genericValue L σ) hv]
  rfl

/-- The same statement with the degree `n - 1` presented through an equal but syntactically
different integer, which is the degree the relation 02U1 produces. -/
private theorem firstChernClassCap_fundamentalCycle_eq_cast {d : ℤ} (hd : d = n - 1) :
    firstChernClassCap C p d (firstChernComponentCycleRule C p d L)
        (cycleAssociatedToClosedSubscheme C p (𝟙 X) (d + 1)) =
      chowGroupCast C p hd.symm (firstChernClassCapFundamental C p n hn L) := by
  subst hd
  rw [chowGroupCast_self]
  exact firstChernClassCapOfInvertible_fundamentalCycle_eq_firstChernClassCapFundamental C p n hn L

/-! ### Stacks 02U2 -/

omit [IsIntegral X] in
/-- Stacks 02TI for `L` in every degree: the cap product with the first Chern class of `L`
factors through rational equivalence (`Stacks.Chow.firstChernCapFactorsEverywhere`). -/
theorem firstChernClassCap_factors :
    ∀ k : ℤ, FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k L) :=
  fun k ↦ firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k p L

/-- **Stacks 02U2.** Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of
finite type over `S`, integral and of delta-dimension `n`, and let `L` be an invertible
`𝒪_X`-module. Then the first Chern class of `L` in the sense of Stacks 02U0 — the member `c_1` of
the family of clause (1), read on the projective bundle of `L`, which is `X` itself with
projection `𝟙 X` and twist `L` — equals the Weil divisor class of `L` of Stacks 02SJ (2).

The proof is the source's. At `r = 1` the relation 02U1 reads
`c₁(L) ∩ π^*c_0 = π^*c_1` on the bundle; the bundle is `X` and `π` is the identity, so its flat
pullback is the identity (`Stacks.Chow.flatPullbackChow_id`) and the relation says
`c_1 = c₁(L) ∩ c_0`. The normalisation `c_0 = [X]` turns the right-hand side into the cap product
of Stacks 02SO on the fundamental cycle, which is the Weil divisor class by
`Stacks.Chow.firstChernClassCapOfInvertible_fundamentalCycle_eq_firstChernClassCapFundamental`.

The twist operator is `Stacks.Chow.invertibleChernCapOperator` of `L`, the source's
`O_{𝐏(L)}(1) = L`, built from Stacks 02TI for `L`
(`Stacks.Chow.firstChernClassCap_factors`); the family `D` of clause (1)
of Stacks 02U0 is a datum, quantified over rather than chosen. It is not an assumption
about the two classes being compared. -/
@[stacks 02U2 "the projective bundle of the rank-one module L is the pair (X, 𝟙 X) and its \
  twist O_P(1) is L itself, so the twist operator is CONSTRUCTED from L rather than assumed. \
  The family of clause (1) of Stacks 02U0 is quantified over as a datum, its existence needing \
  the surjectivity half of Stacks 02TX; it is not an assumption about the classes compared"]
theorem chernClassCapFundamental_one_eq_firstChernClassCapFundamental
    (D : ChernClassFundamentalFamily C p p (𝟙 X) (Category.id_comp p) 1
      (relativeDimension_identity X) (flatPullbackFactorsThroughRationalEquivalence_id C p)
      (invertibleChernCapOperator C p L (firstChernClassCap_factors C p L)) n) :
    chernClassCapFundamental C p p (𝟙 X) (Category.id_comp p) 1
        (relativeDimension_identity X) (flatPullbackFactorsThroughRationalEquivalence_id C p)
        (invertibleChernCapOperator C p L (firstChernClassCap_factors C p L)) n D ⟨1, by omega⟩ =
      firstChernClassCapFundamental C p n hn L := by
  -- the relation 02U1, with its two summands separated
  have h : projectiveBundleChernTerm C p p (𝟙 X) (Category.id_comp p) 1
        (relativeDimension_identity X) (flatPullbackFactorsThroughRationalEquivalence_id C p)
        (invertibleChernCapOperator C p L (firstChernClassCap_factors C p L))
          n 0 (by omega) (D.1 ⟨1, by omega⟩) =
      projectiveBundleChernTerm C p p (𝟙 X) (Category.id_comp p) 1
        (relativeDimension_identity X) (flatPullbackFactorsThroughRationalEquivalence_id C p)
        (invertibleChernCapOperator C p L (firstChernClassCap_factors C p L))
          n 1 (by omega) (D.1 ⟨0, by omega⟩) := by
    have hrel : ∑ i : Fin 2, (-1 : ℤ) ^ i.val •
        projectiveBundleChernTerm C p p (𝟙 X) (Category.id_comp p) 1
          (relativeDimension_identity X) (flatPullbackFactorsThroughRationalEquivalence_id C p)
          (invertibleChernCapOperator C p L (firstChernClassCap_factors C p L))
            n i.val (Nat.lt_succ_iff.mp i.isLt)
          (D.1 ⟨1 - i.val, by omega⟩) = 0 := D.2.2
    rw [Fin.sum_univ_two] at hrel
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
      add_neg_eq_zero] at hrel
    exact hrel
  rw [projectiveBundleChernTerm_id_zero, projectiveBundleChernTerm_id_one] at h
  -- the normalisation `c_0 = [X]`, solved for `c_0`
  have h0 : chowGroupCast C p (show n - ((⟨0, by omega⟩ : Fin 2) : ℤ) = n from by simp)
      (D.1 ⟨0, by omega⟩) =
      QuotientAddGroup.mk' (rationalEquivalences C p n)
        (cycleAssociatedToClosedSubscheme C p (𝟙 X) n) := D.2.1
  have h0' : D.1 ⟨0, by omega⟩ =
      chowGroupCast C p (show (n : ℤ) = n - ((⟨0, by omega⟩ : Fin 2) : ℤ) from by simp)
        (QuotientAddGroup.mk' (rationalEquivalences C p n)
          (cycleAssociatedToClosedSubscheme C p (𝟙 X) n)) := by
    rw [← h0, chowGroupCast_chowGroupCast, chowGroupCast_self]
  rw [h0', chowGroupCast_chowGroupCast, chowGroupCast_mk_cycleAssociatedToClosedSubscheme] at h
  -- the cap product of `L` on the fundamental cycle is the Weil divisor class of `L`
  have hd : n + ((1 - 1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) = n - 1 := by norm_num
  have hcap : ∀ (d : ℤ) (x : chowGroup C p (d + 1)),
      (invertibleChernCapOperator C p L (firstChernClassCap_factors C p L)).capOnChow C p d x =
        firstChernClassCapOnChow C p d (firstChernComponentCycleRule C p d L)
          (firstChernClassCap_factors C p L d) x :=
    fun _ _ ↦ rfl
  rw [hcap, firstChernClassCapOnChow_mk,
    firstChernClassCap_fundamentalCycle_eq_cast C p n hn L hd] at h
  exact (chowGroupCast C p hd.symm).injective h

end Divisor

end Stacks.Chow

end
