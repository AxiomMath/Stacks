module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CompletedFormsShape

/-!
# The comparison of the two shapes of the completed forms is linear over the completed ring

`Crystalline.completedFormsShapeEquiv` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedFormsShape.lean` identifies the
two shapes of the completed forms in positive exterior degree,

`AdicCompletion_B (⋀ⁱ_B N) ≃ AdicCompletion_{B̂} (⋀ⁱ_{B̂} N̂)`,

and identifies them as **additive** groups only.  Both sides are modules over the completed ring
`B̂` — the right one along the identity of `B̂`, the left one along `AdicCompletion.module` — and
the module documentation of that file records the compatibility of the comparison with those two
actions as one of the two things missing before the `hcolumns` hypothesis of
`...SmallSite.computes07LG_of_doubleComplex` could be discharged.  **This module proves it**, as
`Crystalline.completedFormsShapeEquiv_smul`, and upgrades the comparison to
`Crystalline.completedFormsShapeLinearEquiv`.

The other half — naturality in `B`, without which the comparison is not a morphism of
cosimplicial modules and the null homotopy of [Stacks, Lemma 60.19.1, Tag 07LA] does not
transport along it — is **not** proved here; it is proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/CompletedFormsShapeNatural.lean`, as
`Crystalline.completedFormsShapeEquiv_natural`.

## Why it is true

Everything is local to a level `Iᵏ`, and the two actions are computed there by two *different*
lemmas, which is the whole asymmetry of the statement: on the left the scalar acts through its
own level, `AdicCompletion.smul_eval` giving `(r • x).val k = r.val k • x.val k` with
`r.val k ∈ B ⧸ Iᵏ`, while on the right the scalar is an element of the base ring of the ideal and
acts directly, `AdicCompletion.val_smul_apply` giving `(r • y).val k = r • y.val k`.

So what has to be compared, at the level `k`, is the action of `r.val k ∈ B ⧸ Iᵏ` with the action
of `r ∈ B̂`, and `Crystalline.completedFormsShapeLevelEquiv` is linear over `B` and over nothing
larger.  The bridge is that `B → B̂ ⧸ (I B̂)ᵏ` is surjective — which is
`Crystalline.surjective_algebraMap_adicCompletion_quotient`, already proved for exactly this level
comparison: a representative `a : B` of `r.val k` has `a - r ∈ (I B̂)ᵏ`
(`Crystalline.algebraMap_sub_mem_map_pow`), and `(I B̂)ᵏ` annihilates the level `k` of the right
hand side, so `a` and `r` act on it identically.  Over `B` the level comparison is linear, and
that is the identity wanted.

No hypothesis beyond the `I.FG` and `0 < i` the comparison itself carries is needed.

## Main definitions

* `Crystalline.completedFormsShapeLinearEquiv` — **the comparison of the two shapes of the
  completed forms, as a `B̂`-linear equivalence.**

## Main results

* `Crystalline.smul_quotient_eq_zero_of_mem` — an element of an ideal annihilates the quotient of
  a module by that ideal.
* `Crystalline.algebraMap_sub_mem_map_pow` — **a representative in `B` of the level `k` of an
  element of `B̂` differs from it by an element of `(I B̂)ᵏ`.**  This is the content of
  `Crystalline.surjective_algebraMap_adicCompletion_quotient` with the representative named.
* `Crystalline.completedFormsShapeLevelEquiv_smul` — the level comparison carries the action of
  the level of a scalar to the action of the scalar itself.
* `Crystalline.completedFormsShapeEquiv_smul` — **the comparison of the two shapes is
  `B̂`-linear.**

## What is and is not proved

Everything stated is proved.  **No tag attribute is placed**: this is one identification inside
the proof of [Stacks, Proposition 60.21.3, Tag 07LG] and is not a clause of any tag's statement.
In particular [Stacks, Lemma 60.19.1, Tag 07LA] is **not** transported along the comparison here,
and the `hcolumns` hypothesis of `...SmallSite.computes07LG_of_doubleComplex` is **not**
discharged.

## References

* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

@[expose] public section

namespace Crystalline

/-! ### Two lemmas about the levels of a completion -/

/-- **An element of an ideal annihilates the quotient of a module by that ideal.**
`Crystalline.smul_quotient_eq_zero` is the same statement for a power of the ideal `(p)`. -/
public theorem smul_quotient_eq_zero_of_mem {S : Type*} [CommRing S] {K : Ideal S} {Q : Type*}
    [AddCommGroup Q] [Module S Q] {c : S} (hc : c ∈ K)
    (z : Q ⧸ (K • (⊤ : Submodule S Q))) : c • z = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul hc Submodule.mem_top

section Level

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- **A representative in `R` of the level `k` of an element of `R̂` differs from it by an element
of `(I R̂)ᵏ`.**

This is the content of `Crystalline.surjective_algebraMap_adicCompletion_quotient` with the
representative named rather than existentially quantified, which is what the comparison of the
two actions on a level needs: the element of `R` and the element of `R̂` act on the level `k` of
any module identically precisely because their difference lies in `(I R̂)ᵏ`. -/
public theorem algebraMap_sub_mem_map_pow (hI : I.FG) (k : ℕ) (r : AdicCompletion I R) (a : R)
    (ha : Submodule.Quotient.mk a = r.val k) :
    algebraMap R (AdicCompletion I R) a - r ∈
      I.map (algebraMap R (AdicCompletion I R)) ^ k := by
  have hker : algebraMap R (AdicCompletion I R) a - r ∈ (AdicCompletion.eval I R k).ker := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    show AdicCompletion.eval I R k (AdicCompletion.of I R a) = AdicCompletion.eval I R k r
    rw [AdicCompletion.eval_of, AdicCompletion.eval_apply, ← ha]
    rfl
  rwa [← AdicCompletion.pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map,
    Ideal.map_pow] at hker

end Level

/-! ### The comparison is linear over the completed ring -/

section Linear

variable {R : Type*} [CommRing R] {I : Ideal R} {N : Type*} [AddCommGroup N] [Module R N]

/-- **The level comparison carries the action of the level of a scalar to the action of the
scalar itself.**

`Crystalline.completedFormsShapeLevelEquiv` is linear over `R`, and the two actions to be
compared are that of `r.val k ∈ R ⧸ Iᵏ` on the left and that of `r ∈ R̂` on the right.  A
representative `a : R` of `r.val k` acts on the left exactly as `r.val k` does, and on the right
exactly as `r` does, because the two differ by an element of `(I R̂)ᵏ`
(`Crystalline.algebraMap_sub_mem_map_pow`) and `(I R̂)ᵏ` annihilates the level. -/
public theorem completedFormsShapeLevelEquiv_smul (hI : I.FG) (i k : ℕ) (hi : 0 < i)
    (r : AdicCompletion I R)
    (z : ↥(⋀[R]^i N) ⧸ (I ^ k • (⊤ : Submodule R ↥(⋀[R]^i N)))) :
    completedFormsShapeLevelEquiv hI i k hi (r.val k • z) =
      r • completedFormsShapeLevelEquiv hI i k hi z := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective (I ^ k • (⊤ : Submodule R R)) (r.val k)
  have hsmul : completedFormsShapeLevelEquiv hI i k hi (r.val k • z) =
      a • completedFormsShapeLevelEquiv hI i k hi z := by
    rw [← ha]
    exact (completedFormsShapeLevelEquiv hI i k hi).map_smul a z
  rw [hsmul, ← IsScalarTower.algebraMap_smul (AdicCompletion I R) a, ← sub_eq_zero, ← sub_smul]
  exact smul_quotient_eq_zero_of_mem (algebraMap_sub_mem_map_pow hI k r a ha) _

/-- **The comparison of the two shapes of the completed forms is linear over the completed
ring.**

The two actions are computed on a level by two different lemmas — `AdicCompletion.smul_eval` on
the left, where the scalar acts through its own level, and `AdicCompletion.val_smul_apply` on the
right, where it acts directly — and what remains after that is
`Crystalline.completedFormsShapeLevelEquiv_smul`. -/
public theorem completedFormsShapeEquiv_smul (hI : I.FG) (i : ℕ) (hi : 0 < i)
    (r : AdicCompletion I R) (x : AdicCompletion I ↥(⋀[R]^i N)) :
    completedFormsShapeEquiv hI i hi (r • x) = r • completedFormsShapeEquiv hI i hi x := by
  refine AdicCompletion.ext fun k => ?_
  rw [completedFormsShapeEquiv_val, AdicCompletion.smul_eval, AdicCompletion.val_smul_apply,
    completedFormsShapeEquiv_val]
  exact completedFormsShapeLevelEquiv_smul hI i k hi r (x.val k)

/-- **The two shapes of the completed forms agree as modules over the completed ring**, in
positive exterior degree:

`AdicCompletion_B (⋀ⁱ_B N) ≃ₗ[B̂] AdicCompletion_{B̂} (⋀ⁱ_{B̂} N̂)`.

This is `Crystalline.completedFormsShapeEquiv` with the `B̂`-linearity
`Crystalline.completedFormsShapeEquiv_smul` added; it has the same underlying function, so
`Crystalline.completedFormsShapeEquiv_of_ιMulti` pins it down on wedges just as well. -/
public noncomputable def completedFormsShapeLinearEquiv (hI : I.FG) (i : ℕ) (hi : 0 < i) :
    AdicCompletion I ↥(⋀[R]^i N) ≃ₗ[AdicCompletion I R]
      AdicCompletion (I.map (algebraMap R (AdicCompletion I R)))
        ↥(⋀[AdicCompletion I R]^i (AdicCompletion I N)) :=
  { completedFormsShapeEquiv hI i hi with
    map_smul' := completedFormsShapeEquiv_smul hI i hi }

/-- The `B̂`-linear comparison of the two shapes is the comparison. -/
@[simp]
public theorem completedFormsShapeLinearEquiv_apply (hI : I.FG) (i : ℕ) (hi : 0 < i)
    (x : AdicCompletion I ↥(⋀[R]^i N)) :
    completedFormsShapeLinearEquiv hI i hi x = completedFormsShapeEquiv hI i hi x := rfl

end Linear

end Crystalline

end
