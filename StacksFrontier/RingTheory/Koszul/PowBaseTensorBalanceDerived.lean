module

public import StacksFrontier.RingTheory.Koszul.PowBaseTensorBalanceLadder
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# The first step of Tag 0GZJ: balancing the two Koszul derived tensor towers

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `K_m = R⟨ξ₁, …, ξ_r⟩` be the Koszul
differential graded algebra with `d ξᵢ = fᵢ ^ m`, let `(B, d)` be a differential graded
`R`-algebra and let `(M_m)` be an inverse system of differential graded `K_m`-modules with
semilinear transition homomorphisms `M_{m+1} ⟶ M_m|_τ` — recorded, as everywhere in this
development, as
a family of differential graded `(K_m, B)`-bimodules `P_k` indexed from a base `b ≥ 1` by
`k ↦ P_k = M_{b+k}`, together with homomorphisms `P_{k+1} ⟶ P_k|_τ`.

The proof of Tag 0GZJ begins by observing that
$$
M_m \otimes_R^{\mathbf L} K_t = M_m \otimes_{K_m}^{\mathbf L} (K_m \otimes_R^{\mathbf L} K_t)
  = M_m \otimes_{K_m}^{\mathbf L} (K_m \otimes_R K_t),
$$
and only then invokes the pro-isomorphism of `({}_mK_t)` with `(K_m ⊗_R K_t)` to replace the
right-hand side by `M_m ⊗_{K_m}^𝐋 K_t`. **This file proves that first observation**, in the three
strengths in which it is used: objectwise, as an isomorphism of the two inverse systems, and as
an isomorphism of their derived limits. The replacement of `K_m ⊗_R K_t` by `K_t`, which is the
second step and rests on Tag 0GZ7, is not touched here; consequently nothing below mentions
`{}_mK_t`, and the conclusion is about the tower `(M_m ⊗_{K_m}^𝐋 (K_m ⊗_R K_t))` rather than
about `(M_m ⊗_{K_m}^𝐋 K_t)`.

The two inverse systems being compared are already constructed:
`Koszul.powBaseTensorDerivedTensorTower` is `k ↦ P_k ⊗_{K_{b+k}}^𝐋 (K_{b+k} ⊗_R K_t)` and
`Koszul.powBaseDegreeZeroDerivedTensorTower` is `k ↦ P_k ⊗_R^𝐋 K_t`, the latter a tower over the
single algebra `R` placed in degree zero. Both are towers of derived tensor products in the sense
of `DifferentialGraded.Bimodule.DerivedTensorTower`, whose modules are orthogonal on the left to
the acyclic modules, so each term of each is computed by the corresponding plain tensor product;
and `Koszul.powBaseTensorBalanceObjIso` together with
`Koszul.powBaseTensorBalanceObjIso_ladder` is an isomorphism of the two *plain* towers of
differential graded `B`-modules. The whole content of this file is to feed that pair to
`DifferentialGraded.Bimodule.DerivedTensorTower.towerNatIso` and
`DifferentialGraded.Bimodule.DerivedTensorTower.nonempty_iso_of_isDerivedLimit`.

## Main definitions

* `Koszul.powBaseTensorBalanceDerivedObjIso`: **the first observation of Tag 0GZJ**,
  `M_m ⊗_{K_m}^𝐋 (K_m ⊗_R K_t) ≅ M_m ⊗_R^𝐋 K_t` in `D(B, d)`, one `m` at a time.
* `Koszul.powBaseTensorBalanceTowerIso`: the same as an isomorphism of the two inverse systems,
  i.e. of functors `ℕᵒᵖ ⥤ D(B, d)`.
* `Koszul.powBaseTensorBalanceProIso`: the two inverse systems are pro-isomorphic, with both
  reindexings the identity.

## Main results

* `Koszul.nonempty_iso_of_isDerivedLimit_powBaseTensorBalance`: **the first observation of
  Tag 0GZJ passed to derived limits** — `R lim (M_m ⊗_R^𝐋 K_t)` and
  `R lim (M_m ⊗_{K_m}^𝐋 (K_m ⊗_R K_t))` are isomorphic in `D(B, d)`.

## Implementation notes

*Why an isomorphism of towers and not merely of terms.* Passing to derived limits needs the
comparison to be compatible with the transition maps, and a derived tensor product is not a
functor of its arguments in a way that supplies that compatibility for free: the identification
of a derived tensor product with a plain one is only available at a module orthogonal to the
acyclic ones, and the transition map of the derived tower is built from the comparison of the
derived tensor functors. That compatibility is exactly what
`Koszul.powBaseTensorBalanceObjIso_ladder` supplies, at the level of plain tensor products of
differential graded `B`-modules, and
`DifferentialGraded.Bimodule.DerivedTensorTower.towerNatIso` promotes it. No naturality in the
derived category is assumed anywhere.

*The derived limits.* `R lim` is `CategoryTheory.Pretriangulated.IsDerivedLimit` (Tag 08TC), a
predicate rather than a construction, because a derived limit is pinned only up to a non-unique
isomorphism; accordingly the conclusion is that any derived limit of the one tower is isomorphic
to any derived limit of the other, and the products the predicate refers to are hypotheses.

So `hK` and `hK'` are not a result borrowed from another tag: they are Tag 08TC's defining
property, which is how the source spells `R lim` on the two sides of its equation, and they are
never vacuous — `CategoryTheory.Pretriangulated.exists_isDerivedLimit` produces a derived limit of
any inverse system whose product exists, which is Tag 08TC's "by TR1 a derived limit exists as
soon as `∏ K_n` exists". The `Nonempty` conclusion is the source's own strength too: Tag 08TC
calls a derived limit unique up to "(non-unique) isomorphism", and Tag 0H9L, which this step
feeds, concludes that a pro-isomorphism "can be used to produce a (non-canonical) isomorphism".
There is no canonical map here for the statement to be hiding.

*The indexing and the hypothesis on `t`.* The source introduces `{}_mK_t` only for `m ≥ t`,
which is where `K_m → K_t` exists, and a derived limit is unchanged by passing to a cofinal
subsystem; the towers here are therefore indexed by `k ↦ b + k` from an arbitrary base `b ≥ 1`.
The source's standing `t ≥ 1` is not needed for this step — the comparison of the two plain
towers holds for every `t` — so it is not assumed, which only strengthens the statements.

*What is quantified over.* Beyond `f`, `t` and the base `b`, the only data are the differential
graded algebra `B` and the inverse system `(P_k, P_{k+1} ⟶ P_k|_τ)`, which is the object of
`D(ℕ, (K_m))` that Tag 0GZJ is stated for. In the source `B` is `R` placed in degree zero, so
that `D(B, d)` is `D(R)`; leaving it arbitrary is a generalization.

## References

* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) is the statement whose
  first step this is, and [Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7) is the input of
  its second step.
* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) is the derived tensor
  product, [Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2) its comparison with the plain
  tensor product, [Tag 08TC](https://stacks.math.columbia.edu/tag/08TC) the derived limit and
  [Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L) the comparison of the derived limits of
  pro-isomorphic inverse systems.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule
  DifferentialGraded.Bimodule

variable {R : Type u} [CommRing R] {r : ℕ} {B : DifferentialGradedAlgebra.{u, u} R}
  (f : Fin r → R) (t : ℕ) {b : ℕ} (hb : 1 ≤ b)
  (bimod : ∀ k : ℕ, Bimodule (oppAlgebra (powAlgebra f (b + k))) B)
  (bimodTrans : ∀ k : ℕ,
    bimod (k + 1) ⟶ Bimodule.restrictLeft (powSuccTransition f hb k) (bimod k))

/-- **The first step of the proof of Tag 0GZJ, one index at a time:**
`M_m ⊗_{K_m}^𝐋 (K_m ⊗_R K_t) ≅ M_m ⊗_R^𝐋 K_t` in `D(B, d)`, for `m = b + k`.

Both sides are computed by their plain tensor products, because `K_m ⊗_R K_t` and `K_t` are
orthogonal on the left to the acyclic modules, and the plain tensor products are identified by
`Koszul.powBaseTensorBalanceObjIso`. -/
@[stacks 0GZJ "the identification M_n ⊗^𝐋_R K_t = M_n ⊗^𝐋_{K_n} (K_n ⊗_R K_t), objectwise"]
def powBaseTensorBalanceDerivedObjIso (k : ℕ) :
    (powBaseTensorDerivedTensorTower f t hb bimod bimodTrans).obj k ≅
      (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).obj k :=
  DerivedTensorTower.objIso _ _ (powBaseTensorBalanceObjIso f t hb bimod bimodTrans) k

/-- **The first step of the proof of Tag 0GZJ as an isomorphism of inverse systems:** the tower
`(M_m ⊗_{K_m}^𝐋 (K_m ⊗_R K_t))` and the tower `(M_m ⊗_R^𝐋 K_t)` are isomorphic as functors
`ℕᵒᵖ ⥤ D(B, d)`, not merely termwise.

This is `DifferentialGraded.Bimodule.DerivedTensorTower.towerNatIso` applied to the isomorphism
`Koszul.powBaseTensorBalanceObjIso` of the plain towers and the commuting ladder
`Koszul.powBaseTensorBalanceObjIso_ladder` it satisfies. -/
def powBaseTensorBalanceTowerIso :
    (powBaseTensorDerivedTensorTower f t hb bimod bimodTrans).tower ≅
      (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).tower :=
  DerivedTensorTower.towerNatIso _ _ (powBaseTensorBalanceObjIso f t hb bimod bimodTrans)
    (powBaseTensorBalanceObjIso_ladder f t hb bimod bimodTrans)

/-- The components of `Koszul.powBaseTensorBalanceTowerIso` are the objectwise identifications
`Koszul.powBaseTensorBalanceDerivedObjIso`. -/
@[simp] theorem powBaseTensorBalanceTowerIso_hom_app (k : ℕ) :
    (powBaseTensorBalanceTowerIso f t hb bimod bimodTrans).hom.app (op k) =
      (powBaseTensorBalanceDerivedObjIso f t hb bimod bimodTrans k).hom :=
  rfl

/-- **The two inverse systems of the first step of Tag 0GZJ are pro-isomorphic**, with both
reindexings the identity, being isomorphic. -/
def powBaseTensorBalanceProIso :
    InverseSequence.ProIso (powBaseTensorDerivedTensorTower f t hb bimod bimodTrans).tower
      (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).tower :=
  DerivedTensorTower.towerProIso _ _ (powBaseTensorBalanceObjIso f t hb bimod bimodTrans)
    (powBaseTensorBalanceObjIso_ladder f t hb bimod bimodTrans)

/-- **The first step of the proof of Tag 0GZJ, passed to derived limits:**
`R lim (M_m ⊗_R^𝐋 K_t) = R lim (M_m ⊗_{K_m}^𝐋 (K_m ⊗_R K_t))` in `D(B, d)`.

The isomorphism is not canonical — a derived limit is pinned only up to a non-unique isomorphism
— so the conclusion is stated for an arbitrary derived limit of each tower. This is Tag 0H9L
applied to the pro-isomorphism `Koszul.powBaseTensorBalanceProIso`.

Replacing `K_m ⊗_R K_t` by `K_t` on the right-hand side, which turns this into the statement of
Tag 0GZJ, is the second step of the source's proof and is not done here. -/
@[stacks 0GZJ "the identification M_n ⊗^𝐋_R K_t = M_n ⊗^𝐋_{K_n} (K_n ⊗_R K_t), passed to R lim"]
theorem nonempty_iso_of_isDerivedLimit_powBaseTensorBalance
    [HasProduct fun k : ℕ =>
      (powBaseTensorDerivedTensorTower f t hb bimod bimodTrans).tower.obj (op k)]
    [HasProduct fun k : ℕ =>
      (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).tower.obj (op k)]
    (K K' : DifferentialGradedModule.derivedCategory' B)
    (hK : Pretriangulated.IsDerivedLimit
      (powBaseTensorDerivedTensorTower f t hb bimod bimodTrans).tower K)
    (hK' : Pretriangulated.IsDerivedLimit
      (powBaseDegreeZeroDerivedTensorTower f t hb bimod bimodTrans).tower K') :
    Nonempty (K ≅ K') :=
  DerivedTensorTower.nonempty_iso_of_isDerivedLimit _ _
    (powBaseTensorBalanceObjIso f t hb bimod bimodTrans)
    (powBaseTensorBalanceObjIso_ladder f t hb bimod bimodTrans) K K' hK hK'

end Koszul

end
