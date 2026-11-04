module

public import StacksFrontier.Algebra.Group.EllTorsionField
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingPicardExactness
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingPicard

/-!
# The effect of one elementary step on the `ℓ`-torsion of the Picard group

Let `k` be an algebraically closed field and let `ℓ` be a prime different from the
characteristic of `k`, that is, with `(ℓ : k) ≠ 0`. The proof of [Stacks, Tag 0C20] factors the
normalization of a curve as in [Stacks, Tag 0C1L] and runs an induction along the factorization.
[Stacks, Tag 0C1M] and [Stacks, Tag 0C1N] say that each step `f : X' ⟶ X` of that factorization
is of one of three kinds, and give the effect of each on the Picard group. This file computes the
effect of each on `dim_{F_ℓ} Pic[ℓ]`, which is what the induction actually tracks:

1. the glueing of two points lying on **different** connected components of `X'`: the Picard
   groups are isomorphic, so the dimension does not change;
2. the glueing of two points lying on the **same** connected component of `X'`, with `X'`
   proper: there is a short exact sequence `0 ⟶ k^* ⟶ Pic(X) ⟶ Pic(X') ⟶ 0`, and since `k^*`
   is `ℓ`-divisible with `k^*[ℓ]` of order `ℓ`, the dimension **drops by one** on passing from
   `X` to `X'`;
3. the squishing of a tangent vector, with `X'` proper and reduced: there is a short exact
   sequence `0 ⟶ (k,+) ⟶ Pic(X) ⟶ Pic(X') ⟶ 0`, and since `(k,+)` is `ℓ`-divisible with
   trivial `ℓ`-torsion, the dimension does not change.

These are the three lines of the source's table, and the only place where `ℓ ≠ char k` is used.
The dimension is `Module.rank` over `ZMod ℓ`, a cardinal, so that nothing has to be assumed
finite-dimensional: the finiteness of `dim_{F_ℓ} Pic(X)[ℓ]` in [Stacks, Tag 0C20] comes from
[Stacks, Tag 0C1Z] at the far end of the factorization, which is not an input here.

No `@[stacks]` attribute is registered: these statements are the arithmetic of the induction of
Tag 0C20 rather than a clause of any of 0C1M, 0C1N or 0C20 itself.

## Main results

* `Stacks.PicardTorsionStep.rank_torsionBy_picard_eq_of_ne_connectedComponents` — case (1).
* `Stacks.PicardTorsionStep.rank_torsionBy_picard_eq_one_add_of_connectedComponents_eq` —
  case (2).
* `Stacks.PicardTorsionStep.rank_torsionBy_picard_eq_of_isSquishingTangentVector` — case (3).

## References

* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
* [Stacks Project, Tag 0C1M](https://stacks.math.columbia.edu/tag/0C1M)
* [Stacks Project, Tag 0C1N](https://stacks.math.columbia.edu/tag/0C1N)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.PicardTorsionStep

variable {k : Type u} [Field k] [IsAlgClosed k] {X' X : Scheme.{u}}
  [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]

/-! ### Glueing two points on different connected components -/

/-- **Case (1) of the induction of [Stacks, Tag 0C20]: glueing two points on different
connected components does not change the `ℓ`-torsion of the Picard group.** The glueing
homomorphism is zero by
`Stacks.GluePicard.picardGluingHom_eq_zero_of_ne_connectedComponents`, so by exactness pullback
`Pic(X) ⟶ Pic(X')` is injective, and it is surjective by
`Stacks.GluePicard.surjective_schemePullbackClassHom`; an isomorphism of abelian groups induces
an isomorphism of `ℓ`-torsion.

No properness or reducedness is needed: unlike cases (2) and (3), the left-hand term of the
sequence is zero here for a reason internal to the glueing. -/
theorem rank_torsionBy_picard_eq_of_ne_connectedComponents (ℓ : ℕ) [Fact ℓ.Prime]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b)
    (hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) ≠
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k))) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X') (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) =
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X') (ℓ : ℤ)) :=
  Stacks.EllTorsion.rank_torsionBy_eq_of_eq_zero ℓ
    (fun c => by
      rw [Stacks.GluePicard.picardGluingHom_eq_zero_of_ne_connectedComponents f a b h hab]
      exact AddMonoidHom.zero_apply c)
    (Stacks.GluePicard.exact_picardGluingHom_schemePullbackClassHom f a b h)
    (Stacks.GluePicard.surjective_schemePullbackClassHom f a b h)

/-! ### Glueing two points on the same connected component -/

/-- **Case (2) of the induction of [Stacks, Tag 0C20]: glueing two points on the same connected
component of a proper `X'` raises the dimension of the `ℓ`-torsion of the Picard group by
one.** The sequence `0 ⟶ k^* ⟶ Pic(X) ⟶ Pic(X') ⟶ 0` is exact, `k^*` is `ℓ`-divisible, and
`k^*[ℓ]` is the group of `ℓ`-th roots of unity, of order `ℓ`. -/
theorem rank_torsionBy_picard_eq_one_add_of_connectedComponents_eq (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0) (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) [IsProper (X' ↘ Spec (.of k))]
    (hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) =
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k))) :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X') (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) =
      1 + Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X') (ℓ : ℤ)) := by
  have hp := (Fact.out : ℓ.Prime)
  have : NeZero ℓ := ⟨hp.ne_zero⟩
  exact Stacks.EllTorsion.rank_torsionBy_eq_one_add_of_card ℓ
    (Stacks.EllTorsion.card_torsionBy_additive_units k ℓ hℓ)
    (Stacks.GluePicard.injective_picardGluingHom_of_connectedComponents_eq f a b h hab)
    (Stacks.GluePicard.exact_picardGluingHom_schemePullbackClassHom f a b h)
    (Stacks.GluePicard.surjective_schemePullbackClassHom f a b h)
    (Stacks.EllTorsion.exists_zsmul_eq_additive_units k hp.pos)

/-! ### Squishing a tangent vector -/

/-- **Case (3) of the induction of [Stacks, Tag 0C20]: squishing a tangent vector of a proper
reduced `X'` does not change the dimension of the `ℓ`-torsion of the Picard group.** The
sequence `0 ⟶ (k,+) ⟶ Pic(X) ⟶ Pic(X') ⟶ 0` is exact, and `(k,+)` is `ℓ`-divisible with
trivial `ℓ`-torsion because `ℓ` is invertible in `k`.

This is the step whose absence is the equality case of Tag 0C20: a factorization with no
squishings is exactly one along which `dim_{F_ℓ} Pic[ℓ]` and `h¹` fall in step. -/
theorem rank_torsionBy_picard_eq_of_isSquishingTangentVector (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : k) ≠ 0) (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ)
    [IsProper (X' ↘ Spec (.of k))] [IsReduced X'] :
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X') (ℓ : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X) (ℓ : ℤ)) =
      Module.rank (ZMod ℓ) (AddSubgroup.torsionBy (Stacks.Picard.ofScheme X') (ℓ : ℤ)) := by
  have : Subsingleton (AddSubgroup.torsionBy k (ℓ : ℤ)) :=
    Stacks.EllTorsion.subsingleton_torsionBy_self k hℓ
  exact Stacks.EllTorsion.rank_torsionBy_eq_of_subsingleton ℓ
    (Stacks.SquishSheafSequence.injective_picardTangentHom_of_isProper_of_isReduced f θ h)
    (Stacks.SquishSheafSequence.exact_picardTangentHom_schemePullbackClassHom f θ h)
    (Stacks.SquishPicard.surjective_schemePullbackClassHom f θ h)
    (Stacks.EllTorsion.exists_zsmul_eq_self k hℓ)

end Stacks.PicardTorsionStep

end
