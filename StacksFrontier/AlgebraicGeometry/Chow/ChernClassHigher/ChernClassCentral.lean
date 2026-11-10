module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyCompositionRing
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClass

/-!
# The Chern classes are central in the Chow cohomology ring

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `ℰ` be a locally free `O_X`-module of rank `r`. Clause (1)
of **Stacks 02UA** says that

  `c_j(ℰ) ∈ A^j(X)` is in the center of `A^*(X)`.

This file proves it, for the bivariant Chern class `Stacks.Chow.chernClassBivariant` of Stacks
0B7H and the Chow cohomology ring `Stacks.Chow.chowCohomologyRing` of Stacks 0B7E, granted the
commutation on the test schemes. The unconditional statement, for the class
`Stacks.Chow.GenuineChern.chernClass` built from the cap products of Stacks 02U6, is
`Stacks.Chow.GenuineChern.chernClass_mem_center`, where Stacks 02UA is registered.

## What clause (1) says here, and why it is not clause (2)

The source deduces clause (1) from clause (2) by taking `f = 𝟙 X`. Clause (2) is proved, as
`Stacks.Chow.isChernCapFamily_bivariantClass` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClass`, and that
specialization is *not* immediate here, for the reason the implementation notes of that file
record: a bivariant class of degree `p` for `f : X' ⟶ X` caps into the Chow group of the chosen
pullback `X' ×_X T`, so at `f = 𝟙 X` the two iterated cap products of clause (1) are read on
`X ×_X T` and not on `T`, and the two multiplications of `A^*(X)` are composites of operations on
`T`. What bridges the two is `Stacks.Chow.BivariantClass.toIdentityCapRule`: the cap operation of
a class for `𝟙 X`, pushed forward along the base-change isomorphism `X ×_X T ≅ T`. That is the
rule out of which `Stacks.Chow.chowCohomologyRingMul` is built, so it is the operation clause (1)
is about, and it is the shape the source writes `A^*(X)` in.

So the work here is to run the argument of Stacks 02UA for the operation
`Stacks.Chow.BivariantClass.toIdentityCapRule` of an arbitrary `a ∈ A^p(X)`, on each test scheme
separately, and then to assemble the resulting commutation into the two statements about the ring
`A^*(X)`: the graded commutation of the two products, and membership in the center.

## The argument is the one already written down

`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClass` carries out
the proof of Stacks 02UA once, for an arbitrary degree-lowering operation satisfying the
compatibility of Stacks 0B7B with the summands of the projective bundle relation, in
`Stacks.Chow.isChernCapFamily_operation`. Nothing here repeats it. The one new instantiation is
at `X' = X` with both bundles the projective bundle of `ℰ` restricted to the test scheme and the
operation the identity cap rule of `a`; the content of this file is that instantiation and the
passage from it to the ring `A^*(X)`.

## Main definitions

* `Stacks.Chow.ChernCapCommutesWithIdentityCapRule` — **Stacks 02UA clause (1) read on the test
  schemes**: the Chern cap rule of `ℰ` commutes with the identity cap rule of a bivariant class
  for `𝟙 X`, on every test scheme and in every degree.

## Main results

* `Stacks.Chow.chowGroupCast_heq'` — a Chow class is heterogeneously equal to its transport along
  an equality of degrees.
* `Stacks.Chow.toIdentityCapRule_chernClassBivariant` — the rule the bivariant `j`-th Chern class
  induces on the test schemes is `α ↦ c_j(g^*ℰ) ∩ α`.
* `Stacks.Chow.chernIdentityCapRuleOfRank_toIdentityCapRule_comm` — **Stacks 02UA clause (1) on
  one test scheme**: the instantiation of the argument above.
* `Stacks.Chow.chowCohomologyMul_chernClassBivariant_heq` — the two products
  `c_j(ℰ) · a` and `a · c_j(ℰ)` of `A^*(X)` agree.
* `Stacks.Chow.chernClassBivariant_mem_center` — **Stacks 02UA clause (1)**: `c_j(ℰ)` lies in the
  center of the ring `A^*(X)`.

## Implementation notes

### Which hypotheses are carried, and that none of them is an addition to Stacks 02UA

Stacks 02UA assumes exactly that `X` is locally of finite type over the base and that `ℰ` is
locally free of rank `r`. Every hypothesis below beyond those is a stand-in for a tag this
repository does not have, in the same way as for every other tag in
`StacksDraft.AlgebraicGeometry.Chow.ChernClassHigher`:

* The Chern class cap products themselves are the parameter `Stacks.Chow.HigherChernCapRule`,
  standing in for Stacks 0B7G, which is not formalized, and the bivariant class of Stacks 0B7H is
  built from it by carrying the three naturality axioms `hproper`, `hflat`, `hgysin` of Stacks 0B76
  together with the isomorphism case `hiso` of Stacks 02TA. These are the hypotheses
  `Stacks.Chow.chernClassBivariant` is *defined* with; nothing below adds to them.
* `Stacks.Chow.ChowCohomology` has a multiplication only granted `hiso`, so the same hypothesis
  is what makes the ring `A^*(X)` exist at all.
* The projective bundle `(π : P ⟶ T, O_P(1))` of `ℰ` restricted to a test scheme `T`, with its
  flatness, its relative dimension `r - 1`, the instance of Stacks 02S1 for its flat pullback and
  a first Chern class cap operator for its twist, is carried, because the construction of the
  projective bundle of a finite locally free module is not in this repository. The injectivity
  half of Stacks 02TX for it is carried for the same reason, exactly as in
  `Stacks.Chow.chernCapOnChow`, which is *defined* taking both halves.
* That the carried Chern cap rule is the one the projective bundle relation characterizes is the
  hypothesis `hfam`/`hfam'`, which is Stacks 02U6 for that rule. Without it the parameter is an
  arbitrary family of operations and there is nothing to prove about it.
* The compatibility of the summands of the relation with the cap product of `a` is Stacks 0B7B,
  taken in the form `Stacks.Chow.ChernTermsCompatibleWithOperation` that clause (2)
  takes it in; see the implementation notes there for why it cannot be discharged here.

### Why the commutation is carried as a predicate for the ring statements

The two ring statements quantify over all test schemes, while the instantiation of the argument
needs the projective bundle package and the compatibility of Stacks 0B7B for each one. Bundling
that package into the ring statements would mean quantifying over bundles of which there is no
construction, and the package for one test scheme does not determine the package for another. So
the commutation itself is isolated as `Stacks.Chow.ChernCapCommutesWithIdentityCapRule`, a
predicate on `a` alone, which
`Stacks.Chow.chernIdentityCapRuleOfRank_toIdentityCapRule_comm` discharges test scheme by test
scheme from the package there. This is the gap recorded from the other side in the implementation
notes of `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VirtualNormalCommuting`: that applying the
proved Stacks 02UA "would mean carrying such a package for every test scheme over `X` together
with Stacks 0B7B for each".

### Why the graded commutation is heterogeneous, and the center is not

The products `c_j(ℰ) · a` and `a · c_j(ℰ)` lie in `A^{j+p}(X)` and `A^{p+j}(X)`, the same integer
and not the same term, so the equality of the two components is an `HEq`. In the ring `A^*(X)`
itself — the direct sum — both products are elements of one type and no transport appears, which
is why `Stacks.Chow.chernClassBivariant_mem_center` is a plain membership. That is the statement
of clause (1), and it is the reason the direct sum is the right place to state it.

### The ring instance is not an instance

`Stacks.Chow.chowCohomologyRing` is an `@[instance_reducible] def` and not an `instance`, so the
center below is taken with respect to it explicitly rather than by typeclass inference.

## References

* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 0B7B](https://stacks.math.columbia.edu/tag/0B7B)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Stacks.Chow

/-! ### Transport of a degree -/

/-- A Chow class is heterogeneously equal to its transport along an equality of degrees. This is
`Stacks.Chow.chowGroupDegreeEquiv_heq` for `Stacks.Chow.chowGroupCast`, the transport the
projective bundle relation is written with. -/
theorem chowGroupCast_heq' (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] {k l : ℤ} (h : k = l) (x : chowGroup C q k) :
    chowGroupCast C q h x ≍ x := by
  cases h
  rfl

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (F : X.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r]
  (cap : HigherChernCapRule C r) (j : Fin (r + 1)) (p : ℤ)
  (a : chowCohomologyComponent C G sX p)

/-! ### The rule the bivariant Chern class induces on the test schemes -/

variable
  (hproper : IdentityCapRule.ProperNaturality C sX (j : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap j))
  (hflat : IdentityCapRule.FlatNaturality C sX (j : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap j))
  (hgysin : IdentityCapRule.GysinNaturality C sX (j : ℤ)
    (chernIdentityCapRuleOfRank C sX F r cap j) G)
  (hiso : G.IsNaturalUnderInverseIso)

/-- The identity cap rule the bivariant `j`-th Chern class of Stacks 0B7H induces on the test
schemes is intersection with the `j`-th Chern class of the pulled-back module: this is the
characterization of Stacks 0B7H, read through
`Stacks.Chow.BivariantClass.toIdentityCapRule`. -/
theorem toIdentityCapRule_chernClassBivariant {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    BivariantClass.toIdentityCapRule C G sX (j : ℤ)
        (chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso) g k α =
      chernIdentityCapRuleOfRank C sX F r cap j g k α :=
  isChernClassBivariant_chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso g k α

/-! ### Clause (1) read on the test schemes -/

/-- **Stacks 02UA clause (1), read on the test schemes.** That intersection with `c_j(ℰ)` commutes
with the cap operation of a bivariant class `a ∈ A^p(X)` of degree `p` for `𝟙 X`: on every test
scheme `g : T ⟶ X` and in every degree,

  `c_j(g^*ℰ) ∩ (a ∩ α) = a ∩ (c_j(g^*ℰ) ∩ α)`.

Both operations are read on the test scheme itself, as identity cap rules; the two sides lie in
degrees `k - j - p` and `k - p - j`, the same integer and not the same term, whence the
transport. Quantifying over the test schemes is what makes this a statement about `A^*(X)` and
not only about `A_*(X)`: by `Stacks.Chow.BivariantClass.eq_of_toIdentityCapRule_eq` a bivariant
class for `𝟙 X` is determined by the rule it induces, so this identity is exactly the equality
of the two products of `Stacks.Chow.chowCohomologyRingMul`. -/
def ChernCapCommutesWithIdentityCapRule : Prop :=
  ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k),
    chernIdentityCapRuleOfRank C sX F r cap j g (k - p)
        (BivariantClass.toIdentityCapRule C G sX p a g k α) =
      chowGroupCast C (g ≫ sX) (show k - (j : ℤ) - p = k - p - (j : ℤ) from by omega)
        (BivariantClass.toIdentityCapRule C G sX p a g (k - (j : ℤ))
          (chernIdentityCapRuleOfRank C sX F r cap j g k α))

section TestScheme

variable {T PT : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
  (πT : PT ⟶ T) [LocallyOfFiniteType πT] [Flat πT]
  (hsPT : πT ≫ (g ≫ sX) = (πT ≫ g) ≫ sX)
  (hπT : AlgebraicGeometry.RelativeDimension πT (r - 1))
  (hfacT : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C ((πT ≫ g) ≫ sX) (g ≫ sX)
    πT hsPT (r - 1) hπT k)
  (twistT : ChernCapOperator C ((πT ≫ g) ≫ sX))

/-- **Stacks 02UA clause (1), on one test scheme.** Intersection with `c_j(ℰ)` commutes with the
cap operation of a bivariant class `a ∈ A^p(X)`, on the test scheme `g : T ⟶ X`.

This is `Stacks.Chow.isChernCapFamily_operation` — the argument of Stacks 02UA, written there for
an arbitrary degree-lowering operation — instantiated at the operation `a` induces on the test
schemes, with the projective bundle of `ℰ` restricted to `T` on both sides. The hypothesis
`hcompat` is Stacks 0B7B for `a`; `hfam` and `hfam'` are Stacks 02U6 for the carried Chern cap
rule, at `α` and at `a ∩ α`. -/
theorem chernIdentityCapRuleOfRank_toIdentityCapRule_comm
    (hinjT : ProjectiveBundleRelationInjective C (g ≫ sX) ((πT ≫ g) ≫ sX) πT hsPT r hπT hfacT
      twistT)
    (hcompat : ChernTermsCompatibleWithOperation C (g ≫ sX) (g ≫ sX) ((πT ≫ g) ≫ sX)
      ((πT ≫ g) ≫ sX) πT hsPT πT hsPT r hπT hπT hfacT hfacT twistT twistT p
      (fun m ↦ BivariantClass.toIdentityCapRule C G sX p a g m)
      (fun m ↦ BivariantClass.toIdentityCapRule C G sX p a (πT ≫ g) m))
    (k : ℤ) (α : chowGroup C (g ≫ sX) k)
    (hfam : IsChernCapFamily C (g ≫ sX) ((πT ≫ g) ≫ sX) πT hsPT r hπT hfacT twistT k α
      fun i ↦ chernIdentityCapRuleOfRank C sX F r cap i g k α)
    (hfam' : IsChernCapFamily C (g ≫ sX) ((πT ≫ g) ≫ sX) πT hsPT r hπT hfacT twistT (k - p)
      (BivariantClass.toIdentityCapRule C G sX p a g k α)
      fun i ↦ chernIdentityCapRuleOfRank C sX F r cap i g (k - p)
        (BivariantClass.toIdentityCapRule C G sX p a g k α)) :
    chernIdentityCapRuleOfRank C sX F r cap j g (k - p)
        (BivariantClass.toIdentityCapRule C G sX p a g k α) =
      chowGroupCast C (g ≫ sX) (show k - (j : ℤ) - p = k - p - (j : ℤ) from by omega)
        (BivariantClass.toIdentityCapRule C G sX p a g (k - (j : ℤ))
          (chernIdentityCapRuleOfRank C sX F r cap j g k α)) :=
  congrFun
    (isChernCapFamily_operation C (g ≫ sX) (g ≫ sX) ((πT ≫ g) ≫ sX) ((πT ≫ g) ≫ sX) πT hsPT πT
      hsPT r hπT hπT hfacT hfacT twistT twistT p
      (fun m ↦ BivariantClass.toIdentityCapRule C G sX p a g m)
      (fun m ↦ BivariantClass.toIdentityCapRule C G sX p a (πT ≫ g) m) hinjT hcompat k α _ _ hfam
      hfam') j

end TestScheme

/-! ### Clause (1) in the Chow cohomology ring -/

/-- A term of a direct summand is carried into the direct sum by `DirectSum.of` in a way that only
depends on the index up to equality: two heterogeneously equal terms in two equal degrees have the
same image. This is what removes the transport of the degree from the statement of clause (1). -/
private theorem directSum_of_heq {ι : Type*} [DecidableEq ι] {β : ι → Type*}
    [∀ i, AddCommMonoid (β i)] {i i' : ι} (h : i = i') {x : β i} {y : β i'} (hxy : x ≍ y) :
    DirectSum.of β i x = DirectSum.of β i' y := by
  cases h
  exact congrArg _ (eq_of_heq hxy)

/-- **Stacks 02UA clause (1), the two products of `A^*(X)`.** Granted the commutation on the test
schemes, the products `c_j(ℰ) · a` and `a · c_j(ℰ)` of the Chow cohomology ring agree.

They lie in `A^{j+p}(X)` and `A^{p+j}(X)`, the same integer and not the same term, so the
comparison is heterogeneous; `Stacks.Chow.chernClassBivariant_mem_center` is the statement in the
ring itself, where no transport appears. Both products cap, by
`Stacks.Chow.chowCohomologyMul_toIdentityCapRule_heq`, as the two iterated cap products on each
test scheme, and a bivariant class for `𝟙 X` is determined by the rule it induces there. -/
theorem chowCohomologyMul_chernClassBivariant_heq
    (hcomm : ChernCapCommutesWithIdentityCapRule C G sX F r cap j p a) :
    chowCohomologyRingMul C G sX hiso
        (chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso) a ≍
      chowCohomologyRingMul C G sX hiso a
        (chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso) := by
  refine BivariantClass.heq_of_toIdentityCapRule_heq C G sX
    (by ring : (j : ℤ) + p = p + (j : ℤ)) _ _ fun {T} g _ k α ↦ ?_
  refine HEq.trans (chowCohomologyMul_toIdentityCapRule_heq C G sX hiso _ a g k α) ?_
  refine HEq.symm (HEq.trans (chowCohomologyMul_toIdentityCapRule_heq C G sX hiso a _ g k α) ?_)
  simp only [toIdentityCapRule_chernClassBivariant C G sX F r cap j hproper hflat hgysin hiso]
  rw [hcomm g k α]
  exact (chowGroupCast_heq' C (g ≫ sX) _ _).symm

/-- **Stacks 02UA clause (1).** The `j`-th Chern class `c_j(ℰ) ∈ A^j(X)` of a finite locally free
module of rank `r` lies in the center of the Chow cohomology ring `A^*(X)`.

The hypothesis is the commutation of the Chern class cap products with the cap operation of every
bivariant class for `𝟙 X`, read on the test schemes;
`Stacks.Chow.chernIdentityCapRuleOfRank_toIdentityCapRule_comm` discharges it at each test scheme
from the projective bundle of `ℰ` there. The ring structure of Stacks 0B7E is an
`@[instance_reducible] def` and not an `instance`, which is why it is supplied by hand. -/
theorem chernClassBivariant_mem_center
    (hcomm : ∀ (q : ℤ) (b : chowCohomologyComponent C G sX q),
      ChernCapCommutesWithIdentityCapRule C G sX F r cap j q b) :
    letI : Ring (chowCohomology C G sX) := chowCohomologyRing C G sX hiso
    DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) (j : ℤ)
        (chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso) ∈
      Subring.center (chowCohomology C G sX) := by
  let gring : DirectSum.GRing fun q : ℤ ↦ chowCohomologyComponent C G sX q :=
    chowCohomologyGRing C G sX hiso
  let : Ring (chowCohomology C G sX) := chowCohomologyRing C G sX hiso
  rw [Subring.mem_center_iff]
  intro x
  induction x using DirectSum.induction_on with
  | zero => rw [zero_mul, mul_zero]
  | of q b =>
    calc DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) q b *
          DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) (j : ℤ)
            (chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso)
        = DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) (q + (j : ℤ))
            (chowCohomologyRingMul C G sX hiso b
              (chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso)) :=
          DirectSum.of_mul_of _ _
      _ = DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) ((j : ℤ) + q)
            (chowCohomologyRingMul C G sX hiso
              (chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso) b) :=
          directSum_of_heq (add_comm _ _)
            (chowCohomologyMul_chernClassBivariant_heq C G sX F r cap j q b hproper hflat hgysin
              hiso (hcomm q b)).symm
      _ = DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) (j : ℤ)
            (chernClassBivariant C sX F r G cap j hproper hflat hgysin hiso) *
          DirectSum.of (fun q : ℤ ↦ chowCohomologyComponent C G sX q) q b :=
          (DirectSum.of_mul_of _ _).symm
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]

end Stacks.Chow

end
