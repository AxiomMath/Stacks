module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPowDegreeOpen
public import StacksFrontier.AlgebraicGeometry.GoodOpenClose.Basic
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaMultiplicativity
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject

/-!
# `𝒪(n) ≅ 𝒪(1)^{⊗ n}` on Tag 01MU's open `W₁`, in every integer degree

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring and `W₁ ⊆ Proj 𝒮` Tag 01MU's open `W_1`: the largest
open on which every twist `𝒪(n)` is invertible and every multiplication map
`𝒪(n) ⊗ 𝒪(m) → 𝒪(n+m)` is an isomorphism. This is the open Tag 01QI's Situation 01QH names, and
goodness of it is `Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_whereInvertible`
with no hypothesis beyond the grading.

This file builds the comparison

`𝒪_{W₁}(1)^{⊗ n} ≅ 𝒪_{W₁}(n)`

for **every integer** `n`, and proves that it is compatible with the canonical multiplication map
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap` of Tag 01MO in the bidegree
`(n, 1)`, again for every integer `n`. The existing
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta` is the same comparison on the degree
`d` open `U_d` and for a *natural* exponent only; `U_d ⊆ W_d` is in general strict, and the
negative degrees are what Tag 01QI's assertion about `f^*𝒪_Y(n) → L^{⊗ n}` ranges over, so
neither restriction can be lived with there.

## Main definitions

* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.twist` — the twist `𝒪(c)` of `Proj 𝒮` restricted to
  `W₁`, at the library's spelling `Stacks.AlgebraicGeometry.CommonDegreeTwist.restrictedTwist`.
* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistMulIso` — **the canonical multiplication
  isomorphism** `𝒪_{W₁}(n) ⊗ 𝒪_{W₁}(m) ≅ 𝒪_{W₁}(n+m)`, for arbitrary integers `n` and `m`.
* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistZeroIsoUnit` — `𝒪_{W₁}(0) ≅ 𝒪_{W₁}`.
* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.twistHasInverse` — `𝒪_{W₁}(-1)` is a two-sided
  tensor inverse of `𝒪_{W₁}(1)`, as a `CategoryTheory.MonoidalCategory.HasInverse` of Tag 0FFN.
* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta` — **the comparison
  `𝒪_{W₁}(1)^{⊗ n} ≅ 𝒪_{W₁}(n)` in every integer degree**, assembled from the two halves
  `natTheta` and `negTheta`.

## Main results

* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.isInvertibleModule_twist` and `isIso_twistMul` — the
  two clauses of goodness of `W₁`, read at the spellings the tensor-power calculus and Tag 01CD
  are stated in.
* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_mul_one` and `theta_mul_one_of_eq` — **the
  multiplicativity square in the bidegree `(n, 1)` for every integer `n`**: the addition law of
  the tensor powers, followed by the comparison in degree `n + 1`, is the comparison in degree `n`
  and the canonical `𝒪_{W₁}(1)^{⊗ 1} ≅ 𝒪_{W₁}(1)` on the two factors, followed by the canonical
  multiplication at `(n, 1)`. This is the statement that makes the family a *coherent* one rather
  than a degreewise choice, and it is what a degreewise propagation argument composes with.
* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_natCast`,
  `theta_neg_natCast`, `natTheta_succ`, `negTheta_succ`, `natTheta_mul_one`, `negTheta_mul_one` —
  the equations the two halves satisfy, restated as theorems because a `def` by pattern matching
  generates no usable equation lemma.
* `Stacks.AlgebraicGeometry.GoodOpenIntTwist.isEquivalence_tensorRight_twist_one` — tensoring on
  the right by `𝒪_{W₁}(1)` is an equivalence. This is `(3) → (2)` of Tag 0FFM applied to
  `twistHasInverse`; the general statement is
  `CategoryTheory.MonoidalCategory.HasInverse.tensorRightEquivalence` and is not restated here.

## The route

**Nothing is chosen, and in particular the comparison is not defined chartwise.** Both halves are
built out of the two clauses of goodness of `W₁` and nothing else; on the ratio charts of `W₁` one
could declare the comparison to send a trivializing generator to a trivializing generator, but
then Tag 01QI's assertion would be true by construction and therefore empty.

* **Nonnegative degrees.** `natTheta` is the induction of
  `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta`, run on `W₁` and in degree one at
  a time: the step splits `L ^⊗ (k+1)` by the addition law `Stacks.Ample.tensorPowModuleAddIso` of
  Tag 01CU and closes with `twistMulIso` at `(k, 1)`.
* **Negative degrees.** The descent is not run with a second addition law. What makes it work
  instead is that `𝒪_{W₁}(1)` has a two-sided tensor inverse, namely `𝒪_{W₁}(-1)`, so tensoring
  on the right by it is an equivalence and hence fully faithful:
  `CategoryTheory.Functor.preimageIso` of the comparison one degree up, tensored with
  `𝒪_{W₁}(1)`, is the comparison one degree down. This is the device of
  `StacksFrontier/AlgebraicGeometry/PowerFamilyBridge/Basic.lean` and of
  `StacksFrontier/AlgebraicGeometry/ProjTwistPowers/Basic.lean`, and it is also what makes the
  multiplicativity square available in the negative degrees: `Functor.map_preimage` *is* that
  square, tensored with `𝒪_{W₁}(1)`.

## Implementation notes

**What this is not a duplicate of, and why.** Three comparisons `𝒪(1) ^⊗ n ≅ 𝒪(n)` now exist in
this repository and they are deliberately distinct.

* `Stacks.AlgebraicGeometry.ProjTwistPowers.tensorPowModuleIsoTwistingSheaf` is the same
  comparison for every integer `n` on the whole of `Proj 𝒜` — under the hypothesis that `𝒜` is
  generated in degree one over `𝒜 0`, which forces `W₁ = ⊤`. It is obtained by `Classical.choice`
  from `Stacks.AlgebraicGeometry.ProjTwistPowers.nonempty_tensorPowModule_iso_twistingSheaf`, so it
  is an isomorphism in each degree *with no relation between the degrees*, and no multiplicativity
  square can be stated about it. Tag 01QI's situation is `S = Γ_*(X, L)` for an ample `L`, a
  section ring that is in general not generated in degree one, so that hypothesis is exactly what
  cannot be assumed here.
* `Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta` is the coherent, recursion-carrying
  comparison — but on the degree `d` open `U_d`, which is in general a strict subset of `W_d`, and
  only for a natural exponent.
* This file is the third corner: coherent *and* in every integer degree *and* with no hypothesis
  beyond the grading, at the price of living on `W₁` rather than on `Proj 𝒮`.

The abstract shift principle `Stacks.AlgebraicGeometry.ProjTwistPowers.nonempty_iso_of_shift` is
stated for an arbitrary fully faithful endofunctor and does apply here, and the two halves below
are its two induction branches; it is not used because it returns `Nonempty`, and discarding the
construction is precisely what makes a multiplicativity square unstateable. `negTheta` is its
downward branch kept as data.

**No stacks attribute is attached.** Tag 01QI is the conjunction of the factorization of the
canonical morphism through `W₁` with the assertion that the comparison maps are isomorphisms, and
neither is asserted here: this file is the absolute statement on `W₁` that the second assertion is
pulled back from. Tag 01MU is registered on
`Stacks.AlgebraicGeometry.GoodOpenClose.isGoodOpen_iff_le_whereInvertible_of_pos`, which is the
input used here, and nothing in this file strengthens it.

**Every degree is spelled the way the recursion produces it.** The exponents of the two halves
are `(k : ℤ)` and `-((k + 1 : ℕ) : ℤ)` throughout, and the mismatch between `(k : ℤ) + 1` and
`((k + 1 : ℕ) : ℤ)` — the same integer, not the same term — is carried by an explicit `eqToIso`
rather than left to unification. This is not cosmetic: `twist 𝒮 c` unfolds to a module pullback
along the open immersion of a supremum of opens, so a unifier asked to compare two spellings of
`c` underneath it unfolds that instead and exhausts the heartbeat budget. `theta_mul_one_of_eq`
therefore carries its target degree as a hypothesis `h : n + 1 = p`, which lets each branch of the
case analysis name the sum in its own spelling; `theta_mul_one` is the instance at `p = n + 1`.

**The tensor product of two isomorphisms is written `⊗ᵢ`**, the monoidal one, not
`Stacks.RelativeVeryAmple.tensorModulesMapIso`. The two agree — that is
`Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom` — but only up to a lemma, and
rewriting with it inside a composite leaves a term that is type-correct only at default
transparency, at which point `rw` refuses to proceed. With `⊗ᵢ` the forward map is `f ⊗ₘ g` by
definition and the square needs no conversion.

**The square in a bidegree `(n, m)` with `m` other than `1` is in the sibling
`StacksFrontier/AlgebraicGeometry/GoodOpenClose/IntegerTwistBidegree.lean`**, as
`Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_mul`, for arbitrary integers `n` and `m`.
`theta_mul_one` is the column that propagation runs along, and it is what is proved here.

**The degree one value of the family is identified with `tpowOne` in that same sibling**, as
`Stacks.AlgebraicGeometry.GoodOpenIntTwist.theta_one_eq`; it rests on the two unit laws of the two
multiplications and is not needed by `theta_mul_one`.

## References

* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 0FFM](https://stacks.math.columbia.edu/tag/0FFM)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open RingedSpaceModuleAdjunction
open Stacks.Ample
open Stacks.AlgebraicGeometry.CommonDegreeTwist
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open Stacks.RelativeVeryAmple

namespace Stacks.AlgebraicGeometry.GoodOpenIntTwist

universe u

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal

/-! ### The good open, its twists and their multiplication -/

/-- Tag 01MU's open `W₁`: the largest open of `Proj 𝒮` on which every twist is invertible and
every multiplication map between two twists is an isomorphism. -/
abbrev goodOpen : (AlgebraicGeometry.Proj 𝒮).Opens := whereInvertible 𝒮 1

/-- The twist `𝒪(c)` of `Proj 𝒮`, restricted to `W₁`. -/
abbrev twist (c : ℤ) : (goodOpen 𝒮).toScheme.Modules :=
  restrictedTwist 𝒮 (goodOpen 𝒮) c

/-- Reindexing of the restricted twists along an equality of degrees. -/
abbrev twistCongr {c c' : ℤ} (h : c = c') : twist 𝒮 c ≅ twist 𝒮 c' :=
  eqToIso (congrArg (restrictedTwist 𝒮 (goodOpen 𝒮)) h)

/-- **Every twist is invertible on `W₁`**, in every integer degree. This is the first clause of
goodness of `W₁`, with the degree `1 · n` of `Stacks.AlgebraicGeometry.GoodOpenClose` read as the
degree `n`. -/
instance isInvertibleModule_twist (n : ℤ) :
    IsInvertibleModule (goodOpen 𝒮).toScheme (twist 𝒮 n) := by
  have h := (GoodOpenClose.isGoodOpen_whereInvertible 𝒮 1).1 n
  rw [Nat.cast_one, one_mul] at h
  exact h

/-- **Every multiplication map between two twists is an isomorphism on `W₁`**, in every pair of
integer degrees, at the spelling Stacks Tag 01CD is stated in. This is the second clause of
goodness of `W₁`, read through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`. -/
theorem isIso_twistMul (n m : ℤ) :
    IsIso ((modulePullback (goodOpen 𝒮).ι.toLRSHom.toShHom).map
      (twistMultiplicationMap 𝒮 n m)) := by
  have h := (GoodOpenClose.isGoodOpen_whereInvertible 𝒮 1).2 n m
  rw [Nat.cast_one, one_mul, one_mul] at h
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.restrictFunctorIsoPullback (goodOpen 𝒮).ι)
    (twistMultiplicationMap 𝒮 n m)).mp h

/-- **The canonical multiplication isomorphism on `W₁`**,
`𝒪_{W₁}(n) ⊗ 𝒪_{W₁}(m) ≅ 𝒪_{W₁}(n + m)`, in every pair of integer degrees: Stacks Tag 01CD
commutes the restriction past the tensor product, and the canonical multiplication map
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap` of Stacks Tag 01MO is an
isomorphism on `W₁`. No transport appears: the target degree is the degree `n + m`. -/
def twistMulIso (n m : ℤ) : twist 𝒮 n ⊗ twist 𝒮 m ≅ twist 𝒮 (n + m) :=
  (pullbackTensorModulesIso (goodOpen 𝒮).ι (twistingSheaf 𝒮 n) (twistingSheaf 𝒮 m)).symm ≪≫
    @asIso _ _ _ _ _ (isIso_twistMul 𝒮 n m)

/-- **`𝒪_{W₁}(0) ≅ 𝒪_{W₁}`.** The zeroth twist of `Proj 𝒮` is its structure sheaf, by
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit`, and the pullback of the
structure sheaf along the open immersion is the structure sheaf of `W₁`, by the comparison
`Stacks.PullbackTensorCoherence.pullbackUnitComparison` of Stacks Tag 01CD. -/
def twistZeroIsoUnit : twist 𝒮 0 ≅ unitModule (goodOpen 𝒮).toScheme :=
  (modulePullback (goodOpen 𝒮).ι.toLRSHom.toShHom).mapIso
      (ProjEulerSequence.twistingSheafZeroIsoUnit 𝒮) ≪≫
    @asIso _ _ _ _ _ (Stacks.PullbackTensorCoherence.isIso_pullbackUnitComparison
      (goodOpen 𝒮).ι.toLRSHom.toShHom)

/-- **`𝒪_{W₁}(-1)` is a two-sided tensor inverse of `𝒪_{W₁}(1)`**, in the sense of Stacks Tag
0FFN: the two multiplication isomorphisms at `(1, -1)` and `(-1, 1)`, followed by
`𝒪_{W₁}(0) ≅ 𝒪_{W₁}`. -/
def twistHasInverse : HasInverse (twist 𝒮 1) where
  inv := twist 𝒮 (-1)
  isoLeft := twistMulIso 𝒮 1 (-1) ≪≫
    twistCongr 𝒮 (show (1 : ℤ) + (-1) = 0 from by ring) ≪≫ twistZeroIsoUnit 𝒮
  isoRight := twistMulIso 𝒮 (-1) 1 ≪≫
    twistCongr 𝒮 (show (-1 : ℤ) + 1 = 0 from by ring) ≪≫ twistZeroIsoUnit 𝒮

/-- Tensoring on the right by `𝒪_{W₁}(1)` is an equivalence; in particular it is fully faithful,
which is what produces the comparison in the negative degrees. This is `(3) → (2)` of Stacks Tag
0FFM, namely `CategoryTheory.MonoidalCategory.HasInverse.tensorRightEquivalence`. -/
theorem isEquivalence_tensorRight_twist_one :
    (MonoidalCategory.tensorRight (twist 𝒮 1)).IsEquivalence :=
  (twistHasInverse 𝒮).tensorRightEquivalence.isEquivalence_functor

attribute [local instance] isEquivalence_tensorRight_twist_one

/-! ### The tensor powers of `𝒪_{W₁}(1)` -/

/-- The `n`-th integer tensor power of `𝒪_{W₁}(1)`, Stacks Tag 01CU, at the spelling
`Stacks.Ample.tensorPowModule` the ampleness theory uses. -/
abbrev tpow (n : ℤ) : (goodOpen 𝒮).toScheme.Modules :=
  tensorPowModule (goodOpen 𝒮).toScheme (twist 𝒮 1) n

/-- The canonical `𝒪_{W₁}(1)^{⊗ 1} ≅ 𝒪_{W₁}(1)`. -/
abbrev tpowOne : tpow 𝒮 1 ≅ twist 𝒮 1 :=
  tensorPowModuleOneIso (goodOpen 𝒮).toScheme (twist 𝒮 1)

/-- The addition law of the tensor powers, `L ^⊗ n ⊗ L ^⊗ m ≅ L ^⊗ (n + m)` of Stacks Tag 01CU,
in every pair of integer degrees. -/
abbrev tpowAdd (n m : ℤ) : tpow 𝒮 n ⊗ tpow 𝒮 m ≅ tpow 𝒮 (n + m) :=
  tensorPowModuleAddIso (goodOpen 𝒮).toScheme (twist 𝒮 1) n m

/-- Reindexing of the tensor powers along an equality of exponents. -/
abbrev tpowCongr {n m : ℤ} (h : n = m) : tpow 𝒮 n ≅ tpow 𝒮 m :=
  tensorPowModuleCongr (goodOpen 𝒮).toScheme (twist 𝒮 1) h

/-! ### The comparison family -/

/-- **The comparison `𝒪_{W₁}(1)^{⊗ k} ≅ 𝒪_{W₁}(k)` in nonnegative degree**, by induction on `k`.
The step splits `L ^⊗ (k+1)` as `L ^⊗ k ⊗ L ^⊗ 1` by the addition law, rewrites the two factors
by the comparison in degree `k` and by `tpowOne`, and closes with the canonical multiplication
isomorphism at `(k, 1)`. Nothing is chosen in any degree. -/
def natTheta : (k : ℕ) → tpow 𝒮 (k : ℤ) ≅ twist 𝒮 (k : ℤ)
  | 0 =>
      tpowCongr 𝒮 (show ((0 : ℕ) : ℤ) = 0 from by norm_num) ≪≫
        tensorPowModuleZeroIso (goodOpen 𝒮).toScheme (twist 𝒮 1) ≪≫
        (twistZeroIsoUnit 𝒮).symm ≪≫
        twistCongr 𝒮 (show (0 : ℤ) = ((0 : ℕ) : ℤ) from by norm_num)
  | (k + 1) =>
      tpowCongr 𝒮 (show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 from by push_cast; ring) ≪≫
        (tpowAdd 𝒮 (k : ℤ) 1).symm ≪≫
        (natTheta k ⊗ᵢ tpowOne 𝒮) ≪≫
        twistMulIso 𝒮 (k : ℤ) 1 ≪≫
        twistCongr 𝒮 (show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) from by push_cast; ring)

/-- The recursion defining the nonnegative half, as an equation of isomorphisms: a `def` by
pattern matching generates no usable equation lemma, so the clause is restated here. -/
theorem natTheta_succ (k : ℕ) :
    natTheta 𝒮 (k + 1) =
      tpowCongr 𝒮 (show ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 from by push_cast; ring) ≪≫
        (tpowAdd 𝒮 (k : ℤ) 1).symm ≪≫
        (natTheta 𝒮 k ⊗ᵢ tpowOne 𝒮) ≪≫
        twistMulIso 𝒮 (k : ℤ) 1 ≪≫
        twistCongr 𝒮 (show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) from by push_cast; ring) :=
  rfl

/-- The isomorphism of which the comparison in degree `-(k+1)` is the preimage under tensoring on
the right by `𝒪_{W₁}(1)`: it carries a comparison `e` in degree `-k` to an identification of the
two sides in degree `-(k+1)` tensored with `𝒪_{W₁}(1)`, through the addition law of the tensor
powers at `(-(k+1), 1)` on one side and the canonical multiplication at `(-(k+1), 1)` on the
other. -/
def negStep (k : ℕ) (e : tpow 𝒮 (-(k : ℤ)) ≅ twist 𝒮 (-(k : ℤ))) :
    tpow 𝒮 (-((k + 1 : ℕ) : ℤ)) ⊗ twist 𝒮 1 ≅ twist 𝒮 (-((k + 1 : ℕ) : ℤ)) ⊗ twist 𝒮 1 :=
  whiskerLeftIso (tpow 𝒮 (-((k + 1 : ℕ) : ℤ))) (tpowOne 𝒮).symm ≪≫
    tpowAdd 𝒮 (-((k + 1 : ℕ) : ℤ)) 1 ≪≫
    tpowCongr 𝒮 (show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) from by push_cast; ring) ≪≫
    e ≪≫
    twistCongr 𝒮 (show -(k : ℤ) = -((k + 1 : ℕ) : ℤ) + 1 from by push_cast; ring) ≪≫
    (twistMulIso 𝒮 (-((k + 1 : ℕ) : ℤ)) 1).symm

/-- **The comparison `𝒪_{W₁}(1)^{⊗ (-k)} ≅ 𝒪_{W₁}(-k)` in nonpositive degree**, by induction on
`k`. The step down is `negStep`: it identifies the two sides in degree `-(k+1)` tensored with
`𝒪_{W₁}(1)`, and tensoring on the right by `𝒪_{W₁}(1)` is fully faithful, so
`CategoryTheory.Functor.preimageIso` returns the comparison one degree lower. -/
def negTheta : (k : ℕ) → tpow 𝒮 (-(k : ℤ)) ≅ twist 𝒮 (-(k : ℤ))
  | 0 =>
      tpowCongr 𝒮 (show -((0 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) from by norm_num) ≪≫
        natTheta 𝒮 0 ≪≫
        twistCongr 𝒮 (show ((0 : ℕ) : ℤ) = -((0 : ℕ) : ℤ) from by norm_num)
  | (k + 1) =>
      Functor.preimageIso (MonoidalCategory.tensorRight (twist 𝒮 1))
        (negStep 𝒮 k (negTheta k))

/-- The recursion defining the nonpositive half, as an equation of isomorphisms. -/
theorem negTheta_succ (k : ℕ) :
    negTheta 𝒮 (k + 1) =
      Functor.preimageIso (MonoidalCategory.tensorRight (twist 𝒮 1))
        (negStep 𝒮 k (negTheta 𝒮 k)) :=
  rfl

/-- **`𝒪_{W₁}(1)^{⊗ n} ≅ 𝒪_{W₁}(n)` for every integer `n`.** The two halves are `natTheta` and
`negTheta`, assembled by matching on the two constructors of `Int` — the shape
`Stacks.TensorPowers.intTensorPow`, and hence `Stacks.Ample.tensorPowModule`, is itself defined
by, so no reindexing is needed on either branch. -/
def theta (n : ℤ) : tpow 𝒮 n ≅ twist 𝒮 n :=
  match n with
  | Int.ofNat k => natTheta 𝒮 k
  | Int.negSucc k => negTheta 𝒮 (k + 1)

/-- The comparison in a nonnegative degree is `natTheta`. -/
theorem theta_natCast (k : ℕ) : theta 𝒮 (k : ℤ) = natTheta 𝒮 k := rfl

/-- The comparison in a nonpositive degree is `negTheta`. In the degree `-(k+1)` this is the
defining clause; in degree zero the two sides differ by the two reindexings inside `negTheta 0`,
which are identities. -/
theorem theta_neg_natCast : (k : ℕ) → theta 𝒮 (-(k : ℤ)) = negTheta 𝒮 k
  | 0 => by
      refine Iso.ext ?_
      show (natTheta 𝒮 0).hom = 𝟙 _ ≫ (natTheta 𝒮 0).hom ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  | (_ + 1) => rfl

/-! ### Compatibility with the multiplication maps of the twists -/

/-- **Multiplicativity of the comparison in the bidegree `(k, 1)` for a natural number `k`.** The
recursion read as a commuting square: the addition law of the tensor powers at `(k, 1)`, followed
by the comparison in degree `k + 1`, is the comparison in degree `k` and the canonical
`𝒪_{W₁}(1)^{⊗ 1} ≅ 𝒪_{W₁}(1)` on the two factors, followed by the canonical multiplication at
`(k, 1)`. It holds by cancelling one isomorphism against its inverse, exactly as
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.theta_mul_one` does on the degree `d`
open. -/
theorem natTheta_mul_one (k : ℕ) :
    (tpowAdd 𝒮 (k : ℤ) 1).hom ≫
        (tpowCongr 𝒮 (show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) from by push_cast; ring)).hom ≫
        (natTheta 𝒮 (k + 1)).hom =
      ((natTheta 𝒮 k).hom ⊗ₘ (tpowOne 𝒮).hom) ≫ (twistMulIso 𝒮 (k : ℤ) 1).hom ≫
        (twistCongr 𝒮 (show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) from by push_cast; ring)).hom := by
  simp only [natTheta_succ, tensorPowModuleCongr, Iso.trans_hom, Iso.symm_hom,
    MonoidalCategory.tensorIso_hom, eqToIso.hom, eqToHom_refl, Category.id_comp,
    Iso.hom_inv_id_assoc]

/-- **Multiplicativity of the comparison in the bidegree `(-(k+1), 1)` for a natural number
`k`.** The comparison in degree `-(k+1)` is a preimage under tensoring on the right by
`𝒪_{W₁}(1)`, so tensoring the square with `𝒪_{W₁}(1)` on the right turns it into the defining
equation `CategoryTheory.Functor.map_preimage`, and what is left cancels: the two whiskered
copies of `tpowOne`, the multiplication isomorphism against its inverse, and the two reindexings
between the degrees `-(k+1) + 1` and `-k`. -/
theorem negTheta_mul_one (k : ℕ) :
    (tpowAdd 𝒮 (-((k + 1 : ℕ) : ℤ)) 1).hom ≫
        (tpowCongr 𝒮
          (show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) from by push_cast; ring)).hom ≫
        (negTheta 𝒮 k).hom =
      ((negTheta 𝒮 (k + 1)).hom ⊗ₘ (tpowOne 𝒮).hom) ≫
        (twistMulIso 𝒮 (-((k + 1 : ℕ) : ℤ)) 1).hom ≫
        (twistCongr 𝒮
          (show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) from by push_cast; ring)).hom := by
  have hmap : (negTheta 𝒮 (k + 1)).hom ▷ twist 𝒮 1 = (negStep 𝒮 k (negTheta 𝒮 k)).hom :=
    (MonoidalCategory.tensorRight (twist 𝒮 1)).map_preimage _
  have hw : (tpow 𝒮 (-((k + 1 : ℕ) : ℤ)) ◁ (tpowOne 𝒮).hom) ≫
      (tpow 𝒮 (-((k + 1 : ℕ) : ℤ)) ◁ (tpowOne 𝒮).inv) = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id]
  rw [MonoidalCategory.tensorHom_def', hmap]
  simp only [negStep, tensorPowModuleCongr, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
    eqToIso.hom,
    Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id_assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- **The comparison family is compatible with the canonical multiplication of the twists in the
bidegree `(n, 1)`, for every integer `n`.** The addition law of the tensor powers at `(n, 1)`,
followed by the comparison in degree `n + 1`, is the comparison in degree `n` and the canonical
`𝒪_{W₁}(1)^{⊗ 1} ≅ 𝒪_{W₁}(1)` on the two factors, followed by the canonical multiplication at
`(n, 1)` — which is the multiplication map
`Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap` of Stacks Tag 01MO, read on
`W₁`.

The target degree is carried by the hypothesis `h` rather than written as `n + 1`, so that the
spelling of the sum can be chosen on each branch of the case analysis; `theta_mul_one` is the
instance at `p = n + 1`, with the two reindexings removed. -/
theorem theta_mul_one_of_eq {n p : ℤ} (h : n + 1 = p) :
    (tpowAdd 𝒮 n 1).hom ≫ (tpowCongr 𝒮 h).hom ≫ (theta 𝒮 p).hom =
      ((theta 𝒮 n).hom ⊗ₘ (tpowOne 𝒮).hom) ≫ (twistMulIso 𝒮 n 1).hom ≫
        (twistCongr 𝒮 h).hom := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ :
      (∃ k : ℕ, n = (k : ℤ)) ∨ (∃ k : ℕ, n = -((k + 1 : ℕ) : ℤ)) := by
    rcases n with k | k
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, by omega⟩
  · obtain rfl : p = ((k + 1 : ℕ) : ℤ) := by omega
    rw [theta_natCast, theta_natCast]
    exact natTheta_mul_one 𝒮 k
  · obtain rfl : p = -(k : ℤ) := by omega
    rw [theta_neg_natCast, theta_neg_natCast]
    exact negTheta_mul_one 𝒮 k

/-- **The multiplicativity square in the bidegree `(n, 1)` with no reindexing**, the target degree
written as `n + 1`. -/
theorem theta_mul_one (n : ℤ) :
    (tpowAdd 𝒮 n 1).hom ≫ (theta 𝒮 (n + 1)).hom =
      ((theta 𝒮 n).hom ⊗ₘ (tpowOne 𝒮).hom) ≫ (twistMulIso 𝒮 n 1).hom := by
  have h := theta_mul_one_of_eq 𝒮 (show n + 1 = n + 1 from rfl)
  simp only [tensorPowModuleCongr, eqToIso.hom, eqToHom_refl, Category.id_comp,
    Category.comp_id] at h
  exact h

end Stacks.AlgebraicGeometry.GoodOpenIntTwist

end
