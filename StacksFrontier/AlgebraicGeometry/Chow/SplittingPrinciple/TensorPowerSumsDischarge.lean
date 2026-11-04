module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativityInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernComm
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.PowerSumCapProducts
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0F9D with Stacks 02TI and Stacks 02TJ discharged

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, Stacks 02QL, let `X` be
locally of finite type over `S` and let `P_p` be the universal power-sum polynomial of
Stacks 0F9B. `Stacks.Chow.powerSumCap_lexFamily` of
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.PowerSumCapProducts` proves
[Stacks, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D),

  `P_p(ℰ₁ ⊗ ℰ₂) ∩ α = ∑_{p₁ + p₂ = p} C(p, p₁) · (P_{p₁}(ℰ₁) ∘ P_{p₂}(ℰ₂)) ∩ α`,

componentwise on cap products, from four inputs: Stacks 02TI for each quotient of each of the
three filtrations (`hfacL`, `hfacN`, `hfacM`), Stacks 02TJ across the two families of quotients
(`hcommLN`), and the source's lexicographic identification of the quotients of the tensor
filtration (`hquot`). **The first two are discharged here**, so the identity holds with `hquot`
as its only remaining hypothesis.

**The tag itself is proved elsewhere.** Stacks 0F9D is proved unconditionally, for arbitrary
finite locally free `ℰ₁` and `ℰ₂` and their Chern classes, in the bivariant ring `A^*(X)` and
with no hypothesis on the ranks: `Stacks.Chow.modulePowerSumArbitraryRank_tensorObj` and
`Stacks.Chow.modulePowerSumComponentArbitraryRank_tensorObj` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantTensorPowerSum`, and
`Stacks.Chow.totalChernCharacterArbitraryRank_tensorObj` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantChernCharacter`. The
constant-rank step they rest on is `Stacks.Chow.powerSumChernElem_tensorObj` of
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorPowerSumsTotal`, in the
`Stacks.Chow.GradedCapFamily` vocabulary where Stacks 02UI, Stacks 02UJ, Stacks 02U8 and the
descent along `π^*` are all unconditional. What remains below is the conditional form in the
`Stacks.Chow.chernClassCapExt` vocabulary, which is kept because it holds for *every* family of
invertible quotients identified lexicographically with the `ℒ_i ⊗ 𝒩_j`, and because it is the
form in which Stacks 0FA6 is stated in this repository.

## What discharges them

* Stacks 02TI is `Stacks.Chow.firstChernCapFactorsEverywhere` of
  `StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors`, which has no hypothesis.
  `Stacks.Chow.InvertibleChernCapDescends` is that assertion in every degree for the component
  rule of one invertible module, so it follows degreewise.
* Stacks 02TJ is `Stacks.Chow.GenuineChern.firstChernClassCapChow_comm` of
  `StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernComm`, which likewise has no
  hypothesis. It is stated for `Stacks.Chow.firstChernClassCapChow`, the descended operation
  `c₁(ℒ) ∩ - : A_{k+1}(X) ⟶ A_k(X)`, whereas `Stacks.Chow.FirstChernCapStepsCommute` is stated
  for `Stacks.Chow.firstChernCapStep`, the same operation read as a map
  `A_{n-i}(X) ⟶ A_{n-(i+1)}(X)`. The two presentations differ only by the transport of degrees
  `Stacks.Chow.chowGroupDegreeCast`, and `Stacks.Chow.firstChernCapStep_apply` below identifies
  them.

## What is still carried here, and where it is discharged

`hquot` is not a gap: it is a hypothesis on the family `ℳ_k`, universally quantified, so the
statement below holds for *every* family of invertible quotients identified lexicographically
with the `ℒ_i ⊗ 𝒩_j`. What the source supplies in its place is the *reduction*: the filtrations
themselves, and the identification of the operator with `P_p` of the Chern classes of the module
`ℰ₁ ⊗_{𝒪_X} ℰ₂` itself.

**That reduction is now performed**, in the `Stacks.Chow.GradedCapFamily` vocabulary:
`Stacks.Chow.powerSumChernElem_tensorObj` of
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorPowerSumsTotal` states the identity
for arbitrary finite locally free `ℰ₁`, `ℰ₂` of constant ranks, with no hypothesis beyond the
source's, and the tag has moved past it to the identity of bivariant classes in `A^*(X)` that
reads it on every test scheme, in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantTensorPowerSum`. What
follows records where each of the ingredients is proved, since each of them might look like an
obstruction.

**Stacks 02UL is not one.** It is proved unconditionally as
`Stacks.Chow.exists_splittingMorphism_unconditional`, whose layer is the projective bundle of the
module itself, `Stacks.Chow.bundleStep`: the fields of `Stacks.Chow.BundleStep` are discharged by
`Stacks.Chow.bundle`, `Stacks.Chow.bundleProj`, `Stacks.Chow.bundleTwist` and
`Stacks.Chow.isInvertible_bundleTwist` for the bundle and its twist, by
`Stacks.Chow.isProper_bundleProj`, `Stacks.Chow.flat_bundleProj`,
`Stacks.Chow.locallyOfFiniteType_bundleProj` and `Stacks.Chow.relativeDimension_bundleProj` for
Stacks 02TX and Stacks 0800 (all of them for a module of constant rank, not only for a free one),
by `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` for Stacks 02S1 with
nothing carried, by `Stacks.Chow.invCap` of the twist for `c₁(𝒪_P(1)) ∩ -`, by
`Stacks.Chow.projectiveBundleRelationInjective_of_bundleMap` at
`Stacks.Chow.projectiveBundle_formula` for the injectivity half of Stacks 02TX, and by
`Stacks.Chow.shortExact_bundleTautological` with
`Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological` for the tautological sequence
of Stacks 0B3V and the rank of its kernel — including the rank-one end `m = 0`, where the kernel
has rank zero.

**The mathematical content of `hquot` is now proved, elsewhere and in another vocabulary.**
`Stacks.Chow.chernFamily_tensorObj_eq_prod_prod` of
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernRootsTotal` proves, with nothing
carried, that if `ℰ₁` carries a filtration of length `r` with invertible quotients `ℒ_i` and `ℰ₂`
one of length `s` with invertible quotients `𝒩_j`, then

  `c(ℰ₁ ⊗_{𝒪_X} ℰ₂) = ∏_i ∏_j (1 + c₁(𝒩_j) + c₁(ℒ_i))`

in the ring `Stacks.Chow.GradedCapFamily (Stacks.Chow.chowGroup C p)` — that is, the Chern roots
of `ℰ₁ ⊗ ℰ₂` are the `x_i + y_j`. Two apparent obstructions to that
statement do not arise:

* the lexicographic filtration does **not** have to be interpolated. The sum of subobjects
  `ℰ_i ⊗ ℱ_j + ℰ_{i-1} ⊗ ℱ` written in the source's proof has no Lean declaration
  and needs none: tensoring the filtration of `ℰ₁` by `ℰ₂` and then the filtration of `ℰ₂` by each
  invertible `ℒ_i` gives the same Chern class in two stages
  (`Stacks.Chow.chernFamily_tensorObj_eq_prod` and
  `Stacks.Chow.chernFamily_tensorObj_invertible_eq_prod`), the braiding
  `Stacks.Chow.tensorObjSwap` exchanging the two factors between them;
* the exactness of tensoring by a finite locally free module of rank `s` **is** in the
  repository, as `Stacks.Chow.exists_shortExact_tensorModules_of_isFiniteLocallyFree` of
  `StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerTensorExact`.

Likewise, that `Stacks.WeilCohomology.HasInvertibleFiltration` is an inductive `Prop` is not an
obstruction: `Stacks.Chow.exists_hasQuotients_of_hasInvertibleFiltration` eliminates it into the
existence of a named family of invertible quotients, which is legitimate because the target is a
`Prop`, and `Stacks.Chow.isFiniteLocallyFreeOfRank_of_hasQuotients` supplies the rank of every
stage.

The last two ingredients are in place in the `Stacks.Chow.GradedCapFamily` vocabulary rather
than this one:

1. **the power sums as a ring element.** `AlgebraicGeometry.powerSumChernPolynomial` is `P_p`
   itself, `AlgebraicGeometry.powerSumOfChernClasses_eq_powerSumOfRoots` its value at Chern
   classes that split, and `AlgebraicGeometry.powerSumOfRoots_tensorRoots` the binomial
   convolution at the roots `x_i + y_j` — all three in a **commutative** ring, which
   `Stacks.Chow.GradedCapFamily` is not. The commutative ring is the **subring the Chern classes
   generate**, `Stacks.Chow.chernSubring` of
   `StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernPowerSumElem`: any two Chern
   classes commute by Stacks 02UA read componentwise
   (`Stacks.Chow.commute_homComponent_chernFamily`), so `Subring.isMulCommutative_closure` makes
   it commutative, and `Stacks.Chow.powerSumChernElem` is `P_p` evaluated there and read back in
   the ambient ring. `Stacks.Chow.powerSumChernElem_zero` and
   `Stacks.Chow.powerSumChernElem_one` identify it with the rank and with `c₁` in the first two
   degrees. Newton's recursion is not needed in the non-commutative ring;
2. **the descent along `π^*`.** The identity is proved on the `P` that Stacks 02UL delivers,
   where the filtrations live, and carried down to `X` by `Stacks.Chow.eq_of_intertwines`, whose
   two inputs are both unconditional: Stacks 02U8 as
   `Stacks.Chow.GenuineChern.intertwines_chernFamily`, and injectivity of `π^*` as the field
   `Stacks.Chow.SplittingMorphism.injective_pullbackChow`. That the intertwining relation carries
   `P_p` — not just the total Chern class — is
   `Stacks.Chow.intertwines_powerSumChernElem` of
   `StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernPowerSumDescent`: the relation is
   closed under the ring operations and under taking homogeneous components, so the pairs it
   relates form a commutative subring in which `P_p` can be evaluated on pairs. (The older note
   that "no compatibility of the Chern class cap product with flat pullback is stated, so
   injectivity of `π^*` has nothing to descend" was about `Stacks.Chow.chernClassCapExt` and
   `Stacks.Chow.powerSumCap` only; it is not true of `Stacks.Chow.GenuineChern.chernCap`, and the
   response was to state Stacks 0F9D in the latter vocabulary rather than to bridge the two.)

## Main results

* `Stacks.Chow.invertibleChernCapDescends` — Stacks 02TI in the form the power-sum operators
  consume, with no hypothesis.
* `Stacks.Chow.firstChernCapStepsCommute` — **Stacks 02TJ** in the form the power-sum operators
  consume, with no hypothesis.
* `Stacks.Chow.powerSumShift_lexFamily_of_quotients`,
  `Stacks.Chow.powerSumCap_lexFamily_of_quotients` — the tensor identity in the
  `Stacks.Chow.chernClassCapExt` vocabulary, with Stacks 02TI and Stacks 02TJ discharged and
  `hquot` carried. They are untagged: Stacks 0F9D itself is
  `Stacks.Chow.modulePowerSumArbitraryRank_tensorObj` of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantTensorPowerSum`, an
  identity of bivariant classes in `A^*(X)` which carries nothing and assumes nothing about the
  ranks.

## References

* [Stacks Project, Tag 0F9D](https://stacks.math.columbia.edu/tag/0F9D)
* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02TJ](https://stacks.math.columbia.edu/tag/02TJ)
* [Stacks Project, Tag 02UJ](https://stacks.math.columbia.edu/tag/02UJ)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Finset

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-! ### Stacks 02TI in every degree, with no hypothesis -/

/-- **Stacks 02TI for an invertible module, in every degree, with no hypothesis.** The cap
product with the first Chern class of an invertible module factors through rational equivalence
in every degree, which is what `Stacks.Chow.firstChernCapStep` needs in order to be formed.

This is `Stacks.Chow.firstChernCapFactorsEverywhere` read degreewise at the component rule of the
module; the tag itself is carried there. -/
theorem invertibleChernCapDescends (A : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property A] :
    InvertibleChernCapDescends C p A :=
  fun m ↦
    firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C m p A

/-! ### Stacks 02TJ for the degree-raising steps, with no hypothesis -/

section Steps

variable (n : ℤ) (A B : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property A]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property B]

/-- The degree-raising step of `Stacks.Chow.firstChernCapStep` is the descended operation
`Stacks.Chow.firstChernClassCapChow` of Stacks 02TI, read on the transport of its argument along
the equality of degrees `n - i = (n - (i+1)) + 1`. -/
theorem firstChernCapStep_apply (hA : InvertibleChernCapDescends C p A) (i : ℕ)
    (z : chowGroup C p (n - (i : ℤ))) :
    firstChernCapStep C p n A hA i z
      = firstChernClassCapChow C (n - ((i + 1 : ℕ) : ℤ)) p A
          (chowGroupCast C p (by push_cast; ring) z) :=
  chowGroupDegreeCast_apply C p _ _ z

/-- **Stacks 02TJ between two degrees given only up to the transport of Chow groups.** The two
iterated operations agree whenever the three degrees are successive, in whatever form those
equalities are presented. -/
private theorem firstChernClassCapChow_comm_cast {a b c : ℤ} (hab : a = b + 1) (hbc : b = c + 1)
    (z : chowGroup C p a) :
    firstChernClassCapChow C c p A (chowGroupCast C p hbc
        (firstChernClassCapChow C b p B (chowGroupCast C p hab z)))
      = firstChernClassCapChow C c p B (chowGroupCast C p hbc
          (firstChernClassCapChow C b p A (chowGroupCast C p hab z))) := by
  subst hab
  subst hbc
  simpa using GenuineChern.firstChernClassCapChow_comm C p c A B z

/-- **Stacks 02TJ in the form the power-sum operators consume, with no hypothesis.** For two
invertible modules the degree-raising operations `c₁(A) ∩ -` and `c₁(B) ∩ -` of
`Stacks.Chow.firstChernCapStep` commute, in every degree.

This is `Stacks.Chow.GenuineChern.firstChernClassCapChow_comm` — Stacks 02TJ with no
hypothesis beyond the ones the tag states — transported to the presentation
`A_{n-i}(X) ⟶ A_{n-(i+1)}(X)` of the same operation by
`Stacks.Chow.firstChernCapStep_apply`. It discharges every `hcommLN`-style hypothesis of
`StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TensorChernClasses`. -/
@[stacks 02TJ "the identity for the degree-raising steps Stacks.Chow.firstChernCapStep that the \
Chern class power-sum operators of Stacks 0F9B are built from, with no hypothesis: it is \
Stacks.Chow.GenuineChern.firstChernClassCapChow_comm, which is the tag itself with nothing \
carried, transported along the equality of degrees n - i = (n - (i+1)) + 1 that separates the \
two presentations of c_1(L) cap -"]
theorem firstChernCapStepsCommute (hA : InvertibleChernCapDescends C p A)
    (hB : InvertibleChernCapDescends C p B) :
    FirstChernCapStepsCommute C p n A B hA hB := by
  intro i z
  simp only [firstChernCapStep_apply]
  exact firstChernClassCapChow_comm_cast C p A B _ _ z

end Steps

/-! ### Stacks 0F9D with both discharged -/

section Tensor

variable (n : ℤ) {r s : ℕ} (L : Fin r → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (L j)]
  (N : Fin s → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (N j)]
  (M : Fin (r * s) → X.Modules)
  [∀ j, AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (M j)]

/-- **Stacks 0F9D in the operator ring, with Stacks 02TI and Stacks 02TJ discharged.** If the
`(i·s+j)`-th quotient of the filtration of `ℰ₁ ⊗ ℰ₂` is `ℒ_i ⊗ 𝒩_j` — the source's lexicographic
filtration — then the power-sum operator of the tensor product is the binomial convolution of
those of the factors, in every degree. This is
`Stacks.Chow.powerSumShift_lexFamily` with its Stacks 02TI and Stacks 02TJ hypotheses
supplied. -/
theorem powerSumShift_lexFamily_of_quotients
    (hquot : ∀ (i : Fin r) (j : Fin s),
      M (finLexIndex i j) ≅ Scheme.Modules.tensorObj (L i) (N j)) (k : ℕ) :
    powerSumShift C p n M (fun j ↦ invertibleChernCapDescends C p (M j)) k
      = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal k,
          k.choose q.1 •
            (powerSumShift C p n L (fun j ↦ invertibleChernCapDescends C p (L j)) q.1 *
              powerSumShift C p n N (fun j ↦ invertibleChernCapDescends C p (N j)) q.2) :=
  powerSumShift_lexFamily C p n L _ N _ M _ hquot
    (fun a b ↦ firstChernCapStepsCommute C p n (L a) (N b) _ _) k

/-- **Stacks 0F9D, componentwise on cap products, with Stacks 02TI and Stacks 02TJ discharged.**
Let `ℰ₁` be finite locally free of rank `r` with a filtration whose successive quotients are the
invertible modules `ℒ_i = L i`, let `ℰ₂` be finite locally free of rank `s` with quotients
`𝒩_j = N j`, and let the filtration of `ℰ₁ ⊗_{𝒪_X} ℰ₂` be the lexicographic one of the source,
of length `r·s`, whose `(i·s+j)`-th quotient is `ℒ_i ⊗ 𝒩_j`. Then for every `n`-cycle `α` and
every `p ≥ 0`

  `P_p(ℰ₁ ⊗ ℰ₂) ∩ α = ∑_{p₁ + p₂ = p} C(p, p₁) · (P_{p₁}(ℰ₁) ∘ P_{p₂}(ℰ₂)) ∩ α`

in `A_{n-p}(X)`, and `ch(ℰ₁ ⊗ ℰ₂) = ch(ℰ₁) · ch(ℰ₂)` after dividing by `p!`.

This is `Stacks.Chow.powerSumCap_lexFamily` with two of its three inputs discharged: Stacks 02TI
for each quotient by `Stacks.Chow.invertibleChernCapDescends`, and Stacks 02TJ across the two
families of quotients by `Stacks.Chow.firstChernCapStepsCommute`. The identification `hquot` of
the quotients of the tensor filtration remains, universally quantified over the family `ℳ_k`,
which is why the tag is not here: Stacks 0F9D for arbitrary finite locally free `ℰ₁`, `ℰ₂` and
their Chern classes is `Stacks.Chow.modulePowerSumArbitraryRank_tensorObj` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantTensorPowerSum`, an identity
of bivariant classes in `A^*(X)` which carries nothing. -/
theorem powerSumCap_lexFamily_of_quotients
    (hquot : ∀ (i : Fin r) (j : Fin s),
      M (finLexIndex i j) ≅ Scheme.Modules.tensorObj (L i) (N j))
    (k : ℕ) (α : chowGroup C p n) :
    powerSumCap C p n M (fun j ↦ invertibleChernCapDescends C p (M j)) k α
      = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal k, k.choose q.1 •
          evalChowGraded C p n α k
            (powerSumShift C p n L (fun j ↦ invertibleChernCapDescends C p (L j)) q.1 *
              powerSumShift C p n N (fun j ↦ invertibleChernCapDescends C p (N j)) q.2) :=
  powerSumCap_lexFamily C p n L _ N _ M _ hquot
    (fun a b ↦ firstChernCapStepsCommute C p n (L a) (N b) _ _) k α

end Tensor

end Stacks.Chow

end
