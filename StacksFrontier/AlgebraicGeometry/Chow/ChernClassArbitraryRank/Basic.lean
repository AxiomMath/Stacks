module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLoci
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Chern classes of a finite locally free module whose rank is not constant

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `E` be a finite locally free `O_X`-module whose rank need
not be constant. Write `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …` for the decomposition of `X` into the open and
closed loci where the rank of `E` is `r`, built in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLoci`. The decomposition theorem
Stacks 0FDZ then gives

  `A^p(X) = ∏_{r ≥ 0} A^p(X_r)`,

and **Stacks 0ESW** defines `c_p(E) ∈ A^p(X)` to be the class whose component in `A^p(X_r)` is
`c_p(E|_{X_r})`, the Chern class of the constant-rank module `E|_{X_r}`. Equivalently, and this
is how the source puts it, `c_p(E)` is the bivariant class which preserves the product
decompositions `CH_*(X') = ∏_r CH_*(X'_r)` of the Chow groups of every `X' ⟶ X` locally of finite
type and acts on the factors by the already defined operations `c_p(E|_{X_r}) ∩ -`.

## Main definitions

* `Stacks.Chow.bivariantClassCongr` — bivariant classes for two equal morphisms form the same
  group.
* `Stacks.Chow.pieceIdentityCongr` — a bivariant class for the restriction of the identity of `X`
  to a piece, read as a Chow cohomology class on that piece.
* `Stacks.Chow.rankLocusRestriction`, `Stacks.Chow.rankLocusAssembly` — the two directions of the
  product decomposition: restriction of a class in `A^p(X)` to the rank loci, and assembly of a
  family of classes on the rank loci.
* `Stacks.Chow.rankLocusChowCohomologyEquiv` — **Stacks 0ESW**, the isomorphism
  `A^p(X) = ∏_{r ≥ 0} A^p(X_r)` of the remark.
* `Stacks.Chow.rankLocusChernFamily` — the family `(c_p(E|_{X_r}))_r`, extended by zero in the
  degrees above the rank.
* `Stacks.Chow.chernClassArbitraryRank` — **Stacks 0ESW**, the class `c_p(E) ∈ A^p(X)`.

## Main results

* `Stacks.Chow.rankLocusRestriction_rankLocusAssembly`,
  `Stacks.Chow.rankLocusAssembly_rankLocusRestriction` — the two round trips of the product
  decomposition, so restriction to the rank loci is bijective.
* `Stacks.Chow.eq_of_rankLocusRestriction_eq` — a Chow cohomology class on `X` is determined by
  its restrictions to the rank loci.
* `Stacks.Chow.rankLocusRestriction_chernClassArbitraryRank` — **Stacks 0ESW**, the component of
  `c_p(E)` on `X_r` is `c_p(E|_{X_r})`, and is zero when `r < p`.
* `Stacks.Chow.isChernClassBivariant_rankLocusRestriction_chernClassArbitraryRank` —
  **Stacks 0ESW**, on `X_r` the class `c_p(E)` acts by the already defined operation
  `c_p(E|_{X_r}) ∩ -`: its component there satisfies the characterization of Stacks 0B7H for the
  restricted module.
* `Stacks.Chow.eq_chernClassArbitraryRank_of_rankLocusRestriction_eq` — `c_p(E)` is the only
  class with those components.

## Implementation notes

### The constant-rank Chern classes are a quantified family

Stacks 0B7H, which produces the Chern classes of a module of *constant* rank as bivariant
classes, is not available in this repository: only its characterization
`Stacks.Chow.IsChernClassBivariant` and the uniqueness that follows are, and the cap product they
are characterized against is itself the parameter `Stacks.Chow.HigherChernCapRule` standing in
for the unlanded Stacks 0B7G. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic`.

Stacks 0ESW does not construct those classes; it *cites* them, as "the already defined
operations `c_i(E|_{X_r}) ∩ -`". They are therefore carried here as a quantified family together
with the hypothesis that each member satisfies the characterization, which is the device
`Stacks.Chow.isTotalChernClass_bivariantFormalSum` uses for the same reason. What this file
constructs is the assembly, which is the content of the remark, and the `@[stacks 0ESW]`
attributes sit on that.

### Degrees above the rank

The constant-rank Chern classes of a module of rank `r` are indexed by `Fin (r + 1)`, so
`c_p(E|_{X_r})` is given only for `p ≤ r`; above the rank it is zero, and
`Stacks.Chow.rankLocusChernFamily` extends the family by zero accordingly. Since the rank varies,
`c_p(E)` can be nonzero for infinitely many `p`.

### The pieces of the identity decomposition

Chow cohomology `A^p(X)` is the bivariant group of the identity of `X`, and Stacks 0FDZ restricts
the identity to the piece `X_r` as `Stacks.Chow.pieceMap`, which is the identity of `X_r` but not
by definition. `Stacks.Chow.pieceMap_id` identifies the two and
`Stacks.Chow.pieceIdentityCongr` transports classes across that identification, so the components
of the product decomposition are genuine Chow cohomology classes of the pieces and the
characterization of Stacks 0B7H applies to them verbatim.

### The hypotheses carried

Stacks 02S1 and Stacks 02S2 along the legs of a cartesian square are theorems, not hypotheses,
of `Stacks.Chow.bivariantPieceEquiv` and `Stacks.Chow.bivariantPieceRestriction`: see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly`.
What remains, and what everything below carries, are the three Gysin compatibilities of the
`Stacks.Chow.GysinSystem` — the hypotheses of Stacks 0FDZ itself in this repository. Restriction
to the pieces needs only one of them, so it is stated with that.

### What is not covered

Three further assertions of the remark are not formalised here. The total Chern class
`c(E) = c_0(E) + c_1(E) + … ` as an element of the completed bivariant ring `A^*(X)^∧` of
Stacks 0FE0, `Stacks.Chow.completedBivariantGroup`, needs the restrictions of the `c_p(E)` to the
*connected components* of `X` and the vanishing of all but finitely many of them on each
component; the rank `r(E) ∈ A^0(X)`, the operation sending `(α_r)` to `(r α_r)`, needs a nonzero
degree-zero class on each piece, hence the two transported naturality axioms of
`Stacks.Chow.IdentityCapRule` that
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClass` records as missing; and the
centrality of `c_p(E)` and `r(E)` in `A^*(X)`, in the sense of
`Stacks.Chow.BivariantCommute`, needs the centrality of the constant-rank Chern classes, which
the remark also cites rather than proves.

## References

* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Transport along an equality of morphisms -/

section Congr

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- Bivariant classes for two equal morphisms are the same group. -/
def bivariantClassCongr {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (hff : f = f') (hf : f ≫ sY = sX) (hf' : f' ≫ sY = sX) (p : ℤ) :
    BivariantClass C G sX sY f hf p ≃+ BivariantClass C G sX sY f' hf' p := by
  subst hff
  exact AddEquiv.refl _

end Congr

/-! ### The pieces of the identity decomposition -/

section PieceIdentity

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] {I : Type u} (U : I → X.Opens)
  (ha : ∀ i, U i ≤ (𝟙 X) ⁻¹ᵁ U i) (p : ℤ) (i : I)

/-- A bivariant class for the restriction of the identity to a piece is a Chow cohomology class
on that piece. -/
def pieceIdentityCongr
    (hp : pieceMap (𝟙 X) U U id ha i ≫ ((U i).ι ≫ sX) = (U i).ι ≫ sX) :
    BivariantClass C G ((U i).ι ≫ sX) ((U i).ι ≫ sX) (pieceMap (𝟙 X) U U id ha i) hp p ≃+
      chowCohomologyComponent C G ((U i).ι ≫ sX) p :=
  bivariantClassCongr C G ((U i).ι ≫ sX) ((U i).ι ≫ sX) (pieceMap_id U ha i) hp
    (Category.id_comp _) p

end PieceIdentity

/-! ### The rank decomposition in Chow cohomology -/

section RankDecomposition

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- Each rank locus lies in its own preimage under the identity. -/
theorem rankLociFamily_le_preimage (i : ULift.{u} ℕ) :
    rankLociFamily E i ≤ (𝟙 X) ⁻¹ᵁ rankLociFamily E i := by simp

variable (hgysO : G.IsNaturalUnderOpenImmersion) (hgysR : G.IsNaturalUnderOpensRestriction)
  (hgysC : G.IsNaturalUnderPullbackComp) (p : ℤ)

/-- The restriction of a Chow cohomology class of `X` to the rank-`r` locus of `E`. -/
def rankLocusRestriction (c : chowCohomologyComponent C G sX p) (r : ℕ) :
    chowCohomologyComponent C G ((rankLocus E r).ι ≫ sX) p :=
  pieceIdentityCongr C G sX (rankLociFamily E) (rankLociFamily_le_preimage E) p (ULift.up r) _
    (bivariantPieceRestriction C G sX sX (𝟙 X) (Category.id_comp sX) p (rankLociFamily E)
      (rankLociFamily E) id (rankLociFamily_le_preimage E) (ULift.up r) hgysO c)

/-- The Chow cohomology class of `X` assembled from a family of classes on the rank loci. -/
def rankLocusAssembly
    (d : ∀ r : ℕ, chowCohomologyComponent C G ((rankLocus E r).ι ≫ sX) p) :
    chowCohomologyComponent C G sX p :=
  bivariantPieceAssembly C G sX sX (𝟙 X) (Category.id_comp sX) (rankLociFamily E)
    (rankLociFamily E) id (rankLociFamily_le_preimage E)
    (isClopenDecomposition_rankLociFamily E) p hgysO hgysR hgysC
    (fun i ↦ (pieceIdentityCongr C G sX (rankLociFamily E) (rankLociFamily_le_preimage E) p
      i _).symm (d i.down))

/-- Assembling a family of classes on the rank loci and restricting back to the rank-`r` locus
returns the `r`-th member of the family. -/
theorem rankLocusRestriction_rankLocusAssembly
    (d : ∀ r : ℕ, chowCohomologyComponent C G ((rankLocus E r).ι ≫ sX) p) (r : ℕ) :
    rankLocusRestriction C G sX E hgysO p
        (rankLocusAssembly C G sX E hgysO hgysR hgysC p d) r = d r :=
  Eq.trans
    (congrArg _
      (bivariantPieceRestriction_bivariantPieceAssembly C G sX sX (𝟙 X) (Category.id_comp sX)
        (rankLociFamily E) (rankLociFamily E) id (rankLociFamily_le_preimage E)
        (isClopenDecomposition_rankLociFamily E) p hgysO hgysR hgysC _
        (ULift.up r)))
    (AddEquiv.apply_symm_apply _ _)

/-- A Chow cohomology class is the one assembled from its restrictions to the rank loci. -/
theorem rankLocusAssembly_rankLocusRestriction (c : chowCohomologyComponent C G sX p) :
    rankLocusAssembly C G sX E hgysO hgysR hgysC p
        (rankLocusRestriction C G sX E hgysO p c) = c :=
  Eq.trans
    (congrArg (bivariantPieceAssembly C G sX sX (𝟙 X) (Category.id_comp sX) (rankLociFamily E)
      (rankLociFamily E) id (rankLociFamily_le_preimage E)
      (isClopenDecomposition_rankLociFamily E) p hgysO hgysR hgysC)
      (funext fun _ ↦ AddEquiv.symm_apply_apply _ _))
    ((bivariantPieceEquiv C G sX sX (𝟙 X) (Category.id_comp sX) (rankLociFamily E)
      (rankLociFamily E) id (rankLociFamily_le_preimage E)
      (isClopenDecomposition_rankLociFamily E) p hgysO hgysR
      hgysC).symm_apply_apply c)

/-- Restriction to the rank loci is additive. -/
theorem rankLocusRestriction_add (c c' : chowCohomologyComponent C G sX p) (r : ℕ) :
    rankLocusRestriction C G sX E hgysO p (c + c') r =
      rankLocusRestriction C G sX E hgysO p c r +
        rankLocusRestriction C G sX E hgysO p c' r :=
  Eq.trans
    (congrArg _
      (bivariantPieceRestriction_add C G sX sX (𝟙 X) (Category.id_comp sX) p (rankLociFamily E)
        (rankLociFamily E) id (rankLociFamily_le_preimage E) (ULift.up r) hgysO c c'))
    (map_add _ _ _)

/-- **Stacks 0ESW.** `A^p(X) = ∏_{r ≥ 0} A^p(X_r)` for the rank decomposition of `E`:
restriction to the rank loci is an isomorphism onto the product. -/
def rankLocusChowCohomologyEquiv :
    chowCohomologyComponent C G sX p ≃+
      ∀ r : ℕ, chowCohomologyComponent C G ((rankLocus E r).ι ≫ sX) p where
  toFun := rankLocusRestriction C G sX E hgysO p
  invFun := rankLocusAssembly C G sX E hgysO hgysR hgysC p
  left_inv := rankLocusAssembly_rankLocusRestriction C G sX E hgysO hgysR hgysC p
  right_inv d := funext
    (rankLocusRestriction_rankLocusAssembly C G sX E hgysO hgysR hgysC p d)
  map_add' c c' := funext (rankLocusRestriction_add C G sX E hgysO p c c')

include hgysR hgysC in
/-- A Chow cohomology class on `X` is determined by its restrictions to the rank loci. -/
theorem eq_of_rankLocusRestriction_eq {c d : chowCohomologyComponent C G sX p}
    (h : ∀ r : ℕ, rankLocusRestriction C G sX E hgysO p c r =
      rankLocusRestriction C G sX E hgysO p d r) : c = d :=
  (rankLocusChowCohomologyEquiv C G sX E hgysO hgysR hgysC p).injective (funext h)

end RankDecomposition

/-! ### The Chern classes of a module whose rank is not constant -/

section ChernClasses

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (hgysO : G.IsNaturalUnderOpenImmersion) (hgysR : G.IsNaturalUnderOpensRestriction)
  (hgysC : G.IsNaturalUnderPullbackComp)
  (caps : ∀ r : ℕ, HigherChernCapRule C r)
  (hrank : ∀ r : ℕ,
    PullbackPreservesRank ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r)
  (cc : ∀ (r : ℕ) (j : Fin (r + 1)),
    chowCohomologyComponent C G ((rankLocus E r).ι ≫ sX) (j : ℤ))

/-- The family `(c_n(E|_{X_r}))_r` of constant-rank Chern classes on the rank loci, extended by
zero in the degrees above the rank. -/
def rankLocusChernFamily (n r : ℕ) :
    chowCohomologyComponent C G ((rankLocus E r).ι ≫ sX) (n : ℤ) :=
  if h : n ≤ r then cc r ⟨n, Nat.lt_succ_of_le h⟩ else 0

/-- In degrees at most the rank, the family is the constant-rank Chern class. -/
theorem rankLocusChernFamily_of_le (n r : ℕ) (h : n ≤ r) :
    rankLocusChernFamily C G sX E cc n r = cc r ⟨n, Nat.lt_succ_of_le h⟩ := by
  simp only [rankLocusChernFamily, h, reduceDIte]

/-- In degrees above the rank, the family vanishes. -/
theorem rankLocusChernFamily_of_lt (n r : ℕ) (h : r < n) :
    rankLocusChernFamily C G sX E cc n r = 0 := by
  simp only [rankLocusChernFamily, Nat.not_le.mpr h, reduceDIte]

/-- **Stacks 0ESW.** The `n`-th Chern class `c_n(E) ∈ A^n(X)` of a finite locally free module of
not necessarily constant rank: the class which preserves the product decomposition of Chow
cohomology along the rank loci and whose component on `X_r` is `c_n(E|_{X_r})`. -/
@[stacks 0ESW "chern_classes_arbitrary_rank; the constant-rank Chern classes the remark cites enter as a quantified family; the classes of Tag 0B7H themselves are Stacks.Chow.GenuineChern.chernClassBivariantClass"]
def chernClassArbitraryRank (n : ℕ) : chowCohomologyComponent C G sX (n : ℤ) :=
  rankLocusAssembly C G sX E hgysO hgysR hgysC (n : ℤ)
    (rankLocusChernFamily C G sX E cc n)

/-- **Stacks 0ESW.** The component of `c_n(E)` on the rank-`r` locus is `c_n(E|_{X_r})`, and is
zero when `r < n`. -/
@[stacks 0ESW "chern_classes_arbitrary_rank; the constant-rank Chern classes the remark cites enter as a quantified family; the classes of Tag 0B7H themselves are Stacks.Chow.GenuineChern.chernClassBivariantClass"]
theorem rankLocusRestriction_chernClassArbitraryRank (n r : ℕ) :
    rankLocusRestriction C G sX E hgysO (n : ℤ)
        (chernClassArbitraryRank C G sX E hgysO hgysR hgysC cc n) r =
      rankLocusChernFamily C G sX E cc n r :=
  rankLocusRestriction_rankLocusAssembly C G sX E hgysO hgysR hgysC (n : ℤ) _ r

/-- **Stacks 0ESW.** On the rank-`r` locus, `c_n(E)` acts by the already defined operation
`c_n(E|_{X_r}) ∩ -`: its component there satisfies the characterization of Stacks 0B7H for the
restricted module. -/
@[stacks 0ESW "chern_classes_arbitrary_rank; the constant-rank Chern classes the remark cites enter as a quantified family; the classes of Tag 0B7H themselves are Stacks.Chow.GenuineChern.chernClassBivariantClass"]
theorem isChernClassBivariant_rankLocusRestriction_chernClassArbitraryRank
    (hcc : ∀ (r : ℕ) (j : Fin (r + 1)),
      IsChernClassBivariant C ((rankLocus E r).ι ≫ sX)
        ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r G (caps r) (hrank r) j (cc r j))
    (n r : ℕ) (h : n ≤ r) :
    IsChernClassBivariant C ((rankLocus E r).ι ≫ sX)
      ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r G (caps r) (hrank r)
      ⟨n, Nat.lt_succ_of_le h⟩
      (rankLocusRestriction C G sX E hgysO (n : ℤ)
        (chernClassArbitraryRank C G sX E hgysO hgysR hgysC cc n) r) := by
  rw [rankLocusRestriction_chernClassArbitraryRank C G sX E hgysO hgysR hgysC cc,
    rankLocusChernFamily_of_le C G sX E cc n r h]
  exact hcc r ⟨n, Nat.lt_succ_of_le h⟩

include hgysR hgysC in
/-- **Stacks 0ESW.** `c_n(E)` is the only class with these components, so the definition does
not depend on the way the family is assembled. -/
@[stacks 0ESW "chern_classes_arbitrary_rank; the constant-rank Chern classes the remark cites enter as a quantified family; the classes of Tag 0B7H themselves are Stacks.Chow.GenuineChern.chernClassBivariantClass"]
theorem eq_chernClassArbitraryRank_of_rankLocusRestriction_eq (n : ℕ)
    {c : chowCohomologyComponent C G sX (n : ℤ)}
    (h : ∀ r : ℕ, rankLocusRestriction C G sX E hgysO (n : ℤ) c r =
      rankLocusChernFamily C G sX E cc n r) :
    c = chernClassArbitraryRank C G sX E hgysO hgysR hgysC cc n :=
  eq_of_rankLocusRestriction_eq C G sX E hgysO hgysR hgysC (n : ℤ) fun r ↦
    (h r).trans (rankLocusRestriction_chernClassArbitraryRank C G sX E hgysO hgysR
      hgysC cc n r).symm

end ChernClasses

end Stacks.Chow

end
