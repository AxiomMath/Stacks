module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedAlgebra

/-!
# The Leibniz extension of a prescribed degree-one map on the generators of `O⟨S⟩`

Let `(C, O)` be a ringed site, let `𝒮` be a family of sheaves of graded sets on it and let
`O⟨S⟩` be the free graded `O`-algebra of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedAlgebra.lean`. The source's inductive
construction of the differential of `Aᵢ₊₁ = O⟨S₀ ⨿ … ⨿ Sᵢ₊₁⟩` prescribes a degree-one map
`δ` on the generators and extends it by the Leibniz rule. This file carries that out.

A `SheafOfModules.DerivationDatum` is the prescription: a local section `δ(x)` of `O⟨S⟩` of
degree `deg(x) + 1` for every letter `x`, compatible with restriction. Its Leibniz extension on
a word is the signed sum

`d(s₁ ⋯ s_r) = Σₐ (-1)^{deg(s₁) + … + deg(s_{a-1})} s₁ ⋯ s_{a-1} · δ(s_a) · s_{a+1} ⋯ s_r`,

written here as the recursion `d(x · w) = δ(x) · w + (-1)^{deg x} x · d(w)` on the word, and
`SheafOfModules.algD` is its unique extension to a morphism `O⟨S⟩ⁿ ⟶ O⟨S⟩ⁿ⁺¹` of sheaves of
modules.

## Multiplication read in a prescribed degree

Every degree identity in the formula above has the shape `m + j = n` with `n` the total degree
one is working in — for instance `(deg x + 1) + deg w = deg(x · w) + 1`. `SheafOfModules.mulAt`
is the product of two homogeneous local sections carrying that identity as an argument, so
that the *type* of a product is the degree one wants rather than the sum of the two degrees.
That is what keeps the transports out of the statements: `mulAt_naturality` has no transport
on either side, and `mulAt_castHom_left`, `mulAt_castHom_right` and `castHom_mulAt` absorb a
transport into the degree identity, which is a proof and therefore invisible to the kernel.

## Main definitions

* `SheafOfModules.mulAt` and its algebra: additivity, the two scalar laws, associativity
  (`mulAt_assoc`), the unit laws (`mulAt_one`, `one_mulAt` and their transported forms), the
  absorption lemmas and `mulAt_naturality`.
* `SheafOfModules.DerivationDatum` is a prescribed degree-one map on the generators.
* `SheafOfModules.wordD` is its **Leibniz extension evaluated on a word**.
* `SheafOfModules.wordDNat` is that extension as a morphism of presheaves of types,
  `SheafOfModules.algDHom` the induced morphism out of the presentation and
  `SheafOfModules.algD` **the differential of `O⟨S⟩`** obtained from it by sheafification.
* `SheafOfModules.algComplex` is the cochain complex of the pieces of `O⟨S⟩` with `algD` as
  its differential, and `SheafOfModules.freeDGAlgebra` is **`O⟨S⟩` as a sheaf of differential
  graded `O`-algebras**.

## Main results

* `SheafOfModules.mulAt_algSec`: the section attached to a concatenation of words is the
  product of the two sections, read in the degree of the concatenation.
* `SheafOfModules.mulAt_algGen_algSec`: prepending a letter to a word is multiplication by the
  generator of that letter.
* `SheafOfModules.wordD_naturality`: **the Leibniz extension commutes with restriction**, which
  is what makes it a morphism of presheaves and hence defines `algD`.
* `SheafOfModules.algD_algSec`: the differential of the section attached to a word is the
  Leibniz extension of `δ` on that word.
* `SheafOfModules.algD_algGen`: **the differential takes the prescribed value on every
  generator**, `d(x) = δ(x)`.
* `SheafOfModules.wordD_append`: **the Leibniz rule at the level of words**.
* `SheafOfModules.algD_algMul`: **the Leibniz rule for arbitrary local sections of `O⟨S⟩`**.
* `SheafOfModules.algD_algD`: **the square-zero law** `d ∘ d = 0`, under the hypothesis that
  every prescribed value `δ(x)` is closed.
* `SheafOfModules.freeDGAlgebra`: **`O⟨S⟩` with the Leibniz extension of a closed derivation
  datum as its differential, as a sheaf of differential graded `O`-algebras.**
* `SheafOfModules.algD_zero`: the differential attached to the zero derivation datum is zero,
  so the construction specialises to `SheafOfModules.freeDGAlgebraZero`.

## How the Leibniz rule and the square-zero law are proved

The word-level identity `SheafOfModules.wordD_append`,

`d(w · w') = d(w) · w' + (-1)^{deg w} w · d(w')`,

is an induction on `w` whose step is `mulAt_assoc` three times together with
`Int.negOnePow_add` for the sign. Every degree identity in it is a `mulAt` argument, so the
statement carries no transport at all. Three steps carry it to the differential graded algebra.

* `SheafOfModules.algDAdd_mulAdd` is the same identity on the presentation, for `algDAdd` and
  `mulAdd` in place of `wordD` and concatenation. It is a double `algSections_induction` down
  to `algOf`, where `mulAdd_algOf` and `algDHom_algOf` reduce it to `wordD_append`; the
  coefficients are carried through by the scalar laws `mulAt_smul_left` and `mulAt_smul_right`,
  and `w.2 : wordDeg w.1 = n` turns `(-1)^{deg w}` into `(-1)^n`. `algDAdd` and
  `algToSheafAdd` are the two maps out of the presentation written with their source type on
  the nose as a type of finitely supported functions, which is what lets `map_add` and
  `map_zero` apply to them.
* `SheafOfModules.algD_algMul` is the identity for arbitrary local sections, obtained from the
  previous item by lifting both arguments to the presentation on a common cover: `eq_of_lift₃`
  supplies the cover, `algMul_lift` computes the product there and `algD_toSheaf` the
  differential.
* `SheafOfModules.algD_algD` is `d ∘ d = 0` when every `δ(x)` is closed. `algD_wordD` is the
  statement on a word, an induction using `algD_algSec`, `algD_algGen` and `algD_mulAt`, in
  which the two middle terms carrying the signs `(-1)^{deg x + 1}` and `(-1)^{deg x}` cancel;
  `algD_algDAdd` carries it to the presentation and a single local lift to all sections.

`SheafOfModules.algDRel` re-indexes `algD` as the differential of a `ℤ`-indexed cochain
complex, `SheafOfModules.algComplex` is that complex, and `SheafOfModules.freeDGAlgebra`
is `O⟨S⟩` with it. The multiplication carries no Koszul sign, the coefficients sitting in
degree zero; all the signs are in the differential. Taking the derivation datum to be zero
recovers the earlier zero-differential stage: `SheafOfModules.algD_zero` and
`SheafOfModules.algDRel_zero`.

## Where this is used

Tag 0FU1 — the goodness of `O⟨S⟩` with a closed triangular derivation datum — is
`SheafOfModules.freeDGAlgebra_colimit_isGoodToposBaseChange` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedAlgebraGood.lean`, through
the weight filtration of `FreeDifferentialGradedAlgebraFiltration.lean`; the triangularity
condition is `SheafOfModules.DerivationDatum.IsTriangular` of
`FreeDifferentialGradedAlgebraTriangular.lean`.

Tag 0FU2 uses the universal property of `O⟨S⟩`: `SheafOfModules.LetterMap.dgLift` of
`FreeGradedAlgebraLift.lean` extends a map of sheaves of graded sets `S ⟶ B` compatible with the
differentials to a unital homomorphism `O⟨S⟩ ⟶ B`, and `SheafOfModules.freeDGAlgebra_hom_ext` is
its uniqueness; the tower is `DifferentialGradedAlgebraResolutionTower.lean`.

## References

* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
* [Stacks Project, Tag 0FU2](https://stacks.math.columbia.edu/tag/0FU2)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

section GradedAlgebraCast

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Transporting the second argument of the multiplication of a graded algebra along an equality of
degrees. -/
theorem GradedAlgebra.mul_castHom_right (A : GradedAlgebra.{t, t} R) {m j j' : ℤ} (h : j = j')
    (h' : m + j = m + j') (U : Cᵒᵖ) (y : (A.piece m).val.obj U) (c : (A.piece j).val.obj U) :
    (A.mul m j').app U y (castHom A.piece h U c) =
      castHom A.piece h' U ((A.mul m j).app U y c) := by
  subst h
  exact (eq_of_heq (heq_castHom A.piece h' U _)).symm

end GradedAlgebraCast

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J (Type t)] [HasWeakSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {I : Type t} (𝒮 : I → SheafOfGradedSets.{t} J)

/-! ### Multiplication landing in a prescribed degree

Every degree identity in the Leibniz rule has the shape `m + j = n` with `n` the total degree
one is working in. `mulAt` carries that identity as an argument, so the *type* of a product is
the degree one wants rather than the sum of the two degrees, and no transport appears on the
outside of a product. -/

/-- The product of two homogeneous local sections of `O⟨S⟩`, read in a prescribed total degree. -/
noncomputable def mulAt {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ)
    (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    (algPiece (Osharp := Osharp) 𝒮 n).val.obj U :=
  castHom (algPiece (Osharp := Osharp) 𝒮) h U ((algMul 𝒮 m j).app U a b)

/-- A product read in the degree `m + j` is the multiplication of `O⟨S⟩`. -/
theorem mulAt_rfl {m j : ℤ} (U : Cᵒᵖ)
    (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    mulAt 𝒮 (rfl : m + j = m + j) U a b = (algMul 𝒮 m j).app U a b := rfl

/-- A product read in a prescribed degree is additive in its first argument. -/
theorem mulAt_add_left {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ)
    (a a' : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    mulAt 𝒮 h U (a + a') b = mulAt 𝒮 h U a b + mulAt 𝒮 h U a' b := by
  rw [mulAt, mulAt, mulAt, (algMul 𝒮 m j).map_add_left, map_add]

/-- A product read in a prescribed degree is additive in its second argument. -/
theorem mulAt_add_right {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ)
    (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b b' : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    mulAt 𝒮 h U a (b + b') = mulAt 𝒮 h U a b + mulAt 𝒮 h U a b' := by
  rw [mulAt, mulAt, mulAt, map_add, map_add]

/-- A product read in a prescribed degree vanishes when its first argument is zero. -/
theorem mulAt_zero_left {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    mulAt 𝒮 h U (0 : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U) b = 0 := by
  have hz : (algMul 𝒮 m j).app U 0 b = 0 := by
    rw [map_zero ((algMul 𝒮 m j).app U)]
    rfl
  rw [mulAt, hz, Cofree.castHom_zero]

/-- A product read in a prescribed degree vanishes when its second argument is zero. -/
theorem mulAt_zero_right {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ)
    (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U) :
    mulAt 𝒮 h U a (0 : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) = 0 := by
  rw [mulAt, map_zero ((algMul 𝒮 m j).app U a), Cofree.castHom_zero]

/-- A product read in a prescribed degree commutes with integer multiples in its first argument. -/
theorem mulAt_zsmul_left {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (k : ℤ)
    (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    mulAt 𝒮 h U (k • a) b = k • mulAt 𝒮 h U a b := by
  have hz : (algMul 𝒮 m j).app U (k • a) b = k • (algMul 𝒮 m j).app U a b := by
    rw [map_zsmul ((algMul 𝒮 m j).app U) k a]
    rfl
  rw [mulAt, mulAt, hz, map_zsmul (castHom (algPiece (Osharp := Osharp) 𝒮) h U) k]

/-- A product read in a prescribed degree commutes with integer multiples in its second
argument. -/
theorem mulAt_zsmul_right {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (k : ℤ)
    (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    mulAt 𝒮 h U a (k • b) = k • mulAt 𝒮 h U a b := by
  rw [mulAt, mulAt, map_zsmul ((algMul 𝒮 m j).app U a) k b,
    map_zsmul (castHom (algPiece (Osharp := Osharp) 𝒮) h U) k]

/-- A product read in a prescribed degree is linear over the structure sheaf in its first
argument. -/
theorem mulAt_smul_left {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (r : secRing Osharp U)
    (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    mulAt 𝒮 h U (r • a) b = r • mulAt 𝒮 h U a b := by
  rw [mulAt, mulAt, (algMul 𝒮 m j).map_smul_left U r a b,
    castHom_smul (algPiece (Osharp := Osharp) 𝒮) h U r]

/-- A product read in a prescribed degree is linear over the structure sheaf in its second
argument. -/
theorem mulAt_smul_right {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (r : secRing Osharp U)
    (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    mulAt 𝒮 h U a (r • b) = r • mulAt 𝒮 h U a b := by
  rw [mulAt, mulAt, (algMul 𝒮 m j).map_smul_right U r a b,
    castHom_smul (algPiece (Osharp := Osharp) 𝒮) h U r]

/-- A transport in the first argument of a product is absorbed into its degree identity. -/
theorem mulAt_castHom_left {m m' j n : ℤ} (h₁ : m = m') (h : m' + j = n) (h' : m + j = n)
    (U : Cᵒᵖ) (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    mulAt 𝒮 h U (castHom (algPiece (Osharp := Osharp) 𝒮) h₁ U a) b = mulAt 𝒮 h' U a b := by
  subst h₁; rfl

/-- A transport in the second argument of a product is absorbed into its degree identity. -/
theorem mulAt_castHom_right {m j j' n : ℤ} (h₁ : j = j') (h : m + j' = n) (h' : m + j = n)
    (U : Cᵒᵖ) (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    mulAt 𝒮 h U a (castHom (algPiece (Osharp := Osharp) 𝒮) h₁ U b) = mulAt 𝒮 h' U a b := by
  subst h₁; rfl

/-- A transport of a product is absorbed into its degree identity. -/
theorem castHom_mulAt {m j n n' : ℤ} (h : m + j = n) (h₂ : n = n') (h' : m + j = n')
    (U : Cᵒᵖ) (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    castHom (algPiece (Osharp := Osharp) 𝒮) h₂ U (mulAt 𝒮 h U a b) = mulAt 𝒮 h' U a b := by
  subst h₂; rfl

/-- **A product read in a prescribed degree commutes with restriction**, with no transport on
either side. -/
theorem mulAt_naturality {m j n : ℤ} (h : m + j = n) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 n).val f (mulAt 𝒮 h U a b) =
      mulAt 𝒮 h V (Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 m).val f a)
        (Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 j).val f b) := by
  rw [mulAt, mulAt, sectionRestrict_castHom (algPiece (Osharp := Osharp) 𝒮) h f]
  exact congrArg (castHom (algPiece (Osharp := Osharp) 𝒮) h V)
    ((algMul 𝒮 m j).naturality f a b)

/-- **Associativity, read in a prescribed degree.** -/
theorem mulAt_assoc {m j k p q n : ℤ} (h₁ : m + j = p) (h : p + k = n) (h₂ : j + k = q)
    (h' : m + q = n) (U : Cᵒᵖ)
    (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U)
    (c : (algPiece (Osharp := Osharp) 𝒮 k).val.obj U) :
    mulAt 𝒮 h U (mulAt 𝒮 h₁ U a b) c = mulAt 𝒮 h' U a (mulAt 𝒮 h₂ U b c) := by
  subst h₁
  subst h₂
  exact Cofree.castHom_eq_castHom h h' U (algMul_assoc 𝒮 m j k U a b c)

/-- The unit of `O⟨S⟩` is a right identity for a product read in a prescribed degree. -/
theorem mulAt_one {n : ℤ} (h : n + 0 = n) (U : Cᵒᵖ)
    (a : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) :
    mulAt 𝒮 h U a ((algOne 𝒮).eval U) = a :=
  eq_of_heq ((heq_castHom (algPiece (Osharp := Osharp) 𝒮) h U _).trans (algMul_one 𝒮 n U a))

/-- The unit of `O⟨S⟩` is a left identity for a product read in a prescribed degree. -/
theorem one_mulAt {n : ℤ} (h : 0 + n = n) (U : Cᵒᵖ)
    (a : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) :
    mulAt 𝒮 h U ((algOne 𝒮).eval U) a = a :=
  eq_of_heq ((heq_castHom (algPiece (Osharp := Osharp) 𝒮) h U _).trans (algOne_mul 𝒮 n U a))

/-- Multiplying on the right by the unit of `O⟨S⟩`, read in a degree `n'` equal to `n`, is the
transport from degree `n` to degree `n'`. -/
theorem mulAt_one' {n n' : ℤ} (h : n + 0 = n') (h' : n = n') (U : Cᵒᵖ)
    (a : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) :
    mulAt 𝒮 h U a ((algOne 𝒮).eval U) =
      castHom (algPiece (Osharp := Osharp) 𝒮) h' U a := by
  subst h'
  exact mulAt_one 𝒮 h U a

/-- Multiplying on the left by the unit of `O⟨S⟩`, read in a degree `n'` equal to `n`, is the
transport from degree `n` to degree `n'`. -/
theorem one_mulAt' {n n' : ℤ} (h : 0 + n = n') (h' : n = n') (U : Cᵒᵖ)
    (a : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) :
    mulAt 𝒮 h U ((algOne 𝒮).eval U) a =
      castHom (algPiece (Osharp := Osharp) 𝒮) h' U a := by
  subst h'
  exact one_mulAt 𝒮 h U a

/-! ### Words, generators and products -/

/-- **The section attached to a concatenation of words is the product of the two sections.** -/
theorem mulAt_algSec {U : Cᵒᵖ} (w w' : Word 𝒮 U)
    (h : wordDeg w + wordDeg w' = wordDeg (w ++ w')) :
    mulAt 𝒮 h U (algSec (Osharp := Osharp) 𝒮 w) (algSec 𝒮 w') = algSec 𝒮 (w ++ w') := by
  rw [mulAt, algSec_def 𝒮 w, algSec_def 𝒮 w', algMul_toSheaf_right, mulLeft_toSheaf,
    mulAdd_algOf, mul_one, castHom_algToSheaf, algCast_algOf, algSec_def]
  rfl

/-- **The section attached to a word with a letter prepended is the generator of the letter times
the section attached to the rest of the word.** -/
theorem mulAt_algGen_algSec {U : Cᵒᵖ} (x : Letter 𝒮 U) (w : Word 𝒮 U)
    (h : letterDeg x + wordDeg w = wordDeg (x :: w)) :
    mulAt 𝒮 h U (algGen (Osharp := Osharp) 𝒮 x) (algSec 𝒮 w) = algSec 𝒮 (x :: w) := by
  rw [mulAt, algGen_def, algSec_def 𝒮 w, algMul_toSheaf_right, mulLeft_toSheaf, mulAdd_algOf,
    mul_one, castHom_algToSheaf, algCast_algOf, algSec_def]
  rfl

/-- The generator attached to a letter commutes with restriction. -/
theorem algGen_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (x : Letter 𝒮 U) :
    Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (letterDeg x)).val f
        (algGen 𝒮 x) =
      algGen (Osharp := Osharp) 𝒮 (letterMap f x) := by
  rw [algGen_def, algToSheaf_naturality, algRestrict_algOf, map_one, algGen_def]
  rfl

/-! ### The Leibniz extension of a derivation datum -/

/-- A *derivation datum* on a family of sheaves of graded sets: for every letter, a local section
of `O⟨S⟩` of degree one more than the letter, compatible with restriction. This is the source's
degree-one map `δ : S ⟶ O⟨S⟩` on generators. -/
structure DerivationDatum (𝒮 : I → SheafOfGradedSets.{t} J)
    (Osharp : Sheaf J CommRingCat.{t}) where
  /-- The prescribed value of the differential on the generator of a letter. -/
  app (U : Cᵒᵖ) (x : Letter 𝒮 U) :
    (algPiece (Osharp := Osharp) 𝒮 (letterDeg x + 1)).val.obj U
  /-- The prescribed values are compatible with restriction. -/
  naturality {U V : Cᵒᵖ} (f : U ⟶ V) (x : Letter 𝒮 U) :
    Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (letterDeg x + 1)).val f (app U x) =
      app V (letterMap f x)

variable (δ : DerivationDatum (Osharp := Osharp) 𝒮)

/-- **The Leibniz extension of `δ`, evaluated on a word**: the signed sum, over the letters of the
word, of the product of the prefix, the prescribed value on the letter and the suffix, written as a
recursion on the word. -/
noncomputable def wordD {U : Cᵒᵖ} : (w : Word 𝒮 U) →
    (algPiece (Osharp := Osharp) 𝒮 (wordDeg w + 1)).val.obj U
  | [] => 0
  | x :: w =>
      mulAt 𝒮 (by simp only [wordDeg_cons]; omega) U (δ.app U x) (algSec 𝒮 w)
        + (Int.negOnePow (letterDeg x) : ℤ) •
          mulAt 𝒮 (by simp only [wordDeg_cons]; omega) U (algGen 𝒮 x) (wordD w)

/-- The Leibniz extension of `δ` vanishes on the empty word. -/
@[simp] theorem wordD_nil (U : Cᵒᵖ) :
    wordD (Osharp := Osharp) 𝒮 δ ([] : Word 𝒮 U) = 0 := rfl

/-- The Leibniz extension of `δ` on the word `x · w` is `δ(x) · w + (-1)^{deg x} x · d(w)`, with
the products read in the degree of `x · w` plus one. -/
theorem wordD_cons {U : Cᵒᵖ} (x : Letter 𝒮 U) (w : Word 𝒮 U)
    (h₁ : letterDeg x + 1 + wordDeg w = wordDeg (x :: w) + 1)
    (h₂ : letterDeg x + (wordDeg w + 1) = wordDeg (x :: w) + 1) :
    wordD (Osharp := Osharp) 𝒮 δ (x :: w) =
      mulAt 𝒮 h₁ U (δ.app U x) (algSec 𝒮 w)
        + (Int.negOnePow (letterDeg x) : ℤ) •
          mulAt 𝒮 h₂ U (algGen 𝒮 x) (wordD 𝒮 δ w) := rfl

/-- A transport of `a · b + k • (c · d)` is absorbed into the degree identities of the products. -/
private theorem castHom_add_zsmul_mulAt {m j m' j' n n' : ℤ} (h : n = n') (h₁ : m + j = n)
    (h₂ : m' + j' = n) (h₁' : m + j = n') (h₂' : m' + j' = n') (k : ℤ) (U : Cᵒᵖ)
    (a : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U)
    (c : (algPiece (Osharp := Osharp) 𝒮 m').val.obj U)
    (d : (algPiece (Osharp := Osharp) 𝒮 j').val.obj U) :
    castHom (algPiece (Osharp := Osharp) 𝒮) h U (mulAt 𝒮 h₁ U a b + k • mulAt 𝒮 h₂ U c d) =
      mulAt 𝒮 h₁' U a b + k • mulAt 𝒮 h₂' U c d := by
  rw [map_add, map_zsmul, castHom_mulAt 𝒮 h₁ h h₁', castHom_mulAt 𝒮 h₂ h h₂']

/-- **The Leibniz extension commutes with restriction.** -/
theorem wordD_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (w : Word 𝒮 U) :
    Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (wordDeg w + 1)).val f
        (wordD 𝒮 δ w) =
      castHom (algPiece (Osharp := Osharp) 𝒮)
        (by rw [wordDeg_wordMap] : wordDeg (wordMap f w) + 1 = wordDeg w + 1) V
        (wordD 𝒮 δ (wordMap f w)) := by
  induction w with
  | nil => exact (map_zero _).trans (Cofree.castHom_zero _ _ _).symm
  | cons x w ih =>
    have ec : wordDeg (x :: w : Word 𝒮 U) = letterDeg x + wordDeg w := wordDeg_cons x w
    have ec' : wordDeg (letterMap f x :: wordMap f w : Word 𝒮 V) =
        letterDeg x + wordDeg (wordMap f w) := wordDeg_cons _ _
    have g1 : wordDeg (wordMap f w) = wordDeg w := wordDeg_wordMap f w
    have e1 : letterDeg x + 1 + wordDeg w = wordDeg (x :: w : Word 𝒮 U) + 1 := by omega
    have e2 : letterDeg x + (wordDeg w + 1) = wordDeg (x :: w : Word 𝒮 U) + 1 := by omega
    have e3 : letterDeg x + 1 + wordDeg (wordMap f w) =
        wordDeg (letterMap f x :: wordMap f w : Word 𝒮 V) + 1 := by omega
    have e4 : letterDeg x + (wordDeg (wordMap f w) + 1) =
        wordDeg (letterMap f x :: wordMap f w : Word 𝒮 V) + 1 := by omega
    have g2 : letterDeg x + 1 + wordDeg (wordMap f w) = wordDeg (x :: w : Word 𝒮 U) + 1 := by
      omega
    have g3 : wordDeg (wordMap f w) + 1 = wordDeg w + 1 := by omega
    have g4 : letterDeg x + (wordDeg (wordMap f w) + 1) =
        wordDeg (x :: w : Word 𝒮 U) + 1 := by omega
    have gg : wordDeg (wordMap f (x :: w)) = wordDeg (x :: w : Word 𝒮 U) :=
      wordDeg_wordMap f (x :: w)
    have hh : wordDeg (wordMap f (x :: w)) + 1 = wordDeg (x :: w : Word 𝒮 U) + 1 := by omega
    rw [wordD_cons 𝒮 δ x w e1 e2, map_add,
      map_zsmul _ (Int.negOnePow (letterDeg x) : ℤ),
      mulAt_naturality, mulAt_naturality, δ.naturality f x, algSec_naturality,
      algGen_naturality, ih, mulAt_castHom_right 𝒮 g1 e1 g2,
      mulAt_castHom_right 𝒮 g3 e2 g4]
    exact (castHom_add_zsmul_mulAt 𝒮 hh e3 e4 g2 g4 _ V _ _ _ _).symm

/-! ### The differential of `O⟨S⟩` -/

/-- The Leibniz extension of `δ`, as a morphism of presheaves of types from the words of degree `n`
to the degree-`n+1` piece of `O⟨S⟩`. -/
noncomputable def wordDNat (n : ℤ) :
    wordPresheaf 𝒮 n ⟶
      (algPiece (Osharp := Osharp) 𝒮 (n + 1)).val.presheaf ⋙ CategoryTheory.forget _ where
  app U := ↾fun w =>
    castHom (algPiece (Osharp := Osharp) 𝒮) (congrArg (fun z => z + 1) w.2) U
      (wordD 𝒮 δ w.1)
  naturality {U V} f := by
    ext w
    refine Eq.symm ?_
    change Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (n + 1)).val f
        (castHom (algPiece (Osharp := Osharp) 𝒮) (congrArg (fun z => z + 1) w.2) U
          (wordD 𝒮 δ w.1)) = _
    rw [sectionRestrict_castHom (algPiece (Osharp := Osharp) 𝒮) _ f, wordD_naturality,
      Cofree.castHom_castHom]
    exact Cofree.castHom_eq_castHom _ _ V (HEq.refl _)

/-- The Leibniz extension of `δ`, as a morphism of presheaves of modules out of the presentation of
the degree-`n` piece. -/
noncomputable def algDHom (n : ℤ) :
    algPres (Osharp := Osharp) 𝒮 n ⟶ (algPiece (Osharp := Osharp) 𝒮 (n + 1)).val :=
  PresheafOfModules.freeObjDesc (wordDNat 𝒮 δ n)

/-- The morphism `algDHom` sends the basis element of a word of degree `n` to the Leibniz extension
of `δ` on that word. -/
theorem algDHom_word (n : ℤ) (U : Cᵒᵖ) (w : WordIdx 𝒮 n U) :
    (algDHom 𝒮 δ n).app U (algOf 𝒮 n w 1) =
      castHom (algPiece (Osharp := Osharp) 𝒮) (congrArg (fun z => z + 1) w.2) U
        (wordD 𝒮 δ w.1) :=
  ModuleCat.freeDesc_apply ((wordDNat 𝒮 δ n).app U) w

/-- The morphism `algDHom` sends `r` times the basis element of a word of degree `n` to `r` times
the Leibniz extension of `δ` on that word. -/
theorem algDHom_algOf (n : ℤ) (U : Cᵒᵖ) (w : WordIdx 𝒮 n U) (r : secRing Osharp U) :
    (algDHom 𝒮 δ n).app U (algOf 𝒮 n w r) =
      r • castHom (algPiece (Osharp := Osharp) 𝒮) (congrArg (fun z => z + 1) w.2) U
        (wordD 𝒮 δ w.1) := by
  rw [algOf_eq_smul]
  exact ((((algDHom 𝒮 δ n).app U).hom.map_smul r _).trans
    (congrArg (fun z => r • z) (algDHom_word 𝒮 δ n U w)))

/-- The Leibniz extension of `δ` on the presentation over an object of the site, as an additive map
whose source is written plainly as a type of finitely supported functions. -/
noncomputable def algDAdd (n : ℤ) (U : Cᵒᵖ) :
    algSections Osharp 𝒮 n U →+ (algPiece (Osharp := Osharp) 𝒮 (n + 1)).val.obj U :=
  ((algDHom 𝒮 δ n).app U).hom.toAddMonoidHom

/-- The additive map `algDAdd` is the component of `algDHom` over `U`. -/
@[simp] theorem algDAdd_apply (n : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U) :
    algDAdd 𝒮 δ n U a = (algDHom 𝒮 δ n).app U a := rfl

/-- **The differential of `O⟨S⟩` attached to a derivation datum**: the unique extension to the
sheafification of the Leibniz extension of `δ`. -/
noncomputable def algD (n : ℤ) :
    algPiece (Osharp := Osharp) 𝒮 n ⟶ algPiece (Osharp := Osharp) 𝒮 (n + 1) :=
  ⟨(PresheafOfModules.sheafifyHomEquiv' (𝟙 (toRingCat J Osharp).obj)
      (CategoryTheory.toSheafify J (algPres (Osharp := Osharp) 𝒮 n).presheaf)
      (algPiece (Osharp := Osharp) 𝒮 (n + 1)).isSheaf).symm (algDHom 𝒮 δ n)⟩

/-- The differential of `O⟨S⟩` restricts to the Leibniz extension on the presentation. -/
theorem algD_toSheaf (n : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U) :
    (algD 𝒮 δ n).val.app U ((algToSheaf 𝒮 n).app U a) = (algDHom 𝒮 δ n).app U a :=
  congrArg (fun φ : (algPres (Osharp := Osharp) 𝒮 n).presheaf ⟶
      (algPiece (Osharp := Osharp) 𝒮 (n + 1)).val.presheaf => φ.app U a)
    (PresheafOfModules.comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom
      (𝟙 (toRingCat J Osharp).obj)
      (CategoryTheory.toSheafify J (algPres (Osharp := Osharp) 𝒮 n).presheaf)
      (algPiece (Osharp := Osharp) 𝒮 (n + 1)).isSheaf (algDHom 𝒮 δ n))

/-- **The differential of `O⟨S⟩` on the section attached to a word is the Leibniz extension of `δ`
on that word.** -/
theorem algD_algSec {U : Cᵒᵖ} (w : Word 𝒮 U) :
    (algD 𝒮 δ (wordDeg w)).val.app U (algSec (Osharp := Osharp) 𝒮 w) = wordD 𝒮 δ w := by
  rw [algSec_def, algD_toSheaf, algDHom_word]
  exact eq_of_heq (heq_castHom (algPiece (Osharp := Osharp) 𝒮) _ U _)

/-- The Leibniz extension of `δ` on a one-letter word is the prescribed value of `δ` on that
letter. -/
theorem wordD_singleton {U : Cᵒᵖ} (x : Letter 𝒮 U)
    (h : letterDeg x + 1 = wordDeg ([x] : Word 𝒮 U) + 1) :
    wordD (Osharp := Osharp) 𝒮 δ [x] =
      castHom (algPiece (Osharp := Osharp) 𝒮) h U (δ.app U x) := by
  have ea : wordDeg ([] : Word 𝒮 U) = 0 := rfl
  have eb : wordDeg ([x] : Word 𝒮 U) = letterDeg x + wordDeg ([] : Word 𝒮 U) :=
    wordDeg_cons x []
  have h1 : letterDeg x + 1 + wordDeg ([] : Word 𝒮 U) =
      wordDeg ([x] : Word 𝒮 U) + 1 := by omega
  have h2 : letterDeg x + (wordDeg ([] : Word 𝒮 U) + 1) =
      wordDeg ([x] : Word 𝒮 U) + 1 := by omega
  rw [wordD_cons 𝒮 δ x [] h1 h2, wordD_nil, mulAt_zero_right, smul_zero, add_zero]
  exact mulAt_one' 𝒮 h1 h U (δ.app U x)

/-- **The differential of `O⟨S⟩` takes the prescribed value on every generator.** -/
theorem algD_algGen {U : Cᵒᵖ} (x : Letter 𝒮 U) :
    (algD 𝒮 δ (letterDeg x)).val.app U (algGen (Osharp := Osharp) 𝒮 x) = δ.app U x := by
  have eb : wordDeg ([x] : Word 𝒮 U) = letterDeg x + wordDeg ([] : Word 𝒮 U) :=
    wordDeg_cons x []
  have ea : wordDeg ([] : Word 𝒮 U) = 0 := rfl
  have h : letterDeg x + 1 = wordDeg ([x] : Word 𝒮 U) + 1 := by omega
  rw [algGen_def, algD_toSheaf, algDHom_word, wordD_singleton 𝒮 δ x h,
    Cofree.castHom_castHom]
  exact eq_of_heq (heq_castHom (algPiece (Osharp := Osharp) 𝒮) _ U _)

/-- **The Leibniz rule for the Leibniz extension, at the level of words.** -/
theorem wordD_append {U : Cᵒᵖ} (w w' : Word 𝒮 U) :
    wordD (Osharp := Osharp) 𝒮 δ (w ++ w') =
      mulAt 𝒮 (by simp only [wordDeg_append]; omega) U (wordD 𝒮 δ w) (algSec 𝒮 w')
        + (Int.negOnePow (wordDeg w) : ℤ) •
          mulAt 𝒮 (by simp only [wordDeg_append]; omega) U (algSec 𝒮 w)
            (wordD 𝒮 δ w') := by
  induction w with
  | nil =>
    have hA : mulAt 𝒮 (by simp only [wordDeg_append]; omega : wordDeg ([] : Word 𝒮 U) + 1 +
          wordDeg w' = wordDeg (([] : Word 𝒮 U) ++ w') + 1) U
          (wordD (Osharp := Osharp) 𝒮 δ ([] : Word 𝒮 U)) (algSec 𝒮 w') = 0 :=
      mulAt_zero_left 𝒮 _ U _
    have hB : mulAt 𝒮 (by simp only [wordDeg_append]; omega : wordDeg ([] : Word 𝒮 U) +
          (wordDeg w' + 1) = wordDeg (([] : Word 𝒮 U) ++ w') + 1) U
          (algSec (Osharp := Osharp) 𝒮 ([] : Word 𝒮 U)) (wordD 𝒮 δ w') =
        wordD 𝒮 δ w' :=
      one_mulAt' 𝒮 _ rfl U _
    have hsign : (Int.negOnePow (wordDeg ([] : Word 𝒮 U)) : ℤ) = 1 := by
      change (Int.negOnePow (0 : ℤ) : ℤ) = 1
      rw [Int.negOnePow_zero, Units.val_one]
    rw [hA, hB, hsign, one_zsmul, zero_add]
    rfl
  | cons x v ih =>
    have ec1 : wordDeg (x :: v : Word 𝒮 U) = letterDeg x + wordDeg v := wordDeg_cons x v
    have ec2 : wordDeg (v ++ w' : Word 𝒮 U) = wordDeg v + wordDeg w' := wordDeg_append v w'
    have ec3 : wordDeg ((x :: v) ++ w' : Word 𝒮 U) =
        letterDeg x + wordDeg (v ++ w' : Word 𝒮 U) := wordDeg_cons x (v ++ w')
    have G1 : letterDeg x + 1 + wordDeg v = wordDeg (x :: v : Word 𝒮 U) + 1 := by omega
    have G2 : letterDeg x + (wordDeg v + 1) = wordDeg (x :: v : Word 𝒮 U) + 1 := by omega
    have F2 : letterDeg x + wordDeg v = wordDeg (x :: v : Word 𝒮 U) := by omega
    have B : wordDeg v + wordDeg w' = wordDeg (v ++ w' : Word 𝒮 U) := by omega
    have C1 : wordDeg v + 1 + wordDeg w' = wordDeg (v ++ w' : Word 𝒮 U) + 1 := by omega
    have C2 : wordDeg v + (wordDeg w' + 1) = wordDeg (v ++ w' : Word 𝒮 U) + 1 := by omega
    have A1 : letterDeg x + 1 + wordDeg (v ++ w' : Word 𝒮 U) =
        wordDeg ((x :: v) ++ w' : Word 𝒮 U) + 1 := by omega
    have A2 : letterDeg x + (wordDeg (v ++ w' : Word 𝒮 U) + 1) =
        wordDeg ((x :: v) ++ w' : Word 𝒮 U) + 1 := by omega
    have H1 : wordDeg (x :: v : Word 𝒮 U) + 1 + wordDeg w' =
        wordDeg ((x :: v) ++ w' : Word 𝒮 U) + 1 := by omega
    have H2 : wordDeg (x :: v : Word 𝒮 U) + (wordDeg w' + 1) =
        wordDeg ((x :: v) ++ w' : Word 𝒮 U) + 1 := by omega
    have hL1 : wordD (Osharp := Osharp) 𝒮 δ ((x :: v) ++ w') =
        mulAt 𝒮 A1 U (δ.app U x) (algSec 𝒮 (v ++ w'))
          + (Int.negOnePow (letterDeg x) : ℤ) •
            mulAt 𝒮 A2 U (algGen 𝒮 x) (wordD 𝒮 δ (v ++ w')) :=
      wordD_cons 𝒮 δ x (v ++ w') A1 A2
    have hSec : algSec (Osharp := Osharp) 𝒮 (v ++ w') =
        mulAt 𝒮 B U (algSec 𝒮 v) (algSec 𝒮 w') := (mulAt_algSec 𝒮 v w' B).symm
    have hSecCons : algSec (Osharp := Osharp) 𝒮 (x :: v) =
        mulAt 𝒮 F2 U (algGen 𝒮 x) (algSec 𝒮 v) := (mulAt_algGen_algSec 𝒮 x v F2).symm
    have hRcons : wordD (Osharp := Osharp) 𝒮 δ (x :: v) =
        mulAt 𝒮 G1 U (δ.app U x) (algSec 𝒮 v)
          + (Int.negOnePow (letterDeg x) : ℤ) •
            mulAt 𝒮 G2 U (algGen 𝒮 x) (wordD 𝒮 δ v) :=
      wordD_cons 𝒮 δ x v G1 G2
    have ih' : wordD (Osharp := Osharp) 𝒮 δ (v ++ w') =
        mulAt 𝒮 C1 U (wordD 𝒮 δ v) (algSec 𝒮 w')
          + (Int.negOnePow (wordDeg v) : ℤ) •
            mulAt 𝒮 C2 U (algSec 𝒮 v) (wordD 𝒮 δ w') := ih
    have hsign : ((Int.negOnePow (letterDeg x) : ℤ) * (Int.negOnePow (wordDeg v) : ℤ)) =
        (Int.negOnePow (wordDeg (x :: v : Word 𝒮 U)) : ℤ) := by
      rw [← Units.val_mul, ← Int.negOnePow_add, ec1]
    change wordD (Osharp := Osharp) 𝒮 δ ((x :: v) ++ w') =
      mulAt 𝒮 H1 U (wordD 𝒮 δ (x :: v)) (algSec 𝒮 w')
        + (Int.negOnePow (wordDeg (x :: v : Word 𝒮 U)) : ℤ) •
          mulAt 𝒮 H2 U (algSec 𝒮 (x :: v)) (wordD 𝒮 δ w')
    rw [hL1, hSec, hRcons, ih', hSecCons, mulAt_add_right, mulAt_zsmul_right,
      mulAt_add_left, mulAt_zsmul_left, mulAt_assoc 𝒮 G1 H1 B A1,
      mulAt_assoc 𝒮 G2 H1 C1 A2, mulAt_assoc 𝒮 F2 H2 C2 A2, smul_add, smul_smul,
      add_assoc, hsign]

/-! ### The Leibniz rule on the presentation -/

/-- A product of two scalar multiples of transported sections is the product of the scalars times
the product of the sections, read in the degree identity of the sections. -/
private theorem mulAt_smul_castHom_smul_castHom {m m' j j' n : ℤ} (h : m + j = n)
    (h' : m' + j' = n) (e₁ : m' = m) (e₂ : j' = j) (U : Cᵒᵖ) (r s : secRing Osharp U)
    (a : (algPiece (Osharp := Osharp) 𝒮 m').val.obj U)
    (b : (algPiece (Osharp := Osharp) 𝒮 j').val.obj U) :
    mulAt 𝒮 h U (r • castHom (algPiece (Osharp := Osharp) 𝒮) e₁ U a)
        (s • castHom (algPiece (Osharp := Osharp) 𝒮) e₂ U b) = (r * s) • mulAt 𝒮 h' U a b := by
  have h'' : m + j' = n := by omega
  rw [mulAt_smul_left, mulAt_smul_right, mulAt_castHom_right 𝒮 e₂ h h'',
    mulAt_castHom_left 𝒮 e₁ h'' h', smul_smul]

/-- **The Leibniz rule for the Leibniz extension, on the presentation of `O⟨S⟩`.** -/
theorem algDAdd_mulAdd (n i : ℤ) (U : Cᵒᵖ) (h₁ : n + 1 + i = n + i + 1)
    (h₂ : n + (i + 1) = n + i + 1) (a : algSections Osharp 𝒮 n U)
    (b : algSections Osharp 𝒮 i U) :
    algDAdd 𝒮 δ (n + i) U (mulAdd 𝒮 n i U a b) =
      mulAt 𝒮 h₁ U (algDAdd 𝒮 δ n U a) (algToSheafAdd 𝒮 i U b)
        + (Int.negOnePow n : ℤ) •
          mulAt 𝒮 h₂ U (algToSheafAdd 𝒮 n U a) (algDAdd 𝒮 δ i U b) := by
  induction a using algSections_induction with
  | hzero =>
    rw [map_zero (mulAdd 𝒮 n i U), AddMonoidHom.zero_apply, map_zero, map_zero, map_zero,
      mulAt_zero_left, mulAt_zero_left, smul_zero, add_zero]
  | hadd a a' ha ha' =>
    rw [map_add (mulAdd 𝒮 n i U), AddMonoidHom.add_apply, map_add, ha, ha', map_add, map_add,
      mulAt_add_left, mulAt_add_left, smul_add]
    abel
  | hof w r =>
    induction b using algSections_induction with
    | hzero =>
      rw [map_zero (mulAdd 𝒮 n i U (algOf 𝒮 n w r)), map_zero, map_zero, map_zero,
        mulAt_zero_right, mulAt_zero_right, smul_zero, add_zero]
    | hadd b b' hb hb' =>
      rw [map_add (mulAdd 𝒮 n i U (algOf 𝒮 n w r)), map_add, hb, hb', map_add, map_add,
        mulAt_add_right, mulAt_add_right, smul_add]
      abel
    | hof w' s =>
      have e : wordDeg w.1 = n := w.2
      have e' : wordDeg w'.1 = i := w'.2
      have dw : wordDeg w.1 + 1 = n + 1 := by omega
      have dw' : wordDeg w'.1 + 1 = i + 1 := by omega
      have ea : wordDeg (w.1 ++ w'.1) = wordDeg w.1 + wordDeg w'.1 := wordDeg_append w.1 w'.1
      have WA : wordDeg (w.1 ++ w'.1) + 1 = n + i + 1 := by omega
      have P1 : wordDeg w.1 + 1 + wordDeg w'.1 = wordDeg (w.1 ++ w'.1) + 1 := by omega
      have P2 : wordDeg w.1 + (wordDeg w'.1 + 1) = wordDeg (w.1 ++ w'.1) + 1 := by omega
      have Q1 : wordDeg w.1 + 1 + wordDeg w'.1 = n + i + 1 := by omega
      have Q2 : wordDeg w.1 + (wordDeg w'.1 + 1) = n + i + 1 := by omega
      have hsign : (Int.negOnePow (wordDeg w.1) : ℤ) = (Int.negOnePow n : ℤ) := by rw [e]
      have hAp : wordD (Osharp := Osharp) 𝒮 δ (w.1 ++ w'.1) =
          mulAt 𝒮 P1 U (wordD 𝒮 δ w.1) (algSec 𝒮 w'.1)
            + (Int.negOnePow (wordDeg w.1) : ℤ) •
              mulAt 𝒮 P2 U (algSec 𝒮 w.1) (wordD 𝒮 δ w'.1) :=
        wordD_append 𝒮 δ w.1 w'.1
      have hcomm : ∀ (k : ℤ) (z : (algPiece (Osharp := Osharp) 𝒮 (n + i + 1)).val.obj U),
          (r * s) • (k • z) = k • ((r * s) • z) := fun k z =>
        map_zsmul (AddMonoidHom.mk' (fun z => (r * s) • z) (smul_add (r * s))) k z
      have hLHS : algDAdd 𝒮 δ (n + i) U
            (mulAdd 𝒮 n i U (algOf 𝒮 n w r) (algOf 𝒮 i w' s)) =
          (r * s) • (mulAt 𝒮 Q1 U (wordD 𝒮 δ w.1) (algSec 𝒮 w'.1)
            + (Int.negOnePow n : ℤ) •
              mulAt 𝒮 Q2 U (algSec 𝒮 w.1) (wordD 𝒮 δ w'.1)) := by
        rw [mulAdd_algOf, algDAdd_apply, algDHom_algOf]
        change (r * s) • castHom (algPiece (Osharp := Osharp) 𝒮) WA U
            (wordD 𝒮 δ (w.1 ++ w'.1)) = _
        rw [hAp, castHom_add_zsmul_mulAt 𝒮 WA P1 P2 Q1 Q2, hsign]
      have hR1 : mulAt 𝒮 h₁ U (algDAdd 𝒮 δ n U (algOf 𝒮 n w r))
            (algToSheafAdd 𝒮 i U (algOf 𝒮 i w' s)) =
          (r * s) • mulAt 𝒮 Q1 U (wordD 𝒮 δ w.1) (algSec 𝒮 w'.1) := by
        rw [algDAdd_apply, algToSheafAdd_apply, algDHom_algOf,
          algToSheaf_algOf]
        exact mulAt_smul_castHom_smul_castHom 𝒮 h₁ Q1 dw e' U r s _ _
      have hR2 : mulAt 𝒮 h₂ U (algToSheafAdd 𝒮 n U (algOf 𝒮 n w r))
            (algDAdd 𝒮 δ i U (algOf 𝒮 i w' s)) =
          (r * s) • mulAt 𝒮 Q2 U (algSec 𝒮 w.1) (wordD 𝒮 δ w'.1) := by
        rw [algDAdd_apply, algToSheafAdd_apply, algToSheaf_algOf, algDHom_algOf]
        exact mulAt_smul_castHom_smul_castHom 𝒮 h₂ Q2 e dw' U r s _ _
      rw [hR1, hR2, hLHS, smul_add, hcomm]

/-- **The Leibniz rule for the Leibniz extension, on the presentation of `O⟨S⟩`**, written for the
morphisms `algDHom` and `algToSheaf` themselves. -/
theorem algDHom_mulAdd (n i : ℤ) (U : Cᵒᵖ) (h₁ : n + 1 + i = n + i + 1)
    (h₂ : n + (i + 1) = n + i + 1) (a : algSections Osharp 𝒮 n U)
    (b : algSections Osharp 𝒮 i U) :
    (algDHom 𝒮 δ (n + i)).app U (mulAdd 𝒮 n i U a b) =
      mulAt 𝒮 h₁ U ((algDHom 𝒮 δ n).app U a) ((algToSheaf 𝒮 i).app U b)
        + (Int.negOnePow n : ℤ) •
          mulAt 𝒮 h₂ U ((algToSheaf 𝒮 n).app U a) ((algDHom 𝒮 δ i).app U b) :=
  algDAdd_mulAdd 𝒮 δ n i U h₁ h₂ a b

/-! ### The Leibniz rule on `O⟨S⟩` -/

/-- The differential of `O⟨S⟩` commutes with restriction. -/
theorem algD_naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) :
    Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (n + 1)).val f
        ((algD 𝒮 δ n).val.app U x) =
      (algD 𝒮 δ n).val.app V (Stacks.sectionRestrict (algPiece 𝒮 n).val f x) :=
  (PresheafOfModules.naturality_apply (algD 𝒮 δ n).val f x).symm

/-- **The Leibniz rule for the differential of `O⟨S⟩`**: for arbitrary homogeneous local sections,
`d(a · b) = d(a) · b + (-1)^{deg a} a · d(b)`. Both degree identities are carried by `mulAt`, so
the identity holds on the nose with no transport. -/
theorem algD_algMul (n i : ℤ) (U : Cᵒᵖ) (h₁ : n + 1 + i = n + i + 1)
    (h₂ : n + (i + 1) = n + i + 1)
    (x : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U)
    (y : (algPiece (Osharp := Osharp) 𝒮 i).val.obj U) :
    (algD 𝒮 δ (n + i)).val.app U ((algMul 𝒮 n i).app U x y) =
      mulAt 𝒮 h₁ U ((algD 𝒮 δ n).val.app U x) y
        + (Int.negOnePow n : ℤ) • mulAt 𝒮 h₂ U x ((algD 𝒮 δ i).val.app U y) := by
  refine eq_of_lift₃ 𝒮 x y y _ _ ?_
  intro Y f a b _ ha hb _
  have hdx : Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (n + 1)).val f
      ((algD 𝒮 δ n).val.app U x) = (algDHom 𝒮 δ n).app Y a := by
    rw [algD_naturality, ← ha, algD_toSheaf]
  have hdy : Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (i + 1)).val f
      ((algD 𝒮 δ i).val.app U y) = (algDHom 𝒮 δ i).app Y b := by
    rw [algD_naturality, ← hb, algD_toSheaf]
  have hL : Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (n + i + 1)).val f
      ((algD 𝒮 δ (n + i)).val.app U ((algMul 𝒮 n i).app U x y)) =
        (algDHom 𝒮 δ (n + i)).app Y (mulAdd 𝒮 n i Y a b) := by
    rw [algD_naturality, algMul_lift 𝒮 n i U x y f a b ha hb, algD_toSheaf]
  have hR : Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (n + i + 1)).val f
      (mulAt 𝒮 h₁ U ((algD 𝒮 δ n).val.app U x) y
        + (Int.negOnePow n : ℤ) • mulAt 𝒮 h₂ U x ((algD 𝒮 δ i).val.app U y)) =
        mulAt 𝒮 h₁ Y ((algDHom 𝒮 δ n).app Y a) ((algToSheaf 𝒮 i).app Y b)
          + (Int.negOnePow n : ℤ) •
            mulAt 𝒮 h₂ Y ((algToSheaf 𝒮 n).app Y a) ((algDHom 𝒮 δ i).app Y b) := by
    rw [map_add, map_zsmul
        (Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (n + i + 1)).val f),
      mulAt_naturality, mulAt_naturality, hdx, hdy, ha, hb]
  rw [hL, hR, algDHom_mulAdd]

/-- The Leibniz rule for the differential of `O⟨S⟩`, with the degree of the product prescribed. -/
theorem algD_mulAt {m j n : ℤ} (h : m + j = n) (h₁ : m + 1 + j = n + 1)
    (h₂ : m + (j + 1) = n + 1) (U : Cᵒᵖ)
    (x : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (y : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    (algD 𝒮 δ n).val.app U (mulAt 𝒮 h U x y) =
      mulAt 𝒮 h₁ U ((algD 𝒮 δ m).val.app U x) y
        + (Int.negOnePow m : ℤ) • mulAt 𝒮 h₂ U x ((algD 𝒮 δ j).val.app U y) := by
  subst h
  rw [mulAt_rfl]
  exact algD_algMul 𝒮 δ m j U h₁ h₂ x y

/-- Transport along an equality of degrees commutes with the differential of `O⟨S⟩`. -/
theorem algD_castHom_arg {k n : ℤ} (h : k = n) (h' : k + 1 = n + 1) (U : Cᵒᵖ)
    (z : (algPiece (Osharp := Osharp) 𝒮 k).val.obj U) :
    (algD 𝒮 δ n).val.app U (castHom (algPiece (Osharp := Osharp) 𝒮) h U z) =
      castHom (algPiece (Osharp := Osharp) 𝒮) h' U ((algD 𝒮 δ k).val.app U z) := by
  subst h; rfl

/-! ### The differential re-indexed for a cochain complex -/

/-- The differential of `O⟨S⟩` re-indexed as the differential of a `ℤ`-indexed cochain complex: it
is `algD` followed by the transport of degrees when the two degrees are consecutive, and zero
otherwise. -/
noncomputable def algDRel (n m : ℤ) :
    algPiece (Osharp := Osharp) 𝒮 n ⟶ algPiece (Osharp := Osharp) 𝒮 m :=
  if h : n + 1 = m then
    algD 𝒮 δ n ≫ eqToHom (congrArg (algPiece (Osharp := Osharp) 𝒮) h)
  else 0

/-- The re-indexed differential `algDRel n m` is zero unless `m = n + 1`. -/
theorem algDRel_eq_zero {n m : ℤ} (h : ¬ n + 1 = m) : algDRel (Osharp := Osharp) 𝒮 δ n m = 0 :=
  dite_eq_right h

/-- The re-indexed differential from degree `n` to degree `n + 1` is `algD`. -/
@[simp] theorem algDRel_self (n : ℤ) :
    algDRel (Osharp := Osharp) 𝒮 δ n (n + 1) = algD 𝒮 δ n := by
  rw [algDRel, dite_eq_left (rfl : n + 1 = n + 1)]
  exact Category.comp_id _

/-! ### The zero derivation datum

Specialising the construction to the derivation datum which is zero on every generator recovers
the zero differential, hence the stage `A₀ = O⟨S₀⟩` of `freeDGAlgebraZero`. -/

variable (Osharp) in
/-- The derivation datum which prescribes the value zero on every generator. -/
noncomputable def DerivationDatum.zero : DerivationDatum 𝒮 Osharp where
  app _ _ := 0
  naturality f x :=
    map_zero (Stacks.sectionRestrict
      (algPiece (Osharp := Osharp) 𝒮 (letterDeg x + 1)).val f)

/-- The zero derivation datum takes the value zero on every letter. -/
@[simp] theorem DerivationDatum.zero_app (U : Cᵒᵖ) (x : Letter 𝒮 U) :
    (DerivationDatum.zero Osharp 𝒮).app U x = 0 := rfl

/-- The Leibniz extension of the zero derivation datum vanishes on every word. -/
@[simp] theorem wordD_zero {U : Cᵒᵖ} (w : Word 𝒮 U) :
    wordD 𝒮 (DerivationDatum.zero Osharp 𝒮) w = 0 := by
  induction w with
  | nil => rfl
  | cons x v ih =>
    have e1 : letterDeg x + 1 + wordDeg v = wordDeg (x :: v : Word 𝒮 U) + 1 := by
      simp only [wordDeg_cons]; omega
    have e2 : letterDeg x + (wordDeg v + 1) = wordDeg (x :: v : Word 𝒮 U) + 1 := by
      simp only [wordDeg_cons]; omega
    rw [wordD_cons 𝒮 (DerivationDatum.zero Osharp 𝒮) x v e1 e2,
      DerivationDatum.zero_app, mulAt_zero_left, ih, mulAt_zero_right, smul_zero, add_zero]

/-- The Leibniz extension of the zero derivation datum vanishes on the presentation. -/
theorem algDAdd_zero (n : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U) :
    algDAdd 𝒮 (DerivationDatum.zero Osharp 𝒮) n U a = 0 := by
  induction a using algSections_induction with
  | hzero => exact map_zero _
  | hadd a a' ha ha' => rw [map_add, ha, ha', add_zero]
  | hof w r =>
    rw [algDAdd_apply, algDHom_algOf, wordD_zero, Cofree.castHom_zero, smul_zero]

/-- **The differential attached to the zero derivation datum is zero.** -/
theorem algD_zero (n : ℤ) :
    algD 𝒮 (DerivationDatum.zero Osharp 𝒮) n =
      (0 : algPiece (Osharp := Osharp) 𝒮 n ⟶ algPiece (Osharp := Osharp) 𝒮 (n + 1)) := by
  refine algPiece_hom_ext 𝒮 fun U a => ?_
  refine (algD_toSheaf 𝒮 (DerivationDatum.zero Osharp 𝒮) n U a).trans ?_
  refine (algDAdd_zero 𝒮 n U a).trans ?_
  exact (map_zero (((0 : algPiece (Osharp := Osharp) 𝒮 n ⟶
    algPiece (Osharp := Osharp) 𝒮 (n + 1)).val.app U).hom)).symm

/-- The zero derivation datum is closed, so it exhibits `O⟨S⟩` with the zero differential as a
sheaf of differential graded algebras. -/
theorem derivationDatum_zero_closed (U : Cᵒᵖ) (x : Letter 𝒮 U) :
    (algD 𝒮 (DerivationDatum.zero Osharp 𝒮) (letterDeg x + 1)).val.app U
        ((DerivationDatum.zero Osharp 𝒮).app U x) = 0 :=
  map_zero _

/-- The cochain complex attached to the zero derivation datum has zero differential, so it is the
complex of `freeDGAlgebraZero`. -/
@[simp] theorem algDRel_zero (n m : ℤ) :
    algDRel 𝒮 (DerivationDatum.zero Osharp 𝒮) n m = 0 := by
  rw [algDRel]
  split
  · rw [algD_zero, zero_comp]
  · rfl

/-! ### The square-zero law

Under the hypothesis that every prescribed value `δ(x)` is closed, the differential of `O⟨S⟩`
squares to zero. The hypothesis is exactly what the source's inductive construction arranges:
`δ(x)` is a closed section of the previous stage of the tower. -/

variable (hδ : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
  (algD 𝒮 δ (letterDeg x + 1)).val.app U (δ.app U x) = 0)

include hδ

/-- **The Leibniz extension of a closed derivation datum is closed on every word.** The two middle
terms of the induction, carrying the signs `(-1)^{deg x + 1}` and `(-1)^{deg x}`, cancel. -/
theorem algD_wordD {U : Cᵒᵖ} (w : Word 𝒮 U) :
    (algD 𝒮 δ (wordDeg w + 1)).val.app U (wordD 𝒮 δ w) = 0 := by
  induction w with
  | nil => rw [wordD_nil]; exact map_zero _
  | cons x w ih =>
    have ec1 : wordDeg (x :: w : Word 𝒮 U) = letterDeg x + wordDeg w := wordDeg_cons x w
    have G1 : letterDeg x + 1 + wordDeg w = wordDeg (x :: w : Word 𝒮 U) + 1 := by omega
    have G2 : letterDeg x + (wordDeg w + 1) = wordDeg (x :: w : Word 𝒮 U) + 1 := by omega
    have K1 : letterDeg x + 1 + 1 + wordDeg w =
        wordDeg (x :: w : Word 𝒮 U) + 1 + 1 := by omega
    have K2 : letterDeg x + 1 + (wordDeg w + 1) =
        wordDeg (x :: w : Word 𝒮 U) + 1 + 1 := by omega
    have L2 : letterDeg x + (wordDeg w + 1 + 1) =
        wordDeg (x :: w : Word 𝒮 U) + 1 + 1 := by omega
    rw [wordD_cons 𝒮 δ x w G1 G2, map_add,
      map_zsmul,
      algD_mulAt 𝒮 δ G1 K1 K2, algD_mulAt 𝒮 δ G2 K2 L2, hδ U x, algD_algSec, algD_algGen, ih,
      mulAt_zero_left, mulAt_zero_right, smul_zero, zero_add, add_zero, Int.negOnePow_succ,
      Units.val_neg, neg_smul, neg_add_cancel]

/-- The Leibniz extension of a closed derivation datum is closed on the presentation. -/
theorem algD_algDAdd (n : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U) :
    (algD 𝒮 δ (n + 1)).val.app U (algDAdd 𝒮 δ n U a) = 0 := by
  induction a using algSections_induction with
  | hzero => rw [map_zero (algDAdd 𝒮 δ n U)]; exact map_zero _
  | hadd a a' ha ha' => rw [map_add (algDAdd 𝒮 δ n U), map_add, ha, ha', add_zero]
  | hof w r =>
    have e : wordDeg w.1 = n := w.2
    have dw : wordDeg w.1 + 1 = n + 1 := by omega
    have dw' : wordDeg w.1 + 1 + 1 = n + 1 + 1 := by omega
    rw [algDAdd_apply, algDHom_algOf]
    change (algD 𝒮 δ (n + 1)).val.app U
        (r • castHom (algPiece (Osharp := Osharp) 𝒮) dw U (wordD 𝒮 δ w.1)) = 0
    rw [((algD 𝒮 δ (n + 1)).val.app U).hom.map_smul r, algD_castHom_arg 𝒮 δ dw dw',
      algD_wordD 𝒮 δ hδ w.1, Cofree.castHom_zero, smul_zero]

/-- **The differential of `O⟨S⟩` squares to zero** when every prescribed value `δ(x)` is closed. -/
theorem algD_algD (n : ℤ) (U : Cᵒᵖ) (z : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) :
    (algD 𝒮 δ (n + 1)).val.app U ((algD 𝒮 δ n).val.app U z) = 0 := by
  refine Stacks.eq_of_forall_lift
    (algPiece (Osharp := Osharp) 𝒮 (n + 1 + 1)).isSheaf.isSeparated (algToSheaf 𝒮 n) z _ _ ?_
  intro Y f a ha
  have ha' : (algToSheaf 𝒮 n).app Y a =
      Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 n).val f z := ha
  change Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (n + 1 + 1)).val f
      ((algD 𝒮 δ (n + 1)).val.app U ((algD 𝒮 δ n).val.app U z)) =
    Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (n + 1 + 1)).val f 0
  rw [map_zero, algD_naturality, algD_naturality, ← ha']
  exact (congrArg (fun c => (algD 𝒮 δ (n + 1)).val.app Y c)
    (algD_toSheaf 𝒮 δ n Y a)).trans (algD_algDAdd 𝒮 δ hδ n Y a)

/-! ### `O⟨S⟩` as a sheaf of differential graded algebras -/

/-- **The differential of `O⟨S⟩` squares to zero as a morphism of sheaves of modules.** -/
theorem algD_comp_algD (n : ℤ) : algD 𝒮 δ n ≫ algD 𝒮 δ (n + 1) = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  exact algD_algD 𝒮 δ hδ n U z

/-- The cochain complex of the pieces of `O⟨S⟩` with the Leibniz extension of `δ` as its
differential. -/
noncomputable def algComplex : CochainComplex (SheafOfModules.{t} (toRingCat J Osharp)) ℤ where
  X := algPiece (Osharp := Osharp) 𝒮
  d := algDRel 𝒮 δ
  shape _ _ h := algDRel_eq_zero 𝒮 δ h
  d_comp_d' i j k hij hjk := by
    have hij' : i + 1 = j := hij
    have hjk' : j + 1 = k := hjk
    subst hij'
    subst hjk'
    rw [algDRel_self, algDRel_self]
    exact algD_comp_algD 𝒮 δ hδ i

/-- The degree-`n` object of `algComplex` is the degree-`n` piece of `O⟨S⟩`. -/
@[simp] theorem algComplex_X (n : ℤ) :
    (algComplex 𝒮 δ hδ).X n = algPiece (Osharp := Osharp) 𝒮 n := rfl

/-- The differential of `algComplex` from degree `n` to degree `n + 1` is `algD`. -/
@[simp] theorem algComplex_d (n : ℤ) :
    (algComplex 𝒮 δ hδ).d n (n + 1) = algD 𝒮 δ n :=
  algDRel_self 𝒮 δ n

/-- **`O⟨S⟩` as a sheaf of differential graded `O`-algebras**, with the Leibniz extension of a
closed derivation datum `δ` as its differential. This is the stage `Aᵢ₊₁ = O⟨S₀ ⨿ … ⨿ Sᵢ₊₁⟩` of the
source's tower: the generators are free, the differential is prescribed on them and extended by the
Leibniz rule. -/
noncomputable def freeDGAlgebra : DifferentialGradedAlgebra.{t, t} (toRingCat J Osharp) where
  complex := algComplex 𝒮 δ hδ
  mul n i := algMul 𝒮 n i
  one := algOne 𝒮
  mul_assoc n i j U x y z := algMul_assoc 𝒮 n i j U x y z
  one_mul n U x := algOne_mul 𝒮 n U x
  mul_one n U x := algMul_one 𝒮 n U x
  leibniz n i U x y := by
    rw [algComplex_d, algComplex_d, algComplex_d, ← castHom_apply, ← castHom_apply]
    exact algD_algMul 𝒮 δ n i U (add_right_comm n 1 i) (add_assoc n i 1).symm x y

/-- The degree-`n` object of the complex underlying `freeDGAlgebra` is the degree-`n` piece of
`O⟨S⟩`. -/
@[simp] theorem freeDGAlgebra_complex_X (n : ℤ) :
    (freeDGAlgebra 𝒮 δ hδ).complex.X n = algPiece (Osharp := Osharp) 𝒮 n := rfl

/-- The differential of `freeDGAlgebra` from degree `n` to degree `n + 1` is `algD`. -/
@[simp] theorem freeDGAlgebra_complex_d (n : ℤ) :
    (freeDGAlgebra 𝒮 δ hδ).complex.d n (n + 1) = algD 𝒮 δ n :=
  algDRel_self 𝒮 δ n

/-- The multiplication of `freeDGAlgebra` is the multiplication `algMul` of `O⟨S⟩`. -/
@[simp] theorem freeDGAlgebra_mul (n i : ℤ) :
    (freeDGAlgebra 𝒮 δ hδ).mul n i = algMul 𝒮 n i := rfl

/-- The unit of `freeDGAlgebra` is the unit `algOne` of `O⟨S⟩`. -/
@[simp] theorem freeDGAlgebra_one : (freeDGAlgebra 𝒮 δ hδ).one = algOne 𝒮 := rfl

/-- The graded algebra underlying `O⟨S⟩` with the Leibniz extension of `δ` is `O⟨S⟩`. -/
theorem freeDGAlgebra_toGradedAlgebra :
    (freeDGAlgebra 𝒮 δ hδ).toGradedAlgebra = freeGradedAlgebra 𝒮 := rfl

end SheafOfModules

end
