module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedAlgebraWords
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksCore.Tactic.StacksAttribute

/-!
# The free graded `O`-algebra on a sheaf of graded sets

Let `(C, O)` be a ringed site and let `𝒮 : I → SheafOfGradedSets J` be a family of sheaves of
graded sets on it. This file constructs

`O⟨S⟩ = O ⊕ ⨁_{r ≥ 1} O[S × ⋯ × S]`

as a sheaf of graded `O`-algebras, with concatenation of words as multiplication, and as a
sheaf of differential graded `O`-algebras with zero differential. Here `S` is the coproduct
`⨿ⱼ 𝒮 j`, which is never formed: the homogeneous local sections of `S` over `U` are the letters
of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedAlgebraWords.lean`, and the
local sections of `S × ⋯ × S` are the words.

## The construction

The degree-`n` piece of `O⟨S⟩` is the sheafification of the free `O`-module on the presheaf of
words of total degree `n`,

`U ↦ ⨁_{w a word over U with deg(w) = n} w · O(U)`,

which is Mathlib's `PresheafOfModules.freeObj` at `wordPresheaf 𝒮 n`. The multiplication is the
unique extension to the sheafification, in both variables, of concatenation of words and
multiplication of coefficients on the presentation.

**There are no Koszul signs in the multiplication.** The coefficients of `O⟨S⟩` sit in degree
zero, so moving a coefficient past a generator costs `(-1)^(0 · deg) = 1`. The signs of the
source appear in the *differential*, which is built in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedAlgebra.lean`.

## Main definitions

* `SheafOfModules.algPres` is the presentation of the degree-`n` piece, `SheafOfModules.algOf`
  its summand indexed by a word with a prescribed coefficient, `SheafOfModules.algRestrict` its
  restriction maps and `SheafOfModules.mulPres` its multiplication.
* `SheafOfModules.algPiece` is the degree-`n` piece of `O⟨S⟩`, the sheafification of the
  presentation, and `SheafOfModules.algToSheaf` the canonical morphism to it.
* `SheafOfModules.algMul` is the multiplication of `O⟨S⟩`, `SheafOfModules.algOne` its unit,
  `SheafOfModules.algSec` the section attached to a word and `SheafOfModules.algGen` the
  canonical generator attached to a letter.
* `SheafOfModules.freeGradedAlgebra` is **the free graded `O`-algebra `O⟨S⟩`**.
* `SheafOfModules.freeDGAlgebraZero` is `O⟨S⟩` as a sheaf of differential graded `O`-algebras
  with zero differential — the source's base stage `A₀ = O⟨S₀⟩`, whose generators are closed.

## Main results

* `SheafOfModules.algMul_assoc`, `SheafOfModules.algOne_mul` and `SheafOfModules.algMul_one`:
  the multiplication is associative and unital.
* `SheafOfModules.algSec_append`: **the section attached to a concatenation of words is the
  product of the two sections**, so the multiplication really is concatenation.
* `SheafOfModules.algMul_lift`: the value of the multiplication, computed on local lifts of
  both arguments to the presentation.
* `SheafOfModules.algPiece_hom_ext` and `SheafOfModules.eq_of_lift₃`: a morphism out of a piece
  of `O⟨S⟩` is determined by its restriction to the presentation, and three sections of pieces
  of `O⟨S⟩` lift locally all at once.

## Implementation notes

All four universes of the construction are forced to be one universe `t`: Mathlib's
`PresheafOfModules.freeObj` takes a presheaf of types and a presheaf of rings in the same
universe, and the free module on the words then lives in that universe too. That is exactly the
shape `SheafOfModules.DifferentialGradedAlgebra.{t, t} (toRingCat J Osharp)` in which the
neighbouring tags of this chapter are stated.

The base is a sheaf of *commutative* rings, not an arbitrary sheaf of rings as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModule.lean`. Commutativity is used and
is not decoration: bilinearity of the multiplication in the coefficient of its second argument
is `a * (r * b) = r * (a * b)`. A ringed site carries a sheaf of commutative rings, so nothing
is lost.

Multiplication is extended to the sheafification one variable at a time with
`Stacks.BilinearMap.extend`, as the action of `A` on `A[S]` is in `FreeGradedModule.lean`: a
bilinear map into a sheaf extends uniquely along a locally bijective morphism, and
`PresheafOfModules.toSheafify` is locally bijective. `SheafOfModules.mulLeft` is the
half-extended map and `SheafOfModules.algMul` the fully extended one.

Sections of the presentation are written with the plainly-typed `algSections`, `algOf` and
`algRestrict` rather than through `PresheafOfModules.obj` and `PresheafOfModules.map`: a goal
mixing the two spellings is not type-correct at `implicit` transparency, so `rw` refuses it,
exactly as recorded in the implementation notes of `FreeGradedModule.lean`.

## References

* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
* [Stacks Project, Tag 0FU2](https://stacks.math.columbia.edu/tag/0FU2)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

section FinsuppMul

variable {A : Type t} [CommRing A] {X Y Z : Type t}

/-- A singleton finitely supported function is a scalar multiple of a basis vector. -/
theorem single_eq_smul_single (x : X) (r : A) :
    (Finsupp.single x r : X →₀ A) = r • Finsupp.single x 1 := by
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Two bilinear maps on free modules agree as soon as they agree on pairs of basis vectors. -/
theorem finsupp_bilin_ext {f g : (X →₀ A) →ₗ[A] (Y →₀ A) →ₗ[A] (Z →₀ A)}
    (h : ∀ (x : X) (y : Y), f (Finsupp.single x 1) (Finsupp.single y 1) =
      g (Finsupp.single x 1) (Finsupp.single y 1)) : f = g := by
  refine Finsupp.lhom_ext fun x r => ?_
  refine Finsupp.lhom_ext fun y s => ?_
  rw [single_eq_smul_single x r, single_eq_smul_single y s]
  simp only [map_smul, LinearMap.smul_apply, h x y]

/-- The bilinear map on free modules determined by a map on pairs of basis vectors. -/
noncomputable def finsuppBilin (m : X → Y → Z) :
    (X →₀ A) →ₗ[A] (Y →₀ A) →ₗ[A] (Z →₀ A) :=
  Finsupp.lift _ A X fun x => Finsupp.lift _ A Y fun y => Finsupp.single (m x y) 1

/-- `finsuppBilin m` sends `single x r` and `single y s` to `single (m x y) (r * s)`. -/
@[simp] theorem finsuppBilin_single (m : X → Y → Z) (x : X) (y : Y) (r s : A) :
    finsuppBilin (A := A) m (Finsupp.single x r) (Finsupp.single y s) =
      Finsupp.single (m x y) (r * s) := by
  rw [finsuppBilin, Finsupp.lift_apply, Finsupp.sum_single_index (by simp),
    LinearMap.smul_apply, Finsupp.lift_apply, Finsupp.sum_single_index (by simp),
    smul_smul, Finsupp.smul_single, smul_eq_mul, mul_one]

end FinsuppMul

section Presentation

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J (Type t)]
  {I : Type t} (𝒮 : I → SheafOfGradedSets.{t} J)

variable (Osharp) in
/-- The commutative ring of sections of the structure sheaf over an object of the site. -/
abbrev secRing (U : Cᵒᵖ) : Type t := (toRingCat J Osharp).obj.obj U

variable (Osharp) in
/-- The sections of the presentation of the degree-`n` piece of the free graded `O`-algebra:
finitely supported `O(U)`-valued functions on the words of degree `n`. -/
abbrev algSections (n : ℤ) (U : Cᵒᵖ) : Type t := WordIdx 𝒮 n U →₀ secRing Osharp U

/-- Concatenation of a word of degree `n` with a word of degree `i`. -/
def wordIdxAppend (n i : ℤ) {U : Cᵒᵖ} (w : WordIdx 𝒮 n U) (w' : WordIdx 𝒮 i U) :
    WordIdx 𝒮 (n + i) U :=
  ⟨w.1 ++ w'.1, by rw [wordDeg_append, w.2, w'.2]⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The underlying word of a concatenation is the concatenation of the underlying words. -/
@[simp] theorem wordIdxAppend_val (n i : ℤ) {U : Cᵒᵖ} (w : WordIdx 𝒮 n U)
    (w' : WordIdx 𝒮 i U) : (wordIdxAppend 𝒮 n i w w').1 = w.1 ++ w'.1 := rfl

/-- The presentation of the degree-`n` piece of the free graded `O`-algebra: the free
`O`-module on the words of degree `n`. -/
noncomputable def algPres (n : ℤ) : PresheafOfModules.{t} (toRingCat J Osharp).obj :=
  PresheafOfModules.freeObj (R := (toRingCat J Osharp).obj) (wordPresheaf 𝒮 n)

/-- The sections of the presentation are the finitely supported functions on words. -/
theorem algPres_obj (n : ℤ) (U : Cᵒᵖ) :
    (algPres (Osharp := Osharp) 𝒮 n).obj U =
      ModuleCat.of (secRing Osharp U) (algSections Osharp 𝒮 n U) := rfl

/-- The summand of the presentation indexed by a word of degree `n`, with coefficient `r`. -/
noncomputable def algOf (n : ℤ) {U : Cᵒᵖ} (w : WordIdx 𝒮 n U) (r : secRing Osharp U) :
    algSections Osharp 𝒮 n U :=
  Finsupp.single w r

/-- The summand of a word with coefficient `r` is `r` times the summand with coefficient `1`. -/
theorem algOf_eq_smul (n : ℤ) {U : Cᵒᵖ} (w : WordIdx 𝒮 n U) (r : secRing Osharp U) :
    algOf (Osharp := Osharp) 𝒮 n w r = r • algOf 𝒮 n w 1 :=
  single_eq_smul_single w r

/-- The summand of a word is additive in its coefficient. -/
theorem algOf_add (n : ℤ) {U : Cᵒᵖ} (w : WordIdx 𝒮 n U) (r r' : secRing Osharp U) :
    algOf (Osharp := Osharp) 𝒮 n w (r + r') = algOf 𝒮 n w r + algOf 𝒮 n w r' :=
  Finsupp.single_add w r r'

/-- The summand of a word with coefficient `0` is zero. -/
@[simp] theorem algOf_zero (n : ℤ) {U : Cᵒᵖ} (w : WordIdx 𝒮 n U) :
    algOf (Osharp := Osharp) 𝒮 n w 0 = 0 :=
  Finsupp.single_zero w

/-- Two additive maps out of the presentation agree as soon as they agree on the summands. -/
theorem algSections_addHom_ext {n : ℤ} {U : Cᵒᵖ} {G : Type*} [AddCommMonoid G]
    {φ ψ : algSections Osharp 𝒮 n U →+ G}
    (h : ∀ (w : WordIdx 𝒮 n U) (r : secRing Osharp U),
      φ (algOf 𝒮 n w r) = ψ (algOf 𝒮 n w r)) : φ = ψ :=
  Finsupp.addHom_ext fun w r => h w r

/-- An induction principle for sections of the presentation. -/
theorem algSections_induction {n : ℤ} {U : Cᵒᵖ} {P : algSections Osharp 𝒮 n U → Prop}
    (hzero : P 0) (hof : ∀ (w : WordIdx 𝒮 n U) (r : secRing Osharp U), P (algOf 𝒮 n w r))
    (hadd : ∀ a b, P a → P b → P (a + b)) (a : algSections Osharp 𝒮 n U) : P a :=
  Finsupp.induction_linear a hzero hadd hof

/-- The restriction maps of the presentation, with their target type written plainly. -/
noncomputable def algRestrict (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    algSections Osharp 𝒮 n U →+ algSections Osharp 𝒮 n V :=
  Stacks.sectionRestrict (algPres (Osharp := Osharp) 𝒮 n) f

/-- Restriction in the presentation is semilinear along the restriction map of `O`. -/
theorem algRestrict_smul (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (r : secRing Osharp U)
    (a : algSections Osharp 𝒮 n U) :
    algRestrict 𝒮 n f (r • a) = (toRingCat J Osharp).obj.map f r • algRestrict 𝒮 n f a :=
  Stacks.sectionRestrict_smul (algPres (Osharp := Osharp) 𝒮 n) f r a

/-- Restriction sends the basis vector of a word to the basis vector of the restricted word. -/
theorem algRestrict_word (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (w : WordIdx 𝒮 n U) :
    algRestrict (Osharp := Osharp) 𝒮 n f (algOf 𝒮 n w 1) = algOf 𝒮 n (wordIdxMap n f w) 1 := by
  have h := NatTrans.naturality_apply
    (PresheafOfModules.freeAdjunctionUnit (toRingCat J Osharp).obj (wordPresheaf 𝒮 n)) f w
  exact h.symm

/-- Restriction sends the summand of a word with coefficient `r` to the summand of the
restricted word with the restricted coefficient. -/
@[simp] theorem algRestrict_algOf (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (w : WordIdx 𝒮 n U)
    (r : secRing Osharp U) :
    algRestrict (Osharp := Osharp) 𝒮 n f (algOf 𝒮 n w r) =
      algOf 𝒮 n (wordIdxMap n f w) ((toRingCat J Osharp).obj.map f r) := by
  rw [algOf_eq_smul, algRestrict_smul, algRestrict_word, ← algOf_eq_smul]

/-- Multiplication on the presentation: concatenation of words and multiplication of
coefficients. There is no Koszul sign here, the coefficients sitting in degree zero. -/
noncomputable def mulLin (n i : ℤ) (U : Cᵒᵖ) :
    algSections Osharp 𝒮 n U →ₗ[secRing Osharp U]
      (algSections Osharp 𝒮 i U →ₗ[secRing Osharp U] algSections Osharp 𝒮 (n + i) U) :=
  finsuppBilin (wordIdxAppend 𝒮 n i)

/-- Multiplication on the presentation, as a biadditive map on sections. -/
noncomputable def mulAdd (n i : ℤ) (U : Cᵒᵖ) :
    algSections Osharp 𝒮 n U →+
      (algSections Osharp 𝒮 i U →+ algSections Osharp 𝒮 (n + i) U) :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk' (fun b => mulLin 𝒮 n i U a b)
      (fun b b' => map_add (mulLin 𝒮 n i U a) b b'))
    (fun a a' => AddMonoidHom.ext fun b => by
      change mulLin 𝒮 n i U (a + a') b = mulLin 𝒮 n i U a b + mulLin 𝒮 n i U a' b
      rw [map_add, LinearMap.add_apply])

/-- The biadditive multiplication of the presentation agrees with the bilinear one. -/
theorem mulAdd_apply (n i : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U)
    (b : algSections Osharp 𝒮 i U) : mulAdd 𝒮 n i U a b = mulLin 𝒮 n i U a b := rfl

/-- The product of the summands of two words is the summand of their concatenation, with the
product of the coefficients. -/
@[simp] theorem mulAdd_algOf (n i : ℤ) (U : Cᵒᵖ) (w : WordIdx 𝒮 n U) (w' : WordIdx 𝒮 i U)
    (r s : secRing Osharp U) :
    mulAdd (Osharp := Osharp) 𝒮 n i U (algOf 𝒮 n w r) (algOf 𝒮 i w' s) =
      algOf 𝒮 (n + i) (wordIdxAppend 𝒮 n i w w') (r * s) :=
  finsuppBilin_single (wordIdxAppend 𝒮 n i) w w' r s

/-- Multiplication on the presentation is linear in its first argument. -/
theorem mulAdd_smul_left (n i : ℤ) (U : Cᵒᵖ) (r : secRing Osharp U)
    (a : algSections Osharp 𝒮 n U) (b : algSections Osharp 𝒮 i U) :
    mulAdd 𝒮 n i U (r • a) b = r • mulAdd 𝒮 n i U a b := by
  show mulLin 𝒮 n i U (r • a) b = r • mulLin 𝒮 n i U a b
  rw [map_smul, LinearMap.smul_apply]

/-- Multiplication on the presentation is linear in its second argument. -/
theorem mulAdd_smul_right (n i : ℤ) (U : Cᵒᵖ) (r : secRing Osharp U)
    (a : algSections Osharp 𝒮 n U) (b : algSections Osharp 𝒮 i U) :
    mulAdd 𝒮 n i U a (r • b) = r • mulAdd 𝒮 n i U a b := by
  show mulLin 𝒮 n i U a (r • b) = r • mulLin 𝒮 n i U a b
  rw [map_smul]

/-- Multiplication on the presentation commutes with restriction. -/
theorem mulAdd_naturality (n i : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : algSections Osharp 𝒮 n U) (b : algSections Osharp 𝒮 i U) :
    algRestrict 𝒮 (n + i) f (mulAdd 𝒮 n i U a b) =
      mulAdd 𝒮 n i V (algRestrict 𝒮 n f a) (algRestrict 𝒮 i f b) := by
  induction a using algSections_induction with
  | hzero => simp
  | hadd a a' ha ha' => simp only [map_add, AddMonoidHom.add_apply, ha, ha']
  | hof w r =>
    induction b using algSections_induction with
    | hzero => simp
    | hadd b b' hb hb' => simp only [map_add, hb, hb']
    | hof w' s =>
      rw [mulAdd_algOf, algRestrict_algOf, algRestrict_algOf, algRestrict_algOf, mulAdd_algOf,
        map_mul]
      exact congrArg (fun z => algOf 𝒮 (n + i) z _)
        (Subtype.ext (wordMap_append f w.1 w'.1))

/-- Multiplication on the presentation, as a bilinear map of presheaves of modules. -/
noncomputable def mulPres (n i : ℤ) :
    Stacks.BilinearMap (algPres (Osharp := Osharp) 𝒮 n) (algPres 𝒮 i)
      (algPres 𝒮 (n + i)) where
  app U := mulAdd 𝒮 n i U
  map_smul_left U r a b := mulAdd_smul_left 𝒮 n i U r a b
  map_smul_right U r a b := mulAdd_smul_right 𝒮 n i U r a b
  naturality {_ _} f a b := mulAdd_naturality 𝒮 n i f a b

/-- The empty word, in degree zero. -/
def emptyWordIdx (U : Cᵒᵖ) : WordIdx 𝒮 0 U := ⟨[], rfl⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The underlying word of the empty word is the empty list. -/
@[simp] theorem emptyWordIdx_val (U : Cᵒᵖ) : (emptyWordIdx 𝒮 U).1 = [] := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The restriction of the empty word is the empty word. -/
@[simp] theorem wordIdxMap_emptyWordIdx {U V : Cᵒᵖ} (f : U ⟶ V) :
    wordIdxMap 0 f (emptyWordIdx 𝒮 U) = emptyWordIdx 𝒮 V := rfl

/-- Transport of a word along an equality of degrees. -/
def wordIdxCast {n n' : ℤ} (h : n = n') {U : Cᵒᵖ} (w : WordIdx 𝒮 n U) : WordIdx 𝒮 n' U :=
  ⟨w.1, w.2.trans h⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Transport along an equality of degrees does not change the underlying word. -/
@[simp] theorem wordIdxCast_val {n n' : ℤ} (h : n = n') {U : Cᵒᵖ} (w : WordIdx 𝒮 n U) :
    (wordIdxCast 𝒮 h w).1 = w.1 := rfl

/-- Transport of sections of the presentation along an equality of degrees. -/
noncomputable def algCast {n n' : ℤ} (h : n = n') (U : Cᵒᵖ) :
    algSections Osharp 𝒮 n U →+ algSections Osharp 𝒮 n' U := by
  subst h; exact AddMonoidHom.id _

/-- Transport of the summand of a word is the summand of the transported word. -/
@[simp] theorem algCast_algOf {n n' : ℤ} (h : n = n') (U : Cᵒᵖ) (w : WordIdx 𝒮 n U)
    (r : secRing Osharp U) :
    algCast 𝒮 h U (algOf 𝒮 n w r) = algOf 𝒮 n' (wordIdxCast 𝒮 h w) r := by
  subst h; rfl

/-- A section transported along an equality of degrees is heterogeneously equal to itself. -/
theorem heq_algCast {n n' : ℤ} (h : n = n') (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U) :
    HEq (algCast 𝒮 h U a) a := by subst h; rfl

/-- Associativity of the multiplication of the presentation. -/
theorem algCast_mulAdd_assoc (n i j : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U)
    (b : algSections Osharp 𝒮 i U) (c : algSections Osharp 𝒮 j U) :
    algCast 𝒮 (add_assoc n i j) U
        (mulAdd 𝒮 (n + i) j U (mulAdd 𝒮 n i U a b) c) =
      mulAdd 𝒮 n (i + j) U a (mulAdd 𝒮 i j U b c) := by
  induction a using algSections_induction with
  | hzero => simp
  | hadd a a' ha ha' => simp only [map_add, AddMonoidHom.add_apply, ha, ha']
  | hof w r =>
    induction b using algSections_induction with
    | hzero => simp
    | hadd b b' hb hb' => simp only [map_add, AddMonoidHom.add_apply, hb, hb']
    | hof w' s =>
      induction c using algSections_induction with
      | hzero => simp
      | hadd c c' hc hc' => simp only [map_add, hc, hc']
      | hof w'' q =>
        rw [mulAdd_algOf, mulAdd_algOf, algCast_algOf, mulAdd_algOf, mulAdd_algOf]
        exact congrArg₂ (algOf 𝒮 (n + (i + j)))
          (Subtype.ext (List.append_assoc w.1 w'.1 w''.1)) (mul_assoc r s q)

/-- The empty word is a left unit for the multiplication of the presentation. -/
theorem algCast_mulAdd_one_left (n : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U) :
    algCast 𝒮 (zero_add n) U (mulAdd 𝒮 0 n U (algOf 𝒮 0 (emptyWordIdx 𝒮 U) 1) a) = a := by
  induction a using algSections_induction with
  | hzero => simp
  | hadd a a' ha ha' => simp only [map_add, ha, ha']
  | hof w r =>
    rw [mulAdd_algOf, algCast_algOf, one_mul]
    exact congrArg (fun z => algOf 𝒮 n z r) (Subtype.ext (List.nil_append w.1))

/-- The empty word is a right unit for the multiplication of the presentation. -/
theorem algCast_mulAdd_one_right (n : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U) :
    algCast 𝒮 (add_zero n) U (mulAdd 𝒮 n 0 U a (algOf 𝒮 0 (emptyWordIdx 𝒮 U) 1)) = a := by
  induction a using algSections_induction with
  | hzero => simp
  | hadd a a' ha ha' => simp only [map_add, AddMonoidHom.add_apply, ha, ha']
  | hof w r =>
    rw [mulAdd_algOf, algCast_algOf, mul_one]
    exact congrArg (fun z => algOf 𝒮 n z r) (Subtype.ext (List.append_nil w.1))

end Presentation

section Sheafify

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J (Type t)] [HasWeakSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {I : Type t} (𝒮 : I → SheafOfGradedSets.{t} J)

/-- The degree-`n` piece of the free graded `O`-algebra `O⟨S⟩`: the sheafification of the free
`O`-module on the words of degree `n`. -/
noncomputable def algPiece (n : ℤ) : SheafOfModules.{t} (toRingCat J Osharp) :=
  (PresheafOfModules.sheafification (𝟙 (toRingCat J Osharp).obj)).obj
    (algPres (Osharp := Osharp) 𝒮 n)

/-- The canonical morphism from the presentation to the degree-`n` piece of `O⟨S⟩`. -/
noncomputable def algToSheaf (n : ℤ) :
    algPres (Osharp := Osharp) 𝒮 n ⟶ (algPiece 𝒮 n).val :=
  PresheafOfModules.toSheafify (𝟙 (toRingCat J Osharp).obj)
    (CategoryTheory.toSheafify J (algPres (Osharp := Osharp) 𝒮 n).presheaf)

/-- The map from the presentation to its sheafification is locally surjective. -/
instance (n : ℤ) :
    PresheafOfModules.IsLocallySurjective J (algToSheaf (Osharp := Osharp) 𝒮 n) :=
  inferInstanceAs (PresheafOfModules.IsLocallySurjective J
    (PresheafOfModules.toSheafify (𝟙 (toRingCat J Osharp).obj) _))

/-- The map from the presentation to its sheafification is locally injective. -/
instance (n : ℤ) :
    PresheafOfModules.IsLocallyInjective J (algToSheaf (Osharp := Osharp) 𝒮 n) :=
  inferInstanceAs (PresheafOfModules.IsLocallyInjective J
    (PresheafOfModules.toSheafify (𝟙 (toRingCat J Osharp).obj) _))

/-- The map to the sheafification commutes with restriction, with the target types written
plainly. -/
theorem algToSheaf_naturality (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : algSections Osharp 𝒮 n U) :
    Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 n).val f
        ((algToSheaf 𝒮 n).app U a) =
      (algToSheaf 𝒮 n).app V (algRestrict 𝒮 n f a) :=
  (PresheafOfModules.naturality_apply (algToSheaf (Osharp := Osharp) 𝒮 n) f a).symm

/-- Transport along an equality of degrees commutes with the map to the sheafification. -/
theorem castHom_algToSheaf {n n' : ℤ} (h : n = n') (U : Cᵒᵖ)
    (a : algSections Osharp 𝒮 n U) :
    castHom (algPiece (Osharp := Osharp) 𝒮) h U ((algToSheaf 𝒮 n).app U a) =
      (algToSheaf 𝒮 n').app U (algCast 𝒮 h U a) := by
  subst h; rfl

/-- **Two morphisms out of a piece of `O⟨S⟩` which agree on the image of the presentation are
equal.** -/
theorem algPiece_hom_ext {Z : SheafOfModules.{t} (toRingCat J Osharp)} {n : ℤ}
    {φ ψ : algPiece (Osharp := Osharp) 𝒮 n ⟶ Z}
    (h : ∀ (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U),
      φ.val.app U ((algToSheaf 𝒮 n).app U a) = ψ.val.app U ((algToSheaf 𝒮 n).app U a)) :
    φ = ψ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine Stacks.eq_of_forall_lift Z.isSheaf.isSeparated (algToSheaf 𝒮 n) x _ _ ?_
  intro Y f a ha
  show Stacks.sectionRestrict Z.val f (φ.val.app U x) =
    Stacks.sectionRestrict Z.val f (ψ.val.app U x)
  calc Stacks.sectionRestrict Z.val f (φ.val.app U x)
      = φ.val.app Y (Stacks.sectionRestrict (algPiece 𝒮 n).val f x) :=
        (PresheafOfModules.naturality_apply φ.val f x).symm
    _ = φ.val.app Y ((algToSheaf 𝒮 n).app Y a) := congrArg (fun z => φ.val.app Y z) ha.symm
    _ = ψ.val.app Y ((algToSheaf 𝒮 n).app Y a) := h Y a
    _ = ψ.val.app Y (Stacks.sectionRestrict (algPiece 𝒮 n).val f x) :=
        congrArg (fun z => ψ.val.app Y z) ha
    _ = Stacks.sectionRestrict Z.val f (ψ.val.app U x) :=
        PresheafOfModules.naturality_apply ψ.val f x

/-- Restricting a local lift of a section of a piece gives a local lift of its restriction. -/
private theorem algToSheaf_algRestrict_eq (n : ℤ) {U Y Z : Cᵒᵖ} (f : U ⟶ Y) (g : Y ⟶ Z)
    (x : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) (a : algSections Osharp 𝒮 n Y)
    (ha : (algToSheaf 𝒮 n).app Y a = Stacks.sectionRestrict (algPiece 𝒮 n).val f x) :
    (algToSheaf 𝒮 n).app Z (algRestrict 𝒮 n g a) =
      Stacks.sectionRestrict (algPiece 𝒮 n).val (f ≫ g) x := by
  refine (algToSheaf_naturality 𝒮 n g a).symm.trans ?_
  rw [show (algToSheaf 𝒮 n).app Y a = _ from ha, ← Stacks.sectionRestrict_comp]

/-- **Three sections of `O⟨S⟩` lift locally, all at once**: two sections of a sheaf of modules
agree as soon as they agree after restriction along a cover on which three given sections of
pieces of `O⟨S⟩` all come from the presentation. -/
theorem eq_of_lift₃ {Z : SheafOfModules.{t} (toRingCat J Osharp)} {n i j : ℤ} {U : Cᵒᵖ}
    (x : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U)
    (y : (algPiece (Osharp := Osharp) 𝒮 i).val.obj U)
    (z : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) (p q : Z.val.obj U)
    (h : ∀ {Y : Cᵒᵖ} (f : U ⟶ Y) (a : algSections Osharp 𝒮 n Y)
      (b : algSections Osharp 𝒮 i Y) (c : algSections Osharp 𝒮 j Y),
      (algToSheaf 𝒮 n).app Y a = Stacks.sectionRestrict (algPiece 𝒮 n).val f x →
      (algToSheaf 𝒮 i).app Y b = Stacks.sectionRestrict (algPiece 𝒮 i).val f y →
      (algToSheaf 𝒮 j).app Y c = Stacks.sectionRestrict (algPiece 𝒮 j).val f z →
      Stacks.sectionRestrict Z.val f p = Stacks.sectionRestrict Z.val f q) : p = q := by
  refine Stacks.eq_of_forall_lift Z.isSheaf.isSeparated (algToSheaf 𝒮 n) x p q ?_
  intro Y f a ha
  refine Stacks.eq_of_forall_lift Z.isSheaf.isSeparated (algToSheaf 𝒮 i)
    (Stacks.sectionRestrict (algPiece 𝒮 i).val f y) _ _ ?_
  intro Y₂ g b hb
  refine Stacks.eq_of_forall_lift Z.isSheaf.isSeparated (algToSheaf 𝒮 j)
    (Stacks.sectionRestrict (algPiece 𝒮 j).val (f ≫ g) z) _ _ ?_
  intro Y₃ k c hc
  have ha' := algToSheaf_algRestrict_eq 𝒮 n f (g ≫ k) x a ha
  have hb' : (algToSheaf 𝒮 i).app Y₃ (algRestrict 𝒮 i k b) =
      Stacks.sectionRestrict (algPiece 𝒮 i).val (f ≫ g ≫ k) y := by
    rw [algToSheaf_algRestrict_eq 𝒮 i g k _ b hb, ← Stacks.sectionRestrict_comp]
  have hc' : (algToSheaf 𝒮 j).app Y₃ c =
      Stacks.sectionRestrict (algPiece 𝒮 j).val (f ≫ g ≫ k) z := by
    rw [show (algToSheaf 𝒮 j).app Y₃ c =
        Stacks.sectionRestrict (algPiece 𝒮 j).val k
          (Stacks.sectionRestrict (algPiece 𝒮 j).val (f ≫ g) z) from hc,
      ← Stacks.sectionRestrict_comp, Category.assoc]
  have key := h (f ≫ g ≫ k) _ _ c ha' hb' hc'
  show Stacks.sectionRestrict Z.val k (Stacks.sectionRestrict Z.val g
      (Stacks.sectionRestrict Z.val f p)) =
    Stacks.sectionRestrict Z.val k (Stacks.sectionRestrict Z.val g
      (Stacks.sectionRestrict Z.val f q))
  rw [← Stacks.sectionRestrict_comp, ← Stacks.sectionRestrict_comp,
    ← Stacks.sectionRestrict_comp, ← Stacks.sectionRestrict_comp]
  exact key

/-- Multiplication of a section of `O⟨S⟩` by a section of the presentation: the extension of
the multiplication of the presentation in the first variable. -/
noncomputable def mulLeft (n i : ℤ) :
    Stacks.BilinearMap (algPiece (Osharp := Osharp) 𝒮 n).val (algPres 𝒮 i)
      (algPiece 𝒮 (n + i)).val :=
  Stacks.BilinearMap.extend (algPiece 𝒮 (n + i)).isSheaf (algToSheaf 𝒮 n)
    (postcompBilin (mulPres 𝒮 n i) (algToSheaf 𝒮 (n + i)))

/-- **Multiplication on `O⟨S⟩`**: the unique extension to the sheafification, in both
variables, of concatenation of words. -/
noncomputable def algMul (n i : ℤ) :
    Stacks.BilinearMap (algPiece (Osharp := Osharp) 𝒮 n).val (algPiece 𝒮 i).val
      (algPiece 𝒮 (n + i)).val :=
  (Stacks.BilinearMap.extend (algPiece 𝒮 (n + i)).isSheaf (algToSheaf 𝒮 i)
    (mulLeft 𝒮 n i).flip).flip

/-- On the image of the presentation, `mulLeft` is the multiplication of the presentation. -/
@[simp] theorem mulLeft_toSheaf (n i : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U)
    (b : algSections Osharp 𝒮 i U) :
    (mulLeft 𝒮 n i).app U ((algToSheaf 𝒮 n).app U a) b =
      (algToSheaf 𝒮 (n + i)).app U (mulAdd 𝒮 n i U a b) :=
  Stacks.BilinearMap.extendVal_app (algPiece 𝒮 (n + i)).isSheaf (algToSheaf 𝒮 n)
    (postcompBilin (mulPres 𝒮 n i) (algToSheaf 𝒮 (n + i))) a b

/-- When its second argument comes from the presentation, `algMul` is `mulLeft`. -/
@[simp] theorem algMul_toSheaf_right (n i : ℤ) (U : Cᵒᵖ)
    (x : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) (b : algSections Osharp 𝒮 i U) :
    (algMul 𝒮 n i).app U x ((algToSheaf 𝒮 i).app U b) = (mulLeft 𝒮 n i).app U x b :=
  Stacks.BilinearMap.extendVal_app (algPiece 𝒮 (n + i)).isSheaf (algToSheaf 𝒮 i)
    (mulLeft 𝒮 n i).flip b x

/-- **The value of the multiplication of `O⟨S⟩`, computed on local lifts of both arguments to
the presentation.** -/
theorem algMul_lift (n i : ℤ) (U : Cᵒᵖ)
    (x : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U)
    (y : (algPiece (Osharp := Osharp) 𝒮 i).val.obj U) {Y : Cᵒᵖ} (f : U ⟶ Y)
    (a : algSections Osharp 𝒮 n Y) (b : algSections Osharp 𝒮 i Y)
    (ha : (algToSheaf 𝒮 n).app Y a = Stacks.sectionRestrict (algPiece 𝒮 n).val f x)
    (hb : (algToSheaf 𝒮 i).app Y b = Stacks.sectionRestrict (algPiece 𝒮 i).val f y) :
    Stacks.sectionRestrict (algPiece 𝒮 (n + i)).val f ((algMul 𝒮 n i).app U x y) =
      (algToSheaf 𝒮 (n + i)).app Y (mulAdd 𝒮 n i Y a b) := by
  refine ((algMul 𝒮 n i).naturality f x y).trans ?_
  show (algMul 𝒮 n i).app Y (Stacks.sectionRestrict (algPiece 𝒮 n).val f x)
      (Stacks.sectionRestrict (algPiece 𝒮 i).val f y) = _
  rw [← ha, ← hb, algMul_toSheaf_right, mulLeft_toSheaf]

/-- The unit of `O⟨S⟩`: the empty word with coefficient `1`. -/
noncomputable def algOne : (algPiece (Osharp := Osharp) 𝒮 0).sections :=
  PresheafOfModules.sectionsMk
    (fun U => (algToSheaf 𝒮 0).app U (algOf 𝒮 0 (emptyWordIdx 𝒮 U) 1))
    (fun {U V} f => by
      change Stacks.sectionRestrict (algPiece 𝒮 0).val f
          ((algToSheaf 𝒮 0).app U (algOf 𝒮 0 (emptyWordIdx 𝒮 U) 1)) = _
      rw [algToSheaf_naturality, algRestrict_algOf, wordIdxMap_emptyWordIdx, map_one])

/-- Over `U`, the unit of `O⟨S⟩` is the image of the empty word with coefficient `1`. -/
theorem algOne_eval (U : Cᵒᵖ) :
    (algOne (Osharp := Osharp) 𝒮).eval U =
      (algToSheaf 𝒮 0).app U (algOf 𝒮 0 (emptyWordIdx 𝒮 U) 1) := rfl

/-- The restriction of the unit of `O⟨S⟩` along `f` is the image of the empty word with
coefficient `1` over the target of `f`. -/
theorem algOne_lift {U V : Cᵒᵖ} (f : U ⟶ V) :
    (algToSheaf (Osharp := Osharp) 𝒮 0).app V (algOf 𝒮 0 (emptyWordIdx 𝒮 V) 1) =
      Stacks.sectionRestrict (algPiece 𝒮 0).val f ((algOne 𝒮).eval U) :=
  (PresheafOfModules.sections_property (algOne (Osharp := Osharp) 𝒮) f).symm

/-- **Multiplication on `O⟨S⟩` is associative.** -/
theorem algMul_assoc (n i j : ℤ) (U : Cᵒᵖ)
    (x : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U)
    (y : (algPiece (Osharp := Osharp) 𝒮 i).val.obj U)
    (z : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    HEq ((algMul 𝒮 (n + i) j).app U ((algMul 𝒮 n i).app U x y) z)
      ((algMul 𝒮 n (i + j)).app U x ((algMul 𝒮 i j).app U y z)) := by
  refine Cofree.heq_of_castHom_eq (X := algPiece (Osharp := Osharp) 𝒮) (add_assoc n i j) U ?_
  refine eq_of_lift₃ 𝒮 x y z _ _ ?_
  intro Y f a b c ha hb hc
  have h1 := algMul_lift 𝒮 n i U x y f a b ha hb
  have h2 := algMul_lift 𝒮 i j U y z f b c hb hc
  have hL := algMul_lift 𝒮 (n + i) j U ((algMul 𝒮 n i).app U x y) z f
    (mulAdd 𝒮 n i Y a b) c h1.symm hc
  have hR := algMul_lift 𝒮 n (i + j) U x ((algMul 𝒮 i j).app U y z) f a
    (mulAdd 𝒮 i j Y b c) ha h2.symm
  rw [sectionRestrict_castHom (algPiece (Osharp := Osharp) 𝒮) (add_assoc n i j) f, hL,
    castHom_algToSheaf, algCast_mulAdd_assoc, hR]

/-- A section of a piece, transported along an equality of degrees, equals `x` as soon as every
local lift of `x` to the presentation is the transport of a local lift of the section. -/
private theorem castHom_eq_of_lift {n m : ℤ} (h : m = n) (U : Cᵒᵖ)
    (x : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U)
    (P : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (hP : ∀ {Y : Cᵒᵖ} (f : U ⟶ Y) (a : algSections Osharp 𝒮 n Y),
      (algToSheaf 𝒮 n).app Y a = Stacks.sectionRestrict (algPiece 𝒮 n).val f x →
      ∃ c : algSections Osharp 𝒮 m Y,
        Stacks.sectionRestrict (algPiece 𝒮 m).val f P = (algToSheaf 𝒮 m).app Y c ∧
          algCast 𝒮 h Y c = a) :
    castHom (algPiece (Osharp := Osharp) 𝒮) h U P = x := by
  refine Stacks.eq_of_forall_lift (algPiece (Osharp := Osharp) 𝒮 n).isSheaf.isSeparated
    (algToSheaf 𝒮 n) x _ _ ?_
  intro Y f a ha
  obtain ⟨c, hc, hca⟩ := hP f a ha
  change Stacks.sectionRestrict (algPiece 𝒮 n).val f
      (castHom (algPiece (Osharp := Osharp) 𝒮) h U P) =
    Stacks.sectionRestrict (algPiece 𝒮 n).val f x
  rw [sectionRestrict_castHom (algPiece (Osharp := Osharp) 𝒮) h f, hc, castHom_algToSheaf, hca]
  exact ha

/-- **The unit of `O⟨S⟩` is a left identity.** -/
theorem algOne_mul (n : ℤ) (U : Cᵒᵖ)
    (x : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) :
    HEq ((algMul 𝒮 0 n).app U ((algOne 𝒮).eval U) x) x := by
  refine Cofree.heq_of_castHom_eq (X := algPiece (Osharp := Osharp) 𝒮) (zero_add n) U ?_
  refine castHom_eq_of_lift 𝒮 (zero_add n) U x _ fun f a ha => ?_
  exact ⟨_, algMul_lift 𝒮 0 n U ((algOne 𝒮).eval U) x f (algOf 𝒮 0 (emptyWordIdx 𝒮 _) 1) a
    (algOne_lift 𝒮 f) ha, algCast_mulAdd_one_left 𝒮 n _ a⟩

/-- **The unit of `O⟨S⟩` is a right identity.** -/
theorem algMul_one (n : ℤ) (U : Cᵒᵖ)
    (x : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U) :
    HEq ((algMul 𝒮 n 0).app U x ((algOne 𝒮).eval U)) x := by
  refine Cofree.heq_of_castHom_eq (X := algPiece (Osharp := Osharp) 𝒮) (add_zero n) U ?_
  refine castHom_eq_of_lift 𝒮 (add_zero n) U x _ fun f a ha => ?_
  exact ⟨_, algMul_lift 𝒮 n 0 U x ((algOne 𝒮).eval U) f a (algOf 𝒮 0 (emptyWordIdx 𝒮 _) 1) ha
    (algOne_lift 𝒮 f), algCast_mulAdd_one_right 𝒮 n _ a⟩

/-- **The free graded `O`-algebra `O⟨S⟩` on a family of sheaves of graded sets**: in degree `n`
the sheafification of the free `O`-module on the words of degree `n` in the letters of the
family, with concatenation of words as multiplication. -/
noncomputable def freeGradedAlgebra : GradedAlgebra.{t, t} (toRingCat J Osharp) where
  piece := algPiece (Osharp := Osharp) 𝒮
  mul n i := algMul 𝒮 n i
  one := algOne 𝒮
  mul_assoc n i j U x y z := algMul_assoc 𝒮 n i j U x y z
  one_mul n U x := algOne_mul 𝒮 n U x
  mul_one n U x := algMul_one 𝒮 n U x

/-- The degree-`n` piece of `freeGradedAlgebra` is `algPiece`. -/
@[simp] theorem freeGradedAlgebra_piece (n : ℤ) :
    (freeGradedAlgebra (Osharp := Osharp) 𝒮).piece n = algPiece 𝒮 n := rfl

/-- The multiplication of `freeGradedAlgebra` is `algMul`. -/
@[simp] theorem freeGradedAlgebra_mul (n i : ℤ) :
    (freeGradedAlgebra (Osharp := Osharp) 𝒮).mul n i = algMul 𝒮 n i := rfl

/-- The unit of `freeGradedAlgebra` is `algOne`. -/
@[simp] theorem freeGradedAlgebra_one :
    (freeGradedAlgebra (Osharp := Osharp) 𝒮).one = algOne 𝒮 := rfl

/-- The section of `O⟨S⟩` attached to a word: the image of the word in the sheafification. Its
degree is the degree of the word. -/
noncomputable def algSec {U : Cᵒᵖ} (w : Word 𝒮 U) :
    (algPiece (Osharp := Osharp) 𝒮 (wordDeg w)).val.obj U :=
  (algToSheaf 𝒮 (wordDeg w)).app U (algOf 𝒮 (wordDeg w) ⟨w, rfl⟩ 1)

/-- The section attached to a word is the image of its summand with coefficient `1`. -/
theorem algSec_def {U : Cᵒᵖ} (w : Word 𝒮 U) :
    algSec (Osharp := Osharp) 𝒮 w =
      (algToSheaf 𝒮 (wordDeg w)).app U (algOf 𝒮 (wordDeg w) ⟨w, rfl⟩ 1) := rfl

/-- The empty word is the unit of `O⟨S⟩`. -/
theorem algSec_nil (U : Cᵒᵖ) :
    algSec (Osharp := Osharp) 𝒮 ([] : Word 𝒮 U) = (algOne 𝒮).eval U := rfl

/-- The section attached to a word of degree `n`, read in degree `n`. -/
theorem algToSheaf_algOf_one (n : ℤ) (U : Cᵒᵖ) (w : WordIdx 𝒮 n U) :
    (algToSheaf (Osharp := Osharp) 𝒮 n).app U (algOf 𝒮 n w 1) =
      castHom (algPiece (Osharp := Osharp) 𝒮) w.2 U (algSec 𝒮 w.1) := by
  rw [algSec_def, castHom_algToSheaf, algCast_algOf]
  rfl

/-- The map from the presentation to `O⟨S⟩` over an object of the site, as an additive map
whose source is written plainly as a type of finitely supported functions. -/
noncomputable def algToSheafAdd (n : ℤ) (U : Cᵒᵖ) :
    algSections Osharp 𝒮 n U →+ (algPiece (Osharp := Osharp) 𝒮 n).val.obj U :=
  ((algToSheaf 𝒮 n).app U).hom.toAddMonoidHom

/-- `algToSheafAdd` is the map from the presentation to `O⟨S⟩` over `U`. -/
@[simp] theorem algToSheafAdd_apply (n : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U) :
    algToSheafAdd (Osharp := Osharp) 𝒮 n U a = (algToSheaf 𝒮 n).app U a := rfl

/-- The summand of the presentation indexed by a word of degree `n`, read in `O⟨S⟩`: the
coefficient times the section attached to the word, transported to degree `n`. -/
theorem algToSheaf_algOf (n : ℤ) (U : Cᵒᵖ) (w : WordIdx 𝒮 n U) (r : secRing Osharp U) :
    (algToSheaf (Osharp := Osharp) 𝒮 n).app U (algOf 𝒮 n w r) =
      r • castHom (algPiece (Osharp := Osharp) 𝒮) w.2 U (algSec 𝒮 w.1) := by
  rw [algOf_eq_smul]
  exact (((algToSheaf 𝒮 n).app U).hom.map_smul r _).trans
    (congrArg (fun z => r • z) (algToSheaf_algOf_one 𝒮 n U w))

/-- **The section of `O⟨S⟩` attached to a concatenation of words is the product of the two
sections.** -/
theorem algSec_append {U : Cᵒᵖ} (w w' : Word 𝒮 U) :
    castHom (algPiece (Osharp := Osharp) 𝒮) (wordDeg_append w w').symm U
        ((algMul 𝒮 (wordDeg w) (wordDeg w')).app U (algSec 𝒮 w) (algSec 𝒮 w')) =
      algSec 𝒮 (w ++ w') := by
  rw [algSec_def 𝒮 w, algSec_def 𝒮 w', algMul_toSheaf_right, mulLeft_toSheaf, mulAdd_algOf,
    mul_one, castHom_algToSheaf, algCast_algOf, algSec_def]
  rfl

/-- The section attached to a word commutes with restriction. -/
theorem algSec_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (w : Word 𝒮 U) :
    Stacks.sectionRestrict (algPiece (Osharp := Osharp) 𝒮 (wordDeg w)).val f (algSec 𝒮 w) =
      castHom (algPiece (Osharp := Osharp) 𝒮) (wordDeg_wordMap f w) V
        (algSec 𝒮 (wordMap f w)) := by
  rw [algSec_def 𝒮 w, algToSheaf_naturality, algRestrict_algOf, map_one, algSec_def,
    castHom_algToSheaf, algCast_algOf]
  rfl

/-- The canonical generator of `O⟨S⟩` attached to a letter: the one-letter word, in the degree
of the letter. -/
noncomputable def algGen {U : Cᵒᵖ} (x : Letter 𝒮 U) :
    (algPiece (Osharp := Osharp) 𝒮 (letterDeg x)).val.obj U :=
  (algToSheaf 𝒮 (letterDeg x)).app U
    (algOf 𝒮 (letterDeg x) ⟨[x], by simp⟩ 1)

/-- The generator attached to a letter is the image of the one-letter word with coefficient
`1`. -/
theorem algGen_def {U : Cᵒᵖ} (x : Letter 𝒮 U) :
    algGen (Osharp := Osharp) 𝒮 x =
      (algToSheaf 𝒮 (letterDeg x)).app U
        (algOf 𝒮 (letterDeg x) ⟨[x], by simp⟩ 1) := rfl

/-- The cochain complex of the pieces of `O⟨S⟩` with zero differential. -/
noncomputable def algComplexZero :
    CochainComplex (SheafOfModules.{t} (toRingCat J Osharp)) ℤ where
  X := algPiece (Osharp := Osharp) 𝒮
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := zero_comp

/-- The degree-`n` object of `algComplexZero` is `algPiece`. -/
@[simp] theorem algComplexZero_X (n : ℤ) :
    (algComplexZero (Osharp := Osharp) 𝒮).X n = algPiece 𝒮 n := rfl

/-- The differential of `algComplexZero` is zero. -/
@[simp] theorem algComplexZero_d (n m : ℤ) :
    (algComplexZero (Osharp := Osharp) 𝒮).d n m = 0 := rfl

/-- The differential of `algComplexZero` sends every local section to zero. -/
@[simp] theorem algComplexZero_d_app (k l : ℤ) (U : Cᵒᵖ)
    (z : ((algComplexZero (Osharp := Osharp) 𝒮).X k).val.obj U) :
    ((algComplexZero (Osharp := Osharp) 𝒮).d k l).val.app U z = 0 := rfl

/-- **`O⟨S⟩` as a sheaf of differential graded `O`-algebras with zero differential.** This is
the base stage `A₀ = O⟨S₀⟩` of the source's tower, whose generators are closed. -/
noncomputable def freeDGAlgebraZero : DifferentialGradedAlgebra.{t, t} (toRingCat J Osharp) where
  complex := algComplexZero 𝒮
  mul n i := algMul 𝒮 n i
  one := algOne 𝒮
  mul_assoc n i j U x y z := algMul_assoc 𝒮 n i j U x y z
  one_mul n U x := algOne_mul 𝒮 n U x
  mul_one n U x := algMul_one 𝒮 n U x
  leibniz n i U x y := by
    have h1 : (algMul 𝒮 (n + 1) i).app U 0 y = 0 := by
      rw [map_zero ((algMul 𝒮 (n + 1) i).app U)]
      rfl
    have h2 : (algMul 𝒮 n (i + 1)).app U x 0 = 0 := map_zero ((algMul 𝒮 n (i + 1)).app U x)
    have hA : gradedCast (fun q => (((algPiece (Osharp := Osharp) 𝒮 q).val.obj U) : Type t))
        (add_right_comm n 1 i) ((algMul 𝒮 (n + 1) i).app U 0 y) = 0 := by
      rw [h1]
      exact gradedCast_zero _ _
    have hB : gradedCast (fun q => (((algPiece (Osharp := Osharp) 𝒮 q).val.obj U) : Type t))
        (add_assoc n i 1).symm ((algMul 𝒮 n (i + 1)).app U x 0) = 0 := by
      rw [h2]
      exact gradedCast_zero _ _
    rw [algComplexZero_d_app, algComplexZero_d_app, algComplexZero_d_app]
    refine Eq.symm (Eq.trans (congrArg₂ (· + ·) hA
      (congrArg (fun z => (Int.negOnePow n : ℤ) • z) hB)) ?_)
    change (0 : (algPiece (Osharp := Osharp) 𝒮 (n + i + 1)).val.obj U) +
        (Int.negOnePow n : ℤ) • (0 : (algPiece (Osharp := Osharp) 𝒮 (n + i + 1)).val.obj U) =
      (0 : (algPiece (Osharp := Osharp) 𝒮 (n + i + 1)).val.obj U)
    rw [smul_zero, add_zero]

/-- The degree-`n` object of the complex of `freeDGAlgebraZero` is `algPiece`. -/
@[simp] theorem freeDGAlgebraZero_complex_X (n : ℤ) :
    (freeDGAlgebraZero (Osharp := Osharp) 𝒮).complex.X n = algPiece 𝒮 n := rfl

/-- The multiplication of `freeDGAlgebraZero` is `algMul`. -/
@[simp] theorem freeDGAlgebraZero_mul (n i : ℤ) :
    (freeDGAlgebraZero (Osharp := Osharp) 𝒮).mul n i = algMul 𝒮 n i := rfl

/-- The graded algebra underlying `O⟨S⟩` with zero differential is `O⟨S⟩`. -/
theorem freeDGAlgebraZero_toGradedAlgebra :
    (freeDGAlgebraZero (Osharp := Osharp) 𝒮).toGradedAlgebra = freeGradedAlgebra 𝒮 := rfl

end Sheafify

end SheafOfModules

end
