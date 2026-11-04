module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModule
public import StacksCore.Tactic.StacksAttribute

/-!
# Words in a family of sheaves of graded sets

Let `(C, J)` be a site and let `𝒮 : I → SheafOfGradedSets J` be a family of sheaves of graded
sets on it. A *letter* over an object `U` of the site is an index `j` of the family together
with a homogeneous local section of `𝒮 j` over `U`; a *word* is a finite list of letters. The
letters over `U` are exactly the homogeneous local sections of the coproduct `⨿ⱼ 𝒮 j`, and a
word of length `r` is a local section of the `r`-fold product `𝒮 × ⋯ × 𝒮` of that coproduct
with itself, so that the presheaf of words of a fixed total degree is the degree-`n` part of
`⨿_{r ≥ 0} 𝒮 × ⋯ × 𝒮`. This is the index set of the free graded `O`-algebra on `𝒮`.

## Main definitions

* `Stacks.SheafOfGradedSets.Letter` and `Stacks.SheafOfGradedSets.Word` are the letters and the
  words over an object of the site, with `letterDeg`, `letterMap`, `wordDeg`, `wordMap` their
  degrees and their restriction maps.
* `Stacks.SheafOfGradedSets.wordWeight` is the **weight** of a word: for each index `j` of the
  family, the number of letters of the word coming from `𝒮 j`. This is the source's
  `w(s) = (w₀(s), …, wᵢ(s))` of Tag 0FU1.
* `Stacks.SheafOfGradedSets.WordIdx` is the type of words of a given total degree and
  `Stacks.SheafOfGradedSets.wordPresheaf` is the presheaf of types they form.

## Main results

* `wordDeg_append` and `wordWeight_append`: the degree and the weight of a concatenation are
  the sums of the degrees and of the weights. **The degree of the product sheaf is additive**,
  and the weight decomposition of `𝒮 × ⋯ × 𝒮` is the fibre decomposition of `wordWeight`.
* `wordDeg_wordMap` and `wordWeight_wordMap`: both are unchanged by restriction, so the degree
  and weight decompositions are decompositions of presheaves.
* `wordMap_id` and `wordMap_comp`: words form a presheaf.

## Implementation notes

Taking a *family* `𝒮` rather than a single sheaf of graded sets is what makes the weight
well defined on the nose. The source works with `S = S₀ ⨿ … ⨿ Sᵢ` and says that the weight of
a product section is defined when each factor lies in a unique summand; indexing the letters by
the summand records that choice in the datum, so no local hypothesis is needed and
`wordWeight` is a total function. The case `I = PUnit` is a single sheaf of graded sets, and no
coproduct of sheaves of graded sets has to be formed anywhere.

`Word` is an `abbrev` for `List`, so that the `List` API applies to words directly; for that
reason the operations are named `wordDeg`, `wordMap`, `wordWeight` rather than being exposed
through dot notation, which would resolve to `List`.

## References

* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t v u

namespace Stacks

namespace SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type t)] {I : Type t} (𝒮 : I → SheafOfGradedSets.{t} J)

/-- A letter over a family of sheaves of graded sets: an index `j` of the family together with a
homogeneous local section of `𝒮 j`. The letters over `U` are the homogeneous local sections of
the coproduct `⨿ⱼ 𝒮 j`. -/
abbrev Letter (U : Cᵒᵖ) : Type t := Σ j : I, (𝒮 j).Index U

variable {𝒮}

/-- The degree of a letter. -/
abbrev letterDeg {U : Cᵒᵖ} (x : Letter 𝒮 U) : ℤ := x.2.1

/-- Restriction of a letter along a morphism of the site. -/
abbrev letterMap {U V : Cᵒᵖ} (f : U ⟶ V) (x : Letter 𝒮 U) : Letter 𝒮 V :=
  ⟨x.1, Index.map f x.2⟩

/-- Restriction preserves the degree of a letter. -/
@[simp] theorem letterDeg_letterMap {U V : Cᵒᵖ} (f : U ⟶ V) (x : Letter 𝒮 U) :
    letterDeg (letterMap f x) = letterDeg x := rfl

/-- Restriction preserves the index of a letter. -/
@[simp] theorem letterMap_fst {U V : Cᵒᵖ} (f : U ⟶ V) (x : Letter 𝒮 U) :
    (letterMap f x).1 = x.1 := rfl

/-- Restriction of a letter along the identity is the identity. -/
theorem letterMap_id {U : Cᵒᵖ} (x : Letter 𝒮 U) : letterMap (𝟙 U) x = x := by
  obtain ⟨j, p⟩ := x
  exact congrArg (fun q => (⟨j, q⟩ : Letter 𝒮 U)) (Index.map_id p)

/-- Restriction of a letter along `f` and then `g` is restriction along `f ≫ g`. -/
theorem letterMap_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (x : Letter 𝒮 U) :
    letterMap g (letterMap f x) = letterMap (f ≫ g) x := by
  obtain ⟨j, p⟩ := x
  exact congrArg (fun q => (⟨j, q⟩ : Letter 𝒮 W)) (Index.map_comp f g p)

variable (𝒮)

/-- A word over a family of sheaves of graded sets: a finite list of letters. A word of length
`r` is a local section of the `r`-fold product of the coproduct of the family with itself. -/
abbrev Word (U : Cᵒᵖ) : Type t := List (Letter 𝒮 U)

variable {𝒮}

/-- The degree of a word: the sum of the degrees of its letters. This is the additive degree of
the product sheaf `𝒮 × ⋯ × 𝒮`. -/
def wordDeg {U : Cᵒᵖ} (w : Word 𝒮 U) : ℤ := (List.map letterDeg w).sum

/-- The empty word has degree `0`. -/
@[simp] theorem wordDeg_nil {U : Cᵒᵖ} : wordDeg ([] : Word 𝒮 U) = 0 := rfl

/-- The degree of `x :: w` is the degree of `x` plus the degree of `w`. -/
@[simp] theorem wordDeg_cons {U : Cᵒᵖ} (x : Letter 𝒮 U) (w : Word 𝒮 U) :
    wordDeg (x :: w : Word 𝒮 U) = letterDeg x + wordDeg w := rfl

/-- The degree of a concatenation of words is the sum of their degrees. -/
@[simp] theorem wordDeg_append {U : Cᵒᵖ} (w w' : Word 𝒮 U) :
    wordDeg (w ++ w' : Word 𝒮 U) = wordDeg w + wordDeg w' := by
  induction w with
  | nil => rw [List.nil_append, wordDeg_nil, zero_add]
  | cons x w ih =>
    rw [List.cons_append, wordDeg_cons, wordDeg_cons, ih, add_assoc]

/-- Restriction of a word along a morphism of the site. -/
def wordMap {U V : Cᵒᵖ} (f : U ⟶ V) (w : Word 𝒮 U) : Word 𝒮 V :=
  List.map (letterMap f) w

/-- Restriction of the empty word is the empty word. -/
@[simp] theorem wordMap_nil {U V : Cᵒᵖ} (f : U ⟶ V) :
    wordMap f ([] : Word 𝒮 U) = [] := rfl

/-- Restriction of `x :: w` restricts the letter `x` and the word `w`. -/
@[simp] theorem wordMap_cons {U V : Cᵒᵖ} (f : U ⟶ V) (x : Letter 𝒮 U) (w : Word 𝒮 U) :
    wordMap f (x :: w : Word 𝒮 U) = letterMap f x :: wordMap f w := rfl

/-- Restriction preserves the degree of a word. -/
@[simp] theorem wordDeg_wordMap {U V : Cᵒᵖ} (f : U ⟶ V) (w : Word 𝒮 U) :
    wordDeg (wordMap f w) = wordDeg w := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [wordMap_cons, wordDeg_cons, wordDeg_cons, ih, letterDeg_letterMap]

/-- Restriction of a word along the identity is the identity. -/
theorem wordMap_id {U : Cᵒᵖ} (w : Word 𝒮 U) : wordMap (𝟙 U) w = w := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [wordMap_cons, ih, letterMap_id]

/-- Restriction of a word along `f` and then `g` is restriction along `f ≫ g`. -/
theorem wordMap_comp {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (w : Word 𝒮 U) :
    wordMap g (wordMap f w) = wordMap (f ≫ g) w := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [wordMap_cons, wordMap_cons, wordMap_cons, ih, letterMap_comp]

/-- Restriction of a concatenation of words is the concatenation of the restrictions. -/
@[simp] theorem wordMap_append {U V : Cᵒᵖ} (f : U ⟶ V) (w w' : Word 𝒮 U) :
    wordMap f (w ++ w' : Word 𝒮 U) = (wordMap f w ++ wordMap f w' : Word 𝒮 V) :=
  List.map_append ..

/-- The weight of a word: for each index `j` of the family, the number of letters of the word
coming from `𝒮 j`. This is the source's `w(s) = (w₀(s), …, wᵢ(s))`. -/
def wordWeight [DecidableEq I] {U : Cᵒᵖ} (w : Word 𝒮 U) (j : I) : ℕ :=
  (List.filter (fun x => decide (x.1 = j)) w).length

/-- The empty word has weight `0` at every index. -/
@[simp] theorem wordWeight_nil [DecidableEq I] {U : Cᵒᵖ} (j : I) :
    wordWeight ([] : Word 𝒮 U) j = 0 := rfl

/-- The weight of `x :: w` at `j` is the weight of `w` at `j`, plus one if `x` comes from `𝒮 j`. -/
theorem wordWeight_cons [DecidableEq I] {U : Cᵒᵖ} (x : Letter 𝒮 U) (w : Word 𝒮 U) (j : I) :
    wordWeight (x :: w : Word 𝒮 U) j = (if x.1 = j then 1 else 0) + wordWeight w j := by
  unfold wordWeight
  rw [List.filter_cons]
  by_cases h : x.1 = j
  · simp [h, Nat.add_comm]
  · simp [h]

/-- Restriction preserves the weight of a word. -/
@[simp] theorem wordWeight_wordMap [DecidableEq I] {U V : Cᵒᵖ} (f : U ⟶ V) (w : Word 𝒮 U)
    (j : I) : wordWeight (wordMap f w) j = wordWeight w j := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [wordMap_cons, wordWeight_cons, wordWeight_cons, ih, letterMap_fst]

/-- The weight of a concatenation of words is the sum of their weights. -/
@[simp] theorem wordWeight_append [DecidableEq I] {U : Cᵒᵖ} (w w' : Word 𝒮 U) (j : I) :
    wordWeight (w ++ w' : Word 𝒮 U) j = wordWeight w j + wordWeight w' j := by
  unfold wordWeight
  rw [List.filter_append, List.length_append]

/-- A word of total degree `n` over `U`. -/
abbrev WordIdx (𝒮 : I → SheafOfGradedSets.{t} J) (n : ℤ) (U : Cᵒᵖ) : Type t :=
  { w : Word 𝒮 U // wordDeg w = n }

/-- Restriction of a word of degree `n`. -/
def wordIdxMap (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (w : WordIdx 𝒮 n U) : WordIdx 𝒮 n V :=
  ⟨wordMap f w.1, (wordDeg_wordMap f w.1).trans w.2⟩

/-- The underlying word of the restriction of a word of degree `n` is its restriction. -/
@[simp] theorem wordIdxMap_val (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (w : WordIdx 𝒮 n U) :
    (wordIdxMap n f w).1 = wordMap f w.1 := rfl

/-- Restriction of a word of degree `n` along the identity is the identity. -/
theorem wordIdxMap_id (n : ℤ) {U : Cᵒᵖ} (w : WordIdx 𝒮 n U) : wordIdxMap n (𝟙 U) w = w :=
  Subtype.ext (wordMap_id w.1)

/-- Restriction of a word of degree `n` along `f` and then `g` is restriction along `f ≫ g`. -/
theorem wordIdxMap_comp (n : ℤ) {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (w : WordIdx 𝒮 n U) :
    wordIdxMap n g (wordIdxMap n f w) = wordIdxMap n (f ≫ g) w :=
  Subtype.ext (wordMap_comp f g w.1)

/-- The words of total degree `n`, as a presheaf of types: the degree-`n` part of the graded set
of words. -/
def wordPresheaf (𝒮 : I → SheafOfGradedSets.{t} J) (n : ℤ) : Cᵒᵖ ⥤ Type t where
  obj U := WordIdx 𝒮 n U
  map {_ _} f := ↾wordIdxMap n f
  map_id _ := by
    ext w
    simp [wordIdxMap, wordMap_id]
  map_comp f g := by
    ext w
    simp [wordIdxMap, wordMap_comp]

end SheafOfGradedSets

end Stacks

end
