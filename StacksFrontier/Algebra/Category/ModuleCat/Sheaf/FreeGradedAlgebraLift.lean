module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraHom

/-!
# The universal property of the free graded `O`-algebra `O⟨S⟩`

Let `(C, O)` be a ringed site, let `𝒮` be a family of sheaves of graded sets on it, let `O⟨S⟩`
be the free graded `O`-algebra on `𝒮` and let `B` be a sheaf of graded `O`-algebras. A *letter
map* assigns to every letter `x` over `U` a homogeneous local section `g(x)` of `B` of the
degree of `x`, compatibly with restriction. This file constructs the homomorphism of sheaves of
graded algebras `O⟨S⟩ ⟶ B` which sends the generator of every letter `x` to `g(x)`: on a word
`x₁ ⋯ x_r` it is the product `g(x₁) ⋯ g(x_r)`, extended linearly to the presentation and then
to its sheafification. When `B` carries a differential and `O⟨S⟩` the Leibniz extension of a
derivation datum `δ`, the homomorphism commutes with the differentials as soon as `d_B(g(x))`
is the image of `δ(x)` for every letter `x`.

This is the universal property used by the source to write down the maps `Aᵢ ⟶ Aᵢ₊₁` and
`Aᵢ ⟶ B` of the tower of Tag 0FU2.

## Main definitions

* `SheafOfModules.GradedAlgebra.mulAt`: the product of two homogeneous local sections of a
  sheaf of graded algebras, read in a prescribed degree.
* `SheafOfModules.LetterMap`: a letter map `𝒮 ⟶ B`.
* `SheafOfModules.LetterMap.wordEval`: the value of a letter map on a word.
* `SheafOfModules.LetterMap.liftPiece`: the induced morphism `O⟨S⟩ⁿ ⟶ Bⁿ` of sheaves of
  modules.
* `SheafOfModules.LetterMap.dgLift`: the induced homomorphism of sheaves of differential graded
  algebras `O⟨S⟩ ⟶ B`.

## Main results

* `SheafOfModules.LetterMap.liftPiece_algGen`: the lift sends the generator of a letter `x` to
  `g(x)`.
* `SheafOfModules.LetterMap.liftPiece_algMul` and `SheafOfModules.LetterMap.liftPiece_one`: the
  lift is multiplicative and unital.
* `SheafOfModules.LetterMap.liftPiece_algD`: the lift commutes with the differentials when the
  letter map is compatible with them.
* `SheafOfModules.algPiece_hom_ext_of_algGen`: two multiplicative, unital families of morphisms
  out of `O⟨S⟩` which agree on the generators agree.

## References

* [Stacks Project, Tag 0FU2](https://stacks.math.columbia.edu/tag/0FU2)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

section GradedMulAt

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  (A : GradedAlgebra.{t, t} R)

/-- The product of two homogeneous local sections of a sheaf of graded algebras, read in a
prescribed total degree. -/
noncomputable def GradedAlgebra.mulAt {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ)
    (a : (A.piece m).val.obj U) (b : (A.piece j).val.obj U) : (A.piece n).val.obj U :=
  castHom A.piece h U ((A.mul m j).app U a b)

namespace GradedAlgebra

/-- In the degree `m + j` itself, `mulAt` is the multiplication of `A`. -/
theorem mulAt_rfl {m j : ℤ} (U : Cᵒᵖ) (a : (A.piece m).val.obj U)
    (b : (A.piece j).val.obj U) : A.mulAt (rfl : m + j = m + j) U a b = (A.mul m j).app U a b :=
  rfl

/-- `mulAt` is additive in its first argument. -/
theorem mulAt_add_left {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (a a' : (A.piece m).val.obj U)
    (b : (A.piece j).val.obj U) : A.mulAt h U (a + a') b = A.mulAt h U a b + A.mulAt h U a' b := by
  rw [mulAt, mulAt, mulAt, (A.mul m j).map_add_left, map_add]

/-- `mulAt` is additive in its second argument. -/
theorem mulAt_add_right {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (a : (A.piece m).val.obj U)
    (b b' : (A.piece j).val.obj U) :
    A.mulAt h U a (b + b') = A.mulAt h U a b + A.mulAt h U a b' := by
  rw [mulAt, mulAt, mulAt, map_add, map_add]

/-- The product of zero with any section is zero. -/
theorem mulAt_zero_left {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (b : (A.piece j).val.obj U) :
    A.mulAt h U (0 : (A.piece m).val.obj U) b = 0 := by
  have hz : (A.mul m j).app U 0 b = 0 := by
    rw [map_zero ((A.mul m j).app U)]
    rfl
  rw [mulAt, hz, Cofree.castHom_zero]

/-- The product of any section with zero is zero. -/
theorem mulAt_zero_right {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (a : (A.piece m).val.obj U) :
    A.mulAt h U a (0 : (A.piece j).val.obj U) = 0 := by
  rw [mulAt, map_zero ((A.mul m j).app U a), Cofree.castHom_zero]

/-- `mulAt` commutes with integer multiples in its first argument. -/
theorem mulAt_zsmul_left {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (k : ℤ)
    (a : (A.piece m).val.obj U) (b : (A.piece j).val.obj U) :
    A.mulAt h U (k • a) b = k • A.mulAt h U a b := by
  have hz : (A.mul m j).app U (k • a) b = k • (A.mul m j).app U a b := by
    rw [map_zsmul ((A.mul m j).app U) k a]
    rfl
  rw [mulAt, mulAt, hz, map_zsmul (castHom A.piece h U) k]

/-- `mulAt` commutes with integer multiples in its second argument. -/
theorem mulAt_zsmul_right {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (k : ℤ)
    (a : (A.piece m).val.obj U) (b : (A.piece j).val.obj U) :
    A.mulAt h U a (k • b) = k • A.mulAt h U a b := by
  rw [mulAt, mulAt, map_zsmul ((A.mul m j).app U a) k b, map_zsmul (castHom A.piece h U) k]

/-- `mulAt` is linear over the structure sheaf in its first argument. -/
theorem mulAt_smul_left {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (r : R.obj.obj U)
    (a : (A.piece m).val.obj U) (b : (A.piece j).val.obj U) :
    A.mulAt h U (r • a) b = r • A.mulAt h U a b := by
  rw [mulAt, mulAt, (A.mul m j).map_smul_left U r a b, castHom_smul A.piece h U r]

/-- `mulAt` is linear over the structure sheaf in its second argument. -/
theorem mulAt_smul_right {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ) (r : R.obj.obj U)
    (a : (A.piece m).val.obj U) (b : (A.piece j).val.obj U) :
    A.mulAt h U a (r • b) = r • A.mulAt h U a b := by
  rw [mulAt, mulAt, (A.mul m j).map_smul_right U r a b, castHom_smul A.piece h U r]

/-- Transporting the first factor along an equality of degrees does not change the product. -/
theorem mulAt_castHom_left {m m' j n : ℤ} (h₁ : m = m') (h : m' + j = n) (h' : m + j = n)
    (U : Cᵒᵖ) (a : (A.piece m).val.obj U) (b : (A.piece j).val.obj U) :
    A.mulAt h U (castHom A.piece h₁ U a) b = A.mulAt h' U a b := by
  subst h₁; rfl

/-- Transporting the second factor along an equality of degrees does not change the product. -/
theorem mulAt_castHom_right {m j j' n : ℤ} (h₁ : j = j') (h : m + j' = n) (h' : m + j = n)
    (U : Cᵒᵖ) (a : (A.piece m).val.obj U) (b : (A.piece j).val.obj U) :
    A.mulAt h U a (castHom A.piece h₁ U b) = A.mulAt h' U a b := by
  subst h₁; rfl

/-- Transporting a product along an equality of degrees is the product read in the new
degree. -/
theorem castHom_mulAt {m j n n' : ℤ} (h : m + j = n) (h₂ : n = n') (h' : m + j = n')
    (U : Cᵒᵖ) (a : (A.piece m).val.obj U) (b : (A.piece j).val.obj U) :
    castHom A.piece h₂ U (A.mulAt h U a b) = A.mulAt h' U a b := by
  subst h₂; rfl

/-- `mulAt` commutes with restriction. -/
theorem mulAt_naturality {m j n : ℤ} (h : m + j = n) {U V : Cᵒᵖ} (f : U ⟶ V)
    (a : (A.piece m).val.obj U) (b : (A.piece j).val.obj U) :
    Stacks.sectionRestrict (A.piece n).val f (A.mulAt h U a b) =
      A.mulAt h V (Stacks.sectionRestrict (A.piece m).val f a)
        (Stacks.sectionRestrict (A.piece j).val f b) := by
  rw [mulAt, mulAt, sectionRestrict_castHom A.piece h f]
  exact congrArg (castHom A.piece h V) ((A.mul m j).naturality f a b)

/-- `mulAt` is associative. -/
theorem mulAt_assoc {m j k p q n : ℤ} (h₁ : m + j = p) (h : p + k = n) (h₂ : j + k = q)
    (h' : m + q = n) (U : Cᵒᵖ) (a : (A.piece m).val.obj U) (b : (A.piece j).val.obj U)
    (c : (A.piece k).val.obj U) :
    A.mulAt h U (A.mulAt h₁ U a b) c = A.mulAt h' U a (A.mulAt h₂ U b c) := by
  subst h₁
  subst h₂
  exact Cofree.castHom_eq_castHom h h' U (A.mul_assoc m j k U a b c)

/-- The unit section is a right identity for `mulAt`, up to transport of degree. -/
theorem mulAt_one {n n' : ℤ} (h : n + 0 = n') (h' : n = n') (U : Cᵒᵖ)
    (a : (A.piece n).val.obj U) :
    A.mulAt h U a (A.one.eval U) = castHom A.piece h' U a :=
  Cofree.castHom_eq_castHom h h' U (A.mul_one n U a)

/-- The unit section is a left identity for `mulAt`, up to transport of degree. -/
theorem one_mulAt {n n' : ℤ} (h : 0 + n = n') (h' : n = n') (U : Cᵒᵖ)
    (a : (A.piece n).val.obj U) :
    A.mulAt h U (A.one.eval U) a = castHom A.piece h' U a :=
  Cofree.castHom_eq_castHom h h' U (A.one_mul n U a)

end GradedAlgebra

/-- The signed Leibniz rule of a sheaf of differential graded algebras, with the degree of the
product prescribed. -/
theorem DifferentialGradedAlgebra.d_mulAt (B : DifferentialGradedAlgebra.{t, t} R)
    {m j n : ℤ} (h : m + j = n) (h₁ : m + 1 + j = n + 1) (h₂ : m + (j + 1) = n + 1) (U : Cᵒᵖ)
    (a : (B.complex.X m).val.obj U) (b : (B.complex.X j).val.obj U) :
    (B.complex.d n (n + 1)).val.app U (B.toGradedAlgebra.mulAt h U a b) =
      B.toGradedAlgebra.mulAt h₁ U ((B.complex.d m (m + 1)).val.app U a) b
        + (Int.negOnePow m : ℤ) •
          B.toGradedAlgebra.mulAt h₂ U a ((B.complex.d j (j + 1)).val.app U b) := by
  subst h
  rw [GradedAlgebra.mulAt_rfl, GradedAlgebra.mulAt, GradedAlgebra.mulAt, castHom_apply,
    castHom_apply]
  exact B.leibniz m j U a b

end GradedMulAt

section Lift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  [HasWeakSheafify J (Type t)] [HasWeakSheafify J AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {I : Type t} (𝒮 : I → SheafOfGradedSets.{t} J)

/-- A **letter map** from a family of sheaves of graded sets to a sheaf of graded algebras: a
homogeneous local section `g(x)` of the degree of `x` for every letter `x`, compatible with
restriction. This is a map of sheaves of graded sets from `⨿ⱼ 𝒮 j` to the homogeneous local
sections of `B`. -/
structure LetterMap (B : GradedAlgebra.{t, t} (toRingCat J Osharp)) where
  /-- The value of the letter map on a letter. -/
  app (U : Cᵒᵖ) (x : Letter 𝒮 U) : (B.piece (letterDeg x)).val.obj U
  /-- The values are compatible with restriction. -/
  naturality {U V : Cᵒᵖ} (f : U ⟶ V) (x : Letter 𝒮 U) :
    Stacks.sectionRestrict (B.piece (letterDeg x)).val f (app U x) = app V (letterMap f x)

/-- A family of morphisms which is multiplicative in the total degree `m + j` is multiplicative
with any prescribed degree of the product. -/
private theorem family_mulAt (B : GradedAlgebra.{t, t} (toRingCat J Osharp))
    (φ : ∀ n, algPiece (Osharp := Osharp) 𝒮 n ⟶ B.piece n)
    (hφ : ∀ (m j : ℤ) (U : Cᵒᵖ) (x : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
      (y : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U),
      (φ (m + j)).val.app U ((algMul 𝒮 m j).app U x y) =
        (B.mul m j).app U ((φ m).val.app U x) ((φ j).val.app U y))
    {m j k : ℤ} (h : m + j = k) (U : Cᵒᵖ) (x : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (y : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    (φ k).val.app U (mulAt 𝒮 h U x y) =
      B.mulAt h U ((φ m).val.app U x) ((φ j).val.app U y) := by
  subst h
  exact hφ _ _ U x y

namespace LetterMap

variable {𝒮} {B : GradedAlgebra.{t, t} (toRingCat J Osharp)} (g : LetterMap 𝒮 B)

/-- **The value of a letter map on a word**: the product of its values on the letters. -/
noncomputable def wordEval {U : Cᵒᵖ} : (w : Word 𝒮 U) → (B.piece (wordDeg w)).val.obj U
  | [] => B.one.eval U
  | x :: w => B.mulAt (wordDeg_cons x w).symm U (g.app U x) (wordEval w)

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The value of a letter map on the empty word is the unit section. -/
@[simp] theorem wordEval_nil (U : Cᵒᵖ) : g.wordEval ([] : Word 𝒮 U) = B.one.eval U := rfl

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The value of a letter map on `x :: w` is `g(x)` times its value on `w`. -/
theorem wordEval_cons {U : Cᵒᵖ} (x : Letter 𝒮 U) (w : Word 𝒮 U)
    (h : letterDeg x + wordDeg w = wordDeg (x :: w)) :
    g.wordEval (x :: w) = B.mulAt h U (g.app U x) (g.wordEval w) := rfl

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The value of a letter map on a word commutes with restriction. -/
theorem wordEval_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (w : Word 𝒮 U) :
    Stacks.sectionRestrict (B.piece (wordDeg w)).val f (g.wordEval w) =
      castHom B.piece (wordDeg_wordMap f w) V (g.wordEval (wordMap f w)) := by
  induction w with
  | nil =>
    exact (PresheafOfModules.sections_property B.one f)
  | cons x w ih =>
    have ec : wordDeg (x :: w : Word 𝒮 U) = letterDeg x + wordDeg w := wordDeg_cons x w
    have g1 : wordDeg (wordMap f w) = wordDeg w := wordDeg_wordMap f w
    have e1 : letterDeg x + wordDeg (wordMap f w) = wordDeg (x :: w : Word 𝒮 U) := by omega
    have e2 : letterDeg x + wordDeg (wordMap f w) =
        wordDeg (wordMap f (x :: w) : Word 𝒮 V) :=
      (wordDeg_cons (letterMap f x) (wordMap f w)).symm
    rw [wordEval_cons g x w ec.symm, GradedAlgebra.mulAt_naturality, g.naturality, ih,
      GradedAlgebra.mulAt_castHom_right B g1 ec.symm e1]
    change _ = castHom B.piece (wordDeg_wordMap f (x :: w)) V
      (B.mulAt e2 V (g.app V (letterMap f x)) (g.wordEval (wordMap f w)))
    rw [GradedAlgebra.castHom_mulAt B e2 (wordDeg_wordMap f (x :: w)) e1]

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The value of a letter map on a concatenation of words is the product of its values.** -/
theorem wordEval_append {U : Cᵒᵖ} (w w' : Word 𝒮 U)
    (h : wordDeg w + wordDeg w' = wordDeg (w ++ w')) :
    B.mulAt h U (g.wordEval w) (g.wordEval w') = g.wordEval (w ++ w') := by
  induction w with
  | nil => exact (GradedAlgebra.one_mulAt B h rfl U _)
  | cons x w ih =>
    have ec : wordDeg (x :: w : Word 𝒮 U) = letterDeg x + wordDeg w := wordDeg_cons x w
    have ea : wordDeg (w ++ w') = wordDeg w + wordDeg w' := wordDeg_append w w'
    have ec' : wordDeg (x :: (w ++ w') : Word 𝒮 U) = letterDeg x + wordDeg (w ++ w') :=
      wordDeg_cons x (w ++ w')
    rw [wordEval_cons g x w ec.symm,
      GradedAlgebra.mulAt_assoc B ec.symm h ea.symm (by omega), ih ea.symm]
    exact (wordEval_cons g x (w ++ w') ec'.symm).symm

/-- The value of a letter map on the words of degree `n`, as a morphism of presheaves of types
into the degree-`n` piece of `B`. -/
noncomputable def wordEvalNat (n : ℤ) :
    wordPresheaf 𝒮 n ⟶ (B.piece n).val.presheaf ⋙ CategoryTheory.forget _ where
  app U := ↾fun w => castHom B.piece w.2 U (g.wordEval w.1)
  naturality {U V} f := by
    ext w
    refine Eq.symm ?_
    change Stacks.sectionRestrict (B.piece n).val f (castHom B.piece w.2 U (g.wordEval w.1)) = _
    rw [sectionRestrict_castHom B.piece _ f, wordEval_naturality, Cofree.castHom_castHom]
    rfl

/-- The lift of a letter map to the presentation of the degree-`n` piece of `O⟨S⟩`. -/
noncomputable def liftPres (n : ℤ) :
    algPres (Osharp := Osharp) 𝒮 n ⟶ (B.piece n).val :=
  PresheafOfModules.freeObjDesc (g.wordEvalNat n)

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The lift on the presentation sends the basis element of a word to the value of the letter
map on it. -/
theorem liftPres_word (n : ℤ) (U : Cᵒᵖ) (w : WordIdx 𝒮 n U) :
    (g.liftPres n).app U (algOf 𝒮 n w 1) = castHom B.piece w.2 U (g.wordEval w.1) :=
  ModuleCat.freeDesc_apply ((g.wordEvalNat n).app U) w

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The lift on the presentation sends `r` times the basis element of a word to `r` times the
value of the letter map on it. -/
theorem liftPres_algOf (n : ℤ) (U : Cᵒᵖ) (w : WordIdx 𝒮 n U) (r : secRing Osharp U) :
    (g.liftPres n).app U (algOf 𝒮 n w r) = r • castHom B.piece w.2 U (g.wordEval w.1) := by
  rw [algOf_eq_smul]
  exact (((g.liftPres n).app U).hom.map_smul r _).trans
    (congrArg (fun z => r • z) (g.liftPres_word n U w))

/-- **The lift of a letter map**, the morphism `O⟨S⟩ⁿ ⟶ Bⁿ` of sheaves of modules which on a
word is the product of the values of the letter map on its letters. -/
noncomputable def liftPiece (n : ℤ) : algPiece (Osharp := Osharp) 𝒮 n ⟶ B.piece n :=
  ⟨(PresheafOfModules.sheafifyHomEquiv' (𝟙 (toRingCat J Osharp).obj)
      (CategoryTheory.toSheafify J (algPres (Osharp := Osharp) 𝒮 n).presheaf)
      (B.piece n).isSheaf).symm (g.liftPres n)⟩

/-- The lift of a letter map, composed with the map from the presentation to its
sheafification, is the lift on the presentation. -/
theorem liftPiece_toSheaf (n : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U) :
    (g.liftPiece n).val.app U ((algToSheaf 𝒮 n).app U a) = (g.liftPres n).app U a :=
  congrArg (fun φ : (algPres (Osharp := Osharp) 𝒮 n).presheaf ⟶ (B.piece n).val.presheaf =>
      φ.app U a)
    (PresheafOfModules.comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom
      (𝟙 (toRingCat J Osharp).obj)
      (CategoryTheory.toSheafify J (algPres (Osharp := Osharp) 𝒮 n).presheaf)
      (B.piece n).isSheaf (g.liftPres n))

/-- The restriction of the lift of a section is the lift of any presentation element
representing the restricted section. -/
private theorem sectionRestrict_liftPiece {k : ℤ} {U Y : Cᵒᵖ} (f : U ⟶ Y)
    (z : (algPiece (Osharp := Osharp) 𝒮 k).val.obj U) (a : algSections Osharp 𝒮 k Y)
    (h : Stacks.sectionRestrict (algPiece 𝒮 k).val f z = (algToSheaf 𝒮 k).app Y a) :
    Stacks.sectionRestrict (B.piece k).val f ((g.liftPiece k).val.app U z) =
      (g.liftPres k).app Y a := by
  rw [← liftPiece_toSheaf, ← h]
  exact (PresheafOfModules.naturality_apply (g.liftPiece k).val f z).symm

/-- The lift of a letter map commutes with transport along an equality of degrees. -/
theorem liftPiece_castHom {k n : ℤ} (h : k = n) (U : Cᵒᵖ)
    (z : (algPiece (Osharp := Osharp) 𝒮 k).val.obj U) :
    (g.liftPiece n).val.app U (castHom (algPiece (Osharp := Osharp) 𝒮) h U z) =
      castHom B.piece h U ((g.liftPiece k).val.app U z) := by
  subst h; rfl

/-- **The lift sends the section attached to a word to the value of the letter map on it.** -/
theorem liftPiece_algSec {U : Cᵒᵖ} (w : Word 𝒮 U) :
    (g.liftPiece (wordDeg w)).val.app U (algSec (Osharp := Osharp) 𝒮 w) = g.wordEval w := by
  rw [algSec_def, liftPiece_toSheaf, liftPres_word]
  rfl

/-- **The lift sends the generator of a letter to the value of the letter map on it.** -/
theorem liftPiece_algGen {U : Cᵒᵖ} (x : Letter 𝒮 U) :
    (g.liftPiece (letterDeg x)).val.app U (algGen (Osharp := Osharp) 𝒮 x) = g.app U x := by
  have eb : wordDeg ([x] : Word 𝒮 U) = letterDeg x + wordDeg ([] : Word 𝒮 U) :=
    wordDeg_cons x []
  have ea : wordDeg ([] : Word 𝒮 U) = 0 := rfl
  have h1 : letterDeg x + 0 = wordDeg ([x] : Word 𝒮 U) := by omega
  rw [algGen_def, liftPiece_toSheaf, liftPres_word]
  change castHom B.piece _ U (B.mulAt h1 U (g.app U x) (B.one.eval U)) = _
  rw [GradedAlgebra.castHom_mulAt B h1 _ (add_zero _), GradedAlgebra.mulAt_one B _ rfl]
  rfl

/-- **The lift is unital.** -/
theorem liftPiece_one (U : Cᵒᵖ) :
    (g.liftPiece 0).val.app U ((algOne (Osharp := Osharp) 𝒮).eval U) = B.one.eval U := by
  rw [algOne_eval, liftPiece_toSheaf, liftPres_word]
  rfl

/-- The lift of a letter map on the presentation over an object of the site, as an additive
map out of the finitely supported functions on words of degree `n`. -/
noncomputable def liftAdd (n : ℤ) (U : Cᵒᵖ) :
    algSections Osharp 𝒮 n U →+ (B.piece n).val.obj U :=
  ((g.liftPres n).app U).hom.toAddMonoidHom

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- `liftAdd` agrees with the lift on the presentation. -/
@[simp] theorem liftAdd_apply (n : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U) :
    g.liftAdd n U a = (g.liftPres n).app U a := rfl

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The lift on the presentation is multiplicative. -/
theorem liftAdd_mulAdd (n i : ℤ) (U : Cᵒᵖ) (a : algSections Osharp 𝒮 n U)
    (b : algSections Osharp 𝒮 i U) :
    g.liftAdd (n + i) U (mulAdd 𝒮 n i U a b) =
      (B.mul n i).app U (g.liftAdd n U a) (g.liftAdd i U b) := by
  induction a using algSections_induction with
  | hzero =>
    rw [map_zero (mulAdd 𝒮 n i U), AddMonoidHom.zero_apply, map_zero, map_zero,
      map_zero ((B.mul n i).app U), AddMonoidHom.zero_apply]
  | hadd a a' ha ha' =>
    rw [map_add (mulAdd 𝒮 n i U), AddMonoidHom.add_apply, map_add, ha, ha', map_add,
      (B.mul n i).map_add_left]
  | hof w r =>
    induction b using algSections_induction with
    | hzero =>
      rw [map_zero (mulAdd 𝒮 n i U (algOf 𝒮 n w r)), map_zero, map_zero, map_zero]
    | hadd b b' hb hb' =>
      rw [map_add (mulAdd 𝒮 n i U (algOf 𝒮 n w r)), map_add, hb, hb', map_add, map_add]
    | hof w' s =>
      have e : wordDeg w.1 = n := w.2
      have e' : wordDeg w'.1 = i := w'.2
      have ea : wordDeg (w.1 ++ w'.1) = wordDeg w.1 + wordDeg w'.1 := wordDeg_append w.1 w'.1
      have e2 : wordDeg (w.1 ++ w'.1) = n + i := by omega
      rw [mulAdd_algOf, liftAdd_apply, liftAdd_apply, liftAdd_apply, liftPres_algOf,
        liftPres_algOf, liftPres_algOf, (B.mul n i).map_smul_left, (B.mul n i).map_smul_right,
        smul_smul, ← B.mulAt_rfl,
        GradedAlgebra.mulAt_castHom_left B e rfl (by omega : wordDeg w.1 + i = n + i),
        GradedAlgebra.mulAt_castHom_right B e' _ (by omega : wordDeg w.1 + wordDeg w'.1 = n + i),
        ← GradedAlgebra.castHom_mulAt B ea.symm e2, wordEval_append g w.1 w'.1 ea.symm]
      rfl

/-- **The lift of a letter map is multiplicative.** -/
theorem liftPiece_algMul (n i : ℤ) (U : Cᵒᵖ)
    (x : (algPiece (Osharp := Osharp) 𝒮 n).val.obj U)
    (y : (algPiece (Osharp := Osharp) 𝒮 i).val.obj U) :
    (g.liftPiece (n + i)).val.app U ((algMul 𝒮 n i).app U x y) =
      (B.mul n i).app U ((g.liftPiece n).val.app U x) ((g.liftPiece i).val.app U y) := by
  refine eq_of_lift₃ 𝒮 x y y _ _ ?_
  intro Y f a b _ ha hb _
  have hx := g.sectionRestrict_liftPiece f x a ha.symm
  have hy := g.sectionRestrict_liftPiece f y b hb.symm
  have hL := g.sectionRestrict_liftPiece f ((algMul 𝒮 n i).app U x y) (mulAdd 𝒮 n i Y a b)
    (algMul_lift 𝒮 n i U x y f a b ha hb)
  rw [hL, ← liftAdd_apply, liftAdd_mulAdd]
  refine Eq.trans ?_ ((B.mul n i).naturality f _ _).symm
  exact congrArg₂ (fun p q => (B.mul n i).app Y p q) hx.symm hy.symm

/-- The lift of a letter map is multiplicative, with the degree of the product prescribed. -/
theorem liftPiece_mulAt {m j n : ℤ} (h : m + j = n) (U : Cᵒᵖ)
    (x : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
    (y : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U) :
    (g.liftPiece n).val.app U (mulAt 𝒮 h U x y) =
      B.mulAt h U ((g.liftPiece m).val.app U x) ((g.liftPiece j).val.app U y) := by
  exact family_mulAt 𝒮 B g.liftPiece g.liftPiece_algMul h U x y

end LetterMap

/-! ### Uniqueness -/

section Uniqueness

variable {B : GradedAlgebra.{t, t} (toRingCat J Osharp)}

omit [HasWeakSheafify J (Type t)] [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A family of morphisms of sheaves of modules commutes with transport along an equality of
degrees. -/
theorem homFamily_castHom {X Y : ℤ → SheafOfModules.{t} (toRingCat J Osharp)}
    (φ : ∀ n, X n ⟶ Y n) {k n : ℤ} (h : k = n) (U : Cᵒᵖ) (z : (X k).val.obj U) :
    (φ n).val.app U (castHom X h U z) = castHom Y h U ((φ k).val.app U z) := by
  subst h; rfl

/-- **Two multiplicative, unital families of morphisms out of `O⟨S⟩` which agree on the
generators agree.** Every section attached to a word is a product of generators, and the
presentation is spanned by those sections. -/
theorem algPiece_hom_ext_of_algGen (φ ψ : ∀ n, algPiece (Osharp := Osharp) 𝒮 n ⟶ B.piece n)
    (hφ : ∀ (m j : ℤ) (U : Cᵒᵖ) (x : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
      (y : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U),
      (φ (m + j)).val.app U ((algMul 𝒮 m j).app U x y) =
        (B.mul m j).app U ((φ m).val.app U x) ((φ j).val.app U y))
    (hψ : ∀ (m j : ℤ) (U : Cᵒᵖ) (x : (algPiece (Osharp := Osharp) 𝒮 m).val.obj U)
      (y : (algPiece (Osharp := Osharp) 𝒮 j).val.obj U),
      (ψ (m + j)).val.app U ((algMul 𝒮 m j).app U x y) =
        (B.mul m j).app U ((ψ m).val.app U x) ((ψ j).val.app U y))
    (hφ₁ : ∀ U : Cᵒᵖ, (φ 0).val.app U ((algOne (Osharp := Osharp) 𝒮).eval U) = B.one.eval U)
    (hψ₁ : ∀ U : Cᵒᵖ, (ψ 0).val.app U ((algOne (Osharp := Osharp) 𝒮).eval U) = B.one.eval U)
    (hgen : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
      (φ (letterDeg x)).val.app U (algGen (Osharp := Osharp) 𝒮 x) =
        (ψ (letterDeg x)).val.app U (algGen (Osharp := Osharp) 𝒮 x))
    (n : ℤ) : φ n = ψ n := by
  have hword : ∀ {U : Cᵒᵖ} (w : Word 𝒮 U),
      (φ (wordDeg w)).val.app U (algSec (Osharp := Osharp) 𝒮 w) =
        (ψ (wordDeg w)).val.app U (algSec (Osharp := Osharp) 𝒮 w) := by
    intro U w
    induction w with
    | nil => exact (hφ₁ U).trans (hψ₁ U).symm
    | cons x w ih =>
      have h : letterDeg x + wordDeg w = wordDeg (x :: w) := (wordDeg_cons x w).symm
      rw [← mulAt_algGen_algSec 𝒮 x w h, family_mulAt 𝒮 B φ hφ, family_mulAt 𝒮 B ψ hψ, hgen, ih]
  refine algPiece_hom_ext 𝒮 fun U a => ?_
  let F₁ : algSections Osharp 𝒮 n U →+ (B.piece n).val.obj U :=
    ((φ n).val.app U).hom.toAddMonoidHom.comp (algToSheafAdd 𝒮 n U)
  let F₂ : algSections Osharp 𝒮 n U →+ (B.piece n).val.obj U :=
    ((ψ n).val.app U).hom.toAddMonoidHom.comp (algToSheafAdd 𝒮 n U)
  have hF : F₁ = F₂ := by
    refine algSections_addHom_ext 𝒮 fun w r => ?_
    change (φ n).val.app U ((algToSheaf 𝒮 n).app U (algOf 𝒮 n w r)) =
      (ψ n).val.app U ((algToSheaf 𝒮 n).app U (algOf 𝒮 n w r))
    rw [algToSheaf_algOf, map_smul, map_smul, homFamily_castHom φ, homFamily_castHom ψ,
      hword]
  exact DFunLike.congr_fun hF a

end Uniqueness

/-! ### Compatibility with differentials -/

section Derivation

variable {𝒮} (δ : DerivationDatum (Osharp := Osharp) 𝒮)
  {B : GradedAlgebra.{t, t} (toRingCat J Osharp)} (dB : ∀ n, B.piece n ⟶ B.piece (n + 1))
  (hleib : ∀ {m j n : ℤ} (h : m + j = n) (h₁ : m + 1 + j = n + 1) (h₂ : m + (j + 1) = n + 1)
    (U : Cᵒᵖ) (a : (B.piece m).val.obj U) (b : (B.piece j).val.obj U),
    (dB n).val.app U (B.mulAt h U a b) =
      B.mulAt h₁ U ((dB m).val.app U a) b +
        (Int.negOnePow m : ℤ) • B.mulAt h₂ U a ((dB j).val.app U b))
  (hone : ∀ U : Cᵒᵖ, (dB 0).val.app U (B.one.eval U) = 0)
  (g : LetterMap 𝒮 B)
  (hg : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
    (dB (letterDeg x)).val.app U (g.app U x) =
      (g.liftPiece (letterDeg x + 1)).val.app U (δ.app U x))

omit [HasWeakSheafify J (Type t)] [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- A family of morphisms between the pieces of two graded families commutes with transport
along an equality of degrees. -/
theorem homFamilySucc_castHom {X : ℤ → SheafOfModules.{t} (toRingCat J Osharp)}
    (d : ∀ n, X n ⟶ X (n + 1)) {k n : ℤ} (h : k = n) (h' : k + 1 = n + 1) (U : Cᵒᵖ)
    (z : (X k).val.obj U) :
    (d n).val.app U (castHom X h U z) = castHom X h' U ((d k).val.app U z) := by
  subst h; rfl

namespace LetterMap

include hleib hone hg

/-- **The lift carries the Leibniz extension of `δ` on a word to the derivation of the value of
the letter map on it**, for a target carrying a derivation compatible with the letter map. -/
theorem liftPiece_wordD_of_derivation {U : Cᵒᵖ} (w : Word 𝒮 U) :
    (g.liftPiece (wordDeg w + 1)).val.app U (wordD 𝒮 δ w) =
      (dB (wordDeg w)).val.app U (g.wordEval w) := by
  induction w with
  | nil => exact (map_zero _).trans (hone U).symm
  | cons x w ih =>
    have ec : wordDeg (x :: w : Word 𝒮 U) = letterDeg x + wordDeg w := wordDeg_cons x w
    have h₁ : letterDeg x + 1 + wordDeg w = wordDeg (x :: w) + 1 := by omega
    have h₂ : letterDeg x + (wordDeg w + 1) = wordDeg (x :: w) + 1 := by omega
    rw [wordD_cons 𝒮 δ x w h₁ h₂, map_add, map_zsmul, g.liftPiece_mulAt, g.liftPiece_mulAt,
      g.liftPiece_algSec, g.liftPiece_algGen, ih, ← hg, wordEval_cons g x w ec.symm]
    exact (hleib ec.symm h₁ h₂ U _ _).symm

/-- **The lift commutes with the differentials**, for a target carrying a derivation compatible
with the letter map on the generators. -/
theorem algD_comp_liftPiece_of_derivation (n : ℤ) :
    algD 𝒮 δ n ≫ g.liftPiece (n + 1) = g.liftPiece n ≫ dB n := by
  refine algPiece_hom_ext 𝒮 fun U a => ?_
  change (g.liftPiece (n + 1)).val.app U ((algD 𝒮 δ n).val.app U ((algToSheaf 𝒮 n).app U a)) =
    (dB n).val.app U ((g.liftPiece n).val.app U ((algToSheaf 𝒮 n).app U a))
  rw [algD_toSheaf, liftPiece_toSheaf]
  let F₁ : algSections Osharp 𝒮 n U →+ (B.piece (n + 1)).val.obj U :=
    ((g.liftPiece (n + 1)).val.app U).hom.toAddMonoidHom.comp (algDAdd 𝒮 δ n U)
  let F₂ : algSections Osharp 𝒮 n U →+ (B.piece (n + 1)).val.obj U :=
    ((dB n).val.app U).hom.toAddMonoidHom.comp (g.liftAdd n U)
  have hF : F₁ = F₂ := by
    refine algSections_addHom_ext 𝒮 fun w r => ?_
    change (g.liftPiece (n + 1)).val.app U ((algDHom 𝒮 δ n).app U (algOf 𝒮 n w r)) =
      (dB n).val.app U ((g.liftPres n).app U (algOf 𝒮 n w r))
    rw [algDHom_algOf, liftPres_algOf, map_smul, map_smul, liftPiece_castHom,
      g.liftPiece_wordD_of_derivation δ dB hleib hone hg]
    exact congrArg (r • ·) (homFamilySucc_castHom dB w.2 _ U _).symm
  exact DFunLike.congr_fun hF a

end LetterMap

end Derivation

section Differential

variable {𝒮} (δ : DerivationDatum (Osharp := Osharp) 𝒮)
  {B : DifferentialGradedAlgebra.{t, t} (toRingCat J Osharp)}
  (g : LetterMap 𝒮 B.toGradedAlgebra)

namespace LetterMap

section Compatible

variable (hg : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
  (B.complex.d (letterDeg x) (letterDeg x + 1)).val.app U (g.app U x) =
    (g.liftPiece (letterDeg x + 1)).val.app U (δ.app U x))

include hg

/-- **The lift commutes with the differentials**, as soon as the letter map does on the
generators. -/
theorem algD_comp_liftPiece (n : ℤ) :
    algD 𝒮 δ n ≫ g.liftPiece (n + 1) = g.liftPiece n ≫ B.complex.d n (n + 1) :=
  g.algD_comp_liftPiece_of_derivation δ (fun n => B.complex.d n (n + 1))
    (fun h h₁ h₂ U a b => DifferentialGradedAlgebra.d_mulAt B h h₁ h₂ U a b)
    (fun U => B.one_closed U) hg n

end Compatible

/-- **The universal property of `O⟨S⟩` with a differential**: the homomorphism of sheaves of
differential graded algebras out of `O⟨S⟩`, with the Leibniz extension of `δ` as its
differential, which sends the generator of every letter `x` to `g(x)`. -/
noncomputable def dgLift
    (hδ : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
      (algD 𝒮 δ (letterDeg x + 1)).val.app U (δ.app U x) = 0)
    (hg : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
      (B.complex.d (letterDeg x) (letterDeg x + 1)).val.app U (g.app U x) =
        (g.liftPiece (letterDeg x + 1)).val.app U (δ.app U x)) :
    freeDGAlgebra 𝒮 δ hδ ⟶ B where
  toHomologicalComplex :=
    { f := g.liftPiece
      comm' := by
        rintro i j (rfl : i + 1 = j)
        change _ = algDRel 𝒮 δ i (i + 1) ≫ _
        rw [algDRel_self]
        exact (g.algD_comp_liftPiece δ hg i).symm }
  map_mul n m U x y := g.liftPiece_algMul n m U x y

variable (hδ : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
    (algD 𝒮 δ (letterDeg x + 1)).val.app U (δ.app U x) = 0)
  (hg : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
    (B.complex.d (letterDeg x) (letterDeg x + 1)).val.app U (g.app U x) =
      (g.liftPiece (letterDeg x + 1)).val.app U (δ.app U x))

/-- The degree-`n` component of `dgLift` is the lift `liftPiece n`. -/
@[simp] theorem dgLift_f (n : ℤ) : (g.dgLift δ hδ hg).toHomologicalComplex.f n = g.liftPiece n :=
  rfl

/-- The universal homomorphism out of `O⟨S⟩` is unital. -/
theorem dgLift_isUnital (U : Cᵒᵖ) :
    ((g.dgLift δ hδ hg).toHomologicalComplex.f 0).val.app U
        ((freeDGAlgebra 𝒮 δ hδ).one.eval U) = B.one.eval U :=
  g.liftPiece_one U

/-- The universal homomorphism out of `O⟨S⟩` sends the generator of a letter `x` to `g(x)`. -/
theorem dgLift_algGen {U : Cᵒᵖ} (x : Letter 𝒮 U) :
    ((g.dgLift δ hδ hg).toHomologicalComplex.f (letterDeg x)).val.app U
        (algGen (Osharp := Osharp) 𝒮 x) = g.app U x :=
  g.liftPiece_algGen x

end LetterMap

/-- **Two unital homomorphisms of sheaves of differential graded algebras out of `O⟨S⟩` which
agree on the generators are equal.** -/
theorem freeDGAlgebra_hom_ext
    (hδ : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
      (algD 𝒮 δ (letterDeg x + 1)).val.app U (δ.app U x) = 0)
    {φ ψ : freeDGAlgebra 𝒮 δ hδ ⟶ B}
    (hφ : ∀ U : Cᵒᵖ, (φ.toHomologicalComplex.f 0).val.app U
      ((freeDGAlgebra 𝒮 δ hδ).one.eval U) = B.one.eval U)
    (hψ : ∀ U : Cᵒᵖ, (ψ.toHomologicalComplex.f 0).val.app U
      ((freeDGAlgebra 𝒮 δ hδ).one.eval U) = B.one.eval U)
    (hgen : ∀ (U : Cᵒᵖ) (x : Letter 𝒮 U),
      (φ.toHomologicalComplex.f (letterDeg x)).val.app U (algGen (Osharp := Osharp) 𝒮 x) =
        (ψ.toHomologicalComplex.f (letterDeg x)).val.app U (algGen (Osharp := Osharp) 𝒮 x)) :
    φ = ψ :=
  SheafOfModules.DifferentialGradedAlgebra.Hom.ext fun n =>
    algPiece_hom_ext_of_algGen (B := B.toGradedAlgebra) 𝒮 (fun n => φ.toHomologicalComplex.f n)
      (fun n => ψ.toHomologicalComplex.f n) φ.map_mul ψ.map_mul hφ hψ hgen n

end Differential

end Lift

end SheafOfModules

end
