module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiIdempotentComplete

/-!
# Splitting a twisted idempotent along orthogonal idempotents

Let `M = (X, p, m)` be an object of the twisted Karoubi envelope of a graded category. A pair of
orthogonal idempotents `a`, `b` of `M` summing to the identity exhibits `M` as the direct sum of
the two objects `(X, a, m)` and `(X, b, m)` they cut out
(`CategoryTheory.GradedCategory.TwistedKaroubi.imageOfIdem`).

For the category `M_k` of Chow motives (Stacks Section 0FG9) this is the step by which the two
orthogonal projectors `c₀`, `c₂` of Example 0FG6 split `h(P¹_k)` (Stacks 0FGG).

## Main definitions

* `CategoryTheory.GradedCategory.TwistedKaroubi.imageOfIdemBicone`: the binary bicone with point
  `M` over the two objects cut out by orthogonal idempotents of `M`.
* `CategoryTheory.GradedCategory.TwistedKaroubi.imageOfIdemBiproductData`: if the two
  idempotents sum to the identity of `M`, that bicone is a bilimit.
* `CategoryTheory.GradedCategory.TwistedKaroubi.ofObjBiproductData`: the same for `(X, 1, 0)`,
  with the two idempotents given as degree-zero endomorphisms of `X`.
-/

@[expose] public section

namespace CategoryTheory.GradedCategory.TwistedKaroubi

open CategoryTheory.Limits

universe w v u

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C] [GradedCategory R C]
  (M : TwistedKaroubi R C) {a b : M ⟶ M} (ha : a ≫ a = a) (hb : b ≫ b = b)

/-- The binary bicone with point `M = (X, p, m)` over the objects `(X, a, m)` and `(X, b, m)` cut
out by orthogonal idempotents `a`, `b` of `M`: the injections and the projections are given by
`a` and `b` themselves. -/
@[simps]
def imageOfIdemBicone (hab : a ≫ b = 0) (hba : b ≫ a = 0) :
    BinaryBicone (imageOfIdem M a ha) (imageOfIdem M b hb) where
  pt := M
  fst := imageOfIdemπ M a ha
  snd := imageOfIdemπ M b hb
  inl := imageOfIdemι M a ha
  inr := imageOfIdemι M b hb
  inl_snd := by
    ext
    exact (congrArg Hom.val hab :)
  inr_fst := by
    ext
    exact (congrArg Hom.val hba :)

/-- If two orthogonal idempotents `a`, `b` of `M = (X, p, m)` sum to the identity, then `M` is
the direct sum of the objects `(X, a, m)` and `(X, b, m)` they cut out: the bicone
`CategoryTheory.GradedCategory.TwistedKaroubi.imageOfIdemBicone` is a bilimit. -/
def imageOfIdemBiproductData (hab : a ≫ b = 0) (hba : b ≫ a = 0) (hsum : a + b = 𝟙 M) :
    BinaryBiproductData (imageOfIdem M a ha) (imageOfIdem M b hb) where
  bicone := imageOfIdemBicone M ha hb hab hba
  isBilimit := isBinaryBilimitOfTotal _ (by
    change imageOfIdemπ M a ha ≫ imageOfIdemι M a ha +
      imageOfIdemπ M b hb ≫ imageOfIdemι M b hb = 𝟙 M
    rw [imageOfIdemπ_ι, imageOfIdemπ_ι, hsum])

/-- The point of the bicone of `imageOfIdemBiproductData` is `M` itself. -/
@[simp]
theorem imageOfIdemBiproductData_bicone_pt (hab : a ≫ b = 0) (hba : b ≫ a = 0)
    (hsum : a + b = 𝟙 M) : (imageOfIdemBiproductData M ha hb hab hba hsum).bicone.pt = M :=
  rfl

variable {M} in
/-- If two orthogonal degree-zero idempotents `a`, `b` of an object `X` of `C` sum to the
identity, then `(X, 1, 0)` is the direct sum of `(X, a, 0)` and `(X, b, 0)`. This is
`CategoryTheory.GradedCategory.TwistedKaroubi.imageOfIdemBiproductData` at
`CategoryTheory.GradedCategory.TwistedKaroubi.ofObj`, with the idempotents given in `C`. -/
def ofObjBiproductData (X : C) {a b : X ⟶ X} (ha : a ∈ grade (R := R) X X 0)
    (hb : b ∈ grade (R := R) X X 0) (haa : a ≫ a = a) (hbb : b ≫ b = b) (hab : a ≫ b = 0)
    (hba : b ≫ a = 0) (hsum : a + b = 𝟙 X) :
    BinaryBiproductData (⟨X, a, ha, haa, 0⟩ : TwistedKaroubi R C) ⟨X, b, hb, hbb, 0⟩ :=
  imageOfIdemBiproductData (ofObj X) (a := Hom.mk a (mem_homSubmodule_ofObj.2 ha))
    (b := Hom.mk b (mem_homSubmodule_ofObj.2 hb)) (hom_ext haa) (hom_ext hbb) (hom_ext hab)
    (hom_ext hba) (hom_ext hsum)

/-- The point of the bicone of `ofObjBiproductData` is `(X, 1, 0)`, that is, `ofObj X`. -/
@[simp]
theorem ofObjBiproductData_bicone_pt (X : C) {a b : X ⟶ X} (ha : a ∈ grade (R := R) X X 0)
    (hb : b ∈ grade (R := R) X X 0) (haa : a ≫ a = a) (hbb : b ≫ b = b) (hab : a ≫ b = 0)
    (hba : b ≫ a = 0) (hsum : a + b = 𝟙 X) :
    (ofObjBiproductData X ha hb haa hbb hab hba hsum).bicone.pt = ofObj X :=
  rfl

end CategoryTheory.GradedCategory.TwistedKaroubi

end
