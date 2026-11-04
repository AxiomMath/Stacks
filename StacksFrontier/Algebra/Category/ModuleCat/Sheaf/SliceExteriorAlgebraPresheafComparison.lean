module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafificationRecognition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedSliceRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SlicePowerRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraInhabitant

/-!
# The sectionwise exterior algebra and restriction to a slice site: the presheaf-level comparison

Let `C` be a category, `O` a presheaf of commutative rings on it, `F` a presheaf of modules over
the underlying presheaf of rings and `U : C`. `Stacks.GradedAlgebra.extend` of
`PresheafOfModules.extPowGradedAlgebra` is the `ℤ`-graded algebra of presheaves of modules whose
degree-`n` piece is the presheaf `V ↦ ⋀ⁿ_{O(V)}(F(V))` for `n ≥ 0` and the zero presheaf below
zero; `SheafOfModules.sectionwiseExteriorAlgebra` is its degreewise sheafification.

We compare that graded algebra for the restriction of `F` to the slice site over `U` with the
restriction of the graded algebra of `F` to the slice site: the comparison is an isomorphism in
every integer degree, is multiplicative on homogeneous local sections, and carries the degree-zero
unit to the degree-zero unit.

## Main definitions

* `Stacks.SheafOfModules.SliceExterior.sliceBilinear`: a bilinear map of presheaves of modules,
  restricted to the slice site at `U`.
* `Stacks.SheafOfModules.SliceExterior.extendExtPowOver`: the comparison in every integer
  degree — `PresheafOfModules.extPowOverIso` in a nonnegative degree and the zero morphism in a
  negative degree, where both sides are the zero presheaf.
* `Stacks.SheafOfModules.SliceExterior.extendExtPowOverIso`: the same, as an isomorphism.

## Main results

* `Stacks.SheafOfModules.SliceExterior.extendExtPowOver_mul` and `extendExtPowOver_one`: the
  comparison is multiplicative and unital.
* `Stacks.SheafOfModules.SliceExterior.isIso_extendExtPowOver` and
  `isIso_toPresheaf_map_extendExtPowOver`: the comparison is invertible in every integer degree,
  as a morphism of presheaves of modules and on the underlying presheaves of abelian groups.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite PresheafOfModules
  Stacks.SheafOfModules.SliceSheafification

universe v u w

namespace Stacks.SheafOfModules.SliceExterior

section Comparison

variable {C : Type u} [Category.{v} C] (U : C) {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}))

/-- The family of sectionwise exterior powers of the restriction of `F` to the slice site at
`U`, extended by zero into the negative degrees. -/
abbrev sliceExtPowFamily : ℤ → PresheafOfModules.{w} ((Over.forget U).op ⋙ O ⋙
    forget₂ CommRingCat.{w} RingCat.{w}) :=
  Stacks.GradedAlgebra.extendFamily
    (fun k => extPow (O := (Over.forget U).op ⋙ O) k ((sliceRestrict U (O := O)).obj F))

/-- The comparison from the sectionwise exterior powers of the restriction of `F` to the
restriction of the sectionwise exterior powers of `F`, in every integer degree. In a
nonnegative degree it is `PresheafOfModules.extPowOverIso`, the identity on sections; in a
negative degree both sides are the zero presheaf and it is the zero morphism. -/
def extendExtPowOver : (n : ℤ) → sliceExtPowFamily U F n ⟶
    (sliceRestrict U (O := O)).obj
      (Stacks.GradedAlgebra.extendFamily (fun k => extPow k F) n)
  | Int.ofNat k => (extPowOverIso U k F).inv
  | Int.negSucc _ => 0

/-- In a nonnegative degree the comparison is `PresheafOfModules.extPowOverIso`. -/
theorem extendExtPowOver_natCast (k : ℕ) :
    extendExtPowOver U F (k : ℤ) = (extPowOverIso U k F).inv := rfl

/-- The comparison `extendExtPowOver`, in every integer degree, as an isomorphism. In a
nonnegative degree it is `PresheafOfModules.extPowOverIso`; in a negative degree both sides are the
zero presheaf and it is the zero morphism. -/
def extendExtPowOverIso : (n : ℤ) → (sliceExtPowFamily U F n ≅
    (sliceRestrict U (O := O)).obj
      (Stacks.GradedAlgebra.extendFamily (fun k => extPow k F) n))
  | Int.ofNat k => (extPowOverIso U k F).symm
  | Int.negSucc _ =>
    { hom := 0
      inv := 0
      hom_inv_id := by ext X x; exact Subsingleton.elim (α := PUnit.{w + 1}) _ _
      inv_hom_id := by ext X x; exact Subsingleton.elim (α := PUnit.{w + 1}) _ _ }

/-- The forward morphism of `extendExtPowOverIso` is the comparison `extendExtPowOver`. -/
theorem extendExtPowOverIso_hom :
    (n : ℤ) → (extendExtPowOverIso U F n).hom = extendExtPowOver U F n
  | Int.ofNat _ => rfl
  | Int.negSucc _ => rfl

/-- The comparison `extendExtPowOver` is an isomorphism in every integer degree. -/
instance isIso_extendExtPowOver (n : ℤ) : IsIso (extendExtPowOver U F n) :=
  extendExtPowOverIso_hom U F n ▸ (extendExtPowOverIso U F n).isIso_hom

/-- The comparison `extendExtPowOver` is invertible on the underlying presheaves of abelian
groups. -/
instance isIso_toPresheaf_map_extendExtPowOver (n : ℤ) :
    IsIso ((PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ O ⋙
      forget₂ CommRingCat.{w} RingCat.{w})).map (extendExtPowOver U F n)) :=
  (PresheafOfModules.toPresheaf ((Over.forget U).op ⋙ O ⋙
    forget₂ CommRingCat.{w} RingCat.{w})).map_isIso _

/-- A bilinear map of presheaves of modules, restricted to the slice site at `U`: its value on
the sections over an object of the slice site is the value of the original on the sections over
the underlying object. -/
def sliceBilinear {M N Q : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (b : Stacks.BilinearMap M N Q) :
    Stacks.BilinearMap ((sliceRestrict U (O := O)).obj M) ((sliceRestrict U (O := O)).obj N)
      ((sliceRestrict U (O := O)).obj Q) where
  app V := b.app (op V.unop.left)
  map_smul_left V r x y := b.map_smul_left (op V.unop.left) r x y
  map_smul_right V r x y := b.map_smul_right (op V.unop.left) r x y
  naturality f x y := b.naturality f.unop.left.op x y

/-- The value of `sliceBilinear U b` on the sections over an object `V` of the slice site is
the value of `b` on the sections over the underlying object `V.unop.left`. -/
@[simp]
theorem sliceBilinear_app
    {M N Q : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})}
    (b : Stacks.BilinearMap M N Q) (V : (Over U)ᵒᵖ) :
    (sliceBilinear U b).app V = b.app (op V.unop.left) := rfl

/-- The comparison `extendExtPowOver` is multiplicative on homogeneous local sections. -/
theorem extendExtPowOver_mul (i j : ℤ) (V : (Over U)ᵒᵖ)
    (x : (sliceExtPowFamily U F i).obj V) (y : (sliceExtPowFamily U F j).obj V) :
    PresheafOfModules.Hom.app (extendExtPowOver U F (i + j)) V
        (((PresheafOfModules.extPowGradedAlgebra (O := (Over.forget U).op ⋙ O)
          ((sliceRestrict U (O := O)).obj F)).extend.mul i j).app V x y) =
      (sliceBilinear U ((PresheafOfModules.extPowGradedAlgebra F).extend.mul i j)).app V
        (PresheafOfModules.Hom.app (extendExtPowOver U F i) V x)
        (PresheafOfModules.Hom.app (extendExtPowOver U F j) V y) := by
  have zero_case : ∀ (z : (sliceExtPowFamily U F (i + j)).obj V) w, z = 0 → w = 0 →
      PresheafOfModules.Hom.app (extendExtPowOver U F (i + j)) V z = w := by
    rintro z w rfl rfl
    exact map_zero _
  rcases lt_or_ge i 0 with hi | hi
  · exact zero_case _ _
      ((PresheafOfModules.extPowGradedAlgebra (O := (Over.forget U).op ⋙ O)
        ((sliceRestrict U (O := O)).obj F)).extendMul_app_eq_zero_of_neg_left hi j V x y)
      ((PresheafOfModules.extPowGradedAlgebra F).extendMul_app_eq_zero_of_neg_left hi j
        (op V.unop.left) _ _)
  rcases lt_or_ge j 0 with hj | hj
  · exact zero_case _ _
      ((PresheafOfModules.extPowGradedAlgebra (O := (Over.forget U).op ⋙ O)
        ((sliceRestrict U (O := O)).obj F)).extendMul_app_eq_zero_of_neg_right i hj V x y)
      ((PresheafOfModules.extPowGradedAlgebra F).extendMul_app_eq_zero_of_neg_right i hj
        (op V.unop.left) _ _)
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hi
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  rfl

/-- The comparison `extendExtPowOver` carries the degree-zero unit to the degree-zero unit. -/
theorem extendExtPowOver_one (V : (Over U)ᵒᵖ) :
    PresheafOfModules.Hom.app (extendExtPowOver U F 0) V
        ((PresheafOfModules.extPowGradedAlgebra (O := (Over.forget U).op ⋙ O)
          ((sliceRestrict U (O := O)).obj F)).extend.one.eval V) =
      (PresheafOfModules.extPowGradedAlgebra F).extend.one.eval (op V.unop.left) := rfl

end Comparison

end Stacks.SheafOfModules.SliceExterior

end
