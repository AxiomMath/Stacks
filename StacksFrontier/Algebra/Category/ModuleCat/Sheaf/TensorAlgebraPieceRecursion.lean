module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseTensorAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.LinearAlgebra.TensorAlgebra.ToTensorPowerRange

/-!
# The tensor-power recursion for the sectionwise tensor algebra

`SheafOfModules.tensorPowerSheafifyIso` (in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraConstruction`) identifies the
sheafification of a family `Q : ℕ → PresheafOfModules _` with the tensor powers of a sheaf of
modules, given three inputs: the degree-zero and degree-one identifications, and the recursion
`Q (n + 2) ≅ tensorObj (Q 1) (Q (n + 1))`.  For the family of homogeneous pieces of the
sectionwise tensor algebra (`PresheafOfModules.tensorAlgebraPiece`) this file supplies the third
input, as `PresheafOfModules.tensorAlgebraPieceRecursion`.

The comparison **is** multiplication: `tensorAlgebraPieceMul` is the morphism out of the
objectwise tensor product induced by ring multiplication in the tensor algebra of the sections.
That choice makes naturality in the site free — base change `TensorAlgebra.mapₛₗ` is a ring
homomorphism, so the restriction maps commute with multiplication on the nose — and leaves only
bijectivity over each object, which is the module-level statement
`TensorAlgebra.powRangeMulEquivOfEq` of
`StacksFrontier.LinearAlgebra.TensorAlgebra.ToTensorPowerRange`.

## Main definitions

* `PresheafOfModules.tensorAlgebraPieceMul`: multiplication of two homogeneous pieces, as a
  morphism `tensorObj (tensorAlgebraPiece i F) (tensorAlgebraPiece j F) ⟶ tensorAlgebraPiece k F`
  for any `i + j = k`.
* `PresheafOfModules.tensorAlgebraPieceTensorIso`: the same morphism as an isomorphism.
* `PresheafOfModules.tensorAlgebraPieceRecursion`: it in the shape
  `SheafOfModules.tensorPowerSheafifyIso` consumes, `Q (n + 2) ≅ tensorObj (Q 1) (Q (n + 1))` for
  `Q = fun n => tensorAlgebraPiece (n : ℤ) F`.

## Main results

* `PresheafOfModules.tensorAlgebraPieceMul_app_bijective`: multiplication is bijective on
  sections over every object.  This is the one place the module-level bridge is used.
* `PresheafOfModules.tensorAlgebraPieceVal_mul_app` and
  `tensorAlgebraPieceVal_tensorAlgebraPieceRecursion_inv`: the equation that pins the comparison
  down, on a pure tensor of local sections, in both of the two forms a consumer needs.

## Implementation notes

**The target degree is a parameter.** `tensorAlgebraPieceMul` takes `i`, `j`, `k` and
`h : i + j = k` rather than landing in degree `i + j`, because the consumer's degrees are
presented as `1 + (n + 1)` on one side and `n + 2` on the other, and `1 + (n + 1)` is *not*
definitionally `n + 2` — only `(n + 1) + 1` is.  Carrying the equation as a parameter pays that
transport once, as an equation between naturals, instead of as an `Eq.mp` inside every term.

**Bijectivity is proved pointwise, not by an equality of morphisms.** The comparison is shown to
agree with `TensorAlgebra.powRangeMulEquivOfEq` section by section (`key` in the proof of
`tensorAlgebraPieceMul_app_bijective`).  The two sides live at types that agree definitionally but
not syntactically — one is a `ModuleCat` object, the other a subtype — so the additivity step is
term-mode `congrArg₂` rather than `rw [map_add]`, which runs at reducible transparency and fails
there.

**No `@[stacks]` tag.** Nothing here is sheafified, so nothing here is the content of a tag; see
the same remark in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SectionwiseTensorAlgebra`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w a

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat))

/-- **Multiplication of two homogeneous pieces of the sectionwise tensor algebra**, as a morphism
out of their objectwise tensor product.  Naturality is `TensorAlgebra.mapₛₗ` being a ring
homomorphism. -/
noncomputable def tensorAlgebraPieceMul (i j k : ℕ) (h : i + j = k) :
    tensorObj (tensorAlgebraPiece (i : ℤ) F) (tensorAlgebraPiece (j : ℤ) F) ⟶
      tensorAlgebraPiece (k : ℤ) F :=
  tensorMk
    (fun X x y =>
      ⟨tensorAlgebraPieceVal (i : ℤ) F X x * tensorAlgebraPieceVal (j : ℤ) F X y, by
        have hk : ((i : ℤ) + (j : ℤ)) = (k : ℤ) := by omega
        exact hk ▸ TensorAlgebra.mul_mem_intPiece _ _ (i : ℤ) (j : ℤ)
          (x : ↥(TensorAlgebra.intPiece _ _ (i : ℤ))).2
          (y : ↥(TensorAlgebra.intPiece _ _ (j : ℤ))).2⟩)
    (fun _ _ _ _ => Subtype.ext (add_mul _ _ _))
    (fun _ _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ _ => Subtype.ext (mul_add _ _ _))
    (fun _ _ _ _ => Subtype.ext (mul_smul_comm _ _ _))
    (fun _ _ _ _ _ => Subtype.ext (map_mul _ _ _))

/-- On a pure tensor of local sections, `tensorAlgebraPieceMul` is multiplication in the tensor
algebra of the sections. -/
@[simp]
theorem tensorAlgebraPieceVal_mul_app (i j k : ℕ) (h : i + j = k) (X : Cᵒᵖ)
    (x : (tensorAlgebraPiece (i : ℤ) F).obj X) (y : (tensorAlgebraPiece (j : ℤ) F).obj X) :
    tensorAlgebraPieceVal (k : ℤ) F X
        (Hom.app (tensorAlgebraPieceMul F i j k h) X (x ⊗ₜ y)) =
      tensorAlgebraPieceVal (i : ℤ) F X x * tensorAlgebraPieceVal (j : ℤ) F X y := rfl

/-- **Multiplication of homogeneous pieces is bijective on sections.**  This is the sectionwise
content of the tensor-power recursion, and the one place the module-level bridge
`TensorAlgebra.powRangeMulEquivOfEq` is used. -/
theorem tensorAlgebraPieceMul_app_bijective (i j k : ℕ) (h : i + j = k) (X : Cᵒᵖ) :
    Function.Bijective (Hom.app (tensorAlgebraPieceMul F i j k h) X) := by
  set e := TensorAlgebra.powRangeMulEquivOfEq (R := (O ⋙ forget₂ _ RingCat).obj X)
    (M := F.obj X) h
  have key : ∀ z, Hom.app (tensorAlgebraPieceMul F i j k h) X z = e z := by
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    · exact fun u v => Subtype.ext rfl
    · exact fun u v hu hv =>
        (map_add _ u v).trans ((congrArg₂ (· + ·) hu hv).trans (map_add e u v).symm)
  refine ⟨fun x y hxy => e.injective ((key x).symm.trans (hxy.trans (key y))), fun z => ?_⟩
  obtain ⟨w, hw⟩ := e.surjective z
  exact ⟨w, (key w).trans hw⟩

/-- **The homogeneous pieces of the sectionwise tensor algebra multiply isomorphically**: the
objectwise tensor product of the degree-`i` and degree-`j` pieces is the degree-`i + j` piece, by
multiplication. -/
noncomputable def tensorAlgebraPieceTensorIso (i j k : ℕ) (h : i + j = k) :
    tensorObj (tensorAlgebraPiece (i : ℤ) F) (tensorAlgebraPiece (j : ℤ) F) ≅
      tensorAlgebraPiece (k : ℤ) F := by
  have hiso : ∀ X : Cᵒᵖ, IsIso ((tensorAlgebraPieceMul F i j k h).app X) := fun X =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (tensorAlgebraPieceMul_app_bijective F i j k h X)
  refine isoMk (fun X => asIso ((tensorAlgebraPieceMul F i j k h).app X)) ?_
  intro X Y f
  exact (tensorAlgebraPieceMul F i j k h).naturality f

/-- The forward map of `tensorAlgebraPieceTensorIso` is `tensorAlgebraPieceMul`. -/
@[simp]
theorem tensorAlgebraPieceTensorIso_hom (i j k : ℕ) (h : i + j = k) :
    (tensorAlgebraPieceTensorIso F i j k h).hom = tensorAlgebraPieceMul F i j k h := rfl

/-- **The tensor-power recursion for the sectionwise tensor algebra**, in the shape
`SheafOfModules.tensorPowerSheafifyIso` consumes: with
`Q = fun n => tensorAlgebraPiece (n : ℤ) F` this is `Q (n + 2) ≅ tensorObj (Q 1) (Q (n + 1))`. -/
noncomputable def tensorAlgebraPieceRecursion (n : ℕ) :
    tensorAlgebraPiece ((n + 2 : ℕ) : ℤ) F ≅
      tensorObj (tensorAlgebraPiece ((1 : ℕ) : ℤ) F)
        (tensorAlgebraPiece ((n + 1 : ℕ) : ℤ) F) :=
  (tensorAlgebraPieceTensorIso F 1 (n + 1) (n + 2) (by omega)).symm

/-- The recursion, read on a pure tensor of local sections: it is multiplication.  This is the
equation the `tensorPieceIso_mul_left` field of
`SheafOfModules.TensorExteriorSymmetricAlgebras` is proved from. -/
@[simp]
theorem tensorAlgebraPieceVal_tensorAlgebraPieceRecursion_inv (n : ℕ) (X : Cᵒᵖ)
    (x : (tensorAlgebraPiece ((1 : ℕ) : ℤ) F).obj X)
    (y : (tensorAlgebraPiece ((n + 1 : ℕ) : ℤ) F).obj X) :
    tensorAlgebraPieceVal ((n + 2 : ℕ) : ℤ) F X
        (Hom.app (tensorAlgebraPieceRecursion F n).inv X (x ⊗ₜ y)) =
      tensorAlgebraPieceVal ((1 : ℕ) : ℤ) F X x *
        tensorAlgebraPieceVal ((n + 1 : ℕ) : ℤ) F X y := rfl

end PresheafOfModules

end
