module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrict
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraFunctoriality

/-!
# A sheaf of graded algebras from multiplications out of the localized tensor product

Two monoidal structures on sheaves of modules over a sheaf of commutative rings are in use:
`Stacks.SheafOfModules.monoidalCategory`, the localization along sheafification of the objectwise
structure on presheaves of modules, whose tensor product is only isomorphic to the tensor product
sheaf of Tag 01CA through `Stacks.SheafOfModules.tensorObjIso`; and
`Stacks.SheafOfModules.Strict.monoidalCategory`, whose tensor product *is* that sheaf and whose
structural morphisms are the localized ones conjugated by `tensorObjIso`.
`SheafOfModules.GradedAlgebra.ofMorphismData` assembles a sheaf of graded algebras out of a
multiplication and a unit given as morphisms for the **strict** structure.  The multiplications
that descent along an étale presentation produces, on an algebraic space for instance, are
morphisms for the **localized** structure.  This file is the bridge: it conjugates such a
multiplication by `tensorObjIso`, transports the three algebra axioms from the localized to the
strict structure, and feeds the result to `ofMorphismData`.

## Main definitions

* `SheafOfModules.GradedAlgebra.ofLocalizedMorphismData`: **a sheaf of graded algebras assembled
  from a degreewise family of sheaves of modules, a multiplication out of the localized tensor
  product and a unit**, satisfying associativity and the two unit laws as equalities of morphisms
  for the localized monoidal structure.

## Main results

* `Stacks.MonoidalGraded.conjMul_assoc`, `conjOne_mul`, `conjMul_one` and `conjMul_comm`: the
  conjugate by an identification of tensor products of a multiplication that is associative,
  respectively has a left or a right unit, has the same property for the conjugated structural
  morphisms, which is how the structural morphisms of the strict structure are defined.
* `SheafOfModules.GradedAlgebra.ofLocalizedMorphismData_piece`,
  `ofLocalizedMorphismData_mul_app` and `ofLocalizedMorphismData_one`: the data of
  `ofLocalizedMorphismData`.
* `SheafOfModules.GradedAlgebra.ofLocalizedMorphismData_mul_comm`: a multiplication commuting
  with the braiding of the localized structure gives commuting homogeneous local sections.
* `SheafOfModules.GradedAlgebra.mulSheaf_ofLocalizedMorphismData` and
  `oneHom_ofLocalizedMorphismData`: its morphism-level multiplication and unit are the given
  ones.

## Implementation notes

The structural morphisms of the strict structure are defined as conjugates of the localized
ones (`Stacks.SheafOfModules.Strict.whiskerRight_eq`, `…whiskerLeft_eq`, `…associator_eq`,
`…leftUnitor_eq`, `…rightUnitor_eq`, all `rfl`), so the transport is a cancellation of
`tensorObjIso` against its inverse and nothing else.  The degree bookkeeping of a graded algebra
is absorbed into unconstrained outer multiplications, as in
`Stacks.MonoidalGraded.mapMul_assoc`, so that no `eqToHom` enters the transport lemmas.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

open scoped TensorProduct

universe v u w

namespace Stacks.MonoidalGraded

/-! ### Conjugating a multiplication by an identification of tensor products -/

section Conjugate

variable {D : Type*} [Category D] [MonoidalCategory D] {T : D → D → D}
  (e : ∀ X Y : D, X ⊗ Y ≅ T X Y)

/-- **Conjugation by an identification of tensor products transports associativity.**  For
objects `T X Y` identified with the tensor products by `e`, and multiplications `m₁₂`, `m₂₃`, `l`,
`r` out of tensor products, associative up to a tail `t`, the conjugates by `e` are associative for
the whiskerings and the associator conjugated by `e`.  This is the shape in which the structural
morphisms of `Stacks.SheafOfModules.Strict.monoidalCategory` are defined from those of the
localized structure. -/
theorem conjMul_assoc {X₁ X₂ X₃ X₁₂ X₂₃ W W' : D} (m₁₂ : X₁ ⊗ X₂ ⟶ X₁₂)
    (m₂₃ : X₂ ⊗ X₃ ⟶ X₂₃) (l : X₁₂ ⊗ X₃ ⟶ W) (r : X₁ ⊗ X₂₃ ⟶ W') (t : W' ⟶ W)
    (h : m₁₂ ▷ X₃ ≫ l = (α_ X₁ X₂ X₃).hom ≫ X₁ ◁ m₂₃ ≫ r ≫ t) :
    ((e (T X₁ X₂) X₃).inv ≫ ((e X₁ X₂).inv ≫ m₁₂) ▷ X₃ ≫ (e X₁₂ X₃).hom) ≫
        (e X₁₂ X₃).inv ≫ l =
      (((e (T X₁ X₂) X₃).symm ≪≫ ((e X₁ X₂).symm ⊗ᵢ Iso.refl X₃)) ≪≫ α_ X₁ X₂ X₃ ≪≫
          ((Iso.refl X₁ ⊗ᵢ e X₂ X₃) ≪≫ e X₁ (T X₂ X₃))).hom ≫
        ((e X₁ (T X₂ X₃)).inv ≫ X₁ ◁ ((e X₂ X₃).inv ≫ m₂₃) ≫ (e X₁ X₂₃).hom) ≫
          ((e X₁ X₂₃).inv ≫ r) ≫ t := by
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Category.assoc,
    Iso.hom_inv_id_assoc, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, tensorHom_id,
    id_tensorHom, whiskerLeft_hom_inv_assoc, h]

/-- **Conjugation by an identification of tensor products transports a left unit law**, for the
whiskering and the left unitor conjugated by the identification. -/
theorem conjOne_mul {X Y Z : D} (o : 𝟙_ D ⟶ X) (m : X ⊗ Y ⟶ Z) (l : Y ⟶ Z)
    (h : o ▷ Y ≫ m = (λ_ Y).hom ≫ l) :
    ((e (𝟙_ D) Y).inv ≫ o ▷ Y ≫ (e X Y).hom) ≫ (e X Y).inv ≫ m =
      ((e (𝟙_ D) Y).symm ≪≫ λ_ Y).hom ≫ l := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, h]

/-- **Conjugation by an identification of tensor products transports a right unit law**, for the
whiskering and the right unitor conjugated by the identification. -/
theorem conjMul_one {X Y Z : D} (o : 𝟙_ D ⟶ Y) (m : X ⊗ Y ⟶ Z) (r : X ⟶ Z)
    (h : X ◁ o ≫ m = (ρ_ X).hom ≫ r) :
    ((e X (𝟙_ D)).inv ≫ X ◁ o ≫ (e X Y).hom) ≫ (e X Y).inv ≫ m =
      ((e X (𝟙_ D)).symm ≪≫ ρ_ X).hom ≫ r := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, h]

/-- **Conjugation by an identification of tensor products transports commutativity**, for the
braiding conjugated by the identification. -/
theorem conjMul_comm [BraidedCategory D] {X Y Z W : D} (m : X ⊗ Y ⟶ Z) (m' : Y ⊗ X ⟶ W)
    (t : Z ⟶ W) (h : (β_ X Y).hom ≫ m' = m ≫ t) :
    ((e X Y).symm ≪≫ β_ X Y ≪≫ e Y X).hom ≫ (e Y X).inv ≫ m' = (e X Y).inv ≫ m ≫ t := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, h]

end Conjugate

end Stacks.MonoidalGraded

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Osharp : Sheaf J CommRingCat.{w})
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
    Osharp.obj))

section Localized

attribute [local instance] Stacks.SheafOfModules.monoidalCategory

variable (piece : ℤ → SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf Osharp.obj hO))
  (mul : ∀ i j : ℤ, piece i ⊗ piece j ⟶ piece (i + j))
  (one : 𝟙_ (SheafOfModules.{w}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf Osharp.obj hO)) ⟶ piece 0)
  (hassoc : ∀ i j k : ℤ, mul i j ▷ piece k ≫ mul (i + j) k =
    (α_ (piece i) (piece j) (piece k)).hom ≫ piece i ◁ mul j k ≫ mul i (j + k) ≫
      eqToHom (congrArg piece (add_assoc i j k).symm))
  (hone : ∀ i : ℤ, one ▷ piece i ≫ mul 0 i =
    (λ_ (piece i)).hom ≫ eqToHom (congrArg piece (zero_add i).symm))
  (hone' : ∀ i : ℤ, piece i ◁ one ≫ mul i 0 =
    (ρ_ (piece i)).hom ≫ eqToHom (congrArg piece (add_zero i).symm))

/-- **A sheaf of graded algebras assembled from a multiplication out of the localized tensor
product.**  The multiplication `mul` and the unit `one` are morphisms for the localized monoidal
structure `Stacks.SheafOfModules.monoidalCategory`, and associativity and the unit laws are
equalities of morphisms there; the multiplication of the result is `mul` precomposed with the
identification `Stacks.SheafOfModules.tensorObjIso` of the tensor product sheaf with the localized
tensor product, read on local sections by `SheafOfModules.GradedAlgebra.ofMorphismData`. -/
noncomputable def ofLocalizedMorphismData : GradedAlgebra.{w, w} (Sheaf.toRingCat J Osharp) :=
  ofMorphismData hO piece
    (fun i j => (Stacks.SheafOfModules.tensorObjIso Osharp.obj hO (piece i) (piece j)).inv ≫
      mul i j) one
    (fun i j k => Stacks.MonoidalGraded.conjMul_assoc
      (fun X Y => Stacks.SheafOfModules.tensorObjIso Osharp.obj hO X Y) (mul i j) (mul j k)
      (mul (i + j) k) (mul i (j + k)) (eqToHom (congrArg piece (add_assoc i j k).symm))
      (hassoc i j k))
    (fun i => Stacks.MonoidalGraded.conjOne_mul
      (fun X Y => Stacks.SheafOfModules.tensorObjIso Osharp.obj hO X Y) one (mul 0 i)
      (eqToHom (congrArg piece (zero_add i).symm)) (hone i))
    (fun i => Stacks.MonoidalGraded.conjMul_one
      (fun X Y => Stacks.SheafOfModules.tensorObjIso Osharp.obj hO X Y) one (mul i 0)
      (eqToHom (congrArg piece (add_zero i).symm)) (hone' i))

/-- The homogeneous pieces of `ofLocalizedMorphismData` are the given ones. -/
theorem ofLocalizedMorphismData_piece (i : ℤ) :
    (ofLocalizedMorphismData Osharp hO piece mul one hassoc hone hone').piece i = piece i :=
  rfl

/-- The multiplication of `ofLocalizedMorphismData` on a pure tensor of local sections: the
given multiplication applied to the image of the pure tensor in the localized tensor product. -/
theorem ofLocalizedMorphismData_mul_app (i j : ℤ) (U : Cᵒᵖ) (x : (piece i).val.obj U)
    (y : (piece j).val.obj U) :
    ((ofLocalizedMorphismData Osharp hO piece mul one hassoc hone hone').mul i j).app U x y =
      ((Stacks.SheafOfModules.tensorObjIso Osharp.obj hO (piece i) (piece j)).inv ≫
        mul i j).val.app U
        ((PresheafOfModules.tensorSheafUnit (piece i) (piece j)).app U (x ⊗ₜ y)) :=
  rfl

/-- The global unit of `ofLocalizedMorphismData` is the global section the given unit morphism
corresponds to. -/
theorem ofLocalizedMorphismData_one :
    (ofLocalizedMorphismData Osharp hO piece mul one hassoc hone hone').one =
      (piece 0).unitHomEquiv one :=
  rfl

/-- **The morphism-level multiplication of `ofLocalizedMorphismData` is the given one**, read out
of the tensor product sheaf through `Stacks.SheafOfModules.tensorObjIso`. -/
theorem mulSheaf_ofLocalizedMorphismData (i j : ℤ) :
    mulSheaf (ofLocalizedMorphismData Osharp hO piece mul one hassoc hone hone') i j =
      (Stacks.SheafOfModules.tensorObjIso Osharp.obj hO (piece i) (piece j)).inv ≫ mul i j :=
  mulSheaf_ofMorphismData hO piece _ one _ _ _ i j

/-- **The morphism-level unit of `ofLocalizedMorphismData` is the given one.** -/
theorem oneHom_ofLocalizedMorphismData :
    oneHom (ofLocalizedMorphismData Osharp hO piece mul one hassoc hone hone') = one :=
  oneHom_ofMorphismData hO piece _ one _ _ _

section Commutative

attribute [local instance] Stacks.SheafOfModules.braidedCategory

/-- **A commutative multiplication out of the localized tensor product gives a commutative sheaf
of graded algebras**: if `β ≫ mul j i = mul i j` up to the identification of the degrees, for the
braiding of the localized symmetric monoidal structure, then homogeneous local sections of
`ofLocalizedMorphismData` commute.  The braiding of the strict structure is the localized one
conjugated by `Stacks.SheafOfModules.tensorObjIso` and exchanges the two factors of a local pure
tensor (`Stacks.SheafOfModules.braiding_tensorSectionsAt`), which is what turns the equation of
morphisms into the equation on local sections. -/
theorem ofLocalizedMorphismData_mul_comm
    (hcomm : ∀ i j : ℤ, (β_ (piece i) (piece j)).hom ≫ mul j i =
      mul i j ≫ eqToHom (congrArg piece (add_comm i j)))
    (i j : ℤ) (U : Cᵒᵖ) (x : (piece i).val.obj U) (y : (piece j).val.obj U) :
    HEq (((ofLocalizedMorphismData Osharp hO piece mul one hassoc hone hone').mul i j).app U x y)
      (((ofLocalizedMorphismData Osharp hO piece mul one hassoc hone hone').mul j i).app U
        y x) := by
  have key : (Stacks.SheafOfModules.Strict.braiding Osharp.obj hO (piece i) (piece j)).hom ≫
        (Stacks.SheafOfModules.tensorObjIso Osharp.obj hO (piece j) (piece i)).inv ≫ mul j i =
      (Stacks.SheafOfModules.tensorObjIso Osharp.obj hO (piece i) (piece j)).inv ≫ mul i j ≫
        eqToHom (congrArg piece (add_comm i j)) :=
    Stacks.MonoidalGraded.conjMul_comm
      (fun X Y => Stacks.SheafOfModules.tensorObjIso Osharp.obj hO X Y) (mul i j) (mul j i)
      (eqToHom (congrArg piece (add_comm i j))) (hcomm i j)
  have hb : (Stacks.SheafOfModules.Strict.braiding Osharp.obj hO (piece i) (piece j)).hom.val.app U
        (Stacks.SheafOfModules.tensorSectionsAt Osharp.obj hO U (piece i) (piece j) x y) =
      Stacks.SheafOfModules.tensorSectionsAt Osharp.obj hO U (piece j) (piece i) y x :=
    Stacks.SheafOfModules.braiding_tensorSectionsAt Osharp.obj hO U (piece i) (piece j) x y
  have hji : ((ofLocalizedMorphismData Osharp hO piece mul one hassoc hone hone').mul j i).app U
        y x =
      (eqToHom (congrArg piece (add_comm i j))).val.app U
        (((ofLocalizedMorphismData Osharp hO piece mul one hassoc hone hone').mul i j).app U x
          y) :=
    (congrArg (((Stacks.SheafOfModules.tensorObjIso Osharp.obj hO (piece j) (piece i)).inv ≫
      mul j i).val.app U) hb).symm.trans
      (congrArg (fun φ => φ.val.app U
        (Stacks.SheafOfModules.tensorSectionsAt Osharp.obj hO U (piece i) (piece j) x y)) key)
  exact (Stacks.TensorSheafWorld.heq_eqToHom_val_app piece (add_comm i j) U _).symm.trans
    (heq_of_eq hji.symm)

end Commutative

end Localized

end SheafOfModules.GradedAlgebra

end
