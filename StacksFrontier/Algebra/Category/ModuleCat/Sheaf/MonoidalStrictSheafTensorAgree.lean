module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorUnitors
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGradedAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence

/-!
# The two monoidal structures of Tag 01CA on sheaves of modules agree

`Mod(𝒪)` carries two monoidal structures whose tensor product is the tensor product sheaf of
[Stacks, Tag 01CA]: `Stacks.SheafOfModules.Strict.monoidalCategory`, obtained from the localized
structure by `CategoryTheory.Monoidal.induced`, and
`SheafOfModules.monoidalCategorySheafTensor`, obtained from it by
`CategoryTheory.MonoidalCategory.reseat`.  The first has section formulas for its structural
morphisms; the second has `Stacks.SheafOfModules.Tensor.sheafTensor` for its curried tensor
product on the nose, which is what the total tensor complex is stated at.  This file shows that
the two agree on every structural morphism, and deduces that the identity functor between them
is monoidal in both directions — which is what carries a monoidal functor from one structure to
the other.

## Main definitions

* `SheafOfModules.idCoreMonoidalStrictToSheafTensor`: the monoidal data of the identity functor
  from the strict structure to the re-seated one — the identity on tensor products and on units,
  the agreement of the structural morphisms being exactly its coherence.
* `SheafOfModules.idMonoidalStrictToSheafTensor` and
  `SheafOfModules.idMonoidalSheafTensorToStrict`: **the identity functor is monoidal in both
  directions.**  The second is the first read through
  `CategoryTheory.Equivalence.inverseMonoidal` at the identity equivalence.

## Main results

* `SheafOfModules.leftUnitor_eq_strict` and `rightUnitor_eq_strict`: **the two structures have
  the same unitors**, on an arbitrary ringed site.  This was the last structural morphism on
  which they were not known to agree.
* `SheafOfModules.associator_eq_strict`, `whiskerLeft_eq_strict`, `whiskerRight_eq_strict`,
  `tensorObj_eq_strict`, `tensorUnit_eq_strict`: they have the same associator, whiskerings,
  tensor product on objects and unit.
* `Stacks.RingedSpace.strict_rightUnitor_eq` and `strict_leftUnitor_eq`: on a ringed space, the
  unitors of the strict structure are `Stacks.RingedSpace.tensorSheafUnitRightIso` and
  `tensorSheafUnitLeftIso`.
* `Stacks.RingedSpace.rightUnitor_eq_strict` and `leftUnitor_eq_strict`,
  `whiskerLeft_eq_strict`, `whiskerRight_eq_strict`, `associator_eq_strict`,
  `tensorObj_eq_strict`, `tensorUnit_eq_strict`: the same statements read on a ringed space, at
  the `Stacks.PullbackGradedAlgebra.monoidalCategory` spelling of the strict structure.

## Implementation notes

The unitors of the re-seated structure are identified with those of the tensor product sheaf in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorUnitors`, by a computation
inside the localized structure; the unitors of the strict structure are identified with the same
two isomorphisms by their section formulas, both sides carrying a local pure tensor `x ⊗ r` to
`r • x`, in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence`.  The agreement
of the two unitors is the composite of those two identifications; no section formula is proved
here.

The **ringed-space** unitor statements are instances of the site-level ones, not a second proof
of the same fact.  `Stacks.PullbackGradedAlgebra.monoidalCategory Z` and
`Stacks.SheafOfModules.Strict.monoidalCategory Z.sheaf` are two spellings of one term
— they are equal by `rfl`, unlike the strict and re-seated structures, which agree on
`tensorObj`, `tensorUnit` and the associator but not as structures — so
`Stacks.RingedSpace.leftUnitor_eq_strict` is `congrArg Iso.hom` applied to
`SheafOfModules.leftUnitor_eq_strict`, and `strict_leftUnitor_eq` follows from it and
`leftUnitor_sheafTensor_eq`.  Each of the latter two used to be proved again from the section
formulas of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence`, which was
this file's only use of that module.

Neither structure is left to instance synthesis: both are named by `@`-application.  The reason
the `Stacks.PullbackGradedAlgebra` one cannot be a local instance in the ringed-space section is
that it is stated over `Stacks.RingedSpace.structureRingSheaf`, which instance search cannot
recover from the `Stacks.SheafOfModules.Tensor.ringSheaf` spelling the tensor product fixes.

Three identities of the ambient structure are needed to read the coherence fields of
`CategoryTheory.Functor.CoreMonoidal` when every comparison isomorphism is the identity, and
they are stated as local `have`s inside
`SheafOfModules.idCoreMonoidalStrictToSheafTensor` rather than as lemmas: each has to be read
with the *re-seated* structure throughout, whereas the fields themselves mention both, so a
`rw` or a `simp` on the field goal rewrites nothing — the goal is not type-correct at the
transparency those tactics re-check at, and `simp only` reports no error when that happens.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace

universe v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})

section Unitors

variable (A : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-- **The two monoidal structures on `Mod(𝒪)` have the same left unitor.**  Each is the left
unit constraint `𝒪 ⊗_𝒪 ℱ ≅ ℱ` of the tensor product sheaf: for the re-seated structure that is
`SheafOfModules.leftUnitor_sheafTensor_eq_iso`, for the strict one
`Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor`. -/
theorem leftUnitor_eq_strict :
    (@MonoidalCategoryStruct.leftUnitor _ _
        (monoidalCategorySheafTensor R).toMonoidalCategoryStruct A) =
      (@MonoidalCategoryStruct.leftUnitor _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)).toMonoidalCategoryStruct A) :=
  (leftUnitor_sheafTensor_eq_iso R A).trans
    (Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor R.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R) A).symm

/-- **The two monoidal structures on `Mod(𝒪)` have the same right unitor.** -/
theorem rightUnitor_eq_strict :
    (@MonoidalCategoryStruct.rightUnitor _ _
        (monoidalCategorySheafTensor R).toMonoidalCategoryStruct A) =
      (@MonoidalCategoryStruct.rightUnitor _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)).toMonoidalCategoryStruct A) :=
  (rightUnitor_sheafTensor_eq_iso R A).trans
    (Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor R.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R) A).symm

end Unitors

section Data

variable (A B D : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-- The two monoidal structures on `Mod(𝒪)` have the same tensor product on objects: both are
the tensor product sheaf of Tag 01CA. -/
theorem tensorObj_eq_strict :
    @MonoidalCategoryStruct.tensorObj _ _
        (monoidalCategorySheafTensor R).toMonoidalCategoryStruct A B =
      @MonoidalCategoryStruct.tensorObj _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)).toMonoidalCategoryStruct A B :=
  rfl

/-- The two monoidal structures on `Mod(𝒪)` have the same unit: both are
`SheafOfModules.unit`. -/
theorem tensorUnit_eq_strict :
    @MonoidalCategoryStruct.tensorUnit _ _
        (monoidalCategorySheafTensor R).toMonoidalCategoryStruct =
      @MonoidalCategoryStruct.tensorUnit _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)).toMonoidalCategoryStruct :=
  rfl

/-- The two monoidal structures on `Mod(𝒪)` have the same associator: both are the localized
associator conjugated by the same comparison isomorphism. -/
theorem associator_eq_strict :
    (@MonoidalCategoryStruct.associator _ _
        (monoidalCategorySheafTensor R).toMonoidalCategoryStruct A B D) =
      (@MonoidalCategoryStruct.associator _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)).toMonoidalCategoryStruct
        A B D) :=
  by
  apply Iso.ext
  have reseatedFormula := @CategoryTheory.MonoidalCategory.reseat_associator _ _
    (_root_.SheafOfModules.monoidalCategory R) _ _
    (_root_.SheafOfModules.sheafTensorNatIso R)
    (_root_.SheafOfModules.unitIso R) A B D
  have strictFormula := congrArg Iso.hom
    (Stacks.SheafOfModules.Strict.associator_eq R.obj
      (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R) A B D)
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc] at strictFormula
  refine reseatedFormula.trans ?_
  refine Eq.trans ?_ strictFormula.symm
  simp only [Category.assoc]
  rfl

end Data

section Whiskerings

variable {P Q : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)}

/-- The two monoidal structures on `Mod(𝒪)` have the same left whiskering. -/
theorem whiskerLeft_eq_strict
    (X : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (g : P ⟶ Q) :
    @MonoidalCategoryStruct.whiskerLeft _ _
        (monoidalCategorySheafTensor R).toMonoidalCategoryStruct X P Q g =
      @MonoidalCategoryStruct.whiskerLeft _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)).toMonoidalCategoryStruct
        X P Q g :=
  (Stacks.SheafOfModules.Strict.whiskerLeft_eq_sheafTensor R X g).symm

/-- The two monoidal structures on `Mod(𝒪)` have the same right whiskering. -/
theorem whiskerRight_eq_strict (g : P ⟶ Q)
    (X : _root_.SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    @MonoidalCategoryStruct.whiskerRight _ _
        (monoidalCategorySheafTensor R).toMonoidalCategoryStruct P Q g X =
      @MonoidalCategoryStruct.whiskerRight _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)).toMonoidalCategoryStruct
        P Q g X :=
  (Stacks.SheafOfModules.Strict.whiskerRight_eq_sheafTensor R g X).symm

end Whiskerings

section Identity

/-- The monoidal data of the identity functor from the strict structure of Tag 01CA to the
re-seated structure: the identity on tensor products and on units, which typechecks because the
two agree on the nose, together with the agreement of the four remaining structural morphisms. -/
def idCoreMonoidalStrictToSheafTensor :
    @Functor.CoreMonoidal (Stacks.SheafOfModules.Strict.Mod R) _
      (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)) (Stacks.SheafOfModules.Strict.Mod R) _
      (monoidalCategorySheafTensor R) (𝟭 (Stacks.SheafOfModules.Strict.Mod R)) :=
  letI := monoidalCategorySheafTensor R
  have hwr : ∀ (X Y W : Stacks.SheafOfModules.Strict.Mod R) (a : X ⊗ Y ⟶ W),
      𝟙 X ▷ Y ≫ 𝟙 (X ⊗ Y) ≫ a = a := fun _ _ _ _ => by
    rw [MonoidalCategory.id_whiskerRight, Category.id_comp, Category.id_comp]
  have hwl : ∀ (X Y W : Stacks.SheafOfModules.Strict.Mod R) (a : X ⊗ Y ⟶ W),
      X ◁ 𝟙 Y ≫ 𝟙 (X ⊗ Y) ≫ a = a := fun _ _ _ _ => by
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.id_comp]
  have hwl' : ∀ (X Y W : Stacks.SheafOfModules.Strict.Mod R) (b : W ⟶ X ⊗ Y),
      b ≫ X ◁ 𝟙 Y ≫ 𝟙 (X ⊗ Y) = b := fun _ _ _ _ => by
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.comp_id]
  @Functor.CoreMonoidal.mk (Stacks.SheafOfModules.Strict.Mod R) _
    (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)) (Stacks.SheafOfModules.Strict.Mod R) _
    (monoidalCategorySheafTensor R) (𝟭 (Stacks.SheafOfModules.Strict.Mod R))
    (Iso.refl _) (fun _ _ => Iso.refl _)
    (fun f X' => (Category.comp_id _).trans
      ((whiskerRight_eq_strict R f X').trans (Category.id_comp _).symm))
    (fun X' f => (Category.comp_id _).trans
      ((whiskerLeft_eq_strict R X' f).trans (Category.id_comp _).symm))
    (fun X Y Z => (hwr (X ⊗ Y) Z _ _).trans
      ((congrArg Iso.hom (associator_eq_strict R X Y Z)).symm.trans
        (hwl' X (Y ⊗ Z) _ _).symm))
    (fun X => (congrArg Iso.hom (leftUnitor_eq_strict R X)).trans
      (hwr (𝟙_ (Stacks.SheafOfModules.Strict.Mod R)) X X _).symm)
    (fun X => (congrArg Iso.hom (rightUnitor_eq_strict R X)).trans
      (hwl X (𝟙_ (Stacks.SheafOfModules.Strict.Mod R)) X _).symm)

/-- **The identity functor from the strict structure of Tag 01CA to the re-seated structure is
monoidal.** -/
@[instance_reducible]
def idMonoidalStrictToSheafTensor :
    @Functor.Monoidal _ _ (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)) _ _
      (monoidalCategorySheafTensor R) (𝟭 _) :=
  @Functor.CoreMonoidal.toMonoidal _ _
    (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)) _ _
    (monoidalCategorySheafTensor R) _ (idCoreMonoidalStrictToSheafTensor R)

/-- **The identity functor from the re-seated structure to the strict structure of Tag 01CA is
monoidal.**  This is the direction `CategoryTheory.Monoidal.induced` does not supply; it is the
inverse of the identity equivalence, whose forward direction is
`SheafOfModules.idMonoidalStrictToSheafTensor`. -/
@[instance_reducible]
def idMonoidalSheafTensorToStrict :
    @Functor.Monoidal _ _ (monoidalCategorySheafTensor R) _ _
      (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)) (𝟭 _) :=
  @CategoryTheory.Equivalence.inverseMonoidal _ _
    (Stacks.SheafOfModules.Strict.monoidalCategory R.obj
        (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf R)) _ _
    (monoidalCategorySheafTensor R) CategoryTheory.Equivalence.refl
    (idMonoidalStrictToSheafTensor R)

end Identity

end SheafOfModules

namespace Stacks.RingedSpace

variable (Z : RingedSpace.{u, u})
  (A : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))

/-- **The two monoidal structures on `Mod(𝒪_Z)` have the same right unitor.**  This is the
site-level `SheafOfModules.rightUnitor_eq_strict` read at the ringed space: the
`Stacks.PullbackGradedAlgebra.monoidalCategory` spelling of the strict structure of Tag 01CA
*is* `Stacks.SheafOfModules.Strict.monoidalCategory Z.sheaf`, so the ringed-space
statement is an instance of the site-level one and needs no section formula of its own. -/
theorem rightUnitor_eq_strict :
    (@MonoidalCategoryStruct.rightUnitor _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf).toMonoidalCategoryStruct
        A).hom =
      (@MonoidalCategoryStruct.rightUnitor _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory Z).toMonoidalCategoryStruct A).hom :=
  congrArg Iso.hom (_root_.SheafOfModules.rightUnitor_eq_strict Z.sheaf A)

/-- **The two monoidal structures on `Mod(𝒪_Z)` have the same left unitor.** -/
theorem leftUnitor_eq_strict :
    (@MonoidalCategoryStruct.leftUnitor _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf).toMonoidalCategoryStruct
        A).hom =
      (@MonoidalCategoryStruct.leftUnitor _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory Z).toMonoidalCategoryStruct A).hom :=
  congrArg Iso.hom (_root_.SheafOfModules.leftUnitor_eq_strict Z.sheaf A)

/-- **The right unitor of `Stacks.PullbackGradedAlgebra.monoidalCategory` is the right unitor of
the tensor product sheaf**: both carry a local pure tensor `x ⊗ r` to `r • x`. -/
theorem strict_rightUnitor_eq :
    (@MonoidalCategoryStruct.rightUnitor _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory Z).toMonoidalCategoryStruct A).hom =
      (tensorSheafUnitRightIso Z A).hom :=
  (rightUnitor_eq_strict Z A).symm.trans (rightUnitor_sheafTensor_eq Z A)

/-- **The left unitor of `Stacks.PullbackGradedAlgebra.monoidalCategory` is the left unitor of
the tensor product sheaf.** -/
theorem strict_leftUnitor_eq :
    (@MonoidalCategoryStruct.leftUnitor _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory Z).toMonoidalCategoryStruct A).hom =
      (tensorSheafUnitLeftIso Z A).hom :=
  (leftUnitor_eq_strict Z A).symm.trans (leftUnitor_sheafTensor_eq Z A)

variable {Z}

/-- The two monoidal structures on `Mod(𝒪_Z)` have the same tensor product on objects. -/
theorem tensorObj_eq_strict
    (A B : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) :
    @MonoidalCategoryStruct.tensorObj _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf).toMonoidalCategoryStruct A B =
      @MonoidalCategoryStruct.tensorObj _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory Z).toMonoidalCategoryStruct A B :=
  rfl

/-- The two monoidal structures on `Mod(𝒪_Z)` have the same unit. -/
theorem tensorUnit_eq_strict :
    @MonoidalCategoryStruct.tensorUnit _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf).toMonoidalCategoryStruct =
      @MonoidalCategoryStruct.tensorUnit _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory Z).toMonoidalCategoryStruct :=
  rfl

/-- The two monoidal structures on `Mod(𝒪_Z)` have the same associator. -/
theorem associator_eq_strict
    (A B D : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) :
    (@MonoidalCategoryStruct.associator _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf).toMonoidalCategoryStruct A B
        D).hom =
      (@MonoidalCategoryStruct.associator _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory Z).toMonoidalCategoryStruct A B D).hom :=
  congrArg Iso.hom (_root_.SheafOfModules.associator_eq_strict Z.sheaf A B D)

/-- The two monoidal structures on `Mod(𝒪_Z)` have the same left whiskering. -/
theorem whiskerLeft_eq_strict
    (A : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))
    {B B' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)}
    (w : B ⟶ B') :
    @MonoidalCategoryStruct.whiskerLeft _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf).toMonoidalCategoryStruct A B
        B' w =
      @MonoidalCategoryStruct.whiskerLeft _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory Z).toMonoidalCategoryStruct A B B' w :=
  (Stacks.SheafOfModules.Strict.whiskerLeft_eq_sheafTensor Z.sheaf A w).symm

/-- The two monoidal structures on `Mod(𝒪_Z)` have the same right whiskering. -/
theorem whiskerRight_eq_strict
    {A A' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)}
    (v : A ⟶ A')
    (B : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) :
    @MonoidalCategoryStruct.whiskerRight _ _
        (_root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf).toMonoidalCategoryStruct A A'
        v B =
      @MonoidalCategoryStruct.whiskerRight _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory Z).toMonoidalCategoryStruct A A' v B :=
  (Stacks.SheafOfModules.Strict.whiskerRight_eq_sheafTensor Z.sheaf v B).symm

end Stacks.RingedSpace

end
