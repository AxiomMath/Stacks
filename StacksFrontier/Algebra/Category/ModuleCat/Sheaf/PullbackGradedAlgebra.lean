module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackMonoidalSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of a sheaf of graded algebras is a sheaf of graded algebras

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `A` be a sheaf of graded
`𝒪_Y`-algebras. This file equips the degreewise pullback `n ↦ f^*(A_n)` with a
`SheafOfModules.GradedAlgebra` structure.

The multiplication is forced: `f^*` is a monoidal functor, so its tensorator conjugates the
multiplication of `A` into `f^*(A_i) ⊗ f^*(A_j) ⟶ f^*(A_{i+j})`. The work is in the two levels
at which the algebra axioms live. `SheafOfModules.GradedAlgebra` states associativity and the
unit laws as `HEq`s between values of a bilinear map at *arbitrary local sections*, whereas a
monoidal functor transports **equalities of morphisms**. The file therefore does three things.

* It transports a morphism-level multiplication along an arbitrary lax monoidal functor
  (`Stacks.MonoidalGraded`). This is where monoidality is used, and it is used only through
  `CategoryTheory.Functor.LaxMonoidal.associativity`, `left_unitality` and `right_unitality`.
* It supplies the morphism-level **unit laws** for the multiplication
  `SheafOfModules.GradedAlgebra.mulSheaf` of a sheaf of graded algebras, which
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge` left out: that file
  turns the `HEq` field `mul_assoc` into the morphism equality `mulSheaf_assoc`, and this one
  does the same for `one_mul` and `mul_one`.
* It descends morphism-level data back to a `GradedAlgebra`
  (`SheafOfModules.GradedAlgebra.ofMorphismData`), which is the converse of the previous two
  items and needs **no local-generation hypothesis**: the bilinear map read off a morphism
  `φ` out of the tensor product sheaf is `x, y ↦ φ(η(x ⊗ₜ y))` for the sheafification unit
  `η`, so evaluating a morphism identity at `η(η(x ⊗ₜ y) ⊗ₜ z)` yields the `HEq` field at
  arbitrary local sections directly.

The unit laws are *not* the monoidal unitors, and this is the one place where the shape of the
problem is easy to misjudge. `SheafOfModules.GradedAlgebra.one` is a global section of `A_0`,
not the unit object of the monoidal structure; the morphism it corresponds to is
`SheafOfModules.GradedAlgebra.oneHom`, and the morphism-level law
`mulSheaf_one_mul` relates `oneHom ▷ A_i ≫ mulSheaf A 0 i` to the left unitor, so the section
formula for the left unitor is an *ingredient* of it rather than the statement itself.

## Main definitions

* `Stacks.MonoidalGraded.mapMul` and `Stacks.MonoidalGraded.mapOne`: the image of a
  multiplication `X ⊗ Y ⟶ Z` and of a unit `𝟙_ ⟶ X` under a lax monoidal functor, conjugated
  by the tensorator and by the unit morphism.
* `SheafOfModules.GradedAlgebra.oneHom`: the global unit of a sheaf of graded algebras, read as
  a morphism `𝟙_ ⟶ A_0` of sheaves of modules.
* `SheafOfModules.GradedAlgebra.ofMorphismData`: a sheaf of graded algebras assembled from a
  degreewise family of sheaves of modules together with a multiplication and a unit given as
  **morphisms**, satisfying associativity and the two unit laws as equalities of morphisms.
* `Stacks.PullbackGradedAlgebra.pullbackFunctorLocalized` and
  `pullbackFunctorLocalizedMonoidal`: `Stacks.PullbackMonoidalSheaf.pullbackMonoidal` read at
  the type synonym `CategoryTheory.Monoidal.LocalizedMonoidal`.
* `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`: **the pullback of sheaves of modules
  along a morphism of ringed spaces is a monoidal functor for the monoidal structure of Tag
  01CA**, whose tensor product is the tensor product sheaf on the nose.
* `Stacks.PullbackGradedAlgebra.pullbackMul` and `pullbackOne`: the conjugated multiplication
  `f^*(A_i) ⊗ f^*(A_j) ⟶ f^*(A_{i+j})` and the conjugated unit `𝟙_ ⟶ f^*(A_0)`.
* `Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra`: **the sheaf of graded algebras `f^*A`.**

## Main results

* `Stacks.MonoidalGraded.mapMul_assoc`, `mapOne_mul` and `mapMul_one`: a lax monoidal functor
  transports morphism-level associativity and the morphism-level unit laws. Stated with the
  degree bookkeeping absorbed into two unconstrained morphisms `l` and `r`, so that the
  `eqToHom` of a graded algebra never enters the general statement.
* `SheafOfModules.GradedAlgebra.mulSheaf_one_mul` and `mulSheaf_mul_one`: **the morphism-level
  unit laws of a sheaf of graded algebras.**
* `SheafOfModules.GradedAlgebra.ofMorphismData_mul_app`,
  `ofMorphismData_piece` and `ofMorphismData_one`: the data of `ofMorphismData`, so that a
  consumer never has to unfold it.
* `Stacks.PullbackGradedAlgebra.pullbackMul_assoc`, `pullbackOne_mul` and `pullbackMul_one`:
  **the transported multiplication on `f^*A` is associative and unital as an equality of
  morphisms.**
* `Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra_piece` and
  `pullbackGradedAlgebra_mul_app`: the pieces and the multiplication of `f^*A`.

## Implementation notes

**What is forced.** No mathematical choice is made. The monoidal structures are the existing
ones (`Stacks.SheafOfModules.Strict.monoidalCategory` at the sheaf level, named through
`Stacks.TensorSheafWorld.monoidalCategory`), the monoidal functor is
`Stacks.PullbackMonoidalSheaf.pullbackMonoidal`, and the multiplication of `f^*A` is the only
one the tensorator supplies. The one presentational choice is that
`Stacks.MonoidalGraded.mapMul_assoc` takes the two "outer" multiplications as unconstrained
morphisms `l : X₁₂ ⊗ X₃ ⟶ W` and `r : X₁ ⊗ X₂₃ ⟶ W` rather than as a graded family: the
transport is then a statement about a monoidal functor and nothing else, and the
degree-addition `eqToHom`s are supplied by the caller inside `r`.

**The strict and the localized monoidal structures, and the bridge between them.**
`Stacks.PullbackMonoidalSheaf.pullbackMonoidal` is monoidal for
`Stacks.SheafOfModules.monoidalCategory`, the localization of the objectwise structure on
presheaves of modules, whose tensor product is only *isomorphic* to the tensor product sheaf.
Every section formula available here — the associator, the unitors and the two whiskerings of
`...TensorSheafWorldBridge` — is stated for `Stacks.SheafOfModules.Strict.monoidalCategory`,
whose tensor product *is* `Stacks.SheafOfModules.Tensor.sheafTensor`. So the
  transport cannot consume
`pullbackMonoidal` directly. The bridge is
`Stacks.SheafOfModules.SliceRestriction.toLocalizedMonoidalMonoidal` and
`fromLocalizedMonoidalMonoidal`: the identity functor between the two spellings is monoidal in
both directions, the second direction by `CategoryTheory.Equivalence.inverseMonoidal`. Those
two declarations depend only on the ring presheaf and its sheaf condition, not on the slice
object, so they are reused verbatim here and nothing of that argument is repeated.

The implementation notes of `...PullbackMonoidalSheaf` record the inverse direction as "not
here" and the sectionwise associator formula as unavailable; both have since been supplied —
the first in `...SliceRestrictionMonoidal`, the second in `...TensorSheafWorldBridge` — and
this file is what those two unlock.

**Two spellings of one monoidal structure, both needed.**
`Stacks.TensorSheafWorld.monoidalCategory Osharp` and
`Stacks.SheafOfModules.Strict.monoidalCategory 𝒪 h𝒪` are equal by `rfl` when
`Osharp.obj = 𝒪`, but they are different discrimination-tree keys, so an instance named at one
is invisible at a goal written in the other. `pullbackStrictMonoidal` is therefore ascribed at
the `Stacks.TensorSheafWorld.monoidalCategory` spelling — the one the section formulas and
`SheafOfModules.GradedAlgebra.mulSheaf` use — while its body activates the
`Stacks.SheafOfModules.Strict.monoidalCategory` spelling, which the bridge declarations are
stated at. The two are crossed by the defeq check of `:=`, exactly as in
`Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidal`; no limit is raised anywhere.

**No `rw` or `simp` crosses the tensor-product boundary.** `(F ⊗ G).val.obj U` and
`(((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G).val.obj U` are definitionally
equal and
not
syntactically so, and a rewrite in a goal mixing them is rejected as not type-correct at
`implicit` transparency. Every step of `ofMorphismData` and of the section-level lemmas is
therefore `Eq.trans`, `congrArg` or `exact`, and the extensionality principles are applied with
their sheaf arguments passed **explicitly**, since leaving them as metavariables makes the
`isDefEq` check cross that boundary.

**Universes.** The general transport is at two arbitrary monoidal categories. The
morphism-level unit laws and `ofMorphismData` keep the site `C : Type u` with `Category.{v} C`
arbitrary and put the ring sheaf and the modules in a single universe `w`; that is inherited
from Mathlib's monoidal structure on presheaves of modules, which exists only in that form, and
is the same constraint `Stacks.TensorSheafWorld.mulSheaf_assoc` carries. The ringed-space
section is at a single universe `u`, forced by
`RingedSpaceModuleAdjunction.modulePullback`. Nothing is narrowed relative to the imports.

**No new `@[stacks]` attribute.** Tag 01CI asserts `f^*⋀(F) = ⋀(f^*F)`, and nothing here
asserts that: a graded algebra structure on `f^*A` is one of the three inputs that statement
needs, not one of its conclusions. The two Tag 01CI declarations of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso` cover the tensor-algebra
case by a different route. Tags 0FQW and 01CA are already carried by
`SheafOfModules.GradedAlgebra` and by the monoidal structure this file consumes, so tagging
these statements would register one result twice.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI) — pullback and the
  tensor, exterior and symmetric algebras of a sheaf of modules.
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW) — sheaves of graded
  algebras.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes
  with the tensor product.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization AlgebraicGeometry TopologicalSpace
open CategoryTheory.Sheaf PresheafOfModules
open RingedSpaceModuleAdjunction Stacks.RingedSpace

open scoped TensorProduct

universe v₁ v₂ u₁ u₂ v u w

namespace Stacks.MonoidalGraded

/-! ### Transport of a multiplication along a lax monoidal functor -/

section Transport

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]

/-- The image of a multiplication `X ⊗ Y ⟶ Z` under a lax monoidal functor: the tensorator
followed by the functor applied to the multiplication. -/
noncomputable def mapMul {X Y Z : C} (m : X ⊗ Y ⟶ Z) : F.obj X ⊗ F.obj Y ⟶ F.obj Z :=
  Functor.LaxMonoidal.μ F X Y ≫ F.map m

/-- The image of a unit `𝟙_ ⟶ X` under a lax monoidal functor: the unit morphism of the functor
followed by the functor applied to the unit. -/
noncomputable def mapOne {X : C} (o : 𝟙_ C ⟶ X) : 𝟙_ D ⟶ F.obj X :=
  Functor.LaxMonoidal.ε F ≫ F.map o

/-- Transport commutes with postcomposition. This is what lets a caller put the
degree-addition `eqToHom` of a graded algebra at the end of its multiplication. -/
theorem mapMul_comp {X Y Z W : C} (m : X ⊗ Y ⟶ Z) (g : Z ⟶ W) :
    mapMul F (m ≫ g) = mapMul F m ≫ F.map g := by
  simp only [mapMul, Functor.map_comp, Category.assoc]

/-- **A lax monoidal functor transports morphism-level associativity.** The degree bookkeeping
of a graded algebra is absorbed into the two outer multiplications `l` and `r`, so no `eqToHom`
appears here. -/
theorem mapMul_assoc {X₁ X₂ X₃ X₁₂ X₂₃ W : C} (m₁₂ : X₁ ⊗ X₂ ⟶ X₁₂) (m₂₃ : X₂ ⊗ X₃ ⟶ X₂₃)
    (l : X₁₂ ⊗ X₃ ⟶ W) (r : X₁ ⊗ X₂₃ ⟶ W)
    (h : m₁₂ ▷ X₃ ≫ l = (α_ X₁ X₂ X₃).hom ≫ X₁ ◁ m₂₃ ≫ r) :
    mapMul F m₁₂ ▷ F.obj X₃ ≫ mapMul F l =
      (α_ (F.obj X₁) (F.obj X₂) (F.obj X₃)).hom ≫ F.obj X₁ ◁ mapMul F m₂₃ ≫ mapMul F r := by
  have h' : F.map (m₁₂ ▷ X₃) ≫ F.map l =
      F.map (α_ X₁ X₂ X₃).hom ≫ F.map (X₁ ◁ m₂₃) ≫ F.map r := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Category.assoc, h,
      Category.assoc]
  simp only [mapMul, comp_whiskerRight, Category.assoc,
    Functor.LaxMonoidal.μ_natural_left_assoc, h', Functor.LaxMonoidal.associativity_assoc,
    MonoidalCategory.whiskerLeft_comp, Functor.LaxMonoidal.μ_natural_right_assoc]

/-- **A lax monoidal functor transports a morphism-level left unit law.** -/
theorem mapOne_mul {X Y Z : C} (o : 𝟙_ C ⟶ X) (m : X ⊗ Y ⟶ Z) (l : Y ⟶ Z)
    (h : o ▷ Y ≫ m = (λ_ Y).hom ≫ l) :
    mapOne F o ▷ F.obj Y ≫ mapMul F m = (λ_ (F.obj Y)).hom ≫ F.map l := by
  have h' : F.map (o ▷ Y) ≫ F.map m = F.map (λ_ Y).hom ≫ F.map l := by
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  simp only [mapMul, mapOne, comp_whiskerRight, Category.assoc,
    Functor.LaxMonoidal.μ_natural_left_assoc, h', Functor.LaxMonoidal.left_unitality]

/-- **A lax monoidal functor transports a morphism-level right unit law.** -/
theorem mapMul_one {X Y Z : C} (o : 𝟙_ C ⟶ Y) (m : X ⊗ Y ⟶ Z) (r : X ⟶ Z)
    (h : X ◁ o ≫ m = (ρ_ X).hom ≫ r) :
    F.obj X ◁ mapOne F o ≫ mapMul F m = (ρ_ (F.obj X)).hom ≫ F.map r := by
  have h' : F.map (X ◁ o) ≫ F.map m = F.map (ρ_ X).hom ≫ F.map r := by
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  simp only [mapMul, mapOne, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc, h', Functor.LaxMonoidal.right_unitality]

end Transport

end Stacks.MonoidalGraded

namespace SheafOfModules.GradedAlgebra

/-! ### The global unit of a sheaf of graded algebras as a morphism -/

section One

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (A : GradedAlgebra.{w, w} (toRingCat J Osharp))

/-- **The global unit of a sheaf of graded algebras, read as a morphism `𝟙_ ⟶ A_0`.** The unit
object of the monoidal structure of Tag 01CA is the structure sheaf viewed as a module over
itself, and a morphism out of it is the same thing as a global section of the target. -/
noncomputable def oneHom : 𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)) ⟶ A.piece 0 :=
  (A.piece 0).unitHomEquiv.symm A.one

/-- `oneHom` on local sections: a local section `r` of the structure sheaf is carried to
`r` times the global unit. -/
theorem oneHom_val_app (U : Cᵒᵖ) (r : (toRingCat J Osharp).obj.obj U) :
    (oneHom A).val.app U r = r • A.one.eval U := rfl

/-- The global section of `A_0` that `oneHom` corresponds to is the unit of `A`. -/
theorem unitHomEquiv_oneHom : (A.piece 0).unitHomEquiv (oneHom A) = A.one :=
  (A.piece 0).unitHomEquiv.apply_symm_apply A.one

section Sections

variable (i : ℤ) (U : Cᵒᵖ) (r : (toRingCat J Osharp).obj.obj U) (x : (A.piece i).val.obj U)

/-- Multiplying a local section on the left by the image of a scalar under `oneHom` is
multiplication by that scalar, transported along `0 + i = i`. -/
theorem mul_oneHom_left :
    (A.mul 0 i).app U ((oneHom A).val.app U r) x =
      (eqToHom (congrArg A.piece (zero_add i).symm)).val.app U (r • x) :=
  (congrArg (fun t ↦ (A.mul 0 i).app U t x) (oneHom_val_app A U r)).trans
    (((A.mul 0 i).map_smul_left U r (A.one.eval U) x).trans
      ((congrArg (r • ·) (eq_of_heq ((A.one_mul i U x).trans
        (Stacks.TensorSheafWorld.heq_eqToHom_val_app A.piece
          (zero_add i).symm U x).symm))).trans
        (((eqToHom (congrArg A.piece (zero_add i).symm)).val.app U).hom.map_smul r x).symm))

/-- Multiplying a local section on the right by the image of a scalar under `oneHom` is
multiplication by that scalar, transported along `i + 0 = i`. -/
theorem mul_oneHom_right :
    (A.mul i 0).app U x ((oneHom A).val.app U r) =
      (eqToHom (congrArg A.piece (add_zero i).symm)).val.app U (r • x) :=
  (congrArg ((A.mul i 0).app U x) (oneHom_val_app A U r)).trans
    (((A.mul i 0).map_smul_right U r x (A.one.eval U)).trans
      ((congrArg (r • ·) (eq_of_heq ((A.mul_one i U x).trans
        (Stacks.TensorSheafWorld.heq_eqToHom_val_app A.piece
          (add_zero i).symm U x).symm))).trans
        (((eqToHom (congrArg A.piece (add_zero i).symm)).val.app U).hom.map_smul r x).symm))

end Sections

variable (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
  Osharp.obj)) (i : ℤ)

include hO

/-- **The global unit of a sheaf of graded algebras is a left identity, as an equality of
morphisms out of `𝟙_ ⊗ A_i`.** This is the left unit law of `SheafOfModules.GradedAlgebra`,
which the structure states as an `HEq` at arbitrary local sections, in the form a monoidal
functor can transport.

It is **not** the left unitor of the monoidal structure of Tag 01CA: the left unitor is the
statement that a scalar acts on a local section, and the content here is that the global unit
of `A` acts trivially. The section formula for the left unitor is one of the four inputs. -/
theorem mulSheaf_one_mul :
    oneHom A ▷ A.piece i ≫ mulSheaf A 0 i =
      (λ_ (A.piece i)).hom ≫ eqToHom (congrArg A.piece (zero_add i).symm) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp)
    (F := 𝟙_ (SheafOfModules.{w} (toRingCat J Osharp))) (G := A.piece i)
    (Q := A.piece (0 + i)) fun V s y ↦ ?_
  exact (congrArg ((mulSheaf A 0 i).val.app V)
      (Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit Osharp hO V
        (oneHom A) (A.piece i) s y)).trans
    ((mulSheaf_unit A 0 i V ((oneHom A).val.app V s) y).trans
      ((mul_oneHom_left A i V s y).trans
        (congrArg ((eqToHom (congrArg A.piece (zero_add i).symm)).val.app V)
          (Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit Osharp hO
            (A.piece i) V s y).symm)))

/-- **The global unit of a sheaf of graded algebras is a right identity, as an equality of
morphisms out of `A_i ⊗ 𝟙_`.** The right-handed counterpart of `mulSheaf_one_mul`. -/
theorem mulSheaf_mul_one :
    A.piece i ◁ oneHom A ≫ mulSheaf A i 0 =
      (ρ_ (A.piece i)).hom ≫ eqToHom (congrArg A.piece (add_zero i).symm) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := Osharp)
    (F := A.piece i) (G := 𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)))
    (Q := A.piece (i + 0)) fun V y s ↦ ?_
  exact (congrArg ((mulSheaf A i 0).val.app V)
      (Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit Osharp hO V
        (A.piece i) (oneHom A) y s)).trans
    ((mulSheaf_unit A i 0 V y ((oneHom A).val.app V s)).trans
      ((mul_oneHom_right A i V s y).trans
        (congrArg ((eqToHom (congrArg A.piece (add_zero i).symm)).val.app V)
          (Stacks.TensorSheafWorld.rightUnitor_hom_val_app_tensorSheafUnit Osharp hO
            (A.piece i) V y s).symm)))

end One

/-! ### A sheaf of graded algebras from morphism-level data -/

section OfMorphismData

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
  Osharp.obj))
  (piece : ℤ → SheafOfModules.{w} (toRingCat J Osharp))
  (mul : ∀ i j : ℤ, piece i ⊗ piece j ⟶ piece (i + j))
  (one : 𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)) ⟶ piece 0)

/-- The bilinear map on local sections underlying a morphism out of the tensor product sheaf:
`x, y ↦ φ (η (x ⊗ₜ y))`, for `η` the sheafification unit. -/
noncomputable def bilinearOfHom (i j : ℤ) :
    SheafOfModules.BilinearMap (piece i) (piece j) (piece (i + j)) :=
  PresheafOfModules.toBilinear
    (PresheafOfModules.tensorSheafUnit (piece i) (piece j) ≫ (mul i j).val)

/-- `bilinearOfHom` on a pure tensor of local sections. -/
theorem bilinearOfHom_app (i j : ℤ) (U : Cᵒᵖ) (x : (piece i).val.obj U)
    (y : (piece j).val.obj U) :
    (bilinearOfHom piece mul i j).app U x y =
      (mul i j).val.app U
        ((PresheafOfModules.tensorSheafUnit (piece i) (piece j)).app U (x ⊗ₜ y)) :=
  rfl

include hO

/-- **A sheaf of graded algebras assembled from morphism-level data.** The multiplication and
the unit are given as morphisms of sheaves of modules and the three algebra axioms as
equalities of morphisms; the `HEq`s at arbitrary local sections that
`SheafOfModules.GradedAlgebra` demands are read off by evaluating those equalities on the
sheafification-unit images of pure tensors.

No hypothesis that such sections generate is needed, and that is the point: the bilinear map a
morphism out of the tensor product sheaf induces is *defined* by its values there
(`bilinearOfHom_app`), so the evaluation already quantifies over arbitrary local sections. -/
noncomputable def ofMorphismData
    (hassoc : ∀ i j k : ℤ, mul i j ▷ piece k ≫ mul (i + j) k =
      (α_ (piece i) (piece j) (piece k)).hom ≫ piece i ◁ mul j k ≫ mul i (j + k) ≫
        eqToHom (congrArg piece (add_assoc i j k).symm))
    (hone : ∀ i : ℤ, one ▷ piece i ≫ mul 0 i =
      (λ_ (piece i)).hom ≫ eqToHom (congrArg piece (zero_add i).symm))
    (hone' : ∀ i : ℤ, piece i ◁ one ≫ mul i 0 =
      (ρ_ (piece i)).hom ≫ eqToHom (congrArg piece (add_zero i).symm)) :
    GradedAlgebra.{w, w} (toRingCat J Osharp) where
  piece := piece
  mul := bilinearOfHom piece mul
  one := (piece 0).unitHomEquiv one
  mul_assoc i j k U x y z := by
    have hL : (mul i j ▷ piece k ≫ mul (i + j) k).val.app U
          ((PresheafOfModules.tensorSheafUnit (piece i ⊗ piece j) (piece k)).app U
            ((PresheafOfModules.tensorSheafUnit (piece i) (piece j)).app U (x ⊗ₜ y) ⊗ₜ z)) =
        (bilinearOfHom piece mul (i + j) k).app U
          ((bilinearOfHom piece mul i j).app U x y) z :=
      congrArg ((mul (i + j) k).val.app U)
        (Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit Osharp hO U
          (mul i j) (piece k)
          ((PresheafOfModules.tensorSheafUnit (piece i) (piece j)).app U (x ⊗ₜ y)) z)
    have hR : ((α_ (piece i) (piece j) (piece k)).hom ≫ piece i ◁ mul j k ≫
          mul i (j + k) ≫ eqToHom (congrArg piece (add_assoc i j k).symm)).val.app U
          ((PresheafOfModules.tensorSheafUnit (piece i ⊗ piece j) (piece k)).app U
            ((PresheafOfModules.tensorSheafUnit (piece i) (piece j)).app U (x ⊗ₜ y) ⊗ₜ z)) =
        (eqToHom (congrArg piece (add_assoc i j k).symm)).val.app U
          ((bilinearOfHom piece mul i (j + k)).app U x
            ((bilinearOfHom piece mul j k).app U y z)) :=
      congrArg ((eqToHom (congrArg piece (add_assoc i j k).symm)).val.app U)
        (congrArg ((mul i (j + k)).val.app U)
          ((congrArg ((piece i ◁ mul j k).val.app U)
              (Stacks.TensorSheafWorld.associator_hom_val_app_tensorSheafUnit Osharp hO
                (piece i) (piece j) (piece k) U x y z)).trans
            (Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit Osharp hO U
              (piece i) (mul j k) x
              ((PresheafOfModules.tensorSheafUnit (piece j) (piece k)).app U (y ⊗ₜ z)))))
    refine HEq.trans (heq_of_eq (hL.symm.trans ((congrArg
      (fun ψ : (piece i ⊗ piece j) ⊗ piece k ⟶ piece (i + j + k) ↦ ψ.val.app U
        ((PresheafOfModules.tensorSheafUnit (piece i ⊗ piece j) (piece k)).app U
          ((PresheafOfModules.tensorSheafUnit (piece i) (piece j)).app U (x ⊗ₜ y) ⊗ₜ z)))
      (hassoc i j k)).trans hR))) ?_
    exact Stacks.TensorSheafWorld.heq_eqToHom_val_app piece (add_assoc i j k).symm U _
  one_mul i U x := by
    have hL : (one ▷ piece i ≫ mul 0 i).val.app U
          ((PresheafOfModules.tensorSheafUnit
            (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp))) (piece i)).app U
              ((1 : (toRingCat J Osharp).obj.obj U) ⊗ₜ x)) =
        (bilinearOfHom piece mul 0 i).app U
          (((piece 0).unitHomEquiv one).eval U) x :=
      congrArg ((mul 0 i).val.app U)
        (Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit Osharp hO U
          one (piece i) (1 : (toRingCat J Osharp).obj.obj U) x)
    have hR : ((λ_ (piece i)).hom ≫ eqToHom (congrArg piece (zero_add i).symm)).val.app U
          ((PresheafOfModules.tensorSheafUnit
            (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp))) (piece i)).app U
              ((1 : (toRingCat J Osharp).obj.obj U) ⊗ₜ x)) =
        (eqToHom (congrArg piece (zero_add i).symm)).val.app U x :=
      congrArg ((eqToHom (congrArg piece (zero_add i).symm)).val.app U)
        ((Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit Osharp hO
          (piece i) U (1 : (toRingCat J Osharp).obj.obj U) x).trans (one_smul _ x))
    refine HEq.trans (heq_of_eq (hL.symm.trans ((congrArg
      (fun ψ : 𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)) ⊗ piece i ⟶ piece (0 + i) ↦
        ψ.val.app U ((PresheafOfModules.tensorSheafUnit
          (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp))) (piece i)).app U
            ((1 : (toRingCat J Osharp).obj.obj U) ⊗ₜ x)))
      (hone i)).trans hR))) ?_
    exact Stacks.TensorSheafWorld.heq_eqToHom_val_app piece (zero_add i).symm U x
  mul_one i U x := by
    have hL : (piece i ◁ one ≫ mul i 0).val.app U
          ((PresheafOfModules.tensorSheafUnit (piece i)
            (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)))).app U
              (x ⊗ₜ (1 : (toRingCat J Osharp).obj.obj U))) =
        (bilinearOfHom piece mul i 0).app U x
          (((piece 0).unitHomEquiv one).eval U) :=
      congrArg ((mul i 0).val.app U)
        (Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit Osharp hO U
          (piece i) one x (1 : (toRingCat J Osharp).obj.obj U))
    have hR : ((ρ_ (piece i)).hom ≫ eqToHom (congrArg piece (add_zero i).symm)).val.app U
          ((PresheafOfModules.tensorSheafUnit (piece i)
            (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)))).app U
              (x ⊗ₜ (1 : (toRingCat J Osharp).obj.obj U))) =
        (eqToHom (congrArg piece (add_zero i).symm)).val.app U x :=
      congrArg ((eqToHom (congrArg piece (add_zero i).symm)).val.app U)
        ((Stacks.TensorSheafWorld.rightUnitor_hom_val_app_tensorSheafUnit Osharp hO
          (piece i) U x (1 : (toRingCat J Osharp).obj.obj U)).trans (one_smul _ x))
    refine HEq.trans (heq_of_eq (hL.symm.trans ((congrArg
      (fun ψ : piece i ⊗ 𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)) ⟶ piece (i + 0) ↦
        ψ.val.app U ((PresheafOfModules.tensorSheafUnit (piece i)
          (𝟙_ (SheafOfModules.{w} (toRingCat J Osharp)))).app U
            (x ⊗ₜ (1 : (toRingCat J Osharp).obj.obj U))))
      (hone' i)).trans hR))) ?_
    exact Stacks.TensorSheafWorld.heq_eqToHom_val_app piece (add_zero i).symm U x

variable (hassoc : ∀ i j k : ℤ, mul i j ▷ piece k ≫ mul (i + j) k =
    (α_ (piece i) (piece j) (piece k)).hom ≫ piece i ◁ mul j k ≫ mul i (j + k) ≫
      eqToHom (congrArg piece (add_assoc i j k).symm))
  (hone : ∀ i : ℤ, one ▷ piece i ≫ mul 0 i =
    (λ_ (piece i)).hom ≫ eqToHom (congrArg piece (zero_add i).symm))
  (hone' : ∀ i : ℤ, piece i ◁ one ≫ mul i 0 =
    (ρ_ (piece i)).hom ≫ eqToHom (congrArg piece (add_zero i).symm))

/-- The homogeneous pieces of `ofMorphismData` are the given ones. -/
theorem ofMorphismData_piece (i : ℤ) :
    (ofMorphismData hO piece mul one hassoc hone hone').piece i = piece i :=
  rfl

/-- The multiplication of `ofMorphismData` on a pure tensor of local sections. -/
theorem ofMorphismData_mul_app (i j : ℤ) (U : Cᵒᵖ) (x : (piece i).val.obj U)
    (y : (piece j).val.obj U) :
    ((ofMorphismData hO piece mul one hassoc hone hone').mul i j).app U x y =
      (mul i j).val.app U
        ((PresheafOfModules.tensorSheafUnit (piece i) (piece j)).app U (x ⊗ₜ y)) :=
  rfl

/-- The global unit of `ofMorphismData` is the global section the given morphism corresponds
to. -/
theorem ofMorphismData_one :
    (ofMorphismData hO piece mul one hassoc hone hone').one = (piece 0).unitHomEquiv one :=
  rfl

end OfMorphismData

end SheafOfModules.GradedAlgebra

namespace Stacks.PullbackGradedAlgebra

/-! ### The pullback of sheaves of modules is monoidal for the strict structure of Tag 01CA -/

open Stacks.PullbackMonoidalSheaf Stacks.SheafOfModules.SliceRestriction
open SheafOfModules.GradedAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The two spellings of the structure ring sheaf of a ringed space used by the monoidal
machinery agree on the nose: the one indexed by a presheaf of commutative rings together with a
sheaf condition, and `CategoryTheory.Sheaf.toRingCat` of the structure sheaf. -/
theorem structureSheaf_eq (Z : RingedSpace.{u, u}) :
    Stacks.SheafOfModules.TensorSheafification.structureSheaf Z.presheaf
      (structureSheafRing Z).property =
      toRingCat (Opens.grothendieckTopology Z.carrier) Z.sheaf :=
  rfl

/-- The two names for the strict monoidal structure of Tag 01CA on sheaves of modules on a
ringed space denote one and the same structure. `Stacks.TensorSheafWorld.monoidalCategory` is
the spelling the section formulas and `SheafOfModules.GradedAlgebra.mulSheaf` use, and
`Stacks.SheafOfModules.Strict.monoidalCategory` is the spelling the localization bridge is
stated at. -/
theorem monoidalCategory_eq (Z : RingedSpace.{u, u}) :
    Stacks.TensorSheafWorld.monoidalCategory
        (J := Opens.grothendieckTopology Z.carrier) Z.sheaf =
      Stacks.SheafOfModules.Strict.monoidalCategory Z.presheaf
        (structureSheafRing Z).property :=
  rfl

/-- The monoidal structure of Tag 01CA on sheaves of modules on a ringed space, named once at
the `Stacks.RingedSpace.structureRingSheaf` spelling of the ring sheaf, which is the spelling
the ringed-space pullback uses. Every argument is determined by the type, so unlike
`Stacks.TensorSheafWorld.monoidalCategory` applied by hand this is found by instance search. -/
@[instance_reducible]
noncomputable def monoidalCategory (Z : RingedSpace.{u, u}) :
    MonoidalCategory (SheafOfModules.{u} (structureRingSheaf Z)) :=
  Stacks.TensorSheafWorld.monoidalCategory
    (J := Opens.grothendieckTopology Z.carrier) Z.sheaf

attribute [local instance] monoidalCategory

/-- `pullbackFunctor`, retyped between the two type synonyms carrying the localized monoidal
structures, which is where the localization bridge expects it. -/
noncomputable abbrev pullbackFunctorLocalized :
    localizedSrc Y.presheaf (structureSheafRing Y).property ⥤
      localizedSrc X.presheaf (structureSheafRing X).property :=
  pullbackFunctor f

/-- `Stacks.PullbackMonoidalSheaf.pullbackMonoidal`, read at the type-synonym spelling. -/
@[instance_reducible]
noncomputable def pullbackFunctorLocalizedMonoidal :
    (pullbackFunctorLocalized f).Monoidal :=
  pullbackMonoidal f

/-- **The pullback of sheaves of modules along a morphism of ringed spaces is a monoidal
functor for the monoidal structure of Tag 01CA**, whose tensor product is the tensor product
sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` on the nose.

`Stacks.PullbackMonoidalSheaf.pullbackMonoidal` is monoidal for the *localized* structure,
whose tensor product is only isomorphic to the tensor product sheaf. The identity functor
between the two spellings is monoidal in both directions —
`Stacks.SheafOfModules.SliceRestriction.toLocalizedMonoidalMonoidal` and
`fromLocalizedMonoidalMonoidal` — so this is a composite of three monoidal functors. -/
@[instance_reducible,
  ega "0 4.3.4" "partial",
  ega "IV 10.2.8" "more general",
  sga "4 IV 13.4" "(c), formula (13.4.4)"]
noncomputable def pullbackStrictMonoidal : (pullbackFunctor f).Monoidal :=
  letI := Stacks.SheafOfModules.Strict.monoidalCategory Y.presheaf
    (structureSheafRing Y).property
  letI := Stacks.SheafOfModules.Strict.monoidalCategory X.presheaf
    (structureSheafRing X).property
  letI := pullbackFunctorLocalizedMonoidal f
  letI := toLocalizedMonoidalMonoidal Y.presheaf (structureSheafRing Y).property
  letI := fromLocalizedMonoidalMonoidal X.presheaf (structureSheafRing X).property
  inferInstanceAs ((Stacks.SheafOfModules.Strict.toLocalizedMonoidal Y.presheaf
    (structureSheafRing Y).property ⋙ pullbackFunctorLocalized f ⋙
      fromLocalizedMonoidal X.presheaf (structureSheafRing X).property).Monoidal)

/-! ### The pulled-back multiplication and unit -/

section Mul

variable (A : SheafOfModules.GradedAlgebra.{u, u}
  (toRingCat (Opens.grothendieckTopology Y.carrier) Y.sheaf))

/-- **The multiplication of `f^*A`**: the multiplication of `A` in degrees `i` and `j`,
conjugated by the tensorator of the monoidal pullback functor. -/
noncomputable def pullbackMul (i j : ℤ) :
    (pullbackFunctor f).obj (A.piece i) ⊗ (pullbackFunctor f).obj (A.piece j) ⟶
      (pullbackFunctor f).obj (A.piece (i + j)) :=
  letI := pullbackStrictMonoidal f
  Stacks.MonoidalGraded.mapMul (F := pullbackFunctor f) (X := A.piece i) (Y := A.piece j)
    (Z := A.piece (i + j)) (mulSheaf A i j)

/-- **The global unit of `f^*A`**, as a morphism `𝟙_ ⟶ f^*(A_0)`: the global unit of `A`,
conjugated by the unit morphism of the monoidal pullback functor. -/
noncomputable def pullbackOne : 𝟙_ (SheafOfModules.{u} (structureRingSheaf X)) ⟶
    (pullbackFunctor f).obj (A.piece 0) :=
  letI := pullbackStrictMonoidal f
  Stacks.MonoidalGraded.mapOne (F := pullbackFunctor f) (X := A.piece 0) (oneHom A)

variable (hY : Presheaf.IsSheaf (Opens.grothendieckTopology Y.carrier)
  (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Y.sheaf.obj))

include hY

/-- **The multiplication of `f^*A` is associative**, as an equality of morphisms out of
`f^*(A_i) ⊗ f^*(A_j) ⊗ f^*(A_k)`. This is
`Stacks.TensorSheafWorld.mulSheaf_assoc` transported along the monoidal pullback functor. -/
theorem pullbackMul_assoc (i j k : ℤ) :
    pullbackMul f A i j ▷ (pullbackFunctor f).obj (A.piece k) ≫ pullbackMul f A (i + j) k =
      (α_ ((pullbackFunctor f).obj (A.piece i)) ((pullbackFunctor f).obj (A.piece j))
            ((pullbackFunctor f).obj (A.piece k))).hom ≫
        (pullbackFunctor f).obj (A.piece i) ◁ pullbackMul f A j k ≫
          pullbackMul f A i (j + k) ≫
            eqToHom (congrArg (fun n ↦ (pullbackFunctor f).obj (A.piece n))
              (add_assoc i j k).symm) := by
  let _ := pullbackStrictMonoidal f
  refine (Stacks.MonoidalGraded.mapMul_assoc (pullbackFunctor f) (mulSheaf A i j)
    (mulSheaf A j k) (mulSheaf A (i + j) k)
    (mulSheaf A i (j + k) ≫ eqToHom (congrArg A.piece (add_assoc i j k).symm))
    (Stacks.TensorSheafWorld.mulSheaf_assoc Y.sheaf hY A i j k)).trans ?_
  refine congrArg (fun ϑ ↦ (α_ ((pullbackFunctor f).obj (A.piece i))
      ((pullbackFunctor f).obj (A.piece j)) ((pullbackFunctor f).obj (A.piece k))).hom ≫
    (pullbackFunctor f).obj (A.piece i) ◁ pullbackMul f A j k ≫ ϑ) ?_
  exact (Stacks.MonoidalGraded.mapMul_comp (pullbackFunctor f) (mulSheaf A i (j + k))
    (eqToHom (congrArg A.piece (add_assoc i j k).symm))).trans
    (congrArg (fun ϑ ↦ pullbackMul f A i (j + k) ≫ ϑ)
      (eqToHom_map (pullbackFunctor f) (congrArg A.piece (add_assoc i j k).symm)))

/-- **The global unit of `f^*A` is a left identity**, as an equality of morphisms. This is
`SheafOfModules.GradedAlgebra.mulSheaf_one_mul` transported along the monoidal pullback
functor. -/
theorem pullbackOne_mul (i : ℤ) :
    pullbackOne f A ▷ (pullbackFunctor f).obj (A.piece i) ≫ pullbackMul f A 0 i =
      (λ_ ((pullbackFunctor f).obj (A.piece i))).hom ≫
        eqToHom (congrArg (fun n ↦ (pullbackFunctor f).obj (A.piece n)) (zero_add i).symm) := by
  let _ := pullbackStrictMonoidal f
  simpa only [pullbackOne, pullbackMul, eqToHom_map] using
    Stacks.MonoidalGraded.mapOne_mul (pullbackFunctor f) (oneHom A) (mulSheaf A 0 i)
      (eqToHom (congrArg A.piece (zero_add i).symm)) (mulSheaf_one_mul A hY i)

/-- **The global unit of `f^*A` is a right identity**, as an equality of morphisms. This is
`SheafOfModules.GradedAlgebra.mulSheaf_mul_one` transported along the monoidal pullback
functor. -/
theorem pullbackMul_one (i : ℤ) :
    (pullbackFunctor f).obj (A.piece i) ◁ pullbackOne f A ≫ pullbackMul f A i 0 =
      (ρ_ ((pullbackFunctor f).obj (A.piece i))).hom ≫
        eqToHom (congrArg (fun n ↦ (pullbackFunctor f).obj (A.piece n)) (add_zero i).symm) := by
  let _ := pullbackStrictMonoidal f
  simpa only [pullbackOne, pullbackMul, eqToHom_map] using
    Stacks.MonoidalGraded.mapMul_one (pullbackFunctor f) (oneHom A) (mulSheaf A i 0)
      (eqToHom (congrArg A.piece (add_zero i).symm)) (mulSheaf_mul_one A hY i)

/-! ### The sheaf of graded algebras `f^*A` -/

/-- **The pullback of a sheaf of graded algebras along a morphism of ringed spaces is a sheaf
of graded algebras**, with homogeneous pieces the degreewise pullbacks `f^*(A_n)`.

This is `SheafOfModules.GradedAlgebra.ofMorphismData` applied to the three transported
morphism-level identities. -/
noncomputable def pullbackGradedAlgebra :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X) :=
  ofMorphismData (Osharp := X.sheaf) (structureSheafRing X).property
    (fun n ↦ (pullbackFunctor f).obj (A.piece n)) (pullbackMul f A) (pullbackOne f A)
    (pullbackMul_assoc f A hY) (pullbackOne_mul f A hY) (pullbackMul_one f A hY)

/-- The homogeneous pieces of `f^*A` are the pullbacks of those of `A`. -/
theorem pullbackGradedAlgebra_piece (n : ℤ) :
    (pullbackGradedAlgebra f A hY).piece n = (pullbackFunctor f).obj (A.piece n) :=
  rfl

/-- The multiplication of `f^*A` on a pure tensor of local sections of the pullbacks. -/
theorem pullbackGradedAlgebra_mul_app (i j : ℤ) (U : (Opens X.carrier)ᵒᵖ)
    (x : ((pullbackFunctor f).obj (A.piece i)).val.obj U)
    (y : ((pullbackFunctor f).obj (A.piece j)).val.obj U) :
    ((pullbackGradedAlgebra f A hY).mul i j).app U x y =
      (pullbackMul f A i j).val.app U
        ((PresheafOfModules.tensorSheafUnit ((pullbackFunctor f).obj (A.piece i))
          ((pullbackFunctor f).obj (A.piece j))).app U (x ⊗ₜ y)) :=
  rfl

end Mul

end Stacks.PullbackGradedAlgebra

end
