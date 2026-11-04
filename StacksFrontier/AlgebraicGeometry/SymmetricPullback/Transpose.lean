module

public import StacksFrontier.AlgebraicGeometry.SymmetricPullback.Commutes

/-!
# The adjoint transpose of a unital homomorphism out of a pulled-back graded algebra

Let `f : X ⟶ Y` be a morphism of ringed spaces, `A` a sheaf of graded `𝒪_Y`-algebras and `C` a
sheaf of graded `𝒪_X`-algebras. `Stacks.RingedSpace.pullbackGradedAlgebra` makes `f^*A` a sheaf
of graded `𝒪_X`-algebras, and this file establishes the bijection

`UnitalHom (f^*A) C ≃ UnitalHom A (f_*C)`

degreewise given by the adjoint transpose of `f^* ⊣ f_*`.

For `g : UnitalHom (f^*A) C`, the transpose evaluated on a section of `A` over `U` is `g` evaluated
on the pullback-unit image over `f⁻¹U` (`SheafOfModules.GradedAlgebra.homEquiv_val_app`), so its
multiplicativity and unitality are those of `g`. Conversely, for `h : UnitalHom A (f_*C)`, both
sides of the multiplicativity equation for the transpose are bilinear in the two local sections of
`f^*A`, so by `Stacks.RingedSpace.pullbackBilinear_ext`, which rests on the stalk formula
[Stacks, Tag 0098], it suffices that they agree on pullback-unit images, where it is the
multiplicativity of `h`.

## Main definitions

* `Stacks.RingedSpace.bilinPostcomp`: a bilinear map of sheaves of modules composed with a
  morphism out of its target.
* `Stacks.RingedSpace.transposeApp`: the degreewise adjoint transpose of a unital homomorphism
  `A ⟶ f_*C`.
* `Stacks.RingedSpace.transposeUnitalHom`: that transpose, as a unital homomorphism
  `f^*A ⟶ C`.
* `Stacks.RingedSpace.untransposeUnitalHom`: the adjoint transpose of a unital homomorphism
  `f^*A ⟶ C`, as a unital homomorphism `A ⟶ f_*C`.

## Main results

* `Stacks.RingedSpace.transposeApp_pullbackUnit`: the transpose on a pullback-unit image.
* `Stacks.RingedSpace.transposeUnitalHom_untransposeUnitalHom` and
  `Stacks.RingedSpace.untransposeUnitalHom_transposeUnitalHom`: the two transposes are mutually
  inverse.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite
open scoped TensorProduct
universe u

namespace Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction
  SheafOfModules.GradedAlgebra

section Postcomp

variable {X : RingedSpace.{u, u}} {M N P P' : SheafOfModules.{u} (structureRingSheaf X)}

/-- A bilinear map of sheaves of modules composed with a morphism out of its target. -/
def bilinPostcomp (β : SheafOfModules.BilinearMap M N P) (φ : P ⟶ P') :
    SheafOfModules.BilinearMap M N P' where
  app U := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (fun y => φ.val.app U (β.app U x y))
      (fun y y' => by
        change φ.val.app U (β.app U x (y + y')) =
          φ.val.app U (β.app U x y) + φ.val.app U (β.app U x y')
        rw [map_add (β.app U x) y y', map_add]))
    (fun x x' => by
      ext y
      change φ.val.app U (β.app U (x + x') y) =
        φ.val.app U (β.app U x y) + φ.val.app U (β.app U x' y)
      rw [β.map_add_left U x x' y, map_add])
  map_smul_left U r x y := by
    change φ.val.app U (β.app U (r • x) y) = r • φ.val.app U (β.app U x y)
    rw [β.map_smul_left U r x y]
    exact _root_.map_smul (ConcreteCategory.hom (φ.val.app U)) r _
  map_smul_right U r x y := by
    change φ.val.app U (β.app U x (r • y)) = r • φ.val.app U (β.app U x y)
    rw [β.map_smul_right U r x y]
    exact _root_.map_smul (ConcreteCategory.hom (φ.val.app U)) r _
  naturality {U V} g x y :=
    (naturality_apply φ.val g (β.app U x y)).symm.trans
      (congrArg (fun z => φ.val.app V z) (β.naturality g x y))

/-- `bilinPostcomp β φ` evaluated on local sections `x` and `y` is `φ` applied to `β x y`. -/
@[simp] lemma bilinPostcomp_app (β : SheafOfModules.BilinearMap M N P) (φ : P ⟶ P')
    (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (bilinPostcomp β φ).app U x y = φ.val.app U (β.app U x y) := rfl

end Postcomp

section Transpose

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y)}
  {C : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}

/-- The pushforward `f_*C` of a sheaf of graded `𝒪_X`-algebras along `f`, as a sheaf of graded
algebras over `structureRingSheaf Y`. -/
noncomputable abbrev pushforwardAlgebra
    (C : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)) :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y) :=
  pushforwardRingedSpace f C

/-- The degreewise adjoint transpose of a unital homomorphism `A ⟶ f_*C`: a morphism
`f^*(A.piece n) ⟶ C.piece n` for each degree. -/
noncomputable def transposeApp (h : UnitalHom A (pushforwardAlgebra f C)) (n : ℤ) :
    (pullbackGradedAlgebra f A).piece n ⟶ C.piece n :=
  ((pullbackAdjunction f).homEquiv (A.piece n) (C.piece n)).symm (h.app n)

/-- The transpose, evaluated on the pullback-unit image of a local section of `A`, is the
original homomorphism evaluated on that section. -/
lemma transposeApp_pullbackUnit (h : UnitalHom A (pushforwardAlgebra f C)) (n : ℤ)
    (V : Opens Y.carrier) (a : (A.piece n).val.obj (op V)) :
    (transposeApp f h n).val.app (op ((opensMap f).obj V))
        (pullbackUnit f (A.piece n) (op V) a) =
      (h.app n).val.app (op V) a :=
  homEquiv_symm_val_app_unit f (M := A.piece n) (N := C.piece n) (h.app n) (op V) a

/-- The adjoint transpose of a unital homomorphism `A ⟶ f_*C`, as a unital homomorphism
`f^*A ⟶ C`. -/
noncomputable def transposeUnitalHom (h : UnitalHom A (pushforwardAlgebra f C)) :
    UnitalHom (pullbackGradedAlgebra f A) C where
  app := transposeApp f h
  map_mul i j U x y := by
    obtain ⟨U⟩ := U
    refine pullbackBilinear_ext f
      (bilinPostcomp ((pullbackGradedAlgebra f A).mul i j) (transposeApp f h (i + j)))
      ((((C.mul i j).compLeft (transposeApp f h i).val).compRight
        (transposeApp f h j).val)) (fun V a b => ?_) U x y
    change (transposeApp f h (i + j)).val.app (op ((opensMap f).obj V))
        (((pullbackGradedAlgebra f A).mul i j).app (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece i) (op V) a) (pullbackUnit f (A.piece j) (op V) b)) =
      (C.mul i j).app (op ((opensMap f).obj V))
        ((transposeApp f h i).val.app (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece i) (op V) a))
        ((transposeApp f h j).val.app (op ((opensMap f).obj V))
          (pullbackUnit f (A.piece j) (op V) b))
    rw [pullbackGradedAlgebra_mul_pullbackUnit f A i j V a b, transposeApp_pullbackUnit,
      transposeApp_pullbackUnit, transposeApp_pullbackUnit]
    exact h.map_mul i j (op V) a b
  map_one U := by
    obtain ⟨U⟩ := U
    have hres : (pullbackGradedAlgebra f A).one.eval (op U) =
        ((pullbackGradedAlgebra f A).piece 0).val.map (homOfLE (le_top : U ≤ ⊤)).op
          ((pullbackGradedAlgebra f A).one.eval (op ⊤)) :=
      (PresheafOfModules.sections_property (pullbackGradedAlgebra f A).one
        (homOfLE (le_top : U ≤ ⊤)).op).symm
    have htop : (transposeApp f h 0).val.app (op (⊤ : Opens X.carrier))
          ((pullbackGradedAlgebra f A).one.eval (op ⊤)) =
        C.one.eval (op (⊤ : Opens X.carrier)) := by
      have h1 : (pullbackGradedAlgebra f A).one.eval (op (⊤ : Opens X.carrier)) =
          pullbackUnit f (A.piece 0) (op (⊤ : Opens Y.carrier))
            (A.one.eval (op (⊤ : Opens Y.carrier))) :=
        pullbackSectionsUnit_eval f (A.piece 0) A.one ⊤
      have h2 : (transposeApp f h 0).val.app (op (⊤ : Opens X.carrier))
            (pullbackUnit f (A.piece 0) (op (⊤ : Opens Y.carrier))
              (A.one.eval (op (⊤ : Opens Y.carrier)))) =
          (h.app 0).val.app (op (⊤ : Opens Y.carrier))
            (A.one.eval (op (⊤ : Opens Y.carrier))) :=
        transposeApp_pullbackUnit f h 0 ⊤ _
      have h3 : (h.app 0).val.app (op (⊤ : Opens Y.carrier))
            (A.one.eval (op (⊤ : Opens Y.carrier))) =
          C.one.eval (op (⊤ : Opens X.carrier)) :=
        h.map_one (op (⊤ : Opens Y.carrier))
      rw [h1, h2, h3]
    rw [hres, naturality_apply (transposeApp f h 0).val (homOfLE (le_top : U ≤ ⊤)).op, htop]
    exact PresheafOfModules.sections_property C.one (homOfLE (le_top : U ≤ ⊤)).op

/-- The degree-`n` component of `transposeUnitalHom f h` is `transposeApp f h n`. -/
@[simp] lemma transposeUnitalHom_app (h : UnitalHom A (pushforwardAlgebra f C)) (n : ℤ) :
    (transposeUnitalHom f h).app n = transposeApp f h n := rfl

/-- The adjoint transpose of a unital homomorphism `f^*A ⟶ C`, as a unital homomorphism
`A ⟶ f_*C`. -/
noncomputable def untransposeUnitalHom (g : UnitalHom (pullbackGradedAlgebra f A) C) :
    UnitalHom A (pushforwardAlgebra f C) where
  app n := (pullbackAdjunction f).homEquiv (A.piece n) (C.piece n) (g.app n)
  map_mul i j U x y := by
    obtain ⟨U⟩ := U
    have key : ∀ (m : ℤ) (z : (A.piece m).val.obj (op U)),
        ((pullbackAdjunction f).homEquiv (A.piece m) (C.piece m) (g.app m)).val.app (op U) z =
          (g.app m).val.app (op ((opensMap f).obj U))
            (pullbackUnit f (A.piece m) (op U) z) :=
      fun m z => homEquiv_val_app f (M := A.piece m) (N := C.piece m) (g.app m) (op U) z
    have hmul : pullbackUnit f (A.piece (i + j)) (op U) ((A.mul i j).app (op U) x y) =
        ((pullbackGradedAlgebra f A).mul i j).app (op ((opensMap f).obj U))
          (pullbackUnit f (A.piece i) (op U) x) (pullbackUnit f (A.piece j) (op U) y) :=
      (pullbackGradedAlgebra_mul_pullbackUnit f A i j U x y).symm
    exact (key (i + j) _).trans
      ((congrArg (fun z => (g.app (i + j)).val.app (op ((opensMap f).obj U)) z) hmul).trans
        ((g.map_mul i j (op ((opensMap f).obj U)) _ _).trans
          (congrArg₂ (fun p q => (C.mul i j).app (op ((opensMap f).obj U)) p q)
            (key i x).symm (key j y).symm)))
  map_one U := by
    obtain ⟨U⟩ := U
    have key0 : ((pullbackAdjunction f).homEquiv (A.piece 0) (C.piece 0)
            (g.app 0)).val.app (op U) (A.one.eval (op U)) =
        (g.app 0).val.app (op ((opensMap f).obj U))
          (pullbackUnit f (A.piece 0) (op U) (A.one.eval (op U))) :=
      homEquiv_val_app f (M := A.piece 0) (N := C.piece 0) (g.app 0) (op U) _
    have hone : pullbackUnit f (A.piece 0) (op U) (A.one.eval (op U)) =
        (pullbackGradedAlgebra f A).one.eval (op ((opensMap f).obj U)) :=
      (pullbackSectionsUnit_eval f (A.piece 0) A.one U).symm
    exact key0.trans
      ((congrArg (fun z => (g.app 0).val.app (op ((opensMap f).obj U)) z) hone).trans
        (g.map_one (op ((opensMap f).obj U))))

/-- The degree-`n` component of `untransposeUnitalHom f g` is the adjoint transpose of the
degree-`n` component of `g`. -/
@[simp] lemma untransposeUnitalHom_app (g : UnitalHom (pullbackGradedAlgebra f A) C) (n : ℤ) :
    (untransposeUnitalHom f g).app n =
      (pullbackAdjunction f).homEquiv (A.piece n) (C.piece n) (g.app n) := rfl

/-- Transposing a unital homomorphism `A ⟶ f_*C` and then transposing back recovers it. -/
lemma untransposeUnitalHom_transposeUnitalHom (h : UnitalHom A (pushforwardAlgebra f C)) :
    untransposeUnitalHom f (transposeUnitalHom f h) = h := by
  refine UnitalHom.ext fun n => ?_
  exact ((pullbackAdjunction f).homEquiv (A.piece n) (C.piece n)).apply_symm_apply (h.app n)

/-- Transposing a unital homomorphism `f^*A ⟶ C` and then transposing back recovers it. -/
lemma transposeUnitalHom_untransposeUnitalHom (g : UnitalHom (pullbackGradedAlgebra f A) C) :
    transposeUnitalHom f (untransposeUnitalHom f g) = g := by
  refine UnitalHom.ext fun n => ?_
  exact ((pullbackAdjunction f).homEquiv (A.piece n) (C.piece n)).symm_apply_apply (g.app n)

end Transpose

end Stacks.RingedSpace


end
