module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedBimoduleTensorAction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRelativeTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimodule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleTransport

/-!
# The tensor product of a differential graded module with a differential graded bimodule

Let `O` be a sheaf of commutative rings on a site, let `A` and `B` be sheaves of differential
graded `O`-algebras, let `M` be a right differential graded `A`-module and let `N` be a
differential graded `(A, B)`-bimodule. The balanced tensor product `M ⊗_A N` carries a
differential `d (x ⊗ y) = dx ⊗ y + (-1)^{deg x} x ⊗ dy` and a right `B`-action
`(x ⊗ y) b = x ⊗ (y b)`, and this file makes it a right differential graded `B`-module: the
signed Leibniz rule for the right action of `B` is the content.

## Main definitions

* `SheafOfModules.DifferentialGradedBimodule.toLeftDifferentialGradedModule` and
  `SheafOfModules.DifferentialGradedBimodule.toGradedBimodule` are the left differential graded
  `A`-module and the graded `(A, B)`-bimodule underlying a differential graded bimodule; they
  feed `M ⊗_A N` its differential and its right action respectively.
* `SheafOfModules.RelativeTensor.dgTensorRight` is **the right differential graded `B`-module
  `M ⊗_A N`**: its complex is the one of `SheafOfModules.RelativeTensor.dgTensor` and its action
  is the one of `SheafOfModules.RelativeTensor.gradedTensorRight`.
* `Stacks.bilinHomRestrict` is the contravariance of the internal hom in its source, which is
  what expresses the differential of the acting section as a morphism.

## Main results

* `SheafOfModules.RelativeTensor.actPre_leibniz`: **the signed Leibniz rule for the right action
  of `B`**, as an equality of morphisms out of the presheaf-level relative tensor product. The
  content is the Leibniz rule of the right action of the bimodule.
* `SheafOfModules.RelativeTensor.dgTensorRight_mul_tmul` and
  `SheafOfModules.RelativeTensor.dgTensorRight_d_tmul` compute the action and the differential on
  a local section `x ⊗ y`.
* `SheafOfModules.RelativeTensor.smulSheafLeibniz_dgTensorRight` is the morphism-level reading of
  the Leibniz rule, in the form a monoidal functor transports.

## Implementation notes

The differential is the one of the relative tensor product of `M` with the left differential
graded module underlying `N`, so it is not rebuilt here: what is new is its compatibility with
the right action of `B`. Degree `n` of `M ⊗_A N` is a sheafification of a cokernel of a
coproduct, so neither the sections nor the sections of the presheaf-level cokernel can be
written down. The Leibniz rule is therefore first proved as an equality of *morphisms* out of
the presheaf-level cokernel with values in the internal hom `Stacks.bilinHom` of the acting
piece of `B`, where the universal properties of the cokernel and of the coproduct reduce it to
pure tensors; it is then transported to sections of the sheafification along the local
surjectivity of the sheafification unit.

Degrees indexing the two sides of a Leibniz rule agree only propositionally, so the transports
`SheafOfModules.gradedCast` of the Leibniz fields are unavoidable; they are removed from the
computation by `SheafOfModules.RelativeTensor.tmulPre_congr` together with
`SheafOfModules.gradedCast_heq`, and the target degree of
`SheafOfModules.RelativeTensor.actPre` being a parameter means the three terms of the rule live
in one and the same degree `n + i + 1`.

**Universes.** The homogeneous pieces of the two algebras and the sections of the two modules
are at `max u v z` with `z` free, the universe of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedBimoduleTensorAction.lean`: every universe
at least as large as the site's, which is what `Stacks.bilinHom` forces there and all that is
forced. The universe `t` of the sheaf of rings is independent of it, except in the
`MorphismLeibniz` section, where `Stacks.TensorSheafWorld.monoidalCategory` puts the sheaf of
rings and the sheaves of modules in one universe.

Applications of the declarations of `GradedBimoduleTensorAction.lean` and of the local helpers
built from them carry their universe levels explicitly in the five largest proofs. Their module
universe is the atom `z` only inside `max u v z`, so an application leaves the elaborator with
`max u v ?z =?= max u v z`; `Lean.Meta.isLevelDefEqAux` postpones that rather than solving it,
because the approximation that would solve it (`tryApproxMaxMax`) runs only once postponement
is no longer allowed. In a proof with many such applications the postponed constraints cost
more than 200000 heartbeats to discharge, and naming the levels removes them.

## References

* [Stacks Project, Tag 0FRQ](https://stacks.math.columbia.edu/tag/0FRQ)
* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe t w w' a m v u z

namespace Stacks

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{t}}
  {G G' : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
  {P : PresheafOfModules.{w'} (O ⋙ forget₂ CommRingCat RingCat)}

/-- Restriction of a local section commutes with integer multiples. -/
theorem restr_zsmul {R : Cᵒᵖ ⥤ RingCat.{t}} (F : PresheafOfModules.{w} R) {U V : Cᵒᵖ}
    (f : U ⟶ V) (k : ℤ) (x : F.obj U) : restr F f (k • x) = k • restr F f x :=
  map_zsmul (ConcreteCategory.hom (F.map f)) k x

/-- A component of a section of the internal hom commutes with integer multiples. -/
theorem hApp_zsmul (k : ℤ) {U : Cᵒᵖ} (φ : (bilinHom G P).obj U) {V : Cᵒᵖ} (f : U ⟶ V)
    (y : G.obj V) : hApp (k • φ) f y = k • hApp φ f y :=
  map_zsmul (AddMonoidHom.mk' (fun ψ : (bilinHom G P).obj U => hApp ψ f y)
    (fun ψ ψ' => hApp_add ψ ψ' f y)) k φ

/-- **The internal hom is contravariant in its source**: a morphism `G ⟶ G'` precomposes the
families of maps on sections. -/
noncomputable def bilinHomRestrict (ψ : G ⟶ G')
    (P : PresheafOfModules.{w'} (O ⋙ forget₂ CommRingCat RingCat)) :
    bilinHom G' P ⟶ bilinHom G P where
  app U := ModuleCat.ofHom (X := (bilinHom G' P).obj U) (Y := (bilinHom G P).obj U)
    { toFun := fun φ => hMk
        (fun V f => (hApp φ f).comp (ConcreteCategory.hom
          (PresheafOfModules.Hom.app ψ V)).toAddMonoidHom)
        (fun V f r y => by
          change hApp φ f (PresheafOfModules.Hom.app ψ V (r • y)) =
            r • hApp φ f (PresheafOfModules.Hom.app ψ V y)
          rw [map_smul (ConcreteCategory.hom (PresheafOfModules.Hom.app ψ V)) r y,
            hApp_smul_right])
        (fun V W f g y => by
          change restr P g (hApp φ f (PresheafOfModules.Hom.app ψ V y)) =
            hApp φ (f ≫ g) (PresheafOfModules.Hom.app ψ W (restr G g y))
          rw [hApp_naturality, restr_app ψ g])
      map_add' := fun φ φ' => hApp_ext fun V f y => rfl
      map_smul' := fun r φ => hApp_ext fun V f y => rfl }
  naturality {U V} g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => hApp_ext fun W f y => ?_)
    rfl

/-- The precomposition `bilinHomRestrict ψ P` of a family of maps `φ` by `ψ`, evaluated at a
local section `y`, is `φ` evaluated at `ψ y`. -/
@[simp]
theorem hApp_bilinHomRestrict (ψ : G ⟶ G')
    (P : PresheafOfModules.{w'} (O ⋙ forget₂ CommRingCat RingCat)) {U : Cᵒᵖ}
    (φ : (bilinHom G' P).obj U) {V : Cᵒᵖ} (f : U ⟶ V) (y : G.obj V) :
    hApp (PresheafOfModules.Hom.app (bilinHomRestrict ψ P) U φ) f y =
      hApp φ f (PresheafOfModules.Hom.app ψ V y) := rfl

end Stacks

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}} {M N : PresheafOfModules.{w} R}

/-- A sum of morphisms of presheaves of modules, on sections. -/
theorem app_add (φ ψ : M ⟶ N) (X : Cᵒᵖ) (z : M.obj X) :
    Hom.app (φ + ψ) X z = Hom.app φ X z + Hom.app ψ X z := rfl

/-- An integer multiple of a morphism of presheaves of modules, on sections. -/
theorem app_zsmul (k : ℤ) (φ : M ⟶ N) (X : Cᵒᵖ) (z : M.obj X) :
    Hom.app (k • φ) X z = k • Hom.app φ X z :=
  map_zsmul (AddMonoidHom.mk' (fun χ : M ⟶ N => Hom.app χ X z)
    (fun χ χ' => app_add χ χ' X z)) k φ

end PresheafOfModules

namespace SheafOfModules

section OfBimodule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, a} R}

/-- The left differential graded `A`-module underlying a differential graded `(A, B)`-bimodule:
the left action, with its associativity read in the other direction. -/
@[implicit_reducible]
def DifferentialGradedBimodule.toLeftDifferentialGradedModule
    (N : DifferentialGradedBimodule.{t, a, m} A B) :
    LeftDifferentialGradedModule.{t, a, m} A where
  complex := N.complex
  mul := N.leftMul
  mul_assoc n m k U x y z := (N.left_assoc n m k U x y z).symm
  one_mul := N.one_left
  leibniz := N.leibniz_left

/-- The graded `(A, B)`-bimodule underlying a differential graded `(A, B)`-bimodule: the two
actions of the complex, with its differential forgotten. -/
@[implicit_reducible]
def DifferentialGradedBimodule.toGradedBimodule (N : DifferentialGradedBimodule.{t, a, m} A B) :
    GradedBimodule.{t, a, m} A.toGradedAlgebra B.toGradedAlgebra where
  piece := N.complex.X
  rightMul := N.rightMul
  leftMul := N.leftMul
  left_assoc := N.left_assoc
  right_assoc := N.right_assoc
  left_right_assoc := N.left_right_assoc
  one_left := N.one_left
  one_right := N.one_right

/-- The degree-`n` piece of the graded bimodule underlying `N` is the degree-`n` term of the
complex of `N`. -/
@[simp]
theorem DifferentialGradedBimodule.toGradedBimodule_piece
    (N : DifferentialGradedBimodule.{t, a, m} A B) (n : ℤ) :
    N.toGradedBimodule.piece n = N.complex.X n := rfl

/-- The two readings of the left action of a differential graded bimodule agree: the left graded
module of its graded bimodule is the graded module of its left differential graded module. -/
theorem DifferentialGradedBimodule.toLeftGradedModule_toGradedBimodule
    (N : DifferentialGradedBimodule.{t, a, m} A B) :
    N.toGradedBimodule.toLeftGradedModule =
      LeftGradedModule.ofDifferentialGraded N.toLeftDifferentialGradedModule := rfl

end OfBimodule

namespace RelativeTensor

open Stacks

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  {A B : DifferentialGradedAlgebra.{t, max u v z} (toRingCat J Osharp)}
  (M : DifferentialGradedModule.{t, max u v z, max u v z} A)
  (N : DifferentialGradedBimodule.{t, max u v z, max u v z} A B)

/-- **The differential of the presheaf-level relative tensor product on a pure tensor**:
`d (x ⊗ y) = dx ⊗ y + (-1)^{deg x} x ⊗ dy`. -/
theorem dgTensorDiffPre_tmulPre (k : ℤ) (p : TensorIndex k) (X : Cᵒᵖ)
    (u : ((gP M).piece p.1.1).val.obj X)
    (w : (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app
        (dgTensorDiffPre M N.toLeftDifferentialGradedModule k) X
        (tmulPre (gP M) N.toGradedBimodule k p X u w) =
      tmulPre (gP M) N.toGradedBimodule (k + 1) (tensorIndexShiftLeft p) X
          ((M.complex.d p.1.1 (p.1.1 + 1)).val.app X u) w +
        (Int.negOnePow p.1.1 : ℤ) •
          tmulPre (gP M) N.toGradedBimodule (k + 1) (tensorIndexShiftRight p) X u
            ((N.complex.d p.1.2 (p.1.2 + 1)).val.app X w) := by
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app
      (dgTensorDiffPre M N.toLeftDifferentialGradedModule k) X)
    (tmulPre_eq (gP M) N.toGradedBimodule k p X u w)) ?_
  refine (PresheafOfModules.comp_app_apply _ _ X _).symm.trans ?_
  refine (PresheafOfModules.hom_congr_apply'
    (gradedTensorπ_dgTensorDiffPre (P := M) N.toLeftDifferentialGradedModule k) X _).trans ?_
  refine (PresheafOfModules.comp_app_apply _ _ X _).trans ?_
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app
      (gradedTensorπ (gP M) (gN N.toLeftDifferentialGradedModule) (k + 1)) X)
    (dgTensorSumDiff_tensorSumι_apply M N.toLeftDifferentialGradedModule p X u w)) ?_
  rw [map_add, map_zsmul]
  rfl

/-- A pure tensor is linear over the integers in its second factor. -/
theorem tmulPre_zsmul_snd (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ) (k : ℤ)
    (x : ((gP M).piece p.1.1).val.obj X)
    (y : (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val.obj X) :
    tmulPre (gP M) N.toGradedBimodule n p X x (k • y) =
      k • tmulPre (gP M) N.toGradedBimodule n p X x y :=
  map_zsmul ((tmulPreBil (gP M) N.toGradedBimodule n p).app X x) k y

/-- The index `(p + 1, q + i)` of the summand containing `dx ⊗ (y b)`. -/
abbrev tensorIndexLeibnizLeft {n : ℤ} (p : TensorIndex n) (i : ℤ) : TensorIndex (n + i + 1) :=
  actIndex (tensorIndexShiftLeft p) i (n + i + 1) (add_right_comm n 1 i)

/-- The index `(p, (q + 1) + i)` of the summand containing `x ⊗ ((dy) b)`. -/
abbrev tensorIndexLeibnizMid {n : ℤ} (p : TensorIndex n) (i : ℤ) : TensorIndex (n + i + 1) :=
  actIndex (tensorIndexShiftRight p) i (n + i + 1) (add_right_comm n 1 i)

/-- The index `(p, q + (i + 1))` of the summand containing `x ⊗ (y (db))`. -/
abbrev tensorIndexLeibnizRight {n : ℤ} (p : TensorIndex n) (i : ℤ) : TensorIndex (n + i + 1) :=
  actIndex p (i + 1) (n + i + 1) (add_assoc n i 1).symm

/-- Differentiating the bimodule factor of `x ⊗ (y b)` lands in the summand of `x ⊗ ((dy) b)`. -/
theorem tensorIndexShiftRight_actIndex_mid {n : ℤ} (p : TensorIndex n) (i : ℤ) :
    tensorIndexShiftRight (actIndex p i (n + i) rfl) = tensorIndexLeibnizMid p i :=
  Subtype.ext (by simp only [Prod.mk.injEq]; exact ⟨trivial, by omega⟩)

/-- Differentiating the algebra factor of `x ⊗ (y b)` lands in the summand of `x ⊗ (y (db))`. -/
theorem tensorIndexShiftRight_actIndex_right {n : ℤ} (p : TensorIndex n) (i : ℤ) :
    tensorIndexShiftRight (actIndex p i (n + i) rfl) = tensorIndexLeibnizRight p i :=
  Subtype.ext (by simp only [Prod.mk.injEq]; exact ⟨trivial, by omega⟩)

/-- **The differential of the action of `b` on a pure tensor**, expanded by the Leibniz rule of
the right action of the bimodule: it is `dx ⊗ (y b) + (-1)^p x ⊗ ((dy) b + (-1)^q y (db))`. -/
theorem dgTensorDiffPre_actPre_tmulPre (n i : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : ((gP M).piece p.1.1).val.obj X)
    (y : (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val.obj X) {V : Cᵒᵖ} (f : X ⟶ V)
    (b : (B.complex.X i).val.obj V) :
    PresheafOfModules.Hom.app
        (dgTensorDiffPre M N.toLeftDifferentialGradedModule (n + i)) V
        (hApp (PresheafOfModules.Hom.app (actPre (gP M) N.toGradedBimodule n i (n + i) rfl) X
          (tmulPre (gP M) N.toGradedBimodule n p X x y)) f b) =
      tmulPre (gP M) N.toGradedBimodule (n + i + 1) (tensorIndexLeibnizLeft p i) V
          ((M.complex.d p.1.1 (p.1.1 + 1)).val.app V
            (restr ((gP M).piece p.1.1).val f x))
          ((N.rightMul p.1.2 i).app V
            (restr (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val f y) b) +
        (Int.negOnePow p.1.1 : ℤ) •
          (tmulPre (gP M) N.toGradedBimodule (n + i + 1) (tensorIndexLeibnizMid p i) V
              (restr ((gP M).piece p.1.1).val f x)
              ((N.rightMul (p.1.2 + 1) i).app V
                ((N.complex.d p.1.2 (p.1.2 + 1)).val.app V
                  (restr (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val f y)) b) +
            (Int.negOnePow p.1.2 : ℤ) •
              tmulPre (gP M) N.toGradedBimodule (n + i + 1) (tensorIndexLeibnizRight p i) V
                (restr ((gP M).piece p.1.1).val f x)
                ((N.rightMul p.1.2 (i + 1)).app V
                  (restr (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val f y)
                  ((B.complex.d i (i + 1)).val.app V b))) := by
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app
      (dgTensorDiffPre M N.toLeftDifferentialGradedModule (n + i)) V)
    (actPre_tmulPre (gP M) N.toGradedBimodule n i (n + i) rfl p X x y f b)) ?_
  refine (dgTensorDiffPre_tmulPre M N (n + i) (actIndex p i (n + i) rfl) V _ _).trans ?_
  refine congrArg₂ (fun z z' => z + z') rfl (congrArg (fun z =>
    (Int.negOnePow p.1.1 : ℤ) • z) ?_)
  refine Eq.trans (congrArg (tmulPre (gP M) N.toGradedBimodule (n + i + 1)
      (tensorIndexShiftRight (actIndex p i (n + i) rfl)) V
      (restr ((gP M).piece p.1.1).val f x))
    (N.leibniz_right p.1.2 i V
      (restr (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val f y) b)) ?_
  refine (tmulPre_add_right (gP M) N.toGradedBimodule (n + i + 1) _ V _ _ _).trans ?_
  refine congrArg₂ (fun z z' => z + z') ?_ ?_
  · exact tmulPre_congr (gP M) N.toGradedBimodule (n + i + 1)
      (tensorIndexShiftRight_actIndex_mid p i) V HEq.rfl
      (gradedCast_heq (fun q => (N.complex.X q).val.obj V) (add_right_comm p.1.2 1 i) _)
  · refine (tmulPre_zsmul_snd M N (n + i + 1) _ V _ _ _).trans ?_
    exact congrArg (fun z => (Int.negOnePow p.1.2 : ℤ) • z)
      (tmulPre_congr (gP M) N.toGradedBimodule (n + i + 1)
        (tensorIndexShiftRight_actIndex_right p i) V HEq.rfl
        (gradedCast_heq (fun q => (N.complex.X q).val.obj V) (add_assoc p.1.2 i 1).symm _))

/-- **The action of `b` on the differential of a pure tensor**: it is
`dx ⊗ (y b) + (-1)^p x ⊗ ((dy) b)`. -/
theorem actPre_dgTensorDiffPre_tmulPre (n i : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : ((gP M).piece p.1.1).val.obj X)
    (y : (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val.obj X) {V : Cᵒᵖ} (f : X ⟶ V)
    (b : (B.complex.X i).val.obj V) :
    hApp (PresheafOfModules.Hom.app
        (actPre.{t, v, u, z} (gP M) N.toGradedBimodule (n + 1) i (n + i + 1)
          (add_right_comm n 1 i)) X
        (PresheafOfModules.Hom.app (dgTensorDiffPre M N.toLeftDifferentialGradedModule n) X
          (tmulPre (gP M) N.toGradedBimodule n p X x y))) f b =
      tmulPre (gP M) N.toGradedBimodule (n + i + 1) (tensorIndexLeibnizLeft p i) V
          ((M.complex.d p.1.1 (p.1.1 + 1)).val.app V
            (restr ((gP M).piece p.1.1).val f x))
          ((N.rightMul p.1.2 i).app V
            (restr (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val f y) b) +
        (Int.negOnePow p.1.1 : ℤ) •
          tmulPre (gP M) N.toGradedBimodule (n + i + 1) (tensorIndexLeibnizMid p i) V
            (restr ((gP M).piece p.1.1).val f x)
            ((N.rightMul (p.1.2 + 1) i).app V
              ((N.complex.d p.1.2 (p.1.2 + 1)).val.app V
                (restr (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val f y)) b) := by
  rw [dgTensorDiffPre_tmulPre, map_add, map_zsmul, hApp_add, hApp_zsmul]
  erw [actPre_tmulPre.{t, v, u, z} (gP M) N.toGradedBimodule (n + 1) i (n + i + 1)
      (add_right_comm n 1 i) (tensorIndexShiftLeft p) X _ y f b,
    actPre_tmulPre.{t, v, u, z} (gP M) N.toGradedBimodule (n + 1) i (n + i + 1)
      (add_right_comm n 1 i) (tensorIndexShiftRight p) X x _ f b]
  erw [← restr_app, ← restr_app]
  rfl

/-- **The signed Leibniz rule for the right action of `B` on the presheaf-level relative tensor
product**, as an equality of morphisms into the internal hom of the acting piece of `B`:
`d ((x ⊗ y) b) = (d (x ⊗ y)) b + (-1)^n (x ⊗ y) (db)`. -/
theorem actPre_leibniz (n i : ℤ) :
    actPre.{t, v, u, z} (gP M) N.toGradedBimodule n i (n + i) rfl ≫
        bilinHomMap (B.complex.X i).val
          (dgTensorDiffPre M N.toLeftDifferentialGradedModule (n + i)) =
      (dgTensorDiffPre M N.toLeftDifferentialGradedModule n ≫
            actPre.{t, v, u, z} (gP M) N.toGradedBimodule (n + 1) i (n + i + 1)
              (add_right_comm n 1 i) :
          gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule n ⟶
            bilinHom (B.complex.X i).val
              (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1))) +
        (Int.negOnePow n : ℤ) •
          (actPre.{t, v, u, z} (gP M) N.toGradedBimodule n (i + 1) (n + i + 1)
              (add_assoc n i 1).symm ≫
            bilinHomRestrict (B.complex.d i (i + 1)).val
              (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1))) := by
  refine (cancel_epi (gradedTensorπ (gP M) N.toGradedBimodule.toLeftGradedModule n)).mp
    (Sigma.hom_ext _ _ fun p => ?_)
  refine PresheafOfModules.tensorObj_hom_ext fun X x y => ?_
  refine hApp_ext fun V f b => ?_
  have hsign : (Int.negOnePow p.1.1 : ℤ) * (Int.negOnePow p.1.2 : ℤ) =
      (Int.negOnePow n : ℤ) := by
    rw [← Units.val_mul, ← Int.negOnePow_add, p.2]
  refine Eq.trans ((hApp_bilinHomMap (dgTensorDiffPre M N.toLeftDifferentialGradedModule (n + i))
      (PresheafOfModules.Hom.app (actPre.{t, v, u, z} (gP M) N.toGradedBimodule n i (n + i) rfl) X
        (tmulPre (gP M) N.toGradedBimodule n p X x y)) f b).trans
    (dgTensorDiffPre_actPre_tmulPre M N n i p X x y f b)) ?_
  refine Eq.trans ?_ (congrArg (fun z => hApp z f b) (PresheafOfModules.app_add
    (dgTensorDiffPre M N.toLeftDifferentialGradedModule n ≫
      actPre.{t, v, u, z} (gP M) N.toGradedBimodule (n + 1) i (n + i + 1) (add_right_comm n 1 i) :
        gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule n ⟶
          bilinHom (B.complex.X i).val
            (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1)))
    ((Int.negOnePow n : ℤ) •
      (actPre.{t, v, u, z} (gP M) N.toGradedBimodule n (i + 1) (n + i + 1) (add_assoc n i 1).symm ≫
        bilinHomRestrict (B.complex.d i (i + 1)).val
          (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1))))
    X (tmulPre (gP M) N.toGradedBimodule n p X x y))).symm
  refine Eq.trans ?_ (hApp_add _ _ f b).symm
  refine Eq.trans ?_ (congrArg₂ (fun z z' => z + z')
    (actPre_dgTensorDiffPre_tmulPre M N n i p X x y f b)
    ((congrArg (fun z => hApp z f b) (PresheafOfModules.app_zsmul (Int.negOnePow n : ℤ)
          (actPre.{t, v, u, z} (gP M) N.toGradedBimodule n (i + 1) (n + i + 1)
              (add_assoc n i 1).symm ≫
            bilinHomRestrict (B.complex.d i (i + 1)).val
              (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1))) X
          (tmulPre (gP M) N.toGradedBimodule n p X x y))).trans
      ((hApp_zsmul _ _ f b).trans (congrArg (fun z => (Int.negOnePow n : ℤ) • z)
        ((hApp_bilinHomRestrict (B.complex.d i (i + 1)).val _ _ f b).trans
          (actPre_tmulPre.{t, v, u, z} (gP M) N.toGradedBimodule n (i + 1) (n + i + 1)
            (add_assoc n i 1).symm p X x y f _)))))).symm
  rw [smul_add, smul_smul, hsign, ← add_assoc]
  rfl

/-- Changing the target degree of the right action by a propositional equality transports its
values, read on sections. -/
theorem gradedCast_actPre (n i d d' : ℤ) (h : n + i = d) (h' : n + i = d') (hdd : d = d')
    (V : Cᵒᵖ) (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule n).obj V)
    (b : (B.complex.X i).val.obj V) :
    gradedCast
        (fun k => (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule k).obj V) hdd
        (hApp (PresheafOfModules.Hom.app (actPre (gP M) N.toGradedBimodule n i d h) V w)
          (𝟙 V) b) =
      hApp (PresheafOfModules.Hom.app (actPre (gP M) N.toGradedBimodule n i d' h') V w)
        (𝟙 V) b := by
  obtain rfl : d = d' := hdd
  rfl

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v z}]
  [HasWeakSheafify J AddCommGrpCat.{max u v z}]

/-- The right action of `B` on a local section of `M ⊗_A N` coming from the presheaf level. -/
theorem gradedTensorRight_smul_unit (n i : ℤ) (V : Cᵒᵖ)
    (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule n).obj V)
    (b : (B.complex.X i).val.obj V) :
    (gradedTensorRight (gP M) N.toGradedBimodule).smul n i V
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule n) V w) b =
      PresheafOfModules.Hom.app
        (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule (n + i)) V
        (hApp (PresheafOfModules.Hom.app
          (actPre (gP M) N.toGradedBimodule n i (n + i) rfl) V w) (𝟙 V) b) :=
  (preGradedModule (gP M) N.toGradedBimodule).sheafify_smul n i V w b

/-- The differential of `M ⊗_A N` on a local section coming from the presheaf level. -/
theorem dgTensor_d_unit (k : ℤ) (V : Cᵒᵖ)
    (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule k).obj V) :
    PresheafOfModules.Hom.app
        ((dgTensor M N.toLeftDifferentialGradedModule).d k (k + 1)).val V
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule k) V w) =
      PresheafOfModules.Hom.app
        (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule (k + 1)) V
        (PresheafOfModules.Hom.app
          (dgTensorDiffPre M N.toLeftDifferentialGradedModule k) V w) := by
  have hd : (dgTensor M N.toLeftDifferentialGradedModule).d k (k + 1) =
      (PresheafOfModules.sheafification (R := toRingCat J Osharp)
        (𝟙 (toRingCat J Osharp).obj)).map
          (dgTensorDiffPre M N.toLeftDifferentialGradedModule k) :=
    congrArg (fun φ => (PresheafOfModules.sheafification (R := toRingCat J Osharp)
      (𝟙 (toRingCat J Osharp).obj)).map φ) (CochainComplex.of_d _ _ k)
  rw [hd]
  exact PresheafOfModules.unit_naturality_apply (α := 𝟙 (toRingCat J Osharp).obj)
    (φ := dgTensorDiffPre M N.toLeftDifferentialGradedModule k) V w

/-- Transport along an equality of degrees commutes with the sheafification unit. -/
theorem gradedCast_unit {k k' : ℤ} (h : k = k') (V : Cᵒᵖ)
    (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule k).obj V) :
    gradedCast
        (fun q => (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule q).val.obj V) h
        (PresheafOfModules.Hom.app
          (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule k) V w) =
      PresheafOfModules.Hom.app
        (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule k') V
        (gradedCast
          (fun q => (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule q).obj V) h
          w) := by
  subst h
  rfl

/-- Transport along an equality of degrees commutes with restriction of local sections. -/
theorem restr_gradedCast {k k' : ℤ} (h : k = k') {U V : Cᵒᵖ} (f : U ⟶ V)
    (z : (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule k).val.obj U) :
    restr (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule k').val f
        (gradedCast
          (fun q => (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule q).val.obj U) h
          z) =
      gradedCast
        (fun q => (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule q).val.obj V) h
        (restr (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule k).val f z) := by
  subst h
  rfl

/-- The right action of `B` on a local section coming from the presheaf level, transported along
an equality of degrees. -/
private theorem gradedCast_smul_unit (n i d : ℤ) (h : n + i = d) (V : Cᵒᵖ)
    (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule n).obj V)
    (b : (B.complex.X i).val.obj V) :
    gradedCast (fun q => (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule q).val.obj V) h
        ((gradedTensorRight.{t, v, u, z} (gP M) N.toGradedBimodule).smul n i V
          (PresheafOfModules.Hom.app
            (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule n) V w) b) =
      PresheafOfModules.Hom.app
        (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule d) V
        (hApp (PresheafOfModules.Hom.app (actPre (gP M) N.toGradedBimodule n i d h) V w)
          (𝟙 V) b) :=
  (congrArg _ (gradedTensorRight_smul_unit.{t, v, u, z} M N n i V w b)).trans
    ((gradedCast_unit.{t, v, u, z} M N h V _).trans
      (congrArg _ (gradedCast_actPre.{t, v, u, z} M N n i (n + i) d rfl h h V w b)))

/-- **The signed Leibniz rule for the right action of `B` on `M ⊗_A N`**, on a local section
coming from the presheaf level. -/
theorem dgTensorRight_leibniz_unit (n i : ℤ) (V : Cᵒᵖ)
    (w : (gradedTensorPre (gP M) N.toGradedBimodule.toLeftGradedModule n).obj V)
    (b : (B.complex.X i).val.obj V) :
    PresheafOfModules.Hom.app
        ((dgTensor M N.toLeftDifferentialGradedModule).d (n + i) (n + i + 1)).val V
        ((gradedTensorRight.{t, v, u, z} (gP M) N.toGradedBimodule).smul n i V
          (PresheafOfModules.Hom.app
            (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule n) V w) b) =
      gradedCast
          (fun q => (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule q).val.obj V)
          (add_right_comm n 1 i)
          ((gradedTensorRight.{t, v, u, z} (gP M) N.toGradedBimodule).smul (n + 1) i V
            (PresheafOfModules.Hom.app
              ((dgTensor M N.toLeftDifferentialGradedModule).d n (n + 1)).val V
              (PresheafOfModules.Hom.app
                (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule n) V w)) b) +
        (Int.negOnePow n : ℤ) •
          gradedCast
            (fun q => (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule q).val.obj V)
            (add_assoc n i 1).symm
            ((gradedTensorRight.{t, v, u, z} (gP M) N.toGradedBimodule).smul n (i + 1) V
              (PresheafOfModules.Hom.app
                (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule n) V w)
              ((B.complex.d i (i + 1)).val.app V b)) := by
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app
      ((dgTensor M N.toLeftDifferentialGradedModule).d (n + i) (n + i + 1)).val V)
    (gradedTensorRight_smul_unit.{t, v, u, z} M N n i V w b)) ?_
  refine (dgTensor_d_unit.{t, v, u, z} M N (n + i) V _).trans ?_
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app
      (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1)) V)
    ((congrArg (fun φ => hApp (PresheafOfModules.Hom.app φ V w) (𝟙 V) b)
      (actPre_leibniz.{t, v, u, z} M N n i)).trans
        ((congrArg (fun ξ => hApp ξ (𝟙 V) b) (PresheafOfModules.app_add _ _ V w)).trans
          ((hApp_add _ _ (𝟙 V) b).trans (congrArg₂ (fun ξ ξ' => ξ + ξ') rfl
            ((congrArg (fun ξ => hApp ξ (𝟙 V) b)
              (PresheafOfModules.app_zsmul _ _ V w)).trans (hApp_zsmul _ _ (𝟙 V) b))))))) ?_
  refine (map_add (ConcreteCategory.hom (PresheafOfModules.Hom.app
    (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1)) V)) _ _).trans ?_
  refine congrArg₂ (fun ξ ξ' => ξ + ξ') ?_ ?_
  · rw [dgTensor_d_unit.{t, v, u, z} M N n V w]
    exact (gradedCast_smul_unit.{t, v, u, z} M N (n + 1) i (n + i + 1) (add_right_comm n 1 i) V _
      b).symm
  · refine Eq.trans (map_zsmul (ConcreteCategory.hom (PresheafOfModules.Hom.app
        (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1)) V))
      (Int.negOnePow n : ℤ) _) ?_
    exact congrArg (fun ξ => (Int.negOnePow n : ℤ) • ξ)
      (gradedCast_smul_unit.{t, v, u, z} M N n (i + 1) (n + i + 1) (add_assoc n i 1).symm V w
        _).symm

/-- **The right differential graded `B`-module `M ⊗_A N`**, for `M` a right differential graded
`A`-module and `N` a differential graded `(A, B)`-bimodule: the complex of the relative tensor
product, acted on by `B` through the right action of the bimodule. -/
noncomputable def dgTensorRight : DifferentialGradedModule.{t, max u v z, max u v z} B where
  complex := dgTensor M N.toLeftDifferentialGradedModule
  mul n i := (gradedTensorRight (gP M) N.toGradedBimodule).smulBil n i
  mul_assoc := (gradedTensorRight (gP M) N.toGradedBimodule).smul_mul
  mul_one := (gradedTensorRight (gP M) N.toGradedBimodule).smul_one
  leibniz n i U z b := by
    have : PresheafOfModules.IsLocallySurjective J
        (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule n) :=
      PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
        (α := 𝟙 (toRingCat J Osharp).obj) _
    refine Stacks.eq_of_forall_lift
      (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule
        (n + i + 1)).isSheaf.isSeparated
      (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule n) z _ _ ?_
    intro V f w hw
    change restr (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1)).val f _
      = restr (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1)).val f _
    refine Eq.trans ((restr_app ((dgTensor M N.toLeftDifferentialGradedModule).d (n + i)
        (n + i + 1)).val f _).symm.trans
      (congrArg (PresheafOfModules.Hom.app ((dgTensor M N.toLeftDifferentialGradedModule).d
          (n + i) (n + i + 1)).val V)
        ((GradedModule.smul_restr (gradedTensorRight (gP M) N.toGradedBimodule) n i f z b).trans
          (congrArg (fun ξ => (gradedTensorRight (gP M) N.toGradedBimodule).smul n i V ξ
            (restr (B.complex.X i).val f b)) hw.symm)))) ?_
    refine Eq.trans (dgTensorRight_leibniz_unit M N n i V w
      (restr (B.complex.X i).val f b)) ?_
    refine Eq.trans ?_ (restr_add
      (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1)).val f _ _).symm
    refine congrArg₂ (fun ξ ξ' => ξ + ξ') ?_ ?_
    · refine Eq.trans ?_ (restr_gradedCast M N (add_right_comm n 1 i) f _).symm
      refine congrArg (gradedCast
        (fun q => (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule q).val.obj V)
        (add_right_comm n 1 i)) ?_
      refine Eq.trans ?_ ((GradedModule.smul_restr
        (gradedTensorRight (gP M) N.toGradedBimodule) (n + 1) i f _ b).symm)
      exact congrArg (fun ξ => (gradedTensorRight (gP M) N.toGradedBimodule).smul (n + 1) i V ξ
          (restr (B.complex.X i).val f b))
        ((congrArg (PresheafOfModules.Hom.app
            ((dgTensor M N.toLeftDifferentialGradedModule).d n (n + 1)).val V) hw).trans
          (restr_app ((dgTensor M N.toLeftDifferentialGradedModule).d n (n + 1)).val f z))
    · refine Eq.trans ?_ (restr_zsmul
        (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule (n + i + 1)).val f
        (Int.negOnePow n : ℤ) _).symm
      refine congrArg (fun ξ => (Int.negOnePow n : ℤ) • ξ) ?_
      refine Eq.trans ?_ (restr_gradedCast M N (add_assoc n i 1).symm f _).symm
      refine congrArg (gradedCast
        (fun q => (gradedTensor (gP M) N.toGradedBimodule.toLeftGradedModule q).val.obj V)
        (add_assoc n i 1).symm) ?_
      refine Eq.trans ?_ ((GradedModule.smul_restr
        (gradedTensorRight (gP M) N.toGradedBimodule) n (i + 1) f z _).symm)
      exact congrArg₂ (fun ξ ξ' => (gradedTensorRight (gP M) N.toGradedBimodule).smul n (i + 1) V
        ξ ξ') hw (restr_app (B.complex.d i (i + 1)).val f b)

/-- The complex underlying the right differential graded `B`-module `M ⊗_A N` is the tensor
product complex of `M` with the left differential graded `A`-module underlying `N`. -/
@[simp]
theorem dgTensorRight_complex :
    (dgTensorRight M N).complex = dgTensor M N.toLeftDifferentialGradedModule := rfl

/-- **The right action of `B` on a local section `x ⊗ y` of `M ⊗_A N`**: it is `x ⊗ (y b)`. -/
@[simp]
theorem dgTensorRight_mul_tmul (n i : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : ((gP M).piece p.1.1).val.obj X)
    (y : (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val.obj X)
    (b : (B.complex.X i).val.obj X) :
    ((dgTensorRight M N).mul n i).app X
        (tmul (gP M) N.toGradedBimodule.toLeftGradedModule n p X x y) b =
      tmul (gP M) N.toGradedBimodule.toLeftGradedModule (n + i) (actIndex p i (n + i) rfl) X x
        ((N.rightMul p.1.2 i).app X y b) :=
  gradedTensorRight_smul_tmul (gP M) N.toGradedBimodule n i p X x y b

/-- **The differential of `M ⊗_A N` on a local section `x ⊗ y`**: it is
`dx ⊗ y + (-1)^{deg x} x ⊗ dy`. -/
@[simp]
theorem dgTensorRight_d_tmul (n : ℤ) (p : TensorIndex n) (X : Cᵒᵖ)
    (x : ((gP M).piece p.1.1).val.obj X)
    (y : (N.toGradedBimodule.toLeftGradedModule.piece p.1.2).val.obj X) :
    PresheafOfModules.Hom.app ((dgTensorRight M N).complex.d n (n + 1)).val X
        (tmul (gP M) N.toGradedBimodule.toLeftGradedModule n p X x y) =
      tmul (gP M) N.toGradedBimodule.toLeftGradedModule (n + 1) (tensorIndexShiftLeft p) X
          ((M.complex.d p.1.1 (p.1.1 + 1)).val.app X x) y +
        (Int.negOnePow p.1.1 : ℤ) •
          tmul (gP M) N.toGradedBimodule.toLeftGradedModule (n + 1) (tensorIndexShiftRight p) X x
            ((N.complex.d p.1.2 (p.1.2 + 1)).val.app X y) := by
  refine (dgTensor_d_unit M N n X (tmulPre (gP M) N.toGradedBimodule n p X x y)).trans ?_
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app
      (gradedTensorUnit (gP M) N.toGradedBimodule.toLeftGradedModule (n + 1)) X)
    (dgTensorDiffPre_tmulPre M N n p X x y)) ?_
  rw [map_add, map_zsmul]
  rfl

end Sheafify

section MorphismLeibniz

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {C' : Type u} [Category.{v} C'] {K : GrothendieckTopology C'}
  [K.HasSheafCompose (forget₂ CommRingCat.{max u v z} RingCat.{max u v z})]
  {Psharp : Sheaf K CommRingCat.{max u v z}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{max u v z}]
  [HasWeakSheafify K AddCommGrpCat.{max u v z}]
  {A' B' : DifferentialGradedAlgebra.{max u v z, max u v z} (toRingCat K Psharp)}
  (M' : DifferentialGradedModule.{max u v z, max u v z, max u v z} A')
  (N' : DifferentialGradedBimodule.{max u v z, max u v z, max u v z} A' B')
  (hP : Presheaf.IsSheaf K
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))

include hP

/-- **The morphism-level signed Leibniz rule for the right action of `B` on `M ⊗_A N`**: the
form an additive lax monoidal functor transports. -/
theorem smulSheafLeibniz_dgTensorRight (n i : ℤ) :
    DifferentialGradedModule.SmulSheafLeibniz (A := B')
      (dgTensorRight.{max u v z, v, u, z} M' N').complex
      (DifferentialGradedModule.smulSheaf (dgTensorRight.{max u v z, v, u, z} M' N')) n i :=
  DifferentialGradedModule.smulSheafLeibniz_complex
    (dgTensorRight.{max u v z, v, u, z} M' N') hP n i

end MorphismLeibniz

end RelativeTensor

end SheafOfModules

section UniverseWitness

open SheafOfModules SheafOfModules.RelativeTensor

/-- The module universe of `SheafOfModules.RelativeTensor.dgTensorRight` is not the site's:
here it is `max u v (u + 1)`, strictly larger. Only `z := max u v` was available while the
construction was stated at `max u v`, so this is what the generalization buys, and it fails
again if the generalization is lost. The level is named at the application because
`max u v (u + 1)` normalizes to `max (u + 1) v`, which no longer has `max u v` as a prefix for
the level unifier to match. -/
noncomputable example {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v (u + 1)}]
    [HasWeakSheafify J AddCommGrpCat.{max u v (u + 1)}]
    {A B : DifferentialGradedAlgebra.{t, max u v (u + 1)} (toRingCat J Osharp)}
    (M : DifferentialGradedModule.{t, max u v (u + 1), max u v (u + 1)} A)
    (N : DifferentialGradedBimodule.{t, max u v (u + 1), max u v (u + 1)} A B) :
    DifferentialGradedModule.{t, max u v (u + 1), max u v (u + 1)} B :=
  dgTensorRight.{t, v, u, u + 1} M N

end UniverseWitness
