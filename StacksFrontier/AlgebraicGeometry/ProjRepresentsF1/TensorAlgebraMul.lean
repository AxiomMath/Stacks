module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Multiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraDegreeZeroIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGradedAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraFunctoriality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences

/-!
# A homomorphism out of a tensor algebra, degree by degree

Let `T(F)` be the tensor algebra of a sheaf of modules, as the bundle
`SheafOfModules.TensorExteriorSymmetricAlgebras` presents it, and let `g : T(F) ⟶ B` be a
homomorphism of sheaves of graded algebras. Then `g` is an isomorphism in every positive degree
as soon as it is one in degree one and the multiplications `B₁ ⊗ B_k ⟶ B_{1+k}` of `B` are
isomorphisms. On relative `Proj`, this reduces the canonicality clause of Tag 01O4,
`Stacks.AlgebraicGeometry.ProjRepresentsF1.TwistsAreTensorPowers`, to degree zero under
generation in degree one.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.generatorMul_comp_eq_id`: multiplication by the
  degree-one generator of a tensor algebra, read through the identifications of the homogeneous
  pieces with the tensor powers, is the identity of the next tensor power.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.generatorMul_comp_app`: a homomorphism of graded
  algebras commutes with multiplication by a degree-one generator.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.generatorMul_eq`: multiplication by a degree-one
  generator is the generator tensored into the graded multiplication.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_generatorMul_tensorGenerator`: multiplication
  by the degree-one generator of a tensor algebra is an isomorphism in every positive degree.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_hom_app_succ`: a homomorphism out of a tensor
  algebra is an isomorphism in every positive degree when it is one in degree one and the
  target's multiplications by its degree-one part are isomorphisms.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.twistsAreTensorPowers_iff_isIso_app_zero`: under
  generation in degree one, `TwistsAreTensorPowers` is equivalent to invertibility of the
  comparison in degree zero.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.twistsAreTensorPowers_of_pieceZeroIsoUnit`:
  `TwistsAreTensorPowers` holds under generation in degree one when the degree-zero twist is
  identified with the structure sheaf by an identification carrying the algebra unit to `1`.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf TopologicalSpace Opposite

open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe v u w

section Abstract

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Transport of a degreewise family along an equality of degrees acts on local sections as the
corresponding transport of types. -/
private theorem eqToHom_val_app_eq_mp
    (Y : ℤ → SheafOfModules.{w} (toRingCat J Osharp)) {i j : ℤ} (h : i = j) (U : Cᵒᵖ)
    (y : (Y i).val.obj U) :
    (eqToHom (congrArg Y h)).val.app U y =
      Eq.mp (congrArg (fun k : ℤ => ((Y k).val.obj U : Type w)) h) y := by
  subst h; rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Equal morphisms of sheaves of modules act equally on a local section. -/
private theorem val_app_congr {R : Sheaf J RingCat.{w}} {X Y : SheafOfModules.{w} R}
    {a b : X ⟶ Y} (h : a = b) (U : Cᵒᵖ) (x : X.val.obj U) :
    a.val.app U x = b.val.app U x := by
  rw [h]

/-- An identity in the first variable of a bifunctor composes away. -/
private theorem mapId_app_comp {D E K : Type*} [Category D] [Category E] [Category K]
    (G : D ⥤ E ⥤ K) (X : D) {P Q : E} (g : P ⟶ Q) :
    (G.map (𝟙 X)).app P ≫ (G.obj X).map g = (G.obj X).map g := by
  rw [G.map_id, NatTrans.id_app, Category.id_comp]

/-- An identity in the second variable of a bifunctor composes away. -/
private theorem map_app_comp_mapId {D E K : Type*} [Category D] [Category E] [Category K]
    (G : D ⥤ E ⥤ K) {X Y : D} (f : X ⟶ Y) (P : E) :
    (G.map f).app P ≫ (G.obj Y).map (𝟙 P) = (G.map f).app P := by
  rw [(G.obj Y).map_id, Category.comp_id]

/-- A functor carries a composite that is an identity to an identity. -/
private theorem map_comp_eq_id {D E : Type*} [Category D] [Category E] (G : D ⥤ E) {X Y : D}
    (a : X ⟶ Y) (b : Y ⟶ X) (h : a ≫ b = 𝟙 X) :
    G.map a ≫ G.map b = 𝟙 (G.obj X) := by
  rw [← G.map_comp, h, G.map_id]

/-- A bifunctor carries a composite that is an identity to an identity, in its first variable at
a fixed second argument. -/
private theorem map_app_comp_eq_id {D E K : Type*} [Category D] [Category E] [Category K]
    (G : D ⥤ E ⥤ K) {X Y : D} (a : X ⟶ Y) (b : Y ⟶ X) (h : a ≫ b = 𝟙 X) (P : E) :
    (G.map a).app P ≫ (G.map b).app P = 𝟙 ((G.obj X).obj P) := by
  rw [← NatTrans.comp_app, ← G.map_comp, h, G.map_id, NatTrans.id_app]

variable {F : SheafOfModules.{w} (toRingCat J Osharp)}
  (B : SheafOfModules.TensorExteriorSymmetricAlgebras J F)

/-- Multiplication by the degree-one generator of a tensor algebra, read through the canonical
identifications of the homogeneous pieces with the tensor powers, is the identity of the next
tensor power. -/
public theorem generatorMul_comp_eq_id (m : ℕ)
    (hc : (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj F).map
        ((B.tensorPieceIso (m + 1)).inv) ≫
      SheafOfModules.GradedAlgebra.generatorMul (A := B.tensor)
        B.tensorGenerator ((m + 1 : ℕ) : ℤ) ≫
      eqToHom (congrArg B.tensor.piece hc) ≫ (B.tensorPieceIso (m + 2)).hom =
    𝟙 (SheafOfModules.tensorPower J F (m + 2)) := by
  refine PresheafOfModules.tensorSheaf_hom_ext fun U s x => ?_
  change (B.tensorPieceIso (m + 2)).hom.val.app U
      ((eqToHom (congrArg B.tensor.piece hc)).val.app U
        ((SheafOfModules.GradedAlgebra.generatorMul (A := B.tensor)
            B.tensorGenerator ((m + 1 : ℕ) : ℤ)).val.app U
          ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj F).map
              ((B.tensorPieceIso (m + 1)).inv)).val.app U
            ((PresheafOfModules.tensorSheafUnit F
              (SheafOfModules.tensorPower J F (m + 1))).app U (s ⊗ₜ x))))) =
    (PresheafOfModules.tensorSheafUnit F
      (SheafOfModules.tensorPower J F (m + 1))).app U (s ⊗ₜ x)
  have hmap := (val_app_congr (mapId_app_comp
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp) F
      (B.tensorPieceIso (m + 1)).inv) U _).symm.trans
    (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      Osharp _ _ (𝟙 F) (B.tensorPieceIso (m + 1)).inv U s x)
  rw [hmap,
    SheafOfModules.GradedAlgebra.generatorMul_unit,
    eqToHom_val_app_eq_mp B.tensor.piece hc]
  exact B.tensorPieceIso_mul_left m U s x

/-- Cancelling an isomorphism between two composites. -/
private theorem comp_iso_comp_inv {D : Type*} [Category D] {W X Y Z : D} (f : W ⟶ X) (e : X ≅ Y)
    (g : X ⟶ Z) : (f ≫ e.hom) ≫ (e.inv ≫ g) = f ≫ g := by
  rw [Category.assoc, ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp]

/-- A middle factor of a composite that is the identity is invertible, when the outer factors
are invertible with explicitly given inverses. -/
private theorem isIso_middle {D : Type*} [Category D] {P Q R : D} {a : P ⟶ Q} {aInv : Q ⟶ P}
    (b : Q ⟶ R) {cd : R ⟶ P} {cdInv : P ⟶ R}
    (haa' : aInv ≫ a = 𝟙 Q) (hcc : cd ≫ cdInv = 𝟙 R)
    (key : a ≫ b ≫ cd = 𝟙 P) : IsIso b := by
  have h1 : b ≫ cd = aInv := by
    calc b ≫ cd = (aInv ≫ a) ≫ (b ≫ cd) := by rw [haa', Category.id_comp]
    _ = aInv ≫ (a ≫ b ≫ cd) := by simp only [Category.assoc]
    _ = aInv := by rw [key, Category.comp_id]
  have h2 : a ≫ b = cdInv := by
    calc a ≫ b = (a ≫ b) ≫ (cd ≫ cdInv) := by rw [hcc, Category.comp_id]
    _ = (a ≫ b ≫ cd) ≫ cdInv := by simp only [Category.assoc]
    _ = cdInv := by rw [key, Category.id_comp]
  refine ⟨cd ≫ a, ?_, ?_⟩
  · calc b ≫ cd ≫ a = (b ≫ cd) ≫ a := (Category.assoc _ _ _).symm
    _ = aInv ≫ a := by rw [h1]
    _ = 𝟙 Q := haa'
  · calc (cd ≫ a) ≫ b = cd ≫ (a ≫ b) := Category.assoc _ _ _
    _ = cd ≫ cdInv := by rw [h2]
    _ = 𝟙 R := hcc

/-- Multiplication by the degree-one generator of a tensor algebra is an isomorphism in every
positive degree: tensoring the `(m+1)`-st homogeneous piece with the generating sheaf gives the
`(m+2)`-nd piece. -/
public theorem isIso_generatorMul_tensorGenerator (m : ℕ) :
    IsIso (SheafOfModules.GradedAlgebra.generatorMul (A := B.tensor)
      B.tensorGenerator ((m + 1 : ℕ) : ℤ)) := by
  have hc : (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
  refine isIso_middle
      (a := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj F).map
        ((B.tensorPieceIso (m + 1)).inv))
      (aInv := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj F).map
        ((B.tensorPieceIso (m + 1)).hom)) _
      (cd := eqToHom (congrArg B.tensor.piece hc) ≫ (B.tensorPieceIso (m + 2)).hom)
      (cdInv := (B.tensorPieceIso (m + 2)).inv ≫ eqToHom (congrArg B.tensor.piece hc.symm))
      ?_ ?_ (generatorMul_comp_eq_id B m hc)
  · exact map_comp_eq_id _ _ _ (Iso.hom_inv_id (B.tensorPieceIso (m + 1)))
  · exact Eq.trans (comp_iso_comp_inv (eqToHom (congrArg B.tensor.piece hc))
      (B.tensorPieceIso (m + 2)) (eqToHom (congrArg B.tensor.piece hc.symm)))
      (Eq.trans (eqToHom_trans _ _) (eqToHom_refl _ _))

variable {A' : SheafOfModules.GradedAlgebra.{w, w} (toRingCat J Osharp)}

/-- Multiplication by a degree-one generator commutes with a homomorphism of graded
algebras. -/
public theorem generatorMul_comp_app {M : SheafOfModules.{w} (toRingCat J Osharp)}
    {A : SheafOfModules.GradedAlgebra.{w, w} (toRingCat J Osharp)}
    (g : SheafOfModules.GradedAlgebra.Hom A A') (ι : M ⟶ A.piece 1) (k : ℤ) :
    SheafOfModules.GradedAlgebra.generatorMul ι k ≫ g.app (1 + k) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj M).map (g.app k) ≫
        SheafOfModules.GradedAlgebra.generatorMul (ι ≫ g.app 1) k := by
  refine PresheafOfModules.tensorSheaf_hom_ext fun U s y => ?_
  change (g.app (1 + k)).val.app U
      ((SheafOfModules.GradedAlgebra.generatorMul ι k).val.app U
        ((PresheafOfModules.tensorSheafUnit M (A.piece k)).app U (s ⊗ₜ y))) =
    (SheafOfModules.GradedAlgebra.generatorMul (ι ≫ g.app 1) k).val.app U
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj M).map
          (g.app k)).val.app U
        ((PresheafOfModules.tensorSheafUnit M (A.piece k)).app U (s ⊗ₜ y)))
  have hmap := (val_app_congr (mapId_app_comp
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp) M
      (g.app k)) U _).symm.trans
    (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      Osharp _ _ (𝟙 M) (g.app k) U s y)
  rw [SheafOfModules.GradedAlgebra.generatorMul_unit, hmap,
    SheafOfModules.GradedAlgebra.generatorMul_unit]
  exact g.map_mul 1 k U (ι.val.app U s) y

/-- Multiplication by a degree-one generator is the generator tensored into the graded
multiplication. -/
public theorem generatorMul_eq {M : SheafOfModules.{w} (toRingCat J Osharp)}
    (ι : M ⟶ A'.piece 1) (k : ℤ) :
    SheafOfModules.GradedAlgebra.generatorMul ι k =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).map ι).app (A'.piece k) ≫
        SheafOfModules.GradedAlgebra.mulSheaf A' 1 k := by
  refine PresheafOfModules.tensorSheaf_hom_ext fun U s y => ?_
  change (SheafOfModules.GradedAlgebra.generatorMul ι k).val.app U
      ((PresheafOfModules.tensorSheafUnit M (A'.piece k)).app U (s ⊗ₜ y)) =
    (SheafOfModules.GradedAlgebra.mulSheaf A' 1 k).val.app U
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).map ι).app
          (A'.piece k)).val.app U
        ((PresheafOfModules.tensorSheafUnit M (A'.piece k)).app U (s ⊗ₜ y)))
  have hmap := (val_app_congr (map_app_comp_mapId
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp) ι
      (A'.piece k)) U _).symm.trans
    (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      Osharp _ _ ι (𝟙 (A'.piece k)) U s y)
  rw [SheafOfModules.GradedAlgebra.generatorMul_unit, hmap,
    SheafOfModules.GradedAlgebra.mulSheaf_unit]
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Tensoring an isomorphism, given with its inverse, with the identity on the right is an
isomorphism. -/
private theorem isIso_bifunctorMapFst
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (f : M ⟶ N) (fInv : N ⟶ M) (hff : f ≫ fInv = 𝟙 M) (hff' : fInv ≫ f = 𝟙 N) :
    IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).map f).app P) :=
  ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).map fInv).app P,
    map_app_comp_eq_id _ _ _ hff P, map_app_comp_eq_id _ _ _ hff' P⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Tensoring an isomorphism, given with its inverse, with the identity on the left is an
isomorphism. -/
private theorem isIso_bifunctorMapSnd
    {M N P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp)}
    (f : M ⟶ N) (fInv : N ⟶ M) (hff : f ≫ fInv = 𝟙 M) (hff' : fInv ≫ f = 𝟙 N) :
    IsIso (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj P).map f) :=
  ⟨((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Osharp).obj P).map fInv,
    map_comp_eq_id _ _ _ hff, map_comp_eq_id _ _ _ hff'⟩

/-- Multiplication by an invertible degree-one generator is an isomorphism whenever the graded
multiplication in that bidegree is. -/
private theorem isIso_generatorMul {M : SheafOfModules.{w} (toRingCat J Osharp)}
    (ι : M ⟶ A'.piece 1) [hι : IsIso ι] (k : ℤ)
    [hmul : IsIso (SheafOfModules.GradedAlgebra.mulSheaf A' 1 k)] :
    IsIso (SheafOfModules.GradedAlgebra.generatorMul ι k) := by
  rw [generatorMul_eq]
  obtain ⟨ιInv, hιι, hιι'⟩ := hι
  exact IsIso.comp_isIso' (isIso_bifunctorMapFst (P := A'.piece k) ι ιInv hιι hιι') hmul

/-- A homomorphism out of a tensor algebra which is invertible in degree one and in degree
`m + 1` is invertible in degree `1 + (m + 1)`, provided the target's multiplication by its
degree-one part is invertible in that bidegree. -/
private theorem isIso_app_one_add (g : SheafOfModules.GradedAlgebra.Hom B.tensor A') (m : ℕ)
    [IsIso (g.app 1)] [hgm : IsIso (g.app ((m + 1 : ℕ) : ℤ))]
    [IsIso (SheafOfModules.GradedAlgebra.mulSheaf A' 1 ((m + 1 : ℕ) : ℤ))] :
    IsIso (g.app (1 + ((m + 1 : ℕ) : ℤ))) := by
  have := B.isIso_tensorGenerator
  have : IsIso (SheafOfModules.GradedAlgebra.generatorMul (A := B.tensor)
    B.tensorGenerator ((m + 1 : ℕ) : ℤ)) := isIso_generatorMul_tensorGenerator B m
  have hgg : IsIso (SheafOfModules.GradedAlgebra.generatorMul
    (B.tensorGenerator ≫ g.app 1) ((m + 1 : ℕ) : ℤ)) := isIso_generatorMul _ _
  obtain ⟨gInv, hgg', hgg''⟩ := hgm
  have : IsIso (SheafOfModules.GradedAlgebra.generatorMul (A := B.tensor)
      B.tensorGenerator ((m + 1 : ℕ) : ℤ) ≫ g.app (1 + ((m + 1 : ℕ) : ℤ))) := by
    rw [generatorMul_comp_app g B.tensorGenerator ((m + 1 : ℕ) : ℤ)]
    exact IsIso.comp_isIso' (isIso_bifunctorMapSnd (P := F)
      (g.app ((m + 1 : ℕ) : ℤ)) gInv hgg' hgg'') hgg
  exact IsIso.of_isIso_comp_left (SheafOfModules.GradedAlgebra.generatorMul (A := B.tensor)
    B.tensorGenerator ((m + 1 : ℕ) : ℤ)) _

/-- A homomorphism out of a tensor algebra is an isomorphism in every positive degree as soon as
it is an isomorphism in degree one and the target's multiplications by its degree-one part are
isomorphisms. -/
public theorem isIso_hom_app_succ (g : SheafOfModules.GradedAlgebra.Hom B.tensor A')
    (h1 : IsIso (g.app 1))
    (hmul : ∀ k : ℤ, IsIso (SheafOfModules.GradedAlgebra.mulSheaf A' 1 k)) :
    ∀ m : ℕ, IsIso (g.app ((m + 1 : ℕ) : ℤ))
  | 0 => by
      have hc : ((0 + 1 : ℕ) : ℤ) = 1 := by norm_num
      exact Eq.mpr (congrArg (fun k : ℤ => IsIso (g.app k)) hc) h1
  | (m + 1) => by
      have := h1
      have := isIso_hom_app_succ g h1 hmul m
      have := hmul ((m + 1 : ℕ) : ℤ)
      have hc : (1 : ℤ) + ((m + 1 : ℕ) : ℤ) = ((m + 1 + 1 : ℕ) : ℤ) := by push_cast; ring
      exact Eq.mpr (congrArg (fun k : ℤ => IsIso (g.app k)) hc.symm) (isIso_app_one_add B g m)

end Abstract

section Relative

open _root_.AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (TA : TensorAlgebras.{u})
  (D : TwistData A)

/-- Under generation in degree one, the canonical comparison out of the tensor algebra of a
module on relative `Proj` identified with the degree-one twist is an isomorphism in every
nonnegative degree as soon as it is one in degree zero. -/
public theorem twistsAreTensorPowersOf_iff_isIso_app_zero (hgen : IsGeneratedInDegreeOne A)
    (L : (relativeProj A).scheme.Modules) (β : L ≅ D.algebra.piece 1) :
    TwistsAreTensorPowersOf TA D L β ↔ IsIso ((twistComparisonOf TA D L β).app 0) := by
  refine ⟨fun h => h 0, fun h0 n => ?_⟩
  match n with
  | 0 => exact h0
  | (m + 1) =>
      exact isIso_hom_app_succ (TA (relativeProj A).scheme L)
        (twistComparisonOf TA D L β).toHom
        (isIso_twistComparisonOf_app_one TA D L β)
        (Stacks.AlgebraicGeometry.TwistMapsInvertible.twistData_isIso_mulSheaf D hgen 1)
        m

/-- Under generation in degree one, the canonical comparison out of the tensor algebra of a
module on relative `Proj` identified with the degree-one twist is an isomorphism in every
nonnegative degree as soon as the degree-zero twist is identified with the structure sheaf by an
identification carrying the algebra unit to `1`. -/
public theorem twistsAreTensorPowersOf_of_pieceZeroIsoUnit (hgen : IsGeneratedInDegreeOne A)
    (L : (relativeProj A).scheme.Modules) (β : L ≅ D.algebra.piece 1)
    (e : D.algebra.piece 0 ≅
      SheafOfModules.unit (relativeProj A).scheme.ringCatSheaf)
    (he : ∀ U : ((relativeProj A).scheme.Opens)ᵒᵖ,
      e.hom.val.app U (D.algebra.one.eval U) =
        (1 : (relativeProj A).scheme.ringCatSheaf.obj.obj U)) :
    TwistsAreTensorPowersOf TA D L β :=
  (twistsAreTensorPowersOf_iff_isIso_app_zero TA D hgen L β).mpr
    (SheafOfModules.GradedAlgebra.isIso_unitalHom_app_zero
      (TA (relativeProj A).scheme L).tensorPieceZeroIsoUnit
      (TA (relativeProj A).scheme L).tensorPieceZeroIsoUnit_one e he
      (twistComparisonOf TA D L β))

/-- Under generation in degree one, `TwistsAreTensorPowers` for a pair holds exactly when the
comparison is an isomorphism in degree zero. -/
public theorem twistsAreTensorPowers_iff_isIso_app_zero (hgen : IsGeneratedInDegreeOne A)
    (P : F1Pair A TA (relativeProj A).toBase) (β : P.L ≅ D.algebra.piece 1) :
    TwistsAreTensorPowers TA D P β ↔ IsIso ((pairTwistComparison TA D P β).app 0) :=
  twistsAreTensorPowersOf_iff_isIso_app_zero TA D hgen P.L β

/-- Under generation in degree one, `TwistsAreTensorPowers` holds for a pair when the degree-zero
twist is identified with the structure sheaf by an identification carrying the algebra unit to
`1`. -/
public theorem twistsAreTensorPowers_of_pieceZeroIsoUnit (hgen : IsGeneratedInDegreeOne A)
    (P : F1Pair A TA (relativeProj A).toBase) (β : P.L ≅ D.algebra.piece 1)
    (e : D.algebra.piece 0 ≅
      SheafOfModules.unit (relativeProj A).scheme.ringCatSheaf)
    (he : ∀ U : ((relativeProj A).scheme.Opens)ᵒᵖ,
      e.hom.val.app U (D.algebra.one.eval U) =
        (1 : (relativeProj A).scheme.ringCatSheaf.obj.obj U)) :
    TwistsAreTensorPowers TA D P β :=
  twistsAreTensorPowersOf_of_pieceZeroIsoUnit TA D hgen P.L β e he

end Relative

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
