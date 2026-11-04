module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraBridge

/-!
# Pseudofunctoriality of the pullback of a sheaf of graded algebras on schemes

For morphisms of schemes `k : X ⟶ Y` and `h : Y ⟶ Z` and a sheaf `G` of `ℤ`-graded
`𝒪_Z`-algebras, `Stacks.RingedSpace.pullbackGradedAlgebra` gives `k^*h^*G` and `(k ≫ h)^*G`. This
file identifies them as sheaves of graded algebras, degreewise by the pseudofunctoriality
isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackComp k h`, and likewise `f^*G` with `f'^*G`
for `f = f'` by `AlgebraicGeometry.Scheme.Modules.pullbackCongr`. Both identifications preserve the
units, by the general fact that an isomorphism of sheaves of graded algebras does.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso`:
  `k^*h^*G ≅ (k ≫ h)^*G`.
* `Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso`:
  `f^*G ≅ f'^*G` for `f = f'`.

## Main results

* `SheafOfModules.GradedAlgebra.iso_hom_app_one_eval`: an isomorphism of sheaves of graded
  algebras carries the unit to the unit.
* `Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.mulSheaf_comp_pullbackComp`: the
  multiplicativity of `pullbackComp`, at the level of morphisms.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open scoped TensorProduct

universe u

namespace SheafOfModules.GradedAlgebra

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {A B : GradedAlgebra.{u, u} R}

/-- A homomorphism of sheaves of graded algebras carries heterogeneously equal sections of two
pieces whose degrees are equal to heterogeneously equal sections. -/
theorem heq_hom_app (f : A ⟶ B) {n m : ℤ} (h : n = m) (U : Cᵒᵖ) {a : (A.piece n).val.obj U}
    {b : (A.piece m).val.obj U} (hab : HEq a b) :
    HEq ((f.app n).val.app U a) ((f.app m).val.app U b) := by
  subst h
  rw [eq_of_heq hab]

/-- An isomorphism of sheaves of graded algebras carries the unit section to the unit section. -/
theorem iso_hom_app_one_eval (e : A ≅ B) (U : Cᵒᵖ) :
    (e.hom.app 0).val.app U (A.one.eval U) = B.one.eval U := by
  set u := (e.hom.app 0).val.app U (A.one.eval U)
  set x := (e.inv.app 0).val.app U (B.one.eval U)
  have hx : (e.hom.app 0).val.app U x = B.one.eval U := by
    show ((e.inv ≫ e.hom).app 0).val.app U (B.one.eval U) = _
    rw [e.inv_hom_id]
    rfl
  have h2 : HEq ((e.hom.app (0 + 0)).val.app U ((A.mul 0 0).app U (A.one.eval U) x))
      ((e.hom.app 0).val.app U x) := heq_hom_app e.hom (zero_add 0) U (A.one_mul 0 U x)
  rw [e.hom.map_mul 0 0 U, hx] at h2
  exact eq_of_heq ((B.mul_one 0 U u).symm.trans h2)

end SheafOfModules.GradedAlgebra

namespace Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp

open Stacks.AlgebraicGeometry.Tag07ZGTwist Stacks.AlgebraicGeometry.TwistMulLeg

variable {X Y Z : Scheme.{u}}
  (G : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Z.toRingedSpace))

/-- The pseudofunctoriality isomorphism `k^*h^* ≅ (k ≫ h)^*` intertwines the multiplications of
`k^*h^*G` and `(k ≫ h)^*G`, as morphisms out of the tensor product sheaf. -/
theorem mulSheaf_comp_pullbackComp (k : X ⟶ Y) (h : Y ⟶ Z) (i j : ℤ) :
    SheafOfModules.GradedAlgebra.mulSheaf (pullbackGradedAlgebra k.toLRSHom.toShHom
        (pullbackGradedAlgebra h.toLRSHom.toShHom G)) i j ≫
        (Scheme.Modules.pullbackComp k h).hom.app (G.piece (i + j)) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          ((((Scheme.Modules.pullbackComp k h).hom.app (G.piece i)),
            ((Scheme.Modules.pullbackComp k h).hom.app (G.piece j))) : (_, _) ⟶ (_, _)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf
          (pullbackGradedAlgebra (k ≫ h).toLRSHom.toShHom G) i j := by
  rw [mulSheaf_pullbackGradedAlgebra_eq_pbMul k, mulSheaf_pullbackGradedAlgebra_eq_pbMul h,
    mulSheaf_pullbackGradedAlgebra_eq_pbMul (k ≫ h)]
  exact mul_pullbackComp k h _

omit G in
/-- A degreewise family of morphisms between sheaves of graded algebras on a scheme that commutes
with the multiplications `mulSheaf` preserves products of homogeneous local sections. -/
theorem map_mul_of_mulSheaf_comp_tensorSheafMap {W : Scheme.{u}}
    {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf W.toRingedSpace)}
    (e : ∀ n : ℤ, A.piece n ⟶ B.piece n) (i j : ℤ)
    (hsq : SheafOfModules.GradedAlgebra.mulSheaf A i j ≫ e (i + j) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        ((e i, e j) : (_, _) ⟶ (_, _)) ≫
        SheafOfModules.GradedAlgebra.mulSheaf B i j)
    (U : (Opens W.carrier)ᵒᵖ) (x : (A.piece i).val.obj U) (y : (A.piece j).val.obj U) :
    (e (i + j)).val.app U ((A.mul i j).app U x y) =
      (B.mul i j).app U ((e i).val.app U x) ((e j).val.app U y) := by
  refine Eq.trans (congrArg (Hom.app (e (i + j)).val U)
    (SheafOfModules.GradedAlgebra.mulSheaf_unit A i j U x y).symm) ?_
  refine Eq.trans (congrArg (fun φ => Hom.app (SheafOfModules.Hom.val φ) U
    ((tensorSheafUnit (A.piece i) (A.piece j)).app U (x ⊗ₜ y))) hsq) ?_
  refine Eq.trans (congrArg (Hom.app (SheafOfModules.GradedAlgebra.mulSheaf B i j).val U)
    (Stacks.RingedSpace.tensorSheaf_map_unit_tmul W.toRingedSpace (e i) (e j) U x y)) ?_
  exact SheafOfModules.GradedAlgebra.mulSheaf_unit B i j U _ _

/-- `k^*h^*G ≅ (k ≫ h)^*G` as sheaves of graded algebras, degreewise the pseudofunctoriality
isomorphism `Scheme.Modules.pullbackComp k h`. -/
def pullbackGradedAlgebraCompIso (k : X ⟶ Y) (h : Y ⟶ Z) :
    pullbackGradedAlgebra k.toLRSHom.toShHom (pullbackGradedAlgebra h.toLRSHom.toShHom G) ≅
      pullbackGradedAlgebra (k ≫ h).toLRSHom.toShHom G :=
  SheafOfModules.GradedAlgebra.isoOfPieceIso
    (fun n => (Scheme.Modules.pullbackComp k h).app (G.piece n))
    (fun i j U x y => map_mul_of_mulSheaf_comp_tensorSheafMap
      (A := pullbackGradedAlgebra k.toLRSHom.toShHom (pullbackGradedAlgebra h.toLRSHom.toShHom G))
      (B := pullbackGradedAlgebra (k ≫ h).toLRSHom.toShHom G)
      (fun n => (Scheme.Modules.pullbackComp k h).hom.app (G.piece n)) i j
      (mulSheaf_comp_pullbackComp G k h i j) U x y)

/-- The degree-`n` component of `pullbackGradedAlgebraCompIso` is `pullbackComp k h`. -/
theorem pullbackGradedAlgebraCompIso_hom_app (k : X ⟶ Y) (h : Y ⟶ Z) (n : ℤ) :
    (pullbackGradedAlgebraCompIso G k h).hom.app n =
      (Scheme.Modules.pullbackComp k h).hom.app (G.piece n) := rfl

/-- The degree-`n` component of the inverse of `pullbackGradedAlgebraCompIso` is the inverse of
`pullbackComp k h`. -/
theorem pullbackGradedAlgebraCompIso_inv_app (k : X ⟶ Y) (h : Y ⟶ Z) (n : ℤ) :
    (pullbackGradedAlgebraCompIso G k h).inv.app n =
      (Scheme.Modules.pullbackComp k h).inv.app (G.piece n) := rfl

/-- The comparison `k^*h^*G ≅ (k ≫ h)^*G` preserves the units. -/
theorem pullbackGradedAlgebraCompIso_one_eval (k : X ⟶ Y) (h : Y ⟶ Z)
    (U : (Opens X.carrier)ᵒᵖ) :
    ((Scheme.Modules.pullbackComp k h).hom.app (G.piece 0)).val.app U
        ((pullbackGradedAlgebra k.toLRSHom.toShHom
          (pullbackGradedAlgebra h.toLRSHom.toShHom G)).one.eval U) =
      (pullbackGradedAlgebra (k ≫ h).toLRSHom.toShHom G).one.eval U :=
  SheafOfModules.GradedAlgebra.iso_hom_app_one_eval (pullbackGradedAlgebraCompIso G k h) U

/-- `f^*G ≅ f'^*G` for `f = f'` as sheaves of graded algebras, degreewise
`Scheme.Modules.pullbackCongr`. -/
def pullbackGradedAlgebraCongrIso {f f' : X ⟶ Z} (hff : f = f') :
    pullbackGradedAlgebra f.toLRSHom.toShHom G ≅ pullbackGradedAlgebra f'.toLRSHom.toShHom G :=
  SheafOfModules.GradedAlgebra.isoOfPieceIso
    (fun n => (Scheme.Modules.pullbackCongr hff).app (G.piece n))
    (fun i j U x y => by subst hff; rfl)

/-- The degree-`n` component of `pullbackGradedAlgebraCongrIso` is `pullbackCongr`. -/
theorem pullbackGradedAlgebraCongrIso_hom_app {f f' : X ⟶ Z} (hff : f = f') (n : ℤ) :
    (pullbackGradedAlgebraCongrIso G hff).hom.app n =
      (Scheme.Modules.pullbackCongr hff).hom.app (G.piece n) := rfl

/-- The comparison `f^*G ≅ f'^*G` preserves the units. -/
theorem pullbackGradedAlgebraCongrIso_one_eval {f f' : X ⟶ Z} (hff : f = f')
    (U : (Opens X.carrier)ᵒᵖ) :
    ((Scheme.Modules.pullbackCongr hff).hom.app (G.piece 0)).val.app U
        ((pullbackGradedAlgebra f.toLRSHom.toShHom G).one.eval U) =
      (pullbackGradedAlgebra f'.toLRSHom.toShHom G).one.eval U :=
  SheafOfModules.GradedAlgebra.iso_hom_app_one_eval (pullbackGradedAlgebraCongrIso G hff) U

end Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp

end
