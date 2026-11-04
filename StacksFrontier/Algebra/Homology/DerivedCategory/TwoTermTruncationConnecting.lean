module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation

/-!
# The connecting map of the truncation triangle of an object with two cohomology objects

Let `Φ : D⁺(A) ⥤ D⁺(B)` be a triangulated functor and `X` an object of `D⁺(A)`. The truncation
triangle `τ^{<1} X ⟶ X ⟶ τ^{≥1} X ⟶ (τ^{<1} X)[1]` of the canonical t-structure, carried by `Φ`,
has a long exact cohomology sequence, whose connecting map in degree one is a map
`H¹(Φ(τ^{≥1} X)) ⟶ H²(Φ(τ^{<1} X))`. When `X` has cohomology only in degrees `0` and `1`, its two
truncations are its cohomology objects placed in a single degree, and the connecting map reads

`H⁰(Φ(H¹(X)[0])) ⟶ H²(Φ(H⁰(X)[0]))`.

This file constructs that map for every `X`, as a natural transformation of functors
`D⁺(A) ⥤ B` (`DerivedCategory.Plus.truncationConnecting`): on an arbitrary `X` it is built from
the truncation triangle of `τ^{<2} X` and the truncation maps, so that no invertibility is needed
to define it. When `X` is concentrated in degrees `0` and `1` and `H²(Φ(X)) = 0`, it is an
epimorphism (`DerivedCategory.Plus.epi_truncationConnecting_app`).

## Main definitions

* `DerivedCategory.Plus.truncationConnecting`: the natural transformation
  `H⁰(Φ(H¹(-)[0])) ⟶ H²(Φ(H⁰(-)[0]))`.

## Main results

* `DerivedCategory.Plus.epi_truncationConnecting_app`: it is an epimorphism at an object with
  cohomology in degrees `0` and `1` whose image has vanishing `H²`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

universe v v' u u' w w'

namespace DerivedCategory.Plus

variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
  (Φ : Plus A ⥤ Plus B) [Φ.CommShift ℤ] [Φ.IsTriangulated]

/-- The connecting map `H¹(Φ(τ^{≥1} τ^{<2} X)) ⟶ H²(Φ(τ^{<1} τ^{<2} X))` of the truncation
triangle of `τ^{<2} X` carried by `Φ`, as a natural transformation. -/
def truncationTriangleδ :
    TStructure.t.truncGELT 1 2 ⋙ Φ ⋙ homologyFunctor B 1 ⟶
      TStructure.t.truncLT 2 ⋙ TStructure.t.truncLT 1 ⋙ Φ ⋙ homologyFunctor B 2 where
  app X := (homologyFunctor B 0).homologySequenceδ
    (Φ.mapTriangle.obj ((TStructure.t.triangleLTGE 1).obj ((TStructure.t.truncLT 2).obj X)))
    1 2 rfl
  naturality _ _ f := (homologyFunctor B 0).homologySequenceδ_naturality
    (Φ.mapTriangle.map ((TStructure.t.triangleLTGE 1).map ((TStructure.t.truncLT 2).map f)))
    1 2 rfl

/-- The identification `H⁰(Φ(H¹(X)[0])) ≅ H¹(Φ(τ^{≥1} τ^{<2} X))`, natural in `X`. -/
def truncationConnectingSourceIso :
    homologyFunctor A 1 ⋙ singleFunctor A 0 ⋙ Φ ⋙ homologyFunctor B 0 ≅
      TStructure.t.truncGELT 1 2 ⋙ Φ ⋙ homologyFunctor B 1 :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft (homologyFunctor A 1)
      (singleFunctorCompHomologyFunctorShiftIsoOfEq Φ 0 1 1 (by omega)).symm ≪≫
    (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerRight (truncGELTIsoHomologyFunctorCompSingleFunctor 1).symm
      (Φ ⋙ homologyFunctor B 1)

/-- The map `τ^{<1} τ^{<2} X ⟶ τ^{<1} X ⟶ τ^{≥0} τ^{<1} X ≅ H⁰(X)[0]`, natural in `X`. -/
def truncationConnectingTargetMap :
    TStructure.t.truncLT 2 ⋙ TStructure.t.truncLT 1 ⟶ homologyFunctor A 0 ⋙ singleFunctor A 0 :=
  Functor.whiskerRight (TStructure.t.truncLTι 2) (TStructure.t.truncLT 1) ≫
    (Functor.leftUnitor _).hom ≫ Functor.whiskerLeft (TStructure.t.truncLT 1)
      (TStructure.t.truncGEπ 0) ≫ (Functor.rightUnitor _).inv ≫
    (truncGELTIsoHomologyFunctorCompSingleFunctor 0).hom

/-- **The connecting map of the truncation triangle**, `H⁰(Φ(H¹(X)[0])) ⟶ H²(Φ(H⁰(X)[0]))`,
natural in `X`: the connecting map of the truncation triangle of `τ^{<2} X`, read through
`H¹(X)[-1] ≅ τ^{≥1} τ^{<2} X` and followed by `τ^{<1} τ^{<2} X ⟶ τ^{<1} X ⟶ τ^{≥0} τ^{<1} X ≅
H⁰(X)[0]`. -/
def truncationConnecting :
    homologyFunctor A 1 ⋙ singleFunctor A 0 ⋙ Φ ⋙ homologyFunctor B 0 ⟶
      homologyFunctor A 0 ⋙ singleFunctor A 0 ⋙ Φ ⋙ homologyFunctor B 2 :=
  (truncationConnectingSourceIso Φ).hom ≫ truncationTriangleδ Φ ≫
    Functor.whiskerRight (truncationConnectingTargetMap (A := A)) (Φ ⋙ homologyFunctor B 2) ≫
    (Functor.associator _ _ _).hom

omit [Φ.IsTriangulated] in
/-- The component of `truncationConnecting Φ` at `X` is the composite of the components at `X` of
`truncationConnectingSourceIso Φ`, `truncationTriangleδ Φ` and the image under `Φ` and `H²` of
`truncationConnectingTargetMap`. -/
theorem truncationConnecting_app (X : Plus A) :
    (truncationConnecting Φ).app X = (truncationConnectingSourceIso Φ).hom.app X ≫
      (truncationTriangleδ Φ).app X ≫
        (homologyFunctor B 2).map (Φ.map ((truncationConnectingTargetMap (A := A)).app X)) := by
  simp [truncationConnecting]

/-- For `X` with cohomology only in degrees `0` and `1`, the map
`τ^{<1} τ^{<2} X ⟶ H⁰(X)[0]` is an isomorphism. -/
theorem isIso_truncationConnectingTargetMap_app (X : Plus A) [X.IsGE 0] [X.IsLE 1] :
    IsIso ((truncationConnectingTargetMap (A := A)).app X) := by
  have hι : IsIso ((TStructure.t.truncLTι 2).app X) :=
    (TStructure.t.isLE_iff_isIso_truncLTι_app 1 2 rfl X).1 inferInstance
  have h₁ : IsIso ((TStructure.t.truncLT 1).map ((TStructure.t.truncLTι 2).app X)) :=
    Functor.map_isIso _ _
  simp only [truncationConnectingTargetMap, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Category.id_comp]
  have : TStructure.t.IsGE X 0 := inferInstance
  have h₂ : IsIso ((TStructure.t.truncGEπ 0).app ((TStructure.t.truncLT 1).obj X)) :=
    inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (@IsIso.comp_isIso _ _ _ _ _ _ _ (IsIso.id _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ h₂ inferInstance))

/-- For `X` with cohomology only in degrees `0` and `1` and `H²(Φ(X)) = 0`, the component of
`truncationConnecting Φ` at `X` is an epimorphism. -/
theorem epi_truncationConnecting_app (X : Plus A) [X.IsGE 0] [X.IsLE 1]
    (hX : IsZero ((homologyFunctor B 2).obj (Φ.obj X))) :
    Epi ((truncationConnecting Φ).app X) := by
  have hι : IsIso ((TStructure.t.truncLTι 2).app X) :=
    (TStructure.t.isLE_iff_isIso_truncLTι_app 1 2 rfl X).1 inferInstance
  let T := Φ.mapTriangle.obj ((TStructure.t.triangleLTGE 1).obj ((TStructure.t.truncLT 2).obj X))
  have hZ : IsZero ((homologyFunctor B 2).obj T.obj₂) :=
    hX.of_iso ((homologyFunctor B 2).mapIso
      (Φ.mapIso (@asIso _ _ _ _ ((TStructure.t.truncLTι 2).app X) hι)))
  have hδ : Epi ((truncationTriangleδ Φ).app X) :=
    ((homologyFunctor B 0).homologySequence_exact₁ T
      (Φ.map_distinguished _ (TStructure.t.triangleLTGE_distinguished 1 _)) 1 2 rfl).epi_f
      (hZ.eq_of_tgt _ _)
  have := isIso_truncationConnectingTargetMap_app (A := A) X
  rw [truncationConnecting_app]
  infer_instance

end DerivedCategory.Plus

end
