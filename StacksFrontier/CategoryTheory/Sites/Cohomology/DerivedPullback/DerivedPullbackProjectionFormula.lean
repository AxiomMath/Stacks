module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomLeftAdjointTotal
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorAssociativity
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorCommShift
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction

/-!
# The derived projection formula from the module-level one

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi whose pullback of modules is
isomorphic to a functor `G` (by `e : f^* ≅ G`) having an exact left adjoint `E`, as extension by
zero along an étale morphism. Then `E_D ⊣ Lf^*` on unbounded derived categories, through
`Lf^* ≅ G_D`. If the module-level projection maps `E(A ⊗ G M) ⟶ E A ⊗ M` (for `E ⊣ G` and the
comparison of Stacks 03EL transported along `e`) are invertible, then so are the derived ones
`E_D(Z ⊗^L Lf^*M) ⟶ E_D Z ⊗^L M`, formed with the isomorphism of Stacks 07A4.

The proof works on a model `Z = Q W` (any complex `W`) and `M = Q P` with `P` K-flat with flat
terms: there the derived projection map is computed by the right K-flat comparisons of
Stacks 06YU and the projection map on total complexes. The input on the derived side is a form of
Stacks 07A4 against a K-flat right factor and an arbitrary left one
(`derivedPullbackTensorIso_hom_app_comp_comparisonRight`), obtained from its value on pairs of
models by naturality along a K-flat resolution of the left factor.

## Main results

In the namespace `Stacks.Cohomology.DerivedPullbackOfToposHom`:

* `isIso_leftAdjointProjectionMap_mapDerivedCategory`.
* `derivedPullbackTensorIso_hom_app_comp_comparisonRight`.
* `leftDerivedIsoMapDerivedCategoryOfIso_hom_app_Q`: `Lf^* ≅ G_D` on the image of a complex.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

universe u v w d

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- **The unit of the derived adjunction at the image of a complex** is the image of the
degreewise unit, read through the comparisons `Q ⋙ L_D ≅ L_c ⋙ Q` and `Q ⋙ R_D ≅ R_c ⋙ Q`. -/
theorem mapDerivedCategory_unit_app_Q (adj : L ⊣ R) (K : CochainComplex C ℤ) :
    adj.mapDerivedCategory.unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app K) ≫
        R.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app K) := by
  rw [Adjunction.mapDerivedCategory, Adjunction.localization_unit_app]
  rfl

end CategoryTheory.Adjunction


namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {Xs : AlgebraicGeometry.RingedSite.{u, v, w}}
  [HasSheafify Xs.J AddCommGrpCat.{w}] [Xs.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (AlgebraicGeometry.RingedSite.Modules.{u, v, w} Xs)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Xs.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} Xs.O).obj M).Additive]
  [∀ (K L : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, v, w} Xs) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Xs.O)
      (ComplexShape.up ℤ)]
  (T : DerivedTensorProduct.{u, v, w, d} Xs)

/-- The right K-flat comparison is natural in the left complex. -/
theorem comparisonRight_naturality_left
    {K K' L : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u, v, w} Xs) ℤ}
    (a : K ⟶ K') (hL : IsKFlat Xs.O L) :
    (T.tensor.map (DerivedCategory.Q.map a)).app (DerivedCategory.Q.obj L) ≫
        (T.comparisonRight K' L hL).hom =
      (T.comparisonRight K L hL).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap a (𝟙 L)
          (Stacks.SheafOfModules.Tensor.sheafTensor Xs.O) (ComplexShape.up ℤ)) := by
  simpa using T.comparisonRight_naturality a (𝟙 L) hL hL

end Stacks.SheafOfModules.DerivedTensorProduct

namespace Stacks.Homology
universe w₁ w₂ v₁ v₂ u₁ u₂
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- The chase behind `leftDerivedIsoMapDerivedCategoryOfIso_hom_app_Q`. -/
private theorem iota_chase {C : Type*} [Category C] {LQ LQh GQ GQh GhQh FhQh QF QG QhG : C}
    {A : LQ ⟶ GQ} {a : LQ ⟶ LQh} {b : LQh ⟶ GQh} {c : GQh ⟶ GhQh} {d : GhQh ⟶ FhQh}
    {g : FhQh ⟶ QF} {k : QF ⟶ QG} {m : QG ⟶ GQ} {a' : GQ ⟶ GQh} {a'' : GQh ⟶ GQ}
    {fG : GQ ⟶ QG} {qi : QG ⟶ QhG} {mh : QhG ⟶ GhQh} {dq : QhG ⟶ FhQh} {qh : QhG ⟶ QG}
    {ki : QG ⟶ QF}
    (hn : a ≫ b = A ≫ a') (hfh : c = a'' ≫ fG ≫ qi ≫ mh) (h1 : a' ≫ a'' = 𝟙 _)
    (hmd : mh ≫ d = dq) (hq : dq ≫ g = qh ≫ ki) (hqi : qi ≫ qh = 𝟙 _) (hk : ki ≫ k = 𝟙 _)
    (h3 : fG ≫ m = 𝟙 _) :
    A = (a ≫ (b ≫ c ≫ d) ≫ g) ≫ k ≫ m := by
  simp only [Category.assoc]
  rw [reassoc_of% hn, hfh]
  simp only [Category.assoc]
  rw [reassoc_of% h1, reassoc_of% hmd, reassoc_of% hq, reassoc_of% hqi,
    reassoc_of% hk, h3, Category.comp_id]

/-- The isomorphism `LF ≅ G_D` of `leftDerivedIsoMapDerivedCategoryOfIso`, on the image of an
object of the homotopy category, recovers the comparison `α`. -/
theorem leftDerivedIsoMapDerivedCategoryOfIso_hom_app_Qh
    (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (e : F ≅ G) (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (leftDerivedIsoMapDerivedCategoryOfIso F G LF α e).hom.app (DerivedCategory.Qh.obj K) ≫
        G.mapDerivedCategoryFactorsh.hom.app K ≫
          DerivedCategory.Qh.map ((mapHomotopyCategoryIso e.symm (ComplexShape.up ℤ)).hom.app K) =
      α.app K := by
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) G.mapDerivedCategory
    (G.mapDerivedCategoryFactorsh ≪≫
      Functor.isoWhiskerRight (mapHomotopyCategoryIso e.symm (ComplexShape.up ℤ))
        DerivedCategory.Qh)
  have h := Functor.leftDerivedNatTrans_app LF G.mapDerivedCategory α
    (G.mapDerivedCategoryFactorsh ≪≫
      Functor.isoWhiskerRight (mapHomotopyCategoryIso e.symm (ComplexShape.up ℤ))
        DerivedCategory.Qh).hom (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (𝟙 _) K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, NatTrans.id_app, Category.comp_id] at h
  exact h
end Stacks.Homology

namespace Stacks.Cohomology.DerivedPullbackOfToposHom
universe c c'
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy
variable {X : RingedTopos.{u, c, u}} {Y : RingedTopos.{u, c', u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)}
  [hGa : G.Additive] [hGl : PreservesFiniteLimits G] [hGc : PreservesFiniteColimits G]
  (e : f.toModulesHom.pullbackModules ≅ G)

/-- The comparison `Lf^*(QK) ⟶ Q(f^*K)` for an arbitrary complex `K`; for `K` K-flat with flat
terms it is the isomorphism `flatPullbackIso`. -/
def derivedPullbackQComparison
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (derivedPullback f).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((pullbackComplex f).obj K) :=
  (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
    (derivedPullbackComparison f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
          ((pullbackComplex f).obj K)


/-- **`Lf^* ≅ G_D` on the image of a complex** `K`: the comparison `Lf^*(QK) ⟶ Q(f^*K)`, then
`e : f^* ≅ G` degreewise, then `Q(G K) ≅ G_D(QK)`. -/
theorem leftDerivedIsoMapDerivedCategoryOfIso_hom_app_Q
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso f.toModulesHom.pullbackModules G
        (derivedPullback f) (derivedPullbackComparison f) e).hom.app (DerivedCategory.Q.obj K) =
      derivedPullbackQComparison f K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) ≫
          G.mapDerivedCategoryFactors.inv.app K := by
  have h := Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso_hom_app_Qh
    f.toModulesHom.pullbackModules G (derivedPullback f) (derivedPullbackComparison f) e
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  have hn : (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
        (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso f.toModulesHom.pullbackModules G
            (derivedPullback f) (derivedPullbackComparison f) e).hom.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) =
      (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso f.toModulesHom.pullbackModules G
          (derivedPullback f) (derivedPullbackComparison f) e).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map
        ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) :=
    (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso f.toModulesHom.pullbackModules G
        (derivedPullback f) (derivedPullbackComparison f) e).hom.naturality _
  have hfh := G.mapDerivedCategoryFactorsh_hom_app K
  have hq : DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app K)) ≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
          ((pullbackComplex f).obj K) =
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).hom.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app K) :=
    DerivedCategory.quotientCompQhIso_hom_naturality _
  have h1 : G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
      G.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have h3 : G.mapDerivedCategoryFactors.hom.app K ≫ G.mapDerivedCategoryFactors.inv.app K = 𝟙 _ :=
    Iso.hom_inv_id_app _ _
  have hmd : DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
      DerivedCategory.Qh.map
        ((Stacks.Homology.mapHomotopyCategoryIso e.symm (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app K)) := by
    rw [← Functor.map_comp]
    congr 1
  have hk :
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K) =
          𝟙 _ := by
    rw [← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      Iso.inv_hom_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id]
  have hqi := (DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).inv_hom_id_app
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  rw [derivedPullbackQComparison, ← h]
  exact Stacks.Homology.iota_chase hn hfh h1 hmd hq hqi hk h3

/-- **Stacks 03EL at the curried tensor bifunctor**, as an isomorphism of the two uncurried
functors `f^*(- ⊗ -)` and `f^*(-) ⊗ f^*(-)`. -/
def pullbackTensorIsoUncurried :
    Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
        f.toModulesHom.pullbackModules ≅
      f.toModulesHom.pullbackModules.prod f.toModulesHom.pullbackModules ⋙
        Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O) :=
  NatIso.ofComponents (fun AB => (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).app AB)
    (fun {_ _} ab => Stacks.SheafOfModules.pullbackTensorIso_hom_naturality_map
      f.toModulesHom ab.1 ab.2)

/-- On a K-flat complex with flat terms, `flatPullbackIso` is the comparison
`derivedPullbackQComparison`. -/
theorem flatPullbackIso_hom_eq_derivedPullbackQComparison
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i)) :
    (flatPullbackIso f K hK hflat).hom = derivedPullbackQComparison f K := rfl

private theorem nat3_chase {C : Type*} [Category C] {P0 P1 P2 P3 Q0 Q1 Q2 Q3 : C}
    {x : P0 ⟶ Q0} {a' : Q0 ⟶ Q1} {b' : Q1 ⟶ Q2} {c' : Q2 ⟶ Q3} {a : P0 ⟶ P1} {b : P1 ⟶ P2}
    {c : P2 ⟶ P3} {y : P1 ⟶ Q1} {z : P2 ⟶ Q2} {w : P3 ⟶ Q3}
    (hD : x ≫ a' = a ≫ y) (hC : y ≫ b' = b ≫ z) (hX : z ≫ c' = c ≫ w) :
    x ≫ a' ≫ b' ≫ c' = (a ≫ b ≫ c) ≫ w := by
  rw [reassoc_of% hD, reassoc_of% hC, hX]
  simp only [Category.assoc]

/-- The comparison `Lf^*(QK) ⟶ Q(f^*K)` is natural in the complex `K`. -/
theorem derivedPullbackQComparison_naturality
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (a : K ⟶ L) :
    (derivedPullback f).map (DerivedCategory.Q.map a) ≫ derivedPullbackQComparison f L =
      derivedPullbackQComparison f K ≫ DerivedCategory.Q.map ((pullbackComplex f).map a) := by
  have hY := DerivedCategory.quotientCompQhIso_inv_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) a
  have hX := DerivedCategory.quotientCompQhIso_hom_naturality
    (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    ((pullbackComplex f).map a)
  have hC : (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) ≫
        (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) =
      (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((pullbackComplex f).map a)) :=
    (derivedPullbackComparison f).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)
  have hD : (derivedPullback f).map (DerivedCategory.Q.map a) ≫
        (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app L) =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
        (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hY]
  unfold derivedPullbackQComparison
  exact nat3_chase hD hC hX

/-- The chase of `derivedPullbackTensorIso_hom_app_comp_comparisonRight`. -/
private theorem gmf_chase {C : Type*} [Category C] {SK SR TK TR : C}
    (x : SR ≅ SK) {y : TR ⟶ TK} {lK : SK ⟶ TK} {lR : SR ⟶ TR} {rK : SK ⟶ TK}
    {rR : SR ⟶ TR} (hl : x.hom ≫ lK = lR ≫ y) (hr : x.hom ≫ rK = rR ≫ y) (h : lR = rR) :
    lK = rK :=
  (cancel_epi x.hom).1 (by rw [hl, hr, h])

section Projection

variable {E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)}
  [E.Additive] (adj : E ⊣ G)

/-- Stacks 03EL for `f`, transported to the functor `G ≅ f^*`. -/
abbrev pullbackTensorIsoOfIso :
    Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙ G ≅
      G.prod G ⋙ Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O) :=
  PullbackInternalHom.tensorIsoOfNatIsoRight _ _ e.symm (pullbackTensorIsoUncurried f)

variable (hπ : ∀ A M, IsIso (PullbackInternalHom.leftAdjointProjectionMap adj
    (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (pullbackTensorIsoOfIso f e) A M))




/-- The chase of `unit_comp_map_projectionTotalIso`, on one summand. -/
private theorem cl_chase {C : Type*} [Category C]
    {S0 S1 S2 S3 S4 S5 S6 T1 T2 T3 T4 U : C}
    {i0 : S0 ⟶ S1} {ηT : S1 ⟶ S2} {gPi : S2 ⟶ S3} {ei : S3 ⟶ S4} {el : S4 ⟶ S5} {tt : S5 ⟶ S6}
    {η0 : S0 ⟶ T1} {gEi : T1 ⟶ S2} {gπ : T1 ⟶ U} {gi' : U ⟶ S3} {tη : S0 ⟶ T2}
    {m1 : T2 ⟶ T3} {m2 : T3 ⟶ T4} {m3 : T4 ⟶ U} {ei' : U ⟶ T4} {fi' : T4 ⟶ S4}
    {m2' : T4 ⟶ T3} {ι2 : T3 ⟶ S5} {ep : T3 ⟶ T2} {ι3 : T2 ⟶ S6} {rr : S1 ⟶ S6} {j1 : T2 ⟶ T2}
    (hu : i0 ≫ ηT = η0 ≫ gEi) (hPi : gEi ≫ gPi = gπ ≫ gi')
    (hpi : η0 ≫ gπ = tη ≫ m1 ≫ m2 ≫ m3) (he : gi' ≫ ei = ei' ≫ fi') (hme : m3 ≫ ei' = 𝟙 _)
    (h03 : fi' ≫ el = m2' ≫ ι2) (hmm : m2 ≫ m2' = 𝟙 _) (hT : ι2 ≫ tt = ep ≫ ι3)
    (hpair : m1 ≫ ep = 𝟙 _) (hR : i0 ≫ rr = tη ≫ j1 ≫ ι3) (hj : j1 = 𝟙 _) :
    i0 ≫ ηT ≫ gPi ≫ ei ≫ el ≫ tt = i0 ≫ rr := by
  rw [hR, hj, Category.id_comp, reassoc_of% hu, reassoc_of% hPi, ← Category.assoc η0,
    hpi]
  simp only [Category.assoc]
  rw [reassoc_of% he, reassoc_of% hme, reassoc_of% h03, reassoc_of% hmm, hT, reassoc_of% hpair]

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] hGl hGc in
/-- **The unit against the projection map on total complexes**: `η ≫ G(Π)` followed by the
comparison of Stacks 03EL transported to `G` is `Tot(η ⊗ 1)`. -/
theorem unit_comp_map_projectionTotalIso
    (W : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ℤ)
    (P : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) ℤ) :
    (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app (HomologicalComplex.mapBifunctor W
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) ≫
      (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (PullbackInternalHom.projectionTotalIso adj _ _ (pullbackTensorIsoOfIso f e) hπ W P).hom ≫
      (NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app _ ≫
      (pullbackTensorTotalComplexIso f
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P).hom ≫
      HomologicalComplex.mapBifunctorMap
        ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app _)
        ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app P)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) =
      HomologicalComplex.mapBifunctorMap
        ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app W)
        (𝟙 ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  refine HomologicalComplex.mapBifunctor.hom_ext (K₁ := W)
    (K₂ := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (F := Stacks.SheafOfModules.Tensor.sheafTensor X.O) (c := ComplexShape.up ℤ)
    (fun p q hpq => ?_)
  simp only [HomologicalComplex.comp_f]
  have hηf : ∀ (Z : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ℤ) (m : ℤ),
      ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app Z).f m = adj.unit.app (Z.X m) :=
    fun Z m => by simp [Adjunction.mapHomologicalComplex]
  have hu : HomologicalComplex.ιMapBifunctor W ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p q n hpq ≫
      ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app (HomologicalComplex.mapBifunctor W
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))).f n =
      adj.unit.app _ ≫ G.map (E.map (HomologicalComplex.ιMapBifunctor W
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p q n hpq)) := by
    rw [hηf]
    exact adj.unit.naturality _
  have hPi : G.map (E.map (HomologicalComplex.ιMapBifunctor W
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p q n hpq)) ≫
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (PullbackInternalHom.projectionTotalIso adj _ _ (pullbackTensorIsoOfIso f e) hπ W
          P).hom).f n =
      G.map (PullbackInternalHom.leftAdjointProjectionMap adj _ _ (pullbackTensorIsoOfIso f e)
          (W.X p) (P.X q)) ≫
        G.map (HomologicalComplex.ιMapBifunctor
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p q n hpq) := by
    rw [Functor.mapHomologicalComplex_map_f, ← G.map_comp,
      PullbackInternalHom.ι_projectionTotalIso_hom, G.map_comp]
  have hpi := PullbackInternalHom.unit_comp_map_leftAdjointProjectionMap adj _ _
    (pullbackTensorIsoOfIso f e) (W.X p) (P.X q)
  rw [PullbackInternalHom.tensorIsoOfNatIsoRight_inv_app] at hpi
  have he := e.inv.naturality (HomologicalComplex.ιMapBifunctor
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P
    (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p q n hpq)
  have h03 := Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_hom f.toModulesHom
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P p q n hpq
  have hmm := (pullbackTensorIsoUncurried f).inv_hom_id_app ((E.obj (W.X p)), P.X q)
  have hT := (HomologicalComplex.ι_mapBifunctorMap
    ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app
      ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W))
    ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app P)
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p q n hpq).trans
      (Category.assoc _ _ _).symm
  have hpair : ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (e.inv.app (E.obj (W.X p)))).app
        (G.obj (P.X q)) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (f.toModulesHom.pullbackModules.obj (E.obj (W.X p)))).map
        (e.inv.app (P.X q)) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map (e.hom.app (E.obj (W.X p)))).app
        (f.toModulesHom.pullbackModules.obj (P.X q)) ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (G.obj (E.obj (W.X p)))).map
        (e.hom.app (P.X q)) = 𝟙 _ := by
    rw [PullbackInternalHom.bifunctor_map_comp_map, Iso.inv_hom_id_app, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hR := HomologicalComplex.ι_mapBifunctorMap
    ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app W)
    (𝟙 ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p q n hpq
  rw [hηf] at hR
  exact cl_chase hu hPi hpi he (Iso.hom_inv_id_app _ _) h03 hmm hT
    ((Category.assoc _ _ _).trans hpair) hR
    ((congrArg (PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      (PresheafOfModules.tensorHom_id (O := X.O.obj) _ _)).trans
        (CategoryTheory.Functor.map_id _ _))

end Projection


private theorem gmf_lchase {C : Type*} [Category C] {A0 A1 A2 A3 A4 B0 B1 B2 B3 B4 : C}
    {x : A0 ⟶ B0} {μK : B0 ⟶ B1} {μR : A0 ⟶ A1} {t1 : A1 ⟶ B1} {a1K : B1 ⟶ B2}
    {a1R : A1 ⟶ A2} {t2 : A2 ⟶ B2} {a2K : B2 ⟶ B3} {a2R : A2 ⟶ A3} {t3 : A3 ⟶ B3}
    {cK : B3 ⟶ B4} {cR : A3 ⟶ A4} {y : A4 ⟶ B4}
    (n1 : x ≫ μK = μR ≫ t1) (n2 : t1 ≫ a1K = a1R ≫ t2) (n3 : t2 ≫ a2K = a2R ≫ t3)
    (n4 : t3 ≫ cK = cR ≫ y) :
    x ≫ μK ≫ (a1K ≫ a2K) ≫ cK = (μR ≫ (a1R ≫ a2R) ≫ cR) ≫ y := by
  simp only [Category.assoc]
  rw [reassoc_of% n1, reassoc_of% n2, reassoc_of% n3, n4]

section GMF

variable (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)

/-- The left side of `derivedPullbackTensorIso_hom_app_comp_comparisonRight`. -/
private abbrev gmfLeft
    (K P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :=
    (derivedPullbackTensorIso f TX TY).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ≫
      ((TX.tensor.map (derivedPullbackQComparison f K)).app
          ((derivedPullback f).obj (DerivedCategory.Q.obj P)) ≫
        (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).map
          (derivedPullbackQComparison f P)) ≫
        (TX.comparisonRight ((pullbackComplex f).obj K) ((pullbackComplex f).obj P)
          (kFlat_pullbackComplex' f P hP hflatP)).hom

/-- The right side of `derivedPullbackTensorIso_hom_app_comp_comparisonRight`. -/
private abbrev gmfRight
    (K P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :=
      (derivedPullback f).map (TY.comparisonRight K P hP).hom ≫
        derivedPullbackQComparison f (HomologicalComplex.mapBifunctor K P
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f K P).hom

private theorem gmfLeft_eq_gmfRight_of_kFlat
    (R P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hR : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) R)
    (hflatR : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (R.X i))
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    gmfLeft f TX TY R P hP hflatP = gmfRight f TY R P hP hflatP := by
  have hmodel := derivedPullbackTensorIso_hom_app_model_comp f TX TY R P hR hP hflatR hflatP
  rw [← TX.comparisonRight_eq_comparison _ _ (kFlat_pullbackComplex' f R hR hflatR)
      (kFlat_pullbackComplex' f P hP hflatP),
    ← TY.comparisonRight_eq_comparison R P hR hP] at hmodel
  replace hmodel : (derivedPullbackTensorIso f TX TY).hom.app
        (DerivedCategory.Q.obj R, DerivedCategory.Q.obj P) ≫
      ((TX.tensor.map (derivedPullbackQComparison f R)).app
          ((derivedPullback f).obj (DerivedCategory.Q.obj P)) ≫
        (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj R))).map
          (derivedPullbackQComparison f P)) ≫
        (TX.comparisonRight ((pullbackComplex f).obj R) ((pullbackComplex f).obj P)
          (kFlat_pullbackComplex' f P hP hflatP)).hom =
      (derivedPullback f).map (TY.comparisonRight R P hP).hom ≫
        derivedPullbackQComparison f (HomologicalComplex.mapBifunctor R P
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f R P).hom :=
    hmodel.trans (Category.assoc _ _ _)
  exact hmodel

private theorem gmfLeft_naturality
    {R K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (s : R ⟶ K)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    (derivedPullback f).map ((TY.tensor.map (DerivedCategory.Q.map s)).app
        (DerivedCategory.Q.obj P)) ≫ gmfLeft f TX TY K P hP hflatP =
      gmfLeft f TX TY R P hP hflatP ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap ((pullbackComplex f).map s)
          (𝟙 ((pullbackComplex f).obj P)) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ)) := by
  have n1 := PullbackInternalHom.uncurry_natTrans_app_fst TY.tensor (derivedPullback f)
    (derivedPullback f) (derivedPullback f) TX.tensor (derivedPullbackTensorIso f TX TY).hom
    (DerivedCategory.Q.map s) (DerivedCategory.Q.obj P)
  have n2 : (TX.tensor.map ((derivedPullback f).map (DerivedCategory.Q.map s))).app
        ((derivedPullback f).obj (DerivedCategory.Q.obj P)) ≫
      (TX.tensor.map (derivedPullbackQComparison f K)).app
        ((derivedPullback f).obj (DerivedCategory.Q.obj P)) =
      (TX.tensor.map (derivedPullbackQComparison f R)).app _ ≫
        (TX.tensor.map (DerivedCategory.Q.map ((pullbackComplex f).map s))).app _ := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, derivedPullbackQComparison_naturality,
      Functor.map_comp, NatTrans.comp_app]
  have n3 := ((TX.tensor.map (DerivedCategory.Q.map ((pullbackComplex f).map s))).naturality
    (derivedPullbackQComparison f P)).symm
  have n4 : (TX.tensor.map (DerivedCategory.Q.map ((pullbackComplex f).map s))).app
        (DerivedCategory.Q.obj ((pullbackComplex f).obj P)) ≫
      (TX.comparisonRight ((pullbackComplex f).obj K) ((pullbackComplex f).obj P)
        (kFlat_pullbackComplex' f P hP hflatP)).hom =
      (TX.comparisonRight ((pullbackComplex f).obj R) ((pullbackComplex f).obj P)
        (kFlat_pullbackComplex' f P hP hflatP)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap ((pullbackComplex f).map s)
          (𝟙 ((pullbackComplex f).obj P))
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
    TX.comparisonRight_naturality_left ((pullbackComplex f).map s)
      (kFlat_pullbackComplex' f P hP hflatP)
  exact gmf_lchase n1 n2 n3 n4

private theorem gmfRight_naturality
    {R K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (s : R ⟶ K)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    (derivedPullback f).map ((TY.tensor.map (DerivedCategory.Q.map s)).app
        (DerivedCategory.Q.obj P)) ≫ gmfRight f TY K P hP hflatP =
      gmfRight f TY R P hP hflatP ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap ((pullbackComplex f).map s)
          (𝟙 ((pullbackComplex f).obj P)) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (ComplexShape.up ℤ)) := by
  have m1 : (derivedPullback f).map ((TY.tensor.map (DerivedCategory.Q.map s)).app
        (DerivedCategory.Q.obj P)) ≫ (derivedPullback f).map (TY.comparisonRight K P hP).hom =
      (derivedPullback f).map (TY.comparisonRight R P hP).hom ≫
        (derivedPullback f).map (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap s (𝟙 P)
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))) :=
    ((derivedPullback f).map_comp _ _).symm.trans
      ((congrArg (derivedPullback f).map (TY.comparisonRight_naturality_left s hP)).trans
        ((derivedPullback f).map_comp _ _))
  have m2 := derivedPullbackQComparison_naturality f
    (HomologicalComplex.mapBifunctorMap s (𝟙 P) (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ))
  have m3 := ((DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map
    (pullbackTensorTotalComplexIso_hom_naturality f s (𝟙 P)))).trans
      (DerivedCategory.Q.map_comp _ _)
  rw [(pullbackComplex f).map_id] at m3
  exact nat3_chase m1 m2 m3

/-- **Stacks 07A4 against a K-flat right factor**: for an arbitrary complex `K` and a K-flat
complex `P` with flat terms, the isomorphism of Stacks 07A4 at `(QK, QP)`, followed by the
comparisons `Lf^* ⟶ Q f^*` and the right K-flat comparison, is `Lf^*` of the right K-flat
comparison followed by `Lf^* ⟶ Q f^*` and the comparison of Stacks 03EL. -/
theorem derivedPullbackTensorIso_hom_app_comp_comparisonRight
    (K P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    (derivedPullbackTensorIso f TX TY).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ≫
      ((TX.tensor.map (derivedPullbackQComparison f K)).app
          ((derivedPullback f).obj (DerivedCategory.Q.obj P)) ≫
        (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).map
          (derivedPullbackQComparison f P)) ≫
        (TX.comparisonRight ((pullbackComplex f).obj K) ((pullbackComplex f).obj P)
          (kFlat_pullbackComplex' f P hP hflatP)).hom =
      (derivedPullback f).map (TY.comparisonRight K P hP).hom ≫
        derivedPullbackQComparison f (HomologicalComplex.mapBifunctor K P
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f K P).hom:= by
  obtain ⟨R, s, hR, hflatR, hs, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize Y.O K
  have : IsIso (DerivedCategory.Q.map s) := Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) s
    (by rwa [HomologicalComplex.mem_quasiIso_iff])
  exact gmf_chase ((derivedPullback f).mapIso
    ((TY.tensor.mapIso (asIso (DerivedCategory.Q.map s))).app (DerivedCategory.Q.obj P)))
    (gmfLeft_naturality f TX TY s P hP hflatP) (gmfRight_naturality f TY s P hP hflatP)
    (gmfLeft_eq_gmfRight_of_kFlat f TX TY R P hR hflatR hP hflatP)

private theorem cancel3 {C : Type*} [Category C] {A B B' D : C} {a : A ⟶ B} {b : B ⟶ B'}
    {i : B' ⟶ D} {h' : D ⟶ B'} (h : i ≫ h' = 𝟙 _) : (a ≫ b ≫ i) ≫ h' = a ≫ b := by
  rw [Category.assoc, Category.assoc, h, Category.comp_id]

private theorem inv_chase {C : Type*} [Category C] {A B Z V : C}
    {ih : A ⟶ B} {fg : B ⟶ V} {al : A ⟶ Z} {qh : Z ⟶ V} {qi : V ⟶ Z} {ii : B ⟶ A}
    (h : ih ≫ fg = al ≫ qh) (hq : qh ≫ qi = 𝟙 _) (hi : ii ≫ ih = 𝟙 _) :
    ii ≫ al = fg ≫ qi := by
  rw [← Category.comp_id al, ← hq, ← reassoc_of% h, reassoc_of% hi]

/-- The chase of `pullbackTensorIsoOfIso_derived_hom_app_comp_comparisonRight`. -/
private theorem gmfG_chase {C : Type*} [Category C]
    {S S1 S2 S3 S3' S4 S4' S5 S5' S6 Z Z' W0 W1 W2 V : C}
    {iinv : S ⟶ S1} {mu : S1 ⟶ S2} {a1 : S2 ⟶ S3'} {a2 : S3' ⟶ S3} {b1 : S3 ⟶ S4'}
    {b2 : S4' ⟶ S4} {c : S4 ⟶ Z}
    {d1 : S2 ⟶ S5'} {d2 : S5' ⟶ S5} {g1 : S5 ⟶ S6} {g2 : S6 ⟶ S4} {c' : S5 ⟶ Z'} {t : Z' ⟶ Z}
    {l : S1 ⟶ W1} {al : W1 ⟶ W2}
    {q : W2 ⟶ Z'} {m : S ⟶ W0} {ii : W0 ⟶ W1} {fg : W0 ⟶ V} {qe : V ⟶ W2}
    (hab : a1 ≫ a2 ≫ b1 ≫ b2 = d1 ≫ d2 ≫ g1 ≫ g2) (hcn : g1 ≫ g2 ≫ c = c' ≫ t)
    (hgmf : mu ≫ (d1 ≫ d2) ≫ c' = l ≫ al ≫ q)
    (hιn : iinv ≫ l = m ≫ ii) (hιT : ii ≫ al = fg ≫ qe) :
    (iinv ≫ mu ≫ a1 ≫ a2) ≫ (b1 ≫ b2) ≫ c = m ≫ fg ≫ qe ≫ q ≫ t := by
  simp only [Category.assoc] at hgmf ⊢
  rw [reassoc_of% hab, hcn, reassoc_of% hgmf, reassoc_of% hιn, reassoc_of% hιT]

omit hGl hGc in
include e in
/-- The degreewise image under `G ≅ f^*` of a K-flat complex with flat terms is K-flat. -/
theorem kFlat_mapHomologicalComplex_of_iso
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  CochainComplex.KFlatBifunctor.KFlat.of_iso _ (kFlat_pullbackComplex' f P hP hflatP)
    ((NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app P)

/-- **Stacks 07A4 transported to `G ≅ f^*`, against a K-flat right factor.** -/
theorem pullbackTensorIsoOfIso_derived_hom_app_comp_comparisonRight
    (K P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    (PullbackInternalHom.tensorIsoOfNatIsoRight TY.tensor TX.tensor
        (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso f.toModulesHom.pullbackModules G
            (derivedPullback f) (derivedPullbackComparison f) e).symm
        (derivedPullbackTensorIso f TX TY)).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj P) ≫
      ((TX.tensor.map (G.mapDerivedCategoryFactors.hom.app K)).app
          (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        (TX.tensor.obj
            (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))).map
          (G.mapDerivedCategoryFactors.hom.app P)) ≫
        (TX.comparisonRight ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (kFlat_mapHomologicalComplex_of_iso f e P hP hflatP)).hom =
      G.mapDerivedCategory.map (TY.comparisonRight K P hP).hom ≫
        G.mapDerivedCategoryFactors.hom.app (HomologicalComplex.mapBifunctor K P
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app _) ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f K P).hom≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K)
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
  have hι := fun L => leftDerivedIsoMapDerivedCategoryOfIso_hom_app_Q f e L
  have hιf : ∀ L, (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso
      f.toModulesHom.pullbackModules G
      (derivedPullback f) (derivedPullbackComparison f) e).hom.app (DerivedCategory.Q.obj L) ≫
        G.mapDerivedCategoryFactors.hom.app L =
      derivedPullbackQComparison f L ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app L) :=
    fun L => by rw [hι L]; exact cancel3 (Iso.inv_hom_id_app _ _)
  have hab := (PullbackInternalHom.bifunctor_map_comp_map TX.tensor _ _ _ _).trans
    ((congrArg₂ (fun x y => (TX.tensor.map x).app _ ≫ (TX.tensor.obj _).map y) (hιf K)
      (hιf P)).trans
      (PullbackInternalHom.bifunctor_map_comp_map TX.tensor _ _ _ _).symm)
  have hcn := TX.comparisonRight_naturality
    ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K)
    ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app P)
    (kFlat_pullbackComplex' f P hP hflatP) (kFlat_mapHomologicalComplex_of_iso f e P hP hflatP)
  have hgmf := derivedPullbackTensorIso_hom_app_comp_comparisonRight f TX TY K P hP hflatP
  have hιn := (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso
      f.toModulesHom.pullbackModules G
      (derivedPullback f) (derivedPullbackComparison f) e).inv.naturality
    (TY.comparisonRight K P hP).hom
  have hιT : (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso f.toModulesHom.pullbackModules G
      (derivedPullback f) (derivedPullbackComparison f) e).inv.app _ ≫
        derivedPullbackQComparison f (HomologicalComplex.mapBifunctor K P
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) =
      G.mapDerivedCategoryFactors.hom.app _ ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app _) := by
    refine inv_chase (hιf _) ?_ ((Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso
      f.toModulesHom.pullbackModules G (derivedPullback f) (derivedPullbackComparison f)
        e).inv_hom_id_app _)
    rw [← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      Iso.hom_inv_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app,
      CategoryTheory.Functor.map_id]
  rw [PullbackInternalHom.tensorIsoOfNatIsoRight_hom_app]
  exact gmfG_chase hab hcn hgmf hιn.symm hιT

end GMF

section Main

variable (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)
  {E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)}
  [hEa : E.Additive] [hEl : PreservesFiniteLimits E] [hEc : PreservesFiniteColimits E]
  (adj : E ⊣ G)
  (hπ : ∀ A M, IsIso (PullbackInternalHom.leftAdjointProjectionMap adj
    (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
    (pullbackTensorIsoOfIso f e) A M))

private theorem main_chase_a {C : Type*} [Category C]
    {A1 A2 A3 A4 A5 A6 B0 B1 B2 B3 : C}
    {gΦ : A1 ⟶ A2} {μhom : A2 ⟶ B0} {k : B0 ⟶ B1}
    {g1 : A1 ⟶ A3} {g2 : A3 ⟶ A4} {g3 : A4 ⟶ A5} {g4 : A5 ⟶ A6} {g5 : A6 ⟶ A2}
    {μhom' : A6 ⟶ B2} {t5 : B2 ⟶ B0} {kk : B2 ⟶ B1} {g4' : A6 ⟶ A5} {fgT : A5 ⟶ B3}
    {qμ : B3 ⟶ B1}
    (Fphi : gΦ = g1 ≫ g2 ≫ g3 ≫ g4 ≫ g5) (Fnat : g5 ≫ μhom = μhom' ≫ t5) (Fk : t5 ≫ k = kk)
    (Fgmf : μhom' ≫ kk = g4' ≫ fgT ≫ qμ) (Fcy : g4 ≫ g4' = 𝟙 _) :
    gΦ ≫ μhom ≫ k = g1 ≫ g2 ≫ g3 ≫ fgT ≫ qμ := by
  rw [Fphi]
  simp only [Category.assoc]
  rw [reassoc_of% Fnat, Fk, Fgmf, reassoc_of% Fcy]

private theorem main_chase_b {C : Type*} [Category C]
    {A0 A1 A3 A4 A5 B1 B3 B4 B5 : C}
    {uT : A0 ⟶ A1} {g1 : A1 ⟶ A3} {g2 : A3 ⟶ A4} {g3 : A4 ⟶ A5} {fgT : A5 ⟶ B3}
    {qμ : B3 ⟶ B1} {ψ : A0 ⟶ B4} {uQT : B4 ⟶ A3} {qη : B4 ⟶ B5} {fGinv : B5 ⟶ A4}
    {gfe : A4 ⟶ A3} {fGET : A4 ⟶ B5} {qGPi : B5 ⟶ B3} {qTot : B4 ⟶ B1}
    (Funitnat : ψ ≫ uQT = uT ≫ g1) (Funit : uQT = qη ≫ fGinv ≫ gfe) (Ffe : gfe ≫ g2 = 𝟙 _)
    (Ffg : g3 ≫ fgT = fGET ≫ qGPi) (Ffgi : fGinv ≫ fGET = 𝟙 _) (Fcl : qη ≫ qGPi ≫ qμ = qTot) :
    uT ≫ g1 ≫ g2 ≫ g3 ≫ fgT ≫ qμ = ψ ≫ qTot := by
  rw [← reassoc_of% Funitnat, Funit]
  simp only [Category.assoc]
  rw [reassoc_of% Ffe, reassoc_of% Ffg, reassoc_of% Ffgi, Fcl]

private theorem main_chase_c {C : Type*} [Category C] {A0 A1 A2 B0 B1 B4 : C}
    {uT : A0 ⟶ A1} {gΦ : A1 ⟶ A2} {μinv : B0 ⟶ A2} {tu : A0 ⟶ B0} (μI : A2 ≅ B0)
    (kI : B0 ≅ B1) {ψ : A0 ⟶ B4} {qTot : B4 ⟶ B1}
    (S : uT ≫ gΦ ≫ μI.hom ≫ kI.hom = ψ ≫ qTot)
    (Frhs : tu ≫ kI.hom = ψ ≫ qTot) (Finv : μinv ≫ μI.hom = 𝟙 _) :
    uT ≫ gΦ = tu ≫ μinv := by
  rw [← cancel_mono (μI.hom ≫ kI.hom)]
  simp only [Category.assoc]
  rw [reassoc_of% Finv, Frhs, S]


/-- **The projection map on derived categories at a pair of models**: for a complex `W` on the
source and a K-flat complex `P` with flat terms on the target,
`a_!(QW ⊗^L a^*QP) ≅ a_!QW ⊗^L QP`, through the right K-flat comparisons and the projection map
on total complexes. -/
def projectionDerivedIso
    (W : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    E.mapDerivedCategory.obj ((TX.tensor.obj (DerivedCategory.Q.obj W)).obj
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P))) ≅
      (TY.tensor.obj (E.mapDerivedCategory.obj (DerivedCategory.Q.obj W))).obj
        (DerivedCategory.Q.obj P) :=
  E.mapDerivedCategory.mapIso (((TX.tensor.obj (DerivedCategory.Q.obj W)).mapIso
      (G.mapDerivedCategoryFactors.app P) ≪≫
    TX.comparisonRight W ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (kFlat_mapHomologicalComplex_of_iso f e P hP hflatP) :
      _ ≅ DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor W
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)))) ≪≫
  E.mapDerivedCategoryFactors.app (HomologicalComplex.mapBifunctor W
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) ≪≫
  DerivedCategory.Q.mapIso
    (PullbackInternalHom.projectionTotalIso adj _ _ (pullbackTensorIsoOfIso f e) hπ W P) ≪≫
  (TY.comparisonRight ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P hP).symm ≪≫
  ((TY.tensor.mapIso (E.mapDerivedCategoryFactors.app W)).app (DerivedCategory.Q.obj P)).symm

private theorem unit_chase {C : Type*} [Category C] {A B D D' : C}
    {qη : A ⟶ B} {fi : B ⟶ D} {gi : D ⟶ D'} {gh : D' ⟶ D} {fh : D ⟶ B}
    (h1 : gi ≫ gh = 𝟙 _) (h2 : fi ≫ fh = 𝟙 _) : (qη ≫ fi ≫ gi) ≫ gh ≫ fh = qη := by
  simp only [Category.assoc]
  rw [reassoc_of% h1, h2, Category.comp_id]

private theorem rhs_chase {A B C' : Type*} [Category A] [Category B] [Category C']
    (T : A ⥤ B ⥤ C')
    {A0 A1 A2 A3 : A} {B0 B1 : B} {Z Z' : C'}
    {uW : A0 ⟶ A1} {gfe : A1 ⟶ A2} {fg : A2 ⟶ A3} {qη : A0 ⟶ A3} (h1 : uW ≫ gfe ≫ fg = qη)
    {b : B0 ⟶ B1} {c : (T.obj A3).obj B1 ⟶ Z} {c' : (T.obj A0).obj B1 ⟶ Z'} {t : Z' ⟶ Z}
    (hcn : (T.map qη).app B1 ≫ c = c' ≫ t) :
    (T.map uW).app B0 ≫ (T.map gfe).app B0 ≫ ((T.map fg).app B0 ≫ (T.obj A3).map b) ≫ c =
      ((T.obj A0).map b ≫ c') ≫ t := by
  have h : (T.map uW).app B0 ≫ (T.map gfe).app B0 ≫ (T.map fg).app B0 = (T.map qη).app B0 := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp, h1]
  simp only [Category.assoc]
  rw [reassoc_of% h, ← (T.map qη).naturality_assoc, hcn]

/-- The comparison `Q W ⊗^L G_D(Q P) ⟶ Q Tot(W ⊗ G P)`. -/
private abbrev psiMap
    (W : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    (TX.tensor.obj (DerivedCategory.Q.obj W)).obj
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor W
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
  ((TX.tensor.obj (DerivedCategory.Q.obj W)).map (G.mapDerivedCategoryFactors.hom.app P) ≫
          (TX.comparisonRight W ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (kFlat_mapHomologicalComplex_of_iso f e P hP hflatP)).hom :
        _ ⟶ DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor W
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)))

/-- The comparison `G_D(E_D Q W) ⊗^L G_D(Q P) ⟶ Q Tot(G E W ⊗ G P)`. -/
private abbrev kMap
    (W : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    (TX.tensor.obj
        (G.mapDerivedCategory.obj (E.mapDerivedCategory.obj (DerivedCategory.Q.obj W)))).obj
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex X.toRingedSite.O).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W))).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
  (TX.tensor.map (G.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app W))).app
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
      (((TX.tensor.map (G.mapDerivedCategoryFactors.hom.app
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W))).app
          (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        (TX.tensor.obj (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W)))).map
          (G.mapDerivedCategoryFactors.hom.app P)) ≫
        (TX.comparisonRight ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W))
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (kFlat_mapHomologicalComplex_of_iso f e P hP hflatP)).hom)

include hπ in
/-- `G_D` applied to `projectionDerivedIso`, split into its five factors. -/
private theorem map_projectionDerivedIso_hom
    (W : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    G.mapDerivedCategory.map (projectionDerivedIso f e TX TY adj hπ W P hP hflatP).hom =
      G.mapDerivedCategory.map (E.mapDerivedCategory.map (psiMap f e TX W P hP hflatP)) ≫
        G.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app
          (HomologicalComplex.mapBifunctor W ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) ≫
        G.mapDerivedCategory.map (DerivedCategory.Q.map
          (PullbackInternalHom.projectionTotalIso adj _ _ (pullbackTensorIsoOfIso f e) hπ W
            P).hom) ≫
        G.mapDerivedCategory.map
          (TY.comparisonRight ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P hP).inv ≫
        G.mapDerivedCategory.map ((TY.tensor.map (E.mapDerivedCategoryFactors.inv.app W)).app
          (DerivedCategory.Q.obj P)) := by
  have hφ : (projectionDerivedIso f e TX TY adj hπ W P hP hflatP).hom =
      E.mapDerivedCategory.map (psiMap f e TX W P hP hflatP) ≫
      E.mapDerivedCategoryFactors.hom.app (HomologicalComplex.mapBifunctor W
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) ≫
      DerivedCategory.Q.map
        (PullbackInternalHom.projectionTotalIso adj _ _ (pullbackTensorIsoOfIso f e) hπ W P).hom ≫
      (TY.comparisonRight ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P hP).inv ≫
      (TY.tensor.map (E.mapDerivedCategoryFactors.inv.app W)).app (DerivedCategory.Q.obj P) := rfl
  rw [hφ]
  exact (G.mapDerivedCategory.map_comp _ _).trans
    (congrArg _ ((G.mapDerivedCategory.map_comp _ _).trans
    (congrArg _ ((G.mapDerivedCategory.map_comp _ _).trans
      (congrArg _ (G.mapDerivedCategory.map_comp _ _))))))

include hπ in
private theorem unit_comp_map_projectionDerivedIso_aux1
    (W : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    G.mapDerivedCategory.map (projectionDerivedIso f e TX TY adj hπ W P hP hflatP).hom ≫
      (PullbackInternalHom.tensorIsoOfNatIsoRight TY.tensor TX.tensor
      (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso f.toModulesHom.pullbackModules G
        (derivedPullback f) (derivedPullbackComparison f) e).symm
      (derivedPullbackTensorIso f TX TY)).hom.app
        (E.mapDerivedCategory.obj (DerivedCategory.Q.obj W), DerivedCategory.Q.obj P) ≫
      kMap f e TX (E := E) W P hP hflatP =
    G.mapDerivedCategory.map (E.mapDerivedCategory.map (psiMap f e TX W P hP hflatP)) ≫
        G.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app
          (HomologicalComplex.mapBifunctor W ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) ≫
        G.mapDerivedCategory.map (DerivedCategory.Q.map
          (PullbackInternalHom.projectionTotalIso adj _ _ (pullbackTensorIsoOfIso f e) hπ W
            P).hom) ≫
        G.mapDerivedCategoryFactors.hom.app (HomologicalComplex.mapBifunctor
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) ≫
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app _) ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W))
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) := by
  have hGP := kFlat_mapHomologicalComplex_of_iso f e P hP hflatP
  have Fphi := map_projectionDerivedIso_hom f e TX TY adj hπ W P hP hflatP
  have Fnat := PullbackInternalHom.uncurry_natTrans_app_fst TY.tensor G.mapDerivedCategory
    G.mapDerivedCategory G.mapDerivedCategory TX.tensor
    (PullbackInternalHom.tensorIsoOfNatIsoRight TY.tensor TX.tensor
      (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso f.toModulesHom.pullbackModules G
        (derivedPullback f) (derivedPullbackComparison f) e).symm
      (derivedPullbackTensorIso f TX TY)).hom
    (E.mapDerivedCategoryFactors.inv.app W) (DerivedCategory.Q.obj P)
  have Fk := PullbackInternalHom.bifunctor_map_inv_hom_app TX.tensor G.mapDerivedCategory
    (E.mapDerivedCategoryFactors.app W) (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
    (((TX.tensor.map (G.mapDerivedCategoryFactors.hom.app _)).app
          (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        (TX.tensor.obj (DerivedCategory.Q.obj _)).map (G.mapDerivedCategoryFactors.hom.app P)) ≫
        (TX.comparisonRight ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W))
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (kFlat_mapHomologicalComplex_of_iso f e P hP hflatP)).hom)
  have Fgmf := pullbackTensorIsoOfIso_derived_hom_app_comp_comparisonRight f e TX TY
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P hP hflatP
  have Fcy : G.mapDerivedCategory.map
        (TY.comparisonRight ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P hP).inv ≫
      G.mapDerivedCategory.map
        (TY.comparisonRight ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P hP).hom =
        𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  exact main_chase_a Fphi Fnat Fk Fgmf Fcy

include hπ in
private theorem unit_comp_map_projectionDerivedIso_aux2
    (W : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    adj.mapDerivedCategory.unit.app _ ≫
        G.mapDerivedCategory.map (E.mapDerivedCategory.map (psiMap f e TX W P hP hflatP)) ≫
        G.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app
          (HomologicalComplex.mapBifunctor W ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) ≫
        G.mapDerivedCategory.map (DerivedCategory.Q.map
          (PullbackInternalHom.projectionTotalIso adj _ _ (pullbackTensorIsoOfIso f e) hπ W
            P).hom) ≫
        G.mapDerivedCategoryFactors.hom.app (HomologicalComplex.mapBifunctor
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)) ≫
        (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app _) ≫
        DerivedCategory.Q.map (pullbackTensorTotalComplexIso f
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) P).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W))
          ((NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) =
      psiMap f e TX W P hP hflatP ≫ DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app W)
          (𝟙 ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
  have hGP := kFlat_mapHomologicalComplex_of_iso f e P hP hflatP
  have Funitnat := adj.mapDerivedCategory.unit.naturality (psiMap f e TX W P hP hflatP)
  have Funit := Adjunction.mapDerivedCategory_unit_app_Q adj (HomologicalComplex.mapBifunctor W
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))
  have Ffe : G.mapDerivedCategory.map (E.mapDerivedCategoryFactors.inv.app
        (HomologicalComplex.mapBifunctor W ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) ≫
      G.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app
        (HomologicalComplex.mapBifunctor W ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have Ffg := G.mapDerivedCategoryFactors_hom_naturality
    (PullbackInternalHom.projectionTotalIso adj _ _ (pullbackTensorIsoOfIso f e) hπ W P).hom
  have Ffgi := G.mapDerivedCategoryFactors.inv_hom_id_app
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj (HomologicalComplex.mapBifunctor W
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)))
  have Fcl := congrArg DerivedCategory.Q.map (unit_comp_map_projectionTotalIso f e adj hπ W P)
  simp only [Functor.map_comp] at Fcl
  exact main_chase_b Funitnat Funit Ffe Ffg Ffgi Fcl

private theorem unit_comp_map_projectionDerivedIso_aux3
    (W : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    (TX.tensor.map (adj.mapDerivedCategory.unit.app (DerivedCategory.Q.obj W))).app
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫ kMap f e TX (E := E) W P hP hflatP =
      psiMap f e TX W P hP hflatP ≫ DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app W)
          (𝟙 ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
  have hGP := kFlat_mapHomologicalComplex_of_iso f e P hP hflatP
  have hcn : (TX.tensor.map (DerivedCategory.Q.map
        ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app W))).app
        (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≫
        (TX.comparisonRight ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W))
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hGP).hom =
      ((TX.comparisonRight W ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) hGP).hom :
        _ ⟶ DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor W
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app W)
          (𝟙 ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) :=
    TX.comparisonRight_naturality_left _ hGP
  have h1 : adj.mapDerivedCategory.unit.app (DerivedCategory.Q.obj W) ≫
      G.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app W) ≫
        G.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app W) := by
    rw [Adjunction.mapDerivedCategory_unit_app_Q]
    exact unit_chase ((G.mapDerivedCategory.map_comp _ _).symm.trans
      ((congrArg G.mapDerivedCategory.map (Iso.inv_hom_id_app _ _)).trans
        (G.mapDerivedCategory.map_id _))) (Iso.inv_hom_id_app _ _)
  exact rhs_chase TX.tensor (b := G.mapDerivedCategoryFactors.hom.app P) h1 hcn

/-- The transpose identity for `projectionDerivedIso`. -/
theorem unit_comp_map_projectionDerivedIso
    (W : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ℤ)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) P)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (P.X i)) :
    adj.mapDerivedCategory.unit.app _ ≫
        G.mapDerivedCategory.map (projectionDerivedIso f e TX TY adj hπ W P hP hflatP).hom =
      (TX.tensor.map (adj.mapDerivedCategory.unit.app (DerivedCategory.Q.obj W))).app
          (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        (PullbackInternalHom.tensorIsoOfNatIsoRight TY.tensor TX.tensor
          (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso f.toModulesHom.pullbackModules G
            (derivedPullback f) (derivedPullbackComparison f) e).symm
          (derivedPullbackTensorIso f TX TY)).inv.app
          (E.mapDerivedCategory.obj (DerivedCategory.Q.obj W), DerivedCategory.Q.obj P) :=
  main_chase_c ((PullbackInternalHom.tensorIsoOfNatIsoRight TY.tensor TX.tensor
      (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso f.toModulesHom.pullbackModules G
        (derivedPullback f) (derivedPullbackComparison f) e).symm
      (derivedPullbackTensorIso f TX TY)).app
        (E.mapDerivedCategory.obj (DerivedCategory.Q.obj W), DerivedCategory.Q.obj P))
    ((TX.tensor.mapIso (G.mapDerivedCategory.mapIso (E.mapDerivedCategoryFactors.app W))).app
        (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≪≫
      (((TX.tensor.mapIso (G.mapDerivedCategoryFactors.app
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W))).app
          (G.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≪≫
        (TX.tensor.obj (DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W)))).mapIso
          (G.mapDerivedCategoryFactors.app P)) ≪≫
        TX.comparisonRight ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj W))
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          (kFlat_mapHomologicalComplex_of_iso f e P hP hflatP)))
    ((whisker_eq _ (unit_comp_map_projectionDerivedIso_aux1 f e TX TY adj hπ W P hP hflatP)).trans
      (unit_comp_map_projectionDerivedIso_aux2 f e TX adj hπ W P hP hflatP))
    (unit_comp_map_projectionDerivedIso_aux3 f e TX adj W P hP hflatP) (Iso.inv_hom_id_app _ _)

include hπ in
/-- **The derived projection formula from the module-level one.** Let `f` be a morphism of ringed
topoi whose pullback of modules is isomorphic to a functor `G` with an exact left adjoint `E`.
If the module-level projection maps `E(A ⊗ G M) ⟶ E A ⊗ M` are invertible, then so are the
derived ones `E_D(Z ⊗^L Lf^*M) ⟶ E_D Z ⊗^L M`, for the adjunction `E_D ⊣ Lf^*` and the
isomorphism of Stacks 07A4. -/
theorem isIso_leftAdjointProjectionMap_mapDerivedCategory
    (Z : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    IsIso (PullbackInternalHom.leftAdjointProjectionMap
      (adj.mapDerivedCategory.ofNatIsoRight
        (Stacks.Homology.leftDerivedIsoMapDerivedCategoryOfIso f.toModulesHom.pullbackModules G
          (derivedPullback f) (derivedPullbackComparison f) e).symm)
      TY.tensor TX.tensor (derivedPullbackTensorIso f TX TY) Z M) := by
  rw [PullbackInternalHom.isIso_leftAdjointProjectionMap_ofNatIsoRight_iff]
  obtain ⟨P, ⟨hP, hflatP⟩, ⟨eP⟩⟩ := exists_flatKFlatComplexes_iso (Y := Y) M
  have := PullbackInternalHom.isIso_leftAdjointProjectionMap_of_unit_comp _ _ _ _
    (projectionDerivedIso f e TX TY adj hπ (DerivedCategory.Q.objPreimage Z) P hP hflatP)
    (unit_comp_map_projectionDerivedIso f e TX TY adj hπ _ P hP hflatP)
  exact PullbackInternalHom.isIso_leftAdjointProjectionMap_of_iso _ _ _ _
    (DerivedCategory.Q.objObjPreimageIso Z).symm eP.symm

end Main

end Stacks.Cohomology.DerivedPullbackOfToposHom
end
