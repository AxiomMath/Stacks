module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionMapAlongEquivalences
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorBraidingOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAlongASiteMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorBraidingNatTrans
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesHomEq
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-!
# The two derived readings of a morphism of ringed sites

A morphism of ringed sites `h : X ⟶ Y` (Stacks 03AD) is a morphism of ringed topoi in two ways:
as the site-presented morphism `h.toRingedToposSiteHom`, and as the morphism of the underlying
topoi with its structure map, `h.ringedToposHom`. Each reading has its own derived pullback
(Stacks 06YY), its own derived adjunction `Lh^* ⊣ Rh_*` (Stacks 07A6) and its own comparison
`Lh^*(K ⊗^L L) ≅ Lh^*K ⊗^L Lh^*L` (Stacks 07A4), constructed separately. This file identifies
them, for a site-presented morphism `g` and a morphism of topoi `f` between the same ringed topoi
together with an isomorphism `θ : g^* ≅ f^*` of their degreewise pullbacks: the two derived
pullbacks are isomorphic, and if `θ` carries the comparison of total tensor complexes of
Stacks 03EL of one to that of the other, the isomorphism carries one comparison of Stacks 07A4 to
the other. Hence the projection maps of Stacks 0B56 of the two are invertible at the same objects.
For the two readings of a morphism of ringed sites, `θ` is
`RingedSite.Hom.pullbackModulesToposIso`.

## Main definitions

* `Stacks.Cohomology.RingedSiteHomReadings.derivedPullbackIsoOfIso`: the derived pullbacks of the
  two readings, from an isomorphism `θ` of their degreewise pullbacks.
* `Stacks.Cohomology.RingedSiteHomReadings.TotalTensorCompat`: `θ` carries the comparison of total
  tensor complexes of Stacks 03EL of one reading to that of the other.

## Main results

* `Stacks.Cohomology.RingedSiteHomReadings.tensorCompat_derivedPullbackIsoOfIso`: the isomorphism
  of derived pullbacks carries the comparison of Stacks 07A4 of the site-presented reading to that
  of the topos reading.
* `Stacks.Cohomology.RingedSiteHomReadings.isIso_projectionFormulaMap_iff_of_totalTensorCompat`:
  the maps of Stacks 0B56 of the two readings are invertible at the same objects.
* `Stacks.Cohomology.RingedSiteHomReadings.isIso_projectionMap_iff_isIso_projectionFormulaMap`:
  the projection map `K ⊗^L Rh_*E ⟶ Rh_*(Lh^*K ⊗^L E)` of the site-presented reading is
  invertible exactly when the map `Rh_*E ⊗^L K ⟶ Rh_*(E ⊗^L Lh^*K)` of Stacks 0B56 of the topos
  reading is.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Prod
open Stacks.Cohomology.AbstractKunnethMap (TensorCompat TensorCompat.of_eq projectionMap)

universe u

namespace Stacks.Cohomology.RingedSiteHomReadings

-- Both derived pullbacks, `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback` and
-- `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback`, are stated for the
-- standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

/-! ### A chase on models -/

/-- **A transformation `c : P ⟶ Q` between two functors carrying comparisons built from models
carries one comparison to the other**, from the compatibility of `c` with each piece of the two
model descriptions. -/
theorem app_comp_eq_of_models {CY CX : Type*} [Category* CY] [Category* CX]
    {TY : CY × CY ⥤ CY} {TX : CX × CX ⥤ CX} {P Q : CY ⥤ CX} (c : P ⟶ Q) {A B MZ : CY}
    {A₁ B₁ A₂ B₂ MP MQ NP NQ : CX} (s : TY.obj (A, B) ⟶ MZ) (mP : P.obj MZ ⟶ MP)
    (mQ : Q.obj MZ ⟶ MQ) (βP : MP ⟶ NP) (βQ : MQ ⟶ NQ) (cmpP : TX.obj (A₁, B₁) ≅ NP)
    (cmpQ : TX.obj (A₂, B₂) ≅ NQ) (aP : P.obj A ≅ A₁) (aQ : Q.obj A ≅ A₂) (bP : P.obj B ≅ B₁)
    (bQ : Q.obj B ≅ B₂) {κa : A₁ ⟶ A₂} {κb : B₁ ⟶ B₂} {κM : MP ⟶ MQ} {κT : NP ⟶ NQ}
    (hA : c.app A ≫ aQ.hom = aP.hom ≫ κa) (hB : c.app B ≫ bQ.hom = bP.hom ≫ κb)
    (hM : c.app MZ ≫ mQ = mP ≫ κM) (hβ : κM ≫ βQ = βP ≫ κT)
    (hcmp : TX.map (κa ×ₘ κb) ≫ cmpQ.hom = cmpP.hom ≫ κT) :
    c.app (TY.obj (A, B)) ≫ (Q.map s ≫ mQ ≫ βQ ≫ cmpQ.inv ≫ TX.map (aQ.inv ×ₘ bQ.inv)) =
      (P.map s ≫ mP ≫ βP ≫ cmpP.inv ≫ TX.map (aP.inv ×ₘ bP.inv)) ≫
        TX.map (c.app A ×ₘ c.app B) := by
  have hA' := (CommSq.vert_inv ⟨hA⟩).w
  have hB' := (CommSq.vert_inv ⟨hB⟩).w
  have hcmp' := (CommSq.vert_inv ⟨hcmp⟩).w
  rw [← c.naturality_assoc, reassoc_of% hM, reassoc_of% hβ, reassoc_of% hcmp', ← TX.map_comp]
  simp only [Category.assoc, ← TX.map_comp, prod_comp, hA', hB']

/-! ### Two morphisms of ringed topoi with isomorphic pullbacks -/

section Generic

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (g : RingedToposSiteHom X Y) (f : RingedToposHom X Y)
  [(Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
    g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (θ : g.pullbackTopos ≅ f.toModulesHom.pullbackModules)

/-- The two degreewise pullbacks, followed by localization. -/
def pullbackOnHomotopyIsoOfIso :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy g ≅
      Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackOnHomotopy f :=
  Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso θ (ComplexShape.up ℤ))
    DerivedCategory.Qh

/-- **Isomorphic degreewise pullbacks have isomorphic derived pullbacks**, across the two
readings: the isomorphism of total left derived functors induced by `θ`. -/
def derivedPullbackIsoOfIso :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback g ≅
      Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f :=
  Functor.leftDerivedNatIso _ _
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison g)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))
    (pullbackOnHomotopyIsoOfIso g f θ)

/-- **`derivedPullbackIsoOfIso` is compatible with the two comparisons of Stacks 06YY**, which
characterizes it. -/
theorem derivedPullbackIsoOfIso_hom_app
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ)) :
    (derivedPullbackIsoOfIso g f θ).hom.app (DerivedCategory.Qh.obj K) ≫
        (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f).app K =
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison g).app K ≫
        (pullbackOnHomotopyIsoOfIso g f θ).hom.app K :=
  Functor.leftDerivedNatTrans_app
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback g)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f)
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullbackComparison g)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackComparison f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))
    (pullbackOnHomotopyIsoOfIso g f θ).hom K

/-- A square of a transformation `t : F ⟶ G` against two composites `F q ≫ c ≫ r` and
`G q ≫ c' ≫ r'`, from the two squares it is made of. -/
theorem app_comp_comp_comp_eq_of_squares {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (t : F ⟶ G) {Z Z' : C} {W₁ W₂ W₃ W₄ : D} (q : Z ⟶ Z')
    (c : F.obj Z' ⟶ W₁) (c' : G.obj Z' ⟶ W₂) (r : W₁ ⟶ W₃) (r' : W₂ ⟶ W₄) (m : W₁ ⟶ W₂)
    (n : W₃ ⟶ W₄) (h₁ : t.app Z' ≫ c' = c ≫ m) (h₂ : m ≫ r' = r ≫ n) :
    t.app Z ≫ G.map q ≫ c' ≫ r' = (F.map q ≫ c ≫ r) ≫ n := by
  rw [← t.naturality_assoc, reassoc_of% h₁, h₂]
  simp only [Category.assoc]

/-- **`derivedPullbackIsoOfIso` on a K-flat complex with flat terms**: after the identifications
`L(-)^*(QK) ≅ Q((-)^*K)` of Stacks 06YY for the two readings, it is `θ` in each degree. -/
theorem derivedPullbackIsoOfIso_hom_app_flatPullbackIso
    (hmos : g.u.IsMorphismOfSites Y.J X.J)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    (derivedPullbackIsoOfIso g f θ).hom.app (DerivedCategory.Q.obj K) ≫
        (Stacks.Sheaves.DerivedPullback.OfToposHom.flatPullbackIso f K hK hflat).hom =
      (Stacks.Sheaves.DerivedPullback.flatPullbackIso g hmos K hK hflat).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K) := by
  rw [Stacks.Sheaves.DerivedPullback.OfToposHom.flatPullbackIso_hom_eq_pullbackComparisonQ,
    Stacks.Sheaves.DerivedPullback.flatPullbackIso_hom_eq_pullbackComparisonQ]
  exact app_comp_comp_comp_eq_of_squares (derivedPullbackIsoOfIso g f θ).hom _ _ _ _ _ _ _
    (derivedPullbackIsoOfIso_hom_app g f θ
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (DerivedCategory.quotientCompQhIso_hom_naturality
      ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K))

section Tensor

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (hmos : g.u.IsMorphismOfSites Y.J X.J)

/-- **An isomorphism `θ : g^* ≅ φ^*` of the pullback of a site-presented morphism with that of a
four-field morphism carries the comparison of total tensor complexes of Stacks 03EL of one to
that of the other**: `θ_{Tot(K ⊗ L)} ≫ τ_φ = τ_g ≫ Tot(θ_K ⊗ θ_L)`. -/
def TotalTensorCompat (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (θ : g.pullbackTopos ≅ φ.pullbackModules) : Prop :=
  ∀ K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
    (NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app
        (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)) ≫
      (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso φ K L).hom =
    (Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso g hmos K L).hom ≫
      HomologicalComplex.mapBifunctorMap
        ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K)
        ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app L)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)

/-- The identification of the pullback of a site-presented morphism with that of any four-field
morphism equal to `Stacks.Sheaves.DerivedPullback.modulesHomOfSiteHom`. -/
def pullbackModulesSiteIsoOfEq (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (e : Stacks.Sheaves.DerivedPullback.modulesHomOfSiteHom g hmos = φ) :
    g.pullbackTopos ≅ φ.pullbackModules :=
  (Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso g hmos).symm ≪≫
    eqToIso (congrArg (·.pullbackModules) e)

omit [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The comparison of Stacks 07A4 of the site-presented reading at a pair of K-flat complexes
with flat terms, written out factor by factor. -/
theorem derivedPullbackTensorIso_hom_app_model_eq
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso g hmos).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback g).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison
            K L hK hL).hom ≫
        (Stacks.Sheaves.DerivedPullback.flatPullbackIso g hmos
          (HomologicalComplex.mapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))
          (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hL)
          (Stacks.Sheaves.DerivedPullback.isFlat_tensorComplex_X Y.O K L hflatK hflatL)).hom ≫
        DerivedCategory.Q.map
          (Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso g hmos K L).hom ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
          ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex g).obj K)
          ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex g).obj L)
          (Stacks.Sheaves.DerivedPullback.kFlat_pullbackComplex' g hmos K hK hflatK)
          (Stacks.Sheaves.DerivedPullback.kFlat_pullbackComplex' g hmos L hL hflatL)).inv ≫
        (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).map
          ((Stacks.Sheaves.DerivedPullback.flatPullbackIso g hmos K hK hflatK).inv ×ₘ
            (Stacks.Sheaves.DerivedPullback.flatPullbackIso g hmos L hL hflatL).inv) := by
  rw [Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_model g hmos K L hK hL
    hflatK hflatL]
  exact (Category.assoc _ _ _).trans (congrArg _ (congrArg _ (Category.assoc _ _ _)))

variable {g f θ hmos} in
/-- **`derivedPullbackIsoOfIso` carries Stacks 07A4 of one reading to that of the other, at a
pair of K-flat complexes with flat terms.** -/
theorem derivedPullbackIsoOfIso_tensor_app_model (hθ : TotalTensorCompat g hmos f.toModulesHom θ)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (derivedPullbackIsoOfIso g f θ).hom.app
        ((Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O)).obj
          (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L)) ≫
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) =
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso g hmos).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
        ((derivedPullbackIsoOfIso g f θ).hom.app (DerivedCategory.Q.obj K) ×ₘ
          (derivedPullbackIsoOfIso g f θ).hom.app (DerivedCategory.Q.obj L)) := by
  have hA := derivedPullbackIsoOfIso_hom_app_flatPullbackIso g f θ hmos K hK hflatK
  have hB := derivedPullbackIsoOfIso_hom_app_flatPullbackIso g f θ hmos L hL hflatL
  have hM := derivedPullbackIsoOfIso_hom_app_flatPullbackIso g f θ hmos
    (HomologicalComplex.mapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hL)
    (Stacks.Sheaves.DerivedPullback.isFlat_tensorComplex_X Y.O K L hflatK hflatL)
  have hβ : DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app
        (HomologicalComplex.mapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))) ≫
      DerivedCategory.Q.map
        (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso f.toModulesHom K L).hom =
      DerivedCategory.Q.map
          (Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso g hmos K L).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K)
          ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app L)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hθ K L]
  have hcmp := (Category.assoc _ _ _).trans
    ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison_naturality
      ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app K)
      ((NatTrans.mapHomologicalComplex θ.hom (ComplexShape.up ℤ)).app L)
      (Stacks.Sheaves.DerivedPullback.kFlat_pullbackComplex' g hmos K hK hflatK)
      ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).2
        (Stacks.Sheaves.DerivedPullback.OfToposHom.kFlatBifunctor_pullbackComplex f K hK hflatK))
      (Stacks.Sheaves.DerivedPullback.kFlat_pullbackComplex' g hmos L hL hflatL)
      ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).2
        (Stacks.Sheaves.DerivedPullback.OfToposHom.kFlatBifunctor_pullbackComplex f L hL hflatL)))
  rw [Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_hom_app_model_eq f K L
      hK hL hflatK hflatL,
    derivedPullbackTensorIso_hom_app_model_eq g hmos K L hK hL hflatK hflatL]
  exact app_comp_eq_of_models (derivedPullbackIsoOfIso g f θ).hom _ _ _ _ _ _ _ _ _ _ _
    hA hB hM hβ hcmp

variable {g f θ hmos} in
/-- **`derivedPullbackIsoOfIso` carries Stacks 07A4 of the site-presented reading to that of the
topos reading**, given that `θ` carries the comparisons of total tensor complexes of Stacks 03EL
to each other. -/
theorem tensorCompat_derivedPullbackIsoOfIso (hθ : TotalTensorCompat g hmos f.toModulesHom θ) :
    TensorCompat (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso g hmos).hom
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom
      (derivedPullbackIsoOfIso g f θ).hom :=
  TensorCompat.of_eq (Stacks.Sheaves.DerivedPullback.natTrans_ext_of_flatKFlat Y _ _
    fun K L hK hL hflatK hflatL =>
      derivedPullbackIsoOfIso_tensor_app_model hθ K L hK hL hflatK hflatL)

/-- The derived adjunction of the topos reading, at the universes of this file. -/
abbrev derivedAdjunctionTopos :
    Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback f ⊣
      Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := X) (Y := Y) f :=
  Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction f

variable {g f θ hmos} in
/-- **The two projection maps `K ⊗^L R(-)_*E ⟶ R(-)_*(L(-)^*K ⊗^L E)` are invertible at the same
objects**, given that `θ` carries the comparisons of total tensor complexes to each other. -/
theorem isIso_projectionMap_iff_of_totalTensorCompat
    (hθ : TotalTensorCompat g hmos f.toModulesHom θ)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    IsIso (projectionMap
        (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O))
        (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))
        (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction g hmos)
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso g hmos).hom K E) ↔
      IsIso (projectionMap
        (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O))
        (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))
        (derivedAdjunctionTopos f)
        (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom K E) :=
  Stacks.Cohomology.AbstractKunnethMap.isIso_projectionMap_iff_of_iso _ _
    (derivedPullbackIsoOfIso g f θ) _ _ (tensorCompat_derivedPullbackIsoOfIso hθ) K E

variable {g f θ hmos} in
/-- **The maps `Rh_*E ⊗^L K ⟶ Rh_*(E ⊗^L Lh^*K)` of Stacks 0B56 of the two readings are invertible
at the same objects**, given that `θ` carries the comparisons of total tensor complexes to each
other. -/
theorem isIso_projectionFormulaMap_iff_of_totalTensorCompat
    (hθ : TotalTensorCompat g hmos f.toModulesHom θ)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    IsIso (Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap g hmos E K) ↔
      IsIso (Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap f E K) :=
  Stacks.Cohomology.AbstractKunnethMap.isIso_adjunctionTensorMap_iff_of_iso _
    (derivedAdjunctionTopos f) (derivedPullbackIsoOfIso g f θ) _ _
    (tensorCompat_derivedPullbackIsoOfIso hθ) E K

/-- **The commutativity constraint of Stacks 0FPT on the uncurried derived tensor product**, as
an isomorphism `M ⊗^L N ≅ N ⊗^L M` natural in the pair. -/
def braidingIso (Z : RingedTopos.{u, u, u}) [HasSheafify Z.J AddCommGrpCat.{u}]
    [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.O) ≅
      CategoryTheory.Prod.swap _ _ ⋙
        Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.O) :=
  haveI : ∀ P, IsIso
      ((Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingNatTrans Z.O).app P) :=
    fun P => by
      let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Z.O
      let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Z.O
      exact inferInstanceAs (IsIso (β_ P.1 P.2).hom)
  haveI := NatIso.isIso_of_isIso_app
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingNatTrans Z.O)
  asIso (Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingNatTrans Z.O)

variable {g f θ hmos} in
/-- **The projection map `K ⊗^L Rh_*E ⟶ Rh_*(Lh^*K ⊗^L E)` of the site-presented reading is
invertible exactly when the map `Rh_*E ⊗^L K ⟶ Rh_*(E ⊗^L Lh^*K)` of Stacks 0B56 of the topos
reading is**: the two readings have the same projection maps, and the two variants of the
projection map correspond under the commutativity constraint, with which Stacks 07A4 is
compatible. -/
theorem isIso_projectionMap_iff_isIso_projectionFormulaMap
    (hθ : TotalTensorCompat g hmos f.toModulesHom θ)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    IsIso (projectionMap
        (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O))
        (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))
        (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction g hmos)
        (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso g hmos).hom K E) ↔
      IsIso (Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap f E K) := by
  rw [isIso_projectionMap_iff_of_totalTensorCompat hθ]
  exact Stacks.Cohomology.AbstractKunnethMap.isIso_projectionMap_iff_isIso_adjunctionTensorMap
    (derivedAdjunctionTopos f) _ (braidingIso Y) (braidingIso X)
    (fun P Q => Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_braiding f P Q)
    K E

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  [(Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
    g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))] in
/-- **The identification of the two pullbacks carries the comparison of total tensor complexes of
the site-presented reading to that of any four-field morphism equal to its own.** -/
theorem totalTensorCompat_pullbackModulesSiteIsoOfEq
    (φ : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (e : Stacks.Sheaves.DerivedPullback.modulesHomOfSiteHom g hmos = φ) :
    TotalTensorCompat g hmos φ (pullbackModulesSiteIsoOfEq g hmos φ e) := by
  intro K L
  subst e
  simp only [pullbackModulesSiteIsoOfEq, Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso,
    Stacks.Sheaves.DerivedPullback.pullbackComplexSiteIso,
    Stacks.Sheaves.DerivedPullback.mapBifunctorMapIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.assoc,
    HomologicalComplex.mapBifunctorMap_comp]
  have e₁ : ∀ M : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      ((NatIso.mapHomologicalComplex (Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso g hmos)
          (ComplexShape.up ℤ)).app M).hom ≫
        (NatTrans.mapHomologicalComplex
          (Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso g hmos).inv
          (ComplexShape.up ℤ)).app M = 𝟙 _ := fun M =>
    ((NatIso.mapHomologicalComplex (Stacks.Sheaves.DerivedPullback.pullbackModulesSiteIso g hmos)
          (ComplexShape.up ℤ)).app M).hom_inv_id
  rw [e₁, e₁, HomologicalComplex.mapBifunctorMap_id, Category.comp_id]
  rfl

end Tensor

end Generic

end Stacks.Cohomology.RingedSiteHomReadings

end
