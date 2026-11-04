module

public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatTensorComplexGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorTotalAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral
public import StacksFrontier.Homology.MapHomologicalComplexTensorAssociativity

/-!
# The comparison of Tag 03EL as a tensorator, and Stacks 07A4 on K-flat models

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi. The inverse of the comparison
`f^*(a ⊗ b) ≅ f^*a ⊗ f^*b` of Tag 03EL is a tensorator for the monoidal structures of `Mod(O')`
and `Mod(O)` re-seated on `⊗`; this file proves its associativity, lifts it to complexes, where
it is the inverse of the comparison of total tensor complexes `pullbackTensorTotalComplexIso`,
and proves that the lift is associative. It also reads the isomorphism of Stacks 07A4 on a pair
of K-flat complexes with flat terms through the K-flat comparisons of the two derived tensor
products.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorμ`: the tensorator of Tag 03EL.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorComplexμ`: its lift to complexes.

## Main results

* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorμ_associativity`.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackTensorComplexμ_associativity`: the
  comparison of total tensor complexes is compatible with the associators of complexes.
* `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_hom_app_model_comp`.

## Implementation notes

The complexes are pulled back by `pullbackModulesTensor f`, the pullback of modules between the
categories of modules in the spelling of the derived tensor product. Its lift to complexes is
written `mapHomologicalComplex _`, never with an explicit `ComplexShape.up ℤ`: an explicitly
elaborated `ComplexShape.up ℤ` carries other `Add` instance terms than the one inside
`CochainComplex`, and the monoidal structures of complexes over the two shapes do not unify at
an affordable cost.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)
open Stacks.Sheaves.DerivedPullback (isFlat_tensorComplex_X_general)

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

universe u c c'

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  CochainComplex.symmetricCategory

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


/-! ## The comparison of Tag 03EL as a tensorator, and its associativity on complexes -/

section Complexes

/-- The pullback of modules along `f`, between the categories of modules in the spelling of the
derived tensor product, `Stacks.SheafOfModules.Tensor.ringSheaf`. -/
def pullbackModulesTensor :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  f.toModulesHom.pullbackModules

/-- The pullback of modules `pullbackModulesTensor f` is an additive functor. -/
instance pullbackModulesTensor_additive : (pullbackModulesTensor f).Additive :=
  RingedToposHom.pullbackModules_additive f

/-- The inverse of the comparison `f^*(a ⊗ b) ≅ f^*a ⊗ f^*b` of Tag 03EL, in the spelling of the
monoidal structure of `Mod(O)` re-seated on `⊗`. -/
def pullbackTensorμ (a b : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (pullbackModulesTensor f).obj a ⊗ (pullbackModulesTensor f).obj b ⟶
      (pullbackModulesTensor f).obj (a ⊗ b) :=
  (Stacks.SheafOfModules.pullbackTensorIso f.toModulesHom).inv.app (a, b)

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The associativity of the tensorator of Tag 03EL** in the spelling of the monoidal structure
of `Mod(O)` re-seated on `⊗`. -/
theorem pullbackTensorμ_associativity
    (a b c : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    pullbackTensorμ f a b ▷ (pullbackModulesTensor f).obj c ≫
        pullbackTensorμ f (a ⊗ b) c ≫ (pullbackModulesTensor f).map (α_ a b c).hom =
      (α_ ((pullbackModulesTensor f).obj a) ((pullbackModulesTensor f).obj b)
          ((pullbackModulesTensor f).obj c)).hom ≫
        (pullbackModulesTensor f).obj a ◁ pullbackTensorμ f b c ≫
          pullbackTensorμ f a (b ⊗ c) :=
  Stacks.SheafOfModules.pullbackTensorIso_inv_associativity f.toModulesHom a b c

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The tensorator of Tag 03EL is natural in the first module. -/
theorem pullbackTensorμ_natural_left
    {a a' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (g : a ⟶ a')
    (b : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (pullbackModulesTensor f).map g ▷ (pullbackModulesTensor f).obj b ≫
        pullbackTensorμ f a' b =
      pullbackTensorμ f a b ≫ (pullbackModulesTensor f).map (g ▷ b) :=
  Stacks.SheafOfModules.pullbackTensorIso_inv_naturality_fst f.toModulesHom g b

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The tensorator of Tag 03EL is natural in the second module. -/
theorem pullbackTensorμ_natural_right
    (a : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {b b' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (g : b ⟶ b') :
    (pullbackModulesTensor f).obj a ◁ (pullbackModulesTensor f).map g ≫
        pullbackTensorμ f a b' =
      pullbackTensorμ f a b ≫ (pullbackModulesTensor f).map (a ◁ g) :=
  Stacks.SheafOfModules.pullbackTensorIso_inv_naturality_snd f.toModulesHom a g

/-- **The comparison of total tensor complexes of Stacks 07A4, as a tensorator**:
`f^*K ⊗ f^*L ≅ f^*(K ⊗ L)`, the inverse of `pullbackTensorTotalComplexIso`. -/
def pullbackTensorComplexμ
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    ((pullbackModulesTensor f).mapHomologicalComplex _).obj K ⊗
        ((pullbackModulesTensor f).mapHomologicalComplex _).obj L ≅
      ((pullbackModulesTensor f).mapHomologicalComplex _).obj (K ⊗ L) :=
  (pullbackTensorTotalComplexIso f K L).symm

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The inverse comparison of total tensor complexes on the summands, in the spelling of the
total tensor complex by `⊗_O`. -/
private theorem ι_pullbackTensorTotalComplexIso_inv
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor
        (((pullbackModulesTensor f).mapHomologicalComplex _).obj K)
        (((pullbackModulesTensor f).mapHomologicalComplex _).obj L)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p q n h ≫
        (pullbackTensorTotalComplexIso f K L).inv.f n =
      pullbackTensorμ f (K.X p) (L.X q) ≫
        (pullbackModulesTensor f).map (HomologicalComplex.ιMapBifunctor K L
          (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ) p q n h) :=
  Stacks.Sheaves.DerivedPullback.ι_pullbackTensorTotalIso_inv f.toModulesHom K L p q n h

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- The tensorator of complexes on the summands of its source. -/
@[reassoc]
theorem ι_pullbackTensorComplexμ_hom
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj (((pullbackModulesTensor f).mapHomologicalComplex _).obj K)
          (((pullbackModulesTensor f).mapHomologicalComplex _).obj L) p q n h ≫
        (pullbackTensorComplexμ f K L).hom.f n =
      pullbackTensorμ f (K.X p) (L.X q) ≫
        (pullbackModulesTensor f).map (HomologicalComplex.ιTensorObj K L p q n h) :=
  ι_pullbackTensorTotalComplexIso_inv f K L p q n h

omit [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] in
/-- **The comparison of total tensor complexes is associative**: the tensorator
`f^*K ⊗ f^*L ≅ f^*(K ⊗ L)` of Stacks 07A4 is compatible with the associators of the total tensor
products of complexes. On the summand of tridegree `(i₁, i₂, i₃)` this is the associativity of
the comparison of Tag 03EL. -/
theorem pullbackTensorComplexμ_associativity
    (K₁ K₂ K₃ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackTensorComplexμ f K₁ K₂).hom ▷
          ((pullbackModulesTensor f).mapHomologicalComplex _).obj K₃ ≫
        (pullbackTensorComplexμ f (K₁ ⊗ K₂) K₃).hom ≫
          ((pullbackModulesTensor f).mapHomologicalComplex _).map (α_ K₁ K₂ K₃).hom =
      (α_ (((pullbackModulesTensor f).mapHomologicalComplex _).obj K₁)
            (((pullbackModulesTensor f).mapHomologicalComplex _).obj K₂)
            (((pullbackModulesTensor f).mapHomologicalComplex _).obj K₃)).hom ≫
        ((pullbackModulesTensor f).mapHomologicalComplex _).obj K₁ ◁
          (pullbackTensorComplexμ f K₂ K₃).hom ≫
          (pullbackTensorComplexμ f K₁ (K₂ ⊗ K₃)).hom := by
  refine Functor.mapHomologicalComplex_associativity_of_ι
    (pullbackModulesTensor f) (pullbackTensorμ f) ?_ ?_ ?_
    (fun K L ↦ (pullbackTensorComplexμ f K L).hom) ?_ K₁ K₂ K₃
  · exact fun g b ↦ pullbackTensorμ_natural_left f g b
  · exact fun a _ _ g ↦ pullbackTensorμ_natural_right f a g
  · exact pullbackTensorμ_associativity f
  · exact fun K L p q n h ↦ ι_pullbackTensorComplexμ_hom f K L p q n h


end Complexes

/-! ## The derived statement on K-flat complexes with flat terms -/

section Models

variable (TX : Stacks.SheafOfModules.DerivedTensorProduct.{c, u, u} X.toRingedSite)
  (TY : Stacks.SheafOfModules.DerivedTensorProduct.{c', u, u} Y.toRingedSite)

/-- An equation `x = l ≫ r⁻¹` read as `x ≫ r = l`, with `r = a ≫ d ≫ q⁻¹`. -/
private lemma comp_eq_of_eq_trans_symm {𝒞 : Type*} [Category 𝒞] {A B E G H : 𝒞}
    {x : A ⟶ B} {l : A ≅ E} {a : B ≅ G} {d : G ≅ H} {q : E ≅ H}
    (h : x = (l ≪≫ (a ≪≫ d ≪≫ q.symm).symm).hom) :
    x ≫ a.hom ≫ d.hom = l.hom ≫ q.hom := by
  rw [h]
  simp

/-- **The isomorphism of Stacks 07A4 at a pair of K-flat complexes with flat terms**, read
through the computations of `Lf^*` and of `⊗^L` on both sides: followed by `Lf^*K ≅ Q(f^*K)`,
`Lf^*L ≅ Q(f^*L)` and the K-flat comparison of `⊗^L_O`, it is `Lf^*` of the K-flat comparison
of `⊗^L_{O'}`, followed by `Lf^*Q(K ⊗ L) ≅ Q(f^*(K ⊗ L))` and the comparison of Tag 03EL. -/
theorem derivedPullbackTensorIso_hom_app_model_comp
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, c', u, u} (O := Y.O) (L.X i)) :
    (derivedPullbackTensorIso f TX TY).hom.app
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≫
      ((TX.tensor.map (flatPullbackIso f K hK hflatK).hom).app
          ((derivedPullback f).obj (DerivedCategory.Q.obj L)) ≫
        (TX.tensor.obj (DerivedCategory.Q.obj ((pullbackComplex f).obj K))).map
          (flatPullbackIso f L hL hflatL).hom) ≫
        (TX.comparison ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (kFlat_pullbackComplex' f K hK hflatK) (kFlat_pullbackComplex' f L hL hflatL)).hom =
      ((derivedPullback f).mapIso (TY.comparison K L hK hL) ≪≫
          flatPullbackIso f (HomologicalComplex.mapBifunctor K L
            (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ))
            (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hL)
            (isFlat_tensorComplex_X_general Y.O K L hflatK hflatL)).hom ≫
        (DerivedCategory.Q.mapIso (pullbackTensorTotalComplexIso f K L)).hom :=
  comp_eq_of_eq_trans_symm (derivedPullbackTensorIso_hom_app_model f TX TY K L hK hL hflatK hflatL)


end Models

end Stacks.Cohomology.DerivedPullbackOfToposHom

end
