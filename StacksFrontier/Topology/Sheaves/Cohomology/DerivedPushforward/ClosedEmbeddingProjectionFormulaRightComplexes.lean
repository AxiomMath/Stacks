module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaMate
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaRightSheaves

/-!
# The projection formula for a closed embedding with the pushforward on the right, for complexes

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces whose underlying continuous map is
a homeomorphism onto a closed subset.  For arbitrary cochain complexes `B^•` of `𝒪_Y`-modules and
`A^•` of `𝒪_X`-modules there is an isomorphism of complexes

`Tot(B^• ⊗_{𝒪_Y} f_*A^•) ≅ f_* Tot(f^*B^• ⊗_{𝒪_X} A^•)`,

the totalization of the termwise isomorphism
`Stacks.ClosedEmbeddingProjectionFormula.projectionFormulaIsoRight` followed by the comparison
`Tot(f_*(-)) ⟶ f_*(Tot(-))`, which is invertible because `f_*` commutes with direct sums.  This
isomorphism is the complex-level transpose of the comparison of [Stacks, Tag 01CD] followed by
the counit in the right tensor factor.

## Main results

* `projectionFormulaMapRight'_natural_left` and `projectionFormulaMapRight'_natural_right`: the
  two one-sided naturalities of the right-handed projection-formula morphism, at the
  `Stacks.SheafOfModules.Tensor.sheafTensor` presentation of the tensor product.
* `projectionBicomplexIsoRight`: the termwise isomorphism of bicomplexes.
* `complexProjectionFormulaIsoRight`: the projection formula for complexes,
  `Tot(B^• ⊗_{𝒪_Y} f_*A^•) ≅ f_* Tot(f^*B^• ⊗_{𝒪_X} A^•)`.
* `ι_complexProjectionFormulaIsoRight_hom`: its restriction to a summand of the total complex.
* `complexProjectionFormulaIsoRight_mate`: it is the transpose of the comparison of
  [Stacks, Tag 01CD] on total complexes followed by the counit in the right tensor factor.

## References

* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.ProjectionFormula
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.Cohomology.ClosedEmbeddingPushforward
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex comparisonAppIso)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex complexAdjunction
  complexAdjunction_counit_app_f)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

section Construction

attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf
  StacksDraft.KFlat.modulePullback
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-! ### The two one-sided naturalities, at the `sheafTensor` presentation -/

/-- **Naturality of the right-handed projection-formula morphism in the module on `Y`**, stated at
the `Stacks.SheafOfModules.Tensor.sheafTensor` presentation of the tensor product.  There is no
hypothesis on `f`. -/
lemma projectionFormulaMapRight'_natural_left {F F' : SheafOfModules.{u} (structureRingSheaf Y)}
    (k : F ⟶ F') (G : SheafOfModules.{u} (structureRingSheaf X)) :
    ((sheafTensor Y.sheaf).map k).app ((pushforwardFunctor f).obj G) ≫
        projectionFormulaMapRight' f F' G =
      projectionFormulaMapRight' f F G ≫ (pushforwardFunctor f).map
        (((sheafTensor X.sheaf).map ((pullbackFunctor f).map k)).app G) := by
  have h := projectionFormulaMapRight'_natural f k (𝟙 G)
  rw [CategoryTheory.Functor.map_id] at h
  have e₁ :
      (Functor.uncurry.obj (sheafTensor Y.sheaf)).map (k ×ₘ 𝟙 ((pushforwardFunctor f).obj G)) =
      ((sheafTensor Y.sheaf).map k).app ((pushforwardFunctor f).obj G) :=
    (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have e₂ : (Functor.uncurry.obj (sheafTensor X.sheaf)).map ((pullbackFunctor f).map k ×ₘ 𝟙 G) =
      ((sheafTensor X.sheaf).map ((pullbackFunctor f).map k)).app G :=
    (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  exact (congrArg (· ≫ _) e₁).symm.trans
    (h.trans (congrArg (fun t => _ ≫ (pushforwardFunctor f).map t) e₂))

/-- **Naturality of the right-handed projection-formula morphism in the module on `X`**, stated
at the `Stacks.SheafOfModules.Tensor.sheafTensor` presentation of the tensor product.  There is
no hypothesis on `f`. -/
lemma projectionFormulaMapRight'_natural_right (F : SheafOfModules.{u} (structureRingSheaf Y))
    {G G' : SheafOfModules.{u} (structureRingSheaf X)} (g : G ⟶ G') :
    ((sheafTensor Y.sheaf).obj F).map ((pushforwardFunctor f).map g) ≫
        projectionFormulaMapRight' f F G' =
      projectionFormulaMapRight' f F G ≫ (pushforwardFunctor f).map
        (((sheafTensor X.sheaf).obj ((pullbackFunctor f).obj F)).map g) := by
  have h := projectionFormulaMapRight'_natural f (𝟙 F) g
  rw [CategoryTheory.Functor.map_id] at h
  have e₁ : (Functor.uncurry.obj (sheafTensor Y.sheaf)).map (𝟙 F ×ₘ (pushforwardFunctor f).map g) =
      ((sheafTensor Y.sheaf).obj F).map ((pushforwardFunctor f).map g) :=
    (congrArg (· ≫ _) ((NatTrans.congr_app (CategoryTheory.Functor.map_id _ _) _).trans
      (NatTrans.id_app _ _))).trans (Category.id_comp _)
  have e₂ : (Functor.uncurry.obj (sheafTensor X.sheaf)).map (𝟙 ((pullbackFunctor f).obj F) ×ₘ g) =
      ((sheafTensor X.sheaf).obj ((pullbackFunctor f).obj F)).map g :=
    (congrArg (· ≫ _) ((NatTrans.congr_app (CategoryTheory.Functor.map_id _ _) _).trans
      (NatTrans.id_app _ _))).trans (Category.id_comp _)
  exact (congrArg (· ≫ _) e₁).symm.trans
    (h.trans (congrArg (fun t => _ ≫ (pushforwardFunctor f).map t) e₂))

/-! ### The termwise isomorphism of bicomplexes -/

/-- **The right-handed projection formula termwise on a pair of complexes**, as an isomorphism of
bicomplexes: for `f` a homeomorphism onto a closed subset and arbitrary cochain complexes `B^•`
on `Y` and `A^•` on `X`, the bicomplex `(i, j) ↦ B^i ⊗_{𝒪_Y} f_*A^j` is isomorphic to the
bicomplex obtained by applying `f_*` to every term of `(i, j) ↦ f^*B^i ⊗_{𝒪_X} A^j`.  Each
component is `Stacks.ClosedEmbeddingProjectionFormula.projectionFormulaIsoRight`. -/
def projectionBicomplexIsoRight
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (A : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj B).obj
        (((modulePushforward f).mapHomologicalComplex (.up ℤ)).obj A) ≅
      (letI : (modulePushforward f).Additive :=
        modulePushforward_additive f
       HomologicalComplex₂.TotalMap.mapBicomplex
        (C := SheafOfModules.{u} (structureSheafRing X))
        (D := SheafOfModules.{u} (structureSheafRing Y)) (modulePushforward f)
        ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
          ((pullbackComplex f).obj B)).obj A)) :=
  letI : (modulePushforward f).Additive :=
    modulePushforward_additive f
  HomologicalComplex.Hom.isoOfComponents
    (fun i => HomologicalComplex.Hom.isoOfComponents
      (fun j =>
        Stacks.ClosedEmbeddingProjectionFormula.projectionFormulaIsoRight f hf (B.X i) (A.X j))
      (fun j j' _ => (projectionFormulaMapRight'_natural_right f (B.X i) (A.d j j')).symm))
    (fun i i' _ => by
      ext j : 1
      exact (projectionFormulaMapRight'_natural_left f (B.d i i') (A.X j)).symm)

/-! ### The projection formula for complexes -/

/-- **The projection formula for a closed embedding with the pushforward on the right, at the
level of complexes.**  For a morphism of ringed spaces `f : X ⟶ Y` whose underlying continuous
map is a homeomorphism onto a closed subset, and for *arbitrary* cochain complexes `B^•` of
`𝒪_Y`-modules and `A^•` of `𝒪_X`-modules,

`Tot(B^• ⊗_{𝒪_Y} f_*A^•) ≅ f_* Tot(f^*B^• ⊗_{𝒪_X} A^•)`.

It is the termwise isomorphism `projectionBicomplexIsoRight` on totalizations, composed with the
comparison `Tot(f_*(-)) ⟶ f_*(Tot(-))`. -/
def complexProjectionFormulaIsoRight
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (A : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    ((tensorComplex Y.sheaf).obj B).obj
        (((modulePushforward f).mapHomologicalComplex (.up ℤ)).obj A) ≅
      ((modulePushforward f).mapHomologicalComplex (.up ℤ)).obj
        (((tensorComplex X.sheaf).obj
          ((pullbackComplex f).obj B)).obj A) := by
  letI : (modulePushforward f).Additive :=
    modulePushforward_additive f
  letI : (Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} Y
  letI : (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} X
  let e := projectionBicomplexIsoRight f hf B A
  letI := HomologicalComplex₂.hasTotal_of_iso e (.up ℤ)
  have h := isIso_totalMap_modulePushforward f hf
    ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      ((pullbackComplex f).obj B)).obj A)
  exact HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫ @asIso _ _ _ _ _ h

end Construction

section Summands

attribute [local implicit_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-! ### The summand formula -/

/-- **The right-handed complex-level projection formula on a summand.**  The `(p, q)` summand
inclusion of `Tot(B^• ⊗_{𝒪_Y} f_*A^•)` followed by `complexProjectionFormulaIsoRight` is the
termwise morphism `projectionFormulaMapRight' f (B.X p) (A.X q)` followed by `f_*` of the
`(p, q)` summand inclusion of `Tot(f^*B^• ⊗_{𝒪_X} A^•)`. -/
lemma ι_complexProjectionFormulaIsoRight_hom
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    HomologicalComplex₂.ιTotal
          ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj B).obj
            ((pushforwardComplex f).obj A))
          (.up ℤ) p q n hpq ≫
        (complexProjectionFormulaIsoRight f hf B A).hom.f n =
      projectionFormulaMapRight' f (B.X p) (A.X q) ≫
        (StacksDraft.KFlat.modulePushforward f).map
          (HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj B)).obj A)
            (.up ℤ) p q n hpq) := by
  let : (modulePushforward f).Additive :=
    modulePushforward_additive f
  let : (Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} Y
  let : (Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u} X
  let : (StacksDraft.KFlat.modulePushforward f).Additive :=
    StacksDraft.KFlat.modulePushforward_additive f
  let := HomologicalComplex₂.hasTotal_of_iso (projectionBicomplexIsoRight f hf B A) (.up ℤ)
  exact ι_total_map_comp_totalMap (c₁₂ := ComplexShape.up ℤ)
    (StacksDraft.KFlat.modulePushforward f)
    ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      ((pullbackComplex f).obj B)).obj A)
    ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj B).obj
      ((pushforwardComplex f).obj A))
    (projectionBicomplexIsoRight f hf B A).hom p q n hpq

/-- The summand formula pulled back along `f`, with a trailing morphism bound. -/
private lemma map_ιTotal_comp_map_complexProjectionFormulaIsoRight_hom_comp
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (p q n : ℤ) (hpq : p + q = n)
    {Z : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X} (g : _ ⟶ Z) :
    (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex₂.ιTotal
            ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj B).obj
              ((pushforwardComplex f).obj A))
            (.up ℤ) p q n hpq) ≫
        (StacksDraft.KFlat.modulePullback f).map
          ((complexProjectionFormulaIsoRight f hf B A).hom.f n) ≫ g =
      (StacksDraft.KFlat.modulePullback f).map (projectionFormulaMapRight' f (B.X p) (A.X q)) ≫
        (StacksDraft.KFlat.modulePullback f).map
          ((StacksDraft.KFlat.modulePushforward f).map
            (HomologicalComplex₂.ιTotal
              ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
                ((pullbackComplex f).obj B)).obj A)
              (.up ℤ) p q n hpq)) ≫ g := by
  rw [← Category.assoc,
    ((StacksDraft.KFlat.modulePullback f).map_comp
      (HomologicalComplex₂.ιTotal
        ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj B).obj
          ((pushforwardComplex f).obj A))
        (.up ℤ) p q n hpq)
      ((complexProjectionFormulaIsoRight f hf B A).hom.f n)).symm,
    ι_complexProjectionFormulaIsoRight_hom]
  exact (congrArg (· ≫ g) ((StacksDraft.KFlat.modulePullback f).map_comp _ _)).trans
    (Category.assoc _ _ _)

/-- **On each summand, the pullback of `complexProjectionFormulaIsoRight` followed by the counit
is the comparison of [Stacks, Tag 01CD] followed by the counit in the right tensor factor.** -/
private lemma ιTotal_comp_map_complexProjectionFormulaIsoRight_hom_comp_counit
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (p q n : ℤ) (hpq : p + q = n) :
    (StacksDraft.KFlat.modulePullback f).map
          (HomologicalComplex₂.ιTotal
            ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj B).obj
              ((pushforwardComplex f).obj A))
            (.up ℤ) p q n hpq) ≫
        (StacksDraft.KFlat.modulePullback f).map
            ((complexProjectionFormulaIsoRight f hf B A).hom.f n) ≫
          (modulePullbackPushforwardAdjunction f).counit.app
            ((((tensorComplex X.sheaf).obj ((pullbackComplex f).obj B)).obj A).X n) =
      (comparisonAppIso f (B.X p) ((StacksDraft.KFlat.modulePushforward f).obj (A.X q))).hom ≫
        ((sheafTensor X.sheaf).obj ((StacksDraft.KFlat.modulePullback f).obj (B.X p))).map
            ((modulePullbackPushforwardAdjunction f).counit.app (A.X q)) ≫
          HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj B)).obj A)
            (.up ℤ) p q n hpq := by
  have e : (Functor.uncurry.obj (sheafTensor X.sheaf)).map
      (𝟙 ((pullbackFunctor f).obj (B.X p)) ×ₘ (pullbackAdjunction f).counit.app (A.X q)) =
      ((sheafTensor X.sheaf).obj ((pullbackFunctor f).obj (B.X p))).map
        ((pullbackAdjunction f).counit.app (A.X q)) :=
    (congrArg (· ≫ _) ((NatTrans.congr_app (CategoryTheory.Functor.map_id _ _) _).trans
      (NatTrans.id_app _ _))).trans (Category.id_comp _)
  refine (map_ιTotal_comp_map_complexProjectionFormulaIsoRight_hom_comp f hf B A p q n hpq
    _).trans ?_
  refine ((map_comp_map_map_comp_counit (modulePullbackPushforwardAdjunction f) _ _).trans
    (congrArg (· ≫ _)
      (map_projectionFormulaMapRight'_comp_counit f (B.X p) (A.X q)))).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (fun t => _ ≫ t ≫ _) e)

/-! ### The mate identity -/

/-- **The right-handed complex-level projection formula is the transpose of the termwise
comparison.**  Let `ϑ` be the comparison of [Stacks, Tag 01CD] on total complexes,
`Tot(f^*B^• ⊗_{𝒪_X} f^*f_*A^•) ⟶ f^*Tot(B^• ⊗_{𝒪_Y} f_*A^•)`, described on each summand by
`hϑ`, and let `μ` be the counit of `f^* ⊣ f_*` in the right tensor factor, described on each
summand by `hμ`.  Then `ϑ`, followed by the degreewise pullback of
`complexProjectionFormulaIsoRight` and the counit of `f^* ⊣ f_*` on complexes, is `μ`. -/
theorem complexProjectionFormulaIsoRight_mate
    (hf : Topology.IsClosedEmbedding (ConcreteCategory.hom f.hom.base))
    (B : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    (A : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (ϑ : HomologicalComplex₂.total
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj B)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A))) (.up ℤ) ⟶
        (pullbackComplex f).obj
          (((tensorComplex Y.sheaf).obj B).obj ((pushforwardComplex f).obj A)))
    (hϑ : ∀ (p q n : ℤ) (hpq : p + q = n)
        {Z : AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X}
        (g : (StacksDraft.KFlat.modulePullback f).obj
            ((((tensorComplex Y.sheaf).obj B).obj ((pushforwardComplex f).obj A)).X n) ⟶ Z),
      HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj B)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A)))
            (.up ℤ) p q n hpq ≫ ϑ.f n ≫ g =
        (comparisonAppIso f (B.X p) ((StacksDraft.KFlat.modulePushforward f).obj (A.X q))).inv ≫
          (StacksDraft.KFlat.modulePullback f).map
            (HomologicalComplex₂.ιTotal
              ((((sheafTensor Y.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj B).obj
                ((pushforwardComplex f).obj A))
              (.up ℤ) p q n hpq) ≫ g)
    (μ : HomologicalComplex₂.total
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj B)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A))) (.up ℤ) ⟶
        ((tensorComplex X.sheaf).obj ((pullbackComplex f).obj B)).obj A)
    (hμ : ∀ (p q n : ℤ) (hpq : p + q = n),
      HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj B)).obj
              ((pullbackComplex f).obj ((pushforwardComplex f).obj A)))
            (.up ℤ) p q n hpq ≫ μ.f n =
        ((sheafTensor X.sheaf).obj ((StacksDraft.KFlat.modulePullback f).obj (B.X p))).map
            ((modulePullbackPushforwardAdjunction f).counit.app (A.X q)) ≫
          HomologicalComplex₂.ιTotal
            ((((sheafTensor X.sheaf).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
              ((pullbackComplex f).obj B)).obj A)
            (.up ℤ) p q n hpq) :
    ϑ ≫ (pullbackComplex f).map (complexProjectionFormulaIsoRight f hf B A).hom ≫
        (complexAdjunction f).counit.app
          (((tensorComplex X.sheaf).obj ((pullbackComplex f).obj B)).obj A) =
      μ := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦
    HomologicalComplex₂.total.hom_ext (.up ℤ) fun p q hpq ↦ ?_
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_obj_X]
  rw [hμ p q n hpq, complexAdjunction_counit_app_f, hϑ p q n hpq]
  exact (congrArg
    ((comparisonAppIso f (B.X p) ((StacksDraft.KFlat.modulePushforward f).obj (A.X q))).inv ≫ ·)
    (ιTotal_comp_map_complexProjectionFormulaIsoRight_hom_comp_counit f hf B A p q n hpq)).trans
    (Iso.inv_hom_id_assoc _ _)

end Summands

end Stacks.Cohomology.ClosedEmbeddingProjectionFormulaComplexes

end
