module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechComplex
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite
public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact

/-!
# The Čech complex of a simplicial semi-representable object is a sheaf-Hom complex

Let `(C, J)` be a small site and let `K` be a simplicial object of `SR(C)`, for instance a
hypercovering. The simplicial site `n ↦ C/K_n` of Stacks 0D8B carries the augmentation given by
the degree-zero localization functor, with component augmentations `a_n : Sh(C/K_n) ⟶ Sh(C)` and
total augmentation `a : Sh((C/K)_total) ⟶ Sh(C)`. For an abelian sheaf `F` on `C`, Stacks 0D79
attaches to the abelian sheaf `a⁻¹F` on the total site the Čech complex

`a_{0,*}a_0⁻¹F ⟶ a_{1,*}a_1⁻¹F ⟶ a_{2,*}a_2⁻¹F ⟶ …`

and Stacks 0D8F asserts that it is the complex `SheafHom(s(ℤ_{F(K)}^#), F)`, where
`s(ℤ_{F(K)}^#)` is the chain complex of free abelian sheaves of Stacks 01GB on the simplicial
presheaf `F(K)` represented by `K`.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.semiRepresentablePresheaf`: the simplicial
  presheaf of sets `F(K)` represented by `K`.
* `CategoryTheory.SimplicialSemiRepresentable.freeAbelianComplex`: the chain complex
  `s(ℤ_{F(K)}^#)` of Stacks 01GB.
* `CategoryTheory.SimplicialSemiRepresentable.sheafHomComplex`: the cochain complex
  `SheafHom(s(ℤ_{F(K)}^#), F)`, the image of `s(ℤ_{F(K)}^#)` under the abelian internal hom
  `ℋom(-, F)`.
* `CategoryTheory.SimplicialSemiRepresentable.cechComplex`: the Čech complex of Stacks 0D79 for
  the augmentation of Stacks 0D8B, evaluated at `a⁻¹F`.
* `AlgebraicTopology.mapAlternatingFaceMapComplexOp`: the image of the alternating-face complex
  of a simplicial object under a contravariant additive functor, as a cochain complex.

## Main results

* `AlgebraicTopology.alternatingCofaceMapComplexRightOpIso`: for a contravariant additive functor
  `G` and a simplicial object `X`, the alternating-coface complex of the cosimplicial object
  `n ↦ G(X_n)` is the image of the alternating-face complex of `X` under `G`.
* `CategoryTheory.SimplicialSemiRepresentable.sheafHomComplexIsoCofaceComplex`:
  `SheafHom(s(ℤ_{F(K)}^#), F)` is the alternating-coface complex of the cosimplicial abelian
  sheaf `n ↦ ℋom(ℤ_{F(K_n)}^#, F)`.

## Implementation notes

The terms of the two complexes of Stacks 0D8F are identified by
`a_{n,*}a_n⁻¹F = ℋom'(F(K_n)^#, F)` (Stacks 0D86) together with the natural isomorphism
`ℋom'(𝒢, F) = ℋom(ℤ_𝒢, F)` between the hom sheaf out of a sheaf of sets and the abelian internal
hom out of its free abelian sheaf. The differentials of both complexes are the alternating sum
induced by the simplicial structure of `K`.

The hypercovering conditions on `K` play no role in Stacks 0D8F: only the simplicial site of
Stacks 0D8B and its augmentation are used, so the statements are given for an arbitrary
simplicial object of `SR(C)`.

Since the simplicial-site situation of Stacks 09WE fixes one universe for the component sites and
the augmentation site, `C` is small and the index sets of the semi-representable objects `K_n`
live in the same universe; the abelian sheaves then take values in `AddCommGrpCat` of that
universe, which is where the abelian internal hom `ℋom(-, F)` of Stacks 0D7X lives.

## References

* [Stacks Project, Tag 0D8F](https://stacks.math.columbia.edu/tag/0D8F)
* [Stacks Project, Tag 0D86](https://stacks.math.columbia.edu/tag/0D86)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 01GB](https://stacks.math.columbia.edu/tag/01GB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ v₂ u₂ v u

namespace AlgebraicTopology

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B]

/-- The image of the alternating-face complex `s(X)` of a simplicial object under a
contravariant additive functor `G`, as a cochain complex: in degree `n` it is `G(X_n)` and its
differential is `G` applied to the alternating sum of the face maps. -/
def mapAlternatingFaceMapComplexOp (G : Aᵒᵖ ⥤ B) [G.Additive] (X : SimplicialObject A) :
    CochainComplex B ℕ :=
  ((G.rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    ((alternatingFaceMapComplex A).obj X)).unop

/-- The differential of `AlgebraicTopology.mapAlternatingFaceMapComplexOp` is the alternating
sum of the images of the face maps. -/
theorem mapAlternatingFaceMapComplexOp_d (G : Aᵒᵖ ⥤ B) [G.Additive] (X : SimplicialObject A)
    (n : ℕ) :
    (mapAlternatingFaceMapComplexOp G X).d n (n + 1) =
      ∑ j : Fin (n + 2), ((-1 : ℤ) ^ (j : ℕ) • G.map ((X.δ j).op) :
        (mapAlternatingFaceMapComplexOp G X).X n ⟶
          (mapAlternatingFaceMapComplexOp G X).X (n + 1)) := by
  show (((G.rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      ((alternatingFaceMapComplex A).obj X)).unop).d n (n + 1) = _
  rw [HomologicalComplex.unop_d, Functor.mapHomologicalComplex_obj_d,
    alternatingFaceMapComplex_obj_d]
  simp only [AlternatingFaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul,
    unop_sum, unop_zsmul]
  rfl

/-- The differential of the alternating-coface complex of a cosimplicial object is the
alternating sum of its coface maps. -/
@[sga "4 Vbis 2.3.9" "more general"]
private theorem alternatingCofaceMapComplex_obj_d (Y : CosimplicialObject B) (n : ℕ) :
    ((alternatingCofaceMapComplex B).obj Y).d n (n + 1) =
      AlternatingCofaceMapComplex.objD Y n := by
  show CochainComplex.of.d (fun m => Y.obj (SimplexCategory.mk m))
    (AlternatingCofaceMapComplex.objD Y) n (n + 1) = _
  exact CochainComplex.of_d _ _ _

/-- The two complexes of `AlgebraicTopology.alternatingCofaceMapComplexRightOpIso` have the same
differentials: both are the alternating sum of the images under `G` of the face maps of `X`. -/
theorem alternatingCofaceMapComplex_rightOp_d (G : Aᵒᵖ ⥤ B) [G.Additive]
    (X : SimplicialObject A) (n : ℕ) :
    ((alternatingCofaceMapComplex B).obj (X.rightOp ⋙ G)).d n (n + 1) =
      (mapAlternatingFaceMapComplexOp G X).d n (n + 1) :=
  (alternatingCofaceMapComplex_obj_d _ n).trans
    (mapAlternatingFaceMapComplexOp_d G X n).symm

/-- **A contravariant additive functor turns the alternating-face complex of a simplicial object
into the alternating-coface complex of the resulting cosimplicial object.** Both complexes have
`G(X_n)` in degree `n` and the alternating sum of the images of the face maps as differential, so
the comparison is the identity in every degree. -/
def alternatingCofaceMapComplexRightOpIso (G : Aᵒᵖ ⥤ B) [G.Additive] (X : SimplicialObject A) :
    (alternatingCofaceMapComplex B).obj (X.rightOp ⋙ G) ≅
      mapAlternatingFaceMapComplexOp G X :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    rintro i j (rfl : i + 1 = j)
    exact (Category.id_comp _).trans
      ((alternatingCofaceMapComplex_rightOp_d G X i).symm.trans (Category.comp_id _).symm))

end AlgebraicTopology

/-- The abelian internal-hom functor `ℋom(-, G)` is additive. -/
instance internalHomFunctor_additive {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{max u v}) : (internalHomFunctor J G).Additive where
  map_add {_ _} f g := by
    apply Sheaf.hom_ext_iff.mpr
    ext U a
    change Functor.whiskerLeft (Over.forget U.unop).op (f + g).unop.hom ≫ a =
      Functor.whiskerLeft (Over.forget U.unop).op f.unop.hom ≫ a +
        Functor.whiskerLeft (Over.forget U.unop).op g.unop.hom ≫ a
    rw [show Functor.whiskerLeft (Over.forget U.unop).op (f + g).unop.hom =
        Functor.whiskerLeft (Over.forget U.unop).op f.unop.hom +
          Functor.whiskerLeft (Over.forget U.unop).op g.unop.hom from rfl]
    exact Preadditive.add_comp _ _ _ _ _ _

namespace CategoryTheory.SimplicialSemiRepresentable

open AlgebraicTopology

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C))

/-- The simplicial presheaf of sets `F(K)` represented by a simplicial semi-representable
object: in degree `n` it is the coproduct of the presheaves represented by the components of
`K_n`. -/
def semiRepresentablePresheaf : SimplicialObject (Cᵒᵖ ⥤ Type u) := K ⋙ FormalCoproduct.yoneda

/-- The simplicial abelian sheaf `ℤ_{F(K)}^#` of free abelian sheaves on the simplicial presheaf
represented by `K`. -/
def freeAbelianSimplicial : SimplicialObject (Sheaf J AddCommGrpCat.{u}) :=
  ((SimplicialObject.whiskering _ _).obj (Presheaf.freeAbelianSheaf J)).obj
    (semiRepresentablePresheaf K)

/-- The chain complex `s(ℤ_{F(K)}^#)` of Stacks 01GB: the alternating-face complex of the
simplicial abelian sheaf of free abelian sheaves on `F(K)`. -/
def freeAbelianComplex : ChainComplex (Sheaf J AddCommGrpCat.{u}) ℕ :=
  (SimplicialObject.freeAbelianSheafComplexFunctor J).obj (semiRepresentablePresheaf K)

/-- The cochain complex `SheafHom(s(ℤ_{F(K)}^#), F)`: the image of the chain complex
`s(ℤ_{F(K)}^#)` under the abelian internal hom `ℋom(-, F)`. -/
def sheafHomComplex (F : Sheaf J AddCommGrpCat.{u}) :
    CochainComplex (Sheaf J AddCommGrpCat.{u}) ℕ :=
  (((internalHomFunctor J F).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (freeAbelianComplex J K)).unop

/-- The cosimplicial abelian sheaf `n ↦ ℋom(ℤ_{F(K_n)}^#, F)` whose alternating-coface complex is
`SheafHom(s(ℤ_{F(K)}^#), F)`. -/
def sheafHomCosimplicialObject (F : Sheaf J AddCommGrpCat.{u}) :
    CosimplicialObject (Sheaf J AddCommGrpCat.{u}) :=
  (freeAbelianSimplicial J K).rightOp ⋙ internalHomFunctor J F

/-- `SheafHom(s(ℤ_{F(K)}^#), F)` is the alternating-coface complex of the cosimplicial abelian
sheaf `n ↦ ℋom(ℤ_{F(K_n)}^#, F)`. -/
def sheafHomComplexIsoCofaceComplex (F : Sheaf J AddCommGrpCat.{u}) :
    (alternatingCofaceMapComplex (Sheaf J AddCommGrpCat.{u})).obj
        (sheafHomCosimplicialObject J K F) ≅
      sheafHomComplex J K F :=
  alternatingCofaceMapComplexRightOpIso (internalHomFunctor J F) (freeAbelianSimplicial J K)

variable [J.toCoverage.HasPullbacks]

/-- The abelian sheaf `a⁻¹F` on the total site of the simplicial site of Stacks 0D8B: the
inverse image of `F` along the total augmentation. -/
def totalAbelianInverseImage (F : Sheaf J AddCommGrpCat.{u}) :
    Sheaf (situation J K).totalTopology AddCommGrpCat.{u} :=
  (SimplicialSiteSituation.Augmentation.totalInverseImageAb (situation J K) (Cat.of C) J
    (situationAugmentation J K)).obj F

/-- The cosimplicial abelian sheaf `n ↦ a_{n,*}a_n⁻¹F` on `(C, J)` underlying the Čech complex
of Stacks 0D79 for the augmentation of Stacks 0D8B at `a⁻¹F`. -/
def cechCosimplicialObject (F : Sheaf J AddCommGrpCat.{u}) :
    CosimplicialObject (Sheaf J AddCommGrpCat.{u}) :=
  SimplicialSiteSituation.Augmentation.abelianCechDiagram (situation J K) (Cat.of C) J
    (situationAugmentation J K) (totalAbelianInverseImage J K F)

/-- The Čech complex of Stacks 0D79 for the augmentation of Stacks 0D8B at `a⁻¹F`:

`a_{0,*}a_0⁻¹F ⟶ a_{1,*}a_1⁻¹F ⟶ a_{2,*}a_2⁻¹F ⟶ …`

the alternating-coface complex of the cosimplicial abelian sheaf `n ↦ a_{n,*}a_n⁻¹F`. -/
def cechComplex (F : Sheaf J AddCommGrpCat.{u}) :
    CochainComplex (Sheaf J AddCommGrpCat.{u}) ℕ :=
  (alternatingCofaceMapComplex (Sheaf J AddCommGrpCat.{u})).obj (cechCosimplicialObject J K F)

/-- The complex of Stacks 0D79 for the augmentation of Stacks 0D8B at `a⁻¹F`, namely

`0 ⟶ a_*a⁻¹F ⟶ a_{0,*}a_0⁻¹F ⟶ a_{1,*}a_1⁻¹F ⟶ …`,

is `CategoryTheory.SimplicialSemiRepresentable.cechComplex` augmented by the projection of the
direct image `a_*a⁻¹F` along the total augmentation onto `a_{0,*}a_0⁻¹F`. -/
theorem augmentedCechComplex_eq_augment_cechComplex (F : Sheaf J AddCommGrpCat.{u}) :
    SimplicialSiteSituation.Augmentation.augmentedCechComplex (situation J K) (Cat.of C) J
        (situationAugmentation J K) (totalAbelianInverseImage J K F) =
      (cechComplex J K F).augment
        ((SimplicialSiteSituation.Augmentation.abelianCechCone (situation J K) (Cat.of C) J
          (situationAugmentation J K) (totalAbelianInverseImage J K F)).π.app
            (SimplexCategory.mk 0))
        (CosimplicialObject.coneLeg_comp_d _ _) :=
  rfl

end CategoryTheory.SimplicialSemiRepresentable

end
