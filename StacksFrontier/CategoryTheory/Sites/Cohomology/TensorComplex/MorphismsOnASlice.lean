module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.MonoidalStructureOnPresheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.MorphismsOutOfASheafifiedPresheaf
import StacksCore.Tactic.StacksAttribute

/-! # Morphisms on a slice out of the total tensor complex

Let `(C, O)` be a ringed site, let `K` and `L` be complexes of `O`-modules and let `U` be an
object of `C`. The degree-`c` term of the total tensor complex `Tot(K ⊗_O L)` of Stacks 06YM is
the coproduct, over the pairs `t + r = c`, of the sheaf tensor products `K^t ⊗_O L^r`, and each
of those is the sheafification of the objectwise tensor product of the underlying presheaves.
This file assembles the two universal properties into one: a morphism of sheaves of
`O|_U`-modules out of `(Tot(K ⊗_O L)^c)|_U` is the same thing as a family, indexed by the pairs
`t + r = c`, of morphisms of presheaves of `O|_U`-modules out of `(K^t ⊗ L^r)|_U`, and such a
morphism is determined by its values on the restricted pure tensors.

This is what a *cochain* out of the total tensor complex on a slice site is built from, and so
it is the missing half of the currying isomorphism of Stacks 0A90: the sections of the internal
Hom complex `SheafHom(Tot(K ⊗_O L), M)` over `U` are the degree-`n` cochains from
`Tot(K ⊗_O L)|_U` to `M|_U`, whose components are exactly the morphisms described here.

## Main definitions

* `CategoryTheory.GradedObject.descMapObjOfPreserves`: a morphism out of the image of
  `GradedObject.mapObj` under a functor preserving the relevant coproducts, from a family of
  morphisms out of the images of the summands.
* `AlgebraicGeometry.RingedSite.tensorComplexOverι`: the restriction to the site over `U` of
  the inclusion of the `(t, r)` summand.
* `AlgebraicGeometry.RingedSite.tensorComplexOverDesc`: a morphism out of
  `(Tot(K ⊗_O L)^c)|_U` from a family of morphisms out of the restricted summands.
* `AlgebraicGeometry.RingedSite.tensorComplexOverMk`: the same, starting one level lower from
  presheaf-level morphisms out of the restricted objectwise tensor products.
* `AlgebraicGeometry.RingedSite.tensorComplexOverSection`: the restricted pure tensor of a
  section of `K^t` and a section of `L^r` over an object of the slice site.

## Main results

* `CategoryTheory.GradedObject.ι_descMapObjOfPreserves` and
  `CategoryTheory.GradedObject.mapObj_ext_of_preserves`: the universal property.
* `AlgebraicGeometry.RingedSite.ι_tensorComplexOverDesc` and
  `AlgebraicGeometry.RingedSite.tensorComplexOver_hom_ext`: the universal property of the
  restricted coproduct.
* `AlgebraicGeometry.RingedSite.tensorComplexOverMk_section`: `tensorComplexOverMk f` takes the
  restricted pure tensor to the value of `f` on it.
* `AlgebraicGeometry.RingedSite.tensorComplexOverSection_hom_ext`: a morphism out of
  `(Tot(K ⊗_O L)^c)|_U` is determined by its values on the restricted pure tensors.

## Implementation notes

Two facts make this cheap, and both are already in the tree. Restriction of sheaves of modules
to a slice preserves colimits — which is *not* formal, since that functor is a right adjoint and
is known to be a left adjoint only over a site with pullbacks — and is
`Stacks.SheafOfModules.pushforward_preservesColimits`. And a morphism on a slice out of a
sheafification is a morphism out of the presheaf, which is
`AlgebraicGeometry.RingedSite.overSheafifyLift`. The coproduct of `GradedObject.mapObj` is
transported across the restriction by `Limits.isColimitCofanMkObjOfIsColimit`, which is the
only step that needs the index type to be shrunk into the module universe.

Tag 03EM's restriction functor `restrFun` and
`AlgebraicGeometry.RingedSite.overPresheaf` are the same term, so the
retyping vocabulary of `StacksDraft.Ch18.Sec27.TensorInternalHomCurrying` —
`restrTensorHom`, `restrTmul`, `restrSection` — applies verbatim to the presheaf-level
morphisms this file consumes, and is the intended way to produce them from bilinear maps on
sections. Nothing is re-derived here.

The monoidal structure on presheaves of modules is the one of
`StacksDraft.Ch21.Sec34.RingedSiteMonoidalInstances`, switched on file-locally exactly as in
`StacksDraft.Ch21.Sec34.TensorTotalComplex`; `sheafTensor_eq_sheafifyModules` records that
Section 17's sheaf tensor product is the sheafification of that objectwise tensor product, which
is what lets `overSheafifyLift` apply to each summand with no transport.

## References

* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace CategoryTheory.GradedObject

variable {I J : Type*} {C D : Type*} [Category C] [Category D]
  (G : C ⥤ D) (Z : GradedObject I C) (p : I → J) [Z.HasMap p] (j : J)
  [PreservesColimit (Discrete.functor (Z.mapObjFun p j)) G]

/-- A functor preserving the coproduct of the `j`-th summands carries the coproduct
decomposition of `Z.mapObj p j` to a coproduct decomposition of its image. -/
def isColimitMapCofanMapObj :
    IsColimit (Cofan.mk (G.obj (Z.mapObj p j))
      (fun i : p ⁻¹' {j} => G.map (Z.ιMapObj p i.1 j i.2))) :=
  Limits.isColimitCofanMkObjOfIsColimit G _ _ (Z.isColimitCofanMapObj p j)

variable {A : D}

/-- The morphism `G.obj (Z.mapObj p j) ⟶ A` determined by a family of morphisms
`G.obj (Z i) ⟶ A` for the `i` with `p i = j`. -/
def descMapObjOfPreserves (φ : ∀ (i : I) (_ : p i = j), G.obj (Z i) ⟶ A) :
    G.obj (Z.mapObj p j) ⟶ A :=
  Cofan.IsColimit.desc (isColimitMapCofanMapObj G Z p j) (fun ⟨i, hi⟩ => φ i hi)

/-- `descMapObjOfPreserves φ` restricts to `φ i` on the image of the `i`-th summand. -/
lemma ι_descMapObjOfPreserves (φ : ∀ (i : I) (_ : p i = j), G.obj (Z i) ⟶ A)
    (i : I) (hi : p i = j) :
    G.map (Z.ιMapObj p i j hi) ≫ descMapObjOfPreserves G Z p j φ = φ i hi :=
  Cofan.IsColimit.fac (isColimitMapCofanMapObj G Z p j) _ ⟨i, hi⟩

/-- Two morphisms out of `G.obj (Z.mapObj p j)` which agree on the image of every summand are
equal. -/
lemma mapObj_ext_of_preserves {f g : G.obj (Z.mapObj p j) ⟶ A}
    (h : ∀ (i : I) (hi : p i = j),
      G.map (Z.ιMapObj p i j hi) ≫ f = G.map (Z.ιMapObj p i j hi) ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (isColimitMapCofanMapObj G Z p j) _ _ (fun ⟨i, hi⟩ => h i hi)

end CategoryTheory.GradedObject

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] ringSheafOverSectionsCommRing

/-- Section 17's tensor product of sheaves of modules is the sheafification of the objectwise
tensor product of the underlying presheaves of modules. -/
lemma sheafTensor_eq_sheafifyModules
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).obj B =
      sheafifyModules X (A.val ⊗ B.val) :=
  rfl

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

variable (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- The bicomplex of sheaf tensor products of the terms of `K` and `L`, whose total complex is
the total tensor complex of Stacks 06YM. It is an abbreviation, so that the coproduct
decomposition of its total complex is matched by instance search. -/
abbrev tensorBicomplex :
    HomologicalComplex₂ (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj K).obj L

/-- The map from bidegrees to total degrees. -/
abbrev tensorTotalShape : ℤ × ℤ → ℤ :=
  ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

omit [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u,
  u, u} X.O))
    (ComplexShape.up ℤ)),
  HomologicalComplex.HasMapBifunctor K₁ K₂
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- Restriction of sheaves of modules to the site over `U` preserves the coproducts whose
summands are indexed by the bidegrees of a fixed total degree. This is
`Stacks.SheafOfModules.pushforward_preservesColimits` for `Over.forget U`, shrunk to the
universe of the bidegrees. -/
lemma preservesColimit_overFunctor_tensorBicomplex (c : ℤ) :
    PreservesColimit
      (Discrete.functor ((tensorBicomplex X K L).toGradedObject.mapObjFun tensorTotalShape c))
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) := by
  have h : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    Stacks.SheafOfModules.pushforward_preservesColimits (J := X.J.over U) (K := X.J)
      (Over.forget U) (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
  have h0 : PreservesColimitsOfSize.{0, 0}
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
    preservesColimitsOfSize_shrink _
  exact h0.preservesColimitsOfShape.preservesColimit

attribute [local instance] preservesColimit_overFunctor_tensorBicomplex

/-- The restriction to the site over `U` of the inclusion of the `(t, r)` summand into the
degree-`c` term of the total tensor complex. -/
abbrev tensorComplexOverι (t r c : ℤ) (htr : t + r = c) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj (K.X t)).obj
        (L.X r)).over U ⟶
      ((((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.O).obj K).obj L).X c).over U :=
  (HomologicalComplex.ιMapBifunctor
    (show CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ from K)
    (show CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ from L)
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
    (ComplexShape.up ℤ)
    t r c (by simpa using htr)).over U

variable {X U K L}
variable {N : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)} {c : ℤ}

/-- The morphism out of the restriction to the site over `U` of the degree-`c` term of the
total tensor complex determined by a family of morphisms out of the restricted summands. -/
def tensorComplexOverDesc
    (f : ∀ (t r : ℤ) (_ : t + r = c),
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj (K.X t)).obj
        (L.X r)).over U ⟶ N) :
    ((((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.O).obj K).obj L).X c).over U ⟶ N :=
  GradedObject.descMapObjOfPreserves
    (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) from
      SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (tensorBicomplex X K L).toGradedObject tensorTotalShape c
    (fun i hi => f i.1 i.2 (by simpa using hi))

/-- `tensorComplexOverDesc f` restricts to `f t r` on the `(t, r)` summand. -/
lemma ι_tensorComplexOverDesc
    (f : ∀ (t r : ℤ) (_ : t + r = c),
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj (K.X t)).obj
        (L.X r)).over U ⟶ N)
    (t r : ℤ) (htr : t + r = c) :
    tensorComplexOverι X U K L t r c htr ≫ tensorComplexOverDesc f = f t r htr :=
  GradedObject.ι_descMapObjOfPreserves
    _
    (tensorBicomplex X K L).toGradedObject tensorTotalShape c _ (t, r) (by simpa using htr)

/-- Two morphisms out of the restriction to the site over `U` of the degree-`c` term of the
total tensor complex which agree on every summand are equal. -/
lemma tensorComplexOver_hom_ext
    {φ ψ :
      ((((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.O).obj K).obj L).X c).over U ⟶ N}
    (h : ∀ (t r : ℤ) (htr : t + r = c),
      tensorComplexOverι X U K L t r c htr ≫ φ = tensorComplexOverι X U K L t r c htr ≫ ψ) :
    φ = ψ :=
  GradedObject.mapObj_ext_of_preserves
    _
    (tensorBicomplex X K L).toGradedObject tensorTotalShape c
    (fun i hi => h i.1 i.2 (by simpa using hi))

/-- The morphism out of the restriction to the site over `U` of the degree-`c` term of the total
tensor complex determined by a family of *presheaf-level* morphisms out of the restricted
objectwise tensor products of the underlying presheaves. -/
def tensorComplexOverMk
    (f : ∀ (t r : ℤ) (_ : t + r = c),
      overPresheaf X U ((K.X t).val ⊗ (L.X r).val) ⟶ N.val) :
    ((((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.O).obj K).obj L).X c).over U ⟶ N :=
  tensorComplexOverDesc (fun t r htr => overSheafifyLift X U (f t r htr))

/-- The restricted pure tensor of a section of `K^t` and a section of `L^r` over an object
`g : W ⟶ U` of the site over `U`, as a section of the degree-`c` term of the total tensor
complex restricted to that site. -/
def tensorComplexOverSection (t r c : ℤ) (htr : t + r = c) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    ((((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.O).obj K).obj L).X c).over U
      |>.val.obj (op (Over.mk g)) :=
  (tensorComplexOverι X U K L t r c htr).val.app (op (Over.mk g))
    ((overSheafifyUnit X U ((K.X t).val ⊗ (L.X r).val)).app (op (Over.mk g))
      (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l))

/-- `tensorComplexOverMk f` takes the restricted pure tensor of `k` and `l` to the value of
`f t r` on their tensor. -/
lemma tensorComplexOverMk_section
    (f : ∀ (t r : ℤ) (_ : t + r = c),
      overPresheaf X U ((K.X t).val ⊗ (L.X r).val) ⟶ N.val)
    (t r : ℤ) (htr : t + r = c) {W : X.C} (g : W ⟶ U)
    (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)) :
    (tensorComplexOverMk f).val.app (op (Over.mk g))
        (tensorComplexOverSection t r c htr g k l) =
      (f t r htr).app (op (Over.mk g))
        (k ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)] l) := by
  refine (congrArg (fun z : _ ⟶ N => z.val.app (op (Over.mk g)) _)
    (ι_tensorComplexOverDesc (fun t r htr => overSheafifyLift X U (f t r htr)) t r htr)).trans ?_
  exact overSheafifyLift_apply X U (f t r htr) (op (Over.mk g)) _

/-- A morphism out of the restriction to the site over `U` of the degree-`c` term of the total
tensor complex is determined by its values on the restricted pure tensors. -/
lemma tensorComplexOverSection_hom_ext
    {φ ψ :
      ((((Stacks.SheafOfModules.Tensor.tensorComplex.{u, u, u} X.O).obj K).obj L).X c).over U ⟶ N}
    (h : ∀ (t r : ℤ) (htr : t + r = c) (W : X.C) (g : W ⟶ U)
      (k : (K.X t).val.obj (op W)) (l : (L.X r).val.obj (op W)),
      φ.val.app (op (Over.mk g)) (tensorComplexOverSection t r c htr g k l) =
        ψ.val.app (op (Over.mk g)) (tensorComplexOverSection t r c htr g k l)) :
    φ = ψ := by
  refine tensorComplexOver_hom_ext fun t r htr => ?_
  refine overSheafify_hom_ext X U ?_
  refine PresheafOfModules.hom_ext fun V => ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun k l => ?_
  exact h t r htr V.unop.left V.unop.hom k l

end AlgebraicGeometry.RingedSite

end
