module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DiagonalMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism

/-!
# The total tensor complex and a degreewise family of maps of the second factor

Let `X` be a ringed site and let `A`, `B`, `B'` be complexes of `O`-modules. A *morphism of
complexes* `B ⟶ B'` induces a morphism `Tot(A ⊗_O B) ⟶ Tot(A ⊗_O B')` of complexes, namely
`AlgebraicGeometry.RingedSite.tensorTotalMap`. This file provides what is needed when the maps
`B^q ⟶ B'^q` are given for every `q` but do **not** commute with the differentials: a morphism

`Tot(A ⊗_O B)^n ⟶ Tot(A ⊗_O B')^n`

in each single total degree, acting on the summand of index `(p, q)` through the given map in
degree `q`. Nothing else can be expected of such a family, and nothing more is needed: the
degreewise splittings of a short complex are data of exactly this kind, which is why the file
exists.

The corresponding tool for the internal Hom complex is
`AlgebraicGeometry.RingedSite.homDegreeFamilyMap`, and the arrangement here follows it.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorTotalDegreeFamilyMap`: the morphism above.

## Main results

* `AlgebraicGeometry.RingedSite.tensorTotal_degree_hom_ext`: a morphism out of the degree-`n`
  term of a total tensor complex is determined by its values on the homogeneous local pure
  tensors. This is the one-degree form of
  `AlgebraicGeometry.RingedSite.tensorTotal_hom_ext`.
* `AlgebraicGeometry.RingedSite.tensorTotalDegreeFamilyMap_tensorTotalSectionAt`: the morphism
  sends the pure tensor of `a` and `b` to the pure tensor of `a` and the image of `b`. Every
  identity between these morphisms is proved from this and from the ext lemma above.
* `AlgebraicGeometry.RingedSite.tensorTotalMap_comp_tensorTotalDegreeFamilyMap` and its three
  companions: composing with a morphism of complexes on either side gives the family map of the
  composed family, the family of identities gives the identity, and the construction is additive
  in the family. These are what transport the axioms of a splitting of the second factor to the
  total tensor complex.

## Implementation notes

The construction is the one every morphism out of a total tensor complex in this development
uses: the summandwise data is assembled at the level of presheaves of modules by
`HomologicalComplex.mapBifunctorDesc`, and the result is sheafified. The degreewise
sheafification being a functor, no lifting is involved, and the value on a pure tensor is
`AlgebraicGeometry.RingedSite.sheafification_map_unit_apply` followed by
`HomologicalComplex.ι_mapBifunctorDesc`.

## References

* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})

/-- Applying a sum of morphisms of sheaves of modules to a section. -/
private lemma add_val_app_apply₄
    {P Q : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ ψ : P ⟶ Q)
    (W : X.Cᵒᵖ) (x : P.val.obj W) :
    ((φ + ψ).val.app W) x = (φ.val.app W) x + (ψ.val.app W) x := rfl

variable (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  {B B' B'' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **A morphism out of the degree-`n` term of a total tensor complex is determined by its
values on the homogeneous local pure tensors.** This is the one-degree form of
`AlgebraicGeometry.RingedSite.tensorTotal_hom_ext`, which is about morphisms of complexes; the
identities proved in this development between single-degree morphisms — the splitting axioms of
a short complex of total complexes — are not identities of chain maps. -/
lemma tensorTotal_degree_hom_ext
    {W : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (n : ℤ)
    {α β : (tensorTotal X A B).X n ⟶ W}
    (hab : ∀ (U : X.C) (p q : ℤ) (h : p + q = n) (a : (A.X p).val.obj (op U))
      (b : (B.X q).val.obj (op U)),
      α.val.app (op U) (tensorTotalSectionAt X A B U p q n h a b) =
        β.val.app (op U) (tensorTotalSectionAt X A B U p q n h a b)) :
    α = β := by
  refine ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).homEquiv _ _).injective ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun p q hpq ↦ ?_
  refine PresheafOfModules.hom_ext fun U ↦ ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
  exact hab U.unop p q (by simpa using hpq) a b

/-- The presheaf-level degree-`n` morphism assembled from a degreewise family of maps of the
second factor: on the summand of index `(p, q)` it is the given map in degree `q`, tensored
with the identity of `A^p`, followed by the inclusion of that summand. -/
def tensorTotalDegreePresheafMap (g : ∀ q, B.X q ⟶ B'.X q) (n : ℤ) :
    (tensorTotalPresheaf X A B).X n ⟶ (tensorTotalPresheaf X A B').X n :=
  HomologicalComplex.mapBifunctorDesc fun p q h =>
    ((curriedTensor (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
        ((underlyingPresheafComplex X A).X p)).map (g q).val ≫
      ιTensorTotalPresheaf X A B' p q n (by simpa using h)

/-- **The degree-`n` morphism of total tensor complexes induced by a degreewise family of maps
of the second factor.** The family is not required to commute with the differentials, and
accordingly this is a morphism in one total degree and not a morphism of complexes. -/
def tensorTotalDegreeFamilyMap (g : ∀ q, B.X q ⟶ B'.X q) (n : ℤ) :
    (tensorTotal X A B).X n ⟶ (tensorTotal X A B').X n :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
    (tensorTotalDegreePresheafMap X A g n)

/-- **The degreewise family map on a local pure tensor**: it acts on the second factor, through
the member of the family of that degree, and leaves the first factor and the total degree
alone. -/
lemma tensorTotalDegreeFamilyMap_tensorTotalSectionAt (g : ∀ q, B.X q ⟶ B'.X q) (n : ℤ)
    (U : X.C) (p q : ℤ) (h : p + q = n) (a : (A.X p).val.obj (op U))
    (b : (B.X q).val.obj (op U)) :
    (tensorTotalDegreeFamilyMap X A g n).val.app (op U)
        (tensorTotalSectionAt X A B U p q n h a b) =
      tensorTotalSectionAt X A B' U p q n h a ((g q).val.app (op U) b) := by
  have key := congrArg (fun z : tensorTotalPresheafTerm X A B p q ⟶
      (tensorTotalPresheaf X A B').X n ↦
    z.app (op U) (a ⊗ₜ[(Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)] b))
    (HomologicalComplex.ι_mapBifunctorDesc
      (fun p q (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (p, q) = n) =>
        ((curriedTensor
            (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
            ((underlyingPresheafComplex X A).X p)).map (g q).val ≫
          ιTensorTotalPresheaf X A B' p q n (by simpa using h))
      p q (by simpa using h))
  refine Eq.trans (sheafification_map_unit_apply X
    (tensorTotalDegreePresheafMap X A g n) (op U) _) ?_
  exact congrArg
    (fun z ↦ ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
      ((tensorTotalPresheaf X A B').X n)).app (op U) z) key

/-! ### The calculus of the degreewise family maps

Composing a degreewise family map with a morphism of complexes, or with another family map, is
again a degreewise family map, and the operation is additive in the family. These four laws are
everything needed to transport the axioms of a splitting from the second factor to the total
tensor complex, and each is proved by testing on a local pure tensor. -/

/-- A morphism of complexes followed by a degreewise family map is the family map of the
composed family. -/
lemma tensorTotalMap_comp_tensorTotalDegreeFamilyMap (φ : B ⟶ B')
    (g : ∀ q, B'.X q ⟶ B''.X q) (n : ℤ) :
    (tensorTotalMap X (𝟙 A) φ).f n ≫ tensorTotalDegreeFamilyMap X A g n =
      tensorTotalDegreeFamilyMap X A (fun q => φ.f q ≫ g q) n := by
  refine tensorTotal_degree_hom_ext X A n fun U p q h a b ↦ ?_
  rw [comp_val_app_apply', tensorTotalMap_tensorTotalSectionAt,
    tensorTotalDegreeFamilyMap_tensorTotalSectionAt,
    tensorTotalDegreeFamilyMap_tensorTotalSectionAt, comp_val_app_apply']
  rfl

/-- A degreewise family map followed by a morphism of complexes is the family map of the
composed family. -/
lemma tensorTotalDegreeFamilyMap_comp_tensorTotalMap (g : ∀ q, B.X q ⟶ B'.X q) (φ : B' ⟶ B'')
    (n : ℤ) :
    tensorTotalDegreeFamilyMap X A g n ≫ (tensorTotalMap X (𝟙 A) φ).f n =
      tensorTotalDegreeFamilyMap X A (fun q => g q ≫ φ.f q) n := by
  refine tensorTotal_degree_hom_ext X A n fun U p q h a b ↦ ?_
  rw [comp_val_app_apply', tensorTotalDegreeFamilyMap_tensorTotalSectionAt,
    tensorTotalMap_tensorTotalSectionAt, tensorTotalDegreeFamilyMap_tensorTotalSectionAt,
    comp_val_app_apply']
  rfl

/-- The family map of the identities is the identity. -/
lemma tensorTotalDegreeFamilyMap_id (n : ℤ) :
    tensorTotalDegreeFamilyMap X A (fun q => 𝟙 (B.X q)) n = 𝟙 ((tensorTotal X A B).X n) := by
  refine tensorTotal_degree_hom_ext X A n fun U p q h a b ↦ ?_
  rw [tensorTotalDegreeFamilyMap_tensorTotalSectionAt]
  rfl

/-- The family map is additive in the family. -/
lemma tensorTotalDegreeFamilyMap_add (g g' : ∀ q, B.X q ⟶ B'.X q) (n : ℤ) :
    tensorTotalDegreeFamilyMap X A (fun q => g q + g' q) n =
      tensorTotalDegreeFamilyMap X A g n + tensorTotalDegreeFamilyMap X A g' n := by
  refine tensorTotal_degree_hom_ext X A n fun U p q h a b ↦ ?_
  rw [tensorTotalDegreeFamilyMap_tensorTotalSectionAt, add_val_app_apply₄, add_val_app_apply₄,
    tensorTotalDegreeFamilyMap_tensorTotalSectionAt,
    tensorTotalDegreeFamilyMap_tensorTotalSectionAt, tensorTotalSectionAt_add_right]

end AlgebraicGeometry.RingedSite

end
