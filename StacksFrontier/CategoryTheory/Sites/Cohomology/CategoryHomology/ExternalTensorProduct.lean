module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Discrete.SumsProducts
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.HomologyOnACategory
public import StacksCore.Tactic.StacksAttribute

/-!
# External tensor products of diagrams of modules on a product of categories

Let `C₁` and `C₂` be small categories and `B` a commutative ring. Restriction along the two
projections of `C₁ × C₂` turns a pair of diagrams of `B`-modules on `C₁ᵒᵖ` and `C₂ᵒᵖ` into one
diagram on `(C₁ × C₂)ᵒᵖ`, their external tensor product. Its colimit is the tensor product of
the two colimits, and the colimit of a free diagram on a representable is its coefficient
module.

## Main definitions

* `Stacks.CategoryHomology.projFstInverseImage` and
  `Stacks.CategoryHomology.projSndInverseImage`: restriction along the two projections.
* `Stacks.CategoryHomology.externalTensor`: the diagram `(U, V) ↦ F(U) ⊗_B G(V)`.
* `Stacks.CategoryHomology.sigmaTensorSigmaIso`: tensoring a coproduct of copies of `P` with a
  coproduct of copies of `Q` gives a coproduct of copies of `P ⊗ Q`.

## Main results

* `Stacks.CategoryHomology.colimExternalTensorIso`: the colimit of an external tensor product
  is the tensor product of the colimits, natural in both variables.
* `Stacks.CategoryHomology.colimFreeYonedaIso`: the colimit of the free diagram on a
  representable with coefficients `P` is `P`.
* `Stacks.CategoryHomology.externalTensorFreeYonedaIso`: the external tensor product of the free
  diagrams on `U` and on `V` is the free diagram on `(U, V)`.

## Scope of the Tag 08QB clauses

Tag 08QB asserts `L(π₁ × π₂)_!(g₁⁻¹K₁ ⊗^L_B̲ g₂⁻¹K₂) = Lπ_{1,!}K₁ ⊗^L_B Lπ_{2,!}K₂` in `D(B)`.
What is carried here is the identity with both derived functors replaced by the underived ones
(`colimExternalTensorIso`, natural in both variables by `colimExternalTensorIso_naturality`) and
the computation its proof makes on the generators (`externalTensorFreeYonedaIso`). The derived
identity itself needs a derived tensor product on the derived category of diagrams of
`B`-modules, which does not exist yet; it is not covered.

## References

* [Stacks Project, Tag 08QB](https://stacks.math.columbia.edu/tag/08QB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.MonoidalCategory.ExternalProduct

namespace Stacks.CategoryHomology

universe u₁ u₂ w uA vA t₁ t₂

section InverseImage

variable (C₁ : Type u₁) (C₂ : Type u₂) [SmallCategory C₁] [SmallCategory C₂]
  (B : Type w) [CommRing B]

/-- Inverse image of a presheaf of `B̲`-modules along the first projection of a product of
chaotic sites: restriction along `(C₁ × C₂)ᵒᵖ ⥤ C₁ᵒᵖ`. -/
def projFstInverseImage :
    (C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) ⥤ ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) :=
  (Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.fst C₁ C₂).op

/-- Inverse image of a presheaf of `B̲`-modules along the second projection of a product of
chaotic sites: restriction along `(C₁ × C₂)ᵒᵖ ⥤ C₂ᵒᵖ`. -/
def projSndInverseImage :
    (C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) ⥤ ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) :=
  (Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.snd C₁ C₂).op

variable {C₁ C₂ B}

/-- Sections of `g₁⁻¹F` over `(U, V)` are the sections of `F` over `U`. -/
@[simp]
lemma projFstInverseImage_obj_obj (F : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B)
    (Z : (C₁ × C₂)ᵒᵖ) :
    ((projFstInverseImage C₁ C₂ B).obj F).obj Z = F.obj (op Z.unop.1) :=
  rfl

/-- Sections of `g₂⁻¹G` over `(U, V)` are the sections of `G` over `V`. -/
@[simp]
lemma projSndInverseImage_obj_obj (G : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B)
    (Z : (C₁ × C₂)ᵒᵖ) :
    ((projSndInverseImage C₁ C₂ B).obj G).obj Z = G.obj (op Z.unop.2) :=
  rfl

/-- For presheaves of `B̲`-modules `F` on `C₁` and `G` on `C₂`, the presheaf `g₁⁻¹F ⊗ g₂⁻¹G`
on the product category, whose value at `(U, V)` is `F(U) ⊗_B G(V)`. -/
def externalTensor (F : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B)
    (G : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) :
    (C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B :=
  (projFstInverseImage C₁ C₂ B).obj F ⊗ (projSndInverseImage C₁ C₂ B).obj G

/-- The map of external tensor products induced by maps in both variables. -/
def externalTensorMap {F F' : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B}
    {G G' : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B} (φ : F ⟶ F') (ψ : G ⟶ G') :
    externalTensor F G ⟶ externalTensor F' G' :=
  (projFstInverseImage C₁ C₂ B).map φ ⊗ₘ (projSndInverseImage C₁ C₂ B).map ψ

/-- Sections of the external tensor product over `(U, V)` are `F(U) ⊗_B G(V)`. -/
@[simp]
lemma externalTensor_obj (F : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B)
    (G : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) (Z : (C₁ × C₂)ᵒᵖ) :
    (externalTensor F G).obj Z = F.obj (op Z.unop.1) ⊗ G.obj (op Z.unop.2) :=
  rfl

/-- The external tensor product on the opposite of a product of categories is the external
product of diagrams on the product of the opposite categories. -/
def externalTensorIsoExternalProduct (F : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B)
    (G : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) :
    externalTensor F G ≅ (prodOpEquiv (D := C₂) C₁).functor ⋙ F ⊠ G :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} f ↦ by
    simpa [externalTensor, projFstInverseImage, projSndInverseImage] using
      tensorHom_def (((projFstInverseImage C₁ C₂ B).obj F).map f)
        (((projSndInverseImage C₁ C₂ B).obj G).map f))

/-- The comparison with the external product of diagrams is the identity on sections. -/
@[simp]
lemma externalTensorIsoExternalProduct_hom_app (F : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B)
    (G : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) (Z : (C₁ × C₂)ᵒᵖ) :
    (externalTensorIsoExternalProduct F G).hom.app Z = 𝟙 ((externalTensor F G).obj Z) :=
  rfl

end InverseImage

section ProductFormula

variable {C₁ : Type u₁} {C₂ : Type u₂} [SmallCategory C₁] [SmallCategory C₂]
  {B : Type w} [CommRing B]

/-- **Stacks 08QB, the identity with the derived functors replaced by the underived ones.** The
colimit over the product of two opposite categories of an external tensor product of diagrams is
the tensor product of the two colimits. -/
@[stacks 08QB "the identity with both derived functors replaced by the underived ones, \
`π_!(g₁⁻¹F ⊗_B̲ g₂⁻¹G) ≅ π_{1,!}F ⊗_B π_{2,!}G` for diagrams of `B`-modules, with `π_!` the \
colimit over the site of Tag 08PF; the derived identity is not covered"]
def colimExternalTensorIso (F : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B)
    (G : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) :
    (colim : ((C₁ × C₂)ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) ⥤ _).obj (externalTensor F G) ≅
      (colim : (C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) ⥤ _).obj F ⊗
        (colim : (C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) ⥤ _).obj G :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit (externalTensor F G))
    ((IsColimit.precomposeHomEquiv (externalTensorIsoExternalProduct F G) _).symm
      ((IsColimit.tensor₂ (colimit.isColimit F) (colimit.isColimit G)).whiskerEquivalence
        (prodOpEquiv (D := C₂) C₁)))

/-- The product formula sends the colimit cocone of the external tensor product at `(U, V)` to
the tensor product of the colimit cocones at `U` and at `V`. -/
@[reassoc]
lemma ι_comp_colimExternalTensorIso_hom (F : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B)
    (G : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B) (Z : (C₁ × C₂)ᵒᵖ) :
    colimit.ι (externalTensor F G) Z ≫ (colimExternalTensorIso F G).hom =
      colimit.ι F (op Z.unop.1) ⊗ₘ colimit.ι G (op Z.unop.2) := by
  refine (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ Z).trans ?_
  exact (Category.id_comp _).trans
    (tensorHom_def (colimit.ι F (op Z.unop.1)) (colimit.ι G (op Z.unop.2))).symm

/-- The product formula is natural in both presheaves. -/
lemma colimExternalTensorIso_naturality {F F' : C₁ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B}
    {G G' : C₂ᵒᵖ ⥤ ModuleCat.{max u₁ u₂ w} B} (φ : F ⟶ F') (ψ : G ⟶ G') :
    colim.map (externalTensorMap φ ψ) ≫ (colimExternalTensorIso F' G').hom =
      (colimExternalTensorIso F G).hom ≫ (colim.map φ ⊗ₘ colim.map ψ) := by
  refine colimit.hom_ext fun Z ↦ ?_
  have h : (colimit.ι F (op Z.unop.1) ⊗ₘ colimit.ι G (op Z.unop.2)) ≫
      (colim.map φ ⊗ₘ colim.map ψ) =
      (φ.app (op Z.unop.1) ⊗ₘ ψ.app (op Z.unop.2)) ≫
        (colimit.ι F' (op Z.unop.1) ⊗ₘ colimit.ι G' (op Z.unop.2)) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, colimit.ι_map, colimit.ι_map]
  rw [← Category.assoc, colimit.ι_map, Category.assoc,
    ι_comp_colimExternalTensorIso_hom, ← Category.assoc,
    ι_comp_colimExternalTensorIso_hom]
  exact h.symm

end ProductFormula

section Generators

variable {C : Type u₁} [SmallCategory C] {A : Type uA} [Category.{vA} A]
  [HasCoproducts.{u₁} A] [HasColimitsOfShape Cᵒᵖ A]

/-- The colimit over `Cᵒᵖ` of the free presheaf on a representable with coefficients `P`
is `P`. -/
def colimFreeYonedaIso (U : C) (P : A) :
    (colim : (Cᵒᵖ ⥤ A) ⥤ A).obj (Presheaf.freeYoneda U P) ≅ P :=
  Functor.CorepresentableBy.uniqueUpToIso
    (F := coyoneda.obj (op P))
    { homEquiv := fun {_} ↦
        (colimConstAdj.homEquiv _ _).trans Presheaf.freeYonedaHomEquiv
      homEquiv_comp := fun g f ↦ by
        dsimp
        rw [Adjunction.homEquiv_naturality_right, Presheaf.freeYonedaHomEquiv_comp]
        rfl }
    { homEquiv := Equiv.refl _ }

end Generators

section Distributivity

variable {A : Type uA} [Category.{vA} A] [MonoidalCategory A]
  {I : Type t₁} {J : Type t₂} (P Q : A)
  [HasCoproduct fun _ : I ↦ P] [HasCoproduct fun _ : J ↦ Q]
  [HasCoproduct fun _ : I × J ↦ P ⊗ Q]
  [PreservesColimit₂ (Discrete.functor fun _ : I ↦ P)
    (Discrete.functor fun _ : J ↦ Q) (curriedTensor A)]

/-- The constant family `P ⊗ Q` on `I × J` is the external product of the constant family `P` on
`I` with the constant family `Q` on `J`, read through the equivalence `Discrete (I × J) ≌
Discrete I × Discrete J`. -/
def discreteConstTensorIso :
    (Discrete.functor fun _ : I × J ↦ P ⊗ Q) ≅
      (Discrete.productEquiv (J := I) (K := J)).functor ⋙
        ((Discrete.functor fun _ : I ↦ P) ⊠ (Discrete.functor fun _ : J ↦ Q)) :=
  Discrete.natIso fun _ ↦ Iso.refl _

/-- Tensoring a coproduct of copies of `P` with a coproduct of copies of `Q` gives the coproduct
of copies of `P ⊗ Q` indexed by the product of the two index types. -/
def sigmaTensorSigmaIso :
    (∐ fun _ : I × J ↦ P ⊗ Q) ≅ (∐ fun _ : I ↦ P) ⊗ (∐ fun _ : J ↦ Q) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    ((IsColimit.precomposeHomEquiv (discreteConstTensorIso P Q) _).symm
      ((IsColimit.tensor₂ (colimit.isColimit (Discrete.functor fun _ : I ↦ P))
          (colimit.isColimit (Discrete.functor fun _ : J ↦ Q))).whiskerEquivalence
        (Discrete.productEquiv (J := I) (K := J))))

/-- The distributivity isomorphism sends the summand at `(i, j)` to the tensor product of the
summand at `i` and the summand at `j`. -/
@[reassoc]
lemma ι_comp_sigmaTensorSigmaIso_hom (k : I × J) :
    Sigma.ι (fun _ : I × J ↦ P ⊗ Q) k ≫ (sigmaTensorSigmaIso P Q).hom =
      Sigma.ι (fun _ : I ↦ P) k.1 ⊗ₘ Sigma.ι (fun _ : J ↦ Q) k.2 := by
  refine (IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (Discrete.mk k)).trans ?_
  exact (Category.id_comp _).trans (tensorHom_def _ _).symm

/-- The distributivity isomorphism is compatible with reindexing the two coproducts. -/
lemma sigmaTensorSigmaIso_hom_naturality {I' : Type t₁} {J' : Type t₂}
    [HasCoproduct fun _ : I' ↦ P] [HasCoproduct fun _ : J' ↦ Q]
    [HasCoproduct fun _ : I' × J' ↦ P ⊗ Q]
    [PreservesColimit₂ (Discrete.functor fun _ : I' ↦ P)
      (Discrete.functor fun _ : J' ↦ Q) (curriedTensor A)]
    (a : I → I') (b : J → J') :
    Sigma.map' (fun k : I × J ↦ (a k.1, b k.2)) (fun _ ↦ 𝟙 (P ⊗ Q)) ≫
        (sigmaTensorSigmaIso P Q).hom =
      (sigmaTensorSigmaIso P Q).hom ≫
        (Sigma.map' a (fun _ ↦ 𝟙 P) ⊗ₘ Sigma.map' b (fun _ ↦ 𝟙 Q)) := by
  refine Sigma.hom_ext _ _ fun k ↦ ?_
  rw [Sigma.ι_comp_map'_assoc, Category.id_comp, ι_comp_sigmaTensorSigmaIso_hom,
    ι_comp_sigmaTensorSigmaIso_hom_assoc, tensorHom_comp_tensorHom, Sigma.ι_comp_map',
    Sigma.ι_comp_map', Category.id_comp, Category.id_comp]

end Distributivity

section FreeGenerators

variable {C₁ : Type u₁} {C₂ : Type u₂} [SmallCategory C₁] [SmallCategory C₂]
  {B : Type w} [CommRing B]

/-- **Stacks 08QB, the computation of its proof on the generators.** For `U` an object of `C₁`
and `V` an object of `C₂`, the external tensor product of the free diagram on `U` with
coefficients `P` and the free diagram on `V` with coefficients `Q` is the free diagram on
`(U, V)` with coefficients `P ⊗_B Q`. -/
@[stacks 08QB "the computation `g₁⁻¹j_{U!}B̲_U ⊗_B̲ g₂⁻¹j_{V!}B̲_V = j_{(U,V)!}B̲_{(U,V)}` made \
in the proof, for arbitrary coefficient modules in place of `B̲`; the derived identity that it \
is used to prove is not covered"]
def externalTensorFreeYonedaIso (U : C₁) (V : C₂)
    (P Q : ModuleCat.{max u₁ u₂ w} B) :
    externalTensor (C₂ := C₂) (Presheaf.freeYoneda U P) (Presheaf.freeYoneda V Q) ≅
      Presheaf.freeYoneda ((U, V) : C₁ × C₂) (P ⊗ Q) :=
  (NatIso.ofComponents (fun _ ↦ sigmaTensorSigmaIso P Q) (by
    intro _ _ f
    exact sigmaTensorSigmaIso_hom_naturality P Q
      (fun g ↦ f.unop.1 ≫ g) (fun g ↦ f.unop.2 ≫ g))).symm

end FreeGenerators

end Stacks.CategoryHomology

end
