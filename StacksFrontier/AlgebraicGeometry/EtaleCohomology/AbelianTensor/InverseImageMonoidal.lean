module
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbelianTensor.Monoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.CategoryTheory.Sites.SheafPushforwardMonoidal

/-!
# Inverse image of abelian étale sheaves is a monoidal functor

Let `f : X ⟶ Y` be a morphism of schemes. For the tensor product of abelian sheaves on small
étale sites, `Stacks.EtaleCohomology.etaleAbelianMonoidalCategory`, this file shows:

* the direct image `f_*` is lax monoidal (`etaleAbelianDirectImageLaxMonoidal`), its tensorator
  `f_*M ⊗ f_*N ⟶ f_*(M ⊗ N)` being induced by the sectionwise tensor product and the
  sheafification unit;
* the inverse image `f⁻¹` is a strong monoidal functor (`etaleAbelianInverseImageMonoidal`) whose
  oplax structure is the mate of that lax structure, so that
  `etaleAbelianInverseImageTensorIso f M N : f⁻¹(M ⊗ N) ≅ f⁻¹M ⊗ f⁻¹N`;
* the composition isomorphisms `(fg)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` are monoidal natural isomorphisms
  (`isMonoidal_etaleAbelianInverseImageCompIso'_hom`), and consequently, for a commutative square
  of schemes, the four tensor isomorphisms are compatible with the comparison of the two
  composite inverse images around the square (`etaleAbelianInverseImageTensorIso_square`).

## Implementation notes

All of this is the site-level statement of
`StacksFrontier.CategoryTheory.Sites.SheafPushforwardMonoidal` for the base change functor
`smallEtaleBaseChange f` of small étale sites. Its inputs are: the sheafification of abelian
presheaves on a small étale site is monoidal (`isMonoidal_W_smallEtale`), the comma categories
computing the left Kan extension along base change are filtered (base change is representably
flat), and the tensor product of abelian groups commutes with colimits in each variable.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] AddCommGrpCat.monoidalCategory AddCommGrpCat.braidedCategoryGeneral
  AddCommGrpCat.monoidalClosedGeneral etaleAbelianMonoidalCategory isMonoidal_W_smallEtale

/-- The comma categories computing the left Kan extension along base change of small étale sites
are filtered: base change is representably flat. -/
instance isFiltered_costructuredArrow_smallEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : X.Etaleᵒᵖ) : IsFiltered (CostructuredArrow (smallEtaleBaseChange f).op V) :=
  IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange f) V.unop)

/-- Tensoring abelian groups commutes with colimits of diagrams of the size of the comma
categories of base change, in each variable. -/
instance preservesColimit₂_smallEtaleBaseChange {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : X.Etaleᵒᵖ) (P Q : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) :
    PreservesColimit₂ (CostructuredArrow.proj (smallEtaleBaseChange f).op V ⋙ P)
      (CostructuredArrow.proj (smallEtaleBaseChange f).op V ⋙ Q)
      (curriedTensor AddCommGrpCat.{max (u + 1) v}) := by
  have hl (M : AddCommGrpCat.{max (u + 1) v}) :
      PreservesColimitsOfSize.{u, u + 1} ((curriedTensor AddCommGrpCat.{max (u + 1) v}).obj M) :=
    have : PreservesColimitsOfSize.{max (u + 1) v, max (u + 1) v}
        ((curriedTensor AddCommGrpCat.{max (u + 1) v}).obj M) :=
      preservesColimits_tensorLeft_addCommGrpCat M
    preservesColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
  have hr (M : AddCommGrpCat.{max (u + 1) v}) :
      PreservesColimitsOfSize.{u, u + 1}
        ((curriedTensor AddCommGrpCat.{max (u + 1) v}).flip.obj M) :=
    have : PreservesColimitsOfSize.{max (u + 1) v, max (u + 1) v}
        ((curriedTensor AddCommGrpCat.{max (u + 1) v}).flip.obj M) :=
      preservesColimits_tensorRight_addCommGrpCat M
    preservesColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
  infer_instance

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The direct image of abelian étale sheaves is lax monoidal**: the tensorator
`f_*M ⊗ f_*N ⟶ f_*(M ⊗ N)` is the morphism out of the sheafification of the sectionwise tensor
product `U ↦ M(U ×_Y X) ⊗ N(U ×_Y X)` induced by the sheafification unit of `M ⊗ N`. -/
@[instance_reducible]
noncomputable def etaleAbelianDirectImageLaxMonoidal :
    (etaleAbelianDirectImage.{u, v} f).LaxMonoidal :=
  Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal Y.smallEtaleTopology X.smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v} (smallEtaleBaseChange f)

/-- **The inverse image of abelian étale sheaves is a monoidal functor.** Its oplax structure is
the mate of the lax structure `etaleAbelianDirectImageLaxMonoidal` of the direct image, and it is
strong. -/
@[instance_reducible]
noncomputable def etaleAbelianInverseImageMonoidal :
    (etaleAbelianInverseImage.{u, v} f).Monoidal :=
  Stacks.SheafPushforwardMonoidal.pullbackMonoidal Y.smallEtaleTopology X.smallEtaleTopology
    AddCommGrpCat.{max (u + 1) v} (smallEtaleBaseChange f)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f)

attribute [local instance] etaleAbelianDirectImageLaxMonoidal etaleAbelianInverseImageMonoidal

/-- The comparison morphism `δ` of the monoidal structure of the inverse image is the one of the
oplax structure mated from the lax structure of the direct image. -/
lemma etaleAbelianInverseImage_δ
    (M N : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    δ (etaleAbelianInverseImage.{u, v} f) M N =
      (letI := (etaleAbelianInverseImageDirectImageAdj.{u, v} f).leftAdjointOplaxMonoidal;
        δ (etaleAbelianInverseImage.{u, v} f) M N) :=
  rfl

/-- The adjunction between inverse and direct image of abelian étale sheaves is compatible with
the monoidal structure of the inverse image and the lax monoidal structure of the direct
image. -/
instance isMonoidal_etaleAbelianInverseImageDirectImageAdj :
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f).IsMonoidal :=
  Stacks.SheafPushforwardMonoidal.isMonoidal_pullbackMonoidal Y.smallEtaleTopology
    X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} (smallEtaleBaseChange f)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f)

/-- **The inverse image of abelian étale sheaves commutes with the tensor product**:
`f⁻¹(M ⊗ N) ≅ f⁻¹M ⊗ f⁻¹N`, the inverse of the tensorator of the monoidal structure
`etaleAbelianInverseImageMonoidal`, whose forward direction is the comparison morphism `δ`. -/
noncomputable def etaleAbelianInverseImageTensorIso
    (M N : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImage.{u, v} f).obj (M ⊗ N) ≅
      (etaleAbelianInverseImage.{u, v} f).obj M ⊗ (etaleAbelianInverseImage.{u, v} f).obj N :=
  (Functor.Monoidal.μIso (etaleAbelianInverseImage.{u, v} f) M N).symm

/-- The forward direction of `etaleAbelianInverseImageTensorIso f M N` is the comparison
morphism `δ` of the monoidal structure of the inverse image. -/
lemma etaleAbelianInverseImageTensorIso_hom
    (M N : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImageTensorIso.{u, v} f M N).hom =
      δ (etaleAbelianInverseImage.{u, v} f) M N :=
  rfl

/-- Naturality of `etaleAbelianInverseImageTensorIso` in the first variable. -/
lemma etaleAbelianInverseImageTensorIso_hom_natural_left
    {M M' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (φ : M ⟶ M')
    (N : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImage.{u, v} f).map (((etaleAbelianTensor Y).map φ).app N) ≫
        (etaleAbelianInverseImageTensorIso.{u, v} f M' N).hom =
      (etaleAbelianInverseImageTensorIso.{u, v} f M N).hom ≫
        ((etaleAbelianTensor X).map ((etaleAbelianInverseImage.{u, v} f).map φ)).app
          ((etaleAbelianInverseImage.{u, v} f).obj N) :=
  (Functor.OplaxMonoidal.δ_natural_left (etaleAbelianInverseImage.{u, v} f) φ N).symm

/-- Naturality of `etaleAbelianInverseImageTensorIso` in the second variable. -/
lemma etaleAbelianInverseImageTensorIso_hom_natural_right
    (M : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    {N N' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (ψ : N ⟶ N') :
    (etaleAbelianInverseImage.{u, v} f).map (((etaleAbelianTensor Y).obj M).map ψ) ≫
        (etaleAbelianInverseImageTensorIso.{u, v} f M N').hom =
      (etaleAbelianInverseImageTensorIso.{u, v} f M N).hom ≫
        ((etaleAbelianTensor X).obj ((etaleAbelianInverseImage.{u, v} f).obj M)).map
          ((etaleAbelianInverseImage.{u, v} f).map ψ) :=
  (Functor.OplaxMonoidal.δ_natural_right (etaleAbelianInverseImage.{u, v} f) M ψ).symm

end

section Composition

variable {X Y Z : Scheme.{u}}

attribute [local instance] etaleAbelianInverseImageMonoidal

/-- **The composition isomorphism `(fg)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` of inverse images of abelian étale sheaves
is a monoidal natural isomorphism**, for the monoidal structures
`etaleAbelianInverseImageMonoidal` and the composite monoidal structure on `g⁻¹ ⋙ f⁻¹`. -/
instance isMonoidal_etaleAbelianInverseImageCompIso'_hom (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    NatTrans.IsMonoidal (etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).hom := by
  have : NatTrans.IsMonoidal
      (Adjunction.leftAdjointCompIso (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
        (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
        (etaleAbelianInverseImageDirectImageAdj.{u, v} fg)
        (etaleAbelianDirectImageCompIso'.{u, v} f g fg hfg)).hom :=
    Stacks.SheafPushforwardMonoidal.isMonoidal_leftAdjointCompIso_hom
    Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}
    (smallEtaleBaseChangeComp' f g fg hfg).symm
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
    (etaleAbelianInverseImageDirectImageAdj.{u, v} fg)
  exact inferInstanceAs (NatTrans.IsMonoidal
    (Adjunction.leftAdjointCompIso (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
      (etaleAbelianInverseImageDirectImageAdj.{u, v} fg)
      (etaleAbelianDirectImageCompIso'.{u, v} f g fg hfg)).inv)

/-- The inverse `g⁻¹ ⋙ f⁻¹ ⟶ (fg)⁻¹` of the composition isomorphism of inverse images of abelian
étale sheaves is a monoidal natural transformation. -/
instance isMonoidal_etaleAbelianInverseImageCompIso'_inv (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    NatTrans.IsMonoidal (etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).inv :=
  inferInstance

end Composition

section Square

variable {X X' Y Y' : Scheme.{u}}

attribute [local instance] etaleAbelianInverseImageMonoidal

/-- **The four tensor isomorphisms around a commutative square of schemes are compatible with
the comparison of the two composite inverse images.** For a commutative square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
with common composite `P`, write `e : g⁻¹ ⋙ f'⁻¹ ≅ f⁻¹ ⋙ g'⁻¹` for the comparison of the two
composite inverse images, through the composition isomorphisms at `P`. Then going down then
across and going across then down give the same comparison
`f'⁻¹ g⁻¹ (M ⊗ N) ⟶ g'⁻¹ f⁻¹ M ⊗ g'⁻¹ f⁻¹ N`, after transport along `e`. -/
theorem etaleAbelianInverseImageTensorIso_square (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (f' : X' ⟶ Y') (P : X' ⟶ Y) (hP₁ : P = g' ≫ f) (hP₂ : P = f' ≫ g)
    (M N : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    Eq
      ((etaleAbelianInverseImage.{u, v} f').map
          (etaleAbelianInverseImageTensorIso.{u, v} g M N).hom ≫
        (etaleAbelianInverseImageTensorIso.{u, v} f' ((etaleAbelianInverseImage.{u, v} g).obj M)
          ((etaleAbelianInverseImage.{u, v} g).obj N)).hom ≫
        ((etaleAbelianTensor X').map
          (((etaleAbelianInverseImageCompIso'.{u, v} f' g P hP₂).symm ≪≫
            etaleAbelianInverseImageCompIso'.{u, v} g' f P hP₁).hom.app M)).app
            ((etaleAbelianInverseImage.{u, v} f').obj ((etaleAbelianInverseImage.{u, v} g).obj N)) ≫
        ((etaleAbelianTensor X').obj ((etaleAbelianInverseImage.{u, v} g').obj
          ((etaleAbelianInverseImage.{u, v} f).obj M))).map
          (((etaleAbelianInverseImageCompIso'.{u, v} f' g P hP₂).symm ≪≫
            etaleAbelianInverseImageCompIso'.{u, v} g' f P hP₁).hom.app N))
      (((etaleAbelianInverseImageCompIso'.{u, v} f' g P hP₂).symm ≪≫
          etaleAbelianInverseImageCompIso'.{u, v} g' f P hP₁).hom.app
          (((etaleAbelianTensor Y).obj M).obj N) ≫
        (etaleAbelianInverseImage.{u, v} g').map
          (etaleAbelianInverseImageTensorIso.{u, v} f M N).hom ≫
        (etaleAbelianInverseImageTensorIso.{u, v} g' ((etaleAbelianInverseImage.{u, v} f).obj M)
          ((etaleAbelianInverseImage.{u, v} f).obj N)).hom) := by
  have : NatTrans.IsMonoidal ((etaleAbelianInverseImageCompIso'.{u, v} f' g P hP₂).symm ≪≫
      etaleAbelianInverseImageCompIso'.{u, v} g' f P hP₁).hom := by
    rw [Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have h := NatTrans.IsMonoidal.app_tensor_comp_δ
    ((etaleAbelianInverseImageCompIso'.{u, v} f' g P hP₂).symm ≪≫
      etaleAbelianInverseImageCompIso'.{u, v} g' f P hP₁).hom M N
  simp only [Functor.OplaxMonoidal.comp_δ, Category.assoc] at h
  simp only [etaleAbelianInverseImageTensorIso_hom, curriedTensor_map_app,
    curriedTensor_obj_map, curriedTensor_obj_obj]
  rw [h, tensorHom_def]
  rfl

end Square

end Stacks.EtaleCohomology
