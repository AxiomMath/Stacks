module
public import StacksFrontier.CategoryTheory.Sites.InverseImageTensor
import all StacksFrontier.CategoryTheory.Sites.InverseImageTensor

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Sites.Pullback
import StacksCore.Tactic.StacksAttribute

/-!
# InverseImageTensorUnconditional

Stronger forms of declarations of `StacksFrontier.CategoryTheory.Sites.InverseImageTensor`, stated as
separate declarations beside the ones there: over more general coefficient universes, or with
inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u v' u'

namespace Stacks.InverseImageTensor

section Lan

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (K : C ⥤ D)
  (A : Type*) [Category* A] [MonoidalCategory A]
  [∀ X : D, HasColimitsOfShape (CostructuredArrow K X) A]

/-- The comparison morphism from the left Kan extension of an objectwise tensor product of
functors to the tensor product of the two left Kan extensions. It is the morphism which the
universal property of the Kan extension attaches to the tensor product of the two units. -/
def lanDeltaUnconditional (P Q : C ⥤ A) :
    K.lan.obj (P ⊗ Q) ⟶ K.lan.obj P ⊗ K.lan.obj Q :=
  (K.lan.obj (P ⊗ Q)).descOfIsLeftKanExtension (K.lanUnit.app (P ⊗ Q))
    (K.lan.obj P ⊗ K.lan.obj Q) (K.lanUnit.app P ⊗ₘ K.lanUnit.app Q)

/-- The defining property of `lanDeltaUnconditional`: it takes the unit of the Kan extension of
`P ⊗ Q` to the tensor product of the units of the Kan extensions of `P` and `Q`. -/
theorem lanUnit_app_comp_lanDelta_app_general (P Q : C ⥤ A) (c : C) :
    (K.lanUnit.app (P ⊗ Q)).app c ≫ (lanDeltaUnconditional K A P Q).app (K.obj c)
      = (K.lanUnit.app P).app c ⊗ₘ (K.lanUnit.app Q).app c :=
  (K.lan.obj (P ⊗ Q)).descOfIsLeftKanExtension_fac_app (K.lanUnit.app (P ⊗ Q)) _ _ c

/-- The cocone over the costructured arrows of `K` above an object whose colimit is the value
there of the left Kan extension. -/
def lanCoconeUnconditional (P : C ⥤ A) (X : D) :
    Cocone (CostructuredArrow.proj K X ⋙ P) :=
  (Functor.LeftExtension.mk (K.lan.obj P) (K.lanUnit.app P)).coconeAt X

/-- The left Kan extension is computed pointwise by `lanCoconeUnconditional`. -/
def lanIsColimitUnconditional (P : C ⥤ A) (X : D) : IsColimit (lanCoconeUnconditional K A P X) :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := P)
    (K.lan.obj P) (K.lanUnit.app P) X

/-- The pointwise cocone for a tensor product, read as a cocone over the objectwise tensor product
of the two diagrams. The two diagrams agree, the objectwise tensor product of presheaves being
objectwise. -/
def lanTensorCoconeUnconditional (P Q : C ⥤ A) (X : D) :
    Cocone ((CostructuredArrow.proj K X ⋙ P) ⊗ (CostructuredArrow.proj K X ⋙ Q)) :=
  lanCoconeUnconditional K A (P ⊗ Q) X

/-- The cocone `lanTensorCoconeUnconditional` is a colimit cocone. -/
def lanTensorIsColimitUnconditional (P Q : C ⥤ A) (X : D) :
    IsColimit (lanTensorCoconeUnconditional K A P Q X) :=
  lanIsColimitUnconditional K A (P ⊗ Q) X

variable [∀ X : D, IsFiltered (CostructuredArrow K X)]
  [∀ (X : D) (P Q : C ⥤ A), PreservesColimit₂ (CostructuredArrow.proj K X ⋙ P)
    (CostructuredArrow.proj K X ⋙ Q) (curriedTensor A)]

/-- **Left Kan extension commutes with the objectwise tensor product** when the comma categories
computing it pointwise are filtered and the tensor product commutes with colimits over them in
each variable: the comparison morphism `lanDeltaUnconditional` is an isomorphism. -/
instance isIso_lanDelta_unconditional (P Q : C ⥤ A) : IsIso (lanDeltaUnconditional K A P Q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have : IsSifted (CostructuredArrow K X) := { nonempty := IsFiltered.nonempty }
  have h2 : IsColimit
      (Cocone.tensor (lanCoconeUnconditional K A P X) (lanCoconeUnconditional K A Q X)) :=
    (lanIsColimitUnconditional K A P X).tensor (lanIsColimitUnconditional K A Q X)
  have key : ∀ T : CostructuredArrow K X,
      ((K.lanUnit.app (P ⊗ Q)).app T.left ≫ (K.lan.obj (P ⊗ Q)).map T.hom) ≫
          (lanDeltaUnconditional K A P Q).app X
        = ((K.lanUnit.app P).app T.left ≫ (K.lan.obj P).map T.hom) ⊗ₘ
          ((K.lanUnit.app Q).app T.left ≫ (K.lan.obj Q).map T.hom) := by
    intro T
    rw [Category.assoc, (lanDeltaUnconditional K A P Q).naturality T.hom, ← Category.assoc,
      lanUnit_app_comp_lanDelta_app_general]
    exact tensorHom_comp_tensorHom _ _ _ _
  have heq : (lanDeltaUnconditional K A P Q).app X
      = (IsColimit.coconePointUniqueUpToIso
          (lanTensorIsColimitUnconditional K A P Q X) h2).hom := by
    refine (lanTensorIsColimitUnconditional K A P Q X).hom_ext fun T => ?_
    refine (key T).trans ?_
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (lanTensorIsColimitUnconditional K A P Q X) h2 T).symm
  rw [heq]
  exact ⟨⟨_, Iso.hom_inv_id _, Iso.inv_hom_id _⟩⟩

end Lan

section Sheaf

attribute [local instance] Sheaf.monoidalCategory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) (Λ : Type w) [CommRing Λ]
  (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
  [G.IsContinuous J J']
  [HasWeakSheafify J (ModuleCat.{w} Λ)] [HasWeakSheafify J' (ModuleCat.{w} Λ)]
  [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op X) (ModuleCat.{w} Λ)]
  [(G.sheafPushforwardContinuous (ModuleCat.{w} Λ) J J').IsRightAdjoint]

variable [(J.W (A := ModuleCat.{w} Λ)).IsMonoidal] [(J'.W (A := ModuleCat.{w} Λ)).IsMonoidal]
  [∀ X : Dᵒᵖ, IsFiltered (CostructuredArrow G.op X)]

end Sheaf

end Stacks.InverseImageTensor

end
