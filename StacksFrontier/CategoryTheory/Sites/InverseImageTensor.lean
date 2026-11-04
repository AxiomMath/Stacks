module

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
# Inverse image of sheaves of modules commutes with the tensor product

Let `G : C ⥤ D` be a continuous functor of sites and let `Λ` be a commutative ring. The inverse
image functor `G⁻¹ : Sheaf J (ModuleCat Λ) ⥤ Sheaf K (ModuleCat Λ)`, the left adjoint of the
pushforward along `G`, carries the tensor product of two sheaves of `Λ`-modules to the tensor
product of their inverse images.

## Main definitions

* `Stacks.InverseImageTensor.lanDelta`: the comparison morphism from the left Kan extension of an
  objectwise tensor product of presheaves of `Λ`-modules to the tensor product of the two left
  Kan extensions.
* `Stacks.InverseImageTensor.sheafifyCompPullbackIso`: the inverse image of the sheafification of
  a presheaf of `Λ`-modules is the sheafification of its left Kan extension.
* `Stacks.InverseImageTensor.sheafPullbackTensorIso`: `G⁻¹(F ⊗ F') ≅ G⁻¹F ⊗ G⁻¹F'`.

## Main results

* `Stacks.InverseImageTensor.isIso_lanDelta`: the comparison morphism is an isomorphism, i.e.
  left Kan extension commutes with the objectwise tensor product, as soon as the comma
  categories computing it pointwise are filtered.

## Implementation notes

The tensor product of sheaves is the one of `CategoryTheory.Sheaf.monoidalCategory`, the
localization of the objectwise tensor product of presheaves along sheafification, so that
`F ⊗ F'` is the sheafification of `U ↦ F(U) ⊗_Λ F'(U)`. Mathlib does not make that structure an
instance, since on some value categories it clashes with the cartesian one, so it is activated
as a local instance here. The coefficient universe is the universe of `Λ`, because
`ModuleCat.{w} Λ` is monoidal closed only for `Λ : Type w`.

That the inverse image is monoidal is *not* formal: both `G⁻¹(- ⊗ F')` and `G⁻¹(-) ⊗ G⁻¹F'` are
left adjoints, and the comparison of their right adjoints is equivalent to the statement itself,
so some computation with sections is unavoidable. The computation here is the pointwise formula
for the left Kan extension: the value of `G.op.lan` at an object is a colimit over a comma
category, a tensor product of colimits over a *sifted* index category is the colimit of the
objectwise tensor product (`CategoryTheory.Limits.IsColimit.tensor`), and a filtered category is
sifted. So filteredness of the comma categories is the hypothesis; by Tag 00X3 it holds whenever
`G` preserves finite limits, which is the case for the base change functors of étale sites.

The comparison morphism is not built from `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`
but directly from the universal property of the Kan extension, through
`CategoryTheory.Functor.descOfIsLeftKanExtension`; the two agree, but the universal property is
what makes the identification with the colimit comparison a one-line rewrite, and no coherence
of the oplax structure is needed for the conclusion.

Passage from presheaves to sheaves costs only `sheafifyCompPullbackIso`, which is uniqueness of
left adjoints: the inverse image composed with sheafification and sheafification composed with
the Kan extension are both left adjoint to the restriction of a sheaf along `G.op`, the
pushforward being that restriction (`Functor.sheafPushforwardContinuousCompSheafToPresheafIso`).

## References

* [Stacks Project, Tag 00X3](https://stacks.math.columbia.edu/tag/00X3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u v' u'

namespace Stacks.InverseImageTensor

/-! ### Left Kan extension and the objectwise tensor product -/

section Lan

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (K : C ⥤ D)
  (Λ : Type w) [CommRing Λ]
  [∀ X : D, HasColimitsOfShape (CostructuredArrow K X) (ModuleCat.{w} Λ)]

/-- The comparison morphism from the left Kan extension of an objectwise tensor product of
presheaves of `Λ`-modules to the tensor product of the two left Kan extensions. It is the
morphism which the universal property of the Kan extension attaches to the tensor product of
the two units. -/
def lanDelta (P Q : C ⥤ ModuleCat.{w} Λ) :
    K.lan.obj (P ⊗ Q) ⟶ K.lan.obj P ⊗ K.lan.obj Q :=
  (K.lan.obj (P ⊗ Q)).descOfIsLeftKanExtension (K.lanUnit.app (P ⊗ Q))
    (K.lan.obj P ⊗ K.lan.obj Q) (K.lanUnit.app P ⊗ₘ K.lanUnit.app Q)

/-- The defining property of `Stacks.InverseImageTensor.lanDelta`: it takes the unit of the Kan
extension of `P ⊗ Q` to the tensor product of the units of the Kan extensions of `P` and `Q`. -/
theorem lanUnit_app_comp_lanDelta_app (P Q : C ⥤ ModuleCat.{w} Λ) (c : C) :
    (K.lanUnit.app (P ⊗ Q)).app c ≫ (lanDelta K Λ P Q).app (K.obj c)
      = (K.lanUnit.app P).app c ⊗ₘ (K.lanUnit.app Q).app c :=
  (K.lan.obj (P ⊗ Q)).descOfIsLeftKanExtension_fac_app (K.lanUnit.app (P ⊗ Q)) _ _ c

/-- The cocone over the costructured arrows of `K` above an object whose colimit is the value
there of the left Kan extension. -/
def lanCocone (P : C ⥤ ModuleCat.{w} Λ) (X : D) :
    Cocone (CostructuredArrow.proj K X ⋙ P) :=
  (Functor.LeftExtension.mk (K.lan.obj P) (K.lanUnit.app P)).coconeAt X

/-- The left Kan extension is computed pointwise by `Stacks.InverseImageTensor.lanCocone`. -/
def lanIsColimit (P : C ⥤ ModuleCat.{w} Λ) (X : D) : IsColimit (lanCocone K Λ P X) :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension (F := P)
    (K.lan.obj P) (K.lanUnit.app P) X

/-- The pointwise cocone for a tensor product, read as a cocone over the objectwise tensor
product of the two diagrams. The two diagrams agree, the objectwise tensor product of
presheaves being objectwise. -/
def lanTensorCocone (P Q : C ⥤ ModuleCat.{w} Λ) (X : D) :
    Cocone ((CostructuredArrow.proj K X ⋙ P) ⊗ (CostructuredArrow.proj K X ⋙ Q)) :=
  lanCocone K Λ (P ⊗ Q) X

/-- It is a colimit cocone. -/
def lanTensorIsColimit (P Q : C ⥤ ModuleCat.{w} Λ) (X : D) :
    IsColimit (lanTensorCocone K Λ P Q X) :=
  lanIsColimit K Λ (P ⊗ Q) X

variable [∀ X : D, IsFiltered (CostructuredArrow K X)]

/-- **Left Kan extension commutes with the objectwise tensor product of presheaves of
`Λ`-modules** when the comma categories computing it pointwise are filtered: a filtered category
is sifted, so the tensor product of the two colimit cocones is again a colimit cocone, and the
comparison morphism is the induced map between two colimits of one and the same diagram. -/
instance isIso_lanDelta (P Q : C ⥤ ModuleCat.{w} Λ) : IsIso (lanDelta K Λ P Q) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  have : IsSifted (CostructuredArrow K X) := { nonempty := IsFiltered.nonempty }
  have h2 : IsColimit (Cocone.tensor (lanCocone K Λ P X) (lanCocone K Λ Q X)) :=
    (lanIsColimit K Λ P X).tensor (lanIsColimit K Λ Q X)
  have key : ∀ T : CostructuredArrow K X,
      ((K.lanUnit.app (P ⊗ Q)).app T.left ≫ (K.lan.obj (P ⊗ Q)).map T.hom) ≫
          (lanDelta K Λ P Q).app X
        = ((K.lanUnit.app P).app T.left ≫ (K.lan.obj P).map T.hom) ⊗ₘ
          ((K.lanUnit.app Q).app T.left ≫ (K.lan.obj Q).map T.hom) := by
    intro T
    rw [Category.assoc, (lanDelta K Λ P Q).naturality T.hom, ← Category.assoc,
      lanUnit_app_comp_lanDelta_app]
    exact tensorHom_comp_tensorHom _ _ _ _
  have heq : (lanDelta K Λ P Q).app X
      = (IsColimit.coconePointUniqueUpToIso (lanTensorIsColimit K Λ P Q X) h2).hom := by
    refine (lanTensorIsColimit K Λ P Q X).hom_ext fun T => ?_
    refine (key T).trans ?_
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (lanTensorIsColimit K Λ P Q X) h2 T).symm
  rw [heq]
  exact ⟨⟨_, Iso.hom_inv_id _, Iso.inv_hom_id _⟩⟩

end Lan

/-! ### Inverse image of sheaves and the tensor product -/

section Sheaf

attribute [local instance] Sheaf.monoidalCategory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (G : C ⥤ D) (Λ : Type w) [CommRing Λ]
  (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
  [G.IsContinuous J J']
  [HasWeakSheafify J (ModuleCat.{w} Λ)] [HasWeakSheafify J' (ModuleCat.{w} Λ)]
  [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op X) (ModuleCat.{w} Λ)]
  [(G.sheafPushforwardContinuous (ModuleCat.{w} Λ) J J').IsRightAdjoint]

/-- **The inverse image of the sheafification of a presheaf of `Λ`-modules is the sheafification
of its left Kan extension.** Both functors are left adjoint to the restriction along `G.op` of
the underlying presheaf of a sheaf, the pushforward along `G` being that restriction. -/
def sheafifyCompPullbackIso :
    presheafToSheaf J (ModuleCat.{w} Λ) ⋙ G.sheafPullback (ModuleCat.{w} Λ) J J'
      ≅ G.op.lan ⋙ presheafToSheaf J' (ModuleCat.{w} Λ) :=
  Adjunction.leftAdjointUniq
    (((sheafificationAdjunction J (ModuleCat.{w} Λ)).comp
      (G.sheafAdjunctionContinuous (ModuleCat.{w} Λ) J J')).ofNatIsoRight
        (G.sheafPushforwardContinuousCompSheafToPresheafIso (ModuleCat.{w} Λ) J J'))
    ((G.op.lanAdjunction (ModuleCat.{w} Λ)).comp
      (sheafificationAdjunction J' (ModuleCat.{w} Λ)))

variable [(J.W (A := ModuleCat.{w} Λ)).IsMonoidal] [(J'.W (A := ModuleCat.{w} Λ)).IsMonoidal]
  [∀ X : Dᵒᵖ, IsFiltered (CostructuredArrow G.op X)]

/-- **The inverse image of sheaves of `Λ`-modules along a continuous functor of sites commutes
with the tensor product.**

Both sheaves are the sheafification of their underlying presheaf and sheafification is monoidal,
so the tensor product of the two is the sheafification of the objectwise tensor product of the
two presheaves; the inverse image of a sheafification is the sheafification of the left Kan
extension, and the left Kan extension commutes with the objectwise tensor product. -/
@[ega "0 4.3.3" "special case",
  ega "IV 10.2.8" "more general",
  sga "4 IV 3.1.2" "special case",
  sga "4 V 1.6.2" "special case"]
def sheafPullbackTensorIso (F F' : Sheaf J (ModuleCat.{w} Λ)) :
    (G.sheafPullback (ModuleCat.{w} Λ) J J').obj (F ⊗ F')
      ≅ (G.sheafPullback (ModuleCat.{w} Λ) J J').obj F ⊗
        (G.sheafPullback (ModuleCat.{w} Λ) J J').obj F' :=
  (G.sheafPullback (ModuleCat.{w} Λ) J J').mapIso
      ((tensorIso (asIso ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app F))
          (asIso ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app F'))).symm ≪≫
        Functor.Monoidal.μIso (presheafToSheaf J (ModuleCat.{w} Λ))
          ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj F)
          ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj F')) ≪≫
    (sheafifyCompPullbackIso G Λ J J').app
      ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj F ⊗
        (sheafToPresheaf J (ModuleCat.{w} Λ)).obj F') ≪≫
    (presheafToSheaf J' (ModuleCat.{w} Λ)).mapIso
      (asIso (lanDelta G.op Λ ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj F)
        ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj F'))) ≪≫
    (Functor.Monoidal.μIso (presheafToSheaf J' (ModuleCat.{w} Λ))
      (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj F))
      (G.op.lan.obj ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj F'))).symm ≪≫
    tensorIso ((sheafifyCompPullbackIso G Λ J J').app
        ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj F)).symm
      ((sheafifyCompPullbackIso G Λ J J').app
        ((sheafToPresheaf J (ModuleCat.{w} Λ)).obj F')).symm ≪≫
    tensorIso ((G.sheafPullback (ModuleCat.{w} Λ) J J').mapIso
        (asIso ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app F)))
      ((G.sheafPullback (ModuleCat.{w} Λ) J J').mapIso
        (asIso ((sheafificationAdjunction J (ModuleCat.{w} Λ)).counit.app F')))

end Sheaf

end Stacks.InverseImageTensor

end
