module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.Over
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# Comparisons of cartesian structures, inverse images and composite structure maps

* Two cartesian monoidal structures on one category give the same functor `toOver F` up to a
  canonical isomorphism, the product comparison of the identity functor read between the two
  structures.
* An isomorphism of the set-level inverse images of two morphisms of topoi lifts uniquely to an
  isomorphism of their inverse images of sheaves of commutative rings.
* On underlying sheaves of sets, the inverse-image form of the structure map of a composite of
  morphisms of ringed topoi is the composite of the two inverse-image forms.

## Main definitions

* `CategoryTheory.toOverIsoOfCartesianMonoidalCategory`: the comparison of `toOver F` for two
  cartesian monoidal structures on one category.

## Main results

* `Stacks.Sheaves.ToposPushforward.inverseImageCommRingIsoOfToposIso_existsUnique`: an
  isomorphism of set-level inverse images has a unique lift to sheaves of commutative rings
  inducing it.
* `AlgebraicGeometry.RingedToposHom.comp_fSharpInverseImage_forget`: the inverse-image form of
  the structure map of a composite, on underlying sheaves of sets.
* `CategoryTheory.Adjunction.comp_homEquiv_symm_apply` and `.comp_homEquiv_symm_comp`: the
  adjunct of a morphism under a composite adjunction.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- The comparison of `toOver F` for two cartesian monoidal structures on one category. Both
functors send an object `G` to the projection `G × F ⟶ F`, for the two chosen products, and the
comparison is the product comparison of the identity functor read from one structure to the
other. -/
noncomputable def toOverIsoOfCartesianMonoidalCategory
    (s t : CartesianMonoidalCategory C) (F : C) :
    @toOver C _ s F ≅ @toOver C _ t F := by
  let p (G : C) :
      @MonoidalCategoryStruct.tensorObj C _
        s.toSemiCartesianMonoidalCategory.toMonoidalCategory.toMonoidalCategoryStruct G F ≅
      @MonoidalCategoryStruct.tensorObj C _
        t.toSemiCartesianMonoidalCategory.toMonoidalCategory.toMonoidalCategoryStruct G F :=
    @CartesianMonoidalCategory.prodComparisonIso C _ s C _ t (𝟭 _) G F inferInstance
  exact NatIso.ofComponents
    (fun G ↦ Over.isoMk (p G) (by
      change (p G).hom ≫
          @SemiCartesianMonoidalCategory.snd C _ t.toSemiCartesianMonoidalCategory G F =
        @SemiCartesianMonoidalCategory.snd C _ s.toSemiCartesianMonoidalCategory G F
      simpa [p, CartesianMonoidalCategory.prodComparisonIso_hom] using
        (@CartesianMonoidalCategory.prodComparison_snd C _ s C _ t (𝟭 C) G F)))
    (fun f ↦ Over.OverMorphism.ext
      (@CartesianMonoidalCategory.prodComparison_natural_whiskerRight
        C _ s C _ t (𝟭 C) _ F _ f))

/-- The comparison of `toOver F` is the product comparison of the identity functor. -/
@[simp]
theorem toOverIsoOfCartesianMonoidalCategory_hom_app_left
    (s t : CartesianMonoidalCategory C) (F G : C) :
    ((toOverIsoOfCartesianMonoidalCategory s t F).hom.app G).left =
      @CartesianMonoidalCategory.prodComparison C _ s C _ t (𝟭 C) G F :=
  rfl

namespace Adjunction

universe v₂ v₃ u₂ u₃

variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
  {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}

/-- The adjunct of a morphism under a composite adjunction is its adjunct under the second
factor, then under the first. -/
theorem comp_homEquiv_symm_apply (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (A : C) (B : E)
    (a : A ⟶ (I ⋙ G).obj B) :
    ((adj₁.comp adj₂).homEquiv A B).symm a =
      (adj₂.homEquiv (F.obj A) B).symm ((adj₁.homEquiv A (I.obj B)).symm a) := by
  rw [congrFun (congrFun (Adjunction.comp_homEquiv adj₁ adj₂) A) B, Equiv.symm_trans_apply]

/-- The adjunct, under a composite adjunction, of a morphism that is itself a composite
`a ≫ G.map b`: it is the adjunct of `a` under the first factor, pushed along `H`, followed by
the adjunct of `b` under the second. -/
theorem comp_homEquiv_symm_comp (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) {A : C} {B₀ : D} {B : E}
    (a : A ⟶ G.obj B₀) (b : B₀ ⟶ I.obj B) :
    ((adj₁.comp adj₂).homEquiv A B).symm (a ≫ G.map b) =
      H.map ((adj₁.homEquiv A B₀).symm a) ≫ (adj₂.homEquiv B₀ B).symm b := by
  rw [comp_homEquiv_symm_apply, adj₁.homEquiv_naturality_right_symm,
    adj₂.homEquiv_naturality_left_symm]

end Adjunction

end CategoryTheory

namespace Stacks.Sheaves.ToposPushforward

open Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget₂ CommRingCat.{ww} RingCat.{ww})]
  [K.HasSheafCompose (forget₂ CommRingCat.{ww'} RingCat.{ww'})]
  [J.HasSheafCompose (forget CommRingCat.{ww})]
  [K.HasSheafCompose (forget CommRingCat.{ww'})]

/-- An isomorphism of set-level inverse images lifts uniquely to sheaves of commutative rings:
for two morphisms of topoi `f, g` with the same source and target and an isomorphism
`e : f⁻¹ ≅ g⁻¹` of their inverse images of sheaves of sets, there is exactly one isomorphism of
their inverse images of sheaves of commutative rings whose underlying map of sheaves of sets is
`e`. -/
theorem inverseImageCommRingIsoOfToposIso_existsUnique
    (f g : MorphismOfTopoi (Sheaf J (Type ww)) (Sheaf K (Type ww')))
    (e : f.inverseImage ≅ g.inverseImage) :
    ∃! β : inverseImageCommRingFunctor f ≅ inverseImageCommRingFunctor g,
      ∀ R : Sheaf K CommRingCat.{ww'},
        (sheafCompose J (forget CommRingCat.{ww})).map (β.hom.app R) =
          e.hom.app ((sheafCompose K (forget CommRingCat.{ww'})).obj R) :=
  ⟨pullbackCommRingSheafFunctorIsoOfNatIso J e,
    fun R ↦ pullbackCommRingSheafIsoOfNatIso_hom_forget J e R, fun _ hβ ↦
      Iso.ext (NatTrans.ext (funext fun R ↦ (sheafCompose J (forget CommRingCat.{ww})).map_injective
        ((hβ R).trans (pullbackCommRingSheafIsoOfNatIso_hom_forget J e R).symm)))⟩

end Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe v u w v' u' w' v'' u'' w''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]

/-- The inverse-image form of the structure map of a composite, on underlying sheaves of sets, is
the inverse image along `f` of the structure map of `g`, followed by the structure map of `f`. -/
theorem comp_fSharpInverseImage_forget (g : RingedToposHom Y Z) (f : RingedToposHom X Y) :
    X.forgetRing.map (g.comp f).fSharpInverseImage =
      f.toToposHom.inverseImage.map (Y.forgetRing.map g.fSharpInverseImage) ≫
        X.forgetRing.map f.fSharpInverseImage := by
  rw [fSharpInverseImage_forget_homEquiv, fSharpInverseImage_forget_homEquiv,
    fSharpInverseImage_forget_homEquiv, comp_fSharp_forget]
  exact Adjunction.comp_homEquiv_symm_comp g.toToposHom.adj f.toToposHom.adj
    (Z.forgetRing.map g.fSharp) (Y.forgetRing.map f.fSharp)

end AlgebraicGeometry.RingedToposHom

end
