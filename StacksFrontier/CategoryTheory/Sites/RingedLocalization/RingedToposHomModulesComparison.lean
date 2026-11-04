module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
import StacksCore.Tactic.StacksAttribute

/-!
# The two module data of a morphism of ringed topoi agree

A morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` in the sense of
Stacks 01D3 is passed to the pullback of sheaves of modules through one of two four-field data:
`AlgebraicGeometry.RingedToposHom.toModulesHom` takes the inverse-image form `f⁻¹O_D ⟶ O_C` of
the structure map through the adjunction `f⁻¹ ⊣ f_*` for sheaves of rings, and
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` takes it through the adjunction for
sheaves of commutative rings and then forgets commutativity. Both are the adjunct of the same
`f♯`, and the adjunction for commutative rings is the restriction of the one for rings along
the fully faithful inclusion, so the two data are equal.

## Main results

* `AlgebraicGeometry.RingedToposHom.fSharpInverseImageRing_eq_ringFsharpInverseImage`: the two
  inverse-image forms of the structure map agree.
* `AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`: the two
  four-field data agree.
* `AlgebraicGeometry.RingedToposHom.pullbackModules_exact_of_isFlat`:
  **Stacks 04JC** for `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` taken at
  `f.toModulesHom`, pullback of sheaves of modules along a flat morphism of ringed topoi is exact.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

/-- The adjunction bijection of an adjunction restricted along fully faithful functors, read
after the inclusion: it is the adjunction bijection of the ambient adjunction, conjugated by the
two comparison isomorphisms. -/
theorem _root_.CategoryTheory.Adjunction.map_restrictFullyFaithful_homEquiv
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {iC : C ⥤ C'} {iD : D ⥤ D'} {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj : L' ⊣ R')
    (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful) {L : C ⥤ D} {R : D ⥤ C}
    (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC) {X : C} {Y : D}
    (f : L.obj X ⟶ Y) :
    iC.map ((adj.restrictFullyFaithful hiC hiD comm1 comm2).homEquiv X Y f) =
      adj.homEquiv _ _ (comm1.hom.app X ≫ iD.map f) ≫ comm2.hom.app Y := by
  rw [Adjunction.restrictFullyFaithful_homEquiv_apply, Functor.FullyFaithful.map_preimage,
    Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc, Category.assoc]

section Comparison

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y)

/-- The two inverse-image forms `f⁻¹O_D ⟶ O_C` of the structure map of a morphism of ringed
topoi agree: the adjunct of `f♯` for sheaves of rings is the adjunct of `f♯` for sheaves of
commutative rings, with commutativity forgotten. -/
theorem fSharpInverseImageRing_eq_ringFsharpInverseImage :
    f.fSharpInverseImageRing = f.ringFsharpInverseImage := by
  have key : ∀ g : (inverseImageCommRingFunctor f.toToposHom).obj Y.O ⟶ X.O,
      (Stacks.forgetCommRingSheaf Y.J).map
          ((commRingImageAdjunction f.toToposHom).homEquiv Y.O X.O g) =
        (ringImageAdjunction f.toToposHom).homEquiv _ _
          ((Stacks.forgetCommRingSheaf X.J).map g) := by
    intro g
    rw [commRingImageAdjunction, Adjunction.map_restrictFullyFaithful_homEquiv]
    have h₁ : (forgetCommRingSheafCompPullbackIso X.J f.toToposHom.inverseImage).hom.app Y.O ≫
        (Stacks.forgetCommRingSheaf X.J).map g = (Stacks.forgetCommRingSheaf X.J).map g :=
      Category.id_comp _
    rw [h₁]
    exact Category.comp_id _
  have h := key f.fSharpInverseImage
  rw [show (commRingImageAdjunction f.toToposHom).homEquiv Y.O X.O f.fSharpInverseImage =
    f.fSharp from ((commRingImageAdjunction f.toToposHom).homEquiv Y.O X.O).apply_symm_apply
      f.fSharp] at h
  unfold fSharpInverseImageRing
  rw [show f.fSharpRing = (Stacks.forgetCommRingSheaf Y.J).map f.fSharp from rfl, h]
  exact Equiv.symm_apply_apply _ _

/-- The direct-image forms of the structure map agree as well. -/
theorem fSharpRing_eq_ringFsharp : f.fSharpRing = f.ringFsharp := by
  unfold ringFsharp
  rw [← fSharpInverseImageRing_eq_ringFsharpInverseImage, fSharpInverseImageRing]
  exact (Equiv.apply_symm_apply _ _).symm

/-- The four-field datum `toModulesHom`, built over the adjunction for sheaves of rings, is the
four-field datum `toRingedToposModulesHom`, built over the adjunction for sheaves of
commutative rings. -/
theorem toModulesHom_eq_toRingedToposModulesHom :
    f.toModulesHom = f.toRingedToposModulesHom := by
  unfold toModulesHom toRingedToposModulesHom
  congr 1
  · exact f.fSharpRing_eq_ringFsharp
  · exact f.fSharpInverseImageRing_eq_ringFsharpInverseImage

end Comparison

section Flat

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 04JC** for `Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` taken
at `f.toModulesHom`. Pullback of sheaves of modules along a flat morphism of ringed topoi is
exact. -/
theorem pullbackModules_exact_of_isFlat (f : RingedToposHom X Y) (hf : f.IsFlat) :
    exactFunctor (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
      f.toModulesHom.pullbackModules := by
  rw [toModulesHom_eq_toRingedToposModulesHom]
  exact Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap f hf

end Flat

end AlgebraicGeometry.RingedToposHom

end
