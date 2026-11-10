module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism

/-!
# Going through an equivalence of ringed topoi and back

For an equivalence of ringed topoi `f : X ⟶ Y` (direct image an equivalence, structure map an
isomorphism) with inverse `f⁻¹ = AlgebraicGeometry.RingedToposHom.inverse f`, and any morphism
`g : X ⟶ Z`, the composite `(g ∘ f⁻¹) ∘ f` is 2-isomorphic to `g` (Stacks 04IC).

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.compInverseCompRingedToposEquivalenceTwoIso`:
  the 2-isomorphism `(g ∘ f⁻¹) ∘ f ≅ g`.

## Main results

* `AlgebraicGeometry.RingedToposHom.forgetFSharp_inverse_comp_counit_ringedToposEquivalenceTwoIso`:
  the structure map of `f⁻¹`, the inverse image of that of `f` and the counit of `f⁻¹ ⊣ f_*`
  compose to the identity.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u w v' u' w' v'' u'' w''

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]

/-- The structure map of the inverse of an equivalence of ringed topoi, followed by the inverse
image of the structure map of `f` and the counit of `f⁻¹ ⊣ f_*`, is the identity of `O_X`. -/
theorem forgetFSharp_inverse_comp_counit_ringedToposEquivalenceTwoIso (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp] :
    forgetFSharp (inverse f) ≫ f.toToposHom.inverseImage.map (forgetFSharp f) ≫
      f.toToposHom.adj.counit.app (X.forgetRing.obj X.O) = 𝟙 _ := by
  change X.forgetRing.map (inv f.fSharpInverseImage) ≫ _ = _
  rw [Functor.map_inv]
  exact (congrArg (inv (X.forgetRing.map f.fSharpInverseImage) ≫ ·)
    (fSharpInverseImage_forget f).symm).trans (IsIso.inv_hom_id _)

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- **Going through an equivalence and back is a 2-isomorphism**: for an equivalence of ringed
topoi `f : X ⟶ Y` and any `g : Y ⟶ Z`, the composite `(g ∘ f⁻¹) ∘ f` is 2-isomorphic to `g`,
on direct images through the counit of `f⁻¹ ⊣ f_*`. -/
def TwoIso.compInverseCompRingedToposEquivalenceTwoIso (g : RingedToposHom X Z)
    (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp] :
    TwoIso ((g.comp (inverse f)).comp f) g where
  e := Functor.isoWhiskerRight (asIso f.toToposHom.adj.counit) g.toToposHom.pushforward ≪≫
    Functor.leftUnitor _
  commutes := by
    rw [forgetFSharp_comp (g.comp (inverse f)) f, forgetFSharp_comp g (inverse f)]
    have key := congrArg g.toToposHom.pushforward.map
      (forgetFSharp_inverse_comp_counit_ringedToposEquivalenceTwoIso f)
    rw [Functor.map_comp, Functor.map_comp, CategoryTheory.Functor.map_id] at key
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, asIso_hom, Functor.leftUnitor_hom_app, Category.assoc]
    exact (congrArg (forgetFSharp g ≫ ·) key).trans (Category.comp_id _)

end AlgebraicGeometry.RingedToposHom

end
