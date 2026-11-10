module

public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# Composition of morphisms of ringed topoi is associative

`AlgebraicGeometry.RingedToposHom.comp` composes the underlying morphisms of topoi and takes the
structure map of the composite to be `O_W ⟶ h_*O_Z ⟶ h_*g_*O_Y ⟶ h_*g_*f_*O_X`, read through
the comparisons of successive direct images with the direct image of a composite. The two
bracketings of a threefold composite are equal, though not definitionally.

## Main results

* `AlgebraicGeometry.RingedToposHom.comp_assoc`: `h ∘ (g ∘ f) = (h ∘ g) ∘ f`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w' v'' u'' w'' v₃ u₃ w₃

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}} {W : RingedTopos.{v₃, u₃, w₃}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [W.J.HasSheafCompose (forget RingCat.{w₃})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [W.J.HasSheafCompose (forget₂ CommRingCat.{w₃} RingCat.{w₃})]

/-- The direct image along a composite of morphisms of ringed topoi acts on the underlying topoi
as the composite of the two direct images. -/
theorem toToposHom_pushforward_map_comp (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    {A B : X.Topos} (a : A ⟶ B) :
    (g.comp f).toToposHom.pushforward.map a =
      g.toToposHom.pushforward.map (f.toToposHom.pushforward.map a) :=
  rfl

/-- Reassociation of a threefold composite whose last two factors are direct images, with the
outer direct image of the right-hand side recognised as the direct image along a composite of
morphisms of ringed topoi. -/
theorem pushforward_map_comp_assoc (g : RingedToposHom X Y) (h : RingedToposHom Y Z)
    {V : Z.Topos} {A : Y.Topos} {A' B' : X.Topos} (a : V ⟶ h.toToposHom.pushforward.obj A)
    (b : A ⟶ g.toToposHom.pushforward.obj A') (c : A' ⟶ B') :
    a ≫ h.toToposHom.pushforward.map (b ≫ g.toToposHom.pushforward.map c) =
      (a ≫ h.toToposHom.pushforward.map b) ≫ (h.comp g).toToposHom.pushforward.map c := by
  rw [toToposHom_pushforward_map_comp g h, CategoryTheory.Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- **Composition of morphisms of ringed topoi is associative.** -/
@[stacks 01D3 "part (3): composition is associative"]
theorem comp_assoc (f : RingedToposHom X Y) (g : RingedToposHom Y Z) (h : RingedToposHom Z W) :
    h.comp (g.comp f) = (h.comp g).comp f := by
  rw [RingedToposHom.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [MorphismOfTopoi.mk.injEq]
    refine ⟨rfl, rfl, ?_⟩
    apply heq_of_eq
    apply Adjunction.ext
    apply NatTrans.ext
    funext V
    change (h.toToposHom.adj.comp (g.toToposHom.adj.comp f.toToposHom.adj)).unit.app V =
      ((h.toToposHom.adj.comp g.toToposHom.adj).comp f.toToposHom.adj).unit.app V
    simp only [Adjunction.comp_unit_app, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map, Category.assoc]
  · apply heq_of_eq
    apply W.forgetRing.map_injective
    change W.forgetRing.map (h.comp (g.comp f)).fSharp =
      W.forgetRing.map ((h.comp g).comp f).fSharp
    simp only [comp_fSharp_forget]
    exact pushforward_map_comp_assoc g h _ _ _

end AlgebraicGeometry.RingedToposHom

end
