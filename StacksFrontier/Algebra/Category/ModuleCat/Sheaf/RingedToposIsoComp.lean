module

public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# Composites of isomorphisms of ringed topoi

A morphism of ringed topoi is an isomorphism, in the sense used by Stacks 05YZ, when its direct
image is an equivalence of topoi and its structure map `f♯ : O_Y ⟶ f_*O_X` is an isomorphism.
Both conditions pass to composites: the direct image of `g ∘ f` is `f_*` followed by `g_*`, and
the structure map of `g ∘ f` is `g♯` followed by `g_*(f♯)` and the comparison of successive direct
images, an isomorphism.

## Main results

* `AlgebraicGeometry.RingedToposHom.isEquivalence_comp_pushforward`
* `AlgebraicGeometry.RingedToposHom.isIso_comp_fSharp`
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w' v'' u'' w''

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  (g : RingedToposHom Y Z) (f : RingedToposHom X Y)

/-- The direct image of a composite of morphisms of ringed topoi whose direct images are
equivalences is an equivalence. -/
instance isEquivalence_comp_pushforward [f.toToposHom.pushforward.IsEquivalence]
    [g.toToposHom.pushforward.IsEquivalence] :
    (g.comp f).toToposHom.pushforward.IsEquivalence :=
  inferInstanceAs (f.toToposHom.pushforward ⋙ g.toToposHom.pushforward).IsEquivalence

/-- The structure map of a composite of morphisms of ringed topoi with invertible structure maps
is invertible. -/
instance isIso_comp_fSharp [IsIso g.fSharp] [IsIso f.fSharp] : IsIso (g.comp f).fSharp :=
  inferInstanceAs (IsIso (g.fSharp ≫ (pushforwardCommRingFunctor g.toToposHom).map f.fSharp ≫
    (pushforwardCommRingCompIso f.toToposHom g.toToposHom X.O).hom))

end AlgebraicGeometry.RingedToposHom

end
