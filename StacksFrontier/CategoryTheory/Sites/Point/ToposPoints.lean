module

public import StacksFrontier.CategoryTheory.Sites.Point.Defs

/-!
# Morphisms of topoi and points

Composing a morphism of topoi `f : Sh(D) → Sh(C)` with a point `q` of `Sh(D)` gives a point
of `Sh(C)`, and the stalk of `f⁻¹ F` at `q` is the stalk of `F` at the composite point.

## Main definitions

* `PointOfTopos.stalk`: the stalk `F_p = p⁻¹ F` of a sheaf at a point of the topos.
* `MorphismOfTopoi.compPoint`: the point `f ∘ q` of `Sh(C)` obtained from a point `q` of
  `Sh(D)` and a morphism of topoi `f : Sh(D) → Sh(C)`.

## Main results

* `MorphismOfTopoi.stalk_inverseImage`: `(f⁻¹ F)_q = F_{f ∘ q}`.
-/

@[expose] public section

open CategoryTheory

universe w v u v' u'

/-- The stalk `F_p` of a sheaf `F` at a point `p` of the topos `Sh(C, J)` is `p⁻¹ F`. -/
def PointOfTopos.stalk {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (p : PointOfTopos.{w, v, u} J) (F : Sheaf J (Type w)) : Type w :=
  p.inverseImage.obj F

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}

/-- A point `q` of `Sh(D, K)` composed with a morphism of topoi `f : Sh(D, K) → Sh(C, J)` is
a point `f ∘ q` of `Sh(C, J)`. -/
def compPoint (f : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w)))
    (q : PointOfTopos.{w, v', u'} K) : PointOfTopos.{w, v, u} J :=
  f.comp q

/-- For a morphism of topoi `f : Sh(D) → Sh(C)`, a point `q` of `Sh(D)` and a sheaf `F` on `C`,
the stalk `(f⁻¹ F)_q` is the stalk `F_{f ∘ q}` at the composite point `f.compPoint q`. -/
@[stacks 05V2]
theorem stalk_inverseImage (f : MorphismOfTopoi (Sheaf K (Type w)) (Sheaf J (Type w)))
    (q : PointOfTopos.{w, v', u'} K) (F : Sheaf J (Type w)) :
    q.stalk (f.inverseImage.obj F) = (f.compPoint q).stalk F :=
  rfl

end MorphismOfTopoi
