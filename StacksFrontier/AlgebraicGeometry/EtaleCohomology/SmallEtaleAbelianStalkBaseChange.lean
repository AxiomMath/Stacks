module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageStalkRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stalks of abelian étale sheaves under inverse image

Let `g : X' ⟶ X` be a morphism of schemes and let `s : Spec Ω ⟶ X'` be a geometric point of `X'`,
with `Ω` separably closed. For an abelian sheaf `F` on the small étale site of `X` the stalk of
the inverse image `g⁻¹F` at `s` is the stalk of `F` at the image geometric point `s ≫ g`:

`(g⁻¹F)_s = F_{s ≫ g}`,

naturally in `F`. This file proves that, as an isomorphism
`Stacks.EtaleCohomology.smallEtaleStalkPullbackAbIso` of functors
`Sheaf (smallEtaleTopology X) Ab ⥤ Ab`, together with the formula describing it on germs.

## Main definitions

* `Stacks.EtaleCohomology.pointSmallEtaleComapFiberIso` — the fibre functor of the point at
  `s ≫ g` is the fibre functor of the inverse image along base change of the point at `s`.
* `Stacks.EtaleCohomology.smallEtaleStalkPullbackAbIso` — the stalk at `s` of the inverse image
  along `g` of an abelian étale sheaf is its stalk at `s ≫ g`.

## Main results

* `Stacks.EtaleCohomology.toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv` — on the germ at
  `s ≫ g` of a section over an étale neighbourhood `W` of that point, the comparison is the unit
  of the inverse-image/direct-image adjunction followed by the germ at the corresponding lift of
  `s` to `W ×_X X'`.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### The stalk of an abelian inverse image -/

section

variable {X X' : Scheme.{u}} (g : X' ⟶ X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X')

/-- Base change along `g : X' ⟶ X` followed by the fibre functor of the point of the small étale
site of `X'` determined by a geometric point `s` has an initially small category of elements. -/
instance initiallySmall_elements_smallEtaleBaseChange_comp_pointSmallEtale_fiber :
    InitiallySmall.{u}
      (smallEtaleBaseChange g ⋙ (Scheme.pointSmallEtale s).fiber).Elements :=
  initiallySmall_of_initial_of_initiallySmall
    (CategoryOfElements.equivalenceOfNatIso (pointSmallEtaleBaseChangeFiberIso g s)).functor

/-- Base change along a morphism of schemes carries covering sieves of the small étale site of the
target to covering sieves of the small étale site of the source. -/
theorem coverPreserving_smallEtaleBaseChange :
    CoverPreserving (smallEtaleTopology X) (smallEtaleTopology X') (smallEtaleBaseChange g) :=
  CoverPreserving.of_isContinuous _ _ _

/-- The canonical bijection between the lifts of `s` to a base change `W ×_X X'` and the lifts of
`s ≫ g` to `W`, read as an isomorphism between the fibre functor of the point of the small étale
site of `X` determined by `s ≫ g` and that of the inverse image along base change of the point
determined by `s`. -/
def pointSmallEtaleComapFiberIso :
    (Scheme.pointSmallEtale (s ≫ g)).fiber ≅
      ((Scheme.pointSmallEtale s).comap (smallEtaleBaseChange g)
        (coverPreserving_smallEtaleBaseChange g)).fiber :=
  pointSmallEtaleBaseChangeFiberIso g s

/-- **Stalks of an inverse image of abelian étale sheaves.** For `g : X' ⟶ X` and a geometric
point `s : Spec Ω ⟶ X'` with `Ω` separably closed, the stalk at `s` of the inverse image `g⁻¹F` of
an abelian sheaf `F` on the small étale site of `X` is the stalk of `F` at the image geometric
point `s ≫ g`, naturally in `F`.

For a geometric point `x'` of `X'` this reads
`smallEtalePullbackAb g ⋙ smallEtaleStalkAb x'.hom ≅ smallEtaleStalkAb (x'.map g).hom`, the
image geometric point being `AlgebraicGeometry.GeometricPoint.map`. -/
@[sga "4 VIII 3.4" "abelian sheaves", sga "4½ Arcata 2.3.3"]
def smallEtaleStalkPullbackAbIso :
    smallEtalePullbackAb g ⋙ smallEtaleStalkAb s ≅ smallEtaleStalkAb (s ≫ g) :=
  ((Scheme.pointSmallEtale s).sheafFiberComapIso (smallEtaleBaseChange g)
      (coverPreserving_smallEtaleBaseChange g) Ab.{u + 1}).symm ≪≫
    (Point.sheafFiberIsoOfFiberIso (A := Ab.{u + 1}) (Scheme.pointSmallEtale (s ≫ g))
      ((Scheme.pointSmallEtale s).comap (smallEtaleBaseChange g)
        (coverPreserving_smallEtaleBaseChange g)) (pointSmallEtaleComapFiberIso g s)).symm

/-- The comparison of stalks is, on each abelian étale sheaf, the transport along the
isomorphism of fibre functors followed by the identification of the stalk at an
inverse-image point with the stalk of the inverse image. -/
theorem smallEtaleStalkPullbackAbIso_inv_app (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtaleStalkPullbackAbIso g s).inv.app F =
      (Point.presheafFiberIsoOfFiberIso (A := Ab.{u + 1}) (Scheme.pointSmallEtale (s ≫ g))
          ((Scheme.pointSmallEtale s).comap (smallEtaleBaseChange g)
            (coverPreserving_smallEtaleBaseChange g))
          (pointSmallEtaleComapFiberIso g s)).hom.app F.obj ≫
        ((Scheme.pointSmallEtale s).sheafFiberComapIso (smallEtaleBaseChange g)
          (coverPreserving_smallEtaleBaseChange g) Ab.{u + 1}).hom.app F :=
  rfl

/-- On the germ at `s ≫ g` of a section of an abelian étale sheaf `F` over an étale neighbourhood
`W` of that point, the comparison of stalks is the unit of the inverse-image/direct-image
adjunction followed by the germ at the corresponding lift of `s` to the base change `W ×_X X'`.
-/
theorem toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale (s ≫ g)).fiber.obj W) :
    (Scheme.pointSmallEtale (s ≫ g)).toPresheafFiber W v F.obj ≫
        (smallEtaleStalkPullbackAbIso g s).inv.app F =
      ((smallEtaleAdjunctionAb g).unit.app F).hom.app (op W) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber ((smallEtaleBaseChange g).obj W)
          ((pointSmallEtaleComapFiberIso g s).hom.app W v)
          ((smallEtalePullbackAb g).obj F).obj := by
  have h1 := Point.toPresheafFiber_presheafFiberIsoOfFiberIso (A := Ab.{u + 1})
    (Scheme.pointSmallEtale (s ≫ g))
    ((Scheme.pointSmallEtale s).comap (smallEtaleBaseChange g)
      (coverPreserving_smallEtaleBaseChange g)) (pointSmallEtaleComapFiberIso g s) F.obj W v
  have h2 := Point.toSheafFiber_sheafFiberComapIso_hom (Scheme.pointSmallEtale s)
    (smallEtaleBaseChange g) (coverPreserving_smallEtaleBaseChange g) F W
    ((pointSmallEtaleComapFiberIso g s).hom.app W v)
  rw [smallEtaleStalkPullbackAbIso_inv_app]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ((Scheme.pointSmallEtale s).sheafFiberComapIso (smallEtaleBaseChange g)
      (coverPreserving_smallEtaleBaseChange g) Ab.{u + 1}).hom.app F) h1).trans h2)

end

end Stacks.EtaleCohomology

end
