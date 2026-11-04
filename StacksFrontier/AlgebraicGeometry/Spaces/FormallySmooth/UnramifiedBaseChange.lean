module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.BaseChange

/-!
# Base change of a formally unramified morphism of algebraic spaces

In any cartesian square of algebraic spaces over a scheme, the base change of a formally
unramified morphism is formally unramified.

## Main results

* `AlgebraicGeometry.Space.formallyUnramified_of_isPullback`: **Stacks 0600**, which is also the
  first assertion of Stacks 060B.

## Implementation notes

The corresponding statement for transformations of arbitrary set-valued functors on the big
fppf site is `AlgebraicGeometry.Space.formallyUnramified_baseChange`, which is phrased for the
chosen fibre product of presheaves. What is added here is independence of that choice: the
square is only assumed cartesian in the category of algebraic spaces, so the base-changed
morphism is compared with the chosen one through the canonical isomorphism of the two fibre
products. Transporting the lifting condition along that isomorphism is the whole proof, and it
uses only that an isomorphism of presheaves is a bijection on sections over every test object.

## References

* [Stacks Project, Tag 0600](https://stacks.math.columbia.edu/tag/0600)
* [Stacks Project, Tag 060B](https://stacks.math.columbia.edu/tag/060B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0600.** A base change of a formally unramified morphism of algebraic spaces is
formally unramified: in a cartesian square with `f` formally unramified, the opposite side `p`
of the square is formally unramified.

This is also the first assertion of Stacks 060B: in a fibre product diagram
`Z = X ×_Y W` of algebraic spaces over `S` with `h' : W ⟶ Y` formally unramified (here `f`),
the morphism `h : Z ⟶ X` (here `p`) is formally unramified. -/
@[stacks 0600, stacks 060B "the first assertion: in a fibre product diagram, the base change \
`h` of a formally unramified `h'` is formally unramified", ega "IV 17.1.3" "more general"]
theorem formallyUnramified_of_isPullback
    {F G H P : AlgebraicSpaces B S hS}
    (f : F ⟶ G) (g : H ⟶ G) (p : P ⟶ H) (q : P ⟶ F)
    (sq : IsPullback p q g f)
    (unramified : FormallyUnramified f.hom) :
    FormallyUnramified p.hom := by
  let D : FppfFunctorPullbackSituation.{u, u} := ⟨B, S, hS, F.obj, G.obj, H.obj, f.hom, g.hom⟩
  -- Compare `p` with the chosen fibre-product projection through the canonical isomorphism.
  let Q : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS g f
  let eSub : P ≅ Q := sq.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS g f)
  have heSub : eSub.hom.hom ≫ pullback.fst g.hom f.hom = p.hom :=
    congrArg (fun k => k.hom)
      (sq.isoIsPullback_hom_fst _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS g f))
  let eD : Q.obj ≅ D.fibreProduct :=
    IsPullback.isoIsPullback _ _ (IsPullback.of_hasPullback g.hom f.hom) D.isPullback
  have heD : eD.hom ≫ D.toH = pullback.fst g.hom f.hom :=
    IsPullback.isoIsPullback_hom_fst _ _ (IsPullback.of_hasPullback g.hom f.hom) D.isPullback
  let eQ : P.obj ≅ Q.obj := (ObjectProperty.ι _).mapIso eSub
  let e : P.obj ≅ D.fibreProduct := eQ ≪≫ eD
  have he : e.hom ≫ D.toH = p.hom := (Category.assoc _ _ _).trans ((eQ.hom ≫= heD).trans heSub)
  -- Transport the uniqueness of lifts along `e`.
  intro T T' hT hT' i hi x y hxy z₁ z₂ hz₁ hz₂
  have hmap (W : BigFppfOver B S hS) (z : P.obj.obj (op W)) :
      D.toH.app (op W) (e.hom.app (op W) z) = p.hom.app (op W) z := by
    simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using
      congrFun (congrArg (fun k => k.app (op W)) he) z
  have hlift (z : P.obj.obj (op T')) (hz : IsLift p.hom i x y z) :
      IsLift D.toH i (e.hom.app (op T) x) y (e.hom.app (op T') z) := by
    refine ⟨?_, (hmap T' z).trans hz.2⟩
    rw [← e.hom.naturality_apply i.op z, hz.1]
  have heq : e.hom.app (op T') z₁ = e.hom.app (op T') z₂ :=
    formallyUnramified_baseChange D unramified T T' hT hT' i hi _ y ((hmap T x).trans hxy) _ _
      (hlift z₁ hz₁) (hlift z₂ hz₂)
  simpa using congrArg (e.inv.app (op T')) heq

end AlgebraicGeometry.Space

end
