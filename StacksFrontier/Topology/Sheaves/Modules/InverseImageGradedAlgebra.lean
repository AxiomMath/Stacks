module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackGradedAlgebra
public import StacksFrontier.Topology.Sheaves.Modules.InverseImagePushforwardCounit

/-!
# The inverse image of a sheaf of graded algebras along a continuous map

Let `f : Y ⟶ X` be a continuous map of topological spaces, let `O` be a sheaf of commutative
rings on `X` and let `A` be a sheaf of graded `O`-algebras. The degreewise inverse image
`n ↦ f⁻¹(A_n)` is a sheaf of graded algebras over the inverse image `f⁻¹O` of the base ring: the
pullback of `A` along the morphism of ringed spaces `(Y, f⁻¹O) ⟶ (X, O)`, whose homogeneous
pieces are the inverse images `AlgebraicGeometry.SheafOfModules.inverseImageModule` of those of
`A`.

For an inducing `f`, a degreewise identification of `A` with a direct image identifies the pieces
of `f⁻¹A` with the sheaves being pushed forward.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.inverseImageGradedAlgebra`: the sheaf of graded
  `f⁻¹O`-algebras `f⁻¹A`.
* `AlgebraicGeometry.SheafOfModules.inverseImageGradedAlgebraPieceIso`: for an inducing `f`, the
  pieces of `f⁻¹A` are the sheaves a degreewise presentation of `A` as a direct image pushes
  forward.
* `AlgebraicGeometry.SheafOfModules.inverseImageGradedAlgebraPieceIsoRestrictScalars`: the same,
  with the pushed-forward sheaves living over a larger sheaf of rings.

## Main results

* `AlgebraicGeometry.SheafOfModules.inverseImageGradedAlgebra_piece`: the homogeneous pieces of
  `f⁻¹A` are the inverse images of those of `A`.
* `AlgebraicGeometry.SheafOfModules.inverseImageGradedAlgebra_mul_app`: the multiplication of
  `f⁻¹A` on a pure tensor of local sections.

## References

* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX) — functoriality of
  sheaves of graded algebras.
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW) — sheaves of graded
  algebras.
* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633) — the conormal algebra
  of an immersion.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X Y : TopCat.{u}} (f : Y ⟶ X) (O : TopCat.Sheaf CommRingCat.{u} X)
  (A : _root_.SheafOfModules.GradedAlgebra.{u, u} (underlyingRingSheaf O))

/-- **The inverse image of a sheaf of graded algebras along a continuous map.** The homogeneous
pieces are the inverse images `f⁻¹(A_n)`, and the multiplication and the unit are those of `A`
conjugated by the tensorator of the monoidal inverse-image functor: it is the pullback of `A`
along the canonical morphism of ringed spaces `(Y, f⁻¹O) ⟶ (X, O)`. -/
noncomputable def inverseImageGradedAlgebra :
    _root_.SheafOfModules.GradedAlgebra.{u, u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O)) :=
  Stacks.PullbackGradedAlgebra.pullbackGradedAlgebra
    (AlgebraicGeometry.RingedSpace.inverseImageProjection (ringedSpaceOfSheaf O) f) A
    (underlyingRingSheaf O).property

/-- **The homogeneous pieces of `f⁻¹A` are the inverse images of the homogeneous pieces of
`A`**, on the nose. -/
theorem inverseImageGradedAlgebra_piece (n : ℤ) :
    (inverseImageGradedAlgebra f O A).piece n = inverseImageModule f O (A.piece n) :=
  rfl

/-- The multiplication of `f⁻¹A` on a pure tensor of local sections of the inverse images. -/
theorem inverseImageGradedAlgebra_mul_app (i j : ℤ) (U : (Opens Y)ᵒᵖ)
    (x : (inverseImageModule f O (A.piece i)).val.obj U)
    (y : (inverseImageModule f O (A.piece j)).val.obj U) :
    ((inverseImageGradedAlgebra f O A).mul i j).app U x y =
      (Stacks.PullbackGradedAlgebra.pullbackMul
          (AlgebraicGeometry.RingedSpace.inverseImageProjection (ringedSpaceOfSheaf O) f)
          A i j).val.app U
        ((PresheafOfModules.tensorSheafUnit (inverseImageModule f O (A.piece i))
          (inverseImageModule f O (A.piece j))).app U (x ⊗ₜ y)) :=
  rfl

/-! ### The pieces of `f⁻¹A` under a degreewise presentation of `A` as a direct image -/

/-- **The pieces of `f⁻¹A` under a degreewise presentation of `A` as a direct image.** Let `f`
be inducing and suppose each homogeneous piece of `A` is identified with the direct image of a
sheaf `C n` of `f⁻¹O`-modules. Then the `n`-th piece of `f⁻¹A` is `C n`. -/
noncomputable def inverseImageGradedAlgebraPieceIso
    (hf : IsInducing (ConcreteCategory.hom f))
    (C : ℤ → _root_.SheafOfModules.{u}
      (underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O)))
    (e : ∀ n : ℤ, A.piece n ≅
      (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f O)).obj (C n))
    (n : ℤ) :
    (inverseImageGradedAlgebra f O A).piece n ≅ C n :=
  inverseImageIsoOfPushforwardIso f O hf (e n)

/-- **The pieces of `f⁻¹A` under a degreewise presentation of `A` as a direct image**, with the
sheaves `C n` on `Y` given over a sheaf of rings `R` under `f⁻¹O` and read over `f⁻¹O` by
restriction of scalars along `a : f⁻¹O ⟶ R`. -/
noncomputable def inverseImageGradedAlgebraPieceIsoRestrictScalars
    (hf : IsInducing (ConcreteCategory.hom f))
    {R : CategoryTheory.Sheaf.{u, u, u, u + 1} (Opens.grothendieckTopology Y) RingCat.{u}}
    (a : underlyingRingSheaf ((TopCat.Sheaf.pullback CommRingCat.{u} f).obj O) ⟶ R)
    (C : ℤ → _root_.SheafOfModules.{u} R)
    (e : ∀ n : ℤ, A.piece n ≅
      (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom f O)).obj
        ((_root_.SheafOfModules.restrictScalars.{u} a).obj (C n)))
    (n : ℤ) :
    (inverseImageGradedAlgebra f O A).piece n ≅
      (_root_.SheafOfModules.restrictScalars.{u} a).obj (C n) :=
  inverseImageIsoOfPushforwardIso f O hf (e n)

end AlgebraicGeometry.SheafOfModules

end
