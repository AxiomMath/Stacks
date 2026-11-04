module

public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSliceAlgebraEssentialImage
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSliceAlgebraMapArrow
public import StacksFrontier.AlgebraicGeometry.Topologies.CoordinateAlgebraComparison

/-!
# The covering object of the Amitsur endpoint, at an affine object over an affine object

Let `S` be a scheme, `U` an object of `Over S` whose total space is affine, `R = Γ(U.left, 𝒪)`,
and let `f : W ⟶ U` be a morphism of `Over S` whose source has affine total space. Put
`A = Γ(W.left, 𝒪)`, an `R`-algebra through `f`. The spectrum over `U` of the universe lift
`AlgebraicGeometry.overAffineAlgObj U A` of `A` is `Over.mk f`.

## Main definitions

* `AlgebraicGeometry.overAffineSliceAlgebra`: the `R`-algebra structure on `A` induced by `f`.
* `AlgebraicGeometry.overAffineAlgObjIsoGammaAlg`: the isomorphism, given by `ULift.ringEquiv`,
  of `AlgebraicGeometry.overAffineAlgObj U A` with the coordinate algebra that
  `Stacks.Sites.gammaAlg` attaches to `Over.mk f`.
* `AlgebraicGeometry.specOverAffineAlgObjIsoMk`: the spectrum of
  `AlgebraicGeometry.overAffineAlgObj U A`, over `U`, is `Over.mk f`.
* `AlgebraicGeometry.mkIsoMkSpecOverAffineAlgObj`: the same, as an isomorphism
  `Over.mk f ≅ Over.mk (⋯).hom` of objects presented by their structure morphisms.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicTopology
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} (U : Over S) [IsAffine U.left]

/-- The algebra structure on the coordinate ring of the source of a morphism `f : W ⟶ U` of
`Over S` over the coordinate ring of `U.left`, induced by `f` itself. -/
@[instance_reducible]
public def overAffineSliceAlgebra {W : Over S} (f : W ⟶ U) :
    Algebra (Γ(U.left, ⊤) : Type u) (Γ(W.left, ⊤) : Type u) :=
  f.left.appTop.hom.toAlgebra

/-- The isomorphism, over `ULift Γ(U.left, 𝒪)` and given by `ULift.ringEquiv`, of
`AlgebraicGeometry.overAffineAlgObj U Γ(W.left, 𝒪)`, whose carrier is the universe lift of
`Γ(W.left, 𝒪)`, with the algebra `Stacks.Sites.gammaAlg` attaches to `Over.mk f`, whose carrier
is `Γ(W.left, 𝒪)`. -/
public def overAffineAlgObjIsoGammaAlg {W : Over S} (f : W ⟶ U) :
    letI := overAffineSliceAlgebra U f
    overAffineAlgObj U (Γ(W.left, ⊤) : Type u) ≅
      (Stacks.Sites.gammaAlg S (𝟭 (Over S)) U).obj (op (Over.mk f)) :=
  letI := overAffineSliceAlgebra U f
  letI : Algebra (ULift.{u} (Γ(U.left, ⊤) : Type u))
      (((Stacks.Sites.gammaAlg S (𝟭 (Over S)) U).obj (op (Over.mk f))) : Type u) :=
    ((Stacks.Sites.gammaAlg S (𝟭 (Over S)) U).obj (op (Over.mk f))).algebra
  { hom := ConcreteCategory.ofHom
      { __ := (ULift.ringEquiv (R := (Γ(W.left, ⊤) : Type u))).toRingHom
        commutes' := fun _ => rfl }
    inv := ConcreteCategory.ofHom
      { __ := (ULift.ringEquiv (R := (Γ(W.left, ⊤) : Type u))).symm.toRingHom
        commutes' := fun _ => rfl }
    hom_inv_id := rfl
    inv_hom_id := rfl }

/-- The spectrum, over `U`, of the universe lift of the coordinate ring of `W.left` is
isomorphic to `Over.mk f`. -/
public def specOverAffineAlgObjIsoMk {W : Over S} (f : W ⟶ U) [IsAffine W.left] :
    letI := overAffineSliceAlgebra U f
    (overAffineAlgSpec U).obj (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u))) ≅ Over.mk f :=
  letI := overAffineSliceAlgebra U f
  ((overAffineAlgSpec U).mapIso
      (overAffineAlgObjIsoGammaAlg U f ≪≫
        (gammaAlgIsoOverAffineAlgΓ U).app (op (Over.mk f))).op).symm ≪≫
    overAffineAlgSpecΓIsoMk U f

/-- The inverse of `AlgebraicGeometry.specOverAffineAlgObjIsoMk`, with the spectrum presented as
`CategoryTheory.Over.mk` of its structure morphism. -/
public def mkIsoMkSpecOverAffineAlgObj {W : Over S} (f : W ⟶ U) [IsAffine W.left] :
    letI := overAffineSliceAlgebra U f
    Over.mk f ≅ Over.mk ((overAffineAlgSpec U).obj
      (op (overAffineAlgObj U (Γ(W.left, ⊤) : Type u)))).hom :=
  letI := overAffineSliceAlgebra U f
  (specOverAffineAlgObjIsoMk U f).symm ≪≫ Over.isoMk (Iso.refl _)

end AlgebraicGeometry

end
