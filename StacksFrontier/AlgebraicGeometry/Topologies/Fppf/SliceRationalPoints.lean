module

public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SliceFiniteProducts

/-!
# Rational points of a restricted functor of points are rational points of the scheme over `S`

A *rational point* of a presheaf on the big fppf category over `S` is a morphism out of the
terminal object `Over.mk (𝟙 (B.obj hS))`, that is out of `S` itself; this is the notion the
point-space and density statements for algebraic spaces over `S` are phrased with.  For a scheme
`X` over `S` the presheaf in question is the restricted functor of points
`AlgebraicGeometry.bigFppfRestrictedYoneda`, and a rational point of it is the same datum as a
morphism `Over.mk (𝟙 S) ⟶ X` of schemes over `S`, which is the notion the slice-category
statements about products of projective spaces are phrased with.

The identification is the Yoneda lemma and nothing else: a morphism `yoneda.obj T ⟶ F` is an
element of `F.obj (op T)`, and for `F` the restricted functor of points of `X` and `T` the
terminal object of the site that set *is* the set of morphisms `Over.mk (𝟙 S) ⟶ X`, because the
comparison functor `CategoryTheory.Over.post B.inclusion` sends the terminal object of the site
to the identity of `S`.  Being the Yoneda bijection it is natural in `X`, which is the clause
that makes a diagram of schemes over `S` transport to a diagram of presheaves.

Recorded here as well is the naturality in the *site object* of
`AlgebraicGeometry.bigFppfOverRestrictedYonedaIso`, the isomorphism comparing the functor of
points of an object of the site with the restriction of the functor of points of the scheme over
`S` that it names.  That isomorphism is defined one object at a time, so the compatibility of
the comparison with a morphism of the site has to be proved; it holds because the comparison is
the inverse of `CategoryTheory.Functor.FullyFaithful.homEquiv` of
`AlgebraicGeometry.fullyFaithful_overPost_bigFppfInclusion`, hence sends a composite to a
composite.

## Main definitions

* `AlgebraicGeometry.bigFppfRestrictedRationalPointEquiv`: **the rational points of the
  restricted functor of points of a scheme `X` over `S` are the morphisms
  `Over.mk (𝟙 S) ⟶ X`.**

## Main results

* `AlgebraicGeometry.bigFppfRestrictedRationalPointEquiv_comp`: that bijection carries a
  rational point followed by the restricted functor of points of a morphism of schemes over `S`
  to the corresponding morphism of schemes over `S` followed by that morphism.
* `AlgebraicGeometry.yoneda_map_comp_bigFppfOverRestrictedYonedaIso_inv`: the comparison of the
  functor of points of a site object with the restricted functor of points of the scheme over `S`
  it names is natural in the site object.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The rational points of the restricted functor of points of a scheme `X` over `S` are the
morphisms `Over.mk (𝟙 S) ⟶ X` of schemes over `S`.** A rational point is a morphism out of
`yoneda.obj (Over.mk (𝟙 (B.obj hS)))`, the functor of points of the terminal object of the big
fppf category over `S`, so by the Yoneda lemma it is an element of the value of the restricted
functor of points at that terminal object; and the comparison functor to schemes over `S` sends
the terminal object of the site to the identity of `S`, so that value is the set of morphisms
`Over.mk (𝟙 S) ⟶ X`. -/
def bigFppfRestrictedRationalPointEquiv (X : Over S) :
    (yoneda.obj (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B S hS) ⟶
        (bigFppfRestrictedYoneda B S hS).obj X) ≃
      (Over.mk (𝟙 S) ⟶ X) :=
  yonedaEquiv

/-- **The identification of rational points with morphisms of schemes over `S` is natural.** A
rational point of the restricted functor of points of `X` followed by the restricted functor of
points of a morphism `h : X ⟶ Y` of schemes over `S` is the morphism `Over.mk (𝟙 S) ⟶ X` named by
the point, followed by `h`. -/
theorem bigFppfRestrictedRationalPointEquiv_comp {X Y : Over S}
    (ξ : yoneda.obj (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B S hS) ⟶
      (bigFppfRestrictedYoneda B S hS).obj X) (h : X ⟶ Y) :
    bigFppfRestrictedRationalPointEquiv B S hS Y
        (ξ ≫ (bigFppfRestrictedYoneda B S hS).map h) =
      bigFppfRestrictedRationalPointEquiv B S hS X ξ ≫ h := by
  change yonedaEquiv (ξ ≫ (bigFppfRestrictedYoneda B S hS).map h) = yonedaEquiv ξ ≫ h
  rw [yonedaEquiv_comp]
  rfl

/-- **The comparison of the functor of points of an object of the big fppf category over `S` with
the restricted functor of points of the scheme over `S` that it names is natural in the
object.** Its inverse sends a morphism of the site to its image under the comparison functor
`CategoryTheory.Over.post B.inclusion`, and that functor sends a composite to a composite. -/
theorem yoneda_map_comp_bigFppfOverRestrictedYonedaIso_inv {W W' : BigFppfOver B S hS}
    (g : W ⟶ W') :
    yoneda.map g ≫ (bigFppfOverRestrictedYonedaIso B S hS W').inv =
      (bigFppfOverRestrictedYonedaIso B S hS W).inv ≫
        (bigFppfRestrictedYoneda B S hS).map
          ((Over.post (X := B.obj hS) B.inclusion).map g) := by
  ext X v
  change X.unop ⟶ W at v
  change (Over.post (X := B.obj hS) B.inclusion).map (v ≫ g) =
    (Over.post (X := B.obj hS) B.inclusion).map v ≫
      (Over.post (X := B.obj hS) B.inclusion).map g
  rw [Functor.map_comp]

end AlgebraicGeometry

end
