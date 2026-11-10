module

public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequenceSquare
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposNaiveComparison
public import StacksFrontier.Cotangent.SheavesOfRings.SquareFunctoriality

/-!
# The comparison with the naive cotangent complex is natural in degree `-1`

For a commutative square of homomorphisms of sheaves of commutative rings the cotangent
complexes and the naive cotangent complexes built from the degree-zero terms of the standard
resolutions are functorial, and the canonical map `L ⟶ NL` of Tag 08US commutes with the two
functorialities in degree `-1`: on a pure differential `d x` both composites give the class of
the difference of the two faces of the image of `x`, the map of standard resolutions being
simplicial.

## Main results

* `CategoryTheory.Sheaf.squareCotangentTermMap_comp_naiveComparisonNegOne`: the naturality in
  degree `-1`.

## References

* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A A' B B' : Sheaf J CommRingCat.{max u v w}} {f : A ⟶ B} {f' : A' ⟶ B'} {a : A ⟶ A'}
  {b : B ⟶ B'}

/-- The difference of the two faces commutes with a map of standard resolutions. -/
theorem faceDifference_resolution (sq : ResolutionSquareMap.{u, v, w} J f f' a b) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J f (op ⦋1⦌)).obj.obj U) :
    ((sq.resolution (op ⦋0⦌)).hom.app U (faceDifference J f U x) : _) =
      faceDifference J f' U ((sq.resolution (op ⦋1⦌)).hom.app U x) := by
  change (sq.resolution (op ⦋0⦌)).hom.app U (faceSections J f 0 U x - faceSections J f 1 U x) =
    faceSections J f' 0 U _ - faceSections J f' 1 U _
  rw [map_sub]
  exact congrArg₂ (· - ·) (sq.resolution_naturality_app (SimplexCategory.δ 0).op U x)
    (sq.resolution_naturality_app (SimplexCategory.δ 1).op U x)

/-- **The comparison `L ⟶ NL` is natural in degree `-1`.** For a map of standard resolutions
over a square `(a, b)`, the degree `-1` comparison of the target precomposed with the map of
base-changed differentials is the degree `-1` comparison of the source followed by the map of
conormal sheaves of the degree-zero presentations. -/
theorem squareCotangentTermMap_comp_naiveComparisonNegOne
    (sq : ResolutionSquareMap.{u, v, w} J f f' a b) :
    squareCotangentTermMap sq (op ⦋1⦌) ≫
        (squareRestrict.{u, v, w} J b).map (naiveComparisonNegOne J f') =
      naiveComparisonNegOne J f ≫
        Stacks.Sites.Conormal.conormalSheafMapOfSquare.{v, u, max u v w, u} J
          (resolutionTerm.{u, v, w} J f (op ⦋0⦌)) (resolutionTerm.{u, v, w} J f' (op ⦋0⦌)) B B'
          (resolutionAugmentation J f (op ⦋0⦌)) (resolutionAugmentation J f' (op ⦋0⦌))
          (sq.resolution (op ⦋0⦌)) b (sq.resolution_augmentation (op ⦋0⦌)) := by
  refine hom_ext_of_derivationEquiv J f (op ⦋1⦌) fun U x => ?_
  refine (derivationEquiv_val_app J f _ _ _ U x).trans
    (Eq.trans ?_ (derivationEquiv_val_app J f _ _ _ U x).symm)
  change (naiveComparisonNegOne J f').val.app U ((squareCotangentTermMap sq (op ⦋1⦌)).val.app U
      (((cotangentSimplicialModule J f).universalDerivation (op ⦋1⦌)).d x)) =
    (Stacks.Sites.Conormal.conormalSheafMapOfSquare.{v, u, max u v w, u} J
      (resolutionTerm.{u, v, w} J f (op ⦋0⦌)) (resolutionTerm.{u, v, w} J f' (op ⦋0⦌)) B B'
      (resolutionAugmentation J f (op ⦋0⦌)) (resolutionAugmentation J f' (op ⦋0⦌))
      (sq.resolution (op ⦋0⦌)) b (sq.resolution_augmentation (op ⦋0⦌))).val.app U
        ((naiveComparisonNegOne J f).val.app U
          (((cotangentSimplicialModule J f).universalDerivation (op ⦋1⦌)).d x))
  rw [naiveComparisonNegOne_conormalClass,
    ← derivationEquiv_val_app J f (op ⦋1⦌) _ (squareCotangentTermMap sq (op ⦋1⦌)) U x,
    squareCotangentTermMap_d, naiveComparisonNegOne_conormalClass]
  refine Eq.trans ?_ (Stacks.Sites.Conormal.conormalSheafMapOfSquare_conormalClass.{v, u,
    max u v w, u} J A A' _ _ B B' _ _ _ _ _ b _ U _).symm
  exact congrArg _ (Subtype.ext (faceDifference_resolution sq U x).symm)

end CategoryTheory.Sheaf

end
