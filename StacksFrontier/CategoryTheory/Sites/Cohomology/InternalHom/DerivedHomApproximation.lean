module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPseudoCoherent

/-!
# The derived internal Hom out of an approximation

Let `(C, O)` be a ringed site, let `α : P ⟶ M` be a morphism of `D(O)` which is an isomorphism
on cohomology in every degree `> m` and surjective on cohomology in degree `m`, and let `L` be
an object of `D(O)` with no cohomology below `b`. Then

`RSheafHom(M, L) ⟶ RSheafHom(P, L)`

is an isomorphism on cohomology in every degree `n < b - m`. The cone `Z` of `α` lies in
`D^{≤ m - 1}`, so `RSheafHom(Z, L)` lies in `D^{≥ b - m + 1}` (Stacks 0A8Z), and the triangle
obtained by applying `RSheafHom(-, L)` to that of `α` (Stacks 08JC) gives the statement.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_homologyMap_derivedSheafHom_map_of_approximation`: the
  range comparison above.

## References

* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The derived internal Hom out of an approximation.** If `α : P ⟶ M` is an isomorphism on
cohomology in degrees `> m` and surjective on cohomology in degree `m`, and the cohomology of `L`
vanishes below `b`, then `RSheafHom(M, L) ⟶ RSheafHom(P, L)` is an isomorphism on cohomology in
every degree `n < b - m`. -/
theorem isIso_homologyMap_derivedSheafHom_map_of_approximation
    {P M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (α : P ⟶ M) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i).map α))
    (hepi : Epi ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).map α))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (b n : ℤ) (hL : L.IsGE b) (hn : n < b - m) :
    IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).map
      (((derivedSheafHomBifunctor X).map α.op).app L)) := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle α
  have hZ : Z.IsLE (m - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation _ hT m hiso hepi
  have hHL : (((derivedSheafHomBifunctor X).obj (op Z)).obj L).IsGE (b - (m - 1)) :=
    isGE_derivedSheafHom X Z L (m - 1) b hZ hL
  obtain ⟨δ, hT₂⟩ := exists_distinguished_derivedSheafHom X L (Triangle.mk α g h) hT
  exact DerivedCategory.isIso_homologyMap_mor₂_of_isGE₁ _ hT₂ n (b - (m - 1)) hHL (by omega)

end AlgebraicGeometry.RingedSite

end
