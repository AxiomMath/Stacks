module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSourceTriangulated
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomAdjunctionOnARingedSpace
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
import StacksCore.Tactic.StacksAttribute

/-!
# The derived internal hom of a ringed space is triangulated in each variable

Let `(X, O_X)` be a ringed space.  Stacks 08I0 says that the bifunctor `RSheafHom(-, -)` of
Stacks 08DH transforms distinguished triangles into distinguished triangles in both variables.
In the sense of Stacks 014V this asks, for each fixed object, that the functor of the other
variable be an exact functor of triangulated categories: it commutes with the shift, and the
image of a distinguished triangle, with third map the image of the triangle's third map composed
with the commutation isomorphism, is distinguished.  That is Mathlib's
`CategoryTheory.Functor.IsTriangulated`, relative to a `CategoryTheory.Functor.CommShift ℤ`.

## Main results

* `AlgebraicGeometry.RingedSite.isTriangulated_derivedSheafHom`: on a ringed site, `RSheafHom(B, -)`
  is a triangulated functor, as the right adjoint of `- ⊗^L_O B`.
* `Stacks.SheafOfModules.isTriangulated_derivedSheafHom_flip`: for every `L`,
  `RSheafHom(-, L) : D(O_X)ᵒᵖ ⥤ D(O_X)` is a triangulated functor, for the commutation datum
  `Stacks.SheafOfModules.commShift_derivedSheafHom_flip`; the shift of `D(O_X)ᵒᵖ` is the one of
  `CategoryTheory.Pretriangulated.Opposite`.
* `Stacks.SheafOfModules.isTriangulated_derivedSheafHom`: for every `K`,
  `RSheafHom(K, -) : D(O_X) ⥤ D(O_X)` is a triangulated functor, for the commutation datum
  `Stacks.SheafOfModules.commShift_derivedSheafHom`.

## Implementation notes

A topological space with a sheaf of commutative rings is a ringed site, the site of its opens,
and `Stacks.SheafOfModules.derivedSheafHom` is by definition the ringed-site derived internal
hom of `Stacks.SheafOfModules.ringedSite`.  The ringed-space statements carry no hypothesis
beyond `(X, O_X)`: the sheafification and tensor-product instances the ringed-site results ask
for hold on the site of opens and are supplied by
`Stacks.Topology.SheafTensorAdditiveOnOpens` and instance search.

The contravariant variable is `AlgebraicGeometry.RingedSite.derivedSheafHomFlipIsTriangulated`,
whose proof is the source's: the internal Hom complex carries a termwise split short exact
sequence of complexes in its first variable to a termwise split short exact sequence, with the
connecting morphism matched to the one the commutation datum produces.

The covariant variable is obtained from the adjunction `- ⊗^L_{O_X} K ⊣ RSheafHom(K, -)`
(`Stacks.SheafOfModules.derivedSheafHomTensorAdjunction`, Stacks 08DI): the commutation datum on
`RSheafHom(K, -)` is the one transported along it, the adjunction is compatible with the shifts,
the derived tensor product with a fixed factor is triangulated (Stacks 06YU), and the right
adjoint of a triangulated functor is triangulated,
`CategoryTheory.Adjunction.isTriangulated_rightAdjoint`.  This is a different route from the
source's termwise-split argument, which in the covariant variable would need the presentation of
a distinguished triangle by a termwise split sequence of K-injective complexes.

## References

* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
* [Stacks Project, Tag 014V](https://stacks.math.columbia.edu/tag/014V)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The derived internal Hom of a ringed site out of a fixed object is a triangulated
functor**, for the commutation datum `AlgebraicGeometry.RingedSite.commShift_derivedSheafHom`
transported along `AlgebraicGeometry.RingedSite.derivedTensorHomAdjunction`: it is the right
adjoint of the triangulated functor `- ⊗^L_O B`, compatibly with the shifts. -/
instance isTriangulated_derivedSheafHom
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).obj (op B)).IsTriangulated :=
  (derivedTensorHomAdjunction X B).isTriangulated_rightAdjoint

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- **The derived internal hom of a ringed space into a fixed object commutes with the shift**
of its dualized variable: `RSheafHom(K⟦-n⟧, L) ≅ RSheafHom(K, L)⟦n⟧`, coherently in `n`, the
shift of `D(O_X)ᵒᵖ` being the one of `CategoryTheory.Pretriangulated.Opposite`.  This is
`AlgebraicGeometry.RingedSite.derivedSheafHomFlipCommShift` on the ringed site of opens. -/
instance commShift_derivedSheafHom_flip (L : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedSheafHom Rc).flip.obj L).CommShift ℤ :=
  RingedSite.derivedSheafHomFlipCommShift (ringedSite Rc) L

/-- **Stacks 08I0, first variable.**  On a ringed space `(X, O_X)`, for every `L` in `D(O_X)` the
derived internal hom `RSheafHom(-, L) : D(O_X)ᵒᵖ ⥤ D(O_X)` is a triangulated functor: with the
commutation datum `commShift_derivedSheafHom_flip` it carries every distinguished triangle to a
distinguished triangle, the third map of the image being the image of the third map composed
with the commutation isomorphism (Stacks 014V).  A distinguished triangle of `D(O_X)ᵒᵖ` is the
opposite of a distinguished triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` of `D(O_X)`, and its image is the
triangle `RSheafHom(K₃, L) ⟶ RSheafHom(K₂, L) ⟶ RSheafHom(K₁, L) ⟶ RSheafHom(K₃, L)[1]`. -/
@[stacks 08I0 "first variable: `RSheafHom(-, L)` is a triangulated functor `D(O_X)ᵒᵖ ⥤ D(O_X)`"]
instance isTriangulated_derivedSheafHom_flip (L : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedSheafHom Rc).flip.obj L).IsTriangulated :=
  RingedSite.derivedSheafHomFlipIsTriangulated (ringedSite Rc) L

/-- **Stacks 08I0, second variable.**  On a ringed space `(X, O_X)`, for every `K` in `D(O_X)`
the derived internal hom `RSheafHom(K, -) : D(O_X) ⥤ D(O_X)` is a triangulated functor: with the
commutation datum `commShift_derivedSheafHom` it carries every distinguished triangle
`M₁ ⟶ M₂ ⟶ M₃ ⟶ M₁[1]` to the distinguished triangle
`RSheafHom(K, M₁) ⟶ RSheafHom(K, M₂) ⟶ RSheafHom(K, M₃) ⟶ RSheafHom(K, M₁)[1]` whose third map
is the image of the third map composed with the commutation isomorphism (Stacks 014V).

The proof is not the source's: `RSheafHom(K, -)` is right adjoint to the triangulated functor
`- ⊗^L_{O_X} K` (Stacks 08DI, 06YU), compatibly with the shifts, and the right adjoint of a
triangulated functor is triangulated. -/
@[stacks 08I0 "second variable: `RSheafHom(K, -)` is a triangulated functor `D(O_X) ⥤ D(O_X)`"]
instance isTriangulated_derivedSheafHom (K : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedSheafHom Rc).obj (op K)).IsTriangulated :=
  RingedSite.isTriangulated_derivedSheafHom (ringedSite Rc) K

end Stacks.SheafOfModules

end
