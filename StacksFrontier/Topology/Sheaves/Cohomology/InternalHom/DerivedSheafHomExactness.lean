module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.Exactness
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# The derived internal hom of a ringed space on distinguished triangles: the existential form

Let `(X, O_X)` be a ringed space.  For a distinguished triangle `T` of `D(O_X)` and an object `E`
of `D(O_X)`, both

`RSheafHom(T.obj₃, E) ⟶ RSheafHom(T.obj₂, E) ⟶ RSheafHom(T.obj₁, E)`

and

`RSheafHom(E, T.obj₁) ⟶ RSheafHom(E, T.obj₂) ⟶ RSheafHom(E, T.obj₃)`

extend by *some* connecting morphism to a distinguished triangle of `D(O_X)`.  This is weaker
than Stacks 08I0, which is proved as two `CategoryTheory.Functor.IsTriangulated` instances in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomTriangulated`; see the
implementation notes.

A topological space with a sheaf of commutative rings *is* a ringed site, namely the site of its
opens with the open-cover topology, so the ringed-site statement of Stacks 08JC applies verbatim.
The two declarations below read it off along `Stacks.SheafOfModules.ringedSite`, in the
vocabulary of `Stacks.SheafOfModules.StructureSheafModules`.

## Main results

* `Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_first`: exactness in the source,
  the contravariant variable.
* `Stacks.SheafOfModules.exists_distinguished_derivedSheafHom_second`: exactness in the target,
  the covariant variable.

## Implementation notes

Each variable is treated by its own descent of the cochain-level statement that the
internal Hom complex turns a termwise split short exact sequence of complexes into a termwise
split short exact sequence.  The descent is the K-injective model comparison
`AlgebraicGeometry.RingedSite.derivedSheafHomComparison`, which computes `RSheafHom(A, I)` as the
class of the internal Hom complex `SheafHom(A, I)` for an arbitrary source `A` and a K-injective
target `I`.  Because the condition falls on the target, the two variables are not symmetric: in
the contravariant variable the triangle varies in the source, where no condition is needed, while
in the covariant variable the triangle varies in the target and so has to be presented by a
termwise split short exact sequence of *K-injective* complexes.  That refined presentation is
`AlgebraicGeometry.RingedSite.exists_kInjective_degreewiseSplit_presentation`.

The statements are the weak "there is a connecting morphism making the image a distinguished
triangle" form.  They are **not** Stacks 08I0: in the sense of Stacks 014V, transforming
distinguished triangles into distinguished triangles asks that the image triangle *with third map
the image of the given third map composed with the commutation isomorphism* be distinguished,
whereas here the connecting morphism is merely asserted to exist and is identified with nothing.
Stacks 08I0 itself is `Stacks.SheafOfModules.isTriangulated_derivedSheafHom_flip` and
`Stacks.SheafOfModules.isTriangulated_derivedSheafHom` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomTriangulated`, two
`CategoryTheory.Functor.IsTriangulated` instances, which imply the statements below.

The contravariant statement is phrased through `CategoryTheory.Functor.flip`, which turns
`RSheafHom(-, -)` into a functor out of `D(O_X)ᵒᵖ` once the target is fixed; `D(O_X)ᵒᵖ` is
pretriangulated, but the conclusion concerns distinguished triangles of `D(O_X)` and not of its
opposite, so the two morphisms appear in the reversed order that contravariance dictates.

## References

* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- **Exactness in the source, existential form.**  On a ringed space, the derived internal hom
into a fixed object carries a distinguished triangle of `D(O_X)` to a distinguished triangle in
the weak sense that the two morphisms
`RSheafHom(T.obj₃, E) ⟶ RSheafHom(T.obj₂, E) ⟶ RSheafHom(T.obj₁, E)` induced by `T.mor₂` and
`T.mor₁` extend by *some* connecting morphism to a distinguished triangle.

The order of the two morphisms is reversed, which is the contravariance of the first variable.
The connecting morphism is only asserted to exist; Stacks 08I0, which fixes it, is
`Stacks.SheafOfModules.isTriangulated_derivedSheafHom_flip`. -/
theorem exists_distinguished_derivedSheafHom_first
    (E : DerivedCategory (StructureSheafModules Rc))
    (T : Triangle (DerivedCategory (StructureSheafModules Rc)))
    (hT : T ∈ distTriang (DerivedCategory (StructureSheafModules Rc))) :
    ∃ δ : ((derivedSheafHom Rc).flip.obj E).obj (op T.obj₁) ⟶
        (((derivedSheafHom Rc).flip.obj E).obj (op T.obj₃))⟦(1 : ℤ)⟧,
      Triangle.mk
        (((derivedSheafHom Rc).flip.obj E).map T.mor₂.op)
        (((derivedSheafHom Rc).flip.obj E).map T.mor₁.op)
        δ ∈ distTriang (DerivedCategory (StructureSheafModules Rc)) :=
  RingedSite.exists_distinguished_derivedSheafHom (ringedSite Rc) E T hT

/-- **Exactness in the target, existential form.**  On a ringed space, the derived internal hom
out of a fixed object carries a distinguished triangle of `D(O_X)` to a distinguished triangle in
the weak sense that the two morphisms
`RSheafHom(E, T.obj₁) ⟶ RSheafHom(E, T.obj₂) ⟶ RSheafHom(E, T.obj₃)` induced by `T.mor₁` and
`T.mor₂` extend by *some* connecting morphism to a distinguished triangle.  Stacks 08I0, which
fixes the connecting morphism, is `Stacks.SheafOfModules.isTriangulated_derivedSheafHom`. -/
theorem exists_distinguished_derivedSheafHom_second
    (E : DerivedCategory (StructureSheafModules Rc))
    (T : Triangle (DerivedCategory (StructureSheafModules Rc)))
    (hT : T ∈ distTriang (DerivedCategory (StructureSheafModules Rc))) :
    ∃ δ : ((derivedSheafHom Rc).obj (op E)).obj T.obj₃ ⟶
        (((derivedSheafHom Rc).obj (op E)).obj T.obj₁)⟦(1 : ℤ)⟧,
      Triangle.mk
        (((derivedSheafHom Rc).obj (op E)).map T.mor₁)
        (((derivedSheafHom Rc).obj (op E)).map T.mor₂)
        δ ∈ distTriang (DerivedCategory (StructureSheafModules Rc)) :=
  RingedSite.exists_distinguished_derivedSheafHom_second (ringedSite Rc) E T hT

end Stacks.SheafOfModules

end
