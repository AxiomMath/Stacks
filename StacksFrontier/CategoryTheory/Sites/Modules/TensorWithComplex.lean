module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SectionwiseTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SectionwiseComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SheafifiedTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.TensorHomAdjunction
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SectionwiseTensor
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SectionwiseComplex
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.SheafifiedTensor
import all StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex.TensorHomAdjunction

/-!
# Tensoring a differential graded module with a complex of modules on a ringed site

Let `(C, O)` be a ringed site and let `K` be a complex of `O`-modules, viewed as an object of
the differential graded category `Comp^dg(O)` of complexes of `O`-modules. Let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. This file
constructs the differential graded functor `- ⊗_E K : Mod^dg_(E, d) ⥤ Comp^dg(O)`, shows that it
sends the regular module `E` to `K`, and shows that it commutes with direct sums.

For a differential graded `E`-module `M` and an object `U` of `C`, the sections `K(U)` form a
left differential graded `E`-module and a right `O(U)`-module, and these actions commute, so
`K(U)` is a bimodule. The tensor product `M ⊗_E K(U)` is therefore a complex of `O(U)`-modules;
it is functorial in `U`, and sheafifying gives the complex `M ⊗_E K` of `O`-modules.

## Main definitions

* `AlgebraicGeometry.RingedSite.BalancedDegreeMap`: degreewise, sectionwise bilinear maps
  balanced over the endomorphism differential graded algebra.
* `AlgebraicGeometry.RingedSite.TensorWithComplexData`: the tensor differential graded functor
  together with its sectionwise presheaf tensor complex, its pure tensors, its sheafification
  and its tensor-Hom adjunction.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDG`: the construction of this data.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexDG_regular`: the functor sends the regular
  module to `K`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDG_preservesCoproducts`: the functor commutes
  with direct sums.

## Implementation notes

The algebra `E` is the endomorphism algebra supplied by the representable differential graded
functor `Hom(K, -)` of Tag 09LE. In each degree, on each object of the site, the sectionwise
tensor complex is characterised by the universal property of balanced pure tensors; its
differential obeys the signed Leibniz rule and its restriction maps preserve pure tensors. Its
sheafification is characterised by the universal property for maps to complexes of sheaves. The
right adjoint of the resulting functor is the representable functor `Hom(K, -)`, and preservation
of direct sums is deduced from that adjunction. The regular module is represented by
`Hom(K, K)`.

Everything is formed over a base ring `R`, as in Stacks 0CS6, which fixes a ring `R` and a sheaf
of commutative `R`-algebras on `O`: the differential graded category of complexes is
`CochainComplex.dgCategoryLinear` over `R`, so `E` is a differential graded `R`-algebra and the
tensor functor is `R`-linear. Two data carry that. The first is a `CategoryTheory.Linear`
structure on the sheaves of `O`-modules, which is what makes the Hom modules `R`-modules. The
second is `AlgebraicGeometry.RingedSite.ScalarSections`, which says that a scalar acts on
sections by multiplication by a section of `O`; without it the `R`-linearity of the tensor
functor is not provable, because the balancing relation of the tensor product only moves an
operator that is the action of an element of `E`, and for an abstract linear structure `r • 𝟙`
is not one. Taking `R = ℤ` recovers the `ℤ`-linear reading verbatim and definitionally, with
`AlgebraicGeometry.RingedSite.scalarSectionsInt` supplying the second datum.

Those two data are the source's hypothesis exactly, and not a weaker one. No compatibility
between the sections attached to a scalar is imposed above, but it is automatic: the family is a
global section of `O`, and the assignment is a ring map `R ⟶ Γ(C, O)`, which is
`AlgebraicGeometry.RingedSite.ScalarSections.toGlobalSections` of
`StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexBaseRing`. The sheaf of commutative
`R`-algebras it is, is `AlgebraicGeometry.RingedSite.ScalarSections.algebraSheaf`, and
`AlgebraicGeometry.RingedSite.ScalarSections.smul_eq_globalSections_smul` says the linear
structure is that map's restriction of scalars. So `Γ(C, O)` is the universal base ring here,
and `AlgebraicGeometry.RingedSite.scalarSectionsGlobalSectionRing` records that it satisfies the
hypothesis.

The input complex has section universe `t`, independent of the site and of the structure ring.
It is first pushed along the fully faithful sectionwise `ULift` embedding into section universe
`max u v w t s`, where `s` is an independent size parameter for the carriers of the differential
graded modules. Both the tensor products and the sheafification take values in that ambient
universe, and the representable functor and the identification of the regular module use the
lifted complex. In particular no shrinking of arbitrary differential graded modules is asserted.

## References

* [The Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
-/
