module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom

/-!
# The tensor–internal-hom bijection on a ringed space as an adjunction

Let `(X, O_X)` be a ringed space and let `K` be an object of `D(O_X)`. Stacks 08DI is the
bijection

`Hom_{D(O_X)}(M, RSheafHom(K, N)) = Hom_{D(O_X)}(M ⊗^L_{O_X} K, N)`,

which this development has as the family of additive equivalences
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv`. That family, together with its naturality in
the source and in the target, is an adjunction

`− ⊗^L_{O_X} K ⊣ RSheafHom(K, −)`

of endofunctors of `D(O_X)`, and this file records it. A topological space with a sheaf of
commutative rings *is* a ringed site, so the declarations below read off the ringed-site
adjunction `AlgebraicGeometry.RingedSite.derivedTensorHomAdjunction` along
`Stacks.SheafOfModules.ringedSite`, in the vocabulary of
`Stacks.SheafOfModules.StructureSheafModules`, with no comparison layer between the two settings.

## Main definitions

* `Stacks.SheafOfModules.derivedTensorRight`: `− ⊗^L_{O_X} K`.
* `Stacks.SheafOfModules.derivedSheafHomTensorAdjunction`: the adjunction
  `− ⊗^L_{O_X} K ⊣ RSheafHom(K, −)`.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomTensorAdjunction_homEquiv_symm_apply`: the adjunction's
  bijection is `Stacks.SheafOfModules.derivedSheafHomTensorEquiv`, the one Stacks 08DI is
  registered on, with no further identification. So nothing here replaces that registration: the
  adjunction is a *spelling* of it.
* `Stacks.SheafOfModules.commShift_derivedSheafHom`: **`RSheafHom(K, −)` commutes with the
  shift**, by transport along the adjunction.

## Implementation notes

The reason to want the adjunction rather than the bijection is recorded in the implementation
notes of `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomExactness`: the
derived internal hom of a ringed space carried no `CategoryTheory.Functor.CommShift` in either
variable, because its cochain model is the internal hom complex into a chosen K-injective
*resolution* of the target — not known to commute with the shift — and because the one other
route, `CategoryTheory.Adjunction.rightAdjointCommShift`, needs an adjunction and Stacks 08DI
was present only as additive equivalences. `commShift_derivedSheafHom` closes that gap for the
covariant variable. The contravariant variable `RSheafHom(−, N)` is untouched: it has no left
adjoint here.

No declaration below is tagged. Stacks 08DI is an *equation* tag — it asserts the bijection and
nothing else — and it is already registered, on
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv`; the functoriality in the three objects is
the assertion of Stacks 08J9 and is registered at the site level.

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

variable (K : DerivedCategory (StructureSheafModules Rc))

/-- `− ⊗^L_{O_X} K`, the derived tensor product of modules on a ringed space with a fixed right
factor `K`. -/
abbrev derivedTensorRight :
    DerivedCategory (StructureSheafModules Rc) ⥤ DerivedCategory (StructureSheafModules Rc) :=
  (derivedTensor Rc).flip.obj K

/-- **Stacks 08DI as an adjunction.** On a ringed space, tensoring with a fixed object `K` of
`D(O_X)` is left adjoint to the derived internal hom out of `K`,

`− ⊗^L_{O_X} K ⊣ RSheafHom(K, −)`.

The bijection of morphism groups is the one of Stacks 08DI and the two naturality clauses are its
naturality in the source and in the target. -/
def derivedSheafHomTensorAdjunction :
    derivedTensorRight Rc K ⊣ (derivedSheafHom Rc).obj (op K) :=
  RingedSite.derivedTensorHomAdjunction (ringedSite Rc) K

/-- **The adjunction's bijection is the bijection of Stacks 08DI.** Its inverse sends
`h : M ⟶ RSheafHom(K, N)` to the morphism `M ⊗^L_{O_X} K ⟶ N` that
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv` matches with `h`, with no intervening
identification. -/
theorem derivedSheafHomTensorAdjunction_homEquiv_symm_apply
    (M N : DerivedCategory (StructureSheafModules Rc))
    (h : M ⟶ ((derivedSheafHom Rc).obj (op K)).obj N) :
    ((derivedSheafHomTensorAdjunction Rc K).homEquiv M N).symm h =
      derivedSheafHomTensorEquiv Rc M K N h :=
  RingedSite.derivedTensorHomAdjunction_homEquiv_symm_apply (ringedSite Rc) K M N h

/-- **The derived internal hom of a ringed space out of a fixed object commutes with the
shift.** This is `AlgebraicGeometry.RingedSite.commShift_derivedSheafHom`, the transport of the
commutation of `− ⊗^L_{O_X} K` with the shift along `derivedSheafHomTensorAdjunction`. -/
instance commShift_derivedSheafHom :
    ((derivedSheafHom Rc).obj (op K)).CommShift ℤ :=
  RingedSite.commShift_derivedSheafHom (ringedSite Rc) K

end Stacks.SheafOfModules

end
