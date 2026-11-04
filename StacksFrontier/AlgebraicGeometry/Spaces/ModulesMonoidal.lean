module

public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Preadditive
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite

/-!
# The tensor product of `𝒪_F`-modules on an algebraic space

Let `F` be an algebraic space.  Its small étale ringed site carries a structure sheaf of
commutative rings, and `AlgebraicGeometry.Space.Modules` is the category of sheaves of modules
over that structure sheaf with its commutativity forgotten.  This file equips that category with
the tensor product of Stacks 01CA: the sheafification of the objectwise tensor product
`U ↦ G(U) ⊗_{𝒪_F(U)} G'(U)`, as a symmetric monoidal structure whose unit is `𝒪_F` itself.

The construction is `Stacks.SheafOfModules.monoidalCategory` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal`, applied to the structure sheaf of the
small étale site.  Nothing is restated and no new mathematics is proved; what this file does is
check that the construction *applies*, which is a question about universes and nothing else, and
record the two identifications that pin the resulting tensor product down.

## Main definitions

* `AlgebraicGeometry.Space.modulesMonoidalCategory`: **the tensor product of `𝒪_F`-modules.**
* `AlgebraicGeometry.Space.modulesBraidedCategory` and
  `AlgebraicGeometry.Space.modulesSymmetricCategory`: its braiding and the symmetry of that
  braiding.

## Main results

* `AlgebraicGeometry.Space.structureRingPresheaf_isSheaf`: the underlying presheaf of rings of
  the structure sheaf of the small étale site is a sheaf, in the spelling that the tensor product
  of Stacks 05NA is indexed by.
* `AlgebraicGeometry.Space.ringSheaf_eq_structureSheaf`: that spelling of the sheaf of rings is
  the sheaf of rings of `AlgebraicGeometry.Space.smallEtaleRingedSite`, so the monoidal structure
  is carried by `AlgebraicGeometry.Space.Modules` itself with no transport.
* `AlgebraicGeometry.Space.modulesTensorUnit_eq`: the tensor unit is `𝒪_F`, on the nose.
* `AlgebraicGeometry.Space.modulesTensorObjIso`: the tensor product of two `𝒪_F`-modules is the
  sheafification of their objectwise tensor product, which is what identifies it with the tensor
  product of Stacks 01CA rather than with some other bifunctor.
* `AlgebraicGeometry.Space.modulesMonoidalPreadditive`: the tensor product is biadditive.

## Implementation notes

The module universe is pinned to the universe of the schemes.  This is forced and is the whole
content of the file.  Mathlib's monoidal structure on presheaves of modules exists only when the
module sections and the coefficient rings share a universe, so the tensor product of
`𝒪_F`-modules can only live at the universe of `𝒪_F`, which is the universe `u` of the schemes;
the objects of the small étale site, by contrast, live in `Type (u + 1)`.  Sheafification of
`AddCommGrpCat.{u}`-valued presheaves on a site whose objects live in `Type (u + 1)` is not
available in general, and it is available here only because the small étale site is
`CategoryTheory.EssentiallySmall.{u}`
(`AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`), which is what
`AlgebraicGeometry.Space.SmallEtale.instHasSheafify` exploits.  Without that smallness there
would be no tensor product of `𝒪_F`-modules at all.

No `@[stacks 03M1]` attribute is claimed and no clause of Stacks 03M1 is proved here.  Clause (5)
of Stacks 03M1 asserts that a tensor product of quasi-coherent modules is quasi-coherent; this
file supplies the tensor product that that clause is about, and nothing else.  For the same
reason no `@[stacks 01CA]` attribute is claimed either: the tensor product being registered
against that tag is `Stacks.SheafOfModules.Tensor.sheafTensor`, and
`AlgebraicGeometry.Space.modulesTensorObjIso` is the identification with it.

The structure sheaf appears in two spellings, `AlgebraicGeometry.RingedSite.ringSheaf` of the
small étale ringed site and `Stacks.SheafOfModules.TensorSheafification.structureSheaf` of the
  underlying presheaf of commutative
rings.  They are equal by `rfl`, since both are the composition with
`CategoryTheory.forget₂ CommRingCat RingCat` and the sheaf conditions are propositions, which is
`AlgebraicGeometry.Space.ringSheaf_eq_structureSheaf`; the monoidal structure is therefore stated
directly for `AlgebraicGeometry.Space.Modules` and not for a second category.

The monoidal, braided and symmetric structures are `instance_reducible` definitions activated by
`attribute [local instance]`, not global instances, exactly as
`Stacks.SheafOfModules.monoidalCategory` is: a global monoidal instance on a category of sheaves
of modules is found by instance search in every statement about such sheaves, including the ones
whose intended tensor product is a different one.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The presheaf of rings underlying the structure sheaf of the small étale site of an algebraic
space is a sheaf.

This is the sheaf condition in the spelling
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf` that the tensor
product of sheaves of modules is indexed by; it is the sheaf condition already carried by
`AlgebraicGeometry.RingedSite.ringSheaf` of the small étale ringed site. -/
theorem structureRingPresheaf_isSheaf :
    Presheaf.IsSheaf (SmallEtale.topology B S hS F)
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf (structureSheaf B S hS F
        hF).obj) :=
  ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).property

/-- The two spellings of the sheaf of rings `𝒪_F` agree: forgetting the commutativity of the
structure sheaf of the small étale ringed site gives the sheaf of rings that the tensor product
of Stacks 05NA is indexed by.

Both are the composition of the structure sheaf with `CategoryTheory.forget₂ CommRingCat RingCat`
carrying a proof of the sheaf condition, and the sheaf condition is a proposition. -/
theorem ringSheaf_eq_structureSheaf :
    Stacks.SheafOfModules.TensorSheafification.structureSheaf (structureSheaf B S hS F hF).obj
        (structureRingPresheaf_isSheaf B S hS F hF) =
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) :=
  rfl

/-- **The tensor product of `𝒪_F`-modules on an algebraic space `F`.**  The symmetric monoidal
structure on `AlgebraicGeometry.Space.Modules` whose tensor product is the sheafification of the
objectwise tensor product and whose unit is `𝒪_F`.

This is `Stacks.SheafOfModules.monoidalCategory` for the structure sheaf of the small étale site.
The module universe is the universe of the schemes; see the implementation notes for why it
cannot be anything else. -/
@[instance_reducible]
noncomputable def modulesMonoidalCategory :
    MonoidalCategory (Modules.{u, u} B S hS F hF) :=
  Stacks.SheafOfModules.monoidalCategory (structureSheaf B S hS F hF).obj
    (structureRingPresheaf_isSheaf B S hS F hF)

attribute [local instance] modulesMonoidalCategory

/-- The unit of the tensor product of `𝒪_F`-modules is `𝒪_F`, not merely isomorphic to it: the
unit object is a parameter of the localization that defines the monoidal structure, and it is
chosen to be the structure sheaf viewed as a module over itself. -/
theorem modulesTensorUnit_eq :
    𝟙_ (Modules.{u, u} B S hS F hF) =
      SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
  rfl

/-- The tensor product of two `𝒪_F`-modules is the sheafification of their objectwise tensor
product, the tensor product sheaf of Stacks 01CA.

The monoidal structure is produced by localizing the monoidal structure of presheaves of modules
along sheafification, so its associators and unitors are not given by formulas; this isomorphism
is what pins the tensor product itself down. -/
noncomputable def modulesTensorObjIso (G G' : Modules.{u, u} B S hS F hF) :
    G ⊗ G' ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS F hF)).obj G).obj G' :=
  Stacks.SheafOfModules.tensorObjIso (structureSheaf B S hS F hF).obj
    (structureRingPresheaf_isSheaf B S hS F hF) G G'

/-- The braiding of the tensor product of `𝒪_F`-modules, transported from the braiding of
presheaves of modules. -/
@[instance_reducible]
noncomputable def modulesBraidedCategory :
    BraidedCategory (Modules.{u, u} B S hS F hF) :=
  Stacks.SheafOfModules.braidedCategory (structureSheaf B S hS F hF).obj
    (structureRingPresheaf_isSheaf B S hS F hF)

attribute [local instance] modulesBraidedCategory

/-- The tensor product of `𝒪_F`-modules is symmetric. -/
@[instance_reducible]
noncomputable def modulesSymmetricCategory :
    SymmetricCategory (Modules.{u, u} B S hS F hF) :=
  Stacks.SheafOfModules.symmetricCategory (structureSheaf B S hS F hF).obj
    (structureRingPresheaf_isSheaf B S hS F hF)

/-- The tensor product of `𝒪_F`-modules is biadditive.  This is the distributive law that any
argument assembling a presentation of a tensor product out of presentations of its factors
consumes. -/
theorem modulesMonoidalPreadditive :
    MonoidalPreadditive (Modules.{u, u} B S hS F hF) :=
  Stacks.SheafOfModules.monoidalPreadditive (structureSheaf B S hS F hF).obj
    (structureRingPresheaf_isSheaf B S hS F hF)

end AlgebraicGeometry.Space

end
