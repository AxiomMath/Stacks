module

public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentTensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FibredTensorProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.MixedTensorQuasicoherent

/-!
# The monoidal structure on the quasi-coherent modules of an algebraic stack

The category `QCoh(𝒪_𝒳)` of quasi-coherent modules on the fppf site of a category fibred in
groupoids over the big fppf category of schemes over `S` is a monoidal category: the tensor
product of two quasi-coherent modules is again quasi-coherent, the structure sheaf is
quasi-coherent, and the associator and the unitors of the ambient category of sheaves of
modules restrict to the full subcategory they cut out.

Everything is at module universe equal to the universe of the coefficient rings, which is the
only universe at which the ambient tensor product of sheaves of modules exists; the objects of
the fibred category are free to live anywhere.

## Main definitions

* `AlgebraicGeometry.FibredSite.tensorSheafMixedIsoTensorSheaf` identifies the mixed-universe
  tensor product of two sheaves of modules whose sections already lie in the universe of the
  coefficient rings with the equi-universe one.
* `AlgebraicGeometry.FibredSite.quasicoherentTensorObj` is the tensor product of two
  quasi-coherent modules, as an object of `QCoh(𝒪_𝒳)`, and
  `AlgebraicGeometry.FibredSite.quasicoherentTensorUnit` is the unit object.
* `AlgebraicGeometry.FibredSite.quasicoherentTensorBifunctor` is the tensor product as a
  bifunctor on `QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.FibredSite.monoidalCategoryQuasicoherentModules` is the monoidal structure
  on `QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.FibredSite.quasicoherentTensorObjIsoTensorSheafMixed` identifies that
  tensor product with `AlgebraicGeometry.FibredSite.tensorSheafMixed`, the object whose
  universal property is Stacks 06WN(2).

## Main results

* `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_tensorSheaf` and
  `AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_tensorObj`: **the tensor product of two
  quasi-coherent sheaves of modules on an associated site of the fibred category is
  quasi-coherent**, both for the tensor product formed as a sheafification and for the monoidal
  product of `AlgebraicGeometry.FibredSite.monoidalCategory`.
* `AlgebraicGeometry.FibredSite.tensorLE_isQuasicoherentOnSite`,
  `AlgebraicGeometry.FibredSite.containsUnit_isQuasicoherentOnSite` and
  `AlgebraicGeometry.FibredSite.isMonoidal_isQuasicoherentOnSite`: quasi-coherence on an
  associated site of the fibred category is a monoidal property of objects.

## Implementation notes

**Why the generic route is closed.**  The library already carries the generic statement that
quasi-coherence is a monoidal property of objects on a ringed site,
`Stacks.SheafOfModules.isMonoidal_isQuasicoherentOnSite`, built from
`Stacks.SheafOfModules.isQuasicoherentOnSite_tensorSheaf`.  Both are stated in the regime in
which the universe of the coefficient rings dominates the universe of the objects of the site,
and both conditions of that regime are refuted at the fibred fppf site of Stacks 06WG by the
repository's own negative results:

* `AlgebraicGeometry.FibredSite.not_univLE_associatedSite` — the objects of that site lie in
  `Type (u + 1)` while its structure sheaf lies in `Type u`, so the size hypothesis of the
  generic tensor clause reads `UnivLE.{u + 1, u}`, which is false;
* `AlgebraicGeometry.FibredSite.not_hasBinaryProducts_twoLabel` — a category fibred in
  groupoids over the big fppf category need not have binary products, and the generic clause
  uses them to refine two coverings of the final object.

So the generic clause cannot be instantiated here, and
`Stacks.SheafOfModules.TensorProduct.quasicoherentOnSiteTensorBifunctor`, the bifunctor it
yields, is by its own docstring not the one the source asserts.

**The route taken instead.**  The input is
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_tensorSheafMixed`: the mixed-universe
tensor product, whose sections are those of the coefficient rings joined with those of the two
factors, is quasi-coherent, with no size hypothesis and no binary products, because its proof
raises the universe of the coefficient rings instead of lowering that of the sections.  Taking
both factors with sections in the universe of the coefficient rings, that tensor product
differs from the equi-universe one only by a universe lift of the sections that lifts nothing:
by `PresheafOfModules.MixedTensor.tensorObj_eq` the two objectwise tensor products agree on the
nose, and `PresheafOfModules.uliftSectionsSelfIso` undoes the lift, so one application of the
sheafification functor to that isomorphism carries quasi-coherence across.  From there
`Stacks.SheafOfModules.tensorObjIso` moves it onto the monoidal product of
`AlgebraicGeometry.FibredSite.monoidalCategory`, and the two clauses of
`CategoryTheory.ObjectProperty.IsMonoidal` are available.  Full coherence is then inherited
from the ambient category through
`CategoryTheory.ObjectProperty.fullMonoidalSubcategory`; no associator or unitor is
constructed here.

The unit clause needs nothing from this circle of ideas:
`SheafOfModules.isQuasicoherentOnSite_unit` holds over any sheaf of rings on any site, at the
module universe of the rings, and the unit of `AlgebraicGeometry.FibredSite.monoidalCategory`
is that sheaf of modules on the nose, by `Stacks.SheafOfModules.tensorUnit_eq`.

The monoidal structure on the ambient category of sheaves of modules is a definition rather
than an instance, so it is made a local instance only in the section where the monoidal
statements live; making it one earlier sends instance synthesis through it while elaborating
the sheafification comparisons, which is expensive and unnecessary there.

## References

* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06WV](https://stacks.math.columbia.edu/tag/06WV)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) [EssentiallySmall.{u} 𝒳]

/-- The mixed-universe tensor product of two sheaves of modules on an associated site of the
fibred category whose sections already lie in the universe of the coefficient rings is the
equi-universe tensor product.  Both are sheafifications of the same objectwise tensor product —
`PresheafOfModules.MixedTensor.tensorObj_eq` — and differ only by a universe lift of the
sections that lifts nothing, which `PresheafOfModules.uliftSectionsSelfIso` undoes.  No
sheafification is computed. -/
def tensorSheafMixedIsoTensorSheaf (τ : SiteKind)
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) :
    letI := hasWeakSheafify_associatedTopology B S hS p τ
    letI := wEqualsLocallyBijective_associatedTopology B S hS p τ
    tensorSheafMixed B S hS p hp τ F G ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf B S hS p hp τ)).obj F).obj G :=
  have := isLocallyInjective_structureComparison B S hS p hp τ
  have := isLocallySurjective_structureComparison B S hS p hp τ
  have := hasWeakSheafify_associatedTopology B S hS p τ
  have := wEqualsLocallyBijective_associatedTopology B S hS p τ
  (PresheafOfModules.sheafification (structureComparison B S hS p hp τ)).mapIso
    (PresheafOfModules.uliftSectionsSelfIso _)

/-- **The tensor product of two quasi-coherent sheaves of modules on an associated site of the
fibred category is quasi-coherent.**  The tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor`, the sheafification of the objectwise tensor
product, at the module universe of the coefficient rings.

This is the statement that the generic tensor clause of a ringed site,
`Stacks.SheafOfModules.isQuasicoherentOnSite_tensorSheaf`, cannot supply at this site; see the
implementation notes.  It is obtained instead from the mixed-universe statement
`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_tensorSheafMixed`. -/
theorem isQuasicoherentOnSite_tensorSheaf (τ : SiteKind)
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ))
    [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite] :
    letI := hasWeakSheafify_associatedTopology B S hS p τ
    letI := wEqualsLocallyBijective_associatedTopology B S hS p τ
    (((Stacks.SheafOfModules.Tensor.sheafTensor (structureSheaf B S hS p hp τ)).obj F).obj
      G).IsQuasicoherentOnSite :=
  have h := isQuasicoherentOnSite_tensorSheafMixed B S hS p hp τ F G
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (tensorSheafMixedIsoTensorSheaf B S hS p hp τ F G) h

section Monoidal

attribute [local instance] monoidalCategory

/-- **Quasi-coherence is stable under the monoidal product of sheaves of modules on an
associated site of the fibred category.**  The monoidal structure is
`AlgebraicGeometry.FibredSite.monoidalCategory`, whose product is identified with the
sheafification of the objectwise tensor product by `Stacks.SheafOfModules.tensorObjIso`. -/
theorem isQuasicoherentOnSite_tensorObj (τ : SiteKind)
    (F G : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ))
    [F.IsQuasicoherentOnSite] [G.IsQuasicoherentOnSite] :
    (F ⊗ G).IsQuasicoherentOnSite :=
  have h := isQuasicoherentOnSite_tensorSheaf B S hS p hp τ F G
  have := hasWeakSheafify_associatedTopology B S hS p τ
  have := wEqualsLocallyBijective_associatedTopology B S hS p τ
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (Stacks.SheafOfModules.tensorObjIso (structureSheaf B S hS p hp τ).obj
      (structureRingPresheaf_isSheaf B S hS p hp τ) F G).symm h

/-- **Quasi-coherence on an associated site of the fibred category is stable under tensor
product**, in the packaging `CategoryTheory.ObjectProperty.TensorLE` asks for. -/
instance tensorLE_isQuasicoherentOnSite (τ : SiteKind) :
    ObjectProperty.TensorLE
      (SheafOfModules.isQuasicoherentOnSite.{v, u, u, u} (ringStructureSheafCore B S hS p hp τ))
      (SheafOfModules.isQuasicoherentOnSite.{v, u, u, u} (ringStructureSheafCore B S hS p hp τ))
      (SheafOfModules.isQuasicoherentOnSite.{v, u, u, u}
        (ringStructureSheafCore B S hS p hp τ)) where
  prop_tensor F G hF hG :=
    have := hF
    have := hG
    isQuasicoherentOnSite_tensorObj B S hS p hp τ F G

/-- **Quasi-coherence on an associated site of the fibred category contains the tensor unit.**
The unit of `AlgebraicGeometry.FibredSite.monoidalCategory` is the structure sheaf viewed as a
module over itself, which is quasi-coherent on any site over any sheaf of rings. -/
instance containsUnit_isQuasicoherentOnSite (τ : SiteKind) :
    ObjectProperty.ContainsUnit
      (SheafOfModules.isQuasicoherentOnSite.{v, u, u, u}
        (ringStructureSheafCore B S hS p hp τ)) where
  prop_unit := SheafOfModules.isQuasicoherentOnSite_unit _

/-- **Quasi-coherent modules on an associated site of the fibred category form a monoidal
subcategory.**  Together with `CategoryTheory.ObjectProperty.fullMonoidalSubcategory` this is
what provides the tensor product of quasi-coherent modules with its full coherence. -/
instance isMonoidal_isQuasicoherentOnSite (τ : SiteKind) :
    (SheafOfModules.isQuasicoherentOnSite.{v, u, u, u}
      (ringStructureSheafCore B S hS p hp τ)).IsMonoidal where

/-- **The monoidal structure on `QCoh(𝒪_𝒳)`.**  The tensor product of two quasi-coherent
modules on the fppf site of the fibred category is their tensor product as sheaves of modules,
which is again quasi-coherent, and the associator and the unitors are those of the ambient
category of sheaves of modules. -/
@[instance_reducible]
def monoidalCategoryQuasicoherentModules :
    MonoidalCategory (quasicoherentModules.{u, v, u, u} B S hS p hp) :=
  ObjectProperty.fullMonoidalSubcategory _

/-- The tensor product of two quasi-coherent modules on the fppf site of the fibred category, as
an object of `QCoh(𝒪_𝒳)`: the tensor product of the underlying sheaves of modules, together
with the proof that it is quasi-coherent. -/
def quasicoherentTensorObj (F G : quasicoherentModules.{u, v, u, u} B S hS p hp) :
    quasicoherentModules.{u, v, u, u} B S hS p hp :=
  ⟨F.obj ⊗ G.obj,
    have := F.property
    have := G.property
    isQuasicoherentOnSite_tensorObj B S hS p hp .fppf F.obj G.obj⟩

/-- The underlying sheaf of modules of the tensor product of two quasi-coherent modules is the
tensor product of their underlying sheaves of modules. -/
theorem quasicoherentTensorObj_obj (F G : quasicoherentModules.{u, v, u, u} B S hS p hp) :
    (quasicoherentTensorObj B S hS p hp F G).obj = F.obj ⊗ G.obj :=
  rfl

/-- The unit object of `QCoh(𝒪_𝒳)`: the structure sheaf of the fppf site of the fibred
category, viewed as a module over itself, which is quasi-coherent. -/
def quasicoherentTensorUnit : quasicoherentModules.{u, v, u, u} B S hS p hp :=
  ⟨SheafOfModules.unit (ringStructureSheafCore B S hS p hp .fppf),
    SheafOfModules.isQuasicoherentOnSite_unit _⟩

/-- The tensor product of `QCoh(𝒪_𝒳)` as a bifunctor, functorial in both arguments: the curried
monoidal product of `AlgebraicGeometry.FibredSite.monoidalCategoryQuasicoherentModules`. -/
def quasicoherentTensorBifunctor :
    quasicoherentModules.{u, v, u, u} B S hS p hp ⥤
      quasicoherentModules.{u, v, u, u} B S hS p hp ⥤
        quasicoherentModules.{u, v, u, u} B S hS p hp :=
  letI := monoidalCategoryQuasicoherentModules B S hS p hp
  curriedTensor _

/-- The tensor product of two quasi-coherent modules is
`AlgebraicGeometry.FibredSite.tensorSheafMixed`, the object whose universal property is
Stacks 06WN(2).  This is what carries that universal property over to the monoidal product of
`QCoh(𝒪_𝒳)`. -/
def quasicoherentTensorObjIsoTensorSheafMixed
    (F G : quasicoherentModules.{u, v, u, u} B S hS p hp) :
    (quasicoherentTensorObj B S hS p hp F G).obj ≅
      tensorSheafMixed B S hS p hp .fppf F.obj G.obj :=
  have := hasWeakSheafify_associatedTopology B S hS p (.fppf : SiteKind)
  have := wEqualsLocallyBijective_associatedTopology B S hS p (.fppf : SiteKind)
  Stacks.SheafOfModules.tensorObjIso (structureSheaf B S hS p hp .fppf).obj
      (structureRingPresheaf_isSheaf B S hS p hp .fppf) F.obj G.obj ≪≫
    (tensorSheafMixedIsoTensorSheaf B S hS p hp .fppf F.obj G.obj).symm

end Monoidal

end AlgebraicGeometry.FibredSite

end
