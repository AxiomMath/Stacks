module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Adjunction
public import StacksFrontier.Topology.Sheaves.Modules.Coherent

/-!
# Coherent reflexive modules, as a single full subcategory

The category `𝒞` of coherent reflexive `𝒪_X`-modules of [Stacks, Tag
0EBH](https://stacks.math.columbia.edu/tag/0EBH) can be presented in two ways: as the reflexive
objects inside the category of coherent modules, which is `CoherentReflexiveModules` and is what
the reflexive-hull adjunction produces, or as the full subcategory of *all* `𝒪_X`-modules cut
out by the conjunction "coherent and reflexive", which is the shape in which [Stacks, Tag
0EBJ](https://stacks.math.columbia.edu/tag/0EBJ) quantifies over it.  This file identifies the
two.

It also bridges the library's **two** coherence predicates.  Tag 01BV is realized twice, by
field-identical classes under different names: `SheafOfModules.IsCoherent` of
Stacks Tag 01BW, which is what `add_to_stacks 01BV` points at, and
`Stacks.SheafOfModules.IsCoherent` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`, which carries the `@[stacks 01BV]`
attribute and is the one the reflexive-hull adjunction is stated over.  Nothing converted
between them before this file, so a statement about one was not usable where the other was
expected even though the two are interchangeable.

## Main definitions

* `ReflexiveCoherentModules X`: the full subcategory of `X.Modules` on the modules that are
  coherent and reflexive.

## Main results

* `Stacks.SheafOfModules.isCoherent_iff_sheafOfModules_isCoherent`: the two coherence predicates
  agree, with the two directions `IsCoherent.sheafOfModules` and
  `isCoherent_of_sheafOfModules`.
* `Stacks.SheafOfModules.coherentModulesEquiv`: consequently the two categories `Coh(𝒪_X)` that
  the library carries are isomorphic.
* `coherentReflexiveModulesEquiv`: the nested and the flattened presentations of `𝒞` are
  equivalent.

## Implementation notes

The equivalence is an isomorphism of categories on the nose: an object of either side is a
module together with proofs, morphisms on both sides are just morphisms of `X.Modules`, and the
round trips are definitionally the identity because the data carried is propositional.  That is
why both `unitIso` and `counitIso` are `Iso.refl`.

The coherence bridge is deliberately **not** stated as a pair of instances: in both directions
at once that is an instance loop.  Use the named directions, or rewrite with the `iff`.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} (M : SheafOfModules.{u} R)

/-- A coherent sheaf of modules in the sense of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean` is coherent in the sense of
Stacks Tag 01BW.  The two classes have the same two fields. -/
public theorem IsCoherent.sheafOfModules (h : IsCoherent M) : _root_.SheafOfModules.IsCoherent M :=
  ⟨h.isFiniteType, h.kernel_isFiniteType⟩

/-- The converse direction of `IsCoherent.sheafOfModules`. -/
public theorem isCoherent_of_sheafOfModules (h : _root_.SheafOfModules.IsCoherent M) :
    IsCoherent M :=
  ⟨h.isFiniteType, h.kernel_isFiniteType⟩

/-- **The library's two realizations of Tag 01BV agree.**  Both classes say that the sheaf is of
finite type and that the kernel of the associated map of every finite family of sections over
every open is of finite type. -/
public theorem isCoherent_iff_sheafOfModules_isCoherent :
    IsCoherent M ↔ _root_.SheafOfModules.IsCoherent M :=
  ⟨IsCoherent.sheafOfModules M, isCoherent_of_sheafOfModules M⟩

variable {M} (R)

/-- From `Coh(𝒪_X)` as cut out by `Stacks.SheafOfModules.IsCoherent` to `Coh(𝒪_X)` as cut out by
`SheafOfModules.IsCoherent`. -/
public noncomputable def coherentModulesToAlgebraicGeometry :
    CoherentModules R ⥤ _root_.AlgebraicGeometry.SheafOfModules.CoherentModules R where
  obj N := ⟨N.obj, IsCoherent.sheafOfModules _ N.property⟩
  map f := ⟨f.hom⟩

/-- The inverse of `coherentModulesToAlgebraicGeometry`. -/
public noncomputable def coherentModulesOfAlgebraicGeometry :
    _root_.AlgebraicGeometry.SheafOfModules.CoherentModules R ⥤ CoherentModules R where
  obj N := ⟨N.obj, isCoherent_of_sheafOfModules _ N.property⟩
  map f := ⟨f.hom⟩

/-- **The library's two categories `Coh(𝒪_X)` agree.**  `Stacks.SheafOfModules.CoherentModules`
is cut out by the `@[stacks 01BV]`-tagged class and is what the reflexive-hull adjunction is
stated over; `AlgebraicGeometry.SheafOfModules.CoherentModules` is cut out by the class that
`add_to_stacks 01BV` points at.  They are isomorphic on the nose. -/
public noncomputable def coherentModulesEquiv :
    CoherentModules R ≌ _root_.AlgebraicGeometry.SheafOfModules.CoherentModules R where
  functor := coherentModulesToAlgebraicGeometry R
  inverse := coherentModulesOfAlgebraicGeometry R
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Stacks.SheafOfModules

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- The full subcategory of `X.Modules` on the modules that are coherent and reflexive.  This is
the category `𝒞` of Tags 0EBH and 0EBJ, presented as a single full subcategory of all modules
rather than as a subcategory of the coherent ones. -/
public abbrev ReflexiveCoherentModules (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (fun F : X.Modules => _root_.SheafOfModules.IsCoherent F ∧ IsReflexive F)

/-- From the nested presentation of `𝒞` to the flattened one. -/
public noncomputable def toReflexiveCoherentModules (X : Scheme.{u}) :
    CoherentReflexiveModules X ⥤ ReflexiveCoherentModules X where
  obj F := ⟨F.obj.obj, ⟨_root_.Stacks.SheafOfModules.IsCoherent.sheafOfModules _
    F.obj.property, F.property⟩⟩
  map f := ⟨f.hom.hom⟩

/-- From the flattened presentation of `𝒞` to the nested one. -/
public noncomputable def ofReflexiveCoherentModules (X : Scheme.{u}) :
    ReflexiveCoherentModules X ⥤ CoherentReflexiveModules X where
  obj F := ⟨⟨F.obj, _root_.Stacks.SheafOfModules.isCoherent_of_sheafOfModules _
    F.property.1⟩, F.property.2⟩
  map f := ⟨⟨f.hom⟩⟩

/-- **The two presentations of the category `𝒞` of coherent reflexive modules agree.**  On
either side an object is a module carrying proofs and a morphism is a morphism of `X.Modules`,
so the two functors are mutually inverse on the nose. -/
public noncomputable def coherentReflexiveModulesEquiv (X : Scheme.{u}) :
    CoherentReflexiveModules X ≌ ReflexiveCoherentModules X where
  functor := toReflexiveCoherentModules X
  inverse := ofReflexiveCoherentModules X
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Stacks.AlgebraicGeometry.ReflexiveModules

end
