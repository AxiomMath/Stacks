module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiOpens
public import StacksFrontier.AlgebraicGeometry.Topologies.SiteStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# The small Zariski structure sheaf and the structure sheaf of the space

An object of the small Zariski site of a scheme `S` *is* an open subscheme of `S`, so the
structure sheaf `AlgebraicGeometry.SmallZariski.structureSheaf` of that site and the structure
sheaf of the underlying space of `S` carry the same information. This file identifies them: the
presheaves of functions agree naturally in the object, and transporting the sheaf of the small
Zariski site across the equivalence of sheaf categories returns the sheaf of rings of `S`.

## Main definitions

* `AlgebraicGeometry.SmallZariski.structureSheaf` — the structure sheaf of the small Zariski
  site of `S`.

## Main results

* `AlgebraicGeometry.SmallZariski.structure_isSheaf` — global functions are a sheaf of rings
  on the small Zariski site.
* `AlgebraicGeometry.smallZariskiStructurePresheafIso` — the comparison of the two presheaves
  of functions on the small Zariski site.
* `AlgebraicGeometry.smallZariskiStructureSheaf_pullbackIso` — the comparison as an
  isomorphism of sheaves of rings.
* `AlgebraicGeometry.smallZariskiStructureSheaf_iso` — transporting the structure sheaf of the
  small Zariski site across the equivalence of sheaf categories gives the sheaf of rings of
  `S`.

## Implementation notes

The comparison on sections is the canonical isomorphism `IsOpenImmersion.ΓIsoTop` between the
global functions of an open subscheme and the sections of `S` over its image, whose naturality
in the open subscheme is `AlgebraicGeometry.openImmersion_ΓIsoTop_naturality`. This is what
makes `AlgebraicGeometry.smallZariskiStructureSheaf_pullbackIso` an isomorphism of sheaves of
rings and not merely a bijection on sections.

## References

* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Over an object of the small Zariski site of `S`, the sections of the structure sheaf of
`S` on its open image are its own global functions, naturally in that object. -/
public noncomputable def smallZariskiStructurePresheafIso :
    (smallZariskiToOpens B S hS).op ⋙ S.ringCatSheaf.obj ≅
      Stacks.Sites.structurePresheaf S
        (SmallZariski.inclusion B S hS ⋙ Over.post B.inclusion) :=
  NatIso.ofComponents
    (fun X => (forget₂ CommRingCat RingCat).mapIso
      (IsOpenImmersion.ΓIsoTop (smallZariskiOpenImmersion B S hS X.unop)).symm)
    (fun {X Y} f => congrArg (forget₂ CommRingCat RingCat).map
      (openImmersion_ΓIsoTop_naturality
        ((SmallZariski.toScheme B S hS).map f.unop)
        (smallZariskiOpenImmersion B S hS Y.unop)
        (smallZariskiOpenImmersion B S hS X.unop)
        (smallZariskiOpenImmersion_comp B S hS f.unop)
        ((smallZariskiToOpens B S hS).map f.unop).le))

/-- The presheaf of global functions on the small Zariski site of `S` is a sheaf of rings. -/
public theorem SmallZariski.structure_isSheaf :
    Presheaf.IsSheaf (SmallZariski.topology B S hS)
      (Stacks.Sites.structurePresheaf S
        (SmallZariski.inclusion B S hS ⋙ Over.post B.inclusion)) :=
  (Presheaf.isSheaf_of_iso_iff (smallZariskiStructurePresheafIso B S hS)).1
    ((smallZariskiSheafEquivWith B S hS RingCat.{u}).inverse.obj S.ringCatSheaf).property

/-- The structure sheaf of the small Zariski site of `S`, the structure sheaf `𝒪_S` of
Stacks 04HS for the site `S_Zar`: its value at an open `T ⊆ S` is `Γ(T, 𝒪_T)`. -/
public noncomputable def SmallZariski.structureSheaf :
    Sheaf (SmallZariski.topology B S hS) RingCat.{u} :=
  ⟨Stacks.Sites.structurePresheaf S (SmallZariski.inclusion B S hS ⋙ Over.post B.inclusion),
    SmallZariski.structure_isSheaf B S hS⟩

/-- The structure sheaf of the small Zariski site has the presheaf of global functions as its
underlying presheaf. -/
@[simp]
public theorem SmallZariski.structureSheaf_obj :
    (SmallZariski.structureSheaf B S hS).obj =
      Stacks.Sites.structurePresheaf S
        (SmallZariski.inclusion B S hS ⋙ Over.post B.inclusion) :=
  rfl

/-- The structure sheaf of `S` pulls back to the structure sheaf of the small Zariski site by
the canonical open-immersion maps on sections. -/
public noncomputable def smallZariskiStructureSheaf_pullbackIso :
    (smallZariskiSheafEquivWith B S hS RingCat.{u}).inverse.obj S.ringCatSheaf ≅
      SmallZariski.structureSheaf B S hS :=
  ObjectProperty.isoMk _ (smallZariskiStructurePresheafIso B S hS)

/-- On sections over `X`, the inverse of `smallZariskiStructureSheaf_pullbackIso` is the
canonical isomorphism `IsOpenImmersion.ΓIsoTop`. -/
public theorem smallZariskiStructureSheaf_pullbackIso_inv_app (X : SmallZariski B S hS) :
    (smallZariskiStructureSheaf_pullbackIso B S hS).inv.hom.app (op X) =
      (forget₂ CommRingCat RingCat).map
        (IsOpenImmersion.ΓIsoTop (smallZariskiOpenImmersion B S hS X)).hom := rfl

/-- Transporting the structure sheaf of the small Zariski site across the equivalence of
sheaf categories gives the sheaf of rings of `S`. -/
public noncomputable def smallZariskiStructureSheaf_iso :
    (smallZariskiSheafEquivWith B S hS RingCat.{u}).functor.obj
        (SmallZariski.structureSheaf B S hS) ≅ S.ringCatSheaf :=
  ((smallZariskiSheafEquivWith B S hS RingCat.{u}).functor.mapIso
    (smallZariskiStructureSheaf_pullbackIso B S hS)).symm ≪≫
      (smallZariskiSheafEquivWith B S hS RingCat.{u}).counitIso.app S.ringCatSheaf

end AlgebraicGeometry
