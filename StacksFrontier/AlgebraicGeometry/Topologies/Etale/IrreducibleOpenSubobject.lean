module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IrreducibleGenericPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.IrreducibleEtaleNeighborhood

/-!
# Irreducible open subobjects of the small étale site

An open subscheme of an object of the small étale site of `Y` is again an object of that site:
its structure morphism is the open immersion followed by the given étale structure morphism, and
an open immersion is étale. This file records that construction and the following consequence:
**every nonempty object of the small étale site of an irreducible locally Noetherian scheme has a
nonempty irreducible open subobject.**

The subobject is produced at a point over the generic point of `Y`. Such a point exists because
the structure morphism of the object is étale, hence open, so its image is a nonempty open of the
irreducible `Y` and therefore contains the generic point; that is
`AlgebraicGeometry.SmallEtale.genericPoint_mem_range_structureMorphism`. Around such a point
`AlgebraicGeometry.exists_opens_contains_isGenericPoint_of_etale` produces an irreducible open
neighbourhood below the cutoff of the big étale site, which `AlgebraicGeometry.SmallEtale.openObj`
turns into an object of the site.

## Main definitions

* `AlgebraicGeometry.SmallEtale.openObj` and `AlgebraicGeometry.SmallEtale.openObjHom` — an open
  subscheme of an object of the small étale site, as an object of that site, and its inclusion.

## Main results

* `AlgebraicGeometry.SmallEtale.toScheme_obj_openObj` and
  `AlgebraicGeometry.SmallEtale.toScheme_map_openObjHom` — the underlying scheme and morphism of
  that object and inclusion are the open subscheme and its inclusion, on the nose.
* `AlgebraicGeometry.SmallEtale.exists_irreducibleSpace_openObj` — the irreducible open
  subobject of a nonempty object.

## Implementation notes

No `@[stacks]` attribute appears here: an open subobject of the small étale site is a
construction, not a numbered statement of the source.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (Y : Scheme.{u}) (hY : B.Contains Y)

section Shrink

variable {B} {Y} {hY}

/-- An open subscheme of an object of the small étale site, as an object of that site. -/
def openObj (U : SmallEtale B Y hY) (W : ((SmallEtale.toScheme B Y hY).obj U).Opens)
    (hW : B.Contains W.toScheme) : SmallEtale B Y hY :=
  ⟨Over.mk (ObjectProperty.homMk (W.ι ≫ B.inclusion.map U.obj.hom) :
      B.obj W.toScheme hW ⟶ B.obj Y hY),
    show Etale (W.ι ≫ B.inclusion.map U.obj.hom) from inferInstance⟩

/-- The inclusion of an open subscheme of an object of the small étale site. -/
def openObjHom (U : SmallEtale B Y hY) (W : ((SmallEtale.toScheme B Y hY).obj U).Opens)
    (hW : B.Contains W.toScheme) : openObj U W hW ⟶ U :=
  ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk W.ι : B.obj W.toScheme hW ⟶ U.obj.left) rfl)

/-- The underlying scheme of `openObj U W hW` is the open subscheme `W`. -/
theorem toScheme_obj_openObj (U : SmallEtale B Y hY)
    (W : ((SmallEtale.toScheme B Y hY).obj U).Opens) (hW : B.Contains W.toScheme) :
    (SmallEtale.toScheme B Y hY).obj (openObj U W hW) = W.toScheme := rfl

/-- The underlying morphism of schemes of `openObjHom U W hW` is the open immersion `W.ι`. -/
theorem toScheme_map_openObjHom (U : SmallEtale B Y hY)
    (W : ((SmallEtale.toScheme B Y hY).obj U).Opens) (hW : B.Contains W.toScheme) :
    (SmallEtale.toScheme B Y hY).map (openObjHom U W hW) = W.ι := rfl

end Shrink

/-- A nonempty object of the small étale site of an irreducible locally Noetherian scheme has a
nonempty irreducible open subobject. -/
theorem exists_irreducibleSpace_openObj [IrreducibleSpace Y] [IsLocallyNoetherian Y]
    (U : SmallEtale B Y hY) (u : (SmallEtale.toScheme B Y hY).obj U) :
    ∃ (W : ((SmallEtale.toScheme B Y hY).obj U).Opens) (_ : B.Contains W.toScheme),
      IrreducibleSpace W.toScheme := by
  have _ : Nonempty (B.inclusion.obj (Over.left U.obj)) := ⟨u⟩
  have _ : IrreducibleSpace (B.inclusion.obj (B.obj Y hY)) := ‹IrreducibleSpace Y›
  have _ : IsLocallyNoetherian (B.inclusion.obj (B.obj Y hY)) := ‹IsLocallyNoetherian Y›
  obtain ⟨w, hw⟩ :=
    AlgebraicGeometry.genericPoint_mem_range_of_universallyOpen (B.inclusion.map U.obj.hom)
  obtain ⟨W, hwW, hWc, hWirr, -⟩ :=
    AlgebraicGeometry.exists_opens_contains_isGenericPoint_of_etale B U.obj.left.property
      (B.inclusion.map U.obj.hom) hw
  exact ⟨W, hWc, hWirr⟩

end AlgebraicGeometry.SmallEtale

end
