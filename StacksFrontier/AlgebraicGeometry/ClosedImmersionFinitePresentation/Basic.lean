module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation

/-!
# A closed immersion is of finite presentation exactly when its ideal sheaf is of finite type

A closed immersion `f : X ⟶ Y` factors as an isomorphism `X ≅ Y/ker f` followed by the
inclusion of the closed subscheme cut out by `f.ker`, and both finite presentation and local
finite presentation are insensitive to composing with an isomorphism. The characterization of
finite presentation of that inclusion by finite generation of the ideal sheaf is already
available, so the content here is the transport along the factorization.

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker` and
  `AlgebraicGeometry.finitePresentation_iff_fg_ker`: a closed immersion is (locally) of finite
  presentation exactly when its kernel ideal sheaf is finitely generated over every affine
  open of the target.

## Implementation notes

"The associated quasi-coherent sheaf of ideals is of finite type" is read here ideal by ideal,
as `∀ U : Y.affineOpens, (f.ker.ideal U).FG`. This is the condition the source's own proof
uses — it reduces to finite generation of `I` on each affine open by Properties, Tag 01PB —
and it is how the condition is already spelled in
`StacksFrontier/AlgebraicGeometry/Flatness/SubschemeFinitePresentation.lean` and named by
`AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`. The equivalence with finite type of
the ideal sheaf as a module over the structure sheaf, i.e. with
`SheafOfModules.IsFiniteType`, is *not* proved here; `AlgebraicGeometry.tilde_isFiniteType_iff`
(Tag 01PB) is its affine half.

The "finite type" direction of the source's remark needs no hypothesis at all: a closed
immersion is always locally of finite type, which is a Mathlib instance.

## References

* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A closed immersion is locally of finite presentation exactly when its kernel ideal sheaf is
finitely generated over every affine open of the target. -/
theorem locallyOfFinitePresentation_iff_fg_ker (f : X ⟶ Y) [IsClosedImmersion f] :
    LocallyOfFinitePresentation f ↔ ∀ U : Y.affineOpens, (f.ker.ideal U).FG := by
  have h₁ : inv f.toImage ≫ f = f.ker.subschemeι :=
    (IsIso.inv_comp_eq _).mpr f.toImage_imageι.symm
  have h₂ : f.toImage ≫ f.ker.subschemeι = f := f.toImage_imageι
  rw [← Stacks.Flatness.locallyOfFinitePresentation_subschemeι_iff]
  refine ⟨fun hf ↦ h₁ ▸ HasRingHomProperty.comp_of_isOpenImmersion @LocallyOfFinitePresentation
      (Q := RingHom.FinitePresentation) (inv f.toImage) f hf,
    fun hf ↦ h₂ ▸ HasRingHomProperty.comp_of_isOpenImmersion
      @LocallyOfFinitePresentation (Q := RingHom.FinitePresentation) f.toImage
      f.ker.subschemeι hf⟩

/-- **[Stacks Project, Tag 01TV].** A closed immersion is of finite presentation exactly when
the associated quasi-coherent sheaf of ideals is of finite type, i.e. when its ideal over every
affine open of the target is finitely generated.

Quasi-compactness and quasi-separatedness of a closed immersion hold unconditionally, so
finite presentation asks nothing beyond local finite presentation here. -/
@[stacks 01TV, ega "IV 1.4.5" "closed immersion case"]
theorem finitePresentation_iff_fg_ker (f : X ⟶ Y) [IsClosedImmersion f] :
    FinitePresentation f ↔ ∀ U : Y.affineOpens, (f.ker.ideal U).FG := by
  rw [show FinitePresentation f ↔ LocallyOfFinitePresentation f from
    ⟨fun h ↦ h.1, fun h ↦ ⟨h, inferInstance, inferInstance⟩⟩,
    locallyOfFinitePresentation_iff_fg_ker]

end AlgebraicGeometry

end
