module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.PushforwardTwist
public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Coherent ideals, image subschemes and supports of direct images

This file proves that the direct image along a finite morphism of a quasi-coherent ideal of the
structure sheaf is coherent, that the closed subscheme cut out by the kernel of a closed immersion
with integral source is integral, with the image of its generic point a generic point of the
support of the kernel, and that a direct image along a closed immersion is supported inside that
support.

## Main results

* `Stacks.AlgebraicGeometry.CoherentDevissageGlue.isCoherent_of_isQuasicoherent_submodule_unit`:
  a quasi-coherent submodule of the structure sheaf of a locally Noetherian scheme is coherent.
* `Stacks.AlgebraicGeometry.CoherentDevissageGlue.isCoherent_pushforward_submodule_unit`: the
  direct image along a finite morphism into a locally Noetherian scheme of a quasi-coherent
  submodule of the structure sheaf is coherent.
* `Stacks.AlgebraicGeometry.CoherentDevissageGlue.isIntegral_subscheme_ker`: the closed
  subscheme cut out by the kernel of a closed immersion with integral source is integral.
* `Stacks.AlgebraicGeometry.CoherentDevissageGlue.isGenericPoint_subschemeι_genericPoint`: for
  an ideal sheaf whose closed subscheme is integral, the image of the generic point of that
  subscheme is a generic point of the support.
* `Stacks.AlgebraicGeometry.CoherentDevissageGlue.supp_pushforward_subset_support_ker`: a direct
  image along a closed immersion is supported in the support of the kernel ideal.
* `Stacks.AlgebraicGeometry.CoherentDevissageGlue.isGenericPoint_toImage_genericPoint`: for a
  closed immersion with integral source, the image of the generic point of the kernel subscheme
  is a generic point of the range.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
* [Stacks Project, Tag 01YI](https://stacks.math.columbia.edu/tag/01YI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissageGlue

/-! ### Coherence of an ideal and of its direct image -/

/-- A quasi-coherent submodule of the structure sheaf of a locally Noetherian scheme is
coherent. -/
theorem isCoherent_of_isQuasicoherent_submodule_unit {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (J : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    [J.toSheafOfModules.IsQuasicoherent] :
    _root_.SheafOfModules.IsCoherent J.toSheafOfModules :=
  have : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf) :=
    CoherenceCriteria.structureSheaf_isCoherent Z
  have : Mono (C := Z.Modules) J.ι :=
    inferInstanceAs (Mono (C := _root_.SheafOfModules Z.ringCatSheaf) J.ι)
  CoherentSubquotients.isCoherent_of_mono J.ι

/-- The direct image along a finite morphism into a locally Noetherian scheme of a quasi-coherent
ideal of the structure sheaf is coherent. -/
theorem isCoherent_pushforward_submodule_unit {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsFinite i]
    (J : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    [J.toSheafOfModules.IsQuasicoherent] :
    _root_.SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward i).obj J.toSheafOfModules) :=
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have : _root_.SheafOfModules.IsCoherent J.toSheafOfModules :=
    isCoherent_of_isQuasicoherent_submodule_unit J
  FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite i J.toSheafOfModules

/-! ### The image subscheme of an integral closed subscheme -/

/-- The closed subscheme cut out by the kernel of a closed immersion with integral source is
integral. -/
instance isIntegral_subscheme_ker {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] : IsIntegral i.ker.subscheme :=
  have : Nonempty i.ker.subscheme :=
    ⟨i.toImage (Classical.choice (inferInstance : Nonempty Z))⟩
  isIntegral_of_isOpenImmersion (asIso i.toImage).inv

/-- The image of the generic point of an integral closed subscheme is a generic point of the
support of its ideal. -/
theorem isGenericPoint_subschemeι_genericPoint {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] :
    IsGenericPoint (I.subschemeι (genericPoint I.subscheme)) (I.support : Set X) := by
  have hgen : IsGenericPoint (genericPoint I.subscheme) (Set.univ : Set I.subscheme) :=
    (IrreducibleSpace.isIrreducible_univ I.subscheme).isGenericPoint_genericPoint isClosed_univ
  simpa [Set.image_univ, I.range_subschemeι, I.support.isClosed.closure_eq] using
    hgen.image I.subschemeι.continuous

/-! ### The support of a direct image -/

/-- A direct image along a closed immersion is supported in the support of the kernel ideal. -/
theorem supp_pushforward_subset_support_ker {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (G : Z.Modules) :
    _root_.SheafOfModules.supp ((Scheme.Modules.pushforward i).obj G) ⊆
      (i.ker.support : Set X) := by
  rw [supp_pushforward_of_isClosedImmersion, Stacks.AffineClosedUnion.support_ker_eq_range]
  exact Set.image_subset_range _ _

/-- For a closed immersion with integral source, the image of the generic point of the kernel
subscheme is a generic point of the range. -/
theorem isGenericPoint_toImage_genericPoint {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [IsIntegral Z] :
    IsGenericPoint (i.ker.subschemeι (genericPoint i.ker.subscheme))
      (Set.range i.base) :=
  (Stacks.AffineClosedUnion.support_ker_eq_range i) ▸
    isGenericPoint_subschemeι_genericPoint i.ker

end Stacks.AlgebraicGeometry.CoherentDevissageGlue

end
