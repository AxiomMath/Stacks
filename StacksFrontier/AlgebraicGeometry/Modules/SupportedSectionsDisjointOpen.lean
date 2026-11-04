module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Topology.Sheaves.Stalks
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSubmodule

/-!
# Sections supported on a set vanish on an open disjoint from it

Let `F` be a module on a scheme `X` and let `Z ⊆ X` be a subset. The submodule of sections
supported on `Z` (Stacks Tag 084L,
`AlgebraicGeometry.SheafOfModules.supportedSectionsSubmodule`) restricts to zero on any open
`W` disjoint from `Z`: over an open of `W`, a section of the submodule has all its germs
vanishing, since every point of `W` lies outside `Z`, and a section of a *sheaf* all of whose
germs vanish is zero.

Consequently the quotient map `F ⟶ F / F_Z` becomes an isomorphism after restriction to `W`:
restriction to an open preserves colimits, so it carries the cokernel of the inclusion
`F_Z ⟶ F` to a cokernel of the zero map.

## Main results

* `Stacks.Modules.supportedSections_restrict_isZero` and
  `Stacks.Modules.supportedSections_pullback_isZero`: the restriction of `F_Z` to an open
  disjoint from `Z` is the zero module, in the `restrictFunctor` and in the `pullback`
  spelling.
* `Stacks.Modules.isIso_pullback_supportedSections_quotient`: the quotient map `F ⟶ F / F_Z`
  restricts to an isomorphism on an open disjoint from `Z`.

## References

* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Modules

/-- **Sections supported on `Z` restrict to zero on an open disjoint from `Z`.** A section of
the submodule over an open of `W` has vanishing germ at every point outside `Z`, and every
point of `W` is outside `Z`, so the section is zero because `F` is a sheaf. -/
theorem supportedSections_restrict_isZero
    {X : Scheme.{u}} (F : X.Modules) (Z : Set X) (W : X.Opens)
    (hW : Disjoint (W : Set X) Z) :
    IsZero ((Scheme.Modules.restrictFunctor W.ι).obj
      (AlgebraicGeometry.SheafOfModules.supportedSectionsSubmodule Z F).toSheafOfModules) := by
  refine (IsZero.iff_id_eq_zero _).2 ?_
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext s
  refine Subtype.ext ?_
  apply TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩
  intro x hx
  have hxW : x ∈ W := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.2
  exact (s.property x hx (Set.disjoint_left.mp hW hxW)).trans (map_zero _).symm

/-- `supportedSections_restrict_isZero` in the `pullback` spelling: the two functors are
isomorphic. -/
theorem supportedSections_pullback_isZero
    {X : Scheme.{u}} (F : X.Modules) (Z : Set X) (W : X.Opens)
    (hW : Disjoint (W : Set X) Z) :
    IsZero ((Scheme.Modules.pullback W.ι).obj
      (AlgebraicGeometry.SheafOfModules.supportedSectionsSubmodule Z F).toSheafOfModules) :=
  (supportedSections_restrict_isZero F Z W hW).of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _).symm

/-- **The quotient by the sections supported on `Z` is an isomorphism away from `Z`.**
Restriction to an open preserves the cokernel of the inclusion `F_Z ⟶ F`, and `F_Z` restricts
to zero, so the restricted quotient map is a cokernel of a map out of the zero module. -/
theorem isIso_pullback_supportedSections_quotient
    {X : Scheme.{u}} (F : X.Modules) (Z : Set X) (W : X.Opens)
    (hW : Disjoint (W : Set X) Z) :
    IsIso ((Scheme.Modules.pullback W.ι).map
      (cokernel.π
        (AlgebraicGeometry.SheafOfModules.supportedSectionsSubmodule Z F).ι)) := by
  let T := Scheme.Modules.pullback W.ι
  let i := (AlgebraicGeometry.SheafOfModules.supportedSectionsSubmodule Z F).ι
  exact CokernelCofork.IsColimit.isIso_π _
    (isColimitOfHasCokernelOfPreservesColimit T i)
    ((supportedSections_pullback_isZero F Z W hW).eq_of_src _ _)

end Stacks.Modules

end
