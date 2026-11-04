module

public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.DerivedTwistHypercohomology
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.GlobalSections

/-!
# A global section of a sheaf of modules, as a morphism out of the unit

The cocycle the argument of [Stacks, Tag 0BQR] produces is a *global section* of a sheaf of
modules, while
`Stacks.SheafOfModules.not_isZero_homology_derivedModuleGlobalSections_of_cycleHom` consumes a
*morphism out of the unit* `𝒪_X ⟶ Z^p`. This file is the bridge: Mathlib's
`SheafOfModules.unitHomEquiv` identifies the morphisms out of the unit with the compatible
families of sections, and `Stacks.SectionRingGeometric.sectionsEquivObj` identifies those with the
sections over `⊤`, the site of opens of a space having `⊤` as a terminal object.

Three properties are what make the bridge usable: the value of the morphism on the unit section
recovers the section, the morphism is zero only if the section is, and composing it with a
morphism of sheaves gives the morphism attached to the image of the section.

## Main definitions

* `Stacks.AmpleNonvanishing.structureUnit`: the structure sheaf as an `𝒪_X`-module.
* `Stacks.AmpleNonvanishing.unitHomOfGlobalSection`: `Γ(M, ⊤) → (𝒪_X ⟶ M)`.

## Main results

* `Stacks.AmpleNonvanishing.unitHomOfGlobalSection_val_app_one`: the morphism attached to a global
  section carries the unit section of `𝒪_X` over `⊤` to that global section.
* `Stacks.AmpleNonvanishing.eq_zero_of_unitHomOfGlobalSection_eq_zero`.
* `Stacks.AmpleNonvanishing.unitHomOfGlobalSection_comp`: compatibility with composition, which is
  the naturality of `SheafOfModules.unitHomEquiv` together with the naturality of
  `Stacks.SectionRingGeometric.sectionsEquivObj` — the latter not being in the repository, it is
  proved here by comparing the two compatible families over each open.

## Implementation notes

**The module variable is declared at `Stacks.DerivedTensor.RingedSite.Modules X.sheaf`**, the
spelling the termwise twist and the derived tensor product are stated at, and *not* at
`AlgebraicGeometry.Scheme.Modules`. The two are `rfl`-equal types with different instance
provenance: `Preadditive (SheafOfModules R)` is a global instance, whereas `Preadditive X.Modules`
exists only as the local instance `Stacks.SectionRingGeometric.schemePreadditive`. Re-seating that
local instance is **not** enough — with the variable declared at `X.Modules` the numeral `0` of
`(𝒪_X ⟶ M)` is rejected, as `OfNat (SheafOfModules.unit X.ringCatSheaf ⟶ M) 0` — and ascribing
the *object* at the use site does not help, because the `Category` instance is taken from the
declared type of the variable and not from the ascription. The price is that the
`Γ(M, U)` notation, which is `AlgebraicGeometry.Scheme.Modules`-only, cannot be used here, so the
sections are written `M.val.obj (op ⊤)`; a caller holding a `Γ(M, ⊤)` passes it unchanged, the two
being definitionally equal.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AmpleNonvanishing

/-- **The structure sheaf as an `𝒪_X`-module**, at the spelling
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf` of the category of `𝒪_X`-modules that the
termwise twist and the derived tensor product are stated at. -/
abbrev structureUnit (X : Scheme.{u}) : Stacks.DerivedTensor.RingedSite.Modules X.sheaf :=
  _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)

variable {X : Scheme.{u}}

/-- **A global section of an `𝒪_X`-module, as a morphism out of the unit.** The sections over the
terminal open `⊤` are the compatible families of sections
(`Stacks.SectionRingGeometric.sectionsEquivObj`), and those are the morphisms out of the unit
(`SheafOfModules.unitHomEquiv`). -/
def unitHomOfGlobalSection (M : Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
    (ρ : M.val.obj (op (⊤ : X.Opens))) : structureUnit X ⟶ M :=
  M.unitHomEquiv.symm
    ((Stacks.SectionRingGeometric.sectionsEquivObj
      (isTerminalTop (α := X.Opens)) M.val).symm ρ)

/-- **The morphism out of the unit attached to a global section carries the unit section to that
global section.** -/
theorem unitHomOfGlobalSection_val_app_one
    (M : Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
    (ρ : M.val.obj (op (⊤ : X.Opens))) :
    (unitHomOfGlobalSection M ρ).val.app (op ⊤)
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj
          (op (⊤ : X.Opens))) = ρ := by
  rw [← _root_.SheafOfModules.unitHomEquiv_apply_coe M (unitHomOfGlobalSection M ρ) (op ⊤)]
  show (M.unitHomEquiv (M.unitHomEquiv.symm
      ((Stacks.SectionRingGeometric.sectionsEquivObj
        (isTerminalTop (α := X.Opens)) M.val).symm ρ))).val (op ⊤) = ρ
  rw [Equiv.apply_symm_apply]
  exact (Stacks.SectionRingGeometric.sectionsEquivObj
    (isTerminalTop (α := X.Opens)) M.val).apply_symm_apply ρ

/-- **A global section whose morphism out of the unit vanishes is zero.** -/
theorem eq_zero_of_unitHomOfGlobalSection_eq_zero
    (M : Stacks.DerivedTensor.RingedSite.Modules X.sheaf)
    (ρ : M.val.obj (op (⊤ : X.Opens))) (h : unitHomOfGlobalSection M ρ = 0) : ρ = 0 := by
  -- The zero morphism is zero on sections by `rfl`: the additive structure of `SheafOfModules` is
  -- pulled back along `Hom.val` by `Equiv.addCommGroup`, and `PresheafOfModules.zero_app`,
  -- `ModuleCat.hom_zero` and `LinearMap.zero_apply` are each `rfl`. A `simp only` naming those
  -- three does *not* close it, leaving `0 1 = 0`.
  have hz : (0 : structureUnit X ⟶ M).val.app (op ⊤)
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf).obj.obj
        (op (⊤ : X.Opens))) = 0 := rfl
  rw [← unitHomOfGlobalSection_val_app_one M ρ, h]
  exact hz

/-- **Composing the morphism attached to a global section with a morphism of sheaves gives the
morphism attached to the image of that section.** This is the naturality
`SheafOfModules.unitHomEquiv_symm_comp` of Mathlib's bijection, together with the naturality of
`Stacks.SectionRingGeometric.sectionsEquivObj`: the two compatible families agree over every open,
each being the restriction from `⊤` of the image of `ρ`. -/
theorem unitHomOfGlobalSection_comp
    {M N : Stacks.DerivedTensor.RingedSite.Modules X.sheaf}
    (ρ : M.val.obj (op (⊤ : X.Opens))) (φ : M ⟶ N) :
    unitHomOfGlobalSection M ρ ≫ φ =
      unitHomOfGlobalSection N (φ.val.app (op ⊤) ρ) := by
  refine (_root_.SheafOfModules.unitHomEquiv_symm_comp _ φ).trans
    (congrArg N.unitHomEquiv.symm ?_)
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  exact PresheafOfModules.naturality_apply φ.val
    ((isTerminalTop (α := X.Opens)).from U.unop).op ρ

end Stacks.AmpleNonvanishing

end
