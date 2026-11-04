module

public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformChartTorsion
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule

/-!
# Sections of a quotient by a quasi-coherent subsheaf, over an affine open

`AlgebraicGeometry.sectionsCokernelEquivOfAffineOpen` computes the sections of a cokernel of
quasi-coherent modules over an affine open as the sections of the target modulo the *range* of
the sections of the map. When the map is the inclusion of a submodule that range is the
submodule's own sections, so the cokernel's sections are a quotient of modules of sections:

```
Γ(ℱ/𝒩, U) = Γ(ℱ, U) / 𝒩(U)        for `U` affine.
```

This file records that form. It is what transports a statement about a quotient of *modules*
over `Γ(X, U)` — such as the local graded pieces of the filtrations of [Stacks, Tag 0ESU] — to
the quotient *sheaf*.

## Main results

* `AlgebraicGeometry.sectionsSubmodule`: the sections of a subsheaf over an open, as a submodule
  over the ring `Γ(X, U)` rather than over the `RingCat`-valued sections of the structure sheaf.
* `AlgebraicGeometry.range_sectionsLinearMap_ι`: the range of the sections of `𝒩 ⟶ ℱ` over any
  open is `𝒩`'s sections there. No affineness and no quasi-coherence.
* `AlgebraicGeometry.sectionsSubmoduleQuotientEquivOfAffineOpen`:
  `Γ(ℱ, U) / 𝒩(U) ≃ₗ Γ(cokernel 𝒩.ι, U)` for `U` affine and `ℱ`, `𝒩` quasi-coherent.

## Implementation notes

**Why `sectionsSubmodule` exists.** `𝒩.toSubmodule.obj (op U)` is declared as a submodule over
`X.ringCatSheaf.obj.obj (op U)`, and instance search does not cross the `TopCat.Sheaf`
definition to see that as `Γ(X, U)`. The two are definitionally equal, so `sectionsSubmodule` is
the same object at the spelling under which `Submodule.Quotient`'s module instance fires; without
it the quotient `Γ(ℱ, U) ⧸ 𝒩(U)` does not elaborate. For the same reason the module structure on
the sections of `𝒩.toSheafOfModules` needs `Scheme.Modules` to be reducible for instances, which
is the idiom of `StacksFrontier.AlgebraicGeometry.AnnihilatorQcoh.Basic`.

The range computation is immediate: the inclusion is sectionwise the inclusion of a submodule,
so a section of `ℱ` is in the range exactly when it lies in `𝒩`.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F : X.Modules}

/-- **The sections of a subsheaf over an open, as a submodule over `Γ(X, U)`.** This is
`N.toSubmodule.obj (op U)` at the spelling of the scalar ring under which the quotient
`Γ(ℱ, U) ⧸ 𝒩(U)` elaborates; the two are definitionally equal. -/
def sectionsSubmodule (N : F.Submodule) (U : X.Opens) : Submodule Γ(X, U) Γ(F, U) :=
  N.toSubmodule.obj (op U)

/-- Membership in `AlgebraicGeometry.sectionsSubmodule` is membership in the subsheaf. -/
theorem mem_sectionsSubmodule (N : F.Submodule) (U : X.Opens) (s : Γ(F, U)) :
    s ∈ sectionsSubmodule N U ↔ s ∈ N.toSubmodule.obj (op U) := Iff.rfl

/-- **The range of the sections of a subsheaf's inclusion is the subsheaf's sections.** True
over every open, with no affineness and no quasi-coherence: the inclusion is sectionwise the
inclusion of a submodule. -/
theorem range_sectionsLinearMap_ι (N : F.Submodule) (U : X.Opens) :
    LinearMap.range (Scheme.Modules.sectionsLinearMap N.ι U) = sectionsSubmodule N U :=
  Submodule.ext fun s => by
    refine ⟨?_, fun hs => ⟨⟨s, hs⟩, rfl⟩⟩
    rintro ⟨t, rfl⟩
    exact t.2

/-- **Over an affine open the sections of a quotient by a quasi-coherent subsheaf are the
quotient of the sections.** For `U` affine and `ℱ`, `𝒩` quasi-coherent,
`Γ(ℱ/𝒩, U) = Γ(ℱ, U) / 𝒩(U)`.

This is `AlgebraicGeometry.sectionsCokernelEquivOfAffineOpen` for the inclusion `𝒩 ⟶ ℱ`, whose
sections have range `𝒩(U)` by `AlgebraicGeometry.range_sectionsLinearMap_ι`. -/
def sectionsSubmoduleQuotientEquivOfAffineOpen (N : F.Submodule) [F.IsQuasicoherent]
    [N.toSheafOfModules.IsQuasicoherent] (U : X.affineOpens) :
    (Γ(F, U.1) ⧸ sectionsSubmodule N U.1) ≃ₗ[Γ(X, U.1)] Γ(cokernel N.ι, U.1) :=
  (Submodule.quotEquivOfEq _ _ (range_sectionsLinearMap_ι N U.1).symm).trans
    (sectionsCokernelEquivOfAffineOpen N.ι U)

end AlgebraicGeometry

end
