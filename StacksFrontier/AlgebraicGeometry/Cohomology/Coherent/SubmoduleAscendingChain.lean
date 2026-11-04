module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AscendingChain
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel

/-!
# The ascending chain condition for embedded quasi-coherent submodules

On a Noetherian scheme an ascending chain of quasi-coherent subobjects of a coherent sheaf of
modules eventually stabilizes; that is [Stacks, Tag 01Y8], proved in
`StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.AscendingChain` for chains of categorical
subobjects. Its consumers, however, present their submodules as *embedded* ones — families of
submodules of the modules of sections, stable under restriction — and need the conclusion as an
equality of those families, section by section, not as an equality of subobjects.

This file supplies the translation. A submodule `N` of `F` presents the subobject
`Subobject.mk N.ι`, that assignment is monotone, and it *reflects* the order: an inclusion of the
presented subobjects is already an inclusion of the submodules. Hence it is injective, and the
ascending chain condition transfers verbatim.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.Submodule.toSubobject` — the subobject of `F` presented by a
  submodule of `F`.
* `AlgebraicGeometry.SheafOfModules.Submodule.homOfLEModules` — the inclusion of one submodule of
  `F` into a larger one, with both ends ascribed at `X.Modules`.

## Main results

* `AlgebraicGeometry.SheafOfModules.Submodule.toSubobject_le_toSubobject_iff` — the presentation
  is an order embedding, and `AlgebraicGeometry.SheafOfModules.Submodule.toSubobject_injective`
  its injectivity.
* `AlgebraicGeometry.SheafOfModules.Submodule.isQuasicoherent_toSubobject` — the presented
  subobject is quasi-coherent when the submodule is.
* `AlgebraicGeometry.exists_eventually_constant_quasicoherentSubmodules` — the ascending chain
  condition of [Stacks, Tag 01Y8] for embedded quasi-coherent submodules of a coherent sheaf on
  a Noetherian scheme.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` whose
categorical instances are separate declarations, so `SheafOfModules.Submodule.ι` — whose source is
stated at the generic spelling — has no `Mono` instance available at `X.Modules`, and
`Subobject.mk` cannot be applied to it. Everything here is therefore phrased with
`AlgebraicGeometry.SheafOfModules.Submodule.ιModules`, the re-export of the inclusion with its
source ascribed at `X.Modules`; `homOfLEModules` is the corresponding re-export of
`SheafOfModules.Submodule.homOfLE`.

Order reflection is the only step with mathematical content, and it is the evaluation of
`Subobject.ofMkLEMk` on sections: the comparison map `k` of the two presentations satisfies
`k ≫ N₂.ι = N₁.ι`, and both inclusions act on sections as the inclusion of a submodule into its
ambient module, so the image of a section of `N₁` under `k` is that section again, now witnessed
as a section of `N₂`.

## References

* [Stacks Project, Tag 01Y8](https://stacks.math.columbia.edu/tag/01Y8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules.Submodule

noncomputable section

variable {X : Scheme.{u}} {F : X.Modules}

/-- The inclusion of one submodule of `F` into a larger one, with both ends ascribed at
`X.Modules`.

`SheafOfModules.Submodule.homOfLE` has the generic `SheafOfModules X.ringCatSheaf` as the type of
both ends, and no instance registered for `X.Modules` applies to that spelling. -/
noncomputable def homOfLEModules {N₁ N₂ : F.Submodule} (h : N₁ ≤ N₂) :
    N₁.asModules ⟶ N₂.asModules :=
  SheafOfModules.Submodule.homOfLE h

/-- The inclusion between two comparable submodules of `F`, followed by the inclusion of the
larger into `F`, is the inclusion of the smaller. -/
lemma homOfLEModules_ιModules {N₁ N₂ : F.Submodule} (h : N₁ ≤ N₂) :
    homOfLEModules h ≫ N₂.ιModules = N₁.ιModules :=
  SheafOfModules.Submodule.homOfLE_ι h

/-- The subobject of `F` presented by a submodule of `F`. -/
noncomputable def toSubobject (N : F.Submodule) : Subobject F :=
  Subobject.mk N.ιModules

/-- The underlying object of the subobject presented by `N` is `N` itself. -/
noncomputable def underlyingIsoToSubobject (N : F.Submodule) :
    ((toSubobject N : X.Modules)) ≅ N.asModules :=
  Subobject.underlyingIso N.ιModules

/-- A submodule contained in another presents a smaller subobject. -/
lemma toSubobject_le_toSubobject {N₁ N₂ : F.Submodule} (h : N₁ ≤ N₂) :
    toSubobject N₁ ≤ toSubobject N₂ :=
  Subobject.mk_le_mk_of_comm (homOfLEModules h) (homOfLEModules_ιModules h)

/-- A morphism of the two embedded submodules compatible with their inclusions into `F` forces
the containment of the submodules: on sections it carries a section of `N₁` to the same section
of `F`, now exhibited as a section of `N₂`. -/
lemma le_of_hom_comp_ιModules {N₁ N₂ : F.Submodule} (k : N₁.asModules ⟶ N₂.asModules)
    (hk : k ≫ N₂.ιModules = N₁.ιModules) : N₁ ≤ N₂ := by
  intro V y hy
  have h1 := congrArg (fun φ : N₁.asModules ⟶ F => (φ.val.app V).hom
    (show (N₁.asModules).val.obj V from ⟨y, hy⟩)) hk
  let z : N₂.obj V := (ModuleCat.Hom.hom (k.val.app V))
    (show (N₁.asModules).val.obj V from ⟨y, hy⟩)
  have h2 : (z : F.val.obj V) = y := h1
  exact h2 ▸ z.2

/-- The presentation of a submodule as a subobject is an order embedding. -/
lemma toSubobject_le_toSubobject_iff {N₁ N₂ : F.Submodule} :
    toSubobject N₁ ≤ toSubobject N₂ ↔ N₁ ≤ N₂ :=
  ⟨fun h => le_of_hom_comp_ιModules (Subobject.ofMkLEMk N₁.ιModules N₂.ιModules h)
    (Subobject.ofMkLEMk_comp h), toSubobject_le_toSubobject⟩

/-- Distinct submodules present distinct subobjects. -/
lemma toSubobject_injective : Function.Injective (toSubobject (F := F)) := fun _ _ h =>
  le_antisymm (toSubobject_le_toSubobject_iff.1 h.le)
    (toSubobject_le_toSubobject_iff.1 h.ge)

/-- The subobject presented by a quasi-coherent submodule is quasi-coherent. -/
lemma isQuasicoherent_toSubobject (N : F.Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherent) :
    ((toSubobject N : X.Modules)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (underlyingIsoToSubobject N).symm hN

end

end AlgebraicGeometry.SheafOfModules.Submodule

namespace AlgebraicGeometry

/-- **[Stacks, Tag 01Y8] for embedded submodules.** On a Noetherian scheme an ascending chain of
quasi-coherent submodules of a coherent sheaf of modules eventually becomes constant.

This is the subobject form `AlgebraicGeometry.exists_eventually_constant_quasicoherentSubobjects`
read through the order embedding
`AlgebraicGeometry.SheafOfModules.Submodule.toSubobject_le_toSubobject_iff`. -/
theorem exists_eventually_constant_quasicoherentSubmodules (X : Scheme.{u}) [IsNoetherian X]
    (F : X.Modules) [F.IsCoherent] (N : ℕ → F.Submodule)
    (hN : ∀ n, (N n).toSheafOfModules.IsQuasicoherent) (hmono : Monotone N) :
    ∃ n, ∀ m, n ≤ m → N m = N n := by
  obtain ⟨n, hn⟩ := exists_eventually_constant_quasicoherentSubobjects X F
    (fun k => SheafOfModules.Submodule.toSubobject (N k))
    (fun k => SheafOfModules.Submodule.isQuasicoherent_toSubobject (N k) (hN k))
    (fun _ _ h => SheafOfModules.Submodule.toSubobject_le_toSubobject (hmono h))
  exact ⟨n, fun m hm => SheafOfModules.Submodule.toSubobject_injective (hn m hm)⟩

end AlgebraicGeometry

end
