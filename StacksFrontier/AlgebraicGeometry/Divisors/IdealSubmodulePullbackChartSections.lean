module

public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSubmoduleFlatPullback

/-!
# The sections of the canonical map `q^* I ⟶ 𝒪_X` along a flat morphism

Let `q : X ⟶ Y` be a morphism of schemes and `I ⊆ 𝒪_Y` a quasi-coherent sheaf of ideals.
`Stacks.ClosedSubscheme.pullbackIdealMap` is the canonical map `q^* I ⟶ 𝒪_X`; the lemma
`Stacks.ClosedSubscheme.pullbackIdealMap_app_mem_opens` says its image over an open `W` of `X`
lies inside the sections of the inverse-image ideal sheaf `I·𝒪_X = I.comap q` there, and
`Stacks.ClosedSubscheme.exists_app_eq_of_mem` says it is onto those sections over an affine open
lying over an affine open of `Y`.

This file closes the gap between the two when `q` is flat: **over an *arbitrary* open of `X` the
image is exactly the sections of `I.comap q` there.** No pair of affine charts, and so no
condition relating the open to the opens of `Y`, is needed.

## Main results

* `Stacks.ClosedSubscheme.exists_pullbackIdealMap_app_eq_iff_mem`: for flat `q` and any open `W`
  of `X`, a section of `𝒪_X` over `W` is in the image of `q^* I ⟶ 𝒪_X` exactly when it lies in
  the sections of `I.comap q` over `W`.
* `Stacks.ClosedSubscheme.exists_pullbackIdealMap_app_eq_iff_mem_ideal`: the same over an affine
  open, with the right-hand side read as the ideal `(I.comap q).ideal V` by
  `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine`.

## Why flatness, and why only here

The inclusion of the image into the sections of the inverse image is unconditional — it is
`pullbackIdealMap_app_mem_opens`.  The reverse inclusion is not: the comparison
`Stacks.ClosedSubscheme.pullbackIdealComparison` of `q^* I` with `(I.comap q)` is an epimorphism
with no hypothesis (`Stacks.ClosedSubscheme.epi_pullbackIdealComparison`), but an epimorphism of
sheaves of modules is only *locally* surjective, so it says nothing about the sections over a
given open.  Flatness makes the comparison an isomorphism —
`Stacks.ClosedSubscheme.isIso_pullbackIdealComparison`, through
`Stacks.ClosedSubscheme.pullbackIdealFlatIso` — and an isomorphism of sheaves of modules is
bijective on the sections over every open.  So the proof below is the inverse isomorphism read on
sections, and uses `Stacks.ClosedSubscheme.pullbackIdealFlatIso_hom_comp_iota` to say that the
comparison composed with the inclusion of `I.comap q` is the canonical map itself.

An étale morphism is flat, so this is the form in which the identification applies at an étale
chart of a scheme: the chart's structure morphism is étale, hence flat, and the open is the whole
of the chart scheme.

## References

* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR), the inverse image of a
  sheaf of ideals.
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4), flatness and inverse
  images of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

attribute [local instance] Stacks.Algebraization.monoSubmoduleι
  Stacks.Algebraization.sectionsModuleΓ Stacks.Algebraization.sectionsModuleΓSheaf
  Stacks.Algebraization.sectionsSMulCommClassΓ

namespace Stacks.ClosedSubscheme

variable {X Y : Scheme.{u}} (q : X ⟶ Y) (I : Y.IdealSheafData)

/-- **The image of the canonical map `q^* I ⟶ 𝒪_X` over an open, for flat `q`.**  A regular
function on an open `W` of `X` is the image of a section of `q^* I` exactly when it lies in the
sections over `W` of the inverse-image sheaf of ideals `I·𝒪_X`.

One direction is `Stacks.ClosedSubscheme.pullbackIdealMap_app_mem_opens`, which needs no
hypothesis.  The other is the inverse of
`Stacks.ClosedSubscheme.pullbackIdealFlatIso` read on the sections over `W`: that isomorphism
composed with the inclusion of `I.comap q` into the structure sheaf is the canonical map, so the
image of a section of `I.comap q` under the inverse is a preimage of it. -/
theorem exists_pullbackIdealMap_app_eq_iff_mem [AlgebraicGeometry.Flat q] (W : X.Opens)
    (t : Γ(Scheme.unitModule X, W)) :
    (∃ s, Scheme.Modules.Hom.app (pullbackIdealMap q I) W s = t) ↔
      t ∈ ((I.comap q).unitSubmodule).toSubmodule.obj (op W) := by
  refine ⟨?_, fun ht => ?_⟩
  · rintro ⟨s, rfl⟩
    exact pullbackIdealMap_app_mem_opens q I W s
  · have hfac : (pullbackIdealFlatIso q I).inv ≫ pullbackIdealMap q I =
        idealIota (I.comap q) :=
      (congrArg (fun k => (pullbackIdealFlatIso q I).inv ≫ k)
          (pullbackIdealFlatIso_hom_comp_iota q I)).symm.trans
        ((pullbackIdealFlatIso q I).inv_hom_id_assoc (idealIota (I.comap q)))
    obtain ⟨y, hy⟩ : ∃ y : Γ((((I.comap q).unitSubmodule).toSheafOfModules : X.Modules), W),
        Scheme.Modules.Hom.app (idealIota (I.comap q)) W y = t := ⟨⟨t, ht⟩, rfl⟩
    exact ⟨Scheme.Modules.Hom.app (pullbackIdealFlatIso q I).inv W y,
      (congrArg (fun k => Scheme.Modules.Hom.app k W y) hfac).trans hy⟩

/-- **The image of the canonical map `q^* I ⟶ 𝒪_X` over an affine open, for flat `q`**, with the
sections of the inverse-image ideal sheaf read as the ideal `(I.comap q).ideal V` itself.

This is `Stacks.ClosedSubscheme.exists_pullbackIdealMap_app_eq_iff_mem` with
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine` applied to the right-hand
side.  It is the form a consumer at an affine chart uses: the right-hand side is the
affine-local data of the inverse-image sheaf of ideals and nothing else. -/
theorem exists_pullbackIdealMap_app_eq_iff_mem_ideal [AlgebraicGeometry.Flat q]
    (V : X.affineOpens) (t : Γ(Scheme.unitModule X, V.1)) :
    (∃ s, Scheme.Modules.Hom.app (pullbackIdealMap q I) V.1 s = t) ↔
      t ∈ (I.comap q).ideal V := by
  rw [exists_pullbackIdealMap_app_eq_iff_mem q I V.1 t,
    AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule_obj_affine (I.comap q) V]
  exact Iff.rfl

end Stacks.ClosedSubscheme

end
