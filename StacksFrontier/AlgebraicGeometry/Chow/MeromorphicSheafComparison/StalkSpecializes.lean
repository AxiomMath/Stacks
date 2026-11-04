module

public import StacksFrontier.AlgebraicGeometry.Divisors.MeromorphicStalk.ModuleStalk

/-!
# Specialization maps between the stalks of a presheaf of modules

Let `O` be a presheaf of commutative rings on a topological space `X`, let `M` be a presheaf of
`O`-modules and let `x ⤳ y` be a specialization. Mathlib's `TopCat.Presheaf.stalkSpecializes`
gives a map `M_y → M_x` of abelian groups; this file records that it is semilinear over the
corresponding map `O_y → O_x` and packages it as a linear map over `O_y`.

Naturality in `M` is Mathlib's `TopCat.Presheaf.stalkSpecializes_stalkFunctor_map`, since
`Stacks.ModuleStalk.stalkMap` is the stalk-functor map of the underlying presheaf of abelian
groups; it is what makes the comparison map `F_x → 𝒦(F)_x` of a sheaf of meromorphic sections
commute with specialization, so that the specialization map of `𝒦(F)` is determined by that
of `F`.

## Main definitions

* `Stacks.ModuleStalk.specializedStalkModule` — the stalk at the more generic point, as a module
  over the local ring at the more special point.
* `Stacks.ModuleStalk.stalkSpecializesₗ` — the specialization map, as a linear map.

## Main results

* `Stacks.ModuleStalk.stalkSpecializes_smul` — semilinearity.

## References

* [Stacks Project, Tag 007L](https://stacks.math.columbia.edu/tag/007L)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.ModuleStalk

variable {X : TopCat.{u}} {O : X.Presheaf CommRingCat.{u}}
  (M : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat))

/-- The specialization map on the stalks of a presheaf of modules is semilinear over the
specialization map on the stalks of the presheaf of rings. Both are computed on germs, where the
statement is `Stacks.ModuleStalk.germ_smul`. -/
theorem stalkSpecializes_smul {x y : X} (h : x ⤳ y) (r : ↑(O.stalk y))
    (m : ↑((presheafOn M).stalk y)) :
    (presheafOn M).stalkSpecializes h (r • m) =
      O.stalkSpecializes h r • (presheafOn M).stalkSpecializes h m := by
  obtain ⟨U, hyU, ρ, hρ⟩ := O.exists_germ_eq r
  obtain ⟨V, hVU, hyV, t, ht⟩ := exists_le_germ_eq M m hyU
  have hxV : x ∈ V := h.mem_open V.isOpen hyV
  have hρ' : O.germ V y hyV ((O.map (homOfLE hVU).op).hom ρ) = r := by
    rw [← hρ]; exact O.germ_res_apply (homOfLE hVU) y hyV ρ
  have key : ∀ w : ↑(M.obj (op V)),
      (presheafOn M).stalkSpecializes h (germ M V y hyV w) = germ M V x hxV w :=
    fun w => TopCat.Presheaf.germ_stalkSpecializes_apply (F := presheafOn M) hyV h w
  have keyO : ∀ w : ToType (O.obj (op V)),
      O.stalkSpecializes h (O.germ V y hyV w) = O.germ V x hxV w :=
    fun w => TopCat.Presheaf.germ_stalkSpecializes_apply (F := O) hyV h w
  rw [← ht, ← hρ', ← presheafGerm_smul M hyV, key, keyO, key, presheafGerm_smul M]

/-- The stalk of a presheaf of modules at the more generic point of a specialization, as a module
over the stalk of the presheaf of rings at the more special point: scalars act through the
specialization map of the presheaf of rings. -/
@[instance_reducible]
def specializedStalkModule {x y : X} (h : x ⤳ y) :
    Module ↑(O.stalk y) ↑((presheafOn M).stalk x) :=
  Module.compHom _ (O.stalkSpecializes h).hom

/-- The specialization map `M_y → M_x` on the stalks of a presheaf of modules, as a linear map
over the local ring `O_y`. -/
def stalkSpecializesₗ {x y : X} (h : x ⤳ y) :
    letI := specializedStalkModule M h
    ↑((presheafOn M).stalk y) →ₗ[O.stalk y] ↑((presheafOn M).stalk x) :=
  letI := specializedStalkModule M h
  { toFun := (presheafOn M).stalkSpecializes h
    map_add' := map_add _
    map_smul' := fun r m => stalkSpecializes_smul M h r m }

end Stacks.ModuleStalk
