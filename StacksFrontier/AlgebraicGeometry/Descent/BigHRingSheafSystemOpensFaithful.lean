module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemOpens
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Descent along a family of opens is faithful, for a system of sheaves of rings

Let `𝓡` be a system of sheaves of rings on the big h category over `S`
(`AlgebraicGeometry.BigHOver.RingSheafSystem`) with the restriction property
(`AlgebraicGeometry.BigHOver.RingSheafSystem.UnitBijective`), and let `W i` be a family of opens of
the underlying scheme of an object `U` that covers it. Then the canonical functor from sheaves of
`𝓡 U`-modules to descent data along the inclusions of the `W i` is faithful: this is the separated
half of the stack condition for the pseudofunctor of modules of `𝓡` along the family.

The argument: if two morphisms `χ χ' : M ⟶ N` have the same extensions of scalars to every `W i`,
then by naturality of the unit `N ⟶ ι_* ι^* N` they agree after composition with that unit, and
the unit is injective on sections over the opens contained in `W i`. So `χ` and `χ'` agree on the
sections over every open contained in some `W i`, and a morphism into a sheaf is determined by
those (`TopCat.Sheaf.eq_hom_of_restrict`).

## Main results

* `AlgebraicGeometry.BigHOver.RingSheafSystem.eq_of_pull_map_eq_opens`: two morphisms of sheaves
  of `𝓡 U`-modules with equal extensions of scalars to the members of an open covering are equal.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.faithful_toDescentData_opens`: **the descent functor
  of the pseudofunctor of modules of `𝓡` along an open covering is faithful.**

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.BigHOver.RingSheafSystem

universe u

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {𝓡 : RingSheafSystem B S hS}
  {U : BigHOver B S hS}

/-- For a system with the restriction property, a morphism into a module is determined on the
sections over an open `T ≤ V` by its composite with the unit along the inclusion of `V`. -/
lemma app_eq_of_comp_unit_eq (h𝓡 : 𝓡.UnitBijective) (V : ((toScheme B S hS).obj U).Opens)
    {M N : SheafOfModules.{u} (𝓡.ring U)} {χ χ' : M ⟶ N}
    (h : χ ≫ (𝓡.adj (opensι B S hS V)).unit.app N = χ' ≫ (𝓡.adj (opensι B S hS V)).unit.app N)
    (T : ((toScheme B S hS).obj U).Opens) (hT : T ≤ V) :
    χ.val.app (op T) = χ'.val.app (op T) := by
  have e := coe_app_congr h (op T)
  rw [coe_app_comp, coe_app_comp] at e
  exact ModuleCat.hom_ext (LinearMap.ext fun x =>
    congrFun ((h𝓡 U V N T hT).1.comp_left e) x)

/-- **Two morphisms of sheaves of `𝓡 U`-modules with equal extensions of scalars to the members of
an open covering are equal**, for a system with the restriction property. -/
lemma eq_of_pull_map_eq_opens (h𝓡 : 𝓡.UnitBijective) {ι : Type u}
    (W : ι → ((toScheme B S hS).obj U).Opens) (hW : ⨆ i, W i = ⊤)
    {M N : SheafOfModules.{u} (𝓡.ring U)} (χ χ' : M ⟶ N)
    (h : ∀ i, (𝓡.pull (opensι B S hS (W i)).op).map χ =
      (𝓡.pull (opensι B S hS (W i)).op).map χ') :
    χ = χ' := by
  have hloc : ∀ (i : ι) (T : ((toScheme B S hS).obj U).Opens), T ≤ W i →
      χ'.val.app (op T) = χ.val.app (op T) := by
    intro i T hT
    have n := (𝓡.adj (opensι B S hS (W i))).unit.naturality χ
    have n' := (𝓡.adj (opensι B S hS (W i))).unit.naturality χ'
    simp only [Functor.id_map, Functor.comp_map] at n n'
    rw [h i] at n
    exact (app_eq_of_comp_unit_eq h𝓡 (W i) (n.trans n'.symm) T hT).symm
  exact SheafOfModules.hom_ext (TopCat.Sheaf.eq_hom_of_restrict hW N.isSheaf
    (fun _ T _ => χ.val.app (op T)) (fun _ _ _ => rfl) hloc)

/-- **The descent functor of the pseudofunctor of modules of a system of sheaves of rings along an
open covering is faithful**, for a system with the restriction property. This is the separated
half of the stack condition along a family of opens. -/
theorem faithful_toDescentData_opens (h𝓡 : 𝓡.UnitBijective) {ι : Type u}
    (W : ι → ((toScheme B S hS).obj U).Opens) (hW : ⨆ i, W i = ⊤) :
    (𝓡.modulePseudofunctor.toDescentData (fun i => opensι B S hS (W i))).Faithful where
  map_injective {_ _} {χ χ'} h :=
    eq_of_pull_map_eq_opens h𝓡 W hW χ χ' fun i => congrArg (fun φ => φ.hom i) h

end AlgebraicGeometry.BigHOver.RingSheafSystem

end
