module

public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Stalks of a presheaf of modules: germs and induced maps

Let `O` be a presheaf of commutative rings on a topological space `X` and let `M` be a presheaf
of `O`-modules. Mathlib equips the stalk of the underlying presheaf of abelian groups with a
module structure over the stalk of `O`; this file provides the small amount of interface that
makes that structure usable: the germ map and the existence of representing sections *typed at
the module carriers* rather than at the abelian-group carriers, and the linear map induced on
stalks by a morphism of presheaves of modules, which Mathlib has only as a morphism of abelian
groups.

The retyping is load-bearing rather than cosmetic. Mathlib's stalk is `TopCat.Presheaf.stalk`
of `M.presheaf`, whose sections over an open set are `ToType (M.presheaf.obj (op U))`; the
module structure on them is found by instance search only at the spelling
`↑(M.obj (op U))`, so `r • m` does not even elaborate for a section produced by
`TopCat.Presheaf.exists_germ_eq`. The abbreviations below fix the spelling once.

## Main definitions

* `Stacks.ModuleStalk.presheafOn`: the underlying presheaf of abelian groups of a presheaf of
  modules, typed as a presheaf on the space so that the stalk and germ API applies.
* `Stacks.ModuleStalk.germ`, `Stacks.ModuleStalk.res`: the germ of a section of a presheaf of
  modules and its restriction, typed at the module carriers.
* `Stacks.ModuleStalk.moduleStalk`: the module structure on a stalk, named so that it can be
  supplied explicitly.
* `Stacks.ModuleStalk.stalkMap`: the map induced on stalks by a morphism of presheaves of
  modules, as a linear map over the stalk of the presheaf of rings.

## Main results

* `Stacks.ModuleStalk.exists_germ_eq`, `Stacks.ModuleStalk.exists_le_germ_eq`: every element of
  the stalk is the germ of a section, on an arbitrarily small neighbourhood.
* `Stacks.ModuleStalk.germ_smul`: the germ map is semilinear over the germ map of the presheaf
  of rings; `Stacks.ModuleStalk.res_smul`, `.res_res`, `.res_app` are the corresponding
  statements for restriction of sections.
* `Stacks.ModuleStalk.stalkMap_germ`: the defining formula for `stalkMap`.
* `Stacks.ModuleStalk.stalkMap_comp`: `stalkMap` is functorial.
* `Stacks.ModuleStalk.stalk_linearMap_ext`: two linear maps out of a stalk agreeing on germs are
  equal.

## References

* [Stacks Project, Tag 007L](https://stacks.math.columbia.edu/tag/007L)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.ModuleStalk

variable {X : TopCat.{u}} {O : X.Presheaf CommRingCat.{u}}

/-- The underlying presheaf of abelian groups of a presheaf of `O`-modules, typed as a presheaf
on the space `X`, so that the `TopCat.Presheaf` stalk and germ API applies to it by dot
notation. -/
abbrev presheafOn (M : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)) :
    X.Presheaf AddCommGrpCat.{u} := M.presheaf

section Germs

variable (M : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat))

/-- The module structure on the stalk of a presheaf of modules over the stalk of the presheaf of
rings, named so that it can be supplied explicitly. Instance search finds it only when the index
presheaf of rings appears in the syntactic form `O ⋙ forget₂ CommRingCat RingCat`; where a
presheaf of modules is indexed by a presheaf of rings that merely reduces to that form, this
abbreviation supplies the instance, the reduction being checked once at elaboration. -/
abbrev moduleStalk (x : X) : Module ↑(O.stalk x) ↑((presheafOn M).stalk x) := inferInstance

/-- The restriction of a section of a presheaf of modules to a smaller open set, typed at the
module carriers. -/
abbrev res {U V : Opens X} (h : V ≤ U) (m : ↑(M.obj (op U))) : ↑(M.obj (op V)) :=
  (M.map (homOfLE h).op).hom m

/-- The germ at `x` of a section of a presheaf of modules over an open neighbourhood of `x`,
typed at the module carriers. -/
abbrev germ (U : Opens X) (x : X) (hx : x ∈ U) (m : ↑(M.obj (op U))) :
    ↑((presheafOn M).stalk x) := (presheafOn M).germ U x hx m

/-- Every element of the stalk of a presheaf of modules is the germ of a section. -/
theorem exists_germ_eq {x : X} (a : ↑((presheafOn M).stalk x)) :
    ∃ (U : Opens X) (hx : x ∈ U) (m : ↑(M.obj (op U))), germ M U x hx m = a :=
  (presheafOn M).exists_germ_eq a

/-- Every element of the stalk of a presheaf of modules is the germ of a section over an
arbitrarily small open neighbourhood. -/
theorem exists_le_germ_eq {x : X} (a : ↑((presheafOn M).stalk x)) {V : Opens X} (hV : x ∈ V) :
    ∃ U ≤ V, ∃ (hx : x ∈ U) (m : ↑(M.obj (op U))), germ M U x hx m = a :=
  (presheafOn M).exists_le_germ_eq a hV

/-- Restriction of sections is additive. -/
theorem res_add {U V : Opens X} (h : V ≤ U) (m m' : ↑(M.obj (op U))) :
    res M h (m + m') = res M h m + res M h m' := map_add _ _ _

/-- Restriction of sections sends zero to zero. -/
theorem res_zero {U V : Opens X} (h : V ≤ U) : res M h (0 : ↑(M.obj (op U))) = 0 := map_zero _

/-- Restriction of sections is transitive. -/
theorem res_res {U V W : Opens X} (h₁ : V ≤ U) (h₂ : W ≤ V) (m : ↑(M.obj (op U))) :
    res M h₂ (res M h₁ m) = res M (h₂.trans h₁) m :=
  have h : (presheafOn M).map (homOfLE h₁).op ≫ (presheafOn M).map (homOfLE h₂).op =
      (presheafOn M).map (homOfLE (h₂.trans h₁)).op :=
    ((presheafOn M).map_comp (homOfLE h₁).op (homOfLE h₂).op).symm.trans
      (congrArg (presheafOn M).map (Subsingleton.elim _ _))
  (ConcreteCategory.comp_apply ((presheafOn M).map (homOfLE h₁).op)
      ((presheafOn M).map (homOfLE h₂).op) m).symm.trans
    (congrArg (fun φ : (presheafOn M).obj (op U) ⟶ (presheafOn M).obj (op W) =>
      ConcreteCategory.hom φ m) h)

/-- Restriction of sections is semilinear over restriction of scalars. -/
theorem res_smul {U V : Opens X} (h : V ≤ U) (r : ↑(O.obj (op U))) (m : ↑(M.obj (op U))) :
    res M h (r • m) = (O.map (homOfLE h).op).hom r • res M h m :=
  M.map_smul (homOfLE h).op r m

/-- The germ map is additive. -/
theorem germ_add {U : Opens X} {x : X} (hx : x ∈ U) (m m' : ↑(M.obj (op U))) :
    germ M U x hx (m + m') = germ M U x hx m + germ M U x hx m' := map_add _ _ _

/-- The germ map sends zero to zero. -/
theorem germ_zero {U : Opens X} {x : X} (hx : x ∈ U) :
    germ M U x hx (0 : ↑(M.obj (op U))) = 0 := map_zero _

/-- Restricting a section does not change its germ. -/
theorem germ_res {U V : Opens X} (h : V ≤ U) {x : X} (hx : x ∈ V) (m : ↑(M.obj (op U))) :
    germ M V x hx (res M h m) = germ M U x (h hx) m :=
  (presheafOn M).germ_res_apply (homOfLE h) x hx m

/-- The germ map of a presheaf of modules is semilinear over the germ map of the presheaf of
rings. This is Mathlib's `PresheafOfModules.germ_smul`, restated at the carriers used here. The
name says `presheaf` because `Stacks.ModuleStalk.germ_smul` is the same statement for a sheaf of
modules on a scheme, in `StacksDraft.AlgebraicGeometry.F3.Ample.ModuleStalk`. -/
theorem presheafGerm_smul {U : Opens X} {x : X} (hx : x ∈ U) (r : ↑(O.obj (op U)))
    (m : ↑(M.obj (op U))) :
    germ M U x hx (r • m) = O.germ U x hx r • germ M U x hx m :=
  PresheafOfModules.germ_smul M x U hx r m

end Germs

section StalkMap

variable {M N L : PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat RingCat)}

/-- A morphism of presheaves of modules commutes with restriction of sections. -/
theorem res_app (φ : M ⟶ N) {U V : Opens X} (h : V ≤ U) (m : ↑(M.obj (op U))) :
    res N h ((φ.app (op U)).hom m) = (φ.app (op V)).hom (res M h m) :=
  (PresheafOfModules.naturality_apply φ (homOfLE h).op m).symm

/-- The map induced on stalks by a morphism of presheaves of modules sends the germ of a section
to the germ of its image. This is Mathlib's `TopCat.Presheaf.stalkFunctor_map_germ_apply`,
restated at the carriers used here. -/
theorem stalkFunctor_map_germ (φ : M ⟶ N) (x : X) (U : Opens X) (hx : x ∈ U)
    (m : ↑(M.obj (op U))) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf _).map φ)).hom (germ M U x hx m) =
      germ N U x hx ((φ.app (op U)).hom m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf _).map φ) m

/-- The map induced on stalks by a morphism of presheaves of `O`-modules, as a linear map over
the stalk of `O`. Mathlib's stalk functor provides it only as a morphism of abelian groups;
linearity is checked on germs. -/
def stalkMap (φ : M ⟶ N) (x : X) :
    ↑((presheafOn M).stalk x) →ₗ[O.stalk x] ↑((presheafOn N).stalk x) where
  toFun := ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf _).map φ)).hom
  map_add' a b := map_add _ a b
  map_smul' r a := by
    obtain ⟨U, hxU, ρ, hρ⟩ := O.exists_germ_eq r
    obtain ⟨V, hVU, hxV, m, hm⟩ := exists_le_germ_eq M a hxU
    have hrV : O.germ V x hxV (O.map (homOfLE hVU).op ρ) = r := by
      rw [O.germ_res_apply (homOfLE hVU) x hxV ρ]; exact hρ
    simp only [RingHom.id_apply, ← hm, ← hrV, ← presheafGerm_smul M hxV, stalkFunctor_map_germ,
      map_smul, presheafGerm_smul N hxV]

/-- The map `stalkMap φ x` sends the germ of a section to the germ of its image under `φ`. -/
@[simp]
theorem stalkMap_germ (φ : M ⟶ N) (x : X) (U : Opens X) (hx : x ∈ U) (m : ↑(M.obj (op U))) :
    stalkMap φ x (germ M U x hx m) = germ N U x hx ((φ.app (op U)).hom m) :=
  stalkFunctor_map_germ φ x U hx m

/-- Two linear maps out of a stalk which agree on all germs are equal. -/
theorem stalk_linearMap_ext (x : X) {Q : Type u} [AddCommMonoid Q] [Module ↑(O.stalk x) Q]
    {f g : ↑((presheafOn M).stalk x) →ₗ[O.stalk x] Q}
    (h : ∀ (U : Opens X) (hx : x ∈ U) (m : ↑(M.obj (op U))),
      f (germ M U x hx m) = g (germ M U x hx m)) : f = g := by
  refine LinearMap.ext fun a => ?_
  obtain ⟨U, hx, m, rfl⟩ := exists_germ_eq M a
  exact h U hx m

/-- The map induced on stalks is functorial. -/
theorem stalkMap_comp (φ : M ⟶ N) (ψ : N ⟶ L) (x : X) :
    stalkMap (φ ≫ ψ) x = (stalkMap ψ x).comp (stalkMap φ x) :=
  stalk_linearMap_ext x fun U hx m => by
    rw [stalkMap_germ, LinearMap.comp_apply, stalkMap_germ, stalkMap_germ]
    rfl

end StalkMap

end Stacks.ModuleStalk

end
