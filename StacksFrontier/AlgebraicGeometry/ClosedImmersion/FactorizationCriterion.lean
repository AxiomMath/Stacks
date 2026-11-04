module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedSubspace

/-!
# The vanishing criterion for factoring through a closed subspace

Let `X` be a locally ringed space, let `j : J ⟶ 𝒪_X` be a monomorphism of sheaves of modules
exhibiting `J` as a sheaf of ideals, and let `D` realize the associated closed subspace. A
morphism `f : Y ⟶ X` factors through `D` exactly when the canonical map `f^* J ⟶ 𝒪_Y` vanishes.
This file proves the "only if" half of that criterion together with the pieces of the converse
that are independent of the construction of the factorization.

## Main definitions

* `pullbackIdealMap f J j` is the canonical map `f^* J ⟶ 𝒪_Y`, the map whose vanishing is the
  criterion. It is a reducible spelling, retained because the inverse-image ideal of Tag 01HQ is
  its image.
* `quotientStructureSheafMap` is the map `i_* 𝒪_D ⟶ f_* 𝒪_Y` of sheaves of `𝒪_X`-modules obtained
  from the vanishing, `i` being the inclusion of the closed subspace.

## Main results

* `pullbackIdealMap_eq_zero_iff` transposes the criterion across the adjunction `f^* ⊣ f_*`: the
  pulled-back map vanishes exactly when `j` composed into `f_* 𝒪_Y` vanishes.
* `pullbackIdealMap_eq_zero_of_factorsThrough` is the "only if" half of Tag 01HP: a morphism that
  factors through the closed subspace has vanishing pulled-back ideal map.
* `range_base_subset_quotientSupport` is the first half of the converse: the vanishing forces the
  image of `f` into the support of `𝒪_X / J`.
* `exists_base_factorization_of_pullbackIdealMap_eq_zero` upgrades that to a factorization of the
  underlying continuous map through the closed subspace.
* `unitToPushforwardObjUnit_comp_quotientStructureSheafMap` is the second half of the converse:
  the map on structure sheaves of a factorization, obtained by descending `𝒪_X ⟶ f_* 𝒪_Y` through
  the quotient `𝒪_X / J`.

## Implementation notes

The criterion is stated through the adjunction, and the first step of every proof here is to
transpose it. `pullbackIdealMap_eq_zero_iff` does that once and for all: the adjoint transpose of
`f^* J ⟶ 𝒪_Y` is `j ≫ (𝒪_X ⟶ f_* 𝒪_Y)` by `Adjunction.homEquiv_naturality_left` together with
`SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`, and a morphism
vanishes exactly when its transpose does because `f_*` is additive, hence preserves the zero
morphism, so `homEquiv` carries `0` to `0`. Additivity of `f_*` is not an instance in Mathlib but
holds by construction, the pushforward of sheaves of modules being the pushforward of the
underlying presheaves; it is established inline.

Both the vanishing for a composite, `comp_unitToPushforwardObjUnit_comp_eq_zero`, and the
compatibilities used by `range_base_subset_quotientSupport` are proved section by section rather
than by transporting the composition isomorphism `SheafOfModules.pushforwardComp`. The reason is
that the pushforward functor is indexed by the functor between the sites, so a statement about
`f_*` for `f = g ≫ i` and one about `i_* g_*` are statements about different, merely isomorphic,
functors. Section by section no such transport is needed:
`SheafOfModules.unitToPushforwardObjUnit_val_app_apply` makes the map on sections of
`𝒪_X ⟶ f_* 𝒪_Y` literally the map on sections of `f`'s structure-sheaf component, and
`AlgebraicGeometry.PresheafedSpace.comp_c_app` makes the latter for a composite literally a
composite, both by `rfl`.

`range_base_subset_quotientSupport` is the one place where locality of the rings is used. A
section of `J` is carried to `0` in `𝒪_Y`, so its germ is carried to `0` by the stalk map; a ring
homomorphism carries units to units, and `0` is not a unit in the stalk of a locally ringed space,
which is a nontrivial ring.

What is not proved here is the construction of the factorization itself from
`exists_base_factorization_of_pullbackIdealMap_eq_zero` and
`quotientStructureSheafMap`. Two steps are missing. First, `quotientStructureSheafMap` is a map of
sheaves of `𝒪_X`-modules, and turning it into a morphism of sheaves of rings
`𝒪_D ⟶ b_* 𝒪_Y` requires descending it along `i_*` — every open of the closed subspace is the
preimage of an open of `X`, so `i_*` is full on presheaves — and checking multiplicativity, which
follows from `𝒪_X ⟶ i_* 𝒪_D` being locally surjective and `f_* 𝒪_Y` being a separated presheaf.
Second, the resulting morphism of presheafed spaces has to be checked to be a morphism of locally
ringed spaces, that is, local on stalks. Consequently the full criterion, Tag 01HP, is not stated
here; its uniqueness half is
`Stacks.ClosedImmersion.subsingleton_factorizations_closedSubspace`.

## References

* [Stacks Project, Tag 01HP](https://stacks.math.columbia.edu/tag/01HP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

/-- The canonical map `f^* J ⟶ 𝒪_Y` attached to a map `j : J ⟶ 𝒪_X` of sheaves of modules and a
morphism `f : Y ⟶ X` of locally ringed spaces: the pullback of `j` followed by the canonical
identification of the pulled-back structure sheaf with `𝒪_Y`. Its vanishing is the criterion for
`f` to factor through the closed subspace cut out by `j`, and its image is the inverse-image ideal
of Tag 01HQ. -/
noncomputable abbrev pullbackIdealMap {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)
    (J : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace)) :
    (modulePullback f.toShHom).obj J ⟶ SheafOfModules.unit (structureSheafRing Y.toRingedSpace) :=
  letI : (SheafOfModules.pushforward (structureSheafHom f.toShHom)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f.toShHom
  (modulePullback f.toShHom).map j ≫
    SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f.toShHom)

/-- The criterion, transposed across the adjunction `f^* ⊣ f_*`: the canonical map `f^* J ⟶ 𝒪_Y`
vanishes exactly when `j` followed by the structure-sheaf map `𝒪_X ⟶ f_* 𝒪_Y` vanishes. -/
theorem pullbackIdealMap_eq_zero_iff {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)
    (J : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace)) :
    pullbackIdealMap f J j = 0 ↔
      j ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom) = 0 := by
  have : (SheafOfModules.pushforward (structureSheafHom f.toShHom)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f.toShHom
  have : (SheafOfModules.pushforward (structureSheafHom f.toShHom)).Additive :=
    ⟨fun {_ _ _ _} => by ext1; rfl⟩
  have key : (SheafOfModules.pullbackPushforwardAdjunction
        (structureSheafHom f.toShHom)).homEquiv J
        (SheafOfModules.unit (structureSheafRing Y.toRingedSpace))
      ((SheafOfModules.pullback (structureSheafHom f.toShHom)).map j ≫
        SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f.toShHom)) =
      j ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom) := by
    rw [Adjunction.homEquiv_naturality_left,
      SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  have hzero : (SheafOfModules.pullbackPushforwardAdjunction
      (structureSheafHom f.toShHom)).homEquiv J
      (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) 0 = 0 := by
    rw [Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  rw [← key, ← hzero, Equiv.apply_eq_iff_eq]
  exact Iff.rfl

/-- If `k ≫ (𝒪_X ⟶ f_* 𝒪_Y) = 0`, then the structure-sheaf map of `f` kills every section of `k`. -/
private theorem structureSheafHom_app_map_eq_zero {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)
    {K : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (k : K ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (h : k ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom) = 0)
    (U) (s) : (structureSheafHom f.toShHom).hom.app U (k.val.app U s) = 0 :=
  congrArg (fun t => (ModuleCat.Hom.hom (SheafOfModules.Hom.val t |>.app U)) s) h

/-- If a map `k : K ⟶ 𝒪_X` of sheaves of modules dies in `i_* 𝒪_Z`, it dies in `(g ≫ i)_* 𝒪_Y`
for every `g : Y ⟶ Z`. This is the compatibility of the structure-sheaf maps with composition, in
the only form needed: section by section the map for `g ≫ i` is the map for `i` followed by the
map for `g`, so a section killed by the first is killed by the composite. -/
theorem comp_unitToPushforwardObjUnit_comp_eq_zero {X Y Z : LocallyRingedSpace.{u}} (g : Y ⟶ Z)
    (i : Z ⟶ X) {K : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
    (k : K ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace))
    (h : k ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toShHom) = 0) :
    k ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (g ≫ i).toShHom) = 0 := by
  ext1
  ext U s
  change (structureSheafHom g.toShHom).hom.app
      (op ((Opens.map i.toShHom.hom.base).obj U.unop))
      ((structureSheafHom i.toShHom).hom.app U (k.val.app U s)) = 0
  exact (congrArg (fun t => (structureSheafHom g.toShHom).hom.app
      (op ((Opens.map i.toShHom.hom.base).obj U.unop)) t)
    (structureSheafHom_app_map_eq_zero i k h U s)).trans (map_zero _)

variable {X Y : LocallyRingedSpace.{u}}
  {J : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
  {j : J ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace)}

/-- The ideal sheaf dies in the structure sheaf of the closed subspace it cuts out: `j` is the
inclusion of the kernel of `𝒪_X ⟶ i_* 𝒪_D`, read through the identification `D.idealIso`. -/
theorem comp_unitToPushforwardObjUnit_inclusion_eq_zero [Mono j] (D : ClosedSubspaceData X J j) :
    j ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.inclusion.toShHom) = 0 :=
  calc j ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.inclusion.toShHom)
      = D.idealIso.hom ≫ kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom D.inclusion.toShHom)) ≫
        SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.inclusion.toShHom) := by
        rw [← Category.assoc, D.idealIso_compat]
    _ = 0 := by rw [kernel.condition, comp_zero]

/-- **Stacks Project, Tag 01HP, the "only if" half.** A morphism of locally ringed spaces that
factors through the closed subspace cut out by `j` has vanishing canonical map `f^* J ⟶ 𝒪_Y`. -/
theorem pullbackIdealMap_eq_zero_of_factorsThrough [Mono j] (D : ClosedSubspaceData X J j)
    (f : Y ⟶ X) (g : Y ⟶ D.space) (hg : g ≫ D.inclusion = f) :
    pullbackIdealMap f J j = 0 := by
  subst hg
  rw [pullbackIdealMap_eq_zero_iff]
  exact comp_unitToPushforwardObjUnit_comp_eq_zero g D.inclusion j
    (comp_unitToPushforwardObjUnit_inclusion_eq_zero D)

/-- The first half of the converse: if the canonical map `f^* J ⟶ 𝒪_Y` vanishes then the image of
`f` lies in the support of `𝒪_X / J`. Indeed a section of `J` is carried to `0` in `𝒪_Y`, hence
its germ is carried to `0` by the stalk map of `f`; since a ring homomorphism carries units to
units and `0` is not a unit in the stalk of a locally ringed space, that germ is not a unit. -/
theorem range_base_subset_quotientSupport (f : Y ⟶ X) (hf : pullbackIdealMap f J j = 0) :
    Set.range f.base ⊆ quotientSupport X J j := by
  rw [pullbackIdealMap_eq_zero_iff] at hf
  rintro _ ⟨y, rfl⟩ U hx s hu
  have hs : f.c.app (op U) (j.val.app (op U) s) = 0 :=
    structureSheafHom_app_map_eq_zero f j hf (op U) s
  have h2 : f.stalkMap y (X.presheaf.germ U (f.base y) hx (j.val.app (op U) s)) = 0 :=
    (LocallyRingedSpace.stalkMap_germ_apply f U y hx _).trans
      ((congrArg (fun t => Y.presheaf.germ ((Opens.map f.base).obj U) y hx t) hs).trans
        (map_zero _))
  have h3 := (f.stalkMap y).hom.isUnit_map hu
  rw [h2] at h3
  exact zero_ne_one (isUnit_zero_iff.mp h3)

/-- A continuous map whose image lies in the image of an embedding factors continuously through
it. This is the topological content of the converse criterion. -/
theorem exists_base_factorization {Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) (f : Y ⟶ X)
    (hi : Topology.IsEmbedding i.base) (hr : Set.range f.base ⊆ Set.range i.base) :
    ∃ b : Y.toTopCat ⟶ Z.toTopCat, b ≫ i.base = f.base := by
  choose b hb using fun y : Y => hr (Set.mem_range_self y)
  have hcont : Continuous b := by
    rw [hi.isInducing.continuous_iff]
    exact (show Continuous f.base from f.base.hom.continuous).congr fun y => (hb y).symm
  exact ⟨TopCat.ofHom ⟨b, hcont⟩, TopCat.hom_ext (ContinuousMap.ext hb)⟩

/-- The first half of the converse, in its usable form: if the canonical map `f^* J ⟶ 𝒪_Y`
vanishes then the underlying continuous map of `f` factors through the closed subspace cut out by
`j`. -/
theorem exists_base_factorization_of_pullbackIdealMap_eq_zero [Mono j]
    (D : ClosedSubspaceData X J j) (f : Y ⟶ X) (hf : pullbackIdealMap f J j = 0) :
    ∃ b : Y.toTopCat ⟶ D.space.toTopCat, b ≫ D.inclusion.base = f.base :=
  exists_base_factorization D.inclusion f
    (IsClosedImmersion.isClosedEmbedding (i := D.inclusion.toShHom)).isEmbedding
    (D.range_eq_support ▸ range_base_subset_quotientSupport f hf)

/-- The map `i_* 𝒪_D ⟶ f_* 𝒪_Y` of sheaves of `𝒪_X`-modules obtained from the vanishing of the
canonical map `f^* J ⟶ 𝒪_Y`: the structure-sheaf map `𝒪_X ⟶ f_* 𝒪_Y` kills `j`, hence descends to
the quotient `𝒪_X / J`, which `D.quotientIso` identifies with `i_* 𝒪_D`. -/
noncomputable def quotientStructureSheafMap [Mono j] (D : ClosedSubspaceData X J j) {f : Y ⟶ X}
    (hf : pullbackIdealMap f J j = 0) :
    (SheafOfModules.pushforward (structureSheafHom D.inclusion.toShHom)).obj
        (SheafOfModules.unit (structureSheafRing D.space.toRingedSpace)) ⟶
      (SheafOfModules.pushforward (structureSheafHom f.toShHom)).obj
        (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) :=
  D.quotientIso.inv ≫ cokernel.desc j _ ((pullbackIdealMap_eq_zero_iff f J j).1 hf)

/-- The second half of the converse: the descended map `i_* 𝒪_D ⟶ f_* 𝒪_Y` is compatible with the
structure-sheaf maps, which is what makes it the map on structure sheaves of a factorization of
`f` through the closed subspace. -/
theorem unitToPushforwardObjUnit_comp_quotientStructureSheafMap [Mono j]
    (D : ClosedSubspaceData X J j) {f : Y ⟶ X} (hf : pullbackIdealMap f J j = 0) :
    SheafOfModules.unitToPushforwardObjUnit (structureSheafHom D.inclusion.toShHom) ≫
        quotientStructureSheafMap D hf =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f.toShHom) := by
  rw [quotientStructureSheafMap, ← D.quotientIso_compat, Category.assoc, Iso.hom_inv_id_assoc,
    cokernel.π_desc]

end Stacks.ClosedImmersion

end
