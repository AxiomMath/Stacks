module

public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedPointStalkRing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.SectionsOnASubsingletonSpace

/-!
# Modules on a ringed space with at most one point are modules over its global functions

Let `(Z, 𝒪_Z)` be a ringed space whose underlying space has at most one point.  Then

`Γ(Z, -) : Mod(𝒪_Z) ⥤ Mod(Γ(Z, 𝒪_Z))`

is an equivalence of abelian categories.

This is the identification named as missing in the implementation notes of
`Stacks.Cohomology.SupportedComplexes.sectionsAtPointStructureSheafIso`: that declaration records
the *ring* half `Γ({x}, 𝒪_X|_{\{x\}}) ≅ 𝒪_{X,x}` of the reduction to a closed point performed in
the proof of [Stacks, Tag 0G02], and
`Stacks.Cohomology.SubsingletonSections.sectionsIsoStalkFunctor` records the comparison of sections
with the stalk, but neither identifies the *category* of sheaves of modules on the one-point space
with a category of modules over a ring.  Here it is, for a space given as having at most one point
rather than built as a point: the skyscraper presentation
`Stacks.AssociatedSheaf.onePointEquivalence` does not apply to `{x} ⊆ X` with its restricted
structure sheaf.

Nothing beyond `Subsingleton Z.carrier` is assumed.  In particular the empty space is allowed:
there `Γ(Z, 𝒪_Z)` is the zero ring and both categories are zero.

## Main definitions

* `Stacks.Cohomology.SubsingletonSections.evaluationTop`: evaluation on the whole space.
* `Stacks.Cohomology.SubsingletonSections.subsingletonPresheafEquivalence`: the presheaf-level
  identification `Mod(Γ(Z, 𝒪_Z)) ≌ PresheafOfModules 𝒪_Z`.
* `Stacks.Cohomology.SubsingletonSections.subsingletonSectionsEquivalence`: **the identification**
  `Mod(Γ(Z, 𝒪_Z)) ≌ Mod(𝒪_Z)`, whose quasi-inverse is, on the nose,
  `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen Z ⊤`.

## Main results

* `Stacks.Topology.eq_bot_or_eq_top_of_subsingleton`: an open of a space with at most one point is
  `⊥` or `⊤`.
* `Stacks.Cohomology.SubsingletonSections.subsingleton_obj_of_ne_top`: a presheaf of `𝒪_Z`-modules
  has zero sections on a proper open, the scalars there being the zero ring.
* `Stacks.Cohomology.SubsingletonSections.evaluationTop_full` and
  `Stacks.Cohomology.SubsingletonSections.evaluationTop_faithful`: a presheaf of `𝒪_Z`-modules on
  such a space, and its morphisms, are determined by its sections on the whole space.
* `Stacks.Cohomology.SubsingletonSections.isEquivalence_sectionsOverOpen_top`: **sections on the
  whole space are an equivalence of abelian categories.**

## Implementation notes

The equivalence is not obtained from full faithfulness together with essential surjectivity, which
would produce the quasi-inverse by `Classical.choice`.  Instead the adjunction
`Stacks.AssociatedSheaf.presheafGlobalSectionsAdjunction` of clause (4) of [Stacks, Tag 01BH] — the
sheaf `U ↦ 𝒪_Z(U) ⊗_R M` attached to an `R`-module `M` and a ring map `R → Γ(Z, 𝒪_Z)`, left adjoint
to global sections read along that map — is taken at `R = Γ(Z, 𝒪_Z)` with the *identity* scalar
map, and its unit and counit are shown to be invertible.  So both functors of the equivalence are
explicit, exactly as for `Stacks.AssociatedSheaf.onePointPresheafEquivalence`, of which this is the
general-subsingleton analogue.

* The unit `M ⟶ Γ(Z, 𝒪_Z) ⊗_R M` is `m ↦ 1 ⊗ m` by
  `Stacks.AssociatedSheaf.presheafGlobalSectionsAdjunction_unit_app_apply`, and the scalar map is
  the identity, so `Stacks.AssociatedSheaf.bijective_one_tmul` at `RingEquiv.refl` applies.
* The counit is invertible because global sections along the identity are fully faithful.  With the
  identity scalar map, `presheafGlobalSections` *equals* evaluation at `⊤` followed by restriction
  of scalars along `RingHom.id` — an equality of functors, because the two scalar maps are equal
  by `Stacks.AssociatedSheaf.globalSectionsMap_app_top_apply` — and both factors are fully
  faithful: the second is isomorphic to the identity by `ModuleCat.restrictScalarsId'`, and the
  first is the content of `evaluationTop_full` and `evaluationTop_faithful`.

Those two are the argument of `Stacks.AssociatedSheaf.evaluationTop_full` and
`Stacks.AssociatedSheaf.evaluationTop_faithful` with the one-point space replaced by a space merely
known to be a subsingleton: there the case split is on whether the point of `PUnit` lies in the
open, here on whether the open is `⊤`, and the vanishing off `⊤` comes from the sheaf condition for
the structure sheaf (`Stacks.Cohomology.SubsingletonSections.subsingleton_structureSheafRing_bot`)
rather than from the structure sheaf being a skyscraper.

The quasi-inverse is finally replaced by `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen`
through `CategoryTheory.Equivalence.changeInverse`, so that sections on the whole space themselves
— the functor the cohomology cluster is written in terms of — carry the `IsEquivalence` instance,
as in `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence` for the skyscraper
point.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 0G02](https://stacks.math.columbia.edu/tag/0G02)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth

universe u

namespace Stacks.Topology

/-- **An open of a space with at most one point is `⊥` or `⊤`.** If it has a point it is the whole
space by `Stacks.Topology.eq_top_of_mem_of_subsingleton`, and otherwise it is empty. -/
public theorem eq_bot_or_eq_top_of_subsingleton {X : TopCat.{u}} [Subsingleton X]
    (U : Opens X) : U = ⊥ ∨ U = ⊤ := by
  by_cases h : ∃ y, y ∈ U
  · obtain ⟨y, hy⟩ := h
    exact Or.inr (eq_top_of_mem_of_subsingleton y U hy)
  · refine Or.inl ?_
    ext y
    simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
    exact fun hy => h ⟨y, hy⟩

end Stacks.Topology

namespace Stacks.Cohomology.SubsingletonSections

variable (Z : RingedSpace.{u, u}) [Subsingleton Z.carrier]

/-! ### Sections off the whole space vanish -/

/-- **A presheaf of modules on a ringed space with at most one point has zero sections on a proper
open.** Such an open is empty, so the structure sheaf has the zero ring there and a module over it
vanishes. -/
public theorem subsingleton_obj_of_ne_top
    (N : PresheafOfModules.{u} (structureSheafRing Z).obj) {U : Opens Z.carrier} (hU : U ≠ ⊤) :
    Subsingleton (N.obj (op U)) :=
  have : Subsingleton ((structureSheafRing Z).obj.obj (op U)) := by
    obtain rfl := (Stacks.Topology.eq_bot_or_eq_top_of_subsingleton U).resolve_right hU
    exact subsingleton_structureSheafRing_bot Z
  subsingleton_of_subsingleton_ring (S := (structureSheafRing Z).obj.obj (op U))

/-- **A morphism of presheaves of modules on a space with at most one point is determined by its
component on the whole space**: off `⊤` the target has zero sections. -/
public theorem hom_ext_of_app_top
    {N G : PresheafOfModules.{u} (structureSheafRing Z).obj} {f g : N ⟶ G}
    (h : f.app (op ⊤) = g.app (op ⊤)) : f = g := by
  refine PresheafOfModules.hom_ext ?_
  intro U
  by_cases hU : U.unop = ⊤
  · obtain rfl : U = op ⊤ := Opposite.unop_injective hU
    exact h
  · have := subsingleton_obj_of_ne_top Z G hU
    exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)

/-- Evaluation on the whole space, from presheaves of `𝒪_Z`-modules, with the module universe
pinned to that of the space as everywhere in the ringed-space cohomology cluster. -/
public abbrev evaluationTop :
    PresheafOfModules.{u} (structureSheafRing Z).obj ⥤
      ModuleCat.{u} ((structureSheafRing Z).obj.obj (op (⊤ : Opens Z.carrier))) :=
  PresheafOfModules.evaluation _ (op ⊤)

/-- Evaluation on the whole space is faithful on a space with at most one point. -/
public instance evaluationTop_faithful : (evaluationTop Z).Faithful where
  map_injective h := hom_ext_of_app_top Z h

/-- **Evaluation on the whole space is full on a space with at most one point.** A linear map on
sections over `⊤` is extended by zero to the only other open, and the naturality square over a
proper open has zero target. -/
public instance evaluationTop_full : (evaluationTop Z).Full where
  map_surjective {N G} h := by
    classical
    let app : ∀ U, N.obj U ⟶ G.obj U := fun U ↦
      if hU : U.unop = ⊤ then (Opposite.unop_injective hU : U = op ⊤) ▸ h else 0
    have happ : app (op ⊤) = h := dif_pos rfl
    refine ⟨⟨app, ?_⟩, happ⟩
    intro U V i
    by_cases hV : V.unop = ⊤
    · have hU : U.unop = ⊤ := top_le_iff.mp (by rw [← hV]; exact i.unop.le)
      obtain rfl : U = op ⊤ := Opposite.unop_injective hU
      obtain rfl : V = op ⊤ := Opposite.unop_injective hV
      obtain rfl : i = 𝟙 _ := Subsingleton.elim _ _
      rw [happ]
      simp only [PresheafOfModules.map_id]
      exact ((ModuleCat.restrictScalarsId' _ _).inv.naturality h).symm
    · exact ModuleCat.hom_ext
        (LinearMap.ext fun _ ↦ (subsingleton_obj_of_ne_top Z G hV).elim _ _)

/-! ### Global sections along the identity -/

/-- Restriction of scalars along the identity is an equivalence, being isomorphic to the identity
functor. -/
public theorem isEquivalence_restrictScalars_id {R : Type u} [Ring R] :
    (ModuleCat.restrictScalars.{u} (RingHom.id R)).IsEquivalence :=
  Functor.isEquivalence_of_iso (ModuleCat.restrictScalarsId' (RingHom.id R) rfl).symm

attribute [local instance] isEquivalence_restrictScalars_id

/-- **The scalar map of construction (3) of [Stacks, Tag 01BH] at the identity is the identity.**
-/
public theorem globalSectionsMap_id_app_top :
    ((globalSectionsMap Z (RingHom.id (baseRing Z))).app (op ⊤)).hom =
      RingHom.id (baseRing Z) :=
  RingHom.ext (globalSectionsMap_app_top_apply Z (RingHom.id (baseRing Z)))

/-- **Global sections along the identity scalar map are evaluation on the whole space**, up to
restriction of scalars along `RingHom.id`.  The two functors are *equal*: they differ only in the
ring map along which scalars are restricted, and those are equal by
`Stacks.Cohomology.SubsingletonSections.globalSectionsMap_id_app_top`. -/
public theorem presheafGlobalSections_id_eq :
    presheafGlobalSections.{u, u} Z (RingHom.id (baseRing Z)) =
      evaluationTop Z ⋙ ModuleCat.restrictScalars (RingHom.id (baseRing Z)) :=
  congrArg (fun g ↦ evaluationTop Z ⋙ ModuleCat.restrictScalars g)
    (globalSectionsMap_id_app_top Z)

/-- Global sections along the identity scalar map are full on a space with at most one point. -/
public instance presheafGlobalSections_id_full :
    (presheafGlobalSections.{u, u} Z (RingHom.id (baseRing Z))).Full := by
  rw [presheafGlobalSections_id_eq]
  infer_instance

/-- Global sections along the identity scalar map are faithful on a space with at most one
point. -/
public instance presheafGlobalSections_id_faithful :
    (presheafGlobalSections.{u, u} Z (RingHom.id (baseRing Z))).Faithful := by
  rw [presheafGlobalSections_id_eq]
  infer_instance

/-- **The counit of the adjunction at the identity scalar map is invertible**, global sections
along the identity being fully faithful. -/
public instance isIso_subsingletonAdjunction_counit :
    IsIso ((presheafGlobalSectionsAdjunction.{u, u} Z (RingHom.id (baseRing Z))).counit) :=
  Adjunction.counit_isIso_of_R_fully_faithful
    (R := presheafGlobalSections.{u, u} Z (RingHom.id (baseRing Z))) _

/-- **The unit of the adjunction at the identity scalar map is invertible.** It is
`m ↦ 1 ⊗ m : M ⟶ Γ(Z, 𝒪_Z) ⊗_R M` with `R = Γ(Z, 𝒪_Z)` acting through the identity, hence
bijective by `Stacks.AssociatedSheaf.bijective_one_tmul`. -/
public instance isIso_subsingletonAdjunction_unit_app (M : ModuleCat.{u} (baseRing Z)) :
    IsIso ((presheafGlobalSectionsAdjunction.{u, u} Z (RingHom.id (baseRing Z))).unit.app M) := by
  let := ((globalSectionsMap Z (RingHom.id (baseRing Z))).app (op ⊤)).hom.toAlgebra
  have he : ∀ r, algebraMap ((constantRingPresheaf Z (baseRing Z)).obj (op ⊤))
      (Z.presheaf.obj (op (⊤ : Opens Z.carrier))) r = (RingEquiv.refl (baseRing Z)) r := fun r ↦
    globalSectionsMap_app_top_apply Z (RingHom.id (baseRing Z)) r
  have hb : Function.Bijective (fun m : M ↦
      (1 : Z.presheaf.obj (op (⊤ : Opens Z.carrier))) ⊗ₜ[
        (constantRingPresheaf Z (baseRing Z)).obj (op ⊤)] m) :=
    bijective_one_tmul (RingEquiv.refl (baseRing Z)) he
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : (fun m : M ↦ ((presheafGlobalSectionsAdjunction.{u, u} Z
        (RingHom.id (baseRing Z))).unit.app M).hom m) =
      (fun m : M ↦ (1 : Z.presheaf.obj (op (⊤ : Opens Z.carrier))) ⊗ₜ[
        (constantRingPresheaf Z (baseRing Z)).obj (op ⊤)] m) :=
    funext fun m ↦ presheafGlobalSectionsAdjunction_unit_app_apply _ _ M m
  change Function.Bijective (fun m : M ↦ ((presheafGlobalSectionsAdjunction.{u, u} Z
    (RingHom.id (baseRing Z))).unit.app M).hom m)
  rw [hfun]
  exact hb

/-- The unit of the adjunction at the identity scalar map is a natural isomorphism. -/
public instance isIso_subsingletonAdjunction_unit :
    IsIso ((presheafGlobalSectionsAdjunction.{u, u} Z (RingHom.id (baseRing Z))).unit) :=
  NatIso.isIso_of_isIso_app _

/-! ### The identification -/

/-- **Modules over the global functions are presheaves of modules, on a space with at most one
point**: the two functors are construction (3) of [Stacks, Tag 01BH] at the identity scalar map
and sections on the whole space. -/
public def subsingletonPresheafEquivalence :
    ModuleCat.{u} (baseRing Z) ≌ PresheafOfModules.{u} (structureSheafRing Z).obj :=
  (presheafGlobalSectionsAdjunction.{u, u} Z (RingHom.id (baseRing Z))).toEquivalence

/-- The quasi-inverse of the presheaf-level identification is evaluation on the whole space. -/
public theorem subsingletonPresheafEquivalence_inverse :
    (subsingletonPresheafEquivalence Z).inverse =
      evaluationTop Z ⋙ ModuleCat.restrictScalars (RingHom.id (baseRing Z)) :=
  presheafGlobalSections_id_eq Z

/-- **Modules on a ringed space with at most one point are modules over its global functions**:

`Mod(Γ(Z, 𝒪_Z)) ≌ Mod(𝒪_Z)`,

the quasi-inverse being, on the nose, sections on the whole space.  The only hypothesis is
`Subsingleton Z.carrier`. -/
public def subsingletonSectionsEquivalence :
    ModuleCat.{u} (baseRing Z) ≌ SheafOfModules.{u} (structureSheafRing Z) :=
  ((subsingletonPresheafEquivalence Z).trans
      (subsingletonForgetEquivalence Z).symm).changeInverse
    (eqToIso (congrArg (fun F ↦ SheafOfModules.forget (structureSheafRing Z) ⋙ F)
        (subsingletonPresheafEquivalence_inverse Z)) ≪≫
      Functor.isoWhiskerLeft (sectionsOverOpen Z ⊤)
        (ModuleCat.restrictScalarsId' (RingHom.id (baseRing Z)) rfl) ≪≫
      (sectionsOverOpen Z ⊤).rightUnitor)

/-- The quasi-inverse of the identification is sections on the whole space. -/
public theorem subsingletonSectionsEquivalence_inverse :
    (subsingletonSectionsEquivalence Z).inverse = sectionsOverOpen Z ⊤ := rfl

/-- **Sections on the whole space of a ringed space with at most one point are an equivalence of
abelian categories**, hence exact and additive. -/
public instance isEquivalence_sectionsOverOpen_top : (sectionsOverOpen Z ⊤).IsEquivalence :=
  (subsingletonSectionsEquivalence Z).isEquivalence_inverse

end Stacks.Cohomology.SubsingletonSections

end
