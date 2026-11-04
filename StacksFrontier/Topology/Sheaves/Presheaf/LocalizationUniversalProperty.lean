module

public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Topology.Sheaves.Sheafify
import StacksCore.Tactic.StacksAttribute

/-!
# The universal property of a sectionwise localization of a presheaf of rings

Let `O` be a presheaf of commutative rings on a space `X` and let `S` be a restriction-stable
multiplicative subpresheaf of `O`. Mathlib's `S.localizationPresheaf` localizes the sections of
`O` at those of `S`, with canonical map `S.toLocalizationPresheaf : O ⟶ S.localizationPresheaf`.

This file proves that this map is universal: a morphism `f : O ⟶ A` of presheaves of commutative
rings which inverts every section of `S` factors through `S.localizationPresheaf`, and does so
through a unique morphism of presheaves. Sheafifying, the same holds for sheaves: the
sheafification of `S.localizationPresheaf` is universal among sheaves of rings receiving a map
from the sheafification of `O` which inverts the prescribed sections.

The first assertion of Stacks 01D0 — that there is a canonical morphism `O ⟶ O_S` of presheaves
of rings inverting the sections of `S` — is Mathlib's
`TopCat.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf` together with
`IsLocalization.map_units` applied on each open; nothing is redefined for it here, and the tag
is recorded on those two declarations at the end of this file.

## Main definitions

* `Stacks.Presheaf.Localization.toLocalizationSheaf`: the morphism of sheaves of rings obtained
  by sheafifying `S.toLocalizationPresheaf`.

## Main results

* `Stacks.Presheaf.Localization.existsUnique_lift_localizationPresheaf`: the universal property
  of the sectionwise localization, as a presheaf of rings.
* `Stacks.Presheaf.Localization.isUnit_toLocalizationSheaf`: every prescribed section becomes a
  unit in the sheafified localization.
* `Stacks.Presheaf.Localization.existsUnique_lift_localizationSheaf`: the universal property of
  the sheafified localization.

## Implementation notes

The condition on a morphism is imposed open by open, on each section of `S` there, and the
factorization equation is an equality of natural transformations, so it already includes
compatibility with all restriction maps; nothing further has to be said about functoriality.

At the presheaf level the lift is built from `IsLocalization.lift` on each open, and its
uniqueness from `IsLocalization.ringHom_ext`: a ring map out of a localization is determined by
its restriction along `algebraMap`. At the sheaf level the lift is the composite of that
presheaf lift with `CategoryTheory.sheafifyLift`, and uniqueness follows from
`CategoryTheory.sheafify_hom_ext` together with the presheaf-level uniqueness.

The ringed-site analogue of these statements, for a restriction-stable family of multiplicative
subsets of the structure sheaf of an arbitrary ringed site, is Tag 0EMC and lives in
`StacksDraft.Ch18.Sec44.LocalizationOfStructureSheaf`; it is a different construction, since
there the structure sheaf is a sheaf and the site is arbitrary, so neither statement specializes
to the other.

## References

* [Stacks Project, Section 01D0](https://stacks.math.columbia.edu/tag/01D0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TopCat

namespace Stacks.Presheaf.Localization

universe u

variable {X : TopCat.{u}} {O A : X.Presheaf CommRingCat.{u}}

/-- **Stacks 01D0.** A morphism of presheaves of commutative rings which inverts every section
of the multiplicative subpresheaf `S` factors uniquely through the sectionwise localization at
`S`. -/
@[stacks 01D0 "presheaf_universal_property", ega "0 1.2.4" "more general"]
theorem existsUnique_lift_localizationPresheaf (S : O.SubmonoidPresheaf) (f : O ⟶ A)
    (hf : ∀ (U : (Opens X)ᵒᵖ) (s : S.obj U), IsUnit ((f.app U).hom (s : O.obj U))) :
    ∃! g : S.localizationPresheaf ⟶ A, S.toLocalizationPresheaf ≫ g = f := by
  let g : S.localizationPresheaf ⟶ A :=
    { app := fun U =>
        CommRingCat.ofHom <| IsLocalization.lift (M := S.obj U) (g := (f.app U).hom) (hf U)
      naturality := by
        intro U V i
        apply CommRingCat.hom_ext
        apply IsLocalization.ringHom_ext (M := S.obj U)
        ext x
        show (IsLocalization.lift (M := S.obj V) (g := (f.app V).hom) (hf V))
            (IsLocalization.map (Localization (S.obj V)) (O.map i).hom (S.map i)
              (algebraMap (O.obj U) (Localization (S.obj U)) x)) =
          (A.map i).hom ((IsLocalization.lift (M := S.obj U) (g := (f.app U).hom) (hf U))
            (algebraMap (O.obj U) (Localization (S.obj U)) x))
        simp only [IsLocalization.map_eq, IsLocalization.lift_eq]
        exact congrArg (fun k : O.obj U ⟶ A.obj V => k x) (NatTrans.naturality f i) }
  have hcomp (U : (Opens X)ᵒᵖ) :
      (IsLocalization.lift (M := S.obj U) (g := (f.app U).hom) (hf U)).comp
        (algebraMap (O.obj U) (Localization (S.obj U))) = (f.app U).hom :=
    IsLocalization.lift_comp (hf U)
  refine ⟨g, NatTrans.ext (funext fun U => CommRingCat.hom_ext (hcomp U)),
    fun h hh => NatTrans.ext (funext fun U => CommRingCat.hom_ext ?_)⟩
  apply IsLocalization.ringHom_ext (M := S.obj U)
  have hhU := congrArg (fun k : O ⟶ A => (k.app U).hom) hh
  rw [NatTrans.comp_app, CommRingCat.hom_comp] at hhU
  exact hhU.trans (hcomp U).symm

/-- The canonical map from the sheafification of a presheaf of commutative rings to the
sheafification of its sectionwise localization. -/
@[stacks 01D0 "sheaf_universal_property"]
noncomputable def toLocalizationSheaf (S : O.SubmonoidPresheaf) :
    (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj O ⟶
      (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
        S.localizationPresheaf :=
  (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).map S.toLocalizationPresheaf

/-- Naturality of the sheafification unit at `S.toLocalizationPresheaf`: going into the
sheafified localization through `O` or through `S.localizationPresheaf` gives the same map. -/
private theorem toSheafify_comp_toLocalizationSheaf (S : O.SubmonoidPresheaf) :
    toSheafify (Opens.grothendieckTopology X) O ≫ (toLocalizationSheaf S).hom =
      S.toLocalizationPresheaf ≫
        toSheafify (Opens.grothendieckTopology X) S.localizationPresheaf :=
  ((toSheafification (Opens.grothendieckTopology X) CommRingCat.{u}).naturality
    S.toLocalizationPresheaf).symm

/-- **Stacks 01D0.** Every prescribed local denominator becomes invertible in the sheafified
localization. -/
@[stacks 01D0 "sheaf_universal_property"]
theorem isUnit_toLocalizationSheaf (S : O.SubmonoidPresheaf) (U : (Opens X)ᵒᵖ) (s : S.obj U) :
    IsUnit (((toLocalizationSheaf S).hom.app U).hom
      (((toSheafify (Opens.grothendieckTopology X) O).app U).hom (s : O.obj U))) := by
  rw [← CommRingCat.comp_apply, ← NatTrans.comp_app, toSheafify_comp_toLocalizationSheaf,
    NatTrans.comp_app, CommRingCat.comp_apply]
  exact (IsLocalization.map_units (M := S.obj U) (Localization (S.obj U)) s).map _

/-- **Stacks 01D0.** A morphism out of the sheafification of `O` which inverts every prescribed
section factors uniquely through the sheafified localization. -/
@[stacks 01D0 "sheaf_universal_property"]
theorem existsUnique_lift_localizationSheaf (S : O.SubmonoidPresheaf) (A : X.Sheaf CommRingCat.{u})
    (f : (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj O ⟶ A)
    (hf : ∀ (U : (Opens X)ᵒᵖ) (s : S.obj U),
      IsUnit ((f.hom.app U).hom
        (((toSheafify (Opens.grothendieckTopology X) O).app U).hom (s : O.obj U)))) :
    ∃! g : (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
        S.localizationPresheaf ⟶ A,
      toLocalizationSheaf S ≫ g = f := by
  set J := Opens.grothendieckTopology X
  obtain ⟨g₀, hg₀, huniq₀⟩ :=
    existsUnique_lift_localizationPresheaf S (toSheafify J O ≫ f.hom) hf
  refine ⟨⟨sheafifyLift J g₀ A.property⟩, ?_, ?_⟩
  · apply CategoryTheory.Sheaf.hom_ext
    show sheafifyMap J S.toLocalizationPresheaf ≫ sheafifyLift J g₀ A.property = f.hom
    rw [sheafifyMap_sheafifyLift]
    refine CategoryTheory.sheafify_hom_ext _ _ _ A.property ?_
    simpa only [toSheafify_sheafifyLift] using hg₀
  · intro h hh
    apply CategoryTheory.Sheaf.hom_ext
    refine CategoryTheory.sheafify_hom_ext _ _ _ A.property ?_
    refine (huniq₀ _ ?_).trans (toSheafify_sheafifyLift J g₀ A.property).symm
    show S.toLocalizationPresheaf ≫ toSheafify J S.localizationPresheaf ≫ h.hom =
      toSheafify J O ≫ f.hom
    rw [← Category.assoc, ← toSheafify_comp_toLocalizationSheaf, Category.assoc]
    exact congrArg (fun k : _ ⟶ A => toSheafify J O ≫ k.hom) hh

end Stacks.Presheaf.Localization

add_to_stacks 01D0 "localization_map: the canonical morphism to the sectionwise localization"
  TopCat.Presheaf.SubmonoidPresheaf.toLocalizationPresheaf
add_to_stacks 01D0 "localization_map: every prescribed section becomes a unit"
  IsLocalization.map_units

end
