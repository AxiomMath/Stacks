module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import StacksFrontier.Topology.Sheaves.Presheaf.Localization
public import Mathlib.Topology.Sheaves.Sheafify
import StacksCore.Tactic.StacksAttribute

/-!
# Stalks of the sectionwise localization of a presheaf of rings

Let `O` be a presheaf of commutative rings on a space `X` and let `S` be a restriction-stable
multiplicative subpresheaf of `O`. Localizing the sections of `O` at those of `S` gives a
presheaf of rings `S.localizationPresheaf` and a canonical morphism
`S.toLocalizationPresheaf : O ⟶ S.localizationPresheaf`. The stalk at a point `x` of
`S.localizationPresheaf`, and of its sheafification, is the localization of the stalk `O_x` at
the submonoid of germs which are locally represented by sections of `S`.

## Main definitions

* `TopCat.Presheaf.SubmonoidPresheaf.stalk`: the multiplicative subset of `O_x` of germs
  represented, on some neighbourhood of `x`, by a section of `S`.
* `Stacks.Presheaf.Localization.localizationSheaf`: the sheafification of the sectionwise
  localization.
* `Stacks.Presheaf.Localization.toLocalizationSheafStalk`: the induced map from the stalk of `O`
  to the stalk of that sheafification.

## Main results

* `Stacks.Presheaf.Localization.localizationPresheaf_stalk_isLocalization`: the stalk of
  `S.localizationPresheaf` at `x` is the localization of `O_x` at `S.stalk x`, for the algebra
  structure induced by the stalk map of `S.toLocalizationPresheaf`.
* `Stacks.Presheaf.Localization.isLocalization_stalk_localizationSheaf`: the canonical map
  exhibits the stalk of the sheafified localization as the localization of `O_x` at `S.stalk x`.

## Implementation notes

Both identifications are stated through `IsLocalization`, for the algebra structure induced by
the canonical map on stalks, so they identify that map as a localization map rather than only
asserting that an abstract ring isomorphism exists.

## References

* [Stacks Project, Section 01D0](https://stacks.math.columbia.edu/tag/01D0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TopCat.Presheaf.SubmonoidPresheaf

variable {X : TopCat.{u}} {O : X.Presheaf CommRingCat.{u}}

/-- The multiplicative subset of the stalk `O_x` consisting of the germs represented, on some
open neighbourhood `U` of `x`, by a section belonging to `S(U)`. -/
noncomputable def stalk (S : O.SubmonoidPresheaf) (x : X) : Submonoid (O.stalk x) :=
  ⨆ (U : Opens X) (hx : x ∈ U), (S.obj (op U)).map (O.germ U x hx).hom

/-- The germ at `x` of a section of `S(U)` belongs to the stalk submonoid `S.stalk x`. -/
private theorem germ_mem_stalk (S : O.SubmonoidPresheaf) {U : Opens X} {x : X} (hx : x ∈ U)
    {s : O.obj (op U)} (hs : s ∈ S.obj (op U)) : O.germ U x hx s ∈ S.stalk x :=
  Submonoid.mem_iSup_of_mem U (Submonoid.mem_iSup_of_mem hx (Submonoid.mem_map_of_mem _ hs))

end TopCat.Presheaf.SubmonoidPresheaf

namespace Stacks.Presheaf.Localization

open TopCat

/-- The stalk of a sectionwise localization of a presheaf of rings is a localization of the
original stalk at the germs of the prescribed denominators. -/
theorem localizationPresheaf_stalk_isLocalization
    (D : PresheafLocalizationData.{u}) (x : D.X) :
    letI : Algebra (D.O.stalk x) (D.S.localizationPresheaf.stalk x) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        D.S.toLocalizationPresheaf).hom.toAlgebra
    IsLocalization (D.S.stalk x) (D.S.localizationPresheaf.stalk x) := by
  let : Algebra (D.O.stalk x) (D.S.localizationPresheaf.stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map D.S.toLocalizationPresheaf).hom.toAlgebra
  show IsLocalization (D.S.stalk x) (D.S.localizationPresheaf.stalk x)
  let f := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map D.S.toLocalizationPresheaf).hom
  have hf (U : Opens D.X) (hx : x ∈ U) (s : D.O.obj (op U)) :
      f (D.O.germ U x hx s) = D.S.localizationPresheaf.germ U x hx (algebraMap _ _ s) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx D.S.toLocalizationPresheaf s
  have hunit : D.S.stalk x ≤ (IsUnit.submonoid (D.S.localizationPresheaf.stalk x)).comap
      (algebraMap (D.O.stalk x) (D.S.localizationPresheaf.stalk x)) := by
    refine iSup_le fun U => iSup_le fun hx => ?_
    rw [Submonoid.map_le_iff_le_comap]
    intro s hs
    show IsUnit (f (D.O.germ U x hx s))
    rw [hf]
    exact IsUnit.map (D.S.localizationPresheaf.germ U x hx).hom
      (IsLocalization.map_units _ ⟨s, hs⟩)
  rw [isLocalization_iff]
  refine ⟨fun y => hunit y.property, ?_, ?_⟩
  · intro z
    obtain ⟨U, hx, zU, hz⟩ := Presheaf.exists_germ_eq D.S.localizationPresheaf z
    rw [← hz]
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (D.S.obj (op U)) zU
    refine ⟨⟨D.O.germ U x hx a, ?_⟩, ?_⟩
    · exact ⟨D.O.germ U x hx s, D.S.germ_mem_stalk hx s.property⟩
    · show _ * f (D.O.germ U x hx s) = f (D.O.germ U x hx a)
      rw [hf, hf]
      show (D.S.localizationPresheaf.germ U x hx).hom zU *
        (D.S.localizationPresheaf.germ U x hx).hom
        (algebraMap (D.O.obj (op U)) (D.S.localizationPresheaf.obj (op U)) s) =
        (D.S.localizationPresheaf.germ U x hx).hom
          (algebraMap (D.O.obj (op U)) (D.S.localizationPresheaf.obj (op U)) a)
      simpa only [map_mul] using congrArg (D.S.localizationPresheaf.germ U x hx).hom hs
  · intro a b hab
    obtain ⟨U, hxU, aU, ha⟩ := Presheaf.exists_germ_eq D.O a
    obtain ⟨V, hxV, bV, hb⟩ := Presheaf.exists_germ_eq D.O b
    let U' : OpenNhds x := ⟨U, hxU⟩
    let V' : OpenNhds x := ⟨V, hxV⟩
    rw [← ha, ← hb] at hab
    change f _ = f _ at hab
    rw [hf U hxU aU, hf V hxV bV] at hab
    change colimit.ι ((OpenNhds.inclusion x).op ⋙ D.S.localizationPresheaf) (op U') _ =
      colimit.ι ((OpenNhds.inclusion x).op ⋙ D.S.localizationPresheaf) (op V') _ at hab
    obtain ⟨W, i, j, hij⟩ := CategoryTheory.Limits.Concrete.colimit_exists_of_rep_eq
      (i := op U') (j := op V') ((OpenNhds.inclusion x).op ⋙ D.S.localizationPresheaf)
      (D.S.toLocalizationPresheaf.app (op U) aU)
      (D.S.toLocalizationPresheaf.app (op V) bV) hab
    change ({ U : Opens D.X // x ∈ U })ᵒᵖ at W
    let i' : op U ⟶ op W.unop.1 := i.unop.op
    let j' : op V ⟶ op W.unop.1 := j.unop.op
    change D.S.localizationPresheaf.map i' (D.S.toLocalizationPresheaf.app (op U) aU) =
      D.S.localizationPresheaf.map j' (D.S.toLocalizationPresheaf.app (op V) bV) at hij
    rw [← NatTrans.naturality_apply (X := op U) (Y := op W.unop.1)
        D.S.toLocalizationPresheaf i' aU,
      ← NatTrans.naturality_apply (X := op V) (Y := op W.unop.1)
        D.S.toLocalizationPresheaf j' bV] at hij
    obtain ⟨c, hloc⟩ := (IsLocalization.eq_iff_exists (D.S.obj (op W.unop.1))
      (D.S.localizationPresheaf.obj (op W.unop.1))).mp hij
    refine ⟨⟨D.O.germ W.unop.1 x W.unop.2 c, ?_⟩, ?_⟩
    · exact D.S.germ_mem_stalk W.unop.2 c.property
    · rw [← ha, ← hb]
      have h := congrArg (D.O.germ W.unop.1 x W.unop.2).hom hloc
      rwa [map_mul, map_mul, D.O.germ_res_apply' i' x W.unop.2 aU,
        D.O.germ_res_apply' j' x W.unop.2 bV] at h

end Stacks.Presheaf.Localization

end

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace
open TopCat TopCat.Presheaf

namespace Stacks.Presheaf.Localization

/-- The sheafification of the presheaf obtained by localizing the sections of `O` at the
multiplicative subpresheaf `S`. -/
noncomputable def localizationSheaf (D : PresheafLocalizationData.{u}) :
    D.X.Sheaf CommRingCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology D.X) CommRingCat.{u}).obj
    D.S.localizationPresheaf

/-- The canonical map from the stalk of `O` to the stalk of the sheafified sectionwise
localization. -/
noncomputable def toLocalizationSheafStalk (D : PresheafLocalizationData.{u}) (x : D.X) :
    D.O.stalk x ⟶ (localizationSheaf D).presheaf.stalk x :=
  (stalkFunctor CommRingCat x).map
    (D.S.toLocalizationPresheaf ≫
      CategoryTheory.toSheafify (Opens.grothendieckTopology D.X) D.S.localizationPresheaf)

/-- At every point, the stalk of the sheafification of the sectionwise localization is the
localization of the original stalk at the germs of the prescribed denominators. -/
@[stacks 01D0 "sheaf_localization_stalk"]
lemma isLocalization_stalk_localizationSheaf (D : PresheafLocalizationData.{u}) (x : D.X) :
    letI : Algebra (D.O.stalk x) ((localizationSheaf D).presheaf.stalk x) :=
      (toLocalizationSheafStalk D x).hom.toAlgebra
    IsLocalization (D.S.stalk x) ((localizationSheaf D).presheaf.stalk x) := by
  let : Algebra (D.O.stalk x) ((localizationSheaf D).presheaf.stalk x) :=
    (toLocalizationSheafStalk D x).hom.toAlgebra
  show IsLocalization (D.S.stalk x) ((localizationSheaf D).presheaf.stalk x)
  let : Algebra (D.O.stalk x) (D.S.localizationPresheaf.stalk x) :=
    ((stalkFunctor CommRingCat x).map D.S.toLocalizationPresheaf).hom.toAlgebra
  have := localizationPresheaf_stalk_isLocalization D x
  let f := (stalkFunctor CommRingCat x).map
    (toSheafify (Opens.grothendieckTopology D.X) D.S.localizationPresheaf)
  have : IsIso f :=
    stalkFunctor_map_unit_toSheafify_isIso x CommRingCat D.S.localizationPresheaf
  let e : D.S.localizationPresheaf.stalk x ≃ₐ[D.O.stalk x]
      (localizationSheaf D).presheaf.stalk x :=
    { (asIso f).commRingCatIsoToRingEquiv with
      commutes' := fun r => by
        show _ = ((stalkFunctor CommRingCat x).map (D.S.toLocalizationPresheaf ≫ _)).hom r
        rw [Functor.map_comp]
        rfl }
  exact IsLocalization.isLocalization_of_algEquiv (M := D.S.stalk x) e

end Stacks.Presheaf.Localization

add_to_stacks 01D0 "presheaf_localization_stalk: the stalk of the localization presheaf"
  Stacks.Presheaf.Localization.localizationPresheaf_stalk_isLocalization

end
