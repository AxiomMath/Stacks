module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPoints
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.SigmaPoints
public import StacksFrontier.Topology.Irreducible.GenericPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stability properties of birational morphisms

Birationality of a morphism of schemes is a condition on generic points of irreducible
components and on the local rings there. Both halves of that condition are inherited by
composites, by restrictions to an open of the target, and by coproducts.

## Main results

* `AlgebraicGeometry.IsBirational.comp`: a composite of birational morphisms is birational.
* `AlgebraicGeometry.IsBirational.morphismRestrict`: the restriction of a birational morphism
  over an open subscheme of the target is birational.
* `AlgebraicGeometry.isBirational_of_isIso_morphismRestrict`: conversely, a morphism which is an
  isomorphism over an open of the target containing the generic points of both schemes is
  birational.
* `AlgebraicGeometry.isBirational_sigmaMap`: a coproduct of birational morphisms is birational.
* `AlgebraicGeometry.mem_genericPoints_sigmaι_iff`: a point of a summand of a coproduct of
  schemes is a generic point of an irreducible component of the coproduct exactly when it is
  one of its own summand.

## References

* [Stacks Project, Tag 01RO](https://stacks.math.columbia.edu/tag/01RO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point of an open subscheme is a generic point of an irreducible component of that open
subscheme exactly when it is a generic point of an irreducible component of the ambient
scheme. -/
private theorem mem_genericPoints_opens_iff {X : Scheme.{u}} (U : X.Opens) (x : U.toScheme) :
    x ∈ genericPoints U.toScheme ↔ x.1 ∈ genericPoints X := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · simpa only [Scheme.genericPointsInOpenEquiv_symm_val X U ⟨x, hx⟩] using
      ((Scheme.genericPointsInOpenEquiv X U).symm ⟨x, hx⟩).1.2
  · have h := (Scheme.genericPointsInOpenEquiv X U ⟨⟨x.1, hx⟩, x.2⟩).2
    rwa [show (Scheme.genericPointsInOpenEquiv X U ⟨⟨x.1, hx⟩, x.2⟩).1 = x from
      Subtype.ext (Scheme.genericPointsInOpenEquiv_val X U ⟨⟨x.1, hx⟩, x.2⟩)] at h

/-- The stalk map of `f ∣_ U` at a point is an isomorphism iff the stalk map of `f` there is. -/
private theorem isIso_stalkMap_morphismRestrict_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (x : f ⁻¹ᵁ U) : IsIso ((f ∣_ U).stalkMap x) ↔ IsIso (f.stalkMap x.1) :=
  MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _) (morphismRestrictStalkMap f U x)

/-- A point of a summand of a coproduct of schemes is a generic point of an irreducible
component of the coproduct if and only if it is one of its own summand. -/
theorem mem_genericPoints_sigmaι_iff {ι : Type u} [Small.{u} ι] (Y : ι → Scheme.{u}) (i : ι)
    (x : Y i) :
    (Sigma.ι Y i x ∈ genericPoints (∐ Y : Scheme.{u})) ↔ x ∈ genericPoints (Y i) :=
  ⟨fun hx ↦ (mem_genericPoints_iff_forall_specializes_eq x).2 fun _ hx' ↦
      (Sigma.ι Y i).isOpenEmbedding.injective
        ((mem_genericPoints_iff_forall_specializes_eq _).1 hx _
          ((Sigma.ι Y i).base.hom.map_specializes hx')),
    mem_genericPoints_of_generalizingMap (Sigma.ι Y i).isOpenEmbedding.generalizingMap⟩

/-- Birationality is stable under composition. -/
theorem IsBirational.comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsBirational f) (hg : IsBirational g) : IsBirational (f ≫ g) := by
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ?_ ?_
  · have h : (⇑(f ≫ g) : X → Z) = ⇑g ∘ ⇑f := funext fun x ↦ Scheme.Hom.comp_apply f g x
    rw [h]
    exact hg.bijOn.comp hf.bijOn
  · intro x hx
    rw [Scheme.Hom.stalkMap_comp]
    exact IsIso.comp_isIso' (hg.isIso_stalkMap _ (hf.bijOn.mapsTo hx)) (hf.isIso_stalkMap x hx)

/-- Birationality is stable under restriction to an open subscheme of the target. -/
theorem IsBirational.morphismRestrict {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirational f) (U : Y.Opens) : IsBirational (f ∣_ U) := by
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ⟨?_, ?_, ?_⟩ ?_
  · intro x hx
    rw [mem_genericPoints_opens_iff] at hx ⊢
    rw [morphismRestrict_base_coe]
    exact hf.bijOn.mapsTo hx
  · intro x hx y hy hxy
    refine Subtype.ext (hf.bijOn.injOn ((mem_genericPoints_opens_iff _ _).1 hx)
      ((mem_genericPoints_opens_iff _ _).1 hy) ?_)
    rw [← morphismRestrict_base_coe f U x, ← morphismRestrict_base_coe f U y, hxy]
  · intro y hy
    obtain ⟨x, hx, hfx⟩ := hf.bijOn.surjOn ((mem_genericPoints_opens_iff _ _).1 hy)
    have hxU : x ∈ f ⁻¹ᵁ U := show f x ∈ U from hfx ▸ y.2
    exact ⟨⟨x, hxU⟩, (mem_genericPoints_opens_iff _ ⟨x, hxU⟩).2 hx,
      Subtype.ext ((morphismRestrict_base_coe f U _).trans hfx)⟩
  · intro x hx
    exact (isIso_stalkMap_morphismRestrict_iff f U x).2
      (hf.isIso_stalkMap x.1 ((mem_genericPoints_opens_iff _ _).1 hx))

/-- **Birationality is detected on an open containing the generic points.** A morphism which is
an isomorphism over an open subscheme `U` of its target is birational as soon as `U` contains
every generic point of the target and its inverse image contains every generic point of the
source. -/
@[ega "I 6.5.5" "(ii), special case"]
theorem isBirational_of_isIso_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (hU : IsIso (f ∣_ U))
    (hX : ∀ x : X, x ∈ genericPoints X → f x ∈ U)
    (hY : ∀ y : Y, y ∈ genericPoints Y → y ∈ U) :
    IsBirational f := by
  let : IsIso (f ∣_ U) := hU
  have hmap (z : (f ⁻¹ᵁ U).toScheme) : ((f ∣_ U) z).1 = f z.1 := morphismRestrict_base_coe f U z
  have hmem : ∀ x : X, x ∈ genericPoints X → x ∈ f ⁻¹ᵁ U := hX
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ⟨?_, ?_, ?_⟩ ?_
  · intro x hx
    have hz : (⟨x, hmem x hx⟩ : (f ⁻¹ᵁ U).toScheme) ∈ genericPoints (f ⁻¹ᵁ U).toScheme :=
      (mem_genericPoints_opens_iff _ _).2 hx
    have := (mem_genericPoints_opens_iff U
      ((f ∣_ U) (⟨x, hmem x hx⟩ : (f ⁻¹ᵁ U).toScheme))).1
      ((f ∣_ U).homeomorph.mem_genericPoints hz)
    rwa [hmap ⟨x, hmem x hx⟩] at this
  · intro x hx x' hx' hxx'
    have hz : (f ∣_ U) (⟨x, hmem x hx⟩ : (f ⁻¹ᵁ U).toScheme) =
        (f ∣_ U) (⟨x', hmem x' hx'⟩ : (f ⁻¹ᵁ U).toScheme) :=
      Subtype.ext ((hmap ⟨x, hmem x hx⟩).trans (hxx'.trans (hmap ⟨x', hmem x' hx'⟩).symm))
    exact congrArg Subtype.val ((f ∣_ U).homeomorph.injective hz)
  · intro y hy
    have hw : (⟨y, hY y hy⟩ : U.toScheme) ∈ genericPoints U.toScheme :=
      (mem_genericPoints_opens_iff _ _).2 hy
    refine ⟨((f ∣_ U).homeomorph.symm ⟨y, hY y hy⟩).1,
      (mem_genericPoints_opens_iff _ _).1
        ((f ∣_ U).homeomorph.symm.mem_genericPoints hw), ?_⟩
    rw [← hmap]
    exact congrArg Subtype.val ((f ∣_ U).homeomorph.apply_symm_apply ⟨y, hY y hy⟩)
  · intro x hx
    exact (isIso_stalkMap_morphismRestrict_iff f U ⟨x, hmem x hx⟩).1
      (((isIso_iff_isIso_stalkMap (f ∣_ U)).mp hU).2 _)

/-- A coproduct of birational morphisms is birational. -/
theorem isBirational_sigmaMap {ι : Type u} [Small.{u} ι] {S T : ι → Scheme.{u}}
    (f : ∀ i, S i ⟶ T i) (hf : ∀ i, IsBirational (f i)) :
    IsBirational (Sigma.desc fun i ↦ f i ≫ Sigma.ι T i) := by
  have key : ∀ (i : ι) (x : S i),
      (Sigma.desc fun i ↦ f i ≫ Sigma.ι T i) (Sigma.ι S i x) = Sigma.ι T i (f i x) := by
    intro i x
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc, Scheme.Hom.comp_apply]
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ⟨?_, ?_, ?_⟩ ?_
  · intro p hp
    obtain ⟨i, x, rfl⟩ := exists_sigmaι_eq S p
    rw [mem_genericPoints_sigmaι_iff] at hp
    rw [key, mem_genericPoints_sigmaι_iff]
    exact (hf i).bijOn.mapsTo hp
  · intro p hp q hq hpq
    obtain ⟨i, x, rfl⟩ := exists_sigmaι_eq S p
    obtain ⟨j, y, rfl⟩ := exists_sigmaι_eq S q
    rw [mem_genericPoints_sigmaι_iff] at hp hq
    rw [key, key] at hpq
    have h := (sigmaι_eq_iff T i j (f i x) (f j y)).mp hpq
    obtain rfl : i = j := congrArg Sigma.fst h
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
    rw [(hf i).bijOn.injOn hp hq h]
  · intro q hq
    obtain ⟨i, y, rfl⟩ := exists_sigmaι_eq T q
    rw [mem_genericPoints_sigmaι_iff] at hq
    obtain ⟨x, hx, hfx⟩ := (hf i).bijOn.surjOn hq
    exact ⟨Sigma.ι S i x, (mem_genericPoints_sigmaι_iff S i x).2 hx,
      (key i x).trans (congrArg (Sigma.ι T i) hfx)⟩
  · intro p hp
    obtain ⟨i, x, rfl⟩ := exists_sigmaι_eq S p
    rw [mem_genericPoints_sigmaι_iff] at hp
    have : IsIso ((Sigma.desc fun i ↦ f i ≫ Sigma.ι T i).stalkMap (Sigma.ι S i x) ≫
        (Sigma.ι S i).stalkMap x) := by
      have hT : IsIso ((Sigma.ι T i).stalkMap ((f i) x)) := inferInstance
      rw [← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom _ _ (Sigma.ι_desc _ _),
        Scheme.Hom.stalkMap_comp]
      exact IsIso.comp_isIso' (Iso.isIso_hom _)
        (IsIso.comp_isIso' hT ((hf i).isIso_stalkMap x hp))
    exact IsIso.of_isIso_comp_right _ ((Sigma.ι S i).stalkMap x)

end AlgebraicGeometry
