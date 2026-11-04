module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent

/-!
# Sections over the preimage of an affine open of a stage of an inverse limit

Let `{ Dᵢ }` be an inverse system of schemes indexed by a cofiltered category, with affine
transition morphisms, and let `c` be a limit cone over it. For an affine open `W` of a stage
`Dᵢ`, the sections of the limit over `c.π.app i ⁻¹ᵁ W` are the filtered colimit of the sections
of the later stages `Dⱼ` over `D.map a ⁻¹ᵁ W`. This file proves the surjectivity half of that
description: a single section comes from a stage, and finitely many sections come from one and the
same stage.

## Main results

* `AlgebraicGeometry.exists_appLE_π_eq_of_isAffineOpen_of_isLimit`: a section of the limit over
  the preimage of an affine open of a stage is the pullback of a section at some later stage.
* `AlgebraicGeometry.exists_subset_range_appLE_π_of_isAffineOpen_of_isLimit`: finitely many such
  sections all come from one later stage.

## References

* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Restricting a global function along `AlgebraicGeometry.Scheme.Hom.resLE` and reading the
result as a function on the open set is restricting along
`AlgebraicGeometry.Scheme.Hom.appLE`. -/
private theorem topIso_hom_resLE_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (t : Γ(↑U, ⊤)) :
    V.topIso.hom ((f.resLE U V e).appTop t) = f.appLE U V e (U.topIso.hom t) := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]

/-- The preimage of `W` in the limit lies in the preimage of its preimage at any stage over it. -/
private theorem preimage_le_preimage_preimage {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) {i j : I} (a : j ⟶ i) (W : (D.obj i).Opens) :
    c.π.app i ⁻¹ᵁ W ≤ c.π.app j ⁻¹ᵁ (D.map a ⁻¹ᵁ W) :=
  le_of_eq (by rw [← Scheme.Hom.comp_preimage, c.w])

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)] (c : Cone D) (hc : IsLimit c)

include hc in
/-- **A section of an inverse limit over the preimage of an affine open of a stage comes from a
later stage.** Let `{ Dᵢ }` be a cofiltered inverse system of schemes with affine transition
morphisms, let `c` be a limit cone, and let `W` be an affine open of the stage `Dᵢ`. Every
section of the limit over `c.π.app i ⁻¹ᵁ W` is the pullback of a section of `Dⱼ` over
`D.map a ⁻¹ᵁ W` for some `a : j ⟶ i`. -/
theorem exists_appLE_π_eq_of_isAffineOpen_of_isLimit (i : I) {W : (D.obj i).Opens}
    (hW : IsAffineOpen W) (s : Γ(c.pt, c.π.app i ⁻¹ᵁ W)) :
    ∃ (j : I) (a : j ⟶ i) (t : Γ(D.obj j, D.map a ⁻¹ᵁ W)),
      (c.π.app j).appLE (D.map a ⁻¹ᵁ W) (c.π.app i ⁻¹ᵁ W)
        (le_of_eq (by rw [← Scheme.Hom.comp_preimage, c.w])) t = s := by
  have hAff : ∀ k : Over i, IsAffine ((opensDiagram D i W).obj k) :=
    fun k => hW.preimage (D.map k.hom)
  obtain ⟨k, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit (opensDiagram D i W)
    (opensCone D c i W) (isLimitOpensCone D c hc i W) ((c.π.app i ⁻¹ᵁ W).topIso.inv s)
  have hs : (c.π.app i ⁻¹ᵁ W).topIso.hom ((c.π.app i ⁻¹ᵁ W).topIso.inv s) = s :=
    Iso.inv_hom_id_apply _ s
  exact ⟨k.left, k.hom, (D.map k.hom ⁻¹ᵁ W).topIso.hom t,
    (topIso_hom_resLE_appTop (c.π.app k.left) (D.map k.hom ⁻¹ᵁ W) (c.π.app i ⁻¹ᵁ W)
        (preimage_le_preimage_preimage D c k.hom W) t).symm.trans
      ((congrArg (fun z => (c.π.app i ⁻¹ᵁ W).topIso.hom z) ht).trans hs)⟩

include hc in
/-- **Finitely many sections of an inverse limit over the preimage of an affine open of a stage
come from one and the same later stage.** For every finite set `F` of sections of the limit over
`c.π.app i ⁻¹ᵁ W` there is `a : j ⟶ i` such that every member of `F` is the pullback of a section
of `Dⱼ` over `D.map a ⁻¹ᵁ W`. -/
theorem exists_subset_range_appLE_π_of_isAffineOpen_of_isLimit (i : I) {W : (D.obj i).Opens}
    (hW : IsAffineOpen W) (F : Finset Γ(c.pt, c.π.app i ⁻¹ᵁ W)) :
    ∃ (j : I) (a : j ⟶ i), (F : Set Γ(c.pt, c.π.app i ⁻¹ᵁ W)) ⊆
      Set.range ((c.π.app j).appLE (D.map a ⁻¹ᵁ W) (c.π.app i ⁻¹ᵁ W)
        (le_of_eq (by rw [← Scheme.Hom.comp_preimage, c.w]))) := by
  classical
  have hone : ∀ x : Γ(c.pt, c.π.app i ⁻¹ᵁ W), ∃ (k : Over i)
      (t : Γ(D.obj k.left, D.map k.hom ⁻¹ᵁ W)),
      (c.π.app k.left).appLE (D.map k.hom ⁻¹ᵁ W) (c.π.app i ⁻¹ᵁ W)
        (preimage_le_preimage_preimage D c k.hom W) t = x := fun x =>
    let ⟨j, a, t, ht⟩ := exists_appLE_π_eq_of_isAffineOpen_of_isLimit D c hc i hW x
    ⟨Over.mk a, t, ht⟩
  choose kk tt htt using hone
  obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists (F.image kk)
  refine ⟨m.left, m.hom, fun x hx => ?_⟩
  obtain ⟨b⟩ := hm (Finset.mem_image_of_mem kk hx)
  have hWm : D.map m.hom ⁻¹ᵁ W ≤ D.map b.left ⁻¹ᵁ (D.map (kk x).hom ⁻¹ᵁ W) :=
    le_of_eq (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w b])
  refine ⟨(D.map b.left).appLE (D.map (kk x).hom ⁻¹ᵁ W) (D.map m.hom ⁻¹ᵁ W) hWm (tt x), ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_congr_hom (c.w b.left) _ _ _
      (preimage_le_preimage_preimage D c (kk x).hom W)]
  exact htt x

end AlgebraicGeometry

end
