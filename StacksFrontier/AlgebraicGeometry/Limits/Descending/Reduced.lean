module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reducedness passes to filtered colimits of rings and cofiltered limits of schemes

A filtered colimit of reduced commutative rings is reduced, and the limit of a cofiltered
diagram of reduced schemes with affine transition morphisms is reduced.

## Main results

* `CommRingCat.isReduced_filteredColimit_of_isReduced`: a filtered colimit of reduced
  commutative rings is reduced.
* `AlgebraicGeometry.isReduced_cofilteredLimit_of_isReduced`: the limit of a cofiltered diagram
  of reduced schemes with affine transition morphisms is reduced.

## Implementation notes

Reducedness of a scheme is checked on stalks. Around a point of the limit the diagram is
replaced by the inverse system of the preimages of an affine open of one stage, whose ring of
global sections is the filtered colimit of the rings of global sections of the stages
(`AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone`); the ring-level statement then applies.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommRingCat

/-- A filtered colimit of reduced commutative rings is reduced. -/
@[ega "IV 5.13.2" "more general"]
theorem isReduced_filteredColimit_of_isReduced
    {J : Type u} [Category.{u} J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    [∀ j, IsReduced (F.obj j)] : IsReduced c.pt := by
  refine ⟨fun x ⟨n, hn⟩ => ?_⟩
  let cT := (forget CommRingCat).mapCocone c
  let hcT : IsColimit cT := isColimitOfPreserves (forget CommRingCat) hc
  obtain ⟨i, a, rfl⟩ := Types.jointly_surjective_of_isColimit hcT x
  obtain ⟨j, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' hcT (a ^ n) 0).mp (by
      change (c.ι.app i).hom (a ^ n) = (c.ι.app i).hom 0
      rw [map_pow, map_zero]
      exact hn)
  have hnil : (F.map f).hom a ^ n = 0 := by
    rw [← map_pow, ← map_zero (F.map f).hom]
    exact hf
  calc
    c.ι.app i a = c.ι.app j ((F.map f).hom a) := by
      simpa only [Category.assoc, ConcreteCategory.comp_apply] using
        congrArg (fun g : F.obj i ⟶ c.pt => g a) (c.w f).symm
    _ = c.ι.app j 0 := by rw [IsReduced.eq_zero _ ⟨n, hnil⟩]
    _ = 0 := map_zero _

end CommRingCat

namespace AlgebraicGeometry

/-- The limit of a cofiltered diagram of reduced schemes with affine transition morphisms is
reduced. -/
theorem isReduced_cofilteredLimit_of_isReduced
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (E : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (E.map f)]
    (c : Cone E) (hc : IsLimit c) [∀ i, IsReduced (E.obj i)] : IsReduced c.pt := by
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have hπ : IsAffineHom (c.π.app i) := isAffineHom_π_app E c hc i
  have hstalk (x : c.pt) : _root_.IsReduced (c.pt.presheaf.stalk x) := by
    obtain ⟨j, xj, hxi⟩ := (E.obj i).affineCover.exists_eq (c.π.app i x)
    let U : (E.obj i).affineOpens :=
      ⟨((E.obj i).affineCover.f j).opensRange,
        isAffineOpen_opensRange ((E.obj i).affineCover.f j)⟩
    let O := opensDiagram E i U
    let oC := opensCone E c i U
    have hoC : IsLimit oC := isLimitOpensCone E c hc i U
    have (j : Over i) : IsAffine (O.obj j) := U.2.preimage (E.map j.hom)
    have (j : Over i) : CompactSpace (O.obj j) := inferInstance
    have (j : Over i) : QuasiSeparatedSpace (O.obj j) := inferInstance
    have (j : Over i) : IsReduced (O.obj j) := by
      dsimp only [O, opensDiagram]
      infer_instance
    let F : (Over i)ᵒᵖ ⥤ CommRingCat.{u} := O.op ⋙ Scheme.Γ
    let q := Scheme.Γ.mapCocone oC.op
    have hq : IsColimit q := Classical.choice (nonempty_isColimit_Γ_mapCocone O oC hoC)
    have (j : (Over i)ᵒᵖ) : _root_.IsReduced (F.obj j) := by
      change _root_.IsReduced Γ(O.obj j.unop, ⊤)
      exact IsReduced.component_reduced ⊤
    have : IsAffine oC.pt := Scheme.isAffine_of_isLimit oC hoC
    have : _root_.IsReduced Γ(oC.pt, ⊤) :=
      CommRingCat.isReduced_filteredColimit_of_isReduced F q hq
    let W : c.pt.Opens := c.π.app i ⁻¹ᵁ U
    have : IsReduced W := isReduced_of_isAffine_isReduced oC.pt
    have hxW : x ∈ c.π.app i ⁻¹ᵁ U := by
      change c.π.app i x ∈ U.1
      rw [← hxi]
      change (E.obj i).affineCover.f j xj ∈ ((E.obj i).affineCover.f j).opensRange
      exact ⟨xj, rfl⟩
    let y : W := ⟨x, hxW⟩
    have hopen : IsOpenImmersion W.ι := by
      dsimp only [W]
      infer_instance
    have hyiso : IsIso (W.ι.stalkMap y) := (IsOpenImmersion.iff_isIso_stalkMap.mp hopen).2 y
    have : _root_.IsReduced (W.toScheme.presheaf.stalk y) :=
      isReduced_stalk_of_isReduced W.toScheme y
    exact isReduced_of_injective (W.ι.stalkMap y).hom
      (asIso (W.ι.stalkMap y)).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk c.pt

end AlgebraicGeometry

end
