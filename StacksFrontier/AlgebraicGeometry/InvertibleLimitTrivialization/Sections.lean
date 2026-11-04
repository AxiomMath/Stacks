module

public import StacksFrontier.AlgebraicGeometry.InvertibleLimitTrivialization.Basic

/-!
# A section over the preimage of a quasi-compact open comes from a stage

Pinned Mathlib proves that a *global* section of the limit of a cofiltered system of qcqs
schemes with affine transition morphisms comes from a stage
(`AlgebraicGeometry.exists_appTop_π_eq_of_isLimit`), and that two sections over a quasi-compact
open of a stage which agree after pullback to the limit already agree at a later stage
(`AlgebraicGeometry.exists_app_map_eq_map_of_isLimit`). The *surjectivity* half over an open
other than the whole space is not there, and it is what a glueing argument over a cover of a
stage needs: the comparison units of two trivializations live over an overlap, never over the
whole of the limit.

## Main results

* `Stacks.InvertibleLimitTrivialization.exists_appLE_π_eq_of_isLimit`: a section of the limit
  over the preimage of a quasi-compact open of a stage is the pullback of a section over the
  preimage of that open at some later stage.

## Route

`AlgebraicGeometry.isLimitOpensCone` exhibits `c.π.app i ⁻¹ᵁ U` as the limit of the system of
open subschemes `D.map f ⁻¹ᵁ U` indexed by `CategoryTheory.Over i`, and the hypotheses of
`exists_appTop_π_eq_of_isLimit` hold for that system: the transitions are affine by the global
instance Mathlib supplies for `AlgebraicGeometry.opensDiagram`, each member is quasi-compact
because `U` is and the transition morphisms are quasi-compact, and each is quasi-separated as an
open of a quasi-separated scheme. Applying that lemma there produces a section over the whole of
one of those open subschemes, and `AlgebraicGeometry.Scheme.Hom.resLE_app_top` translates the
cone's leg — a `AlgebraicGeometry.Scheme.Hom.resLE` — into
`AlgebraicGeometry.Scheme.Hom.appLE` conjugated by the two
`AlgebraicGeometry.Scheme.Opens.topIso`s, which is the whole of the translation. That square is
taken from Mathlib's `AlgebraicGeometry.arrowResLEAppIso` rather than re-derived; see
`Stacks.InvertibleLimitTrivialization.appTop_resLE_comp_topIso_hom` for why.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.InvertibleLimitTrivialization

/-- **The square comparing `appLE` with the global sections of `resLE`.** This is the commuting
square of pinned Mathlib's `AlgebraicGeometry.arrowResLEAppIso`, read off as an equation.

It is taken from there rather than re-derived from
`AlgebraicGeometry.Scheme.Hom.resLE_app_top`, and the reason is a transparency wall, not taste:
`(f.resLE U V e).app ⊤` has codomain `Γ(V, f.resLE U V e ⁻¹ᵁ ⊤)`, which is the same as
`Γ(V, ⊤)` definitionally and not syntactically, so after rewriting with `resLE_app_top` the goal
is no longer type-correct at `implicit` transparency and `Category.assoc` will not fire on it.
Mathlib pays for that with a compiler option on `resLE_app_top` itself; `arrowResLEAppIso` has
already spent it, and `CategoryTheory.Arrow.w` of its `hom` is exactly the equation wanted. -/
theorem appTop_resLE_comp_topIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) :
    U.topIso.hom ≫ f.appLE U V e =
      Scheme.Hom.appTop (f.resLE U V e) ≫ V.topIso.hom :=
  Arrow.w (arrowResLEAppIso f U V e).hom

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

include hc in
/-- **A section of the limit over the preimage of a quasi-compact open of a stage comes from a
later stage.** The surjectivity half of the colimit description of the sections, over an open
rather than over the whole space; pinned Mathlib has the `⊤` case and the injectivity half at an
arbitrary quasi-compact open, but not this. -/
theorem exists_appLE_π_eq_of_isLimit [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {i : I} {U : (D.obj i).Opens} (hU : IsCompact (X := D.obj i) U)
    (s : Γ(c.pt, c.π.app i ⁻¹ᵁ U)) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)),
      (c.π.app j).appLE (D.map f ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U)
          (by rw [← Scheme.Hom.comp_preimage, c.w]) t = s := by
  have : ∀ k : Over i, CompactSpace ((opensDiagram D i U).obj k) := fun k =>
    isCompact_iff_compactSpace.mp
      (by simpa using (D.map k.hom).isCompact_preimage hU)
  have : ∀ k : Over i, QuasiSeparatedSpace ((opensDiagram D i U).obj k) := fun k =>
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map k.hom ⁻¹ᵁ U).2).mp
      (.of_quasiSeparatedSpace _)
  obtain ⟨k, t, ht⟩ := exists_appTop_π_eq_of_isLimit (opensDiagram D i U) (opensCone D c i U)
    (isLimitOpensCone D c hc i U) ((c.π.app i ⁻¹ᵁ U).topIso.inv s)
  refine ⟨k.left, k.hom, (D.map k.hom ⁻¹ᵁ U).topIso.hom t, ?_⟩
  have hle : c.π.app i ⁻¹ᵁ U ≤ c.π.app k.left ⁻¹ᵁ (D.map k.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  -- The cone's leg IS that `resLE`, definitionally; the ascription is what strips the
  -- `CategoryTheory.Functor.const` wrapper without a rewrite.
  have ht' : (c.π.app i ⁻¹ᵁ U).topIso.inv s =
      Scheme.Hom.appTop
        ((c.π.app k.left).resLE (D.map k.hom ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U) hle) t := ht
  calc (c.π.app k.left).appLE (D.map k.hom ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U) hle
          ((D.map k.hom ⁻¹ᵁ U).topIso.hom t)
      = ((D.map k.hom ⁻¹ᵁ U).topIso.hom ≫
          (c.π.app k.left).appLE (D.map k.hom ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U) hle) t :=
        (CommRingCat.comp_apply _ _ t).symm
    _ = (Scheme.Hom.appTop
            ((c.π.app k.left).resLE (D.map k.hom ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U) hle) ≫
          (c.π.app i ⁻¹ᵁ U).topIso.hom) t := by
        rw [appTop_resLE_comp_topIso_hom]
    _ = (c.π.app i ⁻¹ᵁ U).topIso.hom
          (Scheme.Hom.appTop
            ((c.π.app k.left).resLE (D.map k.hom ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U) hle) t) :=
        CommRingCat.comp_apply _ _ t
    _ = (c.π.app i ⁻¹ᵁ U).topIso.hom ((c.π.app i ⁻¹ᵁ U).topIso.inv s) := by rw [← ht']
    _ = ((c.π.app i ⁻¹ᵁ U).topIso.inv ≫ (c.π.app i ⁻¹ᵁ U).topIso.hom) s :=
        (CommRingCat.comp_apply _ _ s).symm
    _ = s := by rw [Iso.inv_hom_id]; rfl

end Stacks.InvertibleLimitTrivialization

end
