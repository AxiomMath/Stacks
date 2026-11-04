module

public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeSystem
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.GoodDiagramLimit.Reduction

/-!
# The limit of the system of scheme-theoretic images of a good diagram

For a good diagram over a directed inverse limit of Noetherian schemes, the scheme-theoretic
images of `X` in the base changes of its model to the later stages form an inverse system
(`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.imageSystem`) with a canonical cone from
`X`. This file proves that the cone is a limit cone, which is Tag 0CNQ.

## Main results

* `AlgebraicGeometry.le_iSup_comap_map_of_isLimit`: an ideal sheaf on a cofiltered limit of
  schemes with affine transition morphisms is the supremum of the inverse images of its images at
  the stages.
* `AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isLimit_imageCone` identifies `X` as the
  limit of the inverse system of scheme-theoretic images.

## Implementation notes

`StacksFrontier.AlgebraicGeometry.GoodDiagramLimit.Reduction` reduces the limit assertion to
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.KerDetectedOnStages` through
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.isLimit_imageCone_of_kerDetected`: the
morphism `X ⟶ S ×_{S_i} W` of the good diagram is a closed immersion, so a competing cone on the
system of images lifts through it as soon as the ideal sheaf of `X` in `S ×_{S_i} W` is contained
in the supremum of the inverse images of the ideal sheaves of the images. That containment is the
local computation of the Stacks proof and is isolated as
`AlgebraicGeometry.le_iSup_comap_map_of_isLimit`, applied to the limit cone
`AlgebraicGeometry.LimitNoetherianSituation.GoodDiagram.stageConeIsLimit` of the base changes of
the model: on the inverse image of an affine open of a stage every scheme of the restricted
system is affine, so global sections turn the limit into the filtered colimit of rings used in
the source, and every section of the limit therefore comes from a stage.

Since `AlgebraicGeometry.LimitNoetherianSituation` carries its limiting cone as data, no limit has
to be constructed and hence no smallness hypothesis on the index type is needed anywhere in this
file.

## References

* [Stacks Project, Tag 0CNQ](https://stacks.math.columbia.edu/tag/0CNQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry

/-! ### Kernel ideal sheaves on charts -/

section Chart

variable {Y Z : Scheme.{u}}

/-- The chart of the inverse image of an ideal sheaf along an affine morphism contains the
extension of the chart of the original ideal sheaf. -/
private lemma map_ideal_le_ideal_comap (p : Y ⟶ Z) [IsAffineHom p] (J : Z.IdealSheafData)
    (U : Z.affineOpens) :
    Ideal.map (p.app (U : Z.Opens)).hom (J.ideal U) ≤
      (J.comap p).ideal ⟨p ⁻¹ᵁ (U : Z.Opens), U.2.preimage p⟩ := by
  refine Ideal.map_le_iff_le_comap.mpr ?_
  have h := Scheme.IdealSheafData.ideal_mono (Scheme.IdealSheafData.le_map_comap J p) U
  rwa [Scheme.IdealSheafData.ideal_map_of_isAffineHom] at h

/-- The chart of the inverse image of an ideal sheaf along an affine morphism, on an open which
is the inverse image of the chosen affine open. -/
private lemma map_appLE_ideal_le_ideal_comap (p : Y ⟶ Z) [IsAffineHom p] (J : Z.IdealSheafData)
    (U : Z.Opens) (hUaff : IsAffineOpen U) (W : Y.Opens) (hW : W = p ⁻¹ᵁ U)
    (hWaff : IsAffineOpen W) :
    Ideal.map (p.appLE U W hW.le).hom (J.ideal ⟨U, hUaff⟩) ≤ (J.comap p).ideal ⟨W, hWaff⟩ := by
  subst hW
  rw [Scheme.Hom.appLE_eq_app]
  exact map_ideal_le_ideal_comap p J ⟨U, hUaff⟩

/-- The chart of the image of an ideal sheaf along an affine morphism, on an open which is the
inverse image of the chosen affine open. -/
private lemma ideal_map_appLE (p : Y ⟶ Z) [IsAffineHom p] (J : Y.IdealSheafData)
    (U : Z.Opens) (hUaff : IsAffineOpen U) (W : Y.Opens) (hW : W = p ⁻¹ᵁ U)
    (hWaff : IsAffineOpen W) :
    (J.map p).ideal ⟨U, hUaff⟩ = (J.ideal ⟨W, hWaff⟩).comap (p.appLE U W hW.le).hom := by
  subst hW
  rw [Scheme.Hom.appLE_eq_app]
  exact Scheme.IdealSheafData.ideal_map_of_isAffineHom J p ⟨U, hUaff⟩

end Chart

/-! ### Ideal sheaves on a cofiltered limit of schemes -/

section Limit

/-- The inverse image in the limit of an open of a stage does not change when the open is pulled
back to a later stage first. -/
private lemma preimage_π_app_eq {K : Type v} [Category.{w} K] {N : K ⥤ Scheme.{u}} (c : Cone N)
    (k₀ : K) (U : (N.obj k₀).Opens) (b : Over k₀) :
    c.π.app k₀ ⁻¹ᵁ U = c.π.app b.left ⁻¹ᵁ (N.map b.hom ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, c.w b.hom]

variable {K : Type v} [Category.{w} K] [IsCofiltered K] (N : K ⥤ Scheme.{u})
  [∀ {a b : K} (h : a ⟶ b), IsAffineHom (N.map h)] (c : Cone N)

/-- A section over the inverse image in the limit of an affine open of a stage is pulled back from
a section over the inverse image of that open at some later stage. -/
private lemma exists_appLE_eq (hc : IsLimit c) (k₀ : K) (V : (N.obj k₀).affineOpens)
    (x : Γ(c.pt, c.π.app k₀ ⁻¹ᵁ (V : (N.obj k₀).Opens))) :
    ∃ (b : Over k₀) (y : Γ(N.obj b.left, N.map b.hom ⁻¹ᵁ (V : (N.obj k₀).Opens))),
      ((c.π.app b.left).appLE (N.map b.hom ⁻¹ᵁ (V : (N.obj k₀).Opens))
        (c.π.app k₀ ⁻¹ᵁ (V : (N.obj k₀).Opens))
        (preimage_π_app_eq c k₀ (V : (N.obj k₀).Opens) b).le).hom y = x := by
  classical
  have hEaff (b : Over k₀) : IsAffine ((EventualLimit.preimageDiagram N k₀ V.1).obj b) :=
    EventualLimit.isAffine_preimageDiagram_obj N k₀ V.2 b
  have hEaff' (b : (Over k₀)ᵒᵖ) :
      IsAffine (((EventualLimit.preimageDiagram N k₀ V.1).op.obj b).unop) := hEaff b.unop
  have hΓ : IsColimit (Scheme.Γ.mapCocone (EventualLimit.preimageCone N c k₀ V.1).op) :=
    isColimitOfPreserves Scheme.Γ (EventualLimit.isLimitPreimageCone N c hc k₀ V.1).op
  obtain ⟨b, y, hy⟩ := exists_eq_ι_app_of_isColimit _ hΓ
    ((c.π.app k₀ ⁻¹ᵁ (V : (N.obj k₀).Opens)).topIso.inv.hom x)
  have hy' : ((N.map b.unop.hom ⁻¹ᵁ (V : (N.obj k₀).Opens)).topIso.hom ≫
        (c.π.app b.unop.left).appLE (N.map b.unop.hom ⁻¹ᵁ (V : (N.obj k₀).Opens))
          (c.π.app k₀ ⁻¹ᵁ (V : (N.obj k₀).Opens))
          (preimage_π_app_eq c k₀ (V : (N.obj k₀).Opens) b.unop).le ≫
        (c.π.app k₀ ⁻¹ᵁ (V : (N.obj k₀).Opens)).topIso.inv).hom y =
      (c.π.app k₀ ⁻¹ᵁ (V : (N.obj k₀).Opens)).topIso.inv.hom x := by
    rw [← Scheme.Hom.resLE_app_top]
    exact hy
  refine ⟨b.unop, (N.map b.unop.hom ⁻¹ᵁ (V : (N.obj k₀).Opens)).topIso.hom.hom y, ?_⟩
  refine (ConcreteCategory.bijective_of_isIso
    (c.π.app k₀ ⁻¹ᵁ (V : (N.obj k₀).Opens)).topIso.inv).1 ?_
  rw [← hy']
  rfl

/-- An ideal sheaf on a cofiltered limit of schemes with affine transition morphisms is the
supremum of the inverse images of its images at the stages. This is the local content of the
Stacks argument: on the inverse image of an affine open of a stage the ring of sections is the
filtered colimit of the rings of sections at the later stages. -/
lemma le_iSup_comap_map_of_isLimit (hc : IsLimit c) (I : c.pt.IdealSheafData) :
    I ≤ ⨆ k : K, (I.map (c.π.app k)).comap (c.π.app k) := by
  classical
  have hπ : ∀ k : K, IsAffineHom (c.π.app k) := fun k =>
    EventualLimit.isAffineHom_π_app N c hc k
  obtain ⟨k₀⟩ : Nonempty K := IsCofiltered.nonempty
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun V : (N.obj k₀).affineOpens => ⟨c.π.app k₀ ⁻¹ᵁ (V : (N.obj k₀).Opens),
      EventualLimit.isAffineOpen_preimage_π_app N c hc k₀ V.2⟩)
    (Scheme.Hom.iSup_preimage_eq_top _ (iSup_affineOpens_eq_top _)) (fun V x hx => ?_)
  obtain ⟨b, y, hy⟩ := exists_appLE_eq N c hc k₀ V x
  have hLaff : IsAffineOpen (c.π.app k₀ ⁻¹ᵁ (V : (N.obj k₀).Opens)) :=
    EventualLimit.isAffineOpen_preimage_π_app N c hc k₀ V.2
  have hy' : y ∈ (I.map (c.π.app b.left)).ideal
      ⟨N.map b.hom ⁻¹ᵁ (V : (N.obj k₀).Opens), V.2.preimage _⟩ := by
    rw [ideal_map_appLE (c.π.app b.left) I _ (V.2.preimage _) _
      (preimage_π_app_eq c k₀ (V : (N.obj k₀).Opens) b) hLaff]
    rw [Ideal.mem_comap, hy]
    exact hx
  have hstep := map_appLE_ideal_le_ideal_comap (c.π.app b.left) (I.map (c.π.app b.left))
    _ (V.2.preimage (N.map b.hom)) _
    (preimage_π_app_eq c k₀ (V : (N.obj k₀).Opens) b) hLaff
  have hsup := Scheme.IdealSheafData.ideal_mono
    (le_iSup (fun k : K => (I.map (c.π.app k)).comap (c.π.app k)) b.left)
    ⟨c.π.app k₀ ⁻¹ᵁ (V : (N.obj k₀).Opens), hLaff⟩
  exact hsup (hstep (hy ▸ Ideal.mem_map_of_mem _ hy'))

end Limit

namespace LimitNoetherianSituation

namespace GoodDiagram

section Statement

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : LimitNoetherianSituation.{v, u} I} {X : Scheme.{u}} {f : X ⟶ D.limitScheme}

/-- **Stacks Project, Tag 0CNQ.** The scheme-theoretic images of a good diagram at
all later stages form an inverse system with canonical limit `X`. -/
@[stacks 0CNQ, no_expose]
noncomputable def isLimit_imageCone {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : LimitNoetherianSituation.{v, u} I)
    {X : Scheme.{u}} (f : X ⟶ D.limitScheme) [QuasiSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (G : GoodDiagram D f) :
    IsLimit (imageCone G) := by
  -- `S ×_{S_i} W` is the limit of the base changes of the model, whose transitions are affine,
  -- so the ideal of `X` is below the supremum of the pullbacks of its images at the stages.
  refine G.isLimit_imageCone_of_kerDetected fun w hw => ?_
  refine (le_iSup_comap_map_of_isLimit G.stageSystem G.stageCone G.stageConeIsLimit
    G.induced.ker).trans (iSup_le fun j => ?_)
  have hmap : G.induced.ker.map (G.stageProj j) = (G.stageMap j).ker :=
    (Scheme.Hom.ker_comp G.induced (G.stageProj j)).symm.trans
      (congrArg Scheme.Hom.ker (G.induced_comp_stageProj j))
  refine (congrArg (fun J => J.comap (G.stageProj j)) hmap).le.trans ?_
  refine Scheme.IdealSheafData.le_map_iff_comap_le.mp ?_
  rw [← Scheme.Hom.ker_comp]
  exact hw j

end Statement

end GoodDiagram

end LimitNoetherianSituation

end AlgebraicGeometry
