module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeGluing

/-!
# The sections of a relative `Proj` over an open of one chart

Let `s` be a relative-`Proj` situation and `W` an affine open of its base. The chart over `W` is
the open immersion `Stacks.RelativeProj.Situation.relativeProjChart s W` from
`Proj (s.sectionRingGrading W)`, so over an open `V` of the relative `Proj` contained in its
image the restriction map on sections is a *bijection*: the sections of the structure sheaf of
the relative `Proj` over `V` are the sections of the structure sheaf of the chart over the
preimage of `V`.

This is what lets a computation performed inside one chart — where the twisting sheaf is
trivialized by a degree-one element of the graded section ring — be read back as an identity
between sections of the structure sheaf of the relative `Proj` itself, which is where the
trivialization of the exceptional ideal sheaf of a blowup lives.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.isIso_app_of_le_opensRange`: **an open immersion is an
  isomorphism on sections over an open contained in its image.**
* `Stacks.RelativeProj.Situation.chartSectionsIso`: that isomorphism for the chart of a relative
  `Proj` over an affine open of the base.

## Main results

* `Stacks.RelativeProj.Situation.chartSectionsIso_hom_apply`: the forward direction is the chart's
  restriction map on sections.
* `Stacks.RelativeProj.Situation.map_chartSectionsIso_hom` and
  `Stacks.RelativeProj.Situation.chartSectionsIso_inv_map`: **the isomorphism is compatible with
  the restriction maps**, in both directions.

## Implementation notes

The `IsIso` statement is proved from `AlgebraicGeometry.IsOpenImmersion.map_ΓIso_inv`, which
factors `f.app V` as a restriction map `Γ(Y, V) ⟶ Γ(Y, f.opensRange ⊓ V)` followed by the
inverse of `AlgebraicGeometry.IsOpenImmersion.ΓIso`. Under the hypothesis `V ≤ f.opensRange` the
two opens `f.opensRange ⊓ V` and `V` are equal, so that restriction map is the image of an
`eqToHom` — the homs of `Opens` are a subsingleton, so no rewriting is needed to see it — and
hence an isomorphism.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **An open immersion is an isomorphism on sections over an open contained in its image.** -/
theorem isIso_app_of_le_opensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {V : Y.Opens} (hV : V ≤ f.opensRange) : IsIso (f.app V) := by
  have h : op V = op (f.opensRange ⊓ V) := congrArg op (inf_eq_right.mpr hV).symm
  have hmap : IsIso (Y.presheaf.map
      (homOfLE (inf_le_right : f.opensRange ⊓ V ≤ V)).op) := by
    rw [show (homOfLE (inf_le_right : f.opensRange ⊓ V ≤ V)).op = eqToHom h from
      Subsingleton.elim _ _]
    infer_instance
  rw [← IsOpenImmersion.map_ΓIso_inv f V]
  infer_instance

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u}) (W : s.base.affineOpens)

/-- **The sections of a relative `Proj` over an open of the chart over `W`.** The chart is an
open immersion, so over an open `V` contained in its image its restriction map on sections is an
isomorphism onto the sections of `Proj (s.sectionRingGrading W)` over the preimage of `V`. -/
def chartSectionsIso {V : s.relativeProj.Opens}
    (hV : V ≤ (relativeProjChart s W).opensRange) :
    Γ(relativeProj s, V) ≅
      Γ(AlgebraicGeometry.Proj (s.sectionRingGrading W.1), relativeProjChart s W ⁻¹ᵁ V) :=
  @asIso _ _ _ _ ((relativeProjChart s W).app V)
    (Scheme.Hom.isIso_app_of_le_opensRange (relativeProjChart s W) hV)

/-- The forward direction of `chartSectionsIso` is the chart's restriction map on sections. -/
theorem chartSectionsIso_hom {V : s.relativeProj.Opens}
    (hV : V ≤ (relativeProjChart s W).opensRange) :
    (chartSectionsIso s W hV).hom = (relativeProjChart s W).app V := rfl

/-- The chart reads the section that `chartSectionsIso` produces as the section it came from. -/
theorem chartSectionsIso_hom_inv_apply {V : s.relativeProj.Opens}
    (hV : V ≤ (relativeProjChart s W).opensRange)
    (z : Γ(AlgebraicGeometry.Proj (s.sectionRingGrading W.1),
      relativeProjChart s W ⁻¹ᵁ V)) :
    ((relativeProjChart s W).app V).hom ((chartSectionsIso s W hV).inv.hom z) = z := by
  exact (chartSectionsIso s W hV).inv_hom_id_apply z

/-- The inverse of `chartSectionsIso` undoes the chart's restriction map on sections. -/
theorem chartSectionsIso_inv_hom_apply {V : s.relativeProj.Opens}
    (hV : V ≤ (relativeProjChart s W).opensRange) (x : Γ(relativeProj s, V)) :
    (chartSectionsIso s W hV).inv.hom (((relativeProjChart s W).app V).hom x) = x :=
  (chartSectionsIso s W hV).hom_inv_id_apply x

/-- `chartSectionsIso` is injective on sections, being an isomorphism. -/
theorem injective_app_relativeProjChart {V : s.relativeProj.Opens}
    (hV : V ≤ (relativeProjChart s W).opensRange) :
    Function.Injective ((relativeProjChart s W).app V).hom := fun x y hxy =>
  (chartSectionsIso_inv_hom_apply s W hV x).symm.trans
    ((congrArg (chartSectionsIso s W hV).inv.hom hxy).trans
      (chartSectionsIso_inv_hom_apply s W hV y))

/-- **`chartSectionsIso` commutes with the restriction maps.** Restricting a section of the
relative `Proj` and then reading it on the chart is the same as reading it on the chart and then
restricting. -/
theorem map_chartSectionsIso_hom {V V' : s.relativeProj.Opens} (hV'V : V' ≤ V)
    (x : Γ(relativeProj s, V)) :
    ((relativeProjChart s W).app V').hom
        ((s.relativeProj.presheaf.map (homOfLE hV'V).op).hom x)
      = ((AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono (relativeProjChart s W) hV'V)).op).hom
          (((relativeProjChart s W).app V).hom x) := by
  have h := (relativeProjChart s W).naturality (homOfLE hV'V).op
  have h' := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp h) x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
  refine h'.trans (congrArg
    (fun g => (((AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).presheaf.map g).hom)
      (((relativeProjChart s W).app V).hom x)) (Subsingleton.elim _ _))

/-- **The inverse of `chartSectionsIso` commutes with the restriction maps.** -/
theorem chartSectionsIso_inv_map {V V' : s.relativeProj.Opens}
    (hV : V ≤ (relativeProjChart s W).opensRange) (hV'V : V' ≤ V)
    (z : Γ(AlgebraicGeometry.Proj (s.sectionRingGrading W.1),
      relativeProjChart s W ⁻¹ᵁ V)) :
    (chartSectionsIso s W (hV'V.trans hV)).inv.hom
        (((AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono (relativeProjChart s W) hV'V)).op).hom z)
      = (s.relativeProj.presheaf.map (homOfLE hV'V).op).hom
          ((chartSectionsIso s W hV).inv.hom z) := by
  refine injective_app_relativeProjChart s W (hV'V.trans hV) ?_
  refine (chartSectionsIso_hom_inv_apply s W (hV'V.trans hV) _).trans ?_
  refine Eq.symm ((map_chartSectionsIso_hom s W hV'V _).trans ?_)
  exact congrArg (((AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).presheaf.map
      (homOfLE (Scheme.Hom.preimage_mono (relativeProjChart s W) hV'V)).op).hom)
    (chartSectionsIso_hom_inv_apply s W hV z)

end Stacks.RelativeProj.Situation

end
