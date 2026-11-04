module

public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteTypeClosedInFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection

/-!
# Closed subschemes of finite presentation of a cofiltered limit, as subobjects

Let `c` be a limit cone on a cofiltered diagram `N` of quasi-compact and quasi-separated schemes
with affine transition morphisms. A closed subscheme of finite presentation of the limit is the
inverse image of a closed subscheme of finite presentation of a stage, and two closed subschemes
of finite presentation of a stage with the same inverse image in the limit already have the same
inverse image at a later stage. This file states both facts in the language of subobjects, which
is the language of the correspondence between closed subspaces of an algebraic space and
invariant closed subschemes of a chart.

## Main results

* `AlgebraicGeometry.exists_pullback_subobject_eq_of_isLimit`: a closed subobject of finite
  presentation of the limit is the pullback of one of a stage (Stacks 01ZM, 01ZP).
* `AlgebraicGeometry.exists_pullback_subobject_le_of_isLimit` and
  `AlgebraicGeometry.exists_pullback_subobject_eq_of_isLimit_of_eq`: inclusions and equalities of
  closed subobjects of finite presentation over the limit hold at a later stage (Stacks 01ZM,
  part (2)).
* `AlgebraicGeometry.isPullback_pullbackCone_π_app`: the stages of the base change of a limit
  cone along a morphism to one stage are fibre products of the limit with the stages.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

section Subobjects

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (N : I ⥤ Scheme.{u}) (c : Cone N)
  (hc : IsLimit c) [∀ {i j : I} (e : i ⟶ j), IsAffineHom (N.map e)]
  [∀ i, CompactSpace (N.obj i)] [∀ i, QuasiSeparatedSpace (N.obj i)]

/-- A morphism of finite presentation precomposed with an isomorphism is of finite
presentation. -/
theorem FinitePresentation.iso_comp {X X' Y : Scheme.{u}} (e : X' ≅ X) {g : X ⟶ Y}
    (hg : FinitePresentation g) : FinitePresentation (e.hom ≫ g) :=
  FinitePresentation.comp ⟨inferInstance, inferInstance, inferInstance⟩ hg

/-- A closed subobject is the closed subscheme cut out by the kernel of its arrow. -/
theorem Subobject.eq_mk_ker_subschemeι {X : Scheme.{u}} (C : Subobject X)
    [IsClosedImmersion C.arrow] : C = Subobject.mk C.arrow.ker.subschemeι := by
  conv_lhs => rw [← Subobject.mk_arrow C]
  exact Subobject.mk_eq_mk_of_comm _ _ (asIso C.arrow.toImage) C.arrow.toImage_imageι

include hc in
/-- **A closed subobject of finite presentation of the limit comes from a stage.** -/
theorem exists_pullback_subobject_eq_of_isLimit (C : Subobject c.pt)
    [IsClosedImmersion C.arrow] (hC : FinitePresentation C.arrow) :
    ∃ (i : I) (Cᵢ : Subobject (N.obj i)), IsClosedImmersion Cᵢ.arrow ∧
      FinitePresentation Cᵢ.arrow ∧ (Subobject.pullback (c.π.app i)).obj Cᵢ = C := by
  have hK : FinitePresentation C.arrow.ker.subschemeι := by
    have h := FinitePresentation.iso_comp (asIso C.arrow.toImage).symm hC
    have he : inv C.arrow.toImage ≫ C.arrow = C.arrow.ker.subschemeι := by
      rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
    rwa [Iso.symm_hom, asIso_inv, he] at h
  obtain ⟨i, J, hJ, hJK⟩ := Stacks.Hilbert.exists_closed_model N c hc C.arrow.ker hK
  refine ⟨i, Subobject.mk J.subschemeι, ?_, ?_, ?_⟩
  · rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    infer_instance
  · rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    exact FinitePresentation.iso_comp _ hJ
  · rw [Scheme.IdealSheafData.pullback_subobject_mk_subschemeι, hJK]
    exact (Subobject.eq_mk_ker_subschemeι C).symm

include hc in
/-- **An inclusion of closed subobjects of finite presentation over the limit holds at a later
stage.** -/
theorem exists_pullback_subobject_le_of_isLimit (i : I) (C₁ C₂ : Subobject (N.obj i))
    (h₁ : FinitePresentation C₁.arrow) (h₂ : FinitePresentation C₂.arrow)
    (h : (Subobject.pullback (c.π.app i)).obj C₁ ≤ (Subobject.pullback (c.π.app i)).obj C₂) :
    ∃ (j : I) (e : j ⟶ i),
      (Subobject.pullback (N.map e)).obj C₁ ≤ (Subobject.pullback (N.map e)).obj C₂ := by
  let Y₁ : Over (N.obj i) := Over.mk C₁.arrow
  let Y₂ : Over (N.obj i) := Over.mk C₂.arrow
  rw [Subobject.pullback_obj, Subobject.pullback_obj] at h
  let g : (Over.pullback (c.π.app i)).obj Y₁ ⟶ (Over.pullback (c.π.app i)).obj Y₂ :=
    Over.homMk (Subobject.ofMkLEMk _ _ h) (Subobject.ofMkLEMk_comp h)
  obtain ⟨j, e, g', -, -, -, -, -⟩ :=
    exists_morphism_after_baseChange N c hc i Y₁ Y₂ h₁ h₂ g
  refine ⟨j, e, ?_⟩
  rw [Subobject.pullback_obj, Subobject.pullback_obj]
  exact Subobject.mk_le_mk_of_comm g'.left (Over.w g')

include hc in
/-- **An equality of closed subobjects of finite presentation over the limit holds at a later
stage.** -/
theorem exists_pullback_subobject_eq_of_isLimit_of_eq (i : I) (C₁ C₂ : Subobject (N.obj i))
    (h₁ : FinitePresentation C₁.arrow) (h₂ : FinitePresentation C₂.arrow)
    (h : (Subobject.pullback (c.π.app i)).obj C₁ = (Subobject.pullback (c.π.app i)).obj C₂) :
    ∃ (j : I) (e : j ⟶ i),
      (Subobject.pullback (N.map e)).obj C₁ = (Subobject.pullback (N.map e)).obj C₂ := by
  obtain ⟨j, e, hj⟩ := exists_pullback_subobject_le_of_isLimit N c hc i C₁ C₂ h₁ h₂ h.le
  obtain ⟨k, f, hk⟩ := exists_pullback_subobject_le_of_isLimit N c hc i C₂ C₁ h₂ h₁ h.ge
  obtain ⟨l, a, b, hab⟩ := IsCofiltered.cospan e f
  refine ⟨l, a ≫ e, le_antisymm ?_ ?_⟩
  · simpa [Subobject.pullback_comp] using (Subobject.pullback (N.map a)).monotone hj
  · rw [hab]
    simpa [Subobject.pullback_comp] using (Subobject.pullback (N.map b)).monotone hk

end Subobjects

section PullbackCone

variable {I : Type u} [Category.{u} I] {T : Scheme.{u}} (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- **The stages of a base changed limit cone are fibre products.** For `f : T ⟶ D i`, the leg at
`j ≥ i` of the base change of `c` along `f` exhibits `c.pt ×_{D i} T` as the fibre product of
`c.pt` and `D j ×_{D i} T` over `D j`. -/
theorem isPullback_pullbackCone_π_app (i : I) (f : T ⟶ D.obj i) (j : Over i) :
    IsPullback ((pullbackCone D c i f).π.app j) (pullback.fst (c.π.app i) f)
      (pullback.fst (D.map j.hom) f) (c.π.app j.left) := by
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback (D.map j.hom) f).flip
  · have h1 : (pullbackCone D c i f).π.app j ≫ pullback.snd (D.map j.hom) f =
        pullback.snd (c.π.app i) f := by
      rw [pullbackCone_π_app]
      exact pullback.lift_snd _ _ _
    rw [h1, c.w]
    exact (IsPullback.of_hasPullback (c.π.app i) f).flip
  · rw [pullbackCone_π_app]
    exact pullback.lift_fst _ _ _

end PullbackCone

end AlgebraicGeometry

end
