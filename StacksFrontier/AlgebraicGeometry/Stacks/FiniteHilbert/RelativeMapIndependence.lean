module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocus
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SlicePointIso
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverPointIso

/-!
# Independence of the relative map from the choices made

Let `(U, Z, y, x, α)` be an object of the relative finite Hilbert category `ℋ_d(𝒳/𝒴)` of a
1-morphism `F : 𝒳 ⟶ 𝒴` of stacks in groupoids. The relative map `x_α : Z ⟶ X_y` of Stacks 06CK
is built from choices: a scheme-valued point of `𝒴` over `U` extending `y`, an algebraic space
`X_y` representing the 2-fibre product of `F` with it, and an equivalence exhibiting the
representation. The remark following Stacks 06CK says the result does not depend on these
choices: any two sets of choices give relative maps which differ by an isomorphism of the
targets. Consequently membership of the local complete intersection locus of Stacks 06CJ may be
tested on a single set of choices.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.exists_iso_map_comp`: two sets of data
  exhibiting the relative map give maps `Z ⟶ X_y` and `Z ⟶ X'_y` which differ by an
  isomorphism `X_y ≅ X'_y`.
* `AlgebraicGeometry.Stack.FiniteHilbert.lciLocus_of_relativeMapData`: an object of `ℋ_d(𝒳/𝒴)`
  whose relative map for one set of choices is unramified and a local complete intersection
  morphism lies in the local complete intersection locus.

## References

* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
-/

@[expose] public section

open CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry.Stack.FiniteHilbert

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ} {P : Object B S hS 𝒳 𝒴 F d}

/-- The structure morphism of the cover of a quintuple, read over its base, is the morphism to
the tautological object of the big fppf site of the base. -/
theorem Object.coverToBase_eq_toTautological (P : Object B S hS 𝒳 𝒴 F d) :
    P.coverToBase = StacksRepresentableCFG.toTautological P.coverOver :=
  Limits.IsTerminal.hom_ext Over.mkIdTerminal _ _

/-- **The relative map of Stacks 06CK does not depend on the choices made.** Two sets of data
exhibiting the relative map of an object of `ℋ_d(𝒳/𝒴)` give morphisms `Z ⟶ X_y` and
`Z ⟶ X'_y` which differ by an isomorphism `X_y ≅ X'_y` of the representing presheaves. -/
theorem RelativeMapData.exists_iso_map_comp (D₁ D₂ : RelativeMapData P) :
    ∃ φ : D₁.Xy ≅ D₂.Xy, D₁.map.hom ≫ φ.hom = D₂.map.hom := by
  have hY := 𝒴.isStackInGroupoids.isFiberedInGroupoids
  have hfib := hY.fiber_isGroupoid P.U
  have hu₁ := D₁.yUnit_over
  have hu₂ := D₂.yUnit_over
  have : IsIso D₂.yUnit := Functor.isIso_of_fiber_isGroupoid hfib D₂.yUnit D₂.yUnit_over
  have : IsIso D₁.yUnit := Functor.isIso_of_fiber_isGroupoid hfib D₁.yUnit D₁.yUnit_over
  let θ₀ : D₁.y.obj P.baseOver ≅ D₂.y.obj P.baseOver := asIso D₁.yUnit ≪≫ (asIso D₂.yUnit).symm
  have hb : (Over.map P.U.hom).obj (Over.mk (𝟙 P.U.left)) = P.U :=
    (Functor.congr_obj D₁.y_comp P.baseOver).symm.trans
      (IsHomLift.domain_eq 𝒴.toBasedCategory.p (𝟙 P.U) D₁.yUnit)
  have hθ₀ : 𝒴.toBasedCategory.p.IsHomLift
      (𝟙 ((Over.map P.U.hom).obj (Over.mk (𝟙 P.U.left)))) θ₀.hom := by
    rw [hb]
    have h2 : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) (inv D₂.yUnit) :=
      IsHomLift.lift_id_inv_isIso _ _ D₂.yUnit
    change 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) (D₁.yUnit ≫ inv D₂.yUnit)
    simpa using IsHomLift.comp 𝒴.toBasedCategory.p (𝟙 P.U) (𝟙 P.U) D₁.yUnit (inv D₂.yUnit)
  obtain ⟨θ, hθ, hθid⟩ := StacksRepresentableCFG.exists_natIso_of_iso_at_id_app_id P.U.hom
    D₁.y D₂.y D₁.y_comp D₂.y_comp hY θ₀ hθ₀
  have hcover : θ.hom.app P.coverOver = D₁.α.hom ≫ D₂.α.inv := by
    have hc₂ : 𝒴.toBasedCategory.p.IsHomLift ((Over.map P.U.hom).map P.coverToBase)
        (D₂.y.map P.coverToBase) :=
      Functor.isHomLift_map_of_comp_eq D₂.y_comp _ P.coverToBase
    have : 𝒴.toBasedCategory.p.IsStronglyCartesian ((Over.map P.U.hom).map P.coverToBase)
        (D₂.y.map P.coverToBase) :=
      hY.isStronglyCartesian_homLift _ _
    have h1 := hθ P.coverOver
    have hα₁ := D₁.α_over
    have hα₂ := D₂.α_over
    have hα₂' : 𝒴.toBasedCategory.p.IsHomLift (𝟙 ((Over.map P.U.hom).obj P.coverOver))
        D₂.α.inv := IsHomLift.lift_id_inv _ _ D₂.α
    have h2 : 𝒴.toBasedCategory.p.IsHomLift (𝟙 ((Over.map P.U.hom).obj P.coverOver))
        (D₁.α.hom ≫ D₂.α.inv) := by
      simpa using IsHomLift.comp 𝒴.toBasedCategory.p (𝟙 ((Over.map P.U.hom).obj P.coverOver))
        (𝟙 ((Over.map P.U.hom).obj P.coverOver)) D₁.α.hom D₂.α.inv
    refine Functor.IsCartesian.ext 𝒴.toBasedCategory.p ((Over.map P.U.hom).map P.coverToBase)
      (D₂.y.map P.coverToBase) _ _ ?_
    have hθid' : θ.hom.app P.baseOver = D₁.yUnit ≫ inv D₂.yUnit := hθid
    rw [← θ.hom.naturality P.coverToBase, hθid', ← cancel_mono D₂.yUnit]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← cancel_epi D₁.α.inv]
    simpa using D₁.α_comp.trans D₂.α_comp.symm
  have hiso : θ.inv.app P.coverOver ≫ D₁.α.hom = D₂.α.hom := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, hcover, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have key : ∀ (β : D₂.y.obj P.coverOver ≅ F.toFunctor.obj P.x)
      (hβ : 𝒴.toBasedCategory.p.IsHomLift (𝟙 ((Over.map P.U.hom).obj P.coverOver)) β.hom),
      β = D₂.α → relativeObj F D₂.y P.coverOver P.x P.x_over_coverOver β hβ =
        relativeObj F D₂.y P.coverOver P.x P.x_over_coverOver D₂.α D₂.α_over := by
    rintro β hβ rfl
    rfl
  refine ⟨TwoFibreProductOver.mapFstIsoPresheafIso θ hθ D₁.e D₂.e, ?_⟩
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  change (TwoFibreProductOver.mapFstIsoPresheafIso θ hθ D₁.e D₂.e).hom.app (op P.coverOver)
      (yonedaEquiv (relativeMap F D₁.y D₁.e D₁.isAlgebraicSpace P.coverOver P.x
        P.x_over_coverOver D₁.α D₁.α_over).hom) =
    yonedaEquiv (relativeMap F D₂.y D₂.e D₂.isAlgebraicSpace P.coverOver P.x
        P.x_over_coverOver D₂.α D₂.α_over).hom
  rw [yonedaEquiv_relativeMap_hom, yonedaEquiv_relativeMap_hom]
  refine (TwoFibreProductOver.mapFstIsoPresheafIso_hom_app_sectionOfObj θ hθ D₁.e D₂.e
    (relativeObj F D₁.y P.coverOver P.x P.x_over_coverOver D₁.α D₁.α_over) rfl).trans ?_
  have hobj := key ((θ.app P.coverOver).symm ≪≫ D₁.α)
    ((TwoFibreProductOver.mapFstIso θ hθ).obj
      (relativeObj F D₁.y P.coverOver P.x P.x_over_coverOver D₁.α D₁.α_over)).vertical
    (Iso.ext hiso)
  have hsec : ∀ (R R' : TwoFibreProductOver (Over.map P.U.hom) 𝒳.toBasedCategory.p
      𝒴.toBasedCategory.p D₂.y F.toFunctor) (hR : R = R') (h : R.x = P.coverOver)
      (h' : R'.x = P.coverOver), PresheafOfCategories.sectionOfObj D₂.e R h =
        PresheafOfCategories.sectionOfObj D₂.e R' h' := by
    rintro R _ rfl h h'
    rfl
  exact hsec _ _ hobj _ _

/-- **Membership of the local complete intersection locus can be tested on one set of
choices.** An object of `ℋ_d(𝒳/𝒴)` whose relative map, for one set of data exhibiting it, is
unramified and a local complete intersection morphism lies in `ℋ_{d,lci}(𝒳/𝒴)`. -/
theorem lciLocus_of_relativeMapData (D : RelativeMapData P)
    (hD : Space.IsUnramified B P.U.left.1 P.U.left.2 D.map.hom ∧
      Space.IsLocalCompleteIntersection B P.U.left.1 P.U.left.2 D.map.hom) :
    lciLocus (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d) P := by
  intro D'
  obtain ⟨φ, hφ⟩ := D.exists_iso_map_comp D'
  rw [← hφ]
  exact ⟨(Space.holdsOnEveryEtaleChart_comp_iso_iff B P.U.left.1 P.U.left.2 _ _ φ.hom).2 hD.1,
    (Space.holdsOnEveryEtaleChart_comp_iso_iff B P.U.left.1 P.U.left.2 _ _ φ.hom).2 hD.2⟩

end AlgebraicGeometry.Stack.FiniteHilbert

end
