module

public import StacksFrontier.AlgebraicGeometry.CoefficientIso.Unit
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartRestriction
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.Transverse
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictSections
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine

/-!
# Reading the restriction of relative differential forms to a chart on sections

The Gysin map of a chart is built by moving the whole situation onto the open subscheme
`W.toScheme`, and the move is performed by the isomorphism
`Stacks.AlgebraicGeometry.DifferentialsRestrict.relativeDifferentialFormsRestrictIso` of
[Stacks, Tag 0FLV]. To compare the resulting map with the class map of [Stacks, Tag 0G7Q] of the
same chart one has to know what that isomorphism *does to a section*, and this file says so: it
is the pullback `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback` of the form
along the open immersion.

The mechanism is that the isomorphism is built from
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and
`Stacks.Tag01XLCoefficientIso.unit_pullbackPushforwardAdjunction_app_app` already reads that
natural isomorphism on sections: the unit of `f^* ⊣ f_*` at an open immersion is a single
presheaf restriction map followed by it.

## Main results

* `Stacks.Gysin.toRestrictForms_app`: **the comparison `(Ω^n_{X/S})|_{X'} ⟶ Ω^n_{X'/S'}` on
  sections is the pullback of the form.**
* `Stacks.Gysin.relativeDifferentialFormsRestrictIsoOfEq_hom_app`: the same for the
  isomorphism of an open subscheme, in the spelling the chart construction uses.
* `Stacks.Gysin.gysinWedgeOnHom`: right multiplication by the equation wedge of a chart, as a
  morphism of the restrictions to the chart, with
  `Stacks.Gysin.restrictSections_gysinWedgeOnHom` reading it on sections.
* `Stacks.Gysin.relativeDifferentialFormsRestrictIso_hom_comp_gysinWedgeHom`: **the equation
  wedge of a chart is the equation wedge of the chart's own global equations**, transported by
  the identification of the forms. This is the wedge half of the Gysin formula for a chart.

## References

* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.DifferentialsRestrict
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

namespace Stacks.Gysin

variable {X X' S S' : Scheme.{u}}

/-! ### The identification of the forms of an open subscheme, on sections -/

/-- **The comparison `(Ω^n_{X/S})|_{X'} ⟶ Ω^n_{X'/S'}` of [Stacks, Tag 0FLV], on sections, is
the pullback of the form along the open immersion.** The comparison is
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` followed by the canonical map of
the square, and the unit of `f^* ⊣ f_*` at an open immersion is the presheaf restriction map
`Γ(ℱ, U) ⟶ Γ(ℱ, f ''ᵁ f ⁻¹ᵁ U)` followed by that same isomorphism, which is
`Stacks.Tag01XLCoefficientIso.unit_pullbackPushforwardAdjunction_app_app`. -/
theorem toRestrictForms_app (f : X' ⟶ X) [IsOpenImmersion f] (π : X ⟶ S) (π' : X' ⟶ S')
    (t : S' ⟶ S) (hcomm : f ≫ π = π' ≫ t) (n : ℤ) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms π n, U)) :
    Scheme.Modules.Hom.app (toRestrictForms f π π' t hcomm n) (f ⁻¹ᵁ U)
        ((relativeDifferentialForms π n).presheaf.map
          (homOfLE (f.image_preimage_le U)).op ω)
      = relativeDifferentialFormsPullback f π π' t hcomm n U ω := by
  have h : Stacks.Tag01VSPullbackTensor.modulesPullbackUnit f
        (relativeDifferentialForms π n) U ω =
      Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app (relativeDifferentialForms π n))
        (f ⁻¹ᵁ U)
        ((relativeDifferentialForms π n).presheaf.map
          (homOfLE (f.image_preimage_le U)).op ω) :=
    ConcreteCategory.congr_hom
      (Stacks.Tag01XLCoefficientIso.unit_pullbackPushforwardAdjunction_app_app f
        (relativeDifferentialForms π n) U) ω
  exact congrArg
    (Scheme.Modules.Hom.app (relativeDifferentialFormsMap f π π' t hcomm n) (f ⁻¹ᵁ U)) h.symm

/-- **The identification `(Ω^n_{X/S})|_W ≅ Ω^n_{W/S'}` of an open subscheme, on sections**: it
carries a form to its pullback along the inclusion of the open subscheme. -/
theorem relativeDifferentialFormsRestrictIsoOfEq_hom_app (π : X ⟶ S) (W : X.Opens)
    {π' : W.toScheme ⟶ S} (hπ' : W.ι ≫ π = π') (n : ℤ) (U : X.Opens)
    (ω : Γ(relativeDifferentialForms π n, U)) :
    Scheme.Modules.Hom.app (relativeDifferentialFormsRestrictIsoOfEq π W hπ' n).hom
        (W.ι ⁻¹ᵁ U)
        ((relativeDifferentialForms π n).presheaf.map
          (homOfLE (W.ι.image_preimage_le U)).op ω)
      = relativeDifferentialFormsPullback W.ι π π' (𝟙 S)
          (by rw [hπ', Category.comp_id]) n U ω :=
  toRestrictForms_app W.ι π π' (𝟙 S) _ n U ω

/-- **The identification of a restricted direct image with the direct image of the restriction,
on sections.** `Stacks.Modules.pushforwardRestrictFunctorIso` is built from the equality of the
two composite functors of opens `U ↦ q ⁻¹ᵁ (V.ι ''ᵁ U)` and `U ↦ (q ⁻¹ᵁ V).ι ''ᵁ ((q ∣_ V) ⁻¹ᵁ U)`
of `AlgebraicGeometry.image_morphismRestrict_preimage`, so on sections it is the restriction map
along that equality. -/
theorem pushforwardRestrictFunctorIso_hom_app_app {P Q : Scheme.{u}} (q : P ⟶ Q) (V : Q.Opens)
    (M : P.Modules) (U' : V.toScheme.Opens) (m : Γ(M, q ⁻¹ᵁ (V.ι ''ᵁ U'))) :
    Scheme.Modules.Hom.app
        ((Stacks.Modules.pushforwardRestrictFunctorIso q V).hom.app M) U' m =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage q V U')).op m := rfl

/-- Every open of an open subscheme is the preimage of an open of the ambient scheme contained
in it. This is the device by which a statement about the sections of a restriction over an
arbitrary open of the chart is reduced to one over an open of the ambient scheme, which is the
shape the lemmas above come in. -/
theorem exists_ambient_preimage_eq (W : X.Opens) (U' : W.toScheme.Opens) :
    ∃ (U : X.Opens) (_ : U ≤ W), W.ι ⁻¹ᵁ U = U' :=
  ⟨W.ι ''ᵁ U', Scheme.Opens.ι_image_le W U', W.ι.preimage_image_eq U'⟩

/-- Two restriction maps of a sheaf of modules between the same two opens agree, because the
morphisms of the poset of opens between two opens form a subsingleton. -/
theorem modules_presheaf_map_congr {Y : Scheme.{u}} {M : Y.Modules} {U U' : Y.Opens}
    (g g' : op U ⟶ op U') (y : Γ(M, U)) : M.presheaf.map g y = M.presheaf.map g' y :=
  congrArg (fun t => M.presheaf.map t y) (Subsingleton.elim g g')

/-- Two successive restriction maps of a sheaf of modules compose to one. -/
theorem modules_presheaf_map_comp_apply {Y : Scheme.{u}} {M : Y.Modules} {U V T : Y.Opens}
    (g : op U ⟶ op V) (g' : op V ⟶ op T) (y : Γ(M, U)) :
    M.presheaf.map g' (M.presheaf.map g y) = M.presheaf.map (g ≫ g') y :=
  (ConcreteCategory.congr_hom (M.presheaf.map_comp g g') y).symm

/-! ### The equation wedge of a chart as a morphism of restrictions -/

/-- **Right multiplication by the equation wedge `d f₁ ∧ ⋯ ∧ d f_c` of a chart, as a morphism of
the restrictions to the chart.** The sectionwise family `Stacks.Gysin.gysinWedgeOn` is additive,
`𝒪_X`-homogeneous and compatible with restriction, which is exactly the data
`Stacks.AlgebraicGeometry.ModuleLimits.homOfRestrictSections` consumes. -/
def gysinWedgeOnHom (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W)) (p : ℤ) :
    Scheme.Modules.restrict (relativeDifferentialForms π p) W.ι ⟶
      Scheme.Modules.restrict (relativeDifferentialForms π (p + (c : ℤ))) W.ι :=
  homOfRestrictSections W (fun _ hV => gysinWedgeOn π f p hV)
    (fun _ hV => gysinWedgeOn_add π f p hV)
    (fun _ hV => gysinWedgeOn_smul π f p hV)
    (fun _ _ hUV hV m => (gysinWedgeOn_map π f p hV hUV m).symm)

/-- On sections over an open `V ≤ W`, `Stacks.Gysin.gysinWedgeOnHom` is right multiplication
`Stacks.Gysin.gysinWedgeOn` by the equation wedge of the chart. -/
@[simp]
theorem restrictSections_gysinWedgeOnHom (π : X ⟶ S) {W : X.Opens} {c : ℕ}
    (f : Fin c → Γ(X, W)) (p : ℤ) (V : X.Opens) (hV : V ≤ W)
    (ω : Γ(relativeDifferentialForms π p, V)) :
    restrictSections (gysinWedgeOnHom π f p) V hV ω = gysinWedgeOn π f p hV ω :=
  restrictSections_homOfRestrictSections _ _ _ _ _ V hV ω

/-- The identification `(Ω^n_{X/S})|_W ≅ Ω^n_{W/S}` of an open subscheme over the same base, on
sections: it carries a form to its pullback along `W.ι`. -/
theorem relativeDifferentialFormsRestrictIso_hom_app (π : X ⟶ S) (W : X.Opens) (n : ℤ)
    (U : X.Opens) (ω : Γ(relativeDifferentialForms π n, U)) :
    Scheme.Modules.Hom.app (relativeDifferentialFormsRestrictIso π W n).hom (W.ι ⁻¹ᵁ U)
        ((relativeDifferentialForms π n).presheaf.map
          (homOfLE (W.ι.image_preimage_le U)).op ω)
      = relativeDifferentialFormsPullback W.ι π (W.ι ≫ π) (𝟙 S)
          (Category.comp_id (W.ι ≫ π)).symm n U ω :=
  relativeDifferentialFormsRestrictIsoOfEq_hom_app π W rfl n U ω

/-- A chart's equation, restricted to an open `U ≤ W` and read on the chart, is the chart's own
global equation restricted. Both are restriction maps of `𝒪_X` out of `Γ(X, W)`. -/
theorem app_ι_restrict_eq (W : X.Opens) {c : ℕ} (f : Fin c → Γ(X, W))
    {U : X.Opens} (hU : U ≤ W) (j : Fin c) :
    (W.ι.app U).hom (X.presheaf.map (homOfLE hU).op (f j)) =
      W.toScheme.presheaf.map (homOfLE (show W.ι ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        (restrictEquations W f j) :=
  (presheaf_map_comp_apply _ _ (f j)).trans
    ((presheaf_map_congr _ _ (f j)).trans (presheaf_map_comp_apply _ _ (f j)).symm)

/-- **The wedge half of the Gysin formula of a chart.** Wedging with the equation wedge of the
chart's equations, read on the chart through the identification of the forms, is wedging with
the equation wedge of the chart's own global equations. This is
`Stacks.Gysin.relativeDifferentialFormsPullback_gysinWedgeOn` at the open immersion `W.ι`. -/
theorem gysinWedgeHom_app_relativeDifferentialFormsRestrictIso (π : X ⟶ S) (W : X.Opens)
    {c : ℕ} (f : Fin c → Γ(X, W)) (p : ℤ) (U : X.Opens) (hU : U ≤ W)
    (ω : Γ(relativeDifferentialForms π p, U)) :
    Scheme.Modules.Hom.app (gysinWedgeHom (W.ι ≫ π) (restrictEquations W f) p) (W.ι ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app (relativeDifferentialFormsRestrictIso π W p).hom (W.ι ⁻¹ᵁ U)
          ((relativeDifferentialForms π p).presheaf.map
            (homOfLE (W.ι.image_preimage_le U)).op ω))
      = Scheme.Modules.Hom.app
          (relativeDifferentialFormsRestrictIso π W (p + (c : ℤ))).hom (W.ι ⁻¹ᵁ U)
          ((relativeDifferentialForms π (p + (c : ℤ))).presheaf.map
            (homOfLE (W.ι.image_preimage_le U)).op (gysinWedgeOn π f p hU ω)) := by
  rw [relativeDifferentialFormsRestrictIso_hom_app, relativeDifferentialFormsRestrictIso_hom_app,
    ← gysinWedgeOn_restrict π f p hU ω,
    relativeDifferentialFormsPullback_gysinWedgeOn W.ι π (W.ι ≫ π) (𝟙 S)
      (Category.comp_id (W.ι ≫ π)).symm (fun j => X.presheaf.map (homOfLE hU).op (f j)) p ω]
  refine Eq.trans (gysinWedgeOn_top (W.ι ≫ π) (restrictEquations W f) p (W.ι ⁻¹ᵁ U) _).symm ?_
  refine Eq.trans (gysinWedgeOn_restrict (W.ι ≫ π) (restrictEquations W f) p
    (show W.ι ⁻¹ᵁ U ≤ ⊤ from le_top) _).symm ?_
  exact congrArg
    (fun g : Fin c → Γ(W.toScheme, W.ι ⁻¹ᵁ U) =>
      gysinWedgeOn (W.ι ≫ π) g p (le_refl (W.ι ⁻¹ᵁ U))
        (relativeDifferentialFormsPullback W.ι π (W.ι ≫ π) (𝟙 S)
          (Category.comp_id (W.ι ≫ π)).symm p U ω))
    (funext fun j => (app_ι_restrict_eq W f hU j).symm)

end Stacks.Gysin

end
