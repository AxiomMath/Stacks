module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal.Det
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartSection
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal.GlueIso
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal.RankZero
public import StacksFrontier.Homology.TwoTermComplex.DeterminantBaseChangeMapFlat
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist

/-!
# The two constructions of the determinant on a scheme agree

Let `X` be a scheme and `L` a perfect object of `D(𝒪_X)` of Tor amplitude in `[-1, 0]`. The
determinant of Stacks 0FJX is constructed twice in this library:

* `AlgebraicGeometry.DeterminantTwoTerm.globalDet`, the value of the determinant functor
  `AlgebraicGeometry.DeterminantTwoTerm.determinantFunctor`, glued by the glueing datum
  `AlgebraicGeometry.DeterminantTwoTerm.chartComparison` from the determinants on the affine
  charts, whose comparisons are flat base changes `TwoTermDeterminant.detBaseChange`;
* `AlgebraicGeometry.DeterminantTwoTerm.detModule`, glued from the system of local determinants
  `det(M_V)` of More on Algebra, Section 0FJI, whose restriction maps are the base change maps
  `TwoTermDeterminant.baseChangeMap` of the transition isomorphisms.

This file proves that they agree. The transition isomorphisms of the two constructions are the
same (`sourceComplexRestrictionIso_eq_symm_transitionIso`), so the comparisons of the glueing
datum are the restriction maps of the system (`chartRestrictDet_eq_localDetMap`); the sections of
`globalDet L` over an affine open `V` are `det(M_V)` (`globalDetSectionsEquiv`), compatibly with
restriction, and `detModuleIso` is the resulting isomorphism. It carries the canonical section
`deltaSection` to the canonical section `determinantSection` of Stacks 0FJX, and the two notions
of rank zero agree (`isRankZero_iff_isRankZeroOn`).

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.globalDetSectionsEquiv`: `det(M_V) ≅ Γ(globalDet L, V)`.
* `AlgebraicGeometry.DeterminantTwoTerm.detModuleIso`: `detModule L ≅ globalDet L`.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.detModuleIso_hom_app`: on affine opens the isomorphism is
  the identity of `det(M_V)`.
* `AlgebraicGeometry.DeterminantTwoTerm.detModuleIso_hom_deltaSection`: it carries `δ` to `δ`.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite TwoTermDeterminant
open AlgebraicGeometry.StandardModel
open scoped TensorProduct

namespace AlgebraicGeometry.DeterminantTwoTerm

variable {X : Scheme.{u}}

/-! ### The transition isomorphisms agree -/

/-- A composite of isomorphisms followed by the composite of their inverses, in the reverse
order, is the identity. Isolated on variables. -/
theorem comp_inv_cancel {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ : C} (α : X₀ ≅ X₁)
    (φ : X₂ ≅ X₁) (γ : X₃ ≅ X₂) (c : X₃ ⟶ X₄) [IsIso c] :
    (α.hom ≫ φ.inv ≫ γ.inv ≫ c) ≫ inv c ≫ γ.hom ≫ φ.hom ≫ α.inv = 𝟙 X₀ := by
  simp

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **The two transition isomorphisms of the chart complexes agree.** For affine opens `V ≤ W` of
`X`, the identification `sourceComplexRestrictionIso` of the chart complex on `V` with the derived
base change of the chart complex on `W`, used by the glueing datum of the determinant, is the
inverse of the transition isomorphism `transitionIso` along the factorisation
`Spec ρ ≫ W.fromSpec = V.fromSpec`, used by the system of local determinants. -/
theorem sourceComplexRestrictionIso_eq_symm_transitionIso (L : PerfectTwoTermAmplitude X)
    {V W : X.affineOpens} (h : V ≤ W) :
    sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe h) L =
      (transitionIso L (affineRestriction X h) W.2.fromSpec V.2.fromSpec
        (W.2.map_fromSpec V.2 (homOfLE (AffineOpensGlue.coe_le_coe h)).op)).symm := by
  have hh := W.2.map_fromSpec V.2 (homOfLE (AffineOpensGlue.coe_le_coe h)).op
  have hs : (tilde.functor Γ(X, (V.1 : X.Opens))).mapDerivedCategory.map
      (sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe h) L).hom =
        (localComplexIso L V.2.fromSpec).hom ≫
          (fac (Spec.map (affineRestriction X h)) W.2.fromSpec V.2.fromSpec hh L.obj).inv ≫
          (dpb (Spec.map (affineRestriction X h))).map (localComplexIso L W.2.fromSpec).inv ≫
          StandardModel.cmp (affineRestriction X h) (localComplex L W.2.fromSpec).obj :=
    (mapDerivedCategoryFullyFaithful Γ(X, (V.1 : X.Opens))).map_preimage _
  refine Iso.ext ((Iso.comp_hom_eq_id _).mp ?_)
  apply (mapDerivedCategoryFullyFaithful Γ(X, (V.1 : X.Opens))).map_injective
  have ht := tilde_map_transitionIso_hom L (affineRestriction X h) W.2.fromSpec V.2.fromSpec hh
  rw [Functor.map_comp]
  refine Eq.trans (congrArg₂ (fun a b => a ≫ b) hs ht) ?_
  refine Eq.trans ?_ (CategoryTheory.Functor.map_id _ _).symm
  exact comp_inv_cancel (localComplexIso L V.2.fromSpec)
    (fac (Spec.map (affineRestriction X h)) W.2.fromSpec V.2.fromSpec hh L.obj)
    ((dpb (Spec.map (affineRestriction X h))).mapIso (localComplexIso L W.2.fromSpec))
    (StandardModel.cmp (affineRestriction X h) (localComplex L W.2.fromSpec).obj)

/-! ### Elements of the determinant module as sections of the glued determinant -/

/-- A function on an affine open `U`, read as a global function on `U` and transported to
`Spec Γ(X, U)` along `isoSpec`, is the corresponding global function on `Spec Γ(X, U)`, restricted
to the image of `U`. -/
theorem appIso_inv_topIso_inv {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) :
    (hU.isoSpec.hom.appIso ⊤).inv (U.topIso.inv r) =
      (Spec Γ(X, U)).presheaf.map (homOfLE (le_top : hU.isoSpec.hom ''ᵁ ⊤ ≤ ⊤)).op
        ((Scheme.ΓSpecIso Γ(X, U)).inv r) := by
  have h1 := ConcreteCategory.congr_hom (Scheme.Hom.app_appIso_inv hU.isoSpec.hom ⊤)
    ((Scheme.ΓSpecIso Γ(X, U)).inv r)
  have h2 := ConcreteCategory.congr_hom (IsAffineOpen.isoSpec_hom_appTop hU)
    ((Scheme.ΓSpecIso Γ(X, U)).inv r)
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at h1 h2
  rw [← h2]
  exact h1

/-- Two restriction maps of the structure sheaf compose to a restriction map. -/
theorem presheaf_map_apply_eq {Y : Scheme.{u}} {U V W : Y.Opens} (a : op U ⟶ op W)
    (c : op U ⟶ op V) (b : op V ⟶ op W) (r : Γ(Y, U)) :
    Y.presheaf.map a r = Y.presheaf.map b (Y.presheaf.map c r) := by
  obtain rfl : a = c ≫ b := Subsingleton.elim _ _
  rw [Functor.map_comp, ConcreteCategory.comp_apply]

/-- `chartTop`, written with the restriction maps of the underlying presheaves of abelian
groups. -/
theorem chartTop_eq (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (x : chartDetModule L V) :
    chartTop L V x = Scheme.Modules.Hom.app (chartDetSpecRestrictIso L V).hom ⊤
      ((chartDetSpec L V).presheaf.map (homOfLE (le_top : V.2.isoSpec.hom ''ᵁ ⊤ ≤ ⊤)).op
        ((tilde.toOpen (chartDetModule L V) ⊤).hom x)) :=
  rfl

/-- `chartSection`, written with the restriction maps of the underlying presheaves of abelian
groups. -/
theorem chartSection_eq (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (x : chartDetModule L V) :
    chartSection L V x = (chartDet L V).presheaf.map
      (homOfLE (le_top : (V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens) ≤ ⊤)).op (chartTop L V x) :=
  rfl

/-- The global section of `x` on the open subscheme `V` is linear in `x`, the functions on `V`
acting through `topIso`. -/
theorem chartTop_smul (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (r : Γ(X, (V.1 : X.Opens))) (x : chartDetModule L V) :
    chartTop L V (r • x) = (V.1 : X.Opens).topIso.inv r • chartTop L V x := by
  have hc' := (appIso_inv_topIso_inv V.2 r).symm
  have e1 : (show Γ(chartDetSpec L V, ⊤) from (tilde.toOpen (chartDetModule L V) ⊤).hom (r • x)) =
      (Scheme.ΓSpecIso Γ(X, (V.1 : X.Opens))).inv r •
        (show Γ(chartDetSpec L V, ⊤) from (tilde.toOpen (chartDetModule L V) ⊤).hom x) := by
    refine ((tilde.toOpen (chartDetModule L V) ⊤).hom.map_smul r x).trans ?_
    refine (Scheme.Modules.smul_Spec_def (M := chartDetSpec L V) (U := ⊤) r
      ((tilde.toOpen (chartDetModule L V) ⊤).hom x)).trans ?_
    simp only [Opens.leTop, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
      CategoryTheory.id_apply]
  rw [chartTop_eq, chartTop_eq]
  refine (congrArg (fun z => Scheme.Modules.Hom.app (chartDetSpecRestrictIso L V).hom ⊤
    ((chartDetSpec L V).presheaf.map (homOfLE (le_top : V.2.isoSpec.hom ''ᵁ ⊤ ≤ ⊤)).op z))
    e1).trans ?_
  refine (congrArg (fun z => Scheme.Modules.Hom.app (chartDetSpecRestrictIso L V).hom ⊤ z)
    (Scheme.Modules.map_smul (chartDetSpec L V)
      (homOfLE (le_top : V.2.isoSpec.hom ''ᵁ ⊤ ≤ ⊤)) _ _)).trans ?_
  refine (congrArg (fun c => Scheme.Modules.Hom.app (chartDetSpecRestrictIso L V).hom ⊤
    (c • (chartDetSpec L V).presheaf.map (homOfLE (le_top : V.2.isoSpec.hom ''ᵁ ⊤ ≤ ⊤)).op
      (show Γ(chartDetSpec L V, ⊤) from (tilde.toOpen (chartDetModule L V) ⊤).hom x))) hc').trans ?_
  exact Scheme.Modules.Hom.app_smul (chartDetSpecRestrictIso L V).hom _ _

/-- The section of `x` on the chart of `V` is linear in `x`. -/
theorem chartSection_smul (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (r : Γ(X, (V.1 : X.Opens))) (x : chartDetModule L V) :
    (show Γ((Scheme.Modules.pushforward (AffineOpensGlue.chart X V)).obj (chartDet L V),
        (V.1 : X.Opens)) from chartSection L V (r • x)) =
      r • (show Γ((Scheme.Modules.pushforward (AffineOpensGlue.chart X V)).obj (chartDet L V),
        (V.1 : X.Opens)) from chartSection L V x) := by
  have hι : (AffineOpensGlue.chart X V).app (V.1 : X.Opens) r =
      ((V.1 : X.Opens) : Scheme.{u}).presheaf.map
        (homOfLE (le_top : (V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens) ≤ ⊤)).op
        ((V.1 : X.Opens).topIso.inv r) := by
    simp only [Scheme.Opens.ι_app, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map]
    exact presheaf_map_apply_eq _ _ _ r
  have e1 := Scheme.Modules.map_smul (chartDet L V)
    (homOfLE (le_top : (V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens) ≤ ⊤))
    ((V.1 : X.Opens).topIso.inv r) (chartTop L V x)
  refine (congrArg (fun z => (chartDet L V).presheaf.map
    (homOfLE (le_top : (V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens) ≤ ⊤)).op z)
    (chartTop_smul L V r x)).trans (e1.trans ?_)
  rw [← hι]
  rfl

/-- The section of `x` on the chart of `V` is additive in `x`. -/
theorem chartSection_add (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (x y : chartDetModule L V) :
    (show Γ((Scheme.Modules.pushforward (AffineOpensGlue.chart X V)).obj (chartDet L V),
        (V.1 : X.Opens)) from chartSection L V (x + y)) =
      (show Γ((Scheme.Modules.pushforward (AffineOpensGlue.chart X V)).obj (chartDet L V),
        (V.1 : X.Opens)) from chartSection L V x) +
      (show Γ((Scheme.Modules.pushforward (AffineOpensGlue.chart X V)).obj (chartDet L V),
        (V.1 : X.Opens)) from chartSection L V y) := by
  simp only [chartSection_eq, chartTop_eq, map_add]
  exact (congrArg (fun z => ConcreteCategory.hom ((chartDet L V).presheaf.map
      (homOfLE (le_top : (V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens) ≤ ⊤)).op)
      (ConcreteCategory.hom (Scheme.Modules.Hom.app (chartDetSpecRestrictIso L V).hom ⊤) z))
      (map_add (ConcreteCategory.hom ((chartDetSpec L V).presheaf.map
        (homOfLE (le_top : V.2.isoSpec.hom ''ᵁ ⊤ ≤ ⊤)).op)) _ _)).trans
    ((congrArg (fun z => ConcreteCategory.hom ((chartDet L V).presheaf.map
      (homOfLE (le_top : (V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens) ≤ ⊤)).op) z)
      (map_add (ConcreteCategory.hom
        (Scheme.Modules.Hom.app (chartDetSpecRestrictIso L V).hom ⊤)) _ _)).trans
      (map_add (ConcreteCategory.hom ((chartDet L V).presheaf.map
        (homOfLE (le_top : (V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens) ≤ ⊤)).op)) _ _))

/-- The sections map of an isomorphism of sheaves of modules is bijective. -/
theorem bijective_app_hom_of_iso {Y : Scheme.{u}} {A B : Y.Modules} (e : A ≅ B) (U : Y.Opens) :
    Function.Bijective (Scheme.Modules.Hom.app e.hom U) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨Scheme.Modules.Hom.app e.inv U, fun s => ?_, fun s => ?_⟩
  · exact (comp_app_apply e.hom e.inv U s).symm.trans (by rw [e.hom_inv_id]; rfl)
  · exact (comp_app_apply e.inv e.hom U s).symm.trans (by rw [e.inv_hom_id]; rfl)

/-- The restriction map of a sheaf of modules between two equal opens is bijective. -/
theorem bijective_presheaf_map_of_eq {Y : Scheme.{u}} (M : Y.Modules) {U U' : Y.Opens}
    (h : U' ≤ U) (e : U' = U) : Function.Bijective (M.presheaf.map (homOfLE h).op) := by
  subst e
  rw [show homOfLE h = 𝟙 U' from Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
  exact ⟨fun _ _ hab => hab, fun b => ⟨b, rfl⟩⟩

/-- **Reading an element of the determinant module as a section on the chart is bijective.** -/
theorem bijective_chartSection (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    Function.Bijective (chartSection L V) := by
  have b1 : Function.Bijective (tilde.toOpen (chartDetModule L V) ⊤).hom :=
    ConcreteCategory.bijective_of_isIso (tilde.toOpen (chartDetModule L V) ⊤)
  have b2 := bijective_presheaf_map_of_eq (chartDetSpec L V)
    (le_top : V.2.isoSpec.hom ''ᵁ ⊤ ≤ ⊤)
    ((V.2.isoSpec.hom.image_top_eq_opensRange).trans
      (Scheme.Hom.opensRange_of_isIso V.2.isoSpec.hom))
  have b3 := bijective_app_hom_of_iso (chartDetSpecRestrictIso L V) ⊤
  have b4 := bijective_presheaf_map_of_eq (chartDet L V)
    (le_top : (V.1 : X.Opens).ι ⁻¹ᵁ (V.1 : X.Opens) ≤ ⊤) (V.1 : X.Opens).ι_preimage_self
  exact b4.comp (b3.comp (b2.comp b1))

/-- **An element of the determinant module, read as a section on the chart**, as a linear
equivalence onto the sections over `V` of the pushforward of the determinant on `V`. -/
def chartSectionEquiv (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    chartDetModule L V ≃ₗ[Γ(X, (V.1 : X.Opens))]
      Γ((Scheme.Modules.pushforward (AffineOpensGlue.chart X V)).obj (chartDet L V),
        (V.1 : X.Opens)) :=
  LinearEquiv.ofBijective
    ({ toFun := fun x => chartSection L V x
       map_add' := chartSection_add L V
       map_smul' := chartSection_smul L V } :
      chartDetModule L V →ₗ[Γ(X, (V.1 : X.Opens))]
        Γ((Scheme.Modules.pushforward (AffineOpensGlue.chart X V)).obj (chartDet L V),
          (V.1 : X.Opens)))
    (bijective_chartSection L V)

/-- `chartSectionEquiv` is `chartSection`. -/
theorem chartSectionEquiv_apply (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (x : chartDetModule L V) : chartSectionEquiv L V x = chartSection L V x :=
  rfl

/-- Reading a section of the glued determinant on the chart of `V`, over `V`, as a linear map:
the sections map of the transposed chart isomorphism. -/
def chartSecₗ (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    Γ((globalDet L).obj, (V.1 : X.Opens)) →ₗ[Γ(X, (V.1 : X.Opens))]
      Γ((Scheme.Modules.pushforward (AffineOpensGlue.chart X V)).obj (chartDet L V),
        (V.1 : X.Opens)) where
  toFun t := Scheme.Modules.Hom.app ((chartComparison L).chartHom V) (V.1 : X.Opens) t
  map_add' s t := map_add (ConcreteCategory.hom
    (Scheme.Modules.Hom.app ((chartComparison L).chartHom V) (V.1 : X.Opens))) s t
  map_smul' r t := Scheme.Modules.Hom.app_smul ((chartComparison L).chartHom V) r t

/-- `chartSecₗ` is `chartSec`. -/
theorem chartSecₗ_apply (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (t : Γ((globalDet L).obj, (V.1 : X.Opens))) :
    chartSecₗ L V t = (chartComparison L).chartSec V (V.1 : X.Opens) t :=
  rfl

/-- **Reading a section of the glued determinant on the chart of `V`**, over `V`, as a linear
equivalence. -/
def chartSecEquiv (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    Γ((globalDet L).obj, (V.1 : X.Opens)) ≃ₗ[Γ(X, (V.1 : X.Opens))]
      Γ((Scheme.Modules.pushforward (AffineOpensGlue.chart X V)).obj (chartDet L V),
        (V.1 : X.Opens)) :=
  LinearEquiv.ofBijective (chartSecₗ L V)
    ⟨fun _ _ hst => (chartComparison L).chartSec_injective V le_rfl hst, fun y =>
      ⟨localAppFun ((chartComparison L).chartHomIso V).inv (V.1 : X.Opens) le_rfl y,
        (chartComparison L).chartSec_localAppFun_chartHomIso_inv V le_rfl y⟩⟩

/-- **The sections of the glued determinant over an affine open `V` are the determinant module
`det(M_V)` of More on Algebra, Section 0FJI of the chart complex.** -/
def globalDetSectionsEquiv (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    chartDetModule L V ≃ₗ[Γ(X, (V.1 : X.Opens))] Γ((globalDet L).obj, (V.1 : X.Opens)) :=
  (chartSectionEquiv L V).trans (chartSecEquiv L V).symm

/-- The section of the glued determinant attached to `x` reads on the chart of `V` as the section
of `x`. -/
theorem chartSec_globalDetSectionsEquiv (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (x : chartDetModule L V) :
    (chartComparison L).chartSec V (V.1 : X.Opens) (globalDetSectionsEquiv L V x) =
      chartSection L V x :=
  (chartSecEquiv L V).apply_symm_apply (chartSectionEquiv L V x)

/-- `localAppFun` of an isomorphism is injective. -/
theorem localAppFun_injective_of_iso {A B : X.Modules} {P : X.Opens}
    (φ : Scheme.Modules.restrict A P.ι ≅ Scheme.Modules.restrict B P.ι) {O : X.Opens}
    (hO : O ≤ P) : Function.Injective (localAppFun φ.hom O hO) := fun s t hst => by
  have hs := localAppFun_comp φ.hom φ.inv O hO s
  have ht := localAppFun_comp φ.hom φ.inv O hO t
  rw [φ.hom_inv_id, localAppFun_id] at hs ht
  rw [hs, ht, hst]

/-- **The identification of sections over affine opens is compatible with restriction**: for
affine opens `V ≤ W`, restricting the section attached to `x ∈ det(M_W)` to `V` gives the section
attached to the comparison `chartRestrictDet L h x ∈ det(M_V)`. -/
theorem globalDetSectionsEquiv_chartRestrictDet (L : PerfectTwoTermAmplitude X)
    {V W : X.affineOpens} (h : V ≤ W) (x : chartDetModule L W) :
    globalDetSectionsEquiv L V (chartRestrictDet L h x) =
      (globalDet L).obj.presheaf.map (homOfLE (AffineOpensGlue.coe_le_coe h)).op
        (globalDetSectionsEquiv L W x) := by
  refine (chartComparison L).chartSec_injective V le_rfl ?_
  rw [chartSec_globalDetSectionsEquiv]
  refine localAppFun_injective_of_iso ((chartComparison L).comp h) le_rfl ?_
  refine (localAppFun_chartDetComp_chartSection L h x).trans ?_
  refine Eq.trans ?_ ((chartComparison L).localAppFun_comp_chartSec h le_rfl _).symm
  refine Eq.trans ?_ ((chartComparison L).chartSec_naturality W
    (AffineOpensGlue.coe_le_coe h) (globalDetSectionsEquiv L W x)).symm
  exact congrArg _ (chartSec_globalDetSectionsEquiv L W x).symm

/-! ### The comparison of determinant modules is the base change of local determinants -/

/-- **The comparison of determinant modules of the glueing datum is the map of local
determinants.** For affine opens `V ≤ W`, `chartRestrictDet L h`, built from the flat base change
`TwoTermDeterminant.detBaseChange` and `sourceComplexRestrictionIso`, is the map
`localDetMap` of the system of local determinants, built from `TwoTermDeterminant.baseChangeMap`
and `transitionIso`. -/
theorem chartRestrictDet_eq_localDetMap (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) (x : chartDetModule L W) :
    chartRestrictDet L h x = localDetMap L (affineRestriction X h) W.2.fromSpec V.2.fromSpec
      (W.2.map_fromSpec V.2 (homOfLE (AffineOpensGlue.coe_le_coe h)).op) x := by
  let : Algebra Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
    (affineRestriction X h).hom.toAlgebra
  have hflat : Module.Flat Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
    V.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe h)
  have he := (congrArg Iso.symm (sourceComplexRestrictionIso_eq_symm_transitionIso L h)).trans
    (Iso.symm_symm_eq _)
  refine Eq.trans ?_ (baseChangeMap_eq_detIsoEquiv_detBaseChange (affineRestriction X h).hom hflat
    (localComplex L W.2.fromSpec) (localComplex L V.2.fromSpec) _ x).symm
  exact congrArg (fun e => detIsoEquiv e (detBaseChange (affineRestriction X h).hom hflat
    (chartComplex L W) (1 ⊗ₜ[Γ(X, (W.1 : X.Opens))] x))) he

/-! ### The isomorphism of the two determinants -/

/-- The glued determinant is quasi-coherent, being invertible. -/
instance isQuasicoherent_globalDet (L : PerfectTwoTermAmplitude X) :
    (globalDet L).obj.IsQuasicoherent :=
  haveI : Stacks.Ample.IsInvertibleModule X (globalDet L).obj := (globalDet L).property
  Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _

/-- The identification of the sections of the glued determinant over affine opens with the
local determinants is compatible with the restriction maps of the system of local determinants. -/
theorem globalDetSectionsEquiv_map (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : (W : X.Opens) ≤ V) (x : (detSystem L).obj V) :
    globalDetSectionsEquiv L W ((detSystem L).map h x) =
      (globalDet L).obj.presheaf.map (homOfLE h).op (globalDetSectionsEquiv L V x) :=
  (congrArg (globalDetSectionsEquiv L W)
      (chartRestrictDet_eq_localDetMap L (show W ≤ V from h) x).symm).trans
    (globalDetSectionsEquiv_chartRestrictDet L (show W ≤ V from h) x)

/-- **The two constructions of the determinant of Stacks 0FJX agree.** The `𝒪_X`-module
`detModule L`, glued from the local determinants `det(M_V)` of More on Algebra, Section 0FJI
along the base change maps of the transition isomorphisms, is isomorphic to the value
`globalDet L` of the determinant functor `determinantFunctor`, glued from the determinants on
the affine charts; on sections over an affine open `V` the isomorphism is the identity of
`det(M_V)`, read through `detSectionsEquiv` and `globalDetSectionsEquiv`. -/
def detModuleIso (L : PerfectTwoTermAmplitude X) : detModule L ≅ (globalDet L).obj :=
  (detSystem L).isoOfSectionsEquiv (globalDet L).obj (fun V => globalDetSectionsEquiv L V)
    (fun h x => globalDetSectionsEquiv_map L h x)

/-- On sections over an affine open, `detModuleIso` is the identity of the local determinant. -/
theorem detModuleIso_hom_app (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (a : Γ(detModule L, V)) :
    (detModuleIso L).hom.val.app (op (V : X.Opens)) a =
      globalDetSectionsEquiv L V (detSectionsEquiv L V a) :=
  (detSystem L).isoOfSectionsEquiv_hom_app _ _ _ V a

/-- The inverse of `detModuleIso` on sections over an affine open. -/
theorem detSectionsEquiv_detModuleIso_inv_app (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (b : Γ((globalDet L).obj, V)) :
    detSectionsEquiv L V ((detModuleIso L).inv.val.app (op (V : X.Opens)) b) =
      (globalDetSectionsEquiv L V).symm b :=
  (detSystem L).isoOfSectionsEquiv_inv_app _ _ _ V b

/-- **The isomorphism of the two determinants carries the canonical global section to the
canonical global section.** For `L` of rank zero, `detModuleIso` carries `deltaSection` to the
canonical global section `determinantSection` of Stacks 0FJX. -/
theorem detModuleIso_hom_deltaSection (L : PerfectTwoTermAmplitude X) (hL : IsRankZero L) :
    (detModuleIso L).hom.val.app (op ⊤) (deltaSection L hL) =
      determinantSection (hL.isRankZeroOn) := by
  refine (chartComparison L).section_ext fun V => ?_
  rw [determinantSection_chartSec]
  have hnat := PresheafOfModules.naturality_apply (detModuleIso L).hom.val
    (homOfLE (le_top : (V.1 : X.Opens) ≤ ⊤)).op (deltaSection L hL)
  refine (congrArg ((chartComparison L).chartSec V (V.1 : X.Opens)) hnat.symm).trans ?_
  refine (congrArg ((chartComparison L).chartSec V (V.1 : X.Opens))
    (detModuleIso_hom_app L V _)).trans ?_
  refine (chartSec_globalDetSectionsEquiv L V _).trans ?_
  refine (congrArg (chartSection L V) (detSectionsEquiv_deltaSection L hL V)).trans ?_
  exact chartSection_delta (hL.isRankZeroOn) V

end AlgebraicGeometry.DeterminantTwoTerm

end
