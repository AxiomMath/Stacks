module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TwistTransport
public import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.Basic
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Psi

/-!
# The twist datum of the projective bundle of an isomorphic module

For an isomorphism `e : E ≅ E'` of finite locally free modules, the twists of `𝐏(E)` restricted
along the isomorphism `𝐏(E') ≅ 𝐏(E)` are twists of `𝐏(E')` in the sense of Tag 01NR. By the
uniqueness of twists they are identified with any given twists of `𝐏(E')` by a unique isomorphism
of graded algebras commuting with the homogeneous-section maps.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.transportTwistData`: the transported
  twist datum.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.bundleTwistIso`: the isomorphism of the
  restricted twists of `𝐏(E)` with the twists of `𝐏(E')`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists Stacks.AlgebraicGeometry.ProjTwistSections

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

/-! ### Restriction maps -/

section Res

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  (M : SheafOfModules.{u} R)

/-- Three restriction maps compose to the composite of two. -/
public theorem val_map₃ {a b c d e : (Opens X)ᵒᵖ} (f₁ : a ⟶ b) (f₂ : b ⟶ c) (f₃ : c ⟶ d)
    (g₁ : a ⟶ e) (g₂ : e ⟶ d) (x : M.val.obj a) :
    M.val.map f₃ (M.val.map f₂ (M.val.map f₁ x)) = M.val.map g₂ (M.val.map g₁ x) := by
  rw [← M.val.map_comp_apply, ← M.val.map_comp_apply, ← M.val.map_comp_apply,
    Subsingleton.elim ((f₁ ≫ f₂) ≫ f₃) (g₁ ≫ g₂)]

end Res

/-! ### Chart identifications in the forward direction -/

section Forward

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- A section whose image under a chart identification is `z` is the chart comparison of `z`. -/
private theorem mapSection_eq_of_hom_app_eq {algebra : SchemeGradedAlgebra (relativeProj A).scheme}
    (C : ChartData A algebra) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (z : (twistingSheaf (A.grading U) n).val.obj (op V))
    (w : (algebra.piece n).val.obj (op ((relativeProj A).chart U hU ''ᵁ V)))
    (h : (C.chartIso U hU n).hom.val.app (op V) w = z) : C.mapSection U hU n V z = w := by
  subst h
  exact TwistRigidity.iso_inv_app_hom_app (C.chartIso U hU n) (op V) w

/-- A chart identification carries the chart comparison of `z` to `z`. -/
private theorem hom_app_eq_of_mapSection_eq {algebra : SchemeGradedAlgebra (relativeProj A).scheme}
    (C : ChartData A algebra) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (z : (twistingSheaf (A.grading U) n).val.obj (op V))
    (w : (algebra.piece n).val.obj (op ((relativeProj A).chart U hU ''ᵁ V)))
    (h : C.mapSection U hU n V z = w) : (C.chartIso U hU n).hom.val.app (op V) w = z := by
  subst h
  exact TwistRigidity.iso_hom_app_inv_app (C.chartIso U hU n) (op V) _

/-- The chart identification of a twist datum is multiplicative in the forward direction. -/
public theorem chartIso_hom_mul (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (i j : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (x : (D.algebra.piece i).val.obj (op ((relativeProj A).chart U hU ''ᵁ V)))
    (y : (D.algebra.piece j).val.obj (op ((relativeProj A).chart U hU ''ᵁ V))) :
    (D.chartData.chartIso U hU (i + j)).hom.val.app (op V) ((D.algebra.mul i j).app _ x y) =
      absoluteTwistProduct (A.grading U) i j V
        ((D.chartData.chartIso U hU i).hom.val.app (op V) x)
        ((D.chartData.chartIso U hU j).hom.val.app (op V) y) := by
  have hx : D.chartData.mapSection U hU i V ((D.chartData.chartIso U hU i).hom.val.app (op V) x) =
      x := TwistRigidity.iso_inv_app_hom_app (D.chartData.chartIso U hU i) (op V) x
  have hy : D.chartData.mapSection U hU j V ((D.chartData.chartIso U hU j).hom.val.app (op V) y) =
      y := TwistRigidity.iso_inv_app_hom_app (D.chartData.chartIso U hU j) (op V) y
  have h := D.chartIso_mul U hU i j V ((D.chartData.chartIso U hU i).hom.val.app (op V) x)
    ((D.chartData.chartIso U hU j).hom.val.app (op V) y)
  rw [hx, hy] at h
  exact hom_app_eq_of_mapSection_eq _ U hU _ V _ _ h

/-- The chart identification of a twist datum carries the unit to the unit. -/
public theorem chartIso_hom_one (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens) :
    (D.chartData.chartIso U hU 0).hom.val.app (op V)
        (D.algebra.one.eval (op ((relativeProj A).chart U hU ''ᵁ V))) =
      absoluteTwistUnit (A.grading U) V := by
  exact hom_app_eq_of_mapSection_eq _ U hU 0 V _ _ (D.chartIso_one U hU V)

/-- A family of chart identifications respecting the products and the unit in the forward
direction respects them in the sense of `IsGradedChartIso`. -/
public theorem isGradedChartIso_of_forward {algebra : SchemeGradedAlgebra (relativeProj A).scheme}
    (C : ChartData A algebra)
    (hmul : ∀ (U : S.Opens) (hU : IsAffineOpen U) (i j : ℤ)
      (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
      (x : (algebra.piece i).val.obj (op ((relativeProj A).chart U hU ''ᵁ V)))
      (y : (algebra.piece j).val.obj (op ((relativeProj A).chart U hU ''ᵁ V))),
      (C.chartIso U hU (i + j)).hom.val.app (op V) ((algebra.mul i j).app _ x y) =
        absoluteTwistProduct (A.grading U) i j V
          ((C.chartIso U hU i).hom.val.app (op V) x) ((C.chartIso U hU j).hom.val.app (op V) y))
    (hone : ∀ (U : S.Opens) (hU : IsAffineOpen U)
      (V : (AlgebraicGeometry.Proj (A.grading U)).Opens),
      (C.chartIso U hU 0).hom.val.app (op V)
          (algebra.one.eval (op ((relativeProj A).chart U hU ''ᵁ V))) =
        absoluteTwistUnit (A.grading U) V) :
    IsGradedChartIso C := by
  refine ⟨fun U hU i j V a b => ?_, fun U hU V => ?_⟩
  · have h := (hmul U hU i j V (C.mapSection U hU i V a) (C.mapSection U hU j V b)).trans
      (congrArg₂ (absoluteTwistProduct (A.grading U) i j V)
        (TwistRigidity.iso_hom_app_inv_app (C.chartIso U hU i) (op V) a)
        (TwistRigidity.iso_hom_app_inv_app (C.chartIso U hU j) (op V) b))
    exact mapSection_eq_of_hom_app_eq C U hU _ V _ _ h
  · exact mapSection_eq_of_hom_app_eq C U hU 0 V _ _ (hone U hU V)

end Forward

/-! ### The twist along a graded ring isomorphism respects products -/

section AbsoluteMul

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- Two sections of a twist agreeing at every point are equal. -/
public theorem twist_ext {n : ℤ} {V : (AlgebraicGeometry.Proj ℬ).Opens}
    {s t : (twistingSheaf ℬ n).val.obj (op V)} (h : ∀ y, s.1 y = t.1 y) : s = t :=
  Subtype.ext (funext h)

variable (φ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜) (hφχ : ∀ b, φ (χ b) = b) (hχφ : ∀ a, χ (φ a) = a)
  [IsOpenImmersion (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))]

/-- The twist along a graded ring isomorphism respects products of twisted sections. -/
public theorem absTwistIso_hom_mul (i j : ℤ) (V : (AlgebraicGeometry.Proj ℬ).Opens)
    (a : (twistingSheaf 𝒜 i).val.obj
      (op (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ) ''ᵁ V)))
    (b : (twistingSheaf 𝒜 j).val.obj
      (op (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ) ''ᵁ V))) :
    (absTwistIso φ χ hφχ hχφ (i + j)).hom.val.app (op V)
        (absoluteTwistProduct 𝒜 i j (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ) ''ᵁ V) a b) =
      absoluteTwistProduct ℬ i j V ((absTwistIso φ χ hφχ hχφ i).hom.val.app (op V) a)
        ((absTwistIso φ χ hφχ hχφ j).hom.val.app (op V) b) := by
  apply Subtype.ext
  funext y
  have h₁ := absTwistIso_hom_val_app_apply φ χ hφχ hχφ (i + j) V
    (absoluteTwistProduct 𝒜 i j (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ) ''ᵁ V) a b) y
  have h₂ := TwistRigidity.absoluteTwistProduct_apply 𝒜 i j
    (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ) ''ᵁ V) a b ⟨_, ⟨y.1, y.2, rfl⟩⟩
  have h₃ := TwistRigidity.absoluteTwistProduct_apply ℬ i j V
    ((absTwistIso φ χ hφχ hχφ i).hom.val.app (op V) a)
    ((absTwistIso φ χ hφχ hχφ j).hom.val.app (op V) b) y
  have h₄ := absTwistIso_hom_val_app_apply φ χ hφχ hχφ i V a y
  have h₅ := absTwistIso_hom_val_app_apply φ χ hφχ hχφ j V b y
  refine h₁.trans (Eq.trans ?_ h₃.symm)
  rw [h₄, h₅]
  refine (congrArg (Stacks.ProjTwistComparison.fibreMap φ _ y.1) h₂).trans ?_
  exact map_mul (Localization.localRingHom _ _ φ.toRingHom rfl) _ _

/-- The twist along a graded ring isomorphism carries the unit to the unit. -/
public theorem absTwistIso_hom_one (V : (AlgebraicGeometry.Proj ℬ).Opens) :
    (absTwistIso φ χ hφχ hχφ 0).hom.val.app (op V)
        (absoluteTwistUnit 𝒜 (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ) ''ᵁ V)) =
      absoluteTwistUnit ℬ V := by
  apply Subtype.ext
  funext y
  have h₁ := absTwistIso_hom_val_app_apply φ χ hφχ hχφ 0 V
    (absoluteTwistUnit 𝒜 (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ) ''ᵁ V)) y
  have h₂ := ThetaMultiplicative.absoluteTwistUnit_apply 𝒜
    (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ) ''ᵁ V) ⟨_, ⟨y.1, y.2, rfl⟩⟩
  have h₃ := ThetaMultiplicative.absoluteTwistUnit_apply ℬ V y
  refine h₁.trans (Eq.trans ?_ h₃.symm)
  refine (congrArg (Stacks.ProjTwistComparison.fibreMap φ _ y.1) h₂).trans ?_
  exact map_one (Localization.localRingHom _ _ φ.toRingHom rfl)

end AbsoluteMul

/-! ### The transported twist datum -/

section Iso

open Stacks.AlgebraicGeometry.RelativeProjTwistGlue Stacks.AlgebraicGeometry.RelativeProjMapDomain

variable {S : Scheme.{u}} {A A' : SheafGradedAlgebra S}
  (f : (relativeProj A').scheme ⟶ (relativeProj A).scheme) [IsOpenImmersion f]
  (σ : ∀ U : S.Opens, A.grading U →+*ᵍ A'.grading U) (τ : SheafGradedAlgebraHom A' A)
  (hσχ : ∀ U b, σ U (τ.sectionHom U b) = b) (hχσ : ∀ U a, τ.sectionHom U (σ U a) = a)
  [∀ U, IsOpenImmersion (isoChartMap σ (fun U => τ.sectionHom U) hσχ U)]
  (hchart : ∀ (U : S.Opens) (hU : IsAffineOpen U),
    (relativeProj A').chart U hU ≫ f =
      isoChartMap σ (fun U => τ.sectionHom U) hσχ U ≫ (relativeProj A).chart U hU)
  (D : TwistData A)

/-- **The chart data of the transported twists.** -/
public def transportChartData : ChartData A' (restrictAlgebra f D.algebra) where
  chart_isOpenImmersion U hU := inferInstance
  chart_range U hU := chart_image_top _ U hU
  chartIso U hU n := transportChartIso f σ (fun U => τ.sectionHom U) hσχ hχσ hchart D U hU n

/-- **The transported chart identifications respect products and the unit.** -/
public theorem isGradedChartIso_transportChartData :
    IsGradedChartIso (transportChartData f σ τ hσχ hχσ hchart D) := by
  refine isGradedChartIso_of_forward _ (fun U hU i j V x y => ?_) (fun U hU V => ?_)
  · have h₁ := transportChartIso_hom_app f σ (fun U => τ.sectionHom U) hσχ hχσ hchart D U hU
      (i + j) V ((D.algebra.mul i j).app _ x y)
    have h₂ := (D.algebra.mul i j).naturality
      (eqToHom (image_chart_iso f σ (fun U => τ.sectionHom U) hσχ hchart U hU V)).op x y
    have h₃ := chartIso_hom_mul D U hU i j (isoChartMap σ (fun U => τ.sectionHom U) hσχ U ''ᵁ V)
      ((D.algebra.piece i).val.map
        (eqToHom (image_chart_iso f σ (fun U => τ.sectionHom U) hσχ hchart U hU V)).op x)
      ((D.algebra.piece j).val.map
        (eqToHom (image_chart_iso f σ (fun U => τ.sectionHom U) hσχ hchart U hU V)).op y)
    have h₄ := absTwistIso_hom_mul (σ U) (τ.sectionHom U) (hσχ U) (hχσ U) i j V
      ((D.chartData.chartIso U hU i).hom.val.app
        (op (isoChartMap σ (fun U => τ.sectionHom U) hσχ U ''ᵁ V))
        ((D.algebra.piece i).val.map
          (eqToHom (image_chart_iso f σ (fun U => τ.sectionHom U) hσχ hchart U hU V)).op x))
      ((D.chartData.chartIso U hU j).hom.val.app
        (op (isoChartMap σ (fun U => τ.sectionHom U) hσχ U ''ᵁ V))
        ((D.algebra.piece j).val.map
          (eqToHom (image_chart_iso f σ (fun U => τ.sectionHom U) hσχ hchart U hU V)).op y))
    have h₅ := transportChartIso_hom_app f σ (fun U => τ.sectionHom U) hσχ hχσ hchart D U hU i V x
    have h₆ := transportChartIso_hom_app f σ (fun U => τ.sectionHom U) hσχ hχσ hchart D U hU j V y
    refine h₁.trans ((congrArg (fun z => (absTwistIso (σ U) (τ.sectionHom U) (hσχ U) (hχσ U)
      (i + j)).hom.val.app (op V) ((D.chartData.chartIso U hU (i + j)).hom.val.app
        (op (isoChartMap σ (fun U => τ.sectionHom U) hσχ U ''ᵁ V)) z)) h₂).trans
      ((congrArg (fun z => (absTwistIso (σ U) (τ.sectionHom U) (hσχ U) (hχσ U)
        (i + j)).hom.val.app (op V) z) h₃).trans (h₄.trans ?_)))
    exact congrArg₂ _ h₅.symm h₆.symm
  · have h₁ := transportChartIso_hom_app f σ (fun U => τ.sectionHom U) hσχ hχσ hchart D U hU
      0 V (D.algebra.one.eval _)
    have h₂ : (D.algebra.piece 0).val.map
        (eqToHom (image_chart_iso f σ (fun U => τ.sectionHom U) hσχ hchart U hU V)).op
          (D.algebra.one.eval (op (f ''ᵁ ((relativeProj A').chart U hU ''ᵁ V)))) =
        D.algebra.one.eval (op ((relativeProj A).chart U hU ''ᵁ
          (isoChartMap σ (fun U => τ.sectionHom U) hσχ U ''ᵁ V))) :=
      D.algebra.one.property _
    have h₃ := chartIso_hom_one D U hU (isoChartMap σ (fun U => τ.sectionHom U) hσχ U ''ᵁ V)
    have h₄ := absTwistIso_hom_one (σ U) (τ.sectionHom U) (hσχ U) (hχσ U) V
    refine h₁.trans ((congrArg (fun z => (absTwistIso (σ U) (τ.sectionHom U) (hσχ U) (hχσ U)
      0).hom.val.app (op V) ((D.chartData.chartIso U hU 0).hom.val.app
        (op (isoChartMap σ (fun U => τ.sectionHom U) hσχ U ''ᵁ V)) z)) h₂).trans
      ((congrArg (fun z => (absTwistIso (σ U) (τ.sectionHom U) (hσχ U) (hχσ U)
        0).hom.val.app (op V) z) h₃).trans h₄))

variable (hbase : f ≫ (relativeProj A).toBase = (relativeProj A').toBase)

/-- The direct image of a module on `Proj_S(A)` maps to the direct image of its restriction to
`Proj_S(A')`: restriction of sections along the image of the inverse image. -/
public def restrictPushforwardMap (M : (relativeProj A).scheme.Modules) :
    (Scheme.Modules.pushforward (relativeProj A).toBase).obj M ⟶
      (Scheme.Modules.pushforward (relativeProj A').toBase).obj (Scheme.Modules.restrict M f) :=
  (Scheme.Modules.pushforward (relativeProj A).toBase).map
      ((Scheme.Modules.restrictAdjunction f).unit.app M) ≫
    (Scheme.Modules.pushforwardComp f (relativeProj A).toBase).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr hbase).hom.app _

/-- Two restriction maps of a presheaf on the opens of a space, with an identity between them,
compose to one. -/
public theorem presheaf_map_comp₂ {X : TopCat.{u}} {C : Type*} [Category C]
    (P : (Opens X)ᵒᵖ ⥤ C) {a b c : (Opens X)ᵒᵖ} (f₁ : a ⟶ b) (f₂ : b ⟶ c)
    (g : a ⟶ c) : P.map f₁ ≫ 𝟙 _ ≫ P.map f₂ = P.map g := by
  rw [Category.id_comp, ← P.map_comp]
  exact congrArg P.map (Subsingleton.elim _ _)

include hbase in
/-- The image of an inverse image under `f`. -/
public theorem image_preimage_le_preimage (W : S.Opens) :
    f ''ᵁ ((relativeProj A').toBase ⁻¹ᵁ W) ≤ (relativeProj A).toBase ⁻¹ᵁ W := by
  rw [← hbase, Scheme.Hom.comp_preimage]
  exact f.image_preimage_le _

/-- `restrictPushforwardMap` on sections is a restriction map. -/
public theorem restrictPushforwardMap_app (M : (relativeProj A).scheme.Modules) (W : S.Opens)
    (x : Γ(M, (relativeProj A).toBase ⁻¹ᵁ W)) :
    (restrictPushforwardMap f hbase M).app W x =
      M.presheaf.map (homOfLE (image_preimage_le_preimage f hbase W)).op x := by
  simp only [restrictPushforwardMap, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    ConcreteCategory.id_apply]
  exact ConcreteCategory.congr_hom (presheaf_map_comp₂ M.presheaf _ _ _) x

/-- `restrictPushforwardMap_app` on the underlying presheaves. -/
public theorem restrictPushforwardMap_val_app (M : (relativeProj A).scheme.Modules) (W : S.Opens)
    (x : M.val.obj (op ((relativeProj A).toBase ⁻¹ᵁ W))) :
    (restrictPushforwardMap f hbase M).val.app (op W) x =
      M.val.map (homOfLE (image_preimage_le_preimage f hbase W)).op x :=
  restrictPushforwardMap_app f hbase M W x

/-- **The homogeneous-section map of the transported twists**: undo the isomorphism of graded
algebras, apply the homogeneous-section map of `Proj_S(A)`, and restrict. -/
public def transportPsi (n : ℕ) :
    A'.piece (n : ℤ) ⟶ (Scheme.Modules.pushforward (relativeProj A').toBase).obj
      ((restrictAlgebra f D.algebra).piece (n : ℤ)) :=
  τ.app (n : ℤ) ≫ D.ψ n ≫ restrictPushforwardMap f hbase (D.algebra.piece (n : ℤ))

/-- The chart comparison of a chart datum is compatible with restriction to a smaller open. -/
public theorem mapSection_res {algebra : SchemeGradedAlgebra (relativeProj A).scheme}
    (C : ChartData A algebra) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    {V W : (AlgebraicGeometry.Proj (A.grading U)).Opens} (h : W ≤ V)
    (z : (twistingSheaf (A.grading U) n).val.obj (op V)) :
    letI := C.chart_isOpenImmersion U hU
    (algebra.piece n).val.map
        (homOfLE (((relativeProj A).chart U hU).image_mono h)).op (C.mapSection U hU n V z) =
      C.mapSection U hU n W ((twistingSheaf (A.grading U) n).val.map (homOfLE h).op z) :=
  (PresheafOfModules.naturality_apply (C.chartIso U hU n).inv.val (homOfLE h).op z).symm

/-- The homogeneous section of a homogeneous element, localized along a graded ring isomorphism,
restricted to an open, is the homogeneous section of the image. -/
public theorem absTwistIso_degreeSection {A₀ B₀ : Type u} {σ₀ τ₀ : Type u}
    [CommRing A₀] [CommRing B₀] [SetLike σ₀ A₀] [AddSubgroupClass σ₀ A₀]
    [SetLike τ₀ B₀] [AddSubgroupClass τ₀ B₀]
    {𝒜 : ℕ → σ₀} {ℬ : ℕ → τ₀} [GradedRing 𝒜] [GradedRing ℬ]
    (φ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜) (hφχ : ∀ b, φ (χ b) = b) (hχφ : ∀ a, χ (φ a) = a)
    [IsOpenImmersion (Proj.map φ (irrelevant_le_map_of_inverse φ χ hφχ))] (k : ℕ) (a : 𝒜 k)
    (b : ℬ k) (hab : φ a = b) :
    (absTwistIso φ χ hφχ hχφ k).hom.val.app (op ⊤)
        ((twistingSheaf 𝒜 k).val.map (homOfLE le_top).op
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒜 k a)) =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection ℬ k b := by
  apply Subtype.ext
  funext y
  refine (absTwistIso_hom_val_app_apply φ χ hφχ hχφ k ⊤ _ y).trans ?_
  have h₁ := ProjTwistSections.degreeSection_apply 𝒜 k a
    ⟨ProjectiveSpectrum.comapFun φ (irrelevant_le_map_of_inverse φ χ hφχ) y.1, trivial⟩
  have h₂ := ProjTwistSections.degreeSection_apply ℬ k b ⟨y.1, trivial⟩
  refine Eq.trans ?_ h₂.symm
  refine (congrArg (Stacks.ProjTwistComparison.fibreMap φ _ y.1) h₁).trans ?_
  refine (Stacks.ProjTwistComparison.fibreMap_mk φ _ y.1 _ _).trans ?_
  congr 1
  exact Subtype.ext (map_one φ)

/-- A section whose image under a chart identification is `z` is the chart comparison of `z`. -/
public theorem mapSection_eq_of_chartIso_hom {algebra : SchemeGradedAlgebra (relativeProj A).scheme}
    (C : ChartData A algebra) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (z : (twistingSheaf (A.grading U) n).val.obj (op V))
    (w : letI := C.chart_isOpenImmersion U hU
      (Scheme.Modules.restrict (algebra.piece n) ((relativeProj A).chart U hU)).val.obj (op V))
    (h : (C.chartIso U hU n).hom.val.app (op V) w = z) : C.mapSection U hU n V z = w :=
  mapSection_eq_of_hom_app_eq C U hU n V z w h

/-- The chart identification of a twist datum carries the image of its homogeneous-section map
to the homogeneous section, in the forward direction. -/
public theorem chartIso_hom_psi (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (b : A.sectionPieces U n) :
    (D.chartData.chartIso U hU (n : ℤ)).hom.val.app (op ⊤)
        ((D.algebra.piece (n : ℤ)).val.map (eqToHom (D.chartData.chart_range U hU)).op
          ((D.ψ n).val.app (op U) b)) =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading U) n
        ⟨DirectSum.of (A.sectionPieces U) n b, A.of_mem_grading U b⟩ := by
  have h₁ := D.ψ_chart U hU n b
  have h₂ := PresheafOfModules.rec_eq_map (D.algebra.piece (n : ℤ)).val
    (D.chartData.chart_range U hU).symm ((D.ψ n).val.app (op U) b)
  rw [← h₂]
  exact hom_app_eq_of_mapSection_eq _ U hU _ ⊤ _ _ h₁

/-- **The homogeneous-section map of the transported twists has the chart description.** -/
public theorem psiChart_transport :
    Tag01NRPsiCompat.PsiChart (transportChartData f σ τ hσχ hχσ hchart D)
      (transportPsi f τ D hbase) := by
  intro U hU n a'
  have h₀ := PresheafOfModules.rec_eq_map ((restrictAlgebra f D.algebra).piece (n : ℤ)).val
    ((transportChartData f σ τ hσχ hχσ hchart D).chart_range U hU).symm
    ((transportPsi f τ D hbase n).val.app (op U) a')
  rw [h₀]
  refine mapSection_eq_of_chartIso_hom _ U hU (n : ℤ) ⊤ _ _ ?_
  refine (transportChartIso_hom_app f σ (fun U => τ.sectionHom U) hσχ hχσ hchart D U hU
    (n : ℤ) ⊤ _).trans ?_
  have hψ := restrictPushforwardMap_val_app f hbase (D.algebra.piece (n : ℤ)) U
    ((D.ψ n).val.app (op U) (τ.sectionPieceHom U n a'))
  have hR : (D.algebra.piece (n : ℤ)).val.map
      (eqToHom (image_chart_iso f σ (fun U => τ.sectionHom U) hσχ hchart U hU ⊤)).op
      ((D.algebra.piece (n : ℤ)).val.map
        (f.opensFunctor.map (eqToHom ((transportChartData f σ τ hσχ hχσ hchart D).chart_range
          U hU))).op
        ((restrictPushforwardMap f hbase (D.algebra.piece (n : ℤ))).val.app (op U)
          ((D.ψ n).val.app (op U) (τ.sectionPieceHom U n a')))) =
      (D.algebra.piece (n : ℤ)).val.map
        (homOfLE (((relativeProj A).chart U hU).image_mono
          (le_top : isoChartMap σ (fun U => τ.sectionHom U) hσχ U ''ᵁ ⊤ ≤ ⊤))).op
        ((D.algebra.piece (n : ℤ)).val.map (eqToHom (D.chartData.chart_range U hU)).op
          ((D.ψ n).val.app (op U) (τ.sectionPieceHom U n a'))) := by
    rw [hψ]
    exact val_map₃ (D.algebra.piece (n : ℤ)) _ _ _ _ _ _
  have hnat := PresheafOfModules.naturality_apply (D.chartData.chartIso U hU (n : ℤ)).hom.val
    (homOfLE (le_top : isoChartMap σ (fun U => τ.sectionHom U) hσχ U ''ᵁ ⊤ ≤ ⊤)).op
    ((D.algebra.piece (n : ℤ)).val.map (eqToHom (D.chartData.chart_range U hU)).op
      ((D.ψ n).val.app (op U) (τ.sectionPieceHom U n a')))
  refine (congrArg (fun z => (absTwistIso (σ U) (τ.sectionHom U) (hσχ U) (hχσ U)
    (n : ℤ)).hom.val.app (op ⊤) ((D.chartData.chartIso U hU (n : ℤ)).hom.val.app
      (op (isoChartMap σ (fun U => τ.sectionHom U) hσχ U ''ᵁ ⊤)) z)) hR).trans ?_
  refine (congrArg (fun z => (absTwistIso (σ U) (τ.sectionHom U) (hσχ U) (hχσ U)
    (n : ℤ)).hom.val.app (op ⊤) z) hnat).trans ?_
  refine (congrArg (fun z => (absTwistIso (σ U) (τ.sectionHom U) (hσχ U) (hχσ U)
    (n : ℤ)).hom.val.app (op ⊤) ((twistingSheaf (A.grading U) (n : ℤ)).val.map
      (homOfLE (le_top : isoChartMap σ (fun U => τ.sectionHom U) hσχ U ''ᵁ ⊤ ≤ ⊤)).op z))
    (chartIso_hom_psi D U hU n (τ.sectionPieceHom U n a'))).trans ?_
  refine absTwistIso_degreeSection (σ U) (τ.sectionHom U) (hσχ U) (hχσ U) n _ _ ?_
  exact (congrArg (σ U) (SheafGradedAlgebraHom.sectionHom_of τ U a').symm).trans (hσχ U _)

/-- **The transported twist datum** on `Proj_S(A')`: the twists of `Proj_S(A)` restricted along
`f`, with their chart identifications and homogeneous-section map. -/
public def transportTwistData : TwistData A' :=
  Tag01NRPsiCompat.mk (restrictAlgebra f D.algebra) (transportChartData f σ τ hσχ hχσ hchart D)
    (isGradedChartIso_transportChartData f σ τ hσχ hχσ hchart D) (transportPsi f τ D hbase)
    (psiChart_transport f σ τ hσχ hχσ hchart D hbase)

/-- **The twists of `Proj_S(A)` restricted along `f` are the twists of `Proj_S(A')`**: the unique
isomorphism of graded algebras carrying the transported homogeneous-section map to that of `D'`. -/
public def transportTwistIso (D' : TwistData A') : restrictAlgebra f D.algebra ≅ D'.algebra :=
  (TwistExistence.isUniqueTwistData A'
    (transportTwistData f σ τ hσχ hχσ hchart D hbase) D').exists.choose

/-- **Compatibility with the homogeneous-section maps.** -/
public theorem transportTwistIso_psi (D' : TwistData A') (k : ℕ) :
    τ.app (k : ℤ) ≫ D.ψ k ≫ restrictPushforwardMap f hbase (D.algebra.piece (k : ℤ)) ≫
        (Scheme.Modules.pushforward (relativeProj A').toBase).map
          ((transportTwistIso f σ τ hσχ hχσ hchart D hbase D').hom.app (k : ℤ)) = D'.ψ k := by
  have h := (TwistExistence.isUniqueTwistData A' (transportTwistData f σ τ hσχ hχσ hchart D hbase)
    D').exists.choose_spec k
  refine Eq.trans ?_ h
  rw [← Category.assoc, ← Category.assoc]
  rfl

end Iso

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
