module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeTarget

/-!
# The transported target of Tag 02NC's `θ` as twist data over the trivializing basis

Let `P' = Proj_S(ℬ)`, `ℬ = ⨁_d 𝒜_d ⊗ ℒ^{⊗ d}`, and let `E` be the target algebra
`⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` of Tag 02NC's `θ`, transported to `P'` along the canonical isomorphism
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.transportedTarget`). This file shows that `E`,
with the *multiply* map of clause (2) as homogeneous-section map, is twist data over the basis of
affine opens trivializing `ℒ`
(`Stacks.AlgebraicGeometry.TwistExistenceBasis.BasisTwistData`), given, over each member `V` of
the basis, the absolute comparison of the twists along `Proj ℬ(V) ≅ Proj 𝒜(V)`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.AbsTwistCompare`: the absolute comparison of
  the twists over a member of the basis: multiplicative, and carrying the homogeneous section of
  `a` to that of `ψ a`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.targetTwistData`: **`E` as twist data over the
  trivializing basis.**

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.AffineOpenTensorSections
open Stacks.AlgebraicGeometry.ProjTwistSections AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-- The compatibility of an absolute comparison with the homogeneous sections: the homogeneous
section of `a` goes to that of its image under the comparison `ψ : 𝒜(V) ⟶ ℬ(V)`. -/
def IsDegCompat (V : trivializingOpens L)
    (iso : ∀ n : ℤ, (Scheme.Modules.restrictFunctor (basisComparison L 𝒜 V)).obj
      (twistingSheaf (𝒜.grading (V : S.Opens)) n) ≅
    twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) n) : Prop :=
  ∀ (k : ℕ) (a : 𝒜.grading (V : S.Opens) k),
    (iso k).hom.val.app (op ⊤)
        ((Scheme.Modules.restrictAppIso (basisComparison L 𝒜 V)
          (twistingSheaf (𝒜.grading (V : S.Opens)) (k : ℤ)) ⊤).inv
          ((twistingSheaf (𝒜.grading (V : S.Opens)) (k : ℤ)).val.map
            (homOfLE (le_top : basisComparison L 𝒜 V ''ᵁ ⊤ ≤ ⊤)).op
            (degreeSection (𝒜.grading (V : S.Opens)) k a))) =
      ((degreeSection ((twist 𝒜 L).grading (V : S.Opens)) k
        ⟨psiSectionAt L 𝒜 V (basisSection L V) a,
          (psiSectionAt L 𝒜 V (basisSection L V)).map_mem a.2⟩ : twistGlobalSections _ k) :
          (twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) k).val.obj (op ⊤))

/-- **The absolute comparison of the twists over a member `V` of the trivializing basis**: an
identification of the restriction of `𝒪_{Proj 𝒜(V)}(n)` along `Proj ℬ(V) ≅ Proj 𝒜(V)` with
`𝒪_{Proj ℬ(V)}(n)`, multiplicative, and carrying the homogeneous section of `a` to that of its
image under the comparison `ψ : 𝒜(V) ⟶ ℬ(V)`. -/
structure AbsTwistCompare (V : trivializingOpens L) where
  /-- The identification in each degree. -/
  iso (n : ℤ) : (Scheme.Modules.restrictFunctor (basisComparison L 𝒜 V)).obj
      (twistingSheaf (𝒜.grading (V : S.Opens)) n) ≅
    twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) n

  /-- It is multiplicative. -/
  mul (i j : ℤ) (W : (AlgebraicGeometry.Proj ((twist 𝒜 L).grading (V : S.Opens))).Opens)
    (a : ((Scheme.Modules.restrictFunctor (basisComparison L 𝒜 V)).obj
      (twistingSheaf (𝒜.grading (V : S.Opens)) i)).val.obj (op W))
    (b : ((Scheme.Modules.restrictFunctor (basisComparison L 𝒜 V)).obj
      (twistingSheaf (𝒜.grading (V : S.Opens)) j)).val.obj (op W)) :
    (iso (i + j)).hom.val.app (op W)
        (absoluteTwistProduct (𝒜.grading (V : S.Opens)) i j (basisComparison L 𝒜 V ''ᵁ W) a b) =
      absoluteTwistProduct ((twist 𝒜 L).grading (V : S.Opens)) i j W
        ((iso i).hom.val.app (op W) a) ((iso j).hom.val.app (op W) b)
  /-- It carries the homogeneous section of `a` to that of `ψ a`. -/
  deg : IsDegCompat L 𝒜 V iso

/-! ### The homogeneous-section map on a chart -/

/-- The chart of `Proj_S(𝒜)` over an affine open has all of its source over that open. -/
theorem chart_preimage_toBase_preimage_eq_top {V : S.Opens} (hV : IsAffineOpen V) :
    (relativeProj 𝒜).chart V hV ⁻¹ᵁ ((relativeProj 𝒜).toBase ⁻¹ᵁ V) = ⊤ := by
  rw [← RelativeProjTwistGlue.chart_image_top (relativeProj 𝒜) V hV]
  exact Scheme.Hom.preimage_image_eq _ _

/-- A morphism out of a restriction commutes with restricting a section of the module along a
smaller open, given its value on the larger open. -/
private theorem restrict_hom_app_map_eq {X Z : Scheme.{u}} (f : X ⟶ Z) [IsOpenImmersion f]
    (F : Z.Modules) {N : X.Modules} (φ : F.restrict f ⟶ N) {Y Y' : X.Opens} (hY : Y ≤ Y')
    {A : Z.Opens} (h : f ''ᵁ Y ≤ A) (h' : f ''ᵁ Y' ≤ A) (x : F.val.obj (op A))
    {y : N.val.obj (op Y')} (hy : φ.val.app (op Y') (F.val.map (homOfLE h').op x) = y) :
    φ.val.app (op Y) (F.val.map (homOfLE h).op x) = N.val.map (homOfLE hY).op y := by
  subst hy
  exact (congrArg _ (PresheafOfModules.map_map_eq_map F.val (homOfLE h').op
    (homOfLE (f.image_mono hY)).op (homOfLE h).op x).symm).trans
    (PresheafOfModules.naturality_apply φ.val (homOfLE hY).op _)

/-- **The chart identification of Tag 01NR carries the homogeneous-section map to the homogeneous
sections**, on the sections over an arbitrary open of the chart. -/
theorem chartIso_hom_psi {U : S.Opens} (hU : IsAffineOpen U) (k : ℕ) (a : 𝒜.sectionPieces U k)
    (Y : (AlgebraicGeometry.Proj (𝒜.grading U)).Opens)
    (h : (relativeProj 𝒜).chart U hU ''ᵁ Y ≤ (relativeProj 𝒜).toBase ⁻¹ᵁ U) :
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).chartData.chartIso U hU k).hom.val.app (op Y)
        ((Tag07ZGTwist.relativeTwist 𝒜 k).val.map (homOfLE h).op
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k).val.app (op U) a)) =
      (twistingSheaf (𝒜.grading U) (k : ℤ)).val.map (homOfLE (le_top : Y ≤ ⊤)).op
        (degreeSection (𝒜.grading U) k
          ⟨DirectSum.of (𝒜.sectionPieces U) k a, 𝒜.of_mem_grading U a⟩) := by
  have hY : Y ≤ (relativeProj 𝒜).chart U hU ⁻¹ᵁ ((relativeProj 𝒜).toBase ⁻¹ᵁ U) := by
    rw [chart_preimage_toBase_preimage_eq_top 𝒜 hU]
    exact le_top
  have h1 := TwistExistenceBasis.chartLoc_psi
    (TwistExistenceBasis.BasisTwistData.ofTwistData (𝔅 := Set.univ)
      (GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜)) U hU (Set.mem_univ _) k a
  have h1' := (TwistExistenceBasis.chartLoc_app_eq
    (TwistExistenceBasis.BasisTwistData.ofTwistData (𝔅 := Set.univ)
      (GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜)) U hU (Set.mem_univ _) (k : ℤ)
      ((relativeProj 𝒜).toBase ⁻¹ᵁ U) le_rfl
      (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k).val.app (op U) a)).symm.trans h1
  refine (restrict_hom_app_map_eq _ _ _ hY h (((relativeProj 𝒜).chart U hU).image_preimage_le _)
    _ h1').trans ?_
  exact PresheafOfModules.map_map_eq_map _ _ _ _ _

/-- **The chart identification of the transported target carries the *multiply* map to the
homogeneous sections**, before the absolute comparison: the image of `a ⊗ x^k` goes to the
homogeneous section of `a`. -/
theorem chartPre_psi (V : trivializingOpens L) (k : ℕ) (a : 𝒜.sectionPieces V k) :
    (chartPre L 𝒜 V k).hom.val.app
        (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
          ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens))))
        (((transportedTarget L 𝒜).piece (k : ℤ)).val.map
          (homOfLE (((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1).image_preimage_le
            ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))).op
          ((transportedPsi L 𝒜 k).val.app (op (V : S.Opens))
            (psiPieceAt L 𝒜 V (basisSection L V) k a))) =
      (twistingSheaf (𝒜.grading (V : S.Opens)) (k : ℤ)).val.map
        (homOfLE (le_top : basisComparison L 𝒜 V ''ᵁ
          ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
            ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens))) ≤ ⊤)).op
        (degreeSection (𝒜.grading (V : S.Opens)) k
          ⟨DirectSum.of (𝒜.sectionPieces V) k a, 𝒜.of_mem_grading V a⟩) := by
  have hx := basisSection_trivializesPower L V 1 Nat.one_pos
  have h0 : (relativeTwistIso L 𝒜).hom ''ᵁ ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)) ≤
      (relativeProj 𝒜).toBase ⁻¹ᵁ (V : S.Opens) := by
    rintro _ ⟨y, hy, rfl⟩
    change ((relativeTwistIso L 𝒜).hom ≫ (relativeProj 𝒜).toBase) y ∈ (V : S.Opens)
    rw [relativeTwistIso_hom_comp_toBase]
    exact hy
  refine (chartPre_hom_app L 𝒜 V k _ _).trans ?_
  have hmul : (transportedPsi L 𝒜 k).val.app (op (V : S.Opens))
      (psiPieceAt L 𝒜 V (basisSection L V) k a) =
      ((targetAlgebra L 𝒜).piece (k : ℤ)).val.map (homOfLE h0).op
        (gammaTmul (Tag07ZGTwist.relativeTwist 𝒜 (k : ℤ))
          ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L (k : ℤ)))
          ((relativeProj 𝒜).toBase ⁻¹ᵁ (V : S.Opens))
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k).val.app (op (V : S.Opens)) a)
          (pullbackPow L 𝒜 V (k : ℤ))) := by
    refine (transportedPsi_app L 𝒜 k (V : S.Opens) h0 _).trans ?_
    refine congrArg (((targetAlgebra L 𝒜).piece (k : ℤ)).val.map (homOfLE h0).op) ?_
    refine (congrArg _ (psiPieceAt_eq_gammaTmul L 𝒜 (V : S.Opens) (basisSection L V) k a)).trans ?_
    refine (RelativeTwistSections.multiplyHom_app_gammaTmul (relativeProj 𝒜).toBase _
      (V : S.Opens) a _).trans ?_
    refine congrArg (gammaTmul _ _ _ _) ?_
    exact congrArg (Stacks.RingedSpace.pullbackUnit (relativeProj 𝒜).toBase.toLRSHom.toShHom
      (tpMod L (k : ℤ)) (op (V : S.Opens))) (intPow_natCast L hx k).symm
  have hR : (relativeProj 𝒜).chart (V : S.Opens) V.2.1 ''ᵁ (basisComparison L 𝒜 V ''ᵁ
      ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
        ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))) ≤
      (relativeProj 𝒜).toBase ⁻¹ᵁ (V : S.Opens) :=
    PullbackTrivialization.image_le_preimage (relativeProj 𝒜).toBase
      ((relativeProj 𝒜).chart (V : S.Opens) V.2.1) (chart_comp_toBase_preimage 𝒜 V.2.1) _
  have hC : ((targetAlgebra L 𝒜).piece (k : ℤ)).val.map
      (homOfLE (image_chart_relativeTwistIso L 𝒜 V
        ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
          ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))).ge).op
      (((transportedTarget L 𝒜).piece (k : ℤ)).val.map
        (homOfLE (((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1).image_preimage_le
          ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))).op
        ((transportedPsi L 𝒜 k).val.app (op (V : S.Opens))
          (psiPieceAt L 𝒜 V (basisSection L V) k a))) =
      (chartTau L 𝒜 V k).inv.val.app (op (basisComparison L 𝒜 V ''ᵁ
        ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
          ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))))
        ((Tag07ZGTwist.relativeTwist 𝒜 k).val.map (homOfLE hR).op
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k).val.app (op (V : S.Opens)) a)) := by
    refine Eq.trans ?_ (chartTau_inv_app L 𝒜 V k _ _).symm
    refine (congrArg (fun z => ((targetAlgebra L 𝒜).piece (k : ℤ)).val.map _
      (((transportedTarget L 𝒜).piece (k : ℤ)).val.map _ z)) hmul).trans ?_
    have hO3 : (relativeTwistIso L 𝒜).hom ''ᵁ ((relativeProj (twist 𝒜 L)).chart (V : S.Opens)
        V.2.1 ''ᵁ ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
          ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))) ≤
        (relativeProj 𝒜).toBase ⁻¹ᵁ (V : S.Opens) :=
      ((relativeTwistIso L 𝒜).hom.image_mono
        (((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1).image_preimage_le _)).trans h0
    refine (congrArg (((targetAlgebra L 𝒜).piece (k : ℤ)).val.map _)
      (PresheafOfModules.map_map_eq_map ((targetAlgebra L 𝒜).piece (k : ℤ)).val
        (homOfLE h0).op _ (homOfLE hO3).op _)).trans ?_
    refine (PresheafOfModules.map_map_eq_map ((targetAlgebra L 𝒜).piece (k : ℤ)).val
      (homOfLE hO3).op _ (homOfLE hR).op _).trans ?_
    exact Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_naturality
      (relativeProj 𝒜).scheme.sheaf.obj (relativeProj 𝒜).scheme.ringCatSheaf.property
      (Tag07ZGTwist.relativeTwist 𝒜 k)
      ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L (k : ℤ))) _ _ _
  have hY := TwistRigidity.iso_hom_app_inv_app (chartTau L 𝒜 V k)
    (op (basisComparison L 𝒜 V ''ᵁ ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
      ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))))
    ((Tag07ZGTwist.relativeTwist 𝒜 k).val.map (homOfLE hR).op
      (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k).val.app (op (V : S.Opens)) a))
  have hZ := congrArg ((chartTau L 𝒜 V k).hom.val.app
    (op (basisComparison L 𝒜 V ''ᵁ ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
      ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))))) hC
  exact (congrArg (((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).chartData.chartIso
      (V : S.Opens) V.2.1 k).hom.val.app
      (op (basisComparison L 𝒜 V ''ᵁ ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
        ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))))) (hZ.trans hY)).trans
    (chartIso_hom_psi 𝒜 V.2.1 k a _ hR)

/-! ### The transported target as twist data over the trivializing basis -/

section TwistData

variable (abs : ∀ V : trivializingOpens L, AbsTwistCompare L 𝒜 V)

/-- **The chart identification of the transported target** over a member of the basis. -/
def targetChartIso (V : trivializingOpens L) (n : ℤ) :
    Scheme.Modules.restrict ((transportedTarget L 𝒜).piece n)
        ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1) ≅
      twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) n :=
  chartPre L 𝒜 V n ≪≫ (abs V).iso n

/-- The chart identification of the transported target is the composite of `chartPre` with the
absolute comparison, on sections over every open. -/
theorem targetChartIso_hom_app (V : trivializingOpens L) (n : ℤ)
    (W : (AlgebraicGeometry.Proj ((twist 𝒜 L).grading (V : S.Opens))).Opens)
    (x : (Scheme.Modules.restrict ((transportedTarget L 𝒜).piece n)
        ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1)).val.obj (op W)) :
    (targetChartIso L 𝒜 abs V n).hom.val.app (op W) x =
      ((abs V).iso n).hom.val.app (op W) ((chartPre L 𝒜 V n).hom.val.app (op W) x) :=
  Tag07ZGTwist.comp_val_app_apply _ _ W x

/-- The chart identification of the transported target is multiplicative: it carries the product
of the transported target to the product of the twists of `Proj ℬ(V)`. -/
theorem targetChartIso_hom_mul (V : trivializingOpens L) (i j : ℤ)
    (W : (AlgebraicGeometry.Proj ((twist 𝒜 L).grading (V : S.Opens))).Opens)
    (x : ((transportedTarget L 𝒜).piece i).val.obj
      (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ''ᵁ W)))
    (y : ((transportedTarget L 𝒜).piece j).val.obj
      (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ''ᵁ W))) :
    (targetChartIso L 𝒜 abs V (i + j)).hom.val.app (op W)
        (((transportedTarget L 𝒜).mul i j).app
          (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ''ᵁ W)) x y) =
      absoluteTwistProduct ((twist 𝒜 L).grading (V : S.Opens)) i j W
        ((targetChartIso L 𝒜 abs V i).hom.val.app (op W) x)
        ((targetChartIso L 𝒜 abs V j).hom.val.app (op W) y) := by
  refine (targetChartIso_hom_app L 𝒜 abs V (i + j) W _).trans ?_
  refine (congrArg (((abs V).iso (i + j)).hom.val.app (op W))
    (chartPre_hom_mul L 𝒜 V i j W x y)).trans ?_
  exact (abs V).mul i j W _ _

/-- The absolute comparison carries the restriction of the homogeneous section of `a` to the
restriction of the homogeneous section of `ψ a`, over every open. -/
theorem abs_deg_res (V : trivializingOpens L) (k : ℕ) (a : 𝒜.grading (V : S.Opens) k)
    (W : (AlgebraicGeometry.Proj ((twist 𝒜 L).grading (V : S.Opens))).Opens) :
    ((abs V).iso (k : ℤ)).hom.val.app (op W)
        ((twistingSheaf (𝒜.grading (V : S.Opens)) (k : ℤ)).val.map
          (homOfLE (le_top : basisComparison L 𝒜 V ''ᵁ W ≤ ⊤)).op
          (degreeSection (𝒜.grading (V : S.Opens)) k a)) =
      (twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) (k : ℤ)).val.map
        (homOfLE (le_top : W ≤ ⊤)).op
        (degreeSection ((twist 𝒜 L).grading (V : S.Opens)) k
          ⟨psiSectionAt L 𝒜 V (basisSection L V) a,
            (psiSectionAt L 𝒜 V (basisSection L V)).map_mem a.2⟩) := by
  exact restrict_hom_app_map_eq (basisComparison L 𝒜 V) _ ((abs V).iso (k : ℤ)).hom
    (le_top : W ≤ ⊤) le_top le_top (degreeSection (𝒜.grading (V : S.Opens)) k a)
    ((abs V).deg k a)

/-- **The chart identification of the transported target carries the *multiply* map to the
homogeneous sections**, at the image `a ⊗ x^k` of a homogeneous element `a` of `𝒜`. -/
theorem targetChartIso_hom_psi_psiPiece (V : trivializingOpens L) (k : ℕ)
    (a : 𝒜.sectionPieces V k) :
    (targetChartIso L 𝒜 abs V (k : ℤ)).hom.val.app
        (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
          ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens))))
        (((transportedTarget L 𝒜).piece (k : ℤ)).val.map
          (homOfLE (((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1).image_preimage_le
            ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))).op
          ((transportedPsi L 𝒜 k).val.app (op (V : S.Opens))
            (psiPieceAt L 𝒜 V (basisSection L V) k a))) =
      (twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) (k : ℤ)).val.map
        (homOfLE (le_top : (relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
          ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)) ≤ ⊤)).op
        (degreeSection ((twist 𝒜 L).grading (V : S.Opens)) k
          ⟨DirectSum.of ((twist 𝒜 L).sectionPieces V) k
            (psiPieceAt L 𝒜 V (basisSection L V) k a),
            (twist 𝒜 L).of_mem_grading V (psiPieceAt L 𝒜 V (basisSection L V) k a)⟩) := by
  have e1 := targetChartIso_hom_app L 𝒜 abs V k
    ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
      ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))
    (((transportedTarget L 𝒜).piece (k : ℤ)).val.map
      (homOfLE (((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1).image_preimage_le
        ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))).op
      ((transportedPsi L 𝒜 k).val.app (op (V : S.Opens))
        (psiPieceAt L 𝒜 V (basisSection L V) k a)))
  have e2 := congrArg (((abs V).iso (k : ℤ)).hom.val.app
    (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
      ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens))))) (chartPre_psi L 𝒜 V k a)
  have e3 := abs_deg_res L 𝒜 abs V k
    ⟨DirectSum.of (𝒜.sectionPieces V) k a, 𝒜.of_mem_grading V a⟩
    ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
      ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))
  have e4 : (⟨psiSectionAt L 𝒜 V (basisSection L V)
        (DirectSum.of (𝒜.sectionPieces V) k a),
        (psiSectionAt L 𝒜 V (basisSection L V)).map_mem (𝒜.of_mem_grading V a)⟩ :
        (twist 𝒜 L).grading (V : S.Opens) k) =
      ⟨DirectSum.of ((twist 𝒜 L).sectionPieces V) k
        (psiPieceAt L 𝒜 V (basisSection L V) k a),
        (twist 𝒜 L).of_mem_grading V (psiPieceAt L 𝒜 V (basisSection L V) k a)⟩ :=
    Subtype.ext (psiSectionAt_of L 𝒜 V (basisSection L V) a)
  refine e1.trans (e2.trans (e3.trans ?_))
  exact congrArg (fun w => (twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) (k : ℤ)).val.map
    (homOfLE (le_top : (relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
      ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)) ≤ ⊤)).op
    (degreeSection ((twist 𝒜 L).grading (V : S.Opens)) k w)) e4

/-- The two sides of the homogeneous-section compatibility of the transported target, as
functions of the homogeneous element of `ℬ`. -/
def psiLhs (V : trivializingOpens L) (k : ℕ) (b : (twist 𝒜 L).sectionPieces V k) :
    (twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) (k : ℤ)).val.obj
      (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
        ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))) :=
  (targetChartIso L 𝒜 abs V (k : ℤ)).hom.val.app
    (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
      ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens))))
    (((transportedTarget L 𝒜).piece (k : ℤ)).val.map
      (homOfLE (((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1).image_preimage_le
        ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))).op
      ((transportedPsi L 𝒜 k).val.app (op (V : S.Opens)) b))

/-- See `psiLhs`. -/
def psiRhs (V : trivializingOpens L) (k : ℕ) (b : (twist 𝒜 L).sectionPieces V k) :
    (twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) (k : ℤ)).val.obj
      (op ((relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
        ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)))) :=
  (twistingSheaf ((twist 𝒜 L).grading (V : S.Opens)) (k : ℤ)).val.map
    (homOfLE (le_top : (relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ⁻¹ᵁ
      ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ (V : S.Opens)) ≤ ⊤)).op
    (degreeSection ((twist 𝒜 L).grading (V : S.Opens)) k
      ⟨DirectSum.of ((twist 𝒜 L).sectionPieces V) k b, (twist 𝒜 L).of_mem_grading V b⟩)

/-- The chart identification of the transported target carries the image under the *multiply*
map of a homogeneous element `b` of `ℬ` to the homogeneous section of `b`. -/
theorem psiLhs_eq_psiRhs (V : trivializingOpens L) (k : ℕ) (b : (twist 𝒜 L).sectionPieces V k) :
    psiLhs L 𝒜 abs V k b = psiRhs L 𝒜 V k b := by
  obtain ⟨a, ha⟩ := (bijective_psiPieceAt L 𝒜 V (basisSection L V) k
    (intTrivIso L (basisSection_trivializesPower L V 1 Nat.one_pos) k)
    ((generator_intTrivIso L _ k).trans (intPow_natCast L _ k))).surjective b
  exact ha ▸ targetChartIso_hom_psi_psiPiece L 𝒜 abs V k a

/-- **The transported target of Tag 02NC's `θ`, as twist data over the basis of affine opens
trivializing `ℒ`**, with the *multiply* map of clause (2) as its homogeneous-section map. -/
def targetTwistData : TwistExistenceBasis.BasisTwistData (twist 𝒜 L) (trivializingOpens L) :=
  TwistExistenceBasis.BasisTwistData.ofHom' (fun _ h => h.1) (transportedTarget L 𝒜)
    (targetChartIso L 𝒜 abs) (targetChartIso_hom_mul L 𝒜 abs)
    (transportedPsi L 𝒜) (psiLhs_eq_psiRhs L 𝒜 abs)

/-- The algebra of `targetTwistData` is the transported target. -/
theorem targetTwistData_algebra :
    (targetTwistData L 𝒜 abs).algebra = transportedTarget L 𝒜 := rfl

/-- The homogeneous-section map of `targetTwistData` is the transported *multiply* map. -/
theorem targetTwistData_ψ (k : ℕ) :
    (targetTwistData L 𝒜 abs).ψ k = transportedPsi L 𝒜 k := rfl

end TwistData

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
