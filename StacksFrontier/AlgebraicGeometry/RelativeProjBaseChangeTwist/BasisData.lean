module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.PsiChart
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Basis

/-!
# The pulled-back twists as twist data over a basis

The pulled-back twists `f^*(⨁_d 𝒪_{Proj_S(A)}(d))` on `Proj_{S'}(g^*A)`, with their chart
identifications over the members of `baseChangeBasis g` and the base-changed homogeneous-section
map, form twist data of Tag 01NR over that basis.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open AlgebraicGeometry.Scheme.Modules (pullbackSection)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

section GenericBasis

variable {S₀ : Scheme.{u}} (A₀ : SheafGradedAlgebra S₀) {𝔅 : Set S₀.Opens}
  (h𝔅a : ∀ U ∈ 𝔅, IsAffineOpen U)
  (algebra : RelativeProjTwists.SchemeGradedAlgebra
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).scheme)
  (chartIso : ∀ (V : 𝔅) (n : ℤ),
    Scheme.Modules.restrict (algebra.piece n)
        ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1 (h𝔅a V.1 V.2)) ≅
      twistingSheaf (A₀.grading V.1) n)
  (ψ : ∀ n : ℕ, A₀.piece (n : ℤ) ⟶
    (Scheme.Modules.pushforward (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).toBase).obj
      (algebra.piece (n : ℤ)))

/-- The forward homogeneous-section compatibility of chart identifications over a basis, from its
form on the composite into the direct image of the absolute twists. -/
theorem psiChartHom_of_chartPsiHom
    (hyp : ∀ (V : 𝔅) (k : ℕ) (a : A₀.sectionPieces V.1 k),
      (chartPsiHom (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).toBase
          ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1 (h𝔅a V.1 V.2))
          (Bk := algebra.piece (k : ℤ)) (ψ k) (chartIso V (k : ℤ))).val.app (op V.1) a =
        (twistingSheaf (A₀.grading V.1) (k : ℤ)).val.map
          (homOfLE (le_top :
            (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1 (h𝔅a V.1 V.2) ⁻¹ᵁ
              ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).toBase ⁻¹ᵁ V.1) ≤ ⊤)).op
          (degreeSection (A₀.grading V.1) k
            ⟨DirectSum.of (A₀.sectionPieces V.1) k a, A₀.of_mem_grading V.1 a⟩)) :
    ∀ (V : 𝔅) (k : ℕ) (a : A₀.sectionPieces V.1 k),
      (chartIso V (k : ℤ)).hom.val.app
          (op ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1 (h𝔅a V.1 V.2) ⁻¹ᵁ
            ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).toBase ⁻¹ᵁ V.1)))
          ((algebra.piece (k : ℤ)).val.map
            (homOfLE (((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1
              (h𝔅a V.1 V.2)).image_preimage_le
              ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).toBase ⁻¹ᵁ V.1))).op
                ((ψ k).val.app (op V.1) a)) =
        (twistingSheaf (A₀.grading V.1) (k : ℤ)).val.map
          (homOfLE (le_top : (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1
            (h𝔅a V.1 V.2) ⁻¹ᵁ
            ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).toBase ⁻¹ᵁ V.1) ≤ ⊤)).op
          (degreeSection (A₀.grading V.1) k
            ⟨DirectSum.of (A₀.sectionPieces V.1) k a, A₀.of_mem_grading V.1 a⟩) :=
  fun V k a => (chartPsiHom_app _ _ (ψ k) (chartIso V (k : ℤ)) V.1 a).symm.trans (hyp V k a)

/-- The forward multiplicativity of chart identifications over a basis, in the form in which
`TwistExistenceBasis.BasisTwistData.ofHom'` takes it. -/
theorem chartIsoHomMul_of_forall
    (hyp : ∀ (V : 𝔅) (i j : ℤ)
      (W : (AlgebraicGeometry.Proj (A₀.grading V.1)).Opens)
      (x : (algebra.piece i).val.obj
        (op ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1 (h𝔅a V.1 V.2) ''ᵁ
          W)))
      (y : (algebra.piece j).val.obj
        (op ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1 (h𝔅a V.1 V.2) ''ᵁ
          W))),
      (chartIso V (i + j)).hom.val.app (op W)
          ((algebra.mul i j).app
            (op ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1 (h𝔅a V.1 V.2) ''ᵁ
              W)) x y) =
        RelativeProjTwists.absoluteTwistProduct (A₀.grading V.1) i j W
          ((chartIso V i).hom.val.app (op W) x) ((chartIso V j).hom.val.app (op W) y)) :
    ∀ (V : 𝔅) (i j : ℤ)
      (W : (AlgebraicGeometry.Proj (A₀.grading V.1)).Opens)
      (x : (algebra.piece i).val.obj
        (op ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1 (h𝔅a V.1 V.2) ''ᵁ
          W)))
      (y : (algebra.piece j).val.obj
        (op ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1 (h𝔅a V.1 V.2) ''ᵁ
          W))),
      (chartIso V (i + j)).hom.val.app (op W)
          ((algebra.mul i j).app
            (op ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj A₀).chart V.1 (h𝔅a V.1 V.2) ''ᵁ
              W)) x y) =
        RelativeProjTwists.absoluteTwistProduct (A₀.grading V.1) i j W
          ((chartIso V i).hom.val.app (op W) x) ((chartIso V j).hom.val.app (op W) y) :=
  hyp

end GenericBasis

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)

/-- **The chart identification of the pulled-back twists** over a member of the basis. -/
def pulledChart (V : baseChangeBasis g) (n : ℤ) :
    Scheme.Modules.restrict ((pbAlgS (baseChangeHom A g) (twistAlgebra A)).piece n)
        ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).chart V.1
          (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2)) ≅
      twistingSheaf ((A.pullback g).grading V.1) n :=
  (genChartIso (twistAlgebra A) (baseChangeHom A g)
    ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).chart V.1
    (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2))
      (chartSection A g V)
      (mapHom (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V))
      (chartU A g V)
      (mapDomain (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V)).ι
      (chart_comp_baseChangeHom A g V) (chartSection_ι A g V)
      (fun n => twistingSheaf (A.grading (affOf V).1) n)
      (fun n => twistingSheaf ((A.pullback g).grading V.1) n)
      (fun n => chartTwistIso A n (affOf V))
      (fun n => twistMap (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V) n)
      (fun n => isIso_twistMap_chartMap A g V n) n)

/-- **The homogeneous-section map of the pulled-back twists**: Tag 01NR's `ψ` for `A`, base
changed along `g`. -/
def pulledPsiB (k : ℕ) :
    (A.pullback g).piece (k : ℤ) ⟶ (Scheme.Modules.pushforward
      (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase).obj
      ((pbAlgS (baseChangeHom A g) (twistAlgebra A)).piece (k : ℤ)) :=
  (basePsi (M := A.piece (k : ℤ))
    (O := (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.piece (k : ℤ))
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase
    (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase g (baseChangeHom A g)
    (baseChangeHom_comp_toBase A g)
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ k))


/-- **The chart identifications of the pulled-back twists carry the base-changed
homogeneous-section map to the absolute homogeneous sections.** -/
theorem pulledPsiChartHom :
    type_of% (psiChartHom_of_chartPsiHom (A.pullback g) (isAffineOpen_of_mem_baseChangeBasis g)
      (pbAlgS (baseChangeHom A g) (twistAlgebra A))
        (fun V n => pulledChart A g V n)
        (fun k => pulledPsiB A g k)
      (fun V k a => by
        beta_reduce
        exact genChartIso_field (twistAlgebra A) (baseChangeHom A g)
          ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).chart V.1
          (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2))
          (chartSection A g V)
          (mapHom (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V))
          (chartU A g V)
          (mapDomain (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V)).ι
          (chart_comp_baseChangeHom A g V) (chartSection_ι A g V)
          (fun n => twistingSheaf (A.grading (affOf V).1) n)
          (fun n => twistingSheaf ((A.pullback g).grading V.1) n)
          (fun n => chartTwistIso A n (affOf V))
          (fun n => twistMap (A.grading (affOf V).1) ((A.pullback g).grading V.1)
            (chartMap A g V) n)
          (fun n => isIso_twistMap_chartMap A g V n)
          (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase
            (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase g
            (baseChangeHom_comp_toBase A g) (k : ℤ)
          ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ k) (baseOpen V).toOpens
          (affOf V).2 V.1 V.2.1 (le_baseOpen V) (preimage_le_baseChangeHom A g V)
          ((A.pullback g).piece (k : ℤ)) (SheafGradedAlgebra.pullback_piece A g (k : ℤ)).symm
          (TwistExistenceBasis.BasisTwistData.ofTwistData (𝔅 := baseChangeBasis g)
            (GluedTwistAlgebra.twistDataOfGradedAlgebra (A.pullback g))).algebra
            ((TwistExistenceBasis.BasisTwistData.ofTwistData (𝔅 := baseChangeBasis g)
            (GluedTwistAlgebra.twistDataOfGradedAlgebra (A.pullback g))).chartIso V.1
            (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2) V.2 (k : ℤ))
          ((TwistExistenceBasis.BasisTwistData.ofTwistData (𝔅 := baseChangeBasis g)
            (GluedTwistAlgebra.twistDataOfGradedAlgebra (A.pullback g))).ψ k)
          (fun a => (twistingSheaf ((A.pullback g).grading V.1) (k : ℤ)).val.map
            (homOfLE (le_top : (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
              (A.pullback g)).chart V.1 (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2) ⁻¹ᵁ
              ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase ⁻¹ᵁ V.1) ≤
              ⊤)).op
            (degreeSection ((A.pullback g).grading V.1) k
              ⟨DirectSum.of ((A.pullback g).sectionPieces V.1) k a,
                (A.pullback g).of_mem_grading V.1 a⟩))
          (fun b => by
            beta_reduce
            exact (TwistExistenceBasis.chartLoc_app_eq
              (TwistExistenceBasis.BasisTwistData.ofTwistData (𝔅 := baseChangeBasis g)
              (GluedTwistAlgebra.twistDataOfGradedAlgebra (A.pullback g))) V.1
              (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2) V.2 (k : ℤ) _ le_rfl
              (((TwistExistenceBasis.BasisTwistData.ofTwistData (𝔅 := baseChangeBasis g)
                (GluedTwistAlgebra.twistDataOfGradedAlgebra (A.pullback g))).ψ k).val.app
                (op V.1) b)).symm.trans
              (TwistExistenceBasis.chartLoc_psi (TwistExistenceBasis.BasisTwistData.ofTwistData
                (𝔅 := baseChangeBasis g) (GluedTwistAlgebra.twistDataOfGradedAlgebra
                (A.pullback g))) V.1 (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2) V.2 k b))
          (fun a0 => degreeSection (A.grading (affOf V).1) k
            ⟨DirectSum.of (A.sectionPieces (affOf V).1) k a0, A.of_mem_grading (affOf V).1 a0⟩)
          (fun a0 => degreeSection ((A.pullback g).grading V.1) k
            ⟨chartMap A g V (DirectSum.of (A.sectionPieces (affOf V).1) k a0),
              (chartMap A g V).map_mem (A.of_mem_grading (affOf V).1 a0)⟩)
          (fun a0 => chartTwistIso_pullbackSection_psi A g V k a0)
          (fun a0 => twistMap_pullbackSection_top _ _ (chartMap A g V) k
            ⟨DirectSum.of (A.sectionPieces (affOf V).1) k a0, A.of_mem_grading (affOf V).1 a0⟩)
          (fun a0 => (pullbackSection g (A.piece (k : ℤ)) (baseOpen V).toOpens V.1
            (le_baseOpen V) a0 :
            ((A.pullback g).piece (k : ℤ)).val.obj (op V.1)))
          (fun a0 => HEq.rfl)
          (fun a0 => by
            beta_reduce
            have hd : (⟨chartMap A g V (DirectSum.of (A.sectionPieces (affOf V).1) k a0),
                (chartMap A g V).map_mem (A.of_mem_grading (affOf V).1 a0)⟩ :
                  (A.pullback g).grading V.1 k) =
                ⟨DirectSum.of ((A.pullback g).sectionPieces V.1) k
                  (pullbackSection g (A.piece (k : ℤ)) (baseOpen V).toOpens V.1 (le_baseOpen V) a0),
                  (A.pullback g).of_mem_grading V.1 _⟩ :=
              Subtype.ext (sectionBaseChange_of A g (baseOpen V) (siteOf V) (le_baseOpen V) k a0)
            exact (twistingSheaf_val_map_modules ((A.pullback g).grading V.1) (k : ℤ) _ _).trans
              (congrArg (fun z => (twistingSheaf ((A.pullback g).grading V.1) (k : ℤ)).val.map
                (homOfLE (le_top : (Stacks.AlgebraicGeometry.RelativeProj.relativeProj
                  (A.pullback g)).chart V.1 (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2) ⁻¹ᵁ
                  ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj
                  (A.pullback g)).toBase ⁻¹ᵁ V.1) ≤ ⊤)).op
                (degreeSection ((A.pullback g).grading V.1) k z)) hd))
          (pulledChart A g V (k : ℤ)) rfl
          (pulledPsiB A g k) HEq.rfl a)) :=
  psiChartHom_of_chartPsiHom (A.pullback g) (isAffineOpen_of_mem_baseChangeBasis g)
    (pbAlgS (baseChangeHom A g) (twistAlgebra A)) (fun V n => pulledChart A g V n)
    (fun k => pulledPsiB A g k)
    (fun V k a => by
      let E := TwistExistenceBasis.BasisTwistData.ofTwistData (𝔅 := baseChangeBasis g)
        (GluedTwistAlgebra.twistDataOfGradedAlgebra (A.pullback g))
      beta_reduce
      exact genChartIso_field (twistAlgebra A) (baseChangeHom A g)
        ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).chart V.1
          (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2)) (chartSection A g V)
        (mapHom (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V))
        (chartU A g V)
        (mapDomain (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V)).ι
        (chart_comp_baseChangeHom A g V) (chartSection_ι A g V)
        (fun n => twistingSheaf (A.grading (affOf V).1) n)
        (fun n => twistingSheaf ((A.pullback g).grading V.1) n)
        (fun n => chartTwistIso A n (affOf V))
        (fun n => twistMap (A.grading (affOf V).1) ((A.pullback g).grading V.1)
          (chartMap A g V) n)
        (fun n => isIso_twistMap_chartMap A g V n) _ _ _ (baseChangeHom_comp_toBase A g) (k : ℤ)
        ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ k) _ (affOf V).2 V.1 V.2.1
        (le_baseOpen V) (preimage_le_baseChangeHom A g V) _
        (SheafGradedAlgebra.pullback_piece A g (k : ℤ)).symm E.algebra
        (E.chartIso V.1 (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2) V.2 (k : ℤ)) (E.ψ k) _
        (fun b => (TwistExistenceBasis.chartLoc_app_eq E V.1 _ V.2 (k : ℤ) _ le_rfl
          ((E.ψ k).val.app (op V.1) b)).symm.trans
          (TwistExistenceBasis.chartLoc_psi E V.1 _ V.2 k b))
        (fun a0 => degreeSection (A.grading (affOf V).1) k
          ⟨DirectSum.of (A.sectionPieces (affOf V).1) k a0, A.of_mem_grading (affOf V).1 a0⟩)
        (fun a0 => degreeSection ((A.pullback g).grading V.1) k
          ⟨chartMap A g V (DirectSum.of (A.sectionPieces (affOf V).1) k a0),
            (chartMap A g V).map_mem (A.of_mem_grading (affOf V).1 a0)⟩)
        (fun a0 => chartTwistIso_pullbackSection_psi A g V k a0)
        (fun a0 => twistMap_pullbackSection_top _ _ (chartMap A g V) k
          ⟨DirectSum.of (A.sectionPieces (affOf V).1) k a0, A.of_mem_grading (affOf V).1 a0⟩)
        (fun a0 => pullbackSection g (A.piece (k : ℤ)) (baseOpen V).toOpens V.1
          (le_baseOpen V) a0)
        (fun a0 => HEq.rfl)
        (fun a0 => by
          have hd : (⟨chartMap A g V (DirectSum.of (A.sectionPieces (affOf V).1) k a0),
              (chartMap A g V).map_mem (A.of_mem_grading (affOf V).1 a0)⟩ :
                (A.pullback g).grading V.1 k) =
              ⟨DirectSum.of ((A.pullback g).sectionPieces V.1) k
                (pullbackSection g (A.piece (k : ℤ)) (baseOpen V).toOpens V.1 (le_baseOpen V) a0),
                (A.pullback g).of_mem_grading V.1 _⟩ :=
            Subtype.ext (sectionBaseChange_of A g (baseOpen V) (siteOf V) (le_baseOpen V) k a0)
          exact (twistingSheaf_val_map_modules ((A.pullback g).grading V.1) (k : ℤ) _ _).trans
            (congrArg (fun z => (twistingSheaf ((A.pullback g).grading V.1) (k : ℤ)).val.map _
              (degreeSection ((A.pullback g).grading V.1) k z)) hd))
        (pulledChart A g V (k : ℤ)) rfl (pulledPsiB A g k) HEq.rfl a)

/-- **The chart identifications of the pulled-back twists are multiplicative.** -/
theorem pulledChartIsoHomMul :
    type_of% (chartIsoHomMul_of_forall (A.pullback g) (isAffineOpen_of_mem_baseChangeBasis g)
      (pbAlgS (baseChangeHom A g) (twistAlgebra A)) (fun V n => pulledChart A g V n)
      (fun V i j W x y => by
        beta_reduce
        exact genChartIso_field_mul ((A.pullback g).grading V.1) (twistAlgebra A)
          (baseChangeHom A g)
              ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).chart V.1
                (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2)) (chartSection A g V)
              (mapHom (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V))
              (chartU A g V)
              (mapDomain (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V)).ι
              (chart_comp_baseChangeHom A g V) (chartSection_ι A g V)
              (fun n => twistingSheaf (A.grading (affOf V).1) n)
              (fun n => chartTwistIso A n (affOf V))
              (fun n => twistMap (A.grading (affOf V).1) ((A.pullback g).grading V.1)
                (chartMap A g V) n)
              (fun n => isIso_twistMap_chartMap A g V n)
              (fun i j => Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
                (A.grading (affOf V).1) i j)
              (fun i j => chartTwistIso_mul_affOf A g V i j)
              (fun i j => pbMul_twistMultiplicationMap_twistMap _ _ (chartMap A g V) i j)
              (fun n => pulledChart A g V n) rfl i j W x y)) :=
  chartIsoHomMul_of_forall (A.pullback g) (isAffineOpen_of_mem_baseChangeBasis g)
    (pbAlgS (baseChangeHom A g) (twistAlgebra A)) (fun V n => pulledChart A g V n)
    (fun V i j W x y => by
      beta_reduce
      exact genChartIso_field_mul ((A.pullback g).grading V.1) (twistAlgebra A) (baseChangeHom A g)
            ((Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).chart V.1
              (isAffineOpen_of_mem_baseChangeBasis g V.1 V.2)) (chartSection A g V)
            (mapHom (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V))
            (chartU A g V)
            (mapDomain (A.grading (affOf V).1) ((A.pullback g).grading V.1) (chartMap A g V)).ι
            (chart_comp_baseChangeHom A g V) (chartSection_ι A g V)
            (fun n => twistingSheaf (A.grading (affOf V).1) n)
            (fun n => chartTwistIso A n (affOf V))
            (fun n => twistMap (A.grading (affOf V).1) ((A.pullback g).grading V.1)
              (chartMap A g V) n)
            (fun n => isIso_twistMap_chartMap A g V n)
            _ (chartTwistIso_mul_affOf A g V)
            (pbMul_twistMultiplicationMap_twistMap _ _ (chartMap A g V))
            (pulledChart A g V) rfl i j W x y)

/-- **The pulled-back twists as twist data over the basis `baseChangeBasis g`.** -/
def pulledBasisData : TwistExistenceBasis.BasisTwistData (A.pullback g) (baseChangeBasis g) :=
  TwistExistenceBasis.BasisTwistData.ofHom' (isAffineOpen_of_mem_baseChangeBasis g)
    (pbAlgS (baseChangeHom A g) (twistAlgebra A))
    (fun V n => pulledChart A g V n) (pulledChartIsoHomMul A g)
    (fun k => pulledPsiB A g k) (pulledPsiChartHom A g)

/-- **The comparison of the pulled-back twists with the twists of `Proj_{S'}(g^*A)`**, as
graded algebras: the glueing over `baseChangeBasis g` of the chart comparisons. -/
def pulledTwistIso : (pbAlgS (baseChangeHom A g) (twistAlgebra A)) ≅ twistAlgebra (A.pullback g) :=
  TwistExistenceBasis.glueAlgIso (isBasis_baseChangeBasis g) (isAffineOpen_of_mem_baseChangeBasis g)
    (pulledBasisData A g)
    (TwistExistenceBasis.BasisTwistData.ofTwistData (GluedTwistAlgebra.twistDataOfGradedAlgebra
      (A.pullback g)))

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
