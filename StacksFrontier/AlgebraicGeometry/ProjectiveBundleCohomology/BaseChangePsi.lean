module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeTwistMap
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TwistTransportData
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidInvariantSubmodule

/-!
# The comparison of the twists along the base change of a projective bundle and the
homogeneous-section maps

Let `g : X' ⟶ X` be a morphism of schemes, `E` a quasi-coherent `𝒪_X`-module, `E' ≅ g^*E`, and
`b : 𝐏(E') ⟶ 𝐏(E)` the morphism of projective bundles over `g`. The comparison
`θ♭ : 𝒪_{𝐏(E)}(k) ⟶ b_* 𝒪_{𝐏(E')}(k)` carries the image of a homogeneous section `s` of
`Sym^k(E)` under the homogeneous-section map of `𝐏(E)` to the image under that of `𝐏(E')` of the
pullback of `s`, read in `Sym^k(E') = g^* Sym^k(E)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.chartPush_psi_apply`: the chart value of
  a homogeneous-section image is the fraction `s / 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.TwistExistence
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

section Res

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  (M : SheafOfModules.{u} R)

/-- Two restriction maps compose to any other pair with the same source and target. -/
public theorem val_map₂ {a b c e : (Opens X)ᵒᵖ} (f₁ : a ⟶ b) (f₂ : b ⟶ c) (g₁ : a ⟶ e)
    (g₂ : e ⟶ c) (x : M.val.obj a) :
    M.val.map f₂ (M.val.map f₁ x) = M.val.map g₂ (M.val.map g₁ x) := by
  rw [← M.val.map_comp_apply, ← M.val.map_comp_apply, Subsingleton.elim (f₁ ≫ f₂) (g₁ ≫ g₂)]

/-- A restriction map from an open to itself is the identity. -/
public theorem val_map_self {a : (Opens X)ᵒᵖ} (f : a ⟶ a) (x : M.val.obj a) :
    M.val.map f x = x := by
  rw [Subsingleton.elim f (𝟙 a), PresheafOfModules.map_id]
  rfl

/-- Two restriction maps from an open back to itself compose to the identity. -/
public theorem val_map₂_self {a b : (Opens X)ᵒᵖ} (f₁ : a ⟶ b) (f₂ : b ⟶ a) (x : M.val.obj a) :
    M.val.map f₂ (M.val.map f₁ x) = x := by
  rw [← M.val.map_comp_apply]
  exact val_map_self M _ x

end Res

section Chart

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- **The chart value of the image of a homogeneous section** under the homogeneous-section map,
restricted to an open inside the inverse image of the affine open, is the fraction `s / 1` at
every point of the chart. -/
public theorem chartPush_psi_apply (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ)
    (b : A.sectionPieces U n) (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (z : ((relativeProj A).chart U hU ⁻¹ᵁ V : (AlgebraicGeometry.Proj (A.grading U)).Opens)) :
    ((chartPush D U hU (n : ℤ)).val.app (op V) ((D.algebra.piece (n : ℤ)).val.map (homOfLE hV).op
        ((D.ψ n).val.app (op U) b))).1 z =
      (degreeSection (A.grading U) n
        ⟨DirectSum.of (A.sectionPieces U) n b, A.of_mem_grading U b⟩).1 ⟨z.1, trivial⟩ := by
  let := D.chartData.chart_isOpenImmersion U hU
  have hres : (D.algebra.piece (n : ℤ)).val.map
        (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op
        ((D.algebra.piece (n : ℤ)).val.map (homOfLE hV).op ((D.ψ n).val.app (op U) b)) =
      (D.algebra.piece (n : ℤ)).val.map
        (homOfLE (((relativeProj A).chart U hU).image_mono
          (le_top : (relativeProj A).chart U hU ⁻¹ᵁ V ≤ ⊤))).op
        ((D.algebra.piece (n : ℤ)).val.map (eqToHom (D.chartData.chart_range U hU)).op
          ((D.ψ n).val.app (op U) b)) :=
    val_map₂ (D.algebra.piece (n : ℤ)) _ _ _ _ _
  have hnat := PresheafOfModules.naturality_apply (D.chartData.chartIso U hU (n : ℤ)).hom.val
    (homOfLE (le_top : (relativeProj A).chart U hU ⁻¹ᵁ V ≤ ⊤)).op
    ((D.algebra.piece (n : ℤ)).val.map (eqToHom (D.chartData.chart_range U hU)).op
      ((D.ψ n).val.app (op U) b))
  have hψ := chartIso_hom_psi D U hU n b
  change ((D.chartData.chartIso U hU (n : ℤ)).hom.val.app (op ((relativeProj A).chart U hU ⁻¹ᵁ V))
      ((D.algebra.piece (n : ℤ)).val.map
        (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op
        ((D.algebra.piece (n : ℤ)).val.map (homOfLE hV).op ((D.ψ n).val.app (op U) b)))).1 z = _
  rw [hres]
  refine (congrArg (fun s => s.1 z) hnat).trans ?_
  refine (congrArg (fun s => ((ProjectiveSpectrum.Proj.twistingSheaf (A.grading U) (n : ℤ)).val.map
    (homOfLE (le_top : (relativeProj A).chart U hU ⁻¹ᵁ V ≤ ⊤)).op s).1 z) hψ).trans ?_
  rfl

/-- **The chart value of a product** is the product of the chart values, at every point. -/
public theorem chartPush_mul_apply (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U)
    (i j : ℤ) (V : (relativeProj A).scheme.Opens) (x : (D.algebra.piece i).val.obj (op V))
    (y : (D.algebra.piece j).val.obj (op V))
    (z : ((relativeProj A).chart U hU ⁻¹ᵁ V : (AlgebraicGeometry.Proj (A.grading U)).Opens)) :
    ((chartPush D U hU (i + j)).val.app (op V) ((D.algebra.mul i j).app (op V) x y)).1 z =
      ((chartPush D U hU i).val.app (op V) x).1 z *
        ((chartPush D U hU j).val.app (op V) y).1 z := by
  let := D.chartData.chart_isOpenImmersion U hU
  change ((D.chartData.chartIso U hU (i + j)).hom.val.app (op ((relativeProj A).chart U hU ⁻¹ᵁ V))
      ((D.algebra.piece (i + j)).val.map
        (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op
        ((D.algebra.mul i j).app (op V) x y))).1 z = _
  have hn := (D.algebra.mul i j).naturality
    (homOfLE (((relativeProj A).chart U hU).image_preimage_le V)).op x y
  refine (congrArg (fun s => ((D.chartData.chartIso U hU (i + j)).hom.val.app
    (op ((relativeProj A).chart U hU ⁻¹ᵁ V)) s).1 z) hn).trans ?_
  refine (congrArg (fun s => s.1 z) (chartIso_hom_mul D U hU i j _ _ _)).trans ?_
  exact Stacks.AlgebraicGeometry.TwistRigidity.absoluteTwistProduct_apply _ i j _ _ _ z

end Chart

section Fibre

variable {A B : Type u} {σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A]
  [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ]

/-- The fibre comparison of a fraction with denominator one. -/
public theorem fibreMap_mk_one (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (y : ProjectiveSpectrum ℬ) (m : A) (m' : B) (hm : φ m = m') :
    Stacks.ProjTwistComparison.fibreMap φ hφ y (LocalizedModule.mk m 1) =
      LocalizedModule.mk m' 1 := by
  subst hm
  rw [Stacks.ProjTwistComparison.fibreMap_mk]
  congr 1
  exact Subtype.ext (map_one _)

end Fibre

section BaseChange

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E) (E' : X'.Modules) [E'.IsQuasicoherent]
  (hqc' : Stacks.SymGraded.IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (D : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc))
  (D' : TwistData (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc'))

/-- The pullback of a homogeneous section of `Sym(E)` over `U` to an open `W ⊆ g⁻¹U`, read in
`Sym(E')`. -/
public abbrev symPullbackSection (n : ℕ) (U : X.Opens) (W : X'.Opens) (h : W ≤ g ⁻¹ᵁ U)
    (x : (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces U n) :
    (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').sectionPieces W n :=
  Stacks.RelativeProj.Situation.pieceSectionHom (s := Stacks.SymGraded.symSituation E)
    (s' := Stacks.SymGraded.symSituation E') g
    (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE) n U W h x

/-- **The base-change map of graded rings of sections on a homogeneous section** is the pullback
of the section. -/
public theorem bundleChartRingHom_of (U : X.Opens) (W : X'.Opens) (hW : IsAffineOpen W)
    (h : W ≤ g ⁻¹ᵁ U) (n : ℕ)
    (x : (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces U n) :
    bundleChartRingHom g E hqc E' hqc' hE U W hW h
        (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces U) n x) =
      DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').sectionPieces W) n
        (symPullbackSection g E hqc E' hqc' hE n U W h x) := by
  have h1 := Stacks.SymGraded.situationSectionRingHom_of E hqc U x
  have h2 := Stacks.RelativeProj.Situation.sectionRingBaseChange_of
    (s := Stacks.SymGraded.symSituation E) (s' := Stacks.SymGraded.symSituation E') g
    (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE) U W h n x
  have h3 := Stacks.SymGraded.situationSectionRingHomInv_of E' hqc' W
    (symPullbackSection g E hqc E' hqc' hE n U W h x)
  exact (congrArg (Stacks.SymGraded.situationSectionRingHomInv E' hqc' W)
    ((congrArg (Stacks.RelativeProj.Situation.sectionRingBaseChange
      (s := Stacks.SymGraded.symSituation E) (s' := Stacks.SymGraded.symSituation E') g
      (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE) U W h) h1).trans h2)).trans h3

/-- The local comparison of the twists is determined by the fibre values of the charts. -/
private theorem thetaLoc_eq_of_chart_apply (U : X.Opens) (hU : IsAffineOpen U) (W : X'.Opens)
    (hW : IsAffineOpen W) (h : W ≤ g ⁻¹ᵁ U) (k : ℤ)
    (V : (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (x : (D.algebra.piece k).val.obj (op V))
    (x' : (D'.algebra.piece k).val.obj (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ W)))
    (H : ∀ z : ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).chart W hW ⁻¹ᵁ
      (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ W) :
        (AlgebraicGeometry.Proj
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').grading W)).Opens),
      Stacks.ProjTwistComparison.fibreMap (bundleChartRingHom g E hqc E' hqc' hE U W hW h)
        (irrelevant_le_bundleChartRingHom g E hqc E' hqc' hE U hU W hW h) z.1
        (((chartPush D U hU k).val.app (op V) x).1
          ⟨_, chartBC_mem g E hqc E' hqc' hE U hU W hW h V z.1 z.2.1⟩) =
        ((chartPush D' W hW k).val.app _ x').1 z) :
    thetaLoc g E hqc E' hqc' hE D D' U hU W hW h k V x = x' := by
  refine (bijective_chartPush D' W hW k _ inf_le_right).1 ?_
  refine (chartPush_thetaLoc g E hqc E' hqc' hE D D' U hU W hW h k V x).trans ?_
  exact Subtype.ext (funext fun z =>
    (thetaChart_apply g E hqc E' hqc' hE D U hU W hW h k V x ⟨z.1, z.2.1⟩).trans (H z))

/-- **The local comparison of the twists on the image of a homogeneous section**: it is the image
under the homogeneous-section map of `𝐏(E')` of the pullback of the section. -/
public theorem thetaLoc_psi (U : X.Opens) (hU : IsAffineOpen U) (W : X'.Opens)
    (hW : IsAffineOpen W) (h : W ≤ g ⁻¹ᵁ U) (n : ℕ)
    (V : (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (hV : V ≤ (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
    (x : (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces U n) :
    thetaLoc g E hqc E' hqc' hE D D' U hU W hW h (n : ℤ) V
        ((D.algebra.piece (n : ℤ)).val.map (homOfLE hV).op ((D.ψ n).val.app (op U) x)) =
      (D'.algebra.piece (n : ℤ)).val.map (homOfLE inf_le_right).op
        ((D'.ψ n).val.app (op W) (symPullbackSection g E hqc E' hqc' hE n U W h x)) := by
  refine thetaLoc_eq_of_chart_apply g E hqc E' hqc' hE D D' U hU W hW h (n : ℤ) V _ _ fun y => ?_
  refine Eq.trans ?_ (chartPush_psi_apply D' W hW n _ _ inf_le_right y).symm
  refine (congrArg _ (chartPush_psi_apply D U hU n x V hV _)).trans ?_
  rw [degreeSection_apply, degreeSection_apply]
  exact fibreMap_mk_one _ _ _ _ _ (bundleChartRingHom_of g E hqc E' hqc' hE U W hW h n x)

/-- **The local comparison of the twists is multiplicative.** -/
public theorem thetaLoc_mul (U : X.Opens) (hU : IsAffineOpen U) (W : X'.Opens)
    (hW : IsAffineOpen W) (h : W ≤ g ⁻¹ᵁ U) (i j : ℤ)
    (V : (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (x : (D.algebra.piece i).val.obj (op V)) (y : (D.algebra.piece j).val.obj (op V)) :
    thetaLoc g E hqc E' hqc' hE D D' U hU W hW h (i + j) V ((D.algebra.mul i j).app (op V) x y) =
      (D'.algebra.mul i j).app _ (thetaLoc g E hqc E' hqc' hE D D' U hU W hW h i V x)
        (thetaLoc g E hqc E' hqc' hE D D' U hU W hW h j V y) := by
  refine thetaLoc_eq_of_chart_apply g E hqc E' hqc' hE D D' U hU W hW h (i + j) V _ _ fun z => ?_
  refine Eq.trans ?_ (chartPush_mul_apply D' W hW i j _ _ _ z).symm
  refine (congrArg _ (chartPush_mul_apply D U hU i j V x y _)).trans ?_
  refine (map_mul _ _ _).trans ?_
  have hx := congrArg (fun s => s.1 z)
    (chartPush_thetaLoc g E hqc E' hqc' hE D D' U hU W hW h i V x)
  have hy := congrArg (fun s => s.1 z)
    (chartPush_thetaLoc g E hqc E' hqc' hE D D' U hU W hW h j V y)
  exact congrArg₂ (· * ·) hx.symm hy.symm

/-- **The glued comparison of the twists is multiplicative.** -/
public theorem thetaGlue_mul (U : X.Opens) (hU : IsAffineOpen U) (i j : ℤ)
    (V : (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (hV : V ≤ (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece i).val.obj (op V)) (y : (D.algebra.piece j).val.obj (op V)) :
    thetaGlue g E hqc E' hqc' hE D D' U hU (i + j) V hV ((D.algebra.mul i j).app (op V) x y) =
      (D'.algebra.mul i j).app _ (thetaGlue g E hqc E' hqc' hE D D' U hU i V hV x)
        (thetaGlue g E hqc E' hqc' hE D D' U hU j V hV y) := by
  refine (eq_thetaGlue g E hqc E' hqc' hE D D' U hU (i + j) V hV _ _ fun k => ?_).symm
  refine ((D'.algebra.mul i j).naturality (homOfLE inf_le_left).op _ _).trans ?_
  have h₁ := resLE_thetaGlue g E hqc E' hqc' hE D D' U hU i V hV x k
  have h₂ := resLE_thetaGlue g E hqc E' hqc' hE D D' U hU j V hV y k
  rw [PresheafOfModules.resLE_apply] at h₁ h₂
  rw [h₁, h₂]
  exact (thetaLoc_mul g E hqc E' hqc' hE D D' U hU k.1.1 k.1.2 k.2 i j V x y).symm

/-- The comparison of the twists is natural in the open. -/
public theorem thetaFlat_naturality (n : ℤ)
    {V V₁ : (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme.Opens}
    (h : V₁ ≤ V) (x : (D.algebra.piece n).val.obj (op V)) :
    (thetaFlat g E hqc E' hqc' hE D D' n).val.app (op V₁)
        ((D.algebra.piece n).val.map (homOfLE h).op x) =
      (D'.algebra.piece n).val.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op
        ((thetaFlat g E hqc E' hqc' hE D D' n).val.app (op V) x) :=
  PresheafOfModules.naturality_apply (thetaFlat g E hqc E' hqc' hE D D' n).val (homOfLE h).op x

/-- **The comparison of the twists is multiplicative**, on the sections over every open. -/
public theorem thetaFlat_mul (i j : ℤ)
    (V : (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (x : (D.algebra.piece i).val.obj (op V)) (y : (D.algebra.piece j).val.obj (op V)) :
    (thetaFlat g E hqc E' hqc' hE D D' (i + j)).val.app (op V)
        ((D.algebra.mul i j).app (op V) x y) =
      (D'.algebra.mul i j).app (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V))
        ((thetaFlat g E hqc E' hqc' hE D D' i).val.app (op V) x)
        ((thetaFlat g E hqc E' hqc' hE D D' j).val.app (op V) y) := by
  refine Stacks.AlgebraicGeometry.GroupoidCardinalGeneration.sections_eq_of_locally_eq
    (D'.algebra.piece (i + j)) _ _ fun p hp => ?_
  obtain ⟨U, hU, hpU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase.base
      ((bundleBaseChange g E hqc E' hqc' hE).base p) ∈ (⊤ : X.Opens) from trivial)
  have hle :
      V ⊓ (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U ≤ V :=
    inf_le_left
  refine ⟨bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ
      (V ⊓ (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U),
    Scheme.Hom.preimage_mono _ hle, ⟨hp, hpU⟩, ?_⟩
  have e₀ := thetaFlat_naturality g E hqc E' hqc' hE D D' (i + j) hle
    ((D.algebra.mul i j).app (op V) x y)
  have eₓ := thetaFlat_naturality g E hqc E' hqc' hE D D' i hle x
  have eᵧ := thetaFlat_naturality g E hqc E' hqc' hE D D' j hle y
  have hm := (D.algebra.mul i j).naturality (homOfLE hle).op x y
  have hm' := (D'.algebra.mul i j).naturality (homOfLE (Scheme.Hom.preimage_mono _ hle)).op
    ((thetaFlat g E hqc E' hqc' hE D D' i).val.app (op V) x)
    ((thetaFlat g E hqc E' hqc' hE D D' j).val.app (op V) y)
  have hg := thetaGlue_mul g E hqc E' hqc' hE D D' U hU i j _ inf_le_right
    ((D.algebra.piece i).val.map (homOfLE hle).op x)
    ((D.algebra.piece j).val.map (homOfLE hle).op y)
  have t₀ := thetaFlat_app g E hqc E' hqc' hE D D' U hU (i + j) _ inf_le_right
    ((D.algebra.mul i j).app (op (V ⊓
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
      ((D.algebra.piece i).val.map (homOfLE hle).op x)
      ((D.algebra.piece j).val.map (homOfLE hle).op y))
  have tₓ := thetaFlat_app g E hqc E' hqc' hE D D' U hU i _ inf_le_right
    ((D.algebra.piece i).val.map (homOfLE hle).op x)
  have tᵧ := thetaFlat_app g E hqc E' hqc' hE D D' U hU j _ inf_le_right
    ((D.algebra.piece j).val.map (homOfLE hle).op y)
  refine e₀.symm.trans ?_
  refine (congrArg ((thetaFlat g E hqc E' hqc' hE D D' (i + j)).val.app _) hm).trans ?_
  refine t₀.trans (hg.trans ?_)
  refine (congrArg₂ (fun a b => (D'.algebra.mul i j).app _ a b) tₓ.symm tᵧ.symm).trans ?_
  exact (congrArg₂ (fun a b => (D'.algebra.mul i j).app _ a b) eₓ eᵧ).trans hm'.symm

/-- **The comparison of the twists commutes with the homogeneous-section maps**: the composite
`Sym^k(E) ⟶ π_* 𝒪(k) ⟶ π_* b_* 𝒪'(k) = g_* π'_* 𝒪'(k)` is the unit `Sym^k(E) ⟶ g_* g^* Sym^k(E)`
followed by `g_*` of `g^* Sym^k(E) = Sym^k(E') ⟶ π'_* 𝒪'(k)`. -/
public theorem psi_comp_thetaFlat (n : ℕ) :
    D.ψ n ≫ (Scheme.Modules.pushforward
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase).map
        (thetaFlat g E hqc E' hqc' hE D D' (n : ℤ)) ≫
      (Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
        (bundleBaseChange g E hqc E' hqc' hE)
        (bundleBaseChange_toBase g E hqc E' hqc' hE)).hom.app (D'.algebra.piece (n : ℤ)) =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (n : ℤ)) ≫
        (Scheme.Modules.pushforward g).map
          ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (n : ℤ) ≫ D'.ψ n) := by
  refine Stacks.AlgebraicGeometry.GroupoidCardinalGeneration.hom_ext_of_isBasis _ _
    X.isBasis_affineOpens fun U hU z => ?_
  set a := ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (n : ℤ)).val.app
    (op (g ⁻¹ᵁ U)) ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (n : ℤ))).val.app (op U)) z)
  have e : bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ
        ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U) =
      (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ (g ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, bundleBaseChange_toBase]
  let y : (D'.algebra.piece (n : ℤ)).val.obj (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ
      ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))) :=
    (D'.algebra.piece (n : ℤ)).val.map (eqToHom e).op ((D'.ψ n).val.app (op (g ⁻¹ᵁ U)) a)
  have hy : ∀ i : OverIdx g U, (D'.algebra.piece (n : ℤ)).val.resLE inf_le_left y =
      thetaLocFam g E hqc E' hqc' hE D D' U hU (n : ℤ)
        ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
        ((D.ψ n).val.app (op U) z) i := by
    intro i
    have hz : (D.algebra.piece (n : ℤ)).val.map (homOfLE (le_refl
        ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))).op
        ((D.ψ n).val.app (op U) z) = (D.ψ n).val.app (op U) z :=
      val_map_self (D.algebra.piece (n : ℤ)) _ _
    have hΦ := PresheafOfModules.naturality_apply
      ((Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE).app (n : ℤ)).val
      (homOfLE i.2).op ((((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).piece (n : ℤ))).val.app (op U)) z)
    have hψ := PresheafOfModules.naturality_apply (D'.ψ n).val (homOfLE i.2).op a
    have hloc := thetaLoc_psi g E hqc E' hqc' hE D D' U hU i.1.1 i.1.2 i.2 n
      ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U) le_rfl z
    rw [hz] at hloc
    refine Eq.trans ?_ hloc.symm
    have hsps : symPullbackSection g E hqc E' hqc' hE n U i.1.1 i.2 z =
        ((Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc').piece (n : ℤ)).val.map
          (homOfLE i.2).op a := hΦ
    rw [hsps, hψ]
    exact val_map₂ (D'.algebra.piece (n : ℤ)) _ _ _ _ _
  have hglue := eq_thetaGlue g E hqc E' hqc' hE D D' U hU (n : ℤ)
    ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U) le_rfl
    ((D.ψ n).val.app (op U) z) y hy
  change ((Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
        (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
        (bundleBaseChange g E hqc E' hqc' hE)
        (bundleBaseChange_toBase g E hqc E' hqc' hE)).hom.app (D'.algebra.piece (n : ℤ))).app U
      ((thetaFlat g E hqc E' hqc' hE D D' (n : ℤ)).val.app
        (op ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
        ((D.ψ n).val.app (op U) z)) = (D'.ψ n).val.app (op (g ⁻¹ᵁ U)) a
  have hsq :=
    Stacks.AlgebraicGeometry.HigherDirectImageBaseChange.pushforwardSquareIso_hom_app_app
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase g
    (relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E' hqc')).toBase
    (bundleBaseChange g E hqc E' hqc' hE) (bundleBaseChange_toBase g E hqc E' hqc' hE)
    (D'.algebra.piece (n : ℤ)) U
  refine (congrArg (fun φ => φ ((thetaFlat g E hqc E' hqc' hE D D' (n : ℤ)).val.app
        (op ((relativeProj (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U))
        ((D.ψ n).val.app (op U) z))) (congrArg ConcreteCategory.hom hsq)).trans ?_
  have hθ := thetaFlat_app g E hqc E' hqc' hE D D' U hU (n : ℤ) _ le_rfl
    ((D.ψ n).val.app (op U) z)
  refine (congrArg (fun t => (D'.algebra.piece (n : ℤ)).val.map _ t) hθ).trans ?_
  refine (congrArg (fun t => (D'.algebra.piece (n : ℤ)).val.map _ t) hglue.symm).trans ?_
  exact val_map₂_self (D'.algebra.piece (n : ℤ)) _ _ _

end BaseChange

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
