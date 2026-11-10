module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.BaseChangeBundle
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TwistChartTransition
public import StacksFrontier.AlgebraicGeometry.TwistExistence.Chart
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Functorial

/-!
# The twists of a projective bundle under base change

Let `g : X' ⟶ X` be a morphism of schemes, `E` a quasi-coherent `𝒪_X`-module, `E' ≅ g^*E`, and
`b : 𝐏(E') ⟶ 𝐏(E)` the morphism of projective bundles over `g` (Tag 01O3). For twist data `D` on
`𝐏(E)` and `D'` on `𝐏(E')` (Tag 01NR) there is a canonical map
`θ♭ : 𝒪_{𝐏(E)}(n) ⟶ b_* 𝒪_{𝐏(E')}(n)` for every integer `n`: over the chart of an affine open
`W'` of `X'` lying over an affine open `U` of `X` it is the pointwise localization of the
base-change map `Γ(U, Sym E) ⟶ Γ(W', Sym E')` on degree-`n` fractions.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaChart`: the chart description, as a
  morphism `𝒪_{𝐏(E)}(n) ⟶ b_* (chart_{W'})_* 𝒪(n)`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaLoc`: its value on the part of
  `b⁻¹(V)` lying over `W'`, read back through the chart identification of `D'`.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaGlue`: the values over all affine
  opens of `X'` lying over `U`, glued to a section over `b⁻¹(V)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.res_comp_bundleChartRingHom`: the
  base-change map of graded rings of sections is natural in both opens.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaChart_apply`: the chart description
  is the pointwise localization of the base-change map.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaLoc_res`: the local values agree on
  nested charts.
* `Stacks.AlgebraicGeometry.ProjectiveBundleCohomology.thetaLoc_add` and `thetaLoc_resLE`: the
  local values are additive and natural in the open.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SymGraded

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Ring

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (hqc : IsQuasicoherentPieces E)

/-- The inverse identification of the graded rings of sections of the two presentations is
compatible with restriction. -/
public theorem situationGradedInv_res (U V : X.Opens) (h : U ≤ V) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (y : (symSituation E).sectionRing V) :
    (situationSheafGradedAlgebra E hqc).res h (situationGradedInv E hqc ⟨V, hV⟩ y) =
      situationGradedInv E hqc ⟨U, hU⟩
        (Stacks.RelativeProj.Situation.gradedSectionRestriction (symSituation E) U V h y) := by
  have h1 := GradedRingHom.congr_fun (situationGradedHom_res E hqc U V h)
    (situationGradedInv E hqc ⟨V, hV⟩ y)
  simp only [GradedRingHom.comp_apply] at h1
  have h2 : situationGradedHom E hqc V (situationGradedInv E hqc ⟨V, hV⟩ y) = y :=
    situationSectionRingHom_inv E hqc V y
  rw [h2] at h1
  rw [← h1]
  exact (situationSectionRingHomInv_hom E hqc U _).symm

end Ring

section BaseChange

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E) (E' : X'.Modules) [E'.IsQuasicoherent]
  (hqc' : IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)

/-- **The base-change map of graded rings of sections is natural in both opens.** -/
public theorem res_comp_bundleChartRingHom {U₁ U₂ : X.Opens} (hU : U₂ ≤ U₁) {W₁ W₂ : X'.Opens}
    (hW : W₂ ≤ W₁) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂) (h₁ : W₁ ≤ g ⁻¹ᵁ U₁)
    (h₂ : W₂ ≤ g ⁻¹ᵁ U₂) :
    ((situationSheafGradedAlgebra E' hqc').res hW).comp
        (bundleChartRingHom g E hqc E' hqc' hE U₁ W₁ hW₁ h₁) =
      (bundleChartRingHom g E hqc E' hqc' hE U₂ W₂ hW₂ h₂).comp
        ((situationSheafGradedAlgebra E hqc).res hU) := by
  refine GradedRingHom.ext fun x => ?_
  simp only [GradedRingHom.comp_apply, bundleChartRingHom]
  rw [situationGradedInv_res E' hqc' W₂ W₁ hW hW₂ hW₁]
  congr 1
  have e1 := GradedRingHom.congr_fun
    (Stacks.RelativeProj.Situation.gradedRestrict_comp_gradedBaseChange (s := symSituation E)
      (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE) U₁
      hW h₁ (hW.trans h₁)) (situationGradedHom E hqc U₁ x)
  have e2 := GradedRingHom.congr_fun
    (Stacks.RelativeProj.Situation.gradedBaseChange_comp_gradedRestrict (s := symSituation E)
      (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE) hU
      W₂ h₂ (hW.trans h₁)) (situationGradedHom E hqc U₁ x)
  have e3 := GradedRingHom.congr_fun (situationGradedHom_res E hqc U₂ U₁ hU) x
  simp only [GradedRingHom.comp_apply] at e1 e2 e3
  refine (Eq.trans ?_ e1).trans (e2.symm.trans ?_)
  · rfl
  · exact congrArg (Stacks.RelativeProj.Situation.gradedBaseChange (s := symSituation E)
      (s' := symSituation E') g (Stacks.RelativeProj.symmetricSituationPullbackHom g E E' hE) U₂ W₂
      h₂) e3.symm

end BaseChange

section Congr

open AlgebraicGeometry.ProjectiveSpectrum.Proj

variable {R R' : Type u} {σ τ : Type u} [CommRing R] [CommRing R'] [SetLike σ R]
  [AddSubgroupClass σ R] [SetLike τ R'] [AddSubgroupClass τ R'] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ]

/-- The localization of equal graded ring maps at a section gives the same value. -/
public theorem fibreMap_congr_hom {ψ ψ' : 𝒜 →+*ᵍ ℬ} (hψ : HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (hψ' : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ')
    (e : ψ = ψ') {n : ℤ} (Y : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : (twistingSheaf 𝒜 n).val.obj (op Y)) (y : ProjectiveSpectrum ℬ)
    (hy : ProjectiveSpectrum.comapFun ψ hψ y ∈ Y) (hy' : ProjectiveSpectrum.comapFun ψ' hψ' y ∈ Y) :
    Stacks.ProjTwistComparison.fibreMap ψ hψ y (s.1 ⟨_, hy⟩) =
      Stacks.ProjTwistComparison.fibreMap ψ' hψ' y (s.1 ⟨_, hy'⟩) := by
  subst e
  rfl

end Congr

section Theta

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjTwists
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.TwistExistence

variable {X X' : Scheme.{u}} (g : X' ⟶ X) (E : X.Modules) [E.IsQuasicoherent]
  (hqc : IsQuasicoherentPieces E) (E' : X'.Modules) [E'.IsQuasicoherent]
  (hqc' : IsQuasicoherentPieces E') (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (D : TwistData (schemeSheafGradedAlgebra E hqc))
  (D' : TwistData (schemeSheafGradedAlgebra E' hqc'))

/-- The chart of `𝐏(E')` over an affine open `W'` lying over an affine open `U`, followed by the
morphism of projective bundles, through the chart of `𝐏(E)` over `U`. -/
public abbrev chartBC (U : X.Opens) (hU : IsAffineOpen U) (W : X'.Opens) (hW : IsAffineOpen W)
    (h : W ≤ g ⁻¹ᵁ U) :
    AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra E' hqc').grading W) ⟶
      AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra E hqc).grading U) :=
  Proj.map (bundleChartRingHom g E hqc E' hqc' hE U W hW h)
    (irrelevant_le_bundleChartRingHom g E hqc E' hqc' hE U hU W hW h)

/-- The pointwise localization of the base-change map of graded rings of sections on degree-`n`
fractions. -/
public abbrev twistBC (U : X.Opens) (hU : IsAffineOpen U) (W : X'.Opens) (hW : IsAffineOpen W)
    (h : W ≤ g ⁻¹ᵁ U) (n : ℤ) :
    twistingSheaf ((schemeSheafGradedAlgebra E hqc).grading U) n ⟶
      (Scheme.Modules.pushforward (chartBC g E hqc E' hqc' hE U hU W hW h)).obj
        (twistingSheaf ((schemeSheafGradedAlgebra E' hqc').grading W) n) :=
  Stacks.ProjTwistComparison.pushforwardTwistMap (bundleChartRingHom g E hqc E' hqc' hE U W hW h)
    (irrelevant_le_bundleChartRingHom g E hqc E' hqc' hE U hU W hW h) n

/-- **The local comparison of the twists**, over a pair of affine opens `W' ⊆ g⁻¹U`: the chart
identification of `D` over `U`, then the pointwise localization of the base-change map of graded
rings of sections, as a morphism `𝒪_{𝐏(E)}(n) ⟶ b_* (chart_{W'})_* 𝒪_{Proj Γ(W', Sym E')}(n)`. -/
public def thetaChart (U : X.Opens) (hU : IsAffineOpen U) (W : X'.Opens) (hW : IsAffineOpen W)
    (h : W ≤ g ⁻¹ᵁ U) (n : ℤ) :
    D.algebra.piece n ⟶ (Scheme.Modules.pushforward (bundleBaseChange g E hqc E' hqc' hE)).obj
      ((Scheme.Modules.pushforward
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart W hW)).obj
        (twistingSheaf ((schemeSheafGradedAlgebra E' hqc').grading W) n)) :=
  chartPush D U hU n ≫
    (Scheme.Modules.pushforward ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).map
      (twistBC g E hqc E' hqc' hE U hU W hW h n) ≫
    (Scheme.Modules.pushforwardComp (chartBC g E hqc E' hqc' hE U hU W hW h)
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU)).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr
      (chart_comp_bundleBaseChange g E hqc E' hqc' hE U hU W hW h).symm).hom.app _ ≫
    (Scheme.Modules.pushforwardComp ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart W hW)
      (bundleBaseChange g E hqc E' hqc' hE)).inv.app _

/-- **The local value of the comparison**: a section of `𝒪_{𝐏(E)}(n)` over an open inside the
inverse image of `U` gives a section of `𝒪_{𝐏(E')}(n)` over the part of its inverse image under
`b` lying over `W'`. -/
public def thetaLoc (U : X.Opens) (hU : IsAffineOpen U) (W : X'.Opens) (hW : IsAffineOpen W)
    (h : W ≤ g ⁻¹ᵁ U) (n : ℤ) (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (x : (D.algebra.piece n).val.obj (op V)) :
    (D'.algebra.piece n).val.obj (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ W)) :=
  ((chartLoc D' W hW n).app _ inf_le_right).symm
    ((ChartTransNonNested.pushforwardVal
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart W hW)
        (twistingSheaf ((schemeSheafGradedAlgebra E' hqc').grading W) n)).map
      (homOfLE inf_le_left).op ((thetaChart g E hqc E' hqc' hE D U hU W hW h n).val.app (op V) x))

/-- The local value is characterized by its image under the chart identification of `D'`. -/
public theorem chartPush_thetaLoc (U : X.Opens) (hU : IsAffineOpen U) (W : X'.Opens)
    (hW : IsAffineOpen W) (h : W ≤ g ⁻¹ᵁ U) (n : ℤ)
    (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (x : (D.algebra.piece n).val.obj (op V)) :
    (chartPush D' W hW n).val.app (op _) (thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V x) =
      (ChartTransNonNested.pushforwardVal
        ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart W hW)
        (twistingSheaf ((schemeSheafGradedAlgebra E' hqc').grading W) n)).map
      (homOfLE inf_le_left).op ((thetaChart g E hqc E' hqc' hE D U hU W hW h n).val.app (op V) x) :=
  (chartLoc_app D' W hW n _ inf_le_right _).symm.trans
    (LinearEquiv.apply_symm_apply ((chartLoc D' W hW n).app _ inf_le_right) _)

/-- The point below a point of a chart of `𝐏(E')` lies in the chart preimage of `V` when the
point lies in the preimage of `V` under the chart followed by `b`. -/
public theorem chartBC_mem (U : X.Opens) (hU : IsAffineOpen U) (W : X'.Opens) (hW : IsAffineOpen W)
    (h : W ≤ g ⁻¹ᵁ U) (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (y : AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra E' hqc').grading W))
    (hy : y ∈ (relativeProj (schemeSheafGradedAlgebra E' hqc')).chart W hW ⁻¹ᵁ
      (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V)) :
    ProjectiveSpectrum.comapFun (bundleChartRingHom g E hqc E' hqc' hE U W hW h)
        (irrelevant_le_bundleChartRingHom g E hqc E' hqc' hE U hU W hW h) y ∈
      (relativeProj (schemeSheafGradedAlgebra E hqc)).chart U hU ⁻¹ᵁ V := by
  have hy'' : y ∈ ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart W hW ≫
      bundleBaseChange g E hqc E' hqc' hE) ⁻¹ᵁ V := hy
  rw [chart_comp_bundleBaseChange g E hqc E' hqc' hE U hU W hW h] at hy''
  exact hy''

/-- **The local comparison of the twists, pointwise**: the localization of the base-change map
at the point below. -/
public theorem thetaChart_apply (U : X.Opens) (hU : IsAffineOpen U) (W : X'.Opens)
    (hW : IsAffineOpen W) (h : W ≤ g ⁻¹ᵁ U) (n : ℤ)
    (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (x : (D.algebra.piece n).val.obj (op V))
    (y : ((relativeProj (schemeSheafGradedAlgebra E' hqc')).chart W hW ⁻¹ᵁ
      (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V) :
        (AlgebraicGeometry.Proj ((schemeSheafGradedAlgebra E' hqc').grading W)).Opens)) :
    ((thetaChart g E hqc E' hqc' hE D U hU W hW h n).val.app (op V) x).1 y =
      Stacks.ProjTwistComparison.fibreMap (bundleChartRingHom g E hqc E' hqc' hE U W hW h)
        (irrelevant_le_bundleChartRingHom g E hqc E' hqc' hE U hU W hW h) y.1
        (((chartPush D U hU n).val.app (op V) x).1
          ⟨_, chartBC_mem g E hqc E' hqc' hE U hU W hW h V y.1 y.2⟩) :=
  rfl

/-- **The local values of the comparison agree on overlaps**, for nested pairs of affine opens. -/
public theorem thetaLoc_res {U₁ U₂ : X.Opens} (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (hU : U₂ ≤ U₁) {W₁ W₂ : X'.Opens} (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (hW : W₂ ≤ W₁) (h₁ : W₁ ≤ g ⁻¹ᵁ U₁) (h₂ : W₂ ≤ g ⁻¹ᵁ U₂) (n : ℤ)
    (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (x : (D.algebra.piece n).val.obj (op V)) :
    (D'.algebra.piece n).val.map (homOfLE (inf_le_inf_left _ (fun _ hz => hW hz))).op
        (thetaLoc g E hqc E' hqc' hE D D' U₁ hU₁ W₁ hW₁ h₁ n V x) =
      thetaLoc g E hqc E' hqc' hE D D' U₂ hU₂ W₂ hW₂ h₂ n V x := by
  refine (bijective_chartPush D' W₂ hW₂ n _ inf_le_right).1 ?_
  refine Subtype.ext (funext fun z => ?_)
  refine (chartPush_apply_of_le _ hW hW₂ hW₁ D' n _ _ z).trans ?_
  refine Eq.trans ?_ (congrArg (fun s => s.1 z)
    (chartPush_thetaLoc g E hqc E' hqc' hE D D' U₂ hU₂ W₂ hW₂ h₂ n V x).symm)
  have e1 := PresheafOfModules.naturality_apply (chartPush D' W₁ hW₁ n).val
    (homOfLE (inf_le_inf_left _ (fun _ hz => hW hz) :
      bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
        (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ W₂ ≤
      bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
        (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ W₁)).op
    (thetaLoc g E hqc E' hqc' hE D D' U₁ hU₁ W₁ hW₁ h₁ n V x)
  rw [e1, chartPush_thetaLoc]
  refine (congrArg _
    (thetaChart_apply g E hqc E' hqc' hE D U₁ hU₁ W₁ hW₁ h₁ n V x ⟨_, ?_⟩)).trans ?_
  refine (Stacks.ProjTwistComparison.fibreMap_comp _ _ _ _
    (HomogeneousIdeal.irrelevant_le_map_comp
      (irrelevant_le_bundleChartRingHom g E hqc E' hqc' hE U₁ hU₁ W₁ hW₁ h₁)
      (irrelevant_le_res _ hW hW₂ hW₁)) z.1 _).symm.trans ?_
  refine Eq.trans ?_ (thetaChart_apply g E hqc E' hqc' hE D U₂ hU₂ W₂ hW₂ h₂ n V x
    ⟨z.1, ?_⟩).symm
  rotate_left
  · exact z.2.1
  refine Eq.trans ?_ (congrArg _ (chartPush_apply_of_le _ hU hU₂ hU₁ D n V x ⟨_, ?_⟩).symm)
  rotate_left
  · exact chartBC_mem g E hqc E' hqc' hE U₂ hU₂ W₂ hW₂ h₂ V z.1 z.2.1
  refine Eq.trans ?_ (Stacks.ProjTwistComparison.fibreMap_comp _ _ _ _
    (HomogeneousIdeal.irrelevant_le_map_comp (irrelevant_le_res _ hU hU₂ hU₁)
      (irrelevant_le_bundleChartRingHom g E hqc E' hqc' hE U₂ hU₂ W₂ hW₂ h₂)) z.1 _)
  exact fibreMap_congr_hom _ _ (res_comp_bundleChartRingHom g E hqc E' hqc' hE hU hW hW₁ hW₂ h₁ h₂)
    _ _ _ _ _

/-- The affine opens of `X'` lying over an affine open `U` of `X`. -/
public abbrev OverIdx (U : X.Opens) : Type u := {W : X'.affineOpens // W.1 ≤ g ⁻¹ᵁ U}

/-- The parts of the inverse image of an open over the affine opens of `X'` lying over `U` cover
it. -/
public theorem le_iSup_overIdx (U : X.Opens)
    (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
    (hV : V ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U) :
    bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ≤ ⨆ i : OverIdx g U,
      bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
        (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ i.1.1 := by
  intro p hp
  have hg : (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase.base p ∈ g ⁻¹ᵁ U := by
    have h1 : p ∈ (bundleBaseChange g E hqc E' hqc' hE ≫
        (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase) ⁻¹ᵁ U := hV hp
    rw [bundleBaseChange_toBase] at h1
    exact h1
  obtain ⟨W, hW, hpW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens hg
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWU⟩, hp, hpW⟩

variable (U : X.Opens) (hU : IsAffineOpen U) (n : ℤ)
  (V : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens)
  (hV : V ≤ (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U)
  (x : (D.algebra.piece n).val.obj (op V))

/-- The local values over the affine opens lying over `U`. -/
public abbrev thetaLocFam (i : OverIdx g U) :
    (D'.algebra.piece n).val.obj (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ i.1.1)) :=
  thetaLoc g E hqc E' hqc' hE D D' U hU i.1.1 i.1.2 i.2 n V x

/-- The local values over the affine opens lying over `U` agree on overlaps. -/
public theorem thetaLocFam_compat (k l : OverIdx g U) :
    (D'.algebra.piece n).val.resLE inf_le_left (thetaLocFam g E hqc E' hqc' hE D D' U hU n V x k) =
      (D'.algebra.piece n).val.resLE inf_le_right
        (thetaLocFam g E hqc E' hqc' hE D D' U hU n V x l) := by
  let O := (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ k.1.1) ⊓
      (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ l.1.1)
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (D'.algebra.piece n).isSheaf
    (fun m : {m : OverIdx g U // m.1.1 ≤ k.1.1 ⊓ l.1.1} => O ⊓
      (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ m.1.1.1)
    (fun _ => inf_le_left) ?_ fun m => ?_
  · intro p hp
    have hp' := hp
    obtain ⟨⟨hpV, hpk⟩, -, hpl⟩ := hp'
    obtain ⟨W, hW, hpW, hWkl⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens
      (show (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase.base p ∈ k.1.1 ⊓ l.1.1 from
        ⟨hpk, hpl⟩)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨⟨⟨⟨W, hW⟩, hWkl.trans (inf_le_left.trans k.2)⟩, hWkl⟩, hp, hpW⟩
  · have key : ∀ (j : OverIdx g U) (hmj : m.1.1.1 ≤ j.1.1) (hj : O ⊓
        (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ m.1.1.1 ≤
        bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
          (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ j.1.1),
        (D'.algebra.piece n).val.resLE hj (thetaLocFam g E hqc E' hqc' hE D D' U hU n V x j) =
          (D'.algebra.piece n).val.resLE
            (inf_le_inf_right _ (inf_le_left.trans inf_le_left))
            (thetaLoc g E hqc E' hqc' hE D D' U hU m.1.1.1 m.1.1.2 m.1.2 n V x) := fun j hmj hj =>
      ((D'.algebra.piece n).val.resLE_resLE (inf_le_inf_left _ fun _ hz => hmj hz) _ _).symm.trans
        (congrArg _ (thetaLoc_res g E hqc E' hqc' hE D D' hU hU le_rfl j.1.2 m.1.1.2 hmj j.2
          m.1.2 n V x))
    rw [(D'.algebra.piece n).val.resLE_resLE, (D'.algebra.piece n).val.resLE_resLE]
    exact (key k (m.2.trans inf_le_left) _).trans (key l (m.2.trans inf_le_right) _).symm

omit hV in
/-- The local value is additive. -/
public theorem thetaLoc_add (W : X'.Opens) (hW : IsAffineOpen W) (h : W ≤ g ⁻¹ᵁ U)
    (x y : (D.algebra.piece n).val.obj (op V)) :
    thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V (x + y) =
      thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V x +
        thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V y := by
  refine (bijective_chartPush D' W hW n _ inf_le_right).1 ?_
  rw [map_add, chartPush_thetaLoc, chartPush_thetaLoc, chartPush_thetaLoc, map_add]
  exact map_add _ _ _

/-- **The comparison over the inverse image of `U`**, glued from the local values over the affine
opens of `X'` lying over `U`. -/
public def thetaGlue :
    (D'.algebra.piece n).val.obj (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V)) :=
  (TopCat.Sheaf.existsUnique_gluing_of_isSheafPresheaf (D'.algebra.piece n).isSheaf _
    (fun _ => inf_le_left) (le_iSup_overIdx g E hqc E' hqc' hE U V hV)
    (thetaLocFam g E hqc E' hqc' hE D D' U hU n V x)
    (thetaLocFam_compat g E hqc E' hqc' hE D D' U hU n V x)).choose

/-- The glued comparison restricts to the local values. -/
public theorem resLE_thetaGlue (i : OverIdx g U) :
    (D'.algebra.piece n).val.resLE inf_le_left (thetaGlue g E hqc E' hqc' hE D D' U hU n V hV x) =
      thetaLocFam g E hqc E' hqc' hE D D' U hU n V x i :=
  (TopCat.Sheaf.existsUnique_gluing_of_isSheafPresheaf (D'.algebra.piece n).isSheaf _
    (fun _ => inf_le_left) (le_iSup_overIdx g E hqc E' hqc' hE U V hV)
    (thetaLocFam g E hqc E' hqc' hE D D' U hU n V x)
    (thetaLocFam_compat g E hqc E' hqc' hE D D' U hU n V x)).choose_spec.1 i

/-- The glued comparison is determined by its restrictions. -/
public theorem eq_thetaGlue
    (y : (D'.algebra.piece n).val.obj (op (bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V)))
    (hy : ∀ i : OverIdx g U, (D'.algebra.piece n).val.resLE inf_le_left y =
      thetaLocFam g E hqc E' hqc' hE D D' U hU n V x i) :
    y = thetaGlue g E hqc E' hqc' hE D D' U hU n V hV x :=
  TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (D'.algebra.piece n).isSheaf _
    (fun _ => inf_le_left) (le_iSup_overIdx g E hqc E' hqc' hE U V hV) fun i =>
    (hy i).trans (resLE_thetaGlue g E hqc E' hqc' hE D D' U hU n V hV x i).symm

omit hV in
/-- The local value is natural in the open. -/
public theorem thetaLoc_resLE (W : X'.Opens) (hW : IsAffineOpen W) (h : W ≤ g ⁻¹ᵁ U)
    {V₁ : (relativeProj (schemeSheafGradedAlgebra E hqc)).scheme.Opens} (hV₁ : V₁ ≤ V)
    (x : (D.algebra.piece n).val.obj (op V)) :
    thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V₁ ((D.algebra.piece n).val.resLE hV₁ x) =
      (D'.algebra.piece n).val.resLE (inf_le_inf_right _ (fun _ hz => hV₁ hz))
        (thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V x) := by
  refine (bijective_chartPush D' W hW n _ inf_le_right).1 ?_
  have e1 := chartPush_thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V₁
    ((D.algebra.piece n).val.resLE hV₁ x)
  have e2 := chartPush_thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V x
  have e3 := PresheafOfModules.naturality_apply (chartPush D' W hW n).val
    (homOfLE (inf_le_inf_right _ (fun _ hz => hV₁ hz) :
      bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V₁ ⊓
        (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ W ≤
      bundleBaseChange g E hqc E' hqc' hE ⁻¹ᵁ V ⊓
        (relativeProj (schemeSheafGradedAlgebra E' hqc')).toBase ⁻¹ᵁ W)).op
    (thetaLoc g E hqc E' hqc' hE D D' U hU W hW h n V x)
  have e4 := PresheafOfModules.naturality_apply (thetaChart g E hqc E' hqc' hE D U hU W hW h n).val
    (homOfLE hV₁).op x
  refine Subtype.ext (funext fun z => ?_)
  refine (congrFun (congrArg Subtype.val e1) z).trans ?_
  refine Eq.trans ?_ (congrFun (congrArg Subtype.val e3) z).symm
  refine Eq.trans ?_ (congrFun (congrArg Subtype.val e2) ⟨z.1, hV₁ z.2.1, z.2.2⟩).symm
  exact congrFun (congrArg Subtype.val e4) ⟨z.1, z.2.1⟩

end Theta

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end
