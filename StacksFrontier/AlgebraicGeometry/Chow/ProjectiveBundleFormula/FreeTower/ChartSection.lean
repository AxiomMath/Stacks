module

public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Epi
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.ProjMapTwist

/-!
# The homogeneous-section map of a twist datum on a chart

Let `D` be a twist datum of a graded algebra `A` on a scheme `S`, and let `c` be the
projective-spectrum chart over an affine open `W` of `S`. The chart identification of `D`
carries the pullback along `c` of the global section `ψ₁(T)` of `𝒪(1)`, for `T` a global section
of `A₁`, to the section of the absolute twist `𝒪(1)` attached to the restriction of `T` to `W`.

## Main results

* `Stacks.Chow.FreeTower.chartPullbackIso`: the pullback of `𝒪(1)` along the chart, identified
  with the absolute twist.
* `Stacks.Chow.FreeTower.chartPullbackIso_hom_psi`: the identification on `ψ₁(T)`.
* `Stacks.Chow.FreeTower.isTautologicalOn_chart_of_map`: if the chart followed by a morphism to
  projective space is the map induced by a graded map out of the polynomial ring sending each
  variable to the restriction of a section `Tᵢ` of `A₁`, then the pullback of `(𝒪(1), ψ₁(Tᵢ))`
  along the chart is tautological for that morphism.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists Stacks.AlgebraicGeometry.ProjTwistSections
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.Chow.FreeTower

/-- Pulling back a global section along two equal morphisms gives the same section, through
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`. -/
theorem pullbackGlobalSections_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (F : Y.Modules) (t : Γ(F, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr e).hom.app F) ⊤
      (pullbackGlobalSections f F t) = pullbackGlobalSections g F t := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

/-- An isomorphism of `𝒪_X`-modules undoes its inverse on sections. -/
theorem app_hom_app_inv {X : Scheme.{u}} {M N : X.Modules} (β : M ≅ N) (V : X.Opens)
    (x : Γ(N, V)) :
    Scheme.Modules.Hom.app β.hom V (Scheme.Modules.Hom.app β.inv V x) = x :=
  app_inv_app_hom β.symm V x

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : TwistData A)
  (W : S.Opens) (hW : IsAffineOpen W) [IsOpenImmersion ((relativeProj A).chart W hW)]

/-- The pullback of the degree-one twist along the chart over `W`, identified with the absolute
twist `𝒪(1)` of `Proj Γ(W, A)`. -/
def chartPullbackIso :
    (Scheme.Modules.pullback ((relativeProj A).chart W hW)).obj (D.algebra.piece ((1 : ℕ) : ℤ)) ≅
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading W) ((1 : ℕ) : ℤ) :=
  ((Scheme.Modules.restrictFunctorIsoPullback ((relativeProj A).chart W hW)).app _).symm ≪≫
    D.chartData.chartIso W hW ((1 : ℕ) : ℤ)

/-- The identification `chartPullbackIso` carries the pullback along the chart of the global
section `ψ₁(T)` of `𝒪(1)` to the degree-one section of the absolute twist attached to the
restriction of `T` to `W`. -/
theorem chartPullbackIso_hom_psi (T : A.sectionPieces ⊤ 1) :
    Scheme.Modules.Hom.app (chartPullbackIso D W hW).hom ⊤
        (pullbackGlobalSections ((relativeProj A).chart W hW) (D.algebra.piece ((1 : ℕ) : ℤ))
          ((D.ψ 1).val.app (op ⊤) T)) =
      degreeSection (A.grading W) 1
        ⟨DirectSum.of (A.sectionPieces W) 1 (A.resPiece (le_top : W ≤ ⊤) 1 T),
          A.of_mem_grading W _⟩ := by
  set c := (relativeProj A).chart W hW
  set L : (relativeProj A).scheme.Modules := D.algebra.piece ((1 : ℕ) : ℤ)
  set a := A.resPiece (le_top : W ≤ ⊤) 1 T
  have h₁ : Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app L) ⊤
      (pullbackGlobalSections c L ((D.ψ 1).val.app (op ⊤) T)) =
        L.val.map (homOfLE (c.image_preimage_le ⊤)).op ((D.ψ 1).val.app (op ⊤) T) := by
    refine (congrArg (CategoryTheory.ConcreteCategory.hom (Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app L) ⊤))
      (pullbackGlobalSections_eq_unitSection c L _)).trans ?_
    exact Scheme.Modules.restrictFunctorIsoPullback_inv_unit c L ⊤ _
  have hnat : (D.ψ 1).val.app (op W) a =
      L.val.map (homOfLE (le_top : (relativeProj A).toBase ⁻¹ᵁ W ≤ ⊤)).op
        ((D.ψ 1).val.app (op ⊤) T) :=
    PresheafOfModules.naturality_apply (D.ψ 1).val (homOfLE (le_top : W ≤ ⊤)).op T
  have heq := Stacks.AlgebraicGeometry.RelativeProjDegreeOne.map_eqRec (M := L)
    (D.chartData.chart_range W hW) ((D.ψ 1).val.app (op W) a) (le_refl (c ''ᵁ ⊤))
    (D.chartData.chart_range W hW).le
  have hid : L.presheaf.map (homOfLE (le_refl (c ''ᵁ ⊤))).op = 𝟙 _ := by
    rw [show (homOfLE (le_refl (c ''ᵁ ⊤))).op = 𝟙 _ from rfl]
    exact L.presheaf.map_id _
  have hres : L.val.map (homOfLE (c.image_preimage_le ⊤)).op ((D.ψ 1).val.app (op ⊤) T) =
      ((D.chartData.chart_range W hW).symm ▸ (D.ψ 1).val.app (op W) a : Γ(L, c ''ᵁ ⊤)) := by
    refine Eq.trans ?_ (((CategoryTheory.ConcreteCategory.congr_hom hid _).trans
      (CategoryTheory.id_apply _)).symm.trans heq).symm
    rw [hnat]
    have hc := L.presheaf.map_comp (homOfLE (le_top : (relativeProj A).toBase ⁻¹ᵁ W ≤ ⊤)).op
      (homOfLE (D.chartData.chart_range W hW).le).op
    exact (CategoryTheory.ConcreteCategory.congr_hom hc ((D.ψ 1).val.app (op ⊤) T)).trans
      (CategoryTheory.ConcreteCategory.comp_apply _ _ _)
  have hψ := D.ψ_chart W hW 1 a
  show Scheme.Modules.Hom.app (D.chartData.chartIso W hW ((1 : ℕ) : ℤ)).hom ⊤
      (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app L) ⊤
        (pullbackGlobalSections c L ((D.ψ 1).val.app (op ⊤) T))) = _
  rw [h₁, hres]
  refine (congrArg (CategoryTheory.ConcreteCategory.hom (Scheme.Modules.Hom.app
    (D.chartData.chartIso W hW ((1 : ℕ) : ℤ)).hom ⊤)) hψ.symm).trans ?_
  exact Stacks.AlgebraicGeometry.RelativeProjDegreeOne.iso_inv_hom_app
    (D.chartData.chartIso W hW ((1 : ℕ) : ℤ)).symm (op ⊤) _


open Stacks.SectionsToProjectiveSpace Stacks.TwistPullbackPinned Stacks.AmpleProjectiveImmersion

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If `φ : ℤ[T₀, …, Tₘ] → Γ(W, A)` sends `Tᵢ` to the restriction of `Tᵢ' ∈ Γ(S, A₁)`, and the
chart followed by `g : Proj_S(A) ⟶ ℙᵐ_ℤ` is `Proj.map φ`, then the pullback of `(𝒪(1), ψ₁(Tᵢ'))`
along the chart is the tautological pair of the chart followed by `g`. -/
theorem isTautologicalOn_chart_of_map {m : ℕ}
    [Stacks.Ample.IsInvertibleModule (relativeProj A).scheme (D.algebra.piece ((1 : ℕ) : ℤ))]
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (A.grading W)).presheaf
      (AlgebraicGeometry.Proj (A.grading W)).ringCatSheaf.2
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading W) ((1 : ℕ) : ℤ))]
    (φ : coordGrading.{u} m →+*ᵍ A.grading W)
    (hφ : HomogeneousIdeal.irrelevant (A.grading W) ≤
      (HomogeneousIdeal.irrelevant (coordGrading.{u} m)).map φ)
    (g : (relativeProj A).scheme ⟶ AlgebraicGeometry.projectiveSpaceAtUniverse.{u} m)
    (hcg : projMap φ hφ = (relativeProj A).chart W hW ≫ g)
    (T : Fin (m + 1) → A.sectionPieces ⊤ 1)
    (hT : ∀ i, DirectSum.of (A.sectionPieces W) 1 (A.resPiece (le_top : W ≤ ⊤) 1 (T i)) =
      φ (MvPolynomial.X i)) :
    IsTautologicalOn (D.algebra.piece ((1 : ℕ) : ℤ)) (fun i => (D.ψ 1).val.app (op ⊤) (T i)) g
      ((relativeProj A).chart W hW) := by
  refine ⟨chartPullbackIso D W hW ≪≫ (projMapTwistIso φ hφ).symm ≪≫
    (Scheme.Modules.pullbackCongr hcg).app _, fun i => ?_⟩
  show Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hcg).hom.app _) ⊤
    (Scheme.Modules.Hom.app (projMapTwistIso φ hφ).inv ⊤
      (Scheme.Modules.Hom.app (chartPullbackIso D W hW).hom ⊤
        (pullbackGlobalSections ((relativeProj A).chart W hW) (D.algebra.piece ((1 : ℕ) : ℤ))
          ((D.ψ 1).val.app (op ⊤) (T i))))) = _
  rw [chartPullbackIso_hom_psi]
  have hdeg : (⟨DirectSum.of (A.sectionPieces W) 1 (A.resPiece (le_top : W ≤ ⊤) 1 (T i)),
      A.of_mem_grading W _⟩ : A.grading W 1) =
      ⟨φ (MvPolynomial.X i), φ.map_mem (X_mem_coordGrading_one i)⟩ := Subtype.ext (hT i)
  rw [hdeg, ← projMapTwistIso_pullbackCoordSection φ hφ i]
  refine (congrArg (CategoryTheory.ConcreteCategory.hom (Scheme.Modules.Hom.app
    ((Scheme.Modules.pullbackCongr hcg).hom.app (twistingSheafAtUniverse.{u} m)) ⊤))
    (app_inv_app_hom (projMapTwistIso φ hφ) ⊤ _)).trans ?_
  exact pullbackGlobalSections_congr hcg _ _

end Stacks.Chow.FreeTower

end
