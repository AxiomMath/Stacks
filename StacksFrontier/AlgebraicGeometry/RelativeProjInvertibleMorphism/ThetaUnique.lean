module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaChartLaws
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistBasicOpenDecomposition

/-!
# Sections of the relative twists over a standard open of a chart

Over the chart of an affine open `V` of the base, the sections of `𝒪_{Proj_S(𝒜)}(n)` over the
image of a standard open `D₊(g)` are fractions `x / g^j`: `ψ(g^j) · t = ψ(x)` with `x ∈ 𝒜(V)`
homogeneous (`exists_psiU_mul_eq`), and multiplication by `ψ(g)^j` is injective on the sections of
`ℒ^{⊗ n}` over the corresponding open of `U(ψ)` (`psiVal_cancel`). Together these say that a
multiplicative family of maps reading `ψ` is determined on such an open, which is how the local
data of the relative `θ` of [Stacks, Tag 01O9] are shown to agree on overlaps.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- Multiplication by a nonvanishing global section is injective on local sections. -/
theorem localMul_cancel {Y : Scheme.{u}} (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]
    {k n : ℤ} (t : Γ(tensorPowerModule Y L k, ⊤)) {O : Y.Opens}
    (hO : O ≤ nonvanishingOpen Y (tensorPowerModule Y L k) t)
    (a b : Γ(tensorPowerModule Y L n, O))
    (h : Stacks.TensorPowerDivision.localMul L
        (Stacks.TensorPowerTrivialize.resTop (tensorPowerModule Y L k) t O) a =
      Stacks.TensorPowerDivision.localMul L
        (Stacks.TensorPowerTrivialize.resTop (tensorPowerModule Y L k) t O) b) : a = b := by
  refine (Stacks.TensorPowerDivision.bijective_intMulLinear L t hO n le_rfl).injective ?_
  rw [Stacks.TensorPowerDivision.intMulLinear_apply, Stacks.TensorPowerDivision.intMulLinear_apply,
    Stacks.TensorPowerDivision.intMulMap_app_localMul,
    Stacks.TensorPowerDivision.intMulMap_app_localMul]
  exact h

/-- A degreewise family commutes with transport along an equality of degrees. -/
theorem apply_cast {F G : ℤ → Type u} (φ : ∀ k, F k → G k) {k k' : ℤ} (h : k = k') (y : F k) :
    φ k' (cast (congrArg F h) y) = cast (congrArg G h) (φ k y) := by
  subst h
  rfl

namespace GradedPowerMap

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f)

/-- `ψ(a)` for `a ∈ 𝒜(V)` homogeneous of degree `d`, in the integer powers, restricted to the
target open over `W₁`. -/
abbrev psiVal (V : S.Opens) (hV : IsAffineOpen V) (d : ℕ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) (p : A.grading V d) :
    Γ(tensorPowerModule T P.L d, P.targetOpen V hV W₁) :=
  (tensorPowerModule T P.L d).presheaf.map (homOfLE (P.targetOpen_le V hV W₁)).op
    ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L d).hom.app (f ⁻¹ᵁ V)
      (P.value d V (A.componentEquiv V d p)))

/-- **Multiplication by `ψ(g)^j` is injective over `D₊(g)`.** -/
theorem psiVal_cancel (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ} {g : A.sectionRing V}
    (hg : g ∈ A.grading V e) (he : 0 < e) (j : ℕ) (n : ℤ)
    (a b : Γ(tensorPowerModule T P.L n,
      P.targetOpen V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
    (h : Stacks.TensorPowerDivision.localMul P.L
        (P.psiVal V hV (j * e) _ ⟨g ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg j⟩) a =
      Stacks.TensorPowerDivision.localMul P.L
        (P.psiVal V hV (j * e) _ ⟨g ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg j⟩) b) :
    a = b := by
  apply P.lam_injective V hV n _
  have h' := congrArg (P.lam V hV (((j * e : ℕ) : ℤ) + n) _) h
  rw [P.lam_localMul, P.lam_localMul, P.lam_value] at h'
  refine localMul_cancel (P.Lres V) _ ?_ _ _ h'
  refine Stacks.AlgebraicGeometry.ProjChartGradedDivision.le_nonvanishingOpen_intValue_pow
    (P.affineDatum V) hg ?_ j
  exact le_of_eq ((P.affineDatum V).chartOpen_eq hg he)

/-- The inverse chart identification is a left inverse of the forward one on sections. -/
private theorem chartIso_inv_app_hom_app (V : S.Opens) (hV : IsAffineOpen V) (d : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) (x) :
    ((twD A).chartData.chartIso V hV d).inv.app W₁
      (((twD A).chartData.chartIso V hV d).hom.app W₁ x) = x :=
  (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ W₁)
    ((twD A).chartData.chartIso V hV d).hom_inv_id) x).trans rfl

/-- The inverse chart identification carries the section of `p` to `ψ(p)`. -/
theorem chartIso_inv_degreeSection (V : S.Opens) (hV : IsAffineOpen V) (d : ℕ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens) (p : A.grading V d) :
    ((twD A).chartData.chartIso V hV d).inv.app W₁
        ((AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading V) d).val.map
          (homOfLE (le_top : W₁ ≤ ⊤)).op
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading V) d p)) =
      (Otw A d).presheaf.map (homOfLE (chart_image_le V hV W₁)).op
        (psiU A d V (A.componentEquiv V d p)) := by
  have hp : (⟨DirectSum.of (A.sectionPieces V) d (A.componentEquiv V d p),
      A.of_mem_grading V _⟩ : A.grading V d) = p := Subtype.ext (A.of_component V p)
  have h := (chartIso_hom_psiU V hV d W₁ (A.componentEquiv V d p)).trans
    (congrArg (fun q => (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading V)
      d).val.map (homOfLE (le_top : W₁ ≤ ⊤)).op
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading V) d q)) hp)
  exact ((chartIso_inv_app_hom_app V hV d W₁ _).symm.trans (congrArg _ h)).symm

/-- The inverse chart identification carries the canonical product to the product. -/
theorem chartIso_inv_mul (V : S.Opens) (hV : IsAffineOpen V) (i j : ℤ)
    (W₁ : (AlgebraicGeometry.Proj (A.grading V)).Opens)
    (a : (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading V) i).val.obj (op W₁))
    (b : (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading V) j).val.obj
      (op W₁)) :
    ((twD A).chartData.chartIso V hV (i + j)).inv.app W₁
        (((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra (A.grading V)).mul i j).app
          (op W₁) a b) =
      ((twD A).algebra.mul i j).app (op ((relativeProj A).chart V hV ''ᵁ W₁))
        (((twD A).chartData.chartIso V hV i).inv.app W₁ a)
        (((twD A).chartData.chartIso V hV j).inv.app W₁ b) :=
  (congrArg (((twD A).chartData.chartIso V hV (i + j)).inv.app W₁)
    (absoluteTwistProduct_eq_mul (A.grading V) i j W₁ a b).symm).trans
      ((twD A).chartIso_mul V hV i j W₁ a b)

/-- **Every section of `𝒪(n)` over a standard open of a chart is `x / g ^ j`**, read in the
relative twists: `ψ(g ^ j) · t = ψ(x)` there. -/
theorem exists_psiU_mul_eq (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ} {g : A.sectionRing V}
    (hg : g ∈ A.grading V e) (he : 0 < e) (n : ℤ)
    (t : Γ(Otw A n, (relativeProj A).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) :
    ∃ (j N : ℕ) (x : A.grading V N) (_ : ((j * e : ℕ) : ℤ) + n = (N : ℤ)),
      HEq (((twD A).algebra.mul ((j * e : ℕ) : ℤ) n).app
          (op ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
          ((Otw A (j * e : ℕ)).presheaf.map (homOfLE (chart_image_le V hV
            (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))).op
            (psiU A (j * e) V (A.componentEquiv V (j * e)
              ⟨g ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg j⟩))) t)
        ((Otw A N).presheaf.map (homOfLE (chart_image_le V hV
            (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))).op
          (psiU A N V (A.componentEquiv V N x))) := by
  obtain ⟨j, N, x, hN, hH⟩ :=
    Stacks.AlgebraicGeometry.ProjTwistBasicOpenDecomposition.exists_pow_mul_eq_degreeSection
      (A.grading V) hg he n (((twD A).chartData.chartIso V hV n).hom.app
        (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) t)
  refine ⟨j, N, x, hN, ?_⟩
  have ht := chartIso_inv_app_hom_app V hV n (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) t
  have hφ : ∀ {k k' : ℤ} (_ : k = k')
      {a : (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading V) k).val.obj
        (op (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))}
      {b : (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading V) k').val.obj
        (op (AlgebraicGeometry.Proj.basicOpen (A.grading V) g))}, HEq a b →
      HEq (((twD A).chartData.chartIso V hV k).inv.app
          (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) a)
        (((twD A).chartData.chartIso V hV k').inv.app
          (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) b) := by
    intro k k' hk a b hab
    subst hk
    exact heq_of_eq (congrArg _ (eq_of_heq hab))
  have h1 := hφ hN hH
  have h2 := chartIso_inv_mul V hV ((j * e : ℕ) : ℤ) n
    (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)
    ((AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (A.grading V)
        ((j * e : ℕ) : ℤ)).val.map
      (homOfLE (le_top : AlgebraicGeometry.Proj.basicOpen (A.grading V) g ≤ ⊤)).op
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (A.grading V) (j * e)
        ⟨g ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg j⟩))
    (((twD A).chartData.chartIso V hV n).hom.app
        (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) t)
  have h3 := chartIso_inv_degreeSection V hV (j * e)
    (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)
    ⟨g ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg j⟩
  have h4 := chartIso_inv_degreeSection V hV N
    (AlgebraicGeometry.Proj.basicOpen (A.grading V) g) x
  refine (heq_of_eq (h2.trans (congrArg₂ (fun a b => ((twD A).algebra.mul ((j * e : ℕ) : ℤ) n).app
    (op ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) a b)
    h3 ht))).symm.trans (h1.trans (heq_of_eq h4))

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
