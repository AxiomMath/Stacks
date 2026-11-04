module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenus
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedHigherDirectImageAssociatedModule

/-!
# Condition (2) of Stacks 0E6K: a proper scheme of dimension at most one over a field

Stacks 0E6K characterizes the open and closed substacks `Curves_g ⊂ Curves^{h0,1}` by condition (2)
on a scheme `X` proper over a field `k` with `dim(X) ≤ 1`: the classifying morphism
`Spec(k) → Curves` factors through `Curves_g` exactly when `dim(X) = 1`, `k = H⁰(X, 𝒪_X)` and the
genus of `X` is `g`. This file states it for the family of curves of such a scheme, given that
`f_*𝒪_X = 𝒪_S` holds universally whenever it holds on the fibres over fields.

## Main results

* `isFiniteLocallyFreeOfRank_firstDirectImage_curveFamilyOverFieldOfProper_genus`: for a proper
  morphism `p : T → Spec k` of schemes of the site with `dim(T) ≤ 1`, the module `R¹f_*𝒪_X` of
  the associated family of curves is finite locally free of rank the genus of `T` on the small
  étale site of `Spec k`.
* `CurveFamily.isGenusCurveFamily_curveFamilyOfSchemeMorphism_iff`: condition (2)(b) of
  Stacks 0E6K.

## References

* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

section Comparison071N

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **`R¹f_*𝒪_X` of a proper scheme over a field is locally free of rank the genus.**  For a
proper morphism `p : T ⟶ W` of the site with `W = Spec k` and `dim(T) ≤ 1`, the first direct image
of the family of curves `AlgebraicGeometry.curveFamilyOverFieldOfProper` is finite locally free of
rank the genus of `T`. -/
theorem isFiniteLocallyFreeOfRank_firstDirectImage_curveFamilyOverFieldOfProper_genus
    (k : Type u) [Field k] {T W : BigFppfOver B integerBase hZ} (p : T ⟶ W)
    (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map p))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    RingedSite.IsFiniteLocallyFreeOfRank
      (Space.smallEtaleRingedSite B integerBase hZ
        (schemeSpace (curveFamilyOverFieldOfProper B hZ p k hW hproper hdim).base).1
        (schemeSpace (curveFamilyOverFieldOfProper B hZ p k hW hproper hdim).base).2)
      ((curveFamilyOverFieldOfProper B hZ p k hW hproper hdim).firstDirectImage B hZ)
      (genus ((BigFppfOver.toScheme B integerBase hZ).map p ≫ eqToHom hW)) :=
  isFiniteLocallyFreeOfRank_firstHigherDirectImage_curveFamilyOfSchemeMorphism_genus_of
    (fun g' hqc' hsep' F hF j =>
      Space.nonempty_rightDerived_modulePushforward_representedAssociatedModule_of_isSeparated
        B integerBase hZ g' hqc' hsep' F hF j)
    p _ hproper _ _ _ _ hdim k hW

end Comparison071N

namespace CurveFamily

section OverField

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable
    (hpush : ∀ X : CurveFamily B hZ, CurveFamily.HasBijectiveGlobalFunctionsOnFieldFibres B hZ X →
      HasUniversallyBijectiveGlobalFunctions B hZ X)
  {T W : BigFppfOver B integerBase hZ} (g : T ⟶ W)
  (k : Type u) [Field k]
  (hW : (BigFppfOver.toScheme B integerBase hZ).obj W = Spec (.of k))
  (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
  (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
  (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
  (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
  (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1)

include hpush hW in
/-- **Condition (2)(b) of Stacks 0E6K on a proper scheme over a field.**  For the family of
curves of a proper scheme `X = T` of dimension at most one over a field `k = W`: if `f_*𝒪 = 𝒪`
universally follows from the fibrewise condition (the hypothesis `hpush`), then `X` is in
`Curves_n` exactly when `H⁰(X, 𝒪_X) = k`, `dim(X) = 1` and the genus of `X` is `n`. -/
theorem isGenusCurveFamily_curveFamilyOfSchemeMorphism_iff (n : ℕ) :
    IsGenusCurveFamily B hZ n
        (curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp hqc hsep hqsep hdim) ↔
      (Function.Bijective ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW).appTop ∧
        topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) = 1) ∧
        genus ((BigFppfOver.toScheme B integerBase hZ).map g ≫ eqToHom hW) = n :=
  isGenusCurveFamily_curveFamilyOfSchemeMorphism_iff_of_rightDerivedComparison hpush g k hW hflat
    hproper hlfp hqc hsep hqsep hdim
    (fun g' hqc' hsep' F hF j =>
      Space.nonempty_rightDerived_modulePushforward_representedAssociatedModule_of_isSeparated
        B integerBase hZ g' hqc' hsep' F hF j) n

end OverField

end CurveFamily

end AlgebraicGeometry

end
