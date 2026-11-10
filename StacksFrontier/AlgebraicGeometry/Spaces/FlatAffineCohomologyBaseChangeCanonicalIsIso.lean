module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeCanonicalPartTwo

/-!
# Flat base change of affine cohomology: the comparison map is an isomorphism

For a cartesian square

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

with `Y = Spec(A)` and `Y' = Spec(B)` affine, `g` flat, and `f` quasi-compact and
quasi-separated, the canonical comparison map
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap`
`H^i(X, 𝓕) ⊗_A B ⟶ H^i(X', 𝓕')`, the transpose of the pullback map on cohomology, is an
isomorphism.

## Main results

* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap_hom_tmul`: the
  comparison map sends `s ⊗ h` to `s` acting on the pullback map's value at `h`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso_hom_tmul`: the
  `A`-linear isomorphism `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso`
  sends `h ⊗ b` to the image of `b` in `Γ(Y', 𝒪_{Y'})` acting on the pullback map's value at `h`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap_chartTensorToSource`:
  the comparison map precomposed with
  `AlgebraicGeometry.Space.BaseChangeDiagram.chartTensorToSource` is that isomorphism.
* `AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap`: the
  comparison map is an isomorphism.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Cohomology.SiteModules
open Stacks.FlatDevissage
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.TensorByBaseModule hiding ringSheaf
open scoped ChangeOfRings

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] AlgebraicGeometry.RingedSite.globalSectionsCommRing

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace BaseChangeDiagram

variable (D : BaseChangeDiagram B S hS)

/-- The comparison map `H^i(X, 𝓕) ⊗_A B ⟶ H^i(X', 𝓕')` sends `s ⊗ h` to `s` acting on the
pullback map's value at `h`. -/
theorem affineCohomologyBaseChangeMap_hom_tmul (hg : IsFlat B S hS D.g.hom)
    (hY : IsAffineSpace B S hS D.Y.1) (hY' : IsAffineSpace B S hS D.Y'.1) (i : ℕ)
    (s : RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS D.Y'.1 D.Y'.2).O).obj)
    (h : have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
      ↥(D.affineCohomologyOverBase i)) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (D.affineCohomologyBaseChangeMap hg hY hY' i).hom
        (s ⊗ₜ[RingCat.sectionsSubring
            (ringSheaf (smallEtaleRingedSite B S hS D.Y.1 D.Y.2).O).obj,
          globalSectionsRingHomSite B S hS D.g] h) =
      s • (D.affineCohomologyPullbackOverBase hg hY hY' i).hom h :=
  rfl

variable (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom]
  (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom]

/-- The `A`-linear isomorphism `H^i(X, 𝓕) ⊗_A B ≅ H^i(X', 𝓕')` sends `h ⊗ b` to the image of
`b` in `Γ(Y', 𝒪_{Y'})` acting on the pullback map's value at `h`. -/
theorem affineCohomologyBaseChangeIso_hom_tmul (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ)
    (h : D.affineCohomologyOverBaseChart V₀ i) (b : baseChartRing B S hS D.Y' V₀') :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom.hom
        (h ⊗ₜ[baseChartRing B S hS D.Y V₀] b) =
      baseChartBaseRingHom B S hS D.Y' (isTerminal_of_isIso_chart B S hS D.Y' V₀') b •
        (D.affineCohomologyPullbackOverBase hg
          (isAffineSpace_of_isIso_chart B S hS D.Y V₀)
          (isAffineSpace_of_isIso_chart B S hS D.Y' V₀') i).hom h := by
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have := enoughInjectives_modules B S hS D.X.1 D.X.2
  have hY : IsAffineSpace B S hS D.Y.1 := isAffineSpace_of_isIso_chart B S hS D.Y V₀
  have hY' : IsAffineSpace B S hS D.Y'.1 := isAffineSpace_of_isIso_chart B S hS D.Y' V₀'
  refine Eq.trans ?_ (Eq.trans
    (D.affineCohomologyBaseChangeIso_hom_tmul_mul V₀ V₀' hZ hg hqc hqs i b 1 h) ?_)
  · exact congrArg (fun z : baseChartRing B S hS D.Y' V₀' =>
      (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom.hom
        (h ⊗ₜ[baseChartRing B S hS D.Y V₀] z)) (mul_one b).symm
  · exact congrArg (fun y : ↥(D.affineCohomologyTarget i) =>
      baseChartBaseRingHom B S hS D.Y' (isTerminal_of_isIso_chart B S hS D.Y' V₀') b • y)
      ((D.affineCohomologyBaseChangeIso_hom_tmul_one V₀ V₀' hZ hg hqc hqs i h).trans
        (D.affineCohomologyPullbackOverBase_hom_apply hg hY hY' i h).symm)

/-- The comparison map `H^i(X, 𝓕) ⊗_A B ⟶ H^i(X', 𝓕')`, precomposed with
`AlgebraicGeometry.Space.BaseChangeDiagram.chartTensorToSource`, is the `A`-linear isomorphism
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso`. -/
theorem affineCohomologyBaseChangeMap_chartTensorToSource (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ)
    (z : have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
      ↥((tensorLeftFunctor.{u, u + 1, u} (D.affineCohomologyOverBaseChart V₀ i)).obj
        (D.baseModule V₀ V₀'))) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (D.affineCohomologyBaseChangeMap hg
          (isAffineSpace_of_isIso_chart B S hS D.Y V₀)
          (isAffineSpace_of_isIso_chart B S hS D.Y' V₀') i).hom
        (D.chartTensorToSource V₀ V₀' i z) =
      (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom.hom z := by
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have := enoughInjectives_modules B S hS D.X.1 D.X.2
  have hY : IsAffineSpace B S hS D.Y.1 := isAffineSpace_of_isIso_chart B S hS D.Y V₀
  have hY' : IsAffineSpace B S hS D.Y'.1 := isAffineSpace_of_isIso_chart B S hS D.Y' V₀'
  refine TensorProduct.inductionOn (motive := fun z =>
    (D.affineCohomologyBaseChangeMap hg hY hY' i).hom (D.chartTensorToSource V₀ V₀' i z) =
      (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom.hom z) z ?_ ?_
  · intro h b
    refine Eq.trans (congrArg (D.affineCohomologyBaseChangeMap hg hY hY' i).hom
      ((D.chartTensorToSource_tmul V₀ V₀' i h b).trans
        (D.smul_affineCohomologySourceUnit i
          (baseChartBaseRingHom B S hS D.Y'
            (isTerminal_of_isIso_chart B S hS D.Y' V₀') b) h))) ?_
    exact (D.affineCohomologyBaseChangeMap_hom_tmul hg hY hY' i _ h).trans
      (D.affineCohomologyBaseChangeIso_hom_tmul V₀ V₀' hZ hg hqc hqs i h b).symm
  · intro z₁ z₂ h₁ h₂
    refine Eq.trans (congrArg (D.affineCohomologyBaseChangeMap hg hY hY' i).hom
      (map_add (D.chartTensorToSource V₀ V₀' i) z₁ z₂)) ?_
    exact (map_add _ _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans (map_add _ _ _).symm)

/-- For a cartesian square with affine bases `Y = Spec(A)` and `Y' = Spec(B)` presented by the
charts `V₀` and `V₀'`, `g` flat and `f` quasi-compact and quasi-separated, the comparison map
`H^i(X, 𝓕) ⊗_A B ⟶ H^i(X', 𝓕')` is an isomorphism in every degree. -/
theorem isIso_affineCohomologyBaseChangeMap (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    [IsAffine (chartScheme V₀)] [IsAffine (chartScheme V₀')] (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    IsIso (D.affineCohomologyBaseChangeMap hg
      (isAffineSpace_of_isIso_chart B S hS D.Y V₀)
      (isAffineSpace_of_isIso_chart B S hS D.Y' V₀') i) := by
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have := enoughInjectives_modules B S hS D.X.1 D.X.2
  have hstep := D.affineCohomologyBaseChangeMap_chartTensorToSource V₀ V₀' hZ hg hqc hqs i
  have hsurj := D.chartTensorToSource_surjective V₀ V₀' i
  have hbij : Function.Bijective
      (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom.hom :=
    (ConcreteCategory.isIso_iff_bijective
      (D.affineCohomologyBaseChangeIso hZ hg hqc hqs V₀ V₀' i).hom).mp inferInstance
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨zx, rfl⟩ := hsurj x
    obtain ⟨zy, rfl⟩ := hsurj y
    exact congrArg (D.chartTensorToSource V₀ V₀' i)
      (hbij.injective ((hstep zx).symm.trans (hxy.trans (hstep zy))))
  · intro y
    obtain ⟨z, hz⟩ := hbij.surjective y
    exact ⟨D.chartTensorToSource V₀ V₀' i z, (hstep z).trans hz⟩

end BaseChangeDiagram

end AlgebraicGeometry.Space

end

end
