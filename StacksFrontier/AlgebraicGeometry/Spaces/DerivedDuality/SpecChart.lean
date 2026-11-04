module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.EtaleBound
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.SpecDualizingModel

/-!
# The full duality chart of `Spec R` on the model of its small étale site

For a Noetherian ring `R` and a dualizing complex `ω` on `Spec R`, the pullback `ε^*` to the
equi-universe model of the small étale site of `Spec R` is a duality chart for `ε^* ω` at the
class of all objects: the étale vanishing bound
(`AlgebraicGeometry.SmallEtale.isZero_homology_modelSheafHom_of_injectiveAmplitude`, from Stacks
0E50) is the input of the way-out argument of `AlgebraicGeometry.SmallEtale.baseDualityChart`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.specDualityChart`.

## References

* [Stacks Project, Tag 0E50](https://stacks.math.columbia.edu/tag/0E50)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.SmallEtale

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (E : BigEtaleSite.{u})
  (hX : E.Contains (Spec R))

/-- **The étale vanishing bound for a dualizing complex on `Spec R`.** -/
theorem exists_etaleBound (ω : RingedSite.SchemeStdDerived (Spec R))
    (hω : letI : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) :
    ∃ bEt : ℤ, ∀ (m : ℤ) (Y : RingedSite.SchemeStdDerived (Spec R)),
      RingedSite.SchemeCoherent _ Y →
      (∀ i : ℤ, i < m → IsZero ((RingedSite.schemeStdHomology _ i).obj Y)) →
        ∀ j : ℤ, bEt - m < j → IsZero ((RingedSite.stdHomology (modelSite E (Spec R) hX) j).obj
          (((RingedSite.stdSheafHom (modelSite E (Spec R) hX)).obj
            (op ((chartFunctor E (Spec R) hX).derived.obj Y))).obj
              ((chartFunctor E (Spec R) hX).derived.obj ω))) := by
  obtain ⟨L, a, b, hL, ⟨eL⟩⟩ := Space.SpecModel.exists_tilde_iso_of_isDualizingComplex R ω hω
  refine ⟨b, fun m Y hY hYge j hj => ?_⟩
  exact
    (isZero_homology_modelSheafHom_of_injectiveAmplitude R E hX L a b hL m Y hY hYge j hj).of_iso
      ((RingedSite.stdHomology (modelSite E (Spec R) hX) j).mapIso
        (((RingedSite.stdSheafHom (modelSite E (Spec R) hX)).obj _).mapIso
          ((chartFunctor E (Spec R) hX).derived.mapIso eL.symm)))

/-- **The duality chart of `Spec R` at the class of all objects** (Stacks 0A89 read through
Stacks 0E50 and 08JP). -/
def specDualityChart (ω : RingedSite.SchemeStdDerived (Spec R))
    (hω : letI : HasDerivedCategory (Spec R).Modules := HasDerivedCategory.standard _
      Stacks.Duality.IsDualizingComplex ω) :
    RingedSite.DualityChart (modelSite E (Spec R) hX) ((chartFunctor E (Spec R) hX).derived.obj ω)
      RingedSite.ChartClass.all :=
  baseDualityChart E (Spec R) hX ω hω (exists_etaleBound R E hX ω hω).choose
    (exists_etaleBound R E hX ω hω).choose_spec

end AlgebraicGeometry.SmallEtale
