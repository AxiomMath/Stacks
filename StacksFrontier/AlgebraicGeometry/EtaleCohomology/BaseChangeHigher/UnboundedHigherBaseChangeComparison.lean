module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.UnboundedDerivedBaseChangeHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannLimitStep
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.ModuleBaseChangeFromAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections

/-!
# The two base change maps on higher direct images of étale sheaves agree

Let
```
X' <-h-- Y
|f       |e
S  <-g-- T
```
be a commutative square of schemes, `h ≫ f = e ≫ g`, and `F` an abelian sheaf on `T_étale`. The
library carries two base change maps `f⁻¹ Rᵠ g_* F ⟶ Rᵠ h_* e⁻¹ F`:

* `Stacks.EtaleCohomology.higherBaseChangeMapAb` ([Stacks, Tag 0F02]), the degree-`q` cohomology of
  the bounded below derived base change map `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`,
  with the inverse images `Stacks.EtaleCohomology.smallEtalePullbackAb`;
* `Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange`, the
  degree-`q` cohomology of the unbounded derived base change map
  `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange` ([Stacks, Tag 0A2A]), with the inverse
  images `Stacks.EtaleCohomology.etaleAbelianInverseImage`.

Until now the library only knew that they are invertible together
(`isIso_etaleAbelianDerivedBaseChange_app_of_isIso_smallEtaleDerivedBaseChangeAb`, in the namespace
`Stacks.EtaleCohomology`).
**This file proves that they are the same map**, read through the identification
`Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleAbelianInverseImage` of the two inverse images.
This is the compatibility clause of the lemma on stalks of higher direct images
(Travaux de Gabber, Exposé XVIII-A, §2), on the side of the base change maps.

## Main results

* `Stacks.EtaleCohomology.unboundedFac_etaleAbelianDerivedBaseChange` — the unbounded étale base
  change map satisfies `Stacks.Cohomology.BaseChange.UnboundedFac`.
* `etaleAbelianInverseImageRightDerivedDirectImageBaseChange_eq_higherBaseChangeMapAb` (namespace
  `Stacks.EtaleCohomology`) — **the two base change maps on `Rᵠ` agree.**

## Implementation notes

The statement is the instance, at the étale direct and inverse images, of
`Stacks.Cohomology.BaseChange.unboundedHigher_conj_eq_boundedHigher`, whose hypothesis
`Stacks.Cohomology.BaseChange.UnboundedFac` is
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_fac` (through
`Stacks.Cohomology.BaseChange.unboundedFac_of_homotopy`) and whose comparison of the two
underived base change maps is
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange_zero`.

## References

* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/- The spelling of the preferred `Preadditive` structure and zero morphisms of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/BaseChangeMap.lean`, in which
`etaleAbelianDerivedBaseChange_fac` is stated;
with another spelling the kernel has to unfold both, which times out. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive

variable {X' Y S T : Scheme.{u}} (f : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f = e ≫ g)

/-- The unbounded étale base change map satisfies the factorisation
`Stacks.Cohomology.BaseChange.UnboundedFac`: this is `etaleAbelianDerivedBaseChange_fac`, the
degreewise comparison `etaleAbelianHomotopyBaseChange` being by definition the underived one
conjugated by the identity comparisons. -/
theorem unboundedFac_etaleAbelianDerivedBaseChange :
    Stacks.Cohomology.BaseChange.UnboundedFac (etaleAbelianDirectImage.{u, 0} g)
      (etaleAbelianDirectImage.{u, 0} h) (etaleAbelianInverseImage.{u, 0} f)
      (etaleAbelianInverseImage.{u, 0} e) (etaleAbelianBaseChange.{u, 0} g f e h w.symm)
      (etaleAbelianDerivedDirectImage.{u, 0} g) (etaleAbelianDerivedDirectImageUnit.{u, 0} g)
      (etaleAbelianDerivedDirectImage.{u, 0} h) (etaleAbelianDerivedDirectImageUnit.{u, 0} h)
      (etaleAbelianDerivedBaseChange.{u, 0} g f e h w.symm) :=
  Stacks.Cohomology.BaseChange.unboundedFac_of_homotopy _ _ _ _ _ _ _ _ _ _
    (etaleAbelianHomotopyBaseChange.{u, 0} g f e h w.symm) rfl
    (fun K => etaleAbelianDerivedBaseChange_fac.{u, 0} g f e h w.symm K)

/-- **The unbounded and the bounded below base change maps on higher direct images agree.** For a
commutative square `h ≫ f = e ≫ g` of schemes, an abelian sheaf `F` on `T_étale` and `q : ℕ`, the
degree-`q` base change map `f⁻¹ Rᵠ g_* F ⟶ Rᵠ h_* e⁻¹ F` obtained from the unbounded derived base
change map (`etaleAbelianInverseImageRightDerivedDirectImageBaseChange`) is the one of
[Stacks, Tag 0F02] obtained from the bounded below derived base change map
(`higherBaseChangeMapAb`), read through the identification
`smallEtalePullbackAbIsoEtaleAbelianInverseImage` of the two inverse images at the source and the
target. -/
theorem etaleAbelianInverseImageRightDerivedDirectImageBaseChange_eq_higherBaseChangeMapAb
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ) :
    (smallEtalePullbackAbIsoEtaleAbelianInverseImage f).hom.app
        (((smallEtalePushforwardAb g).rightDerived q).obj F) ≫
      etaleAbelianInverseImageRightDerivedDirectImageBaseChange g f e h w.symm F q =
    (higherBaseChangeMapAb f g h e w q).app F ≫
      ((smallEtalePushforwardAb h).rightDerived q).map
        ((smallEtalePullbackAbIsoEtaleAbelianInverseImage e).hom.app F) :=
  Stacks.Cohomology.BaseChange.unboundedHigher_conj_eq_boundedHigher
    (etaleAbelianDirectImage.{u, 0} g) (etaleAbelianDirectImage.{u, 0} h) (smallEtalePullbackAb f)
    (smallEtalePullbackAb e) (etaleAbelianInverseImage.{u, 0} f)
    (etaleAbelianInverseImage.{u, 0} e) (smallEtalePullbackAbIsoInverseImage f)
    (smallEtalePullbackAbIsoInverseImage e) (etaleAbelianDerivedDirectImage.{u, 0} g)
    (etaleAbelianDerivedDirectImageUnit.{u, 0} g) (etaleAbelianDerivedDirectImage.{u, 0} h)
    (etaleAbelianDerivedDirectImageUnit.{u, 0} h)
    (etaleAbelianDerivedBaseChange.{u, 0} g f e h w.symm)
    (by
      have := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} T
      exact Stacks.DerivedFunctor.exists_quasiIso_isKInjective)
    (by
      have := isGrothendieckAbelian_sheaf_smallEtale.{u, 0} Y
      exact Stacks.DerivedFunctor.exists_quasiIso_isKInjective)
    (smallEtaleBaseChangeAb f g h e w) (etaleAbelianBaseChange.{u, 0} g f e h w.symm)
    (smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange_zero f g h e w)
    (unboundedFac_etaleAbelianDerivedBaseChange f g h e w) q F

end Stacks.EtaleCohomology

end
