module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteTypeStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.CategoryTheory.Sites.Point.UliftFiber

/-!
# Constructible sheaves of modules on Mathlib's small étale site have finite stalks

Constructibility of a sheaf of `Λ`-modules, `AlgebraicGeometry.IsConstructibleModuleSheaf`
(Stacks 03RW (3)), is stated on the size-bounded small étale site of Stacks 021B, while the
localization sequence of Tag 095L for sheaves of `Λ`-modules and the étale cohomology it feeds
are stated on Mathlib's small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`. The two
sites have the same sheaves, by `AlgebraicGeometry.SmallEtale.sheafEquiv`, so constructibility of
a sheaf on Mathlib's site means constructibility of the sheaf of the bounded site it corresponds
to. This file records that reading, the module-coefficient counterpart of
`AlgebraicGeometry.IsConstructibleEtaleSiteAbelianSheaf`, and transports the finiteness of the
geometric stalks across it.

## Main definitions

* `AlgebraicGeometry.IsConstructibleEtaleSiteModuleSheaf` — constructibility of a sheaf of
  `Λ`-modules on Mathlib's small étale site.

## Main results

* `AlgebraicGeometry.finite_sheafFiber_of_isConstructibleEtaleSiteModuleSheaf` — the stalk at a
  geometric point of such a sheaf is a finite `Λ`-module.
* `AlgebraicGeometry.finite_sheafFiber_ulift_of_isConstructibleEtaleSiteModuleSheaf` — the same
  for the stalk formed at the universe lift of the point, which is the shape in which the stalk
  appears in `Stacks.EtaleCohomology.etaleModuleInverseImageSheafFiberIso`.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r

namespace AlgebraicGeometry

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **A constructible sheaf of `Λ`-modules on Mathlib's small étale site**: one whose
corresponding sheaf on the size-bounded small étale site of Stacks 021B is constructible in the
sense of Stacks 03RW (3). The two sites have the same sheaves, so this is the notion of Tag 03RW
read on Mathlib's site. -/
abbrev IsConstructibleEtaleSiteModuleSheaf
    (ℱ : Sheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) : Prop :=
  IsConstructibleModuleSheaf B X Λ
    ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).inverse.obj ℱ)

omit [IsNoetherianRing Λ] in
/-- **The geometric stalks of a constructible sheaf of `Λ`-modules on Mathlib's small étale site
are finite `Λ`-modules.** This is
`AlgebraicGeometry.isFG_etaleStalk_of_isConstructibleModuleSheaf` transported along the
identification of the two small étale sites. -/
theorem finite_sheafFiber_of_isConstructibleEtaleSiteModuleSheaf
    (ℱ : Sheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
    (hℱ : IsConstructibleEtaleSiteModuleSheaf B X Λ ℱ) (s : GeometricPoint X.obj) :
    Module.Finite Λ
      (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).obj ℱ) := by
  set e := SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ) with he
  have h2 := finite_sheafFiber_sheafEquiv B X Λ s (e.inverse.obj ℱ)
    ((ModuleCat.isFG_iff _).mp
      (isFG_etaleStalk_of_isConstructibleModuleSheaf B Λ X (e.inverse.obj ℱ) hℱ s))
  have : Module.Finite Λ (((Scheme.pointSmallEtale s.hom).sheafFiber
      (A := ModuleCat.{max (u + 1) r} Λ)).obj ((e.inverse ⋙ e.functor).obj ℱ)) := h2
  exact Module.Finite.equiv
    (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{max (u + 1) r} Λ)).mapIso
      (e.counitIso.app ℱ)).toLinearEquiv

omit [IsNoetherianRing Λ] in
/-- **The geometric stalks of a constructible sheaf of `Λ`-modules on Mathlib's small étale site
are finite `Λ`-modules**, in the form where the stalk is taken at the universe lift of the point,
as `Stacks.EtaleCohomology.etaleModuleInverseImageSheafFiberIso` produces it. -/
theorem finite_sheafFiber_ulift_of_isConstructibleEtaleSiteModuleSheaf
    (ℱ : Sheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))
    (hℱ : IsConstructibleEtaleSiteModuleSheaf B X Λ ℱ) (s : GeometricPoint X.obj) :
    Module.Finite Λ
      (((Scheme.pointSmallEtale s.hom).ulift.{max (u + 1) r}.sheafFiber
        (A := ModuleCat.{max (u + 1) r} Λ)).obj ℱ) :=
  have := finite_sheafFiber_of_isConstructibleEtaleSiteModuleSheaf B X Λ ℱ hℱ s
  Module.Finite.equiv
    (GrothendieckTopology.Point.sheafFiberUliftIso.{u, max (u + 1) r}
      (Scheme.pointSmallEtale s.hom) ℱ).symm.toLinearEquiv

end AlgebraicGeometry

end
