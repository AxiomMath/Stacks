module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseRingUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsUniverseLift

/-!
# Cohomology of an algebraic space in the universe of its structure sheaf

Let `X` be an algebraic space over `Spec A`, for schemes in `Type u`. Its cohomology appears in
this library in two module universes. `AlgebraicGeometry.Space.cohomologyOverBase` is the
cohomology of an `𝒪_X`-module whose sections lie in a universe `max (u + 1) w` containing the
small étale site; the Euler characteristic of Stacks 0DN1 is taken of it. The right derived
functors of `Stacks.Cohomology.SiteModules.globalSectionsFunctor` on `𝒪_X`-modules with sections
in `Type u`, the universe of the structure sheaf, are where direct images
(`AlgebraicGeometry.Space.modulePushforward`) and their higher direct images live.

This file identifies the two: for an `𝒪_X`-module `M` with sections in `Type u`, the
cohomology over the base ring of its universe lift is the universe lift of its cohomology,
`Hⁱ(X, M↑) ≅ Hⁱ(X, M)↑` as `A`-modules.

## Main results

* `AlgebraicGeometry.Space.hasSeparator_modules_ringUniverse`: the `𝒪_X`-modules with sections
  in the universe of the structure sheaf have a separator.
* `AlgebraicGeometry.Space.cohomologyOverBaseUliftForPresentationIso`: **`Hⁱ(X, M↑) ≅ Hⁱ(X, M)↑`**
  over the base ring.
* `AlgebraicGeometry.Space.moduleFinite_cohomologyOverBase_uliftForPresentation_iff_rightDerived`,
  `AlgebraicGeometry.Space.isZero_cohomologyOverBase_uliftForPresentation_iff_rightDerived` and
  `AlgebraicGeometry.Space.finrank_cohomologyOverBase_uliftForPresentation`: finiteness,
  vanishing and dimension of the cohomology may be read in either universe.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Stacks.Cohomology.SiteModules

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

/-- The `𝒪_F`-modules on the small étale ringed site of an algebraic space, at the universe of
the structure rings, have a separator: they form a Grothendieck abelian category, the site being
essentially small. -/
theorem hasSeparator_modules_ringUniverse (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasSeparator (Modules.{u, u} B S hS F hF) := by
  have : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS F)
    infer_instance
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS F hF) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  infer_instance

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- **The cohomology over the base ring of the universe lift of a module is the universe lift of
its cohomology.** For an `𝒪_X`-module `M` with sections in the universe `u` of the structure
sheaf, `AlgebraicGeometry.Space.cohomologyOverBase` of its universe lift is, as an `A`-module, the
universe lift of the `i`-th right derived functor of global sections at `M`, with scalars
restricted along `AlgebraicGeometry.Space.baseRingHom`. -/
def cohomologyOverBaseUliftForPresentationIso (M : Modules.{u, u} B (Spec (.of A)) hA X hX)
    (i : ℕ) :
    have := enoughInjectives_modules B (Spec (.of A)) hA X hX
    cohomologyOverBase.{u, w} A B hA X hX
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} M) i ≅
      (ModuleCat.uliftFunctor.{max (u + 1) w} A).obj
        ((ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived i).obj M)) := by
  have := enoughInjectives_modules B (Spec (.of A)) hA X hX
  have := hasSeparator_modules_ringUniverse B (Spec (.of A)) hA X hX
  have := site_hasSheafify_addCommGrp.{u + 1, u, w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J)
  have := site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, w}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J)
  have := site_hasSheafify_addCommGrp.{u + 1, u, u}
    (J := (smallEtaleRingedSite B (Spec (.of A)) hA X hX).J)
  have := moduleSheavesEnoughInjectives.{u + 1, u, u, w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
  exact (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).mapIso
    ((rightDerivedGlobalSectionsUliftForPresentationIso.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
        i).app M).symm

/-- Finiteness over the base ring of the cohomology of the universe lift of a module is
finiteness of the cohomology of the module. -/
theorem moduleFinite_cohomologyOverBase_uliftForPresentation_iff_rightDerived
    (M : Modules.{u, u} B (Spec (.of A)) hA X hX) (i : ℕ) :
    have := enoughInjectives_modules B (Spec (.of A)) hA X hX
    Module.Finite A (cohomologyOverBase.{u, w} A B hA X hX
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} M) i) ↔
      Module.Finite A ((ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived i).obj M)) := by
  intro
  rw [Module.Finite.equiv_iff
    (cohomologyOverBaseUliftForPresentationIso.{u, w} A B hA X hX M i).toLinearEquiv]
  exact Module.Finite.equiv_iff ULift.moduleEquiv

/-- Vanishing of the cohomology of the universe lift of a module is vanishing of the cohomology
of the module. -/
theorem isZero_cohomologyOverBase_uliftForPresentation_iff_rightDerived
    (M : Modules.{u, u} B (Spec (.of A)) hA X hX) (i : ℕ) :
    have := enoughInjectives_modules B (Spec (.of A)) hA X hX
    IsZero (cohomologyOverBase.{u, w} A B hA X hX
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} M) i) ↔
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived i).obj M) := by
  intro
  rw [Iso.isZero_iff (cohomologyOverBaseUliftForPresentationIso.{u, w} A B hA X hX M i),
    ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  let N := ((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived i).obj M
  let e : ULift.{max (u + 1) w} N ≃ N := Equiv.ulift
  exact ⟨fun h ↦ @Equiv.subsingleton _ _ e.symm h, fun h ↦ @Equiv.subsingleton _ _ e h⟩

/-- The dimension over a field of the cohomology of the universe lift of a module is the
dimension of the cohomology of the module. -/
theorem finrank_cohomologyOverBase_uliftForPresentation (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) (Y : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hY : IsAlgebraicSpace B (Spec (.of k)) hk Y) (M : Modules.{u, u} B (Spec (.of k)) hk Y hY)
    (i : ℕ) :
    have := enoughInjectives_modules B (Spec (.of k)) hk Y hY
    Module.finrank k (cohomologyOverBase.{u, w} k B hk Y hY
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, max (u + 1) w} M) i) =
      Module.finrank k ((ModuleCat.restrictScalars (baseRingHom k B hk Y hY)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of k)) hk Y hY).O)).rightDerived i).obj M)) := by
  intro
  rw [(cohomologyOverBaseUliftForPresentationIso.{u, w} k B hk Y hY M i).toLinearEquiv.finrank_eq]
  exact ULift.moduleEquiv.finrank_eq

end AlgebraicGeometry.Space

end
