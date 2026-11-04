module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitReflection
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Comparison

/-!
# The conclusion of Stacks 0EFL read on the extended Čech complex

Let `I` and `J` be ideals of a Noetherian ring `A` and let `M` be an `A`-module. Stacks 0EFL
concludes that the canonical map `RΓ_{J'}(M) ⟶ RΓ_J(M)^∧` is an isomorphism on cohomology in
degrees `≤ s`, for every admissible `J' ⊆ J₀`
(`Stacks.Algebraization.IsAlgebraizationIdeal`). That map is the unit of derived `I`-adic
completion at `RΓ_{J'}(M)`, followed by an isomorphism. This file moves the statement onto the
extended Čech complex `C^•(g₁, …, g_r; M)` of generators of `J'` and onto any map out of it which
derived completion inverts and whose target is derived complete: such a map is an isomorphism on
cohomology in the same degrees. This is the step of the proof of Stacks 0EIF which turns the
output of Stacks 0EFL into a statement about an explicit complex.

## Main results

* `Stacks.Algebraization.isIso_homologyMap_adicCompletionUnit_cech_iff` — the unit of derived
  completion is an isomorphism on `Hⁱ` at `RΓ_J(M)` exactly when it is at `C^•(g; M)`.
* `Stacks.Algebraization.IsAlgebraizationIdeal.isIso_homologyMap_of_cech` — for `J₀` as in
  Stacks 0EFL and generators `g` of an admissible `J' ⊆ J₀`, every map out of `C^•(g; M)` which
  derived completion inverts and whose target is derived complete is an isomorphism on `Hⁱ`,
  `i ≤ s`.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

variable {A : Type u} [CommRing A] (I J : Ideal A) (hI : I.FG) (hJ : J.FG) {r : ℕ}
  (g : Fin r → A) (hg : Ideal.span (Set.range g) = J) (M : ModuleCat.{u} A)

include hg in
/-- **The unit of derived completion at `RΓ_J(M)` and at the Čech complex.** For generators `g`
of `J`, the unit of derived `I`-adic completion is an isomorphism on `Hⁱ` at `RΓ_J(M)` exactly
when it is one at the extended Čech complex `C^•(g; M)`: the two are identified by
`Stacks.LocalCohomology.localCohomologyIsoCech`, and the unit is natural. -/
public theorem isIso_homologyMap_adicCompletionUnit_cech_iff (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((adicCompletionUnit A I hI).app ((localCohomologyDerived A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))) ↔
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        ((adicCompletionUnit A I hI).app ((extendedCechObjectFunctor.{0} g).obj M))) := by
  let η := Functor.whiskerRight (adicCompletionUnit A I hI)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)
  exact NatTrans.isIso_app_iff_of_iso η ((localCohomologyIsoCech.{0} g J hJ hg).app M)

variable {I} {M} in
/-- **The conclusion of Stacks 0EFL on the Čech complex.** Let `J₀` be an ideal as in the
conclusion of Stacks 0EFL for `M`, `J` and `s`, let `J' ⊆ J₀` be admissible
(`V(J') ∩ V(I) = V(J) ∩ V(I)`) with generators `g`, and let `φ : C^•(g; M) ⟶ Y` be a map of
`D(A)` with `Y` derived `I`-complete which derived `I`-adic completion inverts. Then `φ` is an
isomorphism on `Hⁱ` for every `i ≤ s`.

The map of Stacks 0EFL is the unit of completion at `RΓ_{J'}(M)` followed by an isomorphism, so
the unit is an isomorphism on `Hⁱ`; it then is one at `C^•(g; M)` by
`Stacks.Algebraization.isIso_homologyMap_adicCompletionUnit_cech_iff`, and so is `φ` by
`Stacks.Algebraization.isIso_homologyMap_adicCompletionUnit_app_iff`. -/
public theorem IsAlgebraizationIdeal.isIso_homologyMap_of_cech [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M] {s : ℤ} {J₀ : Ideal A}
    (h : IsAlgebraizationIdeal (M := M) I J s J₀) (J' : Ideal A) (hJ' : J' ≤ J₀)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (g : Fin r → A) (hg : Ideal.span (Set.range g) = J')
    {Y : DerivedCategory (ModuleCat.{u} A)}
    (φ : (extendedCechObjectFunctor.{0} g).obj (ModuleCat.of A M) ⟶ Y)
    (hY : IsDerivedComplete I Y)
    [IsIso ((adicCompletionFunctor A I I.fg_of_isNoetherianRing).map φ)]
    (i : ℤ) (hi : i ≤ s) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map φ) := by
  have h0 := h.isIso J' hJ' hV i hi
  have e := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map_comp
    ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
      ((localCohomologyDerived A J' J'.fg_of_isNoetherianRing).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))))
    (completedLocalCohomologyShrinkIso A I J J' I.fg_of_isNoetherianRing
      J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing (ModuleCat.of A M) hV).hom
  have h0' := Eq.mp (congrArg IsIso e) h0
  have h1 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
        ((localCohomologyDerived A J' J'.fg_of_isNoetherianRing).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))))) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ _
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
        (completedLocalCohomologyShrinkIso A I J J' I.fg_of_isNoetherianRing
          J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing (ModuleCat.of A M) hV)).isIso_hom)
      h0'
  have h2 := (isIso_homologyMap_adicCompletionUnit_cech_iff I J' I.fg_of_isNoetherianRing
    J'.fg_of_isNoetherianRing g hg (ModuleCat.of A M) i).1 h1
  exact (isIso_homologyMap_adicCompletionUnit_app_iff I I.fg_of_isNoetherianRing φ hY i).1 h2

end Stacks.Algebraization

end
