module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportedSectionsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.EmbeddedPoints.SupportedSectionsStalk

/-!
# Dividing out the sections supported on a subset

Let `F` be a module on a scheme `X` and let `Z ⊆ X`. Dividing `F` by its submodule of sections
supported on `Z` leaves a module with **no** nonzero section supported on `Z`. For `Z` a closed
point `x` this says that `x` is not an associated point of the quotient, which is the payoff of
the opening reduction of the induction step of [Stacks, Tag 0F27].

The argument is a diagram chase once the stalks are in place. Write `H` for the sections of `F`
supported on `Z`, `π : F → Q = F/H` for the quotient, and `H'` for the sections of `Q` supported
on `Z`. Form the pullback of `π` along the inclusion of `H'`; its projection to `H'` is epi,
because `π` is, so it suffices to see that its projection `a` to `F` satisfies `a ≫ π = 0`. A
section `a(p)` maps under `π` to a section of `H'`, whose germ at a point `y ∉ Z` vanishes; and at
such a `y` the stalk of `H` vanishes, so `π` is an isomorphism on stalks there and the germ of
`a(p)` itself vanishes. Hence `a(p)` is a section of `H`, which `π` kills.

## Main results

* `Stacks.AlgebraicGeometry.EmbeddedPoints.eq_zero_of_mem_supportedSectionsSubmodule_cokernel`:
  **the quotient of a module by its sections supported on `Z` has no nonzero section supported
  on `Z`.**
* `Stacks.AlgebraicGeometry.EmbeddedPoints.not_isAssociatedPoint_cokernel_supportedSections`:
  **a closed point is not an associated point of the quotient of a module by its sections
  supported at that point.**

## Implementation notes

The first result needs nothing of `Z` and nothing of `F`: no closedness, no retrocompactness, no
quasi-coherence. The second needs all three, not for the chase but for the affine comparison of
associated points with associated primes
(`AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian`) and
for the quasi-coherence of the quotient that comparison is applied to.

The chase is run on sections rather than on stalks, so that the conclusion `a ≫ π = 0` is reached
by `CategoryTheory.Limits.cokernel.condition` applied to an explicitly exhibited section of `H`
rather than by a vanishing-on-all-stalks criterion -- which would be unavailable, since at the
points *of* `Z` nothing is claimed about the stalk of `H`.

Every object is bound as an `AlgebraicGeometry.Scheme.Modules` before any categorical instance is
asked for. `SheafOfModules.Submodule.toSheafOfModules` and `CategoryTheory.Limits.cokernel` report
their values in `SheafOfModules X.ringCatSheaf`, which is the same type but not the same instance
problem: there `X.ringCatSheaf` has to be recognised as a sheaf on the Grothendieck topology of
the opens, which exceeds instance transparency, and neither the zero morphism nor the epimorphism
coming from the pullback of an epimorphism is found.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 084L](https://stacks.math.columbia.edu/tag/084L)
* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.EmbeddedPoints

variable {X : Scheme.{u}}

/-! ### The quotient has no sections supported on the subset -/

/-- **A section of the quotient of `F` by its sections supported on `Z` which is itself supported
on `Z` is zero.**

Nothing is assumed of `Z` or of `F`. -/
theorem eq_zero_of_mem_supportedSectionsSubmodule_cokernel (Z : Set X) (F : X.Modules)
    (U : X.Opens)
    (t : Γ((cokernel (supportedSectionsSubmodule Z F).ι : X.Modules), U))
    (ht : t ∈ (supportedSectionsSubmodule Z
        (cokernel (supportedSectionsSubmodule Z F).ι : X.Modules)).toSubmodule.obj (op U)) :
    t = 0 := by
  let H := supportedSectionsSubmodule Z F
  let HM : X.Modules := H.toSheafOfModules
  let hι : HM ⟶ F := H.ι
  let Q : X.Modules := cokernel hι
  let π : F ⟶ Q := cokernel.π hι
  let H' := supportedSectionsSubmodule Z Q
  let HM' : X.Modules := H'.toSheafOfModules
  let hι' : HM' ⟶ Q := H'.ι
  let a : pullback π hι' ⟶ F := pullback.fst π hι'
  let b : pullback π hι' ⟶ HM' := pullback.snd π hι'
  -- the image in `F` of a section of the pullback is supported on `Z`
  have hmem : ∀ (V : (Opens ↥X)ᵒᵖ) (p : (pullback π hι').val.obj V),
      a.val.app V p ∈ H.toSubmodule.obj V := by
    intro V p
    refine (Scheme.Modules.mem_supportedSectionsSubmodule_iff Z F V.unop (a.val.app V p)).mpr ?_
    intro y hy hyZ
    have hab : π.val.app V (a.val.app V p) = (b.val.app V p).1 :=
      congrArg (fun g : pullback π hι' ⟶ Q ↦ g.val.app V p) pullback.condition
    have hgq : TopCat.Presheaf.germ Q.val.presheaf V.unop y hy
        (π.val.app V (a.val.app V p)) = 0 := by
      rw [hab]
      exact (Scheme.Modules.mem_supportedSectionsSubmodule_iff Z Q V.unop _).mp
        (b.val.app V p).2 y hy hyZ
    set T := AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf y
    have hiso : IsIso (T.map π) :=
      isIso_map_cokernelπ_of_isZero T hι (isZero_stalkFunctor_obj_supportedSections Z F hyZ)
    refine (ConcreteCategory.bijective_of_isIso (T.map π)).1 ?_
    have h2 : (T.map π) (TopCat.Presheaf.germ F.val.presheaf V.unop y hy (a.val.app V p)) =
        TopCat.Presheaf.germ Q.val.presheaf V.unop y hy
          (π.val.app (op V.unop) (a.val.app V p)) :=
      TopCat.Presheaf.stalkFunctor_map_germ_apply (C := AddCommGrpCat.{u}) V.unop y hy
        ((SheafOfModules.toSheaf X.ringCatSheaf).map π).hom (a.val.app V p)
    rw [h2, hgq]
    exact (map_zero _).symm
  -- the pullback projection therefore factors through `H`, which the quotient map kills
  obtain ⟨c, hc⟩ : ∃ c : pullback π hι' ⟶ HM, c ≫ hι = a :=
    ⟨Stacks.SheafOfModules.sheafFactorThruSubmodule a H hmem,
      Stacks.SheafOfModules.sheafFactorThruSubmodule_ι a H hmem⟩
  have hπcond : hι ≫ π = 0 := cokernel.condition hι
  have hkey : a ≫ π = 0 := by rw [← hc, Category.assoc, hπcond, comp_zero]
  have hzero : hι' = 0 := by
    refine (cancel_epi b).mp ?_
    rw [comp_zero]
    exact pullback.condition.symm.trans hkey
  exact congrArg (fun g : HM' ⟶ Q ↦ g.val.app (op U) ⟨t, ht⟩) hzero

/-! ### No associated point at the closed point -/

/-- **A closed point is not an associated point of the quotient of a module by its sections
supported at that point.**

The affine comparison of [Stacks, Tag 02OK] turns an association at `x` into a section of the
quotient over an affine neighbourhood whose colon ideal is the prime of `x`; such a section is
supported on the closure of `x`, which is `{x}`
(`Stacks.AlgebraicGeometry.EmbeddedPoints.mem_supportedSectionsSubmodule_closure_singleton`), and
is therefore zero. But the colon ideal of the zero section is the unit ideal, not a prime.

This is the payoff of the opening reduction of the induction step of [Stacks, Tag 0F27]: after
dividing the closed-fibre member by its sections supported at the closed point, the closed point
is no longer an associated point of it. -/
theorem not_isAssociatedPoint_cokernel_supportedSections [IsLocallyNoetherian X] (F : X.Modules)
    (hF : F.IsQuasicoherent) {x : X} (hx : IsClosed ({x} : Set X)) :
    ¬ Stacks.Divisors.IsAssociatedPoint
      (cokernel (supportedSectionsSubmodule ({x} : Set X) F).ι : X.Modules) x := by
  intro hass
  have hHqc : (supportedSectionsSubmodule ({x} : Set X) F).toSheafOfModules.IsQuasicoherent :=
    supportedSectionsSubmodule_isQuasicoherent ({x} : Set X) hx
      (isRetrocompact_of_isLocallyNoetherian _) F hF
  have hQqc :
      (cokernel (supportedSectionsSubmodule ({x} : Set X) F).ι : X.Modules).IsQuasicoherent :=
    @Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _ _ _
      (supportedSectionsSubmodule ({x} : Set X) F).ι hHqc hF
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) (by simp)
  obtain ⟨hp, s, hs⟩ :=
    (AlgebraicGeometry.isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
      (cokernel (supportedSectionsSubmodule ({x} : Set X) F).ι : X.Modules) U hU hxU).mpr hass
  have hsH := mem_supportedSectionsSubmodule_closure_singleton
    (cokernel (supportedSectionsSubmodule ({x} : Set X) F).ι : X.Modules) U hU hxU s hs
  rw [hx.closure_eq] at hsH
  rw [eq_zero_of_mem_supportedSectionsSubmodule_cokernel ({x} : Set X) F U s hsH,
    Submodule.span_zero_singleton, Submodule.colon_bot] at hs
  exact hp.ne_top hs.symm

end Stacks.AlgebraicGeometry.EmbeddedPoints

end
