module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.AlgebraicGeometry.Blowup.DerivedPullbackAnnihilation

/-!
# The annihilation of [Stacks, Tag 0GA0] as the vanishing of a central endomorphism

[Stacks, Tag 0GA0] — `Stacks.Blowup.exists_pow_le_annihilator_homology_derivedPullback` — states
the annihilation of the cohomology sheaves `H^j(Lp^*M̃)` of the derived pullback to the blowup on
*sections*: an element `r ∈ Iᶜ`, viewed as a global section of the blowup through its structure
morphism and restricted to an open `U`, kills every section over `U`.

The hypercohomology annihilation that consumes it,
`Stacks.Cohomology.FilteredComplex.mem_annihilator_homology_RΓ_single_of_center_app_eq_zero`,
asks instead for the vanishing `η.app F = 0` of the central endomorphism `η` of the category of
module sheaves given by multiplication by that global section. This file is the step between the
two: a morphism of sheaves of modules is determined by what it does to sections, so a scalar
killing every section over every open is the zero endomorphism
(`Stacks.SheafOfModules.terminalSectionToEnd_app_eq_zero`), and the restriction map along which
`Stacks.SheafOfModules.terminalSection` restricts the global scalar is the one appearing in
[Stacks, Tag 0GA0], both being the unique morphism `U ⟶ ⊤` of `Opens X`.

## Main results

* `Stacks.Blowup.exists_pow_le_center_app_homology_derivedPullback_eq_zero`:
  **[Stacks, Tag 0GA0] in the form `η.app H^j(Lp^*M̃) = 0`**, for `η` multiplication by the
  global section of the blowup attached to an element of `Iᶜ`.

## References

* [Stacks Project, Tag 0GA0](https://stacks.math.columbia.edu/tag/0GA0)
* [Stacks Project, Tag 0GA1](https://stacks.math.columbia.edu/tag/0GA1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedPullbackOfATilde

universe u


namespace Stacks.Blowup

-- The same priority bump as [Stacks, Tag 0GA0]'s own file: a second `HasDerivedCategory`
-- instance for module sheaves, with a smaller hom universe, is in scope through these imports,
-- and the statement here has to name the same derived category as the one the source's
-- conclusion is stated in.
attribute [local instance 10000] HasDerivedCategory.standard

/-- On a ringed space the rings of sections of the structure sheaf are commutative. This is the
form in which multiplication by a global section asks for it, and instance search does not see it
through the forgetful functor `CommRingCat ⥤ RingCat` that `structureSheafRing` postcomposes
with. The same instance is declared globally as
`Stacks.Cohomology.DerivedSectionsOverBase.ringSheaf_isMulCommutative`, in a file this one does
not need otherwise. -/
local instance ringSheaf_isMulCommutative (X : AlgebraicGeometry.RingedSpace.{u, u}) :
    ∀ U, IsMulCommutative ((structureSheafRing X).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (X.presheaf.obj U))

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **[Stacks, Tag 0GA0] with its conclusion read as the vanishing of a central endomorphism.**
There is a `c > 0`, depending only on `A` and `I`, such that for every `A`-module `M`, every
`j ≤ -t` and every `r ∈ Iᶜ`, multiplication by the global section of the blowup attached to `r`
is the *zero* endomorphism of the cohomology sheaf `H^j(Lp^*M̃)`.

This is the same statement as `Stacks.Blowup.exists_pow_le_annihilator_homology_derivedPullback`
read through `Stacks.SheafOfModules.terminalSectionToEnd_app_eq_zero`: the restriction of the
global scalar to an open `U` that the central endomorphism multiplies by is the restriction map
of the source, because `Opens X` has a unique morphism `U ⟶ ⊤`. -/
theorem exists_pow_le_center_app_homology_derivedPullback_eq_zero {n : ℕ} (g : Fin (n + 1) → A)
    (I : Ideal A) (hI : I = Ideal.span (Set.range g)) :
    ∃ c : ℕ, 0 < c ∧ ∀ (M : ModuleCat.{u} (CommRingCat.of A)) (j : ℤ), j ≤ -((n : ℤ) + 1) →
      ∀ r ∈ I ^ c,
        (Stacks.SheafOfModules.terminalSectionToEnd
            (structureSheafRing (blowUpSpec I).toRingedSpace) ⊤ isTerminalTop
            ((toSpec I).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv r))).asHom.app
          ((DerivedCategory.homologyFunctor (blowUpSpec I).Modules j).obj
            ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
                ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj M)))))
          = 0 := by
  obtain ⟨c, hc, hann⟩ := exists_pow_le_annihilator_homology_derivedPullback g I hI
  refine ⟨c, hc, fun M j hj r hr => ?_⟩
  refine Stacks.SheafOfModules.terminalSectionToEnd_app_eq_zero _ _ _ _ _ fun U x => ?_
  rw [show (isTerminalTop (α := Opens (blowUpSpec I).toRingedSpace.carrier)).from U.unop =
      homOfLE (le_top) from isTerminalTop.hom_ext _ _]
  exact hann M j hj U.unop r hr x

end Stacks.Blowup

end
