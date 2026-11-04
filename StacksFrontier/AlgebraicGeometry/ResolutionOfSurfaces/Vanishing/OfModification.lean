module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DerivedPushforwardStructureSheaf

/-!
# Situation 0AX8 from a modification, and Tag 0AXC in every shift

Situation [Stacks, Tag 0AX8] (`AlgebraicGeometry.VanishingSituation`) bundles a two-dimensional
Noetherian normal local domain `A`, a modification `f : X ⟶ Spec(A)` and an enumeration of the
irreducible components of the special fibre. The enumeration is not extra data in the source: the
special fibre is of finite type over the residue field, hence a Noetherian space with finitely
many irreducible components. This file builds the situation from `A` and `f` alone, and records
[Stacks, Tag 0AXC] after a shift, in the form in which it is used for [Stacks, Tag 0EA2].

## Main definitions

* `AlgebraicGeometry.VanishingSituation.ofModification`: Situation 0AX8 for a modification of
  the spectrum of a two-dimensional Noetherian normal local domain.

## Main results

* `AlgebraicGeometry.VanishingSituation.hom_singleFunctor_residueField_shift_eq_zero`: for `X`
  normal, every morphism `κ[-(n+1)] ⟶ RΓ(X, 𝒪_X)[-n]` of `D(A)` vanishes, for every `n : ℤ`;
  that is, `Hom(κ[-1], RΓ(X, 𝒪_X)) = 0` read after the shift by `-n`.

## References

* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
attribute [local instance] ModuleCat.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace VanishingSituation

/-- The special fibre of a morphism of finite type to the spectrum of a Noetherian local ring has
finitely many irreducible components. -/
theorem finite_irreducibleComponents_fiber_closedPoint {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    (irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))).Finite := by
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  have : TopologicalSpace.NoetherianSpace (f ⁻¹' {IsLocalRing.closedPoint A}) :=
    TopologicalSpace.NoetherianSpace.set _
  have : TopologicalSpace.NoetherianSpace (f.fiber (IsLocalRing.closedPoint A)) :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph
      (f.fiberHomeo (IsLocalRing.closedPoint A))).mpr this
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- **Situation [Stacks, Tag 0AX8] from a modification.** The enumeration of the irreducible
components of the special fibre is any enumeration of that finite set. -/
def ofModification (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsNormalDomain A] (hdim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (hf : IsModification f) : VanishingSituation.{u} :=
  haveI : IsProper f := hf.isProper
  haveI := (finite_irreducibleComponents_fiber_closedPoint f).to_subtype
  { A := A
    dimension_two := hdim
    X := X
    f := f
    modification := hf
    numberOfComponents := Nat.card
      {Z : Set (f.fiber (IsLocalRing.closedPoint A)) //
        Z ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))}
    components := (Finite.equivFin _).symm }

/-- **[Stacks, Tag 0AXC] after a shift.** In Situation 0AX8 with `X` normal, every morphism
`κ[-(n+1)] ⟶ RΓ(X, 𝒪_X)[-n]` of `D(A)` is zero. Shifting by `n` is an equivalence carrying
`κ[-(n+1)]` to `κ[-1]` and `RΓ(X, 𝒪_X)[-n]` to `RΓ(X, 𝒪_X)`, so this is
`hom_residueFieldShift_derivedGlobalSections_eq_zero`. -/
theorem hom_singleFunctor_residueField_shift_eq_zero (V : VanishingSituation.{u}) [IsNormal V.X]
    (n : ℤ)
    (g : (DerivedCategory.singleFunctor (ModuleCat.{u} V.A) (n + 1)).obj V.residueFieldModule ⟶
      (derivedGlobalSectionsStructureSheaf V.f)⟦-n⟧) : g = 0 := by
  let S := DerivedCategory.singleFunctors (ModuleCat.{u} V.A)
  -- `κ[-(n+1)] ≅ (κ[-1])[-n]`
  let e : (DerivedCategory.singleFunctor (ModuleCat.{u} V.A) (n + 1)).obj V.residueFieldModule ≅
      V.residueFieldShift⟦-n⟧ :=
    ((S.shiftIso (-n) (n + 1) 1 (by omega)).app V.residueFieldModule).symm ≪≫
      (shiftFunctor _ (-n)).mapIso
        ((S.shiftIso (-1) 1 0 (by omega)).app V.residueFieldModule).symm
  obtain ⟨h, hh⟩ := (shiftFunctor (DerivedCategory (ModuleCat.{u} V.A)) (-n)).map_surjective
    (e.inv ≫ g)
  have h0 : h = 0 := V.hom_residueFieldShift_derivedGlobalSections_eq_zero h
  have : e.inv ≫ g = 0 := by rw [← hh, h0, Functor.map_zero]
  simpa using congrArg (e.hom ≫ ·) this

end VanishingSituation

end AlgebraicGeometry

end
