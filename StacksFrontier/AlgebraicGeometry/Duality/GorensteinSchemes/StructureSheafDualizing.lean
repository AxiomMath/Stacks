module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.RingTheory.Dualizing.GorensteinRingDualizing
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport

/-!
# A Gorenstein scheme has a dualizing complex only if its structure sheaf is one

On a Gorenstein scheme a dualizing complex exists exactly when the structure sheaf, placed in
degree zero, is already a dualizing complex.

## Main results

* `Stacks.Duality.isGorensteinRing_sections` — the ring of sections at an affine open of a
  Gorenstein scheme is a Gorenstein ring.
* `Stacks.Duality.exists_isDualizingComplex_iff_unit` — a Gorenstein scheme has a dualizing
  complex if and only if its structure sheaf, placed in degree zero, is one.

## Implementation notes

One direction is immediate. For the other, the condition to be checked at an affine open `U` is
`Stacks.Duality.HasDualizingModelOn`, and the model used is `Γ(X, U)` itself in degree zero: it
is a dualizing complex by [Stacks, Tag 0DW9 (2)] applied to the Gorenstein ring `Γ(X, U)`, whose
hypothesis that *some* dualizing complex exists over `Γ(X, U)` is supplied by the given dualizing
complex on `X`. The required isomorphism is then an identification of structure sheaves:
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso` says restriction along an open immersion takes
`𝒪_Y` to `𝒪_X`, `AlgebraicGeometry.tildeSelf` says the associated sheaf of `Γ(X, U)` is
`𝒪_{Spec Γ(X, U)}`, and `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` moves these
isomorphisms of sheaves through the degree-zero inclusion into the derived categories.

Gorensteinness of `Γ(X, U)` is checked at a prime `p` by transporting it from the point of `U`
that `p` corresponds to under the comparison isomorphism `U ≅ Spec Γ(X, U)`: the stalk there is
the localization at `p` by `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`, and
`Dualizing.isGorensteinLocalRing_of_ringEquiv` moves Gorensteinness across the comparison.

The derived category of `X.Modules` is an instance *argument*, matching
`Stacks.Duality.IsDualizingComplex`. The two derived categories that
`Stacks.Duality.HasDualizingModelOn` chooses internally at `HasDerivedCategory.standard` must be
reintroduced by any proof that reads or builds it, which is what the instance-introducing `let`s
below do.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace Stacks.Duality

variable {X : Scheme.{u}}

/-- The ring of sections at an affine open of a Gorenstein scheme is a Gorenstein ring. -/
public theorem isGorensteinRing_sections [AlgebraicGeometry.IsGorenstein X] (U : X.Opens)
    (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] :
    Dualizing.IsGorensteinRing Γ(X, U) := by
  intro p hp
  obtain ⟨y, hy⟩ : ∃ y : U, hU.primeIdealOf y = ⟨p, hp⟩ := by
    refine ⟨hU.isoSpec.inv.base ⟨p, hp⟩, ?_⟩
    show (hU.isoSpec.inv ≫ hU.isoSpec.hom).base _ = _
    rw [hU.isoSpec.inv_hom_id]
    rfl
  let : Algebra Γ(X, U) (X.presheaf.stalk y.1) :=
    X.presheaf.algebra_section_stalk ⟨y.1, y.2⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk y.1) p := by
    have h := hU.isLocalization_stalk y
    rwa [hy] at h
  exact Dualizing.isGorensteinLocalRing_of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (X.presheaf.stalk y.1)).toRingEquiv
    (AlgebraicGeometry.IsGorenstein.isGorensteinLocalRing y.1)

/-- A Gorenstein scheme has a dualizing complex if and only if its structure sheaf, placed in
degree zero, is a dualizing complex. -/
@[stacks 0BFQ "(2): a Gorenstein scheme has a dualizing complex iff its structure sheaf is one"]
public theorem exists_isDualizingComplex_iff_unit [AlgebraicGeometry.IsGorenstein X]
    [HasDerivedCategory.{w} X.Modules] :
    (∃ K : DerivedCategory X.Modules, IsDualizingComplex K) ↔
      IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  refine ⟨fun ⟨K, hK⟩ U hU => ?_, fun h => ⟨_, h⟩⟩
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  -- The model is `Γ(X, U)` in degree zero; it is dualizing by [Stacks, Tag 0DW9 (2)].
  obtain ⟨ω, hω, -⟩ := hK U hU
  refine ⟨(DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
    (ModuleCat.of Γ(X, U) Γ(X, U)),
    (Dualizing.exists_isDualizingComplex_iff_regularModule.{u, u} Γ(X, U)
      (isGorensteinRing_sections U hU)).mp ⟨ω, hω⟩, ⟨?_⟩⟩
  -- Both sides are the structure sheaf of `U` in degree zero.
  refine ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor U.toScheme.Modules 0).mapIso
      (Scheme.Modules.restrictUnitIso U.ι ≪≫
        (Scheme.Modules.restrictUnitIso hU.isoSpec.hom).symm ≪≫
        (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapIso
          (tildeSelf (R := Γ(X, U))).symm) ≪≫
    (((tilde.functor Γ(X, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategorySingleFunctor 0).app _).symm

end Stacks.Duality

end
