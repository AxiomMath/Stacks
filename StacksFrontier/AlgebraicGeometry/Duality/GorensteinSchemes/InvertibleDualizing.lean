module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StructureSheafDualizing
public import StacksFrontier.RingTheory.Dualizing.GorensteinLocallyShiftedUnit

/-!
# Gorenstein schemes and invertibility of the dualizing complex

Let `X` be a locally Noetherian scheme carrying a dualizing complex `ω^•`. [Stacks, Tag 0BFQ]
clause (1)(a) says that `X` is Gorenstein exactly when `ω^•` is an invertible object of
`D(𝒪_X)`, and proves it by reducing to the affine case, which is
[Stacks, Tag 0DW9] clause (1)(a).

This file states and proves that reduction as the equivalence itself. Invertibility of an object
of `D(𝒪_X)` is a Zariski-local condition, and by the definition of
`Stacks.Duality.IsDualizingComplex` the restriction of `ω^•` to an affine open `U ⊆ X` is the
associated sheaf of a dualizing complex over `Γ(X, U)`; so the condition to be matched against
Gorensteinness of `X` is that each of those models be an invertible object of `D(Γ(X, U))`, which
by [Stacks, Tag 0FNT] is the same as its being, over a principal neighbourhood of every prime, a
shift of the localized ring — an invertible module in one degree, locally on `U`.

## Main definitions

* `Stacks.Duality.HasInvertibleDualizingModelOn` — the local condition at one affine open: `ω^•`
  restricted to `U` is the associated sheaf of a dualizing complex over `Γ(X, U)` which is
  locally a shifted unit.

## Main results

* `Stacks.Duality.isGorensteinLocalRing_stalk_of_isGorensteinRing_sections` — if the ring of
  sections at an affine open is Gorenstein then so is every local ring at a point of that open.
* `Stacks.Duality.isGorenstein_iff_hasInvertibleDualizingModelOn` — **[Stacks, Tag 0BFQ],
  clause (1)(a)**, in the locally shifted unit form.
* `Stacks.Duality.isGorenstein_iff_isInvertible_dualizingModel` — the same, with the models read
  as invertible objects of `D(Γ(X, U))` for the canonical derived tensor product of
  [Stacks, Tag 0FNQ].

## Implementation notes

**What the two statements below say about `D(𝒪_X)`.** The source's condition is that `ω^•` be an
invertible object of `D(𝒪_X)`; the condition proved here is that every one of its affine-local
models be an invertible object of the derived category of the corresponding ring of sections. The
two conditions agree, because invertibility is local and because derived sheafification
`D(Γ(X, U)) ⥤ D_QCoh(𝒪_U)` is an equivalence ([Stacks, Tag 06Z0],
`AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence`); the identification itself is not
made here, and neither is the fully geometric form — that every point has an affine open
neighbourhood `V` with `ω^•|_V ≅ 𝒪_V[n]`. Passing to the geometric form in the Gorenstein
direction needs the derived comparison `(ω^~)|_{D(f)} ≅ (ω_f)^~` between restriction to a
standard open of `Spec Γ(X, U)` and localization of the model, the same input as
[Stacks, Tag 0A86]. In the other direction it needs full faithfulness of
`(AlgebraicGeometry.tilde.functor R).mapDerivedCategory`, which is
`AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful`.

**Where each direction comes from.** If `X` is Gorenstein then `Γ(X, U)` is a Gorenstein ring by
`Stacks.Duality.isGorensteinRing_sections`, so any dualizing complex over it is locally a shifted
unit by `Dualizing.isGorensteinRing_iff_isLocallyShiftedUnit`. Conversely a model that is locally
a shifted unit makes `Γ(X, U)` Gorenstein by the same equivalence, and Gorensteinness of the
stalk at a point `x ∈ U` follows because that stalk is the localization of `Γ(X, U)` at the prime
`x` defines; the affine opens form a basis, so this covers every point of `X`.

The derived category of `X.Modules` is an instance *argument*, matching
`Stacks.Duality.IsDualizingComplex`, so the results read at whatever model the caller works in.
The two derived categories that `Stacks.Duality.HasDualizingModelOn` chooses internally at
`HasDerivedCategory.standard` must be reintroduced by any proof that reads or builds it, which is
what the instance-introducing `let`s below do; `Dualizing.IsGorensteinRing` and
`DerivedCategory.Invertible.IsLocallyShiftedUnit` are stated at the same model.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u w

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- An affine open `U` of a locally Noetherian scheme carries an *invertible dualizing model* of
`K ∈ D(𝒪_X)` when it carries a dualizing model (`Stacks.Duality.HasDualizingModelOn`) which is
moreover locally a shifted unit, that is, which is over a principal neighbourhood of every prime
of `Γ(X, U)` a shift of the localized ring.

By [Stacks, Tag 0FNT] the extra condition says exactly that the model is an invertible object of
`D(Γ(X, U))`. -/
public def HasInvertibleDualizingModelOn (K : DerivedCategory X.Modules) (U : X.Opens)
    (hU : IsAffineOpen U) : Prop :=
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := HasDerivedCategory.standard U.toScheme.Modules
  letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)),
    Dualizing.IsDualizingComplex ω ∧
      DerivedCategory.Invertible.IsLocallyShiftedUnit ω ∧
        Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
          (tilde.functor Γ(X, U) ⋙
            Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)

/-- Carrying an invertible dualizing model is stronger than carrying a dualizing model. -/
public theorem hasDualizingModelOn_of_hasInvertibleDualizingModelOn
    {K : DerivedCategory X.Modules} {U : X.Opens} {hU : IsAffineOpen U}
    (h : HasInvertibleDualizingModelOn K U hU) : HasDualizingModelOn K U hU := by
  obtain ⟨ω, hω, -, hiso⟩ := h
  exact ⟨ω, hω, hiso⟩

omit [HasDerivedCategory X.Modules] in
/-- If the ring of sections at an affine open `U` of a scheme is a Gorenstein ring, then the local
ring at every point of `U` is Gorenstein: that local ring is the localization of `Γ(X, U)` at the
prime the point defines, by `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`. -/
public theorem isGorensteinLocalRing_stalk_of_isGorensteinRing_sections {U : X.Opens}
    (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)]
    (h : Dualizing.IsGorensteinRing Γ(X, U)) (x : U) :
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x.1) := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x.1) :=
    X.presheaf.algebra_section_stalk ⟨x.1, x.2⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x.1) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  exact (isGorensteinLocalRing_ringEquiv_iff
    (IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl
      (X.presheaf.stalk x.1)
      (Localization.AtPrime (hU.primeIdealOf x).asIdeal)).toRingEquiv).mpr
    (h (hU.primeIdealOf x).asIdeal)

/-- A locally Noetherian scheme carrying a dualizing complex is Gorenstein exactly when, at every
affine open, that complex is the associated sheaf of a dualizing complex over the ring of sections
which is locally a shifted unit — an invertible module in a single degree, locally on the affine
open.

By [Stacks, Tag 0FNT] the condition on the model says that it is an invertible object of
`D(Γ(X, U))`; see `Stacks.Duality.isGorenstein_iff_isInvertible_dualizingModel`. -/
@[stacks 0BFQ "(1)(a): Gorenstein iff the dualizing complex is locally a shift of the structure \
ring, read at the affine-local models"]
public theorem isGorenstein_iff_hasInvertibleDualizingModelOn (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) :
    AlgebraicGeometry.IsGorenstein X ↔
      ∀ (U : X.Opens) (hU : IsAffineOpen U), HasInvertibleDualizingModelOn K U hU := by
  constructor
  · intro hG U hU
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let := HasDerivedCategory.standard U.toScheme.Modules
    let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
    obtain ⟨ω, hω, hiso⟩ := hK U hU
    exact ⟨ω, hω,
      (Dualizing.isGorensteinRing_iff_isLocallyShiftedUnit ω hω).mp
        (isGorensteinRing_sections U hU), hiso⟩
  · intro h
    refine { toIsLocallyNoetherian := inferInstance, isGorensteinLocalRing := fun x => ?_ }
    obtain ⟨-, ⟨V, hVmem, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    let U : X.Opens := V
    have hU : IsAffineOpen U := hVmem
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let := HasDerivedCategory.standard U.toScheme.Modules
    let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
    obtain ⟨ω, hω, hinv, -⟩ := h U hU
    exact isGorensteinLocalRing_stalk_of_isGorensteinRing_sections hU
      ((Dualizing.isGorensteinRing_iff_isLocallyShiftedUnit ω hω).mpr hinv) ⟨x, hxV⟩

/-- A locally Noetherian scheme carrying a dualizing complex is Gorenstein exactly when, at every
affine open, that complex is the associated sheaf of a dualizing complex over the ring of sections
which is an invertible object of its derived category, for the canonical derived tensor product of
[Stacks, Tag 0FNQ].

This is `Stacks.Duality.isGorenstein_iff_hasInvertibleDualizingModelOn` rewritten through
[Stacks, Tag 0FNT]. -/
@[stacks 0BFQ "(1)(a): Gorenstein iff the dualizing complex is an invertible object, read at the \
affine-local models"]
public theorem isGorenstein_iff_isInvertible_dualizingModel (K : DerivedCategory X.Modules)
    (hK : IsDualizingComplex K) :
    AlgebraicGeometry.IsGorenstein X ↔
      ∀ (U : X.Opens) (hU : IsAffineOpen U),
        letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
        letI := HasDerivedCategory.standard U.toScheme.Modules
        letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
        letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
          Γ(X, U)).choose
        ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)),
          Dualizing.IsDualizingComplex ω ∧
            MonoidalCategory.IsInvertible ω ∧
              Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
                (tilde.functor Γ(X, U) ⋙
                  Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω) := by
  refine (isGorenstein_iff_hasInvertibleDualizingModelOn K hK).trans
    (forall_congr' fun U => forall_congr' fun hU => exists_congr fun ω =>
      and_congr_right fun _ => and_congr_left fun _ =>
        (DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit ω).1.symm)

end Stacks.Duality

end
