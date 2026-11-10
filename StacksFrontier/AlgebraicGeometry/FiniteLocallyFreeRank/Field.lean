module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module

/-!
# Finite local freeness of a given rank over a field, and the empty source

A module with a basis indexed by `Fin r` is finite locally free of rank `r`: the trivial covering
`{1}` of the ring already trivialises it. Over a field the converse holds in the strong form that
finite local freeness of rank `r` is exactly finiteness together with dimension `r`, because a
finite-dimensional vector space is free and the dimension can be read off any trivialisation.

Two consequences for morphisms of schemes with affine target are recorded: the rank of a morphism
to the spectrum of a field is the dimension of the ring of global sections of its source, and a
morphism with empty source is finite locally free of rank zero.

## Main results

* `Module.isFiniteLocallyFreeOfRank_of_basis`: a basis indexed by `Fin r` makes a module finite
  locally free of rank `r`.
* `Module.IsFiniteLocallyFreeOfRank.finite`: a finite locally free module is finite.
* `Module.isFiniteLocallyFreeOfRank_iff_finrank_eq`: over a field, finite local freeness of rank
  `r` is finiteness together with dimension `r`.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq`: the same statement for a
  morphism to the spectrum of a field, read off the ring of global sections of the source.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_zero_of_isEmpty`: a morphism to an affine scheme
  whose source is empty is finite locally free of rank zero.

## Implementation notes

The trivialisation by `{1}` requires identifying the localisation of a module at the powers of
`1` with the module itself. This is done through
`Module.bijective_mkLinearMap_of_le_isUnitSubmonoid`, which holds for any submonoid consisting of
units, together with `IsLocalization.atUnits` on the ring side and `Module.Basis.mapCoeffs` to
move the coefficients across.

The dimension statements over a field are proved by localising at one nonzero member of a
trivialising family: the powers of a nonzero element of a field are nonzerodivisors, so the
localisation changes neither the dimension of the ring nor that of the module.

## References

* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

namespace Module

/-- Localising a module at a submonoid of units changes nothing: the canonical map to the
localised module is bijective. -/
theorem bijective_mkLinearMap_of_le_isUnitSubmonoid {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] (S : Submonoid R) (hS : S ≤ IsUnit.submonoid R) :
    Function.Bijective (LocalizedModule.mkLinearMap S M) := by
  constructor
  · intro a b hab
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply,
      LocalizedModule.mk_eq] at hab
    obtain ⟨u, hu⟩ := hab
    obtain ⟨w, hw⟩ := hS u.2
    have h : ((w : R)) • a = ((w : R)) • b := by
      rw [hw]; simpa only [one_smul, Submonoid.smul_def] using hu
    simpa [smul_smul] using congrArg ((↑w⁻¹ : R) • ·) h
  · intro x
    induction x using LocalizedModule.induction_on with
    | _ m s =>
      obtain ⟨w, hw⟩ := hS s.2
      refine ⟨(↑w⁻¹ : R) • m, ?_⟩
      rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      change (1 : R) • ((s : R) • ((↑w⁻¹ : R) • m)) = (1 : R) • ((1 : ↥S) : R) • m
      rw [← hw]
      simp [smul_smul]

/-- A module with a basis indexed by `Fin r` is finite locally free of rank `r`: the covering
family consisting of `1` alone trivialises it. -/
theorem isFiniteLocallyFreeOfRank_of_basis {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] {r : ℕ} (b : Basis (Fin r) R M) :
    Module.IsFiniteLocallyFreeOfRank R M r := by
  have hS : Submonoid.powers (1 : R) ≤ IsUnit.submonoid R := by
    rintro x ⟨n, rfl⟩; simp
  refine ⟨PUnit.{u + 1}, fun _ ↦ 1, by simp, fun _ ↦ ?_⟩
  let e : M ≃ₗ[R] LocalizedModule (Submonoid.powers (1 : R)) M :=
    LinearEquiv.ofBijective _ (bijective_mkLinearMap_of_le_isUnitSubmonoid _ hS)
  let ea : R ≃ₐ[R] Localization.Away (1 : R) :=
    IsLocalization.atUnits R (Submonoid.powers (1 : R)) hS
  refine ⟨(b.map e).mapCoeffs ea.toRingEquiv fun c x ↦ ?_⟩
  change ea c • x = c • x
  rw [show ea c = algebraMap R (Localization.Away (1 : R)) c from rfl, algebraMap_smul]

/-- A finite locally free module of rank `r` is a finite module. -/
theorem IsFiniteLocallyFreeOfRank.finite {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
    [Module R M] {r : ℕ} (h : Module.IsFiniteLocallyFreeOfRank R M r) : Module.Finite R M := by
  obtain ⟨ι, f, hspan, hbasis⟩ := h
  refine Module.Finite.of_localizationSpan (Set.range f) hspan ?_
  rintro ⟨g, ⟨i, rfl⟩⟩
  exact Module.Finite.of_basis (hbasis i).some

/-- Over a field, a finite locally free module of rank `r` has dimension `r`. -/
theorem IsFiniteLocallyFreeOfRank.finrank_eq {K : Type u} [Field K] {M : Type v} [AddCommGroup M]
    [Module K M] {r : ℕ} (h : Module.IsFiniteLocallyFreeOfRank K M r) :
    Module.finrank K M = r := by
  obtain ⟨ι, f, hspan, hbasis⟩ := h
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra! hn
    exact top_ne_bot (hspan.symm.trans (Ideal.span_eq_bot.mpr (by rintro x ⟨i, rfl⟩; exact hn i)))
  have hp : Submonoid.powers (f i) ≤ nonZeroDivisors K :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hi
  have : Nontrivial (Localization.Away (f i)) :=
    (IsLocalization.injective (Localization.Away (f i)) hp).nontrivial
  have h₁ : Module.finrank (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) M) = r := by
    simpa using Module.finrank_eq_card_basis (hbasis i).some
  have h₂ : Module.finrank K (LocalizedModule (Submonoid.powers (f i)) M) =
      Module.finrank K M :=
    IsLocalizedModule.finrank_eq (Submonoid.powers (f i)) (LocalizedModule.mkLinearMap _ M) hp
  have h₃ : Module.finrank (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) M) =
      Module.finrank K (LocalizedModule (Submonoid.powers (f i)) M) :=
    IsLocalization.finrank_eq (Localization.Away (f i)) (Submonoid.powers (f i)) hp
  exact h₂.symm.trans (h₃.symm.trans h₁)

/-- Over a field, a module is finite locally free of rank `r` exactly when it is finite of
dimension `r`. -/
theorem isFiniteLocallyFreeOfRank_iff_finrank_eq {K : Type u} [Field K] (M : Type v)
    [AddCommGroup M] [Module K M] (r : ℕ) :
    Module.IsFiniteLocallyFreeOfRank K M r ↔ Module.Finite K M ∧ Module.finrank K M = r := by
  refine ⟨fun h ↦ ⟨h.finite, h.finrank_eq⟩, fun ⟨_, hrank⟩ ↦ ?_⟩
  exact isFiniteLocallyFreeOfRank_of_basis (Module.finBasisOfFinrankEq K M hrank)

end Module

namespace Stacks.Morphisms

/-- A morphism to the spectrum of a field is finite locally free of rank `r` exactly when it is
affine and the ring of global sections of its source has dimension `r` over the field.

This is not the same statement as
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq`, which characterises finite
local freeness of rank `r` for a finite flat morphism to an arbitrary base by the rank function
`AlgebraicGeometry.Scheme.Hom.finrank`. Here the target is the spectrum of a field, no
finiteness is assumed, and the `finrank` is that of the global sections. -/
theorem isFiniteLocallyFreeOfRank_iff_finrank_sections_eq {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (r : ℕ) :
    letI := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
    IsFiniteLocallyFreeOfRank f r ↔
      IsAffineHom f ∧ Module.Finite K ↑Γ(X, ⊤) ∧ Module.finrank K ↑Γ(X, ⊤) = r := by
  let _ : Algebra K ↑Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  constructor
  · intro h
    exact ⟨h.toIsAffineHom, (Module.isFiniteLocallyFreeOfRank_iff_finrank_eq _ r).mp
      ((sheafOfModules_isFiniteLocallyFreeOfRank_iff_module f r).mp
        h.toIsFiniteLocallyFreeOfRank)⟩
  · rintro ⟨haff, hfin, hrank⟩
    rw [isFiniteLocallyFreeOfRank_iff, and_iff_right haff]
    exact (sheafOfModules_isFiniteLocallyFreeOfRank_iff_module f r).mpr
      ((Module.isFiniteLocallyFreeOfRank_iff_finrank_eq _ r).mpr ⟨hfin, hrank⟩)

/-- A morphism to an affine scheme whose source is empty is finite locally free of rank zero. -/
theorem isFiniteLocallyFreeOfRank_zero_of_isEmpty {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [IsEmpty X] : IsFiniteLocallyFreeOfRank f 0 := by
  have hsub : Subsingleton ↑Γ(X, ⊤) :=
    PrimeSpectrum.isEmpty_iff_subsingleton.mp ⟨fun x ↦ ‹IsEmpty X›.elim (X.isoSpec.inv x)⟩
  let _ : Algebra ↑Γ(S, ⊤) ↑Γ(X, ⊤) := f.appTop.hom.toAlgebra
  rw [isFiniteLocallyFreeOfRank_iff_module_of_isAffine f 0 rfl]
  exact Module.isFiniteLocallyFreeOfRank_of_basis (Module.Basis.empty ↑Γ(X, ⊤))

end Stacks.Morphisms

end
