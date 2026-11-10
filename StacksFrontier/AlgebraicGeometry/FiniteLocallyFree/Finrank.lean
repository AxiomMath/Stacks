module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.RingTheory.Flat.LocallyFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.RingTheory.Norm.Projective

/-!
# Finite local freeness of a given rank and the rank function

A finite flat morphism of schemes has a rank function `AlgebraicGeometry.Scheme.Hom.finrank`,
sending a point of the target to the rank at that point of the direct image of the structure
sheaf. This file identifies being finite locally free of rank `r` with that rank function being
constantly `r`, which is the comparison left as a `TODO` in Mathlib's
`Mathlib/AlgebraicGeometry/Morphisms/FlatRank.lean`.

## Main results

* `Module.isFiniteLocallyFreeOfRank_of_rankAtStalk_eq`: a finite flat module whose rank at every
  stalk equals `r` is finite locally free of rank `r`.
* `Module.isFiniteLocallyFreeOfRank_iff_rankAtStalk_eq`: for a finite flat module, being finite
  locally free of rank `r` is having rank `r` at every stalk.
* `Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq`: a finite flat morphism of
  schemes is finite locally free of rank `r` exactly when its rank function is constantly `r`.

## Implementation notes

The module-level criterion is the engine: Mathlib's
`Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant` produces, around each prime, an
element away from which the module is free, and the rank of that free localisation is read off
the hypothesis through `Module.rankAtStalk_isBaseChange`. The localising elements obtained this
way generate the unit ideal because no maximal ideal can contain all of them, which is exactly
the covering family that `Module.IsFiniteLocallyFreeOfRank` asks for. The converse direction is
`Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank`, already available.

Passing to schemes is done in two steps. Over an affine target the statement is transported to
modules by `Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine`, with
`RingHom.finrank` as the intermediary: it is *by definition* the rank at stalks of the target
ring map, so no rewriting is needed to pass between the two, only a type ascription. Relating
`RingHom.finrank` of the global sections map to `AlgebraicGeometry.Scheme.Hom.finrank` uses the
cartesian square comparing a morphism of affine schemes with the spectrum of its global sections
map. The general case follows because being finite locally free of rank `r` is Zariski local at
the target and the rank function is compatible with base change.

No local finite presentation is needed: the module-level criterion only uses finiteness and
flatness.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Module

/-- A finite flat module whose rank at every stalk is `r` is finite locally free of rank `r`:
around each prime Mathlib's `Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant` gives an
element away from which the module is free, that free localisation has rank `r` because rank at
stalks is a base-change invariant, and the elements so obtained generate the unit ideal. -/
theorem isFiniteLocallyFreeOfRank_of_rankAtStalk_eq {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Flat R M] (r : ℕ)
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) :
    Module.IsFiniteLocallyFreeOfRank R M r := by
  classical
  have key : ∀ p : PrimeSpectrum R, ∃ a : R, a ∉ p.asIdeal ∧
      Nonempty (Module.Basis (Fin r) (Localization.Away a) (LocalizedModule.Away a M)) := by
    intro p
    obtain ⟨a, hap, hfree⟩ :=
      Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant M p.asIdeal
        (fun m _ => by rw [h, h])
    refine ⟨a, hap, ?_⟩
    let S := Localization.Away a
    have hpRange : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
      rw [PrimeSpectrum.localization_away_comap_range S a]
      exact (PrimeSpectrum.mem_basicOpen a p).2 hap
    obtain ⟨q, hq⟩ := hpRange
    have : Nontrivial S := not_subsingleton_iff_nontrivial.mp fun _ =>
      q.isPrime.ne_top (Subsingleton.elim _ _)
    have hfin : Module.finrank S (LocalizedModule.Away a M) = r := by
      have h1 : Module.rankAtStalk (R := S) (LocalizedModule.Away a M) q = r := by
        rw [Module.rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers a) M) q,
          hq, h]
      simpa using h1.symm ▸ (congrFun (Module.rankAtStalk_eq_finrank_of_free
        (R := S) (M := LocalizedModule.Away a M)) q).symm
    exact ⟨(Module.finBasis S (LocalizedModule.Away a M)).reindex (finCongr hfin)⟩
  choose a ha hb using key
  refine ⟨PrimeSpectrum R, a, ?_, hb⟩
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  exact ha ⟨m, hm.isPrime⟩ (hle (Ideal.subset_span ⟨⟨m, hm.isPrime⟩, rfl⟩))

/-- For a finite flat module, being finite locally free of rank `r` is the same as having rank
`r` at every stalk. -/
theorem isFiniteLocallyFreeOfRank_iff_rankAtStalk_eq {R M : Type u} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Flat R M] (r : ℕ) :
    Module.IsFiniteLocallyFreeOfRank R M r ↔ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r :=
  ⟨Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank r,
    Module.isFiniteLocallyFreeOfRank_of_rankAtStalk_eq r⟩

end Module

namespace Stacks.Morphisms

/-- For a finite flat morphism of affine schemes, the rank of the global sections map at a prime
of the target ring is the rank function of the morphism at the corresponding point. -/
private theorem ringHom_finrank_appTop_eq {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [Flat f] [IsFinite f] (p : PrimeSpectrum Γ(S, ⊤)) :
    f.appTop.hom.finrank p = f.finrank (S.isoSpec.inv.base p) := by
  have hpb : IsPullback X.isoSpec.inv (Spec.map f.appTop) f S.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by
      rw [← cancel_epi X.isoSpec.hom]
      simp only [Iso.hom_inv_id_assoc]
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun k ↦ k ≫ S.isoSpec.inv) (Scheme.isoSpec_hom_naturality f).symm⟩
  rw [← Scheme.Hom.finrank_SpecMap_eq_finrank f.finite_appTop f.flat_appTop]
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb p

/-- The affine-target case of the comparison between finite local freeness of rank `r` and the
rank function. -/
private theorem isFiniteLocallyFreeOfRank_iff_forall_finrank_eq_of_isAffine {X S : Scheme.{u}}
    [IsAffine S] (f : X ⟶ S) [IsFinite f] [Flat f] (r : ℕ) :
    IsFiniteLocallyFreeOfRank f r ↔ ∀ s : S, f.finrank s = r := by
  have _ : IsAffine X := isAffine_of_isAffineHom f
  let alg : Algebra ↑Γ(S, ⊤) ↑Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have halg : algebraMap ↑Γ(S, ⊤) ↑Γ(X, ⊤) = f.appTop.hom := RingHom.algebraMap_toAlgebra _
  have hfin : Module.Finite ↑Γ(S, ⊤) ↑Γ(X, ⊤) := f.finite_appTop
  have hflat : Module.Flat ↑Γ(S, ⊤) ↑Γ(X, ⊤) := f.flat_appTop
  rw [isFiniteLocallyFreeOfRank_iff_module_of_isAffine f r halg]
  refine ⟨fun h s => ?_, fun h => Module.isFiniteLocallyFreeOfRank_of_rankAtStalk_eq r fun p =>
    (ringHom_finrank_appTop_eq f p).trans (h _)⟩
  have h2 : f.appTop.hom.finrank (S.isoSpec.hom.base s) = r :=
    Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank r h (S.isoSpec.hom.base s)
  rw [ringHom_finrank_appTop_eq f (S.isoSpec.hom.base s)] at h2
  simpa using h2

/-- A finite flat morphism of schemes is finite locally free of rank `r` exactly when its rank
function `AlgebraicGeometry.Scheme.Hom.finrank` is constantly `r`. -/
theorem isFiniteLocallyFreeOfRank_iff_forall_finrank_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] [Flat f] (r : ℕ) :
    IsFiniteLocallyFreeOfRank f r ↔ ∀ s : S, f.finrank s = r := by
  rw [← IsFiniteLocallyFreeOfRank.property_iff,
    IsZariskiLocalAtTarget.iff_of_openCover (P := IsFiniteLocallyFreeOfRank.property.{u} r)
      S.affineCover]
  constructor
  · intro h s
    obtain ⟨y, hy⟩ := S.affineCover.covers s
    have h2 : IsFiniteLocallyFreeOfRank
        (pullback.snd f (S.affineCover.f (S.affineCover.idx s))) r := h _
    have h3 := (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq_of_isAffine _ r).mp h2 y
    rwa [Scheme.Hom.finrank_pullback_snd, hy] at h3
  · intro h i
    change IsFiniteLocallyFreeOfRank (pullback.snd f (S.affineCover.f i)) r
    refine (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq_of_isAffine _ r).mpr fun y => ?_
    rw [Scheme.Hom.finrank_pullback_snd]
    exact h _

end Stacks.Morphisms

end
