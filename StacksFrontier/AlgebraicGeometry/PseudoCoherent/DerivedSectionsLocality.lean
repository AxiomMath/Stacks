module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairDerivedSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairLocality

/-!
# Relative pseudo-coherence is local on compatible pairs of affine opens

Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `E` be an object of
`D_{QCoh}(𝒪_X)` and let `m` be an integer. Stacks 09VF asserts the equivalence of three
conditions: relative `m`-pseudo-coherence of `E`; relative `m`-pseudo-coherence of the complexes
of sections `RΓ(U, E)` over the members of *some* pair of nested affine open coverings; and the
same over *every* compatible pair of affine opens. This file proves that equivalence, in the
shape `AlgebraicGeometry.DerivedSectionsPseudoCoherentComparison'`, for those `E` whose
restriction to every affine open `U` is the complex of quasi-coherent sheaves attached to
`RΓ(U, E)`.

## Main definitions

* `AlgebraicGeometry.AffineDerivedSectionsPresentation`: on every affine open `U` the restriction
  `E|_U` is the complex of quasi-coherent sheaves attached to the object `RΓ(U, E)` of
  `D(Γ(X, U))`.

## Main results

* `AlgebraicGeometry.AffineDerivedSectionsPresentation.isPseudoCoherentFromOnAffinePair_iff`: at
  one compatible pair of affine opens, the local condition of Stacks 09UI for `E` is relative
  `m`-pseudo-coherence of `RΓ(U, E)` over `Γ(S, V)`.
* `AlgebraicGeometry.derivedSectionsPseudoCoherentComparison'_of_affinePresentation`: granted
  `AlgebraicGeometry.AffineDerivedSectionsPresentation`, the three conditions of Stacks 09VF are
  equivalent.

## References

* [The Stacks Project, Lemma 36.61.8 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.3.5 (06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}}

/-- **Affine presentation by derived sections.** On every affine open `U` of `X` the restriction
`E|_U` is the complex of quasi-coherent sheaves attached to an object `K` of `D(Γ(X, U))`,
transported from `Spec Γ(X, U)` to `U` along `AlgebraicGeometry.IsAffineOpen.isoSpec`, and `K` is
the complex of derived sections `RΓ(U, E)`. -/
public abbrev AffineDerivedSectionsPresentation (E : DerivedCategory X.Modules) : Prop :=
  ∀ (U : X.Opens) (hU : IsAffineOpen U),
    ∃ K : DerivedCategory (ModuleCat.{u} Γ(X, U)),
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E ≅
          (Scheme.Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.obj
            ((tilde.functor Γ(X, U)).mapDerivedCategory.obj K)) ∧
        Nonempty (K ≅ (derivedSectionsUnbounded X U).obj E)

/-- **Relative pseudo-coherence at one affine pair.** For `f : X ⟶ S` locally of finite type, an
object `E` of `D(𝒪_X)` presented on every affine open as in
`AlgebraicGeometry.AffineDerivedSectionsPresentation`, and a compatible pair of affine opens
`U ⊆ f ⁻¹ᵁ V`, the local condition of Stacks 09UI for `E` at that pair holds if and only if the
complex of sections `RΓ(U, E)` is `m`-pseudo-coherent relative to `Γ(S, V)`. -/
public theorem AffineDerivedSectionsPresentation.isPseudoCoherentFromOnAffinePair_iff
    {E : DerivedCategory X.Modules} (hpres : AffineDerivedSectionsPresentation E) (f : X ⟶ S)
    [LocallyOfFiniteType f] (m : ℤ) {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens}
    (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) :
    f.IsPseudoCoherentFromOnAffinePair E m ⟨U, hU⟩ ⟨V, hV⟩ e ↔
      f.DerivedSectionsPseudoCoherentOn' E m hU hV e := by
  obtain ⟨K, ⟨hEK⟩, ⟨hKΓ⟩⟩ := hpres U hU
  exact isPseudoCoherentFromOnAffinePair_iff_derivedSectionsPseudoCoherentOn' f E m hU hV e K
    hEK hKΓ

/-- **Relative pseudo-coherence is detected on affine opens, granted an affine presentation by
derived sections.** For `f : X ⟶ S` locally of finite type, `E` an object of the derived category
of `𝒪_X`-modules all of whose cohomology sheaves are quasi-coherent, and `m` an integer, the
following are equivalent:

1. `E` is `m`-pseudo-coherent relative to `S`;
2. there are an affine open covering of `S` and, over each of its members `V i`, an affine open
   covering of `f ⁻¹ᵁ V i` such that `RΓ(U, E)` is `m`-pseudo-coherent relative to `Γ(S, V i)`
   for every member `U` of the latter;
3. `RΓ(U, E)` is `m`-pseudo-coherent relative to `Γ(S, V)` for every compatible pair of affine
   opens `U ⊆ f ⁻¹ᵁ V`.

The derived sections are the unbounded ones, so no boundedness hypothesis is imposed on `E`. -/
public theorem derivedSectionsPseudoCoherentComparison'_of_affinePresentation (f : X ⟶ S)
    [LocallyOfFiniteType f] (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (hpres : AffineDerivedSectionsPresentation E) (m : ℤ) :
    DerivedSectionsPseudoCoherentComparison' f E hE m := by
  tfae_have 1 → 3 := fun h U hU V hV e ↦
    (hpres.isPseudoCoherentFromOnAffinePair_iff f m hU hV e).1
      ((Scheme.Hom.isPseudoCoherentFrom_iff_forall_affinePair f E m).1 h ⟨U, hU⟩ ⟨V, hV⟩ e)
  tfae_have 3 → 2 := exists_affineCover_derivedSectionsPseudoCoherentOn' f E m
  tfae_have 2 → 1 := by
    rintro ⟨ι, V, hVtop, hcov⟩
    refine ⟨ι, V, hVtop, fun i ↦ ?_⟩
    obtain ⟨κ, U, hUtop, hmem⟩ := hcov i
    refine ⟨κ, U, hUtop, fun j ↦ ?_⟩
    obtain ⟨hle, hpc⟩ := hmem j
    exact ⟨hle, (hpres.isPseudoCoherentFromOnAffinePair_iff f m (U j).2 (V i).2 hle).2 hpc⟩
  tfae_finish

end AlgebraicGeometry

end
