module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.FiniteModule
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# Reading local freeness of a localization off a finite locally free sheaf on an open

Let `A` be a ring, `M` an `A`-module and `U` an open of `Spec A`.  If the restriction `M̃|_U` is
a finite locally free sheaf, then for every `f` with `D(f) ⊆ U` the localization `M_f` is a
finite locally free `A_f`-module.

The point is the direction: finite local freeness of a *sheaf* on an open is a statement about
some cover of that open, while `Module.IsFiniteLocallyFree A_f M_f` is a statement about the
ring `A_f`; the passage between them is the identification of `M̃|_{D(f)}` with the sheaf
associated to `M_f` on `Spec A_f`.

## Main results

* `Module.isFiniteLocallyFree_localization_away_of_isFiniteLocallyFree_restrict` — the statement
  above, for an arbitrary open `U` and a basic open `D(f) ≤ U`.
* `Module.isFiniteLocallyFree_localization_away_of_mem_of_isFiniteLocallyFree_zeroLocusCompl` —
  its instance at `U = Spec A ∖ V(I)` and `f ∈ I`, which is the hypothesis `hM` of
  [Stacks, Tag 0BPY] as `Stacks.LocalCohomology`'s
  `localCohomologyWithSupportIn_finite_of_finiteLocallyFree_away`, and so also of the affine
  case of [Stacks, Tag 0BLT].

## Implementation notes

The proof restricts twice and then transports.  Restriction along the open immersion
`D(f) ⟶ U` preserves finite local freeness
(`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree.restrict`), and the two restrictions
compose to the restriction along `D(f) ⟶ Spec A` by `AlgebraicGeometry.Scheme.homOfLE_ι`.
Restriction along the isomorphism `AlgebraicGeometry.basicOpenIsoSpecAway`, which is an open
immersion, moves the result to `Spec A_f`, where
`bridge_N_iso` identifies it with the sheaf associated to `M_f`; the
sheaf-to-module dictionary `tilde_isFiniteLocallyFree_iff` ([Stacks, Tag 05JM]) finishes.

For the instance at `V(I)`: `f ∈ I` gives `V(I) ⊆ V(f)`, hence `D(f) ⊆ Spec A ∖ V(I)`, which is
the only thing the hypothesis `f ∈ I` is used for.

## References

* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
* [Stacks Project, Tag 0BPY](https://stacks.math.columbia.edu/tag/0BPY)
* [Stacks Project, Tag 0BLT](https://stacks.math.columbia.edu/tag/0BLT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Module

/-- **Local freeness of a localization, read off a finite locally free sheaf on an open.** Let
`U` be an open of `Spec A` over which `M̃` restricts to a finite locally free sheaf, and let `f`
be such that `D(f) ≤ U`.  Then `M_f` is a finite locally free `A_f`-module.

Restriction along `D(f) ⟶ U` and then along `D(f) ≅ Spec A_f` carries the hypothesis to
`Spec A_f`, where `bridge_N_iso` identifies the sheaf with the one associated
to `M_f`. -/
public theorem isFiniteLocallyFree_localization_away_of_isFiniteLocallyFree_restrict
    {A : CommRingCat.{u}} (U : (Spec A).Opens) (M : ModuleCat.{u} A)
    (hU : Scheme.Modules.IsFiniteLocallyFree ((tilde M).restrict U.ι))
    (f : ToType A) (hf : specBasicOpen (ToType A) f ≤ U) :
    Module.IsFiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f (M : Type u)) := by
  have hbasic : Scheme.Modules.IsFiniteLocallyFree
      ((tilde M).restrict (specBasicOpen (ToType A) f).ι) :=
    Scheme.Modules.IsFiniteLocallyFree.of_iso
      (((Scheme.Modules.restrictFunctorComp ((Spec A).homOfLE hf) U.ι).app (tilde M)).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr ((Spec A).homOfLE_ι hf)).app (tilde M))
      (Scheme.Modules.IsFiniteLocallyFree.restrict ((Spec A).homOfLE hf) hU)
  let e := AlgebraicGeometry.basicOpenIsoSpecAway (R := A) f
  have : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso e.inv
  exact (tilde_isFiniteLocallyFree_iff (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) (M : Type u))).mp
    (Scheme.Modules.IsFiniteLocallyFree.of_iso (bridge_N_iso (ToType A) (M : Type u) f)
      (Scheme.Modules.IsFiniteLocallyFree.restrict e.inv hbasic))

/-- **The hypothesis of [Stacks, Tag 0BPY], read off a finite locally free sheaf on the
complement of a vanishing locus.** If `M̃` restricts to a finite locally free sheaf on
`Spec A ∖ V(I)` then `M_f` is a finite locally free `A_f`-module for every `f ∈ I`.

For `f ∈ I` the vanishing locus `V(I)` is contained in `V(f)`, so `D(f)` lies in the
complement of `V(I)`. -/
public theorem isFiniteLocallyFree_localization_away_of_mem_of_isFiniteLocallyFree_zeroLocusCompl
    {A : CommRingCat.{u}} (I : Ideal (ToType A)) (M : ModuleCat.{u} A)
    (hU : Scheme.Modules.IsFiniteLocallyFree ((tilde M).restrict (zeroLocusCompl I).ι))
    (f : ToType A) (hf : f ∈ I) :
    Module.IsFiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f (M : Type u)) := by
  refine isFiniteLocallyFree_localization_away_of_isFiniteLocallyFree_restrict _ M hU f ?_
  intro x hx
  change x ∈ (PrimeSpectrum.zeroLocus (I : Set (ToType A)))ᶜ
  intro hzero
  exact (PrimeSpectrum.mem_basicOpen f x).mp hx (hzero hf)

end Module

end
