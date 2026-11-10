module

public import StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapSpreadingOut
public import StacksFrontier.RingTheory.Flat.DevissageLocalizeAtPrime

/-!
# Injectivity of a free map from the generic points of all the fibres

Let `R → S` be a flat ring map of finite presentation with geometrically integral fibres, let
`N` be a finite `S`-module and let `alpha : S^{⊕ n} → N`. For a prime `r ⊆ R` write
`p_r = rS` for the generic point of the fibre over `r`. If, for *every* prime `r` of `R`, the
map `alpha` is injective over the residue field of `p_r` and the localization `N_{p_r}` is flat
over `R`, then `alpha` is injective — on the nose, not merely after a localization.

This is the step that turns the fibrewise information supplied by Stacks 05IA into a global
statement, and it is the shape in which the proof of the first assertion of Stacks 05MS — the
fpqc sheaf property of the generic-rank functor — consumes that tag: there the source builds a
surjection `𝒪_U^{⊕ p} → ℱ_U` on an affine open `U` of the base change which is an isomorphism at
the generic point of every fibre of `U → T`, and concludes that it is an isomorphism.

## Main results

* `Module.injective_localizedMap_under_of_flat_localizedModule`: **Stacks 05IA (1) ⟹ (4)**, the
  composite of the universal injectivity of `alpha_𝔯` with the passage from universal
  injectivity to injectivity.
* `Module.injective_of_forall_flat_localizedModule_genericFibre`: injectivity of `alpha` itself,
  from the fibrewise hypotheses at every prime of `R`.
* `Module.bijective_of_forall_flat_localizedModule_genericFibre`: the same with `alpha` assumed
  surjective, so that it is an isomorphism.

## Implementation notes

The source's conditions are localizations of `alpha` at multiplicative subsets of `R`, following
`StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapSpreadingOut`; nothing here is
stated over a local base, so no comparison of `S` with `S_𝔯` as an `R`-algebra is needed.

Only `Module.Finite S N` is assumed. This matters for the intended application: the module of
Stacks 05MP is of finite type and *not* of finite presentation, which is exactly why the proof of
Stacks 05MS cannot spread a free stalk out by Stacks 080Q and uses Stacks 05I3 instead. The two
results of `FreeMapSpreadingOut` used below,
`Module.universallyInjective_localizedMap_of_flat_localizedModule` and
`Module.injective_localizedMap_of_universallyInjective_localizedMap`, both carry only finiteness.

The passage from "injective after localizing at every prime of `R`" to "injective" is run on the
annihilator ideal of a single element of the kernel: an element killed in every localization
`(S^{⊕ n})_𝔯` is killed by some element outside `𝔯`, so its annihilator in `R` lies in no maximal
ideal and is therefore the unit ideal.

The hypotheses are stated with `Ideal.map (algebraMap R S) r` rather than with a prime `q` of `S`
lying over `r`, and the single application of the spreading out is made at `q = rS` itself, whose
contraction is `r` by `Ideal.comap_map_of_geometricallyIrreducible`. Phrasing the auxiliary
statement in terms of `q.under R` throughout — rather than rewriting `q.under R` to `r` — avoids
rewriting under the `Ideal.IsPrime` instance arguments of `Ideal.primeCompl` and
`Ideal.ResidueField`.

## References

* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
* [Stacks Project, Tag 05MS](https://stacks.math.columbia.edu/tag/05MS)
-/

@[expose] public section

open AlgebraicGeometry CommRingCat
open Stacks.UniversalInjectivity.LocalizationCriteria
open scoped TensorProduct

universe u w

namespace Module

/-- **Stacks Project, Tag 05IA, the implication (1) ⟹ (4).** If `N_𝔮` is flat over `R` and
`alpha` is injective over the residue field of the generic point of the fibre through `𝔮`, then
`alpha_𝔯` is injective, `𝔯` being the contraction of `𝔮`.

This is `Module.universallyInjective_localizedMap_of_flat_localizedModule` followed by
`Module.injective_localizedMap_of_universallyInjective_localizedMap`. -/
public theorem injective_localizedMap_under_of_flat_localizedModule
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (q : Ideal S) [q.IsPrime]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (halpha : letI := Ideal.isPrime_map_of_geometricallyIntegral R S (q.under R)
      Function.Injective (alpha.rTensor
        (Ideal.map (algebraMap R S) (q.under R)).ResidueField))
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Function.Injective
      (LocalizedModule.map (q.under R).primeCompl (alpha.restrictScalars R)) :=
  Module.injective_localizedMap_of_universallyInjective_localizedMap R S (q.under R) N n alpha
    (fun Q _ _ => Module.universallyInjective_localizedMap_of_flat_localizedModule R S q N n
      alpha halpha hflat Q)

/-- **A free map which is an isomorphism at the generic point of every fibre is injective.**

Let `R → S` be flat of finite presentation with geometrically integral fibres and let `N` be a
finite `S`-module. If for every prime `r` of `R` the map `alpha` is injective over the residue
field of the generic point `rS` of the fibre over `r`, and the localization of `N` there is flat
over `R`, then `alpha` is injective.

For each prime the two hypotheses give injectivity of `alpha_𝔯` by Stacks 05IA; an element of
the kernel of `alpha` is therefore killed by an element of `R` outside `𝔯`, so its annihilator is
contained in no maximal ideal of `R` and hence contains `1`. -/
public theorem injective_of_forall_flat_localizedModule_genericFibre
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (halpha : ∀ (r : Ideal R) (_ : r.IsPrime),
      letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Function.Injective (alpha.rTensor (Ideal.map (algebraMap R S) r).ResidueField))
    (hflat : ∀ (r : Ideal R) (_ : r.IsPrime),
      letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Module.Flat R (LocalizedModule (Ideal.map (algebraMap R S) r).primeCompl N)) :
    Function.Injective alpha := by
  classical
  refine (injective_iff_map_eq_zero alpha).mpr fun x hx => ?_
  set I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R (Fin n → S) x)
  have hmem : ∀ r : R, r ∈ I ↔ r • x = 0 := fun _ => Iff.rfl
  have hItop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    have hmp : m.IsPrime := hm.isPrime
    have hq : (Ideal.map (algebraMap R S) m).IsPrime :=
      Ideal.isPrime_map_of_geometricallyIntegral R S m
    set q : Ideal S := Ideal.map (algebraMap R S) m with hqdef
    have hunder : q.under R = m := Ideal.comap_map_of_geometricallyIrreducible R S m
    have hinj := injective_localizedMap_under_of_flat_localizedModule R S q N n alpha
      (halpha (q.under R) inferInstance) (hflat m hmp)
    have h0 : (LocalizedModule.map (q.under R).primeCompl (alpha.restrictScalars R))
        (LocalizedModule.mk x 1) = 0 := by
      rw [LocalizedModule.map_mk]
      change LocalizedModule.mk (alpha x) 1 = 0
      rw [hx]
      simp
    have hx0 : (LocalizedModule.mkLinearMap (q.under R).primeCompl (Fin n → S)) x = 0 := by
      refine hinj ?_
      rw [map_zero]
      exact h0
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (q.under R).primeCompl
      (LocalizedModule.mkLinearMap (q.under R).primeCompl (Fin n → S))).mp hx0
    exact s.2 (hunder.ge (hIm ((hmem _).2 hs)))
  simpa using (hmem 1).1 (hItop ▸ Submodule.mem_top)

/-- **A surjective free map which is an isomorphism at the generic point of every fibre is
bijective.** This is `Module.injective_of_forall_flat_localizedModule_genericFibre` together with
the assumed surjectivity. -/
public theorem bijective_of_forall_flat_localizedModule_genericFibre
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]
    (N : Type w) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] (n : ℕ) (alpha : (Fin n → S) →ₗ[S] N)
    (halpha : ∀ (r : Ideal R) (_ : r.IsPrime),
      letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Function.Injective (alpha.rTensor (Ideal.map (algebraMap R S) r).ResidueField))
    (hflat : ∀ (r : Ideal R) (_ : r.IsPrime),
      letI := Ideal.isPrime_map_of_geometricallyIntegral R S r
      Module.Flat R (LocalizedModule (Ideal.map (algebraMap R S) r).primeCompl N))
    (hsurj : Function.Surjective alpha) :
    Function.Bijective alpha :=
  ⟨injective_of_forall_flat_localizedModule_genericFibre R S N n alpha halpha hflat, hsurj⟩

end Module

end
