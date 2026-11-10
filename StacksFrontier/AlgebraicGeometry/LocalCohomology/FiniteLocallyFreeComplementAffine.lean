module

public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.SchemeOpenSectionsDerived
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.FiniteModule
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LocalCohomologyFiniteness
public import StacksFrontier.RingTheory.LocalCohomology.FiniteLocallyFreeFiniteness
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.Module.LocallyFree.LocalizationAwayRestrict
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherence of the higher direct images along a punctured affine spectrum

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `X = Spec A`, `U = X ∖ V(I)` and
`j : U → X` the inclusion.  This file proves two things.

First, the equivalence of conditions (a) and (b) of clause (3) of [Stacks, Tag 0BK0]: for an
`A`-module `M` and `p ≥ 0`, the higher direct image `R^pj_*(M̃|_U)` is coherent exactly when the
`A`-module `H^p(U, M̃)` is finite.  By clause (1) of that tag every coherent `𝒪_U`-module is such
a restriction, so this is the clause as stated.

Second, the **affine case of [Stacks, Tag 0BLT]**: if `R^pj_*𝒪_U` is coherent for `0 ≤ p < n`
then so is `R^pj_*ℱ` for every finite locally free `𝒪_U`-module `ℱ`.

## Main results

* `Stacks.LocalCohomologySequence.moduleFinite_complementCohomologyBase_iff_isCoherent` —
  **[Stacks, Tag 0BK0] (3), (a) ⟺ (b).**
* `Stacks.LocalCohomologySequence.isCoherent_rightDerived_zeroLocusCompl_of_structureSheaf` — the
  affine case of [Stacks, Tag 0BLT].

## Implementation notes

**No `@[stacks 0BLT]` attribute is attached to anything here, and none may be.** Tag 0BLT is a
single-conclusion statement about an open subscheme of an arbitrary locally Noetherian scheme;
there is one clause, so there is no covering set to split and no sub-label that would describe
the affine case.  Attaching the tag to the statement below would be attaching it to a weakened
statement.  What is missing for the tag is recorded at the end of these notes.

The equivalence (a) ⟺ (b) is assembled from three pieces, none of which is new mathematics:

* `Stacks.Cohomology.SchemeOpenSections.derivedSectionsOnOpenIso`, which is [Stacks, Tag 01E1]
  (2) in the vocabulary of schemes — the cohomology of `U` computed by deriving the sections over
  `U` of sheaves on the ambient `X` agrees with the cohomology of the restriction on the open
  subscheme `U`, both read over `Γ(X, 𝒪_X)`;
* `Stacks.LocalCohomologySequence.complementCohomology`, which is *definitionally* the derived
  functor on the left of that comparison, so no rewriting is needed to apply it;
* `Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_cohomology_iff_isCoherent`,
  which is [Stacks, Tag 01XK] over the affine base `X`: coherence of a higher direct image is
  finiteness of the cohomology upstairs as a `Γ(X, 𝒪_X)`-module.

The only bookkeeping is the ring: `complementCohomologyBase` reads its value over `A` through
`Stacks.LocalCohomologyTilde.globalToBase`, restriction of scalars along the isomorphism
`A ≅ Γ(Spec A, 𝒪)`, and `Module.finite_restrictScalars_ringEquiv_iff` moves finiteness across it.

For the affine case of [Stacks, Tag 0BLT] the three inputs are: clause (1) of
[Stacks, Tag 0BK0] (`AlgebraicGeometry.exists_finiteModule_tilde_restrict_zeroLocusCompl`),
which produces the finite `A`-module `M` with `M̃|_U ≅ ℱ`; the readoff of local freeness of the
localizations `M_f` for `f ∈ I`
(`Module.isFiniteLocallyFree_localization_away_of_mem_of_isFiniteLocallyFree_zeroLocusCompl`);
and the local-cohomology step
`Stacks.LocalCohomologySequence.finite_complementCohomologyBase_of_finite_structureSheaf`,
which is [Stacks, Tag 0BPY] with the comparison of [Stacks, Tag 0DWR] on both sides.  The
structure sheaf enters as `𝒪_U = (Ã)|_U` through Mathlib's `AlgebraicGeometry.tildeSelf` and
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`.

**What tag 0BLT still needs**, beyond this file, is the reduction of a general locally
Noetherian base to an affine one.  Coherence of a higher direct image is local on the base —
`Stacks.AlgebraicGeometry.ProperCohomologyFinite`'s
`isCoherent_rightDerivedPlus_of_forall_isAffineOpen`, whose instance hypotheses an open immersion
into a locally Noetherian scheme satisfies — which
reduces the tag to the case of an affine *open* `V` of the base and the restricted morphism
`j ∣_ V`.  That case is not the statement below: `V.toScheme` is an affine scheme, not `Spec` of
a ring, and `j ∣_ V` is an open immersion but not the inclusion of an open of `V`.  Bridging the
two needs the higher direct images to be transported along the isomorphism
`AlgebraicGeometry.Scheme.isoSpec` of the base and along
`AlgebraicGeometry.Scheme.restrictRestrictComm` on the source, and the library has that transport
for the *undirected* pushforward (`AlgebraicGeometry.Scheme.Modules.pushforwardComp`,
`pushforwardCongr`) but not for its right derived functors.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BLT](https://stacks.math.columbia.edu/tag/0BLT)
* [Stacks Project, Tag 0BPY](https://stacks.math.columbia.edu/tag/0BPY)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProperCohomologyFinite
open Stacks.Cohomology.AffineBase Stacks.Cohomology.ModuleComparison
open Stacks.Cohomology.SchemeOpenSections Stacks.Cohomology.SectionsWithSupport
open Stacks.LocalCohomologyTilde

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Module

/-- **Finiteness is insensitive to restriction of scalars along a ring isomorphism.** For a ring
isomorphism `e : R ≃+* S` and an `S`-module `N`, the module `N` read over `R` along `e` is finite
exactly when `N` is finite over `S`.

In both directions the identity map is semilinear — over `e` one way and over `e.symm` the other,
the latter because `e (e.symm s) = s` — and it is surjective, so `Module.Finite.of_surjective`
applies. -/
public theorem finite_restrictScalars_ringEquiv_iff {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) (N : ModuleCat.{u} S) :
    Module.Finite R ((ModuleCat.restrictScalars e.toRingHom).obj N) ↔ Module.Finite S N :=
  ⟨fun _ => Module.Finite.of_surjective
      (M := ((ModuleCat.restrictScalars e.toRingHom).obj N))
      ({ toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
        ((ModuleCat.restrictScalars e.toRingHom).obj N) →ₛₗ[e.toRingHom] (N : Type u))
      (fun x => ⟨x, rfl⟩),
    fun _ => Module.Finite.of_surjective (M := (N : Type u))
      ({ toFun := id, map_add' := fun _ _ => rfl,
         map_smul' := fun s x => by
           change s • x = e (e.symm s) • x
           rw [e.apply_symm_apply] } :
        (N : Type u) →ₛₗ[(e.symm : S ≃+* R).toRingHom]
          ((ModuleCat.restrictScalars e.toRingHom).obj N))
      (fun x => ⟨x, rfl⟩)⟩

/-- Isomorphic objects of `ModuleCat R` are finite together. -/
public theorem finite_iff_of_moduleCat_iso {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (e : M ≅ N) : Module.Finite R M ↔ Module.Finite R N :=
  ⟨fun _ => Module.Finite.equiv e.toLinearEquiv,
    fun _ => Module.Finite.equiv e.symm.toLinearEquiv⟩

end Module

namespace Stacks.LocalCohomologySequence

variable {A : CommRingCat.{u}}

/-! ### Clause (3) of Tag 0BK0, the equivalence of (a) and (b) -/

/-- **[Stacks, Tag 0BK0] (3), the equivalence of (a) and (b).** Let `A` be a Noetherian ring,
`I ⊆ A` an ideal, `X = Spec A`, `Z = V(I)`, `U = X ∖ Z` and `j : U → X` the inclusion.  For an
`A`-module `M` and any `p ≥ 0` the higher direct image `R^pj_*(M̃|_U)` is coherent if and only if
`H^p(U, M̃)` is a finite `A`-module.

By clause (1) of the same tag every coherent `𝒪_U`-module is isomorphic to a restriction `M̃|_U`
with `M` finite, so this is that clause's equivalence; no finiteness of `M` is needed for the
equivalence itself.

The cohomology of `U` as computed by `complementCohomology` — the derived functor of the sections
over `U` of sheaves of modules on the *ambient* `X` — is identified with the cohomology of the
restriction on the open subscheme `U` by `derivedSectionsOnOpenIso`, which is [Stacks, Tag 01E1]
(2); the latter is what [Stacks, Tag 01XK] over the affine base `X` turns into coherence of the
higher direct image. -/
@[stacks 0BK0 "(3), (a) ⟺ (b)"]
public theorem moduleFinite_complementCohomologyBase_iff_isCoherent [IsNoetherianRing A]
    (I : Ideal (ToType A)) (M : ModuleCat.{u} A) (p : ℕ) :
    Module.Finite A (complementCohomologyBase I M p) ↔
      (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).obj
        ((tilde M).restrict (zeroLocusCompl I).ι)).IsCoherent := by
  have hiso : (((sectionsOnOpen (Spec A).toRingedSpace (zeroLocusCompl I)).rightDerived p).obj
        (tilde M) : ModuleCat.{u} Γ(Spec A, (⊤ : (Spec A).Opens))) ≅
      (ModuleCat.restrictScalars (zeroLocusCompl I).ι.appTop.hom).obj
        (((moduleGlobalSections (zeroLocusCompl I).toScheme).rightDerived p).obj
          ((tilde M).restrict (zeroLocusCompl I).ι)) :=
    (derivedSectionsOnOpenIso (Spec A) (zeroLocusCompl I) p).app (tilde M)
  refine Iff.trans ?_ (moduleFinite_cohomology_iff_isCoherent (zeroLocusCompl I).ι
    ((tilde M).restrict (zeroLocusCompl I).ι) p)
  refine Iff.trans (Module.finite_restrictScalars_ringEquiv_iff (baseRingEquiv A)
    (((sectionsOnOpen (Spec A).toRingedSpace (zeroLocusCompl I)).rightDerived p).obj
      (tilde M))) ?_
  exact Module.finite_iff_of_moduleCat_iso hiso

/-! ### The affine case of Tag 0BLT -/

/-- **[Stacks, Tag 0BPY] read on the complement of `V(I)`.** Let `A` be a Noetherian ring,
`I ⊆ A` an ideal, `U = Spec A ∖ V(I)` and `n ≥ 0`.  Let `M` be a finite `A`-module whose
localization `M_f` is a finite locally free `A_f`-module for every `f ∈ I`.  If the `A`-modules
`H^p(U, 𝒪_U)` are finite for `0 ≤ p < n`, then so are the `A`-modules `H^p(U, M̃)`.

The comparison `H^p(U, -) ≅ H^{p+1}_{V(I)}(-)` of [Stacks, Tag 0DWR], in the finiteness form
`finite_complementCohomologyBase_iff_finite_localCohomology` that also covers degree zero, turns
both the hypothesis and the conclusion into finiteness of local cohomology; in between stands
[Stacks, Tag 0BPY] as `localCohomologyWithSupportIn_finite_of_finiteLocallyFree_away`.  The
hypothesis of that tag runs over all degrees `i ≤ n`, including `i = 0`, where finiteness is
automatic: `H^0_{V(I)}(A)` is a submodule of `A`. -/
private theorem finite_complementCohomologyBase_of_finite_structureSheaf [IsNoetherianRing A]
    (I : Ideal (ToType A)) (n : ℕ)
    (hstruct : ∀ p : ℕ, p < n →
      Module.Finite A (complementCohomologyBase I (ModuleCat.of (ToType A) (ToType A)) p))
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hM : ∀ f ∈ I, Module.IsFiniteLocallyFree (Localization.Away f)
      (LocalizedModule.Away f (M : Type u))) :
    ∀ p : ℕ, p < n → Module.Finite A (complementCohomologyBase I M p) := by
  have hself : Module.Finite (ToType A)
      ((ModuleCat.of (ToType A) (ToType A) : ModuleCat.{u} A) : Type u) :=
    inferInstanceAs (Module.Finite (ToType A) (ToType A))
  have hbase : ∀ i : ℕ, i ≤ n → Module.Finite A
      (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} (ToType A)
        (PrimeSpectrum.zeroLocus (I : Set (ToType A)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of (ToType A) (ToType A))) (i : ℤ)) := by
    rintro (_ | j) hi
    · simpa using Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_of_nonpos.{u, u}
        (ToType A) (PrimeSpectrum.zeroLocus (I : Set (ToType A)))
        (ModuleCat.of (ToType A) (ToType A)) 0 le_rfl
    · exact (finite_complementCohomologyBase_iff_finite_localCohomology I
        (ModuleCat.of (ToType A) (ToType A)) j).mp (hstruct j (by omega))
  intro p hp
  rw [finite_complementCohomologyBase_iff_finite_localCohomology I M p]
  exact Stacks.LocalCohomology.localCohomologyWithSupportIn_finite_of_finiteLocallyFree_away
    (ToType A) I n hbase M hM (p + 1) (by omega)

/-- The restriction of `Ã` to the complement of `V(I)` is the structure sheaf of that open
subscheme: `Ã` is `𝒪_{Spec A}` by `AlgebraicGeometry.tildeSelf`, and restriction along an open
immersion carries the structure sheaf to the structure sheaf. -/
public def tildeSelfRestrictUnitIso (I : Ideal (ToType A)) :
    (tilde (ModuleCat.of (ToType A) (ToType A))).restrict (zeroLocusCompl I).ι ≅
      SheafOfModules.unit (zeroLocusCompl I).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctor (zeroLocusCompl I).ι).mapIso tildeSelf ≪≫
    Scheme.Modules.restrictUnitIso (zeroLocusCompl I).ι

/-- **The affine case of [Stacks, Tag 0BLT].** Let `A` be a Noetherian ring, `I ⊆ A` an ideal,
`U = Spec A ∖ V(I)` and `j : U → Spec A` the inclusion.  If the higher direct images
`R^pj_*𝒪_U` are coherent for `0 ≤ p < n`, then so are `R^pj_*ℱ` for every finite locally free
`𝒪_U`-module `ℱ`.

`ℱ` is coherent ([Stacks, Tag 01XZ]), so clause (1) of [Stacks, Tag 0BK0] writes it as `M̃|_U`
for a finite `A`-module `M`, whose localizations `M_f` are then finite locally free for `f ∈ I`.
Clause (3) (a) ⟺ (b) of that tag, as
`moduleFinite_complementCohomologyBase_iff_isCoherent`, turns both the hypothesis and the
conclusion into finiteness of `H^p(U, -)` over `A`, and in between stands [Stacks, Tag 0BPY] as
`finite_complementCohomologyBase_of_finite_structureSheaf`. -/
public theorem isCoherent_rightDerived_zeroLocusCompl_of_structureSheaf [IsNoetherianRing A]
    (I : Ideal (ToType A)) (n : ℕ)
    (hO : ∀ p : ℕ, p < n →
      (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).obj
        (SheafOfModules.unit (zeroLocusCompl I).toScheme.ringCatSheaf)).IsCoherent)
    (F : (zeroLocusCompl I).toScheme.Modules)
    (hF : Scheme.Modules.IsFiniteLocallyFree F) :
    ∀ p : ℕ, p < n →
      (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).obj F).IsCoherent := by
  have hFclass : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    (Scheme.Modules.isFiniteLocallyFree_iff F).mp hF
  have hFcoh : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree _ F
  obtain ⟨M, hMfin, ⟨e⟩⟩ := exists_finiteModule_tilde_restrict_zeroLocusCompl I F
  have hMfin' : Module.Finite A M := hMfin
  have hU : Scheme.Modules.IsFiniteLocallyFree
      ((tilde M).restrict (zeroLocusCompl I).ι) :=
    Scheme.Modules.IsFiniteLocallyFree.of_iso e.symm hF
  have hstruct : ∀ p : ℕ, p < n →
      Module.Finite A (complementCohomologyBase I (ModuleCat.of (ToType A) (ToType A)) p) := by
    intro p hp
    refine (moduleFinite_complementCohomologyBase_iff_isCoherent I _ p).mpr ?_
    have := hO p hp
    exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).mapIso
        (tildeSelfRestrictUnitIso I))
  have hconc := finite_complementCohomologyBase_of_finite_structureSheaf I n hstruct M
    (fun f hf =>
      Module.isFiniteLocallyFree_localization_away_of_mem_of_isFiniteLocallyFree_zeroLocusCompl
        I M hU f hf)
  intro p hp
  have hMcoh := (moduleFinite_complementCohomologyBase_iff_isCoherent I M p).mp (hconc p hp)
  exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
    (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).mapIso e.symm)

end Stacks.LocalCohomologySequence

end
