module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor
public import StacksFrontier.Algebra.Homology.SpectralSequence.Boundedness
public import StacksFrontier.AlgebraicGeometry.Cohomology.HypercohomologySpectralSequence.DerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulGeneration.TruncationCriterion
public import StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.DirectSums

/-!
# Boundedness and convergence of the hypercohomology spectral sequence on a qcqs scheme

Let `X` be a quasi-compact quasi-separated scheme and let `K` be an object of the derived
category of `𝒪_X`-modules all of whose cohomology sheaves are quasi-coherent. The spectral
sequence
```
E_2^{i, j} = H^i(X, H^j(K)) ⟹ H^{i + j}(X, K)
```
obtained by filtering a representative of `K` by its canonical truncations is bounded, and it
converges to the hypercohomology of `K`.

Both conclusions come from a single degree bound: on a quasi-compact quasi-separated scheme the
cohomology of every quasi-coherent module vanishes from some degree `N` on, so the second page
can be nonzero only in the strip `0 ≤ i ≤ N - 1`, and the hypercohomology of a filtration step
`τ_{≤ -p}K` vanishes in a fixed total degree once `p` is large, while the inclusion of a
filtration step induces an isomorphism on hypercohomology in that degree once `p` is small.
Those are exactly the two hypotheses of the convergence statement of [Stacks, Tag 0BKK] that the
canonical truncation datum carries.

## Main results

* `AlgebraicGeometry.hypercohomologySpectralSequence_isBounded`: **the hypercohomology spectral
  sequence of an object of `D_QCoh(𝒪_X)` on a quasi-compact quasi-separated scheme is bounded.**
* `AlgebraicGeometry.hypercohomologySpectralSequence_abutsTo`: **it converges to the
  hypercohomology of the object.**
* `AlgebraicGeometry.isZero_hypercohomologySpectralSequence_page_two`: **its second page vanishes
  outside the band of columns `0 ≤ p < N`**, in every row.

## Implementation notes

The spectral sequence of the source is the one of [Stacks, Tag 0BKM], renumbered to begin at
page two; convergence is `CategoryTheory.SpectralSequence.AbutsTo`, whose finite decreasing
filtration has the terms of the infinity page as its successive quotients. The abutment is
transported from the unrenumbered sequence of [Stacks, Tag 0BKK] along
`CategoryTheory.SpectralSequence.AbutsTo.shiftStart`, which discards the pages below the first,
and `CategoryTheory.SpectralSequence.AbutsTo.truncationRenumber`, which performs the change of
bidegree `(i, j) ↦ (-j, i + 2j)`.

## References

* [Stacks Project, Tag 0G9Q](https://stacks.math.columbia.edu/tag/0G9Q)
* [Stacks Project, Tag 0BKM](https://stacks.math.columbia.edu/tag/0BKM)
* [Stacks Project, Tag 0BKK](https://stacks.math.columbia.edu/tag/0BKK)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SpectralSequence Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.FilteredComplex

universe u

-- `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, reached through the import of
-- [Stacks, Tag 08D4], supplies a second `HasDerivedCategory` instance for module sheaves, with a
-- smaller hom universe. The derived global-sections functor of the canonical truncation spectral
-- sequence is built with the standard one, so the standard one is given priority here; without
-- that the two readings of `DerivedCategory (SheafOfModules 𝒪_X)` differ by a universe.
attribute [local instance 2000] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- A zero sheaf of modules is quasi-coherent. -/
private theorem isQuasicoherent_of_isZero
    {M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)} (hM : IsZero M) :
    M.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
    hM.isoZero.symm (isQuasicoherent_zero X)

/-- The cohomology sheaves of a canonical truncation of a complex with quasi-coherent cohomology
are quasi-coherent: below the truncation degree they are those of the complex, above it they
vanish. -/
theorem isQuasicoherent_homology_Q_truncLE
    (L : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (hL : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj
        (DerivedCategory.Q.obj L)).IsQuasicoherent) (a j : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj
      (DerivedCategory.Q.obj (L.truncLE a))).IsQuasicoherent := by
  by_cases hj : j ≤ a
  · have := isIso_H_Q_ιTruncLE L a j hj
    exact (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).map
          (DerivedCategory.Q.map (L.ιTruncLE a)))).symm (hL j)
  · exact isQuasicoherent_of_isZero X
      (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj (L.truncLE a)) a j (by omega))

variable (L : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
  (T : CanonicalTruncationSpectralSequence X.toRingedSpace L)

/-- **The inclusion of a canonical truncation induces an isomorphism on hypercohomology in the
degrees the truncation retains.** This is [Stacks, Tag 08D4] part (1) read along the comparison
between the truncation of the complex and the truncation of its class in the derived
category. -/
theorem isIso_homology_RΓ_map_Q_ιTruncLE
    (M : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (hM : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj
        (DerivedCategory.Q.obj M)).IsQuasicoherent)
    (a n : ℤ) (hn : n ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor
      (ModuleCat.{u}
        ((structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.carrier)))) n).map
      (T.RΓ.map (DerivedCategory.Q.map (M.ιTruncLE a)))) := by
  have htrunc : IsIso ((DerivedCategory.TStructure.t.truncLE a).map
      (DerivedCategory.Q.map (M.ιTruncLE a))) :=
    (Stacks.DerivedTruncation.isIso_truncLE_map_iff_forall_isIso_homologyMap
      (DerivedCategory.Q.map (M.ιTruncLE a)) a).2 fun j hj => isIso_H_Q_ιTruncLE M a j hj
  have h₁ := isIso_homology_RΓ_map_truncLEι X L T (DerivedCategory.Q.obj (M.truncLE a))
    (isQuasicoherent_homology_Q_truncLE X M hM a) a n hn
  have h₂ := isIso_homology_RΓ_map_truncLEι X L T (DerivedCategory.Q.obj M) hM a n hn
  have hnat : (DerivedCategory.TStructure.t.truncLE a).map
        (DerivedCategory.Q.map (M.ιTruncLE a)) ≫
      (DerivedCategory.TStructure.t.truncLEι a).app (DerivedCategory.Q.obj M) =
        (DerivedCategory.TStructure.t.truncLEι a).app (DerivedCategory.Q.obj (M.truncLE a)) ≫
          DerivedCategory.Q.map (M.ιTruncLE a) := by
    simpa only [Functor.id_map] using
      (DerivedCategory.TStructure.t.truncLEι a).naturality (DerivedCategory.Q.map (M.ιTruncLE a))
  let F := T.RΓ ⋙ DerivedCategory.homologyFunctor
    (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.carrier)))) n
  have h₃ : IsIso (F.map ((DerivedCategory.TStructure.t.truncLE a).map
      (DerivedCategory.Q.map (M.ιTruncLE a)))) := inferInstance
  have hcomp : IsIso (F.map ((DerivedCategory.TStructure.t.truncLEι a).app
      (DerivedCategory.Q.obj (M.truncLE a)) ≫ DerivedCategory.Q.map (M.ιTruncLE a))) := by
    rw [← hnat, F.map_comp]
    exact IsIso.comp_isIso' h₃ h₂
  rw [F.map_comp] at hcomp
  exact IsIso.of_isIso_comp_left (F.map ((DerivedCategory.TStructure.t.truncLEι a).app
    (DerivedCategory.Q.obj (M.truncLE a)))) (F.map (DerivedCategory.Q.map (M.ιTruncLE a)))

variable (K : QuasicoherentDerivedCategory X)
  (S : HypercohomologySpectralSequence X.toRingedSpace K.obj)

/-- The chosen representative of an object with quasi-coherent cohomology has quasi-coherent
cohomology. -/
theorem isQuasicoherent_homology_representative (j : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj
      (DerivedCategory.Q.obj S.representative)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).mapIso S.representativeIso.symm)
    (K.property j)

/-- **The hypercohomology of a high filtration step vanishes in a fixed total degree.** The
`p`-th step is `τ_{≤ -p}` of the representative, so it lies in degrees `≤ -p`, and the degree
bound of [Stacks, Tag 08D4] puts its hypercohomology in degrees `≤ -p + N - 1`. -/
theorem exists_isZero_hypercohomology_filtration_obj (N : ℕ)
    (hN : ∀ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)), M.IsQuasicoherent →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero (((groupSections X).rightDerivedPlus p).obj M))
    (n : ℤ) :
    ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero (hypercohomology X.toRingedSpace S.truncation.RΓ
        (S.truncation.filtered.filtration.obj (op p)) n) := by
  refine ⟨(N : ℤ) - n, fun p hp => ?_⟩
  have hrep := isQuasicoherent_homology_representative X K S
  have hle : (DerivedCategory.Q.obj (S.representative.truncLE (-p))).IsLE (-p) := inferInstance
  have hz := isZero_hypercohomology_of_isLE X S.representative S.truncation N hN
    (DerivedCategory.Q.obj (S.representative.truncLE (-p)))
    (isQuasicoherent_homology_Q_truncLE X S.representative hrep (-p)) (-p) n hle (by omega)
  exact hz.of_iso ((DerivedCategory.homologyFunctor
    (ModuleCat.{u}
      ((structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.carrier)))) n).mapIso
      (S.truncation.RΓ.mapIso (DerivedCategory.Q.mapIso (S.truncation.stepIso p))))

/-- **The inclusion of a low filtration step is an isomorphism on hypercohomology in a fixed
total degree.** The `p`-th step is `τ_{≤ -p}` of the representative, and for `p ≤ -n` the degree
`n` is one the truncation retains. -/
theorem exists_isIso_hypercohomologyMap_filtration_ι (n : ℤ) :
    ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (hypercohomologyMap X.toRingedSpace S.truncation.RΓ
        (S.truncation.filtered.filtration.ι.app (op p)) n) := by
  refine ⟨-n, fun p hp => ?_⟩
  have hg := isIso_homology_RΓ_map_Q_ιTruncLE X S.representative S.truncation S.representative
    (isQuasicoherent_homology_representative X K S) (-p) n (by omega)
  let F := S.truncation.RΓ ⋙ DerivedCategory.homologyFunctor
    (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.carrier)))) n
  replace hg : IsIso (F.map _) := hg
  have hcomp : IsIso (F.map (DerivedCategory.Q.map (S.truncation.filtered.filtration.ι.app (op p)) ≫
      DerivedCategory.Q.map S.truncation.underlyingIso.hom)) := by
    rw [← Functor.map_comp, ← S.truncation.stepIso_hom_comp p, Functor.map_comp, F.map_comp]
    infer_instance
  rw [F.map_comp] at hcomp
  exact IsIso.of_isIso_comp_right
    (F.map (DerivedCategory.Q.map (S.truncation.filtered.filtration.ι.app (op p))))
    (F.map (DerivedCategory.Q.map S.truncation.underlyingIso.hom))

/-- **A quasi-coherent module placed in degree zero has hypercohomology only in degrees
`0, …, N - 1`.** This is the vanishing that bounds the second page of the hypercohomology
spectral sequence. -/
theorem isZero_hypercohomology_single (N : ℕ)
    (hN : ∀ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)), M.IsQuasicoherent →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero (((groupSections X).rightDerivedPlus p).obj M))
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (hM : M.IsQuasicoherent) (n : ℤ)
    (hn : n < 0 ∨ (N : ℤ) ≤ n) :
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u}
        ((structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.carrier)))) n).obj
      (T.RΓ.obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M))) := by
  have hGE : ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M).IsGE 0 := inferInstance
  have hLE : ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M).IsLE 0 := inferInstance
  have hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)).IsQuasicoherent := by
    intro j
    by_cases hj : j = 0
    · subst hj
      exact (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).app M).symm hM
    · refine isQuasicoherent_of_isZero X ?_
      rcases lt_or_gt_of_ne hj with hj' | hj'
      · exact ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M).isZero_of_isGE 0 j hj'
      · exact ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M).isZero_of_isLE 0 j hj'
  rcases hn with hn | hn
  · exact isZero_hypercohomology_of_isGE X L T _ hcoh 0 n hGE hn
  · exact isZero_hypercohomology_of_isLE X L T N hN _ hcoh 0 n hLE (by omega)

/-- **The second page of the hypercohomology spectral sequence vanishes outside the band of
columns `0 ≤ p < N`.** The term in bidegree `(p, j)` is `H^p(X, H^j(K))`, and `H^j(K)` is
quasi-coherent, so the uniform vanishing bound `N` of
`AlgebraicGeometry.exists_isZero_rightDerivedPlus_groupSections` makes it vanish for `p < 0` and
for `N ≤ p`; the column index alone decides, whatever the row `j`.

This is the band hypothesis that the construction of the filtration of [Stacks, Tag 0GA1] out of
this spectral sequence asks for, at `j := -i - p`. -/
theorem isZero_hypercohomologySpectralSequence_page_two (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (K : QuasicoherentDerivedCategory X) (N : ℕ)
    (hN : ∀ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)), M.IsQuasicoherent →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero (((groupSections X).rightDerivedPlus p).obj M))
    (p j : ℤ) (hp : p < 0 ∨ (N : ℤ) ≤ p) :
    IsZero (((hypercohomologySpectralSequence X.toRingedSpace K.obj).spectralSequence.page 2).X
      (p, j)) := by
  obtain ⟨e₂⟩ := hypercohomologySpectralSequence_e₂ X.toRingedSpace K.obj p j
  exact e₂.isZero_iff.mpr
    (isZero_hypercohomology_single X
      (hypercohomologySpectralSequence X.toRingedSpace K.obj).representative
      (hypercohomologySpectralSequence X.toRingedSpace K.obj).truncation N hN
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) j).obj K.obj) (K.property j)
      p hp)

/-- **Stacks Project, Tag 0G9Q.** The hypercohomology spectral sequence of an object of
`D_QCoh(𝒪_X)` on a quasi-compact quasi-separated scheme is bounded: in each total degree only
finitely many second-page terms are nonzero.

The second page in bidegree `(i, j)` is `H^i(X, H^j(K))`, and `H^j(K)` is quasi-coherent, so by
the uniform vanishing of the cohomology of quasi-coherent modules the term is zero unless
`0 ≤ i ≤ N - 1`. -/
@[stacks 0G9Q "boundedness"]
theorem hypercohomologySpectralSequence_isBounded (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (K : QuasicoherentDerivedCategory X) :
    IsBounded (hypercohomologySpectralSequence X.toRingedSpace K.obj).spectralSequence := by
  obtain ⟨N, hN⟩ := exists_isZero_rightDerivedPlus_groupSections X
  intro n
  refine (Set.finite_Icc 0 ((N : ℤ) - 1)).subset fun p hp => ?_
  replace hp : ¬ IsZero (((hypercohomologySpectralSequence X.toRingedSpace K.obj
    ).spectralSequence.page 2).X (p, n - p)) := hp
  have hzero := isZero_hypercohomologySpectralSequence_page_two X K N hN p (n - p)
  refine ⟨by by_contra h; exact hp (hzero (Or.inl (by omega))), ?_⟩
  by_contra h
  exact hp (hzero (Or.inr (by omega)))

/-- **Stacks Project, Tag 0G9Q.** The hypercohomology spectral sequence of an object `K` of
`D_QCoh(𝒪_X)` on a quasi-compact quasi-separated scheme converges to the hypercohomology of `K`:
there is a finite decreasing filtration of each `H^n(X, K)` whose graded pieces are the terms of
the infinity page.

The two hypotheses of the convergence statement of [Stacks, Tag 0BKK] are supplied by
`AlgebraicGeometry.exists_isZero_hypercohomology_filtration_obj` and
`AlgebraicGeometry.exists_isIso_hypercohomologyMap_filtration_ι`; what that statement delivers is
the abutment of the unrenumbered spectral sequence to the hypercohomology of the underlying
complex of the filtration, which is transported to `K` along the representative and then along
the two renumberings. -/
@[stacks 0G9Q "convergence"]
theorem hypercohomologySpectralSequence_abutsTo (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (K : QuasicoherentDerivedCategory X) :
    (hypercohomologySpectralSequence X.toRingedSpace K.obj).spectralSequence.AbutsTo
      (fun n => (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj
          (op (⊤ : Opens X.carrier)))) n).obj
        ((hypercohomologySpectralSequence X.toRingedSpace K.obj).truncation.RΓ.obj K.obj)) := by
  obtain ⟨N, hN⟩ := exists_isZero_rightDerivedPlus_groupSections X
  set S := hypercohomologySpectralSequence X.toRingedSpace K.obj with hS
  obtain ⟨-, F, hF, -, hfinite, hInf, hgraded⟩ := S.truncation.convergence
    (fun n => exists_isZero_hypercohomology_filtration_obj X K S N hN n)
    (fun n => exists_isIso_hypercohomologyMap_filtration_ι X K S n)
  have hAbuts : S.truncation.spectralSequence.AbutsTo
      (fun n => hypercohomology X.toRingedSpace S.truncation.RΓ S.truncation.filtered.X n) :=
    ⟨hInf, F, hF, hfinite, hgraded⟩
  exact ((hAbuts.of_iso fun n => (DerivedCategory.homologyFunctor
    (ModuleCat.{u}
      ((structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.carrier)))) n).mapIso
      (S.truncation.RΓ.mapIso (DerivedCategory.Q.mapIso S.truncation.underlyingIso ≪≫
        S.representativeIso))).shiftStart (by omega)).truncationRenumber

end AlgebraicGeometry

end
