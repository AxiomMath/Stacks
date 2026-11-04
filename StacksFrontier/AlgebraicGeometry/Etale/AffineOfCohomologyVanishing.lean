module

public import StacksFrontier.Algebra.Homology.SpectralSequence.OriginVanishing
public import StacksFrontier.AlgebraicGeometry.Etale.AffineOverPuncturedSpectrum
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedSectionsResidueFieldVanishing
public import StacksFrontier.AlgebraicGeometry.Etale.PuncturedSpectrumResidueFieldTor
public import StacksFrontier.Homology.Tor.DerivedTensorDegreeZero
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.DerivedSectionsOverBase

/-!
# Affineness from the vanishing of structure-sheaf cohomology in high degrees

Let `(A, 𝔪)` be a regular local ring containing a field, let `f : V ⟶ Spec A` be étale and
quasi-compact, and suppose `f` factors through the punctured spectrum `Spec A ∖ {𝔪}` by an affine
morphism. [Stacks, Tag 0ECC] asserts that `V` is affine as soon as `H ⁱ(V, 𝒪_V) = 0` for every
`i ≥ dim(A) - 1`.

This file assembles the source's proof out of the steps the library carries:

* the complex `K = RΓ(V, 𝒪_V)` of `A`-modules, bounded above by the vanishing hypothesis and
  concentrated in degrees `≥ 0` (`Stacks.LocalCohomology.derivedSectionsMinus`);
* the spectral sequence `''E₂^{p,q} = H^p(H^q(K) ⊗^L_A A/𝔪)` of [Stacks, Tag 0662] read at the
  origin (`Stacks.SpectralSequence.isZero_derivedTensorHomology_zero_singleHomology_zero`);
* the vanishing of the abutment term `H⁰(RΓ(V, 𝒪_V) ⊗^L_A A/𝔪)`, which comes from the emptiness
  of the closed fibre of `V`
  (`Stacks.PuncturedSpectrum.isZero_derivedTensor_derivedSectionsOverBase_residueField`);
* the vanishing of the incoming terms of that spectral sequence, which is [Stacks, Tag 0ECB]
  together with [Stacks, Tag 0EBT]
  (`Stacks.PuncturedSpectrum.isZero_derivedTensorHomology_cohomologyOverBase_residueField`);
* affineness once `Γ(V, 𝒪_V) ⊗_A A/𝔪 = 0`
  (`Stacks.PuncturedSpectrum.isAffine_of_subsingleton_quotTensor_globalSections`).

## Main definitions

* `Stacks.PuncturedSpectrum.residueFieldSingle` — the residue field `A ⧸ 𝔪` as an object of the
  derived category of `A`-modules, placed in degree zero.

## Main results

* `Stacks.PuncturedSpectrum.isAffine_of_isZero_derivedTensor` — the assembly, for an arbitrary
  degree bound above which the cohomology vanishes.
* `Stacks.PuncturedSpectrum.isAffine_of_cohomologyOverBase_vanishing` — the same with the
  source's own bound `dim(A) - 1`, where both the abutment and the `Tor` input are discharged, so
  that the only hypothesis left is the cohomology vanishing of the statement of the tag.

## Implementation notes

`Stacks.LocalCohomology.cohomologyOverBase A f (SheafOfModules.unit V.ringCatSheaf) n` is the
`A`-module model of `H ⁿ(V, 𝒪_V)` used throughout, and the complex `K` is the one whose degree-`n`
cohomology it is. The vanishing hypothesis is imposed only at natural numbers, since that model
is indexed by `ℕ`; the negative degrees are covered by
`Stacks.LocalCohomology.isZero_homology_derivedSectionsOverBase_of_neg`.

The hypothesis `hTor` of `Stacks.PuncturedSpectrum.isAffine_of_isZero_derivedTensor` is needed
only in the finitely many degrees `2 ≤ r ≤ a + 1` left over by the bound `a`: above them the
vanishing of `H^{r-1}(V, 𝒪_V)` already kills the derived tensor product, by
`Stacks.SpectralSequence.isZero_derivedTensorHomology_singleHomology`. That is the one place the
source's degree bound is used, and it is what cuts the obligation down to `2 ≤ r < dim(A)` when
the bound is the source's own `dim(A) - 1` — which is the range in which [Stacks, Tag 0ECB] and
[Stacks, Tag 0EBT] supply it, so that
`Stacks.PuncturedSpectrum.isAffine_of_cohomologyOverBase_vanishing` carries no `Tor` hypothesis.

The last step is stated about `Γ(V, 𝒪_V)` with the `A`-algebra structure induced by `f`; the
algebra structure supplied below is the one `Stacks.LocalCohomology.sectionsOverBase` restricts
scalars along, and `Stacks.PuncturedSpectrum.baseHom_eq_appLE` is the equality of that
ring map with `Stacks.PuncturedSpectrum.baseHom f`.

The dimension of `A` is written `((ringKrullDim A).unbotD 0).toNat`, the Krull dimension of a
local ring read as a natural number. The subtraction `d - 1` is truncated, which matches the
source: for `d = 0` the condition `i ≥ dim(A) - 1` holds for every `i ≥ 0`.

### The two cited inputs

The source cites two results beyond the spectral sequence, and both are available.

The abutment term, the vanishing of `H⁰(RΓ(V, 𝒪_V) ⊗^L_A A/𝔪)`, is
`Stacks.PuncturedSpectrum.isZero_derivedTensor_derivedSectionsOverBase_residueField`: the source
obtains it from cohomology and base change along the empty closed fibre, and the library obtains
the same vanishing by computing the derived tensor product on an injective resolution of `𝒪_V`
tensored with the Koszul complex of a generating family of `𝔪`, which is acyclic because the
standard opens of the generators cover `V`.

The vanishing of `Tor_r^A(H^{r-1}(V, 𝒪_V), A ⧸ 𝔪)` for `2 ≤ r < dim(A)` is
`Stacks.PuncturedSpectrum.isZero_derivedTensorHomology_cohomologyOverBase_residueField`:
[Stacks, Tag 0ECB] makes that cohomology a direct sum of copies of an injective hull `E` of the
residue field, [Stacks, Tag 0EBT] makes `Tor_i^A(E, κ)` vanish for `i ≠ dim(A)`, and the derived
tensor product commutes with arbitrary direct sums
(`Stacks.DerivedTensor.isZero_derivedTensorHomology_directSum_single`).

## References

* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
* [Stacks Project, Tag 0ECB](https://stacks.math.columbia.edu/tag/0ECB)
* [Stacks Project, Tag 0662](https://stacks.math.columbia.edu/tag/0662)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.LocalCohomology Stacks.SpectralSequence CochainComplex.DerivedTensor

universe u

namespace Stacks.PuncturedSpectrum

attribute [local instance 2000] HasDerivedCategory.standard

/-- **The residue field of a local ring, in degree zero of the derived category.** This is the
object called `A/𝔪` in the proof of [Stacks, Tag 0ECC], against which the complex
`RΓ(V, 𝒪_V)` is tensored. -/
abbrev residueFieldSingle (A : Type u) [CommRing A] [IsLocalRing A] :
    DerivedCategory (ModuleCat.{u} A) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
    (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A))

/-- In nonnegative integer degree `n`, `Hⁿ(RΓ(V, F))` is the `A`-module `H ⁿ(V, F)`, `n` read as
a natural number. -/
private theorem nonempty_homology_iso_cohomologyOverBase_toNat (A : Type u) [CommRing A]
    {V : Scheme.{u}} (f : V ⟶ Spec (CommRingCat.of A))
    (F : SheafOfModules.{u} V.ringCatSheaf) {n : ℤ} (hn : 0 ≤ n) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (derivedSectionsOverBase A f F) ≅ cohomologyOverBase.{u, u} A f F n.toNat) := by
  have h := nonempty_homology_derivedSectionsOverBase_iso A f F n.toNat
  rwa [Int.toNat_of_nonneg hn] at h

/-- **[Stacks, Tag 0ECC], the proof assembled, for an arbitrary degree bound.** In the situation
of [Stacks, Tag 0ECB] — `A` a regular local ring containing a field `k`, `f : V ⟶ Spec A` étale
and quasi-compact, and the structure morphism factored through the punctured spectrum by an
affine morphism `g` — suppose `H ⁿ(V, 𝒪_V) = 0` for every natural number `n` above a bound `a`,
and suppose

* `H⁰(RΓ(V, 𝒪_V) ⊗^L_A A/𝔪) = 0`;
* `Tor_r^A(H^{r-1}(V, 𝒪_V), A/𝔪) = 0` for every `r` with `2 ≤ r` and `r - 1 ≤ a`.

Then `V` is affine.

The second hypothesis is required only below the bound: for `r - 1 > a` the vanishing of
`H^{r-1}(V, 𝒪_V)` gives it. -/
theorem isAffine_of_isZero_derivedTensor (A k : Type u) [CommRing A] [IsRegularLocalRing A]
    [Field k] [Algebra k A] {V : Scheme.{u}} (f : V ⟶ Spec (CommRingCat.of A)) [Etale f]
    [QuasiCompact f]
    (g : V ⟶ (Stacks.LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme))
    [IsAffineHom g]
    (hg : g ≫ (Stacks.LocalCohomology.puncturedSpectrum (CommRingCat.of A)).ι = f) (a : ℤ)
    (hvanish : ∀ n : ℕ, a < (n : ℤ) →
      IsZero (cohomologyOverBase A f (SheafOfModules.unit V.ringCatSheaf) n))
    (habut : IsZero (derivedTensorHomology A
      (derivedSectionsOverBase A f (SheafOfModules.unit V.ringCatSheaf))
      (residueFieldSingle A) 0))
    (hTor : ∀ r : ℤ, 2 ≤ r → r - 1 ≤ a → IsZero (derivedTensorHomology A
      (singleHomology A (derivedSectionsOverBase A f (SheafOfModules.unit V.ringCatSheaf))
        (r - 1)) (residueFieldSingle A) (-r))) :
    IsAffine V := by
  set F := SheafOfModules.unit V.ringCatSheaf with hF
  set K : DerivedCategory.Minus (ModuleCat.{u} A) := derivedSectionsMinus A f F a hvanish with hK
  let L : DerivedCategory.Minus (ModuleCat.{u} A) := ⟨residueFieldSingle A, ⟨0, inferInstance⟩⟩
  have hneg : ∀ q : ℤ, q < 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj K.1) := fun q hq =>
    isZero_homology_derivedSectionsOverBase_of_neg A f F q hq
  have hTor' : ∀ r : ℤ, 2 ≤ r →
      IsZero (derivedTensorHomology A (singleHomology A K.1 (r - 1)) L.1 (-r)) := by
    intro r hr
    rcases le_or_gt (r - 1) a with hle | hgt
    · exact hTor r hr hle
    · refine isZero_derivedTensorHomology_singleHomology A K.1 L.1 (r - 1) ?_ (-r)
      obtain ⟨e⟩ := nonempty_homology_iso_cohomologyOverBase_toNat A f F (n := r - 1) (by omega)
      exact IsZero.of_iso (hvanish _ (by omega)) e
  have horigin := isZero_derivedTensorHomology_zero_singleHomology_zero A K L habut hneg hTor'
  have hsub : Subsingleton ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (derivedSectionsOverBase A f F))) :=
    Stacks.DerivedTensor.subsingleton_tensorProduct_symm_of_isZero A _ _ horigin
  obtain ⟨e0⟩ := nonempty_homology_zero_derivedSectionsOverBase_iso_sections A f F
  let _ : Algebra A Γ(V, ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).toAlgebra
  have hsub' : Subsingleton ((A ⧸ IsLocalRing.maximalIdeal A) ⊗[A] Γ(V, ⊤)) :=
    (TensorProduct.congr (LinearEquiv.refl A _) e0.toLinearEquiv).toEquiv.subsingleton_congr.mp
      hsub
  exact isAffine_of_subsingleton_quotTensor_globalSections A k f g hg
    (baseHom_eq_appLE f (by simp)).symm hsub'

/-- **[Stacks, Tag 0ECC], the proof assembled, with the source's own degree bound.** In the
situation of [Stacks, Tag 0ECB], write `d` for the Krull dimension of `A`. If
`H ⁿ(V, 𝒪_V) = 0` for every `n ≥ d - 1`, then `V` is affine.

Both inputs the source cites are discharged: the abutment `H⁰(RΓ(V, 𝒪_V) ⊗^L_A A/𝔪) = 0` by
`Stacks.PuncturedSpectrum.isZero_derivedTensor_derivedSectionsOverBase_residueField`, and the
vanishing of `Tor_r^A(H^{r-1}(V, 𝒪_V), A/𝔪)` for `2 ≤ r < d` by
`Stacks.PuncturedSpectrum.isZero_derivedTensorHomology_cohomologyOverBase_residueField`. See the
module documentation. -/
@[stacks 0ECC "the proof assembled under the source's own hypotheses: the cohomology vanishing \
above dim(A) - 1 is the hypothesis of the tag, and both cited inputs are proved — the abutment \
H⁰(RΓ(V,𝒪_V) ⊗^L_A A/𝔪) = 0 by computing the derived tensor product on an injective resolution \
against the Koszul complex of a generating family of the maximal ideal, which is acyclic because \
the standard opens of the generators cover V, and the Tor vanishing from Tags 0ECB and 0EBT"]
theorem isAffine_of_cohomologyOverBase_vanishing (A k : Type u) [CommRing A]
    [IsRegularLocalRing A] [Field k] [Algebra k A] {V : Scheme.{u}}
    (f : V ⟶ Spec (CommRingCat.of A)) [Etale f] [QuasiCompact f]
    (g : V ⟶ (Stacks.LocalCohomology.puncturedSpectrum (CommRingCat.of A) : Scheme))
    [IsAffineHom g]
    (hg : g ≫ (Stacks.LocalCohomology.puncturedSpectrum (CommRingCat.of A)).ι = f)
    (hvanish : ∀ n : ℕ, ((ringKrullDim A).unbotD 0).toNat - 1 ≤ n →
      IsZero (cohomologyOverBase A f (SheafOfModules.unit V.ringCatSheaf) n)) :
    IsAffine V := by
  have habut : IsZero (derivedTensorHomology A
      (derivedSectionsOverBase A f (SheafOfModules.unit V.ringCatSheaf))
      (residueFieldSingle A) 0) :=
    Functor.map_isZero (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0)
      (isZero_derivedTensor_derivedSectionsOverBase_residueField A g hg
        (SheafOfModules.unit V.ringCatSheaf))
  set d := ((ringKrullDim A).unbotD 0).toNat with hd
  have hdim : ringKrullDim A = (d : WithBot ℕ∞) := by
    rw [hd]
    have hbot : ringKrullDim A ≠ ⊥ := ringKrullDim_ne_bot
    have htop : ringKrullDim A ≠ ⊤ := ringKrullDim_ne_top
    cases hr : ringKrullDim A with
    | bot => exact absurd hr hbot
    | coe y =>
      cases y with
      | top => exact absurd hr htop
      | coe m => simp
  refine isAffine_of_isZero_derivedTensor A k f g hg ((d : ℤ) - 2)
    (fun n hn => hvanish n (by omega)) habut (fun r hr hra => ?_)
  obtain ⟨e⟩ := nonempty_homology_iso_cohomologyOverBase_toNat A f
    (SheafOfModules.unit V.ringCatSheaf) (n := r - 1) (by omega)
  refine IsZero.of_iso (isZero_derivedTensorHomology_cohomologyOverBase_residueField A k f g hg d
    hdim (r - 1).toNat (by omega) r (by omega)) ?_
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-r)).mapIso
    (((canonicalDerivedTensorProductFunctor A).mapIso
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso e)).app (residueFieldSingle A))

end Stacks.PuncturedSpectrum

end
