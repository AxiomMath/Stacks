module

public import StacksFrontier.AlgebraicGeometry.Algebraization.AnnihilatorTruncationReduction
public import StacksFrontier.AlgebraicGeometry.Algebraization.LocalCohomologyAnnihilatorInputs
public import StacksFrontier.AlgebraicGeometry.Algebraization.LocalCohomologyCompletionComparison
public import StacksFrontier.RingTheory.Depth.Localization
public import StacksFrontier.RingTheory.Dualizing.DerivingTorsion.Vanishing
public import StacksFrontier.RingTheory.Dualizing.DualExtSupportDepthCriterion
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.BelowDepth
public import StacksFrontier.RingTheory.Localization.AtPrimeQuotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Annihilating the completed local cohomology of a finite module away from a prime

Let `I` and `J` be ideals of a Noetherian ring `A` with a dualizing complex, let `M` be a finite
`A`-module, let `p` be a prime outside `V(J) ∩ V(I)`, and let `s` and `d` be integers with
`cd(A, I) ≤ d`. If
`depth_{A_{p'}}(M_{p'}) + dim((A/p')_q) > d + s` for every prime `p' ⊆ p` and every
`q ∈ V(p') ∩ V(J) ∩ V(I)`, then one element of `A` outside `p` annihilates
`H^i(RΓ_{V(J)}(M)^∧)` for every `i ≤ s`, where `(-)^∧` is derived `I`-adic completion.

Specializing to a local ring `(A, 𝔪)` and `J = 𝔪` gives the local statement: the same conclusion
for `RΓ_{V(𝔪)}(M)` from the single inequality `depth_{A_p}(M_p) + dim(A/p) > d + s` at `p` alone,
with no condition on `p`. Two things close the gap. The quantification over all `p' ⊆ p` is free
because `p ↦ depth_{A_p}(M_p) + dim(A/p)` is lower semicontinuous: by Stacks 0DWZ(4) the
inequality at `p` says that `p` avoids the support of a finite module, and the support of a finite
module is stable under specialization. The excluded locus `V(𝔪) ∩ V(I) = {𝔪}` is handled
separately: at the closed point the inequality reads `depth_A(𝔪, M) > d + s`, so `H^j_{V(𝔪)}(M)`
vanishes for every `j ≤ s + d` by Stacks 0AVZ and the unit annihilates the whole range.

The proof combines three inputs. The identification
`RΓ_{V(J)}(M)^∧ ≅ RHom_A(RΓ_{V(I)}(A), RΓ_{V(J + I)}(M))` turns the completion into a derived
Hom; `RΓ_{V(I)}(A)` lies in degrees `≤ d` because `cd(A, I) ≤ d` and `RΓ_{V(J + I)}(M)` lies in
degrees `≥ 0`; and Stacks 0EFE supplies, for every degree `j ≤ s + d`, an element outside `p`
annihilating `H^j_{V(J + I)}(M)`. Together they give a single element outside `p` annihilating
the cohomology of the derived Hom in all degrees `≤ s`.

## Main results

* `Stacks.Algebraization.exists_notMem_mem_annihilator_homology_derivedCompletion_localCohomology`
  — Stacks 0EFH: an element outside `p` annihilating `H^i(RΓ_{V(J)}(M)^∧)` for all `i ≤ s`.
* `Stacks.Algebraization.localCohomologyDerivedIsoOfEq` — local cohomology in the coreflection
  model of Stacks 0A6Q depends on the ideal only through its value.
* `Stacks.Algebraization.mem_annihilator_of_iso` — an annihilator of a module annihilates every
  module isomorphic to it.
* `exists_notMem_mem_annihilator_homology_derivedCompletion_localCohomology_maximalIdeal` —
  Stacks 0DXK: over a local ring, an element outside `p` annihilating `H^i(RΓ_{V(𝔪)}(M)^∧)` for
  all `i ≤ s`, from the depth-plus-dimension inequality at `p` alone.

## Implementation notes

Derived `I`-adic completion is `DerivedCompletion.derivedCompletionFunctor A gen`, the derived
Hom out of the extended alternating Čech complex of a finite family `gen` generating `I`: the
library indexes derived completion by a finite generating family rather than by the ideal, so
such a family is taken as data. One always exists because `A` is Noetherian, and the completion
is independent of the choice, being the reflection onto the derived `I`-complete objects.

The sum of the two ideals is spelled `J + I` inside the proof, matching
`Stacks.Algebraization.derivedCompletionLocalCohomologyIsoDerivedHomSup`, while the annihilator
input `Stacks.LocalCohomology.exists_notMem_mem_annihilator_localCohomologyModule_sup` is stated
for `I ⊔ J`. The two are reconciled by `localCohomologyDerivedIsoOfEq`, which substitutes the
equality of ideals and then uses proof irrelevance for the two finite-generation arguments
appearing in the types. The final statement mentions only `J`, so no choice of spelling is baked
into it.

Local cohomology with support in `V(J)` is the coreflection model
`Dualizing.localCohomologyFunctor` of Stacks 0A6Q, composed with the inclusion of the objects
with power-torsion cohomology; applied to `M` placed in degree zero this is
`Stacks.LocalCohomology.localCohomologyOnModules`, which is how the bounded-above side
`RΓ_{V(I)}(A)` is written. Finite generation of an ideal of `A` is obtained from
`Ideal.fg_of_isNoetherianRing`, so it is not a hypothesis.

## References

* [Stacks Project, Tag 0EFH](https://stacks.math.columbia.edu/tag/0EFH)
* [Stacks Project, Tag 0EFE](https://stacks.math.columbia.edu/tag/0EFE)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DXK](https://stacks.math.columbia.edu/tag/0DXK)
* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

/-- Local cohomology in the coreflection model of Stacks 0A6Q depends on the ideal only through
its value: equal ideals `S = T` give an isomorphism `RΓ_{V(S)}(K) ≅ RΓ_{V(T)}(K)`. -/
def localCohomologyDerivedIsoOfEq (A : Type u) [CommRing A] (S T : Ideal A) (hS : S.FG)
    (hT : T.FG) (hST : S = T) (K : DerivedCategory (ModuleCat.{u} A)) :
    (Dualizing.derivedPowerTorsionProperty A S hS).ι.obj
        ((Dualizing.localCohomologyFunctor.{u, u} A S hS).obj K) ≅
      (Dualizing.derivedPowerTorsionProperty A T hT).ι.obj
        ((Dualizing.localCohomologyFunctor.{u, u} A T hT).obj K) := by
  subst hST
  exact Iso.refl _

/-- An element annihilating a module annihilates every module isomorphic to it. -/
theorem mem_annihilator_of_iso {A : Type u} [CommRing A] {M N : ModuleCat.{u} A} (e : M ≅ N)
    {r : A} (h : r ∈ Module.annihilator A N) : r ∈ Module.annihilator A M :=
  (smul_id_eq_zero_iff_mem_annihilator M r).mp
    (smul_id_eq_zero_of_iso r e ((smul_id_eq_zero_iff_mem_annihilator N r).mpr h))

/-- If `K^∧ ≅ RHom_A(RΓ_{V(I)}(A), Q)` with `Q` in degrees `≥ 0`, `cd(A, I) ≤ d`, and `H^j(Q)` is
annihilated by an element outside `p` for every `j ≤ s + d`, then one element outside `p`
annihilates `H^i(K^∧)` for every `i ≤ s`. -/
private theorem exists_notMem_mem_annihilator_homology_derivedCompletion_of_iso
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (p : PrimeSpectrum A) (s d : ℤ)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d)
    {r : ℕ} (gen : Fin r → A) (K Q : DerivedCategory (ModuleCat.{u} A)) [Q.IsGE 0]
    (e : (DerivedCompletion.derivedCompletionFunctor A gen).obj K ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((Stacks.LocalCohomology.localCohomologyOnModules.{u, u} A I
          I.fg_of_isNoetherianRing).obj (ModuleCat.of A A)), Q))
    (hQ : ∀ j : ℤ, j ≤ s + d → ∃ f : A, f ∉ p.asIdeal ∧
      f ∈ Module.annihilator A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj Q)) :
    ∃ g : A, g ∉ p.asIdeal ∧ ∀ i : ℤ, i ≤ s →
      g ∈ Module.annihilator A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((DerivedCompletion.derivedCompletionFunctor A gen).obj K)) := by
  obtain ⟨g, hgp, hg⟩ := exists_notMem_mem_annihilator_homology_derivedHom p 0 d s _ Q
    (fun i hi => Stacks.LocalCohomology.isZero_localCohomologyModule_of_cohomologicalDimension_le
      A I I.fg_of_isNoetherianRing d hcd (ModuleCat.of A A) i hi) hQ
  exact ⟨g, hgp, fun i hi => mem_annihilator_of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e) (hg i hi)⟩

/-- Let `I` and `J` be ideals of a Noetherian ring `A` with a dualizing complex, let `M` be a
finite `A`-module, and let `p` be a prime outside `V(J) ∩ V(I)` with `cd(A, I) ≤ d`. If
`depth_{A_{p'}}(M_{p'}) + dim((A/p')_q) > s + d` for all primes `p' ⊆ p` and all
`q ∈ V(p') ∩ V(J) ∩ V(I)`, then some `f ∈ A` outside `p` annihilates the degree-`i` cohomology of
the derived `I`-adic completion of `RΓ_{V(J)}(M)` for every `i ≤ s`. -/
@[stacks 0EFH "the full statement: an element outside `p` annihilating the cohomology of the
derived `I`-adic completion of `RΓ_{V(J)}(M)` in every degree `≤ s`"]
theorem exists_notMem_mem_annihilator_homology_derivedCompletion_localCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (p : PrimeSpectrum A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hp : p ∉ PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d)
    (hdepth : ∀ x y : PrimeSpectrum A, x.asIdeal ≤ p.asIdeal →
      y ∈ PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
      x.asIdeal ≤ y.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime x.asIdeal)
            (maximalIdeal (Localization.AtPrime x.asIdeal))
            (LocalizedModule x.asIdeal.primeCompl M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime y.asIdeal) ⧸
            x.asIdeal.map (algebraMap A (Localization.AtPrime y.asIdeal)))) >
        ((s + d : ℤ) : EInt))
    {r : ℕ} (gen : Fin r → A) (hgen : Ideal.span (Set.range gen) = I) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ i : ℤ, i ≤ s →
      f ∈ Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((DerivedCompletion.derivedCompletionFunctor A gen).obj
            ((Dualizing.derivedPowerTorsionProperty A J J.fg_of_isNoetherianRing).ι.obj
              ((Dualizing.localCohomologyFunctor.{u, u} A J J.fg_of_isNoetherianRing).obj
                ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                  (ModuleCat.of A M)))))) := by
  have hIfg : I.FG := I.fg_of_isNoetherianRing
  have hJfg : J.FG := J.fg_of_isNoetherianRing
  have hsum : I ⊔ J = J + I := by rw [Ideal.add_eq_sup, sup_comm]
  have hGE := Stacks.LocalCohomology.isGE_localCohomologyDerived_single A (J + I)
    (Submodule.FG.sup hJfg hIfg) (ModuleCat.of A M)
  obtain ⟨f₀, hf₀p, hf₀⟩ :=
    Stacks.LocalCohomology.exists_notMem_mem_annihilator_localCohomologyModule_sup
      A M I J p s d omega homega hp hdepth
  exact exists_notMem_mem_annihilator_homology_derivedCompletion_of_iso I p s d hcd gen _ _
    (derivedCompletionLocalCohomologyIsoDerivedHomSup A I J hIfg hJfg gen hgen
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))
    (fun j hj => ⟨f₀, hf₀p, mem_annihilator_of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).mapIso
        (localCohomologyDerivedIsoOfEq A (I ⊔ J) (J + I) (I ⊔ J).fg_of_isNoetherianRing
          (Submodule.FG.sup hJfg hIfg) hsum
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A M)))).symm (hf₀ j hj)⟩)

/-! ### The local case -/

/-- Over a Noetherian local ring the depth of the localization of a finite module at the
maximal ideal is the depth of the module along the maximal ideal. -/
private theorem depth_localizedModule_eq_depth_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (q : Ideal A) [q.IsPrime] (hq : q = maximalIdeal A) :
    Module.depth (Localization.AtPrime q) (maximalIdeal (Localization.AtPrime q))
        (LocalizedModule q.primeCompl M) = Module.depth A (maximalIdeal A) M := by
  subst hq
  let Sₘ : MaximalSpectrum A → Type u := fun P => Localization.AtPrime P.asIdeal
  let Nₘ : MaximalSpectrum A → Type u := fun P => LocalizedModule P.asIdeal.primeCompl M
  let f : ∀ P : MaximalSpectrum A, M →ₗ[A] Nₘ P := fun P =>
    LocalizedModule.mkLinearMap P.asIdeal.primeCompl M
  have hdecomp := Module.depth_eq_iInf_depth_isLocalized_maximal
    (R := A) (S := A) (N := M) Sₘ Nₘ f
  let Pmax : MaximalSpectrum A := ⟨maximalIdeal A, IsLocalRing.maximalIdeal.isMaximal A⟩
  have hP : ∀ P : MaximalSpectrum A, P = Pmax := fun P =>
    MaximalSpectrum.ext <| P.isMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (IsLocalRing.le_maximalIdeal P.isMaximal.ne_top)
  have hInf : (⨅ P : MaximalSpectrum A,
      Module.depth (Sₘ P) (maximalIdeal (Sₘ P)) (Nₘ P)) =
      Module.depth (Sₘ Pmax) (maximalIdeal (Sₘ Pmax)) (Nₘ Pmax) :=
    le_antisymm (iInf_le _ Pmax) (le_iInf fun P => by rw [hP P])
  exact (hdecomp.trans hInf).symm

/-- Over a local ring the dimension of `A ⧸ p` is unchanged by localizing at the maximal
ideal: `A ⧸ p` is already local at the image of the maximal ideal. -/
private theorem ringKrullDim_localizationAtPrime_quotient_eq
    {A : Type u} [CommRing A] [IsLocalRing A] (p : Ideal A) [p.IsPrime]
    (q : Ideal A) [q.IsPrime] (hq : q = maximalIdeal A) :
    ringKrullDim (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) =
      ringKrullDim (A ⧸ p) := by
  subst hq
  let m := maximalIdeal A
  let R := A ⧸ p
  let Q := m.map (Ideal.Quotient.mk p)
  let _ : IsLocalRing R :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hpM : p ≤ m := IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top'
  have hQmax : Q.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (Ideal.mk_ker.trans_le hpM)
  have hQeq : Q = maximalIdeal R := IsLocalRing.eq_maximalIdeal hQmax
  have hQcomap : Q.comap (Ideal.Quotient.mk p) = m := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hpM]
  let _ : IsLocalization.AtPrime
      (Localization.AtPrime m ⧸ p.map (algebraMap A (Localization.AtPrime m))) Q :=
    isLocalization_atPrime_quotient m (Localization.AtPrime m) p Q hQcomap
  refine Eq.symm ?_
  calc
    ringKrullDim R = (maximalIdeal R).height :=
      (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)).symm
    _ = Q.height := by rw [← hQeq]
    _ = ringKrullDim (Localization.AtPrime m ⧸ p.map (algebraMap A (Localization.AtPrime m))) :=
      (IsLocalization.AtPrime.ringKrullDim_eq_height Q _).symm

/-- Over a Noetherian local ring the dimension of `A ⧸ p` is a natural number. -/
private theorem exists_natCast_eq_ringKrullDim_quotient
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (p : PrimeSpectrum A) :
    ∃ n : ℕ, ringKrullDim (A ⧸ p.asIdeal) = ((n : ℕ∞) : WithBot ℕ∞) := by
  have hlt : ringKrullDim (A ⧸ p.asIdeal) < ⊤ :=
    lt_of_le_of_lt (ringKrullDim_quotient_le p.asIdeal) ringKrullDim_lt_top
  have hne : ringKrullDim (A ⧸ p.asIdeal) ≠ ⊥ := fun hbot =>
    (not_subsingleton_iff_nontrivial.mpr (Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top))
      ((ringKrullDim_eq_bot_iff_subsingleton (R := A ⧸ p.asIdeal)).mp hbot)
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  have hdne : d ≠ ⊤ := by
    intro htop
    exact (ne_of_lt hlt) (by rw [← hd, htop]; rfl)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hdne
  exact ⟨n, hd.symm.trans (congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hn.symm)⟩

/-- A depth plus a finite dimension, read in the extended integers, is the integer cast of
their sum, or `⊤` when the depth is infinite. -/
private theorem enatToEInt_add_krullDimToEInt_natCast (dep : ℕ∞) (e : ℕ) :
    enatToEInt dep + krullDimToEInt ((e : ℕ∞) : WithBot ℕ∞) =
      match dep with
      | ⊤ => (⊤ : EInt)
      | (k : ℕ) => (((k + e : ℕ) : ℤ) : EInt) := by
  cases dep with
  | top =>
    show ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ)) +
      (((e : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) = (⊤ : EInt)
    rw [← WithBot.coe_add, WithTop.top_add]
    rfl
  | coe k =>
    show (((k : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) +
      (((e : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) = _
    rw [← WithBot.coe_add, ← WithTop.coe_add]
    norm_cast

/-- A depth plus a finite dimension is nonnegative in the extended integers. -/
private theorem nonneg_enatToEInt_add_krullDimToEInt (dep : ℕ∞) (e : ℕ) :
    (0 : EInt) ≤ enatToEInt dep + krullDimToEInt ((e : ℕ∞) : WithBot ℕ∞) := by
  rw [enatToEInt_add_krullDimToEInt_natCast]
  cases dep with
  | top => exact le_top
  | coe k => exact WithBotTop.coe_le_coe.mpr (Int.natCast_nonneg _)

/-- Comparing a depth plus a finite dimension against an integer bound in the extended integers
is the same comparison read in `WithBot ℕ∞`. -/
private theorem lt_enatToEInt_add_krullDimToEInt_iff (dep : ℕ∞) (e n : ℕ) :
    ((n : ℤ) : EInt) < enatToEInt dep + krullDimToEInt ((e : ℕ∞) : WithBot ℕ∞) ↔
      ¬ ((dep : WithBot ℕ∞) + ((e : ℕ∞) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞)) := by
  rw [enatToEInt_add_krullDimToEInt_natCast, ← WithBot.coe_add, ← WithBot.coe_natCast,
    WithBot.coe_le_coe, not_le]
  cases dep with
  | top =>
    refine iff_of_true (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)) ?_
    simp
  | coe k =>
    rw [← Nat.cast_add, WithBotTop.coe_lt_coe, Nat.cast_lt, Nat.cast_lt]

/-- **Lower semicontinuity of `p ↦ depth(M_p) + dim(A/p)`.** Over a Noetherian local ring with a
dualizing complex, a strict lower bound for `depth_{A_p}(M_p) + dim(A/p)` at a prime `p` holds at
every prime contained in `p`: by Stacks 0DWZ(4) the bound says that `p` avoids the support of a
finite module, and the support of a finite module is stable under specialization. -/
private theorem lt_depth_add_ringKrullDim_quotient_of_le
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (p p' : PrimeSpectrum A) (hp'p : p'.asIdeal ≤ p.asIdeal) (n : ℤ)
    (hp : (n : EInt) <
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt (ringKrullDim (A ⧸ p.asIdeal))) :
    (n : EInt) <
      enatToEInt
          (Module.depth (Localization.AtPrime p'.asIdeal)
            (maximalIdeal (Localization.AtPrime p'.asIdeal))
            (LocalizedModule p'.asIdeal.primeCompl M)) +
        krullDimToEInt (ringKrullDim (A ⧸ p'.asIdeal)) := by
  obtain ⟨e', he'⟩ := exists_natCast_eq_ringKrullDim_quotient p'
  rcases lt_or_ge n 0 with hn | hn
  · rw [he']
    exact lt_of_lt_of_le (WithBotTop.coe_lt_coe.mpr hn)
      (nonneg_enatToEInt_add_krullDimToEInt _ _)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = n := ⟨n.toNat, Int.toNat_of_nonneg hn⟩
  obtain ⟨e, he⟩ := exists_natCast_eq_ringKrullDim_quotient p
  obtain ⟨k, hk⟩ := Dualizing.exists_isNormalizedDualizingComplex_shift.{u, u} omega homega
  have key : ∀ (q : PrimeSpectrum A) (eq : ℕ),
      ringKrullDim (A ⧸ q.asIdeal) = ((eq : ℕ∞) : WithBot ℕ∞) →
      (((N : ℤ) : EInt) <
          enatToEInt
              (Module.depth (Localization.AtPrime q.asIdeal)
                (maximalIdeal (Localization.AtPrime q.asIdeal))
                (LocalizedModule q.asIdeal.primeCompl M)) +
            krullDimToEInt (ringKrullDim (A ⧸ q.asIdeal)) ↔
        q ∉ Module.support A
          ((j : Fin (N + 1)) → Dualizing.moduleExtInto M (omega⟦-k⟧) (-(j : ℤ)))) := by
    intro q eq heq
    rw [Dualizing.mem_support_pi_moduleExtInto_iff_depth_add_ringKrullDim_le.{u, u}
      (omega⟦-k⟧) hk q N, heq, lt_enatToEInt_add_krullDimToEInt_iff]
  rw [← hN] at hp ⊢
  exact (key p' e' he').mpr fun hmem => (key p e he).mp hp (Module.mem_support_mono hp'p hmem)

/-- An integer strictly below a depth gives a natural-number bound on that depth. -/
private theorem natCast_toNat_succ_le_of_lt_enatToEInt {dep : ℕ∞} {m : ℤ}
    (h : (m : EInt) < enatToEInt dep) : (((m + 1).toNat : ℕ) : ℕ∞) ≤ dep := by
  cases dep with
  | top => exact le_top
  | coe k =>
    have hlt : m < (k : ℤ) := WithBotTop.coe_lt_coe.mp h
    exact Nat.cast_le.mpr (by omega)

/-- Over a Noetherian local ring the local cohomology `H^i_{V(𝔪)}(M)` of a finite module
vanishes in every degree below the depth of `M` along the maximal ideal. -/
@[sga "2 XII 1.5"]
private theorem isZero_localCohomologyModule_maximalIdeal_of_lt_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (n : ℕ)
    (hn : (n : ℕ∞) ≤ Module.depth A (maximalIdeal A) M)
    (i : ℤ) (hi : i < n) :
    IsZero (Stacks.LocalCohomology.localCohomologyModule A (maximalIdeal A)
      (maximalIdeal A).fg_of_isNoetherianRing (ModuleCat.of A M) i) := by
  by_cases hIM : (maximalIdeal A) • (⊤ : Submodule A M) = ⊤
  · have hsub : Subsingleton M := by
      have hbot : (⊤ : Submodule A M) = ⊥ :=
        Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal A) ⊤
          Module.Finite.fg_top hIM.ge
          (by rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top])
      exact (Submodule.subsingleton_iff A).mp (subsingleton_of_bot_eq_top hbot.symm)
    let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)
    have hK : IsZero K := Functor.map_isZero _ (ModuleCat.isZero_iff_subsingleton.mpr hsub)
    exact Functor.map_isZero (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)
      (Functor.map_isZero
        (Dualizing.derivedPowerTorsionProperty A (maximalIdeal A)
          (maximalIdeal A).fg_of_isNoetherianRing).ι
        (Dualizing.localCohomology_isZero_of_isIso_smul A (maximalIdeal A)
          (maximalIdeal A).fg_of_isNoetherianRing K 0 (Ideal.zero_mem _) (hK.isIso hK _)))
  · exact (Stacks.LocalCohomology.isZero_localCohomology_of_lt_depth.{u, u}
      (maximalIdeal A) (ModuleCat.of A M) hIM n hn i hi).of_iso
      (Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule A
        (maximalIdeal A) (maximalIdeal A).fg_of_isNoetherianRing (ModuleCat.of A M) i).symm

/-- Let `(A, 𝔪)` be a Noetherian local ring with a dualizing complex, let `I` be an ideal with
`cd(A, I) ≤ d`, let `M` be a finite `A`-module and let `p` be a prime with
`depth_{A_p}(M_p) + dim(A/p) > d + s`. Then some `f ∈ A` outside `p` annihilates the degree-`i`
cohomology of the derived `I`-adic completion of `RΓ_{V(𝔪)}(M)` for every `i ≤ s`. -/
@[stacks 0DXK "the full statement: an element outside `p` annihilating the cohomology of the \
derived `I`-adic completion of `RΓ_{V(𝔪)}(M)` in every degree `≤ s`"]
theorem exists_notMem_mem_annihilator_homology_derivedCompletion_localCohomology_maximalIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (p : PrimeSpectrum A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d)
    (hdepth : enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt (ringKrullDim (A ⧸ p.asIdeal)) > ((d + s : ℤ) : EInt))
    {r : ℕ} (gen : Fin r → A) (hgen : Ideal.span (Set.range gen) = I) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ i : ℤ, i ≤ s →
      f ∈ Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((DerivedCompletion.derivedCompletionFunctor A gen).obj
            ((Dualizing.derivedPowerTorsionProperty A (maximalIdeal A)
                (maximalIdeal A).fg_of_isNoetherianRing).ι.obj
              ((Dualizing.localCohomologyFunctor.{u, u} A (maximalIdeal A)
                  (maximalIdeal A).fg_of_isNoetherianRing).obj
                ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                  (ModuleCat.of A M)))))) := by
  have hIfg : I.FG := I.fg_of_isNoetherianRing
  have hmfg : (maximalIdeal A).FG := (maximalIdeal A).fg_of_isNoetherianRing
  by_cases hp : p.asIdeal = maximalIdeal A
  · have hdepthM : ((d + s : ℤ) : EInt) < enatToEInt (Module.depth A (maximalIdeal A) M) := by
      rw [depth_localizedModule_eq_depth_maximalIdeal M p.asIdeal hp] at hdepth
      have hdim : ringKrullDim (A ⧸ p.asIdeal) = 0 := by
        rw [hp]
        let _ : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
        exact ringKrullDim_eq_zero_of_field (A ⧸ maximalIdeal A)
      rwa [hdim, show krullDimToEInt (0 : WithBot ℕ∞) = 0 from rfl, add_zero] at hdepth
    have hnle : (((d + s + 1).toNat : ℕ) : ℕ∞) ≤ Module.depth A (maximalIdeal A) M :=
      natCast_toNat_succ_le_of_lt_enatToEInt hdepthM
    have hGE := Stacks.LocalCohomology.isGE_localCohomologyDerived_single A
      (maximalIdeal A) hmfg (ModuleCat.of A M)
    exact exists_notMem_mem_annihilator_homology_derivedCompletion_of_iso I p s d hcd gen _ _
      (derivedCompletionIsoDerivedHomLocalCohomology A I hIfg gen hgen _)
      (fun j hj => ⟨1, p.isPrime.one_notMem, by
        have hzero := isZero_localCohomologyModule_maximalIdeal_of_lt_depth M
          (d + s + 1).toNat hnle j
          (lt_of_lt_of_le (by omega) (Int.self_le_toNat (d + s + 1)))
        exact Module.mem_annihilator.mpr fun x =>
          (ModuleCat.isZero_iff_subsingleton.mp hzero).elim _ _⟩)
  · have hpAway : p ∉ PrimeSpectrum.zeroLocus ((maximalIdeal A : Ideal A) : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) := fun hpV =>
      hp ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le p.isPrime.ne_top
        ((PrimeSpectrum.mem_zeroLocus _ _).mp hpV.1)).symm
    refine exists_notMem_mem_annihilator_homology_derivedCompletion_localCohomology A M I
      (maximalIdeal A) p s d omega homega hpAway hcd ?_ gen hgen
    intro x y hx hy _
    have hyM : y.asIdeal = maximalIdeal A :=
      ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le y.isPrime.ne_top
        ((PrimeSpectrum.mem_zeroLocus _ _).mp hy.1)).symm
    rw [add_comm s d, ringKrullDim_localizationAtPrime_quotient_eq x.asIdeal y.asIdeal hyM]
    exact lt_depth_add_ringKrullDim_quotient_of_le omega homega p x hx (d + s) hdepth

end Stacks.Algebraization

end
