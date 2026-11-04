module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRegularity
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionPackageConstruction
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.KernelHyperplaneChain
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.KernelHyperplaneRestriction

/-!
# The hyperplane step of the induction of [Stacks, Tag 08AG]

Let `k` be an infinite field, `𝒬` a coherent sheaf on `ℙ^{n+1}_k` and `q : 𝒪^{⊕r} ⟶ 𝒬` an
epimorphism with kernel `𝒦`. This file produces, in one theorem, everything the inductive step of
[Stacks, Tag 08AG] needs of a hyperplane:

* a coherent sheaf `𝒢` on `ℙⁿ_k` which is again the kernel of an epimorphism `𝒪^{⊕r} ⟶ 𝒬'` of
  the same rank, so that the inductive hypothesis applies to it;
* the Hilbert polynomial of `𝒬'` is the first difference of that of `𝒬`, so that the polynomial
  the inductive hypothesis is applied with is `P(t) - P(t-1)`;
* and, from `b`-regularity of `𝒢` for any `b`, the chain data
  `AlgebraicGeometry.KernelChainData` for `𝒦` at `b`, which is what
  `AlgebraicGeometry.exists_isMRegular_kernel_free_of_kernelChainData` consumes.

## Main results

* `AlgebraicGeometry.exists_kernelChainData_of_hyperplane`: the three items above, for one
  hyperplane.

## The mathematics

One hyperplane has to serve all three terms of `0 ⟶ 𝒦 ⟶ 𝒪^{⊕r} ⟶ 𝒬 ⟶ 0`, which is
[Stacks, Tag 08A1]: `AlgebraicGeometry.exists_restrictionSequences_pullbackRes_forall` chooses it
at the direct sum `𝒪^{⊕r} ⊕ 𝒬`, and the associated points of all three terms are among those of
that sum — for `𝒦` because it is a subsheaf of `𝒪^{⊕r}` ([Stacks, Tag 05AE],
`AlgebraicGeometry.associatedPoints_subset_of_mono`).

With that hyperplane the restriction of the sequence stays short exact
(`AlgebraicGeometry.mono_pullback_hyperplaneι_map_f` and
`AlgebraicGeometry.shortExact_map_pullback_of_mono`), so the restricted kernel is the kernel of a
surjection of `𝒪^{⊕r}` onto the restricted quotient
(`AlgebraicGeometry.epi_pullbackFreeQuotientHom_and_nonempty_iso`); the Hilbert polynomial of the
restricted quotient is the first difference
(`AlgebraicGeometry.hilbertPolynomial_sub_eq_of_restrictionSequence`); and the restriction
sequences for `𝒦` with the canonical arrows assemble into a hyperplane restriction package whose
`G` is the restriction of `𝒦` — the assembly is that of
`AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage`, carried out here as a structure so
that the regularity hypothesis of `AlgebraicGeometry.kernelChainDataOfPackage` can be stated about
the restriction of `𝒦` itself.

## References

* [Stacks Project, Tag 08AG](https://stacks.math.columbia.edu/tag/08AG)
* [Stacks Project, Tag 08A1](https://stacks.math.columbia.edu/tag/08A1)
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 08AC](https://stacks.math.columbia.edu/tag/08AC)
* [Stacks Project, Tag 05AE](https://stacks.math.columbia.edu/tag/05AE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication (hyperplaneι)

universe u

namespace AlgebraicGeometry

attribute [local instance] isCoherent_projectiveTwist

/-- **The hyperplane step of [Stacks, Tag 08AG].** For an infinite field `k`, a coherent sheaf
`𝒬` on `ℙ^{n+1}_k` and an epimorphism `q : 𝒪^{⊕r} ⟶ 𝒬`, there are a coherent sheaf `𝒢` on
`ℙⁿ_k`, a coherent sheaf `𝒬'` on `ℙⁿ_k` and an epimorphism `q' : 𝒪^{⊕r} ⟶ 𝒬'` such that

* `𝒢 ≅ ker q'`, so `𝒢` is again the kernel of a surjection of the rank-`r` free module;
* the Hilbert polynomial of `𝒬'` is the first difference of that of `𝒬`;
* for every `b`, `b`-regularity of `𝒢` produces `AlgebraicGeometry.KernelChainData` for
  `ker q` at `b`.

See the module documentation for the proof. -/
theorem exists_kernelChainData_of_hyperplane (k : Type u) [Field k] [Infinite k] (n r : ℕ)
    (Q : (projectiveSpaceOverRing (n + 1) (.of k)).Modules) [Q.IsCoherent]
    (q : freeModules k (n + 1) r ⟶ Q) [Epi q] :
    ∃ (G : (projectiveSpaceOverRing n (.of k)).Modules) (hGc : G.IsCoherent)
      (Q' : (projectiveSpaceOverRing n (.of k)).Modules) (hQ'c : Q'.IsCoherent)
      (q' : freeModules k n r ⟶ Q') (_ : Epi q'),
      Nonempty (G ≅ kernel q') ∧
      (∀ d : ℤ, @hilbertPolynomial k _ n Q' hQ'c d
        = hilbertPolynomial k (n + 1) Q d - hilbertPolynomial k (n + 1) Q (d - 1)) ∧
      ∀ b : ℤ, @IsMRegular k _ n G hGc b →
        Nonempty (KernelChainData k (n + 1) (kernel q) b) := by
  have : IsLocallyNoetherian (projectiveSpaceOverRing (n + 1) (.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian (n + 1) (Spec (.of k))
  have : IsLocallyNoetherian (projectiveSpaceOverRing n (.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian n (Spec (.of k))
  have hKc : (kernel q).IsCoherent := CoherentAbelian.isCoherent_kernel q
  -- the sheaf whose associated points the hyperplane is chosen to avoid
  set fam : Bool → (projectiveSpaceOverRing (n + 1) (.of k)).Modules :=
    fun b => bif b then freeModules k (n + 1) r else Q with hfam
  have hfamc : ∀ b : Bool, (fam b).IsCoherent := by
    intro b
    cases b
    · exact inferInstanceAs Q.IsCoherent
    · exact inferInstanceAs (freeModules k (n + 1) r).IsCoherent
  have hAc : (∐ fam).IsCoherent :=
    CoherentAbelian.isCoherent_of_stacksIsCoherent
      (Stacks.SheafOfModules.isCoherent_sigma _ fun b =>
        CoherentAbelian.stacksIsCoherent_of_isCoherent (h := hfamc b))
  obtain ⟨j, hjaff, hjci, hjover, s, φ, θ1, hjeq, hres, hall⟩ :=
    exists_restrictionSequences_pullbackRes_forall k n (∐ fam) hAc
  have := hjci
  have := hjaff
  -- the kernel sequence and the three monicity facts the hyperplane provides
  set S : ShortComplex (projectiveSpaceOverRing (n + 1) (.of k)).Modules :=
    ShortComplex.mk (kernel.ι q) q (kernel.condition q) with hSdef
  have hS : S.ShortExact := ⟨ShortComplex.kernelSequence_exact q⟩
  have hAE : Stacks.Divisors.associatedPoints (freeModules k (n + 1) r) ⊆
      Stacks.Divisors.associatedPoints (∐ fam) :=
    associatedPoints_subset_of_mono (Limits.Sigma.ι fam true)
  have hAQ : Stacks.Divisors.associatedPoints Q ⊆
      Stacks.Divisors.associatedPoints (∐ fam) :=
    associatedPoints_subset_of_mono (Limits.Sigma.ι fam false)
  have hAK : Stacks.Divisors.associatedPoints (kernel q) ⊆
      Stacks.Divisors.associatedPoints (∐ fam) := fun x hx =>
    hAE (associatedPoints_subset_of_mono (kernel.ι q) hx)
  obtain ⟨hmK, hseqK⟩ := hall (kernel q) hKc hAK
  obtain ⟨hmE, -⟩ := hall (freeModules k (n + 1) r) inferInstance hAE
  obtain ⟨hmQ, hseqQ⟩ := hall Q inferInstance hAQ
  -- the restriction of the kernel sequence is short exact
  have hmono_i : Mono ((Scheme.Modules.pullback
      (hyperplaneι (n + 1) (Spec (.of k)) s)).map S.f) :=
    mono_pullback_hyperplaneι_map_f k (n + 1) s hS hmK hmE hmQ
  have hmono_j : Mono ((Scheme.Modules.pullback j).map S.f) := by
    rw [hjeq]
    exact mono_pullback_map_of_isoComp φ _ S.f hmono_i
  obtain ⟨hepi', ⟨eK⟩⟩ :=
    epi_pullbackFreeQuotientHom_and_nonempty_iso j q
      (shortExact_map_pullback_of_mono j hS hmono_j)
  -- the identifications of the twists along `j`, in every degree
  obtain ⟨θ, hθ1, hθ⟩ :=
    Stacks.AlgebraicGeometry.PullbackTwistRegrouping.exists_regroupingFamily (n + 1) n
      (Spec (.of k)) j θ1
  have hGc : ((Scheme.Modules.pullback j).obj (kernel q)).IsCoherent :=
    isCoherent_pullback j (kernel q)
  have hQ'c : ((Scheme.Modules.pullback j).obj Q).IsCoherent := isCoherent_pullback j Q
  -- the square that the `liftSection` clause of the package reduces to
  have hsq : ∀ σ : (twistOver n (Spec (.of k)) 1).sections,
      ∃ σ' : (twistOver (n + 1) (Spec (.of k)) 1).sections, ∀ d : ℤ,
        Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul (n + 1)
            (Spec (.of k)) (kernel q) σ' d ≫ pullbackTwistUnitRes j (kernel q) θ (d + 1) =
          pullbackTwistUnitRes j (kernel q) θ d ≫ (Scheme.Modules.pushforward j).map
            (Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul n
              (Spec (.of k)) ((Scheme.Modules.pullback j).obj (kernel q)) σ d) := by
    intro σ
    obtain ⟨σ', hσ'⟩ := exists_sectionHom_eq_of_surjective_restriction k n θ1 hres σ
    rw [← hθ1] at hσ'
    refine ⟨σ', fun d => ?_⟩
    exact pushforward_square_pullbackTwistUnitRes k n (kernel q) θ σ' σ d
      (Stacks.AlgebraicGeometry.PullbackTwistSectionMul.pullback_twistSectionMul (n + 1) n
        (Spec (.of k)) j (kernel q) d (θ d) (θ 1) (θ (d + 1)) (hθ d) σ' σ hσ')
  -- the hyperplane restriction package for the kernel, with `G` its restriction
  let P : HyperplaneRestrictionPackage k n (kernel q) :=
    { G := (Scheme.Modules.pullback j).obj (kernel q)
      isCoherent := hGc
      j := j
      isAffineHom := hjaff
      s := s
      res := pullbackTwistUnitRes j (kernel q) θ
      comp_res := fun d => (hseqK θ d).choose
      shortExact := fun d => (hseqK θ d).choose_spec
      shortExact' := fun d => exists_shortExact_of_index_eq k n (kernel q) θ s (d - 1) d
        (sub_add_cancel d 1) (hseqK θ (d - 1)).choose (hseqK θ (d - 1)).choose_spec
      compare := fun d => projectiveHPushforwardIso k j hjover
        (projectiveTwist n ((Scheme.Modules.pullback j).obj (kernel q)) d) 0
      liftSection := liftsSectionAlong_of_pushforward_square k n (kernel q)
        ((Scheme.Modules.pullback j).obj (kernel q)) hjover
        (pullbackTwistUnitRes j (kernel q) θ) hsq }
  have : IsClosedImmersion P.j := hjci
  refine ⟨(Scheme.Modules.pullback j).obj (kernel q), hGc,
    (Scheme.Modules.pullback j).obj Q, hQ'c, pullbackFreeQuotientHom j q, hepi',
    ⟨eK⟩, fun d => ?_, fun b hb =>
      ⟨kernelChainDataOfPackage k n (kernel q) P hjover b hb⟩⟩
  -- the Hilbert polynomial of the restricted quotient is the first difference
  obtain ⟨a, w, hSEd⟩ := exists_shortExact_of_index_eq k n Q θ s (d - 1) d (sub_add_cancel d 1)
    (hseqQ θ (d - 1)).choose (hseqQ θ (d - 1)).choose_spec
  have : (projectiveTwist n ((Scheme.Modules.pullback j).obj Q) d).IsCoherent :=
    isCoherent_projectiveTwist n ((Scheme.Modules.pullback j).obj Q) d
  have : (projectiveTwist n ((Scheme.Modules.pullback j).obj Q) d).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have : ((Scheme.Modules.pushforward j).obj
      (projectiveTwist n ((Scheme.Modules.pullback j).obj Q) d)).IsCoherent :=
    ProperCoherenceWitness.isCoherent_pushforward j
      (projectiveTwist n ((Scheme.Modules.pullback j).obj Q) d)
  exact (hilbertPolynomial_sub_eq_of_restrictionSequence k n hjover Q
    ((Scheme.Modules.pullback j).obj Q) hQ'c d hSEd (Iso.refl _) (Iso.refl _) (Iso.refl _)).symm

/-! ### The induction on the dimension, and the descent to an arbitrary field -/

/-- **[Stacks, Tag 08AG] over an infinite field**, by the source's induction on `n`.

For `n = 0` there is nothing to prove: `m`-regularity on `ℙ⁰_k` is a condition on cohomology in
degrees between one and zero. For the step,
`AlgebraicGeometry.exists_kernelChainData_of_hyperplane` restricts the sequence to a hyperplane;
the restricted kernel is again the kernel of a surjection of `𝒪^{⊕r}`, and the Hilbert polynomial
of the restricted quotient is `P(t) - P(t-1)`, so the inductive hypothesis makes it `m'`-regular
for an `m'` depending only on `n`, `r` and `P - P(t-1)`. Raising `m'` to `b = max m' 0` by
[Stacks, Tag 08A6] gives the chain data at `b`, and
`AlgebraicGeometry.exists_isMRegular_kernel_free_of_kernelChainData` turns it into `m`-regularity
of the kernel upstairs at the degree `AlgebraicGeometry.kernelRegularityBound (n+1) P b`. -/
theorem exists_isMRegular_kernel_free_of_hilbertPolynomial_of_infinite (n r : ℕ) (hr : 1 ≤ r)
    (P : Polynomial ℚ) :
    ∃ m : ℤ, ∀ (k : Type u) [Field k] [Infinite k]
      (Q : (projectiveSpaceOverRing n (.of k)).Modules) [Q.IsCoherent]
      (q : freeModules k n r ⟶ Q) [Epi q],
      (∀ d : ℤ, (hilbertPolynomial k n Q d : ℚ) = P.eval (d : ℚ)) →
      @IsMRegular k _ n (kernel q) (CoherentAbelian.isCoherent_kernel q) m := by
  induction n generalizing P with
  | zero =>
    refine ⟨0, ?_⟩
    intro k _ _ Q _ q _ _ i hi hle
    exact absurd hle (by omega)
  | succ n ih =>
    obtain ⟨m', hm'⟩ := ih (P - P.comp (Polynomial.X - 1))
    refine ⟨(exists_isMRegular_kernel_free_of_kernelChainData (n + 1) r hr P (max m' 0)
      (le_max_right _ _)).choose, ?_⟩
    intro k _ _ Q hQ q hq hP
    have := hQ
    have := hq
    obtain ⟨G, hGc, Q', hQ'c, q', hq', ⟨eG⟩, hHilb, hchain⟩ :=
      exists_kernelChainData_of_hyperplane k n r Q q
    have := hGc
    have := hq'
    have hP' : ∀ d : ℤ, (@hilbertPolynomial k _ n Q' hQ'c d : ℚ)
        = (P - P.comp (Polynomial.X - 1)).eval (d : ℚ) := by
      intro d
      have h2 : ((hilbertPolynomial k (n + 1) Q (d - 1) : ℤ) : ℚ) = P.eval ((d : ℚ) - 1) := by
        have h := hP (d - 1)
        push_cast at h
        exact h
      rw [hHilb d, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_one]
      push_cast
      rw [hP d, h2]
    have hreg' := hm' k Q' q' hP'
    have hregG : @IsMRegular k _ n G hGc (max m' 0) :=
      isMRegular_of_le k n G (isMRegular_of_iso k n (CoherentAbelian.isCoherent_kernel q')
        hGc eG.symm hreg') (le_max_left _ _)
    obtain ⟨D⟩ := hchain (max m' 0) hregG
    exact (exists_isMRegular_kernel_free_of_kernelChainData (n + 1) r hr P (max m' 0)
      (le_max_right _ _)).choose_spec k Q q D hP

/-- **[Stacks, Tag 08AG].** Let `n ≥ 0`, `r ≥ 1` and `P ∈ ℚ[t]`. There is a single integer `m`
such that for **every** field `k`, every coherent sheaf `𝒬` on `ℙⁿ_k` with Hilbert polynomial `P`
and every epimorphism `q : 𝒪^{⊕r} ⟶ 𝒬`, the kernel of `q` is `m`-regular.

The quantifier order is the statement: `m` is produced from `n`, `r` and `P` alone, before the
field and before the sequence.

Over an infinite field this is
`AlgebraicGeometry.exists_isMRegular_kernel_free_of_hilbertPolynomial_of_infinite`, the source's
induction on the dimension. An arbitrary field is reduced to that case by base change to the
rational function field `k(t)`, which is infinite (`AlgebraicGeometry.infinite_ratFunc`):
`ℙⁿ_{k(t)} ⟶ ℙⁿ_k` is flat, so the kernel sequence base-changes to the kernel sequence of a
surjection of `𝒪^{⊕r}` onto the base change of `𝒬`; the Hilbert polynomial is unchanged
([Stacks, Tag 08AB], `AlgebraicGeometry.hilbertPolynomial_pullback_fieldExtension`); and
`m`-regularity descends along the extension by [Stacks, Tag 08A4],
`AlgebraicGeometry.isMRegular_iff_fieldExtension`. -/
@[stacks 08AG "with the free sheaf of the source, the short exact sequence read as an \
epimorphism from it, and the Hilbert polynomial of Tag 08AD compared with a rational polynomial \
at every integer"]
theorem exists_isMRegular_kernel_free_of_hilbertPolynomial (n r : ℕ) (hr : 1 ≤ r)
    (P : Polynomial ℚ) :
    ∃ m : ℤ, ∀ (k : Type u) [Field k]
      (Q : (projectiveSpaceOverRing n (.of k)).Modules) [Q.IsCoherent]
      (q : freeModules k n r ⟶ Q) [Epi q],
      (∀ d : ℤ, (hilbertPolynomial k n Q d : ℚ) = P.eval (d : ℚ)) →
      @IsMRegular k _ n (kernel q) (CoherentAbelian.isCoherent_kernel q) m := by
  obtain ⟨m, hm⟩ := exists_isMRegular_kernel_free_of_hilbertPolynomial_of_infinite n r hr P
  refine ⟨m, ?_⟩
  intro k _ Q hQ q hq hP
  have := hQ
  have := hq
  have : Infinite (RatFunc k) := infinite_ratFunc k
  have : IsLocallyNoetherian (projectiveSpaceOverRing n (.of (RatFunc k))) :=
    projectiveSpaceOver_isLocallyNoetherian n (Spec (.of (RatFunc k)))
  have hQK : ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj Q).IsCoherent :=
    isCoherent_pullback (projectiveSpaceFieldExtensionMap k (RatFunc k) n) Q
  have hKc : (kernel q).IsCoherent := CoherentAbelian.isCoherent_kernel q
  have hKK : ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj (kernel q)).IsCoherent :=
    isCoherent_pullback (projectiveSpaceFieldExtensionMap k (RatFunc k) n) (kernel q)
  have hS : (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact :=
    ⟨ShortComplex.kernelSequence_exact q⟩
  have : PreservesFiniteLimits (Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k (RatFunc k) n)) :=
    preservesFiniteLimits_modulesPullback_of_flat
      (projectiveSpaceFieldExtensionMap k (RatFunc k) n)
  have hmono : Mono ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).map (kernel.ι q)) :=
    preserves_mono_of_preservesLimit _ _
  obtain ⟨hepi, ⟨eK⟩⟩ := epi_pullbackFreeQuotientHom_and_nonempty_iso
    (projectiveSpaceFieldExtensionMap k (RatFunc k) n) q
    (shortExact_map_pullback_of_mono (projectiveSpaceFieldExtensionMap k (RatFunc k) n)
      hS hmono)
  have := hepi
  have hPK : ∀ d : ℤ, (@hilbertPolynomial (RatFunc k) _ n ((Scheme.Modules.pullback
        (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj Q) hQK d : ℚ)
      = P.eval (d : ℚ) := by
    intro d
    rw [hilbertPolynomial_pullback_fieldExtension k (RatFunc k) n Q hQK d]
    exact hP d
  have hreg := hm (RatFunc k) ((Scheme.Modules.pullback
    (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj Q)
    (pullbackFreeQuotientHom (projectiveSpaceFieldExtensionMap k (RatFunc k) n) q) hPK
  have hregK : @IsMRegular (RatFunc k) _ n ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj (kernel q)) hKK m :=
    isMRegular_of_iso (RatFunc k) n (CoherentAbelian.isCoherent_kernel _) hKK eK.symm hreg
  exact (isMRegular_iff_fieldExtension k (RatFunc k) n (kernel q) m).mpr hregK

end AlgebraicGeometry

end
