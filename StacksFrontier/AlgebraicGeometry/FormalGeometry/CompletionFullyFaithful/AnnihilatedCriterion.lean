module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Chain
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsBridge
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ComplementSections

/-!
# The annihilation criterion for full faithfulness of the completion functor

Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A` and let `U = Spec(A) ∖ V(𝔞)`. Stacks 0EKS asserts
that if `A` is `f`-adically complete and `H¹_𝔞(A)` and `H²_𝔞(A)` are annihilated by powers of
`f`, then the completion functor `Coh(𝒪_U) ⟶ Coh(U, (f)𝒪_U)` of Stacks 0880 is fully faithful on
the full subcategory of finite locally free objects.

The source's proof is two lines: Stacks 0EKP reduces the assertion to the equality
`Γ(U, 𝒪_U) = lim Γ(U, 𝒪_U/fⁿ𝒪_U)`, and Stacks 0EII supplies that equality.

## Main results

* `Stacks.Algebraization.sectionsCompleteQuasiAffine_complementPrincipalIdealSheaf` — condition
  (1) of Stacks 0EKP for the zero locus of `f` on `U`, from Stacks 0EII.
* `Stacks.Algebraization.completionFullyFaithful_of_annihilated` — the completion functor is fully
  faithful on finite locally free objects.

## Implementation notes

Condition (1) of Stacks 0EKP is `Stacks.FundamentalGroup.SectionsCompleteQuasiAffine`: the
ambient scheme is quasi-affine, and its structure sheaf is infinitesimal-sections-complete along
the closed immersion. The first conjunct is
`Stacks.Algebraization.isQuasiAffine_complementZeroLocus`. The second is Stacks 0EII, which is
stated at the module level as bijectivity of
`Stacks.Algebraization.ComplementTower.sectionsToLimit`; it becomes the sheaf-level comparison
of the completion functor by
`Stacks.Algebraization.isIso_globalSectionsToLimit_coherentPrincipalTilde`, and that comparison
is infinitesimal sections completeness by
`Stacks.Algebraization.isInfinitesimalSectionsComplete_of_isIso_globalSectionsToLimit`. The
module it is applied to is `A` itself, whose associated sheaf on `U` is `𝒪_U` by
`Stacks.LocalCohomology.complementTildeRingIsoUnit`. Stacks 0EKP then runs from (1) to (4) as
`Stacks.Algebraization.completionFullyFaithful_of_sectionsCompleteQuasiAffine`.

## References

* [Stacks Project, Tag 0EKS](https://stacks.math.columbia.edu/tag/0EKS)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.LocalCohomology
open Stacks.FundamentalGroup (SectionsCompleteQuasiAffine)

universe u

namespace Stacks.Algebraization

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A) (f : A)

/-- **Condition (1) of Stacks 0EKP at the zero locus of `f` on `U = Spec(A) ∖ V(𝔞)`.** Let `A` be
a Noetherian ring which is `f`-adically complete, and let `f ∈ 𝔞`. If `H¹_𝔞(A)` and `H²_𝔞(A)` are
annihilated by powers of `f`, then `U` is quasi-affine and `Γ(U, 𝒪_U)` is the inverse limit of
the sections of the structure sheaves of the infinitesimal neighbourhoods of `V(f) ∩ U`. -/
public theorem sectionsCompleteQuasiAffine_complementPrincipalIdealSheaf (hf : f ∈ a)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (h1 : ∃ n, ∀ x : localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a)
      (ModuleCat.of A A) 1, f ^ n • x = 0)
    (h2 : ∃ n, ∀ x : localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a)
      (ModuleCat.of A A) 2, f ^ n • x = 0) :
    SectionsCompleteQuasiAffine (complementPrincipalIdealSheaf A a f).subschemeι := by
  have := hcomplete
  obtain ⟨c₁, h1'⟩ := h1
  obtain ⟨c₂, h2'⟩ := h2
  have hbij : Function.Bijective (ComplementTower.sectionsToLimit A a f (ModuleCat.of A A)) :=
    ComplementTower.bijective_sectionsToLimit a f (ModuleCat.of A A) c₁ c₂ h1' h2'
  have hiso := isIso_globalSectionsToLimit_coherentPrincipalTilde hf (ModuleCat.of A A) hbij
  rw [principalIdealOnOpen_eq,
    ← Scheme.IdealSheafData.ker_subschemeι (complementPrincipalIdealSheaf A a f)] at hiso
  refine ⟨isQuasiAffine_complementZeroLocus A a,
    isInfinitesimalSectionsComplete_of_iso _ (complementTildeRingIsoUnit A a) ?_⟩
  exact isInfinitesimalSectionsComplete_of_isIso_globalSectionsToLimit _
    (coherentPrincipalTilde hf (ModuleCat.of A A)) hiso

/-- Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A` and let `U = Spec(A) ∖ V(𝔞)`. If `A` is
`f`-adically complete and `H¹_𝔞(A)` and `H²_𝔞(A)` are annihilated by powers of `f`, then the
completion functor `Coh(𝒪_U) ⟶ Coh(U, (f)𝒪_U)`, `ℱ ↦ ℱ^∧`, is fully faithful on the full
subcategory of finite locally free objects. -/
@[stacks 0EKS]
public theorem completionFullyFaithful_of_annihilated (hf : f ∈ a)
    (hcomplete : IsAdicComplete (Ideal.span {f}) A)
    (h1 : ∃ n, ∀ x : localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a)
      (ModuleCat.of A A) 1, f ^ n • x = 0)
    (h2 : ∃ n, ∀ x : localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a)
      (ModuleCat.of A A) 2, f ^ n • x = 0) :
    CompletionFullyFaithfulOnFiniteLocallyFree (complementZeroLocus A a : Scheme)
      (complementPrincipalIdealSheaf A a f) := by
  have h := completionFullyFaithful_of_sectionsCompleteQuasiAffine
    (complementPrincipalIdealSheaf A a f).subschemeι
    (sectionsCompleteQuasiAffine_complementPrincipalIdealSheaf A a f hf hcomplete h1 h2)
  rwa [Scheme.IdealSheafData.ker_subschemeι] at h

end Stacks.Algebraization

end
