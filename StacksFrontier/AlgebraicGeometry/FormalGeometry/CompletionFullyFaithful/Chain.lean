module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleEmbedding
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsCompleteClosure
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsCompleteLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SheafHomLocallyFree
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionSectionwiseCriteria
public import StacksFrontier.AlgebraicGeometry.Modules.SectionsLeftExact
import StacksCore.Tactic.StacksAttribute

/-!
# The chain of sectionwise criteria for full faithfulness of the completion functor

Let `X` be a Noetherian scheme, let `Y ⊆ X` be a closed subscheme with ideal sheaf `I`, and let
`Y_n ⊆ X` be the `n`-th infinitesimal neighbourhood of `Y` in `X`. [Stacks, Tag 0EKP] considers
the four conditions

1. `X` is quasi-affine and `Γ(X, 𝒪_X) → lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism;
2. `X` has an ample invertible module `L` and `Γ(X, L^{⊗ m}) → lim Γ(Y_n, L^{⊗ m}|_{Y_n})` is an
   isomorphism for all `m ≫ 0`;
3. for every finite locally free `𝒪_X`-module `ℰ` the map `Γ(X, ℰ) → lim Γ(Y_n, ℰ|_{Y_n})` is an
   isomorphism;
4. the completion functor `Coh(𝒪_X) → Coh(X, I)` of [Stacks, Tag 0880] is fully faithful on the
   full subcategory of finite locally free objects,

and asserts `(1) ⇒ (2) ⇒ (3) ⇒ (4)` together with `(4) ⇒ (3)`.

The isomorphisms in (1)–(3) are expressed by the universal property of the inverse limit:
`Stacks.Algebraization.IsInfinitesimalSectionsComplete` says that every compatible family of
sections over the infinitesimal neighbourhoods has a unique antecedent among the global sections.
The index `n` of `Stacks.Algebraization.nthInfinitesimalNeighbourhood` is the source's `n + 1`, so
the family of neighbourhoods swept out is exactly the source's `Y_1, Y_2, …`; the limit is
unchanged because the index set is cofinal. Conditions (1), (2) and (3) are the predicates
`Stacks.FundamentalGroup.SectionsCompleteQuasiAffine`, `SectionsCompleteAmplePowers` and
`SectionsCompleteFiniteLocallyFree`, and condition (4) is
`Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree`.

## Main results

* `Stacks.Algebraization.sectionsCompleteFiniteLocallyFree_of_sectionsCompleteAmplePowers` —
  **(2) ⇒ (3)**.
* `Stacks.Algebraization.completionFullyFaithful_of_sectionsCompleteFiniteLocallyFree` —
  **(3) ⇒ (4)**.
* `Stacks.Algebraization.sectionsCompleteFiniteLocallyFree_of_completionFullyFaithful` —
  **(4) ⇒ (3)**.
* `Stacks.Algebraization.sectionsComplete_chain` — all four implications.
* `Stacks.Algebraization.completionFullyFaithful_of_sectionsCompleteQuasiAffine` — the chain
  `(1) ⇒ (4)`.

## References

* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.FundamentalGroup (SectionsCompleteQuasiAffine SectionsCompleteAmplePowers
  SectionsCompleteFiniteLocallyFree)

noncomputable section

universe u

namespace Stacks.Algebraization

/-! ### (2) implies (3) -/

/-- If the global sections of all large tensor powers of an ample invertible module are the
inverse limit of their sections over the infinitesimal neighbourhoods of `i`, then so are those of
every finite locally free module: condition (2) of [Stacks, Tag 0EKP] implies condition (3). -/
public theorem sectionsCompleteFiniteLocallyFree_of_sectionsCompleteAmplePowers
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] [IsNoetherian X]
    (h : SectionsCompleteAmplePowers i) : SectionsCompleteFiniteLocallyFree i := by
  have : IsLocallyNoetherian X := AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
  obtain ⟨L, hL, hample, N, hN⟩ := h
  have hLinv : IsInvertibleModule X L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  have hampleA : IsAmple X L := (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple X L).mp hample
  have hSC : ∀ {r : ℤ} {ι : Type u} [Finite ι] {b : Bicone fun _ : ι => tensorPowModule X L (-r)},
      b.IsBilimit → (N : ℤ) ≤ r → IsInfinitesimalSectionsComplete i (dualSheaf b.pt) := by
    intro r _ _ b hb hr
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ((Int.natCast_nonneg N).trans hr)
    exact isInfinitesimalSectionsComplete_bicone_pt i (dualBicone b) (dualBicone_isBilimit b hb)
      fun _ => isInfinitesimalSectionsComplete_of_iso i (dualTensorPowIso X L m)
        (isInfinitesimalSectionsComplete_of_iso i
          (Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X L m) (hN m (by lia)))
  intro E hE
  obtain ⟨p, q, ιp, ιq, hιp, hιq, hpN, hqN, bp, hbp, bq, hbq, q₀, hq₀, β, w, hrefl, hmono, hex,
    huniv⟩ := exists_dual_embedding L hampleA (N : ℤ) E hE
  refine isInfinitesimalSectionsComplete_of_sectionsKernel i _ β w
    (Stacks.AlgebraicGeometry.Modules.injective_app_of_mono _ ⊤)
    (fun u hu => Stacks.AlgebraicGeometry.Modules.exists_app_eq_of_exact _ β w hex ⊤ u hu)
    (fun n => ?_) (hSC hbp hpN) (hSC hbq hqN)
  have := huniv _ (nthInfinitesimalNeighbourhoodι i n)
  exact Stacks.AlgebraicGeometry.Modules.injective_app_of_mono _ ⊤

/-! ### (3) implies (4) and (4) implies (3) -/

/-- If the global sections of every finite locally free module are the inverse limit of their
sections over the infinitesimal neighbourhoods of `i`, then the completion functor is fully
faithful on finite locally free modules: condition (3) of [Stacks, Tag 0EKP] implies
condition (4). -/
public theorem completionFullyFaithful_of_sectionsCompleteFiniteLocallyFree
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (h : SectionsCompleteFiniteLocallyFree i) :
    CompletionFullyFaithfulOnFiniteLocallyFree X i.ker := by
  intro F G hF hG
  refine completionFunctor_map_bijective i.ker F G
    (isIso_globalSectionsToLimit_of_isInfinitesimalSectionsComplete i
      (internalHomCoherent X F G) (h _ ?_))
  exact Stacks.AlgebraicGeometry.SheafHomLocallyFree.isFiniteLocallyFree_internalHomCoherent
    F G hF hG

/-- If the completion functor is fully faithful on finite locally free modules, then the global
sections of every finite locally free module are the inverse limit of their sections over the
infinitesimal neighbourhoods of `i`: condition (4) of [Stacks, Tag 0EKP] implies
condition (3). -/
public theorem sectionsCompleteFiniteLocallyFree_of_completionFullyFaithful
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
    (h : CompletionFullyFaithfulOnFiniteLocallyFree X i.ker) :
    SectionsCompleteFiniteLocallyFree i := by
  intro E hE
  exact isInfinitesimalSectionsComplete_of_completionFullyFaithful i h
    ⟨E, Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree X E⟩ hE

/-! ### The four implications -/

/-- Let `X` be a Noetherian scheme, let `Y ⊆ X` be a closed subscheme and let `Y_n ⊆ X` be the
`n`-th infinitesimal neighbourhood of `Y` in `X`. Consider the conditions

1. `X` is quasi-affine and `Γ(X, 𝒪_X) → lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism;
2. `X` has an ample invertible module `L` and `Γ(X, L^{⊗ m}) → lim Γ(Y_n, L^{⊗ m}|_{Y_n})` is an
   isomorphism for all `m ≫ 0`;
3. for every finite locally free `𝒪_X`-module `ℰ` the map `Γ(X, ℰ) → lim Γ(Y_n, ℰ|_{Y_n})` is an
   isomorphism;
4. the completion functor `Coh(𝒪_X) → Coh(X, I)` is fully faithful on the full subcategory of
   finite locally free objects.

Then `(1) ⇒ (2) ⇒ (3) ⇒ (4)` and `(4) ⇒ (3)`. -/
@[stacks 0EKP]
public theorem sectionsComplete_chain {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
    [IsNoetherian X] :
    (SectionsCompleteQuasiAffine i → SectionsCompleteAmplePowers i) ∧
      (SectionsCompleteAmplePowers i → SectionsCompleteFiniteLocallyFree i) ∧
      (SectionsCompleteFiniteLocallyFree i →
        CompletionFullyFaithfulOnFiniteLocallyFree X i.ker) ∧
      (CompletionFullyFaithfulOnFiniteLocallyFree X i.ker →
        SectionsCompleteFiniteLocallyFree i) :=
  have : IsLocallyNoetherian X := AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
  ⟨fun h => quasiAffine_sectionsComplete_implies_amplePower_sectionsComplete i h.1 h.2,
    sectionsCompleteFiniteLocallyFree_of_sectionsCompleteAmplePowers i,
    completionFullyFaithful_of_sectionsCompleteFiniteLocallyFree i,
    sectionsCompleteFiniteLocallyFree_of_completionFullyFaithful i⟩

/-- The chain `(1) ⇒ (4)` of [Stacks, Tag 0EKP]: on a Noetherian quasi-affine scheme whose global
functions are the inverse limit of the functions on the infinitesimal neighbourhoods, the
completion functor is fully faithful on finite locally free coherent modules. -/
public theorem completionFullyFaithful_of_sectionsCompleteQuasiAffine {X Y : Scheme.{u}}
    (i : Y ⟶ X) [IsClosedImmersion i] [IsNoetherian X] (h : SectionsCompleteQuasiAffine i) :
    CompletionFullyFaithfulOnFiniteLocallyFree X i.ker :=
  have hc := sectionsComplete_chain i
  hc.2.2.1 (hc.2.1 (hc.1 h))

end Stacks.Algebraization

end

end
