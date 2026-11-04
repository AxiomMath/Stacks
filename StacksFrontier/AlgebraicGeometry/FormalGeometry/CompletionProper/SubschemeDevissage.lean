module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ClosedImmersionEssSurj
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistenceSeparated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.GrothendieckExistenceII
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.Universal
public import StacksFrontier.AlgebraicGeometry.Scheme.SubschemeIdealJoin
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dévissage of Stacks 088C after replacing `X` by `V(K)`

The Noetherian induction of [Stacks, Tag 088C] is carried in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/Devissage.lean` over the
quasi-coherent ideal sheaves of `X`, and its inductive step enters there as the hypothesis `hDev`
of `Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`: a coherent `𝓘`-adic
system killed by `K` is in the essential image of the completion functor as soon as every system
killed by an ideal sheaf **strictly larger** than `K` is.

The source discharges that step by Chow's lemma, the projective case and Stacks 088A together
with 088B. Read naively on `X`, the step does not close: Stacks 088A consumes its hypothesis (1)
at the *powers* `𝒦 ᵉ⁺¹` of the ideal sheaf along which the comparison of 088B is annihilated, and
powers descend, so that family lies *below* `𝒦` while the induction hypothesis lives strictly
above `K`. The side condition `∀ e, K < 𝒦 ᵉ⁺¹` on an ideal sheaf `𝒦` of `X` cannot be met: it
forces `K < 𝒦` and places `K` strictly below a descending chain, and at `K = ⊤` nothing lies above
`K` at all.

The source does not read it on `X`. Its step opens

> After replacing `X` by the closed subscheme of `X` corresponding to `𝒦` we may assume that every
> nonzero `𝒦` is in `Ξ`. (This uses the correspondence by coherent modules annihilated by `𝒦` and
> coherent modules on the closed subscheme corresponding to `𝒦`, see [Stacks, Tag 087T].)

and only *then* applies Chow's lemma. So its `𝒦` is an ideal sheaf of `V(K)`, the ideal sheaves at
which hypothesis (1) is consumed are the **inverse images in `X`** of the powers `𝒦₀ ᵉ⁺¹ ⊆
𝒪_{V(K)}` — the joins `K ⊔ 𝒦₀ ᵉ⁺¹` of
`StacksFrontier/AlgebraicGeometry/Scheme/SubschemeIdealJoin.lean`, which lie above `K` by
construction — and those are not the powers of any ideal sheaf of `X`
(`Stacks.IdealSheafData.pow_map_le_map_pow`). This file carries that replacement.

## Main results

* `Stacks.Algebraization.exists_isProjectiveMorphism_denseChowModification_subschemeι` — **Chow's
  lemma on `V(K)`.** Unconditional:
  `AlgebraicGeometry.exists_isProjectiveMorphism_denseChowModification` applies to
  `K.subschemeι ≫ f`, which is proper because a closed immersion is.
* `Stacks.Algebraization.exists_chowModification_lt_map_subschemeι_pow` — **the replacement for
  the side condition, together with the data satisfying it.** Chow's lemma on `V(K)` produces a
  modification, a dense open `U ⊆ V(K)` over which it is an isomorphism, and the ideal sheaf
  `𝒦₀` cutting out the reduced complement `V(K) \ U`, and then **every** join
  `K ⊔ 𝒦₀ ᵉ⁺¹` lies strictly above `K`.
* `Stacks.Algebraization.essImage_completionFunctor_comap_subschemeι_of_essImage_of_ne_bot` —
  **the induction hypothesis transported to `V(K)` through [Stacks, Tag 087T]**: from the
  statement on `X` at ideal sheaves strictly above `K`, the same statement on `V(K)` at ideal
  sheaves strictly above `⊥`, i.e. at every nonzero ideal sheaf of `V(K)`. This is the source's
  "we may assume that every nonzero `𝒦` is in `Ξ`".
* `Stacks.Algebraization.isEquivalence_completionFunctor_comap_subschemeι_pow_of_essImage` —
  **hypothesis (1) of [Stacks, Tag 088A] on `V(K)`, in full**, from the induction hypothesis on
  `X` and the nonvanishing of the support of `𝒦₀`.
* `essImage_completionFunctor_comap_subschemeι_of_isKernelCokernelAnnihilatedByPower`
  — **Stacks 088A on `V(K)` with hypothesis (1) discharged.** The analogue of
  `Stacks.Algebraization.essImage_completionFunctor_of_devissageComparison` in the position the
  source occupies after the replacement; its unsatisfiable `hpow` has become the satisfiable
  `𝒦₀.support ≠ ⊤`.
* `Stacks.Algebraization.essImage_completionFunctor_of_essImage_comap_subschemeι` — the way back:
  a system on `X` killed by `K` is the direct image of a system on `V(K)`, and the essential image
  ascends along that direct image.
* `Stacks.Algebraization.essImage_completionFunctor_of_isEmpty` — **the base case.** The
  completion functor of a scheme with no points is essentially surjective, every sheaf of modules
  there being zero.
* `Stacks.Algebraization.essImage_completionFunctor_of_devissageSubscheme` — **the inductive step
  of [Stacks, Tag 088C], with the comparison of Stacks 088B on `V(K)` as the one remaining
  binder.** Everything else is proved.

## Implementation notes

**What the replacement buys, precisely.** The side condition is restated at the joins, and there
it reduces to a condition which the Chow data satisfies. Three facts of
`StacksFrontier/AlgebraicGeometry/Scheme/SubschemeIdealJoin.lean` do it:

1. `K ≤ 𝒦₀.map K.subschemeι` always, so the inverse image *is* the join `K ⊔ 𝒦₀`;
2. `K < 𝒦₀.map K.subschemeι ↔ 𝒦₀ ≠ ⊥` — strictness is exactly nonvanishing downstairs;
3. `𝒦₀.support ≠ ⊤ → 𝒦₀ ᵉ⁺¹ ≠ ⊥` for every `e`.

So the replacement for `hpow : ∀ e, K < 𝒦 ᵉ⁺¹` is `h𝒦₀ : 𝒦₀.support ≠ ⊤`, a condition on an ideal
sheaf of `V(K)`, and `Stacks.IdealSheafData.lt_map_subschemeι_pow_succ` converts it into
`∀ e, K < K ⊔ 𝒦₀ ᵉ⁺¹`. Chow's lemma supplies it: the complement of the dense open is a *proper*
closed subset of `V(K)` as soon as `V(K)` is nonempty, and the vanishing ideal of a closed set has
that set as its support.

**Where density and reducedness enter — and how little.** Only through `U ≠ ∅`. See the module
docstring of `StacksFrontier/AlgebraicGeometry/Scheme/SubschemeIdealJoin.lean`: the nonvanishing of
the powers follows from the support condition for an *arbitrary* ideal sheaf, so reducedness of
the complement is the source's choice of *which* ideal sheaf cuts out `V(K) \ U` — the largest,
the one whose support is that set on the nose — and not a hypothesis the argument consumes.
Reducedness would be needed only to pass between `𝒦₀ ≠ ⊥` and `𝒦₀.support ≠ ⊤`
(`AlgebraicGeometry.Scheme.IdealSheafData.support_eq_top_iff`), and `V(K)` is not reduced here.

**Nonemptiness of `V(K)` is the induction's base case, and it is discharged.** `V(K)` is empty
exactly when `K = ⊤`, where the side condition is unsatisfiable outright and where the systems
killed by `K` are the zero systems; there `hInd` says nothing, no ideal sheaf being strictly above
`⊤`. Chow's lemma does need it, so
`Stacks.Algebraization.exists_chowModification_lt_map_subschemeι_pow` carries
`[Nonempty K.subscheme]`; the step itself does not, because
`Stacks.Algebraization.essImage_completionFunctor_of_isEmpty` settles the empty case outright —
over a scheme with no points every sheaf of modules is zero, so every system is the completion of
every coherent module. The two cases are joined inside
`Stacks.Algebraization.essImage_completionFunctor_of_devissageChowSubscheme`.

**The transport through [Stacks, Tag 087T].** The induction hypothesis is a statement about
systems on `X`; what Stacks 088A on `V(K)` consumes is the same statement about systems on
`V(K)`. Passing between them is the content of 087T, and in the direction needed it is
`Stacks.Algebraization.essImage_completionFunctor_comap_subschemeι_of_essImage_of_ne_bot`: a
system `G` on `V(K)` killed by `L` has a termwise direct image which is a coherent adic system on
`X` (`Stacks.Coherent.isCoherentAdicSystem_pushforward_closedImmersion`) killed by the join
`K ⊔ L` (`Stacks.Coherent.idealPowerMultiple_pushforward_eq_bot_iff` and
`AlgebraicGeometry.Scheme.IdealSheafData.comap_map_le`), and the join is strictly above `K`
exactly when `L ≠ ⊥`; the induction hypothesis then algebraizes it by some `H`, which is itself
killed by `K` (the descent of annihilation from the completion,
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_isSystemAnnihilatedBy_completion_of_isProper`),
so 087T writes `H ≅ i_* S`, completion commutes with `i_*`
(`Stacks.Algebraization.pushforwardCompletionIso`) and the comparison descends
(`Stacks.Coherent.isoOfWhiskerRightPushforwardIso`). This is the proof of
`Stacks.Algebraization.essSurj_completionFunctor_comap_subschemeι_of_essImage` run at the single
ideal sheaf `K` instead of at a power, with the annihilating ideal sheaf allowed to be larger
than the one cutting out the subscheme.

**No Stacks tag attribute is attached to anything here.** Tag 088A sits on
`Stacks.Coherent.essImage_completionFunctor_of_isKernelCokernelAnnihilatedByPower`, tag 0200 on
`AlgebraicGeometry.hasDenseChowModification`, tag 087T on the carriers of
`StacksFrontier/AlgebraicGeometry/ClosedPushforward/Coherent.lean` and tag 088C on
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage`, whose `hDev` binder is left
exactly as it stands.

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent
open Stacks.AlgebraicGeometry.Tag087TCoherentImage

/-! ### Chow's lemma on the closed subscheme -/

/-- **Chow's lemma applied to `V(K)`.** Let `f : X ⟶ S` be proper with `S` Noetherian and let
`K ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals. Then the closed subscheme `V(K)` admits a proper
surjective modification `π`, an isomorphism over a dense open `U ⊆ V(K)`, which is H-projective
over `S`.

This is `AlgebraicGeometry.exists_isProjectiveMorphism_denseChowModification`, which is
unconditional, applied to `K.subschemeι ≫ f`; that composite is proper because a closed immersion
is proper and properness is stable under composition. This is the move the source makes after
replacing `X` by `V(K)`. -/
@[ega "II 5.6.1" "partial",
  sga "4 XII 7.1" "special case",
  sga "4 XVII 7.0.6" "special case",
  sga "4½ Arcata 3.4.3" "Modification π"]
public theorem exists_isProjectiveMorphism_denseChowModification_subschemeι
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsProper f] (K : X.IdealSheafData) :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ K.subscheme) (U : K.subscheme.Opens),
      IsProper π ∧ Surjective π ∧
        AlgebraicGeometry.IsProjectiveMorphism (π ≫ (K.subschemeι ≫ f)) ∧
          Dense (U : Set K.subscheme) ∧ IsIso (π ∣_ U) :=
  AlgebraicGeometry.exists_isProjectiveMorphism_denseChowModification (K.subschemeι ≫ f)

/-- **The replacement for the dévissage's side condition, together with the data satisfying
it.** Let `f : X ⟶ S` be proper with `S` Noetherian, let `K ⊆ 𝒪_X` be a quasi-coherent sheaf of
ideals and suppose `V(K)` is nonempty. Then there are a proper surjective `π : X'' ⟶ V(K)` which
is H-projective over `S` and an isomorphism over a dense open `U ⊆ V(K)`, and an ideal sheaf
`𝒦₀ ⊆ 𝒪_{V(K)}` — the one cutting out the **reduced** complement `V(K) \ U` — whose support is
that complement and for which

  `∀ e, K < K ⊔ 𝒦₀ ᵉ⁺¹`

holds, where `K ⊔ 𝒦₀ ᵉ⁺¹` denotes the inverse image in `X` of `𝒦₀ ᵉ⁺¹`.

**This is the statement that the unsatisfiable side condition becomes after the source's
replacement of `X` by `V(K)`, and unlike it, it is satisfied.** The side condition read on `X`
asked for an ideal sheaf `𝒦` of `X` with `∀ e, K < 𝒦 ᵉ⁺¹`, which is impossible. Read at the
joins it asks for an ideal sheaf `𝒦₀` of `V(K)` with `∀ e, 𝒦₀ ᵉ⁺¹ ≠ ⊥`
(`Stacks.IdealSheafData.lt_map_subschemeι_iff`), and the support condition gives that
(`Stacks.IdealSheafData.pow_succ_ne_bot_of_support_ne_top`) for an arbitrary ideal sheaf, with no
reducedness used — see the module docstring. What the geometry supplies is the support condition,
and it supplies it from the nonemptiness of the Chow open alone. -/
@[ega "II 5.6.1" "(i), special case, (ii)", sga "4 XVII 7.0.6" "special case"]
public theorem exists_chowModification_lt_map_subschemeι_pow
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsProper f] (K : X.IdealSheafData)
    [Nonempty K.subscheme] :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ K.subscheme) (U : K.subscheme.Opens)
      (𝒦₀ : K.subscheme.IdealSheafData),
      IsProper π ∧ Surjective π ∧
        AlgebraicGeometry.IsProjectiveMorphism (π ≫ (K.subschemeι ≫ f)) ∧
          Dense (U : Set K.subscheme) ∧ IsIso (π ∣_ U) ∧
            𝒦₀ = Scheme.IdealSheafData.vanishingIdeal
              (⟨(U : Set K.subscheme)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds K.subscheme) ∧
              𝒦₀.support ≠ ⊤ ∧
                ∀ e : ℕ, K < (𝒦₀ ^ (e + 1)).map K.subschemeι := by
  obtain ⟨X', π, U, hπ, hsurj, hproj, hU, hiso⟩ :=
    exists_isProjectiveMorphism_denseChowModification_subschemeι f K
  have hsupp : (Scheme.IdealSheafData.vanishingIdeal
      (⟨(U : Set K.subscheme)ᶜ, U.isOpen.isClosed_compl⟩ : Closeds K.subscheme)).support ≠ ⊤ :=
    Stacks.IdealSheafData.support_compl_ne_top_of_dense U hU
  exact ⟨X', π, U, _, hπ, hsurj, hproj, hU, hiso, rfl, hsupp,
    fun e => Stacks.IdealSheafData.lt_map_subschemeι_pow_succ K hsupp e⟩

/-- Annihilation by `K` (the first power) gives annihilation by the kernel of `K.subschemeι`. -/
private theorem annihilatedByKer_subschemeι_of_idealPowerMultiple_one_eq_bot
    {X : Scheme.{u}} {K : X.IdealSheafData} {M : X.Modules}
    (h : idealPowerMultiple K 1 M = ⊥) : AnnihilatedByKer K.subschemeι M := by
  have h2 := Stacks.Coherent.annihilatedByKer_subschemeι_pow_iff K 1 M
  rw [pow_one] at h2
  exact h2.mpr h

/-! ### The induction hypothesis transported to the closed subscheme -/

/-- **The induction hypothesis of [Stacks, Tag 088C], transported to `V(K)` through
[Stacks, Tag 087T].** Let `A` be Noetherian and complete with respect to `I`, let
`f : X ⟶ Spec A` be proper, set `𝓘 = I · 𝒪_X` and let `K ⊆ 𝒪_X` be a quasi-coherent sheaf of
ideals. Assume `hInd`, that every coherent `𝓘`-adic system on `X` killed by an ideal sheaf
strictly larger than `K` is in the essential image of the completion functor of `X`. Then every
coherent `𝓘 𝒪_{V(K)}`-adic system on `V(K)` killed by a **nonzero** ideal sheaf of `V(K)` is in
the essential image of the completion functor of `V(K)`.

This is the source's sentence "After replacing `X` by the closed subscheme of `X` corresponding to
`𝒦` we may assume that every nonzero `𝒦` is in `Ξ`", and the parenthesis the source attaches to
it — "this uses the correspondence by coherent modules annihilated by `𝒦` and coherent modules on
the closed subscheme" — is 087T, which is where the proof goes. **No hypothesis beyond `hInd`.**

The hypothesis is consumed at the inverse image `K ⊔ L` of the annihilating ideal sheaf `L` of
`V(K)`, which lies strictly above `K` exactly because `L ≠ ⊥`
(`Stacks.IdealSheafData.lt_map_subschemeι_iff`). This is the only place the order fact is used,
and it is what the replacement of `X` by `V(K)` is for. -/
public theorem essImage_completionFunctor_comap_subschemeι_of_essImage_of_ne_bot
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (K : X.IdealSheafData)
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ K' : X.IdealSheafData, K < K' →
        ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
          IsSystemAnnihilatedBy K' 𝓖.obj →
            (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsLocallyNoetherian K.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
    ∀ L : K.subscheme.IdealSheafData, L ≠ ⊥ →
      ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems
          ((baseIdealSheaf A I f).comap K.subschemeι),
        IsSystemAnnihilatedBy L 𝓖.obj →
          (completionFunctor K.subscheme
            ((baseIdealSheaf A I f).comap K.subschemeι)).essImage 𝓖 := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : IsLocallyNoetherian K.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
  obtain ⟨hff⟩ := fullyFaithful_completionFunctor_of_isProper A I f
  intro L hL G hGann
  -- Step 1: the ascent of membership in `Coh(-, -)` along the direct image.
  have hP : Stacks.Coherent.IsCoherentAdicSystem (baseIdealSheaf A I f)
      (G.obj ⋙ Scheme.Modules.pushforward K.subschemeι) :=
    isCoherentAdicSystem_pushforward_closedImmersion K.subschemeι
      (baseIdealSheaf A I f) G.obj G.property
  -- Step 2: the direct image is killed by the inverse image of `L`, the join `K ⊔ L`.
  have hann : IsSystemAnnihilatedBy (L.map K.subschemeι)
      (G.obj ⋙ Scheme.Modules.pushforward K.subschemeι) := fun n =>
    (idealPowerMultiple_pushforward_eq_bot_iff K.subschemeι (L.map K.subschemeι) 1
      (G.obj.obj (op n))).mpr
      (hGann.mono (Scheme.IdealSheafData.comap_map_le L K.subschemeι) n)
  -- Step 3: the induction hypothesis algebraizes it, the join being strictly above `K`.
  obtain ⟨H, ⟨eH⟩⟩ := hInd (L.map K.subschemeι)
    ((Stacks.IdealSheafData.lt_map_subschemeι_iff K L).mpr hL) ⟨_, hP⟩ hann
  have eHsys : ((completionFunctor X (baseIdealSheaf A I f)).obj H).obj ≅
      G.obj ⋙ Scheme.Modules.pushforward K.subschemeι :=
    (ObjectProperty.ι _).mapIso eH
  -- Step 4: the descent of annihilation from the completion.
  have hannK : IsSystemAnnihilatedBy K
      (G.obj ⋙ Scheme.Modules.pushforward K.subschemeι) :=
    hann.mono (Stacks.IdealSheafData.le_map_subschemeι K L)
  have hHann : idealPowerMultiple K 1 H.obj = ⊥ :=
    idealPowerMultiple_eq_bot_of_isSystemAnnihilatedBy_completion_of_isProper A I f K H
      (fun n => idealPowerMultiple_eq_bot_of_iso K (eHsys.app (op n)) 1 (hannK n))
  -- Step 5: Tag 087T writes `H` as a direct image.
  have hHcoh : H.obj.IsCoherent := H.property
  obtain ⟨S, hScoh, ⟨eS⟩⟩ := exists_isCoherent_pushforward_iso K.subschemeι H.obj
    (annihilatedByKer_subschemeι_of_idealPowerMultiple_one_eq_bot hHann)
  refine ⟨⟨S, hScoh⟩, ⟨?_⟩⟩
  -- Step 6: completion commutes with the direct image, and the comparison descends.
  refine ObjectProperty.isoMk _ (isoOfWhiskerRightPushforwardIso K.subschemeι ?_)
  refine (pushforwardCompletionIso K.subschemeι (baseIdealSheaf A I f) ⟨S, hScoh⟩).symm ≪≫ ?_
  refine ((ObjectProperty.ι _).mapIso
    ((completionFunctor X (baseIdealSheaf A I f)).mapIso
      (ObjectProperty.isoMk _ eS))) ≪≫ eHsys

/-! ### Hypothesis (1) of Stacks 088A on the closed subscheme -/

/-- **Hypothesis (1) of [Stacks, Tag 088A] on `V(K)`, in full, from the induction hypothesis on
`X`.** With `A`, `I`, `f` and `K` as above, let `𝒦₀ ⊆ 𝒪_{V(K)}` be a quasi-coherent sheaf of
ideals whose support is not the whole of `V(K)`. Granted `hInd`, the completion functor of the
closed subscheme `V(𝒦₀ ᵉ⁺¹)` of `V(K)`, along the inverse image of `𝓘`, is an equivalence for
every `e`.

This is the step at which the replacement pays off. The functor is an equivalence by
`Stacks.Algebraization.isEquivalence_completionFunctor_comap_subschemeι_of_essImage`, applied on
`V(K)` to `K.subschemeι ≫ f` — full faithfulness is unconditional, and essential surjectivity
needs the statement on `V(K)` at the ideal sheaf `𝒦₀ ᵉ⁺¹`, which
`Stacks.Algebraization.essImage_completionFunctor_comap_subschemeι_of_essImage_of_ne_bot` supplies
from `hInd` as soon as `𝒦₀ ᵉ⁺¹ ≠ ⊥`, and
`Stacks.IdealSheafData.pow_succ_ne_bot_of_support_ne_top` supplies *that* from the support
condition. Read on `X` the same step would need `hInd` at `𝒦 ᵉ⁺¹ > K`, which is unsatisfiable. -/
public theorem isEquivalence_completionFunctor_comap_subschemeι_pow_of_essImage
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (K : X.IdealSheafData)
    (𝒦₀ : K.subscheme.IdealSheafData) (h𝒦₀ : 𝒦₀.support ≠ ⊤)
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ K' : X.IdealSheafData, K < K' →
        ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
          IsSystemAnnihilatedBy K' 𝓖.obj →
            (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsLocallyNoetherian K.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
    ∀ e : ℕ,
      letI : IsLocallyNoetherian (𝒦₀ ^ (e + 1)).subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian
          ((𝒦₀ ^ (e + 1)).subschemeι ≫ (K.subschemeι ≫ f))
      (completionFunctor (𝒦₀ ^ (e + 1)).subscheme
        (((baseIdealSheaf A I f).comap K.subschemeι).comap
          (𝒦₀ ^ (e + 1)).subschemeι)).IsEquivalence := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : IsLocallyNoetherian K.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
  have hbase : (baseIdealSheaf A I f).comap K.subschemeι
      = baseIdealSheaf A I (K.subschemeι ≫ f) :=
    Stacks.PuncturedSpectrumPicard.baseIdealSheaf_comap A I f K.subschemeι
  have htr := essImage_completionFunctor_comap_subschemeι_of_essImage_of_ne_bot A I f K hInd
  rw [hbase] at htr
  intro e
  rw [hbase]
  exact isEquivalence_completionFunctor_comap_subschemeι_of_essImage A I
    (K.subschemeι ≫ f) 𝒦₀ e
    (htr (𝒦₀ ^ (e + 1)) (Stacks.IdealSheafData.pow_succ_ne_bot_of_support_ne_top h𝒦₀ e))

/-! ### Stacks 088A on the closed subscheme, hypothesis (1) discharged -/

/-- **Stacks 088A on `V(K)`, with hypothesis (1) discharged from the induction hypothesis on
`X`.** With `A`, `I`, `f`, `K`, `𝒦₀` and `hInd` as above and `𝒦₀.support ≠ ⊤`: any object
`(𝓕_n)` of `Coh(V(K), 𝓘 𝒪_{V(K)})` admitting the comparison data of [Stacks, Tag 088A] — a
coherent `𝒪_{V(K)}`-module `H` and a map `α : (𝓕_n) ⟶ H ^∧` whose levelwise kernels and cokernels
are annihilated by a power of `𝒦₀` — is in the essential image of the completion functor of
`V(K)`.

**This is the statement `Stacks.Algebraization.essImage_completionFunctor_of_devissageComparison`
is in the position the source occupies after replacing `X` by `V(K)`, with its side condition
replaced by one that can be met.** There the condition was `hpow : ∀ e, K < 𝒦 ᵉ⁺¹` on an ideal
sheaf `𝒦` of `X`, which no `𝒦` satisfies; here it is `h𝒦₀ : 𝒦₀.support ≠ ⊤` on an ideal sheaf of
`V(K)`, and `Stacks.Algebraization.exists_chowModification_lt_map_subschemeι_pow` produces an
ideal sheaf satisfying it out of Chow's lemma.

Noetherianity of `V(K)` is not assumed: local Noetherianity comes from `LocallyOfFiniteType` over
the Noetherian base and quasi-compactness from the universal closedness of `K.subschemeι ≫ f`. -/
public theorem essImage_completionFunctor_comap_subschemeι_of_isKernelCokernelAnnihilatedByPower
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (K : X.IdealSheafData)
    (𝒦₀ : K.subscheme.IdealSheafData) (h𝒦₀ : 𝒦₀.support ≠ ⊤)
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ K' : X.IdealSheafData, K < K' →
        ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
          IsSystemAnnihilatedBy K' 𝓖.obj →
            (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI : IsLocallyNoetherian K.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
    ∀ (𝓕 : Stacks.Coherent.CoherentAdicSystems
        ((baseIdealSheaf A I f).comap K.subschemeι))
      (H : AlgebraicGeometry.SheafOfModules.CoherentModules K.subscheme.ringCatSheaf)
      (α : 𝓕.obj ⟶ ((completionFunctor K.subscheme
        ((baseIdealSheaf A I f).comap K.subschemeι)).obj H).obj),
      IsKernelCokernelAnnihilatedByPower 𝒦₀ α →
        (completionFunctor K.subscheme
          ((baseIdealSheaf A I f).comap K.subschemeι)).essImage 𝓕 := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : IsLocallyNoetherian K.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
  let _ : CompactSpace K.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (K.subschemeι ≫ f)
  let _ : IsNoetherian K.subscheme := { }
  intro 𝓕 H α hα
  exact essImage_completionFunctor_of_isKernelCokernelAnnihilatedByPower
    ((baseIdealSheaf A I f).comap K.subschemeι) 𝒦₀ 𝓕
    (isEquivalence_completionFunctor_comap_subschemeι_pow_of_essImage A I f K 𝒦₀ h𝒦₀ hInd)
    H (ObjectProperty.homMk α) hα

/-! ### The way back to `X` -/

/-- **The essential image ascends from `V(K)` to `X` along the direct image, at the systems killed
by `K`.** With `A`, `I`, `f` and `K` as above, assume that every coherent `𝓘 𝒪_{V(K)}`-adic system
on `V(K)` is in the essential image of the completion functor of `V(K)`. Then every coherent
`𝓘`-adic system on `X` killed by `K` is in the essential image of the completion functor of `X`.
**No further hypothesis.**

This is the other half of the source's replacement of `X` by `V(K)` — the half that undoes it —
and it is [Stacks, Tag 087T] again, at the level of systems. A system `(𝓕_n)` killed by `K` is
termwise the direct image of a coherent module on `V(K)`
(`Stacks.Coherent.ClosedImmersion.exists_system_pushforward_iso`, which assembles the termwise
087T into an isomorphism of systems), the system downstairs is a coherent adic system
(`Stacks.Coherent.isCoherentAdicSystem_of_pushforward`), the hypothesis algebraizes it, and
completion commutes with the direct image
(`Stacks.Algebraization.pushforwardCompletionIso`). -/
public theorem essImage_completionFunctor_of_essImage_comap_subschemeι
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (K : X.IdealSheafData)
    (hsub : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      letI : IsLocallyNoetherian K.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
      ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems
          ((baseIdealSheaf A I f).comap K.subschemeι),
        (completionFunctor K.subscheme
          ((baseIdealSheaf A I f).comap K.subschemeι)).essImage 𝓖) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
      IsSystemAnnihilatedBy K 𝓕.obj →
        (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓕 := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : IsLocallyNoetherian K.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
  intro 𝓕 hann
  -- Each term of `(𝓕_n)` is killed by the ideal sheaf cutting out `V(K)`.
  obtain ⟨Q, hQcoh, ⟨eQ⟩⟩ :=
    Stacks.Coherent.exists_system_pushforward_iso K.subschemeι 𝓕.obj
      (fun n => 𝓕.property.1 n.unop)
      fun n => annihilatedByKer_subschemeι_of_idealPowerMultiple_one_eq_bot (hann n.unop)
  have hQ : Stacks.Coherent.IsCoherentAdicSystem
      ((baseIdealSheaf A I f).comap K.subschemeι) Q :=
    Stacks.Coherent.isCoherentAdicSystem_of_pushforward K.subschemeι
      (baseIdealSheaf A I f) Q hQcoh
      (Stacks.Coherent.isCoherentAdicSystem_of_iso (baseIdealSheaf A I f) eQ.symm 𝓕.property)
  -- The hypothesis algebraizes it downstairs, and completion commutes with the direct image.
  obtain ⟨S, ⟨eS⟩⟩ := hsub ⟨Q, hQ⟩
  refine ⟨pushforwardCoherentObj K.subschemeι S, ⟨ObjectProperty.isoMk _ ?_⟩⟩
  refine pushforwardCompletionIso K.subschemeι (baseIdealSheaf A I f) S ≪≫ ?_
  exact Functor.isoWhiskerRight ((ObjectProperty.ι _).mapIso eS)
    (Scheme.Modules.pushforward K.subschemeι) ≪≫ eQ

/-! ### The base case: a scheme with no points -/

/-- **The completion functor of a scheme with no points is essentially surjective.** Over such a
scheme every sheaf of modules is zero, so any two are isomorphic
(`Stacks.Modules.isoOfIsEmpty`) and so are any two inverse systems of them; a system is therefore
the completion of any coherent module whatever, and the system's own zeroth term is one.

This is the base case of the Noetherian induction of [Stacks, Tag 088C]: it is applied below at
`V(K)` for `K = ⊤`, where the induction hypothesis says nothing because no ideal sheaf is
strictly above `⊤`. -/
public theorem essImage_completionFunctor_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (𝓕 : Stacks.Coherent.CoherentAdicSystems I) :
    (completionFunctor X I).essImage 𝓕 :=
  ⟨⟨𝓕.obj.obj (op 0), 𝓕.property.1 0⟩,
    ⟨ObjectProperty.isoMk _
      (NatIso.ofComponents (fun _ => Stacks.Modules.isoOfIsEmpty X _ _)
        (fun _ => (Stacks.Modules.subsingleton_hom_of_isEmpty X _ _).allEq _ _))⟩⟩

/-! ### The inductive step of Stacks 088C, with Stacks 088B on `V(K)` as the only binder -/

/-- **The inductive step of the Noetherian induction of [Stacks, Tag 088C], carried out after the
source's replacement of `X` by `V(K)`.** Let `A` be Noetherian and complete with respect to `I`,
let `f : X ⟶ Spec A` be proper, set `𝓘 = I · 𝒪_X` and let `K ⊆ 𝒪_X` be a quasi-coherent sheaf of
ideals. Let `𝒦₀ ⊆ 𝒪_{V(K)}` be a quasi-coherent sheaf of ideals whose support is not the whole of
`V(K)` and assume

* `hInd`, the antecedent of `hDev`: every coherent `𝓘`-adic system on `X` killed by an ideal sheaf
  **strictly larger** than `K` is in the essential image of the completion functor of `X`; and
* `hComp`, the comparison of [Stacks, Tag 088B] on `V(K)` at `𝒦₀`: every coherent
  `𝓘 𝒪_{V(K)}`-adic system on `V(K)` admits a coherent `𝒪_{V(K)}`-module `H` and a map into its
  completion whose levelwise kernels and cokernels are annihilated by a power of `𝒦₀`.

Then every coherent `𝓘`-adic system on `X` killed by `K` is in the essential image of the
completion functor of `X` — which is the consequent of `hDev` at `K`.

**Everything between those two hypotheses and the conclusion is proved here, and `hInd` is the
dévissage's own antecedent.** So the distance from this statement to the `hDev` binder of
`Stacks.Algebraization.isEquivalence_completionFunctor_of_devissage` is exactly `hComp`, the
comparison of Stacks 088B at a general base, plus the production of `𝒦₀` from Chow's lemma, which
`Stacks.Algebraization.exists_chowModification_lt_map_subschemeι_pow` carries. The side condition
that made the step unreachable on `X` is gone: here it is the support condition on an ideal sheaf
of `V(K)`, which the Chow data satisfies. -/
public theorem essImage_completionFunctor_of_devissageSubscheme
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (K : X.IdealSheafData)
    (𝒦₀ : K.subscheme.IdealSheafData) (h𝒦₀ : 𝒦₀.support ≠ ⊤)
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ K' : X.IdealSheafData, K < K' →
        ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
          IsSystemAnnihilatedBy K' 𝓖.obj →
            (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖)
    (hComp : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      letI : IsLocallyNoetherian K.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
      ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems
          ((baseIdealSheaf A I f).comap K.subschemeι),
        ∃ (H : AlgebraicGeometry.SheafOfModules.CoherentModules K.subscheme.ringCatSheaf)
          (α : 𝓖.obj ⟶ ((completionFunctor K.subscheme
            ((baseIdealSheaf A I f).comap K.subschemeι)).obj H).obj),
          IsKernelCokernelAnnihilatedByPower 𝒦₀ α) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
      IsSystemAnnihilatedBy K 𝓕.obj →
        (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓕 := by
  refine essImage_completionFunctor_of_essImage_comap_subschemeι A I f K fun 𝓖 => ?_
  obtain ⟨H, α, hα⟩ := hComp 𝓖
  exact essImage_completionFunctor_comap_subschemeι_of_isKernelCokernelAnnihilatedByPower
    A I f K 𝒦₀ h𝒦₀ hInd 𝓖 H α hα

/-- **The same step with `𝒦₀` produced by Chow's lemma, so that the only binder left is the
comparison of [Stacks, Tag 088B] on `V(K)`.** Let `A` be Noetherian and complete with respect to
`I`, let `f : X ⟶ Spec A` be proper and let `K ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals with
`V(K)` nonempty. Granted

* `hInd`, the antecedent of `hDev`, and
* `hComp`, Stacks 088B on `V(K)` asked at the Chow data — for every proper surjective
  `π : X'' ⟶ V(K)` which is H-projective over `Spec A` and an isomorphism over a dense open
  `U ⊆ V(K)`, and for the ideal sheaf `𝒦₀` cutting out the reduced complement `V(K) \ U`, every
  coherent adic system on `V(K)` admits the comparison of Stacks 088B at `𝒦₀`,

every coherent `𝓘`-adic system on `X` killed by `K` is in the essential image.

**This is the inductive step of the dévissage of Stacks 088C with one binder, and that binder is
Stacks 088B at a general base.** `hComp` is the output of
`Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_essImage`
run on `V(K)` with `π` the Chow modification: the projective case of Grothendieck existence
(Stacks 0885, which holds outright by
`Stacks.Algebraization.isEquivalenceCompletionFunctorOfIsProjectiveMorphism_holds`) algebraizes
the pullback of the system along `π`, the coherence of a proper direct image (Stacks 02O5) makes
`H = π_* 𝓕'` coherent, and `π` is an isomorphism over `U = V(𝒦₀)ᶜ`, which is the condition that
appears there as `hc`. What is not carried is 088B's own remaining binder at a general base; over
an **affine** base it is unconditional,
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`.

The side condition which made the step unreachable on `X` does not appear: it has become the
support condition on `𝒦₀`, and Chow's lemma discharges it. -/
public theorem essImage_completionFunctor_of_devissageChowSubscheme
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (K : X.IdealSheafData)
    (hInd : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ K' : X.IdealSheafData, K < K' →
        ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
          IsSystemAnnihilatedBy K' 𝓖.obj →
            (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓖)
    (hComp : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      letI : IsLocallyNoetherian K.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
      ∀ (X' : Scheme.{u}) (π : X' ⟶ K.subscheme) (U : K.subscheme.Opens),
        IsProper π → Surjective π →
          AlgebraicGeometry.IsProjectiveMorphism (π ≫ (K.subschemeι ≫ f)) →
            Dense (U : Set K.subscheme) → IsIso (π ∣_ U) →
              ∀ 𝓖 : Stacks.Coherent.CoherentAdicSystems
                  ((baseIdealSheaf A I f).comap K.subschemeι),
                ∃ (H : AlgebraicGeometry.SheafOfModules.CoherentModules
                    K.subscheme.ringCatSheaf)
                  (α : 𝓖.obj ⟶ ((completionFunctor K.subscheme
                    ((baseIdealSheaf A I f).comap K.subschemeι)).obj H).obj),
                  IsKernelCokernelAnnihilatedByPower
                    (Scheme.IdealSheafData.vanishingIdeal
                      (⟨(U : Set K.subscheme)ᶜ, U.isOpen.isClosed_compl⟩ :
                        Closeds K.subscheme)) α) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
      IsSystemAnnihilatedBy K 𝓕.obj →
        (completionFunctor X (baseIdealSheaf A I f)).essImage 𝓕 := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : IsLocallyNoetherian K.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (K.subschemeι ≫ f)
  rcases isEmpty_or_nonempty K.subscheme with hK | hK
  · -- `V(K) = ∅`, i.e. `K = ⊤`: the base case, where `hInd` says nothing.
    let _ := hK
    exact essImage_completionFunctor_of_essImage_comap_subschemeι A I f K
      fun 𝓖 => essImage_completionFunctor_of_isEmpty _ 𝓖
  · let _ := hK
    obtain ⟨X', π, U, 𝒦₀, hπ, hsurj, hproj, hU, hiso, rfl, h𝒦₀, -⟩ :=
      exists_chowModification_lt_map_subschemeι_pow f K
    exact essImage_completionFunctor_of_devissageSubscheme A I f K _ h𝒦₀ hInd
      (hComp X' π U hπ hsurj hproj hU hiso)

end Stacks.Algebraization

end
