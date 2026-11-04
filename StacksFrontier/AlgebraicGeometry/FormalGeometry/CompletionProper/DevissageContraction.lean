module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ClosedSubschemeEquivalence

/-!
# Replacing `X` by the closed subscheme `V(𝒦)` in the dévissage of Tag 088C

The Noetherian induction of [Stacks, Tag 088C] runs over the quasi-coherent ideal sheaves of a
Noetherian scheme `X`: writing

  `Ξ = { 𝒦 ⊆ 𝒪_X : every object of Coh(X, ℐ) killed by 𝒦 is in the essential image of the
         completion functor }`,

the inductive step has to prove `𝒦 ∈ Ξ` knowing `𝒦' ∈ Ξ` for every ideal sheaf `𝒦' > 𝒦`. At that
point the source says

> After replacing `X` by the closed subscheme of `X` corresponding to `𝒦` we may assume that
> every nonzero `𝒦` is in `Ξ`.

**This file performs that replacement**, in the direction in which it transports data: it carries
the two things the inductive step has in hand on the ambient scheme `X` — membership in `Ξ`, and
full faithfulness of the completion functor — down to the closed subscheme `Z = V(𝒦)`. The point
is the change of indexing. On `X` the induction hypothesis speaks about ideal sheaves *strictly
greater than* `𝒦`; on `Z` the same information reads as a statement about the *nonzero* ideal
sheaves of `Z`, and in that form it applies to the ideal sheaves the rest of the argument
produces — in particular to the powers `ℒ ᵉ⁺¹`, which are never `> 𝒦` and so are out of reach of
the uncontracted hypothesis.

The mechanism is the correspondence of [Stacks, Tag 087T] in the shape of the pushforward of
ideal sheaves. For a closed immersion `i : Z ⟶ X` and an ideal sheaf `ℒ ⊆ 𝒪_Z`, Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.map` produces `ℒ · 𝒪_X ⊆ 𝒪_X`, the ideal sheaf cutting
out `V_Z(ℒ)` inside `X`, and

* a module on `Z` killed by `ℒ` has direct image killed by `ℒ · 𝒪_X`
  (`Stacks.Coherent.idealPowerMultiple_pushforward_eq_bot_of_le_map`), and
* `ℒ ≠ 0` exactly forces `ℒ · 𝒪_X > ker(i)` (`Stacks.Coherent.ker_lt_map_of_ne_bot`).

Those two facts turn the induction hypothesis at `ℒ · 𝒪_X` into `Ξ`-membership of `ℒ` on `Z`.
Essential surjectivity is then transported by the argument of
`Stacks.Coherent.isEquivalence_completionFunctor_subscheme_of_essImage`: the direct image of a
system on `Z` killed by `ℒ` is a system on `X` killed by `ℒ · 𝒪_X`, hence algebraizable by the
hypothesis, and the algebraization is itself killed by `ker(i)` — not formally, but because the
projection onto its quotient by `ker(i)` has invertible completion, which is
`Stacks.Coherent.idealPowerMultiple_eq_bot_of_completion_eq_bot`. Full faithfulness is
`Stacks.Coherent.fullyFaithful_completionFunctor_comap`, which is already available.

## Main results

* `Stacks.Coherent.idealPowerMultiple_pushforward_eq_bot_of_le_map` — direct image along a closed
  immersion turns annihilation by `ℒ` into annihilation by any ideal sheaf of `X` below
  `ℒ · 𝒪_X`.
* `Stacks.Coherent.ker_lt_map_of_ne_bot` — a nonzero ideal sheaf of `Z` pushes forward to an
  ideal sheaf strictly larger than the one cutting out `Z`. This is the order-theoretic half of
  the contraction: it is what makes "nonzero on `V(𝒦)`" a consequence of "strictly larger than
  `𝒦` on `X`".
* `Stacks.Coherent.essImage_completionFunctor_comap_of_essImage` — **`Ξ`-membership descends along
  a closed immersion.** If every object of `Coh(X, ℐ)` killed by `𝒥` is in the essential image of
  the completion functor of `X`, then every object of `Coh(Z, ℐ 𝒪_Z)` killed by an `ℒ` with
  `𝒥 ≤ ℒ · 𝒪_X` is in the essential image of the completion functor of `Z`.
* `Stacks.Coherent.essImage_completionFunctor_subscheme_of_lt` — **the contraction.** From the
  induction hypothesis of [Stacks, Tag 088C] at `𝒦`, every object of `Coh(V(𝒦), ℐ 𝒪_{V(𝒦)})`
  killed by a *nonzero* ideal sheaf of `V(𝒦)` is in the essential image.
* `Stacks.Coherent.isEquivalence_completionFunctor_pow_subscheme_of_lt` — hypothesis (1) of
  [Stacks, Tag 088A] on `V(𝒦)`, for an ideal sheaf `ℒ` all of whose positive powers are nonzero,
  from the induction hypothesis on `X`.
* `Stacks.Coherent.essImage_completionFunctor_subscheme_of_lt_of_kernelCokernel` —
  [Stacks, Tag 088A] on `V(𝒦)` with hypothesis (1) discharged by the induction hypothesis on `X`,
  so that only hypothesis (2), the map `α` of [Stacks, Tag 088B], is left to supply.

## Implementation notes

Nothing here is registered against a Stacks tag: this is one step inside the proof of
[Stacks, Tag 088C], not a tag proved under its own hypotheses. The stacks-087T attribute sits on
`Stacks.ClosedImmersion.pushforwardCohEquivalence`, which is the input used below.

The hypothesis `∀ e, ℒ ᵉ⁺¹ ≠ ⊥` of the last two results is *not* a consequence of `ℒ ≠ ⊥`: an
ideal sheaf can be nonzero and nilpotent. In the source it is supplied by the geometry of Chow's
lemma, where `ℒ` cuts out the *reduced* complement of a *dense* open, so that `ℒ` is contained in
no minimal prime of any affine coordinate ring and therefore has no vanishing power. That
deduction belongs to the Chow step and is not carried here; the hypothesis is stated as an
explicit input so that the contraction itself is clean.

The statements about `Z` are phrased for an arbitrary closed immersion `i : Z ⟶ X`, with the ideal
sheaf cutting out `Z` spelled `i.ker`; the consumer-facing forms specialize to
`𝒦.subscheme` and `𝒦.subschemeι`, which is the shape
`Stacks.Coherent.isEquivalence_completionFunctor_pow_of_essImage` and
`Stacks.Coherent.fullyFaithful_completionFunctor_comap` are stated in. Local Noetherianity of `Z`
is never an extra hypothesis: it is `AlgebraicGeometry.isLocallyNoetherian_of_isClosedImmersion`,
supplied by a `letI` in the statement as elsewhere in this directory.

What this file does **not** do is transport the *conclusion* back up: from essential surjectivity
on `V(𝒦)` to `𝒦 ∈ Ξ` on `X`. That direction needs essential surjectivity of
`Stacks.Coherent.coherentAdicPushforwardClosed` onto the `𝒦`-annihilated part of `Coh(X, ℐ)` —
the analogue of [Stacks, Tag 087T] for adic systems rather than for single modules — which the
library carries only in the fully faithful half,
`Stacks.Coherent.fullyFaithfulCoherentAdicPushforwardClosed`.

## References

* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-- **Annihilation by an ideal sheaf passes to smaller ideal sheaves.** If `𝒥' ⁿ M` vanishes and
`𝒥 ≤ 𝒥'`, then `𝒥 ⁿ M` vanishes, because `𝒥(U) ⁿ ≤ 𝒥'(U) ⁿ` on every affine open. -/
public theorem idealPowerMultiple_eq_bot_of_le_ideal {X : Scheme.{u}}
    {J J' : X.IdealSheafData} (h : J ≤ J') (n : ℕ) {M : X.Modules}
    (hM : idealPowerMultiple J' n M = ⊥) : idealPowerMultiple J n M = ⊥ :=
  idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U _ ha x =>
    affine_sections_annihilated_of_idealPowerMultiple_eq_bot hM U
      (pow_le_pow_left' (Scheme.IdealSheafData.le_def.mp h U) n ha) x

end Stacks.Algebraization

namespace Stacks.Coherent

/-! ### Pushing an ideal sheaf forward along a closed immersion -/

section

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The kernel of `V_Z(ℒ) ⟶ Z ⟶ X` is `ℒ · 𝒪_X`. -/
private theorem ker_subschemeι_comp_eq_map {Y W : Scheme.{u}} (j : W ⟶ Y)
    (L : W.IdealSheafData) : (L.subschemeι ≫ j).ker = L.map j := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]

/-- **Direct image turns annihilation by `ℒ` into annihilation by `ℒ · 𝒪_X`**, and hence by any
ideal sheaf of `X` below it.

A module on `Z` killed by `ℒ` is, by [Stacks, Tag 08KS], the direct image of a module on the
closed subscheme `V_Z(ℒ)`; so its direct image along `i` is a direct image along
`V_Z(ℒ) ⟶ Z ⟶ X`, whose kernel is exactly `ℒ · 𝒪_X`, and a direct image is killed by the ideal
sheaf cutting out its source. -/
public theorem idealPowerMultiple_pushforward_eq_bot_of_le_map
    (J : X.IdealSheafData) (L : Z.IdealSheafData) (hJL : J ≤ L.map i)
    {G : Z.Modules} (hG : idealPowerMultiple L 1 G = ⊥) :
    idealPowerMultiple J 1 ((Scheme.Modules.pushforward i).obj G) = ⊥ := by
  have hAnn : Stacks.ClosedImmersion.AnnihilatedByKer L.subschemeι G :=
    (Stacks.ClosedImmersion.annihilatedByKer_iff_ker_ideal L.subschemeι G).mpr
      fun V a ha m =>
        affine_sections_annihilated_of_idealPowerMultiple_eq_bot hG V
          (by rw [pow_one]; rwa [Scheme.IdealSheafData.ker_subschemeι] at ha) m
  obtain ⟨G', ⟨eG⟩⟩ :=
    (Stacks.ClosedImmersion.pushforward_essImage_iff L.subschemeι G).mpr hAnn
  refine idealPowerMultiple_eq_bot_of_le_ideal hJL 1 ?_
  refine idealPowerMultiple_eq_bot_of_iso (L.map i)
    (((Scheme.Modules.pushforward i).mapIso eG).symm ≪≫
      (Scheme.Modules.pushforwardComp L.subschemeι i).app G') 1 ?_
  rw [← ker_subschemeι_comp_eq_map i L]
  exact idealPowerMultiple_ker_pushforward_eq_bot (L.subschemeι ≫ i) G'

/-- **A nonzero ideal sheaf of `Z` pushes forward to an ideal sheaf strictly larger than the one
cutting out `Z`.**

This is the order-theoretic content of the source's replacement of `X` by `V(𝒦)`: under it, the
nonzero ideal sheaves of `V(𝒦)` go to ideal sheaves strictly containing `𝒦`, which is the range
in which the Noetherian induction hypothesis of [Stacks, Tag 088C] is available.

The inequality is monotonicity of pushforward together with `ker(i) = 0 · 𝒪_X`. It is strict
because equality would make `V_Z(ℒ) ⟶ X` and `Z ⟶ X` two closed immersions with the same kernel,
forcing `V_Z(ℒ) ⟶ Z` to be an isomorphism (`AlgebraicGeometry.IsClosedImmersion.isIso_of_ker_eq`)
and hence `ℒ = 0`. -/
public theorem ker_lt_map_of_ne_bot (L : Z.IdealSheafData) (hL : L ≠ ⊥) : i.ker < L.map i := by
  refine lt_of_le_of_ne ?_ fun h => hL ?_
  · rw [← Scheme.IdealSheafData.map_bot i]
    exact Scheme.IdealSheafData.map_mono i bot_le
  · have : IsIso L.subschemeι :=
      IsClosedImmersion.isIso_of_ker_eq (L.subschemeι ≫ i) i L.subschemeι rfl
        (by rw [ker_subschemeι_comp_eq_map, ← h])
    rw [← Scheme.IdealSheafData.ker_subschemeι L]
    exact Scheme.Hom.ker_eq_bot_of_isIso _

/-! ### Membership in `Ξ` descends to a closed subscheme -/

/-- **Membership in the family `Ξ` of [Stacks, Tag 088C] descends along a closed immersion.** Let
`i : Z ⟶ X` be a closed immersion into a locally Noetherian scheme, `ℐ ⊆ 𝒪_X` a quasi-coherent
sheaf of ideals, and suppose

* the completion functor `Coh(𝒪_X) ⥤ Coh(X, ℐ)` of [Stacks, Tag 0880] is fully faithful, and
* every object of `Coh(X, ℐ)` killed by `𝒥` is in its essential image, that is `𝒥 ∈ Ξ`.

Then every object of `Coh(Z, ℐ 𝒪_Z)` killed by an ideal sheaf `ℒ ⊆ 𝒪_Z` with `𝒥 ≤ ℒ · 𝒪_X` is in
the essential image of the completion functor of `Z`.

Taking `ℒ = 0`, so that `ℒ · 𝒪_X = ker(i)`, recovers the essential-surjectivity half of
`Stacks.Coherent.isEquivalence_completionFunctor_subscheme_of_essImage`; the point of the extra
generality is that `ℒ ≠ 0` lets the hypothesis be the induction hypothesis of
[Stacks, Tag 088C], which is available only *strictly above* `ker(i)`.

The direct image `(i_* N_n)` of an object `(N_n)` of `Coh(Z, ℐ 𝒪_Z)` killed by `ℒ` is killed by
`ℒ · 𝒪_X` and hence by `𝒥`, so by hypothesis it is `M ^∧_ℐ` for a coherent `𝒪_X`-module `M`. It
is also killed by `ker(i)`, being a direct image, so the terms of `M ^∧_ℐ` are; that `M` itself
is killed by `ker(i)` is *not* automatic and is where full faithfulness enters a second time,
through `Stacks.Coherent.idealPowerMultiple_eq_bot_of_completion_eq_bot`. Then
`M ^∧_ℐ ≅ i_* ((i^* M) ^∧_{ℐ𝒪_Z})`, and `i_*` is fully faithful on adic systems, so
`(i^* M) ^∧_{ℐ𝒪_Z} ≅ (N_n)`. -/
public theorem essImage_completionFunctor_comap_of_essImage [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (L : Z.IdealSheafData) (hJL : J ≤ L.map i)
    (hff : (completionFunctor X I).FullyFaithful)
    (hJ : ∀ 𝓖 : CoherentAdicSystems I, IsSystemAnnihilatedBy J 𝓖.obj →
      (completionFunctor X I).essImage 𝓖) :
    letI : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
    ∀ 𝓝 : CoherentAdicSystems (I.comap i), IsSystemAnnihilatedBy L 𝓝.obj →
      (completionFunctor Z (I.comap i)).essImage 𝓝 := by
  let : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  let := (fullyFaithfulCoherentAdicPushforwardClosed i I).full
  let := (fullyFaithfulCoherentAdicPushforwardClosed i I).faithful
  intro N hN
  have hannKer : IsSystemAnnihilatedBy i.ker
      ((coherentAdicPushforwardClosed i I).obj N).obj :=
    fun n => idealPowerMultiple_ker_pushforward_eq_bot i (N.obj.obj (op n))
  have hannJ : IsSystemAnnihilatedBy J ((coherentAdicPushforwardClosed i I).obj N).obj :=
    fun n => idealPowerMultiple_pushforward_eq_bot_of_le_map i J L hJL (hN n)
  obtain ⟨M, ⟨e⟩⟩ := hJ ((coherentAdicPushforwardClosed i I).obj N) hannJ
  have hterm : ∀ n : ℕ,
      idealPowerMultiple i.ker 1 (((completionFunctor X I).obj M).obj.obj (op n)) = ⊥ :=
    fun n => idealPowerMultiple_eq_bot_of_iso i.ker
      (((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso e).app (op n)) 1 (hannKer n)
  have hM : idealPowerMultiple i.ker 1 M.obj = ⊥ :=
    idealPowerMultiple_eq_bot_of_completion_eq_bot I i.ker hff M hterm
  refine ⟨(coherentPullback i).obj M, ?_⟩
  exact ⟨(coherentAdicPushforwardClosed i I).preimageIso
    ((ObjectProperty.isoMk (IsCoherentAdicSystem I)
      (completionAnnihilatedPushforwardIso i I M hM)).symm ≪≫ e)⟩

end

/-! ### The contraction -/

section

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I K : X.IdealSheafData)

/-- **The `V(𝒦)` contraction of [Stacks, Tag 088C]: "after replacing `X` by the closed subscheme
corresponding to `𝒦` we may assume that every nonzero ideal sheaf is in `Ξ`".**

Let `X` be a locally Noetherian scheme, let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent sheaves of ideals,
suppose the completion functor `Coh(𝒪_X) ⥤ Coh(X, ℐ)` is fully faithful, and suppose the
induction hypothesis of [Stacks, Tag 088C] at `𝒦`: every object of `Coh(X, ℐ)` killed by an ideal
sheaf **strictly larger** than `𝒦` is in the essential image of the completion functor. Then, on
the closed subscheme `V(𝒦)`, every object of `Coh(V(𝒦), ℐ 𝒪_{V(𝒦)})` killed by a **nonzero**
ideal sheaf of `V(𝒦)` is in the essential image of the completion functor of `V(𝒦)`.

Together with full faithfulness on `V(𝒦)`, which is
`Stacks.Coherent.fullyFaithful_completionFunctor_comap`, this is exactly the position the source
is in after the replacement. The translation is
`Stacks.Coherent.ker_lt_map_of_ne_bot`, which sends a nonzero ideal sheaf `ℒ` of `V(𝒦)` to the
ideal sheaf `ℒ · 𝒪_X > 𝒦` at which the induction hypothesis may be invoked, and
`Stacks.Coherent.essImage_completionFunctor_comap_of_essImage`, which brings the resulting
`Ξ`-membership down to `V(𝒦)`. -/
public theorem essImage_completionFunctor_subscheme_of_lt
    (hff : (completionFunctor X I).FullyFaithful)
    (hIH : ∀ K' : X.IdealSheafData, K < K' → ∀ 𝓖 : CoherentAdicSystems I,
      IsSystemAnnihilatedBy K' 𝓖.obj → (completionFunctor X I).essImage 𝓖) :
    letI : IsLocallyNoetherian K.subscheme :=
      isLocallyNoetherian_of_isClosedImmersion K.subschemeι
    ∀ L : K.subscheme.IdealSheafData, L ≠ ⊥ →
      ∀ 𝓝 : CoherentAdicSystems (I.comap K.subschemeι), IsSystemAnnihilatedBy L 𝓝.obj →
        (completionFunctor K.subscheme (I.comap K.subschemeι)).essImage 𝓝 :=
  fun L hL => essImage_completionFunctor_comap_of_essImage K.subschemeι I
    (L.map K.subschemeι) L le_rfl hff
    (hIH (L.map K.subschemeι)
      (by
        have h := ker_lt_map_of_ne_bot K.subschemeι L hL
        rwa [Scheme.IdealSheafData.ker_subschemeι K] at h))

/-- **Hypothesis (1) of [Stacks, Tag 088A] on the contracted scheme, from the induction
hypothesis of [Stacks, Tag 088C] on the ambient one.**

Granted full faithfulness of the completion functor on `X` and the induction hypothesis at `𝒦` —
every object of `Coh(X, ℐ)` killed by an ideal sheaf strictly larger than `𝒦` is in the essential
image — the completion functor of the closed subscheme `V_{V(𝒦)}(ℒ ᵉ⁺¹)` is an equivalence for
every `e`, for any ideal sheaf `ℒ` of `V(𝒦)` all of whose positive powers are nonzero.

The powers `ℒ ᵉ⁺¹` are the point: they are smaller than `ℒ`, hence never strictly larger than
`𝒦` after the identification of ideal sheaves, so this cannot be obtained from the induction
hypothesis without the contraction. That all of them are nonzero is an input, not a consequence
of `ℒ ≠ 0`; see the module docstring.

This is what `Stacks.Coherent.essImage_completionFunctor_of_isKernelCokernelAnnihilatedByPower`
takes as its hypothesis `h`, on `V(𝒦)`. -/
public theorem isEquivalence_completionFunctor_pow_subscheme_of_lt
    (hff : (completionFunctor X I).FullyFaithful)
    (hIH : ∀ K' : X.IdealSheafData, K < K' → ∀ 𝓖 : CoherentAdicSystems I,
      IsSystemAnnihilatedBy K' 𝓖.obj → (completionFunctor X I).essImage 𝓖) :
    letI : IsLocallyNoetherian K.subscheme :=
      isLocallyNoetherian_of_isClosedImmersion K.subschemeι
    ∀ L : K.subscheme.IdealSheafData, (∀ e : ℕ, L ^ (e + 1) ≠ ⊥) → ∀ e : ℕ,
      letI : IsLocallyNoetherian (L ^ (e + 1)).subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian (L ^ (e + 1)).subschemeι
      (completionFunctor (L ^ (e + 1)).subscheme
        ((I.comap K.subschemeι).comap (L ^ (e + 1)).subschemeι)).IsEquivalence :=
  let : IsLocallyNoetherian K.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion K.subschemeι
  fun L hL => isEquivalence_completionFunctor_pow_of_essImage (I.comap K.subschemeι) L
    (fullyFaithful_completionFunctor_comap I K hff)
    fun e 𝓖 h =>
      essImage_completionFunctor_subscheme_of_lt I K hff hIH (L ^ (e + 1)) (hL e) 𝓖 h

/-- **[Stacks, Tag 088A] on the contracted scheme, with hypothesis (1) discharged by the
induction hypothesis of [Stacks, Tag 088C].**

Let `X` be a Noetherian scheme, `ℐ, 𝒦 ⊆ 𝒪_X` quasi-coherent sheaves of ideals, and assume the
completion functor on `X` is fully faithful and the induction hypothesis of [Stacks, Tag 088C]
holds at `𝒦`. Let `ℒ ⊆ 𝒪_{V(𝒦)}` be an ideal sheaf with no vanishing positive power. Then any
object `(𝓕_n)` of `Coh(V(𝒦), ℐ 𝒪_{V(𝒦)})` admitting a map `α : (𝓕_n) ⟶ 𝓗 ^∧` from a coherent
`𝒪_{V(𝒦)}`-module `𝓗` whose levelwise kernels and cokernels are annihilated by a power of `ℒ`
is in the essential image of the completion functor of `V(𝒦)`.

Only hypothesis (2) — the map `α`, which is the conclusion of [Stacks, Tag 088B] — is left as an
input. This is the form in which the inductive step of [Stacks, Tag 088C] applies
[Stacks, Tag 088A] after the replacement of `X` by `V(𝒦)`. -/
public theorem essImage_completionFunctor_subscheme_of_lt_of_kernelCokernel [IsNoetherian X]
    (hff : (completionFunctor X I).FullyFaithful)
    (hIH : ∀ K' : X.IdealSheafData, K < K' → ∀ 𝓖 : CoherentAdicSystems I,
      IsSystemAnnihilatedBy K' 𝓖.obj → (completionFunctor X I).essImage 𝓖) :
    letI : IsLocallyNoetherian K.subscheme :=
      isLocallyNoetherian_of_isClosedImmersion K.subschemeι
    letI : CompactSpace K.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace K.subschemeι
    letI : IsNoetherian K.subscheme := { }
    ∀ L : K.subscheme.IdealSheafData, (∀ e : ℕ, L ^ (e + 1) ≠ ⊥) →
      ∀ 𝓕 : CoherentAdicSystems (I.comap K.subschemeι),
        ∀ H : AlgebraicGeometry.SheafOfModules.CoherentModules K.subscheme.ringCatSheaf,
          ∀ α : 𝓕 ⟶ (completionFunctor K.subscheme (I.comap K.subschemeι)).obj H,
            IsKernelCokernelAnnihilatedByPower L α.hom →
              (completionFunctor K.subscheme (I.comap K.subschemeι)).essImage 𝓕 :=
  let : IsLocallyNoetherian K.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion K.subschemeι
  let : CompactSpace K.subscheme :=
    QuasiCompact.compactSpace_of_compactSpace K.subschemeι
  let : IsNoetherian K.subscheme := { }
  fun L hL 𝓕 H α hα =>
    essImage_completionFunctor_of_essImage_annihilated (I.comap K.subschemeι) L 𝓕
      (fullyFaithful_completionFunctor_comap I K hff)
      (fun e 𝓖 h =>
        essImage_completionFunctor_subscheme_of_lt I K hff hIH (L ^ (e + 1)) (hL e) 𝓖 h)
      H α hα

end

end Stacks.Coherent

end
