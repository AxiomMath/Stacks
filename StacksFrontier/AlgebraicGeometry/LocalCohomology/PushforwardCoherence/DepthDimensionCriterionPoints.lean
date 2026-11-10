module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.CoherentModuleAffineTransport
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.DepthDimensionCriterionZeroLocus
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.TildeStalkPrime
public import StacksFrontier.RingTheory.DimensionFormula

/-!
# The depth–dimension criterion over the points of the open subscheme

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, put `X = Spec A`, `Z = V(I)`, `U = X ∖ Z`
with `j : U → X` the inclusion, let `M` be a finite `A`-module and let `ℱ = M̃|_U`. This file
restates, in the namespace `Stacks.LocalCohomologySequence`,
`forall_lt_depth_add_height_iff_forall_isCoherent_rightDerivedZeroLocus` with its depth–dimension
condition written **over the points of `U` and the closures of points of `X`**, the way
[Stacks, Tag 0BJY] writes it, rather than over the pairs of primes of `A` the way
[Stacks, Tag 0BJR] does:

* for every `x ∈ Supp(ℱ)` and every `z ∈ Z` with `z ∈ closure {j(x)}`, one has
  `depth_{𝒪_{U,x}}(ℱ_x) + codim(closure {z}, closure {j(x)}) > n`.

Nothing of the condition mentions `M` any more: the depth is the depth of the stalk of `ℱ`, the
support is the support of `ℱ`, and the dimension term is a codimension of closures of points in
`X`. The equivalence is therefore the form in which the criterion applies to a coherent module
that is only *isomorphic* to some `M̃|_U`, which is how an arbitrary coherent module on an open
of an affine scheme presents itself — see
`AlgebraicGeometry.exists_ideal_eq_finiteModule_tilde_restrict_iso`.

## Main results

All in the namespace `Stacks.LocalCohomologySequence`.

* `forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerivedZeroLocus`
  — the equivalence above, for `ℱ = M̃|_U`.
* `forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_opens`
  — **the same at an arbitrary open `W` of `Spec A` and for an arbitrary coherent module**, no
  finite module appearing in either side.

## Implementation notes

Each of the four terms of the condition is moved by one named lemma, and the proof is the four
substitutions with no further content.

* the **depth** term, by `AlgebraicGeometry.Scheme.Modules.depth_stalk_restrict` down to the
  stalk of `M̃` at `j(x)`, and then by
  `AlgebraicGeometry.depth_stalk_tilde_eq_depth_localizedModule` to `depth_{A_𝔭}(M_𝔭)`;
* the **support** term, by `AlgebraicGeometry.Scheme.Modules.supp_restrict` and
  `AlgebraicGeometry.mem_supp_tilde_iff_nontrivial_localizedModule`;
* the **codimension** term, by `topCodim_closureSingleton_eq_height_map_quotientMk`;
* the **two memberships**, by `AlgebraicGeometry.mem_zeroLocusCompl` and, for the comparability
  of the two primes, `PrimeSpectrum.le_iff_specializes` with
  `specializes_iff_mem_closure`.

**A prime is produced for each point.** The carrier of `Spec A` and `PrimeSpectrum A` are
definitionally equal, but not at the transparency instance search uses: at a point of the scheme
`𝔭.IsPrime` is not found, so `Localization.AtPrime 𝔭.asIdeal` cannot be written at a point. Each
point is therefore paired with a prime by `⟨y, rfl⟩ : ∃ 𝔭 : PrimeSpectrum A, (𝔭 : Spec A) = y`
before the algebraic side is mentioned, and that pairing is what the lemmas of
`StacksFrontier/AlgebraicGeometry/LocalCohomology/PushforwardCoherence/TildeStalkPrime.lean` take as
an argument. The same device carries the codimension and the specialization across, where the two
spellings differ in their `TopologicalSpace` instance and so cannot be `rw`-matched.

**The formal-fibres hypothesis is not moved.** It is still Serre's condition on the formal fibres
of `A_𝔮` for the primes `𝔮 ⊇ I`, not on those of `𝒪_{X,z}` for the points `z ∈ Z`; the two are
identified by `AlgebraicGeometry.formalFibersHavePropertySk_stalk_iff_primeIdealOf`, which speaks
of the primes of `Γ(X, V)` at an affine open `V` and therefore applies at the top open of an
affine scheme, not to `A` and `Spec A`.

## References

* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 0BJR](https://stacks.math.columbia.edu/tag/0BJR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TopologicalSpace.IrreducibleCloseds (closureSingleton)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomologySequence

variable {A : CommRingCat.{u}}

/-- The codimension of `closure {w}` in `closure {y}` in `Spec A` is the height of the image of
`𝔮` in `A ⧸ 𝔭`, for primes `𝔭 ≤ 𝔮` naming the points `y` and `w`. -/
public theorem topCodim_closureSingleton_eq_height_of_coe_eq (y w : Spec A)
    (p q : PrimeSpectrum (ToType A)) (hpy : (p : Spec A) = y) (hqw : (q : Spec A) = w)
    (hpq : p.asIdeal ≤ q.asIdeal) :
    IrreducibleClosedsCodim.topCodim (closureSingleton w) (closureSingleton y) =
      (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  subst hpy hqw
  exact topCodim_closureSingleton_eq_height_map_quotientMk p q hpq

/-- **[Stacks, Tag 0BJY] over an affine base, with the depth–dimension condition over the points
of `U`.** Let `A` be a universally catenary Noetherian ring, let `I ⊆ A` be an ideal, put
`X = Spec A`, `Z = V(I)`, `U = X ∖ Z` and let `j : U → X` be the inclusion. Let `M` be a finite
`A`-module, let `ℱ = M̃|_U` and let `n` be a natural number. Assume the formal fibres of `A_𝔮`
satisfy Serre's condition `(Sₙ)` for every prime `𝔮 ⊇ I`. Then `R^pj_*ℱ` is coherent for every
`0 ≤ p < n` if and only if

  `depth_{𝒪_{U,x}}(ℱ_x) + codim(closure {z}, closure {j(x)}) > n`

for every `x ∈ Supp(ℱ)` and every `z ∈ Z` lying in the closure of `{j(x)}`.

This is
`forall_lt_depth_add_height_iff_forall_isCoherent_rightDerivedZeroLocus` with the left-hand
condition read over the points of `U` instead of over the pairs of primes of `A`: the depth of
the stalk of `ℱ` is the depth of `M_𝔭` by
`AlgebraicGeometry.Scheme.Modules.depth_stalk_restrict` and
`AlgebraicGeometry.depth_stalk_tilde_eq_depth_localizedModule`, the support of `ℱ` is the set of
primes with `M_𝔭 ≠ 0` by `AlgebraicGeometry.Scheme.Modules.supp_restrict` and
`AlgebraicGeometry.mem_supp_tilde_iff_nontrivial_localizedModule`, and the codimension is the
height of the image of `𝔮` in `A ⧸ 𝔭` by
`topCodim_closureSingleton_eq_height_map_quotientMk`. -/
@[ega "IV 7.8.3" "(ix)", sga "2 VIII 2.3" "(i) ⇔ (iv), special case"]
public theorem forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerivedZeroLocus
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M]
    (hA : Ring.IsUniversallyCatenary (ToType A)) (n : ℕ)
    (hformal : ∀ q : PrimeSpectrum (ToType A), I ≤ q.asIdeal →
      Stacks.LocalCohomology.FormalFibersHavePropertySk
        (Localization.AtPrime q.asIdeal) n) :
    (∀ x : (zeroLocusCompl I).toScheme,
        x ∈ SheafOfModules.supp ((tilde M).restrict (zeroLocusCompl I).ι) →
        ∀ z : Spec A, z ∉ zeroLocusCompl I →
          z ∈ closure ({(zeroLocusCompl I).ι.base x} : Set (Spec A)) →
          (n : ℕ∞) <
            Module.depth ((zeroLocusCompl I).toScheme.presheaf.stalk x)
                (IsLocalRing.maximalIdeal ((zeroLocusCompl I).toScheme.presheaf.stalk x))
                (((tilde M).restrict (zeroLocusCompl I).ι).presheaf.stalk x) +
              IrreducibleClosedsCodim.topCodim (closureSingleton z)
                (closureSingleton ((zeroLocusCompl I).ι.base x))) ↔
      ∀ p : ℕ, p < n →
        (((Scheme.Modules.pushforward (zeroLocusCompl I).ι).rightDerived p).obj
          ((tilde M).restrict (zeroLocusCompl I).ι)).IsCoherent := by
  -- the specialization, read at a pair of primes
  have hspec (p q : PrimeSpectrum (ToType A)) :
      (q : Spec A) ∈ closure ({(p : Spec A)} : Set (Spec A)) ↔ p.asIdeal ≤ q.asIdeal :=
    specializes_iff_mem_closure.symm.trans
      ((PrimeSpectrum.asIdeal_le_asIdeal p q).trans (PrimeSpectrum.le_iff_specializes p q)).symm
  refine Iff.trans ?_
    (forall_lt_depth_add_height_iff_forall_isCoherent_rightDerivedZeroLocus I M hA n hformal)
  -- the support and the depth–dimension term at a point `x` over a prime `p`, and a prime `q`
  have hsupp (x : (zeroLocusCompl I).toScheme) (p : PrimeSpectrum (ToType A))
      (hp : (p : Spec A) = (zeroLocusCompl I).ι.base x) :
      x ∈ SheafOfModules.supp ((tilde M).restrict (zeroLocusCompl I).ι) ↔
        Nontrivial (LocalizedModule p.asIdeal.primeCompl M) := by
    rw [Scheme.Modules.supp_restrict (zeroLocusCompl I).ι (tilde M), Set.mem_preimage, ← hp]
    exact AlgebraicGeometry.mem_supp_tilde_iff_nontrivial_localizedModule M (p : Spec A) p rfl
  have hterm (x : (zeroLocusCompl I).toScheme) (p q : PrimeSpectrum (ToType A))
      (hp : (p : Spec A) = (zeroLocusCompl I).ι.base x) (hpq : p.asIdeal ≤ q.asIdeal) :
      Module.depth ((zeroLocusCompl I).toScheme.presheaf.stalk x)
          (IsLocalRing.maximalIdeal ((zeroLocusCompl I).toScheme.presheaf.stalk x))
          (((tilde M).restrict (zeroLocusCompl I).ι).presheaf.stalk x) +
        IrreducibleClosedsCodim.topCodim (closureSingleton (q : Spec A))
          (closureSingleton ((zeroLocusCompl I).ι.base x)) =
      Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) +
        (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
    rw [Scheme.Modules.depth_stalk_restrict (zeroLocusCompl I).ι (tilde M) x, ← hp,
      AlgebraicGeometry.depth_stalk_tilde_eq_depth_localizedModule M (p : Spec A) p rfl]
    exact congrArg _ (topCodim_closureSingleton_eq_height_of_coe_eq _ _ p q rfl rfl hpq)
  constructor
  · intro h p q hp hq hpq hnt
    have key := h ⟨(p : Spec A), hp⟩ ((hsupp _ p rfl).mpr hnt) (q : Spec A) (fun hmem => hmem hq)
      ((hspec p q).mpr hpq)
    exact key.trans_eq (hterm ⟨(p : Spec A), hp⟩ p q rfl hpq)
  · intro h x hx z hz hzx
    obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum (ToType A),
        (p : Spec A) = (zeroLocusCompl I).ι.base x := ⟨_, rfl⟩
    obtain ⟨q, rfl⟩ : ∃ q : PrimeSpectrum (ToType A), (q : Spec A) = z := ⟨z, rfl⟩
    have hpq : p.asIdeal ≤ q.asIdeal := (hspec p q).mp (hp ▸ hzx)
    have key := h p q (hp ▸ x.2) (not_not.mp hz) hpq ((hsupp x p hp).mp hx)
    exact key.trans_eq (hterm x p q hp hpq).symm

/-- **[Stacks, Tag 0BJY] at an arbitrary open of a spectrum, for an arbitrary coherent module.**
Let `A` be a universally catenary Noetherian ring, let `W ⊆ Spec A` be an open with inclusion
`j : W → Spec A`, let `ℱ` be a coherent `𝒪_W`-module and let `n` be a natural number. Assume the
formal fibres of `A_𝔮` satisfy Serre's condition `(Sₙ)` for every prime `𝔮 ∉ W`. Then `R^pj_*ℱ`
is coherent for every `0 ≤ p < n` if and only if

  `depth_{𝒪_{W,x}}(ℱ_x) + codim(closure {z}, closure {j(x)}) > n`

for every `x ∈ Supp(ℱ)` and every `z ∉ W` lying in the closure of `{j(x)}`.

Neither side mentions a finite module: `ℱ` is an arbitrary coherent module, not the restriction
of an `M̃`. It is isomorphic to one by
`AlgebraicGeometry.exists_ideal_eq_finiteModule_tilde_restrict_iso`, and that isomorphism moves
all three terms — `AlgebraicGeometry.SheafOfModules.supp_eq_of_iso` for the support,
`AlgebraicGeometry.Scheme.Modules.depth_stalk_congr` for the depth, and
`AlgebraicGeometry.isCoherent_rightDerived_iff_of_tilde_restrict_iso` for the coherence — while
the codimension term does not involve the module at all. The same lemma names the open as the
complement of a vanishing locus, which is what turns the hypothesis `𝔮 ∉ W` into the hypothesis
`I ≤ 𝔮` of
`forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerivedZeroLocus`. -/
@[ega "IV 7.8.3" "more general", sga "2 VIII 2.3" "(i) ⇔ (iv)"]
public theorem forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_opens
    [IsNoetherianRing A] (W : (Spec A).Opens) (G : W.toScheme.Modules) [G.IsCoherent]
    (hA : Ring.IsUniversallyCatenary (ToType A)) (n : ℕ)
    (hformal : ∀ q : PrimeSpectrum (ToType A), (q : Spec A) ∉ W →
      Stacks.LocalCohomology.FormalFibersHavePropertySk
        (Localization.AtPrime q.asIdeal) n) :
    (∀ x : W.toScheme, x ∈ SheafOfModules.supp G →
        ∀ z : Spec A, z ∉ W → z ∈ closure ({W.ι.base x} : Set (Spec A)) →
          (n : ℕ∞) <
            Module.depth (W.toScheme.presheaf.stalk x)
                (IsLocalRing.maximalIdeal (W.toScheme.presheaf.stalk x))
                (G.presheaf.stalk x) +
              IrreducibleClosedsCodim.topCodim (closureSingleton z)
                (closureSingleton (W.ι.base x))) ↔
      ∀ p : ℕ, p < n →
        (((Scheme.Modules.pushforward W.ι).rightDerived p).obj G).IsCoherent := by
  obtain ⟨I, hIW, M, hMfin, ⟨e⟩⟩ :=
    AlgebraicGeometry.exists_ideal_eq_finiteModule_tilde_restrict_iso W G
  subst hIW
  have := hMfin
  refine Iff.trans ?_
    ((forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerivedZeroLocus I M hA n
      fun q hq => hformal q fun hmem =>
        (AlgebraicGeometry.mem_zeroLocusCompl I _).mp hmem hq).trans
      (forall_congr' fun p => imp_congr_right fun _ =>
        AlgebraicGeometry.isCoherent_rightDerived_iff_of_tilde_restrict_iso
          (zeroLocusCompl I) G M e p))
  refine forall_congr' fun x => ?_
  rw [SheafOfModules.supp_eq_of_iso e]
  refine imp_congr_right fun _ => forall_congr' fun z => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  rw [Scheme.Modules.depth_stalk_congr e x]

end Stacks.LocalCohomologySequence

end
