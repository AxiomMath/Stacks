module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendUnramifiedCodimensionOne
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.RegularDimensionTwo
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.CompletionCriterion
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.EssSurjFlatDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.LiftFromHypersurfaceComplete
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.NormalEquivalence
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.DenseOpenGenericPoint
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay

/-!
# Purity for regular local rings

Let `A` be a regular local ring of dimension `d ≥ 2`, `X = Spec A` and `U = X ∖ {𝔪}` its
punctured spectrum. Then restriction `FÉt_X ⟶ FÉt_U` is essentially surjective: every finite
étale cover of `U` extends to a finite étale cover of `X`. This is the Zariski–Nagata purity
theorem in the local form of clause (1) of [Stacks, Tag 0BMA].

## Main results

* `AlgebraicGeometry.hasPurity_of_isRegularLocalRing` — purity for a regular local ring of
  dimension at least two.
* `AlgebraicGeometry.purityAtRegularLocalRings` — the same, packaged as the proposition
  `AlgebraicGeometry.PurityAtRegularLocalRings`.
* `AlgebraicGeometry.hasPurity_of_hasPurity_adicCompletion` — purity descends from the
  `𝔪`-adic completion (from Stacks 0BLL).
* `AlgebraicGeometry.LocalLefschetzSituation.hasPurity_of_hasPurity_quotientRing` — purity
  lifts from `A / fA` to an `f`-adically complete `A` of depth at least `3`.

## Implementation notes

The proof is the source's induction on `d`.

* For `d = 2`, Stacks 0BM9 identifies a finite étale cover of `U` with a finite normal
  torsion-free `A`-algebra étale over `U`, and such an algebra is étale over `A` by clause (2)
  of Stacks 0BMA at `d = 2`
  (`Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_ringKrullDim_eq_two`); the extension
  criterion of Stacks 0BM9 concludes.
* For `d ≥ 3`, Stacks 0BLL reduces to the `𝔪`-adic completion `Â`, which is again regular of
  dimension `d`; its punctured spectrum is the inverse image of `U` because `𝔪 Â` is the
  maximal ideal of `Â`. In `Â` choose `f ∈ 𝔪 ∖ 𝔪²`; then `Â / fÂ` is regular of dimension
  `d - 1` and has purity by induction, `Â` is `f`-adically complete and has depth `d ≥ 3`, so
  purity lifts from `Â / fÂ` to `Â` by
  `…LocalLefschetzSituation.exists_finiteEtale_extension_of_isAdicComplete_of_three_le_depth`
  (Stacks 0BLS in the complete case).

## References

* [Stacks Project, Tag 0BMA](https://stacks.math.columbia.edu/tag/0BMA)
* [Stacks Project, Tag 0BM9](https://stacks.math.columbia.edu/tag/0BM9)
* [Stacks Project, Tag 0BLL](https://stacks.math.columbia.edu/tag/0BLL)
* [Stacks Project, Tag 0BLM](https://stacks.math.columbia.edu/tag/0BLM)
* [Stacks Project, Tag 0BLS](https://stacks.math.columbia.edu/tag/0BLS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Stacks.FundamentalGroup (essSurj_finiteEtaleBaseChange_iff_exists_isPullback)

universe u

namespace AlgebraicGeometry

/-- **Purity descends from the completion.** If purity holds for the `𝔪`-adic completion of a
Noetherian local ring `A`, it holds for `A`. This is the "if" direction of Stacks 0BLL, read
through the identification of the inverse image of the punctured spectrum of `A` with the
punctured spectrum of the completion. -/
theorem hasPurity_of_hasPurity_adicCompletion (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (h : HasPurity (AdicCompletion (maximalIdeal A) A)) :
    HasPurity A := by
  let Ahat := AdicCompletion (maximalIdeal A) A
  let c : Spec (.of Ahat) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A Ahat))
  let U := Stacks.puncturedSpectrum A
  have hW : (finiteEtaleBaseChange (c ⁻¹ᵁ U).ι).EssSurj := by
    have hpre : c ⁻¹ᵁ U = Stacks.puncturedSpectrum Ahat :=
      Stacks.LocalCohomology.preimage_puncturedSpectrum_adicCompletion (CommRingCat.of A)
    rwa [hpre]
  have hpb := isPullback_morphismRestrict c U
  let e : (c ⁻¹ᵁ U).toScheme ≅ pullback U.ι c := hpb.isoPullback
  refine (essSurj_finiteEtaleBaseChange_iff_exists_isPullback _).2 fun V pi _ _ => ?_
  refine (exists_finiteEtale_extension_iff_completion A V pi).2 ?_
  let pihat : pullback pi (pullback.fst U.ι c) ⟶ pullback U.ι c := pullback.snd _ _
  obtain ⟨Y, f, g, hf, hf', hYpb⟩ :=
    (essSurj_finiteEtaleBaseChange_iff_exists_isPullback _).1 hW _ (pihat ≫ e.inv)
  refine ⟨Y, f, g, hf, hf', ?_⟩
  refine hYpb.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change (pihat ≫ e.inv) ≫ e.hom = 𝟙 _ ≫ pihat
    simp
  · simp
  · exact hpb.isoPullback_hom_snd.symm
  · simp

namespace LocalLefschetzSituation

/-- **Purity lifts from a hypersurface section of a complete ring of depth at least three.** In
the local Lefschetz situation let `A` be `f`-adically complete of depth at least `3`. If purity
holds for `A / fA`, it holds for `A`: a finite étale cover of `U` restricts to one of `U₀`, which
by purity comes from `X₀`, so the cover comes from `X` by
`exists_finiteEtale_extension_of_isAdicComplete_of_three_le_depth`. -/
@[sga "2 X 3.9" "(i)"]
theorem hasPurity_of_hasPurity_quotientRing (S : LocalLefschetzSituation.{u})
    (hcomplete : IsAdicComplete (Ideal.span {S.f}) S.A)
    (hdepth : 3 ≤ Module.depth S.A (maximalIdeal S.A) S.A)
    (h : HasPurity S.quotientRing) : HasPurity S.A := by
  have hquot : (finiteEtaleBaseChange S.U₀Open.ι).EssSurj := by
    rwa [S.U₀Open_eq_puncturedSpectrumOpen]
  refine (essSurj_finiteEtaleBaseChange_iff_exists_isPullback _).2 fun V pi _ _ => ?_
  obtain ⟨Y₀, f₀, g₀, hfin₀, het₀, hpb₀⟩ :=
    (essSurj_finiteEtaleBaseChange_iff_exists_isPullback S.U₀Open.ι).1 hquot
      (pullback pi S.U₀ToU) (pullback.snd pi S.U₀ToU)
  have := hfin₀
  have := het₀
  exact S.exists_finiteEtale_extension_of_isAdicComplete_of_three_le_depth hdepth hcomplete
    V pi Y₀ f₀ g₀ hpb₀

end LocalLefschetzSituation

/-- A regular local ring is a normal ring: it is an integrally closed domain. -/
@[ega "0 17.1.3"]
theorem isNormalRing_of_isRegularLocalRing (A : Type u) [CommRing A] [IsRegularLocalRing A] :
    IsNormalRing A := by
  have := IsRegularLocalRing.isDomain A
  have := isIntegrallyClosed_of_isRegularLocalRing A
  exact IsNormalRing.of_isIntegrallyClosed A

/-- Étaleness of the restriction `f ∣_ U` of a morphism to an open of its target is étaleness of
the base change of `f` along the open immersion `U ⟶ Y`. -/
private lemma etale_morphismRestrict_of_etale_pullback_snd {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (h : Etale (pullback.snd f U.ι)) : Etale (f ∣_ U) := by
  rw [← (isPullback_morphismRestrict f U).flip.isoPullback_hom_snd]
  infer_instance

/-- **Purity for a regular local ring of dimension two.** This is the base case of the
induction: by Stacks 0BM9 a finite étale cover of the punctured spectrum is determined by its
ring of global sections, a finite normal torsion-free `A`-algebra étale over the punctured
spectrum, which is étale over `A` by clause (2) of Stacks 0BMA at `d = 2`. -/
@[sga "2 X 3.4" "partial", sga "2 XII 3.5" "partial"]
theorem hasPurity_of_isRegularLocalRing_of_ringKrullDim_eq_two (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) : HasPurity A := by
  have hnormal := isNormalRing_of_isRegularLocalRing A
  have hdim2 : (2 : WithBot ℕ∞) ≤ ringKrullDim A := hdim.ge
  obtain ⟨F, -, ⟨e⟩⟩ :=
    NormalPurity.globalSections_isEquivalence_normalFiniteEtaleAwayAlgebra A hnormal hdim2
  refine (essSurj_finiteEtaleBaseChange_iff_exists_isPullback _).2 fun V π hfin het => ?_
  let C : FiniteEtaleOver (Stacks.puncturedSpectrum A).toScheme :=
    MorphismProperty.Over.mk ⊤ π ⟨hfin, het⟩
  let : Algebra A Γ(V, ⊤) := NormalPurity.globalSectionsAlgebra A C
  let B := F.obj (Opposite.op C)
  let eB : B.obj ≃ₐ[A] Γ(V, ⊤) := CommAlgCat.algEquivOfIso (e.app (Opposite.op C))
  have : Module.Finite A B.obj := B.property.1
  have : Module.IsTorsionFree A B.obj := B.property.2.2.1
  have : Algebra.Etale A B.obj :=
    Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_ringKrullDim_eq_two A B.obj
      B.property.2.1 hdim (etale_morphismRestrict_of_etale_pullback_snd _ _ B.property.2.2.2)
  refine (NormalPurity.exists_finiteEtale_extension_iff_globalSections_finiteEtale A hnormal
    hdim2 V π).2 ?_
  exact ⟨Module.Finite.equiv eB.toLinearEquiv, Algebra.Etale.of_equiv eB⟩

/-- A regular local ring of dimension `n + 1` has an element `f` of its maximal ideal with
`A / fA` regular local of dimension `n`: any `f ∈ 𝔪 ∖ 𝔪²` will do. -/
theorem exists_mem_maximalIdeal_isRegularLocalRing_quotient_of_ringKrullDim_eq_succ
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (n : ℕ)
    (hdim : ringKrullDim A = (n + 1 : ℕ)) :
    ∃ f ∈ maximalIdeal A, IsRegularLocalRing (A ⧸ Ideal.span {f}) ∧
      ringKrullDim (A ⧸ Ideal.span {f}) = n := by
  have hne : ringKrullDim A ≠ 0 := by
    rw [hdim]
    exact_mod_cast Nat.succ_ne_zero n
  obtain ⟨x, hx, hx2⟩ :=
    IsConcreteLE.exists_of_lt (IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero hne)
  obtain ⟨hreg, hdrop⟩ := quotient_isRegularLocalRing A x hx hx2
  refine ⟨x, hx, hreg, ?_⟩
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A ⧸ Ideal.span {x})] at hdrop ⊢
  rw [hdim] at hdrop
  norm_cast at hdrop ⊢
  omega

/-- Purity for regular local rings of a fixed dimension `n ≥ 2`, by induction on `n`. -/
@[sga "2 X 3.4" "partial", sga "2 XII 3.5" "partial"]
private lemma hasPurity_of_isRegularLocalRing_of_ringKrullDim_eq (n : ℕ) (hn : 2 ≤ n) :
    ∀ (A : Type u) [CommRing A] [IsRegularLocalRing A], ringKrullDim A = n → HasPurity A := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A _ _ hdim
    obtain rfl | hn' := eq_or_lt_of_le hn
    · exact hasPurity_of_isRegularLocalRing_of_ringKrullDim_eq_two A hdim
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    apply hasPurity_of_hasPurity_adicCompletion A
    let Ahat := AdicCompletion (maximalIdeal A) A
    have : IsRegularLocalRing Ahat :=
      isRegularLocalRing_iff_adicCompletion_maximalIdeal.1 inferInstance
    have hdimhat : ringKrullDim Ahat = (m + 1 : ℕ) := by
      rwa [← ringKrullDim_adicCompletion_maximalIdeal]
    obtain ⟨f, hf, hreg, hdrop⟩ :=
      exists_mem_maximalIdeal_isRegularLocalRing_quotient_of_ringKrullDim_eq_succ Ahat m hdimhat
    have hquot := ih m (by omega) (by omega) (Ahat ⧸ Ideal.span {f}) hdrop
    have hcomplete : IsAdicComplete (Ideal.span {f}) Ahat :=
      isAdicComplete_of_le_of_fg_of_isAdicComplete
        (Ideal.span_le.2 (Set.singleton_subset_iff.2 hf))
        (inferInstance : IsAdicComplete (maximalIdeal Ahat) Ahat)
        (Ideal.fg_of_isNoetherianRing _)
    have hcm : (Module.depth Ahat (maximalIdeal Ahat) Ahat : WithBot ℕ∞) = ringKrullDim Ahat :=
      (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
        Ahat).2
    have hthree : (3 : WithBot ℕ∞) ≤ (Module.depth Ahat (maximalIdeal Ahat) Ahat : WithBot ℕ∞) := by
      rw [hcm, hdimhat]
      exact_mod_cast (show 3 ≤ m + 1 by omega)
    exact LocalLefschetzSituation.hasPurity_of_hasPurity_quotientRing ⟨Ahat, f, hf⟩ hcomplete
      (WithBot.coe_le_coe.mp hthree) hquot

/-- **Zariski–Nagata purity, [Stacks, Tag 0BMA] clause (1).** Let `A` be a regular local ring
of dimension at least two. Then every finite étale cover of the punctured spectrum of `A` is,
up to isomorphism, the restriction of a finite étale cover of `Spec A`. -/
@[sga "2 X 3.4" "3.4(i), partial", sga "2 XII 3.5" "partial"]
theorem hasPurity_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim R) : HasPurity R := by
  have hd := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  refine hasPurity_of_isRegularLocalRing_of_ringKrullDim_eq (maximalIdeal R).spanFinrank ?_ R
    hd.symm
  rw [← hd] at hdim
  exact_mod_cast hdim

/-- Purity holds at every regular local ring of dimension at least two. -/
@[sga "2 XII 3.5" "partial"]
theorem purityAtRegularLocalRings : PurityAtRegularLocalRings.{u} :=
  fun R _ _ hdim => hasPurity_of_isRegularLocalRing R hdim

end AlgebraicGeometry

end
