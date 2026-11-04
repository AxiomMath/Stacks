module

public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.ChowSteps
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme

/-!
# The inductive step of Stacks 0FA9

Let `ℰ` be finite locally free of rank `r + 2` on `X`, locally of finite type over the base of
chapter 42, with a section `s` satisfying the hypotheses of [Stacks, Tag 0FA9] in `δ`-dimension
`n`. The source's inductive step proves `c_{r+2}(ℰ) ∩ [X]_n = [Z(s)]_{n - r - 2}` from the case of
rank `r + 1`:

* by the projective space bundle formula [Stacks, Tag 02TX] it suffices to prove the equality
  after pulling back along `π : P = 𝐏(ℰ) ⟶ X`;
* on `P` the Whitney formula gives `c_{r+2}(π^*ℰ) = c_{r+1}(ℰ') c_1(𝒪_P(1))` for the kernel
  `ℰ'` of the tautological quotient;
* `c_1(𝒪_P(1)) ∩ [P] = [Z(t)]` for the image `t` of `π^* s` (the claim, [Stacks, Tag 02SQ]);
* `π^* s` restricted to `Z(t)` comes from a section `s'` of `ℰ'|_{Z(t)}` with `Z(s') = Z(π^* s)`,
  which satisfies the hypotheses in rank `r + 1`, so `c_{r+1}(ℰ') ∩ [Z(t)] = [Z(π^* s)]`.

## Main results

* `Stacks.Chow.SectionZeroScheme.reducedTopChernCap_succ_succ`.
* `Stacks.Chow.SectionZeroScheme.reducedTopChernCap` — the reduced statement in every rank.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.SectionZeroScheme

open Stacks.Chow.GenuineChern

/-- Classes of cycles of one closed subscheme in two equal degrees are heterogeneously equal. -/
theorem mk_cycle_heq (C : ChowSituation.{u}) {X Z : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] (i : Z ⟶ X) [IsClosedImmersion i] {k l : ℤ} (h : k = l) :
    QuotientAddGroup.mk' (rationalEquivalences C q k)
        (cycleAssociatedToClosedSubscheme C q i k) ≍
      QuotientAddGroup.mk' (rationalEquivalences C q l)
        (cycleAssociatedToClosedSubscheme C q i l) := by
  subst h
  rfl

/-- **The inductive step of [Stacks, Tag 0FA9], over an abstract bundle.** Let `π : P ⟶ X` be
flat of relative dimension `r + 1` with injective flat pullback on Chow groups, `τ : π^*ℰ ⟶ ℒ` an
epimorphism onto an invertible module, `σ = π^* s` and `Z(t)` the zero scheme of `t = τ(σ)`.
Suppose every point of `Z(t)` has `δ ≤ n + r`, with a nonzerodivisor in the ideal of `Z(t)` where
equality holds. Then rank `r + 1` of the reduced statement gives it for `ℰ` in rank `r + 2`. -/
theorem reducedTopChernCap_step (C : ChowSituation.{u}) (r : ℕ)
    (IH : ReducedTopChernCap C (r + 1)) {X P : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
    (hd : AlgebraicGeometry.RelativeDimension π (r + 1))
    (hinj : ∀ k : ℤ, Function.Injective (flatPullbackChow C (π ≫ q) q π rfl (r + 1) hd k
      (flatPullbackFactorsThroughRationalEquivalence_general C (π ≫ q) q π rfl (r + 1) hd k)))
    (F : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (r + 2)]
    (s : Γ(F, ⊤)) {L : P.Modules}
    [hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    (τ : (Scheme.Modules.pullback π).obj F ⟶ L) [Epi τ] (n : ℤ)
    (hX : schemeDeltaDimension C q ≤ (n : EInt))
    (hZ : schemeDeltaDimension C ((zeroSchemeOfSection X F s).subschemeι ≫ q) ≤
      ((n - ((r + 2 : ℕ) : ℤ) : ℤ) : EInt))
    (hreg : IsRegularZeroSchemeSequence C q F s (r + 2) (n - ((r + 2 : ℕ) : ℤ)))
    (hhyp : ∀ (y : P) (hyD : y ∈ (hyperplane τ (pullbackGlobalSections π F s)).support),
      relativeDimension C.dimensionFunction (π ≫ q) y ≤ n + r ∧
        (relativeDimension C.dimensionFunction (π ≫ q) y = n + r →
          ∃ a ∈ nonZeroDivisors (P.presheaf.stalk y),
            a ∈ Stacks.AlgebraicGeometry.stalkIdeal
              (hyperplane τ (pullbackGlobalSections π F s)) y hyD)) :
    GenuineChern.chernCap C (r + 2) q F n (Fin.last (r + 2))
        (QuotientAddGroup.mk' (rationalEquivalences C q n)
          (cycleAssociatedToClosedSubscheme C q (𝟙 X) n)) =
      QuotientAddGroup.mk' (rationalEquivalences C q (n - ((r + 2 : ℕ) : ℤ)))
        (cycleAssociatedToClosedSubscheme C q (zeroSchemeOfSection X F s).subschemeι
          (n - ((r + 2 : ℕ) : ℤ))) := by
  have hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback π).obj F) (r + 2) :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ F (r + 2)
  have hL : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L :=
    hLinv
  have hL1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_one_of_isInvertible _ hL
  have hK : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (kernel τ : P.Modules) (r + 1) :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible τ
      inferInstance hL r hE
  have hK' := isFiniteLocallyFreeOfRank_liftModule τ (pullbackGlobalSections π F s) r
  set σ := pullbackGlobalSections π F s with hσdef
  set D := hyperplane τ σ with hDdef
  set j := D.subschemeι with hjdef
  set N : ℤ := n + ((r + 1 : ℕ) : ℤ) with hN
  have hPdim : schemeDeltaDimension C (π ≫ q) ≤ (N : EInt) :=
    schemeDeltaDimension_le_of_flat C q π (r + 1) hd hX
  have hDdim : schemeDeltaDimension C (j ≫ π ≫ q) ≤ ((N - 1 : ℤ) : EInt) := by
    refine schemeDeltaDimension_le_of_forall_point C (π ≫ q) j fun z => ?_
    have := (hhyp (j z) z.2).1
    push_cast
    omega
  -- the claim: `c₁(ℒ) ∩ [P]_N = [Z(t)]_{N-1}`
  have hclaim := chernCap_one_mk_fundamental_eq C (π ≫ q) L (τ.app ⊤ σ) N hPdim hDdim
    (fun ξ hξ => (hhyp (j ξ.1) ξ.1.2).2 ((show relativeDimension C.dimensionFunction (π ≫ q)
      (j ξ.1) = N - 1 from hξ).trans (by omega)))
  -- the zero schemes of `σ` and of the lifted section
  set Iσ := zeroSchemeOfSection P ((Scheme.Modules.pullback π).obj F) σ with hIσdef
  set I' := zeroSchemeOfSection D.subscheme (liftModule τ σ) (liftSection τ σ) with hI'def
  have hIσ : Iσ = (zeroSchemeOfSection X F s).comap π := zeroSchemeOfSection_pullback π F (r + 2) s
  have hI' : I' = Iσ.comap j := zeroSchemeOfSection_liftSection τ σ r
  have hker : (I'.subschemeι ≫ j).ker = Iσ := by
    rw [hI']
    refine ker_comap_subschemeι_comp j Iσ ?_
    rw [hjdef, Scheme.IdealSheafData.ker_subschemeι]
    exact hyperplane_le_zeroSchemeOfSection τ σ (r + 2)
  have hIσdim : schemeDeltaDimension C (Iσ.subschemeι ≫ π ≫ q) ≤
      ((n - ((r + 2 : ℕ) : ℤ) + ((r + 1 : ℕ) : ℤ) : ℤ) : EInt) := by
    rw [hIσ]
    exact schemeDeltaDimension_comap_le_of_flat C q π (r + 1) hd _ hZ
  have hI'dim : schemeDeltaDimension C (I'.subschemeι ≫ j ≫ π ≫ q) ≤
      ((N - 1 - ((r + 1 : ℕ) : ℤ) : ℤ) : EInt) := by
    have hrange : Set.range (I'.subschemeι ≫ j) = Set.range Iσ.subschemeι := by
      rw [range_eq_range_ker_subschemeι, hker]
    have h := schemeDeltaDimension_congr_of_range_eq C (π ≫ q) _ _ hrange
    refine ((schemeDeltaDimension_congr C (Category.assoc I'.subschemeι j (π ≫ q))).symm.trans
      h).trans_le (hIσdim.trans (le_of_eq ?_))
    rw [hN]
    push_cast
    ring_nf
  -- the induction hypothesis on `Z(t)`
  have hk : N - 1 - ((r + 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) = n - ((r + 2 : ℕ) : ℤ) := by
    omega
  have hreg' := isRegularZeroSchemeSequence_liftSection C q π (r + 1) hd F r s τ
    (N - 1 - ((r + 1 : ℕ) : ℤ)) (by rw [hk]; exact hZ) (by rw [hk]; exact hreg)
  have hIH := IH (j ≫ π ≫ q) (liftModule τ σ) (liftSection τ σ) (N - 1) hDdim hI'dim hreg'
  -- the Chow computation on `P`
  have hfac := fun k => flatPullbackFactorsThroughRationalEquivalence_general C (π ≫ q) q π rfl
    (r + 1) hd k
  have hpfac := fun k => properPushforwardFactorsThroughRationalEquivalence_of_isProper C
    (j ≫ π ≫ q) (π ≫ q) j rfl k
  have h1 := chernCap_flatPullback_heq C q (π ≫ q) π rfl (r + 1) hd F (r + 2)
    ((Scheme.Modules.pullback π).obj F) (Iso.refl _) n (Fin.last (r + 2)) (hfac n) (hfac _)
    (QuotientAddGroup.mk' (rationalEquivalences C q n)
      (cycleAssociatedToClosedSubscheme C q (𝟙 X) n))
  rw [flatPullbackChow_mk_fundamental C q π (r + 1) hd n hX (hfac n)] at h1
  have hS : (ShortComplex.mk (kernel.ι τ) τ (kernel.condition τ)).ShortExact :=
    { exact := ShortComplex.exact_kernel τ }
  have h2 := chernCap_top_eq_of_shortExact C (π ≫ q)
    (ShortComplex.mk (kernel.ι τ) τ (kernel.condition τ)) hS (r + 1) N
    (QuotientAddGroup.mk' (rationalEquivalences C (π ≫ q) N)
      (cycleAssociatedToClosedSubscheme C (π ≫ q) (𝟙 P) N))
  have hp1 : QuotientAddGroup.mk' (rationalEquivalences C (π ≫ q) (N - 1))
      (cycleAssociatedToClosedSubscheme C (π ≫ q) j (N - 1)) =
      properChowPushforward C (j ≫ π ≫ q) (π ≫ q) j rfl (N - 1) (hpfac _)
        (QuotientAddGroup.mk' (rationalEquivalences C (j ≫ π ≫ q) (N - 1))
          (cycleAssociatedToClosedSubscheme C (j ≫ π ≫ q) (𝟙 D.subscheme) (N - 1))) := by
    rw [properChowPushforward_mk, properPushforward_cycleAssociatedToClosedSubscheme_id]
  have h3 : GenuineChern.chernCap C (r + 1) (π ≫ q) (kernel τ) (N - 1) (Fin.last (r + 1))
      (GenuineChern.chernCap C 1 (π ≫ q) L N (Fin.last 1)
        (QuotientAddGroup.mk' (rationalEquivalences C (π ≫ q) N)
          (cycleAssociatedToClosedSubscheme C (π ≫ q) (𝟙 P) N))) =
      QuotientAddGroup.mk' (rationalEquivalences C (π ≫ q) (N - 1 - ((r + 1 : ℕ) : ℤ)))
        (cycleAssociatedToClosedSubscheme C (π ≫ q) Iσ.subschemeι
          (N - 1 - ((r + 1 : ℕ) : ℤ))) := by
    rw [hclaim]
    refine (congrArg (GenuineChern.chernCap C (r + 1) (π ≫ q) (kernel τ) (N - 1)
      (Fin.last (r + 1))) hp1).trans ?_
    rw [GenuineChern.chernCap_properPushforward C (j ≫ π ≫ q) (π ≫ q) j rfl (kernel τ) (r + 1)
      (liftModule τ σ) (kernelPullbackIso j τ hL) (N - 1) (Fin.last (r + 1)) (hpfac _)
      (hpfac _), hIH]
    refine (properChowPushforward_mk C (j ≫ π ≫ q) (π ≫ q) j rfl (N - 1 - ((r + 1 : ℕ) : ℤ))
      (hpfac _) _).trans ?_
    rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C (j ≫ π ≫ q)
        (π ≫ q) j rfl I'.subschemeι _, cycleAssociatedToClosedSubscheme_ker]
    exact congrArg _ (cycle_subschemeι_congr C (π ≫ q) hker _)
  have hrhs := flatPullbackChow_mk_closedSubscheme C q π (r + 1) hd (zeroSchemeOfSection X F s)
    (n - ((r + 2 : ℕ) : ℤ)) hZ (hfac _)
  apply hinj (n - ((r + 2 : ℕ) : ℤ))
  rw [hrhs]
  refine eq_of_heq (h1.symm.trans (h2.trans ((heq_of_eq h3).trans ?_)))
  refine (mk_cycle_heq C (π ≫ q) Iσ.subschemeι (show N - 1 - ((r + 1 : ℕ) : ℤ) =
    n - ((r + 2 : ℕ) : ℤ) + ((r + 1 : ℕ) : ℤ) by omega)).trans ?_
  exact heq_of_eq (congrArg _ (cycle_subschemeι_congr C (π ≫ q) hIσ _))

/-- **The inductive step of [Stacks, Tag 0FA9]**: rank `r + 1` implies rank `r + 2`, by passing
to the projective space bundle `π : 𝐏(ℰ) ⟶ X` with its tautological quotient
`π^*ℰ ⟶ 𝒪(1)`. -/
theorem reducedTopChernCap_succ_succ (C : ChowSituation.{u}) (r : ℕ)
    (IH : ReducedTopChernCap C (r + 1)) : ReducedTopChernCap C (r + 2) := by
  intro X q _ F _ s n hX hZ hreg
  have hFl : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F (r + 2)
  have : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
  have := GenuineChern.flat_bundleProj F (r + 1)
  have := GenuineChern.locallyOfFiniteType_bundleProj F (r + 1)
  have hd : AlgebraicGeometry.RelativeDimension (bundleProj F) (r + 1) :=
    GenuineChern.relativeDimension_bundleProj F (r + 1)
  have hτ : Epi (Stacks.ProjectiveBundleSplitting.tautologicalMap F (bundlePieces F)) :=
    Stacks.ProjectiveBundleSplitting.epi_tautologicalMap F (bundlePieces F)
  have hLinv : AlgebraicGeometry.SheafOfModules.IsInvertible (bundle F).sheaf.obj
      (bundle F).ringCatSheaf.property
      (Stacks.ProjectiveBundleSplitting.tautologicalTwist F (bundlePieces F)) :=
    isInvertible_bundleTwist F
  let τ : (Scheme.Modules.pullback (bundleProj F)).obj F ⟶ bundleTwist F :=
    Stacks.ProjectiveBundleSplitting.tautologicalMap F (bundlePieces F)
  have hτ' : Epi τ := hτ
  exact reducedTopChernCap_step C r IH q (bundleProj F) hd
    (fun k => GenuineChern.pullback_injective q F (GenuineChern.topHalf C) (r + 1) k) F s
    τ n hX hZ hreg
    fun y hyD => hyperplane_bundleSection_properties C q F (r + 1) hd r rfl s hX hZ y hyD

/-- **[Stacks, Tag 0FA9] in the case `X = X'`, in every rank**, by the source's induction on the
rank. -/
theorem reducedTopChernCap (C : ChowSituation.{u}) (r : ℕ) : ReducedTopChernCap C r := by
  have key : ∀ m : ℕ, ReducedTopChernCap C m ∧ ReducedTopChernCap C (m + 1) := by
    intro m
    induction m with
    | zero => exact ⟨reducedTopChernCap_zero C, reducedTopChernCap_one C⟩
    | succ m ih => exact ⟨ih.2, reducedTopChernCap_succ_succ C m ih.2⟩
  exact (key r).1

end Stacks.Chow.SectionZeroScheme

end
