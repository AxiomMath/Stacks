module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapOnCycles
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleProper
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksCore.Tactic.StacksAttribute

/-!
# The cap products of Stacks 02U5 on Chow groups

Let `ℰ` be a finite locally free module of rank `r` on `X`, locally of finite type over the base
of chapter 42. [Stacks, Tag 02U6] says that for every `k`-cycle `α` on `X` the classes
`c_j(ℰ) ∩ α` of [Stacks, Tag 02U5] are the unique classes `α_j ∈ A_{k-j}(X)` with `α_0 = [α]`
satisfying the projective-bundle relation on `𝐏(ℰ)`. The unique solution of that relation for the
class `[α]` is the cap product `Stacks.Chow.GenuineChern.chernCap`, so the content of
Stacks 02U6 is the identity

  `c_j(ℰ) ∩ [α] = c_j(ℰ) ∩ α`

between `chernCap` applied to the class of `α` and the operation
`Stacks.Chow.GenuineChern.chernCapOnCycles` of Stacks 02U5 applied to `α`. In particular the
operation of Stacks 02U5 factors through rational equivalence, which is [Stacks, Tag 02U7].

The proof is the one of the source. Write `α = ∑ n_a [W_a]` over the locally finite family of
integral closed subschemes `W_a` attached to the points of its support and let
`p : X' = ∐ W_a ⟶ X`, which is proper. The cycle `∑ n_a [W_a]` on `X'` pushes forward to `α`, so
by [Stacks, Tag 02U9] `c_j(ℰ) ∩ [α] = p_*(c_j(p^*ℰ) ∩ [∑ n_a [W_a]])`. The Chow group of `X'` is
the product of the Chow groups of the `W_a`, and the restriction to `W_a` commutes with the cap
products ([Stacks, Tag 02U8] for an open immersion), so `c_j(p^*ℰ) ∩ [∑ n_a [W_a]]` is the class
of the cycle restricting to `n_a` times a representative of `c_j(ℰ|_{W_a}) ∩ [W_a]` on each
`W_a`. Its pushforward is, coefficientwise, the locally finite sum defining `c_j(ℰ) ∩ α`.

## Main results

* `Stacks.Chow.GenuineChern.chernCap_eq_chernCapFamilyOfRank` — the cap products are the family
  `Stacks.Chow.chernCapFamilyOfRank` in every rank.
* `Stacks.Chow.GenuineChern.chernCap_chowGroupRestrict` — the cap products commute with
  restriction to an open subscheme.
* `Stacks.Chow.GenuineChern.chernCap_mk_eq_chernCapOnCycles` — **Stacks 02U6**: on the class of
  a cycle `α`, the cap product is `c_j(ℰ) ∩ α` of Stacks 02U5.
* `Stacks.Chow.GenuineChern.chernCapOnCycles_eq_of_rationallyEquivalent` — **Stacks 02U7**.

## References

* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U7](https://stacks.math.columbia.edu/tag/02U7)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- The cap products are the family of Chern class cap products of every rank. -/
theorem chernCap_eq_chernCapFamilyOfRank {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ)
    (j : Fin (r + 1)) (α : chowGroup C sX k) :
    chernCap C r sX E k j α = chernCapFamilyOfRank E r C sX k α j := by
  cases r with
  | zero => rw [chernCap_zero, chernCapFamilyOfRank_rank_zero]
  | succ n => rw [chernCap_succ, bundleChernCap_apply, chernCapFamilyOfRank_succ]

/-- On the fundamental class the cap products are the Chern classes of Stacks 02U0. -/
theorem chernCap_fundamental {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ)
    (j : Fin (r + 1)) :
    chernCap C r sX E k j (QuotientAddGroup.mk' (rationalEquivalences C sX k)
        (cycleAssociatedToClosedSubscheme C sX (𝟙 X) k)) =
      chernClassFundamentalOfRank E r C sX k j := by
  rw [chernCap_eq_chernCapFamilyOfRank]
  rfl

/-- **Stacks 02U8 for an open immersion.** The cap products commute with restriction of Chow
classes to an open subscheme. -/
theorem chernCap_chowGroupRestrict {X U : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (m : U ⟶ X) [IsOpenImmersion m]
    (hm : m ≫ sX = sU) (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (E' : U.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (eE : E' ≅ (Scheme.Modules.pullback m).obj E) (k : ℤ) (j : Fin (r + 1))
    (x : chowGroup C sX k) :
    chowGroupRestrict C sX sU m hm (k - (j : ℤ)) (chernCap C r sX E k j x) =
      chernCap C r sU E' k j (chowGroupRestrict C sX sU m hm k x) := by
  have hk : k + ((0 : ℕ) : ℤ) = k := by simp
  have hk' : k - (j : ℤ) + ((0 : ℕ) : ℤ) = k - (j : ℤ) := by simp
  have hfac := flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion C sX sU m hm k
  have hfacp :=
    flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion C sX sU m hm (k - (j : ℤ))
  have h := chernCap_flatPullback_heq C sX sU m hm 0 (relativeDimension_of_isOpenImmersion m) E
    r E' eE k j hfac hfacp x
  have key : ∀ (a b : ℤ) (h : a = b) (y : chowGroup C sU a),
      HEq (h ▸ y : chowGroup C sU b) y := by
    intro a b h y
    subst h
    rfl
  have key2 : ∀ (a b : ℤ) (h : a = b) (y : chowGroup C sU a),
      HEq (chernCap C r sU E' a j y) (chernCap C r sU E' b j (h ▸ y : chowGroup C sU b)) := by
    intro a b h y
    subst h
    rfl
  rw [← cast_flatPullbackChow_eq_chowGroupRestrict C sX sU m hm (k - (j : ℤ)) hk' hfacp,
    ← cast_flatPullbackChow_eq_chowGroupRestrict C sX sU m hm k hk hfac]
  exact eq_of_heq ((key _ _ hk' _).trans (h.symm.trans (key2 _ _ hk _)))

/-! ### Descent along the coproduct of the integral components -/

/-- **The class of `β` is the pushforward of the class of `∑ n_i [W_i]`.** For `W_i ⟶ X`, `i` in
the support of `β`, integral closed subschemes with generic point `i`, and `γ` the cycle on
`∐ W_i` restricting to `n_i [W_i]` on each piece, the proper pushforward of `γ` along
`P : ∐ W_i ⟶ X` is `β`: the coefficient of `γ` at the generic point of `W_i` is `n_i`, those are
the only nonzero ones, and the pushforward weights are one. -/
private theorem properChowPushforward_mk_sigma_fundamentalCycle {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (k : ℤ) (β : CycleGroup C sX k)
    (Z : ↥(Function.support (β.1 : X → ℤ)) → Scheme.{u}) [∀ i, IsIntegral (Z i)]
    (v : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (v i)]
    (hv : ∀ i, (v i).base (genericPoint (Z i)) = (i : X))
    (P : (∐ Z : Scheme.{u}) ⟶ X) [IsProper P]
    (hPι : ∀ i (z : Z i), P.base (Sigma.ι Z i z) = (v i).base z)
    (hres : ∀ x : (∐ Z : Scheme.{u}), Function.Bijective ((P.residueFieldMap x).hom))
    (γ : CycleGroup C (P ≫ sX) k)
    (hγ : ∀ i (z : Z i),
      γ.1 (Sigma.ι Z i z) = (β.1 (i : X) • fundamentalCycle C (v i ≫ sX) k).1 z) :
    QuotientAddGroup.mk' (rationalEquivalences C sX k) β =
      properChowPushforward C (P ≫ sX) sX P rfl k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C (P ≫ sX) sX P rfl k)
        (QuotientAddGroup.mk' (rationalEquivalences C (P ≫ sX) k) γ) := by
  classical
  have hdim : ∀ i, relativeDimension C.dimensionFunction (v i ≫ sX) (genericPoint (Z i)) = k :=
    fun i ↦ by
      rw [relativeDimension_comp_closedImmersion, hv i]
      exact (mem_cyclesOfDimension_iff_forall_point C sX k β.1).1 β.2 _ i.2
  have hcoeff : ∀ i, ∀ z : Z i,
      (β.1 (i : X) • fundamentalCycle C (v i ≫ sX) k).1 z =
        if z = genericPoint (Z i) then β.1 (i : X) else 0 := fun i z ↦ by
    change β.1 (i : X) • (fundamentalCycle C (v i ≫ sX) k).1 z = _
    rw [fundamentalCycle_eq_single C (v i ≫ sX) genericPoints_eq_singleton (hdim i)
      (Field.toIsField _)]
    simp [Function.locallyFinsuppWithin.single_apply]
  have hepoint : ∀ i, P.base (Sigma.ι Z i (genericPoint (Z i))) = (i : X) := fun i ↦ by
    rw [hPι, hv i]
  have hpush : properPushforward C (P ≫ sX) sX P rfl k γ = β := by
    refine properPushforward_eq_of_support_section C sX (P ≫ sX) P rfl k hres β γ
      (fun i ↦ Sigma.ι Z i (genericPoint (Z i))) hepoint (fun i ↦ ?_) (fun x hx ↦ ?_)
    · rw [hγ i, hcoeff i]
      simp
    · obtain ⟨⟨i, z⟩, rfl⟩ := (sigmaMk Z).surjective x
      rw [sigmaMk_mk, hγ i, hcoeff i] at hx
      refine ⟨i, ?_⟩
      by_cases hz : z = genericPoint (Z i)
      · rw [sigmaMk_mk, hz]
      · simp [hz] at hx
  rw [properChowPushforward_mk, hpush]

/-- **The cap product on the coproduct of the components.** With `γ` restricting to `n_i [W_i]`
and `δ` to `n_i` times a representative `rep i` of `c_j(ℰ|_{W_i}) ∩ [W_i]` on each piece, the cap
product of the class of `γ` is the class of `δ`: the pieces are a clopen decomposition of
`∐ W_i`, and restriction to each commutes with the cap products by Stacks 02U8. -/
private theorem chernCap_mk_of_sigma {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (k : ℤ)
    (j : Fin (r + 1)) {I : Type u} (Z : I → Scheme.{u}) (v : ∀ i, Z i ⟶ X)
    [∀ i, LocallyOfFiniteType (v i)] (P : (∐ Z : Scheme.{u}) ⟶ X) [IsProper P]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback P).obj E) r]
    (ht : ∀ i, Sigma.ι Z i ≫ (P ≫ sX) = v i ≫ sX) (hPcomp : ∀ i, Sigma.ι Z i ≫ P = v i)
    (b : I → ℤ) (rep : ∀ i, CycleGroup C (v i ≫ sX) (k - (j : ℤ)))
    (hrep : ∀ i,
      haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (v i) E r
      chernCap C r (v i ≫ sX) ((Scheme.Modules.pullback (v i)).obj E) k j
          (QuotientAddGroup.mk' (rationalEquivalences C (v i ≫ sX) k)
            (fundamentalCycle C (v i ≫ sX) k)) =
        QuotientAddGroup.mk' (rationalEquivalences C (v i ≫ sX) (k - (j : ℤ))) (rep i))
    (γ : CycleGroup C (P ≫ sX) k) (δ : CycleGroup C (P ≫ sX) (k - (j : ℤ)))
    (hγ : ∀ i (z : Z i), γ.1 (Sigma.ι Z i z) = (b i • fundamentalCycle C (v i ≫ sX) k).1 z)
    (hδ : ∀ i (z : Z i), δ.1 (Sigma.ι Z i z) = (b i • rep i).1 z) :
    chernCap C r (P ≫ sX) ((Scheme.Modules.pullback P).obj E) k j
        (QuotientAddGroup.mk' (rationalEquivalences C (P ≫ sX) k) γ) =
      QuotientAddGroup.mk' (rationalEquivalences C (P ≫ sX) (k - (j : ℤ))) δ := by
  have : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (v i)).obj E) r := fun i ↦
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (v i) E r
  have eE : ∀ i, (Scheme.Modules.pullback (v i)).obj E ≅
      (Scheme.Modules.pullback (Sigma.ι Z i)).obj ((Scheme.Modules.pullback P).obj E) :=
    fun i ↦ (Scheme.Modules.pullbackCongr (show v i = Sigma.ι Z i ≫ P from
      (hPcomp i).symm)).app E ≪≫ ((Scheme.Modules.pullbackComp (Sigma.ι Z i) P).app E).symm
  rw [← sub_eq_zero]
  refine eq_zero_of_chowGroupRestrict_eq_zero C (P ≫ sX) (fun i ↦ v i ≫ sX) (Sigma.ι Z) ht
    (isClopenDecomposition_opensRange_sigmaι Z) (k - (j : ℤ)) _ fun i ↦ ?_
  have hres : ∀ {d} (c) (w : CycleGroup C (v i ≫ sX) d), (∀ z, c.1 (Sigma.ι Z i z) = w.1 z) →
      cycleGroupRestrict C (P ≫ sX) (v i ≫ sX) (Sigma.ι Z i) (ht i) d c = w := fun c w h ↦
    Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ by
      rw [cycleGroupRestrict_apply]; exact h z)
  rw [map_sub, sub_eq_zero, chernCap_chowGroupRestrict C (P ≫ sX) (v i ≫ sX) (Sigma.ι Z i)
    (ht i) ((Scheme.Modules.pullback P).obj E) r ((Scheme.Modules.pullback (v i)).obj E)
    (eE i) k j, chowGroupRestrict_mk, chowGroupRestrict_mk, hres γ _ (hγ i),
    hres δ _ (hδ i), map_zsmul, map_zsmul, map_zsmul]
  congr 1
  exact hrep i

/-- **The coproduct of a locally finite family of proper morphisms maps properly to `X`.** The
descent `P : ∐ Z ⟶ X` of a family `v i : Z i ⟶ X` with locally finite images is proper, restricts
to `v i` on the `i`-th piece, and is bijective on residue fields because it is surjective on
stalks — so the weights of the proper pushforward along it are one. -/
private theorem exists_proper_sigmaDesc_of_locallyFinite {X : Scheme.{u}} {I : Type u}
    (Z : I → Scheme.{u}) (v : ∀ i, Z i ⟶ X) [∀ i, IsProper (v i)]
    [∀ i, SurjectiveOnStalks (v i)] (hlf : LocallyFinite fun i ↦ Set.range (v i)) :
    ∃ P : (∐ Z : Scheme.{u}) ⟶ X, IsProper P ∧ (∀ i, Sigma.ι Z i ≫ P = v i) ∧
      ∀ x : (∐ Z : Scheme.{u}), Function.Bijective ((P.residueFieldMap x).hom) := by
  have hsurj : SurjectiveOnStalks (Sigma.desc v) := surjectiveOnStalks_sigmaDesc Z v
  exact ⟨Sigma.desc v, isProper_sigmaDesc_of_locallyFinite Z v hlf, fun i ↦ Sigma.ι_comp_desc v i,
    fun x ↦ bijective_residueFieldMap_of_surjective_stalkMap (Sigma.desc v) x
      ((Sigma.desc v).stalkMap_surjective x)⟩

/-- **The fibre of `P` over a point of `X`, reindexed by the sigma type.** For `δ` restricting to
`n_i (rep i)` on the `i`-th piece, the indicator of the fibre `P⁻¹(y)` at the point labelled
`⟨i, z⟩` is `n_i (rep i) z` when `v i` carries `z` to `y` and `0` otherwise.  That function has
finite support: only finitely many images `v i` meet `y`, and each `v i` is injective. -/
private theorem exists_indicator_fibre_eq_of_sigma {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {I : Type u} (Z : I → Scheme.{u}) (v : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (v i)] (hlf : LocallyFinite fun i ↦ Set.range (v i))
    (P : (∐ Z : Scheme.{u}) ⟶ X) [IsProper P]
    (hPι : ∀ i (z : Z i), P.base (Sigma.ι Z i z) = (v i).base z)
    (d : ℤ) (b : I → ℤ) (rep : ∀ i, CycleGroup C (v i ≫ sX) d) (δ : CycleGroup C (P ≫ sX) d)
    (hδ : ∀ i (z : Z i), δ.1 (Sigma.ι Z i z) = (b i • rep i).1 z) (y : X) :
    ∃ g : (Σ i : I, Z i) → ℤ,
      (∀ s, (P.base ⁻¹' {y}).indicator δ.1 ((sigmaMk Z).toEquiv s) = g s) ∧
      (∀ (i : I) (z : Z i), (v i).base z = y → g ⟨i, z⟩ = b i * (rep i).1 z) ∧
      (∀ (i : I) (z : Z i), (v i).base z ≠ y → g ⟨i, z⟩ = 0) ∧
      (Function.support g).Finite := by
  classical
  refine ⟨fun s ↦ if (v s.1).base s.2 = y then b s.1 * (rep s.1).1 s.2 else 0, ?_,
    fun _ _ hz ↦ ite_eq_left hz, fun _ _ hz ↦ ite_eq_right hz, ?_⟩
  · rintro ⟨i, z⟩
    have hval : δ.1 ((sigmaMk Z).toEquiv ⟨i, z⟩) = b i * (rep i).1 z := by
      change δ.1 (sigmaMk Z ⟨i, z⟩) = _
      rw [sigmaMk_mk, hδ i]
      simp
    have hbase : P.base ((sigmaMk Z).toEquiv ⟨i, z⟩) = (v i).base z := by
      change P.base (sigmaMk Z ⟨i, z⟩) = _
      rw [sigmaMk_mk, hPι]
    by_cases hz : (v i).base z = y
    · rw [Set.indicator_of_mem (by rw [Set.mem_preimage, hbase]; exact hz), hval]
      simp [hz]
    · rw [Set.indicator_of_notMem (by rw [Set.mem_preimage, hbase]; exact hz)]
      simp [hz]
  · have hinj : ∀ i : I, Function.Injective (v i).base := fun i ↦
      (v i).isClosedEmbedding.injective
    have hS : {i : I | y ∈ Set.range (v i)}.Finite := hlf.point_finite y
    refine Set.Finite.of_finite_image (f := Sigma.fst) (hS.subset ?_) ?_
    · rintro _ ⟨⟨i, z⟩, hs, rfl⟩
      by_cases hz : (v i).base z = y
      · exact ⟨z, hz⟩
      · exact absurd (by simp [hz]) hs
    · rintro ⟨i, z⟩ hs ⟨i', z'⟩ hs' (hii' : i = i')
      subst hii'
      have hz : (v i).base z = y := by
        by_contra hz
        exact hs (by simp [hz])
      have hz' : (v i).base z' = y := by
        by_contra hz'
        exact hs' (by simp [hz'])
      rw [hinj i (hz.trans hz'.symm)]

/-- **The pushforward of the cycle assembled from the component representatives.** If `cmp i` is
the pushforward to `X` of a cycle `rep i` on `W_i` and `β'` is the locally finite sum of the
`n_i (cmp i)`, then the proper pushforward along `P : ∐ W_i ⟶ X` of the cycle restricting to
`n_i (rep i)` on each piece is `β'`: the fibre of `P` over a point of `X` is the disjoint union of
the fibres of the `W_i`, and the pushforward weights are one. -/
private theorem properPushforward_sigma_eq_of_components {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {I : Type u} (Z : I → Scheme.{u}) (v : ∀ i, Z i ⟶ X)
    [∀ i, IsClosedImmersion (v i)] (hlf : LocallyFinite fun i ↦ Set.range (v i))
    (P : (∐ Z : Scheme.{u}) ⟶ X) [IsProper P]
    (hPι : ∀ i (z : Z i), P.base (Sigma.ι Z i z) = (v i).base z)
    (hres : ∀ x : (∐ Z : Scheme.{u}), Function.Bijective ((P.residueFieldMap x).hom))
    (d : ℤ) (b : I → ℤ) (rep : ∀ i, CycleGroup C (v i ≫ sX) d) (cmp : I → X → ℤ)
    (hcomp : ∀ i y, cmp i y = ∑ᶠ z ∈ (v i).base ⁻¹' {y}, (rep i).1 z)
    (β' : CycleGroup C sX d) (hβ' : ∀ y, β'.1 y = ∑ᶠ i, b i * cmp i y)
    (δ : CycleGroup C (P ≫ sX) d)
    (hδ : ∀ i (z : Z i), δ.1 (Sigma.ι Z i z) = (b i • rep i).1 z) :
    properPushforward C (P ≫ sX) sX P rfl d δ = β' := by
  classical
  -- weights of the pushforward along `P` are one
  have hterm : ∀ (c : CycleGroup C (P ≫ sX) d) (x : (∐ Z : Scheme.{u})), c.1 x *
      (if relativeDimension C.dimensionFunction (P ≫ sX) x =
          relativeDimension C.dimensionFunction sX (P.base x) then (P.residueDegree x : ℤ)
        else 0) = c.1 x := by
    intro c x
    rw [relativeDimension_comp_of_bijective_residueFieldMap C.dimensionFunction P sX x (hres x),
      residueDegree_eq_one_of_bijective_residueFieldMap P x (hres x)]
    simp
  refine Subtype.ext ?_
  apply Function.locallyFinsuppWithin.ext
  intro y
  change (properPushforward C (P ≫ sX) sX P rfl d δ).1 y = β'.1 y
  rw [hβ' y, properPushforward_apply, finsum_mem_congr rfl (fun x _ ↦ hterm δ x)]
  conv_rhs => arg 1; ext i; rw [hcomp i y]
  -- reindex the fibre of `P` over `y` by the sigma type
  obtain ⟨g, hg, hgmem, hgzero, hgfin⟩ :=
    exists_indicator_fibre_eq_of_sigma C sX Z v hlf P hPι d b rep δ hδ y
  rw [finsum_mem_def, ← finsum_comp_equiv (sigmaMk Z).toEquiv, finsum_congr hg,
    finsum_sigma g hgfin]
  refine finsum_congr fun i ↦ ?_
  rw [finsum_mem_def, mul_finsum]
  refine finsum_congr fun z ↦ ?_
  by_cases hz : (v i).base z = y
  · simp [hgmem i z hz, hz]
  · simp [hgzero i z hz, hz]

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]

/-- **Stacks 02U6.** For a `k`-cycle `α` on `X`, the cap product of its class with the `j`-th
Chern class — the `j`-th member of the unique family solving the projective-bundle relation for
`[α]` — is `c_j(ℰ) ∩ α`, the operation of Stacks 02U5 on cycles. -/
theorem chernCap_mk_eq_chernCapOnCycles (k : ℤ) (j : Fin (r + 1)) (β : CycleGroup C sX k) :
    chernCap C r sX E k j (QuotientAddGroup.mk' (rationalEquivalences C sX k) β) =
      chernCapOnCycles C sX E r k j β := by
  classical
  -- the integral components of `β` and the coproduct `W` of them
  let I : Type u := ↥(Function.support (β.1 : X → ℤ))
  let Z : I → Scheme.{u} := fun i ↦ (integralComponentAt (i : X)).subscheme
  let v : ∀ i, Z i ⟶ X := fun i ↦ (integralComponentAt (i : X)).subschemeι
  have : ∀ i, IsIntegral (Z i) := fun i ↦ isIntegral_integralComponentAt (i : X)
  have hv : ∀ i, (v i).base (genericPoint (Z i)) = (i : X) := fun i ↦
    genericPointOf_integralComponentAt (i : X)
  have hlf : LocallyFinite fun i ↦ Set.range (v i) :=
    locallyFinite_range_subschemeι_support C sX k β
  -- the proper descent `P : ∐ W_i ⟶ X`, with weights one for its pushforward
  obtain ⟨P, hproper, hPcomp, hres⟩ := exists_proper_sigmaDesc_of_locallyFinite Z v hlf
  have ht : ∀ i, Sigma.ι Z i ≫ (P ≫ sX) = v i ≫ sX := fun i ↦ by
    rw [← Category.assoc, hPcomp i]
  have hPι : ∀ i (z : Z i), P.base (Sigma.ι Z i z) = (v i).base z := fun i z ↦ by
    rw [← Scheme.Hom.comp_apply, hPcomp i]
  have hDim : ∀ i, schemeDeltaDimension C (v i ≫ sX) = (k : EInt) := fun i ↦
    schemeDeltaDimension_cycleSupportIndex β i
  have hrank : PullbackPreservesRank E r := fun g ↦
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g E r
  -- a representative of `c_j(ℰ|_{W_i}) ∩ [W_i]` on each component
  let rep : ∀ i, CycleGroup C (v i ≫ sX) (k - (j : ℤ)) := fun i ↦
    chernClassComponentCycleOn C sX E r hrank k j (chernCycleRule C r)
      (integralComponentAt (i : X)) (isIntegral_integralComponentAt (i : X)) (hDim i)
  -- the cycle `∑ n_i [W_i]` on `W`
  obtain ⟨γ, hγ⟩ := exists_cycleGroup_of_sigma C Z (P ≫ sX) (fun i ↦ v i ≫ sX) ht k
    (fun i ↦ β.1 (i : X) • fundamentalCycle C (v i ≫ sX) k)
  -- the cycle on `W` restricting to `n_i` times the representative on `W_i`
  obtain ⟨δ, hδ⟩ := exists_cycleGroup_of_sigma C Z (P ≫ sX) (fun i ↦ v i ≫ sX) ht (k - (j : ℤ))
    (fun i ↦ β.1 (i : X) • rep i)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback P).obj E) r :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback P E r
  -- (A) the class of `β` is the pushforward of the class of `γ`
  have hmk := properChowPushforward_mk_sigma_fundamentalCycle C sX k β Z v hv P hPι hres γ hγ
  -- (B) the cap product of `[γ]`, computed on the pieces
  have hC := chernCap_mk_of_sigma C sX E r k j Z v P ht hPcomp (fun i ↦ β.1 (i : X)) rep
    (fun i ↦ (chernCap_fundamental C (v i ≫ sX) ((Scheme.Modules.pullback (v i)).obj E) r k
      j).trans (mk_chowRep C (v i ≫ sX) _).symm) γ δ hγ hδ
  -- (C) the pushforward of `δ` is the cycle defining `c_j(ℰ) ∩ β`
  obtain ⟨β', hβ'mk, hβ'⟩ := chernCapOnCycles_finsum C sX E r k j
    (fun i : I ↦ integralComponentAt (i : X)) (fun i ↦ isIntegral_integralComponentAt (i : X))
    hDim (locallyFinite_support_integralComponentAt β) (fun i ↦ β.1 (i : X)) β
    (cycle_eq_finsum_primeCycles β)
  have hA := properPushforward_sigma_eq_of_components C sX Z v hlf P hPι hres (k - (j : ℤ))
    (fun i ↦ β.1 (i : X)) rep
    (fun i ↦ (chernClassComponentCycle C sX E r hrank k j (chernCycleRule C r)
      (integralComponentAt (i : X)) (isIntegral_integralComponentAt (i : X)) (hDim i)).1)
    (fun i y ↦ properPushforward_apply_of_isClosedImmersion C (v i ≫ sX) sX (v i) rfl
      (k - (j : ℤ)) (rep i) y) β' hβ' δ hδ
  -- assemble
  rw [hmk, chernCap_properPushforward C (P ≫ sX) sX P rfl E r ((Scheme.Modules.pullback P).obj E)
    (Iso.refl _) k j _
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C (P ≫ sX) sX P rfl
      (k - (j : ℤ))), hC, properChowPushforward_mk, hA]
  exact hβ'mk.symm

/-- **Stacks 02U7.** Rationally equivalent `k`-cycles have the same cap products with the Chern
classes: the operation of Stacks 02U5 factors through `A_k(X)`. -/
@[stacks 02U7]
theorem chernCapOnCycles_eq_of_rationallyEquivalent (k : ℤ) (j : Fin (r + 1))
    (α β : CycleGroup C sX k) (h : RationallyEquivalent C sX k α β) :
    chernCapOnCycles C sX E r k j α = chernCapOnCycles C sX E r k j β := by
  have hclass : QuotientAddGroup.mk' (rationalEquivalences C sX k) α =
      QuotientAddGroup.mk' (rationalEquivalences C sX k) β := by
    have h0 : QuotientAddGroup.mk' (rationalEquivalences C sX k) (α - β) = 0 :=
      (QuotientAddGroup.eq_zero_iff (N := rationalEquivalences C sX k) (α - β)).2 h
    rwa [map_sub, sub_eq_zero] at h0
  rw [← chernCap_mk_eq_chernCapOnCycles, ← chernCap_mk_eq_chernCapOnCycles, hclass]

end Stacks.Chow.GenuineChern

end
