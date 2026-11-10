module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseUnconditional.OperationClasses

/-!
# Locality on pieces, central classes and the vertical generators

This part of the proof of Stacks 0FC6 shows that commuting with a bivariant class is local on a
decomposition of the source into open and closed pieces
(`Stacks.Chow.bivariantCommuteOverBase_of_forall_piece`), introduces the classes central over the
base (`Stacks.Chow.IsCentralOverBase`) and the subgroup they form
(`Stacks.Chow.centralOverBaseSubgroup`), shows that the classes built by the operations of
chapter 42 are central, constructs flat pullback after a class towards the base
(`Stacks.Chow.exists_isFlatPullbackAfter`), and shows that the vertical generators of the proof
of Stacks 0FC5 over a closed point of the base are built by those operations
(`Stacks.Chow.exists_isChowOperationClassOverBase_cap_eq_of_closedPoint`), a closed point with a
proper generalization being an effective Cartier divisor on the base
(`Stacks.Chow.IsDedekindChowBase.isEffectiveCartierDivisor_integralComponentAt`).

## References

* [Stacks Project, Tag 0FC6](https://stacks.math.columbia.edu/tag/0FC6)
* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Commuting is local on a decomposition into open and closed pieces -/

/-- An open immersion whose image lies in that of another open immersion `ρ` factors through
`ρ` by an open immersion. -/
private theorem exists_isOpenImmersion_comp_eq_of_opensRange_le {X U V : Scheme.{u}} (ρ : U ⟶ X)
    [IsOpenImmersion ρ] (μ : V ⟶ X) [IsOpenImmersion μ] (hle : μ.opensRange ≤ ρ.opensRange) :
    ∃ (ℓ : V ⟶ U) (_ : IsOpenImmersion ℓ), ℓ ≫ ρ = μ := by
  have hsub : Set.range μ.base ⊆ Set.range ρ.base := hle
  have hfac : IsOpenImmersion.lift ρ μ hsub ≫ ρ = μ := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (IsOpenImmersion.lift ρ μ hsub ≫ ρ) := by rw [hfac]; infer_instance
  exact ⟨_, IsOpenImmersion.of_comp _ ρ, hfac⟩

/-- Two Chow classes with the same restriction along an open immersion `ρ` have the same
restriction along every open immersion `μ` whose image lies in that of `ρ`, since `μ` factors
through `ρ`. -/
theorem chowGroupRestrict_eq_of_opensRange_le (C : ChowSituation.{u}) {X U V : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
    (sV : V ⟶ C.S) [LocallyOfFiniteType sV] (ρ : U ⟶ X) [IsOpenImmersion ρ] (hρ : ρ ≫ sX = sU)
    (μ : V ⟶ X) [IsOpenImmersion μ] (hμ : μ ≫ sX = sV) (hle : μ.opensRange ≤ ρ.opensRange)
    (k : ℤ) {α β : chowGroup C sX k}
    (h : chowGroupRestrict C sX sU ρ hρ k α = chowGroupRestrict C sX sU ρ hρ k β) :
    chowGroupRestrict C sX sV μ hμ k α = chowGroupRestrict C sX sV μ hμ k β := by
  obtain ⟨ℓ, _, hfac⟩ := exists_isOpenImmersion_comp_eq_of_opensRange_le ρ μ hle
  have hℓs : ℓ ≫ sU = sV := by rw [← hρ, ← Category.assoc, hfac, hμ]
  rw [chowGroupRestrict_congr C sX sV μ hμ k _ hfac.symm (by rw [hfac, hμ]),
    ← chowGroupRestrict_comp C sX sU ρ hρ k sV _ hℓs, h, chowGroupRestrict_comp]

/-- Pushforward along an isomorphism `e` over the base is restriction along an inverse `e'`
of `e`. -/
theorem chowPushforwardOfIso_eq_chowGroupRestrict (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (e : A ⟶ B) [IsIso e] (he : e ≫ sB = sA) (e' : B ⟶ A) [IsIso e'] (hee' : e' ≫ e = 𝟙 B)
    (k : ℤ) (α : chowGroup C sA k) :
    chowPushforwardOfIso C sA sB e he k α =
      chowGroupRestrict C sA sB e' (by rw [← he, ← Category.assoc, hee', Category.id_comp]) k
        α := by
  rw [chowGroupRestrict_of_isIso]
  exact chowPushforwardOfIso_congr_apply C sA sB _ _ (IsIso.inv_eq_of_hom_inv_id hee').symm _ _ _ _

/-- The fundamental classes attached to equal structure morphisms over the base are
heterogeneously equal. -/
theorem fundamentalChowClass_heq_of_hom_eq (C : ChowSituation.{u}) {T : Scheme.{u}}
    {f g : T ⟶ C.S} [LocallyOfFiniteType f] [LocallyOfFiniteType g] (h : f = g) (k : ℤ) :
    fundamentalChowClass C f k ≍ fundamentalChowClass C g k := by
  subst h
  rfl

/-- Let `q : A ⟶ B` be proper and an open immersion, the inclusion of an open and closed
subscheme, and let `μ : B' ⟶ B` be an open immersion whose image lies in that of `q`. If
`dim_δ A ≤ k`, then the restriction of `q_*[A]_k` along `μ` is `[B']_k`: restricting `q_*` back
along `q` is the identity, by the open-immersion case of Stacks 02RG for the kernel pair of `q`,
and `μ` factors through `q`. -/
theorem chowGroupRestrict_properChowPushforward_fundamentalChowClass (C : ChowSituation.{u})
    {A B B' : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (sB' : B' ⟶ C.S) [LocallyOfFiniteType sB'] (q : A ⟶ B) [IsProper q]
    [IsOpenImmersion q] (hq : q ≫ sB = sA) (μ : B' ⟶ B) [IsOpenImmersion μ] (hμ : μ ≫ sB = sB')
    (hle : μ.opensRange ≤ q.opensRange) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB q hq k)
    (hdim : schemeDeltaDimension C sA ≤ (k : EInt)) :
    chowGroupRestrict C sB sB' μ hμ k
        (properChowPushforward C sA sB q hq k hfac (fundamentalChowClass C sA k)) =
      fundamentalChowClass C sB' k := by
  obtain ⟨ℓ, _, hfacℓ⟩ := exists_isOpenImmersion_comp_eq_of_opensRange_le q μ hle
  have hℓs : ℓ ≫ sA = sB' := by rw [← hq, ← Category.assoc, hfacℓ, hμ]
  have hback := chowGroupRestrict_properChowPushforward C sA sB sA sA q hq (𝟙 A)
    (Category.id_comp sA) q hq (𝟙 A) (Category.id_comp sA) (IsKernelPair.id_of_mono q) k hfac
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
    (fundamentalChowClass C sA k)
  rw [properChowPushforward_eq_chowPushforwardOfIso C sA sA (𝟙 A), chowGroupRestrict_id,
    chowPushforwardOfIso_id] at hback
  rw [chowGroupRestrict_congr C sB sB' μ hμ k _ hfacℓ.symm (by rw [hfacℓ, hμ]),
    ← chowGroupRestrict_comp C sB sA q hq k sB' _ hℓs, hback,
    chowGroupRestrict_fundamentalChowClass C sA sB' _ hℓs k hdim]

/-- The comparison `Y ×_Z (X ×_S T) ⟶ X ×_S (Y ×_Z T)` is an isomorphism, with inverse
`Stacks.Chow.mixedCommuteHom`. -/
instance isIso_mixedCommuteInv {C : ChowSituation.{u}} {X Y Z : Scheme.{u}} (sX : X ⟶ C.S)
    (sZ : Z ⟶ C.S) (w : Y ⟶ Z) {T : Scheme.{u}} (t : T ⟶ Z) :
    IsIso (mixedCommuteInv sX sZ w t) :=
  ⟨⟨mixedCommuteHom sX sZ w t, mixedCommuteInv_comp_mixedCommuteHom sX sZ w t,
    mixedCommuteHom_comp_mixedCommuteInv sX sZ w t⟩⟩

section Localization

variable (C : ChowSituation.{u}) (G : GysinSystem C) {W Y Z : Scheme.{u}} (sW : W ⟶ C.S)
  [LocallyOfFiniteType sW] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (w : Y ⟶ Z)
  [LocallyOfFiniteType w] (p q : ℤ)

/-- **Commuting is local on the pieces of a decomposition.** Let `W = ∐_i W_i` be a decomposition
into open and closed subschemes and let `c ∈ A^p(W ⟶ S)`. Suppose that for each `i` some class
`d_i ∈ A^p(W ⟶ S)` commuting with `c' ∈ A^q(Y ⟶ Z)` caps like `c` on the piece over `W_i` of
the base change to every test scheme. Then `c` commutes with `c'`.

The identity `c ∩ (c' ∩ α) = c' ∩ (c ∩ α)` is checked on the pieces of `Y ×_Z (W ×_S T)`
(`Stacks.Chow.chowGroupClopenRestrictEquiv`). On the `i`-th piece both sides see `c` only
through its cap operation on the `i`-th piece: for the left side by hypothesis at the test scheme
`Y ×_Z T`, for the right side because capping with `c'` commutes with restricting the test scheme
to an open, the flat-pullback axiom of Stacks 0B76 in relative dimension zero. So each side
restricts as it does for `d_i`, for which the identity holds. -/
theorem bivariantCommuteOverBase_of_forall_piece {I : Type u} (UX : I → W.Opens)
    (hX : IsClopenDecomposition UX)
    (c : BivariantClass C G sW (𝟙 C.S) sW (Category.comp_id sW) p)
    (d : I → BivariantClass C G sW (𝟙 C.S) sW (Category.comp_id sW) p)
    (c' : BivariantClass C G (w ≫ sZ) sZ w rfl q)
    (hd : ∀ i, BivariantCommuteOverBase C G sW sZ w p q (d i) c')
    (hcd : ∀ i {T : Scheme.{u}} (u : T ⟶ C.S) [LocallyOfFiniteType u] (k : ℤ)
      (α : chowGroup C (u ≫ 𝟙 C.S) k),
      chowGroupRestrict C (pullback.fst sW u ≫ sW)
          ((pullback.fst sW u ⁻¹ᵁ UX i).ι ≫ pullback.fst sW u ≫ sW)
          (pullback.fst sW u ⁻¹ᵁ UX i).ι rfl (k - p) (c.cap u k α) =
        chowGroupRestrict C (pullback.fst sW u ≫ sW)
          ((pullback.fst sW u ⁻¹ᵁ UX i).ι ≫ pullback.fst sW u ≫ sW)
          (pullback.fst sW u ⁻¹ᵁ UX i).ι rfl (k - p) ((d i).cap u k α)) :
    BivariantCommuteOverBase C G sW sZ w p q c c' := by
  intro T t _ k α
  have hP : IsClopenDecomposition fun i ↦
      ((pullback.snd w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ pullback.fst sW (t ≫ sZ)) ⁻¹ᵁ
        UX i).ι.opensRange := by
    simp only [Scheme.Opens.opensRange_ι]
    exact hX.preimage _
  refine (chowGroupClopenRestrictEquiv C
    (pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ)) _ _ (fun _ ↦ rfl) hP
    ((k - q) - p)).injective (funext fun i ↦ ?_)
  simp only [chowGroupClopenRestrictEquiv_apply]
  set O := (pullback.snd w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ pullback.fst sW (t ≫ sZ)) ⁻¹ᵁ UX i
    with hO
  -- the side capping first with `c'`
  have hL : ∀ x y : chowGroup C
      (pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ)) ≫ sW) ((k - q) - p),
      chowGroupRestrict C (pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ)) ≫ sW)
          ((pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ)) ⁻¹ᵁ UX i).ι ≫
            pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ)) ≫ sW)
          (pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ)) ⁻¹ᵁ UX i).ι rfl ((k - q) - p) x =
        chowGroupRestrict C (pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ)) ≫ sW)
          ((pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ)) ⁻¹ᵁ UX i).ι ≫
            pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ)) ≫ sW)
          (pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ)) ⁻¹ᵁ UX i).ι rfl ((k - q) - p) y →
      chowGroupRestrict C (pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
          (O.ι ≫ pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ)) O.ι rfl
          ((k - q) - p)
          (chowPushforwardOfIso C (pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ)) ≫ sW)
            (pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
            (mixedCommuteHom sW sZ w t) (mixedCommuteHom_comp_structureMorphism sW sZ w t)
            ((k - q) - p) x) =
        chowGroupRestrict C (pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
          (O.ι ≫ pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ)) O.ι rfl
          ((k - q) - p)
          (chowPushforwardOfIso C (pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ)) ≫ sW)
            (pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
            (mixedCommuteHom sW sZ w t) (mixedCommuteHom_comp_structureMorphism sW sZ w t)
            ((k - q) - p) y) := by
    intro x y hxy
    rw [chowPushforwardOfIso_eq_chowGroupRestrict C _ _ _ _ (mixedCommuteInv sW sZ w t)
        (mixedCommuteInv_comp_mixedCommuteHom sW sZ w t),
      chowPushforwardOfIso_eq_chowGroupRestrict C _ _ _ _ (mixedCommuteInv sW sZ w t)
        (mixedCommuteInv_comp_mixedCommuteHom sW sZ w t),
      chowGroupRestrict_comp, chowGroupRestrict_comp]
    refine chowGroupRestrict_eq_of_opensRange_le C _ _ _ _ rfl _ _ ?_ _ hxy
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.opensRange_ι]
    change ((O.ι ≫ mixedCommuteInv sW sZ w t) ≫
      pullback.fst sW (pullback.fst w t ≫ (w ≫ sZ))).base z ∈ UX i
    rw [Category.assoc, mixedCommuteInv_fst]
    exact z.2
  -- the side capping first with `c`
  set U := pullback.fst sW (t ≫ sZ) ⁻¹ᵁ UX i with hU
  have hR : ∀ γ γ' : chowGroup C ((pullback.snd sW (t ≫ sZ) ≫ t) ≫ sZ) (k - p),
      chowGroupRestrict C ((pullback.snd sW (t ≫ sZ) ≫ t) ≫ sZ)
          ((U.ι ≫ pullback.snd sW (t ≫ sZ) ≫ t) ≫ sZ) U.ι (Category.assoc _ _ _).symm
          (k - p) γ =
        chowGroupRestrict C ((pullback.snd sW (t ≫ sZ) ≫ t) ≫ sZ)
          ((U.ι ≫ pullback.snd sW (t ≫ sZ) ≫ t) ≫ sZ) U.ι (Category.assoc _ _ _).symm
          (k - p) γ' →
      chowGroupRestrict C (pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
          (O.ι ≫ pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ)) O.ι rfl
          ((k - q) - p)
          (chowGroupDegreeEquiv C (pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
            (by ring : (k - p) - q = (k - q) - p)
            (c'.cap (pullback.snd sW (t ≫ sZ) ≫ t) (k - p) γ)) =
        chowGroupRestrict C (pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
          (O.ι ≫ pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ)) O.ι rfl
          ((k - q) - p)
          (chowGroupDegreeEquiv C (pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
            (by ring : (k - p) - q = (k - q) - p)
            (c'.cap (pullback.snd sW (t ≫ sZ) ≫ t) (k - p) γ')) := by
    intro γ γ' hγ
    rw [chowGroupRestrict_chowGroupDegreeEquiv, chowGroupRestrict_chowGroupDegreeEquiv]
    congr 1
    have hbase : bivariantBaseChangeMap w (pullback.snd sW (t ≫ sZ) ≫ t) U.ι ≫
        (pullback.fst w (pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ)) =
        pullback.fst w (U.ι ≫ pullback.snd sW (t ≫ sZ) ≫ t) ≫ (w ≫ sZ) := by
      rw [← Category.assoc (bivariantBaseChangeMap _ _ _), bivariantBaseChangeMap_fst]
    refine chowGroupRestrict_eq_of_opensRange_le C _ _ _
      (bivariantBaseChangeMap w (pullback.snd sW (t ≫ sZ) ≫ t) U.ι) hbase O.ι rfl ?_ _ ?_
    · have sq := (isPullback_bivariantBaseChangeMap w (pullback.snd sW (t ≫ sZ) ≫ t) U.ι).flip
      rintro _ ⟨z, rfl⟩
      have hrange := IsOpenImmersion.range_pullbackFst U.ι
        (pullback.snd w (pullback.snd sW (t ≫ sZ) ≫ t))
      obtain ⟨y, hy⟩ : O.ι.base z ∈ Set.range (pullback.fst
          (pullback.snd w (pullback.snd sW (t ≫ sZ) ≫ t)) U.ι).base := by
        rw [hrange, Scheme.Opens.opensRange_ι]
        exact z.2
      refine ⟨sq.isoPullback.inv.base y, ?_⟩
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hy]
    · rw [BivariantClass.cap_chowGroupRestrict C G (w ≫ sZ) sZ w rfl q c'
          (pullback.snd sW (t ≫ sZ) ≫ t) U.ι (U.ι ≫ pullback.snd sW (t ≫ sZ) ≫ t) rfl
          (bivariantBaseChangeMap w (pullback.snd sW (t ≫ sZ) ≫ t) U.ι)
          (isPullback_bivariantBaseChangeMap w (pullback.snd sW (t ≫ sZ) ≫ t) U.ι)
          (bivariantBaseChangeMap_fst _ _ _) (k - p) (Category.assoc _ _ _).symm hbase γ,
        BivariantClass.cap_chowGroupRestrict C G (w ≫ sZ) sZ w rfl q c'
          (pullback.snd sW (t ≫ sZ) ≫ t) U.ι (U.ι ≫ pullback.snd sW (t ≫ sZ) ≫ t) rfl
          (bivariantBaseChangeMap w (pullback.snd sW (t ≫ sZ) ≫ t) U.ι)
          (isPullback_bivariantBaseChangeMap w (pullback.snd sW (t ≫ sZ) ≫ t) U.ι)
          (bivariantBaseChangeMap_fst _ _ _) (k - p) (Category.assoc _ _ _).symm hbase γ', hγ]
  have hcond : pullback.fst sW (t ≫ sZ) ≫ sW = (pullback.snd sW (t ≫ sZ) ≫ t) ≫ sZ := by
    rw [Category.assoc]; exact pullback.condition
  have hv : U.ι ≫ (pullback.fst sW (t ≫ sZ) ≫ sW) = (U.ι ≫ pullback.snd sW (t ≫ sZ) ≫ t) ≫ sZ := by
    rw [hcond]; simp only [Category.assoc]
  have e1 := hL _ _ (hcd i (pullback.fst w t ≫ (w ≫ sZ)) (k - q)
    (chowGroupCongr C (Category.comp_id _).symm (k - q) (c'.cap t k α)))
  have e0 := congrArg (chowGroupCongr C
    (show U.ι ≫ pullback.fst sW (t ≫ sZ) ≫ sW = (U.ι ≫ pullback.snd sW (t ≫ sZ) ≫ t) ≫ sZ
      from hv) (k - p))
    (hcd i (t ≫ sZ) k (chowGroupCongr C (Category.comp_id (t ≫ sZ)).symm k α))
  rw [chowGroupCongr_chowGroupRestrict C _ _ _ _ _ hv,
    chowGroupCongr_chowGroupRestrict C _ _ _ _ _ hv,
    ← chowGroupRestrict_chowGroupCongr C _ _ _ _ hv (Category.assoc _ _ _).symm hcond,
    ← chowGroupRestrict_chowGroupCongr C _ _ _ _ hv (Category.assoc _ _ _).symm hcond] at e0
  have e2 := hR _ _ e0
  exact e1.trans ((congrArg _ (hd i t k α)).trans e2.symm)

end Localization

/-! ### Classes central over the base -/

/-- A class `c ∈ A^p(X ⟶ S)` towards the base is *central over the base* when it commutes, in
the sense of `Stacks.Chow.BivariantCommuteOverBase`, with every bivariant class
`c' ∈ A^q(Y ⟶ Z)` of every morphism `Y ⟶ Z` of schemes locally of finite type over the base.
This is the conclusion of Stacks 0FC6 for `c`. -/
def IsCentralOverBase (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p) : Prop :=
  ∀ ⦃Y Z : Scheme.{u}⦄ (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (w : Y ⟶ Z)
    [LocallyOfFiniteType w] (q : ℤ) (c' : BivariantClass C G (w ≫ sZ) sZ w rfl q),
    BivariantCommuteOverBase C G sX sZ w p q c c'

/-- The classes central over the base form a subgroup of `A^p(X ⟶ S)`. -/
def centralOverBaseSubgroup (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ) :
    AddSubgroup (BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p) where
  carrier := {c | IsCentralOverBase C G sX p c}
  zero_mem' := fun _ _ sZ _ w _ q c' ↦ bivariantCommuteOverBase_zero C G sX sZ w p q c'
  add_mem' := fun hc hd _ _ sZ _ w _ q c' ↦
    bivariantCommuteOverBase_add C G sX sZ w p q c' (hc sZ w q c') (hd sZ w q c')
  neg_mem' := fun hc _ _ sZ _ w _ q c' ↦
    bivariantCommuteOverBase_neg C G sX sZ w p q c' (hc sZ w q c')

/-- A class lies in `Stacks.Chow.centralOverBaseSubgroup` exactly when it is central over the
base. -/
theorem mem_centralOverBaseSubgroup_iff (C : ChowSituation.{u}) (G : GysinSystem C)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    c ∈ centralOverBaseSubgroup C G sX p ↔ IsCentralOverBase C G sX p c :=
  Iff.rfl

/-- Every class built by the operations of chapter 42 is central over the base, at the Gysin
system `Stacks.Chow.gysinSystemOfInvertible`. -/
theorem IsChowOperationClassOverBase.isCentralOverBase {C : ChowSituation.{u}} {X : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {p : ℤ}
    {c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p}
    (hc : IsChowOperationClassOverBase C (gysinSystemOfInvertible C) sX p c) :
    IsCentralOverBase C (gysinSystemOfInvertible C) sX p c :=
  fun _ _ sZ _ w _ q c' ↦
    bivariantCommuteOverBase_of_isChowOperationClassOverBase_ofInvertible C sZ w q hc c'

/-- A class characterized by the rule of Stacks 0B78 (`Stacks.Chow.IsBivariantFlatPullback`)
for a structure morphism `X ⟶ S` flat of relative dimension `r` is a flat-pullback class towards
the base in the sense of `Stacks.Chow.IsFlatPullbackOverBase`. -/
theorem isFlatPullbackOverBase_flatPullbackBivariantClass (C : ChowSituation.{u})
    (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [Flat sX]
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension sX r)
    (c : BivariantClass C G sX (𝟙 C.S) sX (Category.comp_id sX) (-(r : ℤ)))
    (hc : IsBivariantFlatPullback C G sX (𝟙 C.S) sX (Category.comp_id sX) r hr
      (flatPullbackDescends C) c) :
    IsFlatPullbackOverBase C G sX r (-(r : ℤ)) c := by
  intro U u _ sU' _ _ _ hsU' hr' k hfac α
  refine (hc.cap_heq u k _).trans ?_
  exact flatPullbackChow_heq_congr_base C (by rw [← hsU', ← pullback.condition])
    (Category.comp_id u) rfl _ _ rfl _ _ rfl _ _ _ _ (chowGroupCongr_heq C _ k α)

/-- The composite `π^* ∘ b ∈ A^{p-r}(X ⟶ S)` of a class `b ∈ A^p(D ⟶ S)` with the flat-pullback
class of a flat `π : X ⟶ D` of relative dimension `r` exists in the sense of
`Stacks.Chow.IsFlatPullbackAfter`: it is the composite of Stacks 0B75, and capping with it is cap
with `b` followed by flat pullback along `X ×_S U ⟶ D ×_S U`, by the isomorphism case of
Stacks 02RG. -/
theorem exists_isFlatPullbackAfter (C : ChowSituation.{u}) {X D : Scheme.{u}} (sD : D ⟶ C.S)
    [LocallyOfFiniteType sD] (π : X ⟶ D) [LocallyOfFiniteType π] [Flat π] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension π r) (p : ℤ)
    (b : BivariantClass C (gysinSystemOfInvertible C) sD (𝟙 C.S) sD (Category.comp_id sD) p) :
    ∃ c : BivariantClass C (gysinSystemOfInvertible C) (π ≫ sD) (𝟙 C.S) (π ≫ sD)
        (Category.comp_id (π ≫ sD)) (p - (r : ℤ)),
      IsFlatPullbackAfter C (gysinSystemOfInvertible C) sD π r p b c := by
  set φ := flatPullbackBivariantClassOfInvertible C (π ≫ sD) sD π rfl r hr with hφ
  set κ := bivariantCompositeOfInvertible C (π ≫ sD) sD (𝟙 C.S) π sD rfl (Category.comp_id sD)
    (-(r : ℤ)) p φ b with hκ
  refine ⟨BivariantClass.copy C _ (π ≫ sD) (𝟙 C.S) rfl _ (Category.comp_id (π ≫ sD))
    (by ring) κ, ?_⟩
  intro U u _ _ _ hr' k α
  refine (BivariantClass.copy_cap C _ _ _ _ _ _ _ κ u k α).trans ?_
  refine (isBivariantClassComposition_bivariantCompositeOfInvertible C (π ≫ sD) sD (𝟙 C.S) π sD
    rfl (Category.comp_id sD) (-(r : ℤ)) p φ b u k α).trans ?_
  rw [bivariantCompositeCap_apply, properChowPushforward_eq_chowPushforwardOfIso]
  have hφcap := IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C (π ≫ sD) sD π rfl
      r hr) (pullback.fst sD u) (k - p) (b.cap u k α)
  have hsq : pullback.snd π (pullback.fst sD u) ≫ 𝟙 _ =
      (pullbackRightPullbackFstIso sD u π).hom ≫ bivariantPushforwardBaseChange π sD u := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.comp_id, Category.assoc, bivariantPushforwardBaseChange,
        pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst_assoc]
      exact pullback.condition.symm
    · simp [bivariantPushforwardBaseChange]
  have hpf := flatPullbackChow_chowPushforwardOfIso C (pullback.fst sD u ≫ sD)
    (pullback.fst π (pullback.fst sD u) ≫ (π ≫ sD)) (pullback.fst sD u ≫ sD)
    (pullback.fst (π ≫ sD) u ≫ (π ≫ sD)) (𝟙 _) (Category.id_comp _)
    (pullbackRightPullbackFstIso sD u π).hom
    (pullbackRightPullbackFstIso_hom_comp_fst_comp (π ≫ sD) π sD u)
    (pullback.snd π (pullback.fst sD u)) (pullbackSnd_comp_structureMorphism rfl _)
    (bivariantPushforwardBaseChange π sD u)
    (bivariantPushforwardBaseChange_comp_structure rfl sD u) hsq r
    (relativeDimension_pullbackSnd π hr _) hr' (k - p)
    (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) (b.cap u k α)
  rw [chowPushforwardOfIso_id] at hpf
  refine (chowPushforwardOfIso_heq (pullbackRightPullbackFstIso sD u π).hom
    (pullbackRightPullbackFstIso_hom_comp_fst_comp (π ≫ sD) π sD u)
    (pullbackRightPullbackFstIso_hom_comp_fst_comp (π ≫ sD) π sD u) rfl rfl (by ring)
    hφcap).trans ?_
  refine (heq_of_eq hpf.symm).trans ?_
  exact flatPullbackChow_heq_congr_base C rfl rfl rfl _ _ rfl _ _ rfl _ _ _ _ HEq.rfl

/-! ### The vertical generators towards the base -/

/-- **A closed point of a Dedekind base is an effective Cartier divisor.** If `s` is a closed
point of a base as in section 42.63 with a proper generalization, the reduced point `s` is an
effective Cartier divisor on the whole base: it is one on an integral neighbourhood, where it is
the zero scheme of a section of an invertible module, and its support lies in that
neighbourhood. -/
theorem IsDedekindChowBase.isEffectiveCartierDivisor_integralComponentAt {C : ChowSituation.{u}}
    (hS : IsDedekindChowBase C) {t s : C.S} (hclosed : IsClosed ({s} : Set C.S)) (hts : t ⤳ s)
    (hne : t ≠ s) : Stacks.Divisors.IsEffectiveCartierDivisor (integralComponentAt s) := by
  obtain ⟨V, hsV, L, hL, σ, hVint, hσ⟩ := hS.exists_isIntegral_zeroScheme_eq hts hne
  have htV : t ∈ V := hts.mem_open V.isOpen hsV
  refine isEffectiveCartierDivisor_of_comap_of_isOpenImmersion _ V.ι ?_ ?_
  · intro x hx
    have hx' : x ∈ ((integralComponentAt s).support : Set C.S) := hx
    rw [coe_support_integralComponentAt, hclosed.closure_eq, Set.mem_singleton_iff] at hx'
    subst hx'
    exact ⟨⟨x, hsV⟩, rfl⟩
  · have e : (integralComponentAt s).comap V.ι =
        integralComponentAt (⟨s, hsV⟩ : (V : Scheme.{u})) :=
      comap_integralComponentAt_of_isOpenImmersion V.ι ⟨s, hsV⟩
    rw [e, ← hσ]
    refine Stacks.Divisors.isEffectiveCartierDivisor_of_isLocallyPrincipal _ ?_
      (Stacks.Divisors.isLocallyPrincipal_zeroScheme _ _ _)
    intro hbot
    have h1 : (⟨t, htV⟩ : (V : Scheme.{u})) ∈
        ((Stacks.Divisors.zeroScheme (V : Scheme.{u}) L σ).support : Set (V : Scheme.{u})) := by
      rw [hbot, Scheme.IdealSheafData.support_bot]; trivial
    rw [hσ] at h1
    have h2 := specializes_iff_mem_closure.mpr ((coe_support_integralComponentAt _).le h1)
    have h3 : t ∈ closure ({s} : Set C.S) :=
      specializes_iff_mem_closure.mp (h2.map V.ι.continuous)
    rw [hclosed.closure_eq, Set.mem_singleton_iff] at h3
    exact hne h3

/-- **The vertical generators, towards the base.** Let `s` be a closed point of a base as in
section 42.63 with a proper generalization `t₀`, and let `U'` be integral and locally of finite
type over the base, lying over `s`, of delta-dimension `1 - p`. There is a class
`e ∈ A^p(U' ⟶ S)` built by the operations of chapter 42 which caps the fundamental class of every
integral open `V' ⊆ S` containing `s` and `t₀` to `[U' ×_S V']_{1-p}`. It is the class
`(p')^* ∘ c_s` of the proof of Stacks 0FC5: `c_s ∈ A^1(s ⟶ S)` is the Gysin class of Stacks 0B79
of the effective Cartier divisor `s ⊆ S` with its canonical section, and `(p')^*` is flat
pullback along `U' ⟶ s`, the reduced point `s` being the spectrum of a field. -/
theorem exists_isChowOperationClassOverBase_cap_eq_of_closedPoint {C : ChowSituation.{u}}
    (hS : IsDedekindChowBase C) {t₀ s : C.S} (hclosed : IsClosed ({s} : Set C.S))
    (hts : t₀ ⤳ s) (hne : t₀ ≠ s) {U' : Scheme.{u}} [IsIntegral U'] (sU' : U' ⟶ C.S)
    [LocallyOfFiniteType sU'] (hpt : ∀ w, sU'.base w = s) (p : ℤ)
    (hδ : relativeDimension C.dimensionFunction sU' (genericPoint U') = 1 - p) :
    ∃ e : BivariantClass C (gysinSystemOfInvertible C) sU' (𝟙 C.S) sU' (Category.comp_id sU') p,
      IsChowOperationClassOverBase C (gysinSystemOfInvertible C) sU' p e ∧
      ∀ {V' : Scheme.{u}} (m : V' ⟶ C.S) [IsOpenImmersion m] [LocallyOfFiniteType m]
        [IsIntegral V'] (x x' : V') (_hx : m.base x = s) (_hx' : m.base x' = t₀),
        e.cap m 1 (fundamentalChowClass C (m ≫ 𝟙 C.S) 1) =
          fundamentalChowClass C (pullback.fst sU' m ≫ sU') (1 - p) := by
  have _ := hS.isEffectiveCartierDivisor_integralComponentAt hclosed hts hne
  set L := Stacks.Divisors.divisorSheaf (integralComponentAt s) with hLdef
  set σ := Stacks.Divisors.divisorSheafGlobalSection (integralComponentAt s) with hσdef
  have hσ : Stacks.Divisors.zeroScheme C.S L σ = integralComponentAt s :=
    Stacks.Divisors.zeroScheme_canonicalSection _
  set D := Stacks.Divisors.zeroScheme C.S L σ with hD
  have hsupp : (D.support : Set C.S) = {s} := by
    rw [hσ, coe_support_integralComponentAt, hclosed.closure_eq]
  have hDpt : ∀ z : D.subscheme, D.subschemeι.base z = s := by
    intro z
    have hz : D.subschemeι.base z ∈ (D.support : Set C.S) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    rwa [hsupp, Set.mem_singleton_iff] at hz
  have _ : IsIntegral D.subscheme := by rw [hσ]; exact isIntegral_integralComponentAt s
  have _ : Subsingleton D.subscheme :=
    ⟨fun a b ↦ D.subschemeι.isClosedEmbedding.injective (by rw [hDpt a, hDpt b])⟩
  have hδs : C.dimensionFunction s = 0 := hS.2.1 _ hclosed
  -- the lift of `sU'` to the reduced point `D`
  have hker : D.subschemeι.ker ≤ sU'.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range, hσ]
    refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
    rw [← SetLike.coe_subset_coe, TopologicalSpace.Closeds.coe_closure,
      TopologicalSpace.Closeds.coe_closure]
    refine closure_mono ?_
    rintro _ ⟨w, rfl⟩
    exact hpt w
  set h : U' ⟶ D.subscheme := IsClosedImmersion.lift D.subschemeι sU' hker with hhdef
  have hh : h ≫ D.subschemeι = sU' := IsClosedImmersion.lift_fac _ _ _
  have _ : Flat h := inferInstance
  have _ : LocallyOfFiniteType (h ≫ D.subschemeι) := by rw [hh]; infer_instance
  have _ : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h D.subschemeι
  have hnn : 0 ≤ 1 - p := by
    rw [← hδ]
    change 0 ≤ C.dimensionFunction (sU'.base (genericPoint U')) +
      (Cardinal.toNat (residueTrdeg sU' (genericPoint U')) : ℤ)
    rw [hpt, hδs]
    omega
  obtain ⟨r, hr1⟩ : ∃ r : ℕ, (r : ℤ) = 1 - p := ⟨(1 - p).toNat, Int.toNat_of_nonneg hnn⟩
  have hr : AlgebraicGeometry.RelativeDimension h r := by
    have hh' : h ≫ (D.subschemeι ≫ 𝟙 C.S) = sU' := by rw [Category.comp_id, hh]
    refine relativeDimension_of_flat_of_coheight C h (D.subschemeι ≫ 𝟙 C.S) r fun w ↦ ?_
    have hmax : Order.coheight (h.base w) = 0 :=
      Order.coheight_eq_zero.mpr fun b _ ↦ le_of_eq (Subsingleton.elim _ _)
    rw [hmax, zero_add, hh', hδ, relativeDimension_comp_closedImmersion, relativeDimension_id,
      hDpt]
    change (r : ℕ∞) = ((1 - p - C.dimensionFunction s).toNat : ℕ∞)
    rw [hδs, sub_zero, ← hr1, Int.toNat_natCast]
  clear_value h
  clear hhdef
  subst hh
  obtain rfl : p = 1 - (r : ℤ) := by omega
  obtain ⟨b, hb⟩ := exists_isGysinOverBase C L σ
  obtain ⟨e, he⟩ := exists_isFlatPullbackAfter C D.subschemeι h r hr 1 b
  refine ⟨e, .flatComp (gysinTripleInclusion L σ) h r hr 1 b (.gysin L σ b hb) e he, ?_⟩
  intro V' m _ _ _ x x' hx hx'
  have sq := isPullback_bivariantPushforwardBaseChange h D.subschemeι m
  have _ : LocallyOfFiniteType (bivariantPushforwardBaseChange h D.subschemeι m) :=
    MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
  have _ : Flat (bivariantPushforwardBaseChange h D.subschemeι m) :=
    MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
  have hrm := AlgebraicGeometry.RelativeDimension.of_isPullback sq hr
  have hgen1 : genericPoint V' ⤳ x := (genericPoint_spec V').specializes (Set.mem_univ _)
  have hgen2 : genericPoint V' ⤳ x' := (genericPoint_spec V').specializes (Set.mem_univ _)
  -- the Gysin step
  have _ := Stacks.Divisors.pullback_isInvertible m L
  have hδV : relativeDimension C.dimensionFunction (m ≫ 𝟙 C.S) (genericPoint V') =
      (1 - 1) + 1 := by
    rw [relativeDimension_comp_isOpenImmersion, relativeDimension_id]
    refine (hS.2.2 _ fun hc ↦ ?_).trans (by ring)
    have h1 := specializes_iff_mem_closure.mp (hgen1.map m.continuous)
    have h2 := specializes_iff_mem_closure.mp (hgen2.map m.continuous)
    rw [hc.closure_eq, Set.mem_singleton_iff, hx] at h1
    rw [hc.closure_eq, Set.mem_singleton_iff, hx'] at h2
    exact hne (h2.trans h1.symm)
  have hD'ne : ¬ Stacks.Divisors.zeroScheme V' ((Scheme.Modules.pullback m).obj L)
      (pullbackGlobalSections m L σ) ≤ ⊥ := by
    intro hle
    have h1 := Scheme.IdealSheafData.support_antitone hle
    have h2 : x' ∈ ((Stacks.Divisors.zeroScheme V' ((Scheme.Modules.pullback m).obj L)
        (pullbackGlobalSections m L σ)).support : Set V') :=
      h1 (by rw [Scheme.IdealSheafData.support_bot]; trivial)
    rw [Stacks.Divisors.zeroScheme_pullback, coe_support_comap, Set.mem_preimage, ← hD, hsupp,
      Set.mem_singleton_iff] at h2
    exact hne (hx'.symm.trans h2)
  have h4 : b.cap m 1 (fundamentalChowClass C (m ≫ 𝟙 C.S) 1) ≍
      fundamentalChowClass C (pullback.fst (gysinTripleInclusion L σ) m ≫
        (gysinTripleInclusion L σ ≫ 𝟙 C.S)) (1 - 1) := by
    refine (hb m 1 _).trans (heq_of_eq ?_)
    rw [gysinBivariantCap_apply, chowGroupDegreeEquiv_fundamentalChowClass,
      gysinSystemOfInvertible_onChow_fundamentalChowClass_of_isIntegral C _ _ _ (1 - 1) hδV hD'ne,
      chowPushforwardOfIso_fundamentalChowClass]
  have key : fundamentalChowClass C (pullback.fst D.subschemeι m ≫ (D.subschemeι ≫ 𝟙 C.S))
      (1 - 1) ≍ fundamentalChowClass C (pullback.fst D.subschemeι m ≫ D.subschemeι) (1 - 1) :=
    fundamentalChowClass_heq_of_hom_eq C (by rw [Category.comp_id]) _
  -- the flat step
  have hdimD : schemeDeltaDimension C (pullback.fst D.subschemeι m ≫ D.subschemeι) ≤
      ((1 - 1 : ℤ) : EInt) := by
    rw [schemeDeltaDimension_congr C (h := pullback.snd D.subschemeι m ≫ (m ≫ 𝟙 C.S))
      (by rw [Category.comp_id, pullback.condition])]
    refine schemeDeltaDimension_le_of_forall_relativeDimension_le C _ _ fun w ↦ ?_
    rw [relativeDimension_comp_isOpenImmersion, relativeDimension_id,
      ← Scheme.Hom.comp_apply (pullback.snd D.subschemeι m) m, ← pullback.condition,
      Scheme.Hom.comp_apply, hDpt]
    rw [hδs]
    norm_num
  have h5 := flatPullbackChow_fundamentalChowClass C
    (pullback.fst (h ≫ D.subschemeι) m ≫ (h ≫ D.subschemeι))
    (pullback.fst D.subschemeι m ≫ D.subschemeι) (bivariantPushforwardBaseChange h D.subschemeι m)
    (bivariantPushforwardBaseChange_comp_structure rfl D.subschemeι m) r hrm (1 - 1)
    (flatPullbackDescends C _ _ _ _ _ _ _) hdimD
  refine eq_of_heq ((he m hrm 1 _).trans ?_)
  refine ((flatPullbackChow_heq_congr_base C rfl rfl rfl _ _ rfl _ _ rfl _ _ _ _
    (h4.trans key)).trans (heq_of_eq h5)).trans (fundamentalChowClass_heq C _ (by ring))

end Stacks.Chow

end
