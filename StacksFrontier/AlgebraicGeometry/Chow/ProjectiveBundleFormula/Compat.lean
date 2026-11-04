module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerChow
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapPullback
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Proper

/-!
# The map of the projective space bundle formula under change of base

Let `π : P ⟶ X` be flat of relative dimension `n` and `L` an invertible module on `P`. This file
proves that the summands `c₁(L)^i ∩ π^*(-)` of the map of [Stacks, Tag 02TX], and the operations
`π_*(c₁(L)^s ∩ π^*(-))` of [Stacks, Tag 02TW], are compatible with the two changes of base the
proofs of those tags use: restriction to a closed subscheme `W` of `X`, along which they commute
with pushforward, and restriction to an open subscheme `V` of `X`, along which they commute with
restriction of classes.

## Main results

* `Stacks.Chow.properChowPushforward_bundlePullback_comap` — Stacks 02RG for the closed base
  change, on Chow groups.
* `Stacks.Chow.properChowPushforward_capPow` — Stacks 02SU for a proper morphism, for powers of
  the cap.
* `Stacks.Chow.properChowPushforward_bundleTerm_comap`,
  `Stacks.Chow.properChowPushforward_bundleProjection_comap` — the summands and the operation of
  Stacks 02TW commute with pushforward along the closed base change.

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Chow

/-! ### Closed immersions and powers of the cap -/

/-- **Stacks 02SU for powers of the cap.** Pushforward along a proper morphism `i : D ⟶ P` carries
`c₁(i^*L)^s ∩ -` to `c₁(L)^s ∩ -`. -/
theorem properChowPushforward_capPow (C : ChowSituation.{u}) {D P : Scheme.{u}}
    (sD : D ⟶ C.S) [LocallyOfFiniteType sD] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (i : D ⟶ P) [IsProper i] (hi : i ≫ sP = sD) (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible D.sheaf.obj D.ringCatSheaf.property
      ((Scheme.Modules.pullback i).obj L)]
    (s : ℕ) (a m : ℤ) (h : a = m + s) (x : chowGroup C sD a) :
    properChowPushforward C sD sP i hi m
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sD sP i hi m)
        (capPow C sD (invCap C sD ((Scheme.Modules.pullback i).obj L)) s a m h x) =
      capPow C sP (invCap C sP L) s a m h
        (properChowPushforward C sD sP i hi a
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sD sP i hi a) x) :=
  capPow_comm C sP (invCap C sP L) sD (invCap C sD ((Scheme.Modules.pullback i).obj L))
    (fun d ↦ properChowPushforward C sD sP i hi d
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sD sP i hi d))
    (fun d x ↦ properChowPushforward_invCap_capOnChow C sD sP i hi d L x) s a m h x

/-! ### The closed base change -/

section Closed

variable (C : ChowSituation.{u}) {P X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n)
  (W : X.IdealSheafData)

/-- **Stacks 02RG for the closed base change, on Chow groups.** For `W ⊆ X` closed, with
`π_W : π^{-1}(W) ⟶ W` the restriction of `π` and `j : π^{-1}(W) ⟶ P` the closed immersion,
`j_* π_W^* β = π^*(i_W)_* β`. -/
theorem properChowPushforward_bundlePullback_comap (k : ℤ)
    (β : chowGroup C (W.subschemeι ≫ sX) k) :
    letI := locallyOfFiniteType_comapRestrict W π
    letI := flat_comapRestrict W π
    properChowPushforward C ((W.comap π).subschemeι ≫ sP) sP (W.comap π).subschemeι rfl (k + n)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sP _ rfl (k + n))
        (bundlePullback C (W.subschemeι ≫ sX) ((W.comap π).subschemeι ≫ sP) (comapRestrict W π)
          (comapRestrict_comp_base C sP sX π hsP W) n (relativeDimension_comapRestrict W π hπ) k
          β) =
      bundlePullback C sX sP π hsP n hπ k
        (properChowPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl k) β) := by
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ β
  rw [bundlePullback_mk, properChowPushforward_mk, properChowPushforward_mk, bundlePullback_mk]
  exact congrArg _ (flatPullback_properPushforward_comap C sP sX π hsP n hπ k W b).symm

variable (L : P.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]

/-- **The summands of the map of Stacks 02TX commute with the closed base change.** -/
theorem properChowPushforward_bundleTerm_comap (k : ℤ) (i : ℕ)
    (y : chowGroup C (W.subschemeι ≫ sX) (k + i)) :
    letI := locallyOfFiniteType_comapRestrict W π
    letI := flat_comapRestrict W π
    letI := isInvertible_presheaf_modulePullback L (W.comap π).subschemeι
    properChowPushforward C ((W.comap π).subschemeι ≫ sP) sP (W.comap π).subschemeι rfl (k + n)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sP _ rfl (k + n))
        (bundleTerm C (W.subschemeι ≫ sX) ((W.comap π).subschemeι ≫ sP) (comapRestrict W π)
          (comapRestrict_comp_base C sP sX π hsP W) n (relativeDimension_comapRestrict W π hπ)
          (invCap C _ ((Scheme.Modules.pullback (W.comap π).subschemeι).obj L)) k i y) =
      bundleTerm C sX sP π hsP n hπ (invCap C sP L) k i
        (properChowPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl (k + i)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl (k + i))
          y) := by
  simp only [bundleTerm, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [properChowPushforward_capPow, properChowPushforward_bundlePullback_comap]

/-- **The operation of Stacks 02TW commutes with the closed base change.** -/
theorem properChowPushforward_bundleProjection_comap [IsProper π] (s : ℕ) (k m : ℤ)
    (h : k + n = m + s) (y : chowGroup C (W.subschemeι ≫ sX) k) :
    letI := locallyOfFiniteType_comapRestrict W π
    letI := flat_comapRestrict W π
    letI := isInvertible_presheaf_modulePullback L (W.comap π).subschemeι
    letI : IsProper (comapRestrict W π) :=
      MorphismProperty.of_isPullback (isPullback_comapRestrict W π) inferInstance
    properChowPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl m
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl m)
        (bundleProjection C (W.subschemeι ≫ sX) ((W.comap π).subschemeι ≫ sP)
          (comapRestrict W π) (comapRestrict_comp_base C sP sX π hsP W) n
          (relativeDimension_comapRestrict W π hπ)
          (invCap C _ ((Scheme.Modules.pullback (W.comap π).subschemeι).obj L)) s k m h y) =
      bundleProjection C sX sP π hsP n hπ (invCap C sP L) s k m h
        (properChowPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl k) y) := by
  simp only [bundleProjection, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [← properChowPushforward_bundlePullback_comap C sX sP π hsP n hπ W k y,
    ← properChowPushforward_capPow,
    ← AddMonoidHom.comp_apply (properChowPushforward C _ sX _ _ m _),
    ← AddMonoidHom.comp_apply (properChowPushforward C _ sX π _ m _), properChowPushforward_comp,
    properChowPushforward_comp]
  congr 2
  exact comapRestrict_subschemeι W π

/-- **The map of Stacks 02TX commutes with the closed base change.** -/
theorem properChowPushforward_bundleMap_comap (k : ℤ)
    (β : ∀ i : Fin (n + 1), chowGroup C (W.subschemeι ≫ sX) (k + (i : ℕ))) :
    letI := locallyOfFiniteType_comapRestrict W π
    letI := flat_comapRestrict W π
    letI := isInvertible_presheaf_modulePullback L (W.comap π).subschemeι
    properChowPushforward C ((W.comap π).subschemeι ≫ sP) sP (W.comap π).subschemeι rfl (k + n)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sP _ rfl (k + n))
        (bundleMap C (W.subschemeι ≫ sX) ((W.comap π).subschemeι ≫ sP) (comapRestrict W π)
          (comapRestrict_comp_base C sP sX π hsP W) n (relativeDimension_comapRestrict W π hπ)
          (invCap C _ ((Scheme.Modules.pullback (W.comap π).subschemeι).obj L)) k β) =
      bundleMap C sX sP π hsP n hπ (invCap C sP L) k
        (fun i ↦ properChowPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl (k + (i : ℕ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl _)
          (β i)) := by
  rw [bundleMap_apply, bundleMap_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ properChowPushforward_bundleTerm_comap C sX sP π hsP n hπ
    W L k i (β i)

end Closed

/-! ### Restriction to an open subscheme -/

section Open

/-- **Stacks 02SS for an open immersion.** Restriction of Chow classes to an open subscheme
commutes with the cap product of an invertible module. -/
theorem chowGroupRestrict_invCap (C : ChowSituation.{u}) {O P : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sO : O ⟶ C.S) [LocallyOfFiniteType sO]
    (j : O ⟶ P) [IsOpenImmersion j] (hj : j ≫ sP = sO) (L : P.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible O.sheaf.obj O.ringCatSheaf.property
      ((Scheme.Modules.pullback j).obj L)]
    (k : ℤ) (x : chowGroup C sP (k + 1)) :
    chowGroupRestrict C sP sO j hj k ((invCap C sP L).capOnChow C sP k x) =
      (invCap C sO ((Scheme.Modules.pullback j).obj L)).capOnChow C sO k
        (chowGroupRestrict C sP sO j hj (k + 1) x) := by
  subst hj
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  rw [invCap_capOnChow_mk, chowGroupRestrict_mk, invCap_capOnChow_mk]
  have h02SS := flatPullbackChow_firstChernClassCapOfInvertible_of_invertible C sP j 0
    (relativeDimension_of_isOpenImmersion j) k L
    (flatPullbackFactorsThroughRationalEquivalence_general C _ sP j rfl 0 _ k) α
  have hk : k + ((0 : ℕ) : ℤ) = k := by simp
  have hcast := congrArg (fun z : chowGroup C (j ≫ sP) (k + ((0 : ℕ) : ℤ)) ↦
    (hk ▸ z : chowGroup C (j ≫ sP) k)) h02SS
  rw [cast_flatPullbackChow_eq_chowGroupRestrict] at hcast
  rw [hcast]
  have hgen : ∀ {a b : ℤ} (e : a = b) (c : CycleGroup C (j ≫ sP) (a + 1)),
      (e ▸ firstChernClassCapOfInvertible C (j ≫ sP) a ((Scheme.Modules.pullback j).obj L) c :
        chowGroup C (j ≫ sP) b) =
      firstChernClassCapOfInvertible C (j ≫ sP) b ((Scheme.Modules.pullback j).obj L)
        ((show a + 1 = b + 1 by rw [e]) ▸ c) := by
    intro a b e c; subst e; rfl
  rw [hgen hk]
  congr 1
  rw [← cast_flatPullback_eq_cycleGroupRestrict C sP (j ≫ sP) j rfl (k + 1) (by simp) α]
  refine Subtype.ext ?_
  simp only [val_cycleGroup_cast]

variable (C : ChowSituation.{u}) {P X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n) (V : X.Opens)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sP] [LocallyOfFiniteType π] [Flat π] in
/-- The restriction of `π` over an open `V` of the base, as a morphism over the base situation. -/
theorem morphismRestrict_comp_base (hsP : π ≫ sX = sP) (V : X.Opens) :
    (π ∣_ V) ≫ (V.ι ≫ sX) = (π ⁻¹ᵁ V).ι ≫ sP := by
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hsP]

omit [Flat π] in
/-- The restriction of `π` over an open has the relative dimension of `π`. -/
theorem relativeDimension_morphismRestrict (n : ℕ)
    (hπ : AlgebraicGeometry.RelativeDimension π n) (V : X.Opens) :
    AlgebraicGeometry.RelativeDimension (π ∣_ V) n :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (isPullback_morphismRestrict π V).flip hπ

/-- **Restriction to an open of the base commutes with the flat pullback along `π`.** -/
theorem chowGroupRestrict_bundlePullback_morphismRestrict (k : ℤ) (β : chowGroup C sX k) :
    chowGroupRestrict C sP ((π ⁻¹ᵁ V).ι ≫ sP) (π ⁻¹ᵁ V).ι rfl (k + n)
        (bundlePullback C sX sP π hsP n hπ k β) =
      bundlePullback C (V.ι ≫ sX) ((π ⁻¹ᵁ V).ι ≫ sP) (π ∣_ V)
        (morphismRestrict_comp_base C sX sP π hsP V) n
        (relativeDimension_morphismRestrict π n hπ V) k
        (chowGroupRestrict C sX (V.ι ≫ sX) V.ι rfl k β) := by
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ β
  rw [bundlePullback_mk, chowGroupRestrict_mk, chowGroupRestrict_mk, bundlePullback_mk]
  exact congrArg _ (cycleGroupRestrict_flatPullback C sP sX _ _ π hsP n hπ (π ⁻¹ᵁ V).ι rfl V.ι
    rfl (π ∣_ V) (morphismRestrict_comp_base C sX sP π hsP V) (morphismRestrict_ι π V).symm
    (relativeDimension_morphismRestrict π n hπ V) k b)

omit [LocallyOfFiniteType π] [Flat π] in
/-- **Restriction to an open of the base commutes with pushforward along `π`.** -/
theorem chowGroupRestrict_properChowPushforward_morphismRestrict [IsProper π] (k : ℤ)
    (x : chowGroup C sP k) :
    letI : IsProper (π ∣_ V) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict π V).flip
      inferInstance
    chowGroupRestrict C sX (V.ι ≫ sX) V.ι rfl k
        (properChowPushforward C sP sX π hsP k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sX π hsP k) x) =
      properChowPushforward C ((π ⁻¹ᵁ V).ι ≫ sP) (V.ι ≫ sX) (π ∣_ V)
        (morphismRestrict_comp_base C sX sP π hsP V) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ _ k)
        (chowGroupRestrict C sP ((π ⁻¹ᵁ V).ι ≫ sP) (π ⁻¹ᵁ V).ι rfl k x) := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  rw [properChowPushforward_mk, chowGroupRestrict_mk, chowGroupRestrict_mk,
    properChowPushforward_mk]
  exact congrArg _ (cycleGroupRestrict_properPushforward C sP sX _ _ π hsP (π ⁻¹ᵁ V).ι rfl V.ι
    rfl (π ∣_ V) (morphismRestrict_comp_base C sX sP π hsP V)
    (isPullback_morphismRestrict π V).flip k c)

variable (L : P.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]

/-- **Restriction to an open commutes with the powers of the cap.** -/
theorem chowGroupRestrict_capPow (O : P.Opens)
    [AlgebraicGeometry.SheafOfModules.IsInvertible O.toScheme.sheaf.obj
      O.toScheme.ringCatSheaf.property ((Scheme.Modules.pullback O.ι).obj L)]
    (s : ℕ) (a m : ℤ) (h : a = m + s) (x : chowGroup C sP a) :
    chowGroupRestrict C sP (O.ι ≫ sP) O.ι rfl m (capPow C sP (invCap C sP L) s a m h x) =
      capPow C (O.ι ≫ sP) (invCap C (O.ι ≫ sP) ((Scheme.Modules.pullback O.ι).obj L)) s a m h
        (chowGroupRestrict C sP (O.ι ≫ sP) O.ι rfl a x) :=
  capPow_comm C (O.ι ≫ sP) (invCap C (O.ι ≫ sP) ((Scheme.Modules.pullback O.ι).obj L)) sP
    (invCap C sP L) (fun d ↦ chowGroupRestrict C sP (O.ι ≫ sP) O.ι rfl d)
    (fun d x ↦ chowGroupRestrict_invCap C sP (O.ι ≫ sP) O.ι rfl L d x) s a m h x

/-- **The summands of the map of Stacks 02TX commute with restriction to an open of the
base.** -/
theorem chowGroupRestrict_bundleTerm (k : ℤ) (i : ℕ) (y : chowGroup C sX (k + i)) :
    letI := isInvertible_presheaf_modulePullback L (π ⁻¹ᵁ V).ι
    chowGroupRestrict C sP ((π ⁻¹ᵁ V).ι ≫ sP) (π ⁻¹ᵁ V).ι rfl (k + n)
        (bundleTerm C sX sP π hsP n hπ (invCap C sP L) k i y) =
      bundleTerm C (V.ι ≫ sX) ((π ⁻¹ᵁ V).ι ≫ sP) (π ∣_ V)
        (morphismRestrict_comp_base C sX sP π hsP V) n
        (relativeDimension_morphismRestrict π n hπ V)
        (invCap C _ ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)) k i
        (chowGroupRestrict C sX (V.ι ≫ sX) V.ι rfl (k + i) y) := by
  simp only [bundleTerm, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [chowGroupRestrict_capPow, chowGroupRestrict_bundlePullback_morphismRestrict]

/-- **The operation of Stacks 02TW commutes with restriction to an open of the base.** -/
theorem chowGroupRestrict_bundleProjection [IsProper π] (s : ℕ) (k m : ℤ) (h : k + n = m + s)
    (y : chowGroup C sX k) :
    letI := isInvertible_presheaf_modulePullback L (π ⁻¹ᵁ V).ι
    letI : IsProper (π ∣_ V) :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict π V).flip
      inferInstance
    chowGroupRestrict C sX (V.ι ≫ sX) V.ι rfl m
        (bundleProjection C sX sP π hsP n hπ (invCap C sP L) s k m h y) =
      bundleProjection C (V.ι ≫ sX) ((π ⁻¹ᵁ V).ι ≫ sP) (π ∣_ V)
        (morphismRestrict_comp_base C sX sP π hsP V) n
        (relativeDimension_morphismRestrict π n hπ V)
        (invCap C _ ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)) s k m h
        (chowGroupRestrict C sX (V.ι ≫ sX) V.ι rfl k y) := by
  simp only [bundleProjection, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [chowGroupRestrict_properChowPushforward_morphismRestrict, chowGroupRestrict_capPow,
    chowGroupRestrict_bundlePullback_morphismRestrict]

/-- **The map of Stacks 02TX commutes with restriction to an open of the base.** -/
theorem chowGroupRestrict_bundleMap (k : ℤ)
    (β : ∀ i : Fin (n + 1), chowGroup C sX (k + (i : ℕ))) :
    letI := isInvertible_presheaf_modulePullback L (π ⁻¹ᵁ V).ι
    chowGroupRestrict C sP ((π ⁻¹ᵁ V).ι ≫ sP) (π ⁻¹ᵁ V).ι rfl (k + n)
        (bundleMap C sX sP π hsP n hπ (invCap C sP L) k β) =
      bundleMap C (V.ι ≫ sX) ((π ⁻¹ᵁ V).ι ≫ sP) (π ∣_ V)
        (morphismRestrict_comp_base C sX sP π hsP V) n
        (relativeDimension_morphismRestrict π n hπ V)
        (invCap C _ ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)) k
        (fun i ↦ chowGroupRestrict C sX (V.ι ≫ sX) V.ι rfl (k + (i : ℕ)) (β i)) := by
  rw [bundleMap_apply, bundleMap_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ chowGroupRestrict_bundleTerm C sX sP π hsP n hπ V L k i
    (β i)

end Open

end Stacks.Chow

end
