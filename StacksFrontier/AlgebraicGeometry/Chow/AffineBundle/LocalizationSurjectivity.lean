module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.LocalizationSequence

/-!
# Surjectivity of flat pullback from an open subscheme and its closed complement

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S` which is flat of relative dimension `r`. Let
`V ⊆ Y` be an open subscheme and let `Z ⊆ Y` be a closed subscheme whose support is the
complement of `V`. If flat pullback is surjective in degree `k` along both base changes of `f`
— along `f ∣_ V : f^{-1}(V) ⟶ V` and along `f^{-1}(Z) ⟶ Z` — then it is surjective in degree
`k` along `f` itself.

## Main results

* `Stacks.Chow.chowGroupOpensRestrict_heq_flatPullbackChow` — restriction of Chow classes to an
  open subscheme is flat pullback along its inclusion.
* `Stacks.Chow.chowGroupOpensRestrict_flatPullbackChow` — **Stacks 02RD** across the square
  restricting a flat morphism to an open subscheme of its target.
* `Stacks.Chow.flatPullbackChow_chowPushforward_comap` — **Stacks 02RG on Chow groups** for the
  base change of a closed subscheme along a flat morphism.
* `Stacks.Chow.flatPullbackChow_surjective_of_opens_of_comap` — surjectivity of flat pullback
  from an open subscheme and its closed complement.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RC](https://stacks.math.columbia.edu/tag/02RC)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RX](https://stacks.math.columbia.edu/tag/02RX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Restriction to an open subscheme as a flat pullback, on Chow groups -/

/-- **Restriction of Chow classes to an open subscheme is flat pullback along its inclusion.**
The two maps land in the degrees `k + 0` and `k`, so the identity is a heterogeneous equality. -/
theorem chowGroupOpensRestrict_heq_flatPullbackChow (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (U : X.Opens) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C (U.ι ≫ sX) sX U.ι rfl 0
      (relativeDimension_opensι U) k) (α : chowGroup C sX k) :
    flatPullbackChow C (U.ι ≫ sX) sX U.ι rfl 0 (relativeDimension_opensι U) k hfac α ≍
      chowGroupOpensRestrictOfIsOpenImmersion C sX U k α := by
  have hdeg : k + ((0 : ℕ) : ℤ) = k := by simp
  refine (chowGroupDegreeEquiv_eq_iff_heq C (U.ι ≫ sX) hdeg _ _).mp ?_
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    refine chowGroupDegreeEquiv_mk_eq_mk_of_val C (U.ι ≫ sX) hdeg _ _ ?_
    exact (cycleGroupRestrict_eq_flatPullback C sX (U.ι ≫ sX) U.ι rfl
      (relativeDimension_opensι U) k a).symm

/-- Flat pullback is a congruence for heterogeneous equality of its argument along an equality
of degrees. -/
private theorem flatPullbackChow_heq_congr (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (x : A ⟶ B) [LocallyOfFiniteType x] [Flat x] (hx : x ≫ sB = sA) (n : ℕ)
    (hxn : AlgebraicGeometry.RelativeDimension x n) {j j' : ℤ} (hj : j = j')
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB x hx n hxn j)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sA sB x hx n hxn j')
    (a : chowGroup C sB j) (a' : chowGroup C sB j') (ha : a ≍ a') :
    flatPullbackChow C sA sB x hx n hxn j hfac a ≍
      flatPullbackChow C sA sB x hx n hxn j' hfac' a' := by
  subst hj
  rw [eq_of_heq ha]

/-- Relative dimension is inherited by the restriction of a morphism to an open subscheme of its
target. -/
theorem relativeDimension_morphismRestrict' {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (U : Y.Opens) (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) :
    AlgebraicGeometry.RelativeDimension (f ∣_ U) r :=
  (MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
    (P := AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension r) ⟨inferInstance, hf⟩).2

/-- **Stacks 02RD across the square restricting a flat morphism to an open subscheme of its
target.** Restricting the flat pullback of a Chow class to the inverse image of an open subscheme
`V ⊆ Y` is the flat pullback of its restriction to `V` along `f ∣_ V`. -/
theorem chowGroupOpensRestrict_flatPullbackChow (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [AlgebraicGeometry.Flat f] (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (V : Y.Opens) (β : chowGroup C sY k) :
    chowGroupOpensRestrictOfIsOpenImmersion C (f ≫ sY) (f ⁻¹ᵁ V) (k + (r : ℤ))
        (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k β) =
      flatPullbackChowOfRelativeDimension C ((f ⁻¹ᵁ V).ι ≫ f ≫ sY) (V.ι ≫ sY) (f ∣_ V)
        (by rw [← Category.assoc, morphismRestrict_ι, Category.assoc]) r
        (relativeDimension_morphismRestrict' f V r hf) k
        (chowGroupOpensRestrictOfIsOpenImmersion C sY V k β) := by
  have hdeg : k + ((0 : ℕ) : ℤ) = k := by simp
  have hcomp : f ∣_ V ≫ V.ι ≫ sY = (f ⁻¹ᵁ V).ι ≫ f ≫ sY := by
    simp
  have hsq := flatPullbackChow_comm_of_comp_eq C ((f ⁻¹ᵁ V).ι ≫ f ≫ sY) (f ≫ sY) (V.ι ≫ sY)
    sY (f ⁻¹ᵁ V).ι f (f ∣_ V) V.ι rfl rfl hcomp rfl
    0 r (relativeDimension_opensι (f ⁻¹ᵁ V)) hf
    (relativeDimension_morphismRestrict' f V r hf) (relativeDimension_opensι V)
    (morphismRestrict_ι f V).symm k
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) β
  have hleft := chowGroupOpensRestrict_heq_flatPullbackChow C (f ≫ sY) (f ⁻¹ᵁ V) (k + (r : ℤ))
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k β)
  have hright : flatPullbackChowOfRelativeDimension C ((f ⁻¹ᵁ V).ι ≫ f ≫ sY) (V.ι ≫ sY) (f ∣_ V)
        hcomp r (relativeDimension_morphismRestrict' f V r hf) (k + ((0 : ℕ) : ℤ))
        (flatPullbackChow C (V.ι ≫ sY) sY V.ι rfl 0 (relativeDimension_opensι V) k
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) β) ≍
      flatPullbackChowOfRelativeDimension C ((f ⁻¹ᵁ V).ι ≫ f ≫ sY) (V.ι ≫ sY) (f ∣_ V)
        hcomp r (relativeDimension_morphismRestrict' f V r hf) k
        (chowGroupOpensRestrictOfIsOpenImmersion C sY V k β) :=
    flatPullbackChow_heq_congr C _ _ (f ∣_ V) _ r _ hdeg _ _ _ _
      (chowGroupOpensRestrict_heq_flatPullbackChow C sY V k
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) β)
  exact eq_of_heq (hleft.symm.trans (hsq.trans hright))

/-! ### Stacks 02RG for the inverse image of a closed subscheme, on Chow groups -/

/-- **Stacks 02RG for a closed immersion base change, on Chow groups.** For `f : X' ⟶ X` flat of
relative dimension `r` and `W ⊆ X` a closed subscheme, flat pullback along `f` carries the
pushforward of a `k`-cycle class on `W` to the pushforward of its flat pullback along the
restriction `f^{-1}(W) ⟶ W`. -/
theorem flatPullbackChow_chowPushforward_comap (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (W : X.IdealSheafData)
    (γ : chowGroup C (W.subschemeι ≫ sX) k) :
    letI := locallyOfFiniteType_comapRestrict W f
    letI := flat_comapRestrict W f
    flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf k
        (chowPushforwardOfIsClosedImmersion C (W.subschemeι ≫ sX) sX W.subschemeι rfl k γ) =
      chowPushforwardOfIsClosedImmersion C ((W.comap f).subschemeι ≫ sX') sX'
        (W.comap f).subschemeι rfl (k + (r : ℤ))
        (flatPullbackChowOfRelativeDimension C ((W.comap f).subschemeι ≫ sX')
          (W.subschemeι ≫ sX) (comapRestrict W f)
          (comapRestrict_comp_base C sX' sX f hbase W) r
          (relativeDimension_comapRestrict W f hf) k γ) := by
  let _ := locallyOfFiniteType_comapRestrict W f
  let _ := flat_comapRestrict W f
  induction γ using QuotientAddGroup.induction_on with
  | H c =>
    exact congrArg (QuotientAddGroup.mk' (rationalEquivalences C sX' (k + (r : ℤ))))
      (flatPullback_properPushforward_comap C sX' sX f hbase r hf k W c)

/-! ### Surjectivity from an open subscheme and its closed complement -/

/-- **Surjectivity of flat pullback from an open subscheme and its closed complement.** Let
`f : X ⟶ Y` be flat of relative dimension `r` between schemes locally of finite type over the base
of chapter 42, let `V ⊆ Y` be an open subscheme and let `Z ⊆ Y` be a closed subscheme whose support
is the complement of `V`. If flat pullback in degree `k` is surjective along the restriction
`f ∣_ V : f^{-1}(V) ⟶ V` and along the base change `f^{-1}(Z) ⟶ Z`, then it is surjective along
`f`. -/
theorem flatPullbackChow_surjective_of_opens_of_comap (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (V : Y.Opens) (Z : Y.IdealSheafData)
    (hcomplement : Set.range Z.subschemeι.base = (Set.range V.ι.base)ᶜ)
    (hV : Function.Surjective (flatPullbackChowOfRelativeDimension C
      ((f ⁻¹ᵁ V).ι ≫ f ≫ sY) (V.ι ≫ sY) (f ∣_ V)
      (by rw [← Category.assoc, morphismRestrict_ι, Category.assoc]) r
      (relativeDimension_morphismRestrict' f V r hf) k))
    (hZ : Function.Surjective
      (letI := locallyOfFiniteType_comapRestrict Z f
       letI := flat_comapRestrict Z f
       flatPullbackChowOfRelativeDimension C ((Z.comap f).subschemeι ≫ f ≫ sY)
        (Z.subschemeι ≫ sY) (comapRestrict Z f)
        (comapRestrict_comp_base C (f ≫ sY) sY f rfl Z) r
        (relativeDimension_comapRestrict Z f hf) k)) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) := by
  let _ := locallyOfFiniteType_comapRestrict Z f
  let _ := flat_comapRestrict Z f
  have hcompl : Set.range (Z.comap f).subschemeι.base =
      (Set.range (f ⁻¹ᵁ V).ι.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
      Scheme.Opens.range_ι, TopologicalSpace.Closeds.coe_preimage]
    have hZV : (Z.support : Set Y) = ((V : Set Y))ᶜ := by
      rw [← Scheme.IdealSheafData.range_subschemeι, hcomplement, Scheme.Opens.range_ι]
    rw [hZV]
    rfl
  intro α
  obtain ⟨β₀, hβ₀⟩ := hV (chowGroupOpensRestrictOfIsOpenImmersion C (f ≫ sY) (f ⁻¹ᵁ V)
    (k + (r : ℤ)) α)
  obtain ⟨β, hβ⟩ := surjective_chowGroupOpensRestrictOfIsOpenImmersion C sY V k β₀
  have hzero : chowGroupOpensRestrictOfIsOpenImmersion C (f ≫ sY) (f ⁻¹ᵁ V) (k + (r : ℤ))
      (α - flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k β) = 0 := by
    rw [map_sub, chowGroupOpensRestrict_flatPullbackChow C sY f r hf k V β, hβ, hβ₀, sub_self]
  obtain ⟨a, ha⟩ := (exact_chowPushforward_chowGroupOpensRestrict C (f ≫ sY)
    ((Z.comap f).subschemeι ≫ f ≫ sY) (Z.comap f).subschemeι rfl (f ⁻¹ᵁ V) hcompl
    (k + (r : ℤ)) _).mp hzero
  obtain ⟨γ, hγ⟩ := hZ a
  refine ⟨β + chowPushforwardOfIsClosedImmersion C (Z.subschemeι ≫ sY) sY Z.subschemeι rfl k γ,
    ?_⟩
  rw [map_add, flatPullbackChow_chowPushforward_comap C (f ≫ sY) sY f rfl r hf k Z γ, hγ, ha]
  abel

end Stacks.Chow

end
