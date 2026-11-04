module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRule
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FlatCompatProof
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeHolds
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap

/-!
# The Chern class cap products commute with flat pullback

Let `h : T' ⟶ T` be flat of relative dimension `d` between schemes locally of finite type over
the base of chapter 42 and let `ℱ` be finite locally free of rank `r` on `T`. Then

  `c_j(h^*ℱ) ∩ h^*α = h^*(c_j(ℱ) ∩ α)`,  `0 ≤ j ≤ r`,

for the cap products `Stacks.Chow.GenuineChern.chernCap` of [Stacks, Tag 02U6]. This is
[Stacks, Tag 02U8]. The projective bundle of `h^*ℱ` is the base change of that of `ℱ`,
compatibly with the twists (`Stacks.Chow.GenuineChern.bundleBaseChangeHolds`), so pulling the
relation of Stacks 02U6 back along the flat morphism of bundles gives the relation for `h^*α`
([Stacks, Tag 02SS] for the twists), and the injectivity half of [Stacks, Tag 02TX] identifies
the two families. The argument is the one of `Stacks.Chow.GenuineChern.flatCompat_of`, read for
every member of the family rather than for `j = 1`.

## Main results

* `Stacks.Chow.GenuineChern.chernCap_flatPullback_heq` — Stacks 02U8 for the cap products, for a
  flat morphism over a base and a module identified with a pullback.
* `Stacks.Chow.GenuineChern.chernCap_flatNaturality` — the same as the flat-pullback identity
  `Stacks.Chow.IdentityCapRule.FlatNaturality` of the identity cap rule of the bivariant Chern
  class, which is axiom (2) of Stacks 0B76 read on the test schemes.

## References

* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- **Stacks 02U8 for the cap products of Stacks 02U6, rank `n + 1`.** For `f : Y ⟶ X` flat of
relative dimension `d` over the base, `ℰ` of rank `n + 1` on `X` and `ℰ' ≅ f^*ℰ`, the family of
`f^*α` for `ℰ'` is the flat pullback of the family of `α` for `ℰ`. -/
theorem bundleChernCapFamily_flatPullback {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sX = sY) (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension f d) (E : X.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    (E' : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (n + 1)]
    (eE : E' ≅ (Scheme.Modules.pullback f).obj E) (k : ℤ) (α : chowGroup C sX k) :
    bundleChernCapFamily E' n C sY (k + d)
        (flatPullbackChow C sY sX f hf d hd k
          (flatPullbackFactorsThroughRationalEquivalence_general C sY sX f hf d hd k) α) =
      flatPullbackChernFamily C sY sX (n + 1) f hf d hd
        (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C sY sX f hf d hd j) k
        (bundleChernCapFamily E n C sX k α) := by
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
    (n + 1)
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E'
    (n + 1)
  obtain ⟨e, he, ⟨eT⟩⟩ := bundleBaseChangeHolds f E E' eE
  set f' : bundle E' ⟶ bundle E := e.hom ≫ pullback.snd f (bundleProj E) with hf'def
  have hsq : IsPullback (bundleProj E') f' f (bundleProj E) := by
    refine (IsPullback.of_hasPullback f (bundleProj E)).of_iso e.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]
    · rw [Iso.symm_hom, hf'def, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id]
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hsq inferInstance
  have : Flat f' := MorphismProperty.of_isPullback hsq inferInstance
  have hd' : AlgebraicGeometry.RelativeDimension f' d :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hsq hd
  have hcomm : f' ≫ bundleProj E = bundleProj E' ≫ f := hsq.w.symm
  have hf' : f' ≫ (bundleProj E ≫ sX) = bundleProj E' ≫ sY := by
    rw [← Category.assoc, hcomm, Category.assoc, hf]
  let := Stacks.Chow.flat_bundleProj E n
  let := Stacks.Chow.locallyOfFiniteType_bundleProj E n
  let := Stacks.Chow.flat_bundleProj E' n
  let := Stacks.Chow.locallyOfFiniteType_bundleProj E' n
  have hfacf := fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C sY sX f hf d hd j
  have hfacf' := fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C
    (bundleProj E' ≫ sY) (bundleProj E ≫ sX) f' hf' d hd' j
  have hrY := Stacks.Chow.relativeDimension_bundleProj E' n
  have hrX := Stacks.Chow.relativeDimension_bundleProj E n
  have hfacY := fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C
    (bundleProj E' ≫ sY) sY (bundleProj E') rfl _ hrY j
  have hfacX := fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C
    (bundleProj E ≫ sX) sX (bundleProj E) rfl _ hrX j
  have hcompat := chernTermsCompatibleWithFlatPullback_of_square C sY sX (bundleProj E' ≫ sY)
    (bundleProj E ≫ sX) (bundleProj E') rfl (bundleProj E) rfl (n + 1) hrY hrX hfacY hfacX
    (bundleTwistCap E' C sY) (bundleTwistCap E C sX) f hf d hd hfacf f' hf' hd' hfacf' hcomm
    (fun j y y' hy ↦ flatPullbackChow_firstChernClassCapChow_heq C (bundleProj E' ≫ sY)
      (bundleProj E ≫ sX) f' hf' d hd' hfacf' (bundleTwist E) (bundleTwist E') eT.symm j y y'
      hy)
  have hinj := projectiveBundleRelationInjective_of_bundleMap C sY (bundleProj E' ≫ sY)
    (bundleProj E') rfl n hrY hfacY (bundleTwistCap E' C sY)
    fun j ↦ (projectiveBundle_formula E' n C sY j).1
  exact isChernCapFamily_flatPullback C sY sX (bundleProj E' ≫ sY) (bundleProj E ≫ sX)
    (bundleProj E') rfl (bundleProj E) rfl (n + 1) hrY hrX hfacY hfacX
    (bundleTwistCap E' C sY) (bundleTwistCap E C sX) f hf d hd hfacf f' hf' hd' hfacf'
    hinj hcompat k α _ _ (isChernCapFamily_bundleChernCapFamily E n C sX k α)
    (isChernCapFamily_bundleChernCapFamily E' n C sY (k + d) _)

/-- **Stacks 02U8 for the cap products of Stacks 02U6, in every rank.** For `f : Y ⟶ X` flat of
relative dimension `d` over the base, `ℰ` of rank `r` on `X` and `ℰ' ≅ f^*ℰ`,

  `c_j(ℰ') ∩ f^*α = f^*(c_j(ℰ) ∩ α)`,

as a heterogeneous equality: the two sides lie in `A_{(k+d)-j}(Y)` and `A_{(k-j)+d}(Y)`. -/
theorem chernCap_flatPullback_heq {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y ⟶ X)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sX = sY) (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension f d) (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (E' : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r]
    (eE : E' ≅ (Scheme.Modules.pullback f).obj E) (k : ℤ) (j : Fin (r + 1))
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sY sX f hf d hd k)
    (hfacp : FlatPullbackFactorsThroughRationalEquivalence C sY sX f hf d hd (k - (j : ℤ)))
    (α : chowGroup C sX k) :
    chernCap C r sY E' (k + d) j (flatPullbackChow C sY sX f hf d hd k hfac α) ≍
      flatPullbackChow C sY sX f hf d hd (k - (j : ℤ)) hfacp (chernCap C r sX E k j α) := by
  cases r with
  | zero =>
    rw [chernCap_zero, chernCap_zero]
    refine (chowGroupCast_heq C sY _ _).trans ?_
    exact flatPullbackChow_heq_of_degree C sY sX f hf d hd (by
      rw [show (j : ℕ) = 0 from Fin.val_eq_zero j]; simp) hfac hfacp
      (chowGroupCast_heq C sX _ _).symm
  | succ n =>
    rw [chernCap_succ, chernCap_succ, bundleChernCap_apply, bundleChernCap_apply,
      bundleChernCapFamily_flatPullback C sX sY f hf d hd E n E' eE k α]
    exact chowGroupCast_heq C sY _ _

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 02U8, as the flat-pullback identity of the identity cap rule of the bivariant Chern
class.** For `ℱ` finite locally free of rank `r` on `X` and every `0 ≤ j ≤ r`, the rule
`α ↦ c_j(g^*ℱ) ∩ α` on the test schemes `g : T ⟶ X` commutes with flat pullback of fixed
relative dimension. -/
theorem chernCap_flatNaturality (F : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (j : Fin (r + 1)) :
    IdentityCapRule.FlatNaturality C sX (j : ℤ)
      (chernIdentityCapRuleOfRank C sX F r (chernCap C r) j) := by
  intro T T' g _ h _ _ d hd k hfac hfacp α
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r g
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank F r (h ≫ g)
  exact chernCap_flatPullback_heq C (g ≫ sX) ((h ≫ g) ≫ sX) h (by simp [Category.assoc]) d hd
    ((Scheme.Modules.pullback g).obj F) r ((Scheme.Modules.pullback (h ≫ g)).obj F)
    ((Scheme.Modules.pullbackComp h g).app F).symm k j hfac hfacp α

end Stacks.Chow.GenuineChern

end
