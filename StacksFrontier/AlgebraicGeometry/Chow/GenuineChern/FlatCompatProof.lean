module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernBasic
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InvertibleCap
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bridge
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.TopHalfProof
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.Segre
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleExistence
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleFlatPullback

/-!
# The first Chern class commutes with flat pullback

Let `f : Y ⟶ X` be flat of relative dimension `d` between schemes locally of finite type over the
base of chapter 42, `ℰ` a finite locally free module of rank `n + 1` on `X` and `ℰ' ≅ f^*ℰ`. This
file proves `Stacks.Chow.GenuineChern.FlatCompat`:

  `c₁(ℰ') ∩ f^*α = f^*(c₁(ℰ) ∩ α)`,

the first Chern class part of [Stacks, Tag 02U8]. The projective bundle of `ℰ'` is the base change
of that of `ℰ` along `f`, compatibly with the twists
(`Stacks.Chow.GenuineChern.BundleBaseChangeHolds`), so the second projection `f' : 𝐏(ℰ') ⟶ 𝐏(ℰ)` is
flat of relative dimension `d`, commutes with the projections and carries `c₁(𝒪(1)) ∩ -` to
`c₁(𝒪(1)) ∩ -` ([Stacks, Tag 02SS]). Pulling the relation of [Stacks, Tag 02U6] back along `f'`
therefore gives the relation for `f^*α`, and the uniqueness half of [Stacks, Tag 02U6] —
injectivity in [Stacks, Tag 02TX] — identifies the pulled back family with the family of `f^*α`.
Reading off the member `j = 1`, which is the Segre pushforward, gives the claim.

## Main definitions

* `Stacks.Chow.GenuineChern.BundleBaseChangeHolds` — the projective bundle and its twist commute
  with base change.

## Main results

* `Stacks.Chow.GenuineChern.flatCompat_of` — `Stacks.Chow.GenuineChern.FlatCompat` from
  `Stacks.Chow.GenuineChern.BundleBaseChangeHolds`, which is
  `Stacks.Chow.GenuineChern.bundleBaseChangeHolds`.

## References

* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.GenuineChern

/-- **The projective bundle commutes with base change, compatibly with its twist.** For
`g : X' ⟶ X` and `ℰ' ≅ g^*ℰ` finite locally free, `𝐏(ℰ')` is the fibre product
`X' ×_X 𝐏(ℰ)` over `X'`, and the twist of `𝐏(ℰ')` is the pullback of the twist of `𝐏(ℰ)` along the
second projection. -/
def BundleBaseChangeHolds : Prop :=
  ∀ ⦃X X' : Scheme.{u}⦄ (g : X' ⟶ X) (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (E' : X'.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    (_ : E' ≅ (Scheme.Modules.pullback g).obj E),
    ∃ e : bundle E' ≅ pullback g (bundleProj E),
      e.hom ≫ pullback.fst g (bundleProj E) = bundleProj E' ∧
        Nonempty ((Scheme.Modules.pullback (e.hom ≫ pullback.snd g (bundleProj E))).obj
          (bundleTwist E) ≅ bundleTwist E')

variable (C : ChowSituation.{u})

/-- **Stacks 02U8 for the first Chern class**, from the compatibility of the projective bundle
with base change (`Stacks.Chow.GenuineChern.BundleBaseChangeHolds`). -/
theorem flatCompat_of (hG : BundleBaseChangeHolds.{u}) : FlatCompat C := by
  intro X Y sX _ sY _ f _ _ hf d hd E n _ _ E' _ _ eE k α
  obtain ⟨e, he, ⟨eT⟩⟩ := hG f E E' eE
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
  -- the twists correspond under `f'` (Stacks 02SS)
  have hcompat := chernTermsCompatibleWithFlatPullback_of_square C sY sX (bundleProj E' ≫ sY)
    (bundleProj E ≫ sX) (bundleProj E') rfl (bundleProj E) rfl (n + 1)
    (Stacks.Chow.relativeDimension_bundleProj E' n)
    (Stacks.Chow.relativeDimension_bundleProj E n)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sY _ rfl _ _ j)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
    (bundleTwistCap E' C sY) (bundleTwistCap E C sX) f hf d hd hfacf f' hf' hd' hfacf' hcomm
    (fun j y y' hy ↦ flatPullbackChow_firstChernClassCapChow_heq C (bundleProj E' ≫ sY)
      (bundleProj E ≫ sX) f' hf' d hd' hfacf' (bundleTwist E) (bundleTwist E') eT.symm j y y'
      hy)
  -- the two halves of Stacks 02TX on the two bundles
  have hinj := projectiveBundleRelationInjective_of_bundleMap C sY (bundleProj E' ≫ sY)
    (bundleProj E') rfl n (Stacks.Chow.relativeDimension_bundleProj E' n)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sY _ rfl _ _ j)
    (bundleTwistCap E' C sY) fun j ↦ (projectiveBundle_formula E' n C sY j).1
  have hsurj := projectiveBundleRelationSurjective_of_bundleMap C sX (bundleProj E ≫ sX)
    (bundleProj E) rfl n (Stacks.Chow.relativeDimension_bundleProj E n)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
    (bundleTwistCap E C sX) fun j ↦ (projectiveBundle_formula E n C sX j).2
  have hsurj' := projectiveBundleRelationSurjective_of_bundleMap C sY (bundleProj E' ≫ sY)
    (bundleProj E') rfl n (Stacks.Chow.relativeDimension_bundleProj E' n)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sY _ rfl _ _ j)
    (bundleTwistCap E' C sY) fun j ↦ (projectiveBundle_formula E' n C sY j).2
  -- the families of `α` and of `f^*α`
  obtain ⟨c, hc⟩ := exists_isChernCapFamily C sX _ _ rfl (n + 1) _ _ _ hsurj k α
  obtain ⟨c', hc'⟩ := exists_isChernCapFamily C sY _ _ rfl (n + 1) _ _ _ hsurj' (k + d)
    (flatPullbackChow C sY sX f hf d hd k (hfacf k) α)
  -- uniqueness identifies the family of `f^*α` with the pullback of the family of `α`
  have key := isChernCapFamily_flatPullback C sY sX (bundleProj E' ≫ sY) (bundleProj E ≫ sX)
    (bundleProj E') rfl (bundleProj E) rfl (n + 1)
    (Stacks.Chow.relativeDimension_bundleProj E' n)
    (Stacks.Chow.relativeDimension_bundleProj E n)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sY _ rfl _ _ j)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
    (bundleTwistCap E' C sY) (bundleTwistCap E C sX) f hf d hd hfacf f' hf' hd' hfacf'
    hinj hcompat k α c c' hc hc'
  -- the member `j = 1` is the Segre pushforward (the top half of Stacks 02TW)
  have h1 := chowGroupCast_one_eq_projectiveBundleProjection_of_isChernCapFamily C sX
    (bundleProj E ≫ sX) (bundleProj E) rfl (n + 1) (Stacks.Chow.relativeDimension_bundleProj E n)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sX _ rfl _ _ j)
    (bundleTwistCap E C sX) (by omega) (topHalf C sX E n) k α c hc
  have h1' := chowGroupCast_one_eq_projectiveBundleProjection_of_isChernCapFamily C sY
    (bundleProj E' ≫ sY) (bundleProj E') rfl (n + 1)
    (Stacks.Chow.relativeDimension_bundleProj E' n)
    (fun j ↦ flatPullbackFactorsThroughRationalEquivalence_general C _ sY _ rfl _ _ j)
    (bundleTwistCap E' C sY) (by omega) (topHalf C sY E' n) (k + d) _ c' hc'
  simp only [segre, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom]
  rw [← h1, ← h1', congrFun key ⟨1, by omega⟩]
  refine (chowGroupCast_heq C sY _ _).trans ((chowGroupCast_heq C sY _ _).trans
    ((chowGroupCast_heq C sY _ _).trans ?_))
  exact flatPullbackChow_heq C sY sX f hf d hd hfacf (by simp)
    ((chowGroupCast_heq C sX _ _).trans (chowGroupCast_heq C sX _ _)).symm

end Stacks.Chow.GenuineChern

end
