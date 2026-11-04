module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.BivariantDivision
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.PushforwardSurjective
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundleUnconditional
public import StacksFrontier.AlgebraicGeometry.FlagTower.ProductGrassmannian

/-!
# Proper pushforward along a tower of projective bundles is surjective on Chow groups

Let `(S, δ)` be a base situation of chapter 42 and `ℰ` a finite locally free module of constant
rank `r` on a scheme `X` locally of finite type over `S`. The tower
`Stacks.FlagTower.tower m ℰ ⟶ X` of `m` projective bundles of successive tautological kernels is
proper, and for `m ≤ r` proper pushforward along it is surjective on Chow groups in every
degree: each layer is the projective bundle of a module of rank `r - j ≥ 1`, along which
pushforward is surjective (`Stacks.Chow.properChowPushforward_bundleProj_surjective`, from
Stacks 02TW), and pushforward is functorial (Stacks 02R5,
`Stacks.Chow.properChowPushforward_comp`).

Applied to tower A on the universal quotient of `G(l, n)_X` and transported along
`X ×_k G(l, n)_k ≅ G(l, n)_X` (`Stacks.FlagTower.productGrassmannianIso`), this is the sentence of
the proof of [Stacks, Tag 0FIQ]: *every cycle class on `X × G(l, n)` is the pushforward of a
cycle class on `Y`*, `Y` being the partial flag variety. The statement is not itself a tag.

Every pushforward here is the genuine `Stacks.Chow.properChowPushforward`, its descent through
rational equivalence being Stacks 02S2
(`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`).

## Main results

* `Stacks.FlagTower.isProper_tower`: the projection of the tower is proper.
* `Stacks.FlagTower.properChowPushforward_tower_surjective`: surjectivity along the tower.
* `Stacks.FlagTower.properChowPushforward_towerA_surjective`,
  `Stacks.FlagTower.properChowPushforward_towerB_surjective`: towers A and B.
* `Stacks.FlagTower.properChowPushforward_towerA_productGrassmannian_surjective`: the partial flag
  variety over `X ×_k G(l, n)_k`, for a smooth projective `X` over a field `k`.

## References

* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.FlagTower

/-- **The projection of the tower of projective bundles is proper**: a composite of projections
of projective bundles, each proper (`Stacks.Chow.isProper_bundleProj`). -/
instance isProper_tower (m : ℕ) {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsProper (tower m E).2 := by
  induction m generalizing X with
  | zero => exact inferInstanceAs (IsProper (𝟙 X))
  | succ m ih =>
    have := @ih _ (kernel (bundleTautological E)) (isFiniteLocallyFree_kernel_bundleTautological E)
    exact inferInstanceAs (IsProper ((kernelTower m E).2 ≫ bundleProj E))

/-- **Proper pushforward along a tower of `m` projective bundles is surjective on Chow groups**,
for a module of constant rank `r ≥ m`. The `j`-th layer is the projective bundle of a module of
rank `r - j ≥ 1` (`Stacks.Chow.isFiniteLocallyFreeOfRank_kernel_bundleTautological`), along which
pushforward is surjective by Stacks 02TW; pushforward along the tower is the composite
(Stacks 02R5). -/
theorem properChowPushforward_tower_surjective (C : ChowSituation.{u}) (m : ℕ)
    {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r)
    (hm : m ≤ r) (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : (tower m E).1 ⟶ C.S)
    [LocallyOfFiniteType sY] (hs : (tower m E).2 ≫ sX = sY) (k : ℤ) :
    Function.Surjective (properChowPushforward C sY sX (tower m E).2 hs k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sY sX (tower m E).2
        hs k)) := by
  induction m generalizing X r with
  | zero =>
    subst hs
    exact (properChowPushforward_bijective_of_isIso C _ sX (𝟙 X) (Category.id_comp sX) k _).2
  | succ m ih =>
    obtain ⟨r, rfl⟩ : ∃ r' : ℕ, r = r' + 1 := ⟨r - 1, by omega⟩
    have hK := isFiniteLocallyFreeOfRank_kernel_bundleTautological E r hE
    have hKf := isFiniteLocallyFree_kernel_bundleTautological E
    have hf : (kernelTower m E).2 ≫ (bundleProj E ≫ sX) = sY :=
      (Category.assoc _ _ _).symm.trans hs
    have h1 := @ih _ (kernel (bundleTautological E)) hKf r hK (by omega) (bundleProj E ≫ sX)
      inferInstance sY ‹_› hf
    exact @properChowPushforward_comp_surjective _ C sY ‹_› _ _ (bundleProj E ≫ sX) inferInstance
      sX ‹_› (kernelTower m E).2 (@isProper_tower m _ _ hKf) (bundleProj E) inferInstance hf rfl k
      h1 (properChowPushforward_bundleProj_surjective E r hE C sX (bundleProj E ≫ sX) rfl k)

open AlgebraicGeometry.Grassmannian in
/-- **Tower A**: proper pushforward from the partial flag variety built on the universal quotient
of `G(l, n)_X` to `G(l, n)_X` is surjective on Chow groups. -/
theorem properChowPushforward_towerA_surjective (C : ChowSituation.{u}) (l n : ℕ)
    (X : Scheme.{u}) (sG : schemeOver.{u} l n X ⟶ C.S) [LocallyOfFiniteType sG]
    (sY : (towerA l n X).1 ⟶ C.S) [LocallyOfFiniteType sY] (hs : (towerA l n X).2 ≫ sG = sY)
    (k : ℤ) :
    Function.Surjective (properChowPushforward C sY sG (towerA l n X).2 hs k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sY sG (towerA l n X).2
        hs k)) :=
  have := isFiniteLocallyFree_universalQuotient l n X
  properChowPushforward_tower_surjective C (n - l) (universalQuotient l n X).target (n - l)
    (rank_universalQuotient l n X) le_rfl sG sY hs k

/-- **Tower B**: proper pushforward from the partial flag variety of length `n - l` of `𝒪_X^n`
to `X` is surjective on Chow groups. -/
theorem properChowPushforward_towerB_surjective (C : ChowSituation.{u}) (l n : ℕ)
    (X : Scheme.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : (towerB l n X).1 ⟶ C.S) [LocallyOfFiniteType sY] (hs : (towerB l n X).2 ≫ sX = sY)
    (k : ℤ) :
    Function.Surjective (properChowPushforward C sY sX (towerB l n X).2 hs k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sY sX (towerB l n X).2
        hs k)) :=
  have := isFiniteLocallyFree_freeModule n X
  properChowPushforward_tower_surjective C (n - l) (freeModule n X) n (rank_freeModule n X)
    (Nat.sub_le n l) sX sY hs k

open Stacks.WeilCohomology in
/-- **Every cycle class on `X × G(l, n)` is the pushforward of a cycle class on the partial flag
variety `Y`**: the step of the proof of Stacks 0FIQ. For a smooth projective scheme `X` over a
field `k`, let `h : Y ⟶ X ×_k G(l, n)_k` be tower A over `G(l, n)_X` followed by the
identification `G(l, n)_X ≅ X ×_k G(l, n)_k` (`Stacks.FlagTower.productGrassmannianIso`). Then
`h_*` is surjective on Chow groups in every degree, for every structure morphism to the base
lying over one of `X ×_k G(l, n)_k`. -/
theorem properChowPushforward_towerA_productGrassmannian_surjective (k : Type u) [Field k]
    (X : (SmoothProjectiveScheme k).FullSubcategory) (l n : ℕ) (C : ChowSituation.{u})
    (sP : pullback X.obj.hom (SmoothProjectiveScheme.grassmannian k l n).obj.hom ⟶ C.S)
    [LocallyOfFiniteType sP]
    (sY : (towerA l n ((SmoothProjectiveScheme.toScheme k).obj X)).1 ⟶ C.S)
    [LocallyOfFiniteType sY]
    (hs : ((towerA l n ((SmoothProjectiveScheme.toScheme k).obj X)).2 ≫
      (productGrassmannianIso k X l n).inv) ≫ sP = sY) (d : ℤ) :
    Function.Surjective (properChowPushforward C sY sP
      ((towerA l n ((SmoothProjectiveScheme.toScheme k).obj X)).2 ≫
        (productGrassmannianIso k X l n).inv) hs d
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sY sP _ hs d)) := by
  have hA : (towerA l n ((SmoothProjectiveScheme.toScheme k).obj X)).2 ≫
      ((productGrassmannianIso k X l n).inv ≫ sP) = sY := by
    rw [← hs, Category.assoc]
  have h1 := properChowPushforward_towerA_surjective C l n
    ((SmoothProjectiveScheme.toScheme k).obj X) ((productGrassmannianIso k X l n).inv ≫ sP)
    sY hA d
  exact properChowPushforward_comp_surjective C sY _ sP
    (towerA l n ((SmoothProjectiveScheme.toScheme k).obj X)).2
    (productGrassmannianIso k X l n).inv hA rfl d h1
    (properChowPushforward_bijective_of_isIso C _ sP (productGrassmannianIso k X l n).inv rfl d
      _).2

end Stacks.FlagTower

end
