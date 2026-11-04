module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteBivariantComposite
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothCapFundamentalProduct
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SmoothRelativeDimensionShift
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VirtualNormalCommutingEveryClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleImmersionClass
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalVirtualNormalBundle
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField

/-!
# The Gysin class of the diagonal of a smooth morphism

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `g : Y ⟶ Z` be a
smooth morphism, with `Y` locally of finite type over `S`, and write `P = Y ×_Z Y`,
`Δ : Y ⟶ P` for the diagonal and `pr_1, pr_2 : P ⟶ Y` for the projections. The diagonal is a
regular immersion, and Stacks 0FBR considers its Gysin class `Δ^! ∈ A^*(Y ⟶ P)`, which lies in
`A^d(Y ⟶ P)` when `g` has constant relative dimension `d`.

By Stacks 0FEZ the Gysin class of an immersion is the class `c(Y ⟶ P, 𝒩)` of Stacks 0FBQ (3) of
its normal bundle `𝒩`: choosing the open subscheme `U ⊆ P` in which `Δ` is closed, with closed
factor `Δ' : Y ⟶ U` and inclusion `ι : U ⟶ P`,

  `Δ^! = c(Y ⟶ U, 𝒩) ∘ ι^*`,

the composite (Stacks 0B75) of flat pullback along `ι` (Stacks 0B78) with the class of Stacks
0FBK of the normal bundle of `Δ'`, of rank `d`. This file builds that class, computes its cap
operation, and treats the two properties of `Δ^!` used in Stacks 0FBT: it proves that `Δ^!`
commutes with every bivariant class over `P`, from Stacks 0FBP for the factor `c(Y ⟶ U, 𝒩)`, and
reduces `Δ^! ∘ pr_i^* = 1` (Stacks 0FBS) to the corresponding identity for that factor.

## Main definitions

* `Stacks.Chow.diagonalClosedFactorClass` — the class `c(Y ⟶ U, 𝒩) ∈ A^d(Y ⟶ U)` of Stacks 0FBK
  of the normal bundle of the closed factor `Δ'` of the diagonal.
* `Stacks.Chow.diagonalOpenPullbackClass` — flat pullback `ι^* ∈ A^0(U ⟶ P)` along the inclusion
  of the open subscheme `U`.
* `Stacks.Chow.diagonalGysinClass` — **the Gysin class `Δ^! ∈ A^d(Y ⟶ Y ×_Z Y)`** of the diagonal
  of a smooth morphism of constant relative dimension `d`.

## Main results

* `Stacks.Chow.diagonalGysinClass_eq_bivariantCompositeOfInvertible` — `Δ^!` is the composite
  `c(Y ⟶ U, 𝒩) ∘ ι^*`, read as a class for `Δ = Δ' ≫ ι` in degree `d = d + 0`.
* `Stacks.Chow.diagonalGysinClass_cap_heq` — `Δ^! ∩ α = c(Y ⟶ U, 𝒩) ∩ (ι^* ∩ α)`, read through
  the identification `Y ×_U (U ×_P T) ≅ Y ×_P T`.
* `Stacks.Chow.diagonalGysinClass_commute_of` — if `c(Y ⟶ U, 𝒩)` commutes with every bivariant
  class over `U`, then `Δ^!` commutes with every bivariant class over `Y ×_Z Y`.
* `Stacks.Chow.diagonalGysinClass_compFlatPullbackEqOne_of` — for a flat retraction `pr` of `Δ` of
  relative dimension `d` (either projection), `Δ^! ∘ pr^* = 1` follows from
  `c(Y ⟶ U, 𝒩) ∘ (ι ≫ pr)^* = 1`.

## Implementation notes

The class is `Stacks.Chow.immersionVirtualNormalGysinClass` of the diagonal, at the normal bundle
`Stacks.Chow.diagonalVirtualNormalBundle` read as a virtual normal bundle of `Δ` itself. Its type
is the one Stacks 0FBT consumes: a class for `Δ` whose source lies over the base through
`Δ ≫ pr_1 ≫ s_Y`, in degree `d`.

The commutation and the identity `Δ^! ∘ pr^* = 1` are reduced, not proved: the first is Stacks
0FBP for the closed immersion `Δ'`, the second Stacks 0FBS. Flat pullback along `ι` commutes with
every class (the smooth half of Stacks 0FF6), and the composite of flat pullbacks along
`U ×_P W ⟶ W ⟶ T` is flat pullback along the composite (Stacks 02RD), which is how the identity
for `Δ^!` and the projection `pr` becomes the identity for `c(Y ⟶ U, 𝒩)` and `ι ≫ pr`.

## References

* [Stacks Project, Section 42.60 (Tag 0FBR)](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0FEZ](https://stacks.math.columbia.edu/tag/0FEZ)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FBS](https://stacks.math.columbia.edu/tag/0FBS)
* [Stacks Project, Tag 0FBT](https://stacks.math.columbia.edu/tag/0FBT)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport lemmas -/

/-- The cap operation of the class of Stacks 0FBK depends on the structure morphism of the source
and on the virtual normal bundle only up to equality, and on the degree and the class capped
only up to heterogeneous equality. -/
theorem virtualNormalGysinClass_cap_heq_congr (C : ChowSituation.{u}) {Z X : Scheme.{u}}
    {sZ sZ' : Z ⟶ C.S} [LocallyOfFiniteType sZ] [LocallyOfFiniteType sZ']
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ sX = sZ) (hi' : i ≫ sX = sZ') (hsZ : sZ = sZ') {𝒩 𝒩' : VirtualNormalBundle i}
    (h𝒩 : 𝒩 = 𝒩') (r : ℕ)
    {h𝒩r : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r}
    {h𝒩r' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩'.bundle r} {T : Scheme.{u}}
    (t : T ⟶ X) [LocallyOfFiniteType t] {k k' : ℤ} (hk : k = k')
    {α : chowGroup C (t ≫ sX) k} {α' : chowGroup C (t ≫ sX) k'} (hα : α ≍ α') :
    (virtualNormalBundleClass C sZ sX i hi 𝒩 r).cap t k α ≍
      (virtualNormalBundleClass C sZ' sX i hi' 𝒩' r).cap t k' α' := by
  subst hsZ h𝒩 hk
  obtain rfl := eq_of_heq hα
  rfl

/-- Commuting (Stacks 0FA2) is preserved by transporting the first class along an equality of
degrees. -/
theorem bivariantCommute_bivariantClassDegreeCongr_left (C : ChowSituation.{u})
    {G : GysinSystem C} {X Z₁ Z₂ : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
    {f₁ : Z₁ ⟶ X} [LocallyOfFiniteType f₁] {f₂ : Z₂ ⟶ X} [LocallyOfFiniteType f₂]
    {p₁ p₁' p₂ : ℤ} (h : p₁ = p₁') {c₁ : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁}
    {c₂ : BivariantClass C G (f₂ ≫ sX) sX f₂ rfl p₂}
    (hc : BivariantCommute C G sX f₁ f₂ p₁ p₂ c₁ c₂) :
    BivariantCommute C G sX f₁ f₂ p₁' p₂ (bivariantClassDegreeCongr C G _ sX f₁ rfl h c₁) c₂ := by
  subst h
  exact hc

/-! ### The two factors and the class -/

variable (C : ChowSituation.{u}) {Y Z : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (g : Y ⟶ Z) [Smooth g] {d : ℕ} (hd : RelativeDimension g d)

/-- **The class `c(Y ⟶ U, 𝒩) ∈ A^d(Y ⟶ U)`** of Stacks 0FBK for the closed factor
`Δ' : Y ⟶ U` of the diagonal of `g`, at its normal bundle `𝒩`, of rank `d`. Here
`U = (pullback.diagonal g).coborderRange` is the open subscheme of `Y ×_Z Y` in which the diagonal
is closed. -/
abbrev diagonalClosedFactorClass :
    BivariantClass C (gysinSystemOfInvertible C)
      ((pullback.diagonal g).liftCoborder ≫
        ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))
      ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))
      (pullback.diagonal g).liftCoborder rfl (d : ℤ) :=
  haveI := isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle g hd
  virtualNormalBundleClass C _ _ (pullback.diagonal g).liftCoborder rfl
    (diagonalVirtualNormalBundle g) d

/-- **Flat pullback `ι^* ∈ A^0(U ⟶ Y ×_Z Y)`** (Stacks 0B78) along the inclusion of the open
subscheme `U = (pullback.diagonal g).coborderRange` in which the diagonal is closed. -/
abbrev diagonalOpenPullbackClass :
    BivariantClass C (gysinSystemOfInvertible C)
      ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))
      (pullback.fst g g ≫ sY) (pullback.diagonal g).coborderRange.ι rfl (-((0 : ℕ) : ℤ)) :=
  flatPullbackBivariantClassOfInvertible C _ _ (pullback.diagonal g).coborderRange.ι rfl 0
    (relativeDimension_of_isOpenImmersion _)

/-- **Stacks 0FBR, the Gysin class `Δ^! ∈ A^d(Y ⟶ Y ×_Z Y)`** of the diagonal of a smooth
morphism `g : Y ⟶ Z` of constant relative dimension `d`: the class `c(Y ⟶ Y ×_Z Y, 𝒩)` of Stacks
0FBQ (3) of the normal bundle `𝒩` of the diagonal (Stacks 0FEZ), at the open subscheme
`U = (pullback.diagonal g).coborderRange` in which the diagonal is closed. It is
`c(Y ⟶ U, 𝒩) ∘ ι^*` by `Stacks.Chow.diagonalGysinClass_eq_bivariantCompositeOfInvertible`. -/
@[stacks 0FBR "the Gysin class Δ^! ∈ A^d(X → X ×_Y X) of the diagonal of a smooth morphism of \
constant relative dimension d"]
def diagonalGysinClass :
    BivariantClass C (gysinSystemOfInvertible C)
      (pullback.diagonal g ≫ (pullback.fst g g ≫ sY)) (pullback.fst g g ≫ sY)
      (pullback.diagonal g) rfl d :=
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((diagonalVirtualNormalBundle g).ofOpenFactor
        (pullback.diagonal g).liftCoborder_ι).bundle d :=
    isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle g hd
  immersionVirtualNormalGysinClass C _ _ (pullback.diagonal g) rfl
    ((diagonalVirtualNormalBundle g).ofOpenFactor (pullback.diagonal g).liftCoborder_ι) d

/-- **`Δ^! = c(Y ⟶ U, 𝒩) ∘ ι^*`.** The Gysin class of the diagonal is the composite (Stacks 0B75)
of `Stacks.Chow.diagonalOpenPullbackClass` with `Stacks.Chow.diagonalClosedFactorClass`, read as a
class for `Δ = Δ' ≫ ι` whose source lies over the base through `Δ ≫ pr_1 ≫ s_Y`, in degree
`d = d + -0`. -/
theorem diagonalGysinClass_eq_bivariantCompositeOfInvertible :
    diagonalGysinClass C sY g hd =
      bivariantClassDegreeCongr C (gysinSystemOfInvertible C) _ _ _ rfl
        (show (d : ℤ) + -((0 : ℕ) : ℤ) = d by simp)
        (BivariantClass.congrHom (pullback.diagonal g).liftCoborder_ι rfl
          (bivariantClassCongrBase C (gysinSystemOfInvertible C)
            ((pullback.diagonal g).liftCoborder ≫ (pullback.diagonal g).coborderRange.ι)
            ((Category.assoc _ _ _).symm.trans
              (congrArg (· ≫ (pullback.fst g g ≫ sY)) (pullback.diagonal g).liftCoborder_ι)) rfl
            (hv' := congrArg (· ≫ (pullback.fst g g ≫ sY)) (pullback.diagonal g).liftCoborder_ι)
            ((d : ℤ) + -((0 : ℕ) : ℤ))
            (bivariantCompositeOfInvertible C _ _ _ (pullback.diagonal g).liftCoborder
              (pullback.diagonal g).coborderRange.ι rfl rfl (d : ℤ) (-((0 : ℕ) : ℤ))
              (diagonalClosedFactorClass C sY g hd) (diagonalOpenPullbackClass C sY g)))) := by
  refine BivariantClass.ext C _ _ _ _ _ _ ?_
  intro T t _ k α
  refine eq_of_heq ?_
  refine (BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t k α).trans ?_
  refine (openImmersionComposite_cap_heq C (pullback.diagonal g ≫ (pullback.fst g g ≫ sY))
    ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)) (pullback.fst g g ≫ sY)
    (pullback.diagonal g).liftCoborder (pullback.diagonal g).coborderRange.ι _ rfl d _
    t k α).trans ?_
  refine HEq.symm ((bivariantClassDegreeCongr_cap C _ _ _ _ rfl _ _ t k α).trans ?_)
  refine (BivariantClass.congrHom_cap_heq _ _ _ t k α).trans ?_
  refine (bivariantClassCongrBase_cap C _ _ _ rfl _ _ t k α α HEq.rfl).trans ?_
  refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
  rw [bivariantCompositeCap_apply, properChowPushforward_eq_chowPushforwardOfIso]
  refine chowPushforwardOfIso_heq _ _ _ (by simp) (by simp) (by simp) ?_
  refine virtualNormalGysinClass_cap_heq_congr C _ _ _ _ (by simp)
    ((VirtualNormalBundle.openFactorEquiv (pullback.diagonal g).liftCoborder_ι).right_inv
      (diagonalVirtualNormalBundle g)).symm d
    (h𝒩r := isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle g hd)
    (h𝒩r' := isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle g hd) _ (by simp) ?_
  exact flatPullbackBivariantCap_heq_chowGroupRestrict C _ _ _ rfl t k α

/-! ### The cap operation -/

/-- **The cap operation of `Δ^!`**: `Δ^! ∩ α = c(Y ⟶ U, 𝒩) ∩ (ι^* ∩ α)` for a test scheme
`t : T ⟶ Y ×_Z Y` and `α ∈ CH_k(T)`, pushed forward along the identification
`Y ×_U (U ×_P T) ≅ Y ×_{Δ' ≫ ι} T = Y ×_Δ T`. The degree is written `k - -0 - d` on the right
and `k - d` on the left, whence the heterogeneous equality. -/
theorem diagonalGysinClass_cap_heq {T : Scheme.{u}} (t : T ⟶ pullback g g)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ (pullback.fst g g ≫ sY)) k) :
    (diagonalGysinClass C sY g hd).cap t k α ≍
      chowPushforwardOfIso C
        (pullback.fst (pullback.diagonal g).liftCoborder
            (pullback.fst (pullback.diagonal g).coborderRange.ι t) ≫
          ((pullback.diagonal g).liftCoborder ≫
            ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))))
        (pullback.fst (pullback.diagonal g) t ≫ (pullback.diagonal g ≫ (pullback.fst g g ≫ sY)))
        ((pullbackRightPullbackFstIso (pullback.diagonal g).coborderRange.ι t
            (pullback.diagonal g).liftCoborder).hom ≫
          (pullback.congrHom (pullback.diagonal g).liftCoborder_ι rfl).hom)
        (by simp) (k - -((0 : ℕ) : ℤ) - d)
        ((diagonalClosedFactorClass C sY g hd).cap
          (pullback.fst (pullback.diagonal g).coborderRange.ι t) (k - -((0 : ℕ) : ℤ))
          ((diagonalOpenPullbackClass C sY g).cap t k α)) := by
  rw [diagonalGysinClass_eq_bivariantCompositeOfInvertible]
  refine (bivariantClassDegreeCongr_cap C _ _ _ _ rfl _ _ t k α).trans ?_
  rw [BivariantClass.congrHom_cap]
  refine chowPushforwardOfIso_heq_comp_of_comp_eq (sB := pullback.fst
      ((pullback.diagonal g).liftCoborder ≫ (pullback.diagonal g).coborderRange.ι) t ≫
        ((pullback.diagonal g).liftCoborder ≫
          ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))))
    _ _ _ rfl (by simp) _ (by simp) rfl (by ring) _ _ ?_
  refine (bivariantClassCongrBase_cap C _ _ _ rfl _ _ t k α α HEq.rfl).trans ?_
  exact chowGroupDegreeEquiv_heq C _ _ _

/-! ### Reduction of the two properties used by Stacks 0FBT -/

/-- **`Δ^!` commutes with every bivariant class over `Y ×_Z Y`, given Stacks 0FBP for the closed
factor.** If `c(Y ⟶ U, 𝒩)` commutes, in the sense of Stacks 0FA2, with every bivariant class over
`U`, then `Δ^!` commutes with every bivariant class over `Y ×_Z Y`: flat pullback along the open
immersion `ι` commutes with every class (the smooth half of Stacks 0FF6), and a composite of
commuting classes commutes. -/
theorem diagonalGysinClass_commute_of
    (ha : ∀ {Z₂' : Scheme.{u}} (f₂' : Z₂' ⟶ (pullback.diagonal g).coborderRange.toScheme)
      [LocallyOfFiniteType f₂'] (p₂' : ℤ)
      (c₂' : BivariantClass C (gysinSystemOfInvertible C)
        (f₂' ≫ ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)))
        ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY)) f₂' rfl p₂'),
      BivariantCommute C (gysinSystemOfInvertible C)
        ((pullback.diagonal g).coborderRange.ι ≫ (pullback.fst g g ≫ sY))
        (pullback.diagonal g).liftCoborder f₂' d p₂' (diagonalClosedFactorClass C sY g hd) c₂')
    {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ pullback g g) [LocallyOfFiniteType f₂] (p₂ : ℤ)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ (pullback.fst g g ≫ sY))
      (pullback.fst g g ≫ sY) f₂ rfl p₂) :
    BivariantCommute C (gysinSystemOfInvertible C) (pullback.fst g g ≫ sY) (pullback.diagonal g)
      f₂ d p₂ (diagonalGysinClass C sY g hd) c₂ := by
  rw [diagonalGysinClass_eq_bivariantCompositeOfInvertible]
  exact bivariantCommute_bivariantClassDegreeCongr_left C _ <|
    bivariantCommute_bivariantCompositeOfInvertible C (pullback.fst g g ≫ sY)
      (pullback.diagonal g).liftCoborder (pullback.diagonal g).coborderRange.ι d
      (-((0 : ℕ) : ℤ)) (diagonalClosedFactorClass C sY g hd) (diagonalOpenPullbackClass C sY g)
      ha (fun f₂ _ p₂ c₂ ↦ bivariantCommute_of_isBivariantFlatPullback C _ _ _ f₂ 0 _
        (flatPullbackDescends C) p₂ c₂ (diagonalOpenPullbackClass C sY g)
        (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _
          (pullback.diagonal g).coborderRange.ι rfl 0 (relativeDimension_of_isOpenImmersion _)))
      f₂ p₂ c₂ (pullback.diagonal g).liftCoborder_ι

/-- **`Δ^!` commutes with every bivariant class over `Y ×_Z Y`** (Stacks 0FBP applied to the
closed factor). For `f₂ : Z₂ ⟶ Y ×_Z Y` locally of finite type and `c₂ ∈ A^{p₂}(Z₂ ⟶ Y ×_Z Y)`,
the classes `Δ^!` and `c₂` commute in the sense of Stacks 0FA2: the closed factor `c(Y ⟶ U, 𝒩)`
commutes with every class over `U` by Stacks 0FBP, its normal bundle having rank `d`. -/
theorem diagonalGysinClass_bivariantCommute {Z₂ : Scheme.{u}} (f₂ : Z₂ ⟶ pullback g g)
    [LocallyOfFiniteType f₂] (p₂ : ℤ)
    (c₂ : BivariantClass C (gysinSystemOfInvertible C) (f₂ ≫ (pullback.fst g g ≫ sY))
      (pullback.fst g g ≫ sY) f₂ rfl p₂) :
    BivariantCommute C (gysinSystemOfInvertible C) (pullback.fst g g ≫ sY) (pullback.diagonal g)
      f₂ d p₂ (diagonalGysinClass C sY g hd) c₂ :=
  have := isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle g hd
  diagonalGysinClass_commute_of C sY g hd
    (fun f₂' _ p₂' c₂' ↦ virtualNormalBundleClass_bivariantCommute C _
      (pullback.diagonal g).liftCoborder d (diagonalVirtualNormalBundle g) f₂' p₂' c₂')
    f₂ p₂ c₂

/-- **`Δ^!` commutes with every bivariant class over `Y ×_Z Y`**, in the form
`Stacks.Chow.BivariantClass.CommutesWithEveryClass`. -/
theorem diagonalGysinClass_commutesWithEveryClass :
    (diagonalGysinClass C sY g hd).CommutesWithEveryClass :=
  (BivariantClass.commutesWithEveryClass_iff _).2 fun _ f₂ _ p₂ c₂ ↦
    diagonalGysinClass_bivariantCommute C sY g hd f₂ p₂ c₂

/-- **`Δ^! ∘ pr^* = 1`, given the identity for the closed factor.** Let `pr : Y ×_Z Y ⟶ Y` be a
flat retraction of the diagonal of relative dimension `d`, such as either projection. If
`c(Y ⟶ U, 𝒩) ∘ (ι ≫ pr)^* = 1` on cap operations, then `Δ^! ∘ pr^* = 1`.

For `t : T ⟶ Y`, write `W = (Y ×_Z Y) ×_Y T`. By the cap formula of `Δ^!`, capping the flat
pullback of `α` to `W` with `Δ^!` caps its restriction to `U ×_P W` with `c(Y ⟶ U, 𝒩)`; that
restriction is the flat pullback of `α` along `U ×_P W ⟶ W ⟶ T` (Stacks 02RD), and
`U ×_P W = U ×_Y T` is the fibre product along `ι ≫ pr`, where the hypothesis applies. -/
theorem diagonalGysinClass_compFlatPullbackEqOne_of (pr : pullback g g ⟶ Y)
    [LocallyOfFiniteType pr] [Flat pr] (hpr : pr ≫ sY = pullback.fst g g ≫ sY)
    (hdiag : pullback.diagonal g ≫ pr = 𝟙 Y) (hr : RelativeDimension pr d)
    (hc : (diagonalClosedFactorClass C sY g hd).CompFlatPullbackEqOne (sY := sY)
      ((pullback.diagonal g).coborderRange.ι ≫ pr) (by rw [Category.assoc, hpr])
      (by rw [← Category.assoc, Scheme.Hom.liftCoborder_ι, hdiag])
      (by
        simpa using RelativeDimension.comp_of_flat _ pr
          (relativeDimension_of_isOpenImmersion (pullback.diagonal g).coborderRange.ι) hr)) :
    (diagonalGysinClass C sY g hd).CompFlatPullbackEqOne pr hpr hdiag hr := by
  intro T t _ k α
  set ι := (pullback.diagonal g).coborderRange.ι with hι
  set Δ' := (pullback.diagonal g).liftCoborder with hΔ'
  have hΔ : Δ' ≫ ι = pullback.diagonal g := Scheme.Hom.liftCoborder_ι _
  -- the fibre product `U ×_P W`, presented over `ι ≫ pr`
  have sq : IsPullback (pullback.fst ι (pullback.fst pr t))
      (pullback.snd ι (pullback.fst pr t) ≫ pullback.snd pr t) (ι ≫ pr) t :=
    IsPullback.paste_vert (IsPullback.of_hasPullback ι (pullback.fst pr t))
      (IsPullback.of_hasPullback pr t)
  have hvr : RelativeDimension (pullback.snd ι (pullback.fst pr t) ≫ pullback.snd pr t) d := by
    simpa using RelativeDimension.comp_of_flat (pullback.snd ι (pullback.fst pr t))
      (pullback.snd pr t)
      (relativeDimension_pullbackSnd ι (relativeDimension_of_isOpenImmersion ι)
        (pullback.fst pr t))
      (relativeDimension_pullbackSnd pr hr t)
  have hvs : (pullback.snd ι (pullback.fst pr t) ≫ pullback.snd pr t) ≫ (t ≫ sY) =
      pullback.fst ι (pullback.fst pr t) ≫ (ι ≫ (pullback.fst g g ≫ sY)) := by
    rw [Category.assoc, ← Category.assoc (pullback.snd pr t), ← pullback.condition,
      Category.assoc, hpr, ← Category.assoc, ← pullback.condition, Category.assoc]
  have hdiag' : Δ' ≫ (ι ≫ pr) = 𝟙 Y := by rw [← Category.assoc, hΔ, hdiag]
  -- the section `T ⟶ Y ×_U (U ×_P W)`
  set m : T ⟶ pullback pr t := pullback.lift (t ≫ pullback.diagonal g) (𝟙 T)
    (by rw [Category.assoc, hdiag, Category.comp_id, Category.id_comp]) with hm
  set n : T ⟶ pullback ι (pullback.fst pr t) := pullback.lift (t ≫ Δ') m
    (by rw [Category.assoc, hΔ, hm, pullback.lift_fst]) with hn
  set e : T ⟶ pullback Δ' (pullback.fst ι (pullback.fst pr t)) := pullback.lift t n
    (by rw [hn, pullback.lift_fst]) with he
  have he₁ : e ≫ pullback.fst Δ' (pullback.fst ι (pullback.fst pr t)) = t :=
    pullback.lift_fst _ _ _
  have he₂ : e ≫ pullback.snd Δ' (pullback.fst ι (pullback.fst pr t)) ≫
      (pullback.snd ι (pullback.fst pr t) ≫ pullback.snd pr t) = 𝟙 T := by
    rw [he, pullback.lift_snd_assoc, hn, pullback.lift_snd_assoc, hm, pullback.lift_snd]
  have : IsIso e := isIso_of_isPullback_of_section Δ' (ι ≫ pr) hdiag' t sq e he₁ he₂
  -- the hypothesis, read on `U ×_P W`
  have hP := hc.cap_flatPullbackChow t (pullback.fst ι (pullback.fst pr t))
    (pullback.snd ι (pullback.fst pr t) ≫ pullback.snd pr t) sq hvr hvs e he₁ he₂ k α
  -- the flat pullback `β` of `α` to `W`, and its restriction to `U ×_P W`
  set β := flatPullbackChow C (pullback.fst pr t ≫ (pullback.fst g g ≫ sY)) (t ≫ sY)
    (pullback.snd pr t) (pullbackSnd_comp_structureMorphism hpr t) d
    (relativeDimension_pullbackSnd pr hr t) k (flatPullbackDescends C _ _ _ _ _ _ _) α with hβ
  have h1 := diagonalGysinClass_cap_heq C sY g hd (pullback.fst pr t) (k + d) β
  have h2 : (diagonalOpenPullbackClass C sY g).cap (pullback.fst pr t) (k + d) β ≍
      flatPullbackChow C (pullback.fst ι (pullback.fst pr t) ≫ (ι ≫ (pullback.fst g g ≫ sY)))
        (t ≫ sY) (pullback.snd ι (pullback.fst pr t) ≫ pullback.snd pr t) hvs d hvr k
        (flatPullbackDescends C _ _ _ _ _ _ _) α :=
    (IsBivariantFlatPullback.cap_heq (hS1 := flatPullbackDescends C)
      (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C _ _ ι rfl 0 _)
        (pullback.fst pr t) (k + d) β).trans
      ((flatPullbackChow_comp_heq C (flatPullbackDescends C) _ _ _
        (pullback.snd ι (pullback.fst pr t)) (pullback.snd pr t) _ _ 0 d _ _ k α).trans
        (flatPullbackChow_heq_congr C _ _ _ _ _ hvs rfl (zero_add d) _ hvr rfl _ _ α α HEq.rfl))
  have h3 := (BivariantClass.cap_heq (diagonalClosedFactorClass C sY g hd)
    (pullback.fst ι (pullback.fst pr t)) (by simp) h2).trans
      ((heq_of_eq hP).trans (chowGroupDegreeEquiv_heq C _ _ _))
  -- the composite of the three identifications is the identity of `T`
  have hcomp : e ≫ (((pullbackRightPullbackFstIso ι (pullback.fst pr t) Δ').hom ≫
      (pullback.congrHom hΔ rfl).hom) ≫
        (sectionPullbackIso (pullback.diagonal g) pr hdiag t).hom) = 𝟙 T := by
    have h4 : (pullback.congrHom hΔ rfl).hom ≫
        pullback.snd (pullback.diagonal g) (pullback.fst pr t) =
          pullback.snd (Δ' ≫ ι) (pullback.fst pr t) := by
      simp [pullback.congrHom]
    rw [sectionPullbackIso_hom, Category.assoc, reassoc_of% h4,
      pullbackRightPullbackFstIso_hom_snd_assoc]
    simpa using he₂
  refine eq_of_heq ((chowPushforwardOfIso_heq_comp_of_comp_eq _ _ _ rfl _ _ rfl rfl (by simp) _ _
    h1).trans ?_)
  refine (chowPushforwardOfIso_heq_comp_of_comp_eq e _ _ rfl _ _ rfl rfl (by simp) _ _ h3).trans ?_
  rw [chowPushforwardOfIso_congr_apply C _ _ _ (𝟙 T) hcomp _ (Category.id_comp _),
    chowPushforwardOfIso_id]
  exact (chowGroupDegreeEquiv_heq C _ _ α).symm

end Stacks.Chow

end
