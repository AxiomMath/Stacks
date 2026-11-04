module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction
public import StacksCore.Tactic.StacksAttribute

/-!
# The division defining the class of a virtual normal sheaf, on fundamental classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed immersion carrying a virtual normal sheaf `𝒩`
of constant rank `m` in the sense of Stacks 0FBQ, with vector bundle `p : N ⟶ Z`, and let
`c(Z ⟶ X, 𝒩)` be the class of Stacks 0FBK: the unique class with `p^* ∘ c = ι_* ∘ j^* ∘ C`
(`Stacks.Chow.IsVirtualNormalBundleClass`). Since `p^*` is injective (Stacks 02TY,
`Stacks.Chow.bijective_bundleFlatPullbackChow`), `c ∩ α` is the unique `β` with
`p^* β = (ι_* ∘ j^* ∘ C) ∩ α`. This module records that division as a rule for computing `c ∩ α`,
and its value on a fundamental class, through
`Stacks.Chow.bundleFlatPullbackChow_fundamentalChowClass` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection`, the flat pullback of a
fundamental class being a fundamental class. These are the steps of the proofs of
Stacks 0FBL and Stacks 0FBM which divide by `p^*`; the excess intersection formula itself is in
`Stacks.Chow.virtualNormalBundleClass_cap_fundamentalChowClass` and
`Stacks.Chow.virtualNormalBundleClass_cap_fundamentalChowClass_excess`.

## Main results

* `Stacks.Chow.eq_of_isVirtualNormalBundleClass_cap` — the division that defines the class: a
  class satisfying the relation of Stacks 0FBK takes a prescribed value on a given class as soon as
  the flat pullback of the candidate value agrees with the cap product of `ι_* ∘ j^* ∘ C`.
* `Stacks.Chow.cap_fundamentalChowClass_of_isVirtualNormalBundleClass` — the same on a fundamental
  class: if `(ι_* ∘ j^* ∘ C) ∩ [Y]_n = [N ×_X Y]_n` and `dim_δ(Z ×_X Y) ≤ n - m`, then
  `c ∩ [Y]_n = [Z ×_X Y]_{n - m}`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The division by `p^*` -/

section Division

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z X : Scheme.{u}}
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
  (𝒩 : VirtualNormalBundle i) (m : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle m]

/-- **The division that defines `c(Z ⟶ X, 𝒩)`, evaluated.** A bivariant class satisfying the
relation `p^* ∘ c = ι_* ∘ j^* ∘ C` of Stacks 0FBK takes a prescribed value on a given Chow class:
if the flat pullback of a candidate `β` agrees with `(ι_* ∘ j^* ∘ C) ∩ α`, then `c ∩ α = β`.

This is the source's "`c ∩ α` is the unique `β` with `p^* β = ι_* j^* (C ∩ α)`", read as a rule
for computing `c ∩ α`; the uniqueness is Stacks 02TY. -/
theorem eq_of_isVirtualNormalBundleClass_cap {c : BivariantClass C G sZ sX i hi (m : ℤ)}
    (hc : IsVirtualNormalBundleClass C sZ sX i hi G 𝒩 m c)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) (β : chowGroup C (pullback.fst i g ≫ sZ) (k - (m : ℤ)))
    (hβ : bundleFlatPullback C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl m
        (𝒩.flat_projection_of_rank m) (𝒩.relativeDimension_projection_of_rank m)
        (flatPullbackDescends C) g k β =
      (virtualNormalConeClass C sZ sX i hi 𝒩).cap g k α) :
    c.cap g k α = β := by
  have h := (hc g k α).trans hβ.symm
  rw [bundleFlatPullback_apply, bundleFlatPullback_apply] at h
  exact (bijective_bundleFlatPullbackChow C sZ i 𝒩 m g (k - (m : ℤ))).1
    ((chowGroupDegreeEquiv C _ _).injective h)

/-- **The division that defines `c(Z ⟶ X, 𝒩)`, on a fundamental class.** Let `c` be a bivariant
class of degree `m` satisfying the relation `p^* ∘ c = ι_* ∘ j^* ∘ C` of Stacks 0FBK, and let
`g : Y ⟶ X` be locally of finite type. If `(ι_* ∘ j^* ∘ C) ∩ [Y]_n` is the fundamental class of
`N ×_X Y` and `dim_δ(Z ×_X Y) ≤ n - m`, then

  `c ∩ [Y]_n = [Z ×_X Y]_{n - m}`

in `A_{n-m}(Z ×_X Y)`: the flat pullback of the right-hand side is `[N ×_X Y]_n` by
`Stacks.Chow.bundleFlatPullbackChow_fundamentalChowClass`, and `p^*` is injective. -/
theorem cap_fundamentalChowClass_of_isVirtualNormalBundleClass
    {c : BivariantClass C G sZ sX i hi (m : ℤ)}
    (hc : IsVirtualNormalBundleClass C sZ sX i hi G 𝒩 m c)
    {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] (n : ℤ)
    (hdim : schemeDeltaDimension C (pullback.fst i g ≫ sZ) ≤ ((n - (m : ℤ) : ℤ) : EInt))
    (hcone : chowGroupDegreeEquiv C (pullback.fst (𝒩.projection ≫ i) g ≫ 𝒩.projection ≫ sZ)
        (by omega : n - (0 : ℤ) = (n - (m : ℤ)) + (m : ℤ))
        ((virtualNormalConeClass C sZ sX i hi 𝒩).cap g n (fundamentalChowClass C (g ≫ sX) n)) =
      fundamentalChowClass C (pullback.fst (𝒩.projection ≫ i) g ≫ 𝒩.projection ≫ sZ)
        ((n - (m : ℤ)) + (m : ℤ))) :
    c.cap g n (fundamentalChowClass C (g ≫ sX) n) =
      fundamentalChowClass C (pullback.fst i g ≫ sZ) (n - (m : ℤ)) := by
  refine eq_of_isVirtualNormalBundleClass_cap C G sZ sX i hi 𝒩 m hc g n _ _ ?_
  rw [bundleFlatPullback_apply,
    bundleFlatPullbackChow_fundamentalChowClass C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl m
      (𝒩.flat_projection_of_rank m) (𝒩.relativeDimension_projection_of_rank m)
      (flatPullbackDescends C) g (n - (m : ℤ)) hdim]
  refine (chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).2 ?_
  exact ((chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).1 hcone).symm

end Division

end Stacks.Chow

end
