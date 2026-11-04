module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessNormalSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction

/-!
# The class `ι_* ∘ j^* ∘ C` on a fundamental class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : Z ⟶ X` be a
closed immersion of schemes locally of finite type over `S` with a virtual normal sheaf `𝒩`, and
let `ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ X)` be the class of the construction preceding Stacks 0FBK
(`Stacks.Chow.virtualNormalConeClass`). The proof of Stacks 0FBM evaluates it on a fundamental
class:

* `C ∩ [X]_n = [W_∞]_n` (`Stacks.Chow.gysinAtInfinityClass_cap_fundamentalChowClass`);
* its restriction to the open `C_ZX ⊆ W_∞` is `[C_ZX]_n`, as `dim_δ(W_∞) ≤ n`;
* hence `(ι_* ∘ j^* ∘ C) ∩ [X]_n = ι_*[C_ZX]_n`, and this is `[N]_n` when `ι` is an isomorphism,
  which is the case for the normal bundle of a regular immersion
  (`Stacks.Chow.VirtualNormalBundle.isIso_normalConeEmbedding_ofIsRegularImmersion`).

This file carries that out on every flat test scheme `T ⟶ X` of `δ`-dimension at most `n`, and
derives the dimension bound `dim_δ(Z) ≤ n - r` for a regular immersion of codimension `r` into a
scheme of `δ`-dimension at most `n`.

## Main results

* `Stacks.Chow.virtualNormalConeClass_cap_fundamentalChowClass` —
  `(ι_* ∘ j^* ∘ C) ∩ [T]_n = ι_*[C_ZX ×_X T]_n` for `T ⟶ X` flat with `dim_δ(T) ≤ n`.
* `Stacks.Chow.virtualNormalConeClass_cap_fundamentalChowClass_of_isIso` — the same is
  `[N ×_X T]_n` when `ι : C_ZX ⟶ N` is an isomorphism.
* `Stacks.Chow.schemeDeltaDimension_le_sub_of_isRegularImmersion` — for a regular closed immersion
  `Z ⟶ X` whose conormal sheaf has constant rank `r`, `dim_δ(X) ≤ n` implies `dim_δ(Z) ≤ n - r`.
* `Stacks.Chow.virtualNormalGysinClass_cap_fundamentalChowClass_of_isRegularImmersion` — the case
  `Y = X` of Stacks 0FBM at vanishing excess: for a regular closed immersion `i : Z ⟶ X` of
  codimension `r` and a virtual normal sheaf `𝒩` of rank `r` whose surjection onto the conormal
  sheaf is an isomorphism, `c(Z ⟶ X, 𝒩) ∩ [X]_n = [Z]_{n - r}` when `dim_δ(X) ≤ n`.

## References

* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [Stacks Project, Tag 02R8](https://stacks.math.columbia.edu/tag/02R8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Fundamental classes of two chosen pullbacks along equal morphisms, in degrees that are equal,
are heterogeneously equal. -/
theorem fundamentalChowClass_pullback_heq (C : ChowSituation.{u}) {A B T : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] {f f' : A ⟶ B} (hff' : f = f') (t : T ⟶ B)
    [LocallyOfFiniteType t] {k l : ℤ} (hkl : k = l) :
    fundamentalChowClass C (pullback.fst f t ≫ sA) k ≍
      fundamentalChowClass C (pullback.fst f' t ≫ sA) l := by
  subst hff'
  subst hkl
  rfl

/-- **The restriction of a fundamental class along an open immersion is the fundamental class**,
in the form a degree-zero cap operation of Stacks 0B78 along an open immersion produces it. -/
theorem flatPullbackBivariantCap_fundamentalChowClass_of_isOpenImmersion (C : ChowSituation.{u})
    {U V T : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sV : V ⟶ C.S)
    [LocallyOfFiniteType sV] (v : U ⟶ V) [IsOpenImmersion v] (hv : v ≫ sV = sU) (g : T ⟶ V)
    [LocallyOfFiniteType g] (k : ℤ) (hdim : schemeDeltaDimension C (g ≫ sV) ≤ (k : EInt)) :
    flatPullbackBivariantCap C sU sV v hv 0 (relativeDimension_of_isOpenImmersion v)
        (flatPullbackDescends C) g k (fundamentalChowClass C (g ≫ sV) k) =
      fundamentalChowClass C (pullback.fst v g ≫ sU) (k - -((0 : ℕ) : ℤ)) := by
  refine eq_of_heq ((flatPullbackBivariantCap_heq_chowGroupRestrict C sU sV v hv g k _).trans ?_)
  rw [chowGroupRestrict_fundamentalChowClass C _ _ _ _ k hdim]
  exact fundamentalChowClass_heq C _ (by simp)

section Cone

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ)

/-- **`j^* (C ∩ [T]_n) = [C_ZX ×_X T]_n`.** The composite `j^* ∘ C ∈ A⁰(C_ZX ⟶ X)` of the class at
infinity of Stacks 0F9J with flat pullback along the open immersion `j : C_ZX ⟶ W_∞` of Stacks
0FBH carries the fundamental class of a flat test scheme `T ⟶ X` with `dim_δ(T) ≤ n` to the
fundamental class of `C_ZX ×_X T`. -/
theorem normalConeAtInfinityClass_cap_fundamentalChowClass {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] [Flat t] (n : ℤ) (hT : schemeDeltaDimension C (t ≫ sX) ≤ (n : EInt)) :
    haveI := locallyOfFiniteType_normalConeToBase C sX i
    (bivariantCompositeOfInvertible C (Stacks.Conormal.normalConeToBase i ≫ sZ)
        (modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫
          sX) sX (normalConeToFibreAtInfinity i sX)
        (modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX))
        (normalConeToFibreAtInfinity_comp_projection_comp C sZ sX i hi) rfl (-((0 : ℕ) : ℤ)) 0
        (flatPullbackBivariantClassOfIsOpenImmersionOfInvertible C
          (Stacks.Conormal.normalConeToBase i ≫ sZ)
          (modificationProjectionAtInfinity sX
            (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫ sX)
          (normalConeToFibreAtInfinity i sX)
          (normalConeToFibreAtInfinity_comp_projection_comp C sZ sX i hi))
        (gysinAtInfinityClass C sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
          (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX))).cap t n
        (fundamentalChowClass C (t ≫ sX) n) =
      fundamentalChowClass C (pullback.fst (normalConeToFibreAtInfinity i sX ≫
          modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct i.ker sX))
          t ≫ Stacks.Conormal.normalConeToBase i ≫ sZ) (n - (-((0 : ℕ) : ℤ) + 0)) := by
  have := locallyOfFiniteType_normalConeToBase C sX i
  set b := blowupAtInfinityToProjectiveLineProduct i.ker sX
  have hA := isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX
  have hcart := isEffectiveCartierDivisor_ker_modificationInfinityBaseChange_blowupAtInfinity
    i.ker sX t
  have hC := gysinAtInfinityClass_cap_fundamentalChowClass C sX b hA t n hT hcart
  have hdim := schemeDeltaDimension_modificationInfinityBaseChange_le C sX b hA t n hT hcart
  rw [bivariantCompositeOfInvertible, bivariantComposite_cap, bivariantCompositeCap_apply, hC,
    flatPullbackBivariantClassOfIsOpenImmersionOfInvertible,
    flatPullbackBivariantClassOfIsOpenImmersion_cap,
    flatPullbackBivariantCap_fundamentalChowClass_of_isOpenImmersion C _ _ _ _ _ (n - 0)
      (by rw [sub_zero]; exact hdim),
    properChowPushforward_eq_chowPushforwardOfIso, chowPushforwardOfIso_fundamentalChowClass,
    chowGroupDegreeEquiv_fundamentalChowClass]

/-- **`(ι_* ∘ j^* ∘ C) ∩ [T]_n = ι_*[C_ZX ×_X T]_n`.** For a flat test scheme `T ⟶ X` with
`dim_δ(T) ≤ n`, the class `ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ X)` of the construction preceding Stacks 0FBK
caps the fundamental class of `T` to the pushforward, along the base change of the closed
immersion `ι : C_ZX ⟶ N`, of the fundamental class of `C_ZX ×_X T`. This is the computation of
the proof of Stacks 0FBM. -/
theorem virtualNormalConeClass_cap_fundamentalChowClass (𝒩 : VirtualNormalBundle i)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] [Flat t] (n : ℤ)
    (hT : schemeDeltaDimension C (t ≫ sX) ≤ (n : EInt)) :
    haveI := locallyOfFiniteType_normalConeToBase C sX i
    (virtualNormalConeClass C sZ sX i hi 𝒩).cap t n (fundamentalChowClass C (t ≫ sX) n) =
      properChowPushforward C
        (pullback.fst (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) t ≫
          Stacks.Conormal.normalConeToBase i ≫ sZ)
        (pullback.fst (𝒩.projection ≫ i) t ≫ 𝒩.projection ≫ sZ)
        (bivariantPushforwardBaseChange 𝒩.normalConeEmbedding (𝒩.projection ≫ i) t)
        (bivariantPushforwardBaseChange_comp_structure
          (by rw [𝒩.normalConeEmbedding_projection_assoc]) (𝒩.projection ≫ i) t) (n - 0)
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (pullback.fst (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) t ≫
          Stacks.Conormal.normalConeToBase i ≫ sZ) (n - 0)) := by
  have := locallyOfFiniteType_normalConeToBase C sX i
  rw [virtualNormalConeClass, bivariantProperPushforwardOfInvertible_cap,
    bivariantProperPushforwardCap_apply]
  congr 1
  refine eq_of_heq ((BivariantClass.copy_cap C _ _ _ _ _ _ _ _ t n _).trans ?_)
  rw [normalConeAtInfinityClass_cap_fundamentalChowClass C sZ sX i hi t n hT]
  exact fundamentalChowClass_pullback_heq C _
    (by rw [normalConeToFibreAtInfinity_comp_projection, 𝒩.normalConeEmbedding_projection_assoc])
    t (by simp)

/-- **`(ι_* ∘ j^* ∘ C) ∩ [T]_n = [N ×_X T]_n` when `ι : C_ZX ⟶ N` is an isomorphism**, for a flat
test scheme `T ⟶ X` with `dim_δ(T) ≤ n`. This is the case of the normal bundle of a regular
immersion. -/
theorem virtualNormalConeClass_cap_fundamentalChowClass_of_isIso (𝒩 : VirtualNormalBundle i)
    [IsIso 𝒩.normalConeEmbedding] {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] [Flat t]
    (n : ℤ) (hT : schemeDeltaDimension C (t ≫ sX) ≤ (n : EInt)) :
    (virtualNormalConeClass C sZ sX i hi 𝒩).cap t n (fundamentalChowClass C (t ≫ sX) n) =
      fundamentalChowClass C (pullback.fst (𝒩.projection ≫ i) t ≫ 𝒩.projection ≫ sZ) (n - 0) := by
  have := locallyOfFiniteType_normalConeToBase C sX i
  rw [virtualNormalConeClass_cap_fundamentalChowClass C sZ sX i hi 𝒩 t n hT]
  have : IsIso (bivariantPushforwardBaseChange 𝒩.normalConeEmbedding (𝒩.projection ≫ i) t) := by
    unfold bivariantPushforwardBaseChange
    infer_instance
  rw [properChowPushforward_eq_chowPushforwardOfIso, chowPushforwardOfIso_fundamentalChowClass]

end Cone

/-! ### The dimension of a regular closed subscheme -/

/-- **`dim_δ(Z) ≤ n - r` for a regular closed immersion of codimension `r`.** Let `i : Z ⟶ X` be a
regular closed immersion of schemes locally of finite type over the base whose conormal sheaf has
constant rank `r`, and let `dim_δ(X) ≤ n`. Then `dim_δ(Z) ≤ n - r`.

The normal cone `C_ZX` is an open subscheme of the fibre at infinity `W_∞` of the blowup of
Stacks 0FBG (Stacks 0FBH), and `dim_δ(W_∞) ≤ n` because `W_∞` is an effective Cartier divisor on
`W`, whose generic points lie over `𝐀¹_X`; so `dim_δ(C_ZX) ≤ n`. Since `i` is regular, `C_ZX` is
the vector bundle of the conormal sheaf (Stacks 063M), flat of relative dimension `r` and
surjective over `Z`, so `dim_δ(Z) = dim_δ(C_ZX) - r` (Stacks 02R8). -/
theorem schemeDeltaDimension_le_sub_of_isRegularImmersion (C : ChowSituation.{u})
    {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ)
    (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r]
    (n : ℤ) (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    schemeDeltaDimension C sZ ≤ ((n - (r : ℤ) : ℤ) : EInt) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := locallyOfFiniteType_normalConeToBase C sX i
  set 𝒩 := VirtualNormalBundle.ofIsRegularImmersion i hreg
  set b := blowupAtInfinityToProjectiveLineProduct i.ker sX
  have hA := isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker sX
  -- `dim_δ(W_∞) ≤ n`
  have hW : schemeDeltaDimension C (modificationProjectionAtInfinity sX b ≫ sX) ≤ (n : EInt) := by
    have h := schemeDeltaDimension_modificationInfinityBaseChange_le C sX b hA (𝟙 X) n
      (by simpa using hX)
      (isEffectiveCartierDivisor_ker_modificationInfinityBaseChange_blowupAtInfinity i.ker sX (𝟙 X))
    exact (schemeDeltaDimension_comp_iso C
      (asIso (pullback.fst (modificationProjectionAtInfinity sX b) (𝟙 X)))
      (modificationProjectionAtInfinity sX b ≫ sX)).ge.trans h
  -- `dim_δ(C_ZX) ≤ n`
  have hcone : schemeDeltaDimension C (Stacks.Conormal.normalConeToBase i ≫ sZ) ≤ (n : EInt) := by
    have h : schemeDeltaDimension C (𝟙 _ ≫ Stacks.Conormal.normalConeToBase i ≫ sZ) ≤
        (n : EInt) := by
      refine schemeDeltaDimension_le_of_forall_relativeDimension_le C _ (𝟙 _) fun w => ?_
      rw [← normalConeToFibreAtInfinity_comp_projection_comp C sZ sX i hi,
        relativeDimension_comp_isOpenImmersion]
      exact relativeDimension_le_of_schemeDeltaDimension_le' C _ hW _
    simpa using h
  -- `dim_δ(N) ≤ n`
  have : IsIso 𝒩.normalConeEmbedding :=
    VirtualNormalBundle.isIso_normalConeEmbedding_ofIsRegularImmersion hreg
  have hN : schemeDeltaDimension C (𝒩.projection ≫ sZ) ≤ (n : EInt) := by
    rw [← schemeDeltaDimension_comp_iso C (asIso 𝒩.normalConeEmbedding)]
    simpa only [asIso_hom, 𝒩.normalConeEmbedding_projection_assoc] using hcone
  have := 𝒩.flat_projection_of_rank r
  exact schemeDeltaDimension_le_sub_of_flat_of_surjective C sZ _ 𝒩.projection rfl r
    (𝒩.relativeDimension_projection_of_rank r) (𝒩.surjective_projection r) hN

/-! ### Stacks 0FBM for a regular immersion at vanishing excess, on `[X]_n` -/

/-- **Stacks 0FBM at vanishing excess, on the fundamental class of `X`.** Let `i : Z ⟶ X` be a
regular closed immersion of schemes locally of finite type over the base whose conormal sheaf has
constant rank `r`, let `𝒩` be a virtual normal sheaf for `i` of rank `r` whose surjection
`σ : 𝒩^∨ ⟶ 𝒞_{Z/X}` is an isomorphism — for instance the normal bundle `𝒞_{Z/X}^∨` with the
reflexivity isomorphism, `Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion` — and let
`dim_δ(X) ≤ n`. Then

  `c(Z ⟶ X, 𝒩) ∩ [X]_n = [Z]_{n - r}`

in `A_{n-r}(Z)`, both sides read on the test scheme `𝟙 X`, for the class of Stacks 0FBK.

This is the computation of the proof of Stacks 0FBM: `(ι_* ∘ j^* ∘ C) ∩ [X]_n = [N]_n` because
`ι : C_ZX ⟶ N` is an isomorphism for a regular immersion and an isomorphism `σ`
(`Stacks.Chow.VirtualNormalBundle.isIso_normalConeEmbedding`,
`Stacks.Chow.virtualNormalConeClass_cap_fundamentalChowClass_of_isIso`), `p^*[Z]_{n-r} = [N]_n`
because `dim_δ(Z) ≤ n - r` (`Stacks.Chow.schemeDeltaDimension_le_sub_of_isRegularImmersion`), and
`p^*` is injective. -/
theorem virtualNormalGysinClass_cap_fundamentalChowClass_of_isRegularImmersion
    (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ sX = sZ) (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i)
    (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r]
    (𝒩 : VirtualNormalBundle i) [IsIso 𝒩.surjection]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    (n : ℤ) (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    (virtualNormalBundleClass C sZ sX i hi 𝒩 r).cap (𝟙 X) n
        (fundamentalChowClass C (𝟙 X ≫ sX) n) =
      fundamentalChowClass C (pullback.fst i (𝟙 X) ≫ sZ) (n - (r : ℤ)) := by
  have : IsIso 𝒩.normalConeEmbedding := 𝒩.isIso_normalConeEmbedding hreg
  have hX' : schemeDeltaDimension C (𝟙 X ≫ sX) ≤ (n : EInt) := by simpa using hX
  have hZ := schemeDeltaDimension_le_sub_of_isRegularImmersion C sZ sX i hi hreg r n hX
  have hZ' : schemeDeltaDimension C (pullback.fst i (𝟙 X) ≫ sZ) ≤ ((n - (r : ℤ) : ℤ) : EInt) :=
    (schemeDeltaDimension_comp_iso C (asIso (pullback.fst i (𝟙 X))) sZ).le.trans hZ
  have := 𝒩.flat_projection_of_rank r
  refine (bijective_bundleFlatPullbackChow C sZ i 𝒩 r (𝟙 X) (n - (r : ℤ))).1 ?_
  have hcap := bundleFlatPullbackChow_virtualNormalBundleClass_cap C sZ sX i hi 𝒩 r (𝟙 X) n
    (fundamentalChowClass C (𝟙 X ≫ sX) n)
  rw [virtualNormalConeClass_cap_fundamentalChowClass_of_isIso C sZ sX i hi 𝒩 (𝟙 X) n hX'] at hcap
  refine eq_of_heq (hcap.trans ?_)
  rw [bundleFlatPullbackChow_fundamentalChowClass C sZ (𝒩.projection ≫ sZ) i 𝒩.projection rfl r
    (𝒩.flat_projection_of_rank r) (𝒩.relativeDimension_projection_of_rank r)
    (flatPullbackDescends C) (𝟙 X) (n - (r : ℤ)) hZ']
  exact fundamentalChowClass_heq C _ (by ring)

end Stacks.Chow

end
