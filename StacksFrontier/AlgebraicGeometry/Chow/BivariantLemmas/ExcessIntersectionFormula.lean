module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalConeFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundleClass

/-!
# The excess intersection formula

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S`, let `i : Z ⟶ X` be a closed immersion with a virtual normal sheaf `𝒩` in the
sense of Stacks 0FBQ, and let `g : Y ⟶ X` be locally of finite type such that the base change
`Z ×_X Y ⟶ Y` is a regular closed immersion whose conormal sheaf `𝒞_{Z ×_X Y / Y}` has constant
rank `r`. The surjection of Stacks 0FBQ pulls back to a surjection
`𝒩^∨|_{Z ×_X Y} ⟶ 𝒞_{Z ×_X Y / Y}` (Stacks 0FBJ), and its kernel is `ℰ^∨` for the *excess normal
sheaf* `ℰ`:

  `0 ⟶ ℰ^∨ ⟶ 𝒩^∨|_{Z ×_X Y} ⟶ 𝒞_{Z ×_X Y / Y} ⟶ 0`.

**Stacks 0FBM** asserts that if `dim_δ(Y) = n` then

  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_top(ℰ) ∩ [Z ×_X Y]_{n - r}`

in `CH_*(Z ×_X Y)`.

The proof is the source's. By the base-change clause of Stacks 0FBK
(`Stacks.Chow.virtualNormalGysinClass_cap_baseChange`) the left-hand side is computed on `Y`
itself, for the class `c(Z ×_X Y ⟶ Y, 𝒩|_{Z ×_X Y})` on the test scheme `𝟙 Y`. When `𝒩` has rank
`r` the surjection `𝒩^∨|_{Z ×_X Y} ⟶ 𝒞_{Z ×_X Y / Y}` is an epimorphism of finite locally free
modules of the same rank, hence an isomorphism, and
`Stacks.Chow.virtualNormalGysinClass_cap_fundamentalChowClass_of_isRegularImmersion` evaluates the
class on `[Y]_n`: the normal cone is the vector bundle (Stacks 063M), `C ∩ [Y]_n = [W_∞]_n`, and
`p^*[Z ×_X Y]_{n-r} = [C_{Z ×_X Y} Y]_n`. In general Stacks 0FBL
(`Stacks.Chow.virtualNormalBundleClass_cap_eq_chernCap_comp`), applied to the excess sequence
`0 ⟶ 𝒞^∨ ⟶ 𝒩|_{Z ×_X Y} ⟶ ℰ ⟶ 0`, reduces to that case.

## Main results

* `Stacks.Chow.isIso_of_epi_of_isFiniteLocallyFreeOfRank` — an epimorphism of finite locally free
  modules of the same constant rank is an isomorphism.
* `Stacks.Chow.VirtualNormalBundle.isIso_surjection_of_isFiniteLocallyFreeOfRank` and
  `Stacks.Chow.VirtualNormalBundle.isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add` — the
  surjection onto a conormal sheaf of the same rank is an isomorphism, and the excess normal sheaf
  of a virtual normal sheaf of rank `r + e` over a conormal sheaf of rank `r` has rank `e`.
* `Stacks.Chow.virtualNormalGysinClass_cap_eq_chowPushforwardOfIso_cap_id` — the cap product of
  `c(Z ⟶ X, 𝒩)` on a test scheme `Y ⟶ X` is that of `c(Z' ⟶ Y, 𝒩|_{Z'})` on `𝟙 Y`, for a
  cartesian square `Z' = Z ×_X Y`.
* `Stacks.Chow.virtualNormalBundleClass_cap_fundamentalChowClass` — **Stacks 0FBM at vanishing
  excess**: `c(Z ⟶ X, 𝒩) ∩ [Y]_n = [Z ×_X Y]_{n - r}` when `𝒩` has rank `r`.
* `Stacks.Chow.virtualNormalBundleClass_cap_fundamentalChowClass_excess` — **Stacks 0FBM at
  constant rank**: `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_e(ℰ) ∩ [Z ×_X Y]_{n - r}` when `𝒩` has rank
  `r + e`. The formula for `𝒩` of arbitrary rank is
  `Stacks.Chow.completedVirtualNormalGysinCap_fundamentalChowClass_excess`.

## Implementation notes

The fibre product `Z ×_X Y` is given by an arbitrary cartesian square `Z' = Z ×_X Y`, with
`i' : Z' ⟶ Y` the regular closed immersion; the conclusions are stated in the Chow group of the
chosen fibre product, the one the cap operation of a bivariant class lands in.

The ranks are taken constant: the conormal sheaf of `Z' ⟶ Y` has rank `r`, as in the source, and
`𝒩` has rank `r + e`, so that the excess normal sheaf has rank `e` and `c_top(ℰ)` is the Chern
class `c_e(ℰ)` of Stacks 0B7H (`Stacks.Chow.GenuineChern.chernCap` at `Fin.last e`), and both
sides lie in `CH_{n - (r + e)}`. When `Z'` is nonempty the surjection
`𝒩^∨|_{Z'} ⟶ 𝒞_{Z'/Y}` forces the rank of `𝒩` to be at least `r`, so it is of this form. When
`Z'` is empty and `𝒩` has rank less than `r`, the two sides of the source's formula lie in the
Chow groups of the empty scheme in the two different degrees `n - rank 𝒩` and `n - r`, both zero;
that degenerate case is not an equation in one group and is not stated. The hypothesis
`dim_δ(Y) = n` of the source enters only as `dim_δ(Y) ≤ n`.

## References

* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 063M](https://stacks.math.columbia.edu/tag/063M)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

/-! ### Epimorphisms of finite locally free modules of the same rank -/

/-- **An epimorphism of finite locally free modules of the same constant rank is an
isomorphism**: its kernel is finite locally free of rank `r - r = 0`, hence zero. -/
theorem isIso_of_epi_of_isFiniteLocallyFreeOfRank {P : Scheme.{u}} {M L : P.Modules}
    (q : M ⟶ L) [Epi q] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L r] : IsIso q := by
  have hk := Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi q
    inferInstance r r inferInstance inferInstance
  rw [Nat.sub_self] at hk
  have : Mono q :=
    Preadditive.mono_of_isZero_kernel q (@isZero_of_isFiniteLocallyFreeOfRank_zero _ _ hk)
  exact isIso_of_mono_of_epi q

/-- **The surjection of a virtual normal sheaf of rank `r` onto a conormal sheaf of rank `r` is an
isomorphism**: the excess normal sheaf vanishes. -/
theorem VirtualNormalBundle.isIso_surjection_of_isFiniteLocallyFreeOfRank {Z X : Scheme.{u}}
    {i : Z ⟶ X} [IsImmersion i] (𝒩 : VirtualNormalBundle i) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r] :
    IsIso 𝒩.surjection :=
  isIso_of_epi_of_isFiniteLocallyFreeOfRank 𝒩.conormalSurjection r

/-- **The excess normal sheaf has rank `e`** when the virtual normal sheaf has rank `r + e` and the
conormal sheaf has rank `r`. -/
theorem VirtualNormalBundle.isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add {Z X : Scheme.{u}}
    {i : Z ⟶ X} [IsImmersion i] (𝒩 : VirtualNormalBundle i) (r e : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle (r + e)]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i) r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.excessNormalSheaf e :=
  Nat.add_sub_cancel_left r e ▸ 𝒩.isFiniteLocallyFreeOfRank_excessNormalSheaf (r + e) r

/-! ### Reduction to the test scheme `𝟙 Y` -/

/-- The base change of a virtual normal sheaf of constant rank has the same constant rank. -/
private instance isFiniteLocallyFreeOfRank_baseChange_bundle {Z X Z' Y : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] (𝒩 : VirtualNormalBundle i) (m : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle m] {g : Y ⟶ X} {i' : Z' ⟶ Y}
    [IsClosedImmersion i'] {g' : Z' ⟶ Z} (sq : IsPullback i' g' g i) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.baseChange i i' g' g sq).bundle m :=
  isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle m inferInstance

section Reduction

variable (C : ChowSituation.{u}) {Z X Z' Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) (𝒩 : VirtualNormalBundle i) (m : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle m]

/-- The identification `Z' ×_Y Y ≅ Z ×_X Y` of the base change of `Z' ⟶ Y` along `𝟙 Y` with the
chosen fibre product, for a cartesian square `Z' = Z ×_X Y`. -/
abbrev subschemeIdentityTestIso {i : Z ⟶ X} {g : Y ⟶ X} {i' : Z' ⟶ Y} {g' : Z' ⟶ Z}
    (sq : IsPullback i' g' g i) : pullback i' (𝟙 Y) ⟶ pullback i g :=
  pullback.fst i' (𝟙 Y) ≫ sq.flip.isoPullback.hom

/-- The morphism `subschemeIdentityTestIso sq : Z' ×_Y Y ⟶ Z ×_X Y` is an isomorphism. -/
instance {i : Z ⟶ X} {g : Y ⟶ X} {i' : Z' ⟶ Y} {g' : Z' ⟶ Z} (sq : IsPullback i' g' g i) :
    IsIso (subschemeIdentityTestIso sq) := by
  unfold subschemeIdentityTestIso
  infer_instance

omit [LocallyOfFiniteType sX] in
/-- The identification `Z' ≅ Z ×_X Y` of a cartesian square is one over the base. -/
theorem isoPullback_hom_comp_structureMorphism {i : Z ⟶ X} {g : Y ⟶ X} {i' : Z' ⟶ Y}
    {g' : Z' ⟶ Z} (sq : IsPullback i' g' g i) (hi : i ≫ sX = sZ) (sZ' : Z' ⟶ C.S)
    (hi' : i' ≫ (g ≫ sX) = sZ') :
    sq.flip.isoPullback.hom ≫ (pullback.fst i g ≫ sZ) = sZ' := by
  subst hi hi'
  simp [sq.w_assoc]

omit [LocallyOfFiniteType sX] in
/-- The identification `Z' ×_Y Y ≅ Z ×_X Y` is one over the base. -/
theorem subschemeIdentityTestIso_comp_structureMorphism {i : Z ⟶ X} {g : Y ⟶ X} {i' : Z' ⟶ Y}
    {g' : Z' ⟶ Z} (sq : IsPullback i' g' g i) (hi : i ≫ sX = sZ) (sZ' : Z' ⟶ C.S)
    (hi' : i' ≫ (g ≫ sX) = sZ') :
    subschemeIdentityTestIso sq ≫ (pullback.fst i g ≫ sZ) = pullback.fst i' (𝟙 Y) ≫ sZ' := by
  subst hi hi'
  simp [subschemeIdentityTestIso, sq.w_assoc]

/-- The identification `Z ×_X (𝟙 Y ≫ g) ≅ Z' ×_Y Y` of the base-change clause of Stacks 0FBK at
the test scheme `𝟙 Y`, followed by `Z' ×_Y Y ≅ Z ×_X Y`, is the comparison of the fibre products
along `𝟙 Y ≫ g = g`. -/
theorem subschemeTestBaseChangeIso_hom_comp_subschemeIdentityTestIso {i : Z ⟶ X}
    [IsClosedImmersion i] {g : Y ⟶ X} {i' : Z' ⟶ Y} [IsClosedImmersion i'] {g' : Z' ⟶ Z}
    (sq : IsPullback i' g' g i) :
    (subschemeTestBaseChangeIso i i' g' g sq (𝟙 Y)).hom ≫ subschemeIdentityTestIso sq =
      (pullback.congrHom (rfl : i = i) (Category.id_comp g)).hom := by
  refine pullback.hom_ext ?_ ?_
  · simp [subschemeIdentityTestIso]
  · have h := subschemeTestBaseChangeIso_hom_snd i i' g' g sq (𝟙 Y)
    simp only [subschemeIdentityTestIso, Category.assoc, IsPullback.isoPullback_hom_snd,
      pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
    rw [pullback.condition, Category.comp_id, h]

/-- **Stacks 0FBK, base change, on a test scheme `Y ⟶ X`.** For a cartesian square
`Z' = Z ×_X Y` the cap product of `c(Z ⟶ X, 𝒩)` on the test scheme `g : Y ⟶ X` is the cap
product of `c(Z' ⟶ Y, 𝒩|_{Z'})` on the test scheme `𝟙 Y`, carried along `Z' ×_Y Y ≅ Z ×_X Y`. -/
theorem virtualNormalGysinClass_cap_eq_chowPushforwardOfIso_cap_id (g : Y ⟶ X)
    [LocallyOfFiniteType g] (i' : Z' ⟶ Y) [IsClosedImmersion i'] (g' : Z' ⟶ Z)
    (sq : IsPullback i' g' g i) (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
    (hi' : i' ≫ (g ≫ sX) = sZ') (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.baseChange i i' g' g sq).bundle
        m :=
      isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle m inferInstance
    (virtualNormalBundleClass C sZ sX i hi 𝒩 m).cap g k α =
      chowPushforwardOfIso C (pullback.fst i' (𝟙 Y) ≫ sZ') (pullback.fst i g ≫ sZ)
        (subschemeIdentityTestIso sq)
        (subschemeIdentityTestIso_comp_structureMorphism C sZ sX sq hi sZ' hi') (k - (m : ℤ))
        ((virtualNormalBundleClass C sZ' (g ≫ sX) i' hi' (𝒩.baseChange i i' g' g sq) m).cap
          (𝟙 Y) k (chowGroupCongr C (Category.id_comp (g ≫ sX)).symm k α)) := by
  rw [virtualNormalGysinClass_cap_baseChange C sZ sX i hi i' g' g sq 𝒩 m sZ' hi' (𝟙 Y) k,
    chowPushforwardOfIso_comp_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ _
      (subschemeTestBaseChangeIso_hom_comp_subschemeIdentityTestIso sq),
    chowGroupCongr_chowGroupCongr]
  exact (chowPushforwardOfIso_congrHom_cap C (gysinSystemOfInvertible C) sZ sX i hi (m : ℤ)
    (virtualNormalBundleClass C sZ sX i hi 𝒩 m) (Category.id_comp g) (by simp) k α _ rfl).symm

end Reduction

/-! ### Stacks 0FBM at vanishing excess -/

section Vanishing

variable (C : ChowSituation.{u}) {Z X Z' Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **Stacks 0FBM at vanishing excess.** Let `i : Z ⟶ X` be a closed immersion of schemes locally
of finite type over the base with a virtual normal sheaf `𝒩` of constant rank `r`, and let
`g : Y ⟶ X` be locally of finite type such that the base change `i' : Z ×_X Y ⟶ Y` is a regular
closed immersion whose conormal sheaf has constant rank `r`. Then the excess normal sheaf
vanishes, `c_top(ℰ) = 1`, and if `dim_δ(Y) ≤ n`

  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = [Z ×_X Y]_{n - r}`

in `A_{n-r}(Z ×_X Y)`, for every bivariant class satisfying the relation `p^* ∘ c = ι_* ∘ j^* ∘ C`
of Stacks 0FBK, in particular for `c(Z ⟶ X, 𝒩)`.

By the base-change clause of Stacks 0FBK the cap product is that of `c(Z ×_X Y ⟶ Y, 𝒩|_{Z ×_X Y})`
on `[Y]_n`; the surjection `𝒩^∨|_{Z ×_X Y} ⟶ 𝒞_{Z ×_X Y / Y}` is an isomorphism, both sides having
rank `r`; and `Stacks.Chow.virtualNormalGysinClass_cap_fundamentalChowClass_of_isRegularImmersion`
evaluates the class on `[Y]_n`. -/
theorem virtualNormalBundleClass_cap_fundamentalChowClass {G : GysinSystem C}
    {c : BivariantClass C G sZ sX i hi (r : ℤ)}
    (hc : IsVirtualNormalBundleClass C sZ sX i hi G 𝒩 r c)
    (g : Y ⟶ X) [LocallyOfFiniteType g] (i' : Z' ⟶ Y) [IsClosedImmersion i'] (g' : Z' ⟶ Z)
    (sq : IsPullback i' g' g i) (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
    (hi' : i' ≫ (g ≫ sX) = sZ') (hreg : IsRegularImmersion i')
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i') r]
    (n : ℤ) (hY : schemeDeltaDimension C (g ≫ sX) ≤ (n : EInt)) :
    c.cap g n (fundamentalChowClass C (g ≫ sX) n) =
      fundamentalChowClass C (pullback.fst i g ≫ sZ) (n - (r : ℤ)) := by
  have := (𝒩.baseChange i i' g' g sq).isIso_surjection_of_isFiniteLocallyFreeOfRank r
  rw [cap_eq_virtualNormalBundleClass_cap C sZ sX i hi 𝒩 r hc,
    virtualNormalGysinClass_cap_eq_chowPushforwardOfIso_cap_id C sZ sX i hi 𝒩 r g i' g' sq sZ'
      hi',
    chowGroupCongr_fundamentalChowClass,
    virtualNormalGysinClass_cap_fundamentalChowClass_of_isRegularImmersion C sZ' (g ≫ sX)
      i' hi' hreg r (𝒩.baseChange i i' g' g sq) n hY,
    chowPushforwardOfIso_fundamentalChowClass]

end Vanishing

/-! ### Stacks 0FBM -/

section Excess

variable (C : ChowSituation.{u}) {Z X Z' Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) (𝒩 : VirtualNormalBundle i) (r e : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle (r + e)]

/-- **Stacks 0FBM at constant rank, the excess intersection formula.** Let `i : Z ⟶ X` be a
closed immersion of schemes locally of finite type over the base with a virtual normal sheaf `𝒩` of
constant rank `r + e`, and let `g : Y ⟶ X` be locally of finite type such that the base change
`i' : Z' = Z ×_X Y ⟶ Y` is a regular closed immersion whose conormal sheaf `𝒞_{Z'/Y}` has constant
rank `r`. Let `ℰ` be the excess normal sheaf, `0 ⟶ ℰ^∨ ⟶ 𝒩^∨|_{Z'} ⟶ 𝒞_{Z'/Y} ⟶ 0`
(`Stacks.Chow.VirtualNormalBundle.excessNormalSheaf` of `𝒩|_{Z'}`), of rank `e`. If
`dim_δ(Y) ≤ n` then

  `c(Z ⟶ X, 𝒩) ∩ [Y]_n = c_top(ℰ) ∩ [Z']_{n - r}`

in `A_{n - (r + e)}(Z ×_X Y)`, with `c_top(ℰ) = c_e(ℰ)` and `Z'` identified with the chosen fibre
product; this holds for every bivariant class satisfying the relation `p^* ∘ c = ι_* ∘ j^* ∘ C` of
Stacks 0FBK, in particular for `c(Z ⟶ X, 𝒩)`.

The proof is the source's. By the base-change clause of Stacks 0FBK the cap product is that of
`c(Z' ⟶ Y, 𝒩|_{Z'})` on `[Y]_n`. The excess sequence `0 ⟶ 𝒞_{Z'/Y}^∨ ⟶ 𝒩|_{Z'} ⟶ ℰ ⟶ 0` dualizes
to a factorization of the surjection of `𝒩|_{Z'}` through the normal bundle `𝒞_{Z'/Y}^∨` of the
regular immersion, so Stacks 0FBL gives `c(Z' ⟶ Y, 𝒩|_{Z'}) ∩ [Y]_n =
c_e(ℰ) ∩ c(Z' ⟶ Y, 𝒞_{Z'/Y}^∨) ∩ [Y]_n`, and the last class is `[Z']_{n - r}` by
`Stacks.Chow.virtualNormalGysinClass_cap_fundamentalChowClass_of_isRegularImmersion`. -/
theorem virtualNormalBundleClass_cap_fundamentalChowClass_excess {G : GysinSystem C}
    {c : BivariantClass C G sZ sX i hi ((r + e : ℕ) : ℤ)}
    (hc : IsVirtualNormalBundleClass C sZ sX i hi G 𝒩 (r + e) c)
    (g : Y ⟶ X) [LocallyOfFiniteType g] (i' : Z' ⟶ Y) [IsClosedImmersion i'] (g' : Z' ⟶ Z)
    (sq : IsPullback i' g' g i) (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
    (hi' : i' ≫ (g ≫ sX) = sZ') (hreg : IsRegularImmersion i')
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (conormalModule i') r]
    (n : ℤ) (hY : schemeDeltaDimension C (g ≫ sX) ≤ (n : EInt)) :
    haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (𝒩.baseChange i i' g' g sq).bundle
        (r + e) :=
      isFiniteLocallyFreeOfRank_modulePullback g' 𝒩.bundle (r + e) inferInstance
    haveI := (𝒩.baseChange i i' g' g sq).isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add r e
    c.cap g n (fundamentalChowClass C (g ≫ sX) n) =
      chowPushforwardOfIso C sZ' (pullback.fst i g ≫ sZ) sq.flip.isoPullback.hom
        (isoPullback_hom_comp_structureMorphism C sZ sX sq hi sZ' hi') (n - ((r + e : ℕ) : ℤ))
        (chowGroupDegreeEquiv C sZ' (by push_cast; ring)
          (GenuineChern.chernCap C e sZ' (𝒩.baseChange i i' g' g sq).excessNormalSheaf
            (n - (r : ℤ)) (Fin.last e) (fundamentalChowClass C sZ' (n - (r : ℤ))))) := by
  have := (𝒩.baseChange i i' g' g sq).isFiniteLocallyFreeOfRank_excessNormalSheaf_of_add r e
  have : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
  set 𝒩' := 𝒩.baseChange i i' g' g sq
  set ℰ := 𝒩'.excessNormalSheaf
  set p := pullback.fst i' (𝟙 Y)
  have hC : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (conormalModule i') :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r
  have hL := virtualNormalBundleClass_cap_eq_chernCap_comp C sZ' (g ≫ sX) i' hi' 𝒩'
    (VirtualNormalBundle.ofIsRegularImmersion i' hreg) r e ℰ 𝒩'.excessInclusion
    𝒩'.excessProjection (gysinSystemOfInvertible C) 𝒩'.excessInclusion_comp_excessProjection
    (𝒩'.shortExact_excess hC) (𝒩'.dualMap_excessInclusion_comp_surjection hreg)
    (isVirtualNormalBundleClass_virtualNormalBundleClass C sZ' (g ≫ sX) i' hi' 𝒩' (r + e))
    (isVirtualNormalBundleClass_virtualNormalBundleClass C sZ' (g ≫ sX) i' hi'
      (VirtualNormalBundle.ofIsRegularImmersion i' hreg) r) (𝟙 Y) n
    (fundamentalChowClass C (𝟙 Y ≫ (g ≫ sX)) n)
  rw [virtualNormalGysinClass_cap_fundamentalChowClass_of_isRegularImmersion C sZ' (g ≫ sX)
    i' hi' hreg r (VirtualNormalBundle.ofIsRegularImmersion i' hreg) n hY] at hL
  have hP : GenuineChern.chernCap C e sZ' ℰ (n - (r : ℤ)) (Fin.last e)
        (fundamentalChowClass C sZ' (n - (r : ℤ))) =
      chowPushforwardOfIso C (p ≫ sZ') sZ' p rfl _
        (GenuineChern.chernCap C e (p ≫ sZ') ((Scheme.Modules.pullback p).obj ℰ) (n - (r : ℤ))
          (Fin.last e) (fundamentalChowClass C (p ≫ sZ') (n - (r : ℤ)))) := by
    rw [← chowPushforwardOfIso_fundamentalChowClass C (p ≫ sZ') sZ' p rfl (n - (r : ℤ)),
      ← properChowPushforward_eq_chowPushforwardOfIso C _ _ p rfl _
        (properPushforwardDescends C _ _ _ _ _),
      ← properChowPushforward_eq_chowPushforwardOfIso C _ _ p rfl _
        (properPushforwardDescends C _ _ _ _ _)]
    exact GenuineChern.chernCap_properPushforward C (p ≫ sZ') sZ' p rfl ℰ e _ (Iso.refl _)
      (n - (r : ℤ)) (Fin.last e) _ _ _
  rw [cap_eq_virtualNormalBundleClass_cap C sZ sX i hi 𝒩 (r + e) hc,
    virtualNormalGysinClass_cap_eq_chowPushforwardOfIso_cap_id C sZ sX i hi 𝒩 (r + e) g i' g' sq
      sZ' hi', chowGroupCongr_fundamentalChowClass, hL, hP]
  refine eq_of_heq ((chowPushforwardOfIso_heq_congr C _ _ _ _ (by push_cast; ring) _ _
    (chowGroupDegreeEquiv_heq C _ _ _)).trans (HEq.trans ?_
      (chowPushforwardOfIso_heq_congr C _ _ _ _ (by push_cast; ring) _ _
        (chowGroupDegreeEquiv_heq C _ _ _)).symm))
  refine heq_of_eq ?_
  rw [chowPushforwardOfIso_comp_apply]
  rfl

end Excess

end Stacks.Chow

end
