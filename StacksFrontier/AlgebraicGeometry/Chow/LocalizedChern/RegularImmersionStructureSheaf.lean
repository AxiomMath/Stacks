module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessNormalSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalConeFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedNewton
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedCap
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.LocalReduction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectClosedImmersion
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimConormalRank
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimLocal

/-!
# The localized Chern classes of the structure sheaf of a regular closed immersion

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `i : Z ⟶ X` be a closed immersion which is a perfect morphism, for
instance a regular closed immersion (Stacks 068C). Then `i_*𝒪_Z` is a perfect object of `D(𝒪_X)`
(Stacks 0G2E) whose restriction to `X ∖ Z` is zero, so if `X` is quasi-compact, or has
quasi-compact irreducible components, the data `X`, `Z`, `i_*𝒪_Z` form an instance of
Situation 0GUJ, and the localized classes

  `c_p(Z ⟶ X, i_*𝒪_Z)`, `P_p(Z ⟶ X, i_*𝒪_Z)`, `ch_p(Z ⟶ X, i_*𝒪_Z) = P_p(Z ⟶ X, i_*𝒪_Z)/p!`

of Stacks 0FB2 and Definition 0FB5 are defined, `c_p` for every `p ≥ 1` and `P_p` for every
`p ≥ 0`.

Now let `i` be a regular closed immersion of codimension `r ≥ 1`, with normal sheaf
`𝒩 = 𝒞_{Z/X}^∨` and class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)` (Stacks 0FBK). Lemma 0FEG states that
`c_t(Z ⟶ X, i_*𝒪_Z) = 0` for `1 ≤ t < r` and `c_r(Z ⟶ X, i_*𝒪_Z) = (-1)^{r-1}(r-1)! c(Z ⟶ X, 𝒩)`.
Lemma 0FEH draws the consequences on the fundamental class: if `dim_δ(X) ≤ n` then

1. `c_t(Z ⟶ X, i_*𝒪_Z) ∩ [X]_n = 0` for `1 ≤ t < r`,
2. `c_r(Z ⟶ X, i_*𝒪_Z) ∩ [X]_n = (-1)^{r-1}(r-1)! [Z]_{n-r}`,
3. `ch_t(Z ⟶ X, i_*𝒪_Z) ∩ [X]_n = 0` for `0 ≤ t < r`, and
4. `ch_r(Z ⟶ X, i_*𝒪_Z) ∩ [X]_n = [Z]_{n-r}`.

The argument is the source's. Part (2) is Lemma 0FEG combined with Stacks 0FBM at vanishing
excess, `c(Z ⟶ X, 𝒩) ∩ [X]_n = [Z]_{n-r}`. Parts (3) and (4) follow from Newton's identities of
Stacks 0FBA: the summands `c_{j+1} P_{r-1-j}` of `P_r` vanish, and `P_r = (-1)^{r-1} r c_r`, so
`ch_r = P_r/r! = (-1)^{r-1} c_r/(r-1)!`. Parts (1) and (3), and the vanishing of the summands
`c_{j+1} P_{r-1-j} ∩ [X]_n`, hold for a dimensional reason: `dim_δ(Z) ≤ n - r`, so
`CH_{n-t}(Z) = 0` for `t < r`, and every class of degree `t < r` kills `CH_n(X)`.

## Main definitions

* `Stacks.Chow.regularNormalGysinClass` — the class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)` of the normal sheaf
  of a regular closed immersion of codimension `r`.
* `Stacks.Chow.pushforwardStructureSheafSituation` — Situation 0GUJ for `i_*𝒪_Z`, `i` a perfect
  closed immersion; `Stacks.Chow.regularImmersionStructureSheafSituation` for `i` regular.
* `Stacks.Chow.LocalizedSituation.IsRegularImmersionChernFormula` — the conclusion of
  Lemma 0FEG for a situation whose closed immersion is regular of codimension `r`.

## Main results

* `Stacks.Chow.regularNormalGysinClass_cap_fundamentalChowClass` — Stacks 0FBM at vanishing
  excess: `c(Z ⟶ X, 𝒩) ∩ [X]_n = [Z]_{n-r}`.
* `Stacks.Chow.BivariantClass.cap_eq_zero_of_isRegularClosedImmersionOfCodim` — a class of degree
  `t < r` kills `CH_n(X)` when `dim_δ(X) ≤ n`.
* `Stacks.Chow.LocalizedSituation.localizedPowerSum_cap_fundamentalChowClass` —
  `P_r(Z ⟶ X, E) ∩ [X]_n = r! [Z]_{n-r}`, given Lemma 0FEG.
* `Stacks.Chow.LocalizedSituation.capFundamentalClass_of_isRegularImmersionChernFormula` —
  parts (1)–(4) of Lemma 0FEH, given Lemma 0FEG.
* `Stacks.Chow.LocalizedSituation.hasFundamentalDegreePart_of_isRegularImmersionChernFormula`
  — for `X` all of whose irreducible components have `δ`-dimension `n = k + r`, the degree `k`
  part of `ch(Z ⟶ X, E) ∩ [X]` is `[Z]_k`, given Lemma 0FEG.

## Implementation notes

The consequences of Lemma 0FEG are proved for any instance of Situation 0GUJ with `E|_{X ∖ Z}` zero
and `Z ⟶ X` regular of codimension `r`, from the conclusion of Lemma 0FEG for it
(`Stacks.Chow.LocalizedSituation.IsRegularImmersionChernFormula`); nothing else about `E` is
used. Of that conclusion only the formula for `c_r` enters: parts (1) and (3) hold in every such
situation, by the dimension count above.

The class `c_t(Z ⟶ X, E)` is that of the situation in degree `t`
(`Stacks.Chow.LocalizedSituation.localizedChernClassOfIsZero`), the degree of Situation 0GUJ
being the bound on the rank. The cap products with `[X]_n` are those of Stacks 42.57
(`Stacks.Chow.capFundamentalClassAt`), with values in `CH_{n-t}(Z)`, and the cap product of the
rational class `ch_t` is its base change to `𝐐`. The hypothesis `dim_δ(X) = n` of the source enters
only as `dim_δ(X) ≤ n`. The codimension `r` is required to be positive, as the source's formula
`(-1)^{r-1}(r-1)!` presupposes.

For the degree `k` part of `ch(Z ⟶ X, E) ∩ [X] = ∑_p P_p(Z ⟶ X, E) ∩ [X]_{k+p}/p!` only the summand
`p = r` survives when every irreducible component of `X` has `δ`-dimension `k + r`, because then
`[X]_m = 0` for `m ≠ k + r`.

## References

* [Stacks Project, Tag 0FEH](https://stacks.math.columbia.edu/tag/0FEH)
* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBA](https://stacks.math.columbia.edu/tag/0FBA)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0FB5](https://stacks.math.columbia.edu/tag/0FB5)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0G2E](https://stacks.math.columbia.edu/tag/0G2E)
* [Stacks Project, Tag 068C](https://stacks.math.columbia.edu/tag/068C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open scoped TensorProduct

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The normal sheaf class of a regular closed immersion -/

section NormalSheaf

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) {r : ℕ}

/-- **The class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)` of the normal sheaf `𝒩 = 𝒞_{Z/X}^∨`** of a regular
closed immersion `i : Z ⟶ X` of codimension `r` (Stacks 0FBK): the class of the virtual normal
sheaf `𝒞_{Z/X}^∨`, with the reflexivity isomorphism as its surjection
(`Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`), whose rank is the constant rank `r` of
the conormal sheaf. -/
def regularNormalGysinClass (hreg : IsRegularClosedImmersionOfCodim i r) :
    BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi r :=
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := hreg.isFiniteLocallyFreeOfRank_conormalModule
  virtualNormalBundleClass C sZ sX i hi
    (VirtualNormalBundle.ofIsRegularImmersion i hreg.isRegularImmersion) r

/-- **Stacks 0FBM at vanishing excess for `c(Z ⟶ X, 𝒩)`.** For a regular closed immersion
`i : Z ⟶ X` of codimension `r` and `dim_δ(X) ≤ n`, `c(Z ⟶ X, 𝒩) ∩ [X]_n = [Z]_{n-r}` in
`CH_{n-r}(Z ×_X X)`. -/
theorem regularNormalGysinClass_cap_fundamentalChowClass
    (hreg : IsRegularClosedImmersionOfCodim i r) (n : ℤ)
    (hX : schemeDeltaDimension C sX ≤ (n : EInt)) :
    (regularNormalGysinClass C sZ sX i hi hreg).cap (𝟙 X) n
        (fundamentalChowClass C (𝟙 X ≫ sX) n) =
      fundamentalChowClass C (pullback.fst i (𝟙 X) ≫ sZ) (n - r) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have := hreg.isFiniteLocallyFreeOfRank_conormalModule
  exact virtualNormalGysinClass_cap_fundamentalChowClass_of_isRegularImmersion C sZ sX i hi
    hreg.isRegularImmersion r _ n hX

/-- **A class of degree below the codimension kills `CH_n(X)`.** For a regular closed immersion
`i : Z ⟶ X` of codimension `r`, `dim_δ(X) ≤ n` and `c ∈ A^t(Z ⟶ X)` with `t < r`, the cap product
`c ∩ α` vanishes for every `α ∈ CH_n(X)`: it lies in `CH_{n-t}(Z ×_X X)`, which is zero because
`dim_δ(Z) ≤ n - r < n - t` (`Stacks.Chow.schemeDeltaDimension_le_sub_of_isRegularImmersion`). -/
theorem BivariantClass.cap_eq_zero_of_isRegularClosedImmersionOfCodim {G : GysinSystem C}
    {t : ℤ} (c : BivariantClass C G sZ sX i hi t) (hreg : IsRegularClosedImmersionOfCodim i r)
    (n : ℤ) (hX : schemeDeltaDimension C sX ≤ (n : EInt)) (ht : t < r)
    (α : chowGroup C (𝟙 X ≫ sX) n) : c.cap (𝟙 X) n α = 0 := by
  have := hreg.isFiniteLocallyFreeOfRank_conormalModule
  have hZ := schemeDeltaDimension_le_sub_of_isRegularImmersion C sZ sX i hi
    hreg.isRegularImmersion r n hX
  have hZ' : schemeDeltaDimension C (pullback.fst i (𝟙 X) ≫ sZ) ≤ ((n - (r : ℤ) : ℤ) : EInt) :=
    le_trans (le_of_eq (schemeDeltaDimension_comp_iso C (asIso (pullback.fst i (𝟙 X))) sZ)) hZ
  exact chowGroup_eq_zero C _ (fun z => by
    have := relativeDimension_le_of_schemeDeltaDimension_le' C _ hZ' z
    omega) _

end NormalSheaf

/-! ### Situation 0GUJ for the structure sheaf of a closed subscheme -/

section Situation

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] [Perfect i]

/-- **Situation 0GUJ for `i_*𝒪_Z`.** For a closed immersion `i : Z ⟶ X` which is a perfect
morphism, for instance a regular closed immersion (Stacks 068C,
`AlgebraicGeometry.perfect_of_isRegularImmersion`), of a scheme `X` locally of finite type over
the base which is quasi-compact or has quasi-compact irreducible components, and a degree `p`:
the data `X`, `Z`, `E = i_*𝒪_Z[0]`, perfect by Stacks 0G2E, which vanishes on `X ∖ Z`. -/
abbrev pushforwardStructureSheafSituation
    (hX : CompactSpace X ∨ ∀ T ∈ irreducibleComponents X, IsCompact T) (p : ℕ) :
    LocalizedSituation.{u} where
  base := C
  X := X
  a := sX
  Z := Z
  i := i
  E := (DerivedCategory.singleFunctor X.Modules 0).obj
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
  p := p
  perfect := isPerfect_pushforward_structureSheaf i
  restriction := Or.inl (isZero_derivedPullback_ofRestrict_compl _ _
    i.isClosedEmbedding.isClosed_range (supp_pushforwardStructureSheaf i).subset _ (Iso.refl _))
  finiteness := hX.elim Or.inl fun h => Or.inr (Or.inl h)

variable (hX : CompactSpace X ∨ ∀ T ∈ irreducibleComponents X, IsCompact T)

/-- `i_*𝒪_Z` vanishes on `X ∖ Z`: the first alternative of condition (2) of Situation 0GUJ. -/
theorem isZeroOnComplement_pushforwardStructureSheafSituation (p : ℕ) :
    (pushforwardStructureSheafSituation C sX i hX p).IsZeroOnComplement :=
  isZero_derivedPullback_ofRestrict_compl _ _ i.isClosedEmbedding.isClosed_range
    (supp_pushforwardStructureSheaf i).subset _ (Iso.refl _)

/-- In every degree `p ≥ 1` the second alternative of condition (2) of Situation 0GUJ holds for
`i_*𝒪_Z`: on `X ∖ Z` it is the zero module, finite locally free of rank `0 < p`. -/
theorem isFiniteLocallyFreeOfRankLTOnComplement_pushforwardStructureSheafSituation {p : ℕ}
    (hp : 0 < p) :
    (pushforwardStructureSheafSituation C sX i hX p).IsFiniteLocallyFreeOfRankLTOnComplement :=
  exists_isFiniteLocallyFreeOfRankLT_of_isZero (Scheme.Opens.ι _)
    (isZeroOnComplement_pushforwardStructureSheafSituation C sX i hX p) hp

/-- **`c_p(Z ⟶ X, i_*𝒪_Z)` is the class `c_p` of the situation in degree `0` taken in degree
`p`**: the class of Stacks 0FB2 for the situation in degree `p ≥ 1` is
`Stacks.Chow.LocalizedSituation.localizedChernClassOfIsZero` for the situation in any
degree, here `0`. -/
theorem localizedChern_pushforwardStructureSheafSituation {p : ℕ} (hp : 0 < p) :
    (pushforwardStructureSheafSituation C sX i hX p).localizedChern
        (isFiniteLocallyFreeOfRankLTOnComplement_pushforwardStructureSheafSituation C sX i hX hp) =
      LocalizedSituation.localizedChernClassOfIsZero
        (isZeroOnComplement_pushforwardStructureSheafSituation C sX i hX 0) hp :=
  rfl

end Situation

/-! ### The consequences of Lemma 0FEG on the fundamental class -/

namespace LocalizedSituation

variable (S : LocalizedSituation.{u}) (h : S.IsZeroOnComplement) {r : ℕ}
  (hreg : IsRegularClosedImmersionOfCodim S.i r)

/-- **The conclusion of Stacks 0FEG** for an instance of Situation 0GUJ with `E|_{X ∖ Z}` zero
whose closed immersion `i : Z ⟶ X` is regular of codimension `r ≥ 1`:
`c_t(Z ⟶ X, E) = 0` for `1 ≤ t < r` and `c_r(Z ⟶ X, E) = (-1)^{r-1}(r-1)! c(Z ⟶ X, 𝒩)` in
`A^r(Z ⟶ X)`, with `𝒩 = 𝒞_{Z/X}^∨` the normal sheaf. Lemma 0FEG asserts it for `E = i_*𝒪_Z`. -/
def IsRegularImmersionChernFormula (hr : 0 < r) : Prop :=
  (∀ (t : ℕ) (ht : 0 < t), t < r →
      localizedChernClassOfIsZero h ht = 0) ∧
    localizedChernClassOfIsZero h hr =
      ((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
        regularNormalGysinClass S.base (S.i ≫ S.a) S.a S.i rfl hreg

/-- `(1/r!) ⊗ r! y = 1 ⊗ y` in `ℚ ⊗ M`. -/
private theorem inv_factorial_tmul_zsmul {M : Type*} [AddCommGroup M] (r : ℕ) (y : M) :
    ((r.factorial : ℚ)⁻¹) ⊗ₜ[ℤ] ((r.factorial : ℤ) • y) = (1 : ℚ) ⊗ₜ[ℤ] y := by
  rw [← TensorProduct.smul_tmul, zsmul_eq_mul]
  congr 1
  have : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  push_cast
  field_simp

variable {S h hreg}

/-- **`P_r(Z ⟶ X, E) ∩ [X]_n = r! [Z]_{n-r}`**, given the conclusion of Stacks 0FEG, when `Z ⟶ X`
is regular of codimension `r ≥ 1` and `dim_δ(X) ≤ n`, in `CH_{n-r}(Z ×_X X)`.

By Newton's recursion (Stacks 0FBA)
`P_r = ∑_{j < r-1} (-1)^j c_{j+1} P_{r-1-j} + (-1)^{r-1} r c_r`. Each summand kills `[X]_n`,
because `P_{r-1-j}` is a class of degree `< r`
(`Stacks.Chow.BivariantClass.cap_eq_zero_of_isRegularClosedImmersionOfCodim`), and
`c_r ∩ [X]_n = (-1)^{r-1}(r-1)! [Z]_{n-r}` by Stacks 0FEG and Stacks 0FBM. -/
theorem localizedPowerSum_cap_fundamentalChowClass (hr : 0 < r)
    (hF : S.IsRegularImmersionChernFormula h hreg hr) (n : ℤ)
    (hX : schemeDeltaDimension S.base S.a ≤ (n : EInt)) :
    (S.localizedPowerSum h r).cap (𝟙 S.X) n (fundamentalChowClass S.base (𝟙 S.X ≫ S.a) n) =
      (r.factorial : ℤ) •
        fundamentalChowClass S.base (pullback.fst S.i (𝟙 S.X) ≫ (S.i ≫ S.a)) (n - r) := by
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  set α := fundamentalChowClass S.base (𝟙 S.X ≫ S.a) n
  let φ : BivariantClass S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl
      ((q + 1 : ℕ) : ℤ) →+
      chowGroup S.base (pullback.fst S.i (𝟙 S.X) ≫ (S.i ≫ S.a)) (n - ((q + 1 : ℕ) : ℤ)) :=
    AddMonoidHom.mk' (fun c => c.cap (𝟙 S.X) n α) fun _ _ => rfl
  change φ (S.localizedPowerSum h (q + 1)) = _
  rw [localizedPowerSum_succ S h q, map_add, map_sum,
    map_zsmul]
  have hsum : ∀ j ∈ (Finset.range q).attach, φ (((-1 : ℤ) ^ (j : ℕ)) •
      bivariantClassDegreeCongr S.base _ (S.i ≫ S.a) S.a S.i rfl
        (newton_degree_eq (Finset.mem_range.mp j.2))
        (supportedMul S.base (S.i ≫ S.a) S.a S.i rfl
          (localizedChernClassOfIsZero h
            (Nat.succ_pos (j : ℕ)))
          (S.localizedPowerSum h (q - j)))) = 0 := by
    intro j _
    have hj := Finset.mem_range.mp j.2
    rw [map_zsmul]
    refine (smul_eq_zero_of_right _ ?_)
    refine chowGroup_eq_zero_of_heq_zero S.base
      (j := n - ((q - (j : ℕ) : ℕ) : ℤ) - (((j : ℕ) + 1 : ℕ) : ℤ)) (by push_cast; omega) ?_
    refine (bivariantClassDegreeCongr_cap _ _ _ _ _ _ _ _ _ _ _).trans ?_
    refine (supportedLeftComp_cap _ _ _ _ _ _ _ _ _ _).trans ?_
    rw [BivariantClass.cap_eq_zero_of_isRegularClosedImmersionOfCodim S.base (S.i ≫ S.a) S.a S.i
      rfl _ hreg n hX (by push_cast; omega), map_zero]
  rw [Finset.sum_eq_zero hsum, zero_add]
  change ((-1 : ℤ) ^ q * ((q : ℤ) + 1)) •
    (localizedChernClassOfIsZero h hr).cap (𝟙 S.X) n α = _
  rw [hF.2, BivariantClass.zsmul_cap, regularNormalGysinClass_cap_fundamentalChowClass S.base
    (S.i ≫ S.a) S.a S.i rfl hreg n hX, smul_smul]
  congr 1
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have h1 : ((-1 : ℤ) ^ q) * (-1) ^ q = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  linear_combination ((q : ℤ) + 1) * (q.factorial : ℤ) * h1

variable (S h hreg)

/-- **Stacks 0FEH (1)–(4), given Stacks 0FEG.** In Situation 0GUJ with `E|_{X ∖ Z}` zero, let
`i : Z ⟶ X` be regular of codimension `r ≥ 1`, let `dim_δ(X) ≤ n`, and assume the conclusion of
Stacks 0FEG (`Stacks.Chow.LocalizedSituation.IsRegularImmersionChernFormula`). Then, with the
cap products with `[X]_n` of Stacks 42.57 (`Stacks.Chow.capFundamentalClassAt`) in `CH_*(Z)`,

1. `c_t(Z ⟶ X, E) ∩ [X]_n = 0` for `1 ≤ t < r`,
2. `c_r(Z ⟶ X, E) ∩ [X]_n = (-1)^{r-1}(r-1)! [Z]_{n-r}`,
3. `ch_t(Z ⟶ X, E) ∩ [X]_n = 0` for `0 ≤ t < r`, and
4. `ch_r(Z ⟶ X, E) ∩ [X]_n = [Z]_{n-r}`,

the last two in `CH_*(Z) ⊗ 𝐐`. Parts (1) and (3) do not use Stacks 0FEG: a class of degree
`t < r` kills `CH_n(X)` because `dim_δ(Z) ≤ n - r`. Part (2) is Stacks 0FEG and Stacks 0FBM;
part (4) is `Stacks.Chow.LocalizedSituation.localizedPowerSum_cap_fundamentalChowClass`
divided by `r!`. -/
theorem capFundamentalClass_of_isRegularImmersionChernFormula (hr : 0 < r)
    (hF : S.IsRegularImmersionChernFormula h hreg hr) (n : ℤ)
    (hX : schemeDeltaDimension S.base S.a ≤ (n : EInt)) :
    (∀ (t : ℕ) (ht : 0 < t), t < r →
      capFundamentalClassAt S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl t n
        (localizedChernClassOfIsZero h ht) = 0) ∧
    capFundamentalClassAt S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl r n
        (localizedChernClassOfIsZero h hr) =
      ((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
        fundamentalChowClass S.base (S.i ≫ S.a) (n - r) ∧
    (∀ t : ℕ, t < r →
      (capFundamentalClassAt S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl t
          n).toIntLinearMap.lTensor ℚ (S.localizedChernChar h t) = 0) ∧
    (capFundamentalClassAt S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl r
        n).toIntLinearMap.lTensor ℚ (S.localizedChernChar h r) =
      (1 : ℚ) ⊗ₜ[ℤ] fundamentalChowClass S.base (S.i ≫ S.a) (n - r) := by
  have hfund : ∀ m : ℤ, chowGroupPullbackIdEquiv S.base (S.i ≫ S.a) S.i m
      (fundamentalChowClass S.base (pullback.fst S.i (𝟙 S.X) ≫ (S.i ≫ S.a)) m) =
      fundamentalChowClass S.base (S.i ≫ S.a) m := fun m => by
    rw [chowGroupPullbackIdEquiv, chowGroupEquivOfIso_apply,
      chowPushforwardOfIso_fundamentalChowClass]
  refine ⟨fun t ht htr => ?_, ?_, fun t htr => ?_, ?_⟩
  · rw [capFundamentalClassAt_apply, BivariantClass.cap_eq_zero_of_isRegularClosedImmersionOfCodim
      S.base (S.i ≫ S.a) S.a S.i rfl _ hreg n hX (by exact_mod_cast htr), map_zero]
  · rw [capFundamentalClassAt_apply, hF.2, BivariantClass.zsmul_cap,
      regularNormalGysinClass_cap_fundamentalChowClass S.base (S.i ≫ S.a) S.a S.i rfl hreg n hX,
      map_zsmul, hfund]
  · rw [localizedChernChar_apply, LinearMap.lTensor_tmul, AddMonoidHom.coe_toIntLinearMap,
      capFundamentalClassAt_apply,
      BivariantClass.cap_eq_zero_of_isRegularClosedImmersionOfCodim S.base (S.i ≫ S.a) S.a S.i
        rfl _ hreg n hX (by exact_mod_cast htr), map_zero, TensorProduct.tmul_zero]
  · rw [localizedChernChar_apply, LinearMap.lTensor_tmul, AddMonoidHom.coe_toIntLinearMap,
      capFundamentalClassAt_apply, localizedPowerSum_cap_fundamentalChowClass hr hF n hX,
      map_zsmul, hfund, inv_factorial_tmul_zsmul]

/-- **The degree `k` part of `ch(Z ⟶ X, E) ∩ [X]` is `[Z]_k`, given Stacks 0FEG**: the form of
Stacks 0FEH (3), (4) used in the proof of Stacks 0FEW
(`Stacks.Chow.LocalizedSituation.HasFundamentalDegreePart`). In Situation 0GUJ with
`E|_{X ∖ Z}` zero, let `i : Z ⟶ X` be regular of codimension `r ≥ 1`, let every irreducible
component of `X` have `δ`-dimension `n = k + r`, and assume the conclusion of Stacks 0FEG. Then for
every `N ≥ r` the degree `k` part of `∑_{p ≤ N} P_p(Z ⟶ X, E) ∩ [X] / p!` is `[Z ×_X X]_k`.

Since the irreducible components of `X` all have `δ`-dimension `n`, `[X]_m = 0` for `m ≠ n`
(`Stacks.Chow.fundamentalChowClass_eq_zero_of_deltaDimension_eq`), so only the summand
`P_r ∩ [X]_n / r! = [Z]_{n-r}` survives
(`Stacks.Chow.LocalizedSituation.localizedPowerSum_cap_fundamentalChowClass`). -/
theorem hasFundamentalDegreePart_of_isRegularImmersionChernFormula (hr : 0 < r)
    (hF : S.IsRegularImmersionChernFormula h hreg hr) (n : ℤ)
    (hpure : ∀ W : irreducibleComponents S.X, deltaDimension S.base S.a
      ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set S.X) W.2⟩ = n)
    (N : ℕ) (hN : r ≤ N) (k : ℤ) (hk : k + r = n) :
    S.HasFundamentalDegreePart h N k := by
  have hX : schemeDeltaDimension S.base S.a ≤ (n : EInt) :=
    iSup_le fun W => (congrArg (fun m : ℤ => (m : EInt)) (hpure W)).le
  have hpure' : ∀ W : irreducibleComponents S.X, deltaDimension S.base (𝟙 S.X ≫ S.a)
      ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set S.X) W.2⟩ = n := fun W => by
    simpa using hpure W
  unfold HasFundamentalDegreePart capFundamentalClassDegreePart
  rw [Finset.sum_eq_single r]
  · subst hk
    rw [localizedPowerSum_cap_fundamentalChowClass hr hF _ hX, map_zsmul,
      chowGroupDegreeEquiv_fundamentalChowClass, inv_factorial_tmul_zsmul]
  · intro p _ hp
    rw [fundamentalChowClass_eq_zero_of_deltaDimension_eq S.base _ hpure' (by omega), map_zero,
      map_zero, TensorProduct.tmul_zero]
  · intro hrN
    exact absurd (Finset.mem_range.mpr (by omega)) hrN

end LocalizedSituation

/-! ### The situation of `i_*𝒪_Z` (Stacks 0FEH: `RegularImmersionChernFormula.lean`) -/

section StructureSheaf

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i] {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim i r)
  (hX : CompactSpace X ∨ ∀ T ∈ irreducibleComponents X, IsCompact T)

/-- **Situation 0GUJ for `i_*𝒪_Z`, `i` a regular closed immersion of codimension `r`**, `X`
quasi-compact or with quasi-compact irreducible components, in degree `p`:
`Stacks.Chow.pushforwardStructureSheafSituation`, the closed immersion being perfect by
Stacks 068C (`AlgebraicGeometry.perfect_of_isRegularImmersion`). -/
abbrev regularImmersionStructureSheafSituation (p : ℕ) : LocalizedSituation.{u} :=
  haveI := perfect_of_isRegularImmersion i hreg.isRegularImmersion
  pushforwardStructureSheafSituation C sX i hX p

/-- For a regular closed immersion `i`, `i_*𝒪_Z` vanishes on `X ∖ Z`. -/
theorem isZeroOnComplement_regularImmersionStructureSheafSituation (p : ℕ) :
    (regularImmersionStructureSheafSituation C sX i hreg hX p).IsZeroOnComplement :=
  have := perfect_of_isRegularImmersion i hreg.isRegularImmersion
  isZeroOnComplement_pushforwardStructureSheafSituation C sX i hX p

/-- For a regular closed immersion `i` and `p ≥ 1`, `i_*𝒪_Z` is finite locally free of rank
`< p` on `X ∖ Z`, being zero there. -/
theorem isFiniteLocallyFreeOfRankLTOnComplement_regularImmersionStructureSheafSituation {p : ℕ}
    (hp : 0 < p) :
    LocalizedSituation.IsFiniteLocallyFreeOfRankLTOnComplement
      (regularImmersionStructureSheafSituation C sX i hreg hX p) :=
  have := perfect_of_isRegularImmersion i hreg.isRegularImmersion
  isFiniteLocallyFreeOfRankLTOnComplement_pushforwardStructureSheafSituation C sX i hX hp

end StructureSheaf

end Stacks.Chow

end
