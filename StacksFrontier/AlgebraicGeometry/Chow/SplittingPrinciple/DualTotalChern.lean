module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.IntegralPerfectComplex
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapDivisorInduction
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCharacterDual
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.DualComplexChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ArbitraryRankChern
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.ChernRoots
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualChernClasses
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeOfRank
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chern classes of the dual of a finite locally free module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℰ` be a finite locally free `𝒪_X`-module with dual
`ℰ^∨ = SheafHom(ℰ, 𝒪_X)`. [Stacks, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5) is the
sign rule

  `c_i(ℰ^∨) = (-1)^i c_i(ℰ)`  in  `A^i(X)`.

It is proved here for the bivariant Chern classes `c_i(ℰ) ∈ A^i(X)` of Stacks 0B7H, read in the
ring `Stacks.Chow.TotalChowClass C sX = ∏_{p ≥ 0} A^p(X)` of total Chow cohomology classes at the
Gysin system of the first Chern class of an invertible module: for `ℰ` of constant rank `r` the
class `c_i(ℰ)` is `TotalChowClass.homComponent i (totalChern C sX ℰ r)`, and for `ℰ` of arbitrary
rank it is the degree-`i` part of the total Chern class `Stacks.Chow.totalChernOfFiniteLocallyFree`
of Stacks 0ESW.

The sign rule is the statement that the total Chern class of `ℰ^∨` is the image of that of `ℰ`
under the endomorphism `Stacks.Chow.TotalChowClass.signScale` of the ring of total classes which
multiplies `A^p(X)` by `(-1)^p`; this endomorphism is multiplicative because
`(-1)^i (-1)^j = (-1)^{i+j}`.

## The proof

* **The splitting principle.** By Stacks 02UL two total classes on `X` agree as soon as they
  agree after restriction along every `h : T ⟶ X` along which `h^*ℰ` has a filtration with
  invertible successive quotients
  (`Stacks.Chow.TotalChowClass.eq_of_res_eq_of_hasInvertibleFiltration`).
  Restriction commutes with the total Chern class, with the sign scaling, and with duality
  (`h^*(ℰ^∨) ≅ (h^*ℰ)^∨` for `ℰ` finite locally free).
* **The dual filtration.** Duality is exact on short exact sequences of finite locally free
  modules (`Stacks.AlgebraicGeometry.ReflexiveModules.exists_dualSheaf_shortExact`), so a step
  `0 ⟶ ℱ ⟶ ℰ ⟶ ℒ ⟶ 0` of the filtration dualizes to `0 ⟶ ℒ^∨ ⟶ ℰ^∨ ⟶ ℱ^∨ ⟶ 0`, and the
  Whitney sum formula (Stacks 02UI) gives `c(ℰ) = c(ℱ) c(ℒ)` and `c(ℰ^∨) = c(ℒ^∨) c(ℱ^∨)`.
  Total Chern classes commute, so induction on the length of the filtration reduces the claim to
  the case of an invertible module.
* **The line-bundle case.** `c₁(ℒ^∨) = -c₁(ℒ)` by Stacks 02SP, because the evaluation pairing
  `ℒ^∨ ⊗ ℒ ⟶ 𝒪_X` of an invertible module is an isomorphism (Stacks 01CT): this is
  `Stacks.Chow.firstChernClassCapOfInvertible_eq_neg_of_tensorObj_iso_unit` on every test scheme.
  As `c(ℒ) = 1 + c₁(ℒ)`, this is the sign rule in rank one.

## Main results

* `Stacks.Chow.TotalChowClass.firstChernTotal_dualSheaf` — `c₁(ℒ^∨) = -c₁(ℒ)` for `ℒ` invertible.
* `Stacks.Chow.totalChern_dualSheaf_of_hasInvertibleFiltration` — `c(ℰ^∨) = signScale (c(ℰ))`
  for a module filtered with invertible quotients.
* `Stacks.Chow.homPart_totalChern_dualSheaf` — **Stacks 0FA5** in constant rank.
* `Stacks.Chow.totalChernOfFiniteLocallyFree_dualSheaf` and
  `Stacks.Chow.homPart_totalChernOfFiniteLocallyFree_dualSheaf` — **Stacks 0FA5** for a finite
  locally free module of arbitrary rank.

## References

* [Stacks Project, Tag 0FA5](https://stacks.math.columbia.edu/tag/0FA5)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset

universe u

namespace Stacks.Chow

open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualMap)
open AlgebraicGeometry.VectorBundleKZero (pullbackDualSheafIso)
open Stacks.StalkFreeBridge (finiteLocallyFree_isFiniteLocallyFree)

/-! ### The sign scaling of total classes -/

namespace TotalChowClass

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- The homogeneous parts of the sign scaling: `(signScale c)_i = (-1)^i c_i`. -/
theorem homPart_signScale (i : ℕ) (c : TotalChowClass C sX) :
    TotalChowClass.homComponent i (signScale c) =
      ((-1 : ℤ) ^ i) • TotalChowClass.homComponent i c :=
  ext fun p ↦ by
    change TotalChowClass.homComponent i (signScale c) p =
      ((-1 : ℤ) ^ i) • TotalChowClass.homComponent i c p
    rw [TotalChowClass.homComponent_apply, TotalChowClass.homComponent_apply]
    split_ifs with hp
    · subst hp
      rfl
    · exact (smul_zero _).symm

end TotalChowClass

/-! ### Duality and invertible modules -/

section Invertible

variable {X : Scheme.{u}}

/-- **The dual of an invertible module on a scheme is invertible** (Stacks 01CT). -/
@[ega "0 5.4.3" "special case"]
instance isInvertible_dualSheaf_ofInvertible (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (dualSheaf L) :=
  @Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf _ _ _ X.sheaf.obj
    X.ringCatSheaf.property _ _ _ _ L ‹_›

/-- The isomorphism `g^*(ℳ^∨) ≅ (g^*ℳ)^∨` for `ℳ` finite locally free, both duals being
`Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf`. -/
private def dualPullbackIso {Y : Scheme.{u}} (g : Y ⟶ X) (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    (Scheme.Modules.pullback g).obj (dualSheaf M) ≅ dualSheaf ((Scheme.Modules.pullback g).obj M) :=
  pullbackDualSheafIso g M (finiteLocallyFree_isFiniteLocallyFree M)

end Invertible

/-! ### The first Chern class of the dual of an invertible module -/

section FirstChern

variable (C : ChowSituation.{u})

/-- **Stacks 02SP for the dual**: `c₁(ℒ^∨) ∩ - = -(c₁(ℒ) ∩ -)` on Chow groups for an invertible
module `ℒ`. -/
theorem invCap_capOnChow_dualSheaf {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q]
    (N : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property N]
    (k : ℤ) (x : chowGroup C q (k + 1)) :
    (invCap C q (dualSheaf N)).capOnChow C q k x = -(invCap C q N).capOnChow C q k x := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  rw [invCap_capOnChow_mk, invCap_capOnChow_mk,
    firstChernClassCapOfInvertible_eq_neg_of_tensorObj_iso_unit C q k (dualSheaf N) N
      (@Stacks.SheafOfModules.Scheme.evaluationIso T N ‹_›) α, neg_neg]

namespace TotalChowClass

variable {C} {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **The first Chern class of the dual**: `c₁(ℒ^∨) = -c₁(ℒ)` in `A^1(Y)` for an invertible
module `ℒ`. -/
theorem firstChernTotal_dualSheaf (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    firstChernTotal C sY (dualSheaf L) = -firstChernTotal C sY L := by
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  refine ext_op fun {T} g _ ↦ ?_
  have := isInvertible_pullback g L
  have := isInvertible_pullback g (dualSheaf L)
  rw [op_neg]
  funext k j
  refine AddMonoidHom.ext fun α ↦ ?_
  by_cases hj : j = 1
  · subst hj
    change _ = -((firstChernTotal C sY L).op g k 1 α)
    rw [eq_of_heq (op_firstChernTotal_one_heq C sY (dualSheaf L) g k α),
      eq_of_heq (op_firstChernTotal_one_heq C sY L g k α),
      invCap_capOnChow_congr C (g ≫ sY) _ _ (dualPullbackIso g L),
      invCap_capOnChow_dualSheaf]
  · change _ = -((firstChernTotal C sY L).op g k j α)
    rw [(isHomogeneous_firstChernTotal C sY _).op g k j hj,
      (isHomogeneous_firstChernTotal C sY L).op g k j hj]
    simp

end TotalChowClass

end FirstChern

/-! ### Filtrations with invertible quotients -/

/-- **A module with a filtration of length `r` by invertible quotients is finite locally free of
rank `r`.** -/
theorem _root_.Stacks.WeilCohomology.HasInvertibleFiltration.isFiniteLocallyFreeOfRank
    {X : Scheme.{u}} {E : X.Modules} {r : ℕ}
    (h : Stacks.WeilCohomology.HasInvertibleFiltration X E r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r := by
  induction h with
  | nil E hE => exact AlgebraicGeometry.isFiniteLocallyFreeOfRank_zero_of_isZero hE
  | @step E F L r f g w hS hL hE hF ih =>
      exact GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact (ShortComplex.mk f g w) hS r 1
        ih (@isFiniteLocallyFreeOfRank_one_of_isInvertible _ L hL)

/-! ### Stacks 0FA5 -/

section Dual

variable (C : ChowSituation.{u})

open TotalChowClass

/-- **Stacks 0FA5 in rank one**: `c(ℒ^∨) = signScale (c(ℒ))` for `ℒ` invertible, i.e.
`1 + c₁(ℒ^∨) = 1 - c₁(ℒ)`. -/
theorem totalChern_dualSheaf_of_isInvertible {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    letI := isFiniteLocallyFreeOfRank_one_of_isInvertible L
    totalChern C sY (dualSheaf L) 1 = signScale (totalChern C sY L 1) := by
  let := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  refine ext_homPart fun n ↦ ?_
  rw [homPart_signScale]
  rcases n with _ | _ | n
  · rw [homPart_zero_totalChern, homPart_zero_totalChern, pow_zero, one_smul]
  · rw [← firstChernTotal_eq_homComponent_totalChern, ← firstChernTotal_eq_homComponent_totalChern,
      firstChernTotal_dualSheaf, zero_add, pow_one, neg_one_zsmul]
  · rw [homPart_totalChern_of_lt C sY _ 1 (by omega), homPart_totalChern_of_lt C sY L 1 (by omega),
      smul_zero]

/-- **Stacks 0FA5 on a filtered module**: if `ℰ` has a filtration of length `r` with invertible
successive quotients then `c(ℰ^∨) = signScale (c(ℰ))`. -/
theorem totalChern_dualSheaf_of_hasInvertibleFiltration {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] {E : T.Modules} {r : ℕ}
    (h : Stacks.WeilCohomology.HasInvertibleFiltration T E r) :
    letI := h.isFiniteLocallyFreeOfRank
    totalChern C sT (dualSheaf E) r = signScale (totalChern C sT E r) := by
  induction h with
  | nil E hE =>
      let := AlgebraicGeometry.isFiniteLocallyFreeOfRank_zero_of_isZero hE
      change totalChern C sT (dualSheaf E) 0 = signScale (totalChern C sT E 0)
      rw [totalChern_of_rank_zero, totalChern_of_rank_zero, signScale_one]
  | @step E F L r f g w hS hL hE hF ih =>
      have : AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property
        L := hL
      have := isFiniteLocallyFreeOfRank_one_of_isInvertible L
      have := hF.isFiniteLocallyFreeOfRank
      have := (Stacks.WeilCohomology.HasInvertibleFiltration.step f g w hS hL hE
        hF).isFiniteLocallyFreeOfRank
      have ih' : totalChern C sT (dualSheaf F) r = signScale (totalChern C sT F r) := ih
      change totalChern C sT (dualSheaf E) (r + 1) = signScale (totalChern C sT E (r + 1))
      have hfl : ∀ (M : T.Modules) (s : ℕ)
          [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M s],
          Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := T.ringCatSheaf) M :=
        fun M s _ ↦
          have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
            M s
          finiteLocallyFree_isFiniteLocallyFree M
      obtain ⟨w', hS'⟩ := Stacks.AlgebraicGeometry.ReflexiveModules.exists_dualSheaf_shortExact
        f g w hS.mono_f hS.epi_g hS.exact (hfl F r) (hfl E (r + 1)) (hfl L 1)
      have hW := totalChern_eq_mul_of_shortExact C sT (ShortComplex.mk f g w) hS r 1
      have hW' := totalChern_eq_mul_of_shortExact C sT
        (ShortComplex.mk (dualMap g) (dualMap f) w') hS' 1 r
      have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSheaf E)
          (1 + r) :=
        GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
          (ShortComplex.mk (dualMap g) (dualMap f) w') hS' 1 r inferInstance inferInstance
      calc totalChern C sT (dualSheaf E) (r + 1)
          = totalChern C sT (dualSheaf E) (1 + r) :=
            totalChern_congr C sT (Iso.refl _) (Nat.add_comm r 1)
        _ = totalChern C sT (dualSheaf L) 1 * totalChern C sT (dualSheaf F) r := hW'
        _ = signScale (totalChern C sT L 1) * signScale (totalChern C sT F r) := by
            rw [totalChern_dualSheaf_of_isInvertible, ih']
        _ = signScale (totalChern C sT E (r + 1)) := by
            rw [← signScale_mul, (totalChern_commute C sT L F 1 r).eq, ← hW]

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 0FA5**, constant rank: for `ℰ` finite locally free of rank `r` on `X`,

  `c_i(ℰ^∨) = (-1)^i c_i(ℰ)`

in `A^i(X)`, for every `i`, where `c_i(-)` is the degree-`i` part of the total Chern class, the
bivariant Chern class of Stacks 0B7H, and `ℰ^∨` is the dual sheaf `SheafHom(ℰ, 𝒪_X)`. -/
@[stacks 0FA5 "constant rank: for every X locally of finite type over S, every finite locally \
free E of rank r and every i, with no further hypothesis.  c_i(E) is the degree-i part \
TotalChowClass.homComponent i (totalChern C sX E r) of the total Chern class in the ring \
TotalChowClass C sX of total \
Chow cohomology classes, the bivariant Chern class of Stacks 0B7H, and E^dual is the dual sheaf \
Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E = SheafHom(E, O_X)"]
theorem homPart_totalChern_dualSheaf (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (i : ℕ) :
    TotalChowClass.homComponent i (totalChern C sX (dualSheaf E) r) =
      ((-1 : ℤ) ^ i) • TotalChowClass.homComponent i (totalChern C sX E r) := by
  rw [totalChern_dualSheaf, homPart_signScale]

/-- **Stacks 0FA5 for the total Chern class, arbitrary rank**: for `ℰ` finite locally free, of a
rank which need not be constant, `c(ℰ^∨) = signScale (c(ℰ))` for the total Chern classes of
Stacks 0ESW. -/
theorem totalChernOfFiniteLocallyFree_dualSheaf (E : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf E hE
    totalChernOfFiniteLocallyFree C sX (dualSheaf E) =
      signScale (totalChernOfFiniteLocallyFree C sX E) := by
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf E hE
  refine eq_of_res_eq (isClopenDecomposition_rankLociFamily E) fun r ↦ ?_
  let := isFiniteLocallyFreeOfRank_pullback_rankLociFamily E r
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj (dualSheaf E)) r.down :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (dualPullbackIso (rankLociFamily E r).ι E).symm inferInstance
  rw [res_signScale, res_totalChernOfFiniteLocallyFree_rankLocus C sX E r,
    res_totalChernOfFiniteLocallyFree_of_rank C sX (dualSheaf E) _ rfl r.down,
    totalChern_congr C _ (dualPullbackIso (rankLociFamily E r).ι E) rfl]
  exact totalChern_dualSheaf C _ _ r.down

/-- **Stacks 0FA5**: for `ℰ` finite locally free on `X`, of arbitrary rank,

  `c_i(ℰ^∨) = (-1)^i c_i(ℰ)`

in `A^i(X)`, for every `i`, where `c_i(-)` is the degree-`i` part of the total Chern class of
Stacks 0ESW, which on the locus where `ℰ` has rank `r` is the bivariant Chern class of
Stacks 0B7H. -/
@[stacks 0FA5 "the lemma as stated, for every X locally of finite type over S, every finite \
locally free E (rank not assumed constant) and every i, with no further hypothesis.  c_i(E) is \
the degree-i part of totalChernOfFiniteLocallyFree C sX E, the total Chern class of Stacks 0ESW \
in the ring TotalChowClass C sX of total Chow cohomology classes, and E^dual is the dual sheaf \
Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E = SheafHom(E, O_X)"]
theorem homPart_totalChernOfFiniteLocallyFree_dualSheaf (E : X.Modules)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (i : ℕ) :
    haveI := Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf E hE
    TotalChowClass.homComponent i (totalChernOfFiniteLocallyFree C sX (dualSheaf E)) =
      ((-1 : ℤ) ^ i) • TotalChowClass.homComponent i (totalChernOfFiniteLocallyFree C sX E) := by
  rw [totalChernOfFiniteLocallyFree_dualSheaf, homPart_signScale]

end Dual

end Stacks.Chow

end
