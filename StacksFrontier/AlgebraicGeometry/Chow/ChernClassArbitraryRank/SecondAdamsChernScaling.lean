module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.InvertibleChernScaling
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullback
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.SplittingProjective
public import StacksCore.Tactic.StacksAttribute

/-!
# Chern classes and the Chern character of `ψ²(α)`: Stacks 0FEN

Let `(S, δ)` be as in Situation 02QL and let `X` be locally of finite type over `S`. Let `ψ²` be
the second Adams operator of Stacks 0FEJ on `K_0(Vect(X))`, and let
`c : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X)` and `ch : K_0(Vect(X)) ⟶ ∏_{i ≥ 0} A^i(X) ⊗ 𝐐` be the
maps of Stacks 0FEL and Stacks 0FEM. **Stacks 0FEN** says that for every `α ∈ K_0(Vect(X))`

  `c_i(ψ²(α)) = 2^i c_i(α)`  and  `ch_i(ψ²(α)) = 2^i ch_i(α)`.

## The proof

This is the source's proof. The map multiplying `A^i(X)` by `2^i` is a ring endomorphism of
`∏_{i ≥ 0} A^i(X)` (`Stacks.Chow.TotalChowClass.powScaleRingHom`) and `ψ²` is a ring map, so it
suffices to treat a generator `α = [ℰ]`. The Chern character `ch_p = P_p/p!` is read through the
integral power sums: `α ↦ P_p(α)` is additive on `K_0(Vect(X))`
(`Stacks.Chow.modulePowerSumKGroupHom`, by Stacks 0F9C), and the second equation is
`P_p(ψ²(α)) = 2^p P_p(α)` divided by `p!`.

For a generator the identities are checked after pulling back along a family of morphisms
`γ_r : P_r ⟶ X_r ⊆ X` that is jointly injective on `∏_{i ≥ 0} A^i(X)`: `X_r` is the open and
closed locus where `ℰ` has rank `r` (Stacks 0ESW; restriction to all of them is injective by
Stacks 0FDZ), and `P_r ⟶ X_r` is the projective smooth morphism of the splitting principle,
Stacks 02UL, along which restriction is injective and `ℰ` acquires a filtration with invertible
successive quotients `ℒ_j`. The maps `c`, `P_p` and `ψ²` commute with pullback
(`Stacks.Chow.totalChernKGroupMap_pullback`, `Stacks.Chow.modulePowerSumKGroupHom_pullback`, and
Stacks 0FEJ), and on `P_r` the class `γ_r^*[ℰ]` is `∑_j [ℒ_j]`, so
`ψ²(γ_r^*[ℰ]) = ∑_j [ℒ_j^{⊗ 2}]`. With `x_j = c_1(ℒ_j)`, `c(ℒ_j^{⊗ 2}) = 1 + 2x_j` is the scaling
of `c(ℒ_j) = 1 + x_j`, and `P_p(ℒ_j^{⊗ 2}) = (2x_j)^p = 2^p P_p(ℒ_j)`; summing over `j` gives the
identities on `P_r`.

## Main results

* `Stacks.Chow.totalChernKGroupMap_secondAdams` — `c(ψ²(α))` is the `2^i`-scaling of `c(α)`.
* `Stacks.Chow.modulePowerSumKGroupHom_secondAdams` — `P_p(ψ²(α)) = 2^p P_p(α)`.
* `Stacks.Chow.chernClass_chernCharacter_secondAdams` — **Stacks 0FEN**.

## References

* [Stacks Project, Tag 0FEN](https://stacks.math.columbia.edu/tag/0FEN)
* [Stacks Project, Tag 0FEJ](https://stacks.math.columbia.edu/tag/0FEJ)
* [Stacks Project, Tag 0FEL](https://stacks.math.columbia.edu/tag/0FEL)
* [Stacks Project, Tag 0FEM](https://stacks.math.columbia.edu/tag/0FEM)
* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Restriction of the Chern classes and the power sums -/

section Restriction

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] (f : Y ⟶ X) [LocallyOfFiniteType f]
  (hs : f ≫ sX = sY)

omit [LocallyOfFiniteType f] in
/-- The pullback of a finite locally free module is finite locally free. -/
theorem isFiniteLocallyFree_pullback_of_isFiniteLocallyFree (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) :=
  VectorBundleKZero.isFiniteLocallyFree_pullback f E inferInstance

omit [LocallyOfFiniteType f] in
/-- The pullback of `ℰ` along a rank-locus inclusion of `f^*ℰ` composed with `f` has the rank of
that locus. -/
private theorem isFiniteLocallyFreeOfRank_pullback_comp_rankLociFamily (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (ρ : ULift.{u} ℕ) :
    haveI := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback
        ((rankLociFamily ((Scheme.Modules.pullback f).obj E) ρ).ι ≫ f)).obj E) ρ.down := by
  have := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    ((Scheme.Modules.pullbackComp _ f).app E)
    (isFiniteLocallyFreeOfRank_pullback_rankLociFamily ((Scheme.Modules.pullback f).obj E) ρ)

/-- **Restriction of the total Chern class**: `f^* c(ℰ) = c(f^*ℰ)`, for `ℰ` of any rank. -/
theorem res_totalChernClassOfModule (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    haveI := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
    TotalChowClass.res f hs (totalChernClassOfModule C sX E) =
      totalChernClassOfModule C sY ((Scheme.Modules.pullback f).obj E) := by
  have := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
  refine TotalChowClass.eq_of_res_eq
    (isClopenDecomposition_rankLociFamily ((Scheme.Modules.pullback f).obj E)) fun ρ ↦ ?_
  have hρ := isFiniteLocallyFreeOfRank_pullback_rankLociFamily
    ((Scheme.Modules.pullback f).obj E) ρ
  have := isFiniteLocallyFreeOfRank_pullback_comp_rankLociFamily f E ρ
  rw [TotalChowClass.res_res, res_totalChernClassOfModule_of_rank C sX E _ _ ρ.down,
    res_totalChernClassOfModule_rankLocus]
  exact totalChern_congr C _ ((Scheme.Modules.pullbackComp _ f).app E).symm rfl

/-- **Restriction of the power sums**: `f^* P_p(ℰ) = P_p(f^*ℰ)`, for `ℰ` of any rank. -/
theorem res_modulePowerSumArbitraryRank (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (p : ℕ) :
    haveI := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
    TotalChowClass.res f hs (modulePowerSumArbitraryRank C sX E p) =
      modulePowerSumArbitraryRank C sY ((Scheme.Modules.pullback f).obj E) p := by
  have := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f E
  refine TotalChowClass.eq_of_res_eq
    (isClopenDecomposition_rankLociFamily ((Scheme.Modules.pullback f).obj E)) fun ρ ↦ ?_
  have hρ := isFiniteLocallyFreeOfRank_pullback_rankLociFamily
    ((Scheme.Modules.pullback f).obj E) ρ
  have h₁ := isFiniteLocallyFreeOfRank_pullback_comp_rankLociFamily f E ρ
  rw [TotalChowClass.res_res,
    res_modulePowerSumArbitraryRank_of_constantRank C sX E _ _ ρ.down h₁ p,
    res_modulePowerSumArbitraryRank_rankLociFamily]
  exact modulePowerSum_congr C _ hρ h₁ ((Scheme.Modules.pullbackComp _ f).app E).symm rfl p

end Restriction

/-! ### Restriction along a universally Chow injective morphism is injective -/

/-- Restriction of total classes along a flat morphism which is universally injective on Chow
groups is injective: Stacks 02UL (2) in every degree. -/
theorem TotalChowClass.res_injective_of_universallyChowInjective {C : ChowSituation.{u}}
    {X P : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sP : P ⟶ C.S}
    [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
    (hs : π ≫ sX = sP) (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension π d)
    (hπ : UniversallyChowInjective C π d hd) : Function.Injective (TotalChowClass.res π hs) := by
  subst hs
  intro c c' h
  refine TotalChowClass.ext fun p ↦ ?_
  refine chowCohomologyRestriction_injective C (gysinSystemOfInvertible C) sX π (p : ℤ) d hd hπ
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) ?_
  rw [← TotalChowClass.res_rfl_apply, ← TotalChowClass.res_rfl_apply, h]

/-! ### The power sums on `K_0(Vect(X))` -/

section KGroup

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

open Classical in
/-- `P_p(ℰ)` for a finite locally free module `ℰ`, and `0` for every other module. -/
def modulePowerSumOrZero (p : ℕ) (M : X.Modules) : TotalChowClass C sX :=
  if _h : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M then
    modulePowerSumArbitraryRank C sX M p
  else 0

/-- For a finite locally free module `ℰ`, `modulePowerSumOrZero C sX p ℰ` is `P_p(ℰ)`. -/
theorem modulePowerSumOrZero_of_isFiniteLocallyFree (p : ℕ) (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M] :
    modulePowerSumOrZero C sX p M = modulePowerSumArbitraryRank C sX M p := by
  rw [modulePowerSumOrZero, dite_eq_left
    ‹Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M›]

/-- **The power sum `P_p` on `K_0(Vect(X))`**: the additive map sending `[ℰ]` to `P_p(ℰ)`, well
defined by Stacks 0F9C. -/
def modulePowerSumKGroupHom (p : ℕ) : VectorBundleKZero X →+ TotalChowClass C sX :=
  VectorBundleKZero.liftAddHom (modulePowerSumOrZero C sX p)
    (fun M hM ↦ by rw [modulePowerSumOrZero, dite_eq_right hM])
    (fun {E F G} f g w hE hF hG _ _ hex ↦ by
      rw [modulePowerSumOrZero_of_isFiniteLocallyFree, modulePowerSumOrZero_of_isFiniteLocallyFree,
        modulePowerSumOrZero_of_isFiniteLocallyFree]
      exact modulePowerSumArbitraryRank_eq_add_of_shortExact C sX (ShortComplex.mk f g w)
        { exact := hex } p)

/-- The power sum `P_p` on `K_0(Vect(X))` sends the class `[ℰ]` of a finite locally free module
to `P_p(ℰ)`. -/
theorem modulePowerSumKGroupHom_classOf (p : ℕ) (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    modulePowerSumKGroupHom C sX p (VectorBundleKZero.classOf X E) =
      modulePowerSumArbitraryRank C sX E p :=
  (VectorBundleKZero.liftAddHom_classOf _ _ _ E).trans
    (modulePowerSumOrZero_of_isFiniteLocallyFree C sX p E)

/-- The components of the Chern character map are the power sums divided by `p!`:
`ch_p(α) = P_p(α)/p!` for every `α ∈ K_0(Vect(X))`. -/
theorem chernCharacterRingHom_apply (α : VectorBundleKZero X) (p : ℕ) :
    chernCharacterRingHom C sX α p =
      ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ] modulePowerSumKGroupHom C sX p α p := by
  have h : (Pi.evalAddMonoidHom (fun q : ℕ ↦
        rationalChowCohomologyComponent C (gysinSystemOfInvertible C) sX (q : ℤ)) p).comp
        (chernCharacterRingHom C sX).toAddMonoidHom =
      ((TensorProduct.mk ℤ ℚ _ ((Nat.factorial p : ℚ)⁻¹)).toAddMonoidHom.comp
        (Pi.evalAddMonoidHom (fun q : ℕ ↦
          chowCohomologyComponent C (gysinSystemOfInvertible C) sX (q : ℤ)) p)).comp
        (modulePowerSumKGroupHom C sX p) := by
    refine VectorBundleKZero.addHom_ext fun M hM ↦ ?_
    change chernCharacterRingHom C sX (VectorBundleKZero.classOf X M) p =
      ((Nat.factorial p : ℚ)⁻¹) ⊗ₜ[ℤ]
        modulePowerSumKGroupHom C sX p (VectorBundleKZero.classOf X M) p
    rw [chernCharacterRingHom_classOf, modulePowerSumKGroupHom_classOf]
    rfl
  exact DFunLike.congr_fun h α

/-! ### Compatibility with pullback -/

variable {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] (f : Y ⟶ X)
  [LocallyOfFiniteType f] (hs : f ≫ sX = sY)

/-- **The power sums on `K_0(Vect(-))` commute with pullback**: `f^* P_p(α) = P_p(f^* α)`. -/
theorem modulePowerSumKGroupHom_pullback (p : ℕ) (α : VectorBundleKZero X) :
    TotalChowClass.res f hs (modulePowerSumKGroupHom C sX p α) =
      modulePowerSumKGroupHom C sY p (VectorBundleKZero.pullbackRingHom f α) := by
  have h : (TotalChowClass.res f hs).toAddMonoidHom.comp (modulePowerSumKGroupHom C sX p) =
      (modulePowerSumKGroupHom C sY p).comp
        (VectorBundleKZero.pullbackRingHom f).toAddMonoidHom := by
    refine VectorBundleKZero.addHom_ext fun M hM ↦ ?_
    have := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f M
    change TotalChowClass.res f hs
        (modulePowerSumKGroupHom C sX p (VectorBundleKZero.classOf X M)) =
      modulePowerSumKGroupHom C sY p
        (VectorBundleKZero.pullbackRingHom f (VectorBundleKZero.classOf X M))
    rw [VectorBundleKZero.pullbackRingHom_classOf f M hM, modulePowerSumKGroupHom_classOf,
      modulePowerSumKGroupHom_classOf, res_modulePowerSumArbitraryRank]
  exact DFunLike.congr_fun h α

/-- Two homomorphisms from `K_0(Vect(X))` into the units of a monoid, written additively, agree
when the values on the classes of finite locally free modules do. -/
theorem addHom_units_ext {R : Type*} [Monoid R]
    {φ ψ : VectorBundleKZero X →+ Additive Rˣ}
    (h : ∀ M : X.Modules, Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) M →
      ((Additive.toMul (φ (VectorBundleKZero.classOf X M)) : Rˣ) : R) =
        ((Additive.toMul (ψ (VectorBundleKZero.classOf X M)) : Rˣ) : R)) : φ = ψ := by
  refine AddMonoidHom.ext fun α ↦ ?_
  induction α using QuotientAddGroup.induction_on with
  | H x =>
    induction x using FreeAbelianGroup.induction_on with
    | zero => exact (map_zero φ).trans (map_zero ψ).symm
    | of M =>
      change φ (VectorBundleKZero.classOf X M) = ψ (VectorBundleKZero.classOf X M)
      by_cases hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M
      · exact Additive.toMul.injective (Units.ext (h M hM))
      · rw [VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M hM, map_zero, map_zero]
    | neg x ih => rw [QuotientAddGroup.mk_neg, map_neg, map_neg, ih]
    | add x y ihx ihy => rw [QuotientAddGroup.mk_add, map_add, map_add, ihx, ihy]

/-- **The Chern class map commutes with pullback**: `f^* c(α) = c(f^* α)`. -/
theorem totalChernKGroupMap_pullback (α : VectorBundleKZero X) :
    TotalChowClass.res f hs (totalChernKGroupMap C sX α) =
      totalChernKGroupMap C sY (VectorBundleKZero.pullbackRingHom f α) := by
  have h : (MonoidHom.toAdditive (Units.map (TotalChowClass.res f hs).toMonoidHom)).comp
        (totalChernKGroupHom C sX) =
      (totalChernKGroupHom C sY).comp (VectorBundleKZero.pullbackRingHom f).toAddMonoidHom := by
    refine addHom_units_ext fun M hM ↦ ?_
    have := isFiniteLocallyFree_pullback_of_isFiniteLocallyFree f M
    change TotalChowClass.res f hs (totalChernKGroupMap C sX (VectorBundleKZero.classOf X M)) =
      totalChernKGroupMap C sY
        (VectorBundleKZero.pullbackRingHom f (VectorBundleKZero.classOf X M))
    rw [VectorBundleKZero.pullbackRingHom_classOf f M hM, totalChernKGroupMap_classOf,
      totalChernKGroupMap_classOf, res_totalChernClassOfModule]
  exact congrArg (fun u : Additive (TotalChowClass C sY)ˣ ↦
    ((Additive.toMul u : (TotalChowClass C sY)ˣ) : TotalChowClass C sY)) (DFunLike.congr_fun h α)

end KGroup

/-! ### Filtrations with invertible quotients in `K_0(Vect(X))` -/

section Filtration

/-- A module with a filtration whose successive quotients are invertible is finite locally
free. -/
theorem isFiniteLocallyFree_of_hasInvertibleFiltration {P : Scheme.{u}} {E : P.Modules} {r : ℕ}
    (h : Stacks.WeilCohomology.HasInvertibleFiltration P E r) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := P.ringCatSheaf) E := by
  cases h with
  | nil E hE =>
    exact @Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _
      hE.isoZero.symm (VectorBundleKZero.isFiniteLocallyFree_zero P)
  | step f g w hS hL hE hF => exact hE

/-- **A filtration with invertible successive quotients `ℒ_j` gives `[ℰ] = ∑_j [ℒ_j]`** in
`K_0(Vect(P))`. -/
theorem exists_classOf_eq_sum_of_hasInvertibleFiltration {P : Scheme.{u}} {E : P.Modules} {r : ℕ}
    (h : Stacks.WeilCohomology.HasInvertibleFiltration P E r) :
    ∃ l : List P.Modules,
      (∀ L ∈ l, Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L) ∧
        VectorBundleKZero.classOf P E = (l.map (VectorBundleKZero.classOf P)).sum := by
  induction h with
  | nil E hE =>
    refine ⟨[], by simp, ?_⟩
    rw [List.map_nil, List.sum_nil,
      VectorBundleKZero.classOf_eq_of_iso hE.isoZero (by
        exact @Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _
          hE.isoZero.symm (VectorBundleKZero.isFiniteLocallyFree_zero P)),
      VectorBundleKZero.classOf_zero]
  | @step E F L r f g w hS hL hE hF ih =>
    obtain ⟨l, hl, hsum⟩ := ih
    have := hS.mono_f
    have := hS.epi_g
    have : Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L := hL
    refine ⟨L :: l, fun L' hL' ↦ ?_, ?_⟩
    · rcases List.mem_cons.mp hL' with rfl | hL'
      · exact hL
      · exact hl L' hL'
    · rw [VectorBundleKZero.classOf_shortExact f g w
        (isFiniteLocallyFree_of_hasInvertibleFiltration hF)
        hE
        (VectorBundleKZero.isFiniteLocallyFree_of_isInvertible L) hS.exact, hsum,
        List.map_cons, List.sum_cons, add_comm]

end Filtration

/-! ### The identities on classes of invertible modules -/

section Invertible

variable (C : ChowSituation.{u}) {P : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]

/-- An invertible module is finite locally free. -/
private theorem isFiniteLocallyFree_of_isInvertible {P : Scheme.{u}} (L : P.Modules)
    [Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} L := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L :=
    inferInstance
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible L
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1

/-- On the class of an invertible module, `c(ψ²[ℒ]) = c(ℒ ⊗ ℒ) = 1 + 2c₁(ℒ)` is the scaling of
`c(ℒ) = 1 + c₁(ℒ)`. -/
theorem totalChernKGroupMap_secondAdams_classOf_isInvertible (L : P.Modules)
    [Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L] :
    totalChernKGroupMap C sP
        (VectorBundleKZero.secondAdamsRingHom (VectorBundleKZero.squarePowersData P)
          (VectorBundleKZero.classOf P L)) =
      TotalChowClass.powScale 2 (totalChernKGroupMap C sP (VectorBundleKZero.classOf P L)) := by
  have := isFiniteLocallyFree_of_isInvertible L
  have := isFiniteLocallyFree_of_isInvertible (Scheme.Modules.tensorObj L L)
  rw [VectorBundleKZero.secondAdamsRingHom_apply,
    VectorBundleKZero.secondAdamsAddHom_classOf_isInvertible]
  change totalChernKGroupMap C sP (VectorBundleKZero.classOf P (Scheme.Modules.tensorObj L L)) = _
  rw [totalChernKGroupMap_classOf, totalChernKGroupMap_classOf,
    totalChernClassOfModule_eq_one_add_firstChernTotal,
    totalChernClassOfModule_eq_one_add_firstChernTotal,
    TotalChowClass.firstChernTotal_tensorObj, ← TotalChowClass.powScaleRingHom_apply, map_add,
    map_one, TotalChowClass.powScaleRingHom_apply,
    (TotalChowClass.isHomogeneous_firstChernTotal C sP L).powScale_eq, pow_one, two_smul]

/-- On the class of an invertible module, `P_p(ψ²[ℒ]) = P_p(ℒ ⊗ ℒ) = (2c₁(ℒ))^p = 2^p P_p(ℒ)`. -/
theorem modulePowerSumKGroupHom_secondAdams_classOf_isInvertible (p : ℕ) (L : P.Modules)
    [Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L] :
    modulePowerSumKGroupHom C sP p
        (VectorBundleKZero.secondAdamsRingHom (VectorBundleKZero.squarePowersData P)
          (VectorBundleKZero.classOf P L)) =
      (2 ^ p : ℤ) • modulePowerSumKGroupHom C sP p (VectorBundleKZero.classOf P L) := by
  have := isFiniteLocallyFree_of_isInvertible L
  have := isFiniteLocallyFree_of_isInvertible (Scheme.Modules.tensorObj L L)
  rw [VectorBundleKZero.secondAdamsRingHom_apply,
    VectorBundleKZero.secondAdamsAddHom_classOf_isInvertible]
  change modulePowerSumKGroupHom C sP p
    (VectorBundleKZero.classOf P (Scheme.Modules.tensorObj L L)) = _
  rw [modulePowerSumKGroupHom_classOf, modulePowerSumKGroupHom_classOf,
    modulePowerSumArbitraryRank_eq_pow,
    modulePowerSumArbitraryRank_eq_pow, TotalChowClass.firstChernTotal_tensorObj, ← two_smul ℤ,
    smul_pow]

/-- On a sum of classes of invertible modules, `c(ψ²(α))` is the scaling of `c(α)`. -/
theorem totalChernKGroupMap_secondAdams_sum (l : List P.Modules)
    (hl : ∀ L ∈ l, Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L) :
    totalChernKGroupMap C sP
        (VectorBundleKZero.secondAdamsRingHom (VectorBundleKZero.squarePowersData P)
          (l.map (VectorBundleKZero.classOf P)).sum) =
      TotalChowClass.powScale 2
        (totalChernKGroupMap C sP (l.map (VectorBundleKZero.classOf P)).sum) := by
  induction l with
  | nil =>
    rw [List.map_nil, List.sum_nil, map_zero, totalChernKGroupMap_zero,
      TotalChowClass.powScale_one]
  | cons L l ih =>
    have := hl L List.mem_cons_self
    rw [List.map_cons, List.sum_cons, map_add, totalChernKGroupMap_add, totalChernKGroupMap_add,
      ih fun L' hL' ↦ hl L' (List.mem_cons_of_mem L hL'),
      totalChernKGroupMap_secondAdams_classOf_isInvertible, TotalChowClass.powScale_mul]

/-- On a sum of classes of invertible modules, `P_p(ψ²(α)) = 2^p P_p(α)`. -/
theorem modulePowerSumKGroupHom_secondAdams_sum (p : ℕ) (l : List P.Modules)
    (hl : ∀ L ∈ l, Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L) :
    modulePowerSumKGroupHom C sP p
        (VectorBundleKZero.secondAdamsRingHom (VectorBundleKZero.squarePowersData P)
          (l.map (VectorBundleKZero.classOf P)).sum) =
      (2 ^ p : ℤ) • modulePowerSumKGroupHom C sP p (l.map (VectorBundleKZero.classOf P)).sum := by
  induction l with
  | nil => rw [List.map_nil, List.sum_nil, map_zero, map_zero, smul_zero]
  | cons L l ih =>
    have := hl L List.mem_cons_self
    rw [List.map_cons, List.sum_cons, map_add, map_add, map_add,
      ih fun L' hL' ↦ hl L' (List.mem_cons_of_mem L hL'),
      modulePowerSumKGroupHom_secondAdams_classOf_isInvertible, smul_add]

end Invertible

/-! ### The identities on generators, by the splitting principle -/

section Generators

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **The splitting family.** For a finite locally free `ℰ` on `X` and a rank `r`, a morphism
`γ : P ⟶ X` through the rank-`r` locus of `ℰ`, along which restriction of total classes composed
with restriction to the rank-`r` locus is injective, and along which `[ℰ]` becomes a sum of
classes of invertible modules. -/
theorem exists_splitting (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ULift.{u} ℕ) :
    ∃ (P : Scheme.{u}) (sP : P ⟶ C.S) (_ : LocallyOfFiniteType sP) (π : P ⟶ (rankLociFamily E r))
      (_ : LocallyOfFiniteType π) (hπ : π ≫ (rankLociFamily E r).ι ≫ sX = sP),
      Function.Injective (TotalChowClass.res π hπ) ∧
      ∃ l : List P.Modules,
        (∀ L ∈ l, Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L) ∧
          VectorBundleKZero.pullbackRingHom (π ≫ (rankLociFamily E r).ι)
              (VectorBundleKZero.classOf X E) = (l.map (VectorBundleKZero.classOf P)).sum := by
  have hr := isFiniteLocallyFreeOfRank_pullback_rankLociFamily E r
  obtain ⟨T, -, -, -, huniv, hfilt, -⟩ := exists_splittingMorphism_isProjective C
    ((rankLociFamily E r).ι ≫ sX) Unit
    (fun _ ↦ (Scheme.Modules.pullback (rankLociFamily E r).ι).obj E)
    (fun _ ↦ r.down) (fun _ ↦ hr)
  obtain ⟨l, hl, hsum⟩ := exists_classOf_eq_sum_of_hasInvertibleFiltration (hfilt ())
  refine ⟨T.P, T.sP, inferInstance, T.π, inferInstance, T.hsP,
    TotalChowClass.res_injective_of_universallyChowInjective T.π T.hsP _ T.relDim huniv, l, hl, ?_⟩
  rw [VectorBundleKZero.pullbackRingHom_classOf _ E inferInstance, ← hsum]
  exact VectorBundleKZero.classOf_eq_of_iso ((Scheme.Modules.pullbackComp _ _).app E).symm
    (VectorBundleKZero.isFiniteLocallyFree_pullback _ E inferInstance)

/-- **`c(ψ²[ℰ])` is the scaling of `c(ℰ)`** for a finite locally free `ℰ` of any rank. -/
theorem totalChernKGroupMap_secondAdams_classOf (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    totalChernKGroupMap C sX
        (VectorBundleKZero.secondAdamsRingHom (VectorBundleKZero.squarePowersData X)
          (VectorBundleKZero.classOf X E)) =
      TotalChowClass.powScale 2 (totalChernKGroupMap C sX (VectorBundleKZero.classOf X E)) := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily E) fun r ↦ ?_
  obtain ⟨P, sP, _, π, _, hπ, hinj, l, hl, hsum⟩ := exists_splitting C sX E r
  refine hinj ?_
  rw [TotalChowClass.res_res, TotalChowClass.res_res, TotalChowClass.res_powScale,
    totalChernKGroupMap_pullback,
    totalChernKGroupMap_pullback, ← RingHom.comp_apply,
    ← VectorBundleKZero.secondAdamsRingHom_comp_pullbackRingHom, RingHom.comp_apply, hsum]
  exact totalChernKGroupMap_secondAdams_sum C sP l hl

/-- **`P_p(ψ²[ℰ]) = 2^p P_p(ℰ)`** for a finite locally free `ℰ` of any rank. -/
theorem modulePowerSumKGroupHom_secondAdams_classOf (p : ℕ) (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    modulePowerSumKGroupHom C sX p
        (VectorBundleKZero.secondAdamsRingHom (VectorBundleKZero.squarePowersData X)
          (VectorBundleKZero.classOf X E)) =
      (2 ^ p : ℤ) • modulePowerSumKGroupHom C sX p (VectorBundleKZero.classOf X E) := by
  refine TotalChowClass.eq_of_res_eq (isClopenDecomposition_rankLociFamily E) fun r ↦ ?_
  obtain ⟨P, sP, _, π, _, hπ, hinj, l, hl, hsum⟩ := exists_splitting C sX E r
  refine hinj ?_
  rw [TotalChowClass.res_res, TotalChowClass.res_res, map_zsmul,
    modulePowerSumKGroupHom_pullback, modulePowerSumKGroupHom_pullback,
    ← RingHom.comp_apply, ← VectorBundleKZero.secondAdamsRingHom_comp_pullbackRingHom,
    RingHom.comp_apply, hsum]
  exact modulePowerSumKGroupHom_secondAdams_sum C sP p l hl

end Generators

/-! ### Stacks 0FEN -/

section Adams

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **`c(ψ²(α))` is the `2^i`-scaling of `c(α)`** for every `α ∈ K_0(Vect(X))`: both sides are
homomorphisms from `K_0(Vect(X))` to the units of `∏_{i ≥ 0} A^i(X)`, the scaling being a ring
map, and they agree on the generators. -/
theorem totalChernKGroupMap_secondAdams (α : VectorBundleKZero X) :
    totalChernKGroupMap C sX
        (VectorBundleKZero.secondAdamsRingHom (VectorBundleKZero.squarePowersData X) α) =
      TotalChowClass.powScale 2 (totalChernKGroupMap C sX α) := by
  have h : (totalChernKGroupHom C sX).comp
        (VectorBundleKZero.secondAdamsRingHom
          (VectorBundleKZero.squarePowersData X)).toAddMonoidHom =
      (MonoidHom.toAdditive (Units.map (TotalChowClass.powScaleRingHom (C := C) (sY := sX)
        2).toMonoidHom)).comp (totalChernKGroupHom C sX) := by
    refine addHom_units_ext fun M hM ↦ ?_
    exact totalChernKGroupMap_secondAdams_classOf C sX M
  exact congrArg (fun u : Additive (TotalChowClass C sX)ˣ ↦
    ((Additive.toMul u : (TotalChowClass C sX)ˣ) : TotalChowClass C sX)) (DFunLike.congr_fun h α)

/-- **`P_p(ψ²(α)) = 2^p P_p(α)`** for every `α ∈ K_0(Vect(X))`. -/
theorem modulePowerSumKGroupHom_secondAdams (p : ℕ) (α : VectorBundleKZero X) :
    modulePowerSumKGroupHom C sX p
        (VectorBundleKZero.secondAdamsRingHom (VectorBundleKZero.squarePowersData X) α) =
      (2 ^ p : ℤ) • modulePowerSumKGroupHom C sX p α := by
  have h : (modulePowerSumKGroupHom C sX p).comp
        (VectorBundleKZero.secondAdamsRingHom
          (VectorBundleKZero.squarePowersData X)).toAddMonoidHom =
      (2 ^ p : ℤ) • modulePowerSumKGroupHom C sX p := by
    refine VectorBundleKZero.addHom_ext fun M hM ↦ ?_
    exact modulePowerSumKGroupHom_secondAdams_classOf C sX p M
  exact DFunLike.congr_fun h α

/-- Let `(S, δ)` be as in Situation 02QL and let `X` be locally of finite type over `S`. Let `ψ²`
be the second Adams operator of Stacks 0FEJ
(`AlgebraicGeometry.VectorBundleKZero.secondAdamsRingHom` at
`AlgebraicGeometry.VectorBundleKZero.squarePowersData X`), and let `c` and `ch` be the maps of
Stacks 0FEL and Stacks 0FEM (`Stacks.Chow.totalChernKGroupMap`, into `∏_{i ≥ 0} A^i(X)`, and
`Stacks.Chow.chernCharacterRingHom`, into `∏_{i ≥ 0} A^i(X) ⊗ 𝐐`). Then for every
`α ∈ K_0(Vect(X))` and every `i`

  `c_i(ψ²(α)) = 2^i c_i(α)`  and  `ch_i(ψ²(α)) = 2^i ch_i(α)`,

the subscript `i` being the component in `A^i(X)`, resp. `A^i(X) ⊗ 𝐐`. -/
@[stacks 0FEN]
theorem chernClass_chernCharacter_secondAdams (α : VectorBundleKZero X) (i : ℕ) :
    totalChernKGroupMap C sX
        (VectorBundleKZero.secondAdamsRingHom (VectorBundleKZero.squarePowersData X) α) i =
      (2 ^ i : ℤ) • totalChernKGroupMap C sX α i ∧
    chernCharacterRingHom C sX
        (VectorBundleKZero.secondAdamsRingHom (VectorBundleKZero.squarePowersData X) α) i =
      (2 ^ i : ℤ) • chernCharacterRingHom C sX α i := by
  refine ⟨?_, ?_⟩
  · rw [totalChernKGroupMap_secondAdams, TotalChowClass.powScale_apply]
  · rw [chernCharacterRingHom_apply, chernCharacterRingHom_apply,
      modulePowerSumKGroupHom_secondAdams]
    change ((Nat.factorial i : ℚ)⁻¹) ⊗ₜ[ℤ] ((2 ^ i : ℤ) • modulePowerSumKGroupHom C sX i α i) = _
    rw [TensorProduct.tmul_smul]

end Adams

end Stacks.Chow

end
