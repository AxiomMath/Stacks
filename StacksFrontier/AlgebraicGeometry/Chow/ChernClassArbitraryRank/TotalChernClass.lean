module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.BivariantPowerSum
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.BoundedComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernCommutation
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ComplexChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.IndependenceKTheory
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalClassPieces
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TotalChernWhitney
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Modules.PullbackShortExactFlatScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# The total Chern class of a finite locally free module of arbitrary rank

Let `(S, δ)` be as in Situation 02QL, let `X` be locally of finite type over `S` and let `ℰ` be a
finite locally free `𝒪_X`-module, of rank not necessarily constant. Write
`X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …` for the decomposition into the open and closed loci where the rank of
`ℰ` is `r`. By Stacks 0FDZ a total Chow cohomology class `∏_{p ≥ 0} A^p(X)` is the same thing as
a family of total classes on the `X_r`, and **Stacks 0ESW** defines the total Chern class

  `c(ℰ) = c_0(ℰ) + c_1(ℰ) + c_2(ℰ) + … ∈ ∏_{p ≥ 0} A^p(X)`

as the class whose restriction to `X_r` is the total Chern class `c(ℰ|_{X_r})` of the
constant-rank module `ℰ|_{X_r}`; its degree-`p` component is the class `c_p(ℰ)` of Stacks 0ESW
(`Stacks.Chow.totalChernClassOfModule_apply`).

The Whitney sum formula, **Stacks 02UI**, holds for these classes as an identity of total Chow
cohomology classes: for a short exact sequence `0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free
modules, `c(ℰ) = c(ℰ₁) c(ℰ₂)`. In constant ranks this is checked on the operations on every test
scheme `g : T ⟶ X`, where it is the Whitney sum formula for the cap products of Stacks 02U6
applied to the pulled back sequence; that sequence is short exact because its quotient is finite
locally free (Stacks 0G6R). In arbitrary ranks it follows by restricting to the open and closed
loci where both `ℰ₁` and `ℰ₂` have constant rank. In particular any two total Chern classes
commute.

## Main definitions

* `Stacks.Chow.jointRankLocus` — the open and closed loci where two finite locally free modules
  have prescribed ranks.
* `Stacks.Chow.rankLocusGenuineChernClass` — the constant-rank Chern classes `c_j(ℰ|_{X_r})` of
  Stacks 0B7H on the rank loci.
* `Stacks.Chow.chernClassOfModule` — **Stacks 0ESW**, the class `c_p(ℰ) ∈ A^p(X)` assembled from
  them.
* `Stacks.Chow.totalChernClassOfModule` — **Stacks 0ESW**, the total Chern class `c(ℰ)`.

## Main results

* `Stacks.Chow.totalChernClassOfModule_apply` — the degree-`p` component of `c(ℰ)` is `c_p(ℰ)`.
* `Stacks.Chow.totalChernClassOfModule_apply_zero` — `c_0(ℰ) = 1`.
* `Stacks.Chow.res_totalChernClassOfModule_of_rank` — along a morphism `h` with `h^*ℰ` of
  constant rank `r`, the restriction of `c(ℰ)` is the total Chern class of `h^*ℰ` of rank `r`.
* `Stacks.Chow.totalChernClassOfModule_eq_totalChern` — on a module of constant rank, `c(ℰ)` is
  the total Chern class of Stacks 0B7H.
* `Stacks.Chow.isUnit_totalChernClassOfModule` — `c(ℰ)` is a unit.
* `Stacks.Chow.totalChern_eq_mul_of_shortExact` — **Stacks 02UI**: `c(ℰ) = c(ℰ₁) c(ℰ₂)` in
  `∏_{p ≥ 0} A^p(X)` for `ℰ₁`, `ℰ₂` of constant ranks.
* `Stacks.Chow.totalChernClassOfModule_eq_mul_of_shortExact` — the same with no hypothesis on the
  ranks.
* `Stacks.Chow.totalChernClassOfModule_commute` — `c(ℰ) c(ℱ) = c(ℱ) c(ℰ)`.

## References

* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 02UI](https://stacks.math.columbia.edu/tag/02UI)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The loci where two modules have prescribed ranks -/

section JointRank

variable {X : Scheme.{u}} (E F : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F]

/-- The open and closed locus `X_{a,b}` where `E` has rank `a` and `F` has rank `b`, indexed by
`ULift (ℕ × ℕ)` so that the family lies in the universe of the scheme. -/
def jointRankLocus : ULift.{u} (ℕ × ℕ) → X.Opens := fun ab ↦
  rankLocus E ab.down.1 ⊓ rankLocus F ab.down.2

/-- The loci `X_{a,b}` decompose `X` into open and closed subschemes. -/
theorem isClopenDecomposition_jointRankLocus : IsClopenDecomposition (jointRankLocus E F) where
  disjoint i j hij := Opens.coe_disjoint.mp <| Set.disjoint_left.mpr fun x hx hy ↦ by
    rw [SetLike.mem_coe, jointRankLocus, Opens.mem_inf, mem_rankLocus, mem_rankLocus] at hx hy
    exact hij (ULift.ext (Prod.ext (hx.1.symm.trans hy.1) (hx.2.symm.trans hy.2)))
  iSup_eq_top := by
    apply top_le_iff.mp
    intro x _
    simp only [Opens.mem_iSup]
    exact ⟨ULift.up (moduleRank E x, moduleRank F x),
      Opens.mem_inf.2 ⟨(mem_rankLocus E).2 rfl, (mem_rankLocus F).2 rfl⟩⟩

variable {E} in
/-- On an open subscheme contained in the rank-`r` locus, the module has constant rank `r`. -/
theorem isFiniteLocallyFreeOfRank_of_le_rankLocus {V : X.Opens} {r : ℕ}
    (hV : V ≤ rankLocus E r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback V.ι).obj E) r :=
  AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq E V r
    fun x hx ↦ by rw [fiberRank_eq_moduleRank E x]; exact hV hx

variable {C : ChowSituation.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- **A total class is determined on the loci of constant rank of two modules.** If two total
classes have the same restriction to every open subscheme on which both `E` and `F` have constant
rank, they are equal. -/
theorem TotalChowClass.eq_of_res_eq_of_rank {c d : TotalChowClass C sX}
    (h : ∀ (V : X.Opens) (a b : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj E) a →
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj F) b →
      TotalChowClass.res V.ι rfl c = TotalChowClass.res V.ι rfl d) : c = d :=
  TotalChowClass.eq_of_res_eq (isClopenDecomposition_jointRankLocus E F) fun ab ↦
    h _ ab.down.1 ab.down.2 (isFiniteLocallyFreeOfRank_of_le_rankLocus inf_le_left)
      (isFiniteLocallyFreeOfRank_of_le_rankLocus inf_le_right)

end JointRank

/-! ### The total Chern class -/

section TotalChernClass

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The constant-rank Chern classes `c_j(ℰ|_{X_r}) ∈ A^j(X_r)` of Stacks 0B7H on the rank loci of
`ℰ`, built from the cap products of Stacks 02U6, in the form Stacks 0ESW assembles. -/
def rankLocusGenuineChernClass (r : ℕ) (j : Fin (r + 1)) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) ((rankLocus E r).ι ≫ sX) (j : ℤ) :=
  haveI := isFiniteLocallyFreeOfRank_pullback_rankLocus E r
  GenuineChern.chernClass C ((rankLocus E r).ι ≫ sX)
    ((Scheme.Modules.pullback (rankLocus E r).ι).obj E) r j

/-- **Stacks 0ESW.** The Chern class `c_p(ℰ) ∈ A^p(X)` of a finite locally free module whose rank
need not be constant: the class whose component on the rank-`r` locus `X_r` is the Chern class
`c_p(ℰ|_{X_r})` of Stacks 0B7H, zero when `r < p`. -/
def chernClassOfModule (p : ℕ) :
    chowCohomologyComponent C (gysinSystemOfInvertible C) sX (p : ℤ) :=
  chernClassArbitraryRank C (gysinSystemOfInvertible C) sX E
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C)
    (rankLocusGenuineChernClass C sX E) p

/-- **Stacks 0ESW, the total Chern class.** The total Chern class
`c(ℰ) = c_0(ℰ) + c_1(ℰ) + c_2(ℰ) + … ∈ ∏_{p ≥ 0} A^p(X)` of a finite locally free module of
arbitrary rank: the total class whose restriction to each rank locus `X_r` is the total Chern
class `c(ℰ|_{X_r})` of the module `ℰ|_{X_r}` of constant rank `r`, assembled by Stacks 0FDZ. -/
def totalChernClassOfModule : TotalChowClass C sX :=
  TotalChowClass.glue (isClopenDecomposition_rankLociFamily E) fun r ↦
    haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj E) r.down :=
      isFiniteLocallyFreeOfRank_pullback_rankLociFamily E r
    totalChern C ((rankLociFamily E r).ι ≫ sX)
      ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj E) r.down

/-- The restriction of `c(ℰ)` to the rank-`r` locus is the total Chern class of `ℰ|_{X_r}`. -/
theorem res_totalChernClassOfModule_rankLocus (r : ULift.{u} ℕ) :
    haveI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj E) r.down :=
      isFiniteLocallyFreeOfRank_pullback_rankLociFamily E r
    TotalChowClass.res (rankLociFamily E r).ι rfl (totalChernClassOfModule C sX E) =
      totalChern C ((rankLociFamily E r).ι ≫ sX)
        ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj E) r.down :=
  TotalChowClass.res_glue (isClopenDecomposition_rankLociFamily E) _ r

/-- Restriction to a rank locus in the sense of Stacks 0FDZ is the restriction map of Stacks 0B7F
along the inclusion of the locus. -/
theorem rankLocusRestriction_eq_res (c : TotalChowClass C sX) (p r : ℕ) :
    rankLocusRestriction C (gysinSystemOfInvertible C) sX E
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (p : ℤ) (c p) r =
      TotalChowClass.res (rankLociFamily E (ULift.up r)).ι rfl c p := by
  rw [TotalChowClass.res_rfl_apply]
  exact (chowCohomologyRestriction_eq_pieceIdentityCongr (rankLociFamily E) (c p)
    (ULift.up r)).symm

/-- Two Chow cohomology classes are equal if their restrictions to every rank locus are. -/
private theorem eq_of_rankLocusRestriction_eq_of_invertible {p : ℤ}
    {c d : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p}
    (h : ∀ r : ℕ, rankLocusRestriction C (gysinSystemOfInvertible C) sX E
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) p c r =
      rankLocusRestriction C (gysinSystemOfInvertible C) sX E
        (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) p d r) : c = d :=
  eq_of_rankLocusRestriction_eq C (gysinSystemOfInvertible C) sX E
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C)
    (gysinSystemOfInvertible_isNaturalUnderOpensRestriction C)
    (gysinSystemOfInvertible_isNaturalUnderPullbackComp C) p h

/-- **The components of `c(ℰ)` are the Chern classes of Stacks 0ESW**: the degree-`p` component
of the total Chern class is `c_p(ℰ)`. -/
theorem totalChernClassOfModule_apply (p : ℕ) :
    totalChernClassOfModule C sX E p = chernClassOfModule C sX E p := by
  refine eq_of_rankLocusRestriction_eq_of_invertible C sX E fun r ↦ ?_
  rw [chernClassOfModule, rankLocusRestriction_chernClassArbitraryRank]
  rw [rankLocusRestriction_eq_res, res_totalChernClassOfModule_rankLocus]
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily E (ULift.up r)).ι).obj E) r :=
    isFiniteLocallyFreeOfRank_pullback_rankLociFamily E (ULift.up r)
  by_cases h : p ≤ r
  · rw [rankLocusChernFamily_of_le C _ sX E _ p r h]
    exact totalChern_apply C _ _ r ⟨p, Nat.lt_succ_of_le h⟩
  · rw [rankLocusChernFamily_of_lt C _ sX E _ p r (by omega)]
    exact totalChern_apply_of_lt C _ _ r (by omega)

/-- **`c_0(ℰ) = 1`**: the degree-`0` component of the total Chern class is the class
`1 ∈ A^0(X)`. -/
theorem totalChernClassOfModule_apply_zero :
    totalChernClassOfModule C sX E 0 = (1 : TotalChowClass C sX) 0 := by
  refine eq_of_rankLocusRestriction_eq_of_invertible C sX E fun r ↦ ?_
  rw [rankLocusRestriction_eq_res, rankLocusRestriction_eq_res, map_one,
    res_totalChernClassOfModule_rankLocus]
  have := isFiniteLocallyFreeOfRank_pullback_rankLociFamily E (ULift.up r)
  exact totalChern_apply_zero C _ _ r

/-- **Characterization of `c(ℰ)`.** For every `h : Y' ⟶ X` locally of finite type along which
`h^*ℰ` has constant rank `r`, the restriction of `c(ℰ)` along `h` is the total Chern class of the
module `h^*ℰ` of rank `r`. -/
theorem res_totalChernClassOfModule_of_rank {Y' : Scheme.{u}} {sY' : Y' ⟶ C.S}
    [LocallyOfFiniteType sY']
    (h : Y' ⟶ X) [LocallyOfFiniteType h] (hs : h ≫ sX = sY') (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback h).obj E) r] :
    TotalChowClass.res h hs (totalChernClassOfModule C sX E) =
      totalChern C sY' ((Scheme.Modules.pullback h).obj E) r := by
  have hU := isClopenDecomposition_rankLociFamily E
  refine TotalChowClass.eq_of_res_eq (hU.preimage h) fun ρ ↦ ?_
  have ha : ∀ ρ, h ⁻¹ᵁ rankLociFamily E ρ ≤ h ⁻¹ᵁ rankLociFamily E (id ρ) := fun _ ↦ le_rfl
  have hfac : (h ⁻¹ᵁ rankLociFamily E ρ).ι ≫ h =
      pieceMap h (fun ρ ↦ h ⁻¹ᵁ rankLociFamily E ρ) (rankLociFamily E) id ha ρ ≫
        (rankLociFamily E ρ).ι :=
    (pieceMap_comp_ι h _ _ id ha ρ).symm
  have hpm : pieceMap h (fun ρ ↦ h ⁻¹ᵁ rankLociFamily E ρ) (rankLociFamily E) id ha ρ ≫
      ((rankLociFamily E ρ).ι ≫ sX) = (h ⁻¹ᵁ rankLociFamily E ρ).ι ≫ sY' := by
    rw [← Category.assoc, ← hfac, Category.assoc, hs]
  rw [TotalChowClass.res_res, TotalChowClass.res_congr hfac _ (by rw [Category.assoc, hpm]),
    ← TotalChowClass.res_res (rankLociFamily E ρ).ι rfl _ hpm,
    res_totalChernClassOfModule_rankLocus]
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (rankLociFamily E ρ).ι).obj E) ρ.down :=
    isFiniteLocallyFreeOfRank_pullback_rankLociFamily E ρ
  rw [TotalChowClass.res_totalChern, TotalChowClass.res_totalChern]
  have h₁ := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
    (pieceMap h (fun ρ ↦ h ⁻¹ᵁ rankLociFamily E ρ) (rankLociFamily E) id ha ρ)
    ((Scheme.Modules.pullback (rankLociFamily E ρ).ι).obj E) ρ.down
  have h₂ := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (h ⁻¹ᵁ rankLociFamily E ρ).ι
    ((Scheme.Modules.pullback h).obj E) r
  have e := pullbackPullbackIsoOfComp hfac.symm E
  rcases isEmpty_or_nonempty (h ⁻¹ᵁ rankLociFamily E ρ : Scheme.{u}) with hW | ⟨⟨x⟩⟩
  · have := TotalChowClass.subsingleton_of_isEmpty (C := C) ((h ⁻¹ᵁ rankLociFamily E ρ).ι ≫ sY')
    exact Subsingleton.elim _ _
  · exact totalChern_congr C _ e (Scheme.Modules.isFiniteLocallyFreeOfRank_unique _
      (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e h₁) h₂ x)

/-- **On a module of constant rank `r`, `c(ℰ)` is the total Chern class of Stacks 0B7H** of the
module of rank `r`. -/
theorem totalChernClassOfModule_eq_totalChern (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    totalChernClassOfModule C sX E = totalChern C sX E r := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (𝟙 X)).obj E) r :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (𝟙 X) E r
  rw [← TotalChowClass.res_id (totalChernClassOfModule C sX E),
    res_totalChernClassOfModule_of_rank C sX E (𝟙 X) (Category.id_comp sX) r]
  exact totalChern_congr C sX ((Scheme.Modules.pullbackId X).app E) rfl

/-- **`c(ℰ)` is a unit** of the ring `∏_{p ≥ 0} A^p(X)`: its inverse is glued from the inverses of
the total Chern classes of the modules `ℰ|_{X_r}` of constant rank. -/
@[sga "7 XVII 5.3" "more general"]
theorem isUnit_totalChernClassOfModule : IsUnit (totalChernClassOfModule C sX E) := by
  have hU := isClopenDecomposition_rankLociFamily E
  let v : ∀ r : ULift.{u} ℕ, (TotalChowClass C ((rankLociFamily E r).ι ≫ sX))ˣ := fun r ↦
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj E) r.down :=
      isFiniteLocallyFreeOfRank_pullback_rankLociFamily E r
    totalChernUnit C ((rankLociFamily E r).ι ≫ sX)
      ((Scheme.Modules.pullback (rankLociFamily E r).ι).obj E) r.down
  let d := TotalChowClass.glue hU fun r ↦ ((v r)⁻¹ : (TotalChowClass C _)ˣ).val
  have hres : ∀ r, TotalChowClass.res (rankLociFamily E r).ι rfl (totalChernClassOfModule C sX E) =
      (v r).val := fun r ↦ res_totalChernClassOfModule_rankLocus C sX E r
  have h1 : totalChernClassOfModule C sX E * d = 1 := TotalChowClass.eq_of_res_eq hU fun r ↦ by
    rw [map_mul, map_one, hres, TotalChowClass.res_glue hU, Units.mul_inv]
  have h2 : d * totalChernClassOfModule C sX E = 1 := TotalChowClass.eq_of_res_eq hU fun r ↦ by
    rw [map_mul, map_one, hres, TotalChowClass.res_glue hU, Units.inv_mul]
  exact ⟨⟨_, d, h1, h2⟩, rfl⟩

end TotalChernClass

/-! ### The Whitney sum formula -/

section Whitney

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **Stacks 02UI, the Whitney sum formula.** For a short exact sequence
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of modules with `ℰ₁`, `ℰ₂` finite locally free of ranks `r₁`, `r₂` (so
that `ℰ` is finite locally free of rank `r₁ + r₂`), the total Chern classes satisfy
`c(ℰ) = c(ℰ₁) c(ℰ₂)` in the ring `∏_{p ≥ 0} A^p(X)` of total Chow cohomology classes. -/
theorem totalChern_eq_mul_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (r₁ r₂ : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ r₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ r₂] :
    haveI := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact S hS r₁ r₂ ‹_› ‹_›
    totalChern C sX S.X₂ (r₁ + r₂) = totalChern C sX S.X₁ r₁ * totalChern C sX S.X₃ r₂ := by
  have := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact S hS r₁ r₂ ‹_› ‹_›
  refine TotalChowClass.ext_op fun g _ ↦ ?_
  rw [TotalChowClass.op_mul, op_totalChern, op_totalChern, op_totalChern]
  have hS' : (S.map (Scheme.Modules.pullback g)).ShortExact :=
    Scheme.Modules.shortExact_map_pullback_of_finiteLocallyFree g S hS
      (GenuineChern.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank S.X₃ r₂)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (S.map (Scheme.Modules.pullback g)).X₁ r₁ :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g S.X₁ r₁
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (S.map (Scheme.Modules.pullback g)).X₃ r₂ :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g S.X₃ r₂
  exact GenuineChern.chernFamily_eq_mul_of_shortExact C (g ≫ sX)
    (S.map (Scheme.Modules.pullback g)) hS' r₁ r₂

/-- **Stacks 02UI, for modules of arbitrary rank.** For a short exact sequence
`0 ⟶ ℰ₁ ⟶ ℰ ⟶ ℰ₂ ⟶ 0` of finite locally free modules, whose ranks need not be constant,
`c(ℰ) = c(ℰ₁) c(ℰ₂)` in `∏_{p ≥ 0} A^p(X)`. On the open and closed loci where `ℰ₁` and `ℰ₂` have
constant ranks this is `Stacks.Chow.totalChern_eq_mul_of_shortExact`. -/
theorem totalChernClassOfModule_eq_mul_of_shortExact (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₂]
    [hE₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃] :
    totalChernClassOfModule C sX S.X₂ =
      totalChernClassOfModule C sX S.X₁ * totalChernClassOfModule C sX S.X₃ := by
  refine TotalChowClass.eq_of_res_eq_of_rank S.X₁ S.X₃ fun V a b ha hb ↦ ?_
  have hS' : (S.map (Scheme.Modules.pullback V.ι)).ShortExact :=
    Scheme.Modules.shortExact_map_pullback_of_finiteLocallyFree V.ι S hS
      ⟨hE₃.exists_isFiniteLocallyFreeData⟩
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (S.map (Scheme.Modules.pullback V.ι)).X₁ a := ha
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (S.map (Scheme.Modules.pullback V.ι)).X₃ b := hb
  have h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback V.ι).obj S.X₂) (a + b) :=
    GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact _ hS' a b ‹_› ‹_›
  rw [map_mul, res_totalChernClassOfModule_of_rank C sX S.X₂ V.ι rfl (a + b),
    res_totalChernClassOfModule_of_rank C sX S.X₁ V.ι rfl a,
    res_totalChernClassOfModule_of_rank C sX S.X₃ V.ι rfl b]
  exact totalChern_eq_mul_of_shortExact C (V.ι ≫ sX) (S.map (Scheme.Modules.pullback V.ι)) hS' a b

/-- **Total Chern classes of constant rank commute**, both products being `c(ℰ ⊕ ℱ)`. -/
theorem totalChern_commute (E F : X.Modules) (r s : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F s] :
    Commute (totalChern C sX E r) (totalChern C sX F s) := by
  have := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
    (ShortComplex.mk (biprod.inl : E ⟶ E ⊞ F) (biprod.snd : E ⊞ F ⟶ F) (by simp))
    (ShortComplex.Splitting.ofHasBinaryBiproduct E F).shortExact r s ‹_› ‹_›
  have := GenuineChern.isFiniteLocallyFreeOfRank_of_shortExact
    (ShortComplex.mk (biprod.inl : F ⟶ F ⊞ E) (biprod.snd : F ⊞ E ⟶ E) (by simp))
    (ShortComplex.Splitting.ofHasBinaryBiproduct F E).shortExact s r ‹_› ‹_›
  show totalChern C sX E r * totalChern C sX F s = totalChern C sX F s * totalChern C sX E r
  rw [← totalChern_biprod C sX E F r s, ← totalChern_biprod C sX F E s r]
  exact totalChern_congr C sX (biprod.braiding E F) (Nat.add_comm r s)

/-- **Total Chern classes commute**: `c(ℰ) c(ℱ) = c(ℱ) c(ℰ)` for finite locally free modules of
arbitrary ranks. -/
theorem totalChernClassOfModule_commute (E F : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F] :
    Commute (totalChernClassOfModule C sX E) (totalChernClassOfModule C sX F) := by
  show totalChernClassOfModule C sX E * totalChernClassOfModule C sX F =
    totalChernClassOfModule C sX F * totalChernClassOfModule C sX E
  refine TotalChowClass.eq_of_res_eq_of_rank E F fun V a b ha hb ↦ ?_
  rw [map_mul, map_mul, res_totalChernClassOfModule_of_rank C sX E V.ι rfl a,
    res_totalChernClassOfModule_of_rank C sX F V.ι rfl b]
  exact totalChern_commute C (V.ι ≫ sX) _ _ a b

end Whitney

end Stacks.Chow

end
