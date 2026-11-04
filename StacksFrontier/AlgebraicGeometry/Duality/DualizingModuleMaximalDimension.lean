module

public import StacksFrontier.AlgebraicGeometry.CodimensionOneDivisor.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOfComplex
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkModel
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.RingTheory.Dualizing.NormalizedHomologyRange
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunctionIsCatenary
import StacksCore.Tactic.StacksAttribute

/-!
# The degree of a dualizing module is minus the maximal value of the dimension function

Let `X` be a locally Noetherian scheme with a dualizing complex `ω_X^•` and let `n` be the least
cohomological degree in which `ω_X^•` has nonvanishing cohomology, so that the dualizing module
of [Stacks, Section 48.22] is `ω_X = H^n(ω_X^•)`. The source states this twice over: `n` is that
least degree, and "in other words, `-n` is the maximal value of the dimension function associated
to `ω_X^•`", the function `δ` of [Stacks, Tag 0AWF]. This file proves that the two descriptions
agree, in the form `IsGreatest (Set.range δ) (-n)`, with
`δ = Stacks.Duality.associatedShiftFunction`.

## Main results

* `Stacks.Duality.isDualizingModuleOf_iff` — **[Stacks, Tag 0AWH]**, the definition:
  `ω_X = H^n(ω_X^•)` with `n` the least degree in which `ω_X^•` has nonzero cohomology.
* `Stacks.Duality.isGreatest_neg_of_isDualizingModuleOf` — **[Stacks, Tag 0AWH]**: if `ω` is a
  dualizing module of `K` in degree `n`, then `-n` is the greatest value of the dimension
  function attached to `K`.
* `Stacks.Duality.exists_isNormalizedDualizingComplex_stalk_homology` — the stalk at `x` of
  `H^i(K)` is `H^{i + δ(x)}` of a normalized dualizing complex over `𝒪_{X,x}`.

## The proof

Everything is read off the derived stalks of `K`, which by [Stacks, Tag 0AWF]
(`Stacks.Duality.isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction`) become
normalized dualizing complexes `L_x` over `𝒪_{X,x}` after the shift by `-δ(x)`, with `δ` a
dimension function. The stalk functor is exact, so the stalk of `H^i(K)` is `H^{i + δ(x)}(L_x)`.
Write `d = dim 𝒪_{X,x}`.

*`δ(x) ≤ -n` at every point.* The canonical module `H^{-d}(L_x)` is nonzero ([Stacks, Tag 0A7V]),
so `H^{-δ(x) - d}(K)` is not the zero sheaf, and `n ≤ -δ(x) - d ≤ -δ(x)`.

*`-n` is attained.* `H^n(K)` is nonzero, so it has a nonzero stalk at some `x`, and the degree
bound of [Stacks, Tag 0A7U] gives `δ(x) + d ≥ -n`. Since `d` is the codimension of
`closure {x}`, there is a chain of irreducible closed subsets of length `d` out of `closure {x}`,
along which the dimension function rises by at least one at each step ([Stacks, Tag 02IA]); at
the generic point `ξ` of its top `δ(ξ) ≥ δ(x) + d ≥ -n`.

## References

* [Stacks Project, Tag 0AWH](https://stacks.math.columbia.edu/tag/0AWH)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0A7V](https://stacks.math.columbia.edu/tag/0A7V)
* [Stacks Project, Tag 02IA](https://stacks.math.columbia.edu/tag/02IA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)
open Stacks.AlgebraicGeometry.CodimensionOneDivisor
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.Duality

/-- The local rings of a locally Noetherian scheme have finite Krull dimension: it is a natural
number. -/
theorem exists_natCast_ringKrullDim_stalk {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X) :
    ∃ d : ℕ, ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1
    (Ideal.height_ne_top_of_isPrime (I := IsLocalRing.maximalIdeal (X.presheaf.stalk x)))
  refine ⟨d, ?_⟩
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hd]
  rfl

/-- A sheaf of modules on a scheme is zero as soon as all its stalks are. -/
theorem isZero_of_forall_isZero_modulesStalkFunctor {X : Scheme.{u}} (F : X.Modules)
    (h : ∀ x : X, IsZero ((modulesStalkFunctor x).obj F)) : IsZero F := by
  have hiso : IsIso (0 : (0 : X.Modules) ⟶ F) := by
    refine (AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map
      X.ringCatSheaf _).mpr fun x => ?_
    have h1 : IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).obj F) := by
      have := h x
      rwa [ModuleCat.isZero_iff_subsingleton] at this ⊢
    exact isIso_of_source_target_iso_zero _ (Functor.map_isZero _ (isZero_zero _)).isoZero
      h1.isoZero
  exact (isZero_zero X.Modules).of_iso (asIso (0 : (0 : X.Modules) ⟶ F)).symm

/-- **The stalks of the cohomology sheaves of a dualizing complex.** At a point `x`, the stalk of
`H^i(K)` is `H^{i + δ(x)}` of a normalized dualizing complex over `𝒪_{X,x}`, where
`δ = associatedShiftFunction K` is the function of [Stacks, Tag 0AWF]: the normalized complex is
the shifted derived stalk `ω^•_{X,x}⟦-δ(x)⟧`, and the stalk functor is exact, so it commutes with
cohomology. -/
theorem exists_isNormalizedDualizingComplex_stalk_homology {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) :
    ∃ L : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x)),
      Dualizing.IsNormalizedDualizingComplex.{u, u} L ∧ ∀ i : ℤ,
        Nonempty ((modulesStalkFunctor x).obj
          ((DerivedCategory.homologyFunctor X.Modules i).obj K) ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x))
            (i + associatedShiftFunction K x)).obj L) := by
  obtain ⟨-, hnorm, -⟩ :=
    isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hK
  let E := DerivedCategory.Q.objPreimage K
  have hE : Nonempty (DerivedCategory.Q.obj E ≅ K) := ⟨DerivedCategory.Q.objObjPreimageIso K⟩
  exact ⟨(derivedStalkOfComplex x E)⟦-associatedShiftFunction K x⟧, (hnorm x E hE _).mpr rfl,
    fun i => ⟨(((modulesStalkFunctor x).mapDerivedCategoryHomologyIso i).app K).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso
        ((modulesStalkFunctor x).mapDerivedCategory.mapIso hE.some.symm ≪≫
          (modulesStalkFunctor x).mapDerivedCategoryFactors.app E) ≪≫
      (((DerivedCategory.homologyFunctor _ 0).shiftIso (-associatedShiftFunction K x)
        (i + associatedShiftFunction K x) i (by omega)).app _).symm⟩⟩

private theorem not_isZero_iff_nontrivial {A : Type u} [CommRing A] (M : ModuleCat.{u} A) :
    ¬ IsZero M ↔ Nontrivial M := by
  rw [ModuleCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]

/-- **The canonical module is a stalk of a cohomology sheaf.** If `dim 𝒪_{X,x} = d`, the stalk at
`x` of `H^{-d - δ(x)}(K)` is the canonical module of `𝒪_{X,x}` ([Stacks, Tag 0A7V]), which is
nonzero. -/
theorem not_isZero_stalk_homology_of_isDualizingComplex {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) (d : ℕ)
    (hd : ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞)) :
    ¬ IsZero ((modulesStalkFunctor x).obj ((DerivedCategory.homologyFunctor X.Modules
      (-(d : ℤ) - associatedShiftFunction K x)).obj K)) := by
  obtain ⟨L, hL, hiso⟩ := exists_isNormalizedDualizingComplex_stalk_homology hK x
  obtain ⟨φ⟩ := hiso (-(d : ℤ) - associatedShiftFunction K x)
  rw [sub_add_cancel] at φ
  exact fun hz => (not_isZero_iff_nontrivial _).mpr
    (Dualizing.nontrivial_homology_neg_ringKrullDim _ hL d hd) (hz.of_iso φ.symm)

/-- If the stalk at `x` of `H^i(K)` is nonzero and `dim 𝒪_{X,x} = d`, then `-d ≤ i + δ(x)`. -/
private theorem neg_le_add_associatedShiftFunction_of_not_isZero_stalk_homology {X : Scheme.{u}}
    [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) (d : ℕ)
    (hd : ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞)) (i : ℤ)
    (hi : ¬ IsZero ((modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj K))) :
    -(d : ℤ) ≤ i + associatedShiftFunction K x := by
  obtain ⟨L, hL, hiso⟩ := exists_isNormalizedDualizingComplex_stalk_homology hK x
  obtain ⟨φ⟩ := hiso i
  exact (Dualizing.mem_Icc_of_not_isZero_homology _ hL d hd _ fun hz => hi (hz.of_iso φ)).1

/-- **Below the canonical degree the stalks vanish.** If `dim 𝒪_{X,x} = d`, the stalk at `x` of
`H^j(K)` vanishes for `j < -d - δ(x)` ([Stacks, Tag 0A7U]). -/
theorem isZero_stalk_homology_of_lt {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (x : X) (d : ℕ) (hd : ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞)) (j : ℤ)
    (hj : j < -(d : ℤ) - associatedShiftFunction K x) :
    IsZero ((modulesStalkFunctor x).obj ((DerivedCategory.homologyFunctor X.Modules j).obj K)) := by
  by_contra hz
  have := neg_le_add_associatedShiftFunction_of_not_isZero_stalk_homology hK x d hd j hz
  omega

/-- **The dimension function is read off the stalks of the cohomology sheaves.** If at `x` the
stalk of `H^i(K)` is nonzero and the stalks of `H^j(K)` vanish for `j < i`, then
`δ(x) = -dim 𝒪_{X,x} - i`, for `δ = associatedShiftFunction K`. -/
theorem associatedShiftFunction_eq_of_stalk_homology {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (x : X) (d : ℕ) (hd : ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞)) (i : ℤ)
    (hi : ¬ IsZero ((modulesStalkFunctor x).obj ((DerivedCategory.homologyFunctor X.Modules i).obj
      K)))
    (hlt : ∀ j < i, IsZero ((modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor X.Modules j).obj K))) :
    associatedShiftFunction K x = -(d : ℤ) - i := by
  have hbd := neg_le_add_associatedShiftFunction_of_not_isZero_stalk_homology hK x d hd i hi
  have h₂ : i ≤ -(d : ℤ) - associatedShiftFunction K x := not_lt.mp fun h =>
    not_isZero_stalk_homology_of_isDualizingComplex hK x d hd (hlt _ h)
  omega

/-- **Stacks Project, Tag 0AWH, the definition.** Let `X` be a locally Noetherian scheme and `K`
a dualizing complex on `X`. Let `n` be the smallest integer such that `H^n(K)` is nonzero; then
`H^n(K)` is the dualizing module `ω_X`. This is what `Stacks.Duality.IsDualizingModuleOf ω K n`
says: it holds exactly when `K` is a dualizing complex, `n` is the least degree with nonzero
cohomology, and `ω = H^n(K)`. -/
@[stacks 0AWH "the definition the section states: omega_X = H^n(omega_X^bullet) with n the \
smallest integer such that H^n(omega_X^bullet) is nonzero, for a dualizing complex on a \
(locally) Noetherian scheme; IsDualizingModuleOf omega K n holds exactly when K is a dualizing \
complex, n is the least element of the set of degrees with nonzero cohomology, and omega is the \
cohomology sheaf in degree n"]
theorem isDualizingModuleOf_iff {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] (ω : X.Modules) (K : DerivedCategory X.Modules) (n : ℤ) :
    IsDualizingModuleOf ω K n ↔ IsDualizingComplex K ∧
      IsLeast {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)} n ∧
      ω = (DerivedCategory.homologyFunctor X.Modules n).obj K := by
  refine ⟨fun h => ⟨h.isDualizingComplex, ⟨h.nonzero, fun i hi => not_lt.mp fun hlt =>
    hi (h.isZero_of_lt i hlt)⟩, h.eq_homology⟩, ?_⟩
  rintro ⟨hK, ⟨hn, hleast⟩, hω⟩
  exact ⟨hK, hn, fun i hi => Classical.byContradiction fun hz => not_le.mpr hi (hleast hz), hω⟩

/-- **Stacks Project, Tag 0AWH.** Let `X` be a locally Noetherian scheme and let `ω` be a
dualizing module of the dualizing complex `K`, realized in degree `n`, the least degree in which
`K` has nonvanishing cohomology. Then `-n` is the maximal value of the dimension function attached
to `K` by [Stacks, Tag 0AWF], the function `δ = associatedShiftFunction K` with
`ω^•_{X,x}⟦-δ(x)⟧` a normalized dualizing complex over `𝒪_{X,x}`. -/
@[stacks 0AWH "the section's identification of the degree: -n is the maximal value of the \
dimension function attached to omega_X^bullet (Tag 0AWF), where n is the least degree in which \
the dualizing complex has nonvanishing cohomology. The dimension function is \
associatedShiftFunction K, which Tag 0AWF (isUniversallyCatenary_and_isDimensionFunction_\
associatedShiftFunction) shows is the normalizing shift of the derived stalks and a dimension \
function. Stated for a locally Noetherian scheme, which contains the source's Noetherian case"]
theorem isGreatest_neg_of_isDualizingModuleOf {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} X.Modules] {ω : X.Modules} {K : DerivedCategory X.Modules} {n : ℤ}
    (hω : IsDualizingModuleOf ω K n) :
    IsGreatest (Set.range (associatedShiftFunction K)) (-n) := by
  obtain ⟨-, -, δ, hδ⟩ :=
    isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hω.isDualizingComplex
  have hsober : StacksSober X :=
    stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩
  -- The upper bound: the canonical module of `𝒪_{X,x}` is a nonvanishing stalk in degree
  -- `-δ x - dim 𝒪_{X,x}`, so that degree is at least `n`.
  have hub : ∀ x : X, associatedShiftFunction K x ≤ -n := by
    intro x
    obtain ⟨d, hd⟩ := exists_natCast_ringKrullDim_stalk x
    have hne := not_isZero_stalk_homology_of_isDualizingComplex hω.isDualizingComplex x d hd
    by_contra hcon
    exact hne (Functor.map_isZero _ (hω.isZero_of_lt _ (by omega)))
  -- The value `-n` is attained at the generic point of a maximal chain out of a point where
  -- `H^n(K)` has a nonzero stalk.
  obtain ⟨x, hx⟩ : ∃ x : X, ¬ IsZero ((modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor X.Modules n).obj K)) := by
    by_contra hall
    push Not at hall
    exact hω.nonzero (isZero_of_forall_isZero_modulesStalkFunctor _ hall)
  obtain ⟨d, hd⟩ := exists_natCast_ringKrullDim_stalk x
  have hbd := neg_le_add_associatedShiftFunction_of_not_isZero_stalk_homology
    hω.isDualizingComplex x d hd n hx
  have hcod : (d : ℕ∞) ≤ codimension (closureSingleton x) := by
    refine le_of_eq (WithBot.coe_injective ?_).symm
    rwa [← ringKrullDim_stalk_eq_codimension_closureSingleton x]
  obtain ⟨p, hhead, hlen⟩ := (codimension_iff_exists_chain (closureSingleton x) d).mp hcod
  obtain ⟨ξ, hξ, -⟩ := sober_unique_generic_singleton hsober (p.last : Set X)
    p.last.isClosed' p.last.isIrreducible'
  have hchain : IsClosedIrreducibleChain p.length (fun i => (p i : Set X))
      (closure ({x} : Set X)) (closure ({ξ} : Set X)) :=
    isClosedIrreducibleChain_coe p (by rw [hhead, coe_closureSingleton]) hξ.symm
  have hgrow := chain_length_le_delta_diff hsober δ δ.isDimensionFunctionForCatenary ξ x
    p.length _ hchain
  rw [hlen, hδ, hδ] at hgrow
  have hlow : -n ≤ associatedShiftFunction K ξ := by omega
  exact ⟨⟨ξ, le_antisymm (hub ξ) hlow⟩, fun _ ⟨y, hy⟩ => hy ▸ hub y⟩

end Stacks.Duality

end
