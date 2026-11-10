module

public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleSupportSerre
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.RingTheory.Dualizing.NormalizedHomologyRange
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension

/-!
# Vanishing, support and Serre's condition for a dualizing module over a local base

Let `(A, 𝔪, κ)` be a Noetherian local ring with normalized dualizing complex `ω_A^•`, let
`S = Spec(A)` with `ω_S^•` the corresponding complex, let `f : X ⟶ S` be proper, let
`ω_X^• = f^! ω_S^•` and let `ω_X = H^{-dim(X)}(ω_X^•)`. This is the situation of
[Stacks, Tag 0AWI]; `Stacks.Duality.relativeDualizingComplex` and
`Stacks.Duality.relativeDualizingModule` are the two objects. The content of
[Stacks, Tag 0AWN] is then

1. `H^i(ω_X^•) ≠ 0` implies `i ∈ {-dim(X), …, 0}`,
2. the dimension of the support of `H^i(ω_X^•)` is at most `-i`,
3. `Supp(ω_X)` is the union of the irreducible components of `X` of dimension `dim(X)`,
4. `ω_X` has property `(S₂)`.

## Main definitions

* `Stacks.Duality.HasNormalizedStalks`: the local description of `ω_X^•` in the situation of
  [Stacks, Tag 0AWI]: `ω_X^•` is a dualizing complex, the dimension of `X` is `n`, and at every
  point `x` the derived stalk of `ω_X^•`, shifted by the dimension `e = dim(closure {x})` of the
  closure of `x`, is a normalized dualizing complex over `𝒪_{X,x}` ([Stacks, Tag 0AWL],
  [Stacks, Tag 0AWM]), with `e + dim(𝒪_{X,x}) ≤ n`.

## Main results

* `Stacks.Duality.mem_Icc_of_mem_supp_homology` and
  `Stacks.Duality.exists_bounds_of_nontrivial_stalk_homology`: the pointwise form of the two
  bounds, from the ring-level bounds of [Stacks, Tag 0A7U].
* `Stacks.Duality.mem_Icc_of_not_isZero_homology`: part (1).
* `Stacks.Duality.topologicalKrullDim_supp_homology_le`: part (2).
* `Stacks.Duality.supp_relativeDualizingModule_eq_setOf`: `Supp(ω_X)` is the set of points `x`
  with `dim(closure {x}) + dim(𝒪_{X,x}) = dim(X)`, the intrinsic form of part (3).
* `Stacks.Duality.supp_relativeDualizingModule_eq_topDimensionalComponents`:
  **[Stacks, Tag 0AWN], part (3)**, in the form of the source: the union of the components of
  dimension `dim(X)`.
* `Stacks.Duality.sheafHasPropertySk_two_homology_neg`: part (4), Serre's condition `(S₂)`
  (`AlgebraicGeometry.SheafHasPropertySk`, [Stacks, Tag 0341]) for `H^{-n}(ω_X^•)`, which is
  `ω_X` by `Stacks.Duality.relativeDualizingModule_eq_homology`.

## References

* [Stacks Project, Tag 0AWN](https://stacks.math.columbia.edu/tag/0AWN)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AWK](https://stacks.math.columbia.edu/tag/0AWK)
* [Stacks Project, Tag 0AWE](https://stacks.math.columbia.edu/tag/0AWE)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0AWL](https://stacks.math.columbia.edu/tag/0AWL)
* [Stacks Project, Tag 0AWM](https://stacks.math.columbia.edu/tag/0AWM)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0A7V](https://stacks.math.columbia.edu/tag/0A7V)
* [Stacks Project, Tag 0341](https://stacks.math.columbia.edu/tag/0341)
* [Stacks Project, Tag 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe w u

namespace Stacks.Duality

/-- The stalk of a sheaf of modules on a scheme at a point, as a module over the local ring. -/
abbrev moduleStalkAtPoint {X : Scheme.{u}} (F : X.Modules) (x : X) :=
  TopCat.Presheaf.stalk
    (_root_.SheafOfModules.val
      (R := structureSheafRing X.toRingedSpace)
      F).presheaf x

/-- The derived category of `A`-modules at the standard model of
`CategoryTheory.HasDerivedCategory.standard`. -/
abbrev StandardDerivedCategory (A : Type u) [CommRing A] : Type (u + 1) :=
  @DerivedCategory (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _)

/-- The degree-`i` cohomology of a complex of `A`-modules in the standard model
`Stacks.Duality.StandardDerivedCategory`. -/
abbrev standardHomology {A : Type u} [CommRing A] (L : StandardDerivedCategory A) (i : ℤ) :
    ModuleCat.{u} A :=
  (@DerivedCategory.homologyFunctor (ModuleCat.{u} A) _ _ (HasDerivedCategory.standard _) i).obj L

/-- **The local description of `ω_X^•` in the situation of [Stacks, Tag 0AWI].** The complex `K`
is a dualizing complex on the Noetherian scheme `X`, the dimension of `X` is `n`, and at every
point `x` the derived stalk of `K` is, after a shift by the dimension `e` of the closure of `x`,
a normalized dualizing complex over `𝒪_{X,x}`; moreover `e + dim(𝒪_{X,x}) ≤ n`.

The shift is recorded through its effect on cohomology: `H^i(K)_x ≃ H^{i + e}(L)` for every `i`,
where `L` is the normalized complex. -/
structure HasNormalizedStalks {X : Scheme.{u}} [IsNoetherian X]
    [HasDerivedCategory.{w} X.Modules] (K : DerivedCategory X.Modules) (n : ℕ) : Prop where
  /-- `n` is the dimension of `X`. -/
  dim_eq : topologicalKrullDim X = (n : WithBot ℕ∞)
  /-- `K` is a dualizing complex on `X`. -/
  isDualizingComplex : IsDualizingComplex K
  /-- At every point the derived stalk of `K`, shifted by the dimension of the closure of the
  point, is a normalized dualizing complex over the local ring. -/
  exists_normalized : ∀ x : X,
    ∃ (L : StandardDerivedCategory (X.presheaf.stalk x)) (e h : ℕ),
      _root_.Dualizing.IsNormalizedDualizingComplex.{u, u} L ∧
        topologicalKrullDim (closure ({x} : Set X)) = (e : WithBot ℕ∞) ∧
          ringKrullDim (X.presheaf.stalk x) = (h : WithBot ℕ∞) ∧ e + h ≤ n ∧
            ∀ i : ℤ, Nonempty
              (moduleStalkAtPoint ((DerivedCategory.homologyFunctor X.Modules i).obj K) x
                ≃ₗ[X.presheaf.stalk x] standardHomology L (i + (e : ℤ)))

variable {X : Scheme.{u}} [IsNoetherian X] [HasDerivedCategory.{w} X.Modules]
  {K : DerivedCategory X.Modules} {n : ℕ}

/-- **The two bounds at a point.** If the stalk of `H^i(K)` at `x` is nonzero, then the dimension
`e` of the closure of `x` and the dimension `h` of `𝒪_{X,x}` satisfy `e + h ≤ n` and
`-h ≤ i + e ≤ 0`. -/
theorem exists_bounds_of_nontrivial_stalk_homology (hloc : HasNormalizedStalks K n) (i : ℤ)
    (x : X)
    (hx : Nontrivial (moduleStalkAtPoint ((DerivedCategory.homologyFunctor X.Modules i).obj K) x)) :
    ∃ e h : ℕ, topologicalKrullDim (closure ({x} : Set X)) = (e : WithBot ℕ∞) ∧
      ringKrullDim (X.presheaf.stalk x) = (h : WithBot ℕ∞) ∧ e + h ≤ n ∧
        -(h : ℤ) ≤ i + (e : ℤ) ∧ i + (e : ℤ) ≤ 0 := by
  obtain ⟨L, e, h, hL, he, hh, hle, hiso⟩ := hloc.exists_normalized x
  obtain ⟨φ⟩ := hiso i
  have hnt := φ.toEquiv.nontrivial_congr.mp hx
  have hbd := _root_.Dualizing.mem_Icc_of_nontrivial_homology L hL h hh (i + (e : ℤ)) hnt
  exact ⟨e, h, he, hh, hle, hbd.1, hbd.2⟩

/-- A point in the support of `H^i(K)` forces `i ∈ {-n, …, 0}` and bounds the dimension of the
closure of that point by `-i`. -/
theorem mem_Icc_of_mem_supp_homology (hloc : HasNormalizedStalks K n) (i : ℤ) {x : X}
    (hx : x ∈ _root_.SheafOfModules.supp
      ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :
    i ∈ Set.Icc (-(n : ℤ)) 0 ∧
      topologicalKrullDim (closure ({x} : Set X)) ≤ ((Int.toNat (-i) : ℕ) : WithBot ℕ∞) := by
  have hnt := (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mp hx
  obtain ⟨e, h, he, hh, hle, hlow, hhigh⟩ :=
    exists_bounds_of_nontrivial_stalk_homology hloc i x hnt
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rw [he]
  exact_mod_cast (show e ≤ Int.toNat (-i) by omega)

/-- **Stacks Project, Tag 0AWN, part (1).** In the situation of [Stacks, Tag 0AWI] the complex
`ω_X^•` has cohomology only in degrees `-dim(X)` through `0`. -/
theorem mem_Icc_of_not_isZero_homology (hloc : HasNormalizedStalks K n) (i : ℤ)
    (hi : ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :
    i ∈ Set.Icc (-(n : ℤ)) 0 := by
  by_contra hcon
  refine hi (Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty _ ?_)
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  exact hcon (mem_Icc_of_mem_supp_homology hloc i hx).1

/-- **Stacks Project, Tag 0AWN, part (2).** In the situation of [Stacks, Tag 0AWI] the support of
`H^i(ω_X^•)` has dimension at most `-i`. -/
theorem topologicalKrullDim_supp_homology_le (hloc : HasNormalizedStalks K n) (i : ℤ) :
    topologicalKrullDim (_root_.SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules i).obj K)) ≤
      ((Int.toNat (-i) : ℕ) : WithBot ℕ∞) :=
  topologicalKrullDim_le_of_forall_closure
    (Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp_of_isCoherent _
      (isCoherent_homology_of_isDualizingComplex hloc.isDualizingComplex i))
    fun _ hx => (mem_Icc_of_mem_supp_homology hloc i hx).2

/-- The support of `H^{-n}(K)` is the set of points at which the dimension of the closure and the
dimension of the local ring add up to `n`. -/
theorem supp_homology_neg_eq_setOf (hloc : HasNormalizedStalks K n) :
    _root_.SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules (-(n : ℤ))).obj K) =
      {x : X | topologicalKrullDim (closure ({x} : Set X)) +
        ringKrullDim (X.presheaf.stalk x) = (n : WithBot ℕ∞)} := by
  ext x
  refine (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).trans ?_
  change _ ↔ topologicalKrullDim (closure ({x} : Set X)) +
    ringKrullDim (X.presheaf.stalk x) = (n : WithBot ℕ∞)
  constructor
  · intro hnt
    obtain ⟨e, h, he, hh, hle, hlow, -⟩ :=
      exists_bounds_of_nontrivial_stalk_homology hloc _ x hnt
    rw [he, hh, ← Nat.cast_add, show e + h = n by omega]
  · intro hsum
    obtain ⟨L, e, h, hL, he, hh, -, hiso⟩ := hloc.exists_normalized x
    obtain ⟨φ⟩ := hiso (-(n : ℤ))
    rw [he, hh] at hsum
    have hsum' : e + h = n := by exact_mod_cast hsum
    have hdeg : -(n : ℤ) + (e : ℤ) = -(h : ℤ) := by omega
    refine φ.toEquiv.nontrivial_congr.mpr ?_
    rw [hdeg]
    exact _root_.Dualizing.nontrivial_homology_neg_ringKrullDim L hL h hh

/-- The support of `H^{-n}(K)` is the union of the irreducible components of dimension `n`, once
the locus where the dimension of the closure and the dimension of the local ring add up to `n` is
known to be that union. -/
theorem supp_homology_neg_eq_topDimensionalComponents (hloc : HasNormalizedStalks K n)
    (hcomp : ∀ x : X, topologicalKrullDim (closure ({x} : Set X)) +
          ringKrullDim (X.presheaf.stalk x) = (n : WithBot ℕ∞) ↔
        x ∈ ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = (n : WithBot ℕ∞)}) :
    _root_.SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules (-(n : ℤ))).obj K) =
      ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = (n : WithBot ℕ∞)} := by
  rw [supp_homology_neg_eq_setOf hloc]
  exact Set.ext fun x => hcomp x

/-- **Serre's condition `(S₂)` for `H^{-n}(K)`.** If `K` has normalized stalks on `X` of
dimension `n`, then `H^{-n}(K)` satisfies Serre's condition `(S₂)`. -/
theorem sheafHasPropertySk_two_homology_neg (hloc : HasNormalizedStalks K n) :
    SheafHasPropertySk X ((DerivedCategory.homologyFunctor X.Modules (-(n : ℤ))).obj K) 2 := by
  intro x
  obtain ⟨L, e, h, hL, he, hh, hle, hiso⟩ := hloc.exists_normalized x
  obtain ⟨φ⟩ := hiso (-(n : ℤ))
  rcases eq_or_lt_of_le hle with heq | hlt
  · have hdeg : -(n : ℤ) + (e : ℤ) = -(h : ℤ) := by omega
    rw [hdeg] at φ
    have hdepth := _root_.Dualizing.min_two_le_depth_canonicalModule h L hL hh
    rw [← Module.depth_eq_depth_of_linearEquiv _ φ] at hdepth
    have hsupp := (Module.supportDim_eq_of_equiv φ).trans_le
      ((Module.supportDim_le_ringKrullDim _ _).trans (le_of_eq hh))
    rcases le_total (h : ℕ∞) 2 with hcase | hcase
    · refine (min_le_right _ _).trans (hsupp.trans ?_)
      rw [min_eq_left hcase] at hdepth
      exact_mod_cast hdepth
    · refine (min_le_left _ _).trans ?_
      rw [min_eq_right hcase] at hdepth
      exact WithBot.coe_le_coe.mpr hdepth
  · have hdeg : -(n : ℤ) + (e : ℤ) < -(h : ℤ) := by omega
    have hzero := _root_.Dualizing.isZero_homology_of_lt_neg_ringKrullDim L hL h hh
      (-(n : ℤ) + (e : ℤ)) hdeg
    have hsubL := ModuleCat.isZero_iff_subsingleton.mp hzero
    have := (φ.toEquiv.subsingleton_congr).mpr hsubL
    rw [Module.supportDim_eq_bot_of_subsingleton]
    exact (min_le_right _ _).trans bot_le

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The relative dualizing module of [Stacks, Tag 0AWI] is the cohomology of the relative
dualizing complex in degree `-n` once `n` is the dimension of `X`. -/
theorem relativeDualizingModule_eq_homology {Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} Y.Modules]
    (hpush : ∀ (M : quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor Y.Modules i).obj
        ((derivedPushforward f).obj M.obj)).IsQuasicoherent)
    [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint]
    (ωY : quasiCoherentDerivedCategory Y) (hdim : topologicalKrullDim X = (n : WithBot ℕ∞)) :
    relativeDualizingModule f hpush ωY =
      (DerivedCategory.homologyFunctor X.Modules (-(n : ℤ))).obj
        (relativeDualizingComplex f hpush ωY).obj := by
  rw [relativeDualizingModule]
  congr 2
  rw [hdim]
  rfl

section RelativeDualizing

variable {Y : Scheme.{u}} (f : X ⟶ Y) [HasDerivedCategory.{w} Y.Modules]
  (hpush : ∀ (M : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj M.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint]
  (ωY : quasiCoherentDerivedCategory Y)

/-- **The support of `ω_X`**, in the situation of [Stacks, Tag 0AWI]: the set of points `x` at
which `dim(closure {x}) + dim(𝒪_{X,x}) = dim(X)`. This is the intrinsic form of part (3) of
[Stacks, Tag 0AWN]. -/
theorem supp_relativeDualizingModule_eq_setOf
    (hloc : HasNormalizedStalks (relativeDualizingComplex f hpush ωY).obj n) :
    _root_.SheafOfModules.supp (relativeDualizingModule f hpush ωY) =
      {x : X | topologicalKrullDim (closure ({x} : Set X)) +
        ringKrullDim (X.presheaf.stalk x) = (n : WithBot ℕ∞)} := by
  rw [relativeDualizingModule_eq_homology f hpush ωY hloc.dim_eq]
  exact supp_homology_neg_eq_setOf hloc

/-- **Stacks Project, Tag 0AWN, part (3).** Let `X/A` with `ω_X^•` and `ω_X` be as in
[Stacks, Tag 0AWI]. Then `Supp(ω_X)` is the union of the irreducible components of `X` of
dimension `dim(X)`, given the hypothesis `hcomp` that a point `x` satisfies
`dim(closure {x}) + dim(𝒪_{X,x}) = dim(X)` exactly when it lies on an irreducible component of `X`
of dimension `dim(X)`. -/
@[stacks 0AWN "part (3): Supp(omega_X) is the union of the components of dimension dim(X). \
RESTRICTED: two explicit hypotheses. hloc is the local description of omega_X^bullet, a \
Stacks.Duality.HasNormalizedStalks; see part (1) for what it records and why. hcomp is a \
statement about a catenary Noetherian scheme with no dualizing complex in it -- that a point \
satisfies dim(closure {x}) + dim(O_{X,x}) = dim(X) exactly when it lies on an irreducible \
component of dimension dim(X); its analogue over a Noetherian local ring is the catenary step \
inside Dualizing.support_canonicalModule of Tag 0AWE, but the scheme-level statement is not \
proved here. The dualizing content is proved and is unconditional given hloc: \
supp_relativeDualizingModule_eq_setOf identifies Supp(omega_X) with the locus where that \
equality holds, by the lower degree bound of Tag 0A7U and the nonvanishing of the canonical \
module of Tag 0A7V on the stalk"]
theorem supp_relativeDualizingModule_eq_topDimensionalComponents
    (hloc : HasNormalizedStalks (relativeDualizingComplex f hpush ωY).obj n)
    (hcomp : ∀ x : X, topologicalKrullDim (closure ({x} : Set X)) +
          ringKrullDim (X.presheaf.stalk x) = (n : WithBot ℕ∞) ↔
        x ∈ ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = (n : WithBot ℕ∞)}) :
    _root_.SheafOfModules.supp (relativeDualizingModule f hpush ωY) =
      ⋃₀ {C ∈ irreducibleComponents X | topologicalKrullDim C = (n : WithBot ℕ∞)} := by
  rw [relativeDualizingModule_eq_homology f hpush ωY hloc.dim_eq]
  exact supp_homology_neg_eq_topDimensionalComponents hloc hcomp

end RelativeDualizing

end Stacks.Duality

end
