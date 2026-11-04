module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankChartSectionsConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank
public import StacksFrontier.RingTheory.Fitting.Rank

/-!
# Fitting ideal sheaves and finite locally free modules on an algebraic space

Let `F` be an algebraic space and let `G` be a quasi-coherent `𝒪_F`-module on its small étale
site.  Being finite locally free of rank `r` is equivalent to each of two conditions on the
Fitting ideal sheaves `AlgebraicGeometry.Space.fittingIdeal`: that the `(r-1)`-st vanishes and
the `r`-th is the unit ideal sheaf, and that they vanish below `r` and are the unit ideal sheaf
from `r` onward.

The proof is étale-local.  Each of the three conditions is translated into a statement about the
module-theoretic Fitting ideals of the sections of `G` over the affine étale charts of `F`,
membership in a sheaf of ideals being a local condition; for the first that translation is the
rank form of Descent, Proposition 03DX (2),
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff_freeRankPresieve`.  The chartwise
equivalence is then `finiteLocallyFreeOfRank_fittingIdeal_tfae`.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_tfae_fittingIdeal`: finite local freeness of
  rank `r` of a quasi-coherent `𝒪_F`-module is equivalent to each of the two conditions on its
  Fitting ideal sheaves.

## Implementation notes

**No finiteness hypothesis.**  Finiteness of the sections over a chart, which the chartwise
Fitting ideal presupposes, is produced by the conditions themselves, exactly as in the
scheme-level statement of Tag 0C3G: a section which is the unit of the ring of sections and is
also required to vanish forces that ring, and hence the module of sections, to be zero.  The
statement is therefore stronger than the source's, which assumes `G` of finite type.

**The shape of the second condition.**  The Fitting ideal sheaves of this development are indexed
by the natural numbers, so the source's condition at index `r - 1` has to be guarded at `r = 0`,
where truncated subtraction would read it as the condition at index `0`.  The guard is the
disjunct `r = 0`, as in the scheme-level statement of Tag 0C3G, and it matches the convention
that Fitting ideals at negative indices vanish.

**Universes.**  The rank clause of Stacks 0409 takes its module at the universe of the structure
rings of the ringed site, so the module universe here is the universe `u` of the schemes.

## References

* [Stacks Project, Tag 0CZ8](https://stacks.math.columbia.edu/tag/0CZ8)
* [Stacks Project, Tag 0C3G](https://stacks.math.columbia.edu/tag/0C3G)
* [Stacks Project, Tag 07ZD](https://stacks.math.columbia.edu/tag/07ZD)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory Opposite

universe u m t u₁ v₁

/-! ### Extremal submodules of a sheaf of modules -/

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{t}}

/-- The zero submodule of a sheaf of modules: its membership condition is local because a section
vanishing along a covering sieve vanishes. -/
private def zeroSubmodule (M : SheafOfModules.{m} R) : M.Submodule where
  toSubmodule := ⊥
  isSheaf := by
    intro X s hs
    obtain rfl : s = 0 := by
      refine M.isSheaf.isSeparated _ _ hs s 0 fun Y f hf => ?_
      have hf' : M.val.map f.op s ∈ (⊥ : M.val.Submodule).obj (op Y) := hf
      have h0 : M.val.map f.op s = 0 := (_root_.Submodule.mem_bot _).mp hf'
      change M.val.map f.op s = M.val.map f.op 0
      rw [h0, map_zero]
    exact _root_.Submodule.zero_mem _

/-- The whole of a sheaf of modules, as a submodule of itself. -/
private def univSubmodule (M : SheafOfModules.{m} R) : M.Submodule where
  toSubmodule := ⊤
  isSheaf := fun _ _ _ => _root_.Submodule.mem_top

/-- A section of the zero submodule of a sheaf of modules vanishes. -/
private theorem eq_zero_of_mem_bot_obj {M : SheafOfModules.{m} R} (X : Cᵒᵖ)
    {x : M.val.obj X} (hx : x ∈ (⊥ : M.Submodule).toSubmodule.obj X) : x = 0 :=
  (_root_.Submodule.mem_bot _).mp
    ((PresheafOfModules.Submodule.le_iff.mp
      (le_iff.mp (bot_le : (⊥ : M.Submodule) ≤ zeroSubmodule M))) X hx)

/-- Every section lies in the top submodule of a sheaf of modules. -/
private theorem mem_top_obj {M : SheafOfModules.{m} R} (X : Cᵒᵖ) (x : M.val.obj X) :
    x ∈ (⊤ : M.Submodule).toSubmodule.obj X :=
  (PresheafOfModules.Submodule.le_iff.mp (le_iff.mp (le_top : univSubmodule M ≤ ⊤))) X
    _root_.Submodule.mem_top

end SheafOfModules.Submodule

/-! ### The module-theoretic equivalence, indexed by the natural numbers -/

/-- **Stacks 07ZD, indexed by the natural numbers.**  A finite module over a commutative ring is
finite locally free of rank `r` exactly when its Fitting ideals jump from the zero ideal to the
unit ideal at `r`, and exactly when they vanish below `r` and are the unit ideal from `r` onward.

The condition at index `r - 1` is read with truncated subtraction, so it is guarded by the
disjunct `r = 0`, under which it is vacuous. -/
@[sga "7 VI 5.1" "5.1(b), special case"]
private theorem module_fittingIdeal_tfae_nat {A : Type u} {M : Type m} [CommRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] (r : ℕ) :
    List.TFAE [
      Module.IsFiniteLocallyFreeOfRank A M r,
      (r = 0 ∨ fittingIdeal (R := A) (M := M) ((r - 1 : ℕ) : ℤ) = ⊥) ∧
        fittingIdeal (R := A) (M := M) (r : ℤ) = ⊤,
      (∀ k : ℕ, k < r → fittingIdeal (R := A) (M := M) (k : ℤ) = ⊥) ∧
        (∀ k : ℕ, r ≤ k → fittingIdeal (R := A) (M := M) (k : ℤ) = ⊤)] := by
  have hstd := finiteLocallyFreeOfRank_fittingIdeal_tfae (R := A) (M := M) r
  have hcast : 0 < r → ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := fun hr => by omega
  have hpair : (fittingIdeal (R := A) (M := M) ((r : ℤ) - 1) = ⊥ ∧
      fittingIdeal (R := A) (M := M) (r : ℤ) = ⊤) ↔
      ((r = 0 ∨ fittingIdeal (R := A) (M := M) ((r - 1 : ℕ) : ℤ) = ⊥) ∧
        fittingIdeal (R := A) (M := M) (r : ℤ) = ⊤) := by
    constructor
    · rintro ⟨hlo, hhi⟩
      exact ⟨(Nat.eq_zero_or_pos r).imp id fun hr => by rwa [hcast hr], hhi⟩
    · rintro ⟨hlo, hhi⟩
      refine ⟨?_, hhi⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · simp [fittingIdeal]
      · rcases hlo with h0 | hb
        · omega
        · rwa [hcast hr] at hb
  have hall : ((∀ k : ℤ, k < r → fittingIdeal (R := A) (M := M) k = ⊥) ∧
      (∀ k : ℤ, (r : ℤ) ≤ k → fittingIdeal (R := A) (M := M) k = ⊤)) ↔
      ((∀ k : ℕ, k < r → fittingIdeal (R := A) (M := M) (k : ℤ) = ⊥) ∧
        (∀ k : ℕ, r ≤ k → fittingIdeal (R := A) (M := M) (k : ℤ) = ⊤)) := by
    constructor
    · rintro ⟨hbot, htop⟩
      exact ⟨fun k hk => hbot k (by exact_mod_cast hk),
        fun k hk => htop k (by exact_mod_cast hk)⟩
    · rintro ⟨hbot, htop⟩
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · rcases lt_or_ge k 0 with h0 | h0
        · simp [fittingIdeal, h0]
        · have h := hbot k.toNat (by omega)
          rwa [Int.toNat_of_nonneg h0] at h
      · have h0 : (0 : ℤ) ≤ k := by omega
        have h := htop k.toNat (by omega)
        rwa [Int.toNat_of_nonneg h0] at h
  tfae_have 1 ↔ 2 := (hstd.out 1 2).trans hpair
  tfae_have 2 ↔ 3 := hpair.symm.trans ((hstd.out 2 3).trans hall)
  tfae_finish

/-- The Fitting ideals of a finite locally free module of rank `r` vanish below `r` and are the
unit ideal from `r` onward. -/
@[sga "7 VI 5.1" "5.1(b), special case"]
private theorem fittingIdeal_bot_and_top_of_isFiniteLocallyFreeOfRank {A : Type u} {M : Type m}
    [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] {r : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank A M r) :
    (∀ k : ℕ, k < r → fittingIdeal (R := A) (M := M) (k : ℤ) = ⊥) ∧
      (∀ k : ℕ, r ≤ k → fittingIdeal (R := A) (M := M) (k : ℤ) = ⊤) :=
  ((module_fittingIdeal_tfae_nat (A := A) (M := M) r).out 1 3).mp h

/-- A finite module whose `(r-1)`-st Fitting ideal vanishes and whose `r`-th Fitting ideal is the
unit ideal is finite locally free of rank `r`. -/
private theorem isFiniteLocallyFreeOfRank_of_fittingIdeal {A : Type u} {M : Type m}
    [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] {r : ℕ}
    (hlo : r = 0 ∨ fittingIdeal (R := A) (M := M) ((r - 1 : ℕ) : ℤ) = ⊥)
    (hhi : fittingIdeal (R := A) (M := M) (r : ℤ) = ⊤) :
    Module.IsFiniteLocallyFreeOfRank A M r := by
  have h := (module_fittingIdeal_tfae_nat (A := A) (M := M) r).out 2 1
  exact h.mp ⟨hlo, hhi⟩

/-- A module over a ring in which the unit vanishes is finite, being a zero module. -/
private theorem module_finite_of_one_eq_zero {A : Type u} [CommRing A] {M : Type m}
    [AddCommGroup M] [Module A M] (h : (1 : A) = 0) : Module.Finite A M := by
  have : Subsingleton M :=
    ⟨fun x y => by rw [← one_smul A x, ← one_smul A y, h, zero_smul, zero_smul]⟩
  have _ : Finite M := inferInstance
  infer_instance

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The chartwise reading of finite local freeness -/

/-- An étale chart of `F` whose underlying scheme is affine. -/
private abbrev AffineChart :=
  {W : SmallEtale B S hS F //
    IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)}

/-- The affine étale charts over which the sections of `G` form a finite locally free module of
rank `r`, as a presieve on an étale chart. -/
private def freeRankPresieve (G : Modules.{u, u} B S hS F hF) (r : ℕ)
    (U : SmallEtale B S hS F) : Presieve U :=
  fun V _ => IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V) ∧
    Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF V) (G.val.obj (op V)) r

/-- The chartwise Fitting ideal of the sections of `G` over an étale chart, extended by the zero
ideal over the charts whose sections are not a finite module. -/
private noncomputable def fitOrBot (G : Modules.{u, u} B S hS F hF) (k : ℕ)
    (W : SmallEtale B S hS F) : Ideal (chartRing B S hS F hF W) :=
  ⨆ h : Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)),
    @fittingIdealOnChart B S hS F hF G k W h

private theorem fitOrBot_eq_fittingIdealOnChart (G : Modules.{u, u} B S hS F hF) (k : ℕ)
    (W : SmallEtale B S hS F)
    (h : Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W))) :
    fitOrBot B S hS F hF G k W = @fittingIdealOnChart B S hS F hF G k W h :=
  iSup_pos h

private theorem fitOrBot_eq_bot (G : Modules.{u, u} B S hS F hF) (k : ℕ)
    (W : SmallEtale B S hS F)
    (h : ¬ Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W))) :
    fitOrBot B S hS F hF G k W = ⊥ :=
  iSup_neg h

/-- Over an affine chart on which the sections of `G` are finite locally free of rank `r`, the
chartwise Fitting ideals vanish below `r` and are the unit ideal from `r` onward. -/
private theorem fittingIdealOnChart_bot_and_top_of_isFiniteLocallyFreeOfRank
    (G : Modules.{u, u} B S hS F hF) {r : ℕ} {W : SmallEtale B S hS F}
    (hW : Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF W) (G.val.obj (op W)) r)
    (hfin : Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W))) :
    (∀ k : ℕ, k < r → @fittingIdealOnChart B S hS F hF G k W hfin = ⊥) ∧
      (∀ k : ℕ, r ≤ k → @fittingIdealOnChart B S hS F hF G k W hfin = ⊤) :=
  fittingIdeal_bot_and_top_of_isFiniteLocallyFreeOfRank hW

/-! ### From the chartwise reading to the Fitting ideal sheaves -/

/-- A section of the structure sheaf lies in a sheaf of ideals as soon as, for a covering by affine
charts with finite locally free sections, its restrictions to the members of the covering do. -/
private theorem mem_of_restrict_mem_freeRankPresieve
    (G : Modules.{u, u} B S hS F hF) {r : ℕ}
    (h1 : ∀ U : SmallEtale B S hS F,
      Sieve.generate (freeRankPresieve B S hS F hF G r U) ∈ SmallEtale.topology B S hS F U)
    {U : SmallEtale B S hS F} (I : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (b : chartRing B S hS F hF U)
    (h : ∀ {W : SmallEtale B S hS F} (a : W ⟶ U), freeRankPresieve B S hS F hF G r U a →
      chartRestrict (hF := hF) a b ∈ I.toSubmodule.obj (op W)) :
    b ∈ I.toSubmodule.obj (op U) := by
  have hsub : Sieve.generate (freeRankPresieve B S hS F hF G r U) ≤
      I.toSubmodule.toSubfunctor.sieveOfSection b := by
    rintro Z g ⟨W, g', a, ha, rfl⟩
    have hgoal : chartRestrict (hF := hF) (g' ≫ a) b ∈ I.toSubmodule.obj (op Z) := by
      rw [chartRestrict_comp]
      exact I.toSubmodule.map_mem g'.op (h a ha)
    exact hgoal
  exact I.isSheaf b (GrothendieckTopology.superset_covering _ hsub (h1 U))

/-- **A vanishing chartwise Fitting ideal over the members of a covering forces the Fitting ideal
sheaf to vanish.**  The chartwise Fitting ideal over an affine chart restricts into the chartwise
Fitting ideal over the affine charts of a covering, so if the latter vanish, the former consists
of sections vanishing locally, hence lying in every sheaf of ideals. -/
private theorem fittingIdeal_eq_bot_of_freeRankPresieve
    (G : Modules.{u, u} B S hS F hF) (hG : IsCartesianOnAffineCharts G) {r : ℕ}
    (h1 : ∀ U : SmallEtale B S hS F,
      Sieve.generate (freeRankPresieve B S hS F hF G r U) ∈ SmallEtale.topology B S hS F U)
    {k : ℕ} (hk : k < r) :
    fittingIdeal B S hS F hF G k = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [← sInf_univ]
  refine le_sInf fun I _ => fittingIdeal_le G k fun V hV b hbfin hb => ?_
  have := hbfin
  refine mem_of_restrict_mem_freeRankPresieve B S hS F hF G h1 I b fun a ⟨hWaff, hWfree⟩ => ?_
  have := hWfree.finite
  have hmap := fittingIdealOnChart_map_le_of_surjective_chartBaseChange G k a
    (hG V _ hV hWaff a).2 (Ideal.mem_map_of_mem _ hb)
  rw [(fittingIdealOnChart_bot_and_top_of_isFiniteLocallyFreeOfRank B S hS F hF G hWfree
    hWfree.finite).1 k hk] at hmap
  rw [(_root_.Submodule.mem_bot _).mp hmap]
  exact (I.toSubmodule.obj _).zero_mem

/-- **A unit chartwise Fitting ideal over the members of a covering forces the Fitting ideal sheaf
to be the unit ideal sheaf.**  Every section of the structure sheaf restricts into the chartwise
Fitting ideal over the affine charts of the covering, hence lies locally in every sheaf of ideals
containing the chartwise Fitting ideals, hence lies in it. -/
private theorem fittingIdeal_eq_top_of_freeRankPresieve
    (G : Modules.{u, u} B S hS F hF) {r : ℕ}
    (h1 : ∀ U : SmallEtale B S hS F,
      Sieve.generate (freeRankPresieve B S hS F hF G r U) ∈ SmallEtale.topology B S hS F U)
    {k : ℕ} (hk : r ≤ k) :
    fittingIdeal B S hS F hF G k = ⊤ := by
  have key : ∀ (U : SmallEtale B S hS F) (a : chartRing B S hS F hF U),
      a ∈ (fittingIdeal B S hS F hF G k).toSubmodule.obj (op U) := by
    intro U a
    rw [mem_fittingIdeal_iff]
    intro I hI
    refine mem_of_restrict_mem_freeRankPresieve B S hS F hF G h1 I a fun b ⟨hWaff, hWfree⟩ => ?_
    have := hWfree.finite
    refine hI _ hWaff _ hWfree.finite ?_
    rw [(fittingIdealOnChart_bot_and_top_of_isFiniteLocallyFreeOfRank B S hS F hF G hWfree
      hWfree.finite).2 k hk]
    trivial
  exact le_antisymm le_top (SheafOfModules.Submodule.le_iff.mpr
    (PresheafOfModules.Submodule.le_iff.mpr fun X x _ => key X.unop x))

/-! ### From the Fitting ideal sheaves to the chartwise reading -/

/-- The sections of the structure sheaf which restrict into the chartwise Fitting ideal over every
affine étale chart below the given one.

Over a chart whose sections are not a finite module the chartwise Fitting ideal is not defined,
and the sections demanded there are the vanishing ones; this is what lets finiteness be
*recovered* from the Fitting conditions. -/
private noncomputable def chartwiseFittingSubmodule (G : Modules.{u, u} B S hS F hF) (k : ℕ) :
    (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).val.Submodule where
  obj X :=
    { carrier := {a | ∀ (W : AffineChart B S hS F) (g : W.1 ⟶ X.unop),
        chartRestrict (hF := hF) g a ∈ fitOrBot B S hS F hF G k W.1}
      add_mem' := fun {x y} ha hb W g => by
        let x' : chartRing B S hS F hF X.unop := x
        let y' : chartRing B S hS F hF X.unop := y
        have hgoal : chartRestrict (hF := hF) g (x' + y') ∈
            fitOrBot B S hS F hF G k W.1 := by
          rw [map_add (chartRestrict (hF := hF) g) x' y']
          exact Ideal.add_mem _ (ha W g) (hb W g)
        exact hgoal
      zero_mem' := fun W g => by
        change chartRestrict (hF := hF) g (0 : chartRing B S hS F hF X.unop) ∈ _
        rw [map_zero]
        exact Ideal.zero_mem _
      smul_mem' := fun c x ha W g => by
        let c' : chartRing B S hS F hF X.unop := c
        let x' : chartRing B S hS F hF X.unop := x
        have hgoal : chartRestrict (hF := hF) g (c' * x') ∈
            fitOrBot B S hS F hF G k W.1 := by
          rw [map_mul (chartRestrict (hF := hF) g) c' x']
          exact Ideal.mul_mem_left _ _ (ha W g)
        exact hgoal }
  map {X Y} f := fun a ha W g =>
    (DFunLike.congr_fun (chartRestrict_comp (hF := hF) f.unop g) a) ▸ ha W (g ≫ f.unop)

private theorem mem_chartwiseFittingSubmodule_iff (G : Modules.{u, u} B S hS F hF) (k : ℕ)
    (X : (smallEtaleRingedSite B S hS F hF).Cᵒᵖ)
    (a : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).val.obj X) :
    a ∈ (chartwiseFittingSubmodule B S hS F hF G k).obj X ↔
      ∀ (W : AffineChart B S hS F) (g : W.1 ⟶ X.unop),
        chartRestrict (hF := hF) g a ∈ fitOrBot B S hS F hF G k W.1 := Iff.rfl

/-- The chartwise Fitting ideal over an affine chart is contained in the sections of
`AlgebraicGeometry.Space.chartwiseFittingSubmodule` over that chart: a module cartesian on affine
charts has its chartwise Fitting ideals carried into one another by restriction. -/
private theorem mem_chartwiseFittingSubmodule_of_mem_fittingIdealOnChart
    (G : Modules.{u, u} B S hS F hF) (hG : IsCartesianOnAffineCharts G) (k : ℕ)
    {V : SmallEtale B S hS F}
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (b : chartRing B S hS F hF V)
    (hbfin : Module.Finite (chartRing B S hS F hF V) (G.val.obj (op V)))
    (hb : b ∈ @fittingIdealOnChart B S hS F hF G k V hbfin) :
    b ∈ (chartwiseFittingSubmodule B S hS F hF G k).obj (op V) := by
  have := hbfin
  refine (mem_chartwiseFittingSubmodule_iff B S hS F hF G k (op V) b).mpr ?_
  rintro ⟨W, hW⟩ g
  have hWfin : Module.Finite (chartRing B S hS F hF W) (G.val.obj (op W)) :=
    module_finite_sections_of_bijective_chartBaseChange G g (hG V W hV hW g)
  have := hWfin
  rw [fitOrBot_eq_fittingIdealOnChart B S hS F hF G k W hWfin]
  exact fittingIdealOnChart_map_le_of_surjective_chartBaseChange G k g
    (hG V W hV hW g).2 (Ideal.mem_map_of_mem _ hb)

/-- **The Fitting conditions produce the chartwise reading of finite local freeness.**  If the
`r`-th Fitting ideal sheaf is the unit ideal sheaf and the `(r-1)`-st vanishes, then the affine
charts over which the sections of `G` are finite locally free of rank `r` cover every object of
the small étale site. -/
private theorem freeRankPresieve_mem_topology_of_fittingIdeal
    (G : Modules.{u, u} B S hS F hF) (hG : IsCartesianOnAffineCharts G) (r : ℕ)
    (hlo : r = 0 ∨ fittingIdeal B S hS F hF G (r - 1) = ⊥)
    (hhi : fittingIdeal B S hS F hF G r = ⊤) (U : SmallEtale B S hS F) :
    Sieve.generate (freeRankPresieve B S hS F hF G r U) ∈ SmallEtale.topology B S hS F U := by
  have hle : fittingIdeal B S hS F hF G r ≤
      Stacks.SheafOfModules.localClosure _ (chartwiseFittingSubmodule B S hS F hF G r) := by
    refine fittingIdeal_le G r fun V hV b hbfin hb => ?_
    refine (Stacks.SheafOfModules.mem_localClosure_obj
      (chartwiseFittingSubmodule B S hS F hF G r) (op V) b).mpr ?_
    refine GrothendieckTopology.superset_covering _ ?_
      (GrothendieckTopology.top_mem (SmallEtale.topology B S hS F) V)
    intro Y g _
    exact (chartwiseFittingSubmodule B S hS F hF G r).map_mem g.op
      (mem_chartwiseFittingSubmodule_of_mem_fittingIdealOnChart B S hS F hF G hG r hV b hbfin hb)
  have hone0 : (1 : chartRing B S hS F hF U) ∈
      (fittingIdeal B S hS F hF G r).toSubmodule.obj (op U) := by
    rw [hhi]
    exact SheafOfModules.Submodule.mem_top_obj (op U) _
  have hone := (PresheafOfModules.Submodule.le_iff.mp
    (SheafOfModules.Submodule.le_iff.mp hle)) (op U) hone0
  have hcov : (chartwiseFittingSubmodule B S hS F hF G r).toSubfunctor.sieveOfSection
      (1 : chartRing B S hS F hF U) ∈ SmallEtale.topology B S hS F U :=
    (Stacks.SheafOfModules.mem_localClosure_obj
      (chartwiseFittingSubmodule B S hS F hF G r) (op U)
      (1 : chartRing B S hS F hF U)).mp hone
  refine GrothendieckTopology.transitive _ hcov _ fun Z f hf => ?_
  obtain ⟨ι, Yf, aY, hYaff, hYcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS F Z
  refine GrothendieckTopology.superset_covering _ ?_ hYcov
  rintro T t ht
  obtain ⟨T', g, h, hmem, rfl⟩ := ht
  obtain ⟨j⟩ := hmem
  have hf' : chartRestrict (hF := hF) f (1 : chartRing B S hS F hF U) ∈
      (chartwiseFittingSubmodule B S hS F hF G r).obj (op Z) := hf
  have hsat := (mem_chartwiseFittingSubmodule_iff B S hS F hF G r (op Z) _).mp hf'
    ⟨Yf j, hYaff j⟩ (aY j)
  rw [map_one, map_one] at hsat
  have hfinj : Module.Finite (chartRing B S hS F hF (Yf j)) (G.val.obj (op (Yf j))) := by
    by_contra hcon
    rw [fitOrBot_eq_bot B S hS F hF G r (Yf j) hcon] at hsat
    exact hcon (module_finite_of_one_eq_zero ((_root_.Submodule.mem_bot _).mp hsat))
  rw [fitOrBot_eq_fittingIdealOnChart B S hS F hF G r (Yf j) hfinj] at hsat
  have htopj : @fittingIdealOnChart B S hS F hF G r (Yf j) hfinj = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr hsat
  have hbotj : r = 0 ∨ @fittingIdealOnChart B S hS F hF G (r - 1) (Yf j) hfinj = ⊥ := by
    refine hlo.imp id fun hbot => le_antisymm (fun x hx => ?_) bot_le
    have hx' : x ∈ (fittingIdeal B S hS F hF G (r - 1)).toSubmodule.obj (op (Yf j)) :=
      mem_fittingIdeal_of_mem_fittingIdealOnChart G (r - 1) (Yf j) (hYaff j) x hx
    rw [hbot] at hx'
    exact (_root_.Submodule.mem_bot _).mpr
      (SheafOfModules.Submodule.eq_zero_of_mem_bot_obj (op (Yf j)) hx')
  exact ⟨Yf j, g, aY j ≫ f, ⟨hYaff j, isFiniteLocallyFreeOfRank_of_fittingIdeal hbotj htopj⟩,
    (Category.assoc g (aY j) f).symm⟩

/-! ### The equivalence -/

/-- **Stacks Project, Tag 0CZ8.**  Let `F` be an algebraic space and let `G` be a quasi-coherent
`𝒪_F`-module on its small étale site.  For every `r`, the following are equivalent: `G` is
finite locally free of rank `r`; its `(r-1)`-st Fitting ideal sheaf vanishes and its `r`-th is
the unit ideal sheaf; its Fitting ideal sheaves vanish below `r` and are the unit ideal sheaf
from `r` onward.

The condition at index `r - 1` is read with truncated subtraction and is therefore guarded by the
disjunct `r = 0`, under which it is vacuous.  No finite type hypothesis is needed; see the
implementation notes. -/
@[stacks 0CZ8]
theorem isFiniteLocallyFreeOfRank_tfae_fittingIdeal
    (G : Modules.{u, u} B S hS F hF) (hG : G.IsQuasicoherentOnSite) (r : ℕ) :
    List.TFAE [
      RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) G r,
      (r = 0 ∨ fittingIdeal B S hS F hF G (r - 1) = ⊥) ∧
        fittingIdeal B S hS F hF G r = ⊤,
      (∀ k < r, fittingIdeal B S hS F hF G k = ⊥) ∧
        (∀ k, r ≤ k → fittingIdeal B S hS F hF G k = ⊤)] := by
  have hcart : IsCartesianOnAffineCharts G :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G hG
  have hrank := isFiniteLocallyFreeOfRank_iff_freeRankPresieve B S hS F hF G hcart r
  tfae_have 1 → 3 := by
    intro h1
    have h1' : ∀ U : SmallEtale B S hS F,
        Sieve.generate (freeRankPresieve B S hS F hF G r U) ∈
          SmallEtale.topology B S hS F U := hrank.mp h1
    exact ⟨fun k hk => fittingIdeal_eq_bot_of_freeRankPresieve B S hS F hF G hcart h1' hk,
      fun k hk => fittingIdeal_eq_top_of_freeRankPresieve B S hS F hF G h1' hk⟩
  tfae_have 3 → 2 := fun h3 =>
    ⟨(Nat.eq_zero_or_pos r).imp id fun _ => h3.1 (r - 1) (by omega), h3.2 r le_rfl⟩
  tfae_have 2 → 1 := fun h2 =>
    hrank.mpr (freeRankPresieve_mem_topology_of_fittingIdeal B S hS F hF G hcart r h2.1 h2.2)
  tfae_finish

end AlgebraicGeometry.Space

end
