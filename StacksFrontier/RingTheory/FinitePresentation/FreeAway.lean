module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# Model independence of the condition 051U

Let `R → S` be a ring map, let `M` be an `S`-module and let `f : R`. Writing down the condition
of Stacks 051U — that `S_f` is of finite presentation over `R_f`, that `M_f` is of finite
presentation over `S_f`, and that `S_f` and `M_f` are free over `R_f` — requires a choice of
models for the three localizations. This file proves that the condition does not depend on that
choice: it holds for the canonical models `R_f = Localization.Away f`,
`S_f = Localization (algebraMapSubmonoid S (powers f))` and `M_f = S_f ⊗[S] M` exactly when it
holds for arbitrary ones.

The mathematics is the uniqueness of a localization. Two models `R₁`, `R₂` of `R_f` are
identified by a unique `R`-algebra isomorphism `eR`, two models `S₁`, `S₂` of `S_f` by a unique
`S`-algebra isomorphism `eS`, and two models `M₁`, `M₂` of `M_f` by a unique `S`-linear
isomorphism `eM`; the pairs `(eR, eS)`, `(eS, eM)` and `(eR, eM)` are then semilinear
isomorphisms, along which finite presentation of an algebra, finite presentation of a module and
freeness of a module all transport.

## Main results

* `Stacks.FinitePresentation.FreeAwayModels.solution`: the statement of Stacks Tag `051U`.

## Implementation notes

The compatibility of `eR` with `eS` is the uniqueness of an `R`-algebra map out of a localization
of `R` (`IsLocalization.algHom_subsingleton`). The compatibility of `eS` with `eM` — that `eM` is
semilinear along `eS` and not merely `S`-linear — is obtained by transporting the `S₂`-action on
`M₂` back along `eS` to `M₁` and invoking `LinearMap.extendScalarsOfIsLocalization`: an `S`-linear
map between modules over a localization of `S` is automatically linear over that localization.

The three transport lemmas `Stacks.FinitePresentation.FreeAwayModels.free_of_ringEquiv`,
`Stacks.FinitePresentation.FreeAwayModels.finitePresentation_of_ringEquiv` and
`Stacks.FinitePresentation.FreeAwayModels.algebra_finitePresentation_of_ringEquiv` are stated for a
ring isomorphism `e : A ≃+* B` together with an additive isomorphism semilinear along it, which is
the data that localizations provide; they are general facts about semilinear isomorphisms, with no
localization in sight. Mathlib has the analogous statements for a fixed base ring only
(`LinearEquiv.finitePresentation_iff`, `Module.Free.of_basis`, `Algebra.FinitePresentation.equiv`).

## References

* [StacksProject 051U](https://stacks.math.columbia.edu/tag/051U)
-/

@[expose] public section

namespace Stacks.FinitePresentation.FreeAwayModels

open TensorProduct

section Transport

variable {A B N₁ N₂ : Type*} [CommRing A] [CommRing B] [AddCommGroup N₁] [AddCommGroup N₂]
  [Module A N₁] [Module B N₂]

/-- The image of the `A`-span of `s` under an additive isomorphism `φ` semilinear along
`e : A ≃+* B` lands in the `B`-span of the image of `s`. -/
private theorem mem_span_image {e : A ≃+* B} {φ : N₁ ≃+ N₂}
    (hφ : ∀ (a : A) (x : N₁), φ (a • x) = e a • φ x) (s : Set N₁) {x : N₁}
    (hx : x ∈ Submodule.span A s) : φ x ∈ Submodule.span B (φ '' s) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero => simp
  | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
  | smul a y _ hy =>
    rw [hφ]
    exact Submodule.smul_mem _ _ hy

/-- Freeness transports along a semilinear isomorphism: if `φ : N₁ ≃+ N₂` satisfies
`φ (a • x) = e a • φ x` for a ring isomorphism `e : A ≃+* B`, then `N₂` is free over `B` as soon
as `N₁` is free over `A`. -/
private theorem free_of_ringEquiv (e : A ≃+* B) (φ : N₁ ≃+ N₂)
    (hφ : ∀ (a : A) (x : N₁), φ (a • x) = e a • φ x) [Module.Free A N₁] : Module.Free B N₂ := by
  classical
  set b := Module.Free.chooseBasis A N₁
  refine Module.Free.of_basis (Module.Basis.mk (v := fun i => φ (b i)) ?_ ?_)
  · rw [linearIndependent_iff']
    intro t g hg i hi
    have h0 : ∑ j ∈ t, e.symm (g j) • b j = 0 := by
      apply φ.injective
      rw [map_sum, map_zero]
      simpa [hφ] using hg
    simpa using linearIndependent_iff'.mp b.linearIndependent t (fun j => e.symm (g j)) h0 i hi
  · intro x _
    have h := mem_span_image hφ (Set.range b) (b.mem_span (φ.symm x))
    rwa [← Set.range_comp, φ.apply_symm_apply] at h

/-- Finite presentation of a module transports along a semilinear isomorphism. -/
private theorem finitePresentation_of_ringEquiv (e : A ≃+* B) (φ : N₁ ≃+ N₂)
    (hφ : ∀ (a : A) (x : N₁), φ (a • x) = e a • φ x) [Module.FinitePresentation A N₁] :
    Module.FinitePresentation B N₂ := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := N₁)
  set p := Finsupp.linearCombination A s with hp
  have hpsurj : Function.Surjective p := by
    rw [← LinearMap.range_eq_top, hp, Finsupp.range_linearCombination, hs]
  set ψ : (Fin n →₀ A) ≃+ (Fin n →₀ B) := Finsupp.mapRange.addEquiv e.toAddEquiv with hψdef
  have hψ : ∀ (a : A) (x : Fin n →₀ A), ψ (a • x) = e a • ψ x := by
    intro a x
    ext i
    simp [hψdef, Finsupp.mapRange.addEquiv_apply]
  set q := Finsupp.linearCombination B (fun i => φ (s i)) with hq
  have hcomm : ∀ x : Fin n →₀ A, q (ψ x) = φ (p x) := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp [hq, hp]
    | add x y hx hy => simp [map_add, hx, hy]
    | single i a => simp [hq, hp, hψdef, Finsupp.mapRange.addEquiv_apply, hφ]
  have hqsurj : Function.Surjective q := fun y => by
    obtain ⟨x, rfl⟩ := (φ.surjective.comp hpsurj) y
    exact ⟨ψ x, hcomm x⟩
  refine Module.finitePresentation_of_surjective q hqsurj ?_
  obtain ⟨t, ht⟩ := Module.FinitePresentation.fg_ker p hpsurj
  refine ⟨t.image ψ, ?_⟩
  rw [Finset.coe_image]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨x, hx, rfl⟩
    have hxk : x ∈ LinearMap.ker p := ht ▸ Submodule.subset_span hx
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    rw [hcomm x, LinearMap.mem_ker.mp hxk, map_zero]
  · intro y hy
    have hx : ψ.symm y ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker]
      apply φ.injective
      rw [map_zero, ← hcomm, ψ.apply_symm_apply]
      exact LinearMap.mem_ker.mp hy
    have := mem_span_image (e := e) hψ (t : Set (Fin n →₀ A)) (ht ▸ hx)
    rwa [ψ.apply_symm_apply] at this

/-- Finite presentation of an algebra transports along a pair of ring isomorphisms commuting with
the structure maps. -/
private theorem algebra_finitePresentation_of_ringEquiv {C D : Type*} [CommRing C] [CommRing D]
    [Algebra A C] [Algebra B D] (e : A ≃+* B) (g : C ≃+* D)
    (hg : ∀ a : A, g (algebraMap A C a) = algebraMap B D (e a))
    (H : Algebra.FinitePresentation A C) : Algebra.FinitePresentation B D := by
  have key : (algebraMap B D) =
      (g : C →+* D).comp ((algebraMap A C).comp (e.symm : B →+* A)) := by
    ext b
    simp [hg]
  rw [← RingHom.finitePresentation_algebraMap, key]
  exact (RingHom.FinitePresentation.of_bijective g.bijective).comp
    ((RingHom.finitePresentation_algebraMap.mpr H).comp
      (RingHom.FinitePresentation.of_bijective e.symm.bijective))

end Transport

section Key

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module S M]

/-- The four conditions of 051U are independent of the models chosen for the three localizations:
if `(R₁, S₁, M₁)` and `(R₂, S₂, M₂)` both localize `R`, `R → S` and `M` at the powers of `f`,
the conditions for the first tuple imply those for the second. Applied twice, this is
`Stacks.FinitePresentation.FreeAwayModels.solution`. -/
private theorem keyMp (f : R)
    (R₁ : Type*) [CommRing R₁] [Algebra R R₁] [IsLocalization.Away f R₁]
    (S₁ : Type*) [CommRing S₁] [Algebra R S₁] [Algebra S S₁] [Algebra R₁ S₁]
      [IsScalarTower R S S₁] [IsScalarTower R R₁ S₁]
      [IsLocalization.Away (algebraMap R S f) S₁]
    (M₁ : Type*) [AddCommGroup M₁] [Module S M₁] [Module S₁ M₁] [Module R₁ M₁]
      [IsScalarTower S S₁ M₁] [IsScalarTower R₁ S₁ M₁]
    (l₁ : M →ₗ[S] M₁) [IsLocalizedModule (Submonoid.powers (algebraMap R S f)) l₁]
    (R₂ : Type*) [CommRing R₂] [Algebra R R₂] [IsLocalization.Away f R₂]
    (S₂ : Type*) [CommRing S₂] [Algebra R S₂] [Algebra S S₂] [Algebra R₂ S₂]
      [IsScalarTower R S S₂] [IsScalarTower R R₂ S₂]
      [IsLocalization.Away (algebraMap R S f) S₂]
    (M₂ : Type*) [AddCommGroup M₂] [Module S M₂] [Module S₂ M₂] [Module R₂ M₂]
      [IsScalarTower S S₂ M₂] [IsScalarTower R₂ S₂ M₂]
    (l₂ : M →ₗ[S] M₂) [IsLocalizedModule (Submonoid.powers (algebraMap R S f)) l₂]
    (h : Algebra.FinitePresentation R₁ S₁ ∧ Module.FinitePresentation S₁ M₁ ∧
      Module.Free R₁ S₁ ∧ Module.Free R₁ M₁) :
    Algebra.FinitePresentation R₂ S₂ ∧ Module.FinitePresentation S₂ M₂ ∧
      Module.Free R₂ S₂ ∧ Module.Free R₂ M₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  let eR : R₁ ≃ₐ[R] R₂ := IsLocalization.algEquiv (Submonoid.powers f) R₁ R₂
  let eS : S₁ ≃ₐ[S] S₂ := IsLocalization.algEquiv (Submonoid.powers (algebraMap R S f)) S₁ S₂
  let eM : M₁ ≃ₗ[S] M₂ :=
    IsLocalizedModule.linearEquiv (Submonoid.powers (algebraMap R S f)) l₁ l₂
  -- `eS` restricted to the image of `R₁` is `eR`, since an `R`-algebra map out of `R₁` is unique.
  have hcomp : ∀ x : R₁, eS (algebraMap R₁ S₁ x) = algebraMap R₂ S₂ (eR x) := by
    have := IsLocalization.algHom_subsingleton (S := R₁) (P := S₂) (Submonoid.powers f)
    intro x
    simpa using DFunLike.congr_fun (Subsingleton.elim
      ((eS.restrictScalars R).toAlgHom.comp (IsScalarTower.toAlgHom R R₁ S₁))
      ((IsScalarTower.toAlgHom R R₂ S₂).comp eR.toAlgHom)) x
  -- `eM` is semilinear along `eS`, not merely `S`-linear.
  have hM : ∀ (x : S₁) (m : M₁), eM (x • m) = eS x • eM m := by
    let : Module S₂ M₁ := Module.compHom M₁ (eS.symm : S₂ →+* S₁)
    have hsmul : ∀ (y : S₂) (m : M₁), y • m = eS.symm y • m := fun _ _ => rfl
    have : IsScalarTower S S₂ M₁ := ⟨fun s y m => by
      rw [hsmul, hsmul, Algebra.smul_def, map_mul, AlgEquiv.commutes, mul_smul, algebraMap_smul]⟩
    have key := (eM.toLinearMap.extendScalarsOfIsLocalization
      (Submonoid.powers (algebraMap R S f)) S₂).map_smul
    intro x m
    have h := key (eS x) m
    rwa [LinearMap.extendScalarsOfIsLocalization_apply',
      LinearMap.extendScalarsOfIsLocalization_apply', hsmul, AlgEquiv.symm_apply_apply] at h
  have hS' : ∀ (a : R₁) (x : S₁), eS (a • x) = eR a • eS x := by
    intro a x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcomp]
  have hM' : ∀ (a : R₁) (m : M₁), eM (a • m) = eR a • eM m := by
    intro a m
    rw [← algebraMap_smul S₁ a m, hM, hcomp, algebraMap_smul]
  exact ⟨algebra_finitePresentation_of_ringEquiv eR.toRingEquiv eS.toRingEquiv hcomp h1,
    finitePresentation_of_ringEquiv eS.toRingEquiv eM.toAddEquiv hM,
    free_of_ringEquiv eR.toRingEquiv eS.toRingEquiv.toAddEquiv hS',
    free_of_ringEquiv eR.toRingEquiv eM.toAddEquiv hM'⟩

end Key

public theorem solution {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module S M] (f : R)
    (Rf : Type*) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf]
    (Sf : Type*) [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [Algebra Rf Sf]
      [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
      [IsLocalization.Away (algebraMap R S f) Sf]
    (Mf : Type*) [AddCommGroup Mf] [Module S Mf] [Module Sf Mf] [Module Rf Mf]
      [IsScalarTower S Sf Mf] [IsScalarTower Rf Sf Mf]
    (l : M →ₗ[S] Mf) [IsLocalizedModule (Submonoid.powers (algebraMap R S f)) l] :
    (Algebra.FinitePresentation (Localization.Away f)
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))) ∧
      Module.FinitePresentation (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)))
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) ⊗[S] M) ∧
      Module.Free (Localization.Away f)
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))) ∧
      Module.Free (Localization.Away f)
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) ⊗[S] M)) ↔
      Algebra.FinitePresentation Rf Sf ∧ Module.FinitePresentation Sf Mf ∧
        Module.Free Rf Sf ∧ Module.Free Rf Mf := by
  have hTS : IsLocalization (Submonoid.powers (algebraMap R S f))
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))) := by
    rw [← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  have hLM : IsLocalizedModule (Submonoid.powers (algebraMap R S f))
      (TensorProduct.mk S
        (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f))) M 1) := by
    rw [isLocalizedModule_iff_isBaseChange (Submonoid.powers (algebraMap R S f))
      (Localization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)))]
    exact TensorProduct.isBaseChange S M _
  exact ⟨keyMp f _ _ _ (TensorProduct.mk S _ M 1) Rf Sf Mf l,
    keyMp f Rf Sf Mf l _ _ _ (TensorProduct.mk S _ M 1)⟩

end Stacks.FinitePresentation.FreeAwayModels

end

/-!
# Finite presentation and freeness after inverting an element

Let `R → S` be a ring map and let `M` be an `S`-module. The Stacks project singles out, for an
element `f ∈ R`, the condition
```
S_f       is of finite presentation over R_f
M_f       is of finite presentation as an S_f-module
S_f, M_f  are free as R_f-modules
```
(Stacks 051U). It is the condition whose standard opens `D(f)` sweep out the generic freeness
locus `U(R → S, M) ⊆ Spec R` of Equation 051V, it is what Lemma 051T produces for some nonzero
`f` when `R` is a domain, `R → S` is of finite type and `M` is a finite `S`-module, and it is the
condition manipulated in Lemmas 051W and 051X.

Writing the condition down requires a choice of models for the three localizations `R_f`, `S_f`
and `M_f`, which the source's notation leaves implicit. The condition does not depend on that
choice, and both halves of this file say so: the definition fixes the canonical models, and the
characterization says that the four properties may equally be tested on any other models.

## Main definitions

* `Algebra.IsFinitePresentationFreeAway R S M f`: the condition displayed above.

## Main results

* `Algebra.isFinitePresentationFreeAway_iff`: the condition may be tested on arbitrary models
  `R_f = Rf`, `S_f = Sf`, `M_f = Mf` of the three localizations.

## Implementation notes

The source displays the condition as an unnamed equation, referred to in the surrounding
lemmas by the phrase "`f` satisfies (051U)"; here it becomes a named `Prop`-valued predicate of
`f`, which is the form its dependents 051V, 051W and 051X quantify over.

The models fixed by the definition are Mathlib's canonical ones, as in `Module.freeLocus`:
`R_f` is `Localization.Away f`; `S_f` is
`Localization (Algebra.algebraMapSubmonoid S (.powers f))`,
the localization of `S` at the image of the powers of `f`, which is the spelling carrying
Mathlib's canonical `R_f`-algebra structure, the localization of `R → S` itself; and `M_f` is the
base change `S_f ⊗[S] M`, which carries both the `S_f`-module structure and, through that algebra
structure, the `R_f`-module structure. The `LocalizedModule` spelling of `M_f` carries only the
first of those two, so a formulation using it would have to name two different models of `M_f`,
one for the freeness over `R_f` and one for the finite presentation over `S_f`; the base change
avoids that, and it is the localization of `M` at the image of the powers of `f`
(`isLocalizedModule_iff_isBaseChange`), so nothing is lost. Mathlib states generic freeness in the
same tensor form (`Module.mem_freeLocus_iff_tensor`).

`M` carries only `[Module S M]`: no `R`-module structure on `M` is assumed and none is needed, the
`R_f`-module structure on `M_f` being the restriction of scalars along `R_f → S_f`. In
`Algebra.isFinitePresentationFreeAway_iff` that restriction is what the hypothesis
`IsScalarTower Rf Sf Mf` pins.

Nothing is assumed about `R → S` or `M` beyond the ambient data — no domain, Noetherian or
finiteness hypothesis — since 051U is a condition asked of `f`, not a property proved of it.
Those hypotheses belong to 051T, which asserts that some nonzero `f` satisfies it.

Faithfulness. (1) No hypothesis is idle: the ambient data of the definition is exactly the
source's, a ring map `R → S` and an `S`-module `M`, and `f` occurs in all four conjuncts; in the
characterization every instance argument either pins one of `Rf`, `Sf`, `Mf` as a model of the
corresponding localization or supplies a scalar action named on the right-hand side. (2) The
scalars and the base are the source's, line by line: `S_f` is of finite presentation as an algebra
over `R_f` and not over `R`, `M_f` is of finite presentation as a module over `S_f` and not over
`R_f`, and the two freeness assertions are over `R_f`. (3) The canonical maps are pinned rather
than assumed to exist: the definition uses the canonical localizations of `R`, of the algebra
`R → S` and of `M` at the powers of `f`, and in the characterization `IsLocalization.Away f Rf`,
`IsLocalization.Away (algebraMap R S f) Sf` and
`IsLocalizedModule (Submonoid.powers (algebraMap R S f)) l` pin `R → Rf`, `S → Sf` and `l`,
while `IsScalarTower R Rf Sf` together with `IsScalarTower R S Sf` pins the `R_f`-algebra
structure on `Sf` as the localization of `R → S`. (4) The instantiation is not degenerate: for
`R = S = ℤ` and
`M = ℤ/2ℤ` the condition holds for `f = 2`, where `M_f = 0` is free of rank `0` and
`S_f = ℤ[1/2] = R_f` is free and of finite presentation over `R_f`, and fails for `f = 1`, where
`ℤ/2ℤ` is a nonzero torsion module over the domain `ℤ` and hence not free; so the predicate is
neither empty nor everything. It also holds vacuously for `f = 0`, all three localizations being
zero, which is why 051T asks for a nonzero `f` and is harmless in 051V because `D(0) = ∅`.

## References

* [StacksProject 051U](https://stacks.math.columbia.edu/tag/051U)

## Tags

generic freeness, generic flatness, finite presentation, free module, localization
-/

@[expose] public section

open TensorProduct

namespace Algebra

/-- **Stacks 051U**. Let `R → S` be a ring map, let `M` be an `S`-module and let `f : R`. The
condition `Algebra.IsFinitePresentationFreeAway R S M f` says that, after inverting `f`, the ring
`S_f` is of finite presentation as an `R_f`-algebra, the module `M_f` is of finite presentation as
an `S_f`-module, and `S_f` and `M_f` are free as `R_f`-modules. The localizations are the
canonical ones: `R_f = Localization.Away f`, `S_f` is the localization of `S` at the image of the
powers of `f`, and `M_f = S_f ⊗[S] M`; by `Algebra.isFinitePresentationFreeAway_iff` the four
properties may be tested on any other models. -/
@[stacks 051U "The condition of the source's display, as a predicate on `f`, with the canonical
models of the localizations; `M_f` is the base change `S_f ⊗[S] M`. See the module docstring."]
public def IsFinitePresentationFreeAway (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] (f : R) : Prop :=
  Algebra.FinitePresentation (Localization.Away f)
      (Localization (algebraMapSubmonoid S (Submonoid.powers f))) ∧
    Module.FinitePresentation (Localization (algebraMapSubmonoid S (Submonoid.powers f)))
      (Localization (algebraMapSubmonoid S (Submonoid.powers f)) ⊗[S] M) ∧
    Module.Free (Localization.Away f)
      (Localization (algebraMapSubmonoid S (Submonoid.powers f))) ∧
    Module.Free (Localization.Away f)
      (Localization (algebraMapSubmonoid S (Submonoid.powers f)) ⊗[S] M)

/-- The condition 051U may be tested on arbitrary models of the three localizations: if `Rf` is a
localization of `R` at the powers of `f`, `Sf` a localization of `S` at the powers of the image of
`f` whose `Rf`-algebra structure is the localization of `R → S`, and `l : M →ₗ[S] Mf` a
localization of `M` at the powers of the image of `f`, whose `Rf`-action is the restriction of its
`Sf`-action, then `Algebra.IsFinitePresentationFreeAway R S M f` holds exactly when `Sf` is of
finite presentation over `Rf`, `Mf` is of finite presentation over `Sf`, and `Sf` and `Mf` are
free over `Rf`. -/
public theorem isFinitePresentationFreeAway_iff {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module S M] (f : R)
    (Rf : Type*) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf]
    (Sf : Type*) [CommRing Sf] [Algebra R Sf] [Algebra S Sf] [Algebra Rf Sf]
      [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
      [IsLocalization.Away (algebraMap R S f) Sf]
    (Mf : Type*) [AddCommGroup Mf] [Module S Mf] [Module Sf Mf] [Module Rf Mf]
      [IsScalarTower S Sf Mf] [IsScalarTower Rf Sf Mf]
    (l : M →ₗ[S] Mf) [IsLocalizedModule (Submonoid.powers (algebraMap R S f)) l] :
    IsFinitePresentationFreeAway R S M f ↔
      Algebra.FinitePresentation Rf Sf ∧ Module.FinitePresentation Sf Mf ∧
        Module.Free Rf Sf ∧ Module.Free Rf Mf :=
  Stacks.FinitePresentation.FreeAwayModels.solution f Rf Sf Mf l

end Algebra

end
