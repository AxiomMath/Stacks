module

import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimension.Resolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The right derived functor on the unbounded derived category, in bounded cohomological dimension

Let `F : 𝒜 ⥤ ℬ` be a left exact functor of abelian categories. An object `X` of `𝒜` is
*right acyclic for `F`* if the complex `X[0]` computes `RF` (Stacks 0157(3)), i.e. if `RF` is
defined at `X[0]` and the canonical map `F(X) ⟶ RF(X[0])` is an isomorphism (Stacks 05SX), and
`R ^ n F` denotes the functor `X ↦ H ^ n (RF (X[0]))`. Assume that every object of `𝒜` is a
subobject of an object which is right acyclic for `F`, and that `R ^ n F = 0` for some integer
`n ≥ 0`. Then

1. the right derived functor `RF : D(𝒜) ⥤ D(ℬ)` exists on the *whole* derived category,
2. every complex all of whose terms are right acyclic for `F` computes `RF`,
3. every complex is the source of a quasi-isomorphism into a complex all of whose terms are
   right acyclic for `F`,
4. for `E` in `D(𝒜)`: the map `H ^ i (RF (τ_{≤ a} E)) ⟶ H ^ i (RF E)` is an isomorphism for
   `i ≤ a`, the map `H ^ i (RF E) ⟶ H ^ i (RF (τ_{≥ b - n + 1} E))` is an isomorphism for
   `i ≥ b`, and if `E` lives in degrees `[a, b]` then `RF E` lives in degrees `[a, b + n - 1]`.

## Main results

* `CategoryTheory.Functor.hasRightDerivedFunctor_of_isZero_rightDerived`: parts (1), (3), (2)
  and (4) of Stacks 07K7, in that order.

## Implementation notes

The derived functor is the one of Mathlib's localization theory: `RF : D(𝒜) ⥤ D(ℬ)` is a right
derived functor of `K(𝒜) ⥤ D(ℬ)`, `K ↦ F(K)`, along the localization functor
`Qh : K(𝒜) ⥤ D(𝒜)` at quasi-isomorphisms, so that part (1) is
`Functor.HasRightDerivedFunctor` for that functor and that class of morphisms, and the
assertion that a complex `K` *computes* `RF` is that the unit `α : F(-) ⟶ Qh(-) ⋙ RF` of the
derived functor is invertible at `K`; this is the form Mathlib uses for the derived functor on
`D⁺` (`CategoryTheory.Functor.rightDerivedFunctorPlusUnit`). Parts (2) and (4) are stated for
an *arbitrary* right derived functor `(RF, α)` on `D(𝒜)`, not for a chosen one; any two are
uniquely isomorphic compatibly with their units (`Functor.rightDerivedUnique`), so this is the
strongest reading and it does not depend on a construction.

Right acyclicity (Stacks 0157(3)) refers to the partial right derived functor of `K⁺(𝒜) ⥤ D⁺(ℬ)`
along the quasi-isomorphisms (case (1) of Stacks 05T4), and it is stated in the source's own terms:
`X[0]` computes `RF` in the sense of Stacks 05SX, `CategoryTheory.Functor.ComputesRightDerived`,
which asks that the ind-object `(s : X[0] ⟶ K) ↦ F(K)`, indexed by the quasi-isomorphisms out of
`X[0]`, be essentially constant, and that its coprojection at `𝟙` — the canonical map `F(X[0]) ⟶
RF(X[0])` — be an isomorphism. This is the
hypothesis of Stacks 05TA as formalized in this project
(`CategoryTheory.Functor.hasDerivedFunctors_of_enough_acyclic_objects`), which then provides the
everywhere defined `RF⁺ : D⁺(𝒜) ⥤ D⁺(ℬ)`. The functor `R ^ n F` of hypothesis (2) is stated
through a right derived functor `(RF⁺, α⁺)` of `F` along `Qh : K⁺(𝒜) ⥤ D⁺(𝒜)` taken as data,
`R ^ n F (X) = H ^ n (RF⁺ (X[0]))` as in Stacks 015A; since any two are uniquely isomorphic, the
condition does not depend on that choice, and since the existence of `RF` on the unbounded
`D(𝒜)` is part of the *conclusion*, nothing is available to construct it from here. Under the
hypothesis that every object embeds into a right acyclic one, `X[0]` computes `RF` exactly when
`α⁺` is invertible at `X[0]`
(`Functor.computesRightDerived_iff_isIso_unit_of_enough_source_acyclic_objects`), which is how
the proof uses right acyclicity. The class of right acyclic objects is carried by the
`ObjectProperty` `P`, whose only role is to abbreviate that condition in the hypothesis and in
parts (2) and (3).

*Faithfulness.* Right acyclicity of `X` is not taken to mean that the unit `α⁺` of the chosen
`RF⁺` is invertible at `X[0]`. For a right derived
functor in Mathlib's sense — a left Kan extension, not necessarily pointwise — this is not the
source's notion: it does not say that `RF` is defined at `X[0]` in the sense of Stacks 05S9, and
with it the first hypothesis would not imply the conclusion of Stacks 05TA on which the source
proof rests (that `RF⁺` is computed by complexes of right acyclic objects and is triangulated).
The statement uses the source's definition, via the 05SX predicate already used for
Stacks 05TA.

`F.Additive` is a consequence of left exactness
(`CategoryTheory.Functor.additive_of_preserves_binary_products`) and is assumed only because
`Functor.mapHomotopyCategory` and `Functor.mapHomotopyCategoryPlus` are stated for additive
functors, so instance search needs it; it is not an extra hypothesis on `F`.

Part (4)(c) is split into its two one-sided implications, `H ^ i (E) = 0` for `i < a` implies
`H ^ i (RF E) = 0` for `i < a`, and `H ^ i (E) = 0` for `i > b` implies `H ^ i (RF E) = 0` for
`i > b + n - 1`. This is what the source's `-∞ ≤ a ≤ b ≤ ∞` means: for `a = -∞` only the upper
bound is asserted and for `b = ∞` only the lower one, and the two implications together are
strictly stronger than the conjunction of the two hypotheses implying the conjunction of the
two conclusions. Boundedness of an object of `D(ℬ)` is Mathlib's `DerivedCategory.IsGE` /
`IsLE` for the canonical t-structure, which is exactly the vanishing of homology outside the
range (`DerivedCategory.isGE_iff`, `DerivedCategory.isLE_iff`), and the truncations `τ_{≤ a}`,
`τ_{≥ b}` of parts (4)(a) and (4)(b) are that t-structure's `truncLE`, `truncGE` together with
its canonical maps `truncLEι`, `truncGEπ`.

Faithfulness. (1) No hypothesis is dead: left exactness is what makes right acyclicity of `X`
equivalent to `R ^ i F (X) = 0` for `i > 0` (Stacks 015C), hence what ties the two hypotheses
together; `hP` names the class used by hypothesis (1) and by conclusions (2) and (3); `hmono`
is what produces the resolutions of (3), hence (1) and (2); `n` and `hn` are used in (4)(b)
and (4)(c), where the shift by `n - 1` is precisely the assumed bound on the cohomological
dimension, and for `n = 0` (then `F = 0`) the conclusions degenerate accordingly. (2) The base
is the source's: one left exact `F : 𝒜 ⥤ ℬ` between abelian categories, cochain complexes
graded by `ℤ`, homology taken in `ℬ`, and the derived functors are those of the localizations
`K(𝒜) → D(𝒜)` and `K⁺(𝒜) → D⁺(𝒜)` at quasi-isomorphisms; there is no change of category.
(3) Canonical maps are pinned, not merely asserted to exist: "computes `RF`" on `D(𝒜)` is
invertibility of the unit `α`, right acyclicity is the 05SX condition on the canonical
coprojection, the maps of (4)(a) and (4)(b) are `RF` applied to the canonical truncation
maps and then `H ^ i`, and `R ^ n F` is `H ^ n` of `RF⁺` at `X[0]`. (4) The instantiation is
not degenerate: for `𝒜 = ℬ = ModuleCat R`, `F = 𝟭`, one may take `RF⁺` to be Mathlib's
`Functor.rightDerivedFunctorPlus` (`ModuleCat R` has enough injectives), `P = ⊤` (every object
is right acyclic for an exact functor: the resolution ind-object is essentially constant, since
`𝟭` inverts quasi-isomorphisms) and `n = 1`; the intended instances are
functors of finite cohomological dimension such as `f_*` for a morphism with fibres of bounded
dimension, where `n` is genuinely `> 1` and part (4) has content.

## Proof

This follows the source. By Stacks 05TA the right derived functor `R₀` on `D⁺` exists, is
triangulated, and is computed by bounded below complexes of right acyclic objects. Dimension
shifting along embeddings into right acyclic objects gives `R ^ m F = 0` for `m ≥ n`, so the
function `d (X) = max ({0} ∪ {i | R ^ i F (X) ≠ 0})` is bounded by `n - 1`; it is additive on
biproducts, drops by at most one along cokernels of embeddings, and vanishes exactly on the right
acyclic objects (left exactness), so Stacks 07K6 yields part (3). Along an exact complex of right
acyclic objects `d` drops at each cycle, so its cycles are right acyclic after `n - 1` steps;
hence `F` preserves the exactness of the mapping cone of a quasi-isomorphism between complexes
of right acyclic objects, and the resulting right derivability structure (Stacks 06XN) gives
parts (1) and (2). Part (4) follows from the canonical truncation triangles once `RF` preserves
lower bounds and shifts upper bounds by at most `n - 1`, which is read off on right acyclic
replacements and their good truncations. When `n = 0`, `F = 0` and everything degenerates.

## References

* [StacksProject 07K7](https://stacks.math.columbia.edu/tag/07K7)
* [StacksProject 0157](https://stacks.math.columbia.edu/tag/0157), definition of right acyclic
* [StacksProject 05SX](https://stacks.math.columbia.edu/tag/05SX), objects computing `RF`
* [StacksProject 05TA](https://stacks.math.columbia.edu/tag/05TA), existence of `RF` on `D⁺`
* [StacksProject 07K6](https://stacks.math.columbia.edu/tag/07K6), acyclic replacements
-/

@[expose] public section

open CategoryTheory Limits ZeroObject DerivedCategory Pretriangulated

namespace StacksDraft.RightDerivedBoundedDimension

universe v₁ v₂ u₁ u₂

section Plus

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive]
  (RF : Plus A ⥤ Plus B) (α : F.mapHomotopyCategoryPlus ⋙ Plus.Qh ⟶ Plus.Qh ⋙ RF)
  [RF.CommShift ℤ] [RF.IsTriangulated]
  (hGE : ∀ X : A, (RF.obj ((Plus.singleFunctor A 0).obj X)).IsGE 0)
  (hres : ∀ X : A, ∃ (Y : A) (i : X ⟶ Y), Mono i ∧
    IsIso (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj Y)))

/-! ### The functors `Rⁱ F` of a triangulated `RF` with enough objects computing it -/

/-- `RF` sends the triangle of a short exact sequence, seen through `X ↦ X[0]`, to a
distinguished triangle. -/
private lemma exists_distTriang_map_single (S : ShortComplex A) (hS : S.ShortExact) :
    ∃ δ, RF.mapTriangle.obj (Triangle.mk ((Plus.singleFunctor A 0).map S.f)
      ((Plus.singleFunctor A 0).map S.g) δ) ∈ distTriang (Plus B) := by
  obtain ⟨δ, hT⟩ := Functor.exists_distTriang_singleFunctor (A := A) hS
  exact ⟨δ, RF.map_distinguished _ hT⟩

include hGE in
/-- If `RF(X[0])` lives in degrees `≥ 0` for every `X`, then `R⁰ F` is left exact: the long exact
homology sequence of the image of the triangle of a short exact sequence starts in degree `0`. -/
private lemma preservesFiniteLimits_singleFunctor_comp_homologyFunctor :
    PreservesFiniteLimits (Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B 0) := by
  have : (Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B 0).Additive := inferInstance
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  obtain ⟨δ, hT'⟩ := exists_distTriang_map_single RF S hS
  have hz : IsZero (((Plus.homologyFunctor B 0).shift (-1 : ℤ)).obj
      (RF.obj ((Plus.singleFunctor A 0).obj S.X₃))) := by
    have := hGE S.X₃
    exact Plus.isZero_homology_of_isGE _ 0 (-1) (by norm_num)
  refine ⟨(Plus.homologyFunctor B 0).homologySequence_exact₂ _ hT' 0, ?_⟩
  exact ((Plus.homologyFunctor B 0).homologySequence_mono_shift_map_mor₁_iff
    _ hT' (-1) 0 (by ring)).2 (hz.eq_of_src _ _)

include hGE hres in
/-- For left exact `F`, the map `F(X) ⟶ R⁰ F(X)` is invertible: both functors are left exact,
it is invertible at the objects computing `RF`, and every object is the kernel of a map between
two such objects. -/
private lemma isIso_homology_zero_unit [PreservesFiniteLimits F] (X : A) :
    IsIso ((Plus.homologyFunctor B 0).map
      (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X))) := by
  have h₂ := preservesFiniteLimits_singleFunctor_comp_homologyFunctor RF hGE
  let β := Functor.whiskerRight (Functor.whiskerLeft
    (HomotopyCategory.Plus.singleFunctor A 0) α) (Plus.homologyFunctor B 0)
  have i₁ : PreservesFiniteLimits ((HomotopyCategory.Plus.singleFunctor A 0 ⋙
      F.mapHomotopyCategoryPlus ⋙ Plus.Qh) ⋙ Plus.homologyFunctor B 0) :=
    preservesFiniteLimits_of_natIso (Functor.rightDerivedZeroSourceIso F).symm
  have i₂ : PreservesFiniteLimits ((HomotopyCategory.Plus.singleFunctor A 0 ⋙
      Plus.Qh ⋙ RF) ⋙ Plus.homologyFunctor B 0) :=
    preservesFiniteLimits_of_natIso (Functor.rightDerivedZeroTargetIso RF).symm
  obtain ⟨Y, i, hi, hY⟩ := hres X
  obtain ⟨Z, j, hj, hZ⟩ := hres (cokernel i)
  let g := cokernel.π i ≫ j
  have w : i ≫ g = 0 := by simp [g]
  have hlim : IsLimit (KernelFork.ofι i w) := by
    let k := Abelian.monoIsKernelOfCokernel _ (cokernelIsCokernel i)
    exact isKernelCompMono k j rfl
  have : IsIso (β.app Y) := inferInstanceAs (IsIso ((Plus.homologyFunctor B 0).map
    (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj Y))))
  have : IsIso (β.app Z) := inferInstanceAs (IsIso ((Plus.homologyFunctor B 0).map
    (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj Z))))
  exact Functor.isIso_app_of_isLimit_kernelFork w β hlim

/-- `Hⁱ(RF(X[0]))`, read through the two presentations of the complex `X[0]`. -/
public noncomputable def homologyTargetIso (X : A) (i : ℤ) :
    (Plus.homologyFunctor B i).obj (RF.obj ((Plus.singleFunctor A 0).obj X)) ≅
      (Plus.homologyFunctor B i).obj ((Plus.Qh ⋙ RF).obj
        ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) :=
  (Plus.homologyFunctor B i).mapIso (RF.mapIso ((Functor.singleFunctorPlusIsoCompQh 0).app X))

omit [HasDerivedCategory A] in
/-- The complex `F(X[0]) = F(X)[0]` has no homology outside degree `0`. -/
public lemma isZero_homology_source_single (X : A) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((Plus.homologyFunctor B i).obj ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).obj
      ((HomotopyCategory.Plus.singleFunctor A 0).obj X))) := by
  apply IsZero.of_iso (Y := (Plus.homologyFunctor B i).obj
    ((Plus.singleFunctor B 0).obj (F.obj X)))
  · rcases hi.lt_or_gt with hi | hi
    · exact Plus.isZero_homology_of_isGE _ 0 i hi
    · exact Plus.isZero_homology_of_isLE _ 0 i hi
  · exact (Plus.homologyFunctor B i).mapIso ((Functor.mapSingleFunctorCompQhIso F).app X)

omit [RF.CommShift ℤ] [RF.IsTriangulated] in
/-- If `X[0]` computes `RF`, then `Rⁱ F(X) = 0` for `i ≠ 0`. -/
public lemma isZero_homology_of_isIso_unit (X : A)
    (hX : IsIso (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((Plus.homologyFunctor B i).obj (RF.obj ((Plus.singleFunctor A 0).obj X))) :=
  (isZero_homology_source_single F X i hi).of_iso
    (homologyTargetIso RF X i ≪≫
      ((Plus.homologyFunctor B i).mapIso (asIso (α.app _))).symm)

include hGE hres in
/-- For left exact `F`, if `Rⁱ F(X) = 0` for all `i > 0` then `X[0]` computes `RF`. -/
private lemma isIso_unit_of_isZero_homology_pos [PreservesFiniteLimits F] (X : A)
    (hX : ∀ i : ℤ, 0 < i →
      IsZero ((Plus.homologyFunctor B i).obj (RF.obj ((Plus.singleFunctor A 0).obj X)))) :
    IsIso (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := by
  apply (Plus.isIso_iff _).2
  intro i
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · have := hGE X
    exact (isZero_homology_source_single F X i hi.ne).isIso
      ((Plus.isZero_homology_of_isGE _ 0 i hi).of_iso (homologyTargetIso RF X i).symm) _
  · exact isIso_homology_zero_unit F RF α hGE hres X
  · exact (isZero_homology_source_single F X i hi.ne').isIso
      ((hX i hi).of_iso (homologyTargetIso RF X i).symm) _

/-- The long exact sequence of `Rⁱ F` attached to a short exact sequence `0 → X₁ → X₂ → X₃ → 0`:
`Rⁱ⁺¹ F(X₁) = 0` and `Rⁱ F(X₂) = 0` give `Rⁱ F(X₃) = 0`. -/
private lemma isZero_homology_right_of_shortExact (S : ShortComplex A) (hS : S.ShortExact)
    (i : ℤ)
    (h₁ : IsZero ((Plus.homologyFunctor B (i + 1)).obj
      (RF.obj ((Plus.singleFunctor A 0).obj S.X₁))))
    (h₂ : IsZero ((Plus.homologyFunctor B i).obj
      (RF.obj ((Plus.singleFunctor A 0).obj S.X₂)))) :
    IsZero ((Plus.homologyFunctor B i).obj (RF.obj ((Plus.singleFunctor A 0).obj S.X₃))) := by
  obtain ⟨δ, hT'⟩ := exists_distTriang_map_single RF S hS
  exact ((Plus.homologyFunctor B 0).homologySequence_exact₃ _ hT' i (i + 1) rfl).isZero_X₂
    (h₂.eq_of_src _ _) (h₁.eq_of_tgt _ _)

/-- The long exact sequence of `Rⁱ F` attached to a short exact sequence `0 → X₁ → X₂ → X₃ → 0`:
`Rⁱ⁺¹ F(X₂) = 0` and `Rⁱ F(X₃) = 0` give `Rⁱ⁺¹ F(X₁) = 0`. -/
public lemma isZero_homology_left_of_shortExact (S : ShortComplex A) (hS : S.ShortExact)
    (i : ℤ)
    (h₂ : IsZero ((Plus.homologyFunctor B (i + 1)).obj
      (RF.obj ((Plus.singleFunctor A 0).obj S.X₂))))
    (h₃ : IsZero ((Plus.homologyFunctor B i).obj
      (RF.obj ((Plus.singleFunctor A 0).obj S.X₃)))) :
    IsZero ((Plus.homologyFunctor B (i + 1)).obj
      (RF.obj ((Plus.singleFunctor A 0).obj S.X₁))) := by
  obtain ⟨δ, hT'⟩ := exists_distTriang_map_single RF S hS
  exact ((Plus.homologyFunctor B 0).homologySequence_exact₁ _ hT' i (i + 1) rfl).isZero_X₂
    (h₃.eq_of_src _ _) (h₂.eq_of_tgt _ _)

include hres in
/-- If every object embeds into one computing `RF` and `Rⁿ F = 0` with `n > 0`, then
`Rᵐ F = 0` for all `m ≥ n`, by dimension shifting. -/
private lemma isZero_homology_ge (n : ℕ)
    (hzero : ∀ X : A, IsZero ((Plus.homologyFunctor B n).obj
      (RF.obj ((Plus.singleFunctor A 0).obj X)))) :
    ∀ (m : ℕ), n ≤ m → ∀ X : A, IsZero ((Plus.homologyFunctor B m).obj
      (RF.obj ((Plus.singleFunctor A 0).obj X))) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hzero
  | succ m hm ih =>
    intro X
    obtain ⟨Y, f, hf, hY⟩ := hres X
    have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
      { exact := ShortComplex.exact_cokernel f }
    simpa only [Nat.cast_add, Nat.cast_one] using isZero_homology_left_of_shortExact RF
      (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)) hS m
      (isZero_homology_of_isIso_unit F RF α Y hY (m + 1) (by omega)) (ih (cokernel f))

section Dimension

variable (N : ℕ)
  (hv : ∀ (m : ℕ), N ≤ m → ∀ X : A, IsZero ((Plus.homologyFunctor B m).obj
    (RF.obj ((Plus.singleFunctor A 0).obj X))))

/-- The function `d(X) = max ({0} ∪ {i | Rⁱ F(X) ≠ 0})` of Stacks 07K7, defined using the bound
`N` beyond which all `Rⁱ F` vanish. -/
private noncomputable def dimension (X : A) : ℕ := by
  classical
  exact Nat.find (show ∃ d : ℕ, ∀ i : ℕ, d < i →
    IsZero ((Plus.homologyFunctor B i).obj (RF.obj ((Plus.singleFunctor A 0).obj X))) from
    ⟨N, fun i hi => hv i hi.le X⟩)

omit [RF.CommShift ℤ] [RF.IsTriangulated] in
/-- `d(X) ≤ r` if and only if `Rⁱ F(X) = 0` for all `i > r`. -/
private lemma dimension_le_iff (X : A) (r : ℕ) :
    dimension RF N hv X ≤ r ↔ ∀ i : ℕ, r < i →
      IsZero ((Plus.homologyFunctor B i).obj (RF.obj ((Plus.singleFunctor A 0).obj X))) := by
  classical
  unfold dimension
  exact ⟨fun h i hi => Nat.find_spec (p := fun d => ∀ i : ℕ, d < i →
    IsZero ((Plus.homologyFunctor B i).obj (RF.obj ((Plus.singleFunctor A 0).obj X)))) _
    i (h.trans_lt hi), fun h => Nat.find_min' _ h⟩

omit [RF.CommShift ℤ] [RF.IsTriangulated] in
/-- The function `d` is bounded by `N`. -/
private lemma dimension_le (X : A) : dimension RF N hv X ≤ N :=
  (dimension_le_iff RF N hv X N).2 (fun i hi => hv i hi.le X)

/-- `d(X ⊞ Y) ≤ max (d(X), d(Y))`, since `Rⁱ F` is additive. -/
private lemma dimension_biprod_le (X Y : A) :
    dimension RF N hv (X ⊞ Y) ≤ max (dimension RF N hv X) (dimension RF N hv Y) := by
  apply (dimension_le_iff RF N hv _ _).2
  intro i hi
  let H := Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B i
  have hx : IsZero (H.obj X) := (dimension_le_iff RF N hv X _).1 le_rfl i
    (lt_of_le_of_lt (le_max_left _ _) hi)
  have hy : IsZero (H.obj Y) := (dimension_le_iff RF N hv Y _).1 le_rfl i
    (lt_of_le_of_lt (le_max_right _ _) hi)
  rw [IsZero.iff_id_eq_zero]
  have ht := congrArg H.map (biprod.total (X := X) (Y := Y))
  rw [H.map_add, H.map_comp, H.map_comp, H.map_id,
    hx.eq_of_tgt (H.map biprod.fst) 0, hy.eq_of_tgt (H.map biprod.snd) 0,
    zero_comp, zero_comp, zero_add] at ht
  exact ht.symm

/-- `d(X₃) ≤ max (d(X₁) - 1, d(X₂))` for a short exact sequence `0 → X₁ → X₂ → X₃ → 0`. -/
private lemma dimension_shortExact_le (S : ShortComplex A) (hS : S.ShortExact) :
    dimension RF N hv S.X₃ ≤ max (dimension RF N hv S.X₁ - 1) (dimension RF N hv S.X₂) := by
  apply (dimension_le_iff RF N hv _ _).2
  intro i hi
  apply isZero_homology_right_of_shortExact RF S hS i
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (dimension_le_iff RF N hv S.X₁ _).1 le_rfl (i + 1) (by omega)
  · exact (dimension_le_iff RF N hv S.X₂ _).1 le_rfl i (by omega)

variable (P : ObjectProperty A)
  (hP : ∀ X : A, P X ↔ IsIso (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)))
  (hmono : ∀ X : A, ∃ (Y : A) (i : X ⟶ Y) (_ : Mono i), P Y)

include hGE hres hP in
private lemma dimension_eq_zero_iff [PreservesFiniteLimits F] (X : A) :
    dimension RF N hv X = 0 ↔ P X := by
  rw [← Nat.le_zero, dimension_le_iff]
  constructor
  · intro h
    apply (hP X).2
    apply isIso_unit_of_isZero_homology_pos F RF α hGE hres X
    intro i hi
    simpa only [Int.toNat_of_nonneg hi.le] using h i.toNat (by omega)
  · intro h i hi
    exact isZero_homology_of_isIso_unit F RF α X ((hP X).1 h) i (by omega)

/-- The cast `ℕ → ℕ∞` commutes with `max`. -/
private lemma natCast_max_enat (a b : ℕ) : ((max a b : ℕ) : ℕ∞) = max (a : ℕ∞) b :=
  Nat.mono_cast.map_max

include hGE hres hP hmono in
private lemma boundedCohomologicalDimension [PreservesFiniteLimits F] :
    Stacks.BoundedCohomologicalDimension.BoundedCohomologicalDimension (fun X => (dimension RF N hv
      X : ℕ∞)) := by
  constructor
  · intro X
    obtain ⟨Y, i, hi, hY⟩ := hmono X
    refine ⟨Y, i, hi, ?_⟩
    simp [(dimension_eq_zero_iff F RF α hGE hres N hv P hP Y).2 hY]
  · intro X Y
    simpa only [natCast_max_enat] using
      (ENat.natCast_le_natCast.2 (dimension_biprod_le RF N hv X Y))
  · intro S hS
    simpa only [natCast_max_enat, ENat.natCast_sub, Nat.cast_one] using
      (ENat.natCast_le_natCast.2 (dimension_shortExact_le RF N hv S hS))

end Dimension

section Cycles

omit [HasDerivedCategory A]

/-- At a degree where `K` is exact, the map from the previous term to the cycles is an
epimorphism. -/
private lemma epi_toCycles_of_exactAt (K : CochainComplex A ℤ) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).prev j = i) (h : K.ExactAt j) : Epi (K.toCycles i j) := by
  subst i
  exact h.epi_toCycles

/-- The short complex `Zⁱ(K) → Kⁱ → Zⁱ⁺¹(K)` of a cochain complex `K`. -/
@[implicit_reducible]
private noncomputable def cyclesSequence (K : CochainComplex A ℤ) (i : ℤ) : ShortComplex A :=
  ShortComplex.mk (K.iCycles i) (K.toCycles i (i + 1)) (by
    rw [← cancel_mono (K.iCycles (i + 1)), Category.assoc, K.toCycles_i,
      K.iCycles_d, zero_comp])

/-- If `K` is exact in degree `i + 1`, then `0 → Zⁱ(K) → Kⁱ → Zⁱ⁺¹(K) → 0` is short exact. -/
private lemma cyclesSequence_shortExact (K : CochainComplex A ℤ) (i : ℤ)
    (h : K.ExactAt (i + 1)) : (cyclesSequence K i).ShortExact := by
  have := epi_toCycles_of_exactAt K i (i + 1) (by simp) h
  dsimp only [cyclesSequence]
  refine { exact := ?_ }
  apply ShortComplex.exact_of_f_is_kernel
  exact isKernelOfComp (K.iCycles (i + 1)) (K.d i (i + 1))
    (K.cyclesIsKernel i (i + 1) (by simp)) (cyclesSequence K i).zero (K.toCycles_i i (i + 1))

/-- Along the exact tail of a complex `K` of objects with `d = 0`, the function `d` drops by at
least one at each step of the cycles. -/
private lemma dimension_cycles_le
    (d : A → ℕ) (hd : Stacks.BoundedCohomologicalDimension.BoundedCohomologicalDimension (fun X =>
      (d X : ℕ∞)))
    (K : CochainComplex A ℤ) (hK : ∀ i, d (K.X i) = 0)
    (a : ℤ) (hex : ∀ i : ℤ, a < i → K.ExactAt i) :
    ∀ m : ℕ, d (K.cycles (a + m)) ≤ d (K.cycles a) - m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have he := hd.shortExact_le (cyclesSequence K (a + m))
      (cyclesSequence_shortExact K (a + m) (hex _ (by omega)))
    dsimp only [cyclesSequence] at he
    rw [hK, Nat.cast_zero, max_zero, ← ENat.natCast_one, ← ENat.natCast_sub] at he
    have he' := ENat.natCast_le_natCast.1 he
    have hm : a + (m + 1 : ℕ) = a + (m : ℤ) + 1 := by omega
    rw [hm]
    omega

/-- If `d ≤ N` and `K` is a complex of objects with `d = 0` that is exact in degrees `> a`, then
`d(Z^{a + N}(K)) = 0`. -/
private lemma dimension_cycles_eq_zero
    (d : A → ℕ) (hd : Stacks.BoundedCohomologicalDimension.BoundedCohomologicalDimension (fun X =>
      (d X : ℕ∞)))
    (N : ℕ) (hN : ∀ X, d X ≤ N)
    (K : CochainComplex A ℤ) (hK : ∀ i, d (K.X i) = 0)
    (a : ℤ) (hex : ∀ i : ℤ, a < i → K.ExactAt i) : d (K.cycles (a + N)) = 0 := by
  have h := dimension_cycles_le d hd K hK a hex N
  have h' := hN (K.cycles a)
  omega

end Cycles

include hGE hres in
/-- For left exact `F`, the isomorphism `F ≅ R⁰ F`. -/
private noncomputable def derivedZeroIso [PreservesFiniteLimits F] :
    F ≅ Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B 0 := by
  let β := Functor.whiskerRight (Functor.whiskerLeft
    (HomotopyCategory.Plus.singleFunctor A 0) α) (Plus.homologyFunctor B 0)
  have (X : A) : IsIso (β.app X) := isIso_homology_zero_unit F RF α hGE hres X
  have : IsIso β := NatIso.isIso_of_isIso_app β
  exact (Functor.rightDerivedZeroSourceIso F).symm ≪≫ asIso β ≪≫
    Functor.rightDerivedZeroTargetIso RF

include hGE hres in
/-- For left exact `F` and a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with `X₁[0]` computing
`RF`, the map `F(X₂) → F(X₃)` is an epimorphism. -/
private lemma epi_map_of_isIso_unit [PreservesFiniteLimits F]
    (S : ShortComplex A) (hS : S.ShortExact)
    (hX : IsIso (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj S.X₁))) :
    Epi (F.map S.g) := by
  obtain ⟨δ, hT'⟩ := exists_distTriang_map_single RF S hS
  have he : Epi ((Plus.singleFunctor A 0 ⋙ RF ⋙ Plus.homologyFunctor B 0).map S.g) :=
    ((Plus.homologyFunctor B 0).homologySequence_epi_shift_map_mor₂_iff _ hT' 0 1 (by omega)).2
      ((isZero_homology_of_isIso_unit F RF α S.X₁ hX 1 (by omega)).eq_of_tgt _ _)
  let e := derivedZeroIso F RF α hGE hres
  have : Epi (F.map S.g ≫ e.hom.app S.X₃) := by
    rw [e.hom.naturality]
    infer_instance
  exact (epi_comp_iff_of_isIso (F.map S.g) (e.hom.app S.X₃)).1 inferInstance

include hGE hres in
/-- For left exact `F`, an acyclic complex `K` whose cycles compute `RF` has acyclic image
`F(K)`. -/
private lemma map_acyclic_of_cycles_computing [PreservesFiniteLimits F]
    (K : CochainComplex A ℤ) (hK : K.Acyclic)
    (hc : ∀ i, IsIso (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj (K.cycles i)))) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  intro i
  let S : ShortComplex B := ShortComplex.mk (F.map (K.d (i - 1) i)) (F.map (K.d i (i + 1)))
    (by rw [← F.map_comp, K.d_comp_d, F.map_zero])
  let S' : ShortComplex B := ShortComplex.mk (F.map (K.iCycles i)) (F.map (K.d i (i + 1)))
    (by rw [← F.map_comp, K.iCycles_d, F.map_zero])
  have he : Epi (F.map (K.toCycles (i - 1) i)) := by
    have h := epi_map_of_isIso_unit F RF α hGE hres (cyclesSequence K (i - 1))
      (cyclesSequence_shortExact K (i - 1) (by simpa using hK i)) (hc (i - 1))
    have h' : Epi (F.map (K.toCycles (i - 1) (i - 1 + 1))) := h
    rwa [sub_add_cancel] at h'
  let φ : S ⟶ S' :=
    { τ₁ := F.map (K.toCycles (i - 1) i)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, S', ← F.map_comp]
      comm₂₃ := by simp [S, S'] }
  have hS' : S'.Exact := ShortComplex.exact_of_f_is_kernel _
    (KernelFork.mapIsLimit _ (K.cyclesIsKernel i (i + 1) (by simp)) F)
  have : Epi φ.τ₁ := he
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  let e : S ≅ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).sc' (i - 1) i (i + 1) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact (HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)).2
    ((ShortComplex.exact_iff_of_iso e).1
      ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS'))

section BoundedPreservation

variable (P : ObjectProperty A)
  (hP : ∀ X : A, P X ↔ IsIso (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)))
  (d : A → ℕ) (hd : Stacks.BoundedCohomologicalDimension.BoundedCohomologicalDimension (fun X => (d
    X : ℕ∞)))
  (hdP : ∀ X, d X = 0 ↔ P X) (N : ℕ) (hN : ∀ X, d X ≤ N)

omit [RF.CommShift ℤ] [RF.IsTriangulated] in
include hP in
/-- The class `P` is closed under isomorphisms. -/
private lemma property_of_iso {X Y : A} (e : X ≅ Y) (hX : P X) : P Y :=
  (hP Y).2 ((NatTrans.isIso_app_iff_of_iso α
    ((HomotopyCategory.Plus.singleFunctor A 0).mapIso e)).1 ((hP X).1 hX))

omit [HasDerivedCategory A] in
include hd hdP in
/-- The class `P` is closed under binary biproducts. -/
private lemma property_biprod (X Y : A) (hX : P X) (hY : P Y) : P (X ⊞ Y) := by
  apply (hdP _).1
  have h := hd.biprod_le X Y
  rw [(hdP X).2 hX, (hdP Y).2 hY, Nat.cast_zero, max_self] at h
  exact Nat.eq_zero_of_le_zero (ENat.natCast_le_natCast.1 h)

include hP in
/-- The class `P` contains the zero objects. -/
private lemma property_of_isZero {X : A} (hX : IsZero X) : P X :=
  (hP X).2 <| ((F.mapHomotopyCategoryPlus ⋙ Plus.Qh).map_isZero
    ((HomotopyCategory.Plus.singleFunctor A 0).map_isZero hX)).isIso
    ((Plus.Qh ⋙ RF).map_isZero ((HomotopyCategory.Plus.singleFunctor A 0).map_isZero hX)) _

omit [HasDerivedCategory A] in
include hd hdP hN in
/-- If `K` is a complex with terms in `P` which is exact in degrees `> a`, then its cycles in
degree `a + N` are in `P`. -/
private lemma property_cycles_of_exact_tail (K : CochainComplex A ℤ) (hK : ∀ i, P (K.X i))
    (a : ℤ) (hex : ∀ i : ℤ, a < i → K.ExactAt i) : P (K.cycles (a + N)) :=
  (hdP _).1 (dimension_cycles_eq_zero d hd N hN K (fun i => (hdP _).2 (hK i)) a hex)

include hGE hres hP hd hdP hN in
/-- Uniform dimension bounds force every cycle of an acyclic complex of computing objects
to compute as well; left exactness and dimension shifting then preserve exactness. -/
private lemma map_acyclic_of_bounded_dimension [PreservesFiniteLimits F]
    (K : CochainComplex A ℤ) (hK : K.Acyclic) (hKP : ∀ i, P (K.X i)) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  apply map_acyclic_of_cycles_computing F RF α hGE hres K hK
  intro i
  apply (hP _).1
  have h := property_cycles_of_exact_tail P d hd hdP N hN K hKP (i - N) (fun j _ => hK j)
  rwa [sub_add_cancel] at h

include hGE hres hP hd hdP hN in
/-- `F` preserves quasi-isomorphisms between complexes with terms in `P`: the mapping cone of such
a quasi-isomorphism is an acyclic complex with terms in `P`. -/
private lemma map_quasiIso_of_bounded_dimension [PreservesFiniteLimits F]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (hf : QuasiIso f)
    (hK : ∀ i, P (K.X i)) (hL : ∀ i, P (L.X i)) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have hc := map_acyclic_of_bounded_dimension F RF α hGE hres P hP d hd hdP N hN
    (CochainComplex.mappingCone f) (Functor.acyclic_mappingCone f hf) (fun i =>
      property_of_iso F RF α P hP
        (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl).symm
        (property_biprod P d hd hdP _ _ (hK (i + 1)) (hL i)))
  apply Functor.quasiIso_of_acyclic_mappingCone
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hc i).isZero_homology.of_iso
    (((HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) i).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso f F)).symm)

include hP hd hdP hN in
/-- After `N` exact steps, the boundary cycle has dimension zero, so the good truncation
still consists of computing objects. -/
private lemma property_truncLE [PreservesFiniteLimits F]
    (K : CochainComplex A ℤ) (hK : ∀ i, P (K.X i)) (a : ℤ) [K.IsLE a] :
    ∀ i, P ((K.truncLE (a + N)).X i) := by
  intro i
  rcases lt_trichotomy i (a + N) with hi | rfl | hi
  · exact property_of_iso F RF α P hP (K.truncLEXIso (a + N) i hi).symm (hK i)
  · exact property_of_iso F RF α P hP (K.truncLEXIsoCycles (a + N)).symm
      (property_cycles_of_exact_tail P d hd hdP N hN K hK a
        ((CochainComplex.isLE_iff K a).1 inferInstance))
  · exact property_of_isZero F RF α P hP
      ((CochainComplex.isStrictlyLE_iff _ (a + N)).1 inferInstance i hi)

end BoundedPreservation

section Amplitude

variable (P : ObjectProperty A)
  (R : DerivedCategory A ⥤ DerivedCategory B)
  (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
  (hcomp : ∀ K : CochainComplex A ℤ, (∀ i, P (K.X i)) →
    IsIso (β.app ((HomotopyCategory.quotient A _).obj K)))

/-- If `β` is invertible at a complex `K`, then `Q(F(K)) ≅ R(Q(K))`. -/
private noncomputable def computationIso (K : CochainComplex A ℤ) (hK : ∀ i, P (K.X i)) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      R.obj (DerivedCategory.Q.obj K) :=
  have := hcomp K hK
  ((DerivedCategory.quotientCompQhIso B).app _).symm ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K).symm ≪≫
    asIso (β.app ((HomotopyCategory.quotient A _).obj K)) ≪≫
    R.mapIso ((DerivedCategory.quotientCompQhIso A).app K)

include hcomp in
/-- If complexes with terms in `P` compute `R`, and every object embeds into an object of `P`, then
`R` preserves the lower bound of the degrees in which an object lives. -/
private lemma isGE_of_computing_replacements [P.ContainsZero]
    (hmono : ∀ X : A, ∃ (Y : A) (_ : P Y) (i : X ⟶ Y), Mono i)
    (E : DerivedCategory A) (a : ℤ) (hE : E.IsGE a) : (R.obj E).IsGE a := by
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have : (DerivedCategory.Q.obj K).IsGE a := TStructure.t.isGE_of_iso e.symm a
  have : K.IsGE a := (DerivedCategory.isGE_Q_obj_iff K a).1 inferInstance
  obtain ⟨I, f, hf, hI, _, hIa⟩ :=
    CochainComplex.exists_quasiIso_prop_isStrictlyGE P hmono a K
  have : QuasiIso f := hf
  have : (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)).IsGE a :=
    inferInstance
  exact TStructure.t.isGE_of_iso
    (computationIso F P R β hcomp I hI ≪≫ R.mapIso ((asIso (DerivedCategory.Q.map f)).symm ≪≫ e)) a

include hcomp in
/-- If complexes with terms in `P` compute `R`, every complex has a replacement with terms in `P`,
and truncations `τ_{≤ a + N}` of such replacements have terms in `P`, then `R` shifts the upper
bound of the degrees in which an object lives by at most `N`. -/
private lemma isLE_of_computing_replacements (N : ℕ)
    (hreplace : ∀ K : CochainComplex A ℤ,
      ∃ (L : CochainComplex A ℤ) (f : K ⟶ L) (_ : QuasiIso f), ∀ i, P (L.X i))
    (htrunc : ∀ (K : CochainComplex A ℤ), (∀ i, P (K.X i)) → ∀ a : ℤ, K.IsLE a →
      ∀ i, P ((K.truncLE (a + N)).X i))
    (E : DerivedCategory A) (a : ℤ) (hE : E.IsLE a) : (R.obj E).IsLE (a + N) := by
  let K := DerivedCategory.Q.objPreimage E
  obtain ⟨I, f, hf, hI⟩ := hreplace K
  have : QuasiIso f := hf
  let e : DerivedCategory.Q.obj I ≅ E :=
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have : (DerivedCategory.Q.obj I).IsLE a := TStructure.t.isLE_of_iso e.symm a
  have : I.IsLE a := (DerivedCategory.isLE_Q_obj_iff I a).1 inferInstance
  have : I.IsLE (a + N) := CochainComplex.isLE_of_le I a (a + N) (by omega)
  have : (DerivedCategory.Q.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.truncLE (a + N)))).IsLE (a + N) :=
    inferInstance
  exact TStructure.t.isLE_of_iso
    (computationIso F P R β hcomp _ (htrunc I hI a inferInstance) ≪≫
      R.mapIso (asIso (DerivedCategory.Q.map (I.ιTruncLE (a + N))) ≪≫ e)) (a + N)

end Amplitude

section Canonical

variable (R : DerivedCategory A ⥤ DerivedCategory B) [R.CommShift ℤ] [R.IsTriangulated]
  (N : ℕ)
  (hLower : ∀ (E : DerivedCategory A) (a : ℤ), E.IsGE a → (R.obj E).IsGE a)
  (hUpper : ∀ (E : DerivedCategory A) (a : ℤ), E.IsLE a → (R.obj E).IsLE (a + N))

include hLower in
/-- If `R` preserves lower bounds, then `Hⁱ(R(τ_{≤ a} E)) → Hⁱ(R(E))` is invertible for `i ≤ a`. -/
private lemma isIso_homology_map_truncLE (E : DerivedCategory A) (a i : ℤ) (hi : i ≤ a) :
    IsIso ((DerivedCategory.homologyFunctor B i).map
      (R.map ((TStructure.t.truncLEι a).app E))) := by
  let T := R.mapTriangle.obj ((TStructure.t.triangleLEGE a (a + 1) rfl).obj E)
  have ht : T ∈ distTriang (DerivedCategory B) :=
    R.map_distinguished _ (TStructure.t.triangleLEGE_distinguished a (a + 1) rfl E)
  have hg : T.obj₃.IsGE (a + 1) :=
    hLower ((TStructure.t.truncGE (a + 1)).obj E) (a + 1) inferInstance
  have hz : IsZero ((DerivedCategory.homologyFunctor B i).obj T.obj₃) :=
    T.obj₃.isZero_of_isGE (a + 1) i (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor B (i - 1)).obj T.obj₃) :=
    T.obj₃.isZero_of_isGE (a + 1) (i - 1) (by omega)
  have : Epi ((DerivedCategory.homologyFunctor B i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_epi_shift_map_mor₁_iff T ht i).2
      (hz.eq_of_tgt _ _)
  have : Mono ((DerivedCategory.homologyFunctor B i).map T.mor₁) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_mono_shift_map_mor₁_iff
      T ht (i - 1) i (by omega)).2 (hz'.eq_of_src _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor B i).map T.mor₁)

include hUpper in
/-- If `R` shifts upper bounds by at most `N`, then `Hⁱ(R(E)) → Hⁱ(R(τ_{≥ b - N} E))` is invertible
for `i ≥ b`. -/
private lemma isIso_homology_map_truncGE (E : DerivedCategory A) (b i : ℤ) (hi : b ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor B i).map
      (R.map ((TStructure.t.truncGEπ (b - N)).app E))) := by
  let T := R.mapTriangle.obj
    ((TStructure.t.triangleLEGE (b - N - 1) (b - N) (by omega)).obj E)
  have ht : T ∈ distTriang (DerivedCategory B) := R.map_distinguished _
    (TStructure.t.triangleLEGE_distinguished (b - N - 1) (b - N) (by omega) E)
  have hl : T.obj₁.IsLE (b - N - 1 + N) :=
    hUpper ((TStructure.t.truncLE (b - N - 1)).obj E) (b - N - 1) inferInstance
  have hz : IsZero ((DerivedCategory.homologyFunctor B i).obj T.obj₁) :=
    T.obj₁.isZero_of_isLE (b - N - 1 + N) i (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor B (i + 1)).obj T.obj₁) :=
    T.obj₁.isZero_of_isLE (b - N - 1 + N) (i + 1) (by omega)
  have : Mono ((DerivedCategory.homologyFunctor B i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_mono_shift_map_mor₂_iff T ht i).2
      (hz.eq_of_src _ _)
  have : Epi ((DerivedCategory.homologyFunctor B i).map T.mor₂) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_epi_shift_map_mor₂_iff
      T ht i (i + 1) rfl).2 (hz'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor B i).map T.mor₂)

end Canonical

/-- A right derived functor computed by the complexes with terms in `P`, which have enough
replacements and are closed under mapping cones, is triangulated. -/
public theorem isTriangulated_of_acyclic_replacements
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    (RF : DerivedCategory C ⥤ DerivedCategory D)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.CommShift ℤ] [NatTrans.CommShift α ℤ]
    (P : ObjectProperty C)
    (hPiso : ∀ {X Y : C}, (X ≅ Y) → P X → P Y)
    (hPsum : ∀ X Y : C, P X → P Y → P (X ⊞ Y))
    (hreplace : ∀ K : CochainComplex C ℤ,
      ∃ (L : CochainComplex C ℤ) (f : K ⟶ L) (_ : QuasiIso f), ∀ i : ℤ, P (L.X i))
    (hcompute : ∀ K : CochainComplex C ℤ, (∀ i : ℤ, P (K.X i)) →
      IsIso (α.app ((HomotopyCategory.quotient _ _).obj K))) : RF.IsTriangulated := by
  let Q : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C := DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  have := Localization.essSurj_mapArrow Q W
  apply RF.isTriangulated_of_leftExtension α
  intro X Y f
  let a := Q.mapArrow.objPreimage (Arrow.mk f)
  let e : Arrow.mk (Q.map a.hom) ≅ Arrow.mk f := Q.mapArrow.objObjPreimageIso _
  obtain ⟨K, r, hr, hK⟩ := hreplace a.left.as
  let rH : a.left ⟶ (HomotopyCategory.quotient _ _).obj K :=
    (HomotopyCategory.quotient _ _).map r
  have hrW : W rH := (HomotopyCategory.quotient_map_mem_quasiIso_iff r).2 hr
  let ψ : W.RightFraction ((HomotopyCategory.quotient _ _).obj K) a.right :=
    { s := rH, hs := hrW, f := a.hom }
  obtain ⟨q, hq⟩ := ψ.exists_leftFraction
  obtain ⟨L, s, hs, hL⟩ := hreplace q.Y'.as
  let sH : q.Y' ⟶ (HomotopyCategory.quotient _ _).obj L :=
    (HomotopyCategory.quotient _ _).map s
  have hsW : W sH := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
  let b : (HomotopyCategory.quotient _ _).obj K ⟶ (HomotopyCategory.quotient _ _).obj L :=
    q.f ≫ sH
  let b₀ : K ⟶ L := (HomotopyCategory.quotient _ _).preimage b
  have hb : (HomotopyCategory.quotient _ _).map b₀ = b := Functor.map_preimage _ _
  have hw : rH ≫ b = a.hom ≫ q.s ≫ sH := by
    simpa only [b, Category.assoc] using (hq =≫ sH).symm
  let e₀ : Arrow.mk (Q.map a.hom) ≅ Arrow.mk (Q.map b) :=
    Arrow.isoMk (Localization.isoOfHom Q W rH hrW)
      (Localization.isoOfHom Q W (q.s ≫ sH) (W.comp_mem _ _ q.hs hsW)) (by
        rw [Localization.isoOfHom_hom, Localization.isoOfHom_hom]
        exact (Q.map_comp _ _).symm.trans ((congrArg Q.map hw).trans (Q.map_comp _ _)))
  refine ⟨CochainComplex.mappingCone.triangleh b₀,
    HomotopyCategory.mappingCone_triangleh_distinguished b₀,
    hcompute K hK, hcompute L hL, hcompute _ ?_, ?_⟩
  · intro i
    exact hPiso (HomologicalComplex.homotopyCofiber.XIsoBiprod b₀ i (i + 1) rfl).symm
      (hPsum _ _ (hK (i + 1)) (hL i))
  · rw [CochainComplex.mappingCone.triangleh, Functor.mapTriangle_obj]
    simp only [Triangle.mk_mor₁, CochainComplex.mappingCone.triangle_mor₁]
    have e₁ : Arrow.mk (Q.map ((HomotopyCategory.quotient _ _).map b₀)) ≅ Arrow.mk (Q.map b) := by
      rw [hb]
    exact ⟨e₁ ≪≫ e₀.symm ≪≫ e⟩

end Plus

section DerivedFunctor

/-- A full subcategory admitting right resolutions computes the right derived functor
whenever the functor inverts weak equivalences within that subcategory. -/
private lemma hasPointwiseRightDerivedFunctor_and_isIso_of_resolutions
    {C H : Type*} [Category* C] [Category* H]
    (G : C ⥤ H) (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (P : ObjectProperty C)
    (hres : ∀ X, ∃ (Y : C) (_ : P Y) (r : X ⟶ Y), W r)
    (hinv : ∀ {X Y : C} (f : X ⟶ Y), W f → P X → P Y → IsIso (G.map f)) :
    G.HasPointwiseRightDerivedFunctor W ∧
      ∀ {D : Type*} [Category* D] (L : C ⥤ D) [L.IsLocalization W]
        (RG : D ⥤ H) (α : G ⟶ L ⋙ RG) [RG.IsRightDerivedFunctor α W],
        ∀ X : C, P X → IsIso (α.app X) := by
  let Φ := LocalizerMorphism.ofEq (F := P.ι) (W₁ := W.inverseImage P.ι) rfl
  have : Φ.IsRightDerivabilityStructure :=
    Functor.rightDerivability_of_resolutions W P hres
  have hderive : Φ.Derives G := fun X Y f hf ↦ hinv f.hom hf X.property Y.property
  exact ⟨hderive.hasPointwiseRightDerivedFunctor,
    fun _ _ RG α _ X hX ↦ hderive.isIso_of_isRightDerivedFunctor α ⟨X, hX⟩⟩

end DerivedFunctor

section ZeroFunctor

/-- A right derived functor of a zero functor is zero, and its unit is invertible. -/
private lemma isIso_and_isZero_of_isRightDerivedFunctor_of_isZero
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    {G : C ⥤ H} (hG : ∀ X, IsZero (G.obj X))
    {W : MorphismProperty C} (L : C ⥤ D) [L.IsLocalization W]
    (RG : D ⥤ H) (α : G ⟶ L ⋙ RG) [RG.IsRightDerivedFunctor α W] :
    IsIso α ∧ ∀ Y, IsZero (RG.obj Y) := by
  have hinv : W.IsInvertedBy G := fun X Y f _ ↦ (hG X).isIso (hG Y) (G.map f)
  have hα := Functor.isIso_of_isRightDerivedFunctor_of_inverts RG α hinv
  have := Localization.essSurj L W
  exact ⟨hα, fun Y ↦ (hG (L.objPreimage Y)).of_iso
    ((RG.mapIso (L.objObjPreimageIso Y)).symm ≪≫ (asIso (α.app (L.objPreimage Y))).symm)⟩

end ZeroFunctor

section ZeroObjects

/-- A left Kan extension along a functor between categories with zero objects sends zero
objects to zero objects if the functor being extended preserves zero morphisms. -/
private lemma isZero_obj_zero_of_isLeftKanExtension
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    [HasZeroMorphisms C] [HasZeroMorphisms H] [HasZeroObject C] [HasZeroObject D]
    {F : C ⥤ H} [F.PreservesZeroMorphisms] {L : C ⥤ D}
    (G : D ⥤ H) (α : F ⟶ L ⋙ G) [G.IsLeftKanExtension α] :
    IsZero (G.obj 0) := by
  have hD : IsZero (0 : D) := isZero_zero D
  let mk : (G.obj 0 ⟶ G.obj 0) → (G ⟶ (Functor.const D).obj (G.obj 0)) := fun f ↦
    { app := fun X ↦ G.map (hD.from_ X) ≫ f
      naturality := fun X Y g ↦ by
        dsimp
        rw [Category.comp_id, ← Category.assoc, ← G.map_comp]
        congr 2
        exact hD.eq_of_tgt _ _ }
  have key : mk (𝟙 _) = mk 0 := by
    refine G.hom_ext_of_isLeftKanExtension α _ _ ?_
    ext c
    have hnat := α.naturality (0 : c ⟶ (0 : C))
    dsimp [mk] at hnat ⊢
    rw [Category.comp_id, comp_zero,
      show hD.from_ (L.obj c) = L.map (0 : c ⟶ (0 : C)) ≫ hD.from_ (L.obj 0) from
        hD.eq_of_tgt _ _, G.map_comp, ← Category.assoc, ← hnat]
    simp
  have h := congrArg (fun t ↦ NatTrans.app t 0) key
  dsimp [mk] at h
  rw [show hD.from_ (0 : D) = 𝟙 (0 : D) from hD.eq_of_tgt _ _] at h
  rw [IsZero.iff_id_eq_zero]
  simpa using h

end ZeroObjects

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]

/-- Vanishing of degree-zero derived values and enough objects computing those values
force a left exact functor itself to vanish. -/
private lemma isZero_obj_of_isZero_homology_zero
    (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ RF)
    (hres : ∀ X : A, ∃ (Y : A) (i : X ⟶ Y), Mono i ∧
      IsIso (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj Y)))
    (hzero : ∀ X : A, IsZero ((DerivedCategory.Plus.homologyFunctor B 0).obj
      (RF.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) (X : A) :
    IsZero (F.obj X) := by
  obtain ⟨Y, i, hi, hY⟩ := hres X
  have hFY : IsZero (F.obj Y) := (hzero Y).of_iso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).app (F.obj Y)).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor B 0).mapIso
        (((Functor.mapSingleFunctorCompQhIso F).app Y).symm ≪≫
          asIso (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj Y)) ≪≫
          RF.mapIso ((Functor.singleFunctorPlusIsoCompQh 0).app Y).symm))
  exact hFY.of_mono (F.map i)

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- Applying a zero functor termwise gives a zero object in the homotopy category. -/
private lemma isZero_mapHomotopyCategory_obj_of_isZero
    (F : A ⥤ B) [F.Additive] (hF : ∀ X, IsZero (F.obj X))
    (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    IsZero ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hK : IsZero ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
    rw [IsZero.iff_id_eq_zero]
    ext i
    exact (hF (K.X i)).eq_of_src _ _
  exact ((HomotopyCategory.quotient B _).map_isZero hK).of_iso
    ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app K)

omit [HasDerivedCategory A] in
/-- A uniformly bounded dimension function satisfies the growth condition of 07K6 for
every complex. -/
private lemma exists_quasiIso_of_bounded_dimension
    (d : A → ℕ)
    (hd : Stacks.BoundedCohomologicalDimension.BoundedCohomologicalDimension (fun X ↦ (d X : ℕ∞)))
    (N : ℕ) (hN : ∀ X, d X ≤ N) (K : CochainComplex A ℤ) :
    ∃ (L : CochainComplex A ℤ) (f : K ⟶ L), QuasiIso f ∧ ∀ i : ℤ, d (L.X i) = 0 := by
  have hK : Stacks.BoundedCohomologicalDimension.TendsToNegInfty (fun X ↦ (d X : ℕ∞)) K := by
    intro a
    refine ⟨a - N, fun i hi ↦ ⟨d (K.X i), rfl, ?_⟩⟩
    have h := hN (K.X i)
    omega
  obtain ⟨L, f, hf, hL⟩ := Stacks.BoundedCohomologicalDimension.main_theorem_07k6 _ hd K hK
  exact ⟨L, f, hf, fun i ↦ by simpa using hL i⟩

/-- Termwise acyclic replacements compute the unbounded derived functor if termwise
application preserves quasi-isomorphisms between them. -/
private lemma hasRightDerivedFunctor_and_isIso_of_acyclic_replacements
    (F : A ⥤ B) [F.Additive] (P : ObjectProperty A)
    (hres : ∀ K : CochainComplex A ℤ,
      ∃ (L : CochainComplex A ℤ) (f : K ⟶ L), QuasiIso f ∧ ∀ i, P (L.X i))
    (hinv : ∀ {K L : CochainComplex A ℤ} (f : K ⟶ L), QuasiIso f →
      (∀ i, P (K.X i)) → (∀ i, P (L.X i)) →
      QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      ∀ (RF : DerivedCategory A ⥤ DerivedCategory B)
        (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ RF)
        [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))],
        ∀ K : CochainComplex A ℤ, (∀ i, P (K.X i)) →
          IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) := by
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let G := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let I : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) :=
    fun K ↦ ∀ i, P (K.as.X i)
  have : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  obtain ⟨hG, hcompute⟩ := hasPointwiseRightDerivedFunctor_and_isIso_of_resolutions G W I
    (by
      intro K
      obtain ⟨L, f, hf, hL⟩ := hres K.as
      exact ⟨(HomotopyCategory.quotient A _).obj L, hL,
        (HomotopyCategory.quotient A _).map f,
        (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf⟩)
    (by
      intro K L f hf hK hL
      have hq : QuasiIso f.out := by
        apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1
        rwa [HomotopyCategory.quotient_map_out]
      have hF := hinv f.out hq hK hL
      have key : HomotopyCategory.quasiIso B _ ((F.mapHomotopyCategory _).map
          ((HomotopyCategory.quotient A _).map f.out)) := by
        rw [Functor.mapHomotopyCategory_map]
        exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hF
      rw [HomotopyCategory.quotient_map_out] at key
      exact Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) _ key)
  let := hG
  exact ⟨inferInstance, fun RF α _ K hK ↦ hcompute DerivedCategory.Qh RF α _ hK⟩

/-- A right derived functor of the functor on homotopy categories preserves zero morphisms. -/
private lemma preservesZeroMorphisms_of_isRightDerivedFunctor
    (F : A ⥤ B) [F.Additive] (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))] :
    RF.PreservesZeroMorphisms := by
  have := Functor.IsRightDerivedFunctor.isLeftKanExtension RF α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  exact Functor.preservesZeroMorphisms_of_map_zero_object
    (isZero_obj_zero_of_isLeftKanExtension RF α).isoZero

/-- The canonical lower truncation comparison implies preservation of a lower
cohomological bound. -/
private lemma isGE_obj_of_isIso_homology_map_truncLEι
    (G : DerivedCategory A ⥤ DerivedCategory B) [G.PreservesZeroMorphisms]
    (E : DerivedCategory A)
    (h : ∀ i : ℤ, IsIso ((DerivedCategory.homologyFunctor B i).map
      (G.map ((TStructure.t.truncLEι i).app E))))
    (a : ℤ) (hE : E.IsGE a) : (G.obj E).IsGE a := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have : TStructure.t.IsGE E a := hE
  have : TStructure.t.IsGE E (i + 1) := TStructure.t.isGE_of_ge E (i + 1) a (by omega)
  have hz : IsZero ((TStructure.t.truncLE i).obj E) :=
    TStructure.t.isZero_truncLE_obj_of_isGE i (i + 1) (by omega) E
  have := h i
  exact (Functor.map_isZero _ (Functor.map_isZero G hz)).of_iso
    (asIso ((DerivedCategory.homologyFunctor B i).map
      (G.map ((TStructure.t.truncLEι i).app E)))).symm

/-- The canonical upper truncation comparison shifts an upper cohomological bound
by the same integer. -/
private lemma isLE_obj_of_isIso_homology_map_truncGEπ
    (G : DerivedCategory A ⥤ DerivedCategory B) [G.PreservesZeroMorphisms]
    (E : DerivedCategory A) (d : ℤ)
    (h : ∀ i : ℤ, IsIso ((DerivedCategory.homologyFunctor B i).map
      (G.map ((TStructure.t.truncGEπ (i - d)).app E))))
    (b : ℤ) (hE : E.IsLE b) : (G.obj E).IsLE (b + d) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have : TStructure.t.IsLE E b := hE
  have : TStructure.t.IsLE E (i - d - 1) :=
    TStructure.t.isLE_of_le E b (i - d - 1) (by omega)
  have hz : IsZero ((TStructure.t.truncGE (i - d)).obj E) :=
    TStructure.t.isZero_truncGE_obj_of_isLE (i - d - 1) (i - d) (by omega) E
  have := h i
  exact (Functor.map_isZero _ (Functor.map_isZero G hz)).of_iso
    (asIso ((DerivedCategory.homologyFunctor B i).map
      (G.map ((TStructure.t.truncGEπ (i - d)).app E))))

/-- The conclusion of Stacks 07K7 for the functor `F`, the class `P` of right acyclic objects and
the bound `n` on the cohomological dimension. -/
private abbrev Conclusion (F : A ⥤ B) [F.Additive] (P : ObjectProperty A) (n : ℕ) : Prop :=
  (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
    (∀ K : CochainComplex A ℤ, ∃ (L : CochainComplex A ℤ) (f : K ⟶ L) (_ : QuasiIso f),
      ∀ i : ℤ, P (L.X i)) ∧
    ∀ (RF : DerivedCategory A ⥤ DerivedCategory B)
      (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF)
      [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))],
      (∀ L : CochainComplex A ℤ, (∀ i : ℤ, P (L.X i)) →
          IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L))) ∧
        ∀ E : DerivedCategory A,
          (∀ a i : ℤ, i ≤ a → IsIso ((DerivedCategory.homologyFunctor B i).map
              (RF.map ((TStructure.t.truncLEι a).app E)))) ∧
            (∀ b i : ℤ, b ≤ i → IsIso ((DerivedCategory.homologyFunctor B i).map
              (RF.map ((TStructure.t.truncGEπ (b - (n : ℤ) + 1)).app E)))) ∧
              (∀ a : ℤ, E.IsGE a → (RF.obj E).IsGE a) ∧
                ∀ b : ℤ, E.IsLE b → (RF.obj E).IsLE (b + (n : ℤ) - 1)

/-- Stacks 07K7 when `F = 0`: every right derived functor is zero with invertible unit, and every
object is right acyclic. -/
private lemma conclusion_of_isZero (F : A ⥤ B) [F.Additive] (P : ObjectProperty A)
    (hP : ∀ X, P X) (hF : ∀ X, IsZero (F.obj X)) : Conclusion F P 0 := by
  have hG (K : HomotopyCategory A (ComplexShape.up ℤ)) :
      IsZero ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) :=
    DerivedCategory.Qh.map_isZero (isZero_mapHomotopyCategory_obj_of_isZero F hF K)
  have hinv : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
    fun K L f _ ↦ (hG K).isIso (hG L) _
  have := Functor.hasPointwiseRightDerivedFunctor_of_inverts _ hinv
  refine ⟨inferInstance, fun K ↦ ⟨K, 𝟙 K, inferInstance, fun i ↦ hP (K.X i)⟩, ?_⟩
  intro RF α _
  obtain ⟨hα, hRF⟩ := isIso_and_isZero_of_isRightDerivedFunctor_of_isZero hG
    (W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh RF α
  refine ⟨fun K _ ↦ inferInstance, fun E ↦ ⟨fun a i _ ↦ ?_, fun b i _ ↦ ?_,
    fun a _ ↦ TStructure.t.isGE_of_isZero (hRF E) a,
    fun b _ ↦ TStructure.t.isLE_of_isZero (hRF E) _⟩⟩
  · have := (hRF _).isIso (hRF _) (RF.map ((TStructure.t.truncLEι a).app E))
    infer_instance
  · have := (hRF _).isIso (hRF _) (RF.map ((TStructure.t.truncGEπ (b - (0 : ℕ) + 1)).app E))
    infer_instance

/-- Stacks 07K7 from termwise right acyclic replacements: if every complex has a
quasi-isomorphism into a complex with terms in `P`, if `F` preserves quasi-isomorphisms between
such complexes, and if the good truncation `τ_{≤ a + N}` of such a complex concentrated in
degrees `≤ a` again has terms in `P`, then the conclusion holds with `n = N + 1`. -/
private lemma conclusion_of_replacements (F : A ⥤ B) [F.Additive] (P : ObjectProperty A)
    [P.ContainsZero] (hPiso : ∀ {X Y : A}, (X ≅ Y) → P X → P Y)
    (hPsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hmono : ∀ X : A, ∃ (Y : A) (i : X ⟶ Y) (_ : Mono i), P Y)
    (hres : ∀ K : CochainComplex A ℤ,
      ∃ (L : CochainComplex A ℤ) (f : K ⟶ L), QuasiIso f ∧ ∀ i, P (L.X i))
    (hinv : ∀ {K L : CochainComplex A ℤ} (f : K ⟶ L), QuasiIso f →
      (∀ i, P (K.X i)) → (∀ i, P (L.X i)) →
      QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
    (N : ℕ) (htrunc : ∀ K : CochainComplex A ℤ, (∀ i, P (K.X i)) → ∀ a : ℤ, K.IsLE a →
      ∀ i, P ((K.truncLE (a + N)).X i)) :
    Conclusion F P (N + 1) := by
  obtain ⟨hexists, hcompute⟩ :=
    hasRightDerivedFunctor_and_isIso_of_acyclic_replacements F P hres hinv
  have hreplace (K : CochainComplex A ℤ) :
      ∃ (L : CochainComplex A ℤ) (f : K ⟶ L) (_ : QuasiIso f), ∀ i, P (L.X i) :=
    let ⟨L, f, hf, hL⟩ := hres K
    ⟨L, f, hf, hL⟩
  refine ⟨hexists, hreplace, fun R β _ ↦ ?_⟩
  let := Functor.IsRightDerivedFunctor.commShift R β (HomotopyCategory.quasiIso A _) ℤ
  have := Functor.IsRightDerivedFunctor.natTrans_commShift R β (HomotopyCategory.quasiIso A _) ℤ
  have : R.IsTriangulated :=
    isTriangulated_of_acyclic_replacements F R β P hPiso hPsum hreplace (hcompute R β)
  have hLower := isGE_of_computing_replacements F P R β (hcompute R β) fun X ↦ by
    obtain ⟨Y, i, hi, hY⟩ := hmono X
    exact ⟨Y, hY, i, hi⟩
  have hUpper := isLE_of_computing_replacements F P R β (hcompute R β) N hreplace htrunc
  refine ⟨hcompute R β, fun E ↦ ⟨isIso_homology_map_truncLE R hLower E, fun b i hi ↦ ?_,
    hLower E, fun b hb ↦ ?_⟩⟩
  · have h := isIso_homology_map_truncGE R N hUpper E b i hi
    rwa [show b - (N : ℤ) = b - ((N + 1 : ℕ) : ℤ) + 1 by omega] at h
  · have h := hUpper E b hb
    rwa [show b + (N : ℤ) = b + ((N + 1 : ℕ) : ℤ) - 1 by omega] at h

variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (P : ObjectProperty A)
  (hP : ∀ X : A, P X ↔ (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
    (HomotopyCategory.Plus.quasiIso A) ((HomotopyCategory.Plus.singleFunctor A 0).obj X))
  (hmono : ∀ X : A, ∃ (Y : A) (i : X ⟶ Y) (_ : Mono i), P Y)

omit [PreservesFiniteLimits F] in
include hP hmono in
/-- Enough right acyclic objects in the sense of Stacks 05SX give objects computing `RF` for
every right derived functor `(RF, α)` on `D⁺`, detected by the invertibility of `α`. -/
private lemma iff_isIso_unit (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)] (X : A) :
    P X ↔ IsIso (α.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) :=
  (hP X).trans (Functor.computesRightDerived_iff_isIso_unit_of_enough_source_acyclic_objects F
    (fun X ↦ (hmono X).imp fun Y ⟨i, hi, hY⟩ ↦ ⟨i, hi, (hP Y).1 hY⟩) RF α _)

include hP hmono in
/-- Stacks 07K7 when `n > 0`. The right derived functor `R₀` on `D⁺` of Stacks 05TA is
triangulated and computed by right acyclic objects; the function `d (X) = max {i | Rⁱ F (X) ≠ 0}`
is bounded by `n - 1` and satisfies the hypotheses of Stacks 07K6, which supplies the
replacements, and it vanishes exactly on the right acyclic objects. -/
private lemma conclusion_of_pos (RF' : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (α' : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ RF')
    [RF'.IsRightDerivedFunctor α' (HomotopyCategory.Plus.quasiIso A)]
    (N : ℕ) (hn : ∀ X : A, IsZero ((DerivedCategory.Plus.homologyFunctor B (N + 1 : ℕ)).obj
      (RF'.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) :
    Conclusion F P (N + 1) := by
  have hsource (X : A) : ∃ (Y : A) (i : X ⟶ Y), Mono i ∧
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso A) ((HomotopyCategory.Plus.singleFunctor A 0).obj Y) :=
    (hmono X).imp fun Y ⟨i, hi, hY⟩ ↦ ⟨i, hi, (hP Y).1 hY⟩
  obtain ⟨hpoint, htri, _⟩ :=
    Functor.hasRightDerivedFunctor_of_enough_source_acyclic_objects F hsource
  let R₀ := (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerived
    Plus.Qh (HomotopyCategory.Plus.quasiIso A)
  let α₀ := (F.mapHomotopyCategoryPlus ⋙ Plus.Qh).totalRightDerivedUnit
    Plus.Qh (HomotopyCategory.Plus.quasiIso A)
  have : R₀.IsTriangulated := htri
  let e := Functor.rightDerivedUnique R₀ RF' α₀ α' (HomotopyCategory.Plus.quasiIso A)
  have hu₀ := iff_isIso_unit F P hP hmono R₀ α₀
  have hr₀ (X : A) : ∃ (Y : A) (i : X ⟶ Y), Mono i ∧
      IsIso (α₀.app ((HomotopyCategory.Plus.singleFunctor A 0).obj Y)) :=
    (hmono X).imp fun Y ⟨i, hi, hY⟩ ↦ ⟨i, hi, (hu₀ Y).1 hY⟩
  have hg₀ (X : A) : (R₀.obj ((Plus.singleFunctor A 0).obj X)).IsGE 0 := by
    have hX : CochainComplex.IsGE ((HomotopyCategory.Plus.singleFunctor A 0).obj X).obj.as 0 :=
      inferInstanceAs (CochainComplex.IsGE ((CochainComplex.singleFunctor A 0).obj X) 0)
    have : (R₀.obj ((HomotopyCategory.Plus.singleFunctor A 0 ⋙ Plus.Qh).obj X)).IsGE 0 :=
      (Functor.isIso_unit_and_isGE_of_enough_source_acyclic_objects F hsource R₀ α₀).2
        ((HomotopyCategory.Plus.singleFunctor A 0).obj X) 0 hX
    exact Plus.TStructure.t.isGE_of_iso
      (R₀.mapIso ((Functor.singleFunctorPlusIsoCompQh 0).app X).symm) 0
  have hv := isZero_homology_ge F R₀ α₀ hr₀ (N + 1)
    fun X ↦ (hn X).of_iso ((Plus.homologyFunctor B (N + 1 : ℕ)).mapIso (e.app _))
  let d := dimension R₀ (N + 1) hv
  have hd := boundedCohomologicalDimension F R₀ α₀ hg₀ hr₀ (N + 1) hv P hu₀ hmono
  have hdP := dimension_eq_zero_iff F R₀ α₀ hg₀ hr₀ (N + 1) hv P hu₀
  have hdN (X : A) : d X ≤ N :=
    (dimension_le_iff R₀ (N + 1) hv X N).2 fun i hi ↦ hv i (by omega) X
  have : P.ContainsZero := ⟨0, isZero_zero A, property_of_isZero F R₀ α₀ P hu₀ (isZero_zero A)⟩
  refine conclusion_of_replacements F P (fun e hX ↦ property_of_iso F R₀ α₀ P hu₀ e hX)
    (property_biprod P d hd hdP) hmono (fun K ↦ ?_)
    (map_quasiIso_of_bounded_dimension F R₀ α₀ hg₀ hr₀ P hu₀ d hd hdP N hdN) N
    (fun K hK a _ ↦ property_truncLE F R₀ α₀ P hu₀ d hd hdP N hdN K hK a)
  obtain ⟨L, f, hf, hL⟩ := exists_quasiIso_of_bounded_dimension d hd N hdN K
  exact ⟨L, f, hf, fun i ↦ (hdP _).1 (hL i)⟩

end StacksDraft.RightDerivedBoundedDimension

namespace CategoryTheory.Functor

open StacksDraft.RightDerivedBoundedDimension

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- **Stacks 07K7.** Let `F : 𝒜 ⥤ ℬ` be a left exact functor of abelian categories, let `P` be
the class of objects `X` which are right acyclic for `F`, i.e. such that `X[0]` computes the right
derived functor of `K⁺(𝒜) ⥤ D⁺(ℬ)` in the sense of Stacks 05SX, and let
`RF⁺ : D⁺(𝒜) ⥤ D⁺(ℬ)` be a right derived functor of `F` on the bounded below derived category.
Assume that every object of `𝒜` is a subobject of an object of `P`, and that
`R ^ n F = H ^ n (RF⁺ (- [0])) = 0` for some `n : ℕ`. Then

1. the right derived functor `RF : D(𝒜) ⥤ D(ℬ)` exists,
2. every complex is the source of a quasi-isomorphism into a complex with terms in `P`,
3. every complex with terms in `P` computes `RF`, and
4. for every `E` in `D(𝒜)`, `H ^ i (RF (τ_{≤ a} E)) ⟶ H ^ i (RF E)` is an isomorphism for
   `i ≤ a`, `H ^ i (RF E) ⟶ H ^ i (RF (τ_{≥ b - n + 1} E))` is an isomorphism for `i ≥ b`,
   and `RF` shifts the range of degrees in which `E` lives by at most `n - 1` on the right.

Right acyclicity is the source's notion (Stacks 0157(3) with 05SX); invertibility of the unit of
`RF⁺` at `X[0]` would be a weaker condition for a non-pointwise Kan extension (see the module documentation). -/
@[stacks 07K7,
  sga "4½ Etat_0 3.1.9" "(2) right, σ=F-acyclics",
  sga "4½ Etat_0 4.2.3.2" "right case: Rf on D(A)"]
public theorem hasRightDerivedFunctor_of_isZero_rightDerived
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (RF' : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (α' : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ RF')
    [RF'.IsRightDerivedFunctor α' (HomotopyCategory.Plus.quasiIso A)]
    (P : ObjectProperty A)
    (hP : ∀ X : A, P X ↔ (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso A) ((HomotopyCategory.Plus.singleFunctor A 0).obj X))
    (hmono : ∀ X : A, ∃ (Y : A) (i : X ⟶ Y) (_ : Mono i), P Y)
    (n : ℕ) (hn : ∀ X : A, IsZero ((DerivedCategory.Plus.homologyFunctor B n).obj
      (RF'.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      (∀ K : CochainComplex A ℤ, ∃ (L : CochainComplex A ℤ) (f : K ⟶ L) (_ : QuasiIso f),
        ∀ i : ℤ, P (L.X i)) ∧
      ∀ (RF : DerivedCategory A ⥤ DerivedCategory B)
        (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ RF)
        [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))],
        (∀ L : CochainComplex A ℤ, (∀ i : ℤ, P (L.X i)) →
            IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L))) ∧
          ∀ E : DerivedCategory A,
            (∀ a i : ℤ, i ≤ a → IsIso ((DerivedCategory.homologyFunctor B i).map
                (RF.map ((TStructure.t.truncLEι a).app E)))) ∧
              (∀ b i : ℤ, b ≤ i → IsIso ((DerivedCategory.homologyFunctor B i).map
                (RF.map ((TStructure.t.truncGEπ (b - (n : ℤ) + 1)).app E)))) ∧
                (∀ a : ℤ, E.IsGE a → (RF.obj E).IsGE a) ∧
                  ∀ b : ℤ, E.IsLE b → (RF.obj E).IsLE (b + (n : ℤ) - 1) := by
  obtain _ | N := n
  · have hu := iff_isIso_unit F P hP hmono RF' α'
    have hF : ∀ X, IsZero (F.obj X) := isZero_obj_of_isZero_homology_zero F RF' α'
      (fun X ↦ (hmono X).imp fun Y ⟨i, hi, hY⟩ ↦ ⟨i, hi, (hu Y).1 hY⟩) hn
    have hG (K : HomotopyCategory.Plus A) :
        IsZero ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj K) := by
      apply IsZero.of_full_of_faithful_of_isZero DerivedCategory.Plus.ι
      exact DerivedCategory.Qh.map_isZero (isZero_mapHomotopyCategory_obj_of_isZero F hF K.obj)
    have := (isIso_and_isZero_of_isRightDerivedFunctor_of_isZero hG
      (W := HomotopyCategory.Plus.quasiIso A) DerivedCategory.Plus.Qh RF' α').1
    exact conclusion_of_isZero F P (fun X ↦ (hu X).2 inferInstance) hF
  · exact conclusion_of_pos F P hP hmono RF' α' N hn

end CategoryTheory.Functor

end
