module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectHomVanishingWindow
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulHighDegreeOrthogonality
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
import StacksCore.Tactic.StacksAttribute

/-!
# Detecting boundedness: truncating a quasi-coherent complex on an algebraic space from below

Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S`, let
`P` be a perfect object of `D(𝒪_X)`, let `E` be an object of `D_QCoh(𝒪_X)` and let `a` be an
integer.  [Stacks, Tag 0GFF] says that

1. `Hom_{D(𝒪_X)}(P⟦-i⟧, E) = 0` for `i ≫ 0`, and
2. `Hom_{D(𝒪_X)}(P⟦-i⟧, τ_{≥a}E) = 0` for `i ≫ 0`

are equivalent.  That is
`AlgebraicGeometry.Space.eventually_subsingleton_hom_iff_truncGE_of_isPerfect` below, at the
source's own hypotheses.

## Main results

* `AlgebraicGeometry.Space.exists_threshold_subsingleton_hom_negShift_of_isPerfect`: for `P`
  perfect there is a single integer `c`, depending only on `X` and `P`, such that
  `Hom(P⟦-i⟧, M) = 0` for every `M` in `D_QCoh(𝒪_X)` with no cohomology above `b` and every
  `i ≥ b + c`.
* `AlgebraicGeometry.Space.eventually_subsingleton_hom_iff_truncGE_of_isPerfect`:
  [Stacks, Tag 0GFF].

## Implementation notes

**The argument** is the source's.  Both directions are the truncation triangle
`τ_{≤a-1}E ⟶ E ⟶ τ_{≥a}E ⟶ (τ_{≤a-1}E)⟦1⟧` together with the vanishing of
`Hom(P⟦-i⟧, τ_{≤a-1}E)` and of `Hom(P⟦-i⟧, (τ_{≤a-1}E)⟦1⟧)` for large `i`; the two transports
across the triangle are `Stacks.DerivedTruncation.subsingleton_hom_of_subsingleton_hom_truncGE`
and `Stacks.DerivedTruncation.subsingleton_hom_truncGE_of_subsingleton_hom`, which hold in the
derived category of any abelian category.  Each of the two targets lies in `D_QCoh(𝒪_X)` —
truncation and shift preserve quasi-coherence of the cohomology sheaves, the quasi-coherent
sheaves being closed under isomorphism and containing zero — and each is bounded above, by
`a - 1` and by `a - 2`, so a single threshold `i ≥ a - 1 + c` serves both.

**What perfectness supplies** is the threshold `c`, and that is [Stacks, Tag 09MB] part (1),
`AlgebraicGeometry.Space.exists_window_subsingleton_hom_of_isPerfect`, read through the shift
adjunction `⟦-i⟧ ⊣ ⟦i⟧`: part (1) produces a window `[a₀, b₀]` of degrees such that an object of
`D_QCoh(𝒪_X)` whose cohomology sheaves vanish throughout the window receives no nonzero morphism
from `P`, and if `M` has no cohomology above `b` then `M⟦i⟧` has none above `b - i`, hence none in
the window as soon as `i ≥ b + 1 - a₀`.  So `c = 1 - a₀`.  Both the window and the threshold
depend on `X` and `P` alone, which is what makes the equivalence one of two eventual statements
rather than a statement about a single degree.

**Why the abstract form of the sibling tag is not instantiated.**  The scheme-level
[Stacks, Tag 0GEL] has an abstract shape in this repository,
`Stacks.DerivedTruncation.eventually_subsingleton_hom_iff_truncGE`, whose hypothesis `hwindow`
asks for the window at *every* object of the derived category.  That is strictly stronger than
anything perfectness gives here: [Stacks, Tag 09MB] bounds `Hom(P, −)` only on objects with
quasi-coherent cohomology, and a general `𝒪_X`-module complex is not of that kind.  So the
abstract lemma cannot be instantiated, and the two triangle transports are used directly, exactly
as the scheme-level `Stacks.DerivedQCoh.eventually_subsingleton_hom_iff_truncGE_of_isPerfect`
does with [Stacks, Tag 09M4] in place of [Stacks, Tag 09MB].

**The objects.**  As in `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectHomVanishingWindow`:
`𝒪_X`-modules are the sheaves of modules on the small étale ringed site of `X`,
`AlgebraicGeometry.Space.Modules`, at the module universe of the structure rings; `P` is perfect
in the sense of [Stacks, Tag 08G5] on that ringed site; membership of `E` in `D_QCoh(𝒪_X)`
([Stacks, Tag 071X]) is quasi-coherence of every cohomology sheaf; quasi-separatedness is the
absolute notion `AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated` of [Stacks, Tag 03BS](3),
which is why the ambient big fppf site is required to contain the terminal scheme.  Vanishing of
a group of morphisms of `D(𝒪_X)` is `Subsingleton`, the category being preadditive, and
"for `i ≫ 0`" is `∃ N : ℤ, ∀ i : ℤ, N ≤ i → _`.  The model of `D(𝒪_X)` is an arbitrary
`[HasDerivedCategory.{w} _]`, as it is for [Stacks, Tag 09MB].

## References

* [Stacks Project, Tag 0GFF](https://stacks.math.columbia.edu/tag/0GFF)
* [Stacks Project, Tag 09MB](https://stacks.math.columbia.edu/tag/09MB)
* [Stacks Project, Tag 0GEL](https://stacks.math.columbia.edu/tag/0GEL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

variable (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- The shift of an object of `D_QCoh(𝒪_X)` again lies in `D_QCoh(𝒪_X)`. -/
private theorem isQuasicoherentOnSite_homology_shift
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (M : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hM : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).obj
      M).IsQuasicoherentOnSite) (n j : ℤ) :
    ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).obj
      (M⟦n⟧)).IsQuasicoherentOnSite :=
  (qcohModules B S hS ⟨X, hX⟩).prop_of_iso
    (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) 0).shiftIso n j (n + j)
      rfl).app M).symm (hM (n + j))

/-- **One threshold for every quasi-coherent target bounded above.**  Let `S` be a scheme, let `X`
be a quasi-compact and quasi-separated algebraic space over `S` and let `P` be a perfect object of
`D(𝒪_X)`.  There is an integer `c`, depending only on `X` and `P`, such that
`Hom_{D(𝒪_X)}(P⟦-i⟧, M) = 0` whenever `M` lies in `D_QCoh(𝒪_X)`, has no cohomology above `b`, and
`i ≥ b + c`.

This is [Stacks, Tag 09MB] part (1),
`AlgebraicGeometry.Space.exists_window_subsingleton_hom_of_isPerfect`, read through the shift
adjunction `⟦-i⟧ ⊣ ⟦i⟧`: that part gives a window `[a₀, b₀]` of degrees such that an object of
`D_QCoh(𝒪_X)` whose cohomology sheaves vanish throughout the window admits no nonzero morphism
from `P`, and the shift `M⟦i⟧` has no cohomology above `b - i`, hence none in the window once
`i ≥ b + 1 - a₀`.  So `c = 1 - a₀` works. -/
theorem exists_threshold_subsingleton_hom_negShift_of_isPerfect
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (P : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hP : (smallEtaleRingedSite B S hS X hX).IsPerfect P) :
    ∃ c : ℤ, ∀ M : DerivedCategory (Modules.{u, u} B S hS X hX),
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).obj
        M).IsQuasicoherentOnSite) →
      ∀ b : ℤ, M.IsLE b → ∀ i : ℤ, b + c ≤ i → Subsingleton (P⟦-i⟧ ⟶ M) := by
  obtain ⟨a₀, b₀, -, hvan⟩ :=
    exists_window_subsingleton_hom_of_isPerfect B S hS hZ X hX hqc hqs P hP
  refine ⟨1 - a₀, fun M hMqc b hM i hi => ?_⟩
  refine ((shiftEquiv' (DerivedCategory (Modules.{u, u} B S hS X hX)) (-i) i
      (by omega)).toAdjunction.homEquiv P M).subsingleton_congr.mpr
    (hvan (M⟦i⟧) (fun j => ?_) (fun j hj _ => ?_))
  · exact isQuasicoherentOnSite_homology_shift B S hS X hX M hMqc i j
  · have : (M⟦i⟧).IsLE (b - i) :=
      DerivedCategory.TStructure.t.isLE_shift M b i (b - i) (by omega)
    exact DerivedCategory.isZero_of_isLE _ (b - i) j (by omega)

/-- **[Stacks, Tag 0GFF].**  Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated
algebraic space over `S`, let `P` be a perfect object of `D(𝒪_X)`, let `E` be an object of
`D_QCoh(𝒪_X)` and let `a` be an integer.  Then

1. `Hom_{D(𝒪_X)}(P⟦-i⟧, E) = 0` for `i ≫ 0`

if and only if

2. `Hom_{D(𝒪_X)}(P⟦-i⟧, τ_{≥a}E) = 0` for `i ≫ 0`,

where `τ_{≥a}` is the canonical truncation of `D(𝒪_X)` and vanishing of a Hom-group is
subsingletonness of the morphism type, the derived category being additive.

Both implications are the truncation triangle
`τ_{≤a-1}E ⟶ E ⟶ τ_{≥a}E ⟶ (τ_{≤a-1}E)⟦1⟧`: a morphism `P⟦-i⟧ ⟶ E` which dies in `τ_{≥a}E`
factors through `τ_{≤a-1}E`, and a morphism `P⟦-i⟧ ⟶ τ_{≥a}E` which dies in `(τ_{≤a-1}E)⟦1⟧`
factors through `E`.  So each direction needs only that `τ_{≤a-1}E` and `(τ_{≤a-1}E)⟦1⟧` receive
no nonzero morphism from `P⟦-i⟧` for `i` large; both lie in `D_QCoh(𝒪_X)` and are bounded above,
by `a - 1` and `a - 2`, and
`AlgebraicGeometry.Space.exists_threshold_subsingleton_hom_negShift_of_isPerfect` kills both from
`i ≥ a - 1 + c` on, with `c` the threshold that perfectness of `P` supplies through
[Stacks, Tag 09MB]. -/
@[stacks 0GFF]
theorem eventually_subsingleton_hom_iff_truncGE_of_isPerfect
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS X hX)]
    (P E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hP : (smallEtaleRingedSite B S hS X hX).IsPerfect P)
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).obj
      E).IsQuasicoherentOnSite)
    (a : ℤ) :
    (∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (P⟦-i⟧ ⟶ E)) ↔
      ∃ N : ℤ, ∀ i : ℤ, N ≤ i →
        Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncGE a).obj E) := by
  obtain ⟨c, hc⟩ :=
    exists_threshold_subsingleton_hom_negShift_of_isPerfect B S hS hZ X hX hqc hqs P hP
  have hAqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X hX) j).obj
      ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E)).IsQuasicoherentOnSite := fun j =>
    Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj
      (qcohModules B S hS ⟨X, hX⟩) E (fun k => hE k) (a - 1) j
  have hiff : ∀ i : ℤ, a - 1 + c ≤ i →
      (Subsingleton (P⟦-i⟧ ⟶ E) ↔
        Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncGE a).obj E)) := by
    intro i hi
    have hlow : Subsingleton
        (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncLE (a - 1)).obj E) :=
      hc _ hAqc (a - 1) inferInstance i (by omega)
    have hlow' : Subsingleton
        (P⟦-i⟧ ⟶ ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E)⟦(1 : ℤ)⟧) :=
      hc _ (isQuasicoherentOnSite_homology_shift B S hS X hX _ hAqc 1) (a - 2)
        (DerivedCategory.TStructure.t.isLE_shift _ (a - 1) 1 (a - 2) (by omega)) i (by omega)
    exact ⟨fun h => Stacks.DerivedTruncation.subsingleton_hom_truncGE_of_subsingleton_hom a i
        hlow' h,
      fun h => Stacks.DerivedTruncation.subsingleton_hom_of_subsingleton_hom_truncGE a i hlow h⟩
  exact ⟨fun ⟨N, hN⟩ => ⟨max N (a - 1 + c), fun i hi =>
      (hiff i (le_of_max_le_right hi)).mp (hN i (le_of_max_le_left hi))⟩,
    fun ⟨N, hN⟩ => ⟨max N (a - 1 + c), fun i hi =>
      (hiff i (le_of_max_le_right hi)).mpr (hN i (le_of_max_le_left hi))⟩⟩

end AlgebraicGeometry.Space

end
