module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.PerfectHomVanishingWindowGeneral
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulHighDegreeOrthogonality
import StacksCore.Tactic.StacksAttribute

/-!
# Detecting boundedness of a quasi-coherent complex against a perfect complex

Let `X` be a quasi-compact and quasi-separated scheme, let `P` be a perfect object of `D(𝒪_X)`,
let `E` be an object of `D_QCoh(𝒪_X)` and let `a` be an integer. [Stacks, Tag 0GEL] says that

1. `Hom_{D(𝒪_X)}(P⟦-i⟧, E) = 0` for `i ≫ 0`, and
2. `Hom_{D(𝒪_X)}(P⟦-i⟧, τ_{≥a}E) = 0` for `i ≫ 0`

are equivalent. That is what
`Stacks.DerivedQCoh.eventually_subsingleton_hom_iff_truncGE_of_isPerfect` below states, at the
source's own hypotheses.

## Main results

* `Stacks.DerivedQCoh.subsingleton_hom_negShift_iff`: morphisms out of a negative shift are
  morphisms into the opposite positive shift, since `⟦-i⟧` is left adjoint to `⟦i⟧`.
* `Stacks.DerivedQCoh.exists_threshold_subsingleton_hom_negShift_of_isPerfect`: for `P` perfect
  there is a single integer `c`, depending only on `X` and `P`, with the property that
  `Hom(P⟦-i⟧, M) = 0` for every `M` in `D_QCoh(𝒪_X)` with no cohomology above `b` and every
  `i ≥ b + c`.
* `Stacks.DerivedQCoh.eventually_subsingleton_hom_iff_truncGE_of_isPerfect`:
  [Stacks, Tag 0GEL].

## Implementation notes

**The argument.** Both directions are the truncation triangle
`τ_{≤a-1}E ⟶ E ⟶ τ_{≥a}E ⟶ (τ_{≤a-1}E)⟦1⟧` together with the vanishing of
`Hom(P⟦-i⟧, τ_{≤a-1}E)` and of `Hom(P⟦-i⟧, (τ_{≤a-1}E)⟦1⟧)` for large `i`; those two transports
are `Stacks.DerivedTruncation.subsingleton_hom_of_subsingleton_hom_truncGE` and
`Stacks.DerivedTruncation.subsingleton_hom_truncGE_of_subsingleton_hom`. Each of the two targets
lies in `D_QCoh(𝒪_X)` — truncation and shift preserve quasi-coherence of the cohomology sheaves —
and each is bounded above, by `a - 1` and by `a - 2`, so a single threshold
`i ≥ a - 1 + c` serves both.

The vanishing for a target bounded above is
`exists_threshold_subsingleton_hom_negShift_of_isPerfect`, and that is
[Stacks, Tag 09M4] part (1),
`Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_general`, read through the shift
adjunction: part (1) produces a window `[a₀, b₀]` such that an object of `D_QCoh(𝒪_X)` with no
cohomology in the window receives no nonzero morphism from `P`, and if `M` has no cohomology above
`b` then `M⟦i⟧` has none above `b - i`, hence none in the window as soon as `i ≥ b + 1 - a₀`.
So `c = 1 - a₀`.

Both the window and the threshold depend on `P` and on `X` alone, which is what makes the
equivalence above an equivalence of two eventual statements rather than a statement about a
single degree.

**Derived global sections.** [Stacks, Tag 09M4] is stated for an arbitrary total right derived
functor of `Stacks.Cohomology.sectionsFunctor X ⊤` on the unbounded derived category, presented
as a functor together with its structure morphism. `Stacks.DerivedQCoh.schemeDerivedSections` and
`Stacks.DerivedQCoh.schemeDerivedSectionsUnit` below are the canonical such pair, Mathlib's
`CategoryTheory.Functor.totalRightDerived` along `DerivedCategory.Qh`: it exists because
`X.Modules` is a Grothendieck abelian category, so every cochain complex of `𝒪_X`-modules admits
a K-injective resolution and [Stacks, Tag 070K] applies.

**The derived category is the standard model.** As in
`StacksFrontier.AlgebraicGeometry.DerivedQCoh.PerfectHomVanishingWindow`, which the proof calls,
`CategoryTheory.HasDerivedCategory.standard` is a local instance here, so `DerivedCategory
X.Modules` is the localization at the universe of `X.Modules` itself. The two abstract transports
quoted above are universe-polymorphic in the derived category, and only this file's statements are
pinned.

## References

* [Stacks Project, Tag 0GEL](https://stacks.math.columbia.edu/tag/0GEL)
* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology (sectionsFunctor)

universe u

namespace Stacks.DerivedQCoh

/-! ### Morphisms out of a negative shift -/

/-- **Hom-vanishing out of a negative shift, read as Hom-vanishing into a positive shift.**
Every morphism `P⟦-i⟧ ⟶ M` is zero exactly when every morphism `P ⟶ M⟦i⟧` is, because `⟦-i⟧`
is left adjoint to `⟦i⟧`. -/
theorem subsingleton_hom_negShift_iff {C : Type*} [Category* C] [HasShift C ℤ] (P M : C)
    (i : ℤ) : Subsingleton (P⟦-i⟧ ⟶ M) ↔ Subsingleton (P ⟶ M⟦i⟧) :=
  ((shiftEquiv' C (-i) i (by omega)).toAdjunction.homEquiv P M).subsingleton_congr

/-! ### Derived global sections as a total right derived functor -/

section Scheme

attribute [local instance 100000] HasDerivedCategory.standard

variable (X : Scheme.{u})

/-- **Derived global sections of a scheme on the unbounded derived category.** The total right
derived functor of `Stacks.Cohomology.sectionsFunctor X ⊤` along `DerivedCategory.Qh`. It exists
because `X.Modules` is a Grothendieck abelian category: every cochain complex of `𝒪_X`-modules
has a K-injective resolution, and [Stacks, Tag 070K] turns that into existence of the right
derived functor on the whole of `D(𝒪_X)`. -/
abbrev schemeDerivedSections :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, ⊤)) :=
  ((sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The structure morphism of `Stacks.DerivedQCoh.schemeDerivedSections`, comparing the global
sections of a complex with the derived global sections of its image in `D(𝒪_X)`. -/
abbrev schemeDerivedSectionsUnit :
    (sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ schemeDerivedSections X :=
  ((sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-! ### A uniform threshold for Hom-vanishing into a complex bounded above -/

/-- The cohomology sheaves of a shift of a quasi-coherent complex are quasi-coherent. -/
private theorem isQuasicoherent_homology_shift (M : DerivedCategory X.Modules)
    (hM : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj M).IsQuasicoherent)
    (i j : ℤ) : ((DerivedCategory.homologyFunctor X.Modules j).obj (M⟦i⟧)).IsQuasicoherent :=
  (AlgebraicGeometry.isQuasicoherentModules X).prop_of_iso
    (((DerivedCategory.homologyFunctor X.Modules 0).shiftIso i j (i + j) rfl).app M).symm
    (hM (i + j))

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-! ### [Stacks, Tag 09M4] -/

/-- **[Stacks, Tag 09M4], part (1).** Let `X` be a quasi-compact and quasi-separated scheme and
let `K` be a perfect object of `D(𝒪_X)`. Then there are integers `a ≤ b` such that every
`L ∈ D_QCoh(𝒪_X)` whose cohomology sheaves vanish in the degrees `a, …, b` admits no nonzero
morphism `K ⟶ L`.

This is `Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_general` at the derived
global sections `Stacks.DerivedQCoh.schemeDerivedSections X`, which exist for every scheme; the
statement mentions no derived global sections functor and carries no hypothesis beyond the
source's. -/
@[stacks 09M4 "part (1)"]
theorem exists_window_subsingleton_hom_of_isPerfect_qcqs (K : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) :
    ∃ a b : ℤ, a ≤ b ∧
      ∀ L : DerivedCategory X.Modules,
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsQuasicoherent) →
        (∀ i : ℤ, a ≤ i → i ≤ b → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj L)) →
        Subsingleton (K ⟶ L) :=
  exists_window_subsingleton_hom_of_isPerfect_general X (schemeDerivedSections X)
    (schemeDerivedSectionsUnit X) K hK

/-- **[Stacks, Tag 09M4], part (2).** Let `X` be a quasi-compact and quasi-separated scheme, let
`K` be a perfect object of `D(𝒪_X)` and let `L` be a bounded object of `D_QCoh(𝒪_X)`. Then
`Ext^n_{D(𝒪_X)}(K, L) = Hom_{D(𝒪_X)}(K, L⟦n⟧)` vanishes for all but finitely many `n`.

This is `Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect_general` at the
derived global sections `Stacks.DerivedQCoh.schemeDerivedSections X`. -/
@[stacks 09M4 "part (2)"]
theorem finite_setOf_not_subsingleton_hom_shift_of_isPerfect_qcqs (K : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (L : DerivedCategory X.Modules)
    (hLqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsQuasicoherent)
    (c d : ℤ) (hLGE : L.IsGE c) (hLLE : L.IsLE d) :
    {n : ℤ | ¬ Subsingleton (K ⟶ L⟦n⟧)}.Finite :=
  finite_setOf_not_subsingleton_hom_shift_of_isPerfect_general X (schemeDerivedSections X)
    (schemeDerivedSectionsUnit X) K hK L hLqc c d hLGE hLLE

/-- **One threshold for every target bounded above.** Let `X` be a quasi-compact and
quasi-separated scheme and let `P` be a perfect object of `D(𝒪_X)`. There is an integer `c`,
depending only on `X` and `P`, such that `Hom_{D(𝒪_X)}(P⟦-i⟧, M) = 0` whenever `M` lies in
`D_QCoh(𝒪_X)`, has no cohomology above `b`, and `i ≥ b + c`.

This is [Stacks, Tag 09M4] part (1) read through the shift adjunction: that part gives a window
`[a₀, b₀]` of degrees such that an object of `D_QCoh(𝒪_X)` whose cohomology sheaves vanish
throughout the window admits no nonzero morphism from `P`, and the shift `M⟦i⟧` has no cohomology
above `b - i`, hence none in the window once `i ≥ b + 1 - a₀`. So `c = 1 - a₀` works. -/
theorem exists_threshold_subsingleton_hom_negShift_of_isPerfect
    (P : DerivedCategory X.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P) :
    ∃ c : ℤ, ∀ M : DerivedCategory X.Modules,
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj M).IsQuasicoherent) →
      ∀ b : ℤ, M.IsLE b → ∀ i : ℤ, b + c ≤ i → Subsingleton (P⟦-i⟧ ⟶ M) := by
  obtain ⟨a₀, b₀, -, hvan⟩ :=
    exists_window_subsingleton_hom_of_isPerfect_general X (schemeDerivedSections X)
      (schemeDerivedSectionsUnit X) P hP
  refine ⟨1 - a₀, fun M hMqc b hM i hi => ?_⟩
  refine (subsingleton_hom_negShift_iff P M i).mpr
    (hvan (M⟦i⟧) (isQuasicoherent_homology_shift X M hMqc i) (fun j hj _ => ?_))
  · have : (M⟦i⟧).IsLE (b - i) :=
      DerivedCategory.TStructure.t.isLE_shift M b i (b - i) (by omega)
    exact DerivedCategory.isZero_of_isLE _ (b - i) j (by omega)

/-! ### [Stacks, Tag 0GEL] -/

/-- **[Stacks, Tag 0GEL].** Let `X` be a quasi-compact and quasi-separated scheme, let `P` be a
perfect object of `D(𝒪_X)`, let `E` be an object of `D_QCoh(𝒪_X)` and let `a` be an integer. Then

1. `Hom_{D(𝒪_X)}(P⟦-i⟧, E) = 0` for `i ≫ 0`

if and only if

2. `Hom_{D(𝒪_X)}(P⟦-i⟧, τ_{≥a}E) = 0` for `i ≫ 0`,

where `τ_{≥a}` is the canonical truncation of `D(𝒪_X)` and vanishing of a Hom-group is
subsingletonness of the morphism type, the derived category being additive.

Both implications are the truncation triangle
`τ_{≤a-1}E ⟶ E ⟶ τ_{≥a}E ⟶ (τ_{≤a-1}E)⟦1⟧`: a morphism `P⟦-i⟧ ⟶ E` which dies in `τ_{≥a}E`
factors through `τ_{≤a-1}E`, and a morphism `P⟦-i⟧ ⟶ τ_{≥a}E` which dies in `(τ_{≤a-1}E)⟦1⟧`
factors through `E`. So each direction needs only that `τ_{≤a-1}E` and `(τ_{≤a-1}E)⟦1⟧` receive
no nonzero morphism from `P⟦-i⟧` for `i` large; both of them lie in `D_QCoh(𝒪_X)` and are bounded
above, by `a - 1` and `a - 2`, and
`Stacks.DerivedQCoh.exists_threshold_subsingleton_hom_negShift_of_isPerfect` kills both from
`i ≥ a - 1 + c` on, with `c` the threshold that perfectness of `P` supplies through
[Stacks, Tag 09M4]. -/
@[stacks 0GEL]
theorem eventually_subsingleton_hom_iff_truncGE_of_isPerfect
    (P E : DerivedCategory X.Modules)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P)
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (a : ℤ) :
    (∃ N : ℤ, ∀ i : ℤ, N ≤ i → Subsingleton (P⟦-i⟧ ⟶ E)) ↔
      ∃ N : ℤ, ∀ i : ℤ, N ≤ i →
        Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncGE a).obj E) := by
  obtain ⟨c, hc⟩ := exists_threshold_subsingleton_hom_negShift_of_isPerfect X P hP
  have hAqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj
      ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E)).IsQuasicoherent := fun j =>
    DerivedCategory.prop_homologyFunctor_truncLE_obj
      (AlgebraicGeometry.isQuasicoherentModules X) E (fun k => hE k) (a - 1) j
  have hiff : ∀ i : ℤ, a - 1 + c ≤ i →
      (Subsingleton (P⟦-i⟧ ⟶ E) ↔
        Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncGE a).obj E)) := by
    intro i hi
    have hlow : Subsingleton (P⟦-i⟧ ⟶ (DerivedCategory.TStructure.t.truncLE (a - 1)).obj E) :=
      hc _ hAqc (a - 1) inferInstance i (by omega)
    have hlow' : Subsingleton
        (P⟦-i⟧ ⟶ ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj E)⟦(1 : ℤ)⟧) :=
      hc _ (isQuasicoherent_homology_shift X _ hAqc 1) (a - 2)
        (DerivedCategory.TStructure.t.isLE_shift _ (a - 1) 1 (a - 2) (by omega)) i (by omega)
    exact ⟨fun h => Stacks.DerivedTruncation.subsingleton_hom_truncGE_of_subsingleton_hom a i
        hlow' h,
      fun h => Stacks.DerivedTruncation.subsingleton_hom_of_subsingleton_hom_truncGE a i hlow h⟩
  exact ⟨fun ⟨N, hN⟩ => ⟨max N (a - 1 + c), fun i hi =>
      (hiff i (le_of_max_le_right hi)).mp (hN i (le_of_max_le_left hi))⟩,
    fun ⟨N, hN⟩ => ⟨max N (a - 1 + c), fun i hi =>
      (hiff i (le_of_max_le_right hi)).mpr (hN i (le_of_max_le_left hi))⟩⟩

end Scheme

end Stacks.DerivedQCoh

end
