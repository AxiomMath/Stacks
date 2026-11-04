module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.StructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TwistAcyclicRange

/-!
# The trace isomorphism `Rⁿ f_* 𝒪(-n-1) ≅ 𝒪_S`

Let `S` be a scheme, let `n = m + 1 ≥ 1` and let `f : ℙⁿ_S ⟶ S` be the structure morphism. The
Koszul complex of the coordinates at the dualizing twist,

`0 ⟶ 𝒪(-n-1) ⟶ 𝒪(-n)^{⊕ binom(n+1,1)} ⟶ ⋯ ⟶ 𝒪(-1)^{⊕ (n+1)} ⟶ 𝒪 ⟶ 0`,

is acyclic over every base, and all of its **intermediate** terms are direct sums of twists
`𝒪(d)` with `-n ≤ d ≤ -1`, which have no higher direct image at all. Splicing the complex into the
short exact sequences of its cycles and shifting dimensions `n` times across those intermediate
terms therefore gives

`Rⁿ f_* 𝒪(-n-1) ≅ R ⁿ⁻¹ f_* Z² ≅ ⋯ ≅ R⁰ f_* 𝒪 = 𝒪_S`,

the last identification being `f_* 𝒪_{ℙⁿ_S} = 𝒪_S` of
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.pushZeroTwistIso`. That composite is
the **trace**: it is the degree-`n` row of the display of [Stacks, Tag 01XW] at the twist
`d = -n-1`, where the right-hand side `Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_0, 𝒪_S)` is `𝒪_S`.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `koszulDualizing`: the Koszul complex of the coordinates on `ℙⁿ_S` at the twist `-n-1`.
* `shiftChain`: the chain of dimension shifts across its intermediate terms.
* `trace`: **`Rⁿ f_* 𝒪(-n-1) ≅ 𝒪_S`.**

## Main results

* `isZero_push_koszulDualizing_X`: the intermediate terms of the complex have no higher direct
  image.
* `uniqueKoszulIndexTop`: the only `(n+1)`-element set of coordinates is the whole one, so the
  complex ends in a single twist.

## Implementation notes

The chain of dimension shifts is `shiftChain`, a recursion on the number of shifts carrying the
degree of the derived functor and the degree of the cycles as parameters linked by equations, so
that no transport along an associativity of degrees occurs inside the recursion.

The two ends of the complex are read off its cycles: the cycles in degree `1` are the whole of
the degree-zero term, because the cycles in degree `0` vanish and the complex is exact in degree
`1`; and the cycles in the top degree `n+1` are the whole of that term, because the differential
out of it is zero. The terms in the degrees `0` and `n+1` are direct sums over a one-element index
set, hence single twists, by `CategoryTheory.Limits.biproductUniqueIso`.

`CategoryTheory.HasDerivedCategory.standard` is installed as a local instance at priority `2000`,
as in the modules whose vanishing statements are used here.

No `stacks` attribute is attached: what is below is one entry of one row of [Stacks, Tag 01XW],
at a single twist.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

open Stacks.AlgebraicGeometry.ProjKoszulComplex (koszulFamily koszulIndex)
open Stacks.AlgebraicGeometry.ProjKoszulOverBase (koszulOver)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

variable (m : ℕ) (S : Scheme.{u})

/-- **The only `(n+1)`-element set of coordinates on `ℙⁿ` is the whole one.** -/
instance uniqueKoszulIndexTop (n : ℕ) : Unique (koszulIndex (n + 1) ((n : ℤ) + 1)) where
  default := ⟨Finset.univ, by simp⟩
  uniq a := Subtype.ext (Finset.eq_univ_of_card _ (by
    have := a.2
    simp only [Fintype.card_fin]
    omega))

/-- **The Koszul complex of the coordinates on `ℙⁿ_S` at the dualizing twist `-n-1`.** -/
abbrev koszulDualizing : CochainComplex (projectiveSpaceOver (m + 1) S).Modules ℤ :=
  koszulOver (m + 1) S (-((m + 1 : ℕ) : ℤ) - 1)

/-- A twist in the band `-n ≤ d ≤ -1` has no higher direct image, in Mathlib's `ℕ`-indexing. -/
theorem isZero_push_twistOver_of_acyclic (q : ℕ) {d : ℤ} (hd₁ : -((m + 1 : ℕ) : ℤ) ≤ d)
    (hd₂ : d < 0) : IsZero ((push m S q).obj (twistOver (m + 1) S d)) :=
  IsZero.of_iso (isZero_rightDerivedPlus_pushforward_twistOver_of_acyclic m S hd₁ hd₂ (q : ℤ))
    ((Stacks.DerivedIndexing.rightDerivedIso
      (Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)) q).app _)

/-- **An intermediate term of the Koszul complex at the dualizing twist has no higher direct
image**: it is a direct sum of copies of `𝒪(-n-1+i)` with `1 ≤ i ≤ n`, a twist in the band
`-n ≤ d ≤ -1`. -/
theorem isZero_push_koszulDualizing_X (q : ℕ) (i : ℤ) (h1 : 1 ≤ i) (h2 : i ≤ ((m + 1 : ℕ) : ℤ)) :
    IsZero ((push m S q).obj ((koszulDualizing m S).X i)) :=
  Functor.isZero_obj_biproduct (pullPush m S q)
    (koszulFamily (ULift.{u} ℤ) (m + 1) (-((m + 1 : ℕ) : ℤ) - 1) i)
    fun _ => isZero_push_twistOver_of_acyclic m S q (by omega) (by omega)

/-- **The chain of dimension shifts along the Koszul complex at the dualizing twist**: `k`
successive shifts across the intermediate terms carry `Rᵠ f_* Z ᵏ⁺¹` onto `R ᵠ⁺ᵏ f_* Z¹`. The
degrees are carried as parameters linked by equations so that the recursion needs no transport. -/
def shiftChain (k : ℕ) :
    ∀ (_ : k ≤ m + 1) (q r : ℕ) (i : ℤ), q + k = r → (k : ℤ) + 1 = i →
      ((push m S q).obj ((koszulDualizing m S).cycles i) ≅
        (push m S r).obj ((koszulDualizing m S).cycles 1)) := by
  induction k with
  | zero =>
    intro _ q r i hqr hi
    obtain rfl : q = r := by omega
    obtain rfl : i = 1 := by push_cast at hi; omega
    exact Iso.refl _
  | succ k ih =>
    intro hk q r i hqr hi
    have hrel : (ComplexShape.up ℤ).Rel ((k : ℤ) + 1) i := by
      change (k : ℤ) + 1 + 1 = i
      push_cast at hi
      omega
    refine HigherDirectImage.rightDerivedShiftIso (projectiveSpaceOver (m + 1) S ↘ S)
      ((koszulDualizing m S).cyclesShortComplex_shortExact hrel
        (ProjKoszulOverBase.acyclic_koszulOver (m + 1) S _ i)) q ?_ ?_ ≪≫
      ih (by omega) (q + 1) r ((k : ℤ) + 1) (by omega) rfl
    · exact isZero_push_koszulDualizing_X m S q ((k : ℤ) + 1) (by omega) (by push_cast; omega)
    · exact isZero_push_koszulDualizing_X m S (q + 1) ((k : ℤ) + 1) (by omega)
        (by push_cast; omega)

/-- **The cycles of the Koszul complex in degree `0` vanish**: they are a quotient of the term in
degree `-1`, which is zero. -/
theorem isZero_cycles_zero : IsZero ((koszulDualizing m S).cycles 0) := by
  have hS := (koszulDualizing m S).cyclesShortComplex_shortExact
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by change (-1 : ℤ) + 1 = 0; ring)
    (ProjKoszulOverBase.acyclic_koszulOver (m + 1) S _ 0)
  have he : Epi ((koszulDualizing m S).toCycles (-1) 0) := hS.epi_g
  exact IsZero.of_epi ((koszulDualizing m S).toCycles (-1) 0)
    (ProjKoszulOverBase.isZero_koszulOver_X (m + 1) S _ (-1) (Or.inl (by norm_num)))

/-- **The degree-zero term of the Koszul complex is its cycles in degree `1`**: the complex is
exact in degree `1` and its cycles in degree `0` vanish. -/
def cyclesOneIso : (koszulDualizing m S).X 0 ≅ (koszulDualizing m S).cycles 1 := by
  have hS := (koszulDualizing m S).cyclesShortComplex_shortExact
    (show (ComplexShape.up ℤ).Rel 0 1 from by change (0 : ℤ) + 1 = 1; ring)
    (ProjKoszulOverBase.acyclic_koszulOver (m + 1) S _ 1)
  haveI hm : Mono ((koszulDualizing m S).toCycles 0 1) :=
    hS.exact.mono_g ((isZero_cycles_zero m S).eq_of_src _ _)
  haveI he : Epi ((koszulDualizing m S).toCycles 0 1) := hS.epi_g
  haveI : IsIso ((koszulDualizing m S).toCycles 0 1) :=
    isIso_of_mono_of_epi ((koszulDualizing m S).toCycles 0 1)
  exact asIso ((koszulDualizing m S).toCycles 0 1)

/-- **The cycles of the Koszul complex in its top degree `n+1` are the whole term there**: the
differential out of that degree is zero, the next term vanishing. -/
def cyclesTopIso :
    (koszulDualizing m S).cycles (((m + 1 : ℕ) : ℤ) + 1) ≅
      (koszulDualizing m S).X (((m + 1 : ℕ) : ℤ) + 1) :=
  (koszulDualizing m S).iCyclesIso (((m + 1 : ℕ) : ℤ) + 1) (((m + 1 : ℕ) : ℤ) + 2)
    ((ComplexShape.up ℤ).next_eq' (by
      change ((m + 1 : ℕ) : ℤ) + 1 + 1 = ((m + 1 : ℕ) : ℤ) + 2; ring))
    ((ProjKoszulOverBase.isZero_koszulOver_X (m + 1) S _ (((m + 1 : ℕ) : ℤ) + 2)
      (Or.inr (by push_cast; omega))).eq_of_tgt _ _)

/-- The family of summands of the degree-`i` term of the Koszul complex, typed as a family of
modules on the integral model as a scheme. `CategoryTheory.Limits.HasFiniteBiproducts` is an
instance at that spelling of the category and not at the spelling
`CategoryTheory.SheafOfModules` over
`Stacks.AlgebraicGeometry.ProjTrivialization.projRingSheaf` that
`Stacks.AlgebraicGeometry.ProjKoszulComplex.koszulFamily` carries; the two are definitionally
equal. -/
abbrev koszulFamilyOver (a i : ℤ) :
    koszulIndex (m + 1 + 1) i →
      (AlgebraicGeometry.Proj (ProjPolyChart.polyGrading (ULift.{u} ℤ) (m + 1))).Modules :=
  koszulFamily (ULift.{u} ℤ) (m + 1) a i

/-- **A term of the Koszul complex indexed by a one-element set of coordinates is a single
twist**, read through the higher direct image. -/
def pushKoszulXUniqueIso (q : ℕ) (a : ℤ) (i : ℤ) [Unique (koszulIndex (m + 1 + 1) i)] :
    (push m S q).obj ((koszulOver (m + 1) S a).X i) ≅
      (push m S q).obj (twistOver (m + 1) S (a + i)) :=
  Functor.mapBiproduct (pullPush m S q) (koszulFamilyOver m a i) ≪≫ biproductUniqueIso _

/-- **The trace isomorphism `Rⁿ f_* 𝒪(-n-1) ≅ 𝒪_S`**, for the structure morphism
`f : ℙⁿ_S ⟶ S` over an arbitrary scheme `S` and for `n = m + 1 ≥ 1`.

The Koszul complex of the coordinates at the twist `-n-1` has `𝒪(-n-1)` in degree zero, direct
sums of twists in the band `-n ≤ d ≤ -1` in the degrees `1, …, n` and `𝒪` in degree `n+1`. Its
cycles in degree `1` are the whole of its degree-zero term, its cycles in degree `n+1` are the
whole of its top term, and the `n` dimension shifts across the intermediate terms join the two
ends. -/
def trace :
    (push m S (m + 1)).obj (twistOver (m + 1) S (-((m + 1 : ℕ) : ℤ) - 1)) ≅
      Scheme.unitModule S :=
  (push m S (m + 1)).mapIso (eqToIso (congrArg (twistOver (m + 1) S)
      (show -((m + 1 : ℕ) : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) - 1 + 0 from by ring))) ≪≫
    (pushKoszulXUniqueIso m S (m + 1) (-((m + 1 : ℕ) : ℤ) - 1) 0).symm ≪≫
    (push m S (m + 1)).mapIso (cyclesOneIso m S) ≪≫
    (shiftChain m S (m + 1) le_rfl 0 (m + 1) (((m + 1 : ℕ) : ℤ) + 1) (by omega) rfl).symm ≪≫
    (push m S 0).mapIso (cyclesTopIso m S) ≪≫
    pushKoszulXUniqueIso m S 0 (-((m + 1 : ℕ) : ℤ) - 1) (((m + 1 : ℕ) : ℤ) + 1) ≪≫
    (push m S 0).mapIso (eqToIso (congrArg (twistOver (m + 1) S)
      (show -((m + 1 : ℕ) : ℤ) - 1 + (((m + 1 : ℕ) : ℤ) + 1) = 0 from by ring))) ≪≫
    pushZeroTwistIso m S

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
