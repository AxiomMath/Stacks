module

public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksFrontier.Homology.CyclesShortComplex

/-!
# A cohomological δ-functor applied, in its top degree, to an acyclic complex

Let `F` be a cohomological δ-functor from `A` to `B` and let `K` be an acyclic cochain complex in
`A`, concentrated in nonnegative degrees, whose terms are **silent outside one degree** `n`:

`Fᵠ(Kⁱ) = 0` for every `i` and every `q ≠ n`.

Then the complex `Fⁿ(K)` obtained by applying `Fⁿ` degreewise is again **acyclic**. For `n = 0`
this is left exactness of `F⁰` along the complex; for `n ≥ 1` — the case proved here — it is the
standard dimension-shifting computation, run on the cycles `Zⁱ(K)` of the complex:

* `Fᵠ(Zⁱ) = 0` for `q > n`, by induction on `i` from below, since `Zⁱ` is a subobject of `Kⁱ` and
  the connecting morphism identifies `Fᵠ(Zⁱ)` with a subobject of `F ᵠ⁺¹(Z ⁱ⁻¹)`;
* `Fᵠ(Zⁱ) = 0` for `q < n`, by induction on `q` from `q = 0`, where it is left exactness of `F⁰`,
  the connecting morphism of the sequence `0 ⟶ Zⁱ ⟶ Kⁱ ⟶ Z ⁱ⁺¹ ⟶ 0` carrying `Fᵠ(Z ⁱ⁺¹)` onto
  `F ᵠ⁺¹(Zⁱ)`.

Those two vanishing ranges make `Fⁿ` carry each of the sequences `0 ⟶ Zⁱ ⟶ Kⁱ ⟶ Z ⁱ⁺¹ ⟶ 0` to a
short exact sequence, which is exactly the hypothesis of
`CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact`.

The intended reading: `A` is the modules on a scheme `X`, `B` the modules on a base `S`, `F` the
higher direct images along a morphism `X ⟶ S` and `K` a resolution whose terms have cohomology
only in the top degree `n`; the conclusion is that the degree-`n` higher direct images of the
terms of `K` form an exact sequence.

## Main results

* `CategoryTheory.DeltaFunctor.isZero_functor_cycles_of_gt`: `Fᵠ(Zⁱ(K)) = 0` above the top
  degree.
* `CategoryTheory.DeltaFunctor.isZero_functor_cycles_of_lt`: `Fᵠ(Zⁱ(K)) = 0` below the top
  degree.
* `CategoryTheory.DeltaFunctor.shortExact_map_cyclesShortComplex`: `Fⁿ` keeps the cycles
  sequences short exact.
* `CategoryTheory.DeltaFunctor.acyclic_mapHomologicalComplex_top`: **`Fⁿ(K)` is acyclic.**

## Implementation notes

Left exactness of `F⁰` is asked for as the hypothesis that `F⁰` preserves monomorphisms rather
than being derived from the axioms of a δ-functor: those give `Mono (F⁰ f)` only for the
monomorphism of a *short exact* sequence, and the inclusion of the cycles is presented as a
monomorphism and not as one end of a short exact sequence until the complex is known to be
exact in the degree below.

The induction producing the vanishing above the top degree runs over the indices `(j : ℕ) - 1`,
so that its base case is a degree where the complex itself vanishes; an arbitrary index `i ≥ -1`
is of that form, and an index below `-1` is handled by the same base case.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v v' u u'

namespace CategoryTheory.DeltaFunctor

variable {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B] [Abelian A] [Abelian B]
  (F : DeltaFunctor A B) (K : CochainComplex A ℤ) (p : ℕ)

variable (hK : K.Acyclic)
  (hz : ∀ (i : ℤ) (q : ℕ), q ≠ p + 1 → IsZero ((F.functor q).obj (K.X i)))
  (hGE : ∀ i : ℤ, i < 0 → IsZero (K.X i))
  (hmono : ∀ {X Y : A} (g : X ⟶ Y), Mono g → Mono ((F.functor 0).map g))

include hK hz hGE in
/-- The vanishing of `Fᵠ(Zⁱ(K))` above the top degree, by induction on `i` from `i = -1`. -/
private theorem isZero_functor_cycles_of_gt_aux (q : ℕ) (hq : p + 1 < q) (i : ℤ) :
    IsZero ((F.functor q).obj (K.cycles i)) := by
  have hneg : ∀ (i : ℤ), i < 0 → ∀ q : ℕ, IsZero ((F.functor q).obj (K.cycles i)) :=
    fun i hi q => Functor.map_isZero _ (IsZero.of_mono (K.iCycles i) (hGE i hi))
  rcases lt_or_ge i (-1) with hi | hi
  · exact hneg i (by omega) q
  · induction i, hi using Int.leInduction generalizing q with
    | base => exact hneg _ (by omega) q
    | succ i _ ih =>
      have hS := K.cyclesShortComplex_shortExact (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)
        (hK (i + 1))
      exact (F.exact_δ₁ hS q).isZero_X₂ ((hz _ q (by omega)).eq_of_src _ _)
        ((ih (q + 1) (by omega)).eq_of_tgt _ _)

include hK hz hGE in
/-- **`Fᵠ(Zⁱ(K)) = 0` above the top degree**, for the cycles of an acyclic complex concentrated
in nonnegative degrees whose terms are silent outside the degree `p + 1`. -/
theorem isZero_functor_cycles_of_gt (q : ℕ) (hq : p + 1 < q) (i : ℤ) :
    IsZero ((F.functor q).obj (K.cycles i)) :=
  isZero_functor_cycles_of_gt_aux F K p hK hz hGE q hq i

include hK hz hmono in
/-- **`Fᵠ(Zⁱ(K)) = 0` below the top degree.** The induction starts at `q = 0`, where the
statement is left exactness of `F⁰` applied to the inclusion of the cycles, and climbs by the
connecting morphism of the cycles sequence. -/
theorem isZero_functor_cycles_of_lt :
    ∀ (q : ℕ), q ≤ p → ∀ i : ℤ, IsZero ((F.functor q).obj (K.cycles i)) := by
  intro q
  induction q with
  | zero =>
    intro _ i
    have := hmono (K.iCycles i) inferInstance
    exact IsZero.of_mono ((F.functor 0).map (K.iCycles i)) (hz i 0 (by omega))
  | succ q ih =>
    intro hq i
    have hrel : (ComplexShape.up ℤ).Rel i (i + 1) := rfl
    have hS := K.cyclesShortComplex_shortExact hrel (hK (i + 1))
    exact (F.exact_δ₂ hS q).isZero_X₂ ((ih (by omega) (i + 1)).eq_of_src _ _)
      ((hz i (q + 1) (by omega)).eq_of_tgt _ _)

include hK hz hGE hmono in
/-- **`Fⁿ` keeps the cycles sequences of the complex short exact**, in the top degree
`n = p + 1`: the first map stays a monomorphism because `F ᵖ(Z ⁱ⁺¹) = 0` kills the incoming
connecting morphism, and the second stays an epimorphism because `F ᵖ⁺²(Zⁱ) = 0` kills the
outgoing one. -/
theorem shortExact_map_cyclesShortComplex (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    ((HomologicalComplex.cyclesShortComplex K i j).map (F.functor (p + 1))).ShortExact := by
  have hS := K.cyclesShortComplex_shortExact hij (hK j)
  refine ShortComplex.ShortExact.mk' (F.exact_map hS (p + 1)) ?_ ?_
  · exact (F.exact_δ₂ hS p).mono_g
      ((isZero_functor_cycles_of_lt F K p hK hz hmono p le_rfl j).eq_of_src _ _)
  · exact (F.exact_δ₁ hS (p + 1)).epi_f
      ((isZero_functor_cycles_of_gt F K p hK hz hGE (p + 2) (by omega) i).eq_of_tgt _ _)

include hK hz hGE hmono in
/-- **The complex obtained by applying the top-degree functor `Fⁿ` degreewise to an acyclic
complex whose terms are silent outside the degree `n` is acyclic.** -/
theorem acyclic_mapHomologicalComplex_top :
    (((F.functor (p + 1)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic :=
  CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact _ K
    fun i j hij => shortExact_map_cyclesShortComplex F K p hK hz hGE hmono i j hij

end CategoryTheory.DeltaFunctor

end
