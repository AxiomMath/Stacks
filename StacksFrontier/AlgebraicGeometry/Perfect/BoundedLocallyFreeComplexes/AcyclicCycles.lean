module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingKernel
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Defs
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.Homology.CyclesShortComplex

/-!
# The cycles of a bounded acyclic complex of finite locally free modules

Let `X` be a scheme and let `ℰ^•` be a complex of `𝒪_X`-modules which is bounded, has finite
locally free terms, and is acyclic.  Then every module of cycles `Z^i = ker(ℰ^i ⟶ ℰ^{i+1})` is
again finite locally free. This is step (2) of the proof of [Stacks, Tag 0FDJ].

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.isFiniteLocallyFree_of_shortExact`: the first term
  of a short exact sequence of `𝒪_X`-modules whose other two terms are finite locally free is
  finite locally free.
* `CochainComplex.prop_cycles_of_acyclic_of_boundedAbove`: a class of objects of an abelian
  category closed under passing to the first term of a short exact sequence whose other two terms
  belong to it is inherited by all the cycles of an acyclic cochain complex which has terms in the
  class and vanishes in high degrees.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.isFiniteLocallyFree_cycles_of_acyclic` and its
  `∀`-form `Stacks.Perfect.BoundedLocallyFreeComplexes.forall_isFiniteLocallyFree_cycles`: the
  cycles of a bounded acyclic complex of finite locally free `𝒪_X`-modules are finite locally
  free.

## Implementation notes

`CochainComplex.prop_cycles_of_acyclic_of_boundedAbove` assumes only that the terms vanish above
some degree. Finite local freeness is carried by two classes with identical bodies,
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree` and
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`; Tag 05P2 is stated over the first and
`Stacks.Perfect.BoundedLocallyFreeComplexes.boundedFiniteLocallyFreeComplex` over the second, and
the two are interchanged by `Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree` and
`Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree`.

## References

* [Stacks Project, Tag 0FDJ](https://stacks.math.columbia.edu/tag/0FDJ)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ZeroObject

universe v u

/-! ### The descending induction over the cycles of an acyclic cochain complex -/

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The cycles of a bounded-above acyclic cochain complex inherit a property closed under the
kernel of a short exact sequence.**

If `P` holds for every term of the `ℤ`-indexed cochain complex `K`, the terms of `K` vanish
above the degree `b`, and the first term of a short exact sequence satisfies `P` whenever the
other two do, then `P` holds for the cycles of `K` in every degree. -/
theorem prop_cycles_of_acyclic_of_boundedAbove (P : C → Prop)
    (hP : ∀ S : ShortComplex C, S.ShortExact → P S.X₂ → P S.X₃ → P S.X₁)
    (K : CochainComplex C ℤ) (b : ℤ) (hb : ∀ i : ℤ, b < i → IsZero (K.X i))
    (hK : K.Acyclic) (hX : ∀ i : ℤ, P (K.X i)) (n : ℤ) : P (K.cycles n) := by
  have hzero : P (0 : C) := by
    refine hP (ShortComplex.mk (0 : (0 : C) ⟶ K.X 0) (𝟙 (K.X 0)) (by simp))
      (.mk' ((ShortComplex.exact_iff_mono _ rfl).2 inferInstance) ((isZero_zero C).mono _)
        inferInstance) (hX 0) (hX 0)
  have base : ∀ m : ℤ, b < m → P (K.cycles m) := by
    intro m hm
    refine hP (ShortComplex.mk (K.iCycles m) (0 : K.X m ⟶ (0 : C)) (by simp))
      (.mk' ((ShortComplex.exact_iff_epi _ rfl).2 ((hb m hm).epi _)) inferInstance
        ((isZero_zero C).epi _)) (hX m) hzero
  have step : ∀ m : ℤ, P (K.cycles (m + 1)) → P (K.cycles m) := fun m h ↦
    hP _ (K.cyclesShortComplex_shortExact (i := m) (j := m + 1) rfl (hK (m + 1))) (hX m) h
  have main : ∀ k : ℕ, P (K.cycles (b + 1 - (k : ℤ))) := by
    intro k
    induction k with
    | zero => exact base _ (by push_cast; omega)
    | succ j ih =>
        refine step _ ?_
        have he : b + 1 - ((j + 1 : ℕ) : ℤ) + 1 = b + 1 - (j : ℤ) := by push_cast; ring
        rwa [he]
  by_cases hn : b < n
  · exact base n hn
  · have he : b + 1 - ((b + 1 - n).toNat : ℤ) = n := by
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    exact he ▸ main _

end CochainComplex

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

/-! ### Finite local freeness of the kernel of a short exact sequence -/

/-- **The first term of a short exact sequence of `𝒪_X`-modules whose other two terms are finite
locally free is finite locally free.** -/
theorem isFiniteLocallyFree_of_shortExact {X : Scheme.{u}} (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) S.X₂)
    (h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) S.X₃) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) S.X₁ := by
  obtain ⟨hflat₂, hfp₂⟩ :=
    (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_iff_isFlat_and_isFinitePresentation
      S.X₂).mp h₂
  obtain ⟨hflat₃, -⟩ :=
    (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_iff_isFlat_and_isFinitePresentation
      S.X₃).mp h₃
  refine (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_iff_isFlat_and_isFinitePresentation
    S.X₁).mpr ⟨Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact X.sheaf S hS
      hflat₂ hflat₃, ?_⟩
  have hqc : S.X₂.IsQuasicoherent := by
    obtain ⟨q, hq, -⟩ := h₂.exists_isFiniteLocallyFreeData
    have := hq
    exact q.quasiCoherentData.isQuasicoherent
  have := hfp₂
  have := hqc
  have := hS.epi_g
  have := h₃
  have hker := AlgebraicGeometry.isFinitePresentation_kernel_of_isFiniteLocallyFree S.g
  exact (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hS.fIsKernel) hker

/-! ### The cycles of a bounded acyclic complex of finite locally free modules -/

/-- **The cycles of a bounded acyclic complex of finite locally free `𝒪_X`-modules are finite
locally free.**  This is step (2) of the proof of [Stacks, Tag 0FDJ]. -/
theorem isFiniteLocallyFree_cycles_of_acyclic (X : Scheme.{u})
    (E : CochainComplex X.Modules ℤ) (hE : boundedFiniteLocallyFreeComplex X E)
    (hac : E.Acyclic) (i : ℤ) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (E.cycles i) := by
  obtain ⟨b, hb⟩ := (CochainComplex.minus_iff E).mp hE.1.2
  have : E.IsStrictlyLE b := hb
  have := CochainComplex.prop_cycles_of_acyclic_of_boundedAbove
    (fun M : X.Modules ↦ AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) M)
    isFiniteLocallyFree_of_shortExact E b (fun j hj ↦ E.isZero_of_isStrictlyLE b j hj) hac
    (fun j ↦ have := hE.2 j
      Stacks.StalkFreeBridge.isFiniteLocallyFree_of_finiteLocallyFree (E.X j)) i
  exact Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree (E.cycles i)

/-- For every bounded acyclic complex `E` of finite locally free `𝒪_X`-modules, every module of
cycles of `E` is finite locally free. -/
theorem forall_isFiniteLocallyFree_cycles (X : Scheme.{u}) :
    ∀ E : CochainComplex X.Modules ℤ, boundedFiniteLocallyFreeComplex X E →
      E.Acyclic → ∀ i : ℤ,
        Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
          (E.cycles i) :=
  isFiniteLocallyFree_cycles_of_acyclic X

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
