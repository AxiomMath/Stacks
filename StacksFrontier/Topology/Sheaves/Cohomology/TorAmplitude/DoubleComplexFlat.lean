module

public import Mathlib.Algebra.Homology.Double
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatRepresentative

/-!
# Flatness of the lower term of a two-term complex of Tor amplitude in `[-1, 0]`

Let `d : X₁ ⟶ X₀` be a morphism of `𝒪_X`-modules and let `K` be the two-term complex it spans,
placed in cohomological degrees `-1` and `0`.  If `X₀` is flat and `K` has Tor amplitude in
`[-1, 0]`, then `X₁` is flat as well, so that `K` is a bounded-above complex of flat modules and
therefore K-flat.

This is the ringed-space form of one direction of [Stacks, Tag 0653].

## Main results

* `Stacks.Cohomology.TorAmplitude.DoubleFlat.exists_twoTerm_shortExact`: a complex vanishing
  outside degrees `-1` and `0` is an extension of its degree `-1` term by its degree `0` term.
* `Stacks.Cohomology.TorAmplitude.DoubleFlat.hasTorAmplitude_obj₃`: Tag 08CJ (1) for the
  ringed-space Tor-amplitude predicate.
* `Stacks.Cohomology.TorAmplitude.DoubleFlat.isFlat_X_negOne_of_hasTorAmplitude`: if the degree
  `0` term is flat and the complex has Tor amplitude in `[-1, 0]`, the degree `-1` term is flat.
* `Stacks.Cohomology.TorAmplitude.DoubleFlat.kFlat_of_hasTorAmplitude`: such a two-term complex
  is K-flat.

## References

* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
* [Stacks Project, Tag 08CJ](https://stacks.math.columbia.edu/tag/08CJ)
* [Stacks Project, Tag 08CI](https://stacks.math.columbia.edu/tag/08CI)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry StrictlyPerfect
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback (Modules KFlat
  kFlat_of_boundedAbove_of_flat)

universe u d

namespace Stacks.Cohomology.TorAmplitude.DoubleFlat

/-! ### The stupid filtration of a two-term complex -/

section General

variable {C : Type*} [Category C] [Abelian C]

/-- **The stupid filtration of a two-term complex.**  A complex `K` vanishing outside degrees
`-1` and `0` sits in a short exact sequence of complexes
`0 ⟶ K^0[0] ⟶ K ⟶ K^{-1}[1] ⟶ 0`, where `K^0[0]` is the degree `0` term placed in degree `0`
and `K^{-1}[1]` is the degree `-1` term placed in degree `-1`. -/
theorem exists_twoTerm_shortExact {K : CochainComplex C ℤ}
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i)) :
    ∃ (i : (CochainComplex.singleFunctor C 0).obj (K.X 0) ⟶ K)
      (p : K ⟶ (CochainComplex.singleFunctor C (-1)).obj (K.X (-1)))
      (h : i ≫ p = 0), (ShortComplex.mk i p h).ShortExact := by
  classical
  let i : (CochainComplex.singleFunctor C 0).obj (K.X 0) ⟶ K :=
    HomologicalComplex.mkHomFromSingle (𝟙 (K.X 0))
      (by
        intro k hk
        have : k = 1 := by
          have hk' : (0 : ℤ) + 1 = k := hk
          omega
        subst this
        exact (hK 1 (by decide) (by decide)).eq_of_tgt _ _)
  let p : K ⟶ (CochainComplex.singleFunctor C (-1)).obj (K.X (-1)) :=
    HomologicalComplex.mkHomToSingle (𝟙 (K.X (-1)))
      (by
        intro j hj
        have : j = -2 := by
          have hj' : j + 1 = -1 := hj
          omega
        subst this
        exact (hK (-2) (by decide) (by decide)).eq_of_src _ _)
  have hi : IsIso (i.f 0) := by
    dsimp only [i]
    rw [HomologicalComplex.mkHomFromSingle_f]
    infer_instance
  have hp : IsIso (p.f (-1)) := by
    dsimp only [p]
    rw [HomologicalComplex.mkHomToSingle_f]
    infer_instance
  have hz := HomologicalComplex.isZero_single_obj_X (V := C) (ComplexShape.up ℤ)
  have hip : i ≫ p = 0 := by
    apply HomologicalComplex.from_single_hom_ext
    exact (hz (-1) _ 0 (by omega)).eq_of_tgt _ _
  refine ⟨i, p, hip, HomologicalComplex.shortExact_of_degreewise_shortExact _ ?_⟩
  intro n
  let S := (ShortComplex.mk i p hip).map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
  change S.ShortExact
  have hm : Mono S.f := by
    by_cases hn : n = 0
    · subst n; exact inferInstanceAs (Mono (i.f 0))
    · exact (hz 0 _ n hn).mono _
  have he : Epi S.g := by
    by_cases hn : n = -1
    · subst n; exact inferInstanceAs (Epi (p.f (-1)))
    · exact (hz (-1) _ n hn).epi _
  refine { exact := ?_, mono_f := hm, epi_g := he }
  by_cases hn : n = 0
  · subst n
    refine (S.exact_iff_epi ?_).2 ?_
    · exact (hz (-1) _ 0 (by omega)).eq_of_tgt _ _
    · exact inferInstanceAs (Epi (i.f 0))
  · by_cases hn' : n = -1
    · subst n
      refine (S.exact_iff_mono ?_).2 ?_
      · exact (hz 0 _ (-1) (by omega)).eq_of_src _ _
      · exact inferInstanceAs (Mono (p.f (-1)))
    · exact S.exact_of_isZero_X₂ (hK n hn' hn)

end General

/-! ### Tor amplitude along a distinguished triangle -/

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]

attribute [local instance] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- **Tag 08CJ (1) at the ringed-space Tor-amplitude predicate.**  In a distinguished triangle
`K ⟶ L ⟶ M ⟶ K[1]` of `D(O_X)`, if `K` has Tor amplitude in `[a + 1, b + 1]` and `L` has Tor
amplitude in `[a, b]`, then `M` has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitude_obj₃ (T : Triangle (DerivedCategory (Modules X)))
    (hT : T ∈ distinguishedTriangles) (a b : ℤ)
    (hK : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₁ (a + 1) (b + 1))
    (hL : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₂ a b) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitude X T.obj₃ a b := by
  have h := @TorAmplitude.hasTorAmplitude_obj₃ (Modules X) _ _ _
    (Stacks.Cohomology.TorAmplitude.FlatOpcycles.tensorSingleFunctor X)
    (fun F => (Stacks.Cohomology.TorAmplitude.derTensor X).commShift_left
      ((DerivedCategory.singleFunctor (Modules X) 0).obj F))
    (fun F => (Stacks.Cohomology.TorAmplitude.derTensor X).exact_left
      ((DerivedCategory.singleFunctor (Modules X) 0).obj F))
    T hT a b
    (fun F i hi => hK F i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
    (fun F i hi => hL F i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega))
  exact fun F i hi => h F i (by simp only [Set.mem_Icc, not_and_or, not_le] at hi; omega)

/-! ### Flatness of the lower term -/

/-- **Tag 0653 for a two-term complex, on a ringed space.**  If a complex `K` of
`𝒪_X`-modules vanishes outside degrees `-1` and `0`, has Tor amplitude in `[-1, 0]`, and its
degree `0` term is flat, then its degree `-1` term is flat. -/
theorem isFlat_X_negOne_of_hasTorAmplitude (K : CochainComplex (Modules X) ℤ)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hX₀ : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X 0))
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X (DerivedCategory.Q.obj K) (-1) 0) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X (-1)) := by
  obtain ⟨i, p, hip, hS⟩ := exists_twoTerm_shortExact hK
  have h₀ : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (Modules X) 0).obj (K.X 0)))
      (-1 + 1) (0 + 1) :=
    Stacks.TorAmplitude.FlatRepresentative.hasTorAmplitude_of_flat_representative _
      (-1 + 1) (0 + 1) _
      (fun j => by
        by_cases hj : j = 0
        · subst j
          exact Stacks.Cohomology.TorAmplitude.BoundedFlatRepresentative.isFlat_of_iso
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X 0)) hX₀
        · exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_of_isZero _
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X 0) j hj))
      (fun j hj => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.X 0) j
        (by simp only [Set.mem_Icc, not_and_or, not_le] at hj; omega))
      (Iso.refl _)
  have h₃ := hasTorAmplitude_obj₃ (DerivedCategory.triangleOfSES hS)
    (DerivedCategory.triangleOfSES_distinguished hS) (-1) 0 h₀ hamp
  exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_of_hasTorAmplitude_single
    (K.X (-1)) (-1) 0
    (Stacks.Cohomology.TorAmplitude.FlatOpcycles.hasTorAmplitude_of_iso h₃
      ((DerivedCategory.singleFunctorIsoCompQ (Modules X) (-1)).app (K.X (-1))))

/-- **A two-term complex of Tor amplitude in `[-1, 0]` with flat top term is K-flat.**  A complex
`K` of `𝒪_X`-modules vanishing outside degrees `-1` and `0`, with flat degree `0` term and of Tor
amplitude in `[-1, 0]`, is K-flat. -/
theorem kFlat_of_hasTorAmplitude (K : CochainComplex (Modules X) ℤ)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hX₀ : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (K.X 0))
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X (DerivedCategory.Q.obj K) (-1) 0) :
    KFlat X K := by
  have hX₁ := isFlat_X_negOne_of_hasTorAmplitude K hK hX₀ hamp
  refine kFlat_of_boundedAbove_of_flat X _ ⟨0, ?_⟩ ?_
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hK i (by omega) (by omega)
  · intro i
    by_cases h1 : i = -1
    · subst i; exact hX₁
    · by_cases h0 : i = 0
      · subst i; exact hX₀
      · exact Stacks.Cohomology.TorAmplitude.FlatOpcycles.isFlat_of_isZero _ (hK i h1 h0)

end Stacks.Cohomology.TorAmplitude.DoubleFlat

end
