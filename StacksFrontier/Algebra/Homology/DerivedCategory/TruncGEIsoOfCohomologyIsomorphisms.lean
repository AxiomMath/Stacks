module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

/-!
# The canonical truncation of an approximation which is exact above a degree

Let `C` be an abelian category with a derived category, let `α : P ⟶ F` be a morphism of cochain
complexes of objects of `C` which is an isomorphism on cohomology in every degree `≥ a`, and
suppose `F` has no cohomology below `a`. Then `α` *becomes* an isomorphism after the canonical
truncation of its source: `τ_{≥ a}P` and `F` are isomorphic in `D(C)`.

No hypothesis on `P` is needed. Neither complex is assumed bounded, and `α` itself is neither
injective nor surjective on cohomology in degrees below `a`; all that happens there is
discarded by the truncation.

## Main results

* `CochainComplex.exists_iso_Q_truncGE_of_isIso_homologyMap`: the isomorphism
  `τ_{≥ a}P ≅ F` in `D(C)` described above.

## Implementation notes

The mechanism is the orthogonality of the canonical t-structure. The cokernel sequence of
`P.ιTruncLE (a - 1)` gives a distinguished triangle

`τ_{≤ a-1}P ⟶ P ⟶ X₃ ⟶ (τ_{≤ a-1}P)[1]`

in `D(C)` by `CategoryTheory.DerivedCategory.triangleOfSES`. Its first object is `≤ a - 1` and
`F` is `≥ a`, so every morphism between them vanishes
(`CategoryTheory.Triangulated.TStructure.zero`); hence `α` is killed by the first map of the
triangle and factors through the second, by
`CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂`.

The factor is an isomorphism by `CategoryTheory.DerivedCategory.isIso_iff`, which reduces to one
degree at a time. Above `a - 1` the quotient map `P ⟶ X₃` is already an isomorphism on
cohomology (`HomologicalComplex.isIso_homologyMap_shortComplexTruncLE_g`), so the factor inherits
the hypothesis on `α`; below `a` both sides have vanishing cohomology — for `X₃` because
`HomologicalComplex.shortComplexTruncLE_X₃_isSupportedOutside` makes it exact in exactly those
degrees, and for `F` by the assumption that it is `≥ a`.

Finally `X₃` is identified with `τ_{≥ a}P` by the quasi-isomorphism
`CochainComplex.shortComplexTruncLEX₃ToTruncGE`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **A morphism which is an isomorphism on cohomology above a degree identifies the canonical
truncation of its source with its target.** Let `α : P ⟶ F` be a morphism of cochain complexes
which induces an isomorphism on cohomology in every degree `≥ a`, and assume that `F`, viewed in
`D(C)`, has no cohomology below `a`. Then `τ_{≥ a}P` and `F` are isomorphic in `D(C)`.

This is the step by which a local approximation of a bounded-below object by a strictly perfect
complex, exact only above a degree, is turned into a genuine representative of that object. -/
theorem exists_iso_Q_truncGE_of_isIso_homologyMap {P F : CochainComplex C ℤ} (a : ℤ) (α : P ⟶ F)
    (hα : ∀ i : ℤ, a ≤ i → IsIso (HomologicalComplex.homologyMap α i))
    [(DerivedCategory.Q.obj F).IsGE a] :
    Nonempty (DerivedCategory.Q.obj (P.truncGE a) ≅ DerivedCategory.Q.obj F) := by
  have hSE := P.shortComplexTruncLE_shortExact (a - 1)
  have hdist := DerivedCategory.triangleOfSES_distinguished hSE
  have hzero : ∀ f : DerivedCategory.Q.obj (P.truncLE (a - 1)) ⟶ DerivedCategory.Q.obj F,
      f = 0 := fun f => DerivedCategory.TStructure.t.zero f (a - 1) a (by omega)
  obtain ⟨g, hg⟩ :=
    Triangle.yoneda_exact₂ _ hdist (DerivedCategory.Q.map α) (hzero _)
  have hgiso : IsIso g := by
    rw [DerivedCategory.isIso_iff]
    intro n
    rcases lt_or_ge n a with hn | hn
    · refine IsZero.isIso ?_ ((DerivedCategory.Q.obj F).isZero_of_isGE a n hn) _
      have hex : (P.shortComplexTruncLE (a - 1)).X₃.ExactAt n := by
        have h := (P.shortComplexTruncLE_X₃_isSupportedOutside
          (ComplexShape.embeddingUpIntLE (a - 1))).exactAt (a - 1 - n).toNat
        rwa [show (ComplexShape.embeddingUpIntLE (a - 1)).f (a - 1 - n).toNat = n by
          simp only [ComplexShape.embeddingUpIntLE_f]; omega] at h
      rw [HomologicalComplex.exactAt_iff_isZero_homology] at hex
      exact hex.of_iso
        ((DerivedCategory.homologyFunctorFactors C n).app
          (P.shortComplexTruncLE (a - 1)).X₃)
    · have hQ : ∀ {X Y : CochainComplex C ℤ} (f : X ⟶ Y),
          IsIso (HomologicalComplex.homologyMap f n) →
          IsIso ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.Q.map f)) :=
        fun f => (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C n) f).2
      have h₁ := hQ α (hα n hn)
      have h₂ : IsIso ((DerivedCategory.homologyFunctor C n).map
          (DerivedCategory.triangleOfSES hSE).mor₂) := hQ (P.shortComplexTruncLE (a - 1)).g
        (P.isIso_homologyMap_shortComplexTruncLE_g (ComplexShape.embeddingUpIntLE (a - 1)) n
          ((ComplexShape.notMem_range_embeddingUpIntLE_iff (a - 1) n).2 (by omega)))
      have h₄ : IsIso ((DerivedCategory.homologyFunctor C n).map
          ((DerivedCategory.triangleOfSES hSE).mor₂ ≫ g)) := by
        rw [← hg]
        exact h₁
      rw [Functor.map_comp] at h₄
      exact IsIso.of_isIso_comp_left
        ((DerivedCategory.homologyFunctor C n).map (DerivedCategory.triangleOfSES hSE).mor₂)
        ((DerivedCategory.homologyFunctor C n).map g)
  have hsucc : a - 1 + 1 = a := by omega
  have hφ :
      IsIso (DerivedCategory.Q.map (P.shortComplexTruncLEX₃ToTruncGE (a - 1) a hsucc)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := C) _).2 inferInstance
  exact ⟨(@asIso _ _ _ _ (DerivedCategory.Q.map
      (P.shortComplexTruncLEX₃ToTruncGE (a - 1) a hsucc)) hφ).symm ≪≫
    @asIso _ _ _ _ g hgiso⟩

end CochainComplex

end
