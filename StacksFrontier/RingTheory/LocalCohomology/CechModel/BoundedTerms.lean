module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Morphisms into a bounded complex, read off its terms

Let `C` be an abelian category with a derived category and let `K` be a cochain complex of
objects of `C` which vanishes outside a finite range of degrees. This file records the two
consequences of that boundedness which are used to recognise an explicit complex as a
coreflection.

The first is that a property of objects of `D(C)` which contains the zero object, is closed
under isomorphisms, and is stable under extensions, holds for `K` as soon as it holds for every
object `K^i` placed in every degree: one peels off the bottom term of `K`, which sits in a short
exact sequence of complexes together with the kernel of the projection, and induces on the width
of the range of nonvanishing degrees.

The second specialises this to the right orthogonal of a class of objects, where the property is
the vanishing of all morphisms from that class. There it upgrades to a statement about the bottom
term alone: if every term of `K` except the one in degree `n` admits no nonzero morphism from `W`
in any shift, then composing with the projection `K ⟶ K^n[-n]` identifies the morphisms from `W`
to `K` with the morphisms from `W` to `K^n[-n]`.

## Main definitions

* `Stacks.LocalCohomology.bottomProjection` — the projection of a complex vanishing below `a`
  onto its degree-`a` term, viewed as a complex concentrated in degree `a`.

## Main results

* `Stacks.LocalCohomology.prop_Q_obj_of_bounded_terms` — an extension-stable property of objects
  of `D(C)` holds for a bounded complex if it holds for each of its terms.
* `Stacks.LocalCohomology.subsingleton_hom_Q_obj_of_bounded_terms` — there is no nonzero morphism
  into a bounded complex if there is none into any of its terms.
* `Stacks.LocalCohomology.bijective_comp_toSingle` — the bottom-term comparison is bijective on
  morphisms out of `W` when the other terms are orthogonal to `W`.

## Implementation notes

The proofs are the standard stupid-filtration argument. The same argument appears, in the
dual (contravariant) form and for the left orthogonal, in the private declarations
`prop_of_bounded`, `subsingleton_hom_of_bounded` and `bijective_precomp_to_single` of
`StacksFrontier/Homology/DerivedComplete/CechCompletion.lean`, and again in
`StacksFrontier/Homology/DerivedComplete/CompleteRestrictScalarsEquivalence.lean`; since those are
private, the covariant form is proved here from scratch. The property-level statement
`prop_Q_obj_of_bounded_terms` is stated for an arbitrary `ObjectProperty`, so a future
deduplication can serve both orientations from it.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace Stacks.LocalCohomology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- The projection of a cochain complex that vanishes in degrees below `a` onto the complex
concentrated in degree `a` with value `K^a`. -/
def bottomProjection (K : CochainComplex C ℤ) (a : ℤ) (h : ∀ i, i < a → IsZero (K.X i)) :
    K ⟶ (CochainComplex.singleFunctor C a).obj (K.X a) :=
  HomologicalComplex.mkHomToSingle (𝟙 (K.X a)) (fun i hi =>
    (h i (by change i + 1 = a at hi; omega)).eq_of_src _ _)

omit [HasDerivedCategory C] in
/-- In degree `a` the bottom projection is the identity. -/
theorem isIso_bottomProjection_f (K : CochainComplex C ℤ) (a : ℤ)
    (h : ∀ i, i < a → IsZero (K.X i)) : IsIso ((bottomProjection K a h).f a) := by
  dsimp only [bottomProjection]
  rw [HomologicalComplex.mkHomToSingle_f]
  infer_instance

omit [HasDerivedCategory C] in
/-- A morphism of cochain complexes into a complex concentrated in degree `n` which is
invertible in degree `n` is an epimorphism. -/
theorem epi_of_isIso_f_toSingle {K : CochainComplex C ℤ} {N : C} {n : ℤ}
    (π : K ⟶ (CochainComplex.singleFunctor C n).obj N) (hπ : IsIso (π.f n)) : Epi π := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  by_cases hi : i = n
  · subst i
    have := hπ
    infer_instance
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n N i hi).epi _

section Kernel

variable {K : CochainComplex C ℤ} {N : C} {n : ℤ}

/-- The short complex formed by the kernel of a morphism onto a complex concentrated in one
degree. -/
def toSingleKernelShortComplex (π : K ⟶ (CochainComplex.singleFunctor C n).obj N) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (kernel.ι π) π (kernel.condition π)

omit [HasDerivedCategory C] in
/-- The kernel of a morphism onto a complex concentrated in degree `n`, invertible there, gives
a short exact sequence of complexes. -/
theorem toSingleKernelShortComplex_shortExact
    (π : K ⟶ (CochainComplex.singleFunctor C n).obj N) (hπ : IsIso (π.f n)) :
    (toSingleKernelShortComplex π).ShortExact :=
  have : Epi π := epi_of_isIso_f_toSingle π hπ
  { mono_f := inferInstanceAs (Mono (kernel.ι π))
    epi_g := inferInstanceAs (Epi π)
    exact := ShortComplex.exact_kernel π }

omit [HasDerivedCategory C] in
/-- The kernel vanishes in the degree where the projection is invertible. -/
theorem isZero_kernel_toSingle_X_self
    (π : K ⟶ (CochainComplex.singleFunctor C n).obj N) (hπ : IsIso (π.f n)) :
    IsZero ((kernel π).X n) :=
  ((toSingleKernelShortComplex_shortExact π hπ).map_of_exact
    (HomologicalComplex.eval C _ n)).isIso_g_iff.mp hπ

omit [HasDerivedCategory C] in
/-- Away from that degree the kernel agrees with the complex. -/
theorem isIso_kernel_ι_toSingle_f
    (π : K ⟶ (CochainComplex.singleFunctor C n).obj N) (hπ : IsIso (π.f n))
    (i : ℤ) (hi : i ≠ n) : IsIso ((kernel.ι π).f i) :=
  ((toSingleKernelShortComplex_shortExact π hπ).map_of_exact
    (HomologicalComplex.eval C _ i)).isIso_f_iff.mpr
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n N i hi)

end Kernel

/-- An extension-stable property of objects of `D(C)` holding for every term of a complex,
placed in every degree, holds for the complex, provided the complex vanishes outside a range of
`m` consecutive degrees starting at `a`. -/
theorem prop_Q_obj_of_bounded_terms (P : ObjectProperty (DerivedCategory C))
    [P.IsTriangulatedClosed₂] [P.ContainsZero] [P.IsClosedUnderIsomorphisms] (m : ℕ) :
    ∀ (a : ℤ) (K : CochainComplex C ℤ),
      (∀ i, i < a ∨ a + m ≤ i → IsZero (K.X i)) →
      (∀ i q, P ((DerivedCategory.singleFunctor C q).obj (K.X i))) →
      P (DerivedCategory.Q.obj K) := by
  induction m with
  | zero =>
    intro a K hz _
    refine P.prop_of_isZero (DerivedCategory.Q.map_isZero ((IsZero.iff_id_eq_zero _).mpr ?_))
    ext i
    exact (hz i (by omega)).eq_of_src _ _
  | succ m ih =>
    intro a K hz ht
    let π := bottomProjection K a (fun i hi => hz i (Or.inl hi))
    have hπ : IsIso (π.f a) := isIso_bottomProjection_f K a _
    have hS := toSingleKernelShortComplex_shortExact π hπ
    have hzero : IsZero ((kernel π).X a) := isZero_kernel_toSingle_X_self π hπ
    have hker : P (DerivedCategory.Q.obj (kernel π)) := by
      refine ih (a + 1) _ (fun i hi => ?_) (fun i q => ?_)
      · by_cases hia : i = a
        · subst hia
          exact hzero
        · have := isIso_kernel_ι_toSingle_f π hπ i hia
          exact (hz i (by push_cast at hi ⊢; omega)).of_iso (asIso ((kernel.ι π).f i))
      · by_cases hia : i = a
        · subst hia
          exact P.prop_of_isZero ((DerivedCategory.singleFunctor C q).map_isZero hzero)
        · have := isIso_kernel_ι_toSingle_f π hπ i hia
          exact P.prop_of_iso ((DerivedCategory.singleFunctor C q).mapIso
            (asIso ((kernel.ι π).f i))).symm (ht i q)
    exact P.ext_of_isTriangulatedClosed₂ (DerivedCategory.triangleOfSES hS)
      (DerivedCategory.triangleOfSES_distinguished hS) hker
      (P.prop_of_iso ((DerivedCategory.singleFunctorIsoCompQ C a).app _) (ht a a))

variable (W : DerivedCategory C)

/-- There is no nonzero morphism from `W` into a bounded complex as soon as there is none into
any of its terms, placed in any degree. -/
theorem subsingleton_hom_Q_obj_of_bounded_terms (K : CochainComplex C ℤ) (a : ℤ) (m : ℕ)
    (hz : ∀ i, i < a ∨ a + m ≤ i → IsZero (K.X i))
    (ht : ∀ i q, Subsingleton (W ⟶ (DerivedCategory.singleFunctor C q).obj (K.X i))) :
    Subsingleton (W ⟶ DerivedCategory.Q.obj K) := by
  have hP : (ObjectProperty.rightOrthogonal (fun X : DerivedCategory C => X = W))
      (DerivedCategory.Q.obj K) :=
    prop_Q_obj_of_bounded_terms _ m a K hz (fun i q X f hX => by
      subst hX
      exact (ht i q).elim _ _)
  exact ⟨fun f g => (hP f rfl).trans (hP g rfl).symm⟩

/-- The same statement for the shift of a bounded complex. -/
theorem subsingleton_hom_Q_obj_shift_of_bounded_terms (K : CochainComplex C ℤ) (a : ℤ) (m : ℕ)
    (hz : ∀ i, i < a ∨ a + m ≤ i → IsZero (K.X i))
    (ht : ∀ i q, Subsingleton (W ⟶ (DerivedCategory.singleFunctor C q).obj (K.X i)))
    (p : ℤ) : Subsingleton (W ⟶ (DerivedCategory.Q.obj K)⟦p⟧) := by
  have : Subsingleton (W ⟶ DerivedCategory.Q.obj (K⟦p⟧)) :=
    subsingleton_hom_Q_obj_of_bounded_terms W (K⟦p⟧) (a - p) m
      (fun i hi => hz (i + p) (by omega)) (fun i q => ht (i + p) q)
  have e : DerivedCategory.Q.obj (K⟦p⟧) ≅ (DerivedCategory.Q.obj K)⟦p⟧ :=
    (DerivedCategory.Q.commShiftIso p).app K
  exact (Iso.homCongr (Iso.refl W) e).symm.injective.subsingleton

/-- **The bottom-term comparison.** If no nonzero morphism goes from `W` to any term of `K`
other than the degree-`n` one, in any shift, then composing with a morphism `K ⟶ K^n[-n]` which
is invertible in degree `n` identifies the morphisms from `W` to `K` with the morphisms from `W`
to `K^n[-n]`. -/
theorem bijective_comp_toSingle (K : CochainComplex C ℤ) (N : C) (n a : ℤ) (m : ℕ)
    (π : K ⟶ (CochainComplex.singleFunctor C n).obj N) (hπ : IsIso (π.f n))
    (hz : ∀ i, i < a ∨ a + m ≤ i → IsZero (K.X i))
    (ht : ∀ i, i ≠ n → ∀ q, Subsingleton (W ⟶ (DerivedCategory.singleFunctor C q).obj (K.X i))) :
    Function.Bijective (fun g : W ⟶ DerivedCategory.Q.obj K => g ≫ DerivedCategory.Q.map π) := by
  have hzero : IsZero ((kernel π).X n) := isZero_kernel_toSingle_X_self π hπ
  have hkerzero : ∀ i, i < a ∨ a + m ≤ i → IsZero ((kernel π).X i) := by
    intro i hi
    by_cases hin : i = n
    · exact hin ▸ hzero
    · have := isIso_kernel_ι_toSingle_f π hπ i hin
      exact (hz i hi).of_iso (asIso ((kernel.ι π).f i))
  have hkerterm : ∀ i q,
      Subsingleton (W ⟶ (DerivedCategory.singleFunctor C q).obj ((kernel π).X i)) := by
    intro i q
    by_cases hin : i = n
    · subst i
      exact ⟨fun f g => ((DerivedCategory.singleFunctor C q).map_isZero hzero).eq_of_tgt f g⟩
    · have := isIso_kernel_ι_toSingle_f π hπ i hin
      have hsub := ht i hin q
      exact (Iso.homCongr (Iso.refl W) ((DerivedCategory.singleFunctor C q).mapIso
        (asIso ((kernel.ι π).f i)))).injective.subsingleton
  have hS := toSingleKernelShortComplex_shortExact π hπ
  have h₁ : Subsingleton (W ⟶ DerivedCategory.Q.obj (kernel π)) :=
    subsingleton_hom_Q_obj_of_bounded_terms W (kernel π) a m hkerzero hkerterm
  have h₂ : Subsingleton (W ⟶ (DerivedCategory.Q.obj (kernel π))⟦(1 : ℤ)⟧) :=
    subsingleton_hom_Q_obj_shift_of_bounded_terms W (kernel π) a m hkerzero hkerterm 1
  have hT := DerivedCategory.triangleOfSES_distinguished hS
  have h₁' : ∀ b : W ⟶ (DerivedCategory.triangleOfSES hS).obj₁, b = 0 := fun b => h₁.elim b 0
  have h₂' : ∀ b : W ⟶ (DerivedCategory.triangleOfSES hS).obj₁⟦(1 : ℤ)⟧, b = 0 :=
    fun b => h₂.elim b 0
  refine ⟨fun f g hfg => ?_, fun f => ?_⟩
  · have hfg' : (f - g) ≫ (DerivedCategory.triangleOfSES hS).mor₂ = 0 := by
      change (f - g) ≫ DerivedCategory.Q.map π = 0
      rw [Preadditive.sub_comp]
      exact sub_eq_zero.mpr hfg
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₂ _ hT (f - g) hfg'
    refine sub_eq_zero.mp (hb.trans ?_)
    rw [h₁' b, zero_comp]
    rfl
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ _ hT f (h₂' _)
    exact ⟨g, hg.symm⟩

end Stacks.LocalCohomology

end
