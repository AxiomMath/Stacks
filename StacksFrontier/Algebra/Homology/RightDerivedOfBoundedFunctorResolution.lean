module

public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExactVanishing
public import StacksFrontier.Algebra.Homology.RightDerivedOfFunctorResolution

/-!
# Right derived functors through a bounded resolution of the functor by partially acyclic functors

Let `T : D ⥤ E` be an additive functor between abelian categories, `D` having enough injectives,
and let `Φ : D ⥤ CochainComplex E ℕ` be an additive functor with an augmentation
`ε : T ⟶ Φ⁰` exhibiting `T M` as the kernel of `Φ⁰ M ⟶ Φ¹ M` for every `M`, such that `Φ I` is
exact in positive degrees for every injective `I`, and whose terms `Φᵖ` vanish for `p ≥ d`.  If
`RᵠΦᵖ(M) = 0` for `q ≥ eₚ`, with every `eₚ ≥ 1`, then `RⁿT(M) = 0` for every
`n ≥ max_{p < d} (p + eₚ)`.

This is the vanishing read off the first page `E₁^{p,q} = RᵠΦᵖ(M)` of the spectral sequence of
the resolution, which degenerates in the region `p + q ≥ max (p + eₚ)`; the spectral sequence is
not used.  The proof is induction on the length of the resolution: the functor
`T' = ker (Φ¹ ⟶ Φ²)` sits in a sequence `0 ⟶ T ⟶ Φ⁰ ⟶ T' ⟶ 0` which is short exact on
injectives, and `Φ^{≥ 1}` is a resolution of `T'` of shorter length, so the long exact sequence
of right derived functors gives `RⁿT(M) = 0` from `RⁿΦ⁰(M) = 0` and `R^{n-1}T'(M) = 0`.

## Main definitions

* `Stacks.Cohomology.RightDerivedCoEdge.cyclesComponent`: the functor of cycles in a fixed degree.

## Main results

* `Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_of_isZero_rightDerived_component`:
  the vanishing above `max_{p < d} (p + eₚ)`.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
-/

@[expose] public section

open CategoryTheory Category Limits

universe v₁ v₂ u₁ u₂

namespace Stacks.Cohomology.RightDerivedCoEdge

variable {D : Type u₁} [Category.{v₁} D] [Abelian D] [EnoughInjectives D]
  {E : Type u₂} [Category.{v₂} E] [Abelian E] (Φ : D ⥤ CochainComplex E ℕ)

/-- The functor `M ↦ Zʲ(Φ M)` of cycles of `Φ` in degree `j`. -/
noncomputable abbrev cyclesComponent (j : ℕ) : D ⥤ E :=
  Φ ⋙ HomologicalComplex.cyclesFunctor E (ComplexShape.up ℕ) j

/-- The inclusion of the cycles of `Φ` in degree `j` into its term in degree `j`. -/
noncomputable def iCyclesComponent (j : ℕ) : cyclesComponent Φ j ⟶ component Φ j where
  app N := (Φ.obj N).iCycles j
  naturality _ _ f := HomologicalComplex.cyclesMap_i (Φ.map f) j

/-- The corestriction of the differential `Φᵏ ⟶ Φ^{k+1}` to the cycles in degree `k + 1`. -/
noncomputable def toCyclesComponent (k : ℕ) : component Φ k ⟶ cyclesComponent Φ (k + 1) where
  app N := (Φ.obj N).toCycles k (k + 1)
  naturality N N' f := by
    change (Φ.map f).f k ≫ (Φ.obj N').toCycles k (k + 1) =
      (Φ.obj N).toCycles k (k + 1) ≫ HomologicalComplex.cyclesMap (Φ.map f) (k + 1)
    rw [← cancel_mono ((Φ.obj N').iCycles (k + 1)), assoc, assoc,
      HomologicalComplex.toCycles_i, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.toCycles_i_assoc]
    exact (Φ.map f).comm k (k + 1)

omit [Abelian D] [EnoughInjectives D] in
/-- The corestriction `Φᵏ ⟶ Z^{k+1}` followed by the inclusion `Z^{k+1} ⟶ Φ^{k+1}` is the
differential `Φᵏ ⟶ Φ^{k+1}`. -/
theorem toCyclesComponent_app_iCycles (k : ℕ) (N : D) :
    (toCyclesComponent Φ k).app N ≫ (iCyclesComponent Φ (k + 1)).app N =
      (Φ.obj N).d k (k + 1) :=
  HomologicalComplex.toCycles_i _ _ _

/-- A complex exact in degree `k + 1` has an epimorphism `Xᵏ ⟶ Z^{k+1}` onto its cycles. -/
theorem epi_toCycles_of_exactAt (K : CochainComplex E ℕ) (k : ℕ) (hK : K.ExactAt (k + 1)) :
    Epi (K.toCycles k (k + 1)) :=
  Preadditive.epi_of_isZero_cokernel' _ (K.homologyIsCokernel k (k + 1) (by simp))
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hK)

variable [Φ.Additive]

/-- The functor of cycles in degree `j` of an additive `Φ` is additive. -/
instance additive_cyclesComponent (j : ℕ) : (cyclesComponent Φ j).Additive where
  map_add {N N' f g} := by
    change HomologicalComplex.cyclesMap (Φ.map (f + g)) j =
      HomologicalComplex.cyclesMap (Φ.map f) j + HomologicalComplex.cyclesMap (Φ.map g) j
    rw [← cancel_mono ((Φ.obj N').iCycles j), Preadditive.add_comp,
      HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.cyclesMap_i, Φ.map_add, HomologicalComplex.add_f_apply,
      Preadditive.comp_add]

/-- The induction behind
`Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_of_isZero_rightDerived_component`, for
a resolution `0 ⟶ T ⟶ Φᵏ ⟶ Φ^{k+1} ⟶ ⋯` starting in degree `k`, by induction on `d - k`. -/
theorem isZero_rightDerived_of_isZero_rightDerived_component_aux (d : ℕ)
    (hd : ∀ p, d ≤ p → ∀ N : D, IsZero ((Φ.obj N).X p))
    (hinj : ∀ I : D, Injective I → ∀ n, 0 < n → (Φ.obj I).ExactAt n)
    (M : D) (e : ℕ → ℕ) (he1 : ∀ p, 0 < e p)
    (he : ∀ p q, e p ≤ q → IsZero (((component Φ p).rightDerived q).obj M)) (m : ℕ) :
    ∀ (k : ℕ), d - k = m → ∀ (T : D ⥤ E) [T.Additive] (ε : T ⟶ component Φ k)
      (hw : ∀ N, ε.app N ≫ (Φ.obj N).d k (k + 1) = 0), (∀ N, Mono (ε.app N)) →
      (∀ N, (ShortComplex.mk _ _ (hw N)).Exact) → ∀ n : ℕ,
      (∀ p, k ≤ p → p < d → p - k + e p ≤ n) → IsZero ((T.rightDerived n).obj M) := by
  induction m with
  | zero =>
    intro k hk T _ ε hw hmono _ n _
    have hT : ∀ N, IsZero (T.obj N) := fun N => by
      have := hmono N
      exact IsZero.of_mono (ε.app N) (hd k (by omega) N)
    refine IsZero.of_iso ?_ ((injectiveResolution M).isoRightDerivedObj T n)
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (HomologicalComplex.ExactAt.of_isZero (hT _))
  | succ m ih =>
    intro k hk T _ ε hw hmono hex n hb
    have hkd : k < d := by omega
    have hbk := hb k le_rfl hkd
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := he1 k; omega⟩
    have hT' : IsZero (((cyclesComponent Φ (k + 1)).rightDerived n).obj M) :=
      ih (k + 1) (by omega) (cyclesComponent Φ (k + 1)) (iCyclesComponent Φ (k + 1))
        (fun N => (Φ.obj N).iCycles_d (k + 1) (k + 1 + 1))
        (fun N => inferInstanceAs (Mono ((Φ.obj N).iCycles (k + 1))))
        (fun N => ShortComplex.exact_of_f_is_kernel _
          ((Φ.obj N).cyclesIsKernel (k + 1) (k + 1 + 1) (by simp)))
        n (fun p hp hpd => by have := hb p (by omega) hpd; omega)
    have hiq : ε ≫ toCyclesComponent Φ k = 0 := by
      ext N
      show ε.app N ≫ (Φ.obj N).toCycles k (k + 1) = 0
      rw [← cancel_mono ((Φ.obj N).iCycles (k + 1)), assoc, HomologicalComplex.toCycles_i,
        zero_comp]
      exact hw N
    have hSES : ∀ X : D, Injective X →
        (NatTrans.appShortComplex ε (toCyclesComponent Φ k) hiq X).ShortExact := by
      intro X hX
      have := hmono X
      have hep : Epi ((Φ.obj X).toCycles k (k + 1)) :=
        epi_toCycles_of_exactAt (Φ.obj X) k (hinj X hX (k + 1) (by omega))
      refine ShortComplex.ShortExact.mk' ?_ this hep
      let φ : NatTrans.appShortComplex ε (toCyclesComponent Φ k) hiq X ⟶
          ShortComplex.mk _ _ (hw X) :=
        { τ₁ := 𝟙 _
          τ₂ := 𝟙 _
          τ₃ := (Φ.obj X).iCycles (k + 1)
          comm₁₂ := by
            show 𝟙 _ ≫ ε.app X = ε.app X ≫ 𝟙 _
            rw [id_comp, comp_id]
          comm₂₃ := by
            show 𝟙 _ ≫ (Φ.obj X).d k (k + 1) =
              (Φ.obj X).toCycles k (k + 1) ≫ (Φ.obj X).iCycles (k + 1)
            rw [HomologicalComplex.toCycles_i, id_comp] }
      have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 _))
      have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
      have : Mono φ.τ₃ := inferInstanceAs (Mono ((Φ.obj X).iCycles (k + 1)))
      exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (hex X)
    exact CategoryTheory.isZero_rightDerived_succ_of_isZero ε (toCyclesComponent Φ k) hiq hSES M n
      (he k (n + 1) (by omega)) hT'

/-- **A bounded resolution by partially acyclic functors bounds the right derived functors.**
Let `ε : T ⟶ Φ⁰` exhibit `T M` as the kernel of `Φ⁰ M ⟶ Φ¹ M` for every `M`, let `Φ I` be exact
in positive degrees for every injective `I`, and let the terms `Φᵖ` vanish for `p ≥ d`.  If
`RᵠΦᵖ(M) = 0` for `q ≥ eₚ`, where every `eₚ ≥ 1`, then `RⁿT(M) = 0` as soon as `p + eₚ ≤ n` for
every `p < d`. -/
theorem isZero_rightDerived_of_isZero_rightDerived_component (T : D ⥤ E) [T.Additive]
    (ε : T ⟶ component Φ 0) (hw : ∀ N, ε.app N ≫ (Φ.obj N).d 0 1 = 0)
    (hmono : ∀ N, Mono (ε.app N)) (hex : ∀ N, (ShortComplex.mk _ _ (hw N)).Exact)
    (hinj : ∀ I : D, Injective I → ∀ n, 0 < n → (Φ.obj I).ExactAt n) (d : ℕ)
    (hd : ∀ p, d ≤ p → ∀ N : D, IsZero ((Φ.obj N).X p)) (M : D) (e : ℕ → ℕ)
    (he1 : ∀ p, 0 < e p) (he : ∀ p q, e p ≤ q → IsZero (((component Φ p).rightDerived q).obj M))
    (n : ℕ) (hn : ∀ p, p < d → p + e p ≤ n) : IsZero ((T.rightDerived n).obj M) :=
  isZero_rightDerived_of_isZero_rightDerived_component_aux Φ d hd hinj M e he1 he (d - 0) 0 rfl
    T ε hw hmono hex n (fun p _ hpd => by have := hn p hpd; omega)

end Stacks.Cohomology.RightDerivedCoEdge
