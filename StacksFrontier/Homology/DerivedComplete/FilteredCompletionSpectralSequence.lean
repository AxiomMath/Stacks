module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToWeakSerre
public import StacksFrontier.Homology.DerivedComplete.AdicWeakSerreClass
public import StacksFrontier.Homology.DerivedComplete.FilteredCompletionModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived-completion spectral sequence of a filtered complex

Let `I` be a finitely generated ideal of a commutative ring `A` and let `K^•` be a decreasingly
filtered complex of `A`-modules. Derived completion is represented by any left adjoint to the
inclusion of the derived-complete objects into `D(A)`. There is then a filtered complex `M^•`
representing the derived completion of `K^•` whose canonical spectral sequence
([Stacks, Tag 012M]) consists of derived-complete modules from its first page onward, with
`E₁^{p,q} ≅ H^{p+q}((gr^pK^•)^∧)`. If the filtration of `K^•` is finite in each degree, that
spectral sequence is bounded and converges to the cohomology of `(K^•)^∧`.

## Main results

* `AdicFilteredCompletion.exists_derivedCompletion_spectralSequence`: [Stacks, Tag 0BKD].

## Implementation notes

The filtered complex is the telescope model `filteredCompletionModel` of
`StacksFrontier.Homology.DerivedComplete.FilteredCompletionModel`, and the spectral sequence is
`CochainComplex.Filtered.spectralSequenceFunctor` applied to it, i.e. the canonical
cycle-boundary spectral sequence of a filtered complex. That its pages are derived complete from
`r = 1` on is the weak Serre property of the derived-complete modules ([Stacks, Tag 091U]) applied
to the first page, whose terms are cohomology modules of derived-complete objects. Boundedness and
convergence are [Stacks, Tag 012W], [Stacks, Tag 012Q] and [Stacks, Tag 012V], recorded by the
stable-cycle and stable-boundary equalities together with the canonical comparison to the
associated graded of the induced filtration on cohomology.

## References

* [The Stacks Project, Tag 0BKD](https://stacks.math.columbia.edu/tag/0BKD)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public noncomputable section

set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AdicFilteredCompletion

attribute [local instance] HasDerivedCategory.standard

section FirstPage

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The first page of the spectral sequence of a filtered complex is the cohomology of the
associated graded.** This is the last clause of
`FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage`, read through the functor
`CochainComplex.Filtered.spectralSequenceFunctor`. -/
@[ega "0 11.2.2" "partial", sga "4 Vbis 2.5.2" "(X)"]
lemma nonempty_firstPage_iso_gradedPiece_homology (M : CochainComplex.Filtered C) (p q : ℤ) :
    Nonempty (((CochainComplex.Filtered.spectralSequenceFunctor.obj M).page 1).X (p, q) ≅
      ((FilteredObject.gr p).obj M).homology (p + q)) :=
  (FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage M
    (CochainComplex.filtrationSubobject M) (fun _ _ => rfl)
    (CochainComplex.filtrationSubobject_antitone M)).choose_spec.2.2 p q (p + q) rfl

end FirstPage

/-- On the spectral sequence of a filtered complex of `A`-modules, if every term of the first
page is isomorphic to a cohomology module of a derived-complete object, then every page from the
first on consists of derived-complete modules ([Stacks, Tag 091U] and the weak Serre
property). -/
private lemma pages_isDerivedCompleteModule
    (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (I : Ideal A) (M : CochainComplex.Filtered (ModuleCat.{v} A))
    (L : ℤ → DerivedCategory (ModuleCat.{v} A)) (hL : ∀ p, IsDerivedComplete I (L p))
    (hgraded : ∀ p q : ℤ, Nonempty
      (((CochainComplex.Filtered.spectralSequenceFunctor.obj M).page 1 (by omega)).X (p, q) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) (p + q)).obj (L p))) :
    ∀ (r p q : ℤ) (hr : 1 ≤ r),
      IsDerivedCompleteModule I
        (((CochainComplex.Filtered.spectralSequenceFunctor.obj M).page r
          (by omega)).X (p, q)) := by
  obtain ⟨hSerre, hiff⟩ :=
    AdicWeakSerre.derivedCompleteModules_isWeakSerreClass_and_homology_iff A I
  let P : ObjectProperty (ModuleCat.{v} A) := fun N => IsDerivedCompleteModule I N
  have : P.IsWeakSerreClass := hSerre
  have h1 : ∀ pq : ℤ × ℤ,
      P (((CochainComplex.Filtered.spectralSequenceFunctor.obj M).page 1 (by omega)).X pq) := by
    rintro ⟨p, q⟩
    obtain ⟨e⟩ := hgraded p q
    exact P.prop_of_iso e.symm ((hiff (L p)).2 (hL p) (p + q))
  exact fun r p q hr =>
    CategoryTheory.SpectralSequence.prop_page_of_le _ P (by omega) h1 r hr (by omega) (p, q)

/-- [Stacks, Tag 0BKD] from a filtered model of the derived completion: once a filtered complex
represents the completion, has completed associated graded pieces and finite degreewise filtration
whenever `K` has, the remaining assertions are [Stacks, Tag 012W]. -/
private lemma derivedCompletion_spectralSequence_of_model
    (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (I : Ideal A) (K : FilteredObject (CochainComplex (ModuleCat.{v} A) ℤ) ℤᵒᵖ)
    (P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)))
    (completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory)
    (M : CochainComplex.Filtered (ModuleCat.{v} A))
    (eTotal : DerivedCategory.Q.obj M.X ≅
      (completion ⋙ P.ι).obj (DerivedCategory.Q.obj K.X))
    (hP : ∀ X, IsDerivedComplete I (P.ι.obj X))
    (hgraded : ∀ p q : ℤ, Nonempty
      (((CochainComplex.Filtered.spectralSequenceFunctor.obj M).page 1 (by omega)).X (p, q) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) (p + q)).obj
          ((completion ⋙ P.ι).obj
            (DerivedCategory.Q.obj ((FilteredObject.gr p).obj K)))))
    (hfinite : K.filtration.IsDegreewiseFinite → M.filtration.IsDegreewiseFinite) :
    ∃ (M : CochainComplex.Filtered (ModuleCat.{v} A))
      (eTotal : DerivedCategory.Q.obj M.X ≅
        (completion ⋙ P.ι).obj (DerivedCategory.Q.obj K.X))
      (eCohomology : ∀ n : ℤ, M.X.homology n ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj
          ((completion ⋙ P.ι).obj (DerivedCategory.Q.obj K.X))),
      let E := CochainComplex.Filtered.spectralSequenceFunctor.obj M
      (∀ (r p q : ℤ) (hr : 1 ≤ r),
        IsDerivedCompleteModule I ((E.page r (by omega)).X (p, q))) ∧
      (∀ p q : ℤ, Nonempty
        ((E.page 1 (by omega)).X (p, q) ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{v} A) (p + q)).obj
            ((completion ⋙ P.ι).obj
              (DerivedCategory.Q.obj ((FilteredObject.gr p).obj K))))) ∧
      (K.filtration.IsDegreewiseFinite →
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧
          M.inducedFiltrationStep n a = ⊤ ∧ M.inducedFiltrationStep n b = ⊥) ∧
        (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
          (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
        (∀ p n : ℤ,
          IsGLB (Set.range fun r : ℕ ↦
              CochainComplex.filtrationSubobject M p n ⊓
                (Subobject.pullback (M.X.d n (n + 1))).obj
                  (CochainComplex.filtrationSubobject M (p + r) (n + 1)) ⊔
                CochainComplex.filtrationSubobject M (p + 1) n)
            (kernelSubobject (M.X.d n (n + 1)) ⊓ CochainComplex.filtrationSubobject M p n ⊔
              CochainComplex.filtrationSubobject M (p + 1) n) ∧
          IsLUB (Set.range fun r : ℕ ↦
              CochainComplex.filtrationSubobject M p n ⊓
                (Subobject.«exists» (M.X.d (n - 1) n)).obj
                  (CochainComplex.filtrationSubobject M (p - r) (n - 1)) ⊔
                CochainComplex.filtrationSubobject M (p + 1) n)
            (imageSubobject (M.X.d (n - 1) n) ⊓ CochainComplex.filtrationSubobject M p n ⊔
              CochainComplex.filtrationSubobject M (p + 1) n)) ∧
        (∀ p n : ℤ,
          let C := (Subobject.pullback (M.X.iCycles n)).obj
            (CochainComplex.filtrationSubobject M p n)
          let N := kernelSubobject (M.X.d n (n + 1)) ⊓
            CochainComplex.filtrationSubobject M p n ⊔
            CochainComplex.filtrationSubobject M (p + 1) n
          let B := imageSubobject (M.X.d (n - 1) n) ⊓
            CochainComplex.filtrationSubobject M p n ⊔
            CochainComplex.filtrationSubobject M (p + 1) n
          ∃ (a : (C : ModuleCat.{v} A) ⟶ (N : ModuleCat.{v} A))
            (b : (C : ModuleCat.{v} A) ⟶ (M.inducedFiltrationStep n p : ModuleCat.{v} A))
            (hFH : M.inducedFiltrationStep n (p + 1) ≤ M.inducedFiltrationStep n p)
            (e : cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) ≅
              cokernel (Subobject.ofLE _ _ hFH)),
            C.arrow ≫ M.X.iCycles n = a ≫ N.arrow ∧
            C.arrow ≫ M.X.homologyπ n =
              b ≫ (M.inducedFiltrationStep n p).arrow ∧
            a ≫ cokernel.π (Subobject.ofLE (B ⊓ N) N inf_le_right) ≫ e.hom =
              b ≫ cokernel.π (Subobject.ofLE _ _ hFH))) :=
  ⟨M, eTotal, fun n => (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} A) n).symm.app
      M.X ≪≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).mapIso eTotal,
    pages_isDerivedCompleteModule A I M _ (fun _ => hP _) hgraded, hgraded,
    fun hK => converges_of_filtrationSubobject_finite M (hfinite hK)⟩

/-- **Stacks 0BKD.** Let `I` be a finitely generated ideal, and let `K^•` be a decreasingly
filtered complex of `A`-modules. There is a filtered representative `M^•` of the derived
completion of `K^•` whose canonical spectral sequence consists of derived-complete modules from
its first page onward and has `E₁^{p,q} ≅ H^{p+q}((gr^pK^•)^∧)`. If the filtration of `K^•` is
finite in each degree, the spectral sequence is bounded and converges canonically to the
cohomology of `(K^•)^∧`. -/
@[stacks 0BKD]
theorem exists_derivedCompletion_spectralSequence
    (A : Type u) [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (I : Ideal A) (hI : I.FG)
    (K : FilteredObject (CochainComplex (ModuleCat.{v} A) ℤ) ℤᵒᵖ) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
      fun L ↦ IsDerivedComplete I L
    ∀ (completion : DerivedCategory (ModuleCat.{v} A) ⥤ P.FullSubcategory),
      (completion ⊣ P.ι) →
    ∃ (M : CochainComplex.Filtered (ModuleCat.{v} A))
      (eTotal : DerivedCategory.Q.obj M.X ≅
        (completion ⋙ P.ι).obj (DerivedCategory.Q.obj K.X))
      (eCohomology : ∀ n : ℤ, M.X.homology n ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) n).obj
          ((completion ⋙ P.ι).obj (DerivedCategory.Q.obj K.X))),
      let E := CochainComplex.Filtered.spectralSequenceFunctor.obj M
      (∀ (r p q : ℤ) (hr : 1 ≤ r),
        IsDerivedCompleteModule I ((E.page r (by omega)).X (p, q))) ∧
      (∀ p q : ℤ, Nonempty
        ((E.page 1 (by omega)).X (p, q) ≅
          (DerivedCategory.homologyFunctor (ModuleCat.{v} A) (p + q)).obj
            ((completion ⋙ P.ι).obj
              (DerivedCategory.Q.obj ((FilteredObject.gr p).obj K))))) ∧
      (K.filtration.IsDegreewiseFinite →
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧
          M.inducedFiltrationStep n a = ⊤ ∧ M.inducedFiltrationStep n b = ⊥) ∧
        (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
          (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
        (∀ p n : ℤ,
          IsGLB (Set.range fun r : ℕ ↦
              CochainComplex.filtrationSubobject M p n ⊓
                (Subobject.pullback (M.X.d n (n + 1))).obj
                  (CochainComplex.filtrationSubobject M (p + r) (n + 1)) ⊔
                CochainComplex.filtrationSubobject M (p + 1) n)
            (kernelSubobject (M.X.d n (n + 1)) ⊓ CochainComplex.filtrationSubobject M p n ⊔
              CochainComplex.filtrationSubobject M (p + 1) n) ∧
          IsLUB (Set.range fun r : ℕ ↦
              CochainComplex.filtrationSubobject M p n ⊓
                (Subobject.«exists» (M.X.d (n - 1) n)).obj
                  (CochainComplex.filtrationSubobject M (p - r) (n - 1)) ⊔
                CochainComplex.filtrationSubobject M (p + 1) n)
            (imageSubobject (M.X.d (n - 1) n) ⊓ CochainComplex.filtrationSubobject M p n ⊔
              CochainComplex.filtrationSubobject M (p + 1) n)) ∧
        (∀ p n : ℤ,
          let C := (Subobject.pullback (M.X.iCycles n)).obj
            (CochainComplex.filtrationSubobject M p n)
          let N := kernelSubobject (M.X.d n (n + 1)) ⊓
            CochainComplex.filtrationSubobject M p n ⊔
            CochainComplex.filtrationSubobject M (p + 1) n
          let B := imageSubobject (M.X.d (n - 1) n) ⊓
            CochainComplex.filtrationSubobject M p n ⊔
            CochainComplex.filtrationSubobject M (p + 1) n
          ∃ (a : (C : ModuleCat.{v} A) ⟶ (N : ModuleCat.{v} A))
            (b : (C : ModuleCat.{v} A) ⟶ (M.inducedFiltrationStep n p : ModuleCat.{v} A))
            (hFH : M.inducedFiltrationStep n (p + 1) ≤ M.inducedFiltrationStep n p)
            (e : cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) ≅
              cokernel (Subobject.ofLE _ _ hFH)),
            C.arrow ≫ M.X.iCycles n = a ≫ N.arrow ∧
            C.arrow ≫ M.X.homologyπ n =
              b ≫ (M.inducedFiltrationStep n p).arrow ∧
            a ≫ cokernel.π (Subobject.ofLE (B ⊓ N) N inf_le_right) ≫ e.hom =
              b ≫ cokernel.π (Subobject.ofLE _ _ hFH))) := by
  obtain ⟨r, g, rfl⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  intro P completion adj
  obtain ⟨eTotal⟩ := nonempty_iso_completion_homModel g K.X completion adj
  refine derivedCompletion_spectralSequence_of_model A _ K P completion
    (filteredCompletionModel g K) eTotal (fun X => X.property) (fun p q => ?_)
    (filteredCompletionModel_isDegreewiseFinite g K)
  obtain ⟨e₁⟩ := nonempty_firstPage_iso_gradedPiece_homology (filteredCompletionModel g K) p q
  obtain ⟨eg⟩ := homModel_graded_iso g K p
  obtain ⟨ec⟩ := nonempty_iso_completion_homModel g
    ((FilteredObject.gr p).obj K) completion adj
  exact ⟨e₁ ≪≫ (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} A) (p + q)).symm.app _ ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{v} A) (p + q)).mapIso
      (DerivedCategory.Q.mapIso eg ≪≫ ec)⟩

end AdicFilteredCompletion

end
