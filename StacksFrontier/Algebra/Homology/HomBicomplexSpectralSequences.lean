module

public import StacksFrontier.Algebra.Homology.HomBicomplexCohomology
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToMap
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The two spectral sequences converging to `Ext` out of a complex

Let `C` be an abelian category with enough injectives, let `K` be a bounded above cochain complex
of `C` and let `F` be an object of `C`. Choosing an injective resolution `F → I^•` and forming the
Hom bicomplex `Hom_C(K⁻ᵖ, Iᑫ)`, whose diagonals are finite, the two filtrations of its total
complex produce two cohomological spectral sequences, both converging to the cohomology of that
total complex, which is `Ext^*(K^•, F)`:

* the filtration by the *second* coordinate gives
  `E₂^{i,j} = Extⁱ(H⁻ʲ(K^•), F) ⇒ Extⁱ⁺ʲ(K^•, F)`;
* the filtration by the *first* coordinate gives
  `E₁^{i,j} = Extʲ(K⁻ⁱ, F) ⇒ Extⁱ⁺ʲ(K^•, F)`.

This is [Stacks 07AA], stated for an arbitrary abelian category with enough injectives rather
than only for the category of modules on a ringed site: the latter is an instance, being a
Grothendieck abelian category and hence having enough injectives ([Stacks 01DU]).

## Main results

* `CochainComplex.exists_cohomologyExtSpectralSequence`: the hyper-`Ext` spectral sequence, with
  second page the `Ext` groups of the cohomology objects of `K^•`.
* `CochainComplex.exists_termwiseExtSpectralSequence`: the termwise `Ext` spectral sequence, with
  first page the `Ext` groups of the terms of `K^•`.

## Implementation notes

Convergence is expressed by `CategoryTheory.SpectralSequence.AbutsTo`: the spectral sequence has
an infinity page everywhere, and the terms of the infinity page are the graded pieces of a finite
decreasing filtration of each `Extⁿ(K^•, F)`. For the spectral sequence of a filtered complex with
degreewise finite filtration this is `CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite`, and
the two filtrations of the total complex of a diagonally finite double complex are degreewise
finite by `HomologicalComplex₂.isDegreewiseFinite_totalFiltration₁` and `...₂`.

Boundedness above of `K^•` is the object property `CochainComplex.minus`, an existential over a
bound rather than a bound carried as data; the resolution
`CochainComplex.injectiveResolutionSingle` carries its own boundedness below, so the diagonals of
the Hom bicomplex are finite.

**Universes.** The pages of the spectral sequence of the Hom bicomplex are `Hom` groups of `C`,
hence objects of `AddCommGrpCat.{v}` for `Category.{v} C`, while the `Ext` groups live in the
universe of the `Hom` groups of the derived category. The two are unrelated, so both statements
are made in `AddCommGrpCat.{max u v}` for `[HasDerivedCategory.{max u v} C]`, the spectral
sequence being transported there by `CategoryTheory.SpectralSequence.ulift` and the abutment by
`CategoryTheory.SpectralSequence.AbutsTo.map`. For `C` the category of modules on a ringed site
with objects in `Type (u + 1)` and `Category.{u}`, `HasDerivedCategory.standard` is the instance
at `max u (u + 1) = u + 1`, which is where its `Ext` groups live.

The identifications of the pages are the ones of
`StacksFrontier/Algebra/Homology/HomBicomplexCohomology.lean`, read through [Stacks 0130]: the first
page of the spectral sequence of the first filtration is the cohomology of a row of the bicomplex,
and the second page of the spectral sequence of the second filtration is the iterated cohomology.

## References

* [Stacks, Tag 07AA](https://stacks.math.columbia.edu/tag/07AA)
* [Stacks, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{max u v} C]

/-- Abutment of a spectral sequence to the cohomology of the total Hom bicomplex gives, after
transport to `AddCommGrpCat.{max u v}` and a shift of the starting page, abutment to `Ext`. -/
private theorem abutsTo_ext_shiftStart (K : CochainComplex C ℤ) (hK : CochainComplex.minus C K)
    (F : C) {E : CohomologicalSpectralSequence AddCommGrpCat.{v} 0} {r₁ : ℤ} (h : 0 ≤ r₁)
    (hAbuts : SpectralSequence.AbutsTo E (fun n ↦
      (homBicomplexTotal K (injectiveResolutionSingle F).cocomplex hK
        (injectiveResolutionSingle F).boundedBelow).homology n)) :
    SpectralSequence.AbutsTo ((E.map AddCommGrpCat.uliftFunctor.{max u v, v}).shiftStart h)
      (fun n ↦ AddCommGrpCat.of
        (DerivedCategory.Ext (DerivedCategory.Q.obj K)
          ((DerivedCategory.singleFunctor C 0).obj F) n)) :=
  ((hAbuts.map AddCommGrpCat.uliftFunctor.{max u v, v}).of_iso (fun n ↦
    (AddEquiv.ulift.trans (homBicomplexTotalHomologyAddEquivExt K F hK n)).toAddCommGrpIso
    )).shiftStart h

/-- **Stacks Project, Tag 07AA, the hyper-`Ext` spectral sequence.** Let `C` be an abelian
category with enough injectives, let `K^•` be a bounded above complex of `C` and let `F` be an
object of `C`. There is a cohomological spectral sequence, starting on page two, with
`E₂^{i,j} = Extⁱ(H⁻ʲ(K^•), F)`, abutting to `Extⁱ⁺ʲ(K^•, F)`.

It is the spectral sequence of the total complex of the Hom bicomplex `Hom_C(K⁻ᵖ, Iᑫ)` filtered
by the second coordinate, for `I^•` an injective resolution of `F`. -/
@[stacks 07AA "cohomology_ext"]
public theorem exists_cohomologyExtSpectralSequence (K : CochainComplex C ℤ)
    (hK : CochainComplex.minus C K) (F : C) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{max u v} 2,
      (∀ i j : ℤ, Nonempty
        ((E.page 2).X (i, j) ≅
          AddCommGrpCat.of (Abelian.zExt (K.homology (-j)) F i))) ∧
      SpectralSequence.AbutsTo E (fun n ↦
        AddCommGrpCat.of
          (DerivedCategory.Ext (DerivedCategory.Q.obj K)
            ((DerivedCategory.singleFunctor C 0).obj F) n)) := by
  classical
  let I := (injectiveResolutionSingle F).cocomplex
  let B := homBicomplex K I
  have hfin := homBicomplex_finite_diagonals K I hK (injectiveResolutionSingle F).boundedBelow
  have hf := HomBicomplex.isInjectiveResolution_injectiveResolutionSingle F
  let : B.HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite B (ComplexShape.up ℤ) hfin
  let U := AddCommGrpCat.uliftFunctor.{max u v, v}
  let E := CochainComplex.filteredSpectralSequence B.totalFiltration₂
  obtain ⟨e, -, hδ, -, -, -⟩ := CochainComplex.exists_iso_spectralSequence_page
    B.totalFiltration₂ _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  obtain ⟨-, -, hE2⟩ := B.exists_iso_pages_totalFiltration₂ _ (fun _ _ => rfl) _
    (fun _ _ _ => rfl) _ (fun _ _ _ => rfl) E e hδ
  have hAbuts := CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite'
    B.totalFiltration₂ (B.isDegreewiseFinite_totalFiltration₂ hfin)
  refine ⟨(E.map U).shiftStart zero_le_two, fun i j => ?_, ?_⟩
  · obtain ⟨h₂⟩ := hE2 i j
    exact ⟨U.mapIso h₂ ≪≫ (AddEquiv.ulift.trans
      (HomBicomplex.homologyHomologyAddEquivZExt K I F hf i j)).toAddCommGrpIso⟩
  · exact abutsTo_ext_shiftStart K hK F zero_le_two hAbuts

/-- **Stacks Project, Tag 07AA, the termwise `Ext` spectral sequence.** Let `C` be an abelian
category with enough injectives, let `K^•` be a bounded above complex of `C` and let `F` be an
object of `C`. There is a cohomological spectral sequence, starting on page one, with
`E₁^{i,j} = Extʲ(K⁻ⁱ, F)`, abutting to `Extⁱ⁺ʲ(K^•, F)`.

It is the spectral sequence of the total complex of the Hom bicomplex `Hom_C(K⁻ᵖ, Iᑫ)` filtered
by the first coordinate, for `I^•` an injective resolution of `F`. -/
@[stacks 07AA "termwise_ext"]
public theorem exists_termwiseExtSpectralSequence (K : CochainComplex C ℤ)
    (hK : CochainComplex.minus C K) (F : C) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{max u v} 1,
      (∀ i j : ℤ, Nonempty
        ((E.page 1).X (i, j) ≅ AddCommGrpCat.of (Abelian.zExt (K.X (-i)) F j))) ∧
      SpectralSequence.AbutsTo E (fun n ↦
        AddCommGrpCat.of
          (DerivedCategory.Ext (DerivedCategory.Q.obj K)
            ((DerivedCategory.singleFunctor C 0).obj F) n)) := by
  classical
  let I := (injectiveResolutionSingle F).cocomplex
  let B := homBicomplex K I
  have hfin := homBicomplex_finite_diagonals K I hK (injectiveResolutionSingle F).boundedBelow
  have hf := HomBicomplex.isInjectiveResolution_injectiveResolutionSingle F
  let : B.HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite B (ComplexShape.up ℤ) hfin
  let U := AddCommGrpCat.uliftFunctor.{max u v, v}
  let E := CochainComplex.filteredSpectralSequence B.totalFiltration₁
  obtain ⟨e, -, hδ, -, -, -⟩ := CochainComplex.exists_iso_spectralSequence_page
    B.totalFiltration₁ _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  obtain ⟨-, ⟨β, -⟩, -⟩ := B.exists_iso_pages_totalFiltration₁ _ (fun _ _ => rfl) _
    (fun _ _ _ => rfl) _ (fun _ _ _ => rfl) E e hδ
  have hAbuts := CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite'
    B.totalFiltration₁ (B.isDegreewiseFinite_totalFiltration₁ hfin)
  refine ⟨(E.map U).shiftStart zero_le_one, fun i j => ?_, ?_⟩
  · exact ⟨U.mapIso (β i j) ≪≫ (AddEquiv.ulift.trans
      (HomBicomplex.rowHomologyAddEquivZExt K I F hf i j)).toAddCommGrpIso⟩
  · exact abutsTo_ext_shiftStart K hK F zero_le_one hAbuts

end CochainComplex

end
