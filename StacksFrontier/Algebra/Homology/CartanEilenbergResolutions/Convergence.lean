module

public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.SpectralSequence
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.SpectralSequence.Boundedness
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex.FiniteConvergence
import all StacksFrontier.Algebra.Homology.CartanEilenbergResolutions.SpectralSequence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two spectral sequences of `F` applied to a Cartan-Eilenberg resolution

Let `F : 𝒜 ⥤ ℬ` be an additive functor of abelian categories, `𝒜` having enough injectives, let
`K^•` be a bounded below complex of `𝒜` and let `I^{•,•}` be a Cartan-Eilenberg resolution of
`K^•` ([Stacks, Tag 015H]). The double complex `L = F(I^{•,•})` has two spectral sequences
`('E_r, 'd_r)_{r ≥ 0}` and `(''E_r, ''d_r)_{r ≥ 0}` ([Stacks, Tag 0130]): those of `Tot(L)`
filtered by the first and by the second coordinate. This file proves [Stacks, Tag 015J] for them:
```
'E_1^{p,q} = R^qF(K^p),    ''E_2^{p,q} = R^pF(H^q(K^•)),
```
both spectral sequences are bounded, converge to `H^*(Tot(L)) = H^*(RF(K^•))`, and the filtrations
they induce on each `H^n(RF(K^•))` are finite.

## Main results

* `CochainComplex.CartanEilenbergResolution.spectralSequences_rightDerivedPlus`: [Stacks, Tag 015J].

## Implementation notes

The spectral sequences are the canonical ones of the filtered complexes
`L.totalFiltration₁` and `L.totalFiltration₂`, `CochainComplex.Filtered.spectralSequenceFunctor`
([Stacks, Tag 012M]); their pages are the subquotients `Z_r^{p,q}/B_r^{p,q}` of `Tot(L)`.

Convergence is stated in two forms. `HomologicalComplex₂.ConvergesToTotalHomology₁` and `...₂`
are convergence to `H^*(Tot(L))` in the sense of [Stacks, Tag 012U] (regular, weakly convergent,
induced filtrations separated, exhaustive and complete); the induced filtration of each
`H^n(Tot(L))` is shown to reach `⊤` and `⊥`. `CategoryTheory.SpectralSequence.AbutsTo` with
abutment `n ↦ H^n(RF(K^•))` gives, on each `H^n(RF(K^•))` itself, a finite decreasing filtration
whose graded pieces are the terms `E_∞^{p, n - p}`; it is the induced filtration of
`H^n(Tot(L))` carried along an isomorphism `H^n(Tot(L)) ≅ H^n(RF(K^•))`, which is also stated.

As in the module `StacksFrontier.Algebra.Homology.CartanEilenbergResolutions`, `F` is only assumed
additive: `R^qF` is defined for every additive functor, and left exactness of `F` is used in the
source only to identify `R^0F` with `F`, which the statement does not involve.

## References

* [Stacks, Tag 015J]
* [Stacks, Tag 0130]
* [Stacks, Tag 0132]
* [Stacks, Tag 0133]
* [Stacks, Tag 012U]
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex CochainComplex.Filtered

namespace StacksDraft.CartanEilenbergResolutions

universe w w' v v' u u'

/-- **The spectral sequences of a Cartan-Eilenberg resolution** ([Stacks, Tag 015J]). Let
`F : 𝒜 ⥤ ℬ` be an additive functor of abelian categories, `𝒜` having enough injectives, let `K^•`
be a bounded below complex of `𝒜`, let `I^{•,•}` be a Cartan-Eilenberg resolution of `K^•` and let
`('E_r, 'd_r)_{r ≥ 0}` and `(''E_r, ''d_r)_{r ≥ 0}` be the two spectral sequences of the double
complex `L = F(I^{•,•})`, those of `Tot(L)` filtered by the first and by the second coordinate.
Then
* `'E_1^{p,q} ≅ R^qF(K^p)`, the differential `'d_1^{p,q}` being `R^qF(d_K^p)`;
* `''E_1^{p,q} ≅ F(H^q_I(I^{•,•})^p)`, the differential `''d_1^{p,q}` being `(-1)^q` times `F`
  of the differential of `H^q_I(I^{•,•})`, an injective resolution of `H^q(K^•)`;
* `''E_2^{p,q} ≅ R^pF(H^q(K^•))`;
* both spectral sequences are bounded;
* both converge to `H^*(Tot(L))` in the sense of [Stacks, Tag 012U], and the filtrations they
  induce on each `H^n(Tot(L))` are finite;
* `H^n(Tot(L)) ≅ H^n(RF(K^•))`, and each spectral sequence abuts to `H^*(RF(K^•))`: every
  `H^n(RF(K^•))` carries a finite decreasing filtration whose graded pieces are the terms
  `E_∞^{p, n - p}`. -/
@[stacks 015J "the two spectral sequences are those of `Tot(F(I))` filtered by the first and the
  second coordinate; convergence to `H^*(RF(K^•))` is stated as convergence to `H^*(Tot(F(I)))`
  in the sense of 012U, with finite induced filtrations, together with an isomorphism
  `H^n(Tot(F(I))) ≅ H^n(RF(K^•))` and the abutment of both spectral sequences to `H^*(RF(K^•))`;
  `F` is only assumed additive"]
public theorem _root_.CochainComplex.CartanEilenbergResolution.spectralSequences_rightDerivedPlus
    {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B] (F : A ⥤ B) [F.Additive]
    [EnoughInjectives A] {K : CochainComplex A ℤ} (hK : CochainComplex.plus A K)
    (I : K.CartanEilenbergResolution)
    [HomologicalComplex₂.HasTotal
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.bicomplex) (ComplexShape.up ℤ)] :
    let L : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.bicomplex
    let E₁ := spectralSequenceFunctor.obj L.totalFiltration₁
    let E₂ := spectralSequenceFunctor.obj L.totalFiltration₂
    let H : ℤ → B := fun n => (DerivedCategory.Plus.homologyFunctor B n).obj
      (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj ⟨K, hK⟩))
    (∃ α : ∀ p q : ℤ, (E₁.page 1 zero_le_one).X (p, q) ≅ (F.rightDerivedPlus q).obj (K.X p),
      ∀ p q : ℤ, (E₁.page 1 zero_le_one).d (p, q) (p + 1, q) ≫ (α (p + 1) q).hom =
        (α p q).hom ≫ (F.rightDerivedPlus q).map (K.d p (p + 1))) ∧
    (∃ β : ∀ p q : ℤ, (E₂.page 1 zero_le_one).X (p, q) ≅ F.obj ((I.bicomplex.homology q).X p),
      ∀ p q : ℤ, (E₂.page 1 zero_le_one).d (p, q) (p + 1, q) ≫ (β (p + 1) q).hom =
        (β p q).hom ≫ (q.negOnePow • F.map ((I.bicomplex.homology q).d p (p + 1)))) ∧
    Nonempty (∀ p q : ℤ,
      (E₂.page 2 zero_le_two).X (p, q) ≅ (F.rightDerivedPlus p).obj (K.homology q)) ∧
    IsBounded E₁ ∧ IsBounded E₂ ∧
    L.ConvergesToTotalHomology₁ ∧ L.ConvergesToTotalHomology₂ ∧
    (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ inducedFiltrationStep L.totalFiltration₁ n a = ⊤ ∧
      inducedFiltrationStep L.totalFiltration₁ n b = ⊥) ∧
    (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ inducedFiltrationStep L.totalFiltration₂ n a = ⊤ ∧
      inducedFiltrationStep L.totalFiltration₂ n b = ⊥) ∧
    Nonempty (∀ n : ℤ, (L.total (ComplexShape.up ℤ)).homology n ≅ H n) ∧
    SpectralSequence.AbutsTo E₁ H ∧ SpectralSequence.AbutsTo E₂ H := by
  intro L E₁ E₂ H
  obtain ⟨i₀, hq', hp'⟩ := exists_bounds_bicomplex I
  have hq : ∀ p q, q < 0 → IsZero ((L.X p).X q) := fun p q h => F.map_isZero (hq' p q h)
  have hp : ∀ p, p < i₀ → IsZero (L.X p) := fun p h =>
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map_isZero (hp' p h)
  have hfin : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((L.X pq.1).X pq.2)}.Finite :=
    StacksDraft.TotalComplexQuasiIso.finite_not_isZero_of_bounded L i₀ hq hp
  have hT₁ := L.isDegreewiseFinite_totalFiltration₁ hfin
  have hT₂ := L.isDegreewiseFinite_totalFiltration₂ hfin
  obtain ⟨e₁, hδ₁⟩ := exists_pageIso_d L.totalFiltration₁
  obtain ⟨e₂, hδ₂⟩ := exists_pageIso_d L.totalFiltration₂
  obtain ⟨-, ⟨β₁, hβ₁⟩, -⟩ := L.exists_iso_pages_totalFiltration₁
    (CochainComplex.filtrationSubobject L.totalFiltration₁) (fun _ _ => rfl)
    (FilteredComplexSpectralSequence.cycles L.totalFiltration₁.X
      (CochainComplex.filtrationSubobject L.totalFiltration₁)) (fun _ _ _ => rfl)
    (FilteredComplexSpectralSequence.boundaries L.totalFiltration₁.X
      (CochainComplex.filtrationSubobject L.totalFiltration₁)) (fun _ _ _ => rfl) E₁ e₁ hδ₁
  obtain ⟨-, ⟨β₂, hβ₂⟩, hE₂⟩ := L.exists_iso_pages_totalFiltration₂
    (CochainComplex.filtrationSubobject L.totalFiltration₂) (fun _ _ => rfl)
    (FilteredComplexSpectralSequence.cycles L.totalFiltration₂.X
      (CochainComplex.filtrationSubobject L.totalFiltration₂)) (fun _ _ _ => rfl)
    (FilteredComplexSpectralSequence.boundaries L.totalFiltration₂.X
      (CochainComplex.filtrationSubobject L.totalFiltration₂)) (fun _ _ _ => rfl) E₂ e₂ hδ₂
  obtain ⟨c₁, c₁', -, -, -⟩ := CochainComplex.isBounded_and_converges_of_isDegreewiseFinite
    L.totalFiltration₁ hT₁ (CochainComplex.filtrationSubobject L.totalFiltration₁) (fun _ _ => rfl)
    (FilteredComplexSpectralSequence.cycles L.totalFiltration₁.X
      (CochainComplex.filtrationSubobject L.totalFiltration₁)) (fun _ _ _ => rfl)
    (FilteredComplexSpectralSequence.boundaries L.totalFiltration₁.X
      (CochainComplex.filtrationSubobject L.totalFiltration₁)) (fun _ _ _ => rfl)
    (fun n p => inducedFiltrationStep L.totalFiltration₁ n p) (fun _ _ => rfl) E₁ e₁
  obtain ⟨c₂, c₂', -, -, -⟩ := CochainComplex.isBounded_and_converges_of_isDegreewiseFinite
    L.totalFiltration₂ hT₂ (CochainComplex.filtrationSubobject L.totalFiltration₂) (fun _ _ => rfl)
    (FilteredComplexSpectralSequence.cycles L.totalFiltration₂.X
      (CochainComplex.filtrationSubobject L.totalFiltration₂)) (fun _ _ _ => rfl)
    (FilteredComplexSpectralSequence.boundaries L.totalFiltration₂.X
      (CochainComplex.filtrationSubobject L.totalFiltration₂)) (fun _ _ _ => rfl)
    (fun n p => inducedFiltrationStep L.totalFiltration₂ n p) (fun _ _ => rfl) E₂ e₂
  choose ec hec using fun q => exists_homologyIso_column F I q
  let eh : ∀ q : ℤ, L.homology q ≅
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.bicomplex.homology q) :=
    fun q => (nonempty_mapHomologyIso_bicomplex F I q).some
  have eH : ∀ n : ℤ, Nonempty ((L.total (ComplexShape.up ℤ)).homology n ≅ H n) :=
    fun n => nonempty_homologyIso_total F I hK n
  refine ⟨⟨fun p q => β₁ p q ≪≫ ec q p, fun p q => ?_⟩,
    ⟨fun p q => β₂ p q ≪≫ (HomologicalComplex.eval B (ComplexShape.up ℤ) p).mapIso (eh q),
      fun p q => ?_⟩,
    ⟨fun p q => (hE₂ p q).some ≪≫ (nonempty_homologyIso_homology F I p q).some⟩,
    c₁, c₂, L.convergesToTotalHomology₁_of_finite hfin, L.convergesToTotalHomology₂_of_finite hfin,
    c₁', c₂', ⟨fun n => (eH n).some⟩,
    (abutsTo_of_isDegreewiseFinite' L.totalFiltration₁ hT₁).of_nonempty_iso eH,
    (abutsTo_of_isDegreewiseFinite' L.totalFiltration₂ hT₂).of_nonempty_iso eH⟩
  · rw [Iso.trans_hom, Iso.trans_hom, reassoc_of% (hβ₁ p q), hec q p (p + 1), Category.assoc]
  · have hc := (eh q).hom.comm p (p + 1)
    simp only [Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.eval_map,
      reassoc_of% (hβ₂ p q), Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul]
    rw [← hc]
    rfl

end StacksDraft.CartanEilenbergResolutions

end
