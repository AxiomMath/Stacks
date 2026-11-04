module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplexNaturality
public import StacksFrontier.Algebra.Homology.SpectralSequence.FirstQuadrantDoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.ProductDoubleComplex
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SectionsComplex

/-!
# The cohomology spectral sequence of a simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE), with total site `C_total` and component
sites `C_n`, and let `Z^•` be a cochain complex of abelian sheaves on `C_total`. Taking the
canonical complex of sections of Stacks 0D77 degreewise produces the double complex

```
A^{q,p} = Γ(C_p, Z^q_p)
```

with the degree in `Z^•` outer and the simplicial degree inner, whose horizontal arrows are the
differentials of Stacks 0D77 and whose vertical arrows come from the differentials of `Z^•`.
This file constructs that double complex and the spectral sequence of its filtration by the
second (simplicial) coordinate, identifies its first page as the cohomology of the columns,

```
E_1^{p,q} = H^q(Γ(C_p, Z^•_p)),  d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q},
```

and shows that for a complex concentrated in non-negative degrees it abuts to the cohomology of
the total complex.

Stacks 0H0V replaces the direct-sum totalization by the product totalization `Tot_π`, which is
what makes the construction work for a `Z^•` that is not bounded below. The last section builds
the same double complex in the opposite orientation, `A^{p,q} = Γ(C_p, Z^q_p)` with the
simplicial degree outer, and the spectral sequence of the filtration
`F^i Tot_π^n = ∏_{p + q = n, p ≥ i} Γ(C_p, Z^q_p)`; its zeroth page is `Γ(C_p, Z^q_p)`. No
boundedness hypothesis appears, and no convergence is asserted, as in the source.

Names without a namespace are in `CategoryTheory.SimplicialSiteSituation`.

## Main definitions

* `cechSectionsComplexZ`: the complex of Stacks 0D77 with its simplicial degree extended by zero
  from `ℕ` to `ℤ`.
* `sectionsDoubleComplexFunctor`: the double complex `A^{q,p} = Γ(C_p, Z^q_p)` of a cochain
  complex `Z^•` of abelian sheaves on the total site.
* `sectionsSpectralSequence`: the spectral sequence of the filtration of the total complex by the
  simplicial coordinate.
* `sectionsProductDoubleComplex` and `sectionsProductTotal`: the double complex
  `A^{p,q} = Γ(C_p, Z^q_p)` with the simplicial degree outer, and its product totalization.
* `sectionsProductSpectralSequence`: **Stacks 0H0V**, the spectral sequence of the filtration of
  the product totalization by the simplicial coordinate, for an arbitrary `Z^•`.

## Main results

* `pageOneIsoComponentSections`: the first page is the cohomology of the columns,
  `E_1^{p,q} ≅ H^q(Γ(C_p, Z^•_p))` for a non-negative simplicial degree `p`.
* `pageOneIsoColumnHomology_hom_d`: that identification carries
  `d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}` to the sign `(-1)^q` times the map induced on `H^q` by
  the differential of the complex of Stacks 0D77.
* `isZero_sectionsDoubleComplex_X_X`: the double complex vanishes outside the first quadrant, for
  a complex of sheaves concentrated in non-negative degrees.
* `sectionsSpectralSequence_abutsTo_total`: the spectral sequence abuts to the cohomology of the
  total complex of `A^{•,•}`.
* `sectionsProductSpectralSequenceZeroPageIso` and `sectionsProductSpectralSequenceOnePageIso`:
  `E_0^{p,q} ≅ Γ(C_p, Z^q_p)` and `E_1^{p,q} ≅ H^q(Γ(C_p, Z^•_p))` for the spectral sequence of
  Stacks 0H0V.

## Implementation notes

The index orientation is forced. The spectral sequence of the filtration by the second
coordinate has `E_1^{p,q} = H^q(A^{•,p})`, homology in the *outer* index of the column with
inner index `p`, so for the first page to be the cohomology of the sections over `C_p` the
degree in `Z^•` has to be the outer one. This is the orientation of
`Stacks.Topology.Simplicial.cohomologySpectralSequence` (Stacks 09W6).

The product totalization is what removes the boundedness hypothesis: for an unbounded `Z^•` the
diagonals of `A^{•,•}` are infinite, and the direct-sum totalization differs from `Tot_π`.

## Relation to Stacks 09WJ and 0H0V

Stacks 09WJ asserts, for `K` in `D^+(C_total)`, a spectral sequence with
`E_1^{p,q} = H^q(C_p, K_p)` converging to `H^{p+q}(C_total, K)`, functorial in `K`. Stacks 0H0V
keeps its assumptions except the boundedness of `K`, and asserts no convergence. This file
provides the double complex of their proofs, its spectral sequences and their first pages
`H^q(Γ(C_p, Z^•_p))`; it carries no `@[stacks 09WJ]` attribute, and its `@[stacks 0H0V]`
attributes cover the construction, the filtration `F^i Tot_π^n = ∏_{p + q = n, p ≥ i} A^{p,q}`,
and the pages `E_0` and `E_1`. Three identifications of the source are not made here:

* `H^q(Γ(C_p, I^•_p)) ≅ H^q(C_p, K_p)` for `I^•` a complex of injectives representing `K`, whose
  inputs are `injective_componentRestriction` (Stacks 09WH) and the exactness of `restrictAb`,
  from Stacks 09WG (7);
* `H^n(Tot(A^{•,•})) ≅ H^n(C_total, K)`: for bounded `K` this is Stacks 0133
  (`CochainComplex.quasiIso_total_of_resolution_flip`, or `CochainComplex.comparisonMapP`)
  applied to the augmentation `cechSectionsAugmentation`, whose rows are exact by
  `cechSectionsComplex_exactAt_of_injective` and `cechSectionsComplex_shortComplexZero_exact`;
  for `I^•` K-injective, `Tot_π(A^{•,•})` is the Hom-complex out of the integral resolution of
  Stacks 09WI, which computes `R Hom(Z, K) = RΓ(C_total, K)`;
* the functoriality in `K`, which goes through `HomologicalComplex₂.FilteredHomotopy₂` and
  `HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂`, a bounded-below
  injective resolution being functorial only up to homotopy.

For an abelian sheaf `F` on the total site, that is for `K = F[0]`, the three are
`rightDerivedComponentSectionsNatIso`, `totalCohomologyIsoTotalComplexHomology` and the
functoriality of `cohomologySpectralSequence`, in
`StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequenceTagComponent.lean`,
`StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequenceTagTotal.lean` and
`StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequenceTagSheaf.lean`; the last
carries the `@[stacks 09WJ]` attributes.

## References

* [Stacks Project, Tag 0H0V](https://stacks.math.columbia.edu/tag/0H0V)
* [Stacks Project, Tag 09WJ](https://stacks.math.columbia.edu/tag/09WJ)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D77](https://stacks.math.columbia.edu/tag/0D77)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- Global sections on the total site are additive, being a right adjoint. -/
instance additive_sheafΓ_total : (Sheaf.Γ S.totalTopology Ab.{u}).Additive :=
  haveI : PreservesLimitsOfSize.{0, 0} (Sheaf.Γ S.totalTopology Ab.{u}) :=
    (constantSheafΓAdj S.totalTopology Ab.{u}).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- Global sections on a component site are additive, being a right adjoint. -/
instance additive_sheafΓ_component (n : SimplexCategory) :
    (Sheaf.Γ (S.componentTopology n) Ab.{u}).Additive :=
  haveI : PreservesLimitsOfSize.{0, 0} (Sheaf.Γ (S.componentTopology n) Ab.{u}) :=
    (constantSheafΓAdj (S.componentTopology n) Ab.{u}).rightAdjoint_preservesLimits
  Functor.additive_of_preserves_binary_products _

/-- The complex of Stacks 0D77 is additive in the sheaf, being degreewise `Γ(C_n, (-)_n)`. -/
instance additive_cechSectionsComplex : (S.cechSectionsComplex).Additive where
  map_add := HomologicalComplex.hom_ext _ _ fun n => (S.componentSectionsFunctor ⦋n⦌).map_add

/-- The complex `Γ(C_0, F_0) → Γ(C_1, F_1) → …` of Stacks 0D77, with its simplicial degree
extended by zero from `ℕ` to `ℤ`. -/
abbrev cechSectionsComplexZ : Sheaf S.totalTopology Ab.{u} ⥤ CochainComplex Ab.{u} ℤ :=
  S.cechSectionsComplex ⋙ ComplexShape.embeddingUpNat.extendFunctor Ab.{u}

/-- The complex of Stacks 0D77, extended by zero to `ℤ`, is additive in the sheaf. -/
instance additive_cechSectionsComplexZ : (S.cechSectionsComplexZ).Additive := by
  dsimp only [cechSectionsComplexZ]; infer_instance

/-- **The double complex `A^{q,p} = Γ(C_p, Z^q_p)`** of a cochain complex `Z^•` of abelian
sheaves on the total site of a simplicial-site situation: the complex of Stacks 0D77 applied
degreewise, with the degree in `Z^•` outer and the simplicial degree inner. -/
abbrev sectionsDoubleComplexFunctor :
    CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ ⥤
      HomologicalComplex₂ Ab.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (S.cechSectionsComplexZ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The double complex `A^{q,p} = Γ(C_p, Z^q_p)` is additive in `Z^•`. -/
instance additive_sectionsDoubleComplexFunctor :
    (S.sectionsDoubleComplexFunctor).Additive := by
  dsimp only [sectionsDoubleComplexFunctor]; infer_instance

/-- The term of the double complex in outer degree `q` and simplicial degree `n` is
`Γ(C_n, Z^q_n)`. -/
def sectionsDoubleComplexXXIso
    (Z : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ) (q : ℤ) (n : ℕ) :
    (((S.sectionsDoubleComplexFunctor).obj Z).X q).X (n : ℤ) ≅
      (S.componentSectionsFunctor ⦋n⦌).obj (Z.X q) :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat (i := n) rfl

/-- Evaluating the complex of Stacks 0D77, extended by zero, in a non-negative simplicial degree
`n` gives `Γ(C_n, (-)_n)`. -/
def cechSectionsComplexZCompEval (n : ℕ) :
    S.cechSectionsComplexZ ⋙
        HomologicalComplex.eval Ab.{u} (ComplexShape.up ℤ) (n : ℤ) ≅
      S.componentSectionsFunctor ⦋n⦌ :=
  Functor.isoWhiskerLeft (S.cechSectionsComplex)
    (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso Ab.{u} (i := n) rfl)

/-! ### The spectral sequence of the double complex -/

section SpectralSequence

variable (Z : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)

/-- The double complex `A^{q,p} = Γ(C_p, Z^q_p)` of a cochain complex `Z^•` of abelian sheaves on
the total site. -/
abbrev sectionsDoubleComplex :
    HomologicalComplex₂ Ab.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (S.sectionsDoubleComplexFunctor).obj Z

/-- **The spectral sequence of the double complex `A^{q,p} = Γ(C_p, Z^q_p)`**: the spectral
sequence of the filtration of its total complex by the second, simplicial, coordinate. -/
abbrev sectionsSpectralSequence : CohomologicalSpectralSequence Ab.{u} 0 :=
  (S.sectionsDoubleComplex Z).spectralSequence₂

/-- **The first page of the spectral sequence is the cohomology of the columns**, `E_1^{p,q} =
H^q(A^{•,p})`. This is Stacks 0130 (4) for the double complex `A^{q,p} = Γ(C_p, Z^q_p)`. -/
def pageOneIsoColumnHomology (p q : ℤ) :
    ((S.sectionsSpectralSequence Z).page 1 zero_le_one).X (p, q) ≅
      ((S.sectionsDoubleComplex Z).homology q).X p :=
  HomologicalComplex₂.isoOnePageTotalFiltration₂ (S.sectionsDoubleComplex Z) _
    (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) p q

/-- **The first differential `d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}`.** Under
`pageOneIsoColumnHomology` it is `(-1)^q` times the differential of `H^q(A^{•,•})` in the
simplicial direction. -/
theorem pageOneIsoColumnHomology_hom_d (p p' q : ℤ) (hp' : p' = p + 1) :
    ((S.sectionsSpectralSequence Z).page 1 zero_le_one).d (p, q) (p', q) ≫
        (S.pageOneIsoColumnHomology Z p' q).hom =
      (S.pageOneIsoColumnHomology Z p q).hom ≫
        (q.negOnePow • ((S.sectionsDoubleComplex Z).homology q).d p p') :=
  HomologicalComplex₂.isoOnePageTotalFiltration₂_hom_d (S.sectionsDoubleComplex Z) _
    (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) p p' q hp'

/-- The column of the double complex in a non-negative simplicial degree `n` is the complex of
sections `Γ(C_n, Z^•_n)`, so its `q`-th cohomology is `H^q(Γ(C_n, Z^•_n))`. -/
def columnHomologyIso (n : ℕ) (q : ℤ) :
    ((S.sectionsDoubleComplex Z).homology q).X (n : ℤ) ≅
      (((S.componentSectionsFunctor ⦋n⦌).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z).homology q :=
  (ShortComplex.mapHomologyIso
      (S := (S.sectionsDoubleComplex Z).sc q)
      (HomologicalComplex.eval Ab.{u} (ComplexShape.up ℤ) (n : ℤ))).symm ≪≫
    (HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) q).mapIso
      ((NatIso.mapHomologicalComplex (S.cechSectionsComplexZCompEval n)
        (ComplexShape.up ℤ)).app Z)

/-- **`E_1^{p,q} = H^q(Γ(C_p, Z^•_p))`.** The first page of the spectral sequence of the double
complex `A^{q,p} = Γ(C_p, Z^q_p)`, in a non-negative simplicial degree `p`, is the `q`-th
cohomology of the complex of sections over `C_p` of `Z^•` restricted to `C_p`.

This is the first page of the spectral sequence of the proof of Stacks 09WJ, not the
`H^q(C_p, K_p)` of its statement. -/
def pageOneIsoComponentSections (n : ℕ) (q : ℤ) :
    ((S.sectionsSpectralSequence Z).page 1 zero_le_one).X ((n : ℤ), q) ≅
      (((S.componentSectionsFunctor ⦋n⦌).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z).homology q :=
  S.pageOneIsoColumnHomology Z (n : ℤ) q ≪≫ S.columnHomologyIso Z n q

/-- If the first page vanishes at `(n, q)`, then so does `H^q(Γ(C_n, Z^•_n))`. -/
theorem isZero_componentSectionsHomology_of_isZero_pageOne (n : ℕ) (q : ℤ)
    (h : IsZero (((S.sectionsSpectralSequence Z).page 1 zero_le_one).X ((n : ℤ), q))) :
    IsZero ((((S.componentSectionsFunctor ⦋n⦌).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Z).homology q) :=
  (Iso.isZero_iff (S.pageOneIsoComponentSections Z n q)).1 h

/-- **The first page is nonzero wherever the cohomology of the sections is**: the contrapositive
of `isZero_componentSectionsHomology_of_isZero_pageOne`. -/
theorem not_isZero_pageOne_of_not_isZero_componentSectionsHomology (n : ℕ) (q : ℤ)
    (h : ¬ IsZero ((((S.componentSectionsFunctor ⦋n⦌).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj Z).homology q)) :
    ¬ IsZero (((S.sectionsSpectralSequence Z).page 1 zero_le_one).X ((n : ℤ), q)) :=
  fun hz => h (S.isZero_componentSectionsHomology_of_isZero_pageOne Z n q hz)

/-- **The double complex is nonzero wherever the sections are**: its term in outer degree `q`
and simplicial degree `n` is `Γ(C_n, Z^q_n)`. -/
theorem not_isZero_sectionsDoubleComplex_X_X_of_not_isZero_sections (q : ℤ) (n : ℕ)
    (h : ¬ IsZero ((S.componentSectionsFunctor ⦋n⦌).obj (Z.X q))) :
    ¬ IsZero (((S.sectionsDoubleComplex Z).X q).X (n : ℤ)) :=
  fun hz => h ((Iso.isZero_iff (S.sectionsDoubleComplexXXIso Z q n)).1 hz)

end SpectralSequence

/-! ### Vanishing outside the first quadrant, and convergence -/

section Convergence

variable (Z : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)

/-- The double complex vanishes in negative simplicial degrees, the complex of Stacks 0D77 being
extended by zero. -/
theorem isZero_sectionsDoubleComplex_X_X_of_neg_snd (q p : ℤ) (hp : p < 0) :
    IsZero (((S.sectionsDoubleComplex Z).X q).X p) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat p
    fun i => by change ((i : ℕ) : ℤ) ≠ p; omega

/-- **The double complex vanishes outside the first quadrant**, for a complex of abelian sheaves
vanishing in negative degrees. -/
theorem isZero_sectionsDoubleComplex_X_X (hZ : ∀ q : ℤ, q < 0 → IsZero (Z.X q)) (q p : ℤ)
    (h : q < 0 ∨ p < 0) :
    IsZero (((S.sectionsDoubleComplex Z).X q).X p) := by
  rcases h with hq | hp
  · exact (HomologicalComplex.eval Ab.{u} (ComplexShape.up ℤ) p).map_isZero
      ((S.cechSectionsComplexZ).map_isZero (hZ q hq))
  · exact S.isZero_sectionsDoubleComplex_X_X_of_neg_snd Z q p hp

/-- **The diagonals of the double complex are finite**, for a complex of abelian sheaves vanishing
in negative degrees: a nonzero term has both coordinates non-negative. -/
theorem diagonalFinite_sectionsDoubleComplex (hZ : ∀ q : ℤ, q < 0 → IsZero (Z.X q)) (n : ℤ) :
    {qp : ℤ × ℤ | qp.1 + qp.2 = n ∧
      ¬ IsZero (((S.sectionsDoubleComplex Z).X qp.1).X qp.2)}.Finite := by
  refine Set.Finite.subset (Set.finite_Icc ((0 : ℤ), n - n) (n, n)) ?_
  rintro ⟨q, p⟩ ⟨hsum, hne⟩
  have : 0 ≤ q ∧ 0 ≤ p := by
    by_contra hc
    exact hne (S.isZero_sectionsDoubleComplex_X_X Z hZ q p (by omega))
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- **The spectral sequence abuts to the cohomology of the total complex** of the double complex
`A^{q,p} = Γ(C_p, Z^q_p)`, for a complex of abelian sheaves vanishing in negative degrees: the
filtration by the simplicial coordinate is degreewise finite, so Stacks 012W applies.

This is the convergence of the spectral sequence of the proof of Stacks 09WJ, onto
`H^n(Tot(A^{•,•}))` rather than the `H^{p+q}(C_total, K)` of its statement. -/
theorem sectionsSpectralSequence_abutsTo_total (hZ : ∀ q : ℤ, q < 0 → IsZero (Z.X q)) :
    SpectralSequence.AbutsTo (S.sectionsSpectralSequence Z)
      (fun n => ((S.sectionsDoubleComplex Z).total (ComplexShape.up ℤ)).homology n) :=
  CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite
    (S.sectionsDoubleComplex Z).totalFiltration₂
    (fun p n => (S.sectionsDoubleComplex Z).stepSubobject (fun (_ : ℤ) j => j) p n)
    (fun _ _ => (Subobject.mk_arrow _).symm) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl) _
    (HomologicalComplex₂.pageIso₂ _)
    (HomologicalComplex₂.isDegreewiseFinite_totalFiltration₂ _
      (S.diagonalFinite_sectionsDoubleComplex Z hZ))

end Convergence

/-! ### The unbounded case: the product totalization -/

section Unbounded

variable (Z : CochainComplex (Sheaf S.totalTopology Ab.{u}) ℤ)

/-- **The double complex `A^{p,q} = Γ(C_p, Z^q_p)`** of a cochain complex `Z^•` of abelian
sheaves on the total site, with the simplicial degree `p` outer and the degree `q` in `Z^•`
inner: the orientation of Stacks 0H0V, in which the product totalization is taken. -/
abbrev sectionsProductDoubleComplex :
    HomologicalComplex₂ Ab.{u} (ComplexShape.up ℕ) (ComplexShape.up ℤ) :=
  HomologicalComplex₂.flip
    (((S.cechSectionsComplex).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)

/-- The term of the double complex in simplicial degree `p` and degree `q` is
`Γ(C_p, Z^q_p)`. -/
theorem sectionsProductDoubleComplex_X_X (p : ℕ) (q : ℤ) :
    ((S.sectionsProductDoubleComplex Z).X p).X q =
      (S.componentSectionsFunctor ⦋p⦌).obj (Z.X q) := rfl

/-- **The product totalization `Tot_π(A^{•,•})` of `A^{p,q} = Γ(C_p, Z^q_p)`**, with
`Tot_π^n = ∏_{p + q = n} Γ(C_p, Z^q_p)`: the complex of Stacks 0H0V. -/
abbrev sectionsProductTotal : CochainComplex Ab.{u} ℤ :=
  (S.sectionsProductDoubleComplex Z).productTotal

/-- **Stacks 0H0V**, the spectral sequence. For a cochain complex `Z^•` of abelian sheaves on
the total site of a simplicial-site situation, with no boundedness hypothesis, the filtration
`F^i Tot_π^n = ∏_{p + q = n, p ≥ i} Γ(C_p, Z^q_p)` of the product totalization of
`A^{p,q} = Γ(C_p, Z^q_p)` by the simplicial coordinate has a spectral sequence.

For `Z^•` a K-injective complex of injectives representing `K` in `D(C_total)` this is the
spectral sequence the source constructs; as in the source, no convergence is asserted. -/
@[stacks 0H0V "the spectral sequence of the filtration by the simplicial coordinate of the
product totalization, for a complex that is not bounded below; the identification of the first
page with `H^q(C_p, K_p)` is not carried"]
def sectionsProductSpectralSequence : CohomologicalSpectralSequence Ab.{u} 0 :=
  (S.sectionsProductDoubleComplex Z).productTotalColumnSpectralSequence

/-- **`E_0^{p,q} = Γ(C_p, Z^q_p)`**: the zeroth page of the spectral sequence of Stacks 0H0V is
the complex of sections over `C_p` of the restriction of `Z^q`.

The isomorphism is pinned by
`HomologicalComplex₂.π_productTotalColumnZeroPageIso_hom`: it carries the class of an element of
`F^p Tot_π^{p+q}` to its component in simplicial degree `p`. -/
@[stacks 0H0V "the zeroth page of the spectral sequence is `Γ(C_p, Z^q_p)`"]
def sectionsProductSpectralSequenceZeroPageIso (p : ℕ) (q : ℤ) :
    ((S.sectionsProductSpectralSequence Z).page 0 le_rfl).X ((p : ℤ), q) ≅
      (S.componentSectionsFunctor ⦋p⦌).obj (Z.X q) :=
  (S.sectionsProductDoubleComplex Z).productTotalColumnZeroPageIso p q

/-- **`E_1^{p,q} = H^q(Γ(C_p, Z^•_p))`**: the first page of the spectral sequence of Stacks 0H0V
is the `q`-th cohomology of the complex of sections over `C_p` of the restriction of `Z^•`,
not the `H^q(C_p, K_p)` of the statement of Stacks 0H0V. -/
@[stacks 0H0V "the first page of the spectral sequence is `H^q(Γ(C_p, Z^•_p))`"]
def sectionsProductSpectralSequenceOnePageIso (p : ℕ) (q : ℤ) :
    ((S.sectionsProductSpectralSequence Z).page 1 zero_le_one).X ((p : ℤ), q) ≅
      (((S.componentSectionsFunctor ⦋p⦌).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z).homology q :=
  (S.sectionsProductDoubleComplex Z).productTotalColumnOnePageIso p q

end Unbounded

end CategoryTheory.SimplicialSiteSituation

end
