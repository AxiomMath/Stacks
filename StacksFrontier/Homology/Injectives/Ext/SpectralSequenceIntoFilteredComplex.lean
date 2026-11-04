module

public import StacksCore.Algebra.Homology.SpectralSequence.Basic
public import StacksCore.CategoryTheory.Filtration.GradedPieces
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Canonical
public import StacksFrontier.Homology.Injectives.FilteredComplex.HomComplexCovariant
import StacksCore.Tactic.StacksAttribute

/-!
# The Ext spectral sequence into a filtered complex

Let `A` be a Grothendieck abelian category, let `K^•` be a filtered complex of `A` and let `M` be
an object of `D(A)`.  Choosing a complex `M^•` representing `M` and a filtered K-injective
resolution `j : K^• ⟶ J^•` as in Tag 0BKI, the Hom complex `Hom^•(M^•, J^•)` carries the
decreasing filtration `F^pHom^•(M^•, J^•) = Hom^•(M^•, F^pJ^•)`, and the spectral sequence of
that filtered complex is a cohomological spectral sequence `(E_r, d_r)_{r ≥ 1}` with
`E_1^{p,q} = Ext^{p+q}(M, gr^pK)`.

This is the construction half of Tag 0G1X.  Its dual, with the filtered complex in the *source*
of the Hom complex, is Tag 0G1Z in `StacksDraft.Ch19.Sec13.ExtSpectralSequenceOfFilteredComplex`.

## Main definitions

* `Stacks.Injectives.extIntoSetup`: the chosen representative of `M` and the chosen filtered
  K-injective resolution of `K^•`, packaged as a `FilteredHomComplexSetup`.
* `Stacks.Injectives.extIntoFilteredHomComplex`: the filtered Hom complex `Hom^•(M^•, J^•)` with
  the filtration `Hom^•(M^•, F^pJ^•)`.
* `Stacks.Injectives.extIntoSpectralSequence`: its spectral sequence, from page one on.

## Main results

* `Stacks.Injectives.extSpectralSequenceInto`: **Tag 0G1X.** The spectral sequence together with
  the identifications `E_1^{p,q} = Ext^{p+q}(M, gr^pK)`.
* `Stacks.Injectives.extSpectralSequenceInto_fst`: the spectral sequence is, as a whole, the
  spectral sequence of the filtered Hom complex, so every page, differential and page-turning
  isomorphism is specified.

## Implementation notes

The assertion that the differential on page `r` has bidegree `(r, -r + 1)` is built into
`CohomologicalSpectralSequence`, so it is not restated; neither is the indexing `r ≥ 1`, which is
the `r₀` parameter of the spectral sequence.

The first-page identifications are *additive equivalences*, as are the cohomology–Ext
identifications of `Stacks.Injectives.CohomologyExtComparison` that they are built from.  This is
what keeps the Grothendieck universe `w'`, the derived-category Hom universe `w` and the morphism
universe `v` of `A` independent: the Hom complex `Hom^•(M^•, J^•)` is a complex of
`AddCommGrpCat.{v}`, while `Ext` groups in `D(A)` live in `AddCommGrpCat.{w}`.  No universe is
narrowed here, and in particular `v` and `w` are not identified.  The dual Tag 0G1Z instead moves
the Hom complex into universe `w` with `ShrinkHoms`; that device is not reused here, because the
covariant Hom complex is formed out of the already-chosen K-injective resolution rather than out
of a transported filtered complex.

The graded piece in degree `p` is `gr^pK^• = F^pK^•/F^{p+1}K^•`, i.e. `FilteredObject.gr p`, and
the object of `D(A)` it represents is its image under `DerivedCategory.Q`.

## References

* [Stacks Project, Tag 0G1X](https://stacks.math.columbia.edu/tag/0G1X)
* [Stacks Project, Tag 0BKI](https://stacks.math.columbia.edu/tag/0BKI)
-/

@[expose] public noncomputable section

universe w' w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Injectives

variable {A : Type u} [Category.{v} A] [Abelian A]
  [IsGrothendieckAbelian.{w'} A] [HasDerivedCategory.{w} A]

/-- The choices made in Tag 0G1X: a complex representing `M`, and a filtered K-injective
resolution of `K^•` as supplied by Tag 0BKI. -/
def extIntoSetup (M : DerivedCategory A) (K : CochainComplex.Filtered A) :
    FilteredHomComplexSetup.{w', w} (A := A) where
  K := K
  M := M
  MComplex := DerivedCategory.Q.objPreimage M
  representsM := DerivedCategory.Q.objObjPreimageIso M
  J := (exists_filtered_quasiIso_isKInjective.{w'} K).choose
  j := (exists_filtered_quasiIso_isKInjective.{w'} K).choose_spec.choose
  resolution := (exists_filtered_quasiIso_isKInjective.{w'} K).choose_spec.choose_spec

/-- The filtered Hom complex `Hom^•(M^•, J^•)`, filtered by `Hom^•(M^•, F^pJ^•)`. -/
abbrev extIntoFilteredHomComplex (M : DerivedCategory A) (K : CochainComplex.Filtered A) :
    CochainComplex.Filtered AddCommGrpCat.{v} :=
  (filteredHomComplexRealization (extIntoSetup.{w', w} M K)).complex

/-- The spectral sequence of the filtered Hom complex, starting at page one.  The restriction
retains the page complexes and the page-turning isomorphisms of Tag 012M. -/
def extIntoSpectralSequence (M : DerivedCategory A) (K : CochainComplex.Filtered A) :
    CohomologicalSpectralSequence AddCommGrpCat.{v} 1 :=
  let E := CochainComplex.Filtered.spectralSequenceFunctor.obj
    (extIntoFilteredHomComplex.{w', w} M K)
  { page := fun r hr => E.page r (by omega)
    iso := fun r r' pq hrr' hr => E.iso r r' pq hrr' (by omega) }

/-- **Stacks 0G1X.** For a filtered complex `K^•` of a Grothendieck abelian category and an object
`M` of `D(A)`, the cohomological spectral sequence `(E_r, d_r)_{r ≥ 1}` of the filtered Hom
complex, bundled with the identifications `E_1^{p,q} = Ext^{p+q}(M, gr^pK)`.  Its differential on
page `r` has bidegree `(r, -r + 1)` by the definition of `CohomologicalSpectralSequence`. -/
@[stacks 0G1X "ext_spectral_sequence", ega "0 13.7.3" "Ext functor case"]
def extSpectralSequenceInto (M : DerivedCategory A) (K : CochainComplex.Filtered A) :
    Σ E : CohomologicalSpectralSequence AddCommGrpCat.{v} 1,
      ∀ p q : ℤ, ((E.page 1).X (p, q) : Type v) ≃+
        DerivedCategory.Ext M
          (DerivedCategory.Q.obj ((FilteredObject.gr p).obj K)) (p + q) := by
  let S := extIntoSetup.{w', w} M K
  let R := filteredHomComplexRealization S
  let N := R.complex
  let F : ℤ → ∀ n : ℤ, Subobject (N.X.X n) := CochainComplex.filtrationSubobject N
  have hF : ∀ p n : ℤ, F p n = Subobject.mk ((N.filtration.ι.app (op p)).f n) := fun _ _ => rfl
  have hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n :=
    CochainComplex.filtrationSubobject_antitone N
  let cmp := (cohomologyExtComparison_nonempty S).some
  refine ⟨extIntoSpectralSequence.{w', w} M K, fun p q => ?_⟩
  let h := FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage N F hF hanti
  let e₁ := ((Classical.choose_spec h).2.2 p q (p + q) rfl).some
  let egr := HomologicalComplex.homologyMapIso (R.gradedIso p) (p + q)
  exact (e₁ ≪≫ egr).addCommGroupIsoToAddEquiv.trans (cmp.gradedHomComplexIso p (p + q))

/-- The spectral sequence of Tag 0G1X is the spectral sequence of the filtered Hom complex, as a
whole; it therefore specifies every page, differential and page-turning isomorphism. -/
theorem extSpectralSequenceInto_fst (M : DerivedCategory A) (K : CochainComplex.Filtered A) :
    (extSpectralSequenceInto.{w', w} M K).1 = extIntoSpectralSequence.{w', w} M K := rfl

end Stacks.Injectives

end
