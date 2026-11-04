module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# A map out of a single complex that is nonzero in the derived category

Let `H` be a cochain complex in an abelian category and let `f : A ⟶ Z^p(H)` be a map into its
cycles in degree `p`. Composing with the inclusion of the cycles gives a cochain map
`A[-p] ⟶ H` out of the complex concentrated in degree `p`, namely
`HomologicalComplex.mkHomFromSingle (f ≫ H.iCycles p)`.

This file records that this cochain map is nonzero in the derived category as soon as the class
of `f` in `H^p(H)` is nonzero — that is, as soon as `f ≫ H.homologyπ p ≠ 0`. It is the step by
which a nonzero cohomology class of a complex is converted into a nonzero morphism out of a
single complex, and so the step by which a generation statement is applied to a complex.

## Main results

* `HomologicalComplex.homologyMap_mkHomFromSingle_ne_zero`: the map induced on `H^p` by
  `mkHomFromSingle (f ≫ H.iCycles p)` is nonzero.
* `HomologicalComplex.derivedMap_mkHomFromSingle_ne_zero`: the image of
  `mkHomFromSingle (f ≫ H.iCycles p)` under `DerivedCategory.Q` is nonzero.

## Implementation notes

The second statement is deduced from the first through
`CategoryTheory.DerivedCategory.homologyFunctorFactors`, which compares the homology of the class
of a complex with the homology of the complex. Cancelling its (invertible, hence epimorphic)
component is done with `CategoryTheory.Limits.zero_of_epi_comp` rather than by rewriting with
`comp_zero`: the two spellings `(homologyFunctor C (ComplexShape.up ℤ) p).obj K` and
`K.homology p` of the source are definitionally equal but not syntactically so, and a rewrite
that passes through the zero morphism between them does not typecheck.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type*} [Category C] [Abelian C] (H : CochainComplex C ℤ) (p : ℤ) {A : C}

/-- **The map induced on `H^p` by `A[-p] ⟶ H` is nonzero** when the cycle `f` it is built from
has nonzero class in `H^p(H)`.

The composite of the canonical identification `A ≅ Z^p(A[-p])` with `Z^p` of the cochain map is
`f` itself, so `homologyπ`-naturality turns the vanishing of the induced map on `H^p` into the
vanishing of `f ≫ H.homologyπ p`. -/
theorem homologyMap_mkHomFromSingle_ne_zero
    (f : A ⟶ H.cycles p) (hf : f ≫ H.homologyπ p ≠ 0) :
    homologyMap (mkHomFromSingle (f ≫ H.iCycles p) (fun k _ => by simp)) p ≠ 0 := by
  let φ := mkHomFromSingle (f ≫ H.iCycles p) (fun k _ => by simp)
  have hcycles : (singleObjCyclesSelfIso (ComplexShape.up ℤ) p A).inv ≫
      cyclesMap φ p = f := by
    apply (cancel_mono (H.iCycles p)).mp
    simp [φ]
  intro h
  apply hf
  rw [← hcycles, Category.assoc, ← homologyπ_naturality, h, comp_zero, comp_zero]

/-- **The cochain map `A[-p] ⟶ H` attached to a cycle with nonzero class is nonzero in the
derived category.** -/
theorem derivedMap_mkHomFromSingle_ne_zero [HasDerivedCategory C]
    (f : A ⟶ H.cycles p) (hf : f ≫ H.homologyπ p ≠ 0) :
    DerivedCategory.Q.map (mkHomFromSingle (f ≫ H.iCycles p) (fun k _ => by simp)) ≠ 0 := by
  intro h
  apply homologyMap_mkHomFromSingle_ne_zero H p f hf
  have hn := (DerivedCategory.homologyFunctorFactors C p).hom.naturality
    (mkHomFromSingle (f ≫ H.iCycles p) (fun k _ => by simp))
  dsimp at hn
  rw [h, Functor.map_zero, zero_comp] at hn
  have hb := zero_of_epi_comp
    ((DerivedCategory.homologyFunctorFactors C p).hom.app
      ((HomologicalComplex.single C (ComplexShape.up ℤ) p).obj A)) hn.symm
  rwa [HomologicalComplex.homologyFunctor_map] at hb

end HomologicalComplex

end
