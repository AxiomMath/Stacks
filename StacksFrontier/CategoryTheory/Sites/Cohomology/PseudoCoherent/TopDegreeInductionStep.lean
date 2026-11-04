module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.SingleFreeStrictlyPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.TopDegreeInduction

/-!
# The induction step of Stacks 08HE (2) ⇒ (1), assembled from the local surjection and the lift

Let `(C, O)` be a ringed site, let `F` be an object of `D(O)` in `D^{≤n}`, let
`φ : 𝒪^{⊕t} ⟶ Hⁿ(F)` be an epimorphism of `O`-modules and let `f : 𝒪^{⊕t} ⟶ F⟦n⟧` be a lift of
`φ` through the canonical `F⟦n⟧ ⟶ τ^{≥0}(F⟦n⟧)`, the source being `𝒪^{⊕t}` placed in degree zero.
Then `f`, shifted back, is the first morphism of a distinguished triangle with second vertex `F`,
`m`-pseudo-coherent first vertex for every `m`, and third vertex with no cohomology in any degree
`≥ n`.

That is exactly the triangle datum the recursion
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep` asks of its step, except for
the standing hypothesis `P` on the third vertex, which is not a formal consequence of the triangle
and is left to the caller.  So this module is what checks that the pieces of the induction fit:
the identification `τ^{≥0}(F⟦n⟧) ≅ Hⁿ(F)[0]`, the reading of a surjection through it, the shift
back, the first vertex's pseudo-coherence, and the cone computation.

## Main results

* `AlgebraicGeometry.RingedSite.exists_distTriang_free_of_lift`: **the induction step's triangle.**

## Implementation notes

The source of the lift is `𝒪^{⊕t}` in degree zero rather than in degree `n` because the
affine-chart lifting step is stated at truncation degree `0`; the shift is therefore carried by
`F`, and the triangle's first vertex is `((single 0).obj 𝒪^{⊕t})⟦-n⟧`.  That object is identified
with `(single n).obj 𝒪^{⊕t}` by the shift isomorphism of
`DerivedCategory.singleFunctors`, which is what both supplies its vanishing cohomology outside
degree `n` and transports
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_singleFunctor_obj_free` onto it.

## References

* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v w d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **The triangle of the induction step of Stacks 08HE (2) ⇒ (1).**  For `F` in `D^{≤n}`, an
epimorphism `φ : 𝒪^{⊕t} ⟶ Hⁿ(F)` of `O`-modules with `t` finite, and a lift `f` of
`DerivedCategory.singleMapTruncGEZeroShift F n φ` along `F⟦n⟧ ⟶ τ^{≥0}(F⟦n⟧)`, there is a
distinguished triangle whose second vertex is `F`, whose first vertex is `m`-pseudo-coherent for
every `m`, and whose third vertex has no cohomology in any degree `≥ n`.

The lift `f` is what the affine-chart lifting step
`AlgebraicGeometry.exists_lift_truncGEπ_zero_cofan_of_isAffineOpen` provides, and `φ` is what the
finite-type conclusion of Stacks 08HD provides through
`SheafOfModules.exists_coversTop_epi_free_of_isFiniteType`.  What this returns is the triangle
datum of `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_descentStep`, apart from that
recursion's standing hypothesis on the third vertex. -/
public theorem exists_distTriang_free_of_lift (m n : ℤ)
    (F : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [DerivedCategory.IsLE F n] (ι : Type w) [Finite ι]
    (φ : SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι ⟶
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).obj F)
    (hφ : Epi φ)
    (f : (DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι) ⟶ F⟦n⟧)
    (hf : f ≫ (DerivedCategory.TStructure.t.truncGEπ 0).app (F⟦n⟧) =
      DerivedCategory.singleMapTruncGEZeroShift F n φ) :
    ∃ T : Triangle
        (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      T ∈ distTriang
          (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ∧
        Nonempty (T.obj₂ ≅ F) ∧ X.IsPseudoCoherentFrom T.obj₁ m ∧
          ∀ j : ℤ, n ≤ j →
            IsZero ((DerivedCategory.homologyFunctor
                (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj
              T.obj₃) := by
  have := hφ
  -- `𝒪^{⊕t}` in degree zero, shifted by `-n`, is `𝒪^{⊕t}` in degree `n`.
  let e : ((DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι))⟦(-n : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) n).obj
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι) :=
    ((DerivedCategory.singleFunctors
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).shiftIso (-n) n 0
      (by omega)).app (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ι)
  have hK : ∀ j : ℤ, n < j →
      IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj
        (((DerivedCategory.singleFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (SheafOfModules.free (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) ι))⟦(-n : ℤ)⟧)) :=
    fun j hj => IsZero.of_iso (DerivedCategory.isZero_of_isLE _ n j hj)
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).mapIso e)
  obtain ⟨Q, g, h, hT, hQ⟩ := exists_distTriang_isZero_homology_obj₃_of_epi n
    (f⟦(-n : ℤ)⟧' ≫ (shiftShiftNeg F n).hom) hK
    (fun j hj => DerivedCategory.isZero_of_isLE F n j hj)
    (DerivedCategory.epi_homologyMap_shiftBack_of_lift F n f _ hf
      (DerivedCategory.epi_homologyMap_singleMapTruncGEZeroShift F n φ))
  exact ⟨Triangle.mk (f⟦(-n : ℤ)⟧' ≫ (shiftShiftNeg F n).hom) g h, hT, ⟨Iso.refl _⟩,
    isPseudoCoherentFrom_of_iso X m (X.isPseudoCoherentFrom_singleFunctor_obj_free n m ι) e, hQ⟩

end AlgebraicGeometry.RingedSite

end
