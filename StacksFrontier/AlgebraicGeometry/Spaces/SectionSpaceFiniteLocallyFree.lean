module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.BootstrapEtaleSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceEtaleChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceRepresentable

/-!
# Spaces of sections over a finite locally free cover are algebraic spaces

Let `U` be a scheme contained in a big fppf site, let `Z` be an object of the big fppf site of
`U` whose structure morphism `Z ⟶ U` is finite locally free, and let `w : W ⟶ h_Z` be an
algebraic space over `Z`. Then the space of sections of `W ⟶ Z` over `U`,

```text
Res_{Z/U}(W) : T ↦ {σ : Z_T ⟶ W_T a section of W_T ⟶ Z_T},
```

is an algebraic space over `U`. This is Stacks 05YF for a base which is a scheme, in the
formulation by spaces of sections of `AlgebraicGeometry.Space.sectionSpace`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree`: the theorem
  above.

## Implementation notes

The proof is that of Stacks 05Y7, run directly on the space of sections. An algebraic space `W`
has a surjective étale chart `V ⟶ W` whose source is a disjoint union of affine schemes (Stacks
03FX, `AlgebraicGeometry.IsAlgebraicSpace.exists_etale_surjective_coproduct_affine_cover`).

* The space of sections of `V ⟶ Z` is an algebraic space by
  `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_yoneda`, which rests on Stacks 0BL4: a
  finite set of points of a disjoint union of affine schemes lies in an affine open.
* The induced morphism of spaces of sections is representable by algebraic spaces, étale and
  surjective, by `AlgebraicGeometry.Space.sectionSubfunctorMap_fibre` — this is Stacks 05Y5, and
  it uses Stacks 05XR and Stacks 05XQ over the bases of the scheme-valued points.
* Stacks 03Y3 then descends algebraicity along it, the space of sections of `W ⟶ Z` being a sheaf.

Stacks proves 05YF from 05Y7 and the cartesian square of 05YE; here the space of sections is
handled directly, so no relative morphism functor is needed. The source's further reduction of
the base to an affine scheme is not needed either, because Stacks 0BL4 holds over any base.

The finite local freeness of `Z ⟶ U` is the scheme-level property
`Stacks.Morphisms.IsFiniteLocallyFree` of the underlying morphism of schemes. The library's
`AlgebraicGeometry.Space.IsFiniteLocallyFree` of Stacks 03ZV, phrased through the direct image of
the structure sheaf on the small étale site, would follow from it by Stacks 03ZU, which is not in
the library.

## References

* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
* [Stacks Project, Tag 05Y7](https://stacks.math.columbia.edu/tag/05Y7)
* [Stacks Project, Tag 05Y5](https://stacks.math.columbia.edu/tag/05Y5)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
* [Stacks Project, Tag 03Y3](https://stacks.math.columbia.edu/tag/03Y3)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 0BL4](https://stacks.math.columbia.edu/tag/0BL4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}

/-- **The space of sections of an algebraic space over a finite locally free cover is an
algebraic space** (Stacks 05YF over a scheme base). Let `Z` be an object of the big fppf site of
`U` whose structure morphism is finite locally free, and let `w : W ⟶ h_Z` be an algebraic space
over `Z`. Then the functor `T ↦ {sections of W_T ⟶ Z_T}` of
`AlgebraicGeometry.Space.sectionSpace` is an algebraic space over `U`. -/
theorem isAlgebraicSpace_sectionSpace_of_isFiniteLocallyFree (Z : BigFppfOver B U hU)
    [Stacks.Morphisms.IsFiniteLocallyFree (B.inclusion.map Z.hom)]
    {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B U hU W)
    (w : W ⟶ yoneda.obj Z) :
    IsAlgebraicSpace B U hU (sectionSpace B U hU Z W w) := by
  have hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom) :=
    Stacks.Morphisms.IsFiniteLocallyFree.isFinite _
  obtain ⟨V, c, I, Y, e, hcS, hcE, hYaff, -⟩ :=
    IsAlgebraicSpace.exists_etale_surjective_coproduct_affine_cover B U hU W hW
  let v : V ⟶ Z := yoneda.preimage (c ≫ w)
  have hv : c ≫ w = yoneda.map v := (yoneda.map_preimage _).symm
  have hV : ∀ t : Set ((BigFppfOver.toScheme B U hU).obj V), t.Finite →
      ∃ O : ((BigFppfOver.toScheme B U hU).obj V).Opens, IsAffineOpen O ∧ t ⊆ O :=
    exists_isAffineOpen_finite_of_iso e (exists_isAffineOpen_finite_sigma Y)
  have h₀ := isAlgebraicSpace_sectionSpace_yoneda v hV
  -- the morphism of spaces of sections, read on the subfunctors of `T ↦ W(Z × T)`
  let eW := sectionSpaceIsoSubfunctor Z W w
  have hfib := sectionSubfunctorMap_fibre c hv hZfin hW (isAlgebraicSpace_yoneda B U hU V) hcE hcS
  have hsub : IsAlgebraicSpace B U hU (sectionSubfunctor Z W w).toFunctor :=
    isAlgebraicSpace_of_isRepresentableByAlgebraicSpaces_surjective_etale
      ((Presheaf.isSheaf_of_iso_iff eW).mp (isSheaf_sectionSpace_of_isSheaf Z W w hW.isSheaf))
      (AlgebraicGeometry.isAlgebraicSpace_of_iso B U hU
        (sectionSpaceIsoSubfunctor Z (yoneda.obj V) (yoneda.map v)).symm h₀)
      (sectionSubfunctorMap c hv) (fun T ξ => (hfib T ξ).1) (fun T ξ => (hfib T ξ).2.2)
      (fun T ξ => (hfib T ξ).2.1)
  exact AlgebraicGeometry.isAlgebraicSpace_of_iso B U hU eW hsub

end AlgebraicGeometry.Space

end
