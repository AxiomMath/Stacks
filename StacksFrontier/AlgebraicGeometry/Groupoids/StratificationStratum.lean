module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteStratification

/-!
# The strata of a Fitting stratification

The closed subschemes of a decreasing stratification are cut out by an increasing chain of ideal
sheaves. The locally closed stratum between two consecutive members of the chain is realized
here as an open subscheme of the smaller closed subscheme, whose set-theoretic image is the
difference of the two supports.

## Main results

* `Stacks.IdealSheaf.exists_opens_range_subschemeι_eq_sdiff`: for ideal sheaves `I` and `J` on a
  scheme there is an open subscheme of `I.subscheme` whose image is
  `I.support \ J.support`.
* `Stacks.Groupoids.exists_opens_finiteStratification_stratum`: the `r`-th stratum of the
  Fitting stratification of a groupoid scheme with finite source, as an open subscheme of the
  `(r-1)`-st closed subscheme.

## Implementation notes

The open subscheme is the complement of the inverse image of the support of the larger ideal
sheaf, which is closed because supports are closed. Its image is computed from
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`, which identifies the range of the
closed immersion of a subscheme with the support of its ideal sheaf, together with
`Set.image_preimage_eq_inter_range`.

This is the first half of [Stacks Project, Tag 0AB9] "rank of each stratum": the statement that
source is finite locally free of rank `r` over this stratum is not proved here, so no Stacks
attribute is attached.

## References

* [Stacks Project, Tag 0AB9](https://stacks.math.columbia.edu/tag/0AB9)
* [Stacks Project, Tag 05P8](https://stacks.math.columbia.edu/tag/05P8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.IdealSheaf

/-- The locally closed stratum between two closed subschemes, realized as an open subscheme of
the smaller one: for ideal sheaves `I` and `J` on a scheme `X` there is an open subscheme of
`I.subscheme` whose image in `X` is `I.support \ J.support`. -/
theorem exists_opens_range_subschemeι_eq_sdiff {X : Scheme.{u}} (I J : X.IdealSheafData) :
    ∃ W : I.subscheme.Opens, Set.range (W.ι ≫ I.subschemeι) =
      (I.support : Set X) \ (J.support : Set X) := by
  refine ⟨⟨(I.subschemeι ⁻¹' (J.support : Set X))ᶜ,
    (J.support.isClosed.preimage I.subschemeι.continuous).isOpen_compl⟩, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    show ((⟨(I.subschemeι ⁻¹' (J.support : Set X))ᶜ,
        (J.support.isClosed.preimage I.subschemeι.continuous).isOpen_compl⟩ :
          I.subscheme.Opens) : Set I.subscheme)
      = I.subschemeι ⁻¹' ((J.support : Set X)ᶜ) from rfl,
    Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
    Set.sdiff_eq, Set.inter_comm]

end Stacks.IdealSheaf

namespace Stacks.Groupoids

/-- The `r`-th stratum of the Fitting stratification of a groupoid scheme: an open subscheme of
the `(r-1)`-st closed subscheme whose image in the object scheme is the difference of the two
supports. Finiteness of source and target is not needed for this statement; it enters only in
the identification of the rank of source on this stratum. -/
theorem exists_opens_finiteStratification_stratum {S : Scheme.{u}} (G : GroupoidScheme S)
    (r : ℕ) :
    ∃ W : (finiteStratification G (r - 1)).subscheme.Opens,
      Set.range (W.ι ≫ (finiteStratification G (r - 1)).subschemeι) =
        ((finiteStratification G (r - 1)).support : Set G.objects.left) \
          ((finiteStratification G r).support : Set G.objects.left) :=
  IdealSheaf.exists_opens_range_subschemeι_eq_sdiff _ _

end Stacks.Groupoids

end
