module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.BaseChangeDegree
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# The complementary degree of a component is unchanged by extension of the ground field

Let `E` be a field, let `V` be a scheme over `E`, and let `T ⊆ V` be a closed subset, carrying its
reduced closed subscheme structure `P T = vanishingIdeal (Closeds.closure T)`.  Writing `V'` for
the scheme-theoretic closure of the complement of `T`, cut out by
`AlgebraicGeometry.complementaryCurveIdeal (P T)`, the *complementary degree* of `T` is
`h⁰(T ∩ V', 𝒪)`, the dimension over `E` of the degree-zero cohomology of the structure sheaf of
the intersection.  This is the quantity the curve files of this directory call the degree of an
intersection, and the one clause (4) of `AlgebraicGeometry.IsRationalBridge` constrains to be two.

For a field extension `Ω/E` and `W = V_Ω` the base change, the closed subset `T` has preimage
`b ⁻¹' T` in `W`, where `b : W ⟶ V` is the projection.  As long as the reduced structure on `T`
stays reduced upstairs, the complementary degree is unchanged:

`h⁰((b ⁻¹' T) ∩ W', 𝒪) = h⁰(T ∩ V', 𝒪)`,

the two sides being taken over `Ω` and over `E` respectively.

## Main results

* `AlgebraicGeometry.finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_comap`:
  **the complementary degree of a reduced closed subset is invariant under extension of the ground
  field**, provided its inverse image stays reduced.

## Implementation notes

The three steps of the proof are independent of one another.

*The reduced structure on the preimage is the inverse image of the reduced structure.*  Both
`vanishingIdeal (Closeds.closure (b ⁻¹' T))` and `(P T).comap b` have support `b ⁻¹' T`, by
`AlgebraicGeometry.Scheme.IdealSheafData.support_comap` and
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal`; the hypothesis `hred` then
lets `AlgebraicGeometry.Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme` identify
the inverse image with the vanishing ideal of that support.  Reducedness upstairs is a genuine
hypothesis and not a consequence: over an imperfect field the reduced structure on a closed point
can acquire nilpotents after base change, and then the two ideal sheaves differ.  On a curve it is
supplied by geometric reducedness of the ambient scheme, which [Stacks, Tag 0E37] provides from
nodality.

*The intersection with the complementary curve commutes with flat pullback.*  This is
`AlgebraicGeometry.intersectionWithComplementaryCurveIdeal_comap`, whose content is that flatness
makes the inverse image of the open immersion of the complement of the support again the open
immersion of the complement of the inverse image of the support.  Flatness of `b` is flatness of
`Spec Ω ⟶ Spec E` transported along the pullback square, every field extension being flat.

*The degree is invariant.*
`AlgebraicGeometry.finrank_structureSheafCohomology_zero_comap_baseChange` applied to the ideal
sheaf `intersectionWithComplementaryCurveIdeal (P T)`, which is where the quasi-compactness and
quasi-separatedness hypotheses on `(P T ⊔ complementaryCurveIdeal (P T))` over `E` are used.
No properness and no finiteness: if the degree is infinite both sides are `0` by the convention of
`Module.finrank`, and the equality still holds.

## References

* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry

/-- **The degree of the intersection of a reduced closed subset with the scheme-theoretic closure
of its complement is unchanged by extension of the ground field.**  Let `g : V ⟶ Spec E` be a
scheme over a field `E`, let `Ω/E` be a field extension, and let `b : W ⟶ V`, `q : W ⟶ Spec Ω`
exhibit `W` as the base change `V_Ω`.  Let `T ⊆ V` be closed, carrying the reduced structure
`vanishingIdeal (Closeds.closure T)`, and assume its inverse image along `b` is still reduced.
Then the degree of the intersection of `T` with the closure of its complement, taken over `E`,
equals the degree of the intersection of `b ⁻¹' T` with the closure of *its* complement, taken
over `Ω`.

Taken at an irreducible component of a nodal curve this says that the complementary degree
appearing in `AlgebraicGeometry.IsRationalBridge` is insensitive to the ground field, which is
what lets the local analysis of a rational bridge be carried out over an algebraically closed
field. -/
theorem finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_comap
    (E Ω : Type u) [Field E] [Field Ω] [Algebra E Ω]
    {V W : Scheme.{u}} (g : V ⟶ Spec (.of E)) (b : W ⟶ V) (q : W ⟶ Spec (.of Ω))
    (hpb : IsPullback b q g (Spec.map (CommRingCat.ofHom (algebraMap E Ω))))
    (T : Set V) (hT : IsClosed T)
    (hred : IsReduced ((vanishingIdeal (Closeds.closure T)).comap b).subscheme)
    [QuasiCompact (Scheme.Opens.ι (vanishingIdeal (Closeds.closure T)).support.compl)]
    [QuasiCompact ((vanishingIdeal (Closeds.closure T) ⊔
      complementaryCurveIdeal (vanishingIdeal (Closeds.closure T))).subschemeι ≫ g)]
    [QuasiSeparated ((vanishingIdeal (Closeds.closure T) ⊔
      complementaryCurveIdeal (vanishingIdeal (Closeds.closure T))).subschemeι ≫ g)] :
    Module.finrank Ω (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure (b.base ⁻¹' T)) ⊔
          complementaryCurveIdeal
            (vanishingIdeal (Closeds.closure (b.base ⁻¹' T)))).subschemeι ≫ q) 0)
      = Module.finrank E (structureSheafCohomology
          ((vanishingIdeal (Closeds.closure T) ⊔
            complementaryCurveIdeal (vanishingIdeal (Closeds.closure T))).subschemeι ≫ g) 0) := by
  have := hred
  -- The inverse image of the reduced structure on `T` has support `b ⁻¹' T`.
  have hsupp : ((vanishingIdeal (Closeds.closure T)).comap b).support
      = Closeds.closure (b.base ⁻¹' T) := by
    apply Closeds.ext
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, coe_support_vanishingIdeal,
      Closeds.coe_closure, Closeds.coe_closure, hT.closure_eq,
      (hT.preimage b.continuous).closure_eq]
  -- Hence it *is* the reduced structure on `b ⁻¹' T`.
  have hcomap : vanishingIdeal (Closeds.closure (b.base ⁻¹' T))
      = (vanishingIdeal (Closeds.closure T)).comap b :=
    (Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ hsupp).symm
  -- The projection of the base change of a field extension is flat.
  have : Flat b :=
    MorphismProperty.of_isPullback hpb.flip
      (Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance))
  -- The intersection with the complementary curve commutes with that flat pullback.
  have hinter : vanishingIdeal (Closeds.closure (b.base ⁻¹' T)) ⊔
      complementaryCurveIdeal (vanishingIdeal (Closeds.closure (b.base ⁻¹' T)))
      = (vanishingIdeal (Closeds.closure T) ⊔
          complementaryCurveIdeal (vanishingIdeal (Closeds.closure T))).comap b := by
    rw [hcomap]
    exact intersectionWithComplementaryCurveIdeal_comap (vanishingIdeal (Closeds.closure T)) b
  rw [hinter]
  exact finrank_structureSheafCohomology_zero_comap_baseChange E Ω g b q hpb _

end AlgebraicGeometry

end
