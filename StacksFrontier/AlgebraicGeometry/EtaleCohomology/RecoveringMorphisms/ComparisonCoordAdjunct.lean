module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ComparisonNatural
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# The comparison of step (3) of Stacks 04I6, in terms of Yoneda morphisms

Clause (ii) of the third identification owed by step (3) of [Stacks Project, Tag 04I6] is that the
fibre at a geometric point `x̄` of `X` of the comparison
`AlgebraicGeometry.comparisonSheafHom : g⁻¹h_V ⟶ h_{X ×_Y V}` is, under the two computations of
the fibres as solution sets, the solution-set map `a ↦ φ ∘ a` of
`AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso`.

The isomorphism `e` of geometric stalk functors out of which `φ` is built is arbitrary, and no
description of it on germs exists.  In clause (i) that was dealt with by *evaluating* `e` at the
terminal sheaf (`MorphismOfTopoi.germ_globalSections_of_sheafFiberIso`).  **Clause (ii) is
different: there `e` cancels.**  The coordinates of both solution sets are germs of global
functions on charts, and a global function on a chart is a Yoneda morphism out of the
representable sheaf; naturality of `e` at such a morphism moves `e` past it, and the same `e` sits
on the source side of the comparison, so it disappears.  What is left is two identities with no
point and no `e` in them, and this file proves both.

## Main results

* `AlgebraicGeometry.comparisonCoord_eq_inverseImage_yoneda` — the `i`-th coordinate of the
  comparison is `g⁻¹` of the Yoneda morphism of the `i`-th coordinate function of the
  presentation, followed by the inverse-image form of `g^♯`.
* `AlgebraicGeometry.comparisonSheafHom_comp_yoneda_elt` — the comparison followed by the Yoneda
  morphism of an arbitrary global function on `V`, pulled back to `X ×_Y V`, is the generalized
  element of that function.  This is the identity out of which both the coordinate case below and
  the agreement of the two structure maps come.
* `AlgebraicGeometry.comparisonSheafHom_comp_yoneda` — the comparison followed by the Yoneda
  morphism of the `i`-th coordinate function of `X ×_Y V` is that same `i`-th coordinate.

## What this does not do

Nothing here carries a `@[stacks 04I6]` tag.  These are the `e`-free halves of clause (ii); what
remains of the clause is to apply a geometric fibre functor to them and match the result against
`AlgebraicGeometry.geometricPointFiberEquivEtaleLocalSolutions_coe` and
`AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions_coe`.  See the "What is missing"
section of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineCase.lean`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback Stacks.EtaleCohomology AlgebraicGeometry.SmallEtale

universe u

namespace AlgebraicGeometry

section Coord

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X hX))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y hY)))
  [IsAffine Y] {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(Y, ⊤)}
  (V : SmallEtale B Y hY) [IsAffine ((SmallEtale.toScheme B Y hY).obj V)]
  (pres : StandardPresentationOver ((SmallEtale.toScheme B Y hY).obj V)
    (schemeStructureHom B Y hY V) P)

omit [IsAffine Y] [IsAffine ((toScheme B Y hY).obj V)] in
/-- **The `i`-th coordinate of the comparison is `g⁻¹` of a Yoneda morphism followed by `g^♯`.**

`AlgebraicGeometry.comparisonCoord` is defined by transporting `g^♯(xᵢ)` across the ring
isomorphism `MorphismOfTopoi.inverseImageYonedaRingEquiv`.  That isomorphism is, underneath, the
adjunction `g⁻¹ ⊣ g_*` followed by the Yoneda lemma
(`MorphismOfTopoi.inverseImageYonedaRingHom_apply`), so its inverse at `g^♯(xᵢ)` is the adjunct of
the Yoneda morphism `β_i : h_V ⟶ 𝒪_Y` of the coordinate function `xᵢ` composed with `g^♯` — which
by `CategoryTheory.Adjunction.homEquiv_naturality_left` and
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv` is `g⁻¹β_i` followed by the
inverse-image form of the structure map.

**This identity mentions no point and no isomorphism of stalk functors**, and that is the whole
reason for it.  Clause (ii) of the third identification owed by step (3) of
[Stacks Project, Tag 04I6] — that the fibre at `x̄` of the comparison is the solution-set map — is
proved by applying a geometric fibre functor to this identity: naturality of the arbitrary
isomorphism `e` of stalk functors at `β_i` moves `e` past it, and since the same `e` sits on the
source side of the comparison it cancels.  Contrast clause (i), where `e` does *not* cancel and
has to be evaluated at the terminal sheaf
(`MorphismOfTopoi.germ_globalSections_of_sheafFiberIso`). -/
theorem comparisonCoord_eq_inverseImage_yoneda (i : Fin n) :
    comparisonCoord B hX hY g V pres i =
      g.toToposHom.inverseImage.map
          (((SmallEtale.topology B Y hY).yonedaEquiv
            (F := Sheaf.ringSheaf (smallEtaleRingSheaf B hY))).symm
            (presCoord B hY V pres i)) ≫
        (RingedSite.toRingedTopos (smallEtaleRingedSite B X hX)).forgetRing.map
          g.fSharpInverseImage := by
  refine ((MorphismOfTopoi.inverseImageYonedaRingEquiv g.toToposHom
    (smallEtaleRingSheaf B hX) V).symm_apply_eq).2 ?_
  refine Eq.trans ?_ (MorphismOfTopoi.inverseImageYonedaRingHom_apply g.toToposHom
    (smallEtaleRingSheaf B hX) V _).symm
  refine Eq.trans ?_ (congrArg (SmallEtale.topology B Y hY).yonedaEquiv
    (g.toToposHom.adj.homEquiv_naturality_left (((SmallEtale.topology B Y hY).yonedaEquiv
        (F := Sheaf.ringSheaf (smallEtaleRingSheaf B hY))).symm (presCoord B hY V pres i))
      ((RingedSite.toRingedTopos (smallEtaleRingedSite B X hX)).forgetRing.map
        g.fSharpInverseImage))).symm
  refine Eq.trans ?_ (congrArg (fun z => (SmallEtale.topology B Y hY).yonedaEquiv
      ((((SmallEtale.topology B Y hY).yonedaEquiv
        (F := Sheaf.ringSheaf (smallEtaleRingSheaf B hY))).symm (presCoord B hY V pres i)) ≫ z))
    ((congrArg (g.toToposHom.adj.homEquiv _ _)
        (RingedToposHom.fSharpInverseImage_forget_homEquiv g)).trans
      (Equiv.apply_symm_apply _ _))).symm
  refine Eq.trans ?_ ((SmallEtale.topology B Y hY).yonedaEquiv_comp
    (((SmallEtale.topology B Y hY).yonedaEquiv
        (F := Sheaf.ringSheaf (smallEtaleRingSheaf B hY))).symm (presCoord B hY V pres i))
    ((RingedSite.toRingedTopos (smallEtaleRingedSite B Y hY)).forgetRing.map g.fSharp)).symm
  exact congrArg _ (Equiv.apply_symm_apply _ _).symm

end Coord

section SheafHom

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (f : X ⟶ Y)
  (hf : (B.inclusion.map f).appTop =
    g.globalSectionsMap (SmallEtale.finalIsTerminal B X.obj X.property)
      (SmallEtale.finalIsTerminal B Y.obj Y.property))
  [IsAffine Y.obj] {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(Y.obj, ⊤)}
  (V : SmallEtale B Y.obj Y.property)
  [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)]
  (pres : StandardPresentationOver ((SmallEtale.toScheme B Y.obj Y.property).obj V)
    (schemeStructureHom B Y.obj Y.property V) P)

include hf in
/-- **The comparison followed by the Yoneda morphism of a pulled-back global function is the
generalized element of that function.**  For `t` a global function on the chart `V` of `Y`, write
`β'_t : h_{X ×_Y V} ⟶ 𝒪_X` for the Yoneda morphism of `t` pulled back along the projection
`AlgebraicGeometry.SmallEtale.baseChangeProj`.  Then

`comparisonSheafHom ≫ β'_t = comparisonElt t`.

No presentation is involved: both sides are read at a chart `U` of `X` and a section `s` of
`g⁻¹h_V` there, where the left-hand side is the pullback of `t` along the morphism of schemes
`AlgebraicGeometry.comparisonSchemeHom` and the right-hand side is
`AlgebraicGeometry.comparisonRingHom` at `t`, and those are the same by
`AlgebraicGeometry.toScheme_map_comparisonChartHom_comp_baseChangeProj`,
`AlgebraicGeometry.appTop_comparisonSchemeHom` and
`AlgebraicGeometry.comparisonRingHom_apply`.  The Yoneda morphism unfolds to a restriction map,
which is definitional for the structure presheaf of the small étale site.

Two things come out of this one identity.  At `t` the `i`-th coordinate function of a standard
presentation it is `AlgebraicGeometry.comparisonSheafHom_comp_yoneda`, the second `e`-free half of
clause (ii) of the third identification owed by step (3) of [Stacks Project, Tag 04I6].  At
arbitrary `t` it is the agreement of the two structure maps — the source's closing paragraph —
because the comparison is an isomorphism and so the identity can be read with
`comparisonSheafHom` moved to the other side; see
`AlgebraicGeometry.forgetFSharp_comp_pushforwardIsoOfAffineRepresentableComparison`.  The source
checks the closing paragraph on `B` and on the coordinate functions separately and appeals to
generation; here no generation argument is needed, because
`AlgebraicGeometry.comparisonRingHom` is defined at every `t` at once. -/
theorem comparisonSheafHom_comp_yoneda_elt
    (t : Γ((SmallEtale.toScheme B Y.obj Y.property).obj V, ⊤)) :
    comparisonSheafHom B g f hf V ≫
        ((SmallEtale.topology B X.obj X.property).yonedaEquiv
          (F := Sheaf.ringSheaf (smallEtaleRingSheaf B X.property))).symm
          ((SmallEtale.baseChangeProj B f V).appTop.hom t) =
      comparisonElt B X.property Y.property g V t := by
  refine Sheaf.hom_ext_sections fun U s => ?_
  rw [(sectionsFunctor (SmallEtale.topology B X.obj X.property) U).map_comp_apply,
    comparisonSheafHom_app_apply, Sheaf.sectionsFunctor_map_apply]
  change ((SmallEtale.toScheme B X.obj X.property).map
        (comparisonChartHom B g f hf V U s)).appTop.hom
      ((SmallEtale.baseChangeProj B f V).appTop.hom t) = _
  have h2 := toScheme_map_comparisonChartHom_comp_baseChangeProj B g f hf V U s
  have h3 := appTop_comparisonSchemeHom B g V U s
  rw [← h2, Scheme.Hom.comp_appTop] at h3
  refine Eq.trans (ConcreteCategory.congr_hom h3 t) ?_
  exact comparisonRingHom_apply B X.property Y.property g V U s t

include hf in
/-- **The comparison followed by the `i`-th coordinate function of the base-changed chart is the
`i`-th coordinate of the comparison.**  Writing `β'ᵢ : h_{X ×_Y V} ⟶ 𝒪_X` for the Yoneda morphism
of the global function on `X ×_Y V` obtained by pulling `AlgebraicGeometry.presCoord i` back along
the projection `AlgebraicGeometry.SmallEtale.baseChangeProj`,

`comparisonSheafHom ≫ β'ᵢ = comparisonCoord i`.

This is the second `e`-free half of clause (ii) of the third identification owed by step (3) of
[Stacks Project, Tag 04I6]: it says that reading the comparison's value as a point of `X ×_Y V`
and then taking its `i`-th coordinate returns the `i`-th coordinate the comparison was built from.
It is `AlgebraicGeometry.comparisonSheafHom_comp_yoneda_elt` at the `i`-th coordinate function,
the `i`-th coordinate of the comparison being the generalized element of that function
(`AlgebraicGeometry.comparisonCoord_eq_comparisonElt`). -/
theorem comparisonSheafHom_comp_yoneda (i : Fin n) :
    comparisonSheafHom B g f hf V ≫
        ((SmallEtale.topology B X.obj X.property).yonedaEquiv
          (F := Sheaf.ringSheaf (smallEtaleRingSheaf B X.property))).symm
          ((SmallEtale.baseChangeProj B f V).appTop.hom
            (presCoord B Y.property V pres i)) =
      comparisonCoord B X.property Y.property g V pres i :=
  (comparisonSheafHom_comp_yoneda_elt B g f hf V (presCoord B Y.property V pres i)).trans
    (comparisonCoord_eq_comparisonElt B X.property Y.property g V pres i).symm

end SheafHom

end AlgebraicGeometry

end
