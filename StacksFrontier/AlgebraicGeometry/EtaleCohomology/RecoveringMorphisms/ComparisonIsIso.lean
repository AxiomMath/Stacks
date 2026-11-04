module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.ComparisonFiberSolutionMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkIsomorphismCriterion

/-!
# The comparison of step (3) of Stacks 04I6 is an isomorphism

Clauses (i) and (ii) of the third identification owed by step (3) of [Stacks Project, Tag 04I6]
compute the fibre at a geometric point `x̄` of `X` of the comparison
`AlgebraicGeometry.comparisonSheafHom : g⁻¹h_V ⟶ h_{X ×_Y V}` as the solution-set map of
[Stacks Project, Tag 04GX].  This file packages that as an isomorphism.

Two things have to happen.  The clauses compute the fibre map only on elements of the form
`e.hom.app (germ of 𝟙_V)`; since `e.hom.app` and the identification of the fibre of a
representable sheaf with the set of lifts are bijections, every element is of that form, so the
fibre map is *conjugate* to the solution map and bijectivity transfers.  Then the geometric points
of the small étale site are a conservative family, so bijectivity at all of them gives `IsIso`.

The geometric point `ȳ` of `Y` and the isomorphism `e` of stalk functors are chosen inside the
proof rather than carried in the statement; that is what makes the result consumable.

## Main results

* `AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso_comp_etaleCoefficientGerm_schemeHom` —
  clause (i) in the spelling the solution subtypes use.
* `AlgebraicGeometry.bijective_etaleLocalSolutionMap` — [Stacks Project, Tag 04GX] as a bijection
  of those subtypes.
* `AlgebraicGeometry.bijective_sheafFiber_map_comparisonSheafHom` — the fibre of the comparison at
  a geometric point is bijective.
* `AlgebraicGeometry.isIso_comparisonSheafHom` — **the comparison is an isomorphism.**

## What this does not do

Nothing here carries a `@[stacks 04I6]` tag, and the comparison is produced only at the *affine*
étale charts of `Y`; it never is produced at a non-affine one, since recovering it from its
restriction to the affine charts would be cancellation on the left, which is false.  The tag is
nonetheless closed, because what is transported to all charts is the isomorphism of *direct
images* and not the comparison: the standard-presentation hypothesis below is discharged at every
affine chart by `Stacks.EtaleCohomology.exists_standardPresentationOverSmallEtale` and the result
assembled in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineExistence.lean`, where
[Stacks Project, Tag 04I6] is `AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_isLocallyRinged`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open AlgebraicGeometry.SmallEtale Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (x : GeometricPoint X.obj) (y : GeometricPoint Y.obj)
  (e : (geometricPointSitePoint B Y.obj Y.property y).sheafFiber (A := Type u) ≅
    g.toToposHom.inverseImage ⋙
      (geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))
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
/-- **The coefficient maps of the two solution sets agree, in the spelling the subtypes use.**
Clause (i) of the third identification of step (3) of [Stacks Project, Tag 04I6]
(`AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso_comp_etaleCoefficientGerm`) gives
`φ ∘ γ_Y = γ_X ∘ φ_glob`; since `f` is chosen with `f^♯ = φ_glob` this is the coefficient map of
`AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions`, which is the form needed to
identify the target of [Stacks Project, Tag 04GX] with the set of lifts to `X ×_Y V`. -/
theorem etaleLocalRingHomOfSheafFiberIso_comp_etaleCoefficientGerm_schemeHom :
    (etaleLocalRingHomOfSheafFiberIso B g x y e).comp
        (etaleCoefficientGerm B Y.obj Y.property y) =
      (etaleCoefficientGerm B X.obj X.property x).comp
        (B.inclusion.map f).appTop.hom :=
  (etaleLocalRingHomOfSheafFiberIso_comp_etaleCoefficientGerm B g x y e).trans
    (congrArg (fun φ : Γ(Y.obj, ⊤) ⟶ Γ(X.obj, ⊤) =>
      (etaleCoefficientGerm B X.obj X.property x).comp φ.hom) hf.symm)

include hf in
/-- **[Stacks Project, Tag 04GX] as a bijection of the two solution subtypes.**
`AlgebraicGeometry.bijOn_etaleLocalSolutions_etaleLocalRingHom` is a `Set.BijOn` between the
solutions of `P` in the two étale local rings; this is the same statement with the sets replaced by
the subtypes that the two fibre computations produce, the target coefficient map being rewritten by
the clause (i) identification above. -/
theorem bijective_etaleLocalSolutionMap (hg : g.IsLocallyRinged) :
    Function.Bijective
      (fun a : EtaleLocalSolutions B Y.obj Y.property y P =>
        (⟨fun i => etaleLocalRingHomOfSheafFiberIso B g x y e (a.1 i), by
            have h := (bijOn_etaleLocalSolutions_etaleLocalRingHom B g x y e pres hg).1 a.2
            rw [etaleLocalRingHomOfSheafFiberIso_comp_etaleCoefficientGerm_schemeHom
              B g x y e f hf] at h
            exact h⟩ :
          {b : Fin n → ↥(etaleLocalRing B X.obj X.property x) //
            MvPolynomial.IsSolution P
              ((etaleCoefficientGerm B X.obj X.property x).comp
                (B.inclusion.map f).appTop.hom) b})) := by
  have hbij := bijOn_etaleLocalSolutions_etaleLocalRingHom B g x y e pres hg
  constructor
  · intro a b hab
    exact Subtype.ext (hbij.2.1 a.2 b.2 (congrArg Subtype.val hab))
  · intro b
    have hb : b.1 ∈ {c | MvPolynomial.IsSolution P
        ((etaleLocalRingHomOfSheafFiberIso B g x y e).comp
          (etaleCoefficientGerm B Y.obj Y.property y)) c} := by
      rw [Set.mem_setOf_eq,
        etaleLocalRingHomOfSheafFiberIso_comp_etaleCoefficientGerm_schemeHom B g x y e f hf]
      exact b.2
    obtain ⟨a, ha, hfa⟩ := hbij.2.2 hb
    exact ⟨⟨a, ha⟩, Subtype.ext hfa⟩

include hf pres in
/-- **Assembly step 1: the fibre of the comparison at a geometric point of `X` is bijective.**
Clauses (i) and (ii) of the third identification of step (3) of [Stacks Project, Tag 04I6]
compute that fibre on elements of the form `e.hom.app (germ of 𝟙_V)`, and every element of the
source fibre is of that form because `e.hom.app` and the identification of the fibre of a
representable sheaf with the set of lifts
(`AlgebraicGeometry.yonedaIso_symm_eq_toPresheafFiber_id`) are both bijections.  So the fibre map
is conjugate, through the two solution-set identifications, to the solution map of
[Stacks Project, Tag 04GX], which is bijective.

The geometric point `ȳ` of `Y` and the identification `e` of stalk functors are *chosen* here, by
`AlgebraicGeometry.exists_geometricPoint_inverseImage_comp_sheafFiber_iso`, rather than carried in
the statement — which is what makes this consumable by the iso-detection criterion. -/
theorem bijective_sheafFiber_map_comparisonSheafHom (hg : g.IsLocallyRinged) :
    Function.Bijective (((geometricPointSitePoint B X.obj X.property x).sheafFiber
      (A := Type u)).map (comparisonSheafHom B g f hf V)) := by
  obtain ⟨y', ⟨i0⟩⟩ := exists_geometricPoint_inverseImage_comp_sheafFiber_iso B
    X.property Y.property g.toToposHom x
  have e' := i0.symm
  set E₁ := (((yonedaCompEtaleStalkPresheafFunctorIso B Y.obj Y.property y').app V).toEquiv).symm
    |>.trans (e'.app ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V)).toEquiv
  set E₂ := (((yonedaCompEtaleStalkPresheafFunctorIso B X.obj X.property x).app
      ((smallEtaleBaseChange B f).obj V)).toEquiv).trans
    (baseChangeGeometricPointFiberEquivSolutions B f V pres x)
  have hb : Function.Bijective (E₂ ∘
      ((geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u)).map
        (comparisonSheafHom B g f hf V) ∘ E₁) := by
    convert (bijective_etaleLocalSolutionMap B g x y' e' f hf V pres hg).comp
      (geometricPointFiberEquivEtaleLocalSolutions B Y.obj Y.property y' V pres).bijective using 1
    funext u
    refine Subtype.ext (funext fun i => ?_)
    refine (congrArg (fun z => (E₂ ((((geometricPointSitePoint B X.obj X.property x).sheafFiber
        (A := Type u)).map (comparisonSheafHom B g f hf V))
          ((e'.app ((SmallEtale.topology B Y.obj Y.property).yoneda.obj V)).toEquiv z))).1 i)
      (yonedaIso_symm_eq_toPresheafFiber_id B Y.obj Y.property y' V u)).trans ?_
    exact baseChangeGeometricPointFiberEquivSolutions_comparisonSheafHom_apply
      B g x y' e' f hf V pres u i
  exact (Equiv.bijective_comp E₁ _).mp ((Equiv.comp_bijective _ E₂).mp hb)

include hf pres in
/-- **The comparison of step (3) of [Stacks Project, Tag 04I6] is an isomorphism.**  For a
*locally* ringed morphism `(g, g^♯)` of the small étale ringed topoi, an affine `Y`, an affine
étale chart `V` of `Y` carrying a standard presentation, and `f` the morphism of schemes chosen in
the first paragraph of the source's proof,

`g⁻¹h_V ≅ h_{X ×_Y V}`.

This is the conclusion of step (3): the fibre at every geometric point of `X` is bijective by
`AlgebraicGeometry.bijective_sheafFiber_map_comparisonSheafHom`, and the geometric points of the
small étale site are a conservative family, so
`AlgebraicGeometry.isIso_iff_forall_bijective_geometricSheafFiber` applies.

It is not itself [Stacks Project, Tag 04I6]: the comparison is available only at the *affine*
étale charts of `Y`, and the passage to all of them is the source's appeal to
[Stacks Project, Tag 04HR], which transports the isomorphism of *direct images* rather than the
comparison — `AlgebraicGeometry.pushforwardIsoOfAffineRepresentableComparison`.  Fed that, with
the standard presentation obtained from
`Stacks.EtaleCohomology.exists_standardPresentationOverSmallEtale` at each affine chart, the tag
follows: `AlgebraicGeometry.existsUnique_schemeHom_twoIso_of_isLocallyRinged` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/RecoveringMorphisms/AffineExistence.lean`. -/
theorem isIso_comparisonSheafHom (hg : g.IsLocallyRinged) :
    IsIso (comparisonSheafHom B g f hf V) :=
  (isIso_iff_forall_bijective_geometricSheafFiber B X.obj X.property
    (comparisonSheafHom B g f hf V)).2 fun p =>
      bijective_sheafFiber_map_comparisonSheafHom B g (GeometricPoint.ofPoint X.obj p) f hf V
        pres hg

end AlgebraicGeometry

end
