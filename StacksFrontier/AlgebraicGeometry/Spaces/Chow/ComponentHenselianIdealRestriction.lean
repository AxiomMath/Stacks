module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentHenselianIdealIncidence

/-!
# The component ideals, with the quotient maps computing restriction of germs

Let `X` be a decent algebraic space over `S`, let `x` be a point of it, write `A = 𝒪^h_{X, x}`
for the henselian local ring of Stacks 0ENK there, and let `V` be an elementary étale
neighborhood of `x`. For closed subspaces `X_i ⊆ X` whose point sets are the irreducible
components of `|X|` through `x`,
`AlgebraicGeometry.Space.exists_componentIdealFamily_ringEquiv_le_iff` produces one family of
ideals `I i` of `A` carrying both the presentations `A ⧸ I i ≅ 𝒪^h_{X_i, ξ i}` and the incidence
of the branches, the isomorphisms being produced existentially.

This file records their behaviour. The maps `A → A ⧸ I i ≅ 𝒪^h_{X_i, ξ i}` compute
*restriction*: the class of the image in `A` of a germ `a` at the distinguished point of `V` is
the image in `𝒪^h_{X_i, ξ i}` of the restriction of `a` to the base-change chart `V ×_X X_i`.

## Main results

* `AlgebraicGeometry.Space.componentIdealFamily_ringEquiv_stalkToHenselianLocalRing_le_iff`:
  **the one family, with the elementwise compatibility.** For points `w i` of the base changes
  `V ×_X X_i` over the distinguished point of `V` and over `ξ i`, the ideals
  `I i = (ker 𝒪_{V, V.point} → 𝒪_{V ×_X X_i, w i}) · A` carry isomorphisms
  `e i : A ⧸ I i ≅ 𝒪^h_{X_i, ξ i}` with

    `e i (mk (I i) (σ_V a)) = σ_{V ×_X X_i} (α i a)`   for every germ `a` at `V.point`,

  `σ` being the canonical maps of Stacks 0EMY and `α i` the Zariski stalk map of the projection,
  together with the incidence of the branches.
* `AlgebraicGeometry.Space.exists_componentIdealFamily_ringEquiv_stalkToHenselianLocalRing_le_iff`:
  the same with the points of the base changes quantified existentially, which is the form in
  which it strengthens `AlgebraicGeometry.Space.exists_componentIdealFamily_ringEquiv_le_iff`.
* `exists_ringEquiv_henselianLocalRing_quotient_sectionsToHenselianLocalRing`:
  the compatibility on *global sections* of the chart rather than germs — the class of the image
  of a section `s` of `𝒪_V` goes to the image of the section `j^♯ s` of `𝒪_U`, for any chart `U`
  of `X'` and any `j : U.scheme ⟶ V.scheme` surjective on stalks, in particular for the
  base-change chart and its projection.

## Implementation notes

The ideals are *not* quantified existentially here; they are the formula in the chosen points
`w i` of the base changes that
`AlgebraicGeometry.Space.exists_componentIdealFamily_ringEquiv_le_iff` chooses inside its proof.
That is forced: the compatibility mentions the chart `V ×_X X_i` and the restriction map `α i`,
both of which are formulas in `w i`, so a statement that forgets `w i` cannot state it. The
existential form quantifies `w i` together with everything said about it.

## References

* [Stacks Project, Tag 05WQ](https://stacks.math.columbia.edu/tag/05WQ)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXd : IsDecentSpace B S hS X) (x : points B S hS X)
    (V : ElementaryEtaleNeighborhood B S hS X hX x)

/-! ### The one family, with the quotient maps computing restriction -/

include hX hXd in
/-- **One family of component ideals, carrying the quotient presentations with their behaviour
on germs, and the incidence.** Let `X` be a decent algebraic space over `S`, let `x` be a point
of it and let `V` be an elementary étale neighborhood of `x`. Let `X_i ⊆ X` be closed subspaces
whose point sets are irreducible components of `|X|`, with points `ξ i` of `X_i`, and let `w i`
be a point of the base change `V ×_X X_i` lying over `ξ i` and over the distinguished point of
`V`. Write `α i : 𝒪_{V, V.point} → 𝒪_{V ×_X X_i, w i}` for the Zariski stalk map of the
projection and `I i = (ker α i) · A` for the ideal it generates in `A = 𝒪^h_{X, x}`. Then for
every `i`

* there is a ring isomorphism `e i : A ⧸ I i ≅ 𝒪^h_{X_i, ξ i}` carrying the class of the image
  in `A` of a germ `a` at `V.point` to the image in `𝒪^h_{X_i, ξ i}` of its restriction
  `α i a`, and
* a branch `𝔮` of `A` contains `I i` exactly when the irreducible component of `|X|` on which
  `𝔮` lies is `|X_i|`. -/
theorem componentIdealFamily_ringEquiv_stalkToHenselianLocalRing_le_iff {ι : Type*}
    (Y : ι → Subfunctor X) (hY : ∀ i, IsClosedSubspace B S hS (Y i))
    (hYd : ∀ i, IsDecentSpace B S hS (Y i).toFunctor)
    (hYcomp : ∀ i, subspacePointSet B S hS X (Y i) ∈
      irreducibleComponents (points B S hS X))
    (ξ : ∀ i, points B S hS (Y i).toFunctor)
    (w : ∀ i, ((hY i).2.rep.pullback V.toSpace).left.1)
    (hw : ∀ i, pointsMap B S hS (yoneda.obj ((hY i).2.rep.pullback V.toSpace))
        ((hY i).2.rep.fst V.toSpace)
        (presheafPoint B S hS ((hY i).2.rep.pullback V.toSpace) (w i)
          (B.residueField_spec_contains ((hY i).2.rep.pullback V.toSpace).left.property (w i))) =
      ξ i)
    (hpw : ∀ i, ((hY i).2.rep.snd V.toSpace).left.1 (w i) = V.point) :
    letI := elementaryEtaleChartStalkAlgebra B S hS hX hXd x V
    letI := flat_elementaryEtaleChartStalk B S hS hX hXd x V
    (∀ i, ∃ e : ((henselianLocalRing B S hS X hX x hXd : Type (u + 1)) ⧸
          (RingHom.ker ((V.scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
            ((hY i).2.rep.snd V.toSpace).left.1.stalkMap (w i)).hom).map
            (stalkToHenselianLocalRing B S hS X hX x hXd V)) ≃+*
        (henselianLocalRing B S hS (Y i).toFunctor (hY i).1 (ξ i) (hYd i) : Type (u + 1)),
      ∀ a : V.scheme.left.1.presheaf.stalk V.point,
        e (Ideal.Quotient.mk _ (stalkToHenselianLocalRing B S hS X hX x hXd V a)) =
          stalkToHenselianLocalRing B S hS (Y i).toFunctor (hY i).1 (ξ i) (hYd i)
            (closedImmersionBaseChangeNeighborhood B S hS (hY i).1 (hY i).2 V (w i) (hw i)
              (hpw i))
            (((V.scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
              ((hY i).2.rep.snd V.toSpace).left.1.stalkMap (w i)).hom a)) ∧
      ∀ (i : ι) (q : {q : PrimeSpectrum ↥(henselianLocalRing B S hS X hX x hXd) //
          q.asIdeal ∈ minimalPrimes ↥(henselianLocalRing B S hS X hX x hXd)}),
        (RingHom.ker ((V.scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
            ((hY i).2.rep.snd V.toSpace).left.1.stalkMap (w i)).hom).map
            (stalkToHenselianLocalRing B S hS X hX x hXd V) ≤ q.1.asIdeal ↔
          ((componentOfFlatBranch B S hS hX hXd V.chart V.point
              ↥(henselianLocalRing B S hS X hX x hXd) q).1 :
            irreducibleComponents (points B S hS X)).1 = subspacePointSet B S hS X (Y i) := by
  let := elementaryEtaleChartStalkAlgebra B S hS hX hXd x V
  let := flat_elementaryEtaleChartStalk B S hS hX hXd x V
  refine ⟨fun i => ?_, fun i q => ?_⟩
  · exact exists_ringEquiv_henselianLocalRing_quotient_stalkToHenselianLocalRing_rep_snd B S hS
      hX hXd (hY i).1 (hYd i) (hY i).2 V (w i) (hw i) (hpw i)
  · exact componentIdeal_le_iff_componentOfFlatBranch_of_proj_eq B S hS hX hXd (Y i) (hY i)
      (hYcomp i) V.chart (w i) V.point (hpw i) _ q

include hX hXd in
/-- **The one family with the elementwise compatibility, with the points of the base changes
quantified existentially.** This is
`AlgebraicGeometry.Space.componentIdealFamily_ringEquiv_stalkToHenselianLocalRing_le_iff` with
the points `w i` of the base changes `V ×_X X_i`, lying over `ξ i` and over the distinguished
point of `V`, quantified existentially. -/
theorem exists_componentIdealFamily_ringEquiv_stalkToHenselianLocalRing_le_iff {ι : Type*}
    (Y : ι → Subfunctor X) (hY : ∀ i, IsClosedSubspace B S hS (Y i))
    (hYd : ∀ i, IsDecentSpace B S hS (Y i).toFunctor)
    (hYcomp : ∀ i, subspacePointSet B S hS X (Y i) ∈
      irreducibleComponents (points B S hS X))
    (ξ : ∀ i, points B S hS (Y i).toFunctor)
    (hx : ∀ i, pointsMap B S hS (Y i).toFunctor (Y i).ι (ξ i) = x) :
    letI := elementaryEtaleChartStalkAlgebra B S hS hX hXd x V
    letI := flat_elementaryEtaleChartStalk B S hS hX hXd x V
    ∃ (w : ∀ i, ((hY i).2.rep.pullback V.toSpace).left.1)
        (hw : ∀ i, pointsMap B S hS (yoneda.obj ((hY i).2.rep.pullback V.toSpace))
            ((hY i).2.rep.fst V.toSpace)
            (presheafPoint B S hS ((hY i).2.rep.pullback V.toSpace) (w i)
              (B.residueField_spec_contains ((hY i).2.rep.pullback V.toSpace).left.property
                (w i))) =
          ξ i)
        (hpw : ∀ i, ((hY i).2.rep.snd V.toSpace).left.1 (w i) = V.point),
      (∀ i, ∃ e : ((henselianLocalRing B S hS X hX x hXd : Type (u + 1)) ⧸
            (RingHom.ker ((V.scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
              ((hY i).2.rep.snd V.toSpace).left.1.stalkMap (w i)).hom).map
              (stalkToHenselianLocalRing B S hS X hX x hXd V)) ≃+*
          (henselianLocalRing B S hS (Y i).toFunctor (hY i).1 (ξ i) (hYd i) : Type (u + 1)),
        ∀ a : V.scheme.left.1.presheaf.stalk V.point,
          e (Ideal.Quotient.mk _ (stalkToHenselianLocalRing B S hS X hX x hXd V a)) =
            stalkToHenselianLocalRing B S hS (Y i).toFunctor (hY i).1 (ξ i) (hYd i)
              (closedImmersionBaseChangeNeighborhood B S hS (hY i).1 (hY i).2 V (w i) (hw i)
                (hpw i))
              (((V.scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
                ((hY i).2.rep.snd V.toSpace).left.1.stalkMap (w i)).hom a)) ∧
        ∀ (i : ι) (q : {q : PrimeSpectrum ↥(henselianLocalRing B S hS X hX x hXd) //
            q.asIdeal ∈ minimalPrimes ↥(henselianLocalRing B S hS X hX x hXd)}),
          (RingHom.ker ((V.scheme.left.1.presheaf.stalkCongr (.of_eq (hpw i).symm)).hom ≫
              ((hY i).2.rep.snd V.toSpace).left.1.stalkMap (w i)).hom).map
              (stalkToHenselianLocalRing B S hS X hX x hXd V) ≤ q.1.asIdeal ↔
            ((componentOfFlatBranch B S hS hX hXd V.chart V.point
                ↥(henselianLocalRing B S hS X hX x hXd) q).1 :
              irreducibleComponents (points B S hS X)).1 =
              subspacePointSet B S hS X (Y i) := by
  let := elementaryEtaleChartStalkAlgebra B S hS hX hXd x V
  let := flat_elementaryEtaleChartStalk B S hS hX hXd x V
  choose w hw hpw using fun i => exists_point_closedImmersionBaseChangeNeighborhood B S hS hX
    (hY i).1 (hYd i) (Y i).ι (hY i).2 (ξ i) x (hx i) V
  exact ⟨w, hw, hpw, componentIdealFamily_ringEquiv_stalkToHenselianLocalRing_le_iff B S hS hX
    hXd x V Y hY hYd hYcomp ξ w hw hpw⟩

/-! ### The compatibility on global sections of the chart -/

include hX hXd in
/-- **The quotient presentation computes restriction of global sections of the chart.** Let `V`
be an elementary étale neighborhood of a point `x` of `X`, let `U` be an elementary étale
neighborhood of a point `ξ` of `X'`, and let `j : U.scheme ⟶ V.scheme` carry the distinguished
point to the distinguished point with surjective Zariski stalk map `α`. Then the isomorphism

  `e : 𝒪^h_{X, x} ⧸ (ker α) · 𝒪^h_{X, x} ≅ 𝒪^h_{X', ξ}`

carries the class of the image in `𝒪^h_{X, x}` of a *global section* `s` of `𝒪_V` to the image
in `𝒪^h_{X', ξ}` of the global section `j^♯ s` of `𝒪_U`. -/
theorem exists_ringEquiv_henselianLocalRing_quotient_sectionsToHenselianLocalRing
    {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX'd : IsDecentSpace B S hS X')
    {ξ : points B S hS X'}
    (U : ElementaryEtaleNeighborhood B S hS X' hX' ξ) (j : U.scheme ⟶ V.scheme)
    (hj : j.left.1 U.point = V.point)
    (hsurj : Function.Surjective ((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
      j.left.1.stalkMap U.point).hom) :
    ∃ e : ((henselianLocalRing B S hS X hX x hXd : Type (u + 1)) ⧸
          (RingHom.ker ((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
            j.left.1.stalkMap U.point).hom).map
            (stalkToHenselianLocalRing B S hS X hX x hXd V)) ≃+*
        (henselianLocalRing B S hS X' hX' ξ hX'd : Type (u + 1)),
      ∀ s : Γ(V.scheme.left.1, ⊤),
        e (Ideal.Quotient.mk _ (stalkToHenselianLocalRing B S hS X hX x hXd V
            ((V.scheme.left.1.presheaf.germ ⊤ V.point trivial).hom s))) =
          stalkToHenselianLocalRing B S hS X' hX' ξ hX'd U
            ((U.scheme.left.1.presheaf.germ ⊤ U.point trivial).hom
              ((j.left.1.appTop).hom s)) := by
  obtain ⟨e, he⟩ := exists_ringEquiv_henselianLocalRing_quotient_stalkToHenselianLocalRing B S hS
    hX hXd hX' hX'd V U j hj hsurj
  refine ⟨e, fun s => (he _).trans (congrArg _ ?_)⟩
  rw [CommRingCat.hom_comp, RingHom.comp_apply,
    show ((V.scheme.left.1.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom).hom
          ((V.scheme.left.1.presheaf.germ ⊤ V.point trivial).hom s) =
        (V.scheme.left.1.presheaf.germ ⊤ (j.left.1 U.point) trivial).hom s from
      congrArg (fun φ : V.scheme.left.1.presheaf.obj (Opposite.op ⊤) ⟶ _ => φ.hom s)
        (V.scheme.left.1.presheaf.germ_stalkSpecializes (U := ⊤) trivial
          (Inseparable.of_eq hj.symm).ge)]
  exact Scheme.Hom.germ_stalkMap_apply j.left.1 ⊤ U.point trivial s

end AlgebraicGeometry.Space

end
