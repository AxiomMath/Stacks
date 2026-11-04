module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStructureMapChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoProjectionDescent

/-!
# The chart projections of a 2-isomorphism of small étale ringed topoi agree on functions

Let `a, b : X ⟶ Y` be two representable morphisms of algebraic spaces over a scheme `S` whose
morphisms of small étale ringed topoi are 2-isomorphic.  For every étale scheme chart `V` of `Y`
the 2-isomorphism produces an isomorphism `ε_V : X ×_{Y,b} V ≅ X ×_{Y,a} V` of étale scheme
charts of `X`; this file shows that `ε_V` followed by the cartesian projection
`π_a : X ×_{Y,a} V ⟶ V` and the cartesian projection `π_b : X ×_{Y,b} V ⟶ V` induce the *same
map on regular functions*.

That is the whole use the source makes of the structure maps `a^♯` and `b^♯`: the compatibility
of the 2-isomorphism with them says exactly that the two projections pull functions back the
same way.

## Main results

* `AlgebraicGeometry.Space.chartComparison_structureSharp`: **the transport of the chart formula
  for `f^♯` along the comparison of the direct image with chart base change** — for a
  representable `f`, reading `f^♯` over an étale chart `V` of `Y` through that comparison gives
  pullback of regular functions along the cartesian projection `X ×_Y V ⟶ V`.
* `AlgebraicGeometry.Space.exists_smallBaseChange_iso_gamma_projection`: from a 2-isomorphism of
  the morphisms of small étale ringed topoi of two representable morphisms, an isomorphism of
  the chart base-change functors whose composite with the one cartesian projection pulls
  regular functions back as the other cartesian projection does.

## Implementation notes

The comparison used here is not the one of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representable` but
`AlgebraicGeometry.Space.chartComparison`, which factors the direct image through its right Kan
extension form.  The two have the same endpoints, but only the second is computable on
sections — that is the point of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartComparison.lean` — and
`AlgebraicGeometry.Space.structureSharp_comp_chartRanIso` already identifies the structure map
read through it with `AlgebraicGeometry.Space.smallBaseChangeSharp`, whose sections are pullback
along the cartesian projection by construction.  What is added here is reading that identity on
sections and at the universe of sheaves of sets, which is the form in which a 2-morphism of
ringed topoi acts.

The corepresentability step is
`AlgebraicGeometry.Space.exists_natIso_of_pushforward_iso`, proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleTwoIsoChartComparison.lean`: the small étale
topology of an algebraic space is subcanonical, so an isomorphism of the two direct images is
restriction along an isomorphism of the two base-change functors.

The passage from the equality of the two pullback maps on regular functions to the equality of
the two morphisms of schemes `ε_V ≫ π_a = π_b` is not here: over an *affine* chart `V` it is
the universal property of an affine scheme
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleTwoIsoAffineChart.lean`), and the passage from
the affine charts to a surjective one — which is what finishes Stacks 04M6 — is
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleTwoIsoAffineCover.lean`.

## References

* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- For a representable morphism, the comparison of the direct image of sheaves of sets with
restriction along base change of étale scheme charts, in the form which is computable on
sections: the right Kan extension form of the direct image followed by the chart projection to
the base-changed chart. -/
noncomputable def chartComparison (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom) :
    letI := isContinuous_smallBaseChange B S hS f hf
    smallEtaleDirectImage B S hS f ≅
      (smallBaseChange B S hS f hf).sheafPushforwardContinuous (Type u)
        (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1) :=
  letI := isContinuous_smallBaseChange B S hS f hf
  smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf

/-- `AlgebraicGeometry.Space.chartComparison` is the right Kan extension form of the direct
image followed by the chart projection; the identity is definitional and is recorded so that
the sections of the comparison can be rewritten without unfolding the definition. -/
theorem chartComparison_hom_app (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    letI := isContinuous_smallBaseChange B S hS f hf
    (chartComparison B S hS f hf).hom.app P =
      (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom.app P :=
  rfl

/-- The structure map of the morphism of small étale ringed *sites* attached to a representable
morphism, read on sections of underlying sheaves of sets: pullback of regular functions along
the cartesian projection, by construction. -/
theorem smallBaseChangeSharp_app_apply (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (s : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    letI := isContinuous_smallBaseChange B S hS f hf
    ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
        (smallBaseChangeSharp B S hS f hf)).hom.app (op V) s =
      (forget CommRingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op) s :=
  rfl

/-- **The chart formula for `f^♯`, transported along the chart comparison.** For a representable
morphism `f : X ⟶ Y` the structure map `f^♯`, read over an étale scheme chart `V` of `Y` through
`AlgebraicGeometry.Space.chartComparison`, is pullback of regular functions along the cartesian
projection `X ×_Y V ⟶ V`. -/
theorem chartComparison_structureSharp (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (s : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    ((chartComparison B S hS f hf).hom.app (structureSetSheaf B S hS X)).hom.app (op V)
        (((smallEtaleRingedTopos B S hS Y).forgetRing.map
          (smallEtaleRingedToposHom B S hS f).fSharp).hom.app (op V) s) =
      (forget CommRingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op) s := by
  let := isContinuous_smallBaseChange B S hS f hf
  have h1 := congrArg (fun m ↦ (sheafCompose (SmallEtale.topology B S hS Y.1)
    (forget RingCat.{u})).map m) (structureSharp_comp_chartRanIso B S hS f hf)
  simp only [CategoryTheory.Functor.map_comp, ringSheafMap_pullbackRingSheafMapOfNatTrans,
    restrictionRingIso_hom_ringSheafMap] at h1
  have h2 := CategoryTheory.Sheaf.hom_congr_app_apply h1 (op V) s
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply] at h2
  rw [forgetRing_map_fSharp, chartComparison_hom_app]
  exact h2.trans (smallBaseChangeSharp_app_apply B S hS f hf V s)

/-- From a 2-isomorphism of the morphisms of small étale ringed topoi of two representable
morphisms `a, b : X ⟶ Y`, an isomorphism of the two chart base-change functors such that the
cartesian projection of `a`, precomposed with it, pulls regular functions back exactly as the
cartesian projection of `b` does.

This is Stacks 04M6 up to the step from that equality of pullbacks to the equality of the two
morphisms of schemes; see the implementation notes. -/
theorem exists_smallBaseChange_iso_gamma_projection (a b : X ⟶ Y)
    (ha : yoneda.relativelyRepresentable a.hom) (hb : yoneda.relativelyRepresentable b.hom)
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS a) (smallEtaleRingedToposHom B S hS b)) :
    letI := isContinuous_smallBaseChange B S hS a ha
    letI := isContinuous_smallBaseChange B S hS b hb
    ∃ e : smallBaseChange B S hS b hb ≅ smallBaseChange B S hS a ha,
      ∀ (V : SmallEtale B S hS Y.1) (s : (structureSetSheaf B S hS Y).obj.obj (op V)),
        (forget CommRingCat.{u}).map
            (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
              ((e.hom.app V).hom.left ≫ ha.snd V.1.hom)).op) s =
          (forget CommRingCat.{u}).map
            (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hb.snd V.1.hom)).op) s := by
  let := isContinuous_smallBaseChange B S hS a ha
  let := isContinuous_smallBaseChange B S hS b hb
  let : (SmallEtale.topology B S hS X.1).Subcanonical :=
    smallEtaleTopology_subcanonical B S hS X
  let te : smallEtaleDirectImage B S hS a ≅ smallEtaleDirectImage B S hS b := t.e
  obtain ⟨e, he⟩ := exists_natIso_of_pushforward_iso (SmallEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS X.1) (smallBaseChange B S hS a ha)
    (smallBaseChange B S hS b hb)
    ((chartComparison B S hS a ha).symm ≪≫ te ≪≫ chartComparison B S hS b hb)
  refine ⟨e, fun V s => ?_⟩
  set H := structureSetSheaf B S hS X with hH
  set ya := (((smallEtaleRingedTopos B S hS Y).forgetRing.map
    (smallEtaleRingedToposHom B S hS a).fSharp).hom.app (op V) s) with hya
  set yb := (((smallEtaleRingedTopos B S hS Y).forgetRing.map
    (smallEtaleRingedToposHom B S hS b).fSharp).hom.app (op V) s) with hyb
  set xa := ((chartComparison B S hS a ha).hom.app H).hom.app (op V) ya with hxa
  have hinv : ((chartComparison B S hS a ha).inv.app H).hom.app (op V) xa = ya := by
    have h := CategoryTheory.Sheaf.iso_inv_hom_app_apply
      ((chartComparison B S hS a ha).app H) (op V) ya
    exact h
  have hcomm : (te.hom.app H).hom.app (op V) ya = yb :=
    CategoryTheory.Sheaf.hom_congr_app_apply t.commutes (op V) s
  have hLHS : (((chartComparison B S hS a ha).symm ≪≫ te ≪≫
        chartComparison B S hS b hb).hom.app H).hom.app (op V) xa =
      (forget CommRingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hb.snd V.1.hom)).op) s := by
    have hc : ((chartComparison B S hS a ha).symm ≪≫ te ≪≫
          chartComparison B S hS b hb).hom =
        (chartComparison B S hS a ha).inv ≫ te.hom ≫
          (chartComparison B S hS b hb).hom := by
      simp only [Iso.trans_hom, Iso.symm_hom]
    rw [NatTrans.congr_app hc H]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, types_comp_apply]
    rw [hinv, hcomm]
    exact chartComparison_structureSharp B S hS b hb V s
  have hRHS : H.obj.map (op (e.hom.app V)) xa =
      (forget CommRingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          ((e.hom.app V).hom.left ≫ ha.snd V.1.hom)).op) s := by
    rw [hxa, chartComparison_structureSharp B S hS a ha V s]
    rfl
  exact hRHS.symm.trans ((he H V xa).symm.trans hLHS)

end AlgebraicGeometry.Space

end
