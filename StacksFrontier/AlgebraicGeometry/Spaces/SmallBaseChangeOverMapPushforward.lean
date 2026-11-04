module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentableComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMap

/-!
# The chart value of the direct-image map is pullback along the base-changed morphism

Let `X` be an algebraic space, `f : Y ⟶ Z` a morphism of algebraic spaces over `X` whose two
structure morphisms are representable, and `V` an étale scheme chart of `X`.
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` identifies the sections of the
direct-image algebras over `V` with the global regular functions on the base-changed charts
`Y ×_X V` and `Z ×_X V`, so the component at `V` of
`AlgebraicGeometry.Space.pushforwardRingMap f` becomes a ring map
`Γ(Z ×_X V) ⟶ Γ(Y ×_X V)`.  **This file proves that it is pullback of regular functions along
`AlgebraicGeometry.Space.smallBaseChangeOverMap`, the base change of `f` to the chart.**

What was available before is the same equality after precomposition with pullback along the
cartesian projection `Z ×_X V ⟶ V`
(`AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_pushforwardRingMap_app_eq`), the
triangle over the base, and the equality itself under the hypothesis that that precomposition is
surjective (`AlgebraicGeometry.Space.pushforwardRingMap_app_eq_of_surjective`).  The result
below carries no hypothesis beyond representability of the two structure morphisms, which is
what the faithfulness clause of Stacks 081V in the chart presentation needs.

## Main results

* `AlgebraicGeometry.Space.smallBaseChangeComp_hom_app_snd`: the component of
  `AlgebraicGeometry.Space.smallBaseChangeComp` commutes with the cartesian projections to the
  original chart.  Compatibility with the projections to the *source space* is the triangle over
  the chart and comes for free; this is the other half, and it is what makes the composition law
  of chart base change a comparison of fibre products rather than merely a morphism of charts.
* `AlgebraicGeometry.Space.smallBaseChangeComp_hom_app_left_comp`: **the factorisation.**  The
  cartesian projection `Y ×_Z (Z ×_X V) ⟶ Z ×_X V` is the component of
  `AlgebraicGeometry.Space.smallBaseChangeComp` followed by the base-changed morphism
  `Y ×_X V ⟶ Z ×_X V`.  The base-changed morphism is given by its universal property rather than
  as `AlgebraicGeometry.Space.smallBaseChangeOverMap`, for the reason recorded in the
  implementation notes of
  `StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMap`.
* `AlgebraicGeometry.Space.pushforwardRingMap_app_eq`: **the identification itself**, with no
  hypothesis on `Z`.

## Implementation notes

**The reindexing that the gap was about.**  Assembling the four factors of
`AlgebraicGeometry.Space.pushforwardRingMap` needs
`AlgebraicGeometry.Space.smallBaseChangeComp` for the pair `f.left`, `Z.hom`, whose third
representability witness is one for `f.left ≫ Z.hom`, while the base-changed morphism is indexed
by a witness for `Y.hom`; the two morphisms agree only by `CategoryTheory.Over.w`, and
`AlgebraicGeometry.Space.smallBaseChange` depends on the witness it is handed.  There is nothing
to transport: `CategoryTheory.Functor.relativelyRepresentable` is a
`CategoryTheory.MorphismProperty`, hence `Prop`-valued, so two witnesses for the *same* morphism
are definitionally equal by proof irrelevance, and the only genuine mismatch is the morphism
itself.  That one is removed by stating the identification with the structure morphism of the
source as a *variable* together with the equation
`AlgebraicGeometry.Space.pushforwardRingMap`'s fourth factor is built from, so that the equation
can be eliminated: after it is, the fourth factor is `CategoryTheory.eqToHom` of a reflexive
equality and the two witnesses are the same one.  No comparison isomorphism of base-change
functors is needed, and no `CategoryTheory.eqToHom` occurs in the statement of the result.

**Why the chain is a lemma at variables.**  Joining the four factors is four rewrites inside a
five-fold composite of maps of sections, each factor of which is a long term.  Performed in
place the rewrites do not terminate within the heartbeat budget: a rewrite keys on the head
symbol of its pattern, here `CategoryTheory.CategoryStruct.comp`, so it offers the whole
composite as the first candidate and spends the budget deciding that two unrelated maps of
sections are not definitionally equal.  Restated at variables, as
`AlgebraicGeometry.Space.comp_eq_of_comp_chain` below, each of the four rewrites matches or
fails at once, because every candidate head is a variable of a visibly different type.

For the same reason the two `rfl` identifications of
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` with the component of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing` it is defined to be are
discharged by the final `exact`, which compares the two sides argument by argument, and not by
rewriting with them: a rewrite keyed on `CategoryTheory.Iso.hom` offers every other isomorphism
in the composite as a candidate, and deciding those exhausts the budget as well.

**No `@[stacks]` attribute is placed.**  What is proved is the chart reading of Stacks 03G8's
direct-image map, internal to this development; the clause of Stacks 081V it serves is its
faithfulness, which is not proved here.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), parts (3) and (4).
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map and
  the sections of a direct image over a chart.
* [Stacks Project, Tag 0AGC](https://stacks.math.columbia.edu/tag/0AGC), part (1), used to see
  that the morphism over `X` is itself representable.
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe v u

namespace AlgebraicGeometry.Space

/-! ### The composition law of chart base change, over the base -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The component of the composition law of chart base change commutes with the cartesian
projections to the original chart.**  For representable `f : X ⟶ Y` and `g : Y ⟶ Z` with `f ≫ g`
representable and `W` an étale scheme chart of `Z`, the comparison
`X ×_Y (Y ×_Z W) ⟶ X ×_Z W` of `AlgebraicGeometry.Space.smallBaseChangeComp` followed by the
projection `X ×_Z W ⟶ W` is the two projections `X ×_Y (Y ×_Z W) ⟶ Y ×_Z W ⟶ W`.

Compatibility with the projections to `X` is `CategoryTheory.CostructuredArrow.w` of the
comparison, the chart structure maps being those projections.  This is the other half, and it is
not formal: it is `AlgebraicGeometry.Space.smallBaseChangeComp_comparison`, which pins the
comparison down against the spaces-étale composition law, read on the projections by
`AlgebraicGeometry.Space.smallBaseChangeComparisonIso_hom_projection` and
`AlgebraicGeometry.Space.spacesBaseChange_comp_projection`. -/
theorem smallBaseChangeComp_hom_app_snd (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (W : SmallEtale B S hS Z.1) :
    ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).hom.left ≫ hfg.snd W.1.hom =
      hf.snd ((smallBaseChange B S hS g hg).obj W).1.hom ≫ hg.snd W.1.hom := by
  have hnat :
      ((spacesBaseChange B S hS f).functor.map
            (smallBaseChangeComparisonIso B S hS g hg W).hom).hom.left ≫
          (spacesBaseChange B S hS f).projection.app
            ((spacesBaseChange B S hS g).functor.obj ((comparisonFunctor B S hS Z).obj W)) =
        (spacesBaseChange B S hS f).projection.app
            ((comparisonFunctor B S hS Y).obj ((smallBaseChange B S hS g hg).obj W)) ≫
          (smallBaseChangeComparisonIso B S hS g hg W).hom.hom.left :=
    (spacesBaseChange B S hS f).projection.naturality _
  have hcmp := smallBaseChangeComp_comparison B S hS f g hf hg hfg W
  have main :
      ((comparisonFunctor B S hS X).map
            ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W)).hom.left ≫
          (smallBaseChange_projection B S hS (f ≫ g) hfg).app W =
        (smallBaseChange_projection B S hS f hf).app ((smallBaseChange B S hS g hg).obj W) ≫
          (smallBaseChange_projection B S hS g hg).app W := by
    rw [← smallBaseChangeComparisonIso_hom_projection B S hS (f ≫ g) hfg W,
      ← smallBaseChangeComparisonIso_hom_projection B S hS f hf
        ((smallBaseChange B S hS g hg).obj W),
      ← smallBaseChangeComparisonIso_hom_projection B S hS g hg W,
      ← Category.assoc, ← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom, hcmp]
    simp only [ObjectProperty.FullSubcategory.comp_hom, Over.comp_left, Category.assoc]
    rw [spacesBaseChange_comp_projection B S hS f g ((comparisonFunctor B S hS Z).obj W),
      ← Category.assoc (((spacesBaseChange B S hS f).functor.map
        (smallBaseChangeComparisonIso B S hS g hg W).hom).hom.left), hnat, Category.assoc]
  have main' : yoneda.map ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).hom.left ≫
        yoneda.map (hfg.snd W.1.hom) =
      yoneda.map (hf.snd ((smallBaseChange B S hS g hg).obj W).1.hom) ≫
        yoneda.map (hg.snd W.1.hom) :=
    congrArg (fun k => k.hom) main
  exact yoneda.map_injective
    ((yoneda.map_comp _ _).trans (main'.trans (yoneda.map_comp _ _).symm))

/-- **The cartesian projection of an iterated base change factors through the base-changed
morphism.**  For representable `f : X ⟶ Y` and `g : Y ⟶ Z` with `f ≫ g` representable and `W` an
étale scheme chart of `Z`, the projection `X ×_Y (Y ×_Z W) ⟶ Y ×_Z W` is the comparison
`AlgebraicGeometry.Space.smallBaseChangeComp` followed by the base change of `f` to the chart
`Y ×_Z W`.

The base-changed morphism is given as a morphism `m` satisfying the two identities that
determine it — `AlgebraicGeometry.Space.eq_smallBaseChangeOverMap` — rather than as
`AlgebraicGeometry.Space.smallBaseChangeOverMap` itself, so that the statement is in one
spelling of the base-changed charts throughout; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeOverMap`.

Both sides are morphisms into the fibre product `Y ×_Z W`, so it is enough to compare the two
projections: the one to `Y` is `CategoryTheory.CostructuredArrow.w` of the comparison together
with the cartesian square of `f`, and the one to `W` is
`AlgebraicGeometry.Space.smallBaseChangeComp_hom_app_snd`. -/
theorem smallBaseChangeComp_hom_app_left_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : yoneda.relativelyRepresentable f.hom)
    (hg : yoneda.relativelyRepresentable g.hom)
    (hfg : yoneda.relativelyRepresentable (f ≫ g).hom) (W : SmallEtale B S hS Z.1)
    (m : hfg.pullback W.1.hom ⟶ hg.pullback W.1.hom)
    (hfst : yoneda.map m ≫ hg.fst W.1.hom = hfg.fst W.1.hom ≫ f.hom)
    (hsnd : m ≫ hg.snd W.1.hom = hfg.snd W.1.hom) :
    ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).hom.left ≫ m =
      hf.snd ((smallBaseChange B S hS g hg).obj W).1.hom := by
  have hw : yoneda.map ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).hom.left ≫
        hfg.fst W.1.hom =
      hf.fst ((smallBaseChange B S hS g hg).obj W).1.hom :=
    CostructuredArrow.w ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).hom
  have hww : hf.fst ((smallBaseChange B S hS g hg).obj W).1.hom ≫ f.hom =
      yoneda.map (hf.snd ((smallBaseChange B S hS g hg).obj W).1.hom) ≫ hg.fst W.1.hom :=
    hf.w ((smallBaseChange B S hS g hg).obj W).1.hom
  refine hg.hom_ext ?_ ?_
  · refine (congrArg (fun k => k ≫ hg.fst W.1.hom) (yoneda.map_comp _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k =>
      yoneda.map ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).hom.left ≫ k)
      hfst).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ f.hom) hw).trans hww)
  · refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (fun k =>
        ((smallBaseChangeComp B S hS f g hf hg hfg).hom.app W).hom.left ≫ k) hsnd).trans
      (smallBaseChangeComp_hom_app_snd B S hS f g hf hg hfg W)

/-! ### The chart value of the direct-image map -/

/-- The chain of four identities that joins the factors of
`AlgebraicGeometry.Space.pushforwardRingMap` on the sections over a chart, stated at variables:
`ρ` is split off on the right by the retraction `ρ'`, and what is left is read with `h₁`, `h₂`,
`h₃` and `h₄` in turn.

It is a lemma at variables, rather than the same four rewrites performed in place, for the
reason given in the implementation notes of this file: in place each rewrite offers a long map
of sections as its first candidate, and deciding that the candidate does not match exhausts the
heartbeat budget. -/
private theorem comp_eq_of_comp_chain {C : Type u} [Category.{v} C]
    {A A' A'' A₃ A₄ A₅ G H : C} (φ₁ : A ⟶ A') (φ₂ : A' ⟶ A'') (φ₃ : A'' ⟶ A₃) (ψ : A₃ ⟶ A₄)
    (ρ : A₄ ⟶ A₅) (ρ' : A₅ ⟶ A₄) (σ : A' ⟶ G) (τ : G ⟶ A₅) (ζ : A ⟶ H) (θ : H ⟶ G)
    (μ : H ⟶ A₄) (ν : H ⟶ A₅) (hr : ρ ≫ ρ' = 𝟙 A₄)
    (h₁ : φ₂ ≫ φ₃ ≫ ψ ≫ ρ = σ ≫ τ) (h₂ : φ₁ ≫ σ = ζ ≫ θ) (h₃ : θ ≫ τ = ν)
    (h₄ : μ ≫ ρ = ν) :
    (φ₁ ≫ φ₂ ≫ φ₃) ≫ ψ = ζ ≫ μ := by
  have : IsSplitMono ρ := .mk' ⟨ρ', hr⟩
  rw [← cancel_mono ρ]
  simp only [Category.assoc]
  rw [h₁, ← Category.assoc, h₂, Category.assoc, h₃, h₄]

/-- `AlgebraicGeometry.Space.pushforwardRingMap_app_eq` with the structure morphism of the
source and the equation identifying it with the composite as separate data, so that the equation
can be eliminated, and with the base-changed morphism given by its universal property. -/
private theorem pushforwardRingMap_app_eq_aux {Xx Yl Zl : AlgebraicSpaces B S hS}
    (fl : Yl ⟶ Zl) (zh : Zl ⟶ Xx) (yh : Yl ⟶ Xx) (hw : fl ≫ zh = yh)
    (hY : yoneda.relativelyRepresentable yh.hom)
    (hZ : yoneda.relativelyRepresentable zh.hom)
    (V : SmallEtale B S hS Xx.1)
    (m : hY.pullback V.1.hom ⟶ hZ.pullback V.1.hom)
    (hfst : yoneda.map m ≫ hZ.fst V.1.hom = hY.fst V.1.hom ≫ fl.hom)
    (hsnd : m ≫ hZ.snd V.1.hom = hY.snd V.1.hom) :
    (pushforwardAlgebraSectionsIso B S hS (Over.mk zh) hZ V).inv ≫
        ((pushforwardCommRingFunctor
                (smallEtaleRingedToposHom B S hS zh).toToposHom).map
              (smallEtaleRingedToposHom B S hS fl).fSharp ≫
            (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS fl).toToposHom
                (smallEtaleRingedToposHom B S hS zh).toToposHom
                (smallEtaleRingedTopos B S hS Yl).O).hom ≫
            (smallEtaleRingedToposHom_compRingIso B S hS fl zh).hom.app
              (smallEtaleRingedTopos B S hS Yl).O ≫
            eqToHom (congrArg
              (fun q : Yl ⟶ Xx =>
                (pushforwardCommRingFunctor
                  (smallEtaleRingedToposHom B S hS q).toToposHom).obj
                    (smallEtaleRingedTopos B S hS Yl).O)
              hw)).hom.app (op V) ≫
        (pushforwardAlgebraSectionsIso B S hS (Over.mk yh) hY V).hom =
      ((BigFppfOver.toScheme B S hS).map m).appTop := by
  rcases hw with rfl
  have hfl : yoneda.relativelyRepresentable fl.hom :=
    relativelyRepresentable_of_comp B S hS Zl.2.diagonal_representable fl.hom zh.hom hY
  have hfact :
      ((smallBaseChangeComp B S hS fl zh hfl hZ hY).hom.app V).hom.left ≫ m =
        hfl.snd ((smallBaseChange B S hS zh hZ).obj V).1.hom :=
    smallBaseChangeComp_hom_app_left_comp B S hS fl zh hfl hZ hY V m hfst hsnd
  have hnat :
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS zh).toToposHom).map
            (smallEtaleRingedToposHom B S hS fl).fSharp).hom.app (op V) ≫
          ((smallEtaleRingedToposHom_representableRing B S hS zh hZ).hom.app
            ((pushforwardCommRingFunctor
              (smallEtaleRingedToposHom B S hS fl).toToposHom).obj
                (smallEtaleRingedTopos B S hS Yl).O)).hom.app (op V) =
        ((smallEtaleRingedToposHom_representableRing B S hS zh hZ).hom.app
            (smallEtaleRingedTopos B S hS Zl).O).hom.app (op V) ≫
          ((smallEtaleRingedToposHom B S hS fl).fSharp).hom.app
            (op ((smallBaseChange B S hS zh hZ).obj V)) :=
    congrArg (fun t => t.hom.app (op V))
      ((smallEtaleRingedToposHom_representableRing B S hS zh hZ).hom.naturality
        (smallEtaleRingedToposHom B S hS fl).fSharp)
  have h03G8 :
      ((smallEtaleRingedToposHom B S hS fl).fSharp).hom.app
            (op ((smallBaseChange B S hS zh hZ).obj V)) ≫
          ((smallEtaleRingedToposHom_representableRing B S hS fl hfl).hom.app
            (smallEtaleRingedTopos B S hS Yl).O).hom.app
              (op ((smallBaseChange B S hS zh hZ).obj V)) =
        ((BigFppfOver.toScheme B S hS).map
          (hfl.snd ((smallBaseChange B S hS zh hZ).obj V).1.hom)).appTop :=
    fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS (Over.mk fl) hfl
      ((smallBaseChange B S hS zh hZ).obj V)
  have hcomp := smallBaseChangeComp_smallEtaleRingedToposHom_compRingIso B S hS fl zh hfl hZ hY
    (smallEtaleRingedTopos B S hS Yl).O V
  have hrestr :
      ((BigFppfOver.toScheme B S hS).map m).appTop ≫
          ((smallEtaleRingedTopos B S hS Yl).O).obj.map
            ((smallBaseChangeComp B S hS fl zh hfl hZ hY).hom.app V).op =
        ((BigFppfOver.toScheme B S hS).map
          (hfl.snd ((smallBaseChange B S hS zh hZ).obj V).1.hom)).appTop :=
    (Scheme.Hom.comp_appTop ((BigFppfOver.toScheme B S hS).map
          ((smallBaseChangeComp B S hS fl zh hfl hZ hY).hom.app V).hom.left)
        ((BigFppfOver.toScheme B S hS).map m)).symm.trans
      (congrArg (fun h => Scheme.Hom.appTop h)
        (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
          (congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) hfact)))
  have hretr : ((smallEtaleRingedTopos B S hS Yl).O).obj.map
        ((smallBaseChangeComp B S hS fl zh hfl hZ hY).hom.app V).op ≫
      ((smallEtaleRingedTopos B S hS Yl).O).obj.map
        ((smallBaseChangeComp B S hS fl zh hfl hZ hY).inv.app V).op = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← op_comp,
      (smallBaseChangeComp B S hS fl zh hfl hZ hY).inv_hom_id_app V, op_id,
      CategoryTheory.Functor.map_id]
  have hfinal :
      (((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS zh).toToposHom).map
                (smallEtaleRingedToposHom B S hS fl).fSharp).hom.app (op V) ≫
            (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS fl).toToposHom
                (smallEtaleRingedToposHom B S hS zh).toToposHom
                (smallEtaleRingedTopos B S hS Yl).O).hom.hom.app (op V) ≫
              ((smallEtaleRingedToposHom_compRingIso B S hS fl zh).hom.app
                (smallEtaleRingedTopos B S hS Yl).O).hom.app (op V)) ≫
          ((smallEtaleRingedToposHom_representableRing B S hS (fl ≫ zh) hY).hom.app
            (smallEtaleRingedTopos B S hS Yl).O).hom.app (op V) =
        ((smallEtaleRingedToposHom_representableRing B S hS zh hZ).hom.app
            (smallEtaleRingedTopos B S hS Zl).O).hom.app (op V) ≫
          ((BigFppfOver.toScheme B S hS).map m).appTop :=
    comp_eq_of_comp_chain _ _ _ _ _ _ _ _ _ _ _ _ hretr hcomp hnat h03G8 hrestr
  simp only [eqToHom_refl]
  exact (Iso.inv_comp_eq _).mpr hfinal

/-- **The chart value of the direct-image map of a morphism over `X` is pullback of regular
functions along the base-changed morphism.**

Let `f : Y ⟶ Z` be a morphism of algebraic spaces over `X` whose two structure morphisms are
representable, and let `V` be an étale scheme chart of `X`.  Read through
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso` at the source and the target, the
component at `V` of `AlgebraicGeometry.Space.pushforwardRingMap f` is the map
`Γ(Z ×_X V) ⟶ Γ(Y ×_X V)` induced on global regular functions by
`AlgebraicGeometry.Space.smallBaseChangeOverMap`, the base change of `f` to the chart.

This strengthens
`AlgebraicGeometry.Space.cartesianProjectionAppTop_comp_pushforwardRingMap_app_eq`, which is the
same equality after precomposition with pullback along the cartesian projection `Z ×_X V ⟶ V`,
and removes the surjectivity hypothesis of
`AlgebraicGeometry.Space.pushforwardRingMap_app_eq_of_surjective`.

The proof reads the four factors of `AlgebraicGeometry.Space.pushforwardRingMap` on the sections
over `V`: the direct image along `Z.hom` of the structure map of `f.left` by naturality of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_representableRing` in the sheaf argument
followed by `AlgebraicGeometry.Space.fSharp_app_comp_pushforwardAlgebraSectionsIso`, the two
composition-carrying factors by
`AlgebraicGeometry.Space.smallBaseChangeComp_smallEtaleRingedToposHom_compRingIso`, and the
transport along `CategoryTheory.Over.w` by eliminating that equation.  What the first two produce
is the projection `Y ×_Z (Z ×_X V) ⟶ Z ×_X V`, and
`AlgebraicGeometry.Space.smallBaseChangeComp_hom_app_left_comp` is what turns it into the
base-changed morphism. -/
theorem pushforwardRingMap_app_eq {Xx : AlgebraicSpaces B S hS} {Yy Zz : Over Xx} (f : Yy ⟶ Zz)
    (hY : yoneda.relativelyRepresentable Yy.hom.hom)
    (hZ : yoneda.relativelyRepresentable Zz.hom.hom) (V : SmallEtale B S hS Xx.1) :
    (pushforwardAlgebraSectionsIso B S hS Zz hZ V).inv ≫
        (pushforwardRingMap B S hS f).hom.app (op V) ≫
        (pushforwardAlgebraSectionsIso B S hS Yy hY V).hom =
      ((BigFppfOver.toScheme B S hS).map (smallBaseChangeOverMap B S hS f hY hZ V)).appTop :=
  pushforwardRingMap_app_eq_aux B S hS f.left Zz.hom Yy.hom (Over.w f) hY hZ V
    (smallBaseChangeOverMap B S hS f hY hZ V)
    (yoneda_map_smallBaseChangeOverMap_fst B S hS f hY hZ V)
    (smallBaseChangeOverMap_snd B S hS f hY hZ V)

end AlgebraicGeometry.Space

end
