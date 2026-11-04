module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMapDerivationCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoChartProjection

/-!
# Restriction of derivations along a representable morphism, on sections over an étale chart

Let `f : X' ⟶ X` be a *representable* morphism of algebraic spaces over a scheme `S`.  Stacks
04CX attaches to a commutative square with top edge `f` and left edge `p' : X' ⟶ Y'` the
composite `f_*d_{X'/Y'} ∘ f♯ : 𝒪_X ⟶ f_*Ω_{X'/Y'}`, and
`AlgebraicGeometry.Space.restrictDerivation` postcomposes it with the direct image of a morphism
`g : Ω_{X'/Y'} ⟶ C`.  This file computes the value of that derivation on a regular function over
an étale scheme chart `V` of `X`:

> read through the identification of the direct image of modules with the direct image along base
> change of charts, `f_*(d_{X'/Y'} ∘ g) ∘ f♯` sends a regular function `t` on `V` to
> `g(d_{X'/Y'}(t|_{V ×_X X'}))`, the restriction being pullback along the cartesian projection
> `V ×_X X' ⟶ V`,

`AlgebraicGeometry.Space.modulePushforwardChartIso_restrictDerivation_d`.  **That is the formula
the square of Stacks 05ZC and Stacks 05ZD needs**: it is literally
`AlgebraicGeometry.Scheme.Hom.restrictRelativeDerivation_d`, the scheme-level formula of
Morphisms, Lemma 01V0, read on the small étale site of an algebraic space.

The obstruction this file removes is that the comparison collapsing the sections of
`f_*Ω_{X'/Y'}` over `V` — a limit over the étale scheme charts of `X'` above `X' ×_X V` — to the
sections over the base-changed chart `V ×_X X'` is
`AlgebraicGeometry.Space.chartComparison`, which is
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` followed by
`AlgebraicGeometry.Space.chartRanIso`, and only the second factor is computable: the first is
`CategoryTheory.Functor.isoWhiskerRight` of
`AlgebraicGeometry.Space.smallEtaleComparisonRanIso`, which is
`CategoryTheory.Adjunction.rightAdjointUniq`.  What makes the *composite* computable is that the
adjoint-uniqueness factor cancels against `AlgebraicGeometry.Space.structureSharp`, which is
built through the inverse of that same isomorphism.  At the level of sheaves of rings that
cancellation is `AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`, read on sections by
`AlgebraicGeometry.Space.chartComparison_structureSharp`; the first result below is its
module-level analogue, and the two after it carry it to `restrictDerivation`.

The sections action of `AlgebraicGeometry.Space.modulePushforwardChartIso` *is* statable — it is
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_apply` below — but its right-hand
side is the comparison of the direct images of sheaves of *sets*, which still contains the
adjoint-uniqueness factor.  So that lemma alone computes nothing; it is useful exactly because it
reduces the module-level comparison to the set-level one, where the cancellation above applies.

## Main results

* `AlgebraicGeometry.Space.chartComparison_structureSharpSet`: the chart formula for `f♯` with
  the structure map written as `AlgebraicGeometry.Space.structureSharpSet`.
* `AlgebraicGeometry.Space.chartComparison_pushforwardUniversalDerivationHom`: **the value of
  `f_*d_{X'/Y'} ∘ f♯` on a regular function over an étale chart**, the module-level analogue of
  `AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`.
* `AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_apply`: the sections action of the
  identification of the two direct images of modules.
* `AlgebraicGeometry.Space.modulePushforwardChartIso_restrictDerivation_d`: **the value of
  `AlgebraicGeometry.Space.restrictDerivation` on sections over an étale chart.**

## Implementation notes

No Stacks tag is registered: the content is Stacks 04CX's composite read through the chart
comparison of Stacks 03G2, part (4), both of which are attributed where they are proved.

Three lemmas are proved in the abstract setting of
`Stacks.Sheaves.ToposPullback` — `pullbackModuleFunctorIsoOfNatIso_hom_app_val_app_apply`,
`restrictionModuleIso_hom_app_val_app_apply` and their composite
`isoWhiskerRight_restriction_hom_app_val_app_apply` — and one,
`CategoryTheory.eqToIso_trans_hom_app_val_app_apply`, for an arbitrary equality of functors into
sheaves of modules.  All four hold by `rfl` or by substituting the equality away, and all four
are *about* the factors of `AlgebraicGeometry.Space.modulePushforwardChartIso`.  They are stated
abstractly because the same identities, written out for the functors of the small étale sites of
algebraic spaces, exhaust the heartbeats: the single `rfl` for
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_apply` times out at `whnf`, and so
does the abstract composite if the two halves are not proved separately first.  For the same
reason that lemma's proof is staged with `refine`/`exact` rather than written as one term — with
the metavariable for the comparison solved first, the remaining heterogeneous equality is
between concrete terms and goes through, while the one-term form times out at `whnf`.

`AlgebraicGeometry.Space.modulePushforwardChartIso` cannot be rewritten in a goal: unfolding it
leaves a term that `rw` reports as "not type-correct under the `implicit` transparency level",
the two spellings of the objects of a small étale site being definitionally but not reducibly
equal (the problem recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModulePullbackBaseChange.lean`).  That is why
the route above goes through lemmas matched by unification rather than through `simp` or `rw`.

## References

* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0), the scheme-level formula
  this one matches.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace CategoryTheory

universe m v₁ u₁ v₂ u₂

/-- **Transport along an equality of functors into sheaves of modules does nothing on
sections.**  For an isomorphism `α : F ≅ G` of functors into sheaves of modules and an equality
`G = H`, the composite `α ≪≫ eqToIso E` acts on sections over an object exactly as `α` does: the
two targets have the same sections, so the transport is the identity up to a heterogeneous
equality.

The equality `E` is substituted away, which is the only way to reduce the transport: an
`eqToHom` of an equality of *functors*, read on sections, is not a `rfl` the elaborator can see
through at the size of the comparison this file is for.  See the implementation notes. -/
theorem eqToIso_trans_hom_app_val_app_apply {D : Type u₂} [Category.{v₂} D] {C : Type u₁}
    [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{m}}
    {F G H : D ⥤ SheafOfModules.{m} R} (α : F ≅ G) (E : G = H) (M : D) (W : Cᵒᵖ)
    (z : (F.obj M).val.obj W) (y : (H.obj M).val.obj W)
    (hy : HEq (((α.hom.app M).val.app W).hom z) y) :
    (((α ≪≫ eqToIso E).hom.app M).val.app W).hom z = y := by
  subst E
  rw [eqToIso_refl, Iso.trans_refl]
  exact eq_of_heq hy

end CategoryTheory

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (O : Sheaf K RingCat.{ww})

/-- **The transport of the inverse image of modules along a natural isomorphism is that
isomorphism on sections.**  `Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso` is
built from `Stacks.Sheaves.ToposPullback.pullbackModuleMapOfNatTrans`, whose underlying morphism
of sheaves of sets is `ε` by
`Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_pullbackModuleMapOfNatTrans`. -/
theorem pullbackModuleFunctorIsoOfNatIso_hom_app_val_app_apply
    {Φ Φ' : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)} [Limits.PreservesFiniteProducts Φ]
    [Limits.PreservesFiniteProducts Φ'] (ε : Φ ≅ Φ')
    (β : pullbackRingSheaf J Φ O ⟶ pullbackRingSheaf J Φ' O)
    (hβ : (sheafCompose J (forget RingCat.{ww})).map β = ε.hom.app (Sheaf.ringSheaf O))
    (M : SheafOfModules.{ww} O) (W : Cᵒᵖ)
    (z : ((pullbackModuleFunctor J Φ O).obj M).val.obj W) :
    (((pullbackModuleFunctorIsoOfNatIso J O ε β hβ).hom.app M).val.app W).hom z =
      (ε.hom.app (Sheaf.moduleSheaf O M)).hom.app W z :=
  rfl

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- **The comparison of the inverse image along a restriction functor with restriction is the
identity on sections.**  `Stacks.Sheaves.ToposPullback.restrictionModuleIso` changes only the
module structure, not the sections; this is
`Stacks.Sheaves.ToposPullback.restrictionModuleHom`, whose underlying function is `id`. -/
theorem restrictionModuleIso_hom_app_val_app_apply (G : C ⥤ D) [G.IsContinuous J K]
    (M : SheafOfModules.{ww} O) (W : Cᵒᵖ)
    (z : ((pullbackModuleFunctor J (G.sheafPushforwardContinuous (Type ww) J K) O).obj
      M).val.obj W) :
    (((restrictionModuleIso J K G O).hom.app M).val.app W).hom z = z :=
  rfl

/-- **The whole module-comparison factor of
`AlgebraicGeometry.Space.modulePushforwardChartIso`, on sections.**  Transporting the inverse
image of modules along a natural isomorphism `ε` onto a restriction functor, identifying that
inverse image with restriction, and restricting scalars along a further structure map, acts on
sections over an object exactly as `ε` does.

The two previous lemmas composed.  They are composed *here*, in the abstract setting, rather
than at the point of use: stated for the concrete functors of the small étale sites of algebraic
spaces, the same `rfl` exhausts the heartbeats.  See the implementation notes. -/
theorem isoWhiskerRight_restriction_hom_app_val_app_apply (G : C ⥤ D) [G.IsContinuous J K]
    {Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)} [Limits.PreservesFiniteProducts Φ]
    (ε : Φ ≅ G.sheafPushforwardContinuous (Type ww) J K)
    (β : pullbackRingSheaf J Φ O ⟶
      pullbackRingSheaf J (G.sheafPushforwardContinuous (Type ww) J K) O)
    (hβ : (sheafCompose J (forget RingCat.{ww})).map β = ε.hom.app (Sheaf.ringSheaf O))
    {R : Sheaf J RingCat.{ww}} (φ : R ⟶ pullbackRingSheaf J Φ O)
    (M : SheafOfModules.{ww} O) (W : Cᵒᵖ)
    (z : ((pullbackModuleFunctor J Φ O ⋙ SheafOfModules.restrictScalars φ).obj M).val.obj W) :
    (((Functor.isoWhiskerRight
            (pullbackModuleFunctorIsoOfNatIso J O ε β hβ ≪≫
              Functor.isoWhiskerRight (restrictionModuleIso J K G O)
                (SheafOfModules.restrictScalars β))
            (SheafOfModules.restrictScalars φ)).hom.app M).val.app W).hom z =
      (ε.hom.app (Sheaf.moduleSheaf O M)).hom.app W z :=
  (restrictionModuleIso_hom_app_val_app_apply J K O G M W _).trans
    (pullbackModuleFunctorIsoOfNatIso_hom_app_val_app_apply J K O ε β hβ M W z)

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Y Y' : AlgebraicSpaces B S hS}

/-- **The chart formula for `f♯`, with the structure map written at the level of sheaves of
sets.**  For a representable `f : X' ⟶ X`, reading `f♯` over an étale scheme chart `V` of `X`
through `AlgebraicGeometry.Space.chartComparison` is pullback of regular functions along the
cartesian projection `V ×_X X' ⟶ V`.

This is `AlgebraicGeometry.Space.chartComparison_structureSharp` with
`AlgebraicGeometry.Space.forgetRing_map_fSharp` applied to its left-hand side. -/
theorem chartComparison_structureSharpSet (f : X' ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS X.1)
    (t : (structureSetSheaf B S hS X).obj.obj (op V)) :
    ((chartComparison B S hS f hf).hom.app (structureSetSheaf B S hS X')).hom.app (op V)
        ((structureSharpSet B S hS f).hom.app (op V) t) =
      (forget CommRingCat.{u}).map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op) t := by
  rw [← forgetRing_map_fSharp B S hS f]
  exact chartComparison_structureSharp B S hS f hf V t

/-- **The derivation `f_*d_{X'/Y'} ∘ f♯` of Stacks 04CX on sections over an étale chart.**  For a
representable `f : X' ⟶ X` and an étale scheme chart `V` of `X`, the composite
`f_*d_{X'/Y'} ∘ f♯`, read through the chart comparison, carries a regular function `t` on `V` to
the universal differential of the pullback of `t` along the cartesian projection
`V ×_X X' ⟶ V`.

This is the module-level analogue of
`AlgebraicGeometry.Space.structureSharp_comp_chartRanIso`; see the module documentation for why
the two factors of the comparison cannot be computed separately. -/
theorem chartComparison_pushforwardUniversalDerivationHom (f : X' ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom) (p' : X' ⟶ Y')
    (V : SmallEtale B S hS X.1) (t : (structureSetSheaf B S hS X).obj.obj (op V)) :
    ((chartComparison B S hS f hf).hom.app
          (CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X')
            (sheafOfDifferentials B S hS p'))).hom.app (op V)
        ((pushforwardUniversalDerivationHom B S hS f p').hom.app (op V) t) =
      (universalDerivation B S hS p').d (X := op ((smallBaseChange B S hS f hf).obj V))
        ((forget CommRingCat.{u}).map
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op) t) := by
  have h := CategoryTheory.Sheaf.hom_congr_app_apply
    ((chartComparison B S hS f hf).hom.naturality (universalDerivationHom B S hS p'))
    (op V) ((structureSharpSet B S hS f).hom.app (op V) t)
  exact h.trans (congrArg (fun z ↦ (universalDerivation B S hS p').d z)
    (chartComparison_structureSharpSet B S hS f hf V t))

attribute [local instance] isContinuous_smallBaseChange

/-- **The sections action of
`AlgebraicGeometry.Space.modulePushforwardChartIso`.**  For a representable `f : X' ⟶ X` and an
étale scheme chart `V` of `X`, the identification of the direct image of modules of Stacks 03LU
with the direct image along base change of charts acts on sections over `V` as the comparison
`AlgebraicGeometry.Space.chartComparison` of the direct images of sheaves of *sets*.

The right-hand side is written out as
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso` followed by
`AlgebraicGeometry.Space.chartRanIso`, which is `AlgebraicGeometry.Space.chartComparison` by
`AlgebraicGeometry.Space.chartComparison_hom_app`; naming the composite instead makes the proof
below exceed the heartbeats. -/
theorem modulePushforwardChartIso_hom_app_apply (f : X' ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom) (M : Modules.{u, u} B S hS X'.1 X'.2)
    (V : SmallEtale B S hS X.1)
    (z : ((modulePushforward B S hS f).obj M).val.obj (op V)) :
    (((modulePushforwardChartIso B S hS f hf).hom.app M).val.app (op V)).hom z =
      ((smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf).hom.app
        (CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X') M)).hom.app
          (op V) z :=
  by
  refine CategoryTheory.eqToIso_trans_hom_app_val_app_apply _ _ M (op V) z _ ?_
  refine heq_of_eq ?_
  exact (isoWhiskerRight_restriction_hom_app_val_app_apply
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS X'.1)
      (structureRingSheaf B S hS X') (smallBaseChange B S hS f hf)
      (smallEtaleDirectImageRanIso B S hS f ≪≫ chartRanIso B S hS f hf)
      (chartRingSheafMap B S hS f hf) _ (structureSharp B S hS f) M (op V) z)

/-- **Restriction of derivations along a representable morphism, on sections over an étale
chart.**  For a commutative square with representable top edge `f : X' ⟶ X` and a morphism
`g : Ω_{X'/Y'} ⟶ C`, the derivation `f_*(d_{X'/Y'} ∘ g) ∘ f♯` of
`AlgebraicGeometry.Space.restrictDerivation`, read over an étale scheme chart `V` of `X` through
`AlgebraicGeometry.Space.modulePushforwardChartIso`, sends a regular function `t` on `V` to
`g` of the universal differential of the pullback of `t` along the cartesian projection
`V ×_X X' ⟶ V`.

**This is the formula the Stacks 05ZC/05ZD square needs**, and it is the scheme-level formula
`AlgebraicGeometry.Scheme.Hom.restrictRelativeDerivation_d` read on the small étale site: the
Kan-extension comparison has cancelled against the `f♯` it is composed with, and what is left
mentions only `g`, the universal derivation of `p'` and pullback of regular functions along the
cartesian projection.

It is `AlgebraicGeometry.Space.chartComparison_pushforwardUniversalDerivationHom` and
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_apply` composed, with naturality of
the chart comparison in the module moving it past the direct image of `g`. -/
theorem modulePushforwardChartIso_restrictDerivation_d (f : X' ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom) (p : X ⟶ Y) (p' : X' ⟶ Y') (q : Y' ⟶ Y)
    (hcomm : f ≫ p = p' ≫ q) (C : Modules.{u, u} B S hS X'.1 X'.2)
    (g : sheafOfDifferentials B S hS p' ⟶ C) (V : SmallEtale B S hS X.1)
    (t : (structureSetSheaf B S hS X).obj.obj (op V)) :
    (((modulePushforwardChartIso B S hS f hf).hom.app C).val.app (op V)).hom
        ((restrictDerivation B S hS f p p' q hcomm C g).d t) =
      (g.val.app (op ((smallBaseChange B S hS f hf).obj V))).hom
        ((universalDerivation B S hS p').d (X := op ((smallBaseChange B S hS f hf).obj V))
          ((forget CommRingCat.{u}).map
            (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op) t)) := by
  have h1 : (((modulePushforwardChartIso B S hS f hf).hom.app
        (sheafOfDifferentials B S hS p')).val.app (op V)).hom
        ((pushforwardUniversalDerivation B S hS f p p' q hcomm).d t) =
      (universalDerivation B S hS p').d (X := op ((smallBaseChange B S hS f hf).obj V))
        ((forget CommRingCat.{u}).map
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).op) t) := by
    refine (modulePushforwardChartIso_hom_app_apply B S hS f hf
      (sheafOfDifferentials B S hS p') V _).trans ?_
    exact chartComparison_pushforwardUniversalDerivationHom B S hS f hf p' V t
  have hnat := SheafOfModules.hom_congr_app_apply
    ((modulePushforwardChartIso B S hS f hf).hom.naturality g) (op V)
    ((pushforwardUniversalDerivation B S hS f p p' q hcomm).d t)
  refine hnat.trans ?_
  exact congrArg (fun z ↦ (g.val.app (op ((smallBaseChange B S hS f hf).obj V))).hom z) h1

end AlgebraicGeometry.Space

end
