module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssentialSurjectivityAffineModels

/-!
# The affine case of essential surjectivity for Stacks 09RJ, at an affine point of the base

In Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms, a chosen limit `X` and a
chosen index `0` — Stacks 09RJ asserts that the category of perfect objects of `D(𝒪_X)` is the
colimit of the categories of perfect objects of the `D(𝒪_{X_i})`.  Full faithfulness is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectObjectsPerfectTarget.lean`; the source
proves essential surjectivity by the induction principle of Stacks 08GP over the quasi-compact
quasi-separated objects of `(X_0)_{spaces,étale}`, and **this file concludes the affine case of
that induction for Situation 09RH itself**.

`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectObjectsAffineBase.lean` proves the
affine case abstractly, as `AlgebraicGeometry.Space.exists_isPerfect_representedAffineStage`, for
a filtered diagram `V : J ⥤ (BigFppfOver B S hS)ᵒᵖ` of objects of the big fppf category with
affine underlying schemes and a cocone `c` on it with affine vertex, under the hypothesis `hc`
that `(bigFppfSectionsRing B S hS).mapCocone c` is a colimit cocone of rings.
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssentialSurjectivityAffineModels.lean`
builds that diagram and that cocone out of Situation 09RH base changed along an affine point
`u : h_U ⟶ X₀` of the chosen stage — the affine models `V_i` of `X_i ×_{X₀} U` and `V_∞` of
`X ×_{X₀} U`, as `AlgebraicGeometry.Space.DescentSituation.affineModelDiagram` and
`affineModelCocone` — and leaves exactly `hc` open.  **This file closes `hc` and applies the
affine case.**

## The chain

* `AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit_affinePointSituation` is
  Stacks 07SI for the structure sheaf on the base-changed situation: the ring of global functions
  of `X ×_{X₀} U` is the filtered colimit of those of the `X_i ×_{X₀} U`, elementwise as
  `Stacks.IsStagesColimit`.  It is proved in the library.
* `AlgebraicGeometry.Space.DescentSituation.affineModelSectionsEquiv` and
  `affineModelLimitSectionsEquiv` identify those rings with the rings of global functions of the
  affine models.  `AlgebraicGeometry.Space.DescentSituation.affineModelSectionsEquiv_sections_map`
  and `affineModelLimitSectionsEquiv_sections_map` are the two compatibility identities that
  `Stacks.IsStagesColimit.ofEquiv` needs in order to transfer the colimit assertion across them;
  this is `AlgebraicGeometry.Space.DescentSituation.isStagesColimit_affineModelSections`.
* `Stacks.isColimit_commRingCat_of_elementwise` turns that elementwise assertion into the
  categorical colimit, which is
  `AlgebraicGeometry.Space.DescentSituation.isColimit_mapCocone_affineModelCocone` — the `hc` the
  affine case asks for.

The leaf the two compatibility identities rest on is the **inverse-direction** naturality of
`AlgebraicGeometry.Space.globalFunctionsYonedaRingEquiv`, which is proved here as
`AlgebraicGeometry.Space.globalFunctionsMap_globalFunctionsYonedaRingEquiv_symm`; the forward
direction,
  `AlgebraicGeometry.Space.globalFunctionsYonedaRingEquiv_globalFunctionsMap_representedSpaceMap`
  , is proved in the library.
Each identity then reduces to a square of morphisms of algebraic spaces,
`AlgebraicGeometry.Space.DescentSituation.transition_comp_affineModelSpaceIso_hom` and
`projection_comp_affineModelSpaceIso_hom`, which are
`AlgebraicGeometry.Space.DescentSituation.yoneda_map_affineModelMap` and
`yoneda_map_affineModelProj` read through `CategoryTheory.ObjectProperty.hom_ext`.

## Main results

* `AlgebraicGeometry.Space.globalFunctionsMap_globalFunctionsYonedaRingEquiv_symm`: the inverse
  naturality leaf described above.  It is stated with `AlgebraicGeometry.Scheme.Hom.appTop`
  rather than with `AlgebraicGeometry.Scheme.Γ.map`, although the two are equal by `rfl`: the
  types `Γ(Y, ⊤)` and `Scheme.Γ.obj (op Y)` are equal only after unfolding `Scheme.Γ`, which is
  semireducible, so a statement in the second spelling is one whose subterms `rw` refuses to
  abstract over.  That, and not a universe gap between `globalFunctions'` and `Γ(Y, ⊤)`, is what
  blocks the naive rewrite.
* `AlgebraicGeometry.Space.DescentSituation.isStagesColimit_affineModelSections`: the ring of
  global functions of the affine model of `X ×_{X₀} U` is the filtered colimit of the rings of
  global functions of the affine models of the `X_i ×_{X₀} U`, elementwise.
* `AlgebraicGeometry.Space.DescentSituation.isColimit_mapCocone_affineModelCocone`: **the
  hypothesis `hc` of the affine case, discharged for
  `AlgebraicGeometry.Space.DescentSituation.affineModelCocone`.**  It is a `def` and not a
  `theorem` because `CategoryTheory.Limits.IsColimit` is data, not a `Prop`.
* `AlgebraicGeometry.Space.DescentSituation.exists_isPerfect_affineModelStage`: **the affine case
  of the essential-surjectivity half of Stacks 09RJ, for Situation 09RH.**  For an affine object
  `U` of `(X_0)_{étale}`, every perfect object of the derived category of modules on the affine
  model of `X ×_{X₀} U` is, at some stage `j`, the derived pullback of a perfect object on the
  affine model of `X_j ×_{X₀} U`.

Nothing here is tagged: this is the affine case of the induction inside the source's proof of
Stacks 09RJ, not Stacks 09RJ, and the step for an elementary distinguished square is not here.

## The hypotheses carried, and why each is an input of the source's proof

Exactly the two hypotheses of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssentialSurjectivityAffineModels.lean`
are carried, and no others.

*`I : Type u`, the index set of the situation lies in the universe of the site.*  This is forced
by `AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit`, available only there
because `AlgebraicGeometry.Space.DescentSituation.toLimitSituation`, through which it is proved,
carries its index set as a field.  Situation 09RH itself allows an index in any universe.

*`hI : #I < B.cutoff.ord.cof`, the size hypothesis of Stacks 07SF.*  Both of its uses are
results of the library about limits of algebraic spaces rather than about perfect objects:
`AlgebraicGeometry.Space.DescentSituation.isAffineHom_limitCone_π` for the affineness of
`X ×_{X₀} U`, and `AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit` for the
colimit of rings.  In the big fppf sites of this library it is not removable:
`AlgebraicGeometry.Space.Refute07SQ.not_forall_exists_isAffineSpace_system_obj` of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineStageLargeIndexCounterexample.lean` refutes
the unbounded statement.

`hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)` and the point
`u : h_U ⟶ X₀` are not hypotheses but the data of the case being treated: the object of
`(X_0)_{étale}` at which the induction's predicate is being verified, in the case where it is
affine.  No clause of Stacks 09RJ, 09RI or 09RF is assumed anywhere below, and no `Prop` binder
stands in for missing mathematics.

## What is not here

*The statement is about the chosen affine models, not about `X ×_{X₀} U` itself.*  The affine
models `V_i`, `V_∞` are objects of the big fppf site with affine underlying scheme, chosen
together with isomorphisms of algebraic spaces
`AlgebraicGeometry.Space.DescentSituation.affineModelSpaceIso` and `affineModelLimitSpaceIso` to
`X_i ×_{X₀} U` and `X ×_{X₀} U`; the conclusion of
`AlgebraicGeometry.Space.DescentSituation.exists_isPerfect_affineModelStage` quantifies over the
perfect objects of `D(𝒪_{h_{V_∞}})` rather than those of `D(𝒪_{X ×_{X₀} U})`.  Transporting it
along those isomorphisms needs derived pullback along an isomorphism of algebraic spaces to be
identified with an equivalence — `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`
and `smallEtaleDerivedModulePullbackCongr` are in the tree, and the remaining input, the
identification of `L(𝟙)^*` with the identity functor for the small étale ringed topos of an
algebraic space, is not.  The square that such a transport consumes is proved here:
`AlgebraicGeometry.Space.DescentSituation.projection_comp_affineModelSpaceIso_hom`.

*The step of the induction of Stacks 08GP for an elementary distinguished square is not here*,
so essential surjectivity for Stacks 09RJ is not concluded.  See "What is not here" in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitPerfectEssentialSurjectivityAffineModels.lean`
for what that step needs.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 70.5.1 (Tag 07SF)](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Lemma 70.5.6 (Tag 07SI)](https://stacks.math.columbia.edu/tag/07SI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullback of global regular functions along a composite is the composite of the pullbacks,
in the form in which it applies to an element. -/
theorem globalFunctionsMap_globalFunctionsMap {X Y Z : AlgebraicSpaces B S hS} (f : Z ⟶ Y)
    (g : Y ⟶ X) (s : globalFunctions' B S hS X.obj) :
    globalFunctionsMap B S hS f (globalFunctionsMap B S hS g s) =
      globalFunctionsMap B S hS (f ≫ g) s :=
  (RingHom.congr_fun (globalFunctionsMap_comp B S hS f g) s).symm

/-- **Naturality of the identification of the global functions of a representable algebraic
space with those of the representing object, in the inverse direction**: the global function on
`h_{U'}` attached to a regular function on `U'` pulled back along `g : U' ⟶ U` is the pullback
along `h_g` of the global function on `h_U` attached to the original.

This is
  `AlgebraicGeometry.Space.globalFunctionsYonedaRingEquiv_globalFunctionsMap_representedSpaceMap`
  , the forward
direction, moved across the identification by its injectivity.  The ring map of `g` is spelled
`AlgebraicGeometry.Scheme.Hom.appTop` rather than `AlgebraicGeometry.Scheme.Γ.map _`, which is
the same map by `rfl`: it keeps the type of a regular function spelled `Γ(Y, ⊤)` rather than
`Scheme.Γ.obj (op Y)`, and the two are equal only after unfolding the semireducible
`AlgebraicGeometry.Scheme.Γ`, which puts the statement out of reach of `rw`. -/
theorem globalFunctionsMap_globalFunctionsYonedaRingEquiv_symm {U' U : BigFppfOver B S hS}
    (g : U' ⟶ U) (t : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    globalFunctionsMap B S hS (representedSpaceMap B S hS g)
        ((globalFunctionsYonedaRingEquiv B S hS U).symm t) =
      (globalFunctionsYonedaRingEquiv B S hS U').symm
        (((BigFppfOver.toScheme B S hS).map g).appTop.hom t) :=
  (globalFunctionsYonedaRingEquiv B S hS U').injective
    (((globalFunctionsYonedaRingEquiv_globalFunctionsMap_representedSpaceMap g
            ((globalFunctionsYonedaRingEquiv B S hS U).symm t)).trans
          (congrArg (fun x => ((BigFppfOver.toScheme B S hS).map g).appTop.hom x)
            ((globalFunctionsYonedaRingEquiv B S hS U).apply_symm_apply t))).trans
      ((globalFunctionsYonedaRingEquiv B S hS U').apply_symm_apply _).symm)

/-- A morphism of algebraic spaces, read through isomorphisms with representables, commutes with
`h_g` when `yoneda.map g` is its conjugate by those isomorphisms. -/
private theorem comp_hom_eq_of_yoneda_map {Z' Z : AlgebraicSpaces B S hS}
    {V' V : BigFppfOver B S hS} (t : Z' ⟶ Z) (i' : Z'.obj ≅ yoneda.obj V')
    (i : Z.obj ≅ yoneda.obj V) (g : V' ⟶ V) (h : yoneda.map g = i'.inv ≫ t.hom ≫ i.hom) :
    t ≫ (ObjectProperty.isoMk _ i).hom = (ObjectProperty.isoMk _ i').hom ≫
      representedSpaceMap B S hS g :=
  ObjectProperty.hom_ext _ (((congrArg (fun φ => i'.hom ≫ φ) h).trans (i'.hom_inv_id_assoc _)).symm)

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {U : BigFppfOver B S hS}
  (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
  (u : yoneda.obj U ⟶ (stagesSystem D).obj (op (baseStage D)))
  (hI : #I < B.cutoff.ord.cof)

/-- **The transition morphism of the base-changed stages, read through the chosen isomorphisms
with the affine models**: the square
`X_j ×_{X₀} U ⟶ X_i ×_{X₀} U ⟶ h_{V_i}` versus `X_j ×_{X₀} U ⟶ h_{V_j} ⟶ h_{V_i}` commutes.

This is `AlgebraicGeometry.Space.DescentSituation.yoneda_map_affineModelMap`, which defines the
transition morphism of the affine models, read in the category of algebraic spaces over the
base. -/
theorem transition_comp_affineModelSpaceIso_hom {i j : D.Stages} (h : i ≤ j) :
    (affinePointSituation D hU u).transition h ≫ (affineModelSpaceIso hU u i).hom =
      (affineModelSpaceIso hU u j).hom ≫
        representedSpaceMap B S hS (affineModelMap hU u h) :=
  comp_hom_eq_of_yoneda_map _ _ _ _ (yoneda_map_affineModelMap hU u h)

/-- **The projection of the limit cone of the base-changed situation, read through the chosen
isomorphisms with the affine models**: the square
`X ×_{X₀} U ⟶ X_i ×_{X₀} U ⟶ h_{V_i}` versus `X ×_{X₀} U ⟶ h_{V_∞} ⟶ h_{V_i}` commutes.

This is `AlgebraicGeometry.Space.DescentSituation.yoneda_map_affineModelProj` read in the
category of algebraic spaces over the base.  It is also the square that any transport of
`AlgebraicGeometry.Space.DescentSituation.exists_isPerfect_affineModelStage` from the affine
models to `X ×_{X₀} U` itself has to consume. -/
theorem projection_comp_affineModelSpaceIso_hom (i : D.Stages) :
    (affinePointSituation D hU u).projection i ≫ (affineModelSpaceIso hU u i).hom =
      (affineModelLimitSpaceIso hU u hI).hom ≫
        representedSpaceMap B S hS (affineModelProj hU u hI i) :=
  comp_hom_eq_of_yoneda_map _ _ _ _ (yoneda_map_affineModelProj hU u hI i)

/-- The identification of the global functions of a base-changed stage with those of its affine
model is pullback along the chosen isomorphism after the identification at the representing
object. -/
theorem affineModelSectionsEquiv_apply (i : D.Stages)
    (s : Γ((BigFppfOver.toScheme B S hS).obj (affineModel hU u i), ⊤)) :
    affineModelSectionsEquiv hU u i s =
      globalFunctionsMap B S hS (affineModelSpaceIso hU u i).hom
        ((globalFunctionsYonedaRingEquiv B S hS (affineModel hU u i)).symm s) := rfl

/-- The identification of the global functions of the base-changed limit with those of its
affine model is pullback along the chosen isomorphism after the identification at the
representing object. -/
theorem affineModelLimitSectionsEquiv_apply
    (s : Γ((BigFppfOver.toScheme B S hS).obj (affineModelLimit hU u hI), ⊤)) :
    affineModelLimitSectionsEquiv hU u hI s =
      globalFunctionsMap B S hS (affineModelLimitSpaceIso hU u hI).hom
        ((globalFunctionsYonedaRingEquiv B S hS (affineModelLimit hU u hI)).symm s) := rfl

/-- **The identification of global functions with those of the affine models intertwines the
transition maps**: the ring map of a transition morphism of the affine models becomes pullback
along the corresponding transition morphism of the base-changed stages.

This is the first of the two compatibility identities that
`Stacks.IsStagesColimit.ofEquiv` consumes.  It is the inverse naturality leaf
`AlgebraicGeometry.Space.globalFunctionsMap_globalFunctionsYonedaRingEquiv_symm` followed by the
square `AlgebraicGeometry.Space.DescentSituation.transition_comp_affineModelSpaceIso_hom`. -/
theorem affineModelSectionsEquiv_sections_map {i j : D.Stages} (h : i ≤ j)
    (s : Γ((BigFppfOver.toScheme B S hS).obj (affineModel hU u i), ⊤)) :
    affineModelSectionsEquiv hU u j
        (((BigFppfOver.toScheme B S hS).map (affineModelMap hU u h)).appTop.hom s) =
      globalFunctionsMap B S hS ((affinePointSituation D hU u).transition h)
        (affineModelSectionsEquiv hU u i s) := by
  rw [affineModelSectionsEquiv_apply, affineModelSectionsEquiv_apply,
    ← globalFunctionsMap_globalFunctionsYonedaRingEquiv_symm,
    globalFunctionsMap_globalFunctionsMap, globalFunctionsMap_globalFunctionsMap,
    transition_comp_affineModelSpaceIso_hom]

/-- **The identification of global functions with those of the affine models intertwines the
maps to the limit**: the ring map of a projection of the affine models becomes pullback along the
corresponding projection of the limit cone of the base-changed situation.

This is the second of the two compatibility identities that `Stacks.IsStagesColimit.ofEquiv`
consumes. -/
theorem affineModelLimitSectionsEquiv_sections_map (i : D.Stages)
    (s : Γ((BigFppfOver.toScheme B S hS).obj (affineModel hU u i), ⊤)) :
    affineModelLimitSectionsEquiv hU u hI
        (((BigFppfOver.toScheme B S hS).map (affineModelProj hU u hI i)).appTop.hom s) =
      globalFunctionsMap B S hS ((affinePointSituation D hU u).projection i)
        (affineModelSectionsEquiv hU u i s) := by
  rw [affineModelLimitSectionsEquiv_apply, affineModelSectionsEquiv_apply,
    ← globalFunctionsMap_globalFunctionsYonedaRingEquiv_symm,
    globalFunctionsMap_globalFunctionsMap, globalFunctionsMap_globalFunctionsMap,
    projection_comp_affineModelSpaceIso_hom]

/-- **The ring of global functions of the affine model of the base-changed limit is the filtered
colimit of the rings of global functions of the affine models of the base-changed stages**,
elementwise.

This is Stacks 07SI for the structure sheaf on the base-changed situation,
`AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit_affinePointSituation`,
transferred across `AlgebraicGeometry.Space.DescentSituation.affineModelSectionsEquiv` and
`affineModelLimitSectionsEquiv` by `Stacks.IsStagesColimit.ofEquiv`.  The size hypothesis `hI` of
Stacks 07SF enters only through that assertion and through the affineness of the limit. -/
theorem isStagesColimit_affineModelSections :
    Stacks.IsStagesColimit
      (fun (i j : D.Stages) (h : i ≤ j)
          (s : Γ((BigFppfOver.toScheme B S hS).obj (affineModel hU u i), ⊤)) =>
        ((BigFppfOver.toScheme B S hS).map (affineModelMap hU u h)).appTop.hom s)
      (fun (i : D.Stages) s =>
        ((BigFppfOver.toScheme B S hS).map (affineModelProj hU u hI i)).appTop.hom s) :=
  Stacks.IsStagesColimit.ofEquiv _ _
    (fun i => (affineModelSectionsEquiv hU u i).toEquiv)
    (affineModelLimitSectionsEquiv hU u hI).toEquiv
    (fun _ _ h s => affineModelSectionsEquiv_sections_map hU u h s)
    (fun i s => affineModelLimitSectionsEquiv_sections_map hU u hI i s)
    (isGlobalFunctionsColimit_affinePointSituation D hU u hI)

/-- The stages at or beyond the chosen index of a descent situation are nonempty: the chosen
index is one of them. -/
instance nonempty_stages : Nonempty D.Stages := ⟨baseStage D⟩

/-- **The hypothesis `hc` of the affine case, discharged for the cocone of affine models**: the
cocone of rings of global functions over the diagram of affine models of the base-changed stages,
with the ring of the affine model of the base-changed limit as its vertex, is a colimit cocone.

This is `AlgebraicGeometry.Space.DescentSituation.isStagesColimit_affineModelSections` — Stacks
07SI for the structure sheaf, read on the affine models — turned from its elementwise form into
the categorical one by `Stacks.isColimit_commRingCat_of_elementwise`.  It is what
`AlgebraicGeometry.Space.exists_isPerfect_representedAffineStage` asks for, and it is a `def`
because `CategoryTheory.Limits.IsColimit` is data. -/
def isColimit_mapCocone_affineModelCocone :
    IsColimit ((bigFppfSectionsRing B S hS).mapCocone (affineModelCocone hU u hI)) := by
  refine Stacks.isColimit_commRingCat_of_elementwise _ _ ?_ ?_
  · exact fun t => (isStagesColimit_affineModelSections hU u hI).exists_stage t
  · intro i x y hxy
    obtain ⟨j, h, hj⟩ := (isStagesColimit_affineModelSections hU u hI).exists_trans_eq i x y hxy
    exact ⟨j, homOfLE h, hj⟩

section AffineBase

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-- **The affine case of the essential-surjectivity half of Stacks 09RJ, for Situation 09RH.**
Let `U` be an object of `(X_0)_{étale}` with affine underlying scheme, given by an affine object
of the big fppf site over `S` and a point `u : h_U ⟶ X₀` of the chosen stage.  Write `V_i` for
the chosen affine model of the base-changed stage `X_i ×_{X₀} U` and `V_∞` for that of the
base-changed limit `X ×_{X₀} U`.

Then every perfect object `E` of `D(𝒪_{h_{V_∞}})` is, at some stage `j`, the derived pullback
along `h_{V_∞} ⟶ h_{V_j}` of a perfect object of `D(𝒪_{h_{V_j}}})`.

This is condition (1) of the induction principle of Stacks 08GP in the source's proof of
essential surjectivity, instantiated at Situation 09RH: it is
`AlgebraicGeometry.Space.exists_isPerfect_representedAffineStage` applied to
`AlgebraicGeometry.Space.DescentSituation.affineModelDiagram` and `affineModelCocone`, with the
hypothesis `hc` supplied by
`AlgebraicGeometry.Space.DescentSituation.isColimit_mapCocone_affineModelCocone`.  Only the two
hypotheses of this file's module documentation are carried; the statement is about the chosen
affine models rather than about `X ×_{X₀} U` itself, for the reason given there under "What is
not here".

Nothing here is tagged: the step of the induction for an elementary distinguished square is
absent, so this is a case of the source's proof and not Stacks 09RJ. -/
theorem exists_isPerfect_affineModelStage
    (E : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj (affineModelLimit hU u hI))
      (isAlgebraicSpace_yoneda B S hS (affineModelLimit hU u hI))))
    (hE : (smallEtaleRingedSite B S hS (yoneda.obj (affineModelLimit hU u hI))
      (isAlgebraicSpace_yoneda B S hS (affineModelLimit hU u hI))).IsPerfect E) :
    ∃ (j : D.Stages) (Ej : DerivedCategory (Modules.{u, u} B S hS
        (yoneda.obj (affineModel hU u j))
        (isAlgebraicSpace_yoneda B S hS (affineModel hU u j)))),
      (smallEtaleRingedSite B S hS (yoneda.obj (affineModel hU u j))
          (isAlgebraicSpace_yoneda B S hS (affineModel hU u j))).IsPerfect Ej ∧
        Nonempty ((smallEtaleDerivedModulePullback B S hS
          (representedSpaceMap B S hS (affineModelProj hU u hI j))).obj Ej ≅ E) := by
  have : ∀ j : D.Stages, IsAffine ((BigFppfOver.toScheme B S hS).obj
      (unop ((affineModelDiagram hU u).obj j))) := fun j => isAffine_affineModel hU u j
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (unop (affineModelCocone hU u hI).pt)) := isAffine_affineModelLimit hU u hI
  exact exists_isPerfect_representedAffineStage B S hS (affineModelDiagram hU u)
    (affineModelCocone hU u hI) (isColimit_mapCocone_affineModelCocone hU u hI) E hE

end AffineBase

end DescentSituation

end AlgebraicGeometry.Space

end
