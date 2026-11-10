module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleHomEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSectionsEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleSectionsNaturality

/-!
# The components of the Hom-set transport of the chart restriction

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `M`, `N` be
quasi-coherent `𝒪_X`-modules, let `A` be an étale scheme chart of `X` and let `α : M|_A ⟶ N|_A`
be a morphism of the restrictions to the slice of the small étale site of `X` at `A`.
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` carries `α` to a morphism of the chart
restrictions of `M` and `N` on the chart's scheme.  Nothing in the tree says what its components
are: the transport is assembled from reindexing equivalences and from Descent, Proposition
03DX (2), whose inverse is a chosen preimage.

This file computes them.  Over a Zariski open `V` of the chart's scheme the `V`-component of
`AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` of `α` is — read through
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` and
`AlgebraicGeometry.Space.chartSectionsLinearEquiv` — the component of `α` itself over the object
of the slice which `V` cuts out.

## Main definitions

* `AlgebraicGeometry.Space.openChartOfComparisonOver`: the object of the slice of the small étale
  site of `X` at the chart which a Zariski open of the chart's scheme cuts out.  This is
  `AlgebraicGeometry.Space.openChartOfComparison` *before* the projection of the slice, which is
  what a morphism of the restrictions to the slice has a component at.
* `AlgebraicGeometry.Space.chartEtaleQcohHom`: the Hom-set transport with its last leg — the
  inverse of the equivalence of Descent, Proposition 03DX (2) — not yet applied.
* `AlgebraicGeometry.Space.chartHomSectionsMap`: the transport of `α` to the small Zariski site of
  the chart's scheme, read on sections over a Zariski open.
* `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModuleLinearEquiv`: the component at a
  Zariski open of the chart's scheme of the chart transport isomorphism, as a linear equivalence
  — the first factor of `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv`, named.

## Main results

* `Stacks.SheafOfModules.pushforward_id_two_map_val_app`: **three pushforwards of sheaves of
  modules whose innermost structure map is the identity, read on a component**, collapse to one
  restriction of scalars of a component, naturally in the module.
* `Stacks.ModuleCat.eqToHom_hom_apply`: a transport along an equality of modules, on an element,
  is the cast of the underlying equality of types.
* `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv_eq_ι_map`: the Hom-set transport, factored
  through the inverse of the equivalence of Descent, Proposition 03DX (2), by `rfl`.
* `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv_naturality`: **the chart transport
  isomorphism is natural along the Hom-set transport of an arbitrary `α`.**  This is what
  `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule_naturality` gives only for morphisms
  coming from global quasi-coherent `𝒪_X`-modules, and it is what crosses the chosen preimage.
* `AlgebraicGeometry.Space.chartHomSectionsMap_naturality` and
  `AlgebraicGeometry.Space.chartHomSectionsMap_naturality_apply`: the component square of the
  transport over a Zariski open of the chart's scheme, and the same read on a section.
* `AlgebraicGeometry.Space.chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply`: **the
  component formula.**  The `V`-component of `chartSchemeModuleHomEquiv … A α`, read through
  `chartSchemeModuleIsoRestrictModule` and `chartSectionsLinearEquiv`, is the component of `α`
  over `AlgebraicGeometry.Space.openChartOfComparisonOver … A V`.
* `AlgebraicGeometry.Space.chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_symm_apply`: the
  same read backwards — the component over that object of the morphism which the transport sends
  to a given morphism of the chart restrictions.
* `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv_apply`: **the composite sections
  identification, read on a section**, is its second factor at the component of the chart
  transport isomorphism.
* `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply`:
  **the component formula at the composite.**  The same formula as the one just named, but with
  `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv` on both sides in place of
  `chartSectionsLinearEquiv` after the component of `chartSchemeModuleIsoRestrictModule`.  This is
  the spelling the affine-chart reading of the internal Hom consumes, and it cannot be derived
  from the other one after the fact: see the implementation notes.

## Implementation notes

**The formula holds at this generality, and it has to be proved rather than being automatic.**
The Hom-set transport is indexed by `M.over A` and not by `M`, because
`CategoryTheory.SheafOfModules.overFunctor` is not fully faithful; on the leg
`AlgebraicGeometry.Space.chartSmallEtaleRestrictionHomEquiv` the transport is a pushforward and so
is computable on components, but it then passes the inverse of
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`, which is a
`CategoryTheory.Functor.objPreimage` and therefore a `Classical.choice`.  That leg is crossed by
*conjugating* with `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` — the naturality
square `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv_naturality`, whose two halves are the
unit of the associated-module adjunction and the counit of the equivalence of Descent, Proposition
03DX (2) — and never by unfolding it.

**The square is glued by `Stacks.CategoryTheory.comp_unit_comp_map`**, the same abstract lemma
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule_naturality` uses, and for the same
reason: on the concrete goal every rewrite whose pattern is headed by a composition spends the
whole heartbeat budget inside `isDefEq`.  The only change is that the morphism of the chart
restrictions is the image of an arbitrary `g` under the inverse of that equivalence rather than
the image of a morphism of quasi-coherent `𝒪_X`-modules under
`AlgebraicGeometry.Space.chartSchemeQcohFunctor`; the counit naturality which the gluing needs is
`CategoryTheory.NatTrans.naturality` at `g`, so nothing in the first proof used that `g` came from
a global morphism.

**The innermost identity structure map is hard-coded into the generic lemma, and that is what
brings the component square inside the budget.**  The chart restriction of `M` to the small
Zariski site of the chart's scheme is three `CategoryTheory.SheafOfModules.pushforward`s of
`M.over A`: along the inclusion of the small Zariski site, along the inverse of the comparison of
the two small étale sites, and along the comparison of Stacks 04M0 — and the last of those has the
identity as its structure map.  A generic three-layer statement with the third structure map free
has `AlgebraicGeometry.Space.chartSectionsRingHom` equal to its composite scalar map only after an
identity `RingHom.comp` is collapsed, and that collapse, repeated at every occurrence of the
composite inside a `CategoryTheory.eqToHom`, exhausts the budget.
`Stacks.SheafOfModules.pushforward_id_two_map_val_app` takes the third structure map to *be*
`CategoryTheory.CategoryStruct.id`, so its composite scalar map is
`AlgebraicGeometry.Space.chartSectionsRingHom` on the nose and the instantiation's `hg` is `rfl`
syntactically.

**Each declaration below pays at most one cross-spelling definitional check, and that is why
there are so many of them.**  The sections of the chart restriction over `V` have two spellings —
the one the generic lemma produces, whose module is three pushforwards of `M.over A` and whose
sections are those of `M.over A`, and
`AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_obj_moduleCat`, whose module is
`AlgebraicGeometry.SmallEtale.restrictModule` of
`AlgebraicGeometry.Space.chartSchemeEtaleModule` and whose sections are those of `M`, and of which
`AlgebraicGeometry.Space.chartSectionsLinearEquiv` is the `CategoryTheory.eqToIso`.  Respelling
both sides at once does not fit — that is the two-step proof of
`AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_obj_moduleCat` itself —
so each declaration respells at most one:
`AlgebraicGeometry.Space.chartSectionsOver_obj_moduleCat` therefore respells only the *sections*
side, leaving the module side at its original spelling, so that every step after it composes with it
syntactically; the one remaining passage, from it to
`AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_obj_moduleCat` itself, is made on
an *element* by `AlgebraicGeometry.Space.eqToHom_chartSectionsOver_apply`, where
`Stacks.ModuleCat.eqToHom_hom_apply` reduces both transports to `cast`s along equalities of types
and proof irrelevance finishes.  The same passage *unapplied* does not fit, which is why
`AlgebraicGeometry.Space.chartHomSectionsMap_naturality_apply` is stated on a section and has no
unapplied counterpart at the original spelling.

**The composite sections identification is crossed on a section with its second factor left a
variable, and never by unfolding the composite against that factor.**
`AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv` is a `LinearEquiv.trans`, and —
as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomAffineChartEvaluation` record —
every comparison which unfolds it against its two factors applied in turn exhausts the heartbeat
budget, in either direction and unapplied as well as applied. What is free at the default budget is
this pair:

* `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv_eq_trans`, the delta equation
  *unapplied*, which is `rfl`, and `congrArg` of it at a section; and
* `AlgebraicGeometry.Space.trans_chartSchemeModuleIsoRestrictModuleLinearEquiv_apply`, the
  transitivity read on a section with the *second* factor a variable, which is `rfl` because
  `whnf` has nothing to unfold there.

Putting `AlgebraicGeometry.Space.chartSectionsLinearEquiv` in that variable's place is what costs
the budget: `whnf` of the composite's coercion then unfolds that factor's
`CategoryTheory.eqToIso` and the equality of `CategoryTheory.ModuleCat` objects inside it.
Instantiating a statement already proved costs nothing, so the two steps compose to
`AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv_apply` and the component formula at
the composite follows from the one at the factors by `Eq.trans` at `M` and at `N`.

**No hypothesis beyond quasi-coherence of `M` and `N` is carried** — and that only because
`AlgebraicGeometry.Space.chartSchemeModule` is defined for a quasi-coherent module — and no
declaration here carries a `stacks` tag: this is an input to the reduction of Stacks 07UM to a
chart, not an assertion of any tag.  Descent, Proposition 03DX (2) is used through
`AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`, which is unconditional.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.SheafOfModules

universe w m v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁} {J₂ : GrothendieckTopology C₂}
  {J₃ : GrothendieckTopology C₃}
  {F₁ : C₀ ⥤ C₁} {F₂ : C₁ ⥤ C₂} {F₃ : C₂ ⥤ C₃}
  [inst₁ : F₁.IsContinuous J₀ J₁] [inst₂ : F₂.IsContinuous J₁ J₂]
  [inst₃ : F₃.IsContinuous J₂ J₃]
  {R₀ : CategoryTheory.Sheaf J₀ RingCat.{w}} {R₁ : CategoryTheory.Sheaf J₁ RingCat.{w}}
  {R₃ : CategoryTheory.Sheaf J₃ RingCat.{w}}
  (φ₁ : R₀ ⟶ (F₁.sheafPushforwardContinuous RingCat.{w} J₀ J₁).obj R₁)
  (φ₂ : R₁ ⟶ (F₂.sheafPushforwardContinuous RingCat.{w} J₁ J₂).obj
    ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))

/-- **Three pushforwards of sheaves of modules whose innermost structure map is the identity are
natural in the module on a component.**  For a morphism `f` of sheaves of modules, the image of
`f` under the three pushforwards, read on sections over `A` and followed by the collapse at the
target, is the collapse at the source followed by `f` on sections over the threefold image of `A`,
with its scalars restricted along the composite of the two non-identity structure maps.

The innermost structure map is `CategoryTheory.CategoryStruct.id` rather than a parameter, so that
the composite scalar map is the composite of the two others *on the nose*: a free third structure
map would put an identity `RingHom.comp` in front of it, and that collapse, repeated at every
occurrence of the composite inside a `CategoryTheory.eqToHom`, costs the heartbeat budget at the
chart.

The chain morphism `k`, the image object `P` and the composite ring map `g` are parameters with
equations rather than the composites themselves, for the reason recorded at
`Stacks.SheafOfModules.pushforward_four_map_val_app`. -/
theorem pushforward_id_two_map_val_app {M N : _root_.SheafOfModules.{m} R₃} (f : M ⟶ N) (A : C₀)
    (k : (_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m}
            (𝟙 ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))).obj M) ⟶
        (_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m}
            (𝟙 ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))).obj N))
    (hk : k = (_root_.SheafOfModules.pushforward.{m} φ₂).map
      ((_root_.SheafOfModules.pushforward.{m}
        (𝟙 ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))).map f))
    (P : C₃) (hP : F₃.obj (F₂.obj (F₁.obj A)) = P)
    (g : R₀.obj.obj (op A) →+* R₃.obj.obj (op P))
    (hg : g = hP ▸ ((φ₂.hom.app (op (F₁.obj A))).hom.comp (φ₁.hom.app (op A)).hom))
    (hM : ((_root_.SheafOfModules.pushforward.{m} φ₁).obj
        ((_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m}
            (𝟙 ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))).obj M))).val.obj
        (op A) =
      (ModuleCat.restrictScalars g).obj (M.val.obj (op P)))
    (hN : ((_root_.SheafOfModules.pushforward.{m} φ₁).obj
        ((_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m}
            (𝟙 ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))).obj N))).val.obj
        (op A) =
      (ModuleCat.restrictScalars g).obj (N.val.obj (op P))) :
    ((_root_.SheafOfModules.pushforward.{m} φ₁).map k).val.app (op A) ≫ eqToHom hN =
      eqToHom hM ≫ (ModuleCat.restrictScalars g).map (f.val.app (op P)) := by
  subst hP
  subst hk
  subst hg
  rfl

/-- **The component square of
`Stacks.SheafOfModules.pushforward_id_two_map_val_app`, read on a section.**

Stated generically rather than obtained at the chart from
`Stacks.ModuleCat.comp_hom_apply`: splitting the composite there asks for the middle object of the
composition, and the two sides of the square name it in two definitionally equal spellings, which
is a definitional check of the whole chain. -/
theorem pushforward_id_two_map_val_app_hom_apply {M N : _root_.SheafOfModules.{m} R₃}
    (f : M ⟶ N) (A : C₀)
    (k : (_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m}
            (𝟙 ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))).obj M) ⟶
        (_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m}
            (𝟙 ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))).obj N))
    (hk : k = (_root_.SheafOfModules.pushforward.{m} φ₂).map
      ((_root_.SheafOfModules.pushforward.{m}
        (𝟙 ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))).map f))
    (P : C₃) (hP : F₃.obj (F₂.obj (F₁.obj A)) = P)
    (g : R₀.obj.obj (op A) →+* R₃.obj.obj (op P))
    (hg : g = hP ▸ ((φ₂.hom.app (op (F₁.obj A))).hom.comp (φ₁.hom.app (op A)).hom))
    (hM : ((_root_.SheafOfModules.pushforward.{m} φ₁).obj
        ((_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m}
            (𝟙 ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))).obj M))).val.obj
        (op A) =
      (ModuleCat.restrictScalars g).obj (M.val.obj (op P)))
    (hN : ((_root_.SheafOfModules.pushforward.{m} φ₁).obj
        ((_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m}
            (𝟙 ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))).obj N))).val.obj
        (op A) =
      (ModuleCat.restrictScalars g).obj (N.val.obj (op P)))
    (x : ((_root_.SheafOfModules.pushforward.{m} φ₁).obj
        ((_root_.SheafOfModules.pushforward.{m} φ₂).obj
          ((_root_.SheafOfModules.pushforward.{m}
            (𝟙 ((F₃.sheafPushforwardContinuous RingCat.{w} J₂ J₃).obj R₃))).obj M))).val.obj
        (op A)) :
    (eqToHom hN).hom ((((_root_.SheafOfModules.pushforward.{m} φ₁).map k).val.app (op A)).hom x) =
      (f.val.app (op P)).hom ((eqToHom hM).hom x) := by
  subst hP
  subst hk
  subst hg
  rfl

/-- A composite of morphisms of sheaves of modules, read on a section. -/
theorem comp_val_app_hom_apply {M N P : _root_.SheafOfModules.{m} R₀} (a : M ⟶ N) (b : N ⟶ P)
    (Z : C₀ᵒᵖ) (x : M.val.obj Z) :
    ((a ≫ b).val.app Z).hom x = (b.val.app Z).hom ((a.val.app Z).hom x) := rfl

end Stacks.SheafOfModules

namespace Stacks.ModuleCat

universe v w

/-- **A transport along an equality of modules, read on an element, is the cast of the underlying
equality of types.**

This is what lets two spellings of one sections identification be compared without comparing the
two *modules*: a `cast` depends only on an equality of types, and two equalities of one pair of
types are equal by proof irrelevance, whereas an equality of two `CategoryTheory.ModuleCat`
objects carries the scalar actions and comparing those means eta-expanding `Module.compHom`. -/
theorem eqToHom_hom_apply {R : RingCat.{w}} {U V : _root_.ModuleCat.{v} ↑R} (h : U = V) (x : U) :
    (eqToHom h).hom x =
      cast (congrArg (fun W : _root_.ModuleCat.{v} ↑R => (W : Type v)) h) x := by
  subst h
  rfl

end Stacks.ModuleCat

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The object of the slice which a Zariski open of the chart's scheme cuts out -/

/-- **The object of the slice of the small étale site of `X` at a chart which a Zariski open of
the chart's scheme cuts out.**  This is `AlgebraicGeometry.Space.openChartOfComparison` *before*
the projection of the slice: the étale chart which the open cuts out, together with its structural
morphism to `A`.  A morphism of the restrictions to the slice has a component at this object, not
at the étale chart alone. -/
noncomputable abbrev openChartOfComparisonOver (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) : CategoryTheory.Over A :=
  (SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor.obj
    ((representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A)).inverse.obj
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property V))

/-- The étale chart underlying `AlgebraicGeometry.Space.openChartOfComparisonOver` is
`AlgebraicGeometry.Space.openChartOfComparison`, by `rfl`. -/
theorem openChartOfComparisonOver_left (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    (openChartOfComparisonOver B S hS X A V).left = openChartOfComparison B S hS X A V := rfl

variable (M N : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)

/-! ### The Hom-set transport, factored -/

/-- **The Hom-set transport of the chart restriction with its last leg not yet applied**: a
morphism of the restrictions to the slice of the small étale site of `X` at a chart, read as a
morphism of the quasi-coherent restrictions to the small étale site of the chart's *scheme*. -/
noncomputable def chartEtaleQcohHom (A : SmallEtale B S hS X.1) (α : M.over A ⟶ N.over A) :
    chartSchemeEtaleQcoh B S hS X M hM A ⟶ chartSchemeEtaleQcoh B S hS X N hN A :=
  (representedQuasicoherentEquivalence B S hS (chartFppfObject B S hS X A)).inverse.map
    ((chartSmallEtaleQcohHomEquiv B S hS X M N hM hN A).symm
      (chartSmallEtaleRestrictionHomEquiv B S hS X M N A α))

/-- **The Hom-set transport is the image of `AlgebraicGeometry.Space.chartEtaleQcohHom` under the
inverse of the equivalence of Descent, Proposition 03DX (2)**, by `rfl`: the two legs before it
are a pushforward and the inverse of the inclusion of a full subcategory. -/
theorem chartSchemeModuleHomEquiv_eq_ι_map (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) :
    chartSchemeModuleHomEquiv B S hS X M N hM hN A α =
      (SheafOfModules.isQuasicoherent (chartScheme A).ringCatSheaf).ι.map
        ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
          (associatedBigEtaleSite B) (chartScheme A)
          (chartFppfObject B S hS X A).left.property).inverse.map
            (chartEtaleQcohHom B S hS X M N hM hN A α)) := rfl

/-- **The leg before the equivalence of Descent, Proposition 03DX (2) is a pushforward of a
pushforward**, by `rfl`: this is what makes the Hom-set transport computable on components at all.

The two structure maps are written the way
`Stacks.SheafOfModules.pushforward_id_two_map_val_app` writes them, with the identity of the
comparison of Stacks 04M0 at the *image* of the structure sheaf of the slice rather than at
`AlgebraicGeometry.Space.chartStructureRingSheaf`: the two are definitionally equal, but the
second spelling makes every later definitional check compare them again, once for each occurrence
inside the chain. -/
theorem ι_map_chartEtaleQcohHom (A : SmallEtale B S hS X.1) (α : M.over A ⟶ N.over A) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).ι.map
        (chartEtaleQcohHom B S hS X M N hM hN A α) =
      (SheafOfModules.pushforward.{u} (Stacks.SheafOfModules.reindexBackSharp
          (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
          (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
          (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)))).map
        ((SheafOfModules.pushforward.{u}
            (𝟙 (((SmallEtale.chartLocalizationEquivalence B S hS X.1
                    A).functor.sheafPushforwardContinuous RingCat.{u}
                  (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
                  ((SmallEtale.topology B S hS X.1).over A)).obj
                ((structureRingSheaf B S hS X).over A)))).map α) := rfl

/-! ### Naturality of the chart transport along the Hom-set transport -/

/-- **The counit of the equivalence of Descent, Proposition 03DX (2) is natural at an arbitrary
morphism of the quasi-coherent restrictions to the small étale site of the chart's scheme.**

This is `AlgebraicGeometry.Space.associatedModuleChartSchemeModuleIso_naturality` with the
morphism no longer required to come from a morphism of quasi-coherent `𝒪_X`-modules: the first
proof only ever used `CategoryTheory.NatTrans.naturality` of that counit. -/
theorem associatedModuleChartSchemeModuleIso_naturality_hom (A : SmallEtale B S hS X.1)
    (g : chartSchemeEtaleQcoh B S hS X M hM A ⟶ chartSchemeEtaleQcoh B S hS X N hN A) :
    (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS X A).left.property).map
        ((SheafOfModules.isQuasicoherent (chartScheme A).ringCatSheaf).ι.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
            (associatedBigEtaleSite B) (chartScheme A)
            (chartFppfObject B S hS X A).left.property).inverse.map g)) ≫
        (associatedModuleChartSchemeModuleIso B S hS X N hN A).hom =
      (associatedModuleChartSchemeModuleIso B S hS X M hM A).hom ≫
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).ι.map g :=
  have h := congrArg (fun k =>
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).ι.map k)
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
      (associatedBigEtaleSite B) (chartScheme A)
      (chartFppfObject B S hS X A).left.property).counitIso.hom.naturality g)
  (((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedSchemeStructureSheaf B S hS
        (chartFppfObject B S hS X A))).ι.map_comp _ _).symm.trans
    (h.trans ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedSchemeStructureSheaf B S hS
        (chartFppfObject B S hS X A))).ι.map_comp _ _)))

/-- **The chart transport isomorphism is natural at an arbitrary morphism of the quasi-coherent
restrictions to the small étale site of the chart's scheme.**

This is `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule_naturality` for a morphism
which need not come from a morphism of quasi-coherent `𝒪_X`-modules; it is glued from the unit of
the associated-module adjunction and the counit of the equivalence of Descent, Proposition
03DX (2) by `Stacks.CategoryTheory.comp_unit_comp_map`, exactly as the first one is. -/
theorem chartSchemeModuleIsoRestrictModule_naturality_hom (A : SmallEtale B S hS X.1)
    (g : chartSchemeEtaleQcoh B S hS X M hM A ⟶ chartSchemeEtaleQcoh B S hS X N hN A) :
    (SheafOfModules.isQuasicoherent (chartScheme A).ringCatSheaf).ι.map
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
            (associatedBigEtaleSite B) (chartScheme A)
            (chartFppfObject B S hS X A).left.property).inverse.map g) ≫
        (chartSchemeModuleIsoRestrictModule B S hS X N hN A).hom =
      (chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            (chartScheme A) (chartFppfObject B S hS X A).left.property).map
          ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).ι.map g) :=
  Stacks.CategoryTheory.comp_unit_comp_map
    (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS X A).left.property)
    ((SheafOfModules.isQuasicoherent (chartScheme A).ringCatSheaf).ι.map
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'
        (associatedBigEtaleSite B) (chartScheme A)
        (chartFppfObject B S hS X A).left.property).inverse.map g))
    (associatedModuleChartSchemeModuleIso B S hS X M hM A).hom
    (associatedModuleChartSchemeModuleIso B S hS X N hN A).hom
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).ι.map g)
    (associatedModuleChartSchemeModuleIso_naturality_hom B S hS X M N hM hN A g)

/-- **The naturality square of the Hom-set transport.**  The transport of `α` followed by the
chart transport isomorphism at the target is the chart transport isomorphism at the source
followed by the restriction, along the inclusion of the small Zariski site, of the leg
`AlgebraicGeometry.Space.chartEtaleQcohHom` of the transport.

This is the statement that crosses the `CategoryTheory.Functor.objPreimage` in the inverse of
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`: the transport is never
unfolded there, it is conjugated. -/
theorem chartSchemeModuleHomEquiv_naturality (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) :
    chartSchemeModuleHomEquiv B S hS X M N hM hN A α ≫
        (chartSchemeModuleIsoRestrictModule B S hS X N hN A).hom =
      (chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom ≫
        (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            (chartScheme A) (chartFppfObject B S hS X A).left.property).map
          ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).ι.map
            (chartEtaleQcohHom B S hS X M N hM hN A α)) :=
  chartSchemeModuleIsoRestrictModule_naturality_hom B S hS X M N hM hN A
    (chartEtaleQcohHom B S hS X M N hM hN A α)

/-! ### The transport on sections over a Zariski open -/

/-- **The transport of `α` to the small Zariski site of the chart's scheme, read on sections over
a Zariski open.**  This is the morphism whose components the formula below computes. -/
noncomputable def chartHomSectionsMap (A : SmallEtale B S hS X.1) (α : M.over A ⟶ N.over A)
    (V : (chartScheme A).Opens) :
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V) ⟶
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X N hN A)).val.obj (op V) :=
  ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS X A).left.property).map
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).ι.map
      (chartEtaleQcohHom B S hS X M N hM hN A α))).val.app (op V)

/-- **The naturality square of the Hom-set transport, read on a section.** -/
theorem chartSchemeModuleHomEquiv_naturality_apply (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    ((chartSchemeModuleIsoRestrictModule B S hS X N hN A).hom.val.app (op V)).hom
        (((chartSchemeModuleHomEquiv B S hS X M N hM hN A α).val.app (op V)).hom x) =
      (chartHomSectionsMap B S hS X M N hM hN A α V).hom
        (((chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V)).hom x) :=
  (Stacks.SheafOfModules.comp_val_app_hom_apply _ _ (op V) x).symm.trans
    ((congrArg (fun k => ((k.val.app (op V)).hom x))
        (chartSchemeModuleHomEquiv_naturality B S hS X M N hM hN A α)).trans
      (Stacks.SheafOfModules.comp_val_app_hom_apply _ _ (op V) x))

/-! ### The component square -/

include hM in
/-- **The chart sections identification with its sections side spelled on the slice.**
This is `AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_obj_moduleCat` with the
sections of `M` over `AlgebraicGeometry.Space.openChartOfComparison` read as the sections of
`M.over A` over `AlgebraicGeometry.Space.openChartOfComparisonOver` — which is what
`Stacks.SheafOfModules.pushforward_id_two_map_val_app` produces, the morphism it is natural in
living on the slice.

Only the sections side is respelled: the module side is left at its original spelling, so that every
step below composes with it syntactically.  Respelling both at once is what
`AlgebraicGeometry.Space.restrictModule_chartSchemeEtaleModule_obj_moduleCat` already does in two
steps, for the heartbeat reason recorded there. -/
theorem chartSectionsOver_obj_moduleCat (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V) =
      (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).obj
        ((M.over A).val.obj (op (openChartOfComparisonOver B S hS X A V))) :=
  restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M hM A V

/-- **The component square of the transport over a Zariski open of the chart's scheme**, with the
two sections identifications as parameters.

They are parameters because the conclusion mentions each of them inside a
`CategoryTheory.eqToHom`: as parameters their types are elaborated once and nothing is matched,
whereas the three-layer spelling of the chart restriction which they carry would otherwise be
matched against the original one at every occurrence. -/
theorem chartHomSectionsMapRaw_naturality (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens)
    (hM' : ((SheafOfModules.pushforward.{u} (_root_.AlgebraicGeometry.SmallEtale.structureMap
            (associatedBigEtaleSite B) (chartScheme A)
            (chartFppfObject B S hS X A).left.property)).obj
        ((SheafOfModules.pushforward.{u} (Stacks.SheafOfModules.reindexBackSharp
            (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
            (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
            (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)))).obj
          ((SheafOfModules.pushforward.{u}
              (𝟙 (((SmallEtale.chartLocalizationEquivalence B S hS X.1
                      A).functor.sheafPushforwardContinuous RingCat.{u}
                    (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
                    ((SmallEtale.topology B S hS X.1).over A)).obj
                  ((structureRingSheaf B S hS X).over A)))).obj (M.over A)))).val.obj (op V) =
      (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).obj
        ((M.over A).val.obj (op (openChartOfComparisonOver B S hS X A V))))
    (hN' : ((SheafOfModules.pushforward.{u} (_root_.AlgebraicGeometry.SmallEtale.structureMap
            (associatedBigEtaleSite B) (chartScheme A)
            (chartFppfObject B S hS X A).left.property)).obj
        ((SheafOfModules.pushforward.{u} (Stacks.SheafOfModules.reindexBackSharp
            (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
            (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
            (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)))).obj
          ((SheafOfModules.pushforward.{u}
              (𝟙 (((SmallEtale.chartLocalizationEquivalence B S hS X.1
                      A).functor.sheafPushforwardContinuous RingCat.{u}
                    (SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
                    ((SmallEtale.topology B S hS X.1).over A)).obj
                  ((structureRingSheaf B S hS X).over A)))).obj (N.over A)))).val.obj (op V) =
      (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).obj
        ((N.over A).val.obj (op (openChartOfComparisonOver B S hS X A V)))) :
    ((SheafOfModules.pushforward.{u} (_root_.AlgebraicGeometry.SmallEtale.structureMap
              (associatedBigEtaleSite B) (chartScheme A)
              (chartFppfObject B S hS X A).left.property)).map
          ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).ι.map
            (chartEtaleQcohHom B S hS X M N hM hN A α))).val.app (op V) ≫ eqToHom hN' =
      eqToHom hM' ≫
        (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).map
          (α.val.app (op (openChartOfComparisonOver B S hS X A V))) :=
  Stacks.SheafOfModules.pushforward_id_two_map_val_app
    (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS X A).left.property)
    (Stacks.SheafOfModules.reindexBackSharp
      (J' := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
      (representedSmallEtaleEquivalence B S hS (chartFppfObject B S hS X A))
      (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A)))
    (J₂ := SmallEtale.topology B S hS (yoneda.obj (chartFppfObject B S hS X A)))
    (C₃ := CategoryTheory.Over A)
    (J₃ := (SmallEtale.topology B S hS X.1).over A)
    (F₃ := (SmallEtale.chartLocalizationEquivalence B S hS X.1 A).functor)
    (R₃ := (structureRingSheaf B S hS X).over A)
    (inst₃ := isContinuous_chartLocalization_chartSpace B S hS X A)
    (f := α) (A := V)
    (k := (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).ι.map
      (chartEtaleQcohHom B S hS X M N hM hN A α))
    (hk := ι_map_chartEtaleQcohHom B S hS X M N hM hN A α)
    (P := openChartOfComparisonOver B S hS X A V) (hP := rfl)
    (g := chartSectionsRingHom B S hS X A V) (hg := rfl)
    (hM := hM') (hN := hN')

/-- `AlgebraicGeometry.Space.chartHomSectionsMapRaw_naturality` at the chart sections
identification. -/
theorem chartHomSectionsMapRaw_naturality' (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens) :
    ((SheafOfModules.pushforward.{u} (_root_.AlgebraicGeometry.SmallEtale.structureMap
              (associatedBigEtaleSite B) (chartScheme A)
              (chartFppfObject B S hS X A).left.property)).map
          ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS X A))).ι.map
            (chartEtaleQcohHom B S hS X M N hM hN A α))).val.app (op V) ≫
        eqToHom (chartSectionsOver_obj_moduleCat B S hS X N hN A V) =
      eqToHom (chartSectionsOver_obj_moduleCat B S hS X M hM A V) ≫
        (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).map
          (α.val.app (op (openChartOfComparisonOver B S hS X A V))) :=
  chartHomSectionsMapRaw_naturality B S hS X M N hM hN A α V
    (chartSectionsOver_obj_moduleCat B S hS X M hM A V)
    (chartSectionsOver_obj_moduleCat B S hS X N hN A V)

/-- `AlgebraicGeometry.Space.chartHomSectionsMapRaw_naturality'` with its left factor spelled by
`AlgebraicGeometry.Space.chartHomSectionsMap`. -/
theorem chartHomSectionsMap_naturality (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens) :
    chartHomSectionsMap B S hS X M N hM hN A α V ≫
        eqToHom (chartSectionsOver_obj_moduleCat B S hS X N hN A V) =
      eqToHom (chartSectionsOver_obj_moduleCat B S hS X M hM A V) ≫
        (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).map
          (α.val.app (op (openChartOfComparisonOver B S hS X A V))) :=
  chartHomSectionsMapRaw_naturality' B S hS X M N hM hN A α V

/-- The left-hand composite of `AlgebraicGeometry.Space.chartHomSectionsMap_naturality`, read on
a section. -/
theorem chartHomSectionsMap_comp_eqToHom_apply (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens)
    (y : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V)) :
    (chartHomSectionsMap B S hS X M N hM hN A α V ≫
        eqToHom (chartSectionsOver_obj_moduleCat B S hS X N hN A V)).hom y =
      (eqToHom (chartSectionsOver_obj_moduleCat B S hS X N hN A V)).hom
        ((chartHomSectionsMap B S hS X M N hM hN A α V).hom y) :=
  Stacks.ModuleCat.comp_hom_apply (chartHomSectionsMap B S hS X M N hM hN A α V)
    (eqToHom (chartSectionsOver_obj_moduleCat B S hS X N hN A V)) y

/-- The right-hand composite of `AlgebraicGeometry.Space.chartHomSectionsMap_naturality`, read on
a section. -/
theorem eqToHom_comp_restrictScalars_map_chartHom_apply (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens)
    (y : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V)) :
    (eqToHom (chartSectionsOver_obj_moduleCat B S hS X M hM A V) ≫
        (ModuleCat.restrictScalars (chartSectionsRingHom B S hS X A V)).map
          (α.val.app (op (openChartOfComparisonOver B S hS X A V)))).hom y =
      (α.val.app (op (openChartOfComparisonOver B S hS X A V))).hom
        ((eqToHom (chartSectionsOver_obj_moduleCat B S hS X M hM A V)).hom y) :=
  Stacks.ModuleCat.eqToHom_comp_restrictScalars_map_hom_apply
    (chartSectionsRingHom B S hS X A V)
    (chartSectionsOver_obj_moduleCat B S hS X M hM A V)
    (α.val.app (op (openChartOfComparisonOver B S hS X A V))) y

/-- **The component square, read on a section.** -/
theorem chartHomSectionsMap_naturality_over_apply (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens)
    (y : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V)) :
    (eqToHom (chartSectionsOver_obj_moduleCat B S hS X N hN A V)).hom
        ((chartHomSectionsMap B S hS X M N hM hN A α V).hom y) =
      (α.val.app (op (openChartOfComparisonOver B S hS X A V))).hom
        ((eqToHom (chartSectionsOver_obj_moduleCat B S hS X M hM A V)).hom y) :=
  (chartHomSectionsMap_comp_eqToHom_apply B S hS X M N hM hN A α V y).symm.trans
    ((DFunLike.congr_fun
        (congrArg ModuleCat.Hom.hom
          (chartHomSectionsMap_naturality B S hS X M N hM hN A α V)) y).trans
      (eqToHom_comp_restrictScalars_map_chartHom_apply B S hS X M N hM A α V y))

/-- **The two spellings of the chart sections identification agree on every section.**  Both are
transports along equalities of modules whose underlying types agree by projections alone, so
`Stacks.ModuleCat.eqToHom_hom_apply` reduces each to a `cast` and proof irrelevance finishes. -/
theorem eqToHom_chartSectionsOver_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens)
    (y : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V)) :
    (eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M hM A V)).hom y =
      (eqToHom (chartSectionsOver_obj_moduleCat B S hS X M hM A V)).hom y :=
  (Stacks.ModuleCat.eqToHom_hom_apply _ y).trans
    (Stacks.ModuleCat.eqToHom_hom_apply
      (chartSectionsOver_obj_moduleCat B S hS X M hM A V) y).symm

/-- **The component square, read on a section, at the original chart sections identification.** -/
theorem chartHomSectionsMap_naturality_apply (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens)
    (y : ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V)) :
    (eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X N hN A V)).hom
        ((chartHomSectionsMap B S hS X M N hM hN A α V).hom y) =
      (α.val.app (op (openChartOfComparisonOver B S hS X A V))).hom
        ((eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X M hM A V)).hom
          y) :=
  ((eqToHom_chartSectionsOver_apply B S hS X N hN A V
          ((chartHomSectionsMap B S hS X M N hM hN A α V).hom y)).trans
      (chartHomSectionsMap_naturality_over_apply B S hS X M N hM hN A α V y)).trans
    (congrArg (α.val.app (op (openChartOfComparisonOver B S hS X A V))).hom
      (eqToHom_chartSectionsOver_apply B S hS X M hM A V y).symm)

/-! ### The component formula -/

/-- **The component formula for the Hom-set transport of the chart restriction at a Zariski open
of the chart's scheme.**  Let `α : M|_A ⟶ N|_A` be a morphism of the restrictions to the slice of
the small étale site of `X` at an étale scheme chart `A`, and let `V` be a Zariski open of the
chart's scheme.  Then the `V`-component of `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` of
`α`, read through `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` and
`AlgebraicGeometry.Space.chartSectionsLinearEquiv`, is the component of `α` over
`AlgebraicGeometry.Space.openChartOfComparisonOver … A V`, the object of the slice which `V` cuts
out.

This is `AlgebraicGeometry.Space.chartSectionsLinearEquiv_naturality_apply` for an arbitrary
morphism on the slice in place of one coming from a morphism of global quasi-coherent
`𝒪_X`-modules.  It is what the descent of the chart half of Stacks 07UM needs: the surviving
per-chart condition of `AlgebraicGeometry.Space.homRestr_eq_of_forall_openChart_le` mentions `α`
only through `homRestr … (openChartInclusion … A (V i)) α`, whose components are the components of
`α` over the objects of the slice which the Zariski opens cut out, and this computes those from
the transport on the chart's scheme. -/
theorem chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply (A : SmallEtale B S hS X.1)
    (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    chartSectionsLinearEquiv B S hS X N hN A V
        (((chartSchemeModuleIsoRestrictModule B S hS X N hN A).hom.val.app (op V)).hom
          (((chartSchemeModuleHomEquiv B S hS X M N hM hN A α).val.app (op V)).hom x)) =
      (α.val.app (op (openChartOfComparisonOver B S hS X A V))).hom
        (chartSectionsLinearEquiv B S hS X M hM A V
          (((chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V)).hom x)) :=
  (((chartSectionsLinearEquiv_apply B S hS X N hN A V _).trans
        (congrArg
          (eqToHom (restrictModule_chartSchemeEtaleModule_obj_moduleCat B S hS X N hN A V)).hom
          (chartSchemeModuleHomEquiv_naturality_apply B S hS X M N hM hN A α V x))).trans
      (chartHomSectionsMap_naturality_apply B S hS X M N hM hN A α V _)).trans
    (congrArg (α.val.app (op (openChartOfComparisonOver B S hS X A V))).hom
      (chartSectionsLinearEquiv_apply B S hS X M hM A V _).symm)

/-- **The component formula, read backwards.**  The component of `(chartSchemeModuleHomEquiv …
A).symm β` over the object of the slice which a Zariski open `V` cuts out is the `V`-component of
`β`, read through `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` and
`AlgebraicGeometry.Space.chartSectionsLinearEquiv`.

This is the direction in which a morphism produced on the chart's scheme — such as the one
`AlgebraicGeometry.Space.chartAlpha` carries back from the first display of [Stacks, Tag 01YB] —
has its components over the Zariski opens of the chart's scheme computed. -/
theorem chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_symm_apply
    (A : SmallEtale B S hS X.1)
    (β : chartSchemeModule B S hS X M hM A ⟶ chartSchemeModule B S hS X N hN A)
    (V : (chartScheme A).Opens)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    (((chartSchemeModuleHomEquiv B S hS X M N hM hN A).symm β).val.app
          (op (openChartOfComparisonOver B S hS X A V))).hom
        (chartSectionsLinearEquiv B S hS X M hM A V
          (((chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V)).hom x)) =
      chartSectionsLinearEquiv B S hS X N hN A V
        (((chartSchemeModuleIsoRestrictModule B S hS X N hN A).hom.val.app (op V)).hom
          ((β.val.app (op V)).hom x)) :=
  (chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply B S hS X M N hM hN A
      ((chartSchemeModuleHomEquiv B S hS X M N hM hN A).symm β) V x).symm.trans
    (congrArg (fun k : chartSchemeModule B S hS X M hM A ⟶ chartSchemeModule B S hS X N hN A =>
        chartSectionsLinearEquiv B S hS X N hN A V
          (((chartSchemeModuleIsoRestrictModule B S hS X N hN A).hom.val.app (op V)).hom
            ((k.val.app (op V)).hom x)))
      ((chartSchemeModuleHomEquiv B S hS X M N hM hN A).apply_symm_apply β))


/-! ### The component formula at the composite -/

/-- **The component at a Zariski open of the chart's scheme of the chart transport isomorphism, as
a linear equivalence** over the functions on that open.

This is the first factor of `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv`. -/
noncomputable def chartSchemeModuleIsoRestrictModuleLinearEquiv (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    (chartSchemeModule B S hS X M hM A).val.obj (op V)
      ≃ₗ[(chartScheme A).ringCatSheaf.obj.obj (op V)]
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V) :=
  Iso.toLinearEquiv
    { hom := (chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V)
      inv := (chartSchemeModuleIsoRestrictModule B S hS X M hM A).inv.val.app (op V)
      hom_inv_id := congrArg (fun k => k.val.app (op V))
        (chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom_inv_id
      inv_hom_id := congrArg (fun k => k.val.app (op V))
        (chartSchemeModuleIsoRestrictModule B S hS X M hM A).inv_hom_id }

/-- **The component of the chart transport isomorphism followed by an arbitrary linear
equivalence, read on a section.**  The first factor contributes the component of
`AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule` at the Zariski open.

The second equivalence is left a variable deliberately, and that is what makes this `rfl`: with
`AlgebraicGeometry.Space.chartSectionsLinearEquiv` in its place the `whnf` of the coercion unfolds
that factor's `CategoryTheory.eqToIso` and the comparison exhausts the heartbeat budget. -/
theorem trans_chartSchemeModuleIsoRestrictModuleLinearEquiv_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens)
    {Z : _root_.ModuleCat.{u} ((chartScheme A).ringCatSheaf.obj.obj (op V))}
    (e : (((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        (chartScheme A) (chartFppfObject B S hS X A).left.property).obj
          (chartSchemeEtaleModule B S hS X M hM A)).val.obj (op V))
      ≃ₗ[(chartScheme A).ringCatSheaf.obj.obj (op V)] Z)
    (y : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    (LinearEquiv.trans (chartSchemeModuleIsoRestrictModuleLinearEquiv B S hS X M hM A V) e) y =
      e (((chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V)).hom y) :=
  rfl

/-- The composite sections identification is the transitivity of its two factors, by `rfl`: that
is how it is defined.  Stated *unapplied*, which is where the comparison is free. -/
theorem chartSchemeModuleSectionsLinearEquiv_eq_trans (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) :
    chartSchemeModuleSectionsLinearEquiv B S hS X M hM A V =
      LinearEquiv.trans (chartSchemeModuleIsoRestrictModuleLinearEquiv B S hS X M hM A V)
        (chartSectionsLinearEquiv B S hS X M hM A V) :=
  rfl

/-- **The composite sections identification, read on a section.**  Over a Zariski open `V` of the
chart's scheme, `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv` of a section of the
chart restriction is `AlgebraicGeometry.Space.chartSectionsLinearEquiv` of its image under the
`V`-component of `AlgebraicGeometry.Space.chartSchemeModuleIsoRestrictModule`.

This is the delta equation, read on a section through the two free steps described in the
implementation notes. -/
theorem chartSchemeModuleSectionsLinearEquiv_apply (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens)
    (y : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    chartSchemeModuleSectionsLinearEquiv B S hS X M hM A V y =
      chartSectionsLinearEquiv B S hS X M hM A V
        (((chartSchemeModuleIsoRestrictModule B S hS X M hM A).hom.val.app (op V)).hom y) :=
  (congrArg (fun e => e y)
      (chartSchemeModuleSectionsLinearEquiv_eq_trans B S hS X M hM A V)).trans
    (trans_chartSchemeModuleIsoRestrictModuleLinearEquiv_apply B S hS X M hM A V
      (chartSectionsLinearEquiv B S hS X M hM A V) y)

/-- **The component formula for the Hom-set transport, at the composite sections
identification.**  Let `α : M|_A ⟶ N|_A` be a morphism of the restrictions to the slice of the
small étale site of `X` at an étale scheme chart `A`, and let `V` be a Zariski open of the chart's
scheme.  Then the `V`-component of `AlgebraicGeometry.Space.chartSchemeModuleHomEquiv` of `α`,
read through `AlgebraicGeometry.Space.chartSchemeModuleSectionsLinearEquiv`, is the component of
`α` over `AlgebraicGeometry.Space.openChartOfComparisonOver … A V`.

This is `AlgebraicGeometry.Space.chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply` at the
composite of the two factors in place of the second factor after the component of the first, and
it is the spelling in which the affine-chart reading of the internal Hom conjugates the Hom-module
on the chart's scheme onto the chart: there the two conjugates have to be shown to be the same
component of the section, and the composite is what that reading holds.  It is proved here, from
the formula at the factors, and not there from it: the composite cannot be decomposed after the
fact, and the implementation notes say what that costs and why this pair of steps does not. -/
theorem chartSchemeModuleSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply
    (A : SmallEtale B S hS X.1) (α : M.over A ⟶ N.over A) (V : (chartScheme A).Opens)
    (x : (chartSchemeModule B S hS X M hM A).val.obj (op V)) :
    chartSchemeModuleSectionsLinearEquiv B S hS X N hN A V
        (((chartSchemeModuleHomEquiv B S hS X M N hM hN A α).val.app (op V)).hom x) =
      (α.val.app (op (openChartOfComparisonOver B S hS X A V))).hom
        (chartSchemeModuleSectionsLinearEquiv B S hS X M hM A V x) := by
  rw [chartSchemeModuleSectionsLinearEquiv_apply, chartSchemeModuleSectionsLinearEquiv_apply]
  exact chartSectionsLinearEquiv_chartSchemeModuleHomEquiv_apply B S hS X M N hM hN A α V x

end AlgebraicGeometry.Space

end
