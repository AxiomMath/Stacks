module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparison
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.AlgebraIso
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Comparison
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Invertible
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageStructureSheaf

/-!
# Base change of the chart restriction of an algebra sheaf

Let `X` be an algebraic space over a scheme `S` in a big fppf site `B`, let `A` be a sheaf of
commutative `𝒪_X`-algebras on the small étale site of `X`, and let `h : V' ⟶ V` be a morphism of
étale scheme charts of `X`.  Restricting `A` to the two chart schemes gives sheaves of
commutative algebras `A|_V` and `A|_{V'}` on the Zariski sites of `chartScheme V` and
`chartScheme V'` (`AlgebraicGeometry.Space.chartSchemeAlgebra`), and this file constructs the
**canonical comparison between `A|_{V'}` and the base change of `A|_V` along the morphism of
chart schemes `chartSchemeMap h`**, in the three equivalent forms

* a morphism of sheaves of commutative rings `A|_V ⟶ (chartSchemeMap h)_* A|_{V'}`,
* its transpose `(chartSchemeMap h)^{-1} A|_V ⟶ A|_{V'}`, and
* a morphism of sheaves of commutative algebras
  `(algebraPullback (chartSchemeMap h)).obj (A|_V) ⟶ A|_{V'}`
  out of the algebra pullback `g^{-1}(A|_V) ⊗_{g^{-1}𝒪_V} 𝒪_{V'}` of Stacks 01SA.

The third is the one the atlas construction of the relative spectrum consumes: it is the map
whose invertibility identifies the relative spectrum of `A|_{V'}` with the base change along
`chartSchemeMap h` of the relative spectrum of `A|_V`.

## Main definitions

* `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardComparison`: the comparison
  `A|_V ⟶ (chartSchemeMap h)_* A|_{V'}` of sheaves of commutative rings.
* `AlgebraicGeometry.Space.chartSchemeAlgebraPullbackComparison`: its inverse-image transpose.
* `AlgebraicGeometry.Space.chartSchemeAlgebraBaseChangeHom`: **the canonical comparison
  `(algebraPullback (chartSchemeMap h)).obj (A|_V) ⟶ A|_{V'}` of sheaves of commutative
  algebras.**

## Main results

* `AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardComparison_app`: over a Zariski open `O`
  of `chartScheme V` the comparison is, on the nose, the restriction map of `A` along the
  morphism of étale charts `AlgebraicGeometry.Space.openChartRestrict`.  No sheafification
  intervenes, so the comparison is computable at every open.
* `AlgebraicGeometry.Space.hom_comp_chartSchemeAlgebraPushforwardComparison` and
  `AlgebraicGeometry.Space.pullback_map_hom_comp_chartSchemeAlgebraPullbackComparison`: the
  comparison carries the structure morphism of `A|_V` to the structure morphism of `A|_{V'}`.
  The second is the commuting square the universal property of the algebra pullback consumes,
  and is what makes the algebra-level comparison exist at all.
* `AlgebraicGeometry.Space.chartSchemeAlgebraBaseChangeHom_right` and
  `AlgebraicGeometry.Space.algebraPullbackMap_comp_chartSchemeAlgebraBaseChangeHom`: the
  algebra-level comparison is the map out of the pushout determined by the inverse-image
  comparison and the structure morphism, so it is canonical: it is the unique map of algebras
  whose composite with `Stacks.AffineAlgebraEquivalence.algebraPullbackMap` is the
  inverse-image comparison.

## Implementation notes

**Nothing is sheafified, and that is what makes the comparison computable.**  Both chart
restrictions of `A` are direct images of sheaves of commutative rings along the index functor
`AlgebraicGeometry.Space.openChartFunctor`, which is continuous
(`AlgebraicGeometry.Space.isContinuous_openChartFunctor`), so the sections of `A|_V` over a
Zariski open `O` are the sections of `A` over the étale chart `O` cuts out, on the nose.  The
comparison in the direct-image direction is therefore the map on sections induced by
`AlgebraicGeometry.Space.openChartRestrictNatTrans`, with no unit of a sheafification
adjunction to transpose.  This is in contrast with the module-level comparison
`AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison`, whose definition goes
through `CategoryTheory.PresheafOfModules.sheafificationHomEquiv` and whose components the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartModuleRestrictionComparison.lean` record as not
stated.

**The compatibility with the structure morphisms is the one piece of scheme geometry**, and it
is already in the tree:
`AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict` says that
restricting a morphism of schemes to an open of its target and the preimage of that open is, on
global sections, the map on sections over the open.  That is exactly the component
of `AlgebraicGeometry.Space.hom_comp_chartSchemeAlgebraPushforwardComparison` after the
naturality of the structure-algebra map of `A` has been used, and no other computation enters.

**The two spellings of a sheaf of commutative rings on a chart scheme.**
`AlgebraicGeometry.Scheme.sheaf` ascribes its type, so `(chartScheme V).sheaf` and the
corresponding `CategoryTheory.Sheaf` of the Zariski topology are definitionally equal but not
syntactically equal, and a `rw` inside a goal mixing them fails on a term that is not
type-correct at reducible transparency.  Two measures are taken.  First, the
identification of the transpose of the structural map `g^{-1}𝒪_S ⟶ 𝒪_T` with the comparison of
structure sheaves is taken from
`AlgebraicGeometry.Scheme.Hom.homEquiv_inverseImageStructureMap`, which states it at a bare
morphism of schemes where only one spelling occurs, and is handed to the proof by application
rather than reached for by rewriting the definition.  Second, the component computation of
`AlgebraicGeometry.Space.hom_comp_chartSchemeAlgebraPushforwardComparison` is assembled in term
mode from `CategoryTheory.Category.assoc` and `congrArg`, since the goal mixes
`(structureSheaf …).obj.obj (op (openChart V O))` with `Γ(chartScheme V, O)` — again
definitionally equal, again not matchable.

**No `stacks` attribute is carried.**  The algebra-level chart base-change comparison is not a
numbered assertion of the source: Stacks 01SA supplies the algebra pullback and its universal
property on a *scheme*, and the restriction of an algebra on an algebraic space to a chart
scheme is `AlgebraicGeometry.Space.chartSchemeAlgebra`, which is untagged for the reasons
recorded there.  What is built here is the comparison morphism between the two, and its
invertibility — the statement a consumer wants — is *not* proved; see the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeAlgebra.lean` and the discussion below.

**Invertibility is proved downstream.**  Invertibility of the algebra-level comparison is
equivalent to invertibility of the module-level one
(`AlgebraicGeometry.Space.isIso_chartSchemeAlgebraBaseChangeHom_of_isIso_module`), which is
Descent, Proposition 03DX (2) in sheafified form, and that is
`AlgebraicGeometry.Space.isIso_chartSchemeModuleBaseChangeHom` of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSchemeModuleBaseChangeIso.lean`, with
`AlgebraicGeometry.Space.isIso_chartSchemeAlgebraBaseChangeHom` the algebra-level statement.  It
is not proved here only because the proof needs the affine-open machinery of
`StacksFrontier/AlgebraicGeometry/PullbackSections/` and of
`StacksFrontier/AlgebraicGeometry/AffineBaseChange/`, which is not in this file's closure.

The proof runs the three steps this file's notes used to list as open, and the one of them with
no ready-made lemma — transporting a base change across the isomorphism
`AlgebraicGeometry.Scheme.restrictFunctorΓ` of the two base rings, which
`IsBaseChange.iff_of_equiv_comm` cannot do because it keeps the rings fixed — is done with
`TensorProduct.addEquivOfRingEquiv` of
`StacksFrontier/LinearAlgebra/TensorProduct/BaseRingAddEquiv.lean`, which moves the base ring along
a ring isomorphism.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    {V' V : SmallEtale B S hS X.1} (h : V' ⟶ V)

/-! ### The comparison in the direct-image direction -/

/-- **Chart functoriality of the restriction of an algebra sheaf to a chart scheme.**  For a
morphism `h : V' ⟶ V` of étale charts of `X`, the restriction of `A` to the larger chart scheme
maps to the direct image along `chartSchemeMap h` of its restriction to the smaller one.

Over a Zariski open `O` of `chartScheme V` it is the restriction map of `A` along the morphism
of étale charts `AlgebraicGeometry.Space.openChartRestrict`; no sheafification occurs, the index
functor of the chart restriction being continuous. -/
def chartSchemeAlgebraPushforwardComparison :
    (chartSchemeAlgebra B S hS X A V).right ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap h).base).obj
        (chartSchemeAlgebra B S hS X A V').right :=
  ⟨Functor.whiskerRight (NatTrans.op (openChartRestrictNatTrans B S hS X.1 h)) A.right.obj⟩

/-- **The comparison on sections over a Zariski open is the restriction map of `A`** along the
morphism of étale charts that open determines. -/
theorem chartSchemeAlgebraPushforwardComparison_app (O : (chartScheme V).Opens) :
    (chartSchemeAlgebraPushforwardComparison B S hS X A h).hom.app (op O) =
      A.right.obj.map ((openChartRestrictNatTrans B S hS X.1 h).app O).op :=
  rfl

/-- **The comparison carries the structure morphism of `A|_V` to the structure morphism of
`A|_{V'}`.**

Over a Zariski open this is the naturality of the structure-algebra map of `A` followed by
`AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict`, the one piece
of scheme geometry the comparison needs. -/
theorem hom_comp_chartSchemeAlgebraPushforwardComparison :
    (chartSchemeAlgebra B S hS X A V).hom ≫
        chartSchemeAlgebraPushforwardComparison B S hS X A h =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            (chartSchemeMap h).base).homEquiv _ _)
          (_root_.AlgebraicGeometry.inverseImageStructureMap (chartSchemeMap h)) ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (chartSchemeMap h).base).map
          (chartSchemeAlgebra B S hS X A V').hom := by
  rw [_root_.AlgebraicGeometry.Scheme.Hom.homEquiv_inverseImageStructureMap]
  refine Sheaf.hom_ext (NatTrans.ext (funext fun Oop => ?_))
  obtain ⟨O⟩ := Oop
  change (Scheme.restrictFunctorΓ (X := chartScheme V)).inv.app (op O) ≫
        A.hom.hom.app (op ((openChartFunctor B S hS X.1 V).obj O)) ≫
        A.right.obj.map ((openChartRestrictNatTrans B S hS X.1 h).app O).op =
      (chartSchemeMap h).c.app (op O) ≫
        (Scheme.restrictFunctorΓ (X := chartScheme V')).inv.app
          (op ((Opens.map (chartSchemeMap h).base).obj O)) ≫
        A.hom.hom.app (op ((openChartFunctor B S hS X.1 V').obj
          ((Opens.map (chartSchemeMap h).base).obj O)))
  refine Eq.trans (congrArg (fun z =>
      (Scheme.restrictFunctorΓ (X := chartScheme V)).inv.app (op O) ≫ z)
    (A.hom.hom.naturality ((openChartRestrictNatTrans B S hS X.1 h).app O).op).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
      A.hom.hom.app (op ((openChartFunctor B S hS X.1 V').obj
        ((Opens.map (chartSchemeMap h).base).obj O))))
    (Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict (chartSchemeMap h) O)) ?_
  exact Category.assoc _ _ _

/-! ### The comparison in the inverse-image direction -/

/-- **Chart functoriality of the restriction of an algebra sheaf, inverse-image form.**  For a
morphism `h : V' ⟶ V` of étale charts of `X`, the inverse image along `chartSchemeMap h` of the
restriction of `A` to the larger chart scheme maps to its restriction to the smaller one.

This is the transpose of
`AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardComparison` along
`CategoryTheory.TopCat.Sheaf.pullbackPushforwardAdjunction`. -/
def chartSchemeAlgebraPullbackComparison :
    (TopCat.Sheaf.pullback CommRingCat.{u} (chartSchemeMap h).base).obj
        (chartSchemeAlgebra B S hS X A V).right ⟶
      (chartSchemeAlgebra B S hS X A V').right :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (chartSchemeMap h).base).homEquiv _ _).symm
      (chartSchemeAlgebraPushforwardComparison B S hS X A h)

/-- **The commuting square the universal property of the algebra pullback consumes**: the
inverse image of the structure morphism of `A|_V`, followed by the inverse-image comparison, is
the structural map `g^{-1}𝒪_V ⟶ 𝒪_{V'}` followed by the structure morphism of `A|_{V'}`. -/
theorem pullback_map_hom_comp_chartSchemeAlgebraPullbackComparison :
    (TopCat.Sheaf.pullback CommRingCat.{u} (chartSchemeMap h).base).map
        (chartSchemeAlgebra B S hS X A V).hom ≫
        chartSchemeAlgebraPullbackComparison B S hS X A h =
      _root_.AlgebraicGeometry.inverseImageStructureMap (chartSchemeMap h) ≫
        (chartSchemeAlgebra B S hS X A V').hom := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    (chartSchemeMap h).base).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    chartSchemeAlgebraPullbackComparison, Equiv.apply_symm_apply,
    hom_comp_chartSchemeAlgebraPushforwardComparison]

/-! ### The comparison of algebras -/

/-- **The algebra-level chart base-change comparison.**  For a morphism `h : V' ⟶ V` of étale
charts of `X`, the base change along `chartSchemeMap h` of the restriction of `A` to
`chartScheme V` maps to the restriction of `A` to `chartScheme V'`, as sheaves of commutative
algebras on `chartScheme V'`.

The algebra pullback of Stacks 01SA is the pushout `g^{-1}(A|_V) ⊗_{g^{-1}𝒪_V} 𝒪_{V'}`, so a map
out of it is exactly a pair of maps agreeing on `g^{-1}𝒪_V`: the inverse-image comparison
`AlgebraicGeometry.Space.chartSchemeAlgebraPullbackComparison` and the structure morphism of
`A|_{V'}`, which agree by
`AlgebraicGeometry.Space.pullback_map_hom_comp_chartSchemeAlgebraPullbackComparison`.  This is
the comparison whose invertibility identifies the relative spectrum of `A|_{V'}` with the base
change of the relative spectrum of `A|_V`; invertibility is not proved here, see the
implementation notes. -/
def chartSchemeAlgebraBaseChangeHom :
    (Stacks.AffineAlgebraEquivalence.algebraPullback (chartSchemeMap h)).obj
        (chartSchemeAlgebra B S hS X A V) ⟶
      chartSchemeAlgebra B S hS X A V' :=
  Under.homMk (pushout.desc (chartSchemeAlgebraPullbackComparison B S hS X A h)
    (chartSchemeAlgebra B S hS X A V').hom
    (pullback_map_hom_comp_chartSchemeAlgebraPullbackComparison B S hS X A h))
    (pushout.inr_desc _ _ _)

/-- The algebra-level comparison is the map out of the pushout described by the inverse-image
comparison and the structure morphism. -/
theorem chartSchemeAlgebraBaseChangeHom_right :
    (chartSchemeAlgebraBaseChangeHom B S hS X A h).right =
      pushout.desc (chartSchemeAlgebraPullbackComparison B S hS X A h)
        (chartSchemeAlgebra B S hS X A V').hom
        (pullback_map_hom_comp_chartSchemeAlgebraPullbackComparison B S hS X A h) :=
  rfl

/-- **The algebra-level comparison restricts to the inverse-image comparison.**  Composed with
the canonical map from the inverse image into the algebra pullback it is
`AlgebraicGeometry.Space.chartSchemeAlgebraPullbackComparison`; together with
`AlgebraicGeometry.Space.chartSchemeAlgebraBaseChangeHom` being a map of algebras this
determines it uniquely, the algebra pullback being a pushout. -/
theorem algebraPullbackMap_comp_chartSchemeAlgebraBaseChangeHom :
    (Stacks.AffineAlgebraEquivalence.algebraPullbackMap (chartSchemeMap h)).app
          (chartSchemeAlgebra B S hS X A V) ≫
        (chartSchemeAlgebraBaseChangeHom B S hS X A h).right =
      chartSchemeAlgebraPullbackComparison B S hS X A h :=
  pushout.inl_desc _ _ _

/-! ### The comparison of the underlying modules -/

/-- **The module-level chart base-change comparison attached to the algebra-level one.**  The
pullback along `chartSchemeMap h` of the module underlying `A|_V` maps to the module underlying
`A|_{V'}`: the module underlying the algebra pullback *is* the module pullback, by
`Stacks.AlgebraPullbackQcoh.isIso_comparison`, and the algebra-level comparison is a map of
algebras, hence of underlying modules.

By `AlgebraicGeometry.Space.underlyingModule_chartSchemeAlgebra` the two modules are the chart
restrictions of the module underlying `A`, so this is a canonical morphism
`(chartSchemeMap h)^* (M|_V) ⟶ M|_{V'}`. -/
def chartSchemeModuleBaseChangeHom :
    (Scheme.Modules.pullback (chartSchemeMap h)).obj
        (chartSchemeAlgebra B S hS X A V).underlyingModule ⟶
      (chartSchemeAlgebra B S hS X A V').underlyingModule :=
  Stacks.ModuleStalkTensor.comparison (chartSchemeMap h) (chartSchemeAlgebra B S hS X A V) ≫
    Stacks.AlgebraPullbackQcoh.moduleMap (chartSchemeAlgebraBaseChangeHom B S hS X A h)

/-- **The inverse-image comparison on sections in the image of the unit** of the
inverse-image/direct-image adjunction on sheaves of commutative rings is the direct-image
comparison.  This is the triangle identity of that adjunction, read on sections. -/
theorem chartSchemeAlgebraPullbackComparison_app_unit (O : (chartScheme V).Opens)
    (a : (chartSchemeAlgebra B S hS X A V).right.obj.obj (op O)) :
    (chartSchemeAlgebraPullbackComparison B S hS X A h).hom.app
        (op ((Opens.map (chartSchemeMap h).base).obj O))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          (chartSchemeMap h).base).unit.app
        (chartSchemeAlgebra B S hS X A V).right).hom.app (op O) a) =
      (chartSchemeAlgebraPushforwardComparison B S hS X A h).hom.app (op O) a := by
  have h1 : ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
        (chartSchemeMap h).base).homEquiv _ _)
        (chartSchemeAlgebraPullbackComparison B S hS X A h) =
      chartSchemeAlgebraPushforwardComparison B S hS X A h := by
    rw [chartSchemeAlgebraPullbackComparison, Equiv.apply_symm_apply]
  have h2 := h1.symm.trans (Adjunction.homEquiv_unit
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (chartSchemeMap h).base)
    (chartSchemeAlgebra B S hS X A V).right _
    (chartSchemeAlgebraPullbackComparison B S hS X A h))
  exact (congrArg (fun φ => (φ.hom.app (op O)) a) h2).symm

/-- **The module-level comparison, on a section in the image of the unit of the module
pullback/direct-image adjunction, is the restriction map of `A`** along the morphism of étale
charts cut out by a Zariski open.

This is the computation that makes the comparison usable: such sections generate the pullback
locally, so the comparison is determined by it, and no sheafification has to be unwound.  The
three steps are `Stacks.AlgebraPullbackQcoh.comparison_app_moduleUnit_algebraPullbackMap` — the
comparison of Stacks 01SA is `Stacks.AffineAlgebraEquivalence.algebraPullbackMap` on unit-image
sections — then
`AlgebraicGeometry.Space.algebraPullbackMap_comp_chartSchemeAlgebraBaseChangeHom`, and then
`AlgebraicGeometry.Space.chartSchemeAlgebraPullbackComparison_app_unit`. -/
theorem chartSchemeModuleBaseChangeHom_app_unit (O : (chartScheme V).Opens)
    (a : (chartSchemeAlgebra B S hS X A V).right.obj.obj (op O)) :
    PresheafOfModules.Hom.app (chartSchemeModuleBaseChangeHom B S hS X A h).val
        (op ((Opens.map (chartSchemeMap h).base).obj O))
      (PresheafOfModules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction
          (chartSchemeMap h)).unit.app
        (chartSchemeAlgebra B S hS X A V).underlyingModule).val (op O) a) =
      A.right.obj.map ((openChartRestrictNatTrans B S hS X.1 h).app O).op a := by
  have e1 := Stacks.AlgebraPullbackQcoh.comparison_app_moduleUnit_algebraPullbackMap
    (chartSchemeMap h) (chartSchemeAlgebra B S hS X A V) O a
  have e2 := congrArg (fun φ => (φ.hom.app
      (op ((Opens.map (chartSchemeMap h).base).obj O)))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
          (chartSchemeMap h).base).unit.app
        (chartSchemeAlgebra B S hS X A V).right).hom.app (op O) a))
    (algebraPullbackMap_comp_chartSchemeAlgebraBaseChangeHom B S hS X A h)
  have e3 := chartSchemeAlgebraPullbackComparison_app_unit B S hS X A h O a
  change (chartSchemeAlgebraBaseChangeHom B S hS X A h).right.hom.app
      (op ((Opens.map (chartSchemeMap h).base).obj O))
      (PresheafOfModules.Hom.app (Stacks.ModuleStalkTensor.comparison (chartSchemeMap h)
          (chartSchemeAlgebra B S hS X A V)).val
        (op ((Opens.map (chartSchemeMap h).base).obj O))
        (PresheafOfModules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction
            (chartSchemeMap h)).unit.app
          (chartSchemeAlgebra B S hS X A V).underlyingModule).val (op O) a)) = _
  rw [e1]
  exact e2.trans e3

/-- **The algebra-level comparison is invertible as soon as the module-level one is.**

A morphism of algebra sheaves whose underlying morphism of modules is invertible is invertible
(`Stacks.AlgebraPullbackQcoh.isIso_of_isIso_moduleMap`), and the comparison of Stacks 01SA
identifying the module underlying the algebra pullback with the module pullback is invertible
unconditionally (`Stacks.AlgebraPullbackQcoh.isIso_comparison`), so the two invertibility
questions are the same one. -/
theorem isIso_chartSchemeAlgebraBaseChangeHom_of_isIso_module
    (hm : IsIso (chartSchemeModuleBaseChangeHom B S hS X A h)) :
    IsIso (chartSchemeAlgebraBaseChangeHom B S hS X A h) := by
  have : IsIso (Stacks.ModuleStalkTensor.comparison (chartSchemeMap h)
      (chartSchemeAlgebra B S hS X A V)) := Stacks.AlgebraPullbackQcoh.isIso_comparison _ _
  have : IsIso (Stacks.ModuleStalkTensor.comparison (chartSchemeMap h)
        (chartSchemeAlgebra B S hS X A V) ≫
      Stacks.AlgebraPullbackQcoh.moduleMap
        (chartSchemeAlgebraBaseChangeHom B S hS X A h)) := hm
  exact Stacks.AlgebraPullbackQcoh.isIso_of_isIso_moduleMap _
    (IsIso.of_isIso_comp_left (Stacks.ModuleStalkTensor.comparison (chartSchemeMap h)
      (chartSchemeAlgebra B S hS X A V)) _)

end AlgebraicGeometry.Space

end
