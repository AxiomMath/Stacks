module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LocallyQuasiIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeWeakSerre
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleSheafifiedBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleSheafifiedPullbackUnivLE
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageFlatBaseChangeDegrees

/-!
# Colimits of étale sheaves of modules with the flat base change property

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. **Stacks 0762** attaches to a
module on `𝒳` the *flat base change property*: the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 0761** is an isomorphism for every arrow
`φ : x ⟶ y` of `𝒳` lying over a flat morphism of schemes `a : U ⟶ V`.

`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeColimits.lean` proves part (4)
of **Stacks 0764** — that the modules with the property admit colimits agreeing with the
colimits of the ambient category — with the ambient category the *presheaves* of modules, and
with `a_{small}^*` read as the inverse image of presheaves of modules. The source's ambient
category is `Mod(𝒳_étale, 𝒪_𝒳)`, the étale *sheaves* of `𝒪_𝒳`-modules, and its `a_{small}^*` is
the inverse image of sheaves on the small étale sites. This file states and proves part (4) as
the source states it, beside that presheaf reading rather than in place of it: nothing in
`FlatBaseChangeColimits.lean` is changed, and the two readings are genuinely different
statements, not a weaker and a stronger form of one statement — see the implementation notes.

The argument is the source's. The comparison map is natural in the module, and both of the
functors it runs between preserve colimits: the inverse image of sheaves of modules is a left
adjoint, by `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction`, and the
restriction of étale sheaves of modules to a small étale site preserves colimits, by
`AlgebraicGeometry.Stack.preservesColimitsOfShape_restrictSheafToSmallEtale`. A natural
transformation of colimit-preserving functors which is an isomorphism on a diagram is an
isomorphism at its colimit.

## Main definitions

* `AlgebraicGeometry.Stack.restrictSheafPullbackComparison`: the comparison map `c_φ` of
  **Stacks 0761** for an étale sheaf of `𝒪_𝒳`-modules, with `a_{small}^*` the inverse image of
  sheaves of modules on the small étale sites — the source's comparison map.
* `AlgebraicGeometry.Stack.restrictSheafPullbackComparisonNatTrans`: the same, as a natural
  transformation in the sheaf.
* `AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheafUnivLE`: **Stacks 0762** for an étale
  sheaf of `𝒪_𝒳`-modules, read with that comparison map.

## Main results

* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_colimit` and
  `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_isColimit`: **Stacks 0764** part (4)
  as the source states it — a colimit of étale sheaves of `𝒪_𝒳`-modules with the flat base
  change property has the flat base change property.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_cokernel`,
  `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_initial` and
  `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_shortExact`: three of the four
  clauses of **Stacks 0764** part (2) as the source states them, not registered separately —
  the closure under cokernels, the zero object, and the closure under extensions asked for by
  **Stacks 0754**. The first two are the cases of part (4) at the walking parallel pair and at
  the empty diagram; the third is the diagram argument of
  `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_of_shortExact`. The fourth
  clause, kernels, and the whole of part (2) are in `FlatBaseChangeSheafWeakSerre.lean`.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheafUnivLE_of_iso`: the property depends only
  on the isomorphism class, which is the strict fullness condition (2) of **Stacks 0754**.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheafUnivLE_of_hasFlatBaseChangePropertyUnivLE`
  states that the presheaf reading of the property implies the sheaf reading, for a module that
  is an étale sheaf. The converse is not available and is not expected to hold; see the
  implementation notes.

## Implementation notes

**Why this is a second property and not a restatement.** The comparison map of
`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` is
`AlgebraicGeometry.Stack.restrictModulePullbackComparison`, whose source is the inverse image of
*presheaves* of modules along the map `a_{small}^♯` of **Stacks 06WC**. The source's
`a_{small}^*` is the inverse image of *sheaves*, which is that presheaf inverse image followed by
sheafification — the functor
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison`, identified with
`SheafOfModules.pullback` along the morphism of ringed sites `ε_a` by
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`. So the two comparison maps are
related by `c_φ = η ≫ c_φ^{sh}` with `η` the sheafification unit: the sheaf comparison is the
adjunct of the presheaf one, which is what
`AlgebraicGeometry.Stack.restrictSheafPullbackComparison` is defined as. Hence the presheaf
reading implies the sheaf reading, the adjunct of an isomorphism into a sheaf being an
isomorphism; the converse would ask the presheaf inverse image of `F|_{V_ét}` to be a sheaf
already, which no statement here supplies. The presheaf reading is therefore the *stronger* of
the two on an étale sheaf, so neither the hypothesis nor the conclusion of the part (4)
statements of `FlatBaseChangeColimits.lean` is the source's, and the two are not comparable as
closure statements. That is why both are tagged, each with a clause string naming its ambient
category.

**Why this is not in `FlatBaseChangeColimits.lean`.** The coordinate of the argument that is not
formal is that the restriction of étale sheaves of modules to a small étale site preserves
colimits, which is
`AlgebraicGeometry.Stack.preservesColimitsOfShape_restrictSheafToSmallEtale` of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LocallyQuasicoherentAbelian.lean`; that
module imports `FlatBaseChangeColimits.lean`, so the statements below cannot be added there
without a cycle. They are placed in the first module that can see both that instance and
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison`.

**The colimit-preservation hypotheses.** The shape `J` is gated by
`CategoryTheory.Limits.HasColimitsOfShape J AddCommGrpCat.{m}`, as in the presheaf file, which is
what Mathlib asks for colimits of modules with sections in `u`; the étale sheafification
instances are the ones
`AlgebraicGeometry.Stack.preservesColimitsOfShape_restrictSheafToSmallEtale` asks for, and they
are supplied for the associated étale topology by
`AlgebraicGeometry.Stack.hasSheafify_etaleAssociatedTopology` and
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_etaleAssociatedTopology`.

**The universe of the sections.** Module sections live in any universe `m` with
`UnivLE.{u, m}` above the universe `u` of the schemes: the comparison map is built from
`AlgebraicGeometry.Stack.restrictModulePullbackComparisonUnivLE` and the inverse image of sheaves
of modules from `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonUnivLE`, which at `m = u` are
the objects of the same names without the suffix. The case `m = u + 1` is the one the higher
direct images of **Stacks 0765** need.

The extension clause and the statement it is proved from carry those two sheafification
instances for the associated étale topology as *instance arguments* rather than introducing them
inside a proof, because `CategoryTheory.ShortComplex.ShortExact` and the abelian structure on
the étale sheaves of modules are needed already to state them. They are not restrictions: both
are supplied unconditionally, for any `B`, `S`, `p`, by the two theorems named above. Everything
else in this file introduces them with `have` and so does not carry them.

`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeWeakSerre.lean` is imported for
the additivity of the inverse image of presheaves of modules below an arrow,
`AlgebraicGeometry.Stack.additive_pullback_smallEtaleStructureComparison_univLE`, and
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/LocallyQuasiIso.lean` for
`PresheafOfModules.additive_sheafification`; together with additivity of the forgetful functor
these make the inverse image of sheaves of modules additive, which the diagram lemmas consume.
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/HigherDirectImageFlatBaseChangeDegrees.lean`
is imported for the naturality in the module of the comparison map of **Stacks 06WC** at the
section universe `m`, `AlgebraicGeometry.Stack.restrictModulePullbackComparisonUnivLE_naturality`.

**Where the other parts of Stacks 0764 are.** This file proves part (4), registered both as a
closure statement and as the full subcategory `flatBaseChangeEtaleModules` having the colimits of
`Mod(𝒳_étale, 𝒪_𝒳)`, together with three of the four clauses of part (2): the cokernel clause and
the zero object are cases of part (4), and the extension clause reruns the presheaf diagram
argument with the inverse image of sheaves. Those clauses are not registered on their own. The
kernel clause needs left exactness of `a_{small}^*` along a flat morphism of schemes, and the
whole of part (2), as a weak Serre subcategory in the sense of **Stacks 0754**, is
`AlgebraicGeometry.Stack.isWeakSerreClass_flatBaseChangeEtaleModules` of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeSheafWeakSerre.lean`. Part (1)
is in `FlatBaseChangeSheafInverseImage.lean`, part (3) in `FlatBaseChangeSheafSmoothLocal.lean`,
part (5) in `FlatBaseChangeSheafTensor.lean` and part (6) in `FlatBaseChangeSheafInternalHom.lean`,
all in the same directory and all in the source's ambient category.

## References

* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w m j jv

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  [UnivLE.{u, m}]

section Comparison

variable {x y : 𝒳} (φ : x ⟶ y)

/-- **Stacks 0761 for an étale sheaf of modules.** The comparison map
`c_φ^{sh} : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` below an arrow `φ : x ⟶ y` of `𝒳` lying over a
morphism of schemes `a : U ⟶ V`, with `a_{small}^*` the inverse image of *sheaves* of modules on
the small étale sites, which is the reading the source uses.

It is the adjunct, across the sheafification adjunction of the small étale site of the scheme
below `x`, of the comparison map
`AlgebraicGeometry.Stack.restrictModulePullbackComparison` of the underlying presheaf of
modules: the target `F|_{U_ét}` is a sheaf, and `a_{small}^*` is the presheaf inverse image
followed by sheafification. -/
noncomputable def restrictSheafPullbackComparison
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    (sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ).obj
        ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp y).obj F) ⟶
      (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj F :=
  ((smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x).homEquiv _
    ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj F)).symm
      (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F.val)

/-- **Stacks 0761 for an étale sheaf of modules.** The comparison map `c_φ^{sh}` is natural in
the sheaf.

The square is the square of
`AlgebraicGeometry.Stack.restrictModulePullbackComparison_naturality` for the underlying
presheaves, carried across the sheafification adjunction of the small étale site below `x`:
naturality of the adjunction isomorphism on the left turns the left-hand composite into an
adjunct, naturality on the right does the same for the right-hand composite, and the two
adjuncts agree by that presheaf square. -/
theorem restrictSheafPullbackComparison_naturality
    {F F' : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} (α : F ⟶ F') :
    (sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ).map
        ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp y).map α) ≫
          restrictSheafPullbackComparison B E h S hS p hp φ F' =
      restrictSheafPullbackComparison B E h S hS p hp φ F ≫
        (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).map α := by
  have hleft :=
    (smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x).homEquiv_naturality_left_symm
      (Y := (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj F')
      ((PresheafOfModules.pullback.{m}
        (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B))).map
        ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) y).map α.val))
      (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F'.val)
  have hright :=
    (smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x).homEquiv_naturality_right_symm
      (Y := (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj F)
      (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F.val)
      ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).map α)
  have h₃ : (PresheafOfModules.pullback.{m}
        (smallEtaleStructureComparison B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B))).map
          ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp (etaleTopology B)
            (etaleTopology_le_topology B) y).map α.val) ≫
        (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) F'.val :
            _ ⟶ (SheafOfModules.forget _).obj
              ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj F')) =
      (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F.val :
          _ ⟶ (SheafOfModules.forget _).obj
            ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj F)) ≫
        (SheafOfModules.forget _).map
          ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).map α) :=
    restrictModulePullbackComparisonUnivLE_naturality B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ α.val
  exact hleft.symm.trans
    ((congrArg ((smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x).homEquiv _
      ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj F')).symm h₃).trans hright)

/-- **Stacks 0761 for an étale sheaf of modules.** The comparison map `c_φ^{sh}` below an arrow
`φ : x ⟶ y` of `𝒳`, as a natural transformation from the restriction at `y` followed by the
inverse image `a_{small}^*` of sheaves of modules to the restriction at `x`. -/
noncomputable def restrictSheafPullbackComparisonNatTrans :
    restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp y ⋙
        sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B) φ ⟶
      restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x where
  app F := restrictSheafPullbackComparison B E h S hS p hp φ F
  naturality _ _ α := restrictSheafPullbackComparison_naturality B E h S hS p hp φ α

end Comparison

/-- **Stacks 0762 for an étale sheaf of modules.** An étale sheaf of `𝒪_𝒳`-modules *has the flat
base change property* when the comparison map `c_φ^{sh}` of **Stacks 0761** — taken with
`a_{small}^*` the inverse image of sheaves of modules, as the source takes it — is an isomorphism
for every arrow `φ` of `𝒳` lying over a flat morphism of schemes.

This is the property read in the source's ambient category `Mod(𝒳_étale, 𝒪_𝒳)`.
`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty` is the same definition with the inverse image
of presheaves of modules, which on an étale sheaf is strictly the stronger demand; the
implementation notes of this file say why. -/
noncomputable abbrev HasFlatBaseChangePropertySheafUnivLE
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) : Prop :=
  ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ F)

/-- The flat base change property of the underlying presheaf of modules implies the flat base
change property of an étale sheaf of modules in the source's reading.

The sheaf comparison map is the adjunct of the presheaf one across the sheafification
adjunction, so it is `L(c_φ)` followed by the counit; the counit of a sheafification adjunction
is an isomorphism, the subcategory of sheaves being reflective. The converse would ask the
presheaf inverse image of `F|_{V_ét}` to be a sheaf already and is not available here. -/
theorem hasFlatBaseChangePropertySheafUnivLE_of_hasFlatBaseChangePropertyUnivLE
    (F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))
    (hF : HasFlatBaseChangePropertyUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F.val) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp F := by
  intro x y φ hflat
  have hpre : IsIso (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
    (etaleTopology_le_topology B) F.val) := hF φ hflat
  rw [show restrictSheafPullbackComparison B E h S hS p hp φ F =
      (smallEtaleSheafificationUnivLE B E h S hS p x).map
        (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
          (etaleTopology_le_topology B) F.val) ≫
        (smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x).counit.app
          ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj F) from
    Adjunction.homEquiv_counit _ _ _ _]
  have hcounit : IsIso ((smallEtaleSheafificationAdjunctionUnivLE B E h S hS p x).counit.app
      ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).obj F)) :=
    NatIso.isIso_app_of_isIso _ _
  have hmap : IsIso ((smallEtaleSheafificationUnivLE B E h S hS p x).map
      (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F.val)) :=
    ((smallEtaleSheafificationUnivLE B E h S hS p x).mapIso
      (asIso (restrictModulePullbackComparisonUnivLE B E h S hS p hp φ (etaleTopology B)
        (etaleTopology_le_topology B) F.val))).isIso_hom
  exact IsIso.comp_isIso' hmap hcounit

section Colimits

variable {J : Type j} [Category.{jv} J] [HasColimitsOfShape J AddCommGrpCat.{m}]

/-- **Stacks 0764, part (4), as the source states it.** The colimit of a diagram of étale sheaves
of `𝒪_𝒳`-modules each having the flat base change property of **Stacks 0762** again has the flat
base change property, the colimit being the colimit of `Mod(𝒳_étale, 𝒪_𝒳)`.

For an arrow `φ` of `𝒳` lying over a flat morphism of schemes, `c_φ^{sh}` is the component of a
natural transformation from `F ↦ a_{small}^*(F|_{V_ét})` to `F ↦ F|_{U_ét}`. Both functors
preserve colimits — the first because the inverse image of sheaves of modules is a left adjoint,
by `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction`, the second by
`AlgebraicGeometry.Stack.preservesColimitsOfShape_restrictSheafToSmallEtale` — and the component
at a colimit of a natural transformation of colimit-preserving functors is an isomorphism as
soon as every component on the diagram is. -/
@[stacks 0764 "part (4), with the ambient category the étale sheaves of modules, as the source \
  states it -- and so with a_small^* the inverse image of sheaves of modules, not the inverse \
  image of presheaves of modules used by the part (4) registrations of FlatBaseChangeColimits: \
  a colimit of étale sheaves of modules with the flat base change property has the flat base \
  change property"]
theorem hasFlatBaseChangePropertySheaf_colimit
    (K : J ⥤ SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) [HasColimit K]
    (hK : ∀ i, HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp (K.obj i)) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp (colimit K) := by
  intro _ _ φ hflat
  have := hasSheafify_etaleAssociatedTopology_univLE.{u, _, _, m} B S hS p hp
  have := wEqualsLocallyBijective_etaleAssociatedTopology_univLE.{u, _, _, m} B S hS p hp
  have : PreservesColimitsOfShape J
      (sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ) :=
    ((sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).leftAdjoint_preservesColimits).preservesColimitsOfShape
  exact NatTrans.isIso_app_colimit
    (restrictSheafPullbackComparisonNatTrans B E h S hS p hp φ) K fun i => hK i φ hflat

/-- The comparison map `c_φ^{sh}` is an isomorphism at one of two isomorphic sheaves if it is at
the other. -/
private theorem isIso_restrictSheafPullbackComparison_of_iso
    {x y : 𝒳} (φ : x ⟶ y)
    {F F' : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} (e : F ≅ F')
    (hF : IsIso (restrictSheafPullbackComparison B E h S hS p hp φ F)) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ F') := by
  have : IsIso ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).map e.hom) :=
    ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x).mapIso e).isIso_hom
  have : IsIso ((sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).map
      ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp y).map e.hom)) :=
    ((sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).mapIso
      ((restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp y).mapIso e)).isIso_hom
  exact IsIso.of_isIso_fac_left
    (restrictSheafPullbackComparison_naturality B E h S hS p hp φ e.hom)

/-- **Stacks 0764, part (4), as the source states it**, in the form for an arbitrary colimit
cocone: the vertex of a colimit cocone on a diagram of étale sheaves of `𝒪_𝒳`-modules with the
flat base change property has the flat base change property.

This is `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_colimit` transported along the
canonical isomorphism of the vertex with the chosen colimit. -/
@[stacks 0764 "part (4), with the ambient category the étale sheaves of modules, as the source \
  states it -- and so with a_small^* the inverse image of sheaves of modules, not the inverse \
  image of presheaves of modules used by the part (4) registrations of FlatBaseChangeColimits: \
  the vertex of a colimit cocone on a diagram of étale sheaves of modules with the flat base \
  change property has the flat base change property"]
theorem hasFlatBaseChangePropertySheaf_of_isColimit
    {K : J ⥤ SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} {c : Cocone K} (hc : IsColimit c)
    (hK : ∀ i, HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp (K.obj i)) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp c.pt := by
  have hcol : HasColimit K := ⟨c, hc⟩
  intro x y φ hflat
  exact isIso_restrictSheafPullbackComparison_of_iso B E h S hS p hp φ
    (hc.coconePointUniqueUpToIso (colimit.isColimit K)).symm
    (hasFlatBaseChangePropertySheaf_colimit B E h S hS p hp K hK φ hflat)

end Colimits

/-- The flat base change property of an étale sheaf of modules, in the source's reading, depends
only on the isomorphism class of the sheaf.

The two comparison maps sit in the naturality square of
`AlgebraicGeometry.Stack.restrictSheafPullbackComparison_naturality` for the isomorphism, whose
other two sides are its images under the restriction at the target followed by `a_{small}^*` and
under the restriction at the source; both are isomorphisms. -/
theorem hasFlatBaseChangePropertySheafUnivLE_of_iso
    {F F' : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} (e : F ≅ F')
    (hF : HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp F) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp F' :=
  fun φ hflat => isIso_restrictSheafPullbackComparison_of_iso B E h S hS p hp φ e (hF φ hflat)

section WeakSerreClauses

variable [HasColimitsOfShape WalkingParallelPair AddCommGrpCat.{m}]

/-- **Stacks 0764, part (2), as the source states it, the cokernel clause.** The cokernel of a
morphism of étale sheaves of `𝒪_𝒳`-modules with the flat base change property of **Stacks 0762**
has the flat base change property. This is the closure under cokernels asked for by
**Stacks 0754**, with the cokernel the cokernel of `Mod(𝒳_étale, 𝒪_𝒳)`.

A cokernel is a colimit indexed by the walking parallel pair, whose two values are the source
and the target of the morphism, so this is a case of
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_colimit`. -/
theorem hasFlatBaseChangePropertySheaf_cokernel
    {F G : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} (α : F ⟶ G) [HasCokernel α]
    (hF : HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp F)
    (hG : HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp G) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp (cokernel α) :=
  hasFlatBaseChangePropertySheaf_colimit B E h S hS p hp (parallelPair α 0) (by
    rintro (_ | _)
    · exact hF
    · exact hG)

end WeakSerreClauses

/-- **Stacks 0764, part (2), as the source states it, the zero object clause.** An initial étale
sheaf of `𝒪_𝒳`-modules — equivalently, a zero object — has the flat base change property of
**Stacks 0762**. This is the containment of a zero object asked for by **Stacks 0754**.

An initial object is the colimit of the empty diagram, so this is the case of
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_isColimit` in which the hypothesis on
the diagram is vacuous. -/
theorem hasFlatBaseChangePropertySheaf_initial
    {F : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} (hF : IsInitial F) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp F :=
  hasFlatBaseChangePropertySheaf_of_isColimit B E h S hS p hp hF (fun i => i.as.elim)

section Extension

variable [HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{m}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{m}]
  {x y : 𝒳} (φ : x ⟶ y)

/-- The source `F ↦ a_{small}^*(F|_{V_ét})` of the comparison map `c_φ^{sh}` below an arrow
`φ : x ⟶ y` of `𝒳`, as a functor of the étale sheaf: restriction to the small étale site of the
scheme below `y`, followed by the inverse image of *sheaves* of modules below `φ`.

This is the domain of `AlgebraicGeometry.Stack.restrictSheafPullbackComparisonNatTrans`. -/
noncomputable abbrev restrictSheafPullbackComparisonSource :
    SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)) ⥤
      SheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)) :=
  restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp y ⋙
    sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ

/-- The restriction of étale sheaves of modules to a small étale site is additive: on underlying
presheaves of modules it is `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFunctor`, which is
additive, and addition of morphisms of sheaves of modules is addition of the underlying
morphisms of presheaves. -/
instance additive_restrictSheafToSmallEtale (z : 𝒳) :
    (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp z).Additive where
  map_add := SheafOfModules.hom_ext
    ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) z).map_add)

/-- The inverse image `a_{small}^*` of sheaves of modules below an arrow of `𝒳` is additive: it
is the forgetful functor to presheaves of modules, the inverse image of presheaves of modules,
and sheafification, each of which is additive. -/
instance additive_sheafifiedPullbackComparisonUnivLE :
    (sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).Additive := by
  unfold sheafifiedPullbackComparisonUnivLE
  infer_instance

/-- The source of `c_φ^{sh}` is right exact: the inverse image of sheaves of modules is a left
adjoint, by `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction`, and the restriction
of étale sheaves of modules to a small étale site is right exact. -/
instance preservesFiniteColimits_restrictSheafPullbackComparisonSource :
    PreservesFiniteColimits
      (restrictSheafPullbackComparisonSource.{u, v, w, m} B E h S hS p hp φ) :=
  letI : PreservesColimitsOfSize.{0, 0}
      (sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ) :=
    (sheafifiedPullbackComparisonAdjunctionUnivLE B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) φ).leftAdjoint_preservesColimits
  letI : PreservesFiniteColimits
      (sheafifiedPullbackComparisonUnivLE B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ) := ⟨fun _ _ _ => inferInstance⟩
  comp_preservesFiniteColimits _ _

/-- The comparison map `c_φ^{sh}` at the middle term of a short exact sequence of étale sheaves
of modules is an isomorphism as soon as it is one at the two outer terms.

The source of `c_φ^{sh}` is right exact, so the short exact sequence is carried to an exact
complex whose right-hand map is an epimorphism; the target is exact, so it is carried to a short
exact sequence. The resulting map of three-term complexes is a monomorphism and an epimorphism
at the outer terms, so the two three-term diagram lemmas of an abelian category make it a
monomorphism and an epimorphism at the middle term. This is the argument of
`AlgebraicGeometry.Stack.isIso_restrictModulePullbackComparison_of_shortExact`, rerun with the
inverse image of sheaves of modules in place of the inverse image of presheaves. -/
theorem isIso_restrictSheafPullbackComparison_of_shortExact
    {T : ShortComplex (SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))} (hT : T.ShortExact)
    (h₁ : IsIso (restrictSheafPullbackComparison B E h S hS p hp φ T.X₁))
    (h₃ : IsIso (restrictSheafPullbackComparison B E h S hS p hp φ T.X₃)) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ T.X₂) := by
  let Φ := restrictSheafPullbackComparisonSource.{u, v, w, m} B E h S hS p hp φ
  let Ψ := restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp x
  let η := restrictSheafPullbackComparisonNatTrans B E h S hS p hp φ
  obtain ⟨hΦex, hΦepi⟩ :=
    (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi Φ).mp inferInstance T hT
  obtain ⟨hΨex, hΨmono⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono Ψ).mp inferInstance T hT
  have : IsIso ((T.mapNatTrans η).τ₁) := h₁
  have : IsIso ((T.mapNatTrans η).τ₃) := h₃
  have hm : Mono (η.app T.X₂) :=
    ShortComplex.mono_of_mono_of_mono_of_mono (T.mapNatTrans η) hΦex hΨmono
      inferInstance inferInstance
  have he : Epi (η.app T.X₂) :=
    ShortComplex.epi_of_epi_of_epi_of_epi (T.mapNatTrans η) hΨex hΦepi
      (IsIso.epi_of_iso _) (IsIso.epi_of_iso _)
  exact isIso_of_mono_of_epi (η.app T.X₂)

end Extension

section ExtensionClause

variable [HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{m}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **Stacks 0764, part (2), as the source states it, the extension clause.** In a short exact
sequence of étale sheaves of `𝒪_𝒳`-modules whose outer terms have the flat base change property
of **Stacks 0762**, the middle term has the flat base change property. This is the closure under
extensions asked for by **Stacks 0754**, with the sequence exact in `Mod(𝒳_étale, 𝒪_𝒳)`.

At each arrow lying over a flat morphism of schemes this is
`AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_of_shortExact`. -/
theorem hasFlatBaseChangePropertySheaf_of_shortExact
    {T : ShortComplex (SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)))} (hT : T.ShortExact)
    (h₁ : HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp T.X₁)
    (h₃ : HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp T.X₃) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp T.X₂ := fun φ hflat =>
  isIso_restrictSheafPullbackComparison_of_shortExact B E h S hS p hp φ hT
    (h₁ φ hflat) (h₃ φ hflat)

end ExtensionClause

section Subcategory

/-- The full subcategory of `Mod(𝒳_étale, 𝒪_𝒳)` of the étale sheaves of `𝒪_𝒳`-modules with the
flat base change property of **Stacks 0762**, as an object property. This is the subcategory
**Stacks 0764** parts (2) and (4) are about, in the source's ambient category. -/
abbrev flatBaseChangeEtaleModules :
    ObjectProperty (SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :=
  fun F => HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp F

/-- The flat base change property of an étale sheaf of modules depends only on its isomorphism
class, by `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheafUnivLE_of_iso`. -/
instance isClosedUnderIsomorphisms_flatBaseChangeEtaleModules :
    ObjectProperty.IsClosedUnderIsomorphisms
      (flatBaseChangeEtaleModules.{u, v, w} B E h S hS p hp) where
  of_iso e hF := hasFlatBaseChangePropertySheafUnivLE_of_iso B E h S hS p hp e hF

variable {J : Type j} [Category.{jv} J] [HasColimitsOfShape J AddCommGrpCat.{m}]

/-- The étale sheaves of modules with the flat base change property are closed under colimits of
shape `J` in `Mod(𝒳_étale, 𝒪_𝒳)`, by
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_isColimit`. -/
instance isClosedUnderColimitsOfShape_flatBaseChangeEtaleModules :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (flatBaseChangeEtaleModules.{u, v, w} B E h S hS p hp) J where
  colimitsOfShape_le _ := by
    rintro ⟨hc⟩
    exact hasFlatBaseChangePropertySheaf_of_isColimit B E h S hS p hp hc.isColimit
      hc.prop_diag_obj

/-- **Stacks 0764, part (4), as the source states it**: the category of étale sheaves of
`𝒪_𝒳`-modules with the flat base change property has the colimits that `Mod(𝒳_étale, 𝒪_𝒳)`
has; those colimits exist, the étale sheafification of abelian presheaves on `𝒳` being
available unconditionally. -/
@[stacks 0764 "part (4), in the source's ambient category Mod(X_etale, O_X): the full \
  subcategory of etale sheaves of modules with the flat base change property has colimits"]
theorem hasColimitsOfShape_flatBaseChangeEtaleModules :
    HasColimitsOfShape J (flatBaseChangeEtaleModules.{u, v, w} B E h S hS p hp).FullSubcategory :=
  have := hasSheafify_etaleAssociatedTopology_univLE.{u, _, _, m} B S hS p hp
  have := wEqualsLocallyBijective_etaleAssociatedTopology_univLE.{u, _, _, m} B S hS p hp
  have : HasColimitsOfShape J (PresheafOfModules.{m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) :=
    inferInstance
  have : HasColimitsOfShape J (SheafOfModules.{m} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B))) := inferInstance
  inferInstance

/-- **Stacks 0764, part (4), as the source states it**: the colimits of étale sheaves of
`𝒪_𝒳`-modules with the flat base change property agree with the colimits of
`Mod(𝒳_étale, 𝒪_𝒳)`, the inclusion preserving them. -/
@[stacks 0764 "part (4), in the source's ambient category Mod(X_etale, O_X): the colimits of \
  the subcategory agree with the colimits in Mod(X_etale, O_X)"]
theorem preservesColimitsOfShape_flatBaseChangeEtaleModules_ι :
    PreservesColimitsOfShape J (flatBaseChangeEtaleModules.{u, v, w} B E h S hS p hp).ι :=
  have := hasSheafify_etaleAssociatedTopology_univLE.{u, _, _, m} B S hS p hp
  have := wEqualsLocallyBijective_etaleAssociatedTopology_univLE.{u, _, _, m} B S hS p hp
  have : HasColimitsOfShape J (PresheafOfModules.{m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) :=
    inferInstance
  have : HasColimitsOfShape J (SheafOfModules.{m} (ringStructureSheafCore B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B))) := inferInstance
  inferInstance

end Subcategory

end AlgebraicGeometry.Stack

end
