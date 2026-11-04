module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeNaturality

/-!
# Colimits of modules with the flat base change property (Stacks 0764, parts (2) and (4))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. **Stacks 0762** attaches to a
presheaf of `𝒪_𝒳`-modules the *flat base change property*: the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 0761** is an isomorphism for every arrow
`φ : x ⟶ y` of `𝒳` lying over a flat morphism of schemes `a : U ⟶ V`.

**Stacks 0764** part (4) says that the modules with the property admit colimits which agree with
the colimits of the ambient category of modules, and part (2) that they form a weak Serre
subcategory (**Stacks 0754**), which among other things asks for closure under cokernels and for
a zero object. This file proves both at the level of *presheaves* of modules. The source's
argument is exactly the one used here: `c_φ` is natural in the module, its source
`F ↦ a_{small}^*(F|_{V_ét})` and its target `F ↦ F|_{U_ét}` both commute with colimits — the
first because `a_{small}^*` is a left adjoint, the second because restriction to the small étale
site is restriction along a functor followed by a change of scalars — and a natural
transformation of colimit-preserving functors which is an isomorphism on a diagram is an
isomorphism on its colimit.

The ambient category of the source is `Mod(𝒳_étale, 𝒪_𝒳)`, the étale *sheaves* of
`𝒪_𝒳`-modules, whose colimits are the sheafifications of the colimits of presheaves. Passing
from the statements below to the source's would need restriction to the small étale site to
commute with étale sheafification, which is not available here; the part keys of the tags record
that the ambient category is the presheaves of modules.

## Main definitions

* `AlgebraicGeometry.Stack.flatBaseChangeModulePresheaves`: the full subcategory of the
  presheaves of `𝒪_𝒳`-modules with the flat base change property of **Stacks 0762**, as an
  object property.

## Main results

* `CategoryTheory.NatTrans.isIso_app_colimit`: a natural transformation between functors which
  preserve colimits of shape `J`, and which is an isomorphism at each object of a diagram of
  that shape, is an isomorphism at the colimit of the diagram.
* `PresheafOfModules.preservesColimitsOfShape_restrictScalars_of_ringUniverse` and
  `PresheafOfModules.preservesColimitsOfShape_pushforward₀`: change of scalars and restriction
  along a functor preserve colimits of presheaves of modules.
* `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_of_isColimit` and
  `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_colimit`: **Stacks 0764** part (4), for
  presheaves of modules — a colimit of presheaves of modules with the flat base change property
  has the flat base change property.
* `AlgebraicGeometry.Stack.isClosedUnderColimitsOfShape_flatBaseChangeModulePresheaves`:
  **Stacks 0764** part (4), for presheaves of modules — the subcategory is closed under
  colimits, so by Mathlib's instances it has colimits and they agree with those of the ambient
  category.
* `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_cokernel`: **Stacks 0764** part (2), the
  closure under cokernels asked for by **Stacks 0754**, for presheaves of modules.
* `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_initial`: **Stacks 0764** part (2), the
  zero object asked for by **Stacks 0754**, for presheaves of modules.

## Implementation notes

The comparison map `c_φ` exists only for a presheaf of modules whose sections lie in the
universe `u` of the schemes, because it is the mate of the direct-image comparison under an
adjunction supplied by essential smallness of the small étale site in that universe; see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleModuleComparison.lean`. All
module sections below therefore live in `u`, and the shapes `J` of the colimits are gated by
`CategoryTheory.Limits.HasColimitsOfShape J AddCommGrpCat.{u}`, which is the hypothesis under
which Mathlib provides colimits of presheaves of modules with sections in `u`. No smallness of
`𝒳` is needed and the topology `τ` is arbitrary among those coarser than the fppf one, as the
flat base change property itself is.

Restriction to the small étale site is packaged as the functor
`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFunctor`, and `c_φ` as the natural
transformation `AlgebraicGeometry.Stack.restrictModulePullbackComparisonNatTrans`, both from
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeNaturality.lean`; nothing
about the comparison map is reproved here. That the inverse image `a_{small}^*` of presheaves of
modules is a left adjoint is
`AlgebraicGeometry.Stack.isRightAdjoint_pushforward_smallEtaleStructureComparison` together with
`PresheafOfModules.pullbackPushforwardAdjunction`.

Change of scalars and restriction along a functor are shown to preserve colimits through
`PresheafOfModules.evaluationJointlyReflectsColimits`: a cocone of presheaves of modules is a
colimit as soon as it is one after evaluation at every object, and after evaluation the two
functors become, respectively, the change of scalars of modules over a ring — a left adjoint to
coextension of scalars, whence colimit-preserving — and a reindexing, which changes nothing.
The restriction of the module universe to the universe of the rings is what makes the first of
these a left adjoint, coextension of scalars raising the universe otherwise.

The zero object is obtained as the initial object, that is as the colimit of the empty diagram,
rather than by a separate argument: a presheaf of modules is initial exactly when it is a zero
object.

## References

* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w j jv

namespace CategoryTheory.NatTrans

/-- A natural transformation `η : Φ ⟶ Ψ` between functors which preserve colimits of shape `J`
is an isomorphism at the colimit of a diagram `K : J ⥤ C` as soon as it is an isomorphism at
each `K i`.

Both `Φ` and `Ψ` turn the colimit cocone of `K` into a colimit cocone, and `η` whiskered with
`K` is an isomorphism, so precomposing the image under `Ψ` with it gives a second colimit cocone
on `K ⋙ Φ`. The component of `η` at the colimit is the comparison of the two, by naturality. -/
theorem isIso_app_colimit {C : Type*} [Category C] {D : Type*} [Category D]
    {J : Type*} [Category J] {Φ Ψ : C ⥤ D} (η : Φ ⟶ Ψ) (K : J ⥤ C) [HasColimit K]
    [PreservesColimitsOfShape J Φ] [PreservesColimitsOfShape J Ψ]
    (hη : ∀ i, IsIso (η.app (K.obj i))) :
    IsIso (η.app (colimit K)) := by
  have hΦ : IsColimit (Φ.mapCocone (colimit.cocone K)) :=
    isColimitOfPreserves Φ (colimit.isColimit K)
  have hΨ : IsColimit (Ψ.mapCocone (colimit.cocone K)) :=
    isColimitOfPreserves Ψ (colimit.isColimit K)
  let α : K ⋙ Φ ≅ K ⋙ Ψ :=
    NatIso.ofComponents (fun i => asIso (η.app (K.obj i))) fun f => η.naturality (K.map f)
  have hΦ' : IsColimit ((Cocone.precompose α.hom).obj (Ψ.mapCocone (colimit.cocone K))) :=
    (IsColimit.precomposeHomEquiv α _).symm hΨ
  have heq : η.app (colimit K) = (IsColimit.coconePointUniqueUpToIso hΦ hΦ').hom := by
    refine hΦ.hom_ext fun i => ?_
    rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact η.naturality (colimit.ι K i)
  rw [heq]
  infer_instance

end CategoryTheory.NatTrans

namespace PresheafOfModules

variable {C : Type*} [Category C] {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')
variable {J : Type j} [Category.{jv} J] [HasColimitsOfShape J AddCommGrpCat.{u}]

/-- Change of scalars along a morphism of presheaves of rings preserves colimits of presheaves
of modules whose sections lie in the universe of the rings.

A cocone of presheaves of modules is a colimit as soon as it is one after evaluation at every
object, and after evaluation the functor is the change of scalars of modules over a ring, which
is a left adjoint to coextension of scalars and hence preserves colimits. -/
noncomputable instance preservesColimitsOfShape_restrictScalars_of_ringUniverse :
    PreservesColimitsOfShape J (restrictScalars.{u} α) := by
  refine ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩
  refine ⟨evaluationJointlyReflectsColimits (K ⋙ restrictScalars.{u} α) _ fun X => ?_⟩
  exact isColimitOfPreserves (ModuleCat.restrictScalars.{u} (α.app X).hom)
    (isColimitOfPreserves (evaluation R' X) hc)

variable {D : Type*} [Category D] (G : C ⥤ D) (T : Dᵒᵖ ⥤ RingCat.{u})

/-- Restriction of presheaves of modules along a functor preserves colimits: after evaluation it
is a reindexing, and colimits of presheaves of modules are computed objectwise. -/
noncomputable instance preservesColimitsOfShape_pushforward₀ :
    PreservesColimitsOfShape J (pushforward₀.{u} G T) := by
  refine ⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩
  refine ⟨evaluationJointlyReflectsColimits (K ⋙ pushforward₀.{u} G T) _ fun X => ?_⟩
  exact isColimitOfPreserves (evaluation T (G.op.obj X)) hc

end PresheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

section Shape

variable {J : Type j} [Category.{jv} J] [HasColimitsOfShape J AddCommGrpCat.{u}]

/-- Restriction to the small étale site of the scheme below an object of `𝒳` preserves colimits
of presheaves of modules: it is restriction along a functor followed by a change of scalars, and
both preserve colimits. -/
noncomputable instance preservesColimitsOfShape_restrictModuleToSmallEtaleFunctor (x : 𝒳) :
    PreservesColimitsOfShape J
      (restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ x) := by
  have := isEquivalence_overPost B S hS p hp x
  unfold restrictModuleToSmallEtaleFunctor
  infer_instance

end Shape

/-- The inverse image `a_{small}^*` of presheaves of modules below an arrow of `𝒳` is a left
adjoint, the direct image along the map of structure sheaves being its right adjoint. -/
noncomputable instance isLeftAdjoint_pullback_smallEtaleStructureComparison
    {x y : 𝒳} (φ : x ⟶ y) :
    (PresheafOfModules.pullback.{u}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).IsLeftAdjoint :=
  (PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).isLeftAdjoint

section Colimits

variable {J : Type j} [Category.{jv} J] [HasColimitsOfShape J AddCommGrpCat.{u}]

/-- **Stacks 0764, part (4), for presheaves of modules.** The colimit of a diagram of presheaves
of `𝒪_𝒳`-modules each having the flat base change property of **Stacks 0762** again has the flat
base change property, and the colimit is the colimit of presheaves of modules.

For an arrow `φ` of `𝒳` lying over a flat morphism of schemes, the comparison map `c_φ` is the
component of a natural transformation from `F ↦ a_{small}^*(F|_{V_ét})` to `F ↦ F|_{U_ét}`. Both
functors preserve colimits — the first because `a_{small}^*` is a left adjoint, the second
because restriction to the small étale site is restriction along a functor followed by a change
of scalars — and the component at a colimit of a natural transformation of colimit-preserving
functors is an isomorphism as soon as every component on the diagram is. -/
@[stacks 0764 "part (4), with the ambient category the presheaves of modules rather than the \
  étale sheaves of modules: a colimit of presheaves of modules with the flat base change \
  property has the flat base change property"]
theorem hasFlatBaseChangeProperty_colimit
    (K : J ⥤ PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hK : ∀ i, HasFlatBaseChangeProperty B E h S hS p hp τ hτ (K.obj i)) :
    HasFlatBaseChangeProperty B E h S hS p hp τ hτ (colimit K) := fun φ hflat =>
  NatTrans.isIso_app_colimit
    (restrictModulePullbackComparisonNatTrans B E h S hS p hp τ hτ φ) K
    fun i => hK i φ hflat

/-- **Stacks 0764, part (4), for presheaves of modules**, in the form for an arbitrary colimit
cocone: the vertex of a colimit cocone on a diagram of presheaves of `𝒪_𝒳`-modules with the flat
base change property has the flat base change property.

This is `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_colimit` transported along the
canonical isomorphism of the vertex with the chosen colimit. -/
@[stacks 0764 "part (4), with the ambient category the presheaves of modules rather than the \
  étale sheaves of modules: the vertex of a colimit cocone on a diagram of presheaves of \
  modules with the flat base change property has the flat base change property"]
theorem hasFlatBaseChangeProperty_of_isColimit
    {K : J ⥤ PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj}
    {c : Cocone K} (hc : IsColimit c)
    (hK : ∀ i, HasFlatBaseChangeProperty B E h S hS p hp τ hτ (K.obj i)) :
    HasFlatBaseChangeProperty B E h S hS p hp τ hτ c.pt := by
  have hcol : HasColimit K := ⟨c, hc⟩
  have key : HasFlatBaseChangeProperty B E h S hS p hp τ hτ (colimit K) :=
    hasFlatBaseChangeProperty_colimit B E h S hS p hp τ hτ K hK
  exact fun {_ _} φ hflat => hasFlatBaseChangeProperty_of_iso B E h S hS p hp τ hτ
    (hc.coconePointUniqueUpToIso (colimit.isColimit K)).symm key φ hflat

end Colimits

/-- The full subcategory of the presheaves of `𝒪_𝒳`-modules with the flat base change property
of **Stacks 0762**, as an object property. This is the subcategory **Stacks 0764** part (2) is
about, read in the presheaves of modules rather than in the étale sheaves of modules. -/
abbrev flatBaseChangeModulePresheaves :
    ObjectProperty (PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj) :=
  fun F => HasFlatBaseChangeProperty B E h S hS p hp τ hτ F

/-- The flat base change property depends only on the isomorphism class of the presheaf of
modules, by `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_of_iso`. This is condition (2) of
**Stacks 0754**, the strict fullness of the subcategory. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms
    (flatBaseChangeModulePresheaves.{u, v, w} B E h S hS p hp τ hτ) where
  of_iso e hF := hasFlatBaseChangeProperty_of_iso B E h S hS p hp τ hτ e hF

section ClosedUnderColimits

variable {J : Type j} [Category.{jv} J] [HasColimitsOfShape J AddCommGrpCat.{u}]

/-- The presheaves of modules with the flat base change property are closed under colimits of
shape `J`, by `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_of_isColimit`.

This is **Stacks 0764, part (4), for presheaves of modules**: through Mathlib's instances
`CategoryTheory.Limits.hasColimitsOfShape_of_closedUnderColimits` and
`CategoryTheory.preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape`, the
subcategory has colimits of shape `J` and its inclusion preserves them. -/
@[stacks 0764 "part (4), with the ambient category the presheaves of modules rather than the \
  étale sheaves of modules: the modules with the flat base change property have colimits",
  stacks 0764 "part (4), with the ambient category the presheaves of modules rather than the \
  étale sheaves of modules: those colimits agree with the colimits of all modules"]
instance isClosedUnderColimitsOfShape_flatBaseChangeModulePresheaves :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (flatBaseChangeModulePresheaves.{u, v, w} B E h S hS p hp τ hτ) J where
  colimitsOfShape_le _ := by
    rintro ⟨hc⟩
    exact hasFlatBaseChangeProperty_of_isColimit B E h S hS p hp τ hτ hc.isColimit
      hc.prop_diag_obj

end ClosedUnderColimits

/-- **Stacks 0764, part (2), for presheaves of modules.** The cokernel of a morphism of
presheaves of `𝒪_𝒳`-modules with the flat base change property of **Stacks 0762** has the flat
base change property. This is the closure under cokernels asked for by **Stacks 0754**.

A cokernel is a colimit indexed by the walking parallel pair, whose two values are the source
and the target of the morphism, so this is a case of
`AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_colimit`. -/
@[stacks 0764 "part (2), with the ambient category the presheaves of modules rather than the \
  étale sheaves of modules: the closure under cokernels asked for by Stacks 0754"]
theorem hasFlatBaseChangeProperty_cokernel
    {F G : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj} (α : F ⟶ G)
    (hF : HasFlatBaseChangeProperty B E h S hS p hp τ hτ F)
    (hG : HasFlatBaseChangeProperty B E h S hS p hp τ hτ G) :
    HasFlatBaseChangeProperty B E h S hS p hp τ hτ (cokernel α) :=
  hasFlatBaseChangeProperty_colimit B E h S hS p hp τ hτ (parallelPair α 0) (by
    rintro (_ | _)
    · exact hF
    · exact hG)

/-- **Stacks 0764, part (2), for presheaves of modules.** An initial presheaf of
`𝒪_𝒳`-modules — equivalently, a zero object — has the flat base change property of
**Stacks 0762**. This is the containment of a zero object asked for by **Stacks 0754**.

An initial object is the colimit of the empty diagram, so this is the case of
`AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_of_isColimit` in which the hypothesis on the
diagram is vacuous. -/
@[stacks 0764 "part (2), with the ambient category the presheaves of modules rather than the \
  étale sheaves of modules: the zero object asked for by Stacks 0754"]
theorem hasFlatBaseChangeProperty_initial
    {F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj}
    (hF : IsInitial F) :
    HasFlatBaseChangeProperty B E h S hS p hp τ hτ F :=
  hasFlatBaseChangeProperty_of_isColimit B E h S hS p hp τ hτ hF (fun i => i.as.elim)

end AlgebraicGeometry.Stack

end
