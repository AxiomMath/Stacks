module

public import Mathlib.Topology.Sheaves.Module
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.Topology.Bases.QuotientRealizing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ConnectivityOnABasis
public import StacksFrontier.Topology.Sheaves.Functors.Pushforward.IsSheaf
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact
import StacksCore.Tactic.StacksAttribute

/-!
# Negative self-Ext detected on a collection of opens

Let `(X, 𝒪_X)` be a ringed space and let `ℬ` be a collection of open subsets of `X` such that
`X = ⋃_{U ∈ ℬ} U` and such that for `U, V ∈ ℬ` the intersection `U ∩ V` is the union of the
members of `ℬ` it contains.  If `K` is an object of the unbounded derived category `D(𝒪_X)`
whose restrictions satisfy `Ext^i(K|_U, K|_U) = 0` for `i < 0` and `U ∈ ℬ`, then
`Ext^i(K, K) = 0` for `i < 0`.

This is the second conclusion of [Stacks, Tag 0D68], and is also stated here in the vocabulary
of Situation 0D67, for the global object of a solution of a system of locally given derived
objects.  The first conclusion of Tag 0D68, that a solution is unique up to a unique
isomorphism, is not proved here.

The collection `ℬ` need not be a basis for the topology of `X`, which is what makes the
statement more than [Stacks, Tag 0D66] part (2): one passes to the coarser space `Y` of
[Stacks, Tag 0D5Q], on which the images of the members of `ℬ` *are* a basis, equipped with the
pushforward of `𝒪_X`, and applies Tag 0D66 part (2) there.

## Main results

* `Stacks.DerivedGlueing.exists_coarsening_opens` and
  `Stacks.DerivedGlueing.exists_coarsening` — the coarsening of [Stacks, Tag 0D5Q], as a reusable
  construction: for a collection of opens, and for a ringed space.
* `Stacks.DerivedGlueing.exists_preimage_eq_of_sSup_covered` — a coarsening sees every open that
  is a union of members of the collection, which is what relativizes an argument run through it
  from the whole space to such an open.
* `Stacks.DerivedGlueing.subsingleton_shiftedHom_self_of_covers` — the statement above.
* `Stacks.DerivedGlueing.subsingleton_shiftedHom_restrict_of_sSup_covered` — the same for two
  objects and over any open that the collection covers, not only over `X`.
* `Stacks.DerivedGlueing.Solution` — a solution of a system of locally given derived objects.
* `Stacks.DerivedGlueing.Solution.subsingleton_shiftedHom_self` — the statement above read in
  Situation 0D67: the global object of a solution has no negative self-Ext.

## Implementation notes

The source packages its hypothesis as `Ext^i(K_U, K_U) = 0` for a family `K_U` of objects of
`D(𝒪_U)` together with isomorphisms `K|_U ≅ K_U`; the two readings agree, and the one used here
mentions only `K`.

Restriction of `𝒪_X`-modules to an open `U` is read on the slice site over `U`, as
`CategoryTheory.SheafOfModules.overFunctor`, which is the reading of Tag 0D66.  Reading the
conclusion at the open `⊤` of `Y`, whose inverse image is the open `⊤` of `X`, produces negative
self-Ext vanishing for the restriction of `K` to `⊤` rather than for `K` itself; restriction to
`⊤` is an equivalence, because extension by zero along `⊤` is one, and
`Stacks.DerivedGlueing.faithful_mapDerivedCategory_of_comp` transports that to the derived
categories.

## References

* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D5Q](https://stacks.math.columbia.edu/tag/0D5Q)
* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules RingedSpaceModuleAdjunction
open Stacks.Cohomology.UnboundedHigherDirectImage (preimageRestrict
  subsingleton_shiftedHom_preimageRestrict_of_isBasis)

namespace Stacks.DerivedGlueing

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃ u

/-! ### Derived categories of exact functors: identity, composition, isomorphism -/

section Generic

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁] [HasDerivedCategory.{w₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂] [HasDerivedCategory.{w₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [Abelian C₃] [HasDerivedCategory.{w₃} C₃]

/-- The functor induced on unbounded derived categories by a composite of exact functors is the
composite of the induced functors. -/
def mapDerivedCategoryCompIso (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : C₂ ⥤ C₃) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] [(F ⋙ G).Additive] [PreservesFiniteLimits (F ⋙ G)]
    [PreservesFiniteColimits (F ⋙ G)] :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ (F ⋙ G).mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory)
    ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) (F ⋙ G).mapDerivedCategory
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ))
        DerivedCategory.Q)

/-- Isomorphic exact functors induce isomorphic functors on unbounded derived categories. -/
def mapDerivedCategoryCongr {F F' : C₁ ⥤ C₂} [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (e : F ≅ F') :
    F.mapDerivedCategory ≅ F'.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (F'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory F'.mapDerivedCategory
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ))
      DerivedCategory.Q)

/-- An exact functor with an exact retraction induces a faithful functor on unbounded derived
categories. -/
theorem faithful_mapDerivedCategory_of_comp (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (G : C₂ ⥤ C₁) [G.Additive] [PreservesFiniteLimits G]
    [PreservesFiniteColimits G] (e : F ⋙ G ≅ 𝟭 C₁) :
    F.mapDerivedCategory.Faithful := by
  have := comp_preservesFiniteLimits F G
  have := comp_preservesFiniteColimits F G
  have h : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ 𝟭 (DerivedCategory C₁) :=
    mapDerivedCategoryCompIso F G ≪≫ mapDerivedCategoryCongr e ≪≫
      Stacks.Homology.mapDerivedCategoryIdIso
  have : (F.mapDerivedCategory ⋙ G.mapDerivedCategory).Faithful :=
    Functor.Faithful.of_iso (F := 𝟭 (DerivedCategory C₁)) h.symm
  exact Functor.Faithful.of_comp F.mapDerivedCategory G.mapDerivedCategory

/-- A faithful functor commuting with the shift reflects the vanishing of a shifted Hom
group. -/
theorem subsingleton_shiftedHom_of_faithful (F : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    [F.Faithful] [F.CommShift ℤ] (K L : DerivedCategory C₁) (i : ℤ)
    (h : Subsingleton (ShiftedHom (F.obj K) (F.obj L) i)) :
    Subsingleton (ShiftedHom K L i) := by
  refine ⟨fun a b => F.map_injective (?_ : F.map a = F.map b)⟩
  exact (cancel_mono ((F.commShiftIso i).hom.app L)).mp (h.elim _ _)

/-- The vanishing of a shifted Hom group only depends on the isomorphism classes of its two
arguments. -/
theorem subsingleton_shiftedHom_of_iso {K L K' L' : DerivedCategory C₁} (eK : K ≅ K')
    (eL : L ≅ L') (i : ℤ) (h : Subsingleton (ShiftedHom K' L' i)) :
    Subsingleton (ShiftedHom K L i) :=
  Equiv.subsingleton (eK.homCongr ((shiftFunctor (DerivedCategory C₁) i).mapIso eL))

end Generic

/-! ### Restriction to the open `⊤` -/

section Top

attribute [local instance] HasDerivedCategory.standard

variable {T : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u})

/-- Passing from the slice-site model of modules on an open to the open-subspace model, with
the target named in the open-subspace model. -/
abbrev sliceToSubspace (U : Opens T) :
    SheafOfModules.{u} (O.over U) ⥤ SheafOfModules.{u} (resRing U O) :=
  (U.sheafOfModulesEquivOver O).functor

/-- Passing between the two models of modules on an open is additive: it is the identity on the
underlying maps of sheaves. -/
instance sliceToSubspace_additive (U : Opens T) : (sliceToSubspace O U).Additive :=
  ⟨fun {_ _} _ _ => rfl⟩

/-- Passing from the open-subspace model of modules on an open back to the slice-site model,
with the source named in the open-subspace model. -/
abbrev subspaceToSlice (U : Opens T) :
    SheafOfModules.{u} (resRing U O) ⥤ SheafOfModules.{u} (O.over U) :=
  (U.sheafOfModulesEquivOver O).inverse

/-- Passing back between the two models of modules on an open is additive: it is the identity
on the underlying maps of sheaves. -/
instance subspaceToSlice_additive (U : Opens T) : (subspaceToSlice O U).Additive :=
  ⟨fun {_ _} _ _ => rfl⟩

/-- Passing back between the two models of modules on an open preserves finite limits, being
one half of an equivalence. -/
instance subspaceToSlice_preservesFiniteLimits (U : Opens T) :
    PreservesFiniteLimits (subspaceToSlice O U) :=
  inferInstanceAs (PreservesFiniteLimits (U.sheafOfModulesEquivOver O).inverse)

/-- Passing back between the two models of modules on an open preserves finite colimits, being
one half of an equivalence. -/
instance subspaceToSlice_preservesFiniteColimits (U : Opens T) :
    PreservesFiniteColimits (subspaceToSlice O U) :=
  inferInstanceAs (PreservesFiniteColimits (U.sheafOfModulesEquivOver O).inverse)

/-- Passing between the two models of modules on an open preserves finite limits, being one
half of an equivalence. -/
instance sliceToSubspace_preservesFiniteLimits (U : Opens T) :
    PreservesFiniteLimits (sliceToSubspace O U) :=
  inferInstanceAs (PreservesFiniteLimits (U.sheafOfModulesEquivOver O).functor)

/-- Passing between the two models of modules on an open preserves finite colimits, being one
half of an equivalence. -/
instance sliceToSubspace_preservesFiniteColimits (U : Opens T) :
    PreservesFiniteColimits (sliceToSubspace O U) :=
  inferInstanceAs (PreservesFiniteColimits (U.sheafOfModulesEquivOver O).functor)

/-- Restriction of modules to the opens contained in `⊤`, read in the open-subspace model, is
the restriction of modules to the open subspace `⊤`. -/
theorem overFunctorTop_comp_sliceToSubspace :
    SheafOfModules.overFunctor.{u} O ⊤ ⋙ sliceToSubspace O ⊤ = jStar (⊤ : Opens T) O :=
  rfl

/-- Restriction of modules to the opens contained in an open, followed by the passage to the
open-subspace model, is restriction to the open subspace.  This is
`Stacks.DerivedGlueing.overFunctorTop_comp_sliceToSubspace` for an arbitrary open. -/
theorem overFunctor_comp_sliceToSubspace (U : Opens T) :
    SheafOfModules.overFunctor.{u} O U ⋙ sliceToSubspace O U = jStar U O :=
  rfl

/-- Restriction of modules to the opens contained in an open is additive. -/
instance overFunctor_additive (U : Opens T) :
    (SheafOfModules.overFunctor.{u} O U).Additive :=
  ⟨fun {_ _} _ _ => rfl⟩

/-- **The counit of extension by zero along `⊤` is invertible** ([Stacks, Tag 00AB]): a sheaf of
modules lies in the essential image of extension by zero along `⊤` exactly under a stalk
condition away from `⊤`, which is vacuous. -/
theorem isIso_jShriekAdjunction_counit_app_top (G : SheafOfModules.{u} O) :
    IsIso ((jShriekAdjunction (⊤ : Opens T) O).counit.app G) :=
  counit_isIso_of_stalk_isZero (⊤ : Opens T) O G fun _ hx => absurd trivial hx

/-- Extension by zero along `⊤` after restriction to the open subspace `⊤` is the identity on
modules; this is the counit of that adjunction, which is invertible. -/
def jStarTopCompJShriekTopIso :
    jStar (⊤ : Opens T) O ⋙ jShriek (⊤ : Opens T) O ≅ 𝟭 (SheafOfModules.{u} O) :=
  NatIso.ofComponents
    (fun G => @asIso _ _ _ _ ((jShriekAdjunction (⊤ : Opens T) O).counit.app G)
      (isIso_jShriekAdjunction_counit_app_top O G))
    fun f => (jShriekAdjunction (⊤ : Opens T) O).counit.naturality f

/-- A retraction of restriction to the opens contained in `⊤`: pass to the open-subspace model
and extend by zero. -/
abbrev overFunctorTopRetraction :
    SheafOfModules.{u} (O.over ⊤) ⥤ SheafOfModules.{u} O :=
  sliceToSubspace O ⊤ ⋙ jShriek (⊤ : Opens T) O

/-- Restriction to the opens contained in `⊤`, followed by its retraction, is the identity. -/
def overFunctorTopCompRetractionIso :
    SheafOfModules.overFunctor.{u} O ⊤ ⋙ overFunctorTopRetraction O ≅
      𝟭 (SheafOfModules.{u} O) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (overFunctorTop_comp_sliceToSubspace O))
      (jShriek (⊤ : Opens T) O) ≪≫
    jStarTopCompJShriekTopIso O

/-- Restriction of modules to an open subspace preserves finite limits, being a right
adjoint. -/
instance jStar_preservesFiniteLimits (U : Opens T) : PreservesFiniteLimits (jStar U O) :=
  letI : PreservesLimitsOfSize.{0, 0} (jStar U O) :=
    (jShriekAdjunction U O).rightAdjoint_preservesLimits
  inferInstance

/-- Restriction of modules to an open subspace preserves finite colimits, being a left
adjoint. -/
instance jStar_preservesFiniteColimits (U : Opens T) : PreservesFiniteColimits (jStar U O) :=
  letI : PreservesColimitsOfSize.{0, 0} (jStar U O) :=
    (jStarAdjunction U O).leftAdjoint_preservesColimits
  inferInstance

/-- Restriction of modules to the opens contained in an open, followed by the passage to the
open-subspace model, is restriction to the open subspace; so it is additive. -/
instance overFunctorCompSliceToSubspace_additive (U : Opens T) :
    (SheafOfModules.overFunctor.{u} O U ⋙ sliceToSubspace O U).Additive :=
  inferInstanceAs ((jStar U O).Additive)

/-- Restriction of modules to the opens contained in an open, followed by the passage to the
open-subspace model, preserves finite limits. -/
instance overFunctorCompSliceToSubspace_preservesFiniteLimits (U : Opens T) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} O U ⋙ sliceToSubspace O U) :=
  inferInstanceAs (PreservesFiniteLimits (jStar U O))

/-- Restriction of modules to the opens contained in an open, followed by the passage to the
open-subspace model, preserves finite colimits. -/
instance overFunctorCompSliceToSubspace_preservesFiniteColimits (U : Opens T) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} O U ⋙ sliceToSubspace O U) :=
  inferInstanceAs (PreservesFiniteColimits (jStar U O))

/-- Extension by zero along `⊤` followed by restriction to the opens contained in an open, read
in the open-subspace model, is additive. -/
instance jShriekTopCompRestriction_additive (U : Opens T) :
    (jShriek (⊤ : Opens T) O ⋙
      (SheafOfModules.overFunctor.{u} O U ⋙ sliceToSubspace O U)).Additive :=
  inferInstance

/-- Extension by zero along `⊤` followed by restriction to the opens contained in an open, read
in the open-subspace model, preserves finite limits. -/
instance jShriekTopCompRestriction_preservesFiniteLimits (U : Opens T) :
    PreservesFiniteLimits (jShriek (⊤ : Opens T) O ⋙
      (SheafOfModules.overFunctor.{u} O U ⋙ sliceToSubspace O U)) :=
  comp_preservesFiniteLimits _ _

/-- Extension by zero along `⊤` followed by restriction to the opens contained in an open, read
in the open-subspace model, preserves finite colimits. -/
instance jShriekTopCompRestriction_preservesFiniteColimits (U : Opens T) :
    PreservesFiniteColimits (jShriek (⊤ : Opens T) O ⋙
      (SheafOfModules.overFunctor.{u} O U ⋙ sliceToSubspace O U)) :=
  comp_preservesFiniteColimits _ _

/-- Passing between the two models of modules on an open is faithful on derived categories, the
two being inverse equivalences. -/
theorem faithful_sliceToSubspace_mapDerivedCategory (U : Opens T) :
    (sliceToSubspace O U).mapDerivedCategory.Faithful :=
  faithful_mapDerivedCategory_of_comp (sliceToSubspace O U) (subspaceToSlice O U)
    (U.sheafOfModulesEquivOver O).unitIso.symm

/-- **Extension by zero along an open is faithful on derived categories**: restriction to the
open subspace undoes it, the unit of that adjunction being invertible ([Stacks, Tag 00AB]). This
holds for an arbitrary open `U`, not only `U = ⊤`: full faithfulness of `j_!` along an open
immersion does not need the immersion to be onto. -/
theorem faithful_jShriek_mapDerivedCategory (U : Opens T) :
    (jShriek U O).mapDerivedCategory.Faithful :=
  faithful_mapDerivedCategory_of_comp (jShriek U O) (jStar U O)
    (@asIso _ _ _ _ (jShriekAdjunction U O).unit (isIso_jShriekAdjunction_unit U O)).symm

/-- Extension by zero along `⊤` is faithful on derived categories: the special case of
`faithful_jShriek_mapDerivedCategory` at `U = ⊤`. -/
theorem faithful_jShriekTop_mapDerivedCategory :
    (jShriek (⊤ : Opens T) O).mapDerivedCategory.Faithful :=
  faithful_jShriek_mapDerivedCategory O ⊤

/-- **Restriction to `⊤` reflects the vanishing of a negative shifted Hom group.** If the
restrictions of `K` and `L` to the opens contained in `⊤` admit no nonzero degree-`i` morphism,
then neither do `K` and `L`. -/
theorem subsingleton_shiftedHom_of_overTop
    [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} O ⊤)]
    [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} O ⊤)]
    (K L : DerivedCategory (SheafOfModules.{u} O)) (i : ℤ)
    (h : Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} O ⊤).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} O ⊤).mapDerivedCategory.obj L) i)) :
    Subsingleton (ShiftedHom K L i) := by
  have := faithful_mapDerivedCategory_of_comp (SheafOfModules.overFunctor.{u} O ⊤)
    (overFunctorTopRetraction O) (overFunctorTopCompRetractionIso O)
  exact subsingleton_shiftedHom_of_faithful
    (SheafOfModules.overFunctor.{u} O ⊤).mapDerivedCategory K L i h

end Top

/-! ### The coarsening of Tag 0D5Q, in the vocabulary of opens -/

section Coarsening

/-- **[Stacks, Tag 0D5Q] in the vocabulary of `Opens`.** Let `ℬ` be a collection of open subsets
covering a space `T` such that the intersection of two members of `ℬ` is the union of the members
contained in it.  Then there are a space `Z`, a continuous `f : T ⟶ Z` and, for each member `W` of
`ℬ`, an open `g W` of `Z` whose preimage is `W`, such that the `g W` form a basis for the topology
of `Z`.

This is `create_map_from_subcollection` packaged for a collection of `Opens` rather than of bare
sets; the members of `ℬ` need not be a basis of `T`, and the point of the coarsening is that their
images *are* a basis of `Z`. -/
theorem exists_coarsening_opens {T : TopCat.{u}} (ℬ : Set (Opens T)) (hcover : sSup ℬ = ⊤)
    (hinter : ∀ U ∈ ℬ, ∀ V ∈ ℬ, U ⊓ V = sSup {W | W ∈ ℬ ∧ W ≤ U ⊓ V}) :
    ∃ (Z : TopCat.{u}) (f : T ⟶ Z) (g : ℬ → Opens Z),
      (∀ W : ℬ, (Opens.map f).obj (g W) = W.1) ∧ Opens.IsBasis (Set.range g) := by
  classical
  set B : Set (Set T) := (fun U : Opens T => (U : Set T)) '' ℬ with hBdef
  have hB_open : ∀ s ∈ B, IsOpen s := by
    rintro _ ⟨U, -, rfl⟩
    exact U.isOpen
  have hB_cover : ⋃₀ B = Set.univ := by
    have : (↑(sSup ℬ) : Set T) = ⋃ U ∈ ℬ, (U : Set T) := Opens.coe_sSup
    rw [hcover] at this
    simpa [hBdef, Set.sUnion_image, Set.sUnion_eq_biUnion] using this.symm
  have hB_inter : ∀ s ∈ B, ∀ t ∈ B, s ∩ t = ⋃₀ {r ∈ B | r ⊆ s ∩ t} := by
    rintro _ ⟨U, hU, rfl⟩ _ ⟨V, hV, rfl⟩
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.sUnion_subset fun _ hr => hr.2)
    have hx' : x ∈ (U ⊓ V : Opens T) := hx
    rw [hinter U hU V hV] at hx'
    obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.mp hx'
    exact ⟨(W : Set T), ⟨⟨W, hW.1, rfl⟩, fun _ hy => hW.2 hy⟩, hxW⟩
  obtain ⟨Z, τ, c, hcc, hcopen, hcpre, hcbasis⟩ :=
    create_map_from_subcollection B hB_open hB_cover hB_inter
  let _ : TopologicalSpace Z := τ
  refine ⟨TopCat.of Z, TopCat.ofHom ⟨c, hcc⟩,
    fun W => ⟨c '' (W.1 : Set T), hcopen _ ⟨W.1, W.2, rfl⟩⟩,
    fun W => Opens.ext (hcpre _ ⟨W.1, W.2, rfl⟩), ?_⟩
  have hcoe : (fun U : Opens (TopCat.of Z) => (U : Set Z)) ''
      Set.range (fun W : ℬ => (⟨c '' (W.1 : Set T), hcopen _ ⟨W.1, W.2, rfl⟩⟩ : Opens _)) =
      (fun s => c '' s) '' B := by
    refine Set.ext fun s => ⟨?_, ?_⟩
    · rintro ⟨-, ⟨W, rfl⟩, rfl⟩
      exact ⟨(W.1 : Set T), ⟨W.1, W.2, rfl⟩, rfl⟩
    · rintro ⟨-, ⟨U, hU, rfl⟩, rfl⟩
      exact ⟨_, ⟨⟨U, hU⟩, rfl⟩, rfl⟩
  rwa [Opens.IsBasis, hcoe]

/-- **A coarsening sees every open that is a union of members of the collection.** If the preimage
along `f` of the open `g W` attached to each member `W` of `ℬ` is `W` itself, then an open `O` of
the source which is the union of the members of `ℬ` contained in it is the preimage of an open of
the target, namely of the union of the `g W` for the members `W` contained in `O`.

This is what relativizes an argument run through the coarsening of [Stacks, Tag 0D5Q] from the
whole space to an arbitrary open: a statement proved for every open of the coarse space is thereby
available at every open of the source that `ℬ` covers, with no second coarsening. -/
theorem exists_preimage_eq_of_sSup_covered {T Z : TopCat.{u}} (f : T ⟶ Z) (ℬ : Set (Opens T))
    (g : ℬ → Opens Z) (himage : ∀ W : ℬ, (Opens.map f).obj (g W) = W.1)
    (O : Opens T) (hO : O = sSup {W | W ∈ ℬ ∧ W ≤ O}) :
    ∃ V : Opens Z, (Opens.map f).obj V = O := by
  classical
  refine ⟨sSup {V | ∃ W : ℬ, W.1 ≤ O ∧ g W = V},
    Opens.ext (Set.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩)⟩
  · obtain ⟨V, ⟨W, hWO, rfl⟩, hxV⟩ := Opens.mem_sSup.mp hx
    have : x ∈ ((Opens.map f).obj (g W) : Set T) := hxV
    rw [himage W] at this
    exact hWO this
  · rw [hO] at hx
    obtain ⟨W, hW, hxW⟩ := Opens.mem_sSup.mp hx
    refine Opens.mem_sSup.mpr ⟨g ⟨W, hW.1⟩, ⟨⟨W, hW.1⟩, hW.2, rfl⟩, ?_⟩
    change x ∈ ((Opens.map f).obj (g ⟨W, hW.1⟩) : Set T)
    rwa [himage ⟨W, hW.1⟩]

end Coarsening

/-! ### Tag 0D68, the vanishing of negative self-Ext -/

section Main

attribute [local instance] HasDerivedCategory.standard

/-- The pushforward of the structure sheaf of a ringed space along a continuous map, as a ringed
space on the target. -/
abbrev pushforwardRingedSpace {X : RingedSpace.{u, u}} {T : TopCat.{u}} (g : X.carrier ⟶ T) :
    RingedSpace.{u, u} where
  carrier := T
  presheaf := ((TopCat.Sheaf.pushforward CommRingCat.{u} g).obj X.sheaf).1
  IsSheaf := ((TopCat.Sheaf.pushforward CommRingCat.{u} g).obj X.sheaf).2

/-- A continuous map, as a morphism of ringed spaces into the pushforward of the source along
it; the map of structure sheaves is the identity. -/
abbrev pushforwardRingedMap {X : RingedSpace.{u, u}} {T : TopCat.{u}} (g : X.carrier ⟶ T) :
    X ⟶ pushforwardRingedSpace g :=
  InducedCategory.homMk { base := g, c := 𝟙 _ }

/-- **The coarsening of [Stacks, Tag 0D5Q] for a ringed space.** A collection `ℬ` of open subsets
covering `X`, the intersection of two members being the union of the members contained in it,
gives a morphism of ringed spaces `X ⟶ Y` with `𝒪_Y = f_* 𝒪_X` — the identity on structure
sheaves — and, for each member `W` of `ℬ`, an open of `Y` whose inverse image is `W`, the opens so
obtained being a basis of `Y`.

This is `Stacks.DerivedGlueing.exists_coarsening_opens` read through
`Stacks.DerivedGlueing.pushforwardRingedMap`; it is the input of Tag 0D66 part (2) for a
collection that is not a basis, and
`Stacks.DerivedGlueing.exists_preimage_eq_of_sSup_covered` relativizes a conclusion drawn from it
to any open of `X` that `ℬ` covers. -/
theorem exists_coarsening {X : RingedSpace.{u, u}} (ℬ : Set (Opens X.carrier))
    (hcover : sSup ℬ = ⊤)
    (hinter : ∀ U ∈ ℬ, ∀ V ∈ ℬ, U ⊓ V = sSup {W | W ∈ ℬ ∧ W ≤ U ⊓ V}) :
    ∃ (T : TopCat.{u}) (base : X.carrier ⟶ T) (imageOpen : ℬ → Opens T),
      (∀ W : ℬ, (opensMap (pushforwardRingedMap base)).obj (imageOpen W) = W.1) ∧
        Opens.IsBasis (Set.range imageOpen) :=
  exists_coarsening_opens ℬ hcover hinter

/-- If the restrictions of `K` and `L` to the members of `ℬ` have no negative Ext, then neither do
their restrictions along the coarsening to the images of the members. -/
private theorem subsingleton_shiftedHom_preimageRestrict_imageOpen {X : RingedSpace.{u, u}}
    {ℬ : Set (Opens X.carrier)} {T : TopCat.{u}} (base : X.carrier ⟶ T) (imageOpen : ℬ → Opens T)
    (himage : ∀ W : ℬ, (opensMap (pushforwardRingedMap base)).obj (imageOpen W) = W.1)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hExt : ∀ U ∈ ℬ, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj L) i)) :
    ∀ V ∈ Set.range imageOpen, ∀ j : ℤ, j < 0 → Subsingleton
      (ShiftedHom ((preimageRestrict (pushforwardRingedMap base) V).obj K)
        ((preimageRestrict (pushforwardRingedMap base) V).obj L) j) := by
  rintro - ⟨U, rfl⟩ j hj
  have h := hExt U.1 U.2 j hj
  rwa [← himage U] at h

/-- **Stacks 0D68, the vanishing of negative self-Ext.** Let `(X, 𝒪_X)` be a ringed space and
let `ℬ` be a collection of open subsets covering `X` such that the intersection of two members
of `ℬ` is the union of the members of `ℬ` contained in it. If `K` is an object of `D(𝒪_X)` with
`Ext^i(K|_U, K|_U) = 0` for `i < 0` and every `U ∈ ℬ`, then `Ext^i(K, K) = 0` for `i < 0`.

The members of `ℬ` need not form a basis; by Tag 0D5Q there is a continuous `f : X → Y` whose
images of the members of `ℬ` do form a basis of `Y` and satisfy `f⁻¹(f(U)) = U`, and Tag 0D66
part (2) applied to `f` with `𝒪_Y = f_* 𝒪_X` gives the vanishing over every open of `Y`,
including `⊤`.

Here `K` is an arbitrary object of `D(𝒪_X)` and `ℬ` an arbitrary collection;
`Stacks.DerivedGlueing.Solution.subsingleton_shiftedHom_self` is this statement applied to the
global object of a `Stacks.DerivedGlueing.Solution` of a system of locally given objects. -/
@[stacks 0D68 "the vanishing of negative self-Ext, for an arbitrary object `K` of `D(𝒪_X)`
  and an arbitrary collection of opens covering `X` with intersections covered by members, such
  that `K|_U` has no negative self-Ext for every member `U`"]
theorem subsingleton_shiftedHom_self_of_covers {X : RingedSpace.{u, u}}
    (ℬ : Set (Opens X.carrier)) (hcover : sSup ℬ = ⊤)
    (hinter : ∀ U ∈ ℬ, ∀ V ∈ ℬ, U ⊓ V = sSup {W | W ∈ ℬ ∧ W ≤ U ⊓ V})
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hExt : ∀ U ∈ ℬ, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K) i))
    (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom K K i) := by
  obtain ⟨Z, base, imageOpen, himage, hbasis⟩ := exists_coarsening ℬ hcover hinter
  have htop := subsingleton_shiftedHom_preimageRestrict_of_isBasis hbasis
    (pushforwardRingedMap base) K K
    (subsingleton_shiftedHom_preimageRestrict_imageOpen base imageOpen himage K K hExt) ⊤ i hi
  exact subsingleton_shiftedHom_of_overTop (structureSheafRing X) K K i htop

/-- **The vanishing clause of Tag 0D68, relativized to an open that the collection covers.** Let
`ℬ` be a collection of open subsets covering `X` whose pairwise intersections are unions of
members, and let `K`, `L` be objects of `D(𝒪_X)` with `Ext^i(K|_U, L|_U) = 0` for `i < 0` and
every `U ∈ ℬ`.  Then `Ext^i(K|_O, L|_O) = 0` for `i < 0` and *every* open `O` that is the union of
the members of `ℬ` contained in it, not only for `O = X`.

No second coarsening is involved.  Tag 0D66 part (2), as
`Stacks.Cohomology.UnboundedHigherDirectImage.subsingleton_shiftedHom_preimageRestrict_of_isBasis`,
already concludes at every open of the coarse space `Y` of Tag 0D5Q, and
`Stacks.DerivedGlueing.exists_preimage_eq_of_sSup_covered` exhibits such an `O` as the inverse
image of one: the union of the images of the members contained in `O`.  Taking `O = ⊤` recovers
the input of `Stacks.DerivedGlueing.subsingleton_shiftedHom_self_of_covers`. -/
theorem subsingleton_shiftedHom_restrict_of_sSup_covered {X : RingedSpace.{u, u}}
    (ℬ : Set (Opens X.carrier)) (hcover : sSup ℬ = ⊤)
    (hinter : ∀ U ∈ ℬ, ∀ V ∈ ℬ, U ⊓ V = sSup {W | W ∈ ℬ ∧ W ≤ U ⊓ V})
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hExt : ∀ U ∈ ℬ, ∀ i : ℤ, i < 0 → Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) U).mapDerivedCategory.obj L) i))
    (O : Opens X.carrier) (hO : O = sSup {W | W ∈ ℬ ∧ W ≤ O})
    (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} (structureSheafRing X) O).mapDerivedCategory.obj L) i) := by
  obtain ⟨Z, base, imageOpen, himage, hbasis⟩ := exists_coarsening ℬ hcover hinter
  obtain ⟨V, hV⟩ := exists_preimage_eq_of_sSup_covered base ℬ imageOpen himage O hO
  rw [← hV]
  exact subsingleton_shiftedHom_preimageRestrict_of_isBasis hbasis (pushforwardRingedMap base)
    K L (subsingleton_shiftedHom_preimageRestrict_imageOpen base imageOpen himage K L hExt) V i hi

end Main

/-! ### Tag 0D68 in the vocabulary of Situation 0D67 -/

section Solutions

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- Restriction of modules from an open to a smaller one preserves finite limits. -/
instance openModuleRestriction_preservesFiniteLimits (V U : Opens X.carrier) (hVU : V ≤ U) :
    PreservesFiniteLimits (openModuleRestriction X V U hVU) :=
  comp_preservesFiniteLimits _ _

/-- Restriction of modules from an open to a smaller one preserves finite colimits. -/
instance openModuleRestriction_preservesFiniteColimits (V U : Opens X.carrier) (hVU : V ≤ U) :
    PreservesFiniteColimits (openModuleRestriction X V U hVU) :=
  comp_preservesFiniteColimits _ _

/-- Restriction of modules from `X` to an open `U`, as extension by zero from the open subspace
`⊤` followed by restriction to the opens contained in `U` and the passage to the open-subspace
model. -/
theorem openModuleRestriction_top_eq (U : Opens X.carrier) :
    jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X) ⋙
        (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U ⋙
          sliceToSubspace (underlyingRingSheaf X) U) =
      openModuleRestriction X U ⊤ le_top :=
  rfl

/-- The displayed restriction of a system of locally given derived objects is the functor
induced on derived categories by restriction of complexes of sheaves: both invert the
quasi-isomorphisms and factor the same functor through the localization. -/
def restrictionIsoMapDerivedCategory (S : LocallyGiven X) (V U : Opens X.carrier)
    (hVU : V ≤ U) :
    S.restriction V U hVU ≅ (openModuleRestriction X V U hVU).mapDerivedCategory :=
  letI : Localization.Lifting
      (DerivedCategory.Q (C := SheafOfModules.{u} (restrictedRingSheaf X U)))
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (restrictedRingSheaf X U))
        (ComplexShape.up ℤ))
      ((openModuleRestriction X V U hVU).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) (S.restriction V U hVU) :=
    ⟨S.restrictionFactors V U hVU⟩
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (restrictedRingSheaf X U))
      (ComplexShape.up ℤ))
    ((openModuleRestriction X V U hVU).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    ((openModuleRestriction X V U hVU).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    (S.restriction V U hVU) (openModuleRestriction X V U hVU).mapDerivedCategory
    (Iso.refl _)

/-- **A solution of a system of locally given derived objects** (Situation 0D67): a global
object of the derived category together with isomorphisms identifying its restrictions with the
prescribed local objects, compatibly with all the prescribed transition isomorphisms. -/
structure Solution (S : LocallyGiven X) where
  /-- The global object, taken in the derived category of the open subspace `⊤`. -/
  obj : OpenDerivedCategory X ⊤
  /-- The identification of the restriction of the global object with the prescribed local
  object. -/
  rho : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens),
    (S.restriction U ⊤ le_top).obj obj ≅ S.obj U hU
  /-- Restricting the identification over `U` to a smaller member `V` and composing with the
  prescribed transition isomorphism gives the identification over `V`. -/
  compatibility : ∀ (V U : Opens X.carrier) (hVU : V ≤ U) (hU : U ∈ S.opens)
      (hV : V ∈ S.opens),
    (S.restrictionComp V U ⊤ hVU le_top).hom.app obj ≫
        (S.restriction V U hVU).map (rho U hU).hom ≫ (S.rho V U hVU hU hV).hom =
      (rho V hV).hom

/-- The global object of a solution, read in the derived category of `𝒪_X`-modules on the whole
of `X` rather than on the open subspace `⊤`. -/
abbrev Solution.globalObj {S : LocallyGiven X} (A : Solution S) :
    DerivedCategory (SheafOfModules.{u} (underlyingRingSheaf X)) :=
  (jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory.obj A.obj

/-- The restriction of the global object of a solution to a member of the displayed collection,
read in the open-subspace model, is its restriction in the model of Situation 0D67. -/
def Solution.canonicalRestrictionIso {S : LocallyGiven X} (A : Solution S)
    (U : Opens X.carrier) :
    (sliceToSubspace (underlyingRingSheaf X) U).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U).mapDerivedCategory.obj
          A.globalObj) ≅
      (openModuleRestriction X U ⊤ le_top).mapDerivedCategory.obj A.obj :=
  (mapDerivedCategoryCompIso (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U)
      (sliceToSubspace (underlyingRingSheaf X) U)).app A.globalObj ≪≫
    (mapDerivedCategoryCompIso (jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X))
      (SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U ⋙
        sliceToSubspace (underlyingRingSheaf X) U)).app A.obj ≪≫
    (mapDerivedCategoryCongr (eqToIso (openModuleRestriction_top_eq U))).app A.obj

/-- The restriction of the global object of a solution to a member of the displayed collection,
read in the open-subspace model, is the prescribed local object there. -/
def Solution.restrictionIso {S : LocallyGiven X} (A : Solution S) (U : Opens X.carrier)
    (hU : U ∈ S.opens) :
    (sliceToSubspace (underlyingRingSheaf X) U).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} (underlyingRingSheaf X) U).mapDerivedCategory.obj
          A.globalObj) ≅
      S.obj U hU :=
  A.canonicalRestrictionIso U ≪≫
    ((restrictionIsoMapDerivedCategory S U ⊤ le_top).app A.obj).symm ≪≫ A.rho U hU

/-- **Stacks 0D68, the vanishing of negative self-Ext.** In Situation 0D67, suppose that the
displayed opens cover `X` and that the intersection of two of them is the union of the members
of the collection it contains, and that the prescribed local objects have no negative
self-Ext.  Then the global object of a solution has no negative self-Ext either.

The restrictions of the global object are the prescribed local objects, by
`Stacks.DerivedGlueing.Solution.restrictionIso`, so this is
`Stacks.DerivedGlueing.subsingleton_shiftedHom_self_of_covers` read through the equivalences
comparing the models of restriction of modules to an open. -/
@[stacks 0D68 "the vanishing of negative self-Ext of the global object of a solution"]
theorem Solution.subsingleton_shiftedHom_self {S : LocallyGiven X} (A : Solution S)
    (hcover : sSup S.opens = ⊤)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (i : ℤ) (hi : i < 0) :
    Subsingleton (ShiftedHom A.obj A.obj i) := by
  have := faithful_jShriekTop_mapDerivedCategory (underlyingRingSheaf X)
  refine subsingleton_shiftedHom_of_faithful
    (jShriek (⊤ : Opens X.carrier) (underlyingRingSheaf X)).mapDerivedCategory A.obj A.obj i ?_
  refine subsingleton_shiftedHom_self_of_covers S.opens hcover hinter A.globalObj ?_ i hi
  intro U hU j hj
  have := faithful_sliceToSubspace_mapDerivedCategory (underlyingRingSheaf X) U
  refine subsingleton_shiftedHom_of_faithful
    (sliceToSubspace (underlyingRingSheaf X) U).mapDerivedCategory _ _ j ?_
  exact subsingleton_shiftedHom_of_iso (A.restrictionIso U hU) (A.restrictionIso U hU) j
    (hExt U hU j hj)

end Solutions

end Stacks.DerivedGlueing

end
