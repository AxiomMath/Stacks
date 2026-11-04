module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyFilteredColimitsTypeU
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SectionsOnALocallySmallSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors

/-!
# Filtered colimits and the cohomology of `𝒪_F`-modules on the small étale site, at module
universe `u`

On a quasi-compact and quasi-separated algebraic space `F` over a scheme `S`, the cohomology of
`𝒪_F`-modules **in the universe `u` of the structure rings** commutes with filtered colimits, on
the small étale site of `F` itself.

`AlgebraicGeometry.Space.isIso_colimit_post_globalModuleCohomology_smallEtaleModel` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyFilteredColimitsTypeU` is this
statement on the equi-universe *model* `AlgebraicGeometry.Space.smallEtaleModelRingedSite` of the
small étale ringed site. What is added here is the passage back to the small étale site itself,
that is, to `AlgebraicGeometry.Space.Modules.{u, u}` and to the cohomology
`(Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u} 𝒪_F).rightDerived p`
which the rest of the algebraic-spaces development uses — see
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyOverBase` of
`StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap`.

## Main results

* `Stacks.Cohomology.SiteModules.ModelComparison.functorSectionsEquiv`: **compatible families of
  elements of a type-valued functor transport along an equivalence of index categories**, the two
  index categories being allowed to live in different universes.
* `Stacks.Cohomology.SiteModules.ModelComparison.sectionsRestrictAddEquiv` and
  `…sectionsRestrictUliftAddEquiv`: **global sections of a sheaf of modules restrict bijectively
  and additively along an equivalence of sites**, and the same with the universe lift inserted.
* `AlgebraicGeometry.Space.smallEtaleGlobalSectionsForgetModelIso`: the abelian-group comparison
  of global sections on the small étale site with global sections on its equi-universe model, the
  universe lift included.
* `AlgebraicGeometry.Space.smallEtaleDerivedGlobalSectionsForgetModelIso`: the same, derived.
* `AlgebraicGeometry.Space.isIso_colimit_post_smallEtaleModuleCohomology_typeU`: **Stacks 073E at
  module coefficients in the universe `u` of the structure rings, on the small étale site.**
* `AlgebraicGeometry.Space.preservesColimit_smallEtaleModuleCohomology_typeU`: the same as
  preservation of the colimit.

## Implementation notes

*Why this is a construction and not a transport.* For `M : SheafOfModules.{u} 𝒪_F` on the small
étale site, whose objects lie in `Type (u + 1)`, the compatible global sections `M.sections` form
a subtype of a product indexed by those objects, hence lie in `Type (u + 1)`; so
`Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}` takes values in
`ModuleCat.{u + 1}` over a ring that itself lies in `Type (u + 1)`, however the module universe
is chosen. On the model everything is in `Type u`. The two sides are therefore not related by any
equivalence of categories, and
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_of_equivalences`, which
wants an equivalence of the two *target* categories, does not apply.

*Why no ring comparison is needed.* A comparison of the two coefficient rings `Γ(F, 𝒪_F)` and
`Γ(F_model, 𝒪_model)` — a ring isomorphism between a ring in `Type (u + 1)` and a ring in
`Type u`, and then a restriction of scalars along it — would be needed to compare the two
module-valued functors directly. It is avoided:
`CategoryTheory.forget₂ (ModuleCat A) AddCommGrpCat` reflects isomorphisms, preserves colimits
and is exact, so the whole statement may be read in abelian groups, where the only comparison
left is the additive one. That comparison is
`Stacks.Cohomology.SiteModules.ModelComparison.sectionsRestrictAddEquiv`: a compatible family of
sections on the small étale site restricts to one on the model, and the equivalence of sites makes
this bijective, the inverse reinstating the section over `X` from the section over
`e.functor.obj (e.inverse.obj X)` along the counit. It is proved at the underlying type-valued
functor, where the restriction of scalars that the transport of a sheaf of modules performs is
invisible; at the level of sheaves of modules the two types of sections are definitionally equal
but not so to `rw`, whose transparency does not see through the two structure rings.

*The chain of derived comparisons.*
`Stacks.Cohomology.ColimitsOfCohomology.rightDerivedCompExactIso` pulls the exact `forget₂` out of
the derived functor on each side, and
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` pulls out the precomposition by
`AlgebraicGeometry.Space.modulesEquivModelModules`, which is an equivalence and so is exact and
preserves injective objects. The universe lift `AddCommGrpCat.uliftFunctor` is exact and preserves
colimits of every size, which is what lets it be moved past both `Functor.rightDerived` and
`CategoryTheory.Limits.colimit.post`.

*Instances supplied by hand, and why.* Three families of instances are not found by search at
these universes.

* `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and
  `Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives` conclude at the module universe
  `max u v r w`; on the model that is `max u w`, and instance search cannot solve
  `max u ?w =?= u`. They are supplied explicitly at `w := u`. These are the very instances
  `Stacks.Cohomology.SiteModules.globalModuleCohomology` is elaborated with, which is what makes
  the model statement applicable.
* On the small étale site itself the module universe `u` is *below* the universe of the objects,
  so those two lemmas do not apply at all; the abelian structure is Mathlib's
  `SheafOfModules.instAbelian`, raised to priority 5000 so that it is reached before them, and
  the injective resolutions are `AlgebraicGeometry.Space.hasInjectiveResolutions_modules`, which
  is a theorem rather than an instance and is therefore carried in the statements as a `have`,
  exactly as in `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyOverBase`.
* Colimit preservation by `CategoryTheory.forget₂ (ModuleCat A) AddCommGrpCat` has the same
  shape of obstruction: Mathlib's instance concludes for `ModuleCat.{max w w'}`, and the module
  universes here are the concrete `u + 1` and `u`. The four statements
  `AlgebraicGeometry.Space.preservesColimitsOfShape_smallEtaleGlobalSectionsForget` and its three
  companions discharge this, at the shape universe of the schemes and for finite shapes.

*No `@[stacks]` attribute.* [Stacks, Tag 073E] is a statement about abelian sheaves, registered on
exactly that statement in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits`; the module reading is
not an enumerated part of the tag.

## References

* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

namespace Stacks.Cohomology.SiteModules.ModelComparison

universe w m u₁ v₁ u₂ v₂ w₀ a b a' b'

/-! ### Compatible families along an equivalence of index categories -/

section FunctorSections

variable {K : Type a} [Category.{b} K] {K' : Type a'} [Category.{b'} K']

/-- **A compatible family of elements of a type-valued functor is the same thing as a compatible
family of elements of its restriction along an equivalence of index categories.**

The restriction is evaluation at `E.functor.obj j`; the inverse reads the value at
`E.inverse.obj k` and transports it along the counit
`E.functor.obj (E.inverse.obj k) ⟶ k`. The two index categories may live in different
universes, so the two types of compatible families do too. -/
def functorSectionsEquiv (E : K' ≌ K) (G : K ⥤ Type w₀) :
    G.sections ≃ (E.functor ⋙ G).sections where
  toFun s := ⟨fun j ↦ s.1 (E.functor.obj j), fun f ↦ s.2 (E.functor.map f)⟩
  invFun t := ⟨fun k ↦ G.map (E.counit.app k) (t.1 (E.inverse.obj k)), fun {k k'} f ↦ by
    have ht : G.map ((E.inverse ⋙ E.functor).map f) (t.1 (E.inverse.obj k)) =
        t.1 (E.inverse.obj k') := t.2 (E.inverse.map f)
    change G.map f (G.map (E.counit.app k) (t.1 (E.inverse.obj k))) =
      G.map (E.counit.app k') (t.1 (E.inverse.obj k'))
    rw [← ht, ← Functor.map_comp_apply, ← Functor.map_comp_apply, E.counit.naturality f,
      Functor.id_map]⟩
  left_inv s := Subtype.ext (funext fun k ↦ s.2 (E.counit.app k))
  right_inv t := Subtype.ext (funext fun j ↦ by
    have ht : G.map (E.functor.map (E.unit.app j)) (t.1 j) =
        t.1 (E.inverse.obj (E.functor.obj j)) := t.2 (E.unit.app j)
    have hid : E.functor.map (E.unit.app j) ≫ E.counit.app (E.functor.obj j) =
        𝟙 (E.functor.obj j) := E.functor_unitIso_comp j
    change G.map (E.counit.app (E.functor.obj j))
      (t.1 (E.inverse.obj (E.functor.obj j))) = t.1 j
    rw [← ht, ← Functor.map_comp_apply, hid]
    exact G.map_id_apply _ _)

end FunctorSections

/-! ### Global sections of a sheaf of modules along an equivalence of sites -/

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- **Global sections of a sheaf of modules restrict bijectively along an equivalence of sites**,
the two underlying categories being allowed to live in different universes.

Global sections of a sheaf of modules are the compatible families of its underlying abelian
presheaf, and the transport of the sheaf along the equivalence has for underlying abelian presheaf
the restriction along `e.functor.op`; so this is
`Stacks.Cohomology.SiteModules.ModelComparison.functorSectionsEquiv` for the opposite
equivalence. -/
def sectionsRestrictEquiv (M : SheafOfModules.{m} R) :
    M.sections ≃
      ((Stacks.SheafOfModules.reindexEquivalence (J' := J') e R).functor.obj M).sections :=
  functorSectionsEquiv e.op (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})

/-- **Restriction of global sections along an equivalence of sites is additive.** This is the
comparison that the universe gap between the small étale site of an algebraic space and its
equi-universe model turns on: the two types of global sections live in the two different universes
of the objects of the two sites, and the restriction map between them is an additive
bijection. -/
def sectionsRestrictAddEquiv (M : SheafOfModules.{m} R) :
    M.sections ≃+
      ((Stacks.SheafOfModules.reindexEquivalence (J' := J') e R).functor.obj M).sections :=
  { sectionsRestrictEquiv J' e R M with
      map_add' := fun _ _ ↦ by ext _; rfl }

/-- `Stacks.Cohomology.SiteModules.ModelComparison.sectionsRestrictAddEquiv` followed by the
universe lift, which is the shape in which the comparison of the two global-sections functors is
read: the ambient site may have its objects in a universe strictly above the one in which the
compatible families on the equivalent site live. -/
def sectionsRestrictUliftAddEquiv (M : SheafOfModules.{m} R) :
    M.sections ≃+ ULift.{w₀}
      ((Stacks.SheafOfModules.reindexEquivalence (J' := J') e R).functor.obj M).sections :=
  (sectionsRestrictAddEquiv J' e R M).trans AddEquiv.ulift.symm

end Stacks.Cohomology.SiteModules.ModelComparison

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### Forgetting the scalars on global sections -/

/-- Global sections of `𝒪_F`-modules at module universe `u`, read as abelian groups. They lie in
`Type (u + 1)`: a compatible family is indexed by the objects of the small étale site, which lie
one universe above the sections themselves. -/
abbrev smallEtaleGlobalSectionsForget :
    ModuleCat.{u + 1} (RingCat.sectionsSubring
      (ringSheaf (smallEtaleRingedSite B S hS F hF).O).obj) ⥤ Ab.{u + 1} :=
  forget₂ _ _

/-- Global sections of modules on the equi-universe model, read as abelian groups. On the model
everything lies in `Type u`. -/
abbrev smallEtaleModelGlobalSectionsForget :
    ModuleCat.{u} (RingCat.sectionsSubring
      (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O).obj) ⥤ Ab.{u} :=
  forget₂ _ _

/-- Forgetting the scalars on the global sections of `𝒪_F`-modules preserves colimits of a given
shape in the universe of the schemes.

Stated rather than inferred: the ambient instance of Mathlib concludes for
`ModuleCat.{max w w'}`, and matching that against the concrete module universe `u + 1` sets
instance search the constraint `max (u + 1) ?w =?= u + 1`, which it does not solve. -/
theorem preservesColimitsOfShape_smallEtaleGlobalSectionsForget
    (I : Type u) [Category.{u} I] :
    PreservesColimitsOfShape I (smallEtaleGlobalSectionsForget B S hS F hF) :=
  ModuleCat.forget₂PreservesColimitsOfShape _ _

/-- Forgetting the scalars on the global sections of `𝒪_F`-modules preserves finite colimits. -/
theorem preservesFiniteColimits_smallEtaleGlobalSectionsForget :
    PreservesFiniteColimits (smallEtaleGlobalSectionsForget B S hS F hF) :=
  ⟨fun _ _ _ ↦ ModuleCat.forget₂PreservesColimitsOfShape _ _⟩

/-- Forgetting the scalars on the global sections of `𝒪_F`-modules preserves finite limits. -/
theorem preservesFiniteLimits_smallEtaleGlobalSectionsForget :
    PreservesFiniteLimits (smallEtaleGlobalSectionsForget B S hS F hF) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- The model counterpart of
`AlgebraicGeometry.Space.preservesColimitsOfShape_smallEtaleGlobalSectionsForget`. -/
theorem preservesColimitsOfShape_smallEtaleModelGlobalSectionsForget
    (I : Type u) [Category.{u} I] :
    PreservesColimitsOfShape I (smallEtaleModelGlobalSectionsForget B S hS F hF) :=
  ModuleCat.forget₂PreservesColimitsOfShape _ _

/-- The model counterpart of
`AlgebraicGeometry.Space.preservesFiniteColimits_smallEtaleGlobalSectionsForget`. -/
theorem preservesFiniteColimits_smallEtaleModelGlobalSectionsForget :
    PreservesFiniteColimits (smallEtaleModelGlobalSectionsForget B S hS F hF) :=
  ⟨fun _ _ _ ↦ ModuleCat.forget₂PreservesColimitsOfShape _ _⟩

/-- The model counterpart of
`AlgebraicGeometry.Space.preservesFiniteLimits_smallEtaleGlobalSectionsForget`. -/
theorem preservesFiniteLimits_smallEtaleModelGlobalSectionsForget :
    PreservesFiniteLimits (smallEtaleModelGlobalSectionsForget B S hS F hF) :=
  ⟨fun _ _ _ ↦ inferInstance⟩

/-- Transport of `𝒪_F`-modules to the equi-universe model is an additive functor: on underlying
presheaves it is restriction along the equivalence, which does not touch the addition. -/
theorem additive_modulesEquivModelModules_functor :
    (modulesEquivModelModules B S hS F hF).functor.Additive :=
  ⟨rfl⟩

/-! ### The abelian-group comparison of global sections with the model -/

attribute [local instance] preservesColimitsOfShape_smallEtaleGlobalSectionsForget
  preservesFiniteColimits_smallEtaleGlobalSectionsForget
  preservesFiniteLimits_smallEtaleGlobalSectionsForget
  preservesColimitsOfShape_smallEtaleModelGlobalSectionsForget
  preservesFiniteColimits_smallEtaleModelGlobalSectionsForget
  preservesFiniteLimits_smallEtaleModelGlobalSectionsForget
  additive_modulesEquivModelModules_functor

/-- **Global sections of `𝒪_F`-modules, read in abelian groups, are the global sections of their
transports to the equi-universe model, lifted to the universe of the objects of the small étale
site.**

The content is
`Stacks.Cohomology.SiteModules.ModelComparison.sectionsRestrictUliftAddEquiv`; everything else is
the observation that both sides are the compatible families of sections with their pointwise
addition, so the comparison is natural on the nose. -/
def smallEtaleGlobalSectionsForgetModelIso :
    globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS F hF).O) ⋙
        smallEtaleGlobalSectionsForget B S hS F hF ≅
      (modulesEquivModelModules B S hS F hF).functor ⋙
        globalSectionsFunctor.{u, u, u, u}
            (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) ⋙
          smallEtaleModelGlobalSectionsForget B S hS F hF ⋙
            AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  NatIso.ofComponents
    (fun M ↦ AddEquiv.toAddCommGrpIso
      (ModelComparison.sectionsRestrictUliftAddEquiv (smallEtaleModelTopology B S hS F)
        (smallEtaleModelEquivalence B S hS F)
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O) M))
    (by intro M N f; rfl)

/-! ### Stacks 073E at module universe `u` on the small étale site -/

/-- The abelian-group comparison of
`AlgebraicGeometry.Space.smallEtaleGlobalSectionsForgetModelIso` in every degree: the cohomology of
`𝒪_F`-modules at module universe `u`, read in abelian groups, is the cohomology on the
equi-universe model, lifted.

The exact functors `forget₂ (ModuleCat _) AddCommGrpCat` and `AddCommGrpCat.uliftFunctor` are
moved past `CategoryTheory.Functor.rightDerived` by
`Stacks.Cohomology.ColimitsOfCohomology.rightDerivedCompExactIso`, and the precomposition by the
equivalence `AlgebraicGeometry.Space.modulesEquivModelModules` by
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`. -/
def smallEtaleDerivedGlobalSectionsForgetModelIso (p : ℕ) :
    have := hasInjectiveResolutions_modules B S hS F hF
    letI : Abelian (SheafOfModules.{u}
        (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)) :=
      moduleSheavesAbelian.{u, u, u, u} _
    letI : EnoughInjectives (SheafOfModules.{u}
        (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)) :=
      moduleSheavesEnoughInjectives.{u, u, u, u} _
    (globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).rightDerived p ⋙
        smallEtaleGlobalSectionsForget B S hS F hF ≅
      (modulesEquivModelModules B S hS F hF).functor ⋙
        globalModuleCohomology.{u, u, u, u}
            (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) p ⋙
          smallEtaleModelGlobalSectionsForget B S hS F hF ⋙
            AddCommGrpCat.uliftFunctor.{u + 1, u} := by
  have := hasInjectiveResolutions_modules B S hS F hF
  letI : Abelian (SheafOfModules.{u}
      (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)) :=
    moduleSheavesAbelian.{u, u, u, u} _
  letI : EnoughInjectives (SheafOfModules.{u}
      (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)) :=
    moduleSheavesEnoughInjectives.{u, u, u, u} _
  refine (Stacks.Cohomology.ColimitsOfCohomology.rightDerivedCompExactIso
      (globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O))
      (smallEtaleGlobalSectionsForget B S hS F hF) p).symm ≪≫ ?_
  refine Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso
      (smallEtaleGlobalSectionsForgetModelIso B S hS F hF) p ≪≫ ?_
  refine Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (modulesEquivModelModules B S hS F hF).functor _ p ≪≫ ?_
  exact Functor.isoWhiskerLeft _
    (Stacks.Cohomology.ColimitsOfCohomology.rightDerivedCompExactIso
      (globalSectionsFunctor.{u, u, u, u}
        (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O))
      (smallEtaleModelGlobalSectionsForget B S hS F hF ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}) p)

/-- **Stacks 073E at module coefficients, in the universe `u` of the structure rings, on the small
étale site of the algebraic space `F`.** For a filtered diagram `D` of `𝒪_F`-modules with sections
in `Type u`, the comparison `colim_i H^p(F, D_i) ⟶ H^p(F, colim_i D_i)` is an isomorphism.

This is the cohomology the rest of the algebraic-spaces development uses, the one of
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyOverBase`. The statement on the
equi-universe model is
`AlgebraicGeometry.Space.isIso_colimit_post_globalModuleCohomology_smallEtaleModel`, and the
passage back is `AlgebraicGeometry.Space.smallEtaleDerivedGlobalSectionsForgetModelIso` together
with the fact that `forget₂ (ModuleCat _) AddCommGrpCat` reflects isomorphisms. -/
theorem isIso_colimit_post_smallEtaleModuleCohomology_typeU
    (hqc : IsQuasiCompactSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (p : ℕ) {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Modules.{u, u} B S hS F hF) :
    have := hasInjectiveResolutions_modules B S hS F hF
    IsIso (colimit.post D
      ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).rightDerived p)) := by
  intro _
  let : Abelian (SheafOfModules.{u}
      (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)) :=
    moduleSheavesAbelian.{u, u, u, u} _
  let : EnoughInjectives (SheafOfModules.{u}
      (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)) :=
    moduleSheavesEnoughInjectives.{u, u, u, u} _
  have hmo := isIso_colimit_post_globalModuleCohomology_smallEtaleModel.{u, u}
    B S hS hZ F hF hqc hqs p (D ⋙ (modulesEquivModelModules B S hS F hF).functor)
  have hΦ : IsIso (colimit.post D (modulesEquivModelModules B S hS F hF).functor) :=
    inferInstance
  have hE : IsIso (colimit.post (D ⋙ (modulesEquivModelModules B S hS F hF).functor)
      (globalModuleCohomology.{u, u, u, u}
          (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) p ⋙
        smallEtaleModelGlobalSectionsForget B S hS F hF ⋙
          AddCommGrpCat.uliftFunctor.{u + 1, u})) := by
    rw [← colimit.post_post]
    infer_instance
  have hD : IsIso (colimit.post D ((modulesEquivModelModules B S hS F hF).functor ⋙
      globalModuleCohomology.{u, u, u, u}
          (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) p ⋙
        smallEtaleModelGlobalSectionsForget B S hS F hF ⋙
          AddCommGrpCat.uliftFunctor.{u + 1, u})) :=
    Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_of_equivalence_comp D
      (modulesEquivModelModules B S hS F hF) _
  have hforget : IsIso (colimit.post D
      ((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).rightDerived p ⋙
        smallEtaleGlobalSectionsForget B S hS F hF)) :=
    Stacks.Cohomology.isIso_colimit_post_of_natIso D _ _
      (smallEtaleDerivedGlobalSectionsForgetModelIso B S hS F hF p).symm
  rw [← colimit.post_post] at hforget
  have : IsIso ((smallEtaleGlobalSectionsForget B S hS F hF).map
      (colimit.post D ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).rightDerived p))) :=
    IsIso.of_isIso_comp_left (colimit.post (D ⋙ _) (smallEtaleGlobalSectionsForget B S hS F hF)) _
  exact isIso_of_reflects_iso _ (smallEtaleGlobalSectionsForget B S hS F hF)

/-- **Stacks 073E at module coefficients, in the universe `u` of the structure rings**, as
preservation of the colimit. This is the form a consumer that needs the colimit cocone uses; the
content is `AlgebraicGeometry.Space.isIso_colimit_post_smallEtaleModuleCohomology_typeU`. -/
theorem preservesColimit_smallEtaleModuleCohomology_typeU
    (hqc : IsQuasiCompactSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (p : ℕ) {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Modules.{u, u} B S hS F hF) :
    have := hasInjectiveResolutions_modules B S hS F hF
    PreservesColimit D
      ((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).rightDerived p) :=
  have := hasInjectiveResolutions_modules B S hS F hF
  have := isIso_colimit_post_smallEtaleModuleCohomology_typeU B S hS hZ F hF hqc hqs p D
  preservesColimit_of_isIso_post _ _

end AlgebraicGeometry.Space

end
