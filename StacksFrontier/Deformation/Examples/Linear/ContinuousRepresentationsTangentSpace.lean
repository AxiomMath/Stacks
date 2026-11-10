module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ExtComparison
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.ComponentCohomology
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentations
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsDenseRestriction
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsInfinitesimalAutomorphisms
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsRimSchlessinger
public import StacksFrontier.Deformation.PredeformationTangent.DifferentialLinear
public import StacksFrontier.Deformation.Representation.TangentSelfExt
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.ExtTorsor

/-!
# The tangent space of a continuous representation

Let `Γ` be a topological group and `ρ₀ : Γ → GL_k(V)` a finite-dimensional continuous
representation. The tangent space of the deformation category of Stacks 0D3K is the first
continuous cohomology `H¹(Γ, End_k(V))` of the conjugation action on the endomorphisms of `V`.

The category of Stacks 0D3K is a full subcategory of the category of Stacks 0D3J, so the
differential of the inclusion is an injective `k`-linear map from the continuous tangent space
into the tangent space of Stacks 0DVT, which is `Ext¹_{k[Γ]}(V, V)`. The category of continuous
discrete `k`-`Γ`-modules is also a full subcategory of `k[Γ]`-modules, by an exact fully faithful
functor, so its `Ext¹` injects into the same group. The two images coincide: an extension of `V`
by itself over the group algebra has continuous orbit maps exactly when the deformation it is
associated to is continuous, which is Stacks 0DVT's `Deformation.IsAssociatedSelfExtension` read
on both sides. Hence the continuous tangent space is `Ext¹` of `V` by itself in continuous
discrete modules, which is `H¹(Γ, Vᵛ ⊗_k V)` by Stacks 0DVE.

## Main results

* `Deformation.Examples.FiniteProjectiveRepresentation.tangentSpaceEquivContinuousCohomology`:
  **Stacks 0DVW**, the tangent clause. The natural tangent space of the deformation category of
  a finite-dimensional continuous representation is `H¹(Γ, End_k(V))`, together with the
  equivariant identification of the coefficient module with the conjugation action on
  `End_k(V)`.
* `Deformation.Examples.FiniteProjectiveRepresentation.tangentSpaceEquivContinuousSelfExt`: the
  intermediate identification with `Ext¹` in continuous discrete modules.

## Implementation notes

The coefficient ring, the group and the representation space all live in one universe `w`, as
they do for the infinitesimal-automorphism clause of the same tag: the cohomology functor
`Stacks.ContinuousCohomology.cohomologyFunctor` is stated on
`Stacks.Injectives.ContinuousModule.{u, v, max u v w}`, and taking the three equal is what makes
the representation space land in the coefficient universe without a lift.

The coefficient module of the comparison is the dual tensor module `Vᵛ ⊗_k V` of Stacks 0DVE
rather than a separate endomorphism module. Its representation is identified with
`Representation.linHom ρ₀ ρ₀`, the conjugation action on `End_k(V)`, inside the statement, so
nothing about the coefficients is left to the reader.

The comparison with Stacks 0DVT runs in the `Ext`-universe that tag is stated at, namely the
one `CategoryTheory.HasExt.standard` supplies, because the comparison of a fully faithful exact
functor on `Ext¹` needs the same universe on both categories. Stacks 0DVE is instead stated in
the morphism universe, where `Stacks.ContinuousCohomology.hasExt_continuousModule` lives, so
`continuousSelfExtEquivCohomology` moves between the two with
`Stacks.ExtUniverse.extChgUnivLinearEquivOfHasExt`, which takes the two smallness hypotheses as
explicit arguments precisely so that both universes can be named at the point of use.

The model of the derived category is left as a free instance argument, as it is for
`Stacks.ContinuousCohomology.cohomologyFunctor` itself and for Stacks 0DVF.

## References

* [Stacks Project, Tag 0DVW](https://stacks.math.columbia.edu/tag/0DVW)
* [Stacks Project, Tag 0DVT](https://stacks.math.columbia.edu/tag/0DVT)
* [Stacks Project, Tag 0DVE](https://stacks.math.columbia.edu/tag/0DVE)
* [Stacks Project, Tag 0D3K](https://stacks.math.columbia.edu/tag/0D3K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

/-! ### The auxiliary universe of an `Ext`-group -/

namespace Stacks.ExtUniverse

universe t w₁ w₂ v' u'

variable {R : Type t} [Ring R] {C : Type u'} [Category.{v'} C] [Abelian C] [Linear R C]
  [HasExt.{w₁} C] [HasExt.{w₂} C]

/-- Changing the auxiliary universe of an `Ext`-group commutes with the scalar action. -/
theorem extChgUniv_smul {X Y : C} {n : ℕ} (r : R) (e : Ext.{w₁} X Y n) :
    Ext.chgUniv.{w₂} (r • e) = r • Ext.chgUniv.{w₂} e := by
  let := HasDerivedCategory.standard C
  refine (Ext.homEquiv (X := X) (Y := Y) (n := n)).injective ?_
  rw [Ext.homEquiv_chgUniv]
  change (r • e).hom = (r • Ext.chgUniv.{w₂} e).hom
  rw [Ext.smul_hom, Ext.smul_hom]
  exact congrArg (fun z => r • z) (Ext.homEquiv_chgUniv e).symm

/-- An `Ext`-group does not depend on its auxiliary universe, as an `R`-module: the groups
computed with the smallness hypotheses `h₁` and `h₂` are `R`-linearly equivalent. -/
def extChgUnivLinearEquivOfHasExt {R : Type t} [Ring R] {C : Type u'} [Category.{v'} C]
    [Abelian C] [Linear R C] (h₁ : HasExt.{w₁} C) (h₂ : HasExt.{w₂} C) (X Y : C) (n : ℕ) :
    @Ext C _ _ h₁ X Y n ≃ₗ[R] @Ext C _ _ h₂ X Y n :=
  letI := h₁
  letI := h₂
  AddEquiv.toLinearEquiv Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv
    extChgUniv_smul

end Stacks.ExtUniverse

namespace Stacks.ContinuousCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

universe e u v w

/-! ### Continuous discrete modules as modules over the group algebra -/

section ToGroupAlgebra

variable (k : Type u) [Field k] (G : Type v) [Group G] [TopologicalSpace G]

/-- A continuous discrete `k`-`G`-module read as a `k`-linear representation of `G`. -/
abbrev continuousModuleToRep :
    Stacks.Injectives.ContinuousModule.{u, v, w} k G ⥤ Rep.{w} k G :=
  continuousModuleToAction k G ⋙ Rep.ActionToRep k G

/-- Reading a continuous discrete module as a representation preserves finite limits. -/
theorem continuousModuleToRep_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (continuousModuleToRep.{u, v, w} k G) :=
  Limits.preservesFiniteLimits_of_reflects_of_preserves _
    (forget₂ (Rep.{w} k G) (ModuleCat.{w} k))

/-- Reading a continuous discrete module as a representation preserves finite colimits. -/
theorem continuousModuleToRep_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (continuousModuleToRep.{u, v, w} k G) :=
  Limits.preservesFiniteColimits_of_reflects_of_preserves _
    (forget₂ (Rep.{w} k G) (ModuleCat.{w} k))

/-- Reading a continuous discrete module as a representation is an additive functor. -/
theorem continuousModuleToRep_additive :
    (continuousModuleToRep.{u, v, w} k G).Additive where
  map_add := by intros; rfl

/-- Reading a continuous discrete module as a representation is a `k`-linear functor. -/
theorem continuousModuleToRep_linear :
    (continuousModuleToRep.{u, v, w} k G).Linear k where
  map_smul := by intros; rfl

/-- Reading a continuous discrete module as a representation is fully faithful. -/
private def continuousModuleToRep_fullyFaithful :
    (continuousModuleToRep.{u, v, w} k G).FullyFaithful :=
  (ObjectProperty.fullyFaithfulι ContAction.IsDiscrete).comp
    ((ObjectProperty.fullyFaithfulι Action.IsContinuous).comp
      (Functor.FullyFaithful.ofFullyFaithful (Rep.ActionToRep k G)))

/-- Reading a continuous discrete module as a representation is a full functor. -/
theorem continuousModuleToRep_full : (continuousModuleToRep.{u, v, w} k G).Full :=
  (continuousModuleToRep_fullyFaithful.{u, v, w} k G).full

/-- Reading a continuous discrete module as a representation is a faithful functor. -/
theorem continuousModuleToRep_faithful : (continuousModuleToRep.{u, v, w} k G).Faithful :=
  (continuousModuleToRep_fullyFaithful.{u, v, w} k G).faithful

/-- A continuous discrete `k`-`G`-module read as a module over the group algebra. -/
abbrev continuousModuleToGroupAlgebra :
    Stacks.Injectives.ContinuousModule.{u, v, w} k G ⥤ ModuleCat.{w} (MonoidAlgebra k G) :=
  continuousModuleToRep k G ⋙ Rep.toModuleMonoidAlgebra

/-- Reading a continuous discrete module as a module over the group algebra is a full
functor. -/
theorem continuousModuleToGroupAlgebra_full :
    (continuousModuleToGroupAlgebra.{u, v, w} k G).Full := by
  let := continuousModuleToRep_full.{u, v, w} k G
  infer_instance

/-- Reading a continuous discrete module as a module over the group algebra is a faithful
functor. -/
theorem continuousModuleToGroupAlgebra_faithful :
    (continuousModuleToGroupAlgebra.{u, v, w} k G).Faithful := by
  let := continuousModuleToRep_faithful.{u, v, w} k G
  infer_instance

/-- Reading a continuous discrete module as a module over the group algebra preserves finite
limits. -/
theorem continuousModuleToGroupAlgebra_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (continuousModuleToGroupAlgebra.{u, v, w} k G) := by
  let := continuousModuleToRep_preservesFiniteLimits.{u, v, w} k G
  infer_instance

/-- Reading a continuous discrete module as a module over the group algebra preserves finite
colimits. -/
theorem continuousModuleToGroupAlgebra_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (continuousModuleToGroupAlgebra.{u, v, w} k G) := by
  let := continuousModuleToRep_preservesFiniteColimits.{u, v, w} k G
  infer_instance

/-- Reading a continuous discrete module as a module over the group algebra is an additive
functor. -/
theorem continuousModuleToGroupAlgebra_additive :
    (continuousModuleToGroupAlgebra.{u, v, w} k G).Additive where
  map_add := by intros; rfl

/-- Reading a continuous discrete module as a module over the group algebra is a `k`-linear
functor. -/
theorem continuousModuleToGroupAlgebra_linear :
    (continuousModuleToGroupAlgebra.{u, v, w} k G).Linear k where
  map_smul := by
    intro source target morphism scalar
    ext element
    let ρ := ((continuousModuleToRep k G).obj target).ρ
    change ρ.asModuleEquiv.symm (scalar • morphism.hom.hom.hom element) =
      (algebraMap k (MonoidAlgebra k G) scalar) •
        ρ.asModuleEquiv.symm (morphism.hom.hom.hom element)
    exact ρ.asModuleEquiv_symm_map_smul _ _

/-! ### Recognising the essential image by continuity of the orbit maps -/

/-- The orbit maps of a continuous discrete module are continuous for the discrete topology. -/
theorem continuousModule_rep_orbit_continuous
    (M : Stacks.Injectives.ContinuousModule.{u, v, w} k G) :
    letI : TopologicalSpace ((Rep.ActionToRep k G).obj M.obj.obj) := ⊥
    ∀ z : M.obj.obj.V,
      Continuous (fun γ : G => ((Rep.ActionToRep k G).obj M.obj.obj).ρ γ z) := by
  let : TopologicalSpace ((Rep.ActionToRep k G).obj M.obj.obj) := ⊥
  exact continuous_prod_of_discrete_right.mp
    ((Action.isContinuous_def M.obj.obj).mp M.obj.property)

/-- A function into a set with the discrete topology that agrees with the image of a continuous
function under any map from a discrete set is continuous. -/
private theorem continuous_bot_of_comp_eq {H X Y : Type*} [TopologicalSpace H] (f : X → Y)
    {g : H → X} {g' : H → Y} (hg : letI : TopologicalSpace X := ⊥; Continuous g)
    (h : ∀ γ, f (g γ) = g' γ) :
    letI : TopologicalSpace Y := ⊥
    Continuous g' := by
  let : TopologicalSpace X := ⊥
  let : DiscreteTopology X := ⟨rfl⟩
  let : TopologicalSpace Y := ⊥
  let : DiscreteTopology Y := ⟨rfl⟩
  exact (continuous_of_discreteTopology.comp hg).congr h

/-- The orbit maps of a continuous discrete module, read on the group algebra. -/
theorem continuousModule_groupAlgebra_orbit_continuous
    (M : Stacks.Injectives.ContinuousModule.{u, v, w} k G) :
    let N := (Rep.toModuleMonoidAlgebra (k := k) (G := G)).obj
      ((continuousModuleToRep k G).obj M)
    letI : TopologicalSpace N := ⊥
    ∀ z : N, Continuous (fun γ : G => (MonoidAlgebra.single γ (1 : k)) • z) := by
  dsimp only
  intro z
  let ρ := ((Rep.ActionToRep k G).obj M.obj.obj).ρ
  let equiv := ρ.asModuleEquiv.toAddEquiv
  refine continuous_bot_of_comp_eq equiv.symm
    (continuousModule_rep_orbit_continuous k G M (equiv z)) fun γ => ?_
  apply equiv.injective
  rw [equiv.apply_symm_apply]
  change ρ γ (ρ.asModuleEquiv z) =
    ρ.asAlgebraHom (MonoidAlgebra.single γ (1 : k)) (ρ.asModuleEquiv z)
  rw [Representation.asAlgebraHom_single_one]

/-- A representation whose orbit maps are continuous for the discrete topology is a continuous
discrete module. -/
def continuousModuleOfRepOrbits (ρ : Rep.{w} k G)
    (hcont : letI : TopologicalSpace ρ := ⊥
      ∀ z : ρ, Continuous (fun γ : G => ρ.ρ γ z)) :
    Stacks.Injectives.ContinuousModule.{u, v, w} k G :=
  ⟨⟨(Rep.RepToAction k G).obj ρ,
      (Action.isContinuous_def _).2 (continuous_prod_of_discrete_right.mpr hcont)⟩, ⟨rfl⟩⟩

/-- A representation whose orbit maps are continuous for the discrete topology lies in the
essential image of the continuous discrete modules. -/
theorem continuousModuleToRep_essImage_of_orbit_continuous (ρ : Rep.{w} k G)
    (hcont : letI : TopologicalSpace ρ := ⊥
      ∀ z : ρ, Continuous (fun γ : G => ρ.ρ γ z)) :
    (continuousModuleToRep.{u, v, w} k G).essImage ρ :=
  ⟨continuousModuleOfRepOrbits.{u, v, w} k G ρ hcont, ⟨Rep.ActionToRep_RepToAction k G ρ⟩⟩

/-- A module over the group algebra whose orbit maps `γ ↦ γ • z` are continuous for the discrete
topology lies in the essential image of the continuous discrete modules. -/
theorem continuousModuleToGroupAlgebra_essImage_of_orbit_continuous
    (N : ModuleCat.{w} (MonoidAlgebra k G))
    (hcont : letI : TopologicalSpace N := ⊥
      ∀ z : N, Continuous (fun γ : G => (MonoidAlgebra.single γ (1 : k)) • z)) :
    (continuousModuleToGroupAlgebra.{u, v, w} k G).essImage N := by
  let ρ := (Rep.ofModuleMonoidAlgebra (k := k) (G := G)).obj N
  let equiv := RestrictScalars.addEquiv k (MonoidAlgebra k G) N
  obtain ⟨P, ⟨iso⟩⟩ :=
    continuousModuleToRep_essImage_of_orbit_continuous.{u, v, w} k G ρ fun z =>
      continuous_bot_of_comp_eq equiv.symm (hcont (equiv z)) fun _ => rfl
  exact ⟨P, ⟨(Rep.toModuleMonoidAlgebra (k := k) (G := G)).mapIso iso ≪≫ Rep.counitIso N⟩⟩

/-! ### The range of the comparison on `Ext¹` -/

section Ext

variable [HasExt.{e} (Stacks.Injectives.ContinuousModule.{u, v, w} k G)]
  [HasExt.{e} (ModuleCat.{w} (MonoidAlgebra k G))]

/-- The map on `Ext¹` from continuous discrete modules to modules over the group algebra is
injective. -/
theorem continuousModuleToGroupAlgebra_mapExt_injective
    (A B : Stacks.Injectives.ContinuousModule.{u, v, w} k G) :
    letI := continuousModuleToGroupAlgebra_additive.{u, v, w} k G
    letI := continuousModuleToGroupAlgebra_preservesFiniteLimits.{u, v, w} k G
    letI := continuousModuleToGroupAlgebra_preservesFiniteColimits.{u, v, w} k G
    Function.Injective ((continuousModuleToGroupAlgebra k G).mapExtAddHom A B 1) := by
  let := continuousModuleToGroupAlgebra_additive.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_preservesFiniteLimits.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_preservesFiniteColimits.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_full.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_faithful.{u, v, w} k G
  exact Functor.mapExtAddHom_injective_of_fullyFaithful _ A B

/-- The class of an extension over the group algebra of two continuous discrete modules whose
middle term has continuous orbit maps lies in the image of `Ext¹` of continuous discrete
modules. -/
theorem extClass_mem_range_of_orbit_continuous
    (A B : Stacks.Injectives.ContinuousModule.{u, v, w} k G)
    (E : ModuleCat.{w} (MonoidAlgebra k G))
    (i : (continuousModuleToGroupAlgebra k G).obj B ⟶ E)
    (p : E ⟶ (continuousModuleToGroupAlgebra k G).obj A)
    (hzero : i ≫ p = 0) (hexact : (ShortComplex.mk i p hzero).ShortExact)
    (hcont : letI : TopologicalSpace E := ⊥
      ∀ z : E, Continuous (fun γ : G => (MonoidAlgebra.single γ (1 : k)) • z)) :
    letI := continuousModuleToGroupAlgebra_additive.{u, v, w} k G
    letI := continuousModuleToGroupAlgebra_preservesFiniteLimits.{u, v, w} k G
    letI := continuousModuleToGroupAlgebra_preservesFiniteColimits.{u, v, w} k G
    hexact.extClass ∈
      Set.range ((continuousModuleToGroupAlgebra k G).mapExtAddHom A B 1) := by
  let := continuousModuleToGroupAlgebra_additive.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_preservesFiniteLimits.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_preservesFiniteColimits.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_full.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_faithful.{u, v, w} k G
  exact Functor.exists_mapExtAddHom_eq_of_essImage _ A B hexact.extClass
    ⟨E, i, p, hzero, hexact, rfl,
      continuousModuleToGroupAlgebra_essImage_of_orbit_continuous.{u, v, w} k G E hcont⟩

end Ext

/-- Continuity of the orbit maps of a module over the group algebra is invariant under
isomorphism. -/
theorem module_orbit_continuous_of_iso {A B : ModuleCat.{w} (MonoidAlgebra k G)} (iso : A ≅ B)
    (hA : letI : TopologicalSpace A := ⊥
      ∀ z : A, Continuous (fun γ : G => (MonoidAlgebra.single γ (1 : k)) • z)) :
    letI : TopologicalSpace B := ⊥
    ∀ z : B, Continuous (fun γ : G => (MonoidAlgebra.single γ (1 : k)) • z) := by
  intro z
  exact continuous_bot_of_comp_eq iso.hom (hA (iso.inv z)) fun γ => by
    rw [map_smul, show iso.hom (iso.inv z) = z from ConcreteCategory.congr_hom iso.inv_hom_id z]

section Ext

variable [HasExt.{e} (Stacks.Injectives.ContinuousModule.{u, v, w} k G)]
  [HasExt.{e} (ModuleCat.{w} (MonoidAlgebra k G))]

/-- An extension over the group algebra whose class comes from continuous discrete modules has
continuous orbit maps. -/
private theorem orbit_continuous_of_extClass_mem_range
    (A B : Stacks.Injectives.ContinuousModule.{u, v, w} k G)
    (E : ModuleCat.{w} (MonoidAlgebra k G))
    (i : (continuousModuleToGroupAlgebra k G).obj B ⟶ E)
    (p : E ⟶ (continuousModuleToGroupAlgebra k G).obj A)
    (hzero : i ≫ p = 0) (hexact : (ShortComplex.mk i p hzero).ShortExact) :
    letI := continuousModuleToGroupAlgebra_additive.{u, v, w} k G
    letI := continuousModuleToGroupAlgebra_preservesFiniteLimits.{u, v, w} k G
    letI := continuousModuleToGroupAlgebra_preservesFiniteColimits.{u, v, w} k G
    hexact.extClass ∈
        Set.range ((continuousModuleToGroupAlgebra k G).mapExtAddHom A B 1) →
      (letI : TopologicalSpace E := ⊥
        ∀ z : E, Continuous (fun γ : G => (MonoidAlgebra.single γ (1 : k)) • z)) := by
  let := continuousModuleToGroupAlgebra_additive.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_preservesFiniteLimits.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_preservesFiniteColimits.{u, v, w} k G
  rintro ⟨ξ, hξ⟩
  obtain ⟨E', i', p', hzero', hexact', hclass'⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (Stacks.Injectives.ContinuousModule.{u, v, w} k G) A B).1 ξ
  let F := continuousModuleToGroupAlgebra.{u, v, w} k G
  have hmap : ((ShortComplex.mk i' p' hzero').map F).ShortExact :=
    hexact'.map_of_exact F
  have hmapClass : hmap.extClass = hexact.extClass := by
    calc
      hmap.extClass = F.mapExtAddHom A B 1 hexact'.extClass := by
        rw [Functor.mapExtAddHom_apply]
        exact (Ext.mapExactFunctor_extClass F hexact').symm
      _ = F.mapExtAddHom A B 1 ξ := congrArg _ hclass'
      _ = hexact.extClass := hξ
  obtain ⟨iso, -, -⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (ModuleCat.{w} (MonoidAlgebra k G)) (F.obj A) (F.obj B)).2.1
      _ E _ _ _ i p hzero hmap hexact |>.1 hmapClass
  exact module_orbit_continuous_of_iso k G iso
    (continuousModule_groupAlgebra_orbit_continuous.{u, v, w} k G E')

/-- **An extension class over the group algebra comes from continuous discrete modules exactly
when the extension has continuous orbit maps.** -/
theorem extClass_mem_range_iff_orbit_continuous
    (A B : Stacks.Injectives.ContinuousModule.{u, v, w} k G)
    (E : ModuleCat.{w} (MonoidAlgebra k G))
    (i : (continuousModuleToGroupAlgebra k G).obj B ⟶ E)
    (p : E ⟶ (continuousModuleToGroupAlgebra k G).obj A)
    (hzero : i ≫ p = 0) (hexact : (ShortComplex.mk i p hzero).ShortExact) :
    letI := continuousModuleToGroupAlgebra_additive.{u, v, w} k G
    letI := continuousModuleToGroupAlgebra_preservesFiniteLimits.{u, v, w} k G
    letI := continuousModuleToGroupAlgebra_preservesFiniteColimits.{u, v, w} k G
    hexact.extClass ∈
        Set.range ((continuousModuleToGroupAlgebra k G).mapExtAddHom A B 1) ↔
      (letI : TopologicalSpace E := ⊥
        ∀ z : E, Continuous (fun γ : G => (MonoidAlgebra.single γ (1 : k)) • z)) := by
  let := continuousModuleToGroupAlgebra_additive.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_preservesFiniteLimits.{u, v, w} k G
  let := continuousModuleToGroupAlgebra_preservesFiniteColimits.{u, v, w} k G
  exact ⟨orbit_continuous_of_extClass_mem_range.{e, u, v, w} k G A B E i p hzero hexact,
    extClass_mem_range_of_orbit_continuous.{e, u, v, w} k G A B E i p hzero hexact⟩

end Ext

end ToGroupAlgebra

end Stacks.ContinuousCohomology

namespace Deformation.Examples.FiniteProjectiveRepresentation

open Deformation Stacks.ContinuousCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

universe d u w

variable {Λ : Type u} {k Γ : Type w} [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
  [TopologicalSpace Γ]

/-! ### Forgetting continuity -/

/-- A finite projective representation of `Γ`, read in the second presentation of Stacks 0D3J:
the two presentations have the same fields, so the reading is the identity. -/
def toRepresentationCategory (X : FiniteProjectiveRepresentation.{u, w, w, w} Λ k Γ) :
    Deformation.RepresentationCategory.{u, w, w, w, w} Λ k Γ where
  base := X.base
  carrier := X.carrier
  action := X.action

/-- A representation in the second presentation of Stacks 0D3J, read in the first. -/
def ofRepresentationCategory (X : Deformation.RepresentationCategory.{u, w, w, w, w} Λ k Γ) :
    FiniteProjectiveRepresentation.{u, w, w, w} Λ k Γ where
  base := X.base
  carrier := X.carrier
  action := X.action

/-- A morphism of finite projective representations, read in the second presentation. -/
def toRepresentationCategoryHom {X Y : FiniteProjectiveRepresentation.{u, w, w, w} Λ k Γ}
    (f : FiniteProjectiveRepresentation.Hom X Y) :
    Deformation.RepresentationCategory.Hom (toRepresentationCategory X)
      (toRepresentationCategory Y) where
  base := f.base
  map := f.map
  map_smul := f.map_smul
  equivariant := f.equivariant
  isBaseChange := f.isBaseChange

/-- A morphism in the second presentation, read in the first. -/
def ofRepresentationCategoryHom
    {X Y : Deformation.RepresentationCategory.{u, w, w, w, w} Λ k Γ}
    (f : Deformation.RepresentationCategory.Hom X Y) :
    FiniteProjectiveRepresentation.Hom (ofRepresentationCategory X)
      (ofRepresentationCategory Y) where
  base := f.base
  map := f.map
  map_smul := f.map_smul
  equivariant := f.equivariant
  isBaseChange := f.isBaseChange

/-- Forgetting continuity and changing presentation, as a functor from the category of
continuous finite projective representations of Stacks 0D3K to the second presentation of the
category of Stacks 0D3J. -/
def forgetContinuityPresentation :
    (continuousObjects.{u, w, w, w} Λ k Γ).FullSubcategory ⥤
      Deformation.RepresentationCategory.{u, w, w, w, w} Λ k Γ where
  obj X := toRepresentationCategory X.obj
  map f := toRepresentationCategoryHom f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forgetting continuity and changing presentation is a full functor. -/
theorem full_forgetContinuityPresentation :
    (forgetContinuityPresentation.{u, w} (Λ := Λ) (k := k) (Γ := Γ)).Full where
  map_surjective g := ⟨ObjectProperty.homMk (ofRepresentationCategoryHom g), rfl⟩

/-- Forgetting continuity and changing presentation is a faithful functor. -/
theorem faithful_forgetContinuityPresentation :
    (forgetContinuityPresentation.{u, w} (Λ := Λ) (k := k) (Γ := Γ)).Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    apply FiniteProjectiveRepresentation.Hom.ext
    · exact congrArg (·.base) h
    · exact congrArg (·.map) h

/-- The inclusion of the deformation category of Stacks 0D3K into the deformation category of
Stacks 0D3J: it forgets that the action is continuous and changes presentation. -/
def forgetContinuity (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀) :
    BasedFunctor
      (BasedCategory.ofFunctor (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀))
      (BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀)) where
  toFunctor := Over.post (X := continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)
    (forgetContinuityPresentation.{u, w} (Λ := Λ) (k := k) (Γ := Γ))
  w := rfl

/-- The inclusion of the deformation category of Stacks 0D3K into that of Stacks 0D3J is
faithful. -/
theorem forgetContinuity_faithful (V : Type w) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V)
    (hρ₀ : IsContinuousRepresentation ρ₀) :
    (forgetContinuity (Λ := Λ) V ρ₀ hρ₀).toFunctor.Faithful := by
  let := faithful_forgetContinuityPresentation.{u, w} (Λ := Λ) (k := k) (Γ := Γ)
  change (Over.post (X := continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)
    (forgetContinuityPresentation.{u, w} (Λ := Λ) (k := k) (Γ := Γ))).Faithful
  infer_instance

/-- The inclusion of the deformation category of Stacks 0D3K into that of Stacks 0D3J is
full. -/
theorem forgetContinuity_full (V : Type w) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V)
    (hρ₀ : IsContinuousRepresentation ρ₀) :
    (forgetContinuity (Λ := Λ) V ρ₀ hρ₀).toFunctor.Full := by
  let := faithful_forgetContinuityPresentation.{u, w} (Λ := Λ) (k := k) (Γ := Γ)
  let := full_forgetContinuityPresentation.{u, w} (Λ := Λ) (k := k) (Γ := Γ)
  change (Over.post (X := continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀)
    (forgetContinuityPresentation.{u, w} (Λ := Λ) (k := k) (Γ := Γ))).Full
  infer_instance

/-- A deformation of `(V, ρ₀)` whose action is continuous, read as an object of the
deformation category of Stacks 0D3K. -/
def fiberObjectOfContinuous (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber A)
    (hx : IsContinuousRepresentation x.val.left.action) :
    (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀).Fiber A := by
  let X : (continuousObjects.{u, w, w, w} Λ k Γ).FullSubcategory :=
    ⟨ofRepresentationCategory x.val.left, hx⟩
  let f : X ⟶ continuousSpecialFiber (Λ := Λ) V ρ₀ hρ₀ :=
    ObjectProperty.homMk (ofRepresentationCategoryHom x.val.hom)
  exact ⟨Over.mk f, x.property⟩

/-- A deformation with continuous action, read in the deformation category of Stacks 0D3K and
sent back by the inclusion, is the deformation it started from. -/
theorem forgetContinuity_fiberObjectOfContinuous (V : Type w) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V)
    (hρ₀ : IsContinuousRepresentation ρ₀)
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber A)
    (hx : IsContinuousRepresentation x.val.left.action) :
    (fiberFunctor (forgetContinuity (Λ := Λ) V ρ₀ hρ₀) A).obj
      (fiberObjectOfContinuous V ρ₀ hρ₀ A x hx) = x :=
  Subtype.ext rfl

/-- The isomorphism class of a deformation whose action is continuous lies in the image of the
isomorphism classes of the deformation category of Stacks 0D3K. -/
theorem classOf_mem_range_forgetContinuity (V : Type w) [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ₀ : Representation k Γ V)
    (hρ₀ : IsContinuousRepresentation ρ₀)
    (hcont : IsCofiberedInGroupoids
      (BasedCategory.ofFunctor (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀)).p)
    (hord : IsCofiberedInGroupoids
      (BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀)).p)
    (A : ArtinianLocalAlgCat.{u, w, w} Λ k)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber A)
    (hx : IsContinuousRepresentation x.val.left.action) :
    classOf (BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀)) hord x ∈
      Set.range (mapIsomorphismClasses hcont hord
        (forgetContinuity (Λ := Λ) V ρ₀ hρ₀) A) :=
  ⟨classOf (BasedCategory.ofFunctor (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀)) hcont
      (fiberObjectOfContinuous V ρ₀ hρ₀ A x hx),
    (mapIsomorphismClasses_classOf hcont hord (forgetContinuity (Λ := Λ) V ρ₀ hρ₀) _).trans
      (congrArg (classOf _ hord) (forgetContinuity_fiberObjectOfContinuous V ρ₀ hρ₀ A x hx))⟩

/-! ### Continuity of a deformation and of its associated extension -/

/-- A representation additively isomorphic to a continuous action is continuous. -/
theorem representation_isContinuous_of_addEquiv {R : Type*} [CommSemiring R] {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [DiscreteTopology M] {N : Type*} [AddCommMonoid N] [Module R N] [Module.Finite R N]
    (ρ : Representation R G N) (action : G → M → M)
    (hcont : ∀ z, Continuous (fun γ => action γ z))
    (equiv : M ≃+ N) (hequiv : ∀ γ z, equiv (action γ z) = ρ γ (equiv z)) :
    IsContinuousRepresentation ρ := by
  let : TopologicalSpace N := ⊥
  let : DiscreteTopology N := ⟨rfl⟩
  let : MulAction G N := MulAction.compHom N ρ.asGroupHom
  refine (continuous_representation_iff_continuousSMul R N G ρ.asGroupHom).mpr ⟨?_⟩
  refine continuous_prod_of_discrete_right.mpr fun z => ?_
  exact ((continuous_of_discreteTopology : Continuous equiv).comp (hcont (equiv.symm z))).congr
    fun γ => by
      change equiv (action γ (equiv.symm z)) = ρ γ z
      rw [hequiv, equiv.apply_symm_apply]

/-- If the extension associated to a dual-number deformation has continuous orbit maps then the
deformation is continuous. -/
theorem associatedSelfExtension_isContinuous [IsTopologicalGroup Γ]
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (augmentedDualNumbers (Λ := Λ) (k := k)))
    (M : ModuleCat.{w} (MonoidAlgebra k Γ))
    (f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀) ⟶ M)
    (g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀))
    (hass : IsAssociatedSelfExtension V ρ₀ x M f g)
    (hcont : letI : TopologicalSpace M := ⊥
      ∀ z : M, Continuous (fun γ : Γ => (MonoidAlgebra.single γ (1 : k)) • z)) :
    IsContinuousRepresentation x.val.left.action := by
  obtain ⟨equiv, -, hequiv, -, -⟩ := hass
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  exact representation_isContinuous_of_addEquiv x.val.left.action
    (fun γ z => (MonoidAlgebra.single γ (1 : k)) • z) hcont equiv hequiv

/-- If a dual-number deformation is continuous then the extension associated to it has
continuous orbit maps. -/
theorem associatedSelfExtension_orbit_continuous [IsTopologicalGroup Γ]
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V)
    (x : (deformationCategoryProjection (Λ := Λ) V ρ₀).Fiber
      (augmentedDualNumbers (Λ := Λ) (k := k)))
    (M : ModuleCat.{w} (MonoidAlgebra k Γ))
    (f : (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀) ⟶ M)
    (g : M ⟶ (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := Γ)).functor.obj (Rep.of ρ₀))
    (hass : IsAssociatedSelfExtension V ρ₀ x M f g)
    (hx : IsContinuousRepresentation x.val.left.action) :
    letI : TopologicalSpace M := ⊥
    ∀ z : M, Continuous (fun γ : Γ => (MonoidAlgebra.single γ (1 : k)) • z) := by
  obtain ⟨equiv, -, hequiv, -, -⟩ := hass
  let : TopologicalSpace x.val.left.carrier := ⊥
  let : DiscreteTopology x.val.left.carrier := ⟨rfl⟩
  let : MulAction Γ x.val.left.carrier :=
    MulAction.compHom _ x.val.left.action.asGroupHom
  let : ContinuousSMul Γ x.val.left.carrier :=
    (continuous_representation_iff_continuousSMul
      x.val.left.base x.val.left.carrier Γ x.val.left.action.asGroupHom).mp hx
  intro z
  exact continuous_bot_of_comp_eq equiv.symm
    (show Continuous (fun γ : Γ => x.val.left.action γ (equiv z)) from
      continuous_id.smul continuous_const) fun γ => by rw [← hequiv, equiv.symm_apply_apply]

/-! ### The tangent space as continuous self-extensions -/

/-- A finite-dimensional continuous representation as a continuous discrete module. -/
def continuousModuleOfContinuousRepresentation [IsTopologicalGroup Γ]
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀) :
    Stacks.Injectives.ContinuousModule.{w, w, w} k Γ := by
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  letI : MulAction Γ V := MulAction.compHom V ρ₀.asGroupHom
  letI : ContinuousSMul Γ V :=
    (continuous_representation_iff_continuousSMul k V Γ ρ₀.asGroupHom).mp hρ₀
  exact continuousModuleOfRepOrbits k Γ (Rep.of ρ₀)
    (fun _ => continuous_id.smul continuous_const)

/-- **The tangent space of the deformation category of a finite-dimensional continuous
representation is `Ext¹` of the representation by itself in continuous discrete modules.**

Both sides inject into `Ext¹_{k[Γ]}(V, V)`: the left by the differential of
`forgetContinuity`, which is injective because that functor is fully faithful and `k`-linear by
Stacks 06IJ, and the right by the comparison of the exact fully faithful functor
`continuousModuleToGroupAlgebra`. The images agree because a deformation is continuous exactly
when its associated extension has continuous orbit maps. -/
def tangentSpaceEquivContinuousSelfExt [IsTopologicalGroup Γ]
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀)
    (hpre : IsPredeformationCategory
      (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀))
    (hS2 : SchlessingerConditionS2 (Functor.Elements.π (isomorphismClasses
      (BasedCategory.ofFunctor (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀))
      hpre.cofibered))) :
    let 𝓕 := BasedCategory.ofFunctor (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀)
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
    letI := hasExt_of_enoughInjectives.{w + 1, w, w + 1}
      (Stacks.Injectives.ContinuousModule.{w, w, w} k Γ)
    let M := continuousModuleOfContinuousRepresentation V ρ₀ hρ₀
    artinianTangentSpace Λ k (isomorphismClasses 𝓕 hpre.cofibered) ≃ₗ[k]
      Abelian.Ext M M 1 := by
  let φ := forgetContinuity (Λ := Λ) V ρ₀ hρ₀
  let 𝓕 := BasedCategory.ofFunctor (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀)
  let 𝓖 := BasedCategory.ofFunctor (deformationCategoryProjection (Λ := Λ) V ρ₀)
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hpre⟩
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 hpre.cofibered))) := ⟨hS2⟩
  obtain ⟨hord, hordS2, ordinaryEquiv, hrep, hclass⟩ :=
    Deformation.tangentSpaceEquivSelfExt (Λ := Λ) V ρ₀
  letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨hord⟩
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓖 hord.cofibered))) := ⟨hordS2⟩
  letI := HasExt.standard (ModuleCat.{w} (MonoidAlgebra k Γ))
  letI := hasExt_of_enoughInjectives.{w + 1, w, w + 1}
    (Stacks.Injectives.ContinuousModule.{w, w, w} k Γ)
  letI := continuousModuleToGroupAlgebra_additive.{w, w, w} k Γ
  letI := continuousModuleToGroupAlgebra_linear.{w, w, w} k Γ
  letI := continuousModuleToGroupAlgebra_preservesFiniteLimits.{w, w, w} k Γ
  letI := continuousModuleToGroupAlgebra_preservesFiniteColimits.{w, w, w} k Γ
  letI := forgetContinuity_full (Λ := Λ) V ρ₀ hρ₀
  letI := forgetContinuity_faithful (Λ := Λ) V ρ₀ hρ₀
  let M := continuousModuleOfContinuousRepresentation V ρ₀ hρ₀
  let dφ : artinianTangentSpace Λ k (isomorphismClasses 𝓕 hpre.cofibered) →ₗ[k]
      artinianTangentSpace Λ k (isomorphismClasses 𝓖 hord.cofibered) :=
    IsLinearMap.mk' _ (differential_isLinearMap 𝓕 𝓖 hpre hord hS2 hordS2 φ)
  let tangentMap := ordinaryEquiv.toLinearMap.comp dφ
  let extensionMap := (continuousModuleToGroupAlgebra k Γ).mapExtLinearMap k M M 1
  have htangent : Function.Injective tangentMap :=
    ordinaryEquiv.injective.comp
      (mapIsomorphismClasses_injective hpre.cofibered hord.cofibered φ _)
  have hextension : Function.Injective extensionMap :=
    continuousModuleToGroupAlgebra_mapExt_injective k Γ M M
  have hrange : LinearMap.range tangentMap = LinearMap.range extensionMap := by
    refine Submodule.ext fun ξ => ⟨?_, ?_⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨x, rfl⟩ := classOf_surjective 𝓕 hpre.cofibered _ t
      let y := (fiberFunctor φ _).obj x
      obtain ⟨E, i, p, hzero, hexact, hass⟩ := hrep y
      have hvalue : tangentMap (classOf 𝓕 hpre.cofibered x) = hexact.extClass :=
        (congrArg ordinaryEquiv
            (mapIsomorphismClasses_classOf hpre.cofibered hord.cofibered φ x)).trans
          (hclass y E i p hzero hexact hass)
      obtain ⟨η, hη⟩ := extClass_mem_range_of_orbit_continuous k Γ M M E i p hzero hexact
        (associatedSelfExtension_orbit_continuous V ρ₀ y E i p hass x.val.left.property)
      exact ⟨η, hη.trans hvalue.symm⟩
    · rintro ⟨ξ, rfl⟩
      obtain ⟨x, hx⟩ := classOf_surjective 𝓖 hord.cofibered _
        (ordinaryEquiv.symm (extensionMap ξ))
      obtain ⟨E, i, p, hzero, hexact, hass⟩ := hrep x
      have hvalue : hexact.extClass = extensionMap ξ :=
        (hclass x E i p hzero hexact hass).symm.trans
          ((congrArg ordinaryEquiv hx).trans (ordinaryEquiv.apply_symm_apply _))
      have hcont := (extClass_mem_range_iff_orbit_continuous k Γ M M E i p hzero
        hexact).mp ⟨ξ, hvalue.symm⟩
      obtain ⟨t, ht⟩ := classOf_mem_range_forgetContinuity V ρ₀ hρ₀ hpre.cofibered
        hord.cofibered _ x (associatedSelfExtension_isContinuous V ρ₀ x E i p hass hcont)
      exact ⟨t, (congrArg ordinaryEquiv ht).trans
        ((hclass x E i p hzero hexact hass).trans hvalue)⟩
  exact ((LinearEquiv.ofInjective tangentMap htangent).trans
    (LinearEquiv.ofEq (LinearMap.range tangentMap) (LinearMap.range extensionMap)
      hrange)).trans
    (LinearEquiv.ofInjective extensionMap hextension).symm

/-! ### The tangent space as continuous cohomology -/

/-- The coefficient module of the comparison is `End_k(V)` with the conjugation action: the
dual tensor module `Vᵛ ⊗_k V` of Stacks 0DVE is equivariantly `Representation.linHom ρ₀ ρ₀`. -/
def dualTensorRepEquivLinHom [IsTopologicalGroup Γ]
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀) :
    let M := continuousModuleOfContinuousRepresentation V ρ₀ hρ₀
    letI : Module.Finite k (M.obj.obj.V : Type w) := inferInstanceAs (Module.Finite k V)
    letI : Module.Projective k (M.obj.obj.V : Type w) :=
      inferInstanceAs (Module.Projective k V)
    (Stacks.ContinuousCohomology.rep k Γ
      (Stacks.ContinuousCohomology.dualTensorContinuousModule k Γ M M)).Equiv
        (Representation.linHom ρ₀ ρ₀) :=
  let M := continuousModuleOfContinuousRepresentation V ρ₀ hρ₀
  letI : Module.Finite k (M.obj.obj.V : Type w) := inferInstanceAs (Module.Finite k V)
  letI : Module.Projective k (M.obj.obj.V : Type w) :=
    inferInstanceAs (Module.Projective k V)
  (Stacks.ContinuousCohomology.continuousDualTensor k Γ M M).2.trans
    (Representation.Equiv.dualTensorHom ρ₀ ρ₀)

/-- **Stacks 0DVE in this setting.** `Ext¹` of a finite-dimensional continuous representation
by itself, computed in continuous discrete modules, is the first continuous cohomology of the
dual tensor module `Vᵛ ⊗_k V`. The auxiliary universe of the `Ext`-group is moved from the one
Stacks 0DVT's comparison is stated at down to the morphism universe, which is the one Stacks
0DVE is stated at. -/
def continuousSelfExtEquivCohomology [IsTopologicalGroup Γ]
    [HasDerivedCategory.{d} (Stacks.Injectives.ContinuousModule.{w, w, w} k Γ)]
    [HasDerivedCategory.{d} (ModuleCat.{w} k)]
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀) :
    letI := hasExt_of_enoughInjectives.{w + 1, w, w + 1}
      (Stacks.Injectives.ContinuousModule.{w, w, w} k Γ)
    let M := continuousModuleOfContinuousRepresentation V ρ₀ hρ₀
    letI : Module.Finite k (M.obj.obj.V : Type w) := inferInstanceAs (Module.Finite k V)
    letI : Module.Projective k (M.obj.obj.V : Type w) :=
      inferInstanceAs (Module.Projective k V)
    Abelian.Ext M M 1 ≃ₗ[k]
      (Stacks.ContinuousCohomology.cohomologyFunctor.{d, w, w, w} k Γ 1).obj
        (Stacks.ContinuousCohomology.dualTensorContinuousModule k Γ M M) := by
  letI := hasExt_of_enoughInjectives.{w + 1, w, w + 1}
    (Stacks.Injectives.ContinuousModule.{w, w, w} k Γ)
  letI := Stacks.ContinuousCohomology.hasExt_continuousModule.{w, w, w} k Γ
  let M := continuousModuleOfContinuousRepresentation V ρ₀ hρ₀
  letI : Module.Finite k (M.obj.obj.V : Type w) := inferInstanceAs (Module.Finite k V)
  letI : Module.Projective k (M.obj.obj.V : Type w) :=
    inferInstanceAs (Module.Projective k V)
  exact (Stacks.ExtUniverse.extChgUnivLinearEquivOfHasExt (R := k)
      (hasExt_of_enoughInjectives.{w + 1, w, w + 1}
        (Stacks.Injectives.ContinuousModule.{w, w, w} k Γ))
      (Stacks.ContinuousCohomology.hasExt_continuousModule.{w, w, w} k Γ) M M 1).trans
    (Stacks.ContinuousCohomology.extIsoCohomologyDualTensor.{d, w, w, w} k Γ M M 1)

/-- **Stacks 0DVW, the tangent clause.** For a finite-dimensional continuous representation
`ρ₀ : Γ → GL_k(V)` of a topological group, the tangent space of the deformation category of
Stacks 0D3K — in its natural `k`-vector space structure of Stacks 06IH — is the first
continuous cohomology `H¹(Γ, End_k(V))` of the conjugation action on the endomorphisms of `V`.

The coefficient module is the dual tensor module `Vᵛ ⊗_k V` of Stacks 0DVE, and the second
component of the statement identifies its representation equivariantly with
`Representation.linHom ρ₀ ρ₀`, the conjugation action on `End_k(V)`, so the cohomology on the
right is `H¹(Γ, End_k(V))`.

The proof is the one of Stacks 0DVT: `tangentSpaceEquivContinuousSelfExt` identifies the
tangent space with `Ext¹` of `V` by itself in continuous discrete modules, and Stacks 0DVE turns
that `Ext¹` into continuous cohomology of `Vᵛ ⊗_k V`. -/
@[stacks 0DVW "tangent_space"]
def tangentSpaceEquivContinuousCohomology [IsTopologicalGroup Γ]
    [HasDerivedCategory.{d} (Stacks.Injectives.ContinuousModule.{w, w, w} k Γ)]
    [HasDerivedCategory.{d} (ModuleCat.{w} k)]
    (V : Type w) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ₀ : Representation k Γ V) (hρ₀ : IsContinuousRepresentation ρ₀) :
    let 𝓕 := BasedCategory.ofFunctor (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀)
    let hD := isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
    letI : Fact (SchlessingerConditionS2
        (Functor.Elements.π
          (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
      ⟨Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
        𝓕 hD⟩
    letI := Stacks.ContinuousCohomology.hasExt_continuousModule.{w, w, w} k Γ
    let M := continuousModuleOfContinuousRepresentation V ρ₀ hρ₀
    letI : Module.Finite k (M.obj.obj.V : Type w) := inferInstanceAs (Module.Finite k V)
    letI : Module.Projective k (M.obj.obj.V : Type w) :=
      inferInstanceAs (Module.Projective k V)
    Σ' _ : artinianTangentSpace Λ k
          (isomorphismClasses 𝓕 hD.predeformation.cofibered) ≃ₗ[k]
        (Stacks.ContinuousCohomology.cohomologyFunctor.{d, w, w, w} k Γ 1).obj
          (Stacks.ContinuousCohomology.dualTensorContinuousModule k Γ M M),
      (Stacks.ContinuousCohomology.rep k Γ
        (Stacks.ContinuousCohomology.dualTensorContinuousModule k Γ M M)).Equiv
          (Representation.linHom ρ₀ ρ₀) := by
  let 𝓕 := BasedCategory.ofFunctor (continuousDeformationProjection (Λ := Λ) V ρ₀ hρ₀)
  let hD := isDeformationCategory_continuousDeformationCategory (Λ := Λ) V ρ₀ hρ₀
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hD.predeformation⟩
  letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hD.predeformation.cofibered))) :=
    ⟨Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
      𝓕 hD⟩
  letI := Stacks.ContinuousCohomology.hasExt_continuousModule.{w, w, w} k Γ
  let M := continuousModuleOfContinuousRepresentation V ρ₀ hρ₀
  letI : Module.Finite k (M.obj.obj.V : Type w) := inferInstanceAs (Module.Finite k V)
  letI : Module.Projective k (M.obj.obj.V : Type w) :=
    inferInstanceAs (Module.Projective k V)
  exact ⟨(tangentSpaceEquivContinuousSelfExt (Λ := Λ) V ρ₀ hρ₀ hD.predeformation
      (Deformation.Artin.schlessingerConditionS2_isomorphismClasses_of_isDeformationCategory
        𝓕 hD)).trans (continuousSelfExtEquivCohomology V ρ₀ hρ₀),
    dualTensorRepEquivLinHom V ρ₀ hρ₀⟩

end Deformation.Examples.FiniteProjectiveRepresentation

end
