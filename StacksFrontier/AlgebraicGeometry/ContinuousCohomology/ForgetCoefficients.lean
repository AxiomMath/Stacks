module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.DiscreteTopology

/-!
# Forgetting the coefficient ring in continuous group cohomology

Let `G` be a topological group and `R` a ring. A continuous discrete `R`-`G`-module has an
underlying continuous discrete `G`-module, obtained by restricting scalars along `ℤ → R`, and
continuous group cohomology commutes with this forgetful functor: the `R`-module
`Hⁱ(G, M)` of `Stacks.ContinuousCohomology.cohomologyFunctor` has, as its underlying abelian
group, the group `Hⁱ(G, M)` of `continuousGroupCohomologyFunctor`,
naturally in `M`.

## Main definitions

* `Stacks.ContinuousCohomology.continuousModuleForget` — the functor forgetting the `R`-module
  structure of a continuous discrete `R`-`G`-module.
* `Stacks.ContinuousCohomology.continuousModuleExtendScalars` — its left adjoint
  `M ↦ R ⊗[ℤ] M`, with the adjunction
  `Stacks.ContinuousCohomology.continuousModuleExtendForgetAdj`.
* `Stacks.ContinuousCohomology.flatUnderlyingProperty` — the continuous discrete `G`-modules
  with flat underlying abelian group, which cover every continuous discrete `G`-module.
* `Stacks.ContinuousCohomology.trivialIntegerModule` — `ℤ` with the trivial action, which
  corepresents invariants (`Stacks.ContinuousCohomology.invariantsCorepresentation`).

## Main results

* `Stacks.ContinuousCohomology.continuousModuleCohomologyForgetIso` — continuous group
  cohomology commutes with forgetting the coefficient ring.

## Implementation notes

The comparison is stated for a commutative coefficient ring, which is the generality in which
`Stacks.ContinuousCohomology.cohomologyFunctor` is available: invariants are taken there through
`Rep.invariantsFunctor`, so that the comparison is an isomorphism of `R`-modules rather than of
abelian groups, and `Rep R G` needs `R` commutative. Everything that does not mention the
cohomology functor — the forgetful functor, its exactness and its faithfulness — is proved for
an arbitrary ring.

Both right derived functors are compared through Mathlib's `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`, and transported to the `ℤ`-indexed
`CategoryTheory.Functor.rightDerivedPlus` used by the two cohomology functors by
`Stacks.DerivedIndexing.rightDerivedIso`. The derived category of the `R`-side is a free
instance argument, as in `Stacks.ContinuousCohomology.cohomologyFunctor`; the `ℤ`-side is
pinned to the standard model by
`continuousGroupCohomologyFunctor` itself.

## References

* [Stacks Project, Tag 04JF](https://stacks.math.columbia.edu/tag/04JF)
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR)
* [Stacks Project, Tag 0DVD](https://stacks.math.columbia.edu/tag/0DVD)
-/


@[expose] public noncomputable section

open CategoryTheory Limits ZeroObject Opposite

universe d u v w

namespace Stacks.ContinuousCohomology

attribute [local instance] Stacks.DiscreteModuleTopology.hasForget₂ModuleCatTopCat
  Stacks.DiscreteModuleTopology.actionDiscreteTopology

section Forget

variable (R : Type u) [Ring R] (G : Type v) [Group G] [TopologicalSpace G]

/-- The functor forgetting the `R`-module structure of a continuous discrete `R`-`G`-module:
restriction of scalars along `ℤ → R`. -/
def continuousModuleForget :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G ⥤
      ContinuousGModule.{v, w} G :=
  ObjectProperty.lift _
    (ObjectProperty.lift _
      (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙
        (ModuleCat.restrictScalars (Int.castRingHom R)).mapAction G)
      (fun X => X.obj.property))
    (fun X => X.property)

/-- Forgetting the coefficient ring is additive. -/
instance additive_continuousModuleForget :
    (continuousModuleForget.{u, v, w} R G).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    rfl

/-- The underlying `G`-action on an `R`-module of a continuous discrete `R`-`G`-module. -/
abbrev continuousModuleToAction :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G ⥤ Action (ModuleCat.{w} R) G :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _

end Forget

section Exactness

/-- The inclusion of a full subcategory of an abelian category closed under kernels, cokernels
and finite products preserves finite limits. -/
lemma preservesFiniteLimits_ι {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts] :
    PreservesFiniteLimits (ObjectProperty.ι P) := by
  let _ : ∀ ⦃X Y : P.FullSubcategory⦄ (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) (ObjectProperty.ι P) :=
    fun _ _ f => ObjectProperty.preservesKernels_ι P f
  exact Functor.preservesFiniteLimits_of_preservesKernels _

/-- The inclusion of a full subcategory of an abelian category closed under kernels, cokernels
and finite products preserves finite colimits. -/
lemma preservesFiniteColimits_ι {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderKernels]
    [P.IsClosedUnderCokernels] [P.IsClosedUnderFiniteProducts] :
    PreservesFiniteColimits (ObjectProperty.ι P) := by
  let _ : ∀ ⦃X Y : P.FullSubcategory⦄ (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) (ObjectProperty.ι P) :=
    fun _ _ f => ObjectProperty.preservesCokernels_ι P f
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

end Exactness

section Underlying

variable (G : Type v) [Group G] [TopologicalSpace G]

/-- The underlying `G`-action on an abelian group of a continuous discrete `G`-module. -/
abbrev continuousGModuleToAction :
    ContinuousGModule.{v, w} G ⥤ Action (ModuleCat.{w} ℤ) G :=
  ObjectProperty.ι _ ⋙ ObjectProperty.ι _

/-- The underlying abelian group of a continuous discrete `G`-module. -/
abbrev continuousGModuleUnderlying :
    ContinuousGModule.{v, w} G ⥤ ModuleCat.{w} ℤ :=
  continuousGModuleToAction.{v, w} G ⋙ Action.forget (ModuleCat.{w} ℤ) G

/-- Passing to the underlying `G`-action is left exact. -/
instance preservesFiniteLimits_continuousGModuleToAction :
    PreservesFiniteLimits (continuousGModuleToAction.{v, w} G) := by
  change PreservesFiniteLimits
    (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{w} ℤ) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} ℤ) (G := G)))
  have := preservesFiniteLimits_ι (ContAction.IsDiscrete (V := ModuleCat.{w} ℤ) (G := G))
  have := preservesFiniteLimits_ι (Action.IsContinuous (V := ModuleCat.{w} ℤ) (G := G))
  exact comp_preservesFiniteLimits _ _

/-- Passing to the underlying `G`-action is right exact. -/
instance preservesFiniteColimits_continuousGModuleToAction :
    PreservesFiniteColimits (continuousGModuleToAction.{v, w} G) := by
  change PreservesFiniteColimits
    (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{w} ℤ) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} ℤ) (G := G)))
  have := preservesFiniteColimits_ι (ContAction.IsDiscrete (V := ModuleCat.{w} ℤ) (G := G))
  have := preservesFiniteColimits_ι (Action.IsContinuous (V := ModuleCat.{w} ℤ) (G := G))
  exact comp_preservesFiniteColimits _ _

/-- Passing to the underlying abelian group is left exact. -/
instance preservesFiniteLimits_continuousGModuleUnderlying :
    PreservesFiniteLimits (continuousGModuleUnderlying.{v, w} G) :=
  comp_preservesFiniteLimits _ _

/-- Passing to the underlying abelian group is right exact. -/
instance preservesFiniteColimits_continuousGModuleUnderlying :
    PreservesFiniteColimits (continuousGModuleUnderlying.{v, w} G) :=
  comp_preservesFiniteColimits _ _

/-- A map of continuous discrete `G`-modules is determined by the underlying group map. -/
instance faithful_continuousGModuleUnderlying :
    (continuousGModuleUnderlying.{v, w} G).Faithful :=
  inferInstanceAs (Functor.Faithful
    (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ Action.forget (ModuleCat.{w} ℤ) G))

end Underlying

section ForgetExact

variable (R : Type u) [Ring R] (G : Type v) [Group G] [TopologicalSpace G]

/-- The underlying abelian group of a continuous discrete `R`-`G`-module. -/
abbrev continuousModuleUnderlyingZ :
    Stacks.Injectives.ContinuousModule.{u, v, w} R G ⥤ ModuleCat.{w} ℤ :=
  continuousModuleForget.{u, v, w} R G ⋙ continuousGModuleUnderlying.{v, w} G

/-- A map of continuous discrete `R`-`G`-modules is determined by the underlying map of
actions. -/
instance faithful_continuousModuleToAction :
    (continuousModuleToAction.{u, v, w} R G).Faithful := by
  change (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)) ⋙
    ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} R) (G := G))).Faithful
  infer_instance

/-- A map of continuous discrete `R`-`G`-modules is determined by the underlying group map. -/
instance faithful_continuousModuleUnderlyingZ :
    (continuousModuleUnderlyingZ.{u, v, w} R G).Faithful := by
  change (continuousModuleToAction.{u, v, w} R G ⋙
    ((ModuleCat.restrictScalars.{w} (Int.castRingHom R)).mapAction G ⋙
      Action.forget (ModuleCat.{w} ℤ) G)).Faithful
  infer_instance

/-- Restriction of scalars along `ℤ → R` is left exact. -/
instance preservesFiniteLimits_restrictScalars :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{w} (Int.castRingHom R)) := by
  let _ : ∀ ⦃X Y : ModuleCat.{w} R⦄ (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0)
        (ModuleCat.restrictScalars.{w} (Int.castRingHom R)) := fun _ _ _ => inferInstance
  exact Functor.preservesFiniteLimits_of_preservesKernels _

/-- Restriction of scalars along `ℤ → R` is right exact. -/
instance preservesFiniteColimits_restrictScalars :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{w} (Int.castRingHom R)) := by
  let _ : ∀ ⦃X Y : ModuleCat.{w} R⦄ (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0)
        (ModuleCat.restrictScalars.{w} (Int.castRingHom R)) := fun _ _ _ => inferInstance
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

/-- Passing to the underlying `R`-linear `G`-action is left exact. -/
instance preservesFiniteLimits_continuousModuleToAction :
    PreservesFiniteLimits (continuousModuleToAction.{u, v, w} R G) := by
  change PreservesFiniteLimits
    (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)))
  have := preservesFiniteLimits_ι (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G))
  have := preservesFiniteLimits_ι (Action.IsContinuous (V := ModuleCat.{w} R) (G := G))
  exact comp_preservesFiniteLimits _ _

/-- Passing to the underlying `R`-linear `G`-action is right exact. -/
instance preservesFiniteColimits_continuousModuleToAction :
    PreservesFiniteColimits (continuousModuleToAction.{u, v, w} R G) := by
  change PreservesFiniteColimits
    (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)))
  have := preservesFiniteColimits_ι (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G))
  have := preservesFiniteColimits_ι (Action.IsContinuous (V := ModuleCat.{w} R) (G := G))
  exact comp_preservesFiniteColimits _ _

/-- Passing to the underlying abelian group of an `R`-`G`-module is left exact. -/
instance preservesFiniteLimits_continuousModuleUnderlyingZ :
    PreservesFiniteLimits (continuousModuleUnderlyingZ.{u, v, w} R G) := by
  change PreservesFiniteLimits (continuousModuleToAction.{u, v, w} R G ⋙
    ((ModuleCat.restrictScalars.{w} (Int.castRingHom R)).mapAction G ⋙
      Action.forget (ModuleCat.{w} ℤ) G))
  exact comp_preservesFiniteLimits _ _

/-- Passing to the underlying abelian group of an `R`-`G`-module is right exact. -/
instance preservesFiniteColimits_continuousModuleUnderlyingZ :
    PreservesFiniteColimits (continuousModuleUnderlyingZ.{u, v, w} R G) := by
  change PreservesFiniteColimits (continuousModuleToAction.{u, v, w} R G ⋙
    ((ModuleCat.restrictScalars.{w} (Int.castRingHom R)).mapAction G ⋙
      Action.forget (ModuleCat.{w} ℤ) G))
  exact comp_preservesFiniteColimits _ _

/-- A diagram of continuous discrete `G`-modules is a limit as soon as the underlying diagram
of abelian groups is. -/
instance reflectsFiniteLimits_continuousGModuleUnderlying :
    ReflectsFiniteLimits (continuousGModuleUnderlying.{v, w} G) :=
  inferInstanceAs (ReflectsFiniteLimits
    (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ Action.forget (ModuleCat.{w} ℤ) G))

/-- A diagram of continuous discrete `G`-modules is a colimit as soon as the underlying diagram
of abelian groups is. -/
instance reflectsFiniteColimits_continuousGModuleUnderlying :
    ReflectsFiniteColimits (continuousGModuleUnderlying.{v, w} G) :=
  inferInstanceAs (ReflectsFiniteColimits
    (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ Action.forget (ModuleCat.{w} ℤ) G))

/-- Forgetting the coefficient ring is left exact. -/
instance preservesFiniteLimits_continuousModuleForget :
    PreservesFiniteLimits (continuousModuleForget.{u, v, w} R G) :=
  preservesFiniteLimits_of_reflects_of_preserves _ (continuousGModuleUnderlying.{v, w} G)

/-- Forgetting the coefficient ring is right exact. -/
instance preservesFiniteColimits_continuousModuleForget :
    PreservesFiniteColimits (continuousModuleForget.{u, v, w} R G) :=
  preservesFiniteColimits_of_reflects_of_preserves _ (continuousGModuleUnderlying.{v, w} G)

/-- A map of continuous discrete `R`-`G`-modules is determined by the underlying map of
continuous discrete `G`-modules. -/
instance faithful_continuousModuleForget :
    (continuousModuleForget.{u, v, w} R G).Faithful :=
  Functor.Faithful.of_comp (continuousModuleForget.{u, v, w} R G)
    (continuousGModuleUnderlying.{v, w} G)

end ForgetExact

section ExtendScalars

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G]

/-- Each orbit map of a continuous action on a module with the discrete topology is continuous. -/
private lemma continuous_action_apply (X : Action (ModuleCat.{w} ℤ) G)
    (hX : Action.IsContinuous X) (x : X.V) :
    Continuous fun g : G => (forget₂ (ModuleCat.{w} ℤ) TopCat).map (X.ρ g) x :=
  (continuous_prod_of_discrete_right.mp (Action.isContinuous_def X |>.mp hX)) x

/-- Extension of scalars `M ↦ R ⊗[ℤ] M` along `ℤ → R`, applied to a `G`-action. -/
abbrev actionExtendScalars :
    Action (ModuleCat.{max u v w} ℤ) G ⥤ Action (ModuleCat.{max u v w} R) G :=
  (ModuleCat.extendScalars (Int.castRingHom R)).mapAction G

/-- Extension of scalars along `ℤ → R` keeps a continuous action continuous. -/
lemma actionExtendScalars_isContinuous (X : Action (ModuleCat.{max u v w} ℤ) G)
    (hX : Action.IsContinuous X) :
    Action.IsContinuous ((actionExtendScalars.{u, v, w} R G).obj X) := by
  let _ : Add ((forget₂ (ModuleCat.{max u v w} R) TopCat).obj
      ((actionExtendScalars.{u, v, w} R G).obj X).V) :=
    ⟨fun a b => @Add.add _ (inferInstance :
      Add ((ModuleCat.extendScalars (Int.castRingHom R)).obj X.V)) a b⟩
  have : DiscreteTopology ((forget₂ (ModuleCat.{max u v w} R) TopCat).obj
      ((actionExtendScalars.{u, v, w} R G).obj X).V) := ⟨rfl⟩
  have : ContinuousAdd ((forget₂ (ModuleCat.{max u v w} R) TopCat).obj
      ((actionExtendScalars.{u, v, w} R G).obj X).V) := ⟨continuous_of_discreteTopology⟩
  rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact continuous_const
  | tmul a m =>
    have hm := continuous_action_apply.{v, max u v w} G X hX m
    let hmap : (forget₂ (Action (ModuleCat.{max u v w} ℤ) G) TopCat).obj X →
        (forget₂ (Action (ModuleCat.{max u v w} R) G) TopCat).obj
          ((actionExtendScalars.{u, v, w} R G).obj X) := fun y => a ⊗ₜ y
    exact ((continuous_of_discreteTopology (f := hmap)).comp hm).congr fun _ => rfl
  | add x y hx hy =>
    refine (hx.add hy).congr fun g => Eq.symm ?_
    exact map_add (((actionExtendScalars.{u, v, w} R G).obj X).ρ g).hom x y

/-- Extension of scalars `M ↦ R ⊗[ℤ] M` on continuous discrete modules, the left adjoint of
`Stacks.ContinuousCohomology.continuousModuleForget`. -/
def continuousModuleExtendScalars :
    ContinuousGModule.{v, max u v w} G ⥤
      Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G :=
  ObjectProperty.lift _
    (ObjectProperty.lift _
      (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ actionExtendScalars.{u, v, w} R G)
      (fun X => actionExtendScalars_isContinuous R G X.obj.obj X.obj.property))
    (fun _ => ⟨rfl⟩)

/-- An adjunction between two categories induces an adjunction between the categories of
`H`-actions in them. -/
def adjunctionMapAction {V W : Type*} [Category* V] [Category* W]
    {L : V ⥤ W} {T : W ⥤ V} (adj : L ⊣ T) (H : Type*) [Monoid H] :
    L.mapAction H ⊣ T.mapAction H :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨adj.homEquiv X.V Y.V f.hom,
            fun g => (adj.homEquiv_naturality_left (X.ρ g) f.hom).symm.trans
              ((congrArg (adj.homEquiv X.V Y.V) (f.comm g)).trans
                (adj.homEquiv_naturality_right f.hom (Y.ρ g)))⟩
          invFun := fun f => ⟨(adj.homEquiv X.V Y.V).symm f.hom,
            fun g => (adj.homEquiv_naturality_left_symm (X.ρ g) f.hom).symm.trans
              ((congrArg (adj.homEquiv X.V Y.V).symm (f.comm g)).trans
                (adj.homEquiv_naturality_right_symm f.hom (Y.ρ g)))⟩
          left_inv := fun _ => Action.hom_ext _ _ ((adj.homEquiv X.V Y.V).symm_apply_apply _)
          right_inv := fun _ => Action.hom_ext _ _ ((adj.homEquiv X.V Y.V).apply_symm_apply _) }
      homEquiv_naturality_left_symm := fun f g =>
        Action.hom_ext _ _ (adj.homEquiv_naturality_left_symm f.hom g.hom)
      homEquiv_naturality_right := fun f g =>
        Action.hom_ext _ _ (adj.homEquiv_naturality_right f.hom g.hom) }

/-- Extension of scalars along `ℤ → R` is left adjoint to restriction of scalars, on
`G`-actions. -/
def actionExtendRestrictAdj :
    actionExtendScalars.{u, v, w} R G ⊣
      (ModuleCat.restrictScalars.{max u v w} (Int.castRingHom R)).mapAction G :=
  adjunctionMapAction (ModuleCat.extendRestrictScalarsAdj.{max u v w} (Int.castRingHom R)) G

/-- **Extension of scalars is left adjoint to forgetting the coefficient ring.** -/
def continuousModuleExtendForgetAdj :
    continuousModuleExtendScalars.{u, v, w} R G ⊣
      continuousModuleForget.{u, v, max u v w} R G :=
  Adjunction.restrictFullyFaithful (iC := continuousGModuleToAction.{v, max u v w} G)
    (iD := continuousModuleToAction.{u, v, max u v w} R G) (actionExtendRestrictAdj.{u, v, w} R G)
    ((ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _))
    ((ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _))
    (Iso.refl _) (Iso.refl _)

/-- Extension of scalars is additive. -/
instance additive_continuousModuleExtendScalars :
    (continuousModuleExtendScalars.{u, v, w} R G).Additive :=
  (continuousModuleExtendForgetAdj.{u, v, w} R G).left_adjoint_additive

end ExtendScalars

section FlatCover

variable (G : Type v) [Group G] [TopologicalSpace G]

/-- The free abelian group on the underlying set of a `G`-action, with the induced permutation
action. -/
def freeAction (X : Action (ModuleCat.{w} ℤ) G) : Action (ModuleCat.{w} ℤ) G where
  V := ModuleCat.of ℤ (X.V →₀ ℤ)
  ρ :=
    { toFun := fun g => ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ fun x => (X.ρ g).hom x)
      map_one' := by
        apply ModuleCat.hom_ext
        ext f x
        simp [Finsupp.lmapDomain_apply, X.ρ.map_one]
      map_mul' := by
        intro g h
        apply ModuleCat.hom_ext
        ext f x
        simp [Finsupp.lmapDomain_apply, X.ρ.map_mul, End.mul_def] }

/-- The augmentation of the free action on the underlying set: a formal sum of elements goes to
its actual sum. -/
def freeActionAugmentation (X : Action (ModuleCat.{w} ℤ) G) : freeAction G X ⟶ X where
  hom := ModuleCat.ofHom (Finsupp.linearCombination ℤ fun x : X.V => x)
  comm := by
    intro g
    apply ModuleCat.hom_ext
    ext f
    change (Finsupp.linearCombination ℤ (fun x : X.V => x))
        ((Finsupp.lmapDomain ℤ ℤ (fun x => (X.ρ g).hom x)) f) =
      (X.ρ g).hom ((Finsupp.linearCombination ℤ (fun x : X.V => x)) f)
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single a n =>
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
        Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      exact (LinearMap.map_smul (ModuleCat.Hom.hom (X.ρ g)) n a).symm

/-- The free action on the underlying set of a continuous action is continuous. -/
lemma freeAction_isContinuous (X : Action (ModuleCat.{w} ℤ) G)
    (hX : Action.IsContinuous X) : Action.IsContinuous (freeAction.{v, w} G X) := by
  let _ : TopologicalSpace (X.V : Type w) := ⊥
  have : DiscreteTopology (X.V : Type w) := ⟨rfl⟩
  let _ : TopologicalSpace ((X.V : Type w) →₀ ℤ) := ⊥
  have : DiscreteTopology ((X.V : Type w) →₀ ℤ) := ⟨rfl⟩
  let _ : TopologicalSpace ((freeAction.{v, w} G X).V : Type w) := ⊥
  have : DiscreteTopology ((freeAction.{v, w} G X).V : Type w) := ⟨rfl⟩
  rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
  intro f
  show Continuous fun g : G => ((freeAction.{v, w} G X).ρ g).hom f
  induction f using Finsupp.induction_linear with
  | zero => exact continuous_const
  | add f₁ f₂ hf₁ hf₂ =>
    exact (hf₁.add hf₂).congr fun g => (((freeAction.{v, w} G X).ρ g).hom.map_add f₁ f₂).symm
  | single x n =>
    have hs : Continuous fun g : G =>
        (Finsupp.single ((X.ρ g).hom x) n : (freeAction.{v, w} G X).V) :=
      (continuous_of_discreteTopology (f := fun y : X.V => (Finsupp.single y n : X.V →₀ ℤ))).comp
        (continuous_action_apply.{v, w} G X hX x)
    exact hs.congr fun g => (Finsupp.mapDomain_single (M := ℤ)).symm

/-- The free continuous discrete `G`-module on the underlying set of a continuous discrete
`G`-module. -/
def flatCoverAction (X : ContinuousGModule.{v, w} G) :
    ContinuousGModule.{v, w} G :=
  ⟨⟨freeAction.{v, w} G X.obj.obj,
    freeAction_isContinuous.{v, w} G X.obj.obj X.obj.property⟩, ⟨rfl⟩⟩

/-- The augmentation of the free cover, as a map of continuous discrete `G`-modules. -/
def flatCoverActionAugmentation
    (X : ContinuousGModule.{v, w} G) : flatCoverAction.{v, w} G X ⟶ X :=
  ObjectProperty.homMk (ObjectProperty.homMk (freeActionAugmentation.{v, w} G X.obj.obj))

/-- The augmentation of the free cover is an epimorphism. -/
lemma flatCoverActionAugmentation_epi
    (X : ContinuousGModule.{v, w} G) :
    Epi (flatCoverActionAugmentation.{v, w} G X) := by
  have hs : Function.Surjective (freeActionAugmentation.{v, w} G X.obj.obj).hom.hom := by
    intro x
    refine ⟨Finsupp.single x 1, ?_⟩
    show Finsupp.linearCombination ℤ (fun y : X.obj.obj.V => y) (Finsupp.single x 1) = x
    rw [Finsupp.linearCombination_single]
    exact (Int.cast_smul_eq_zsmul (R := ℤ) (1 : ℤ) x).trans (one_zsmul x)
  have he : Epi (freeActionAugmentation.{v, w} G X.obj.obj) := by
    apply (Action.forget (ModuleCat.{w} ℤ) G).epi_of_epi_map
    exact (ModuleCat.epi_iff_surjective _).2 hs
  exact (ObjectProperty.ι _).epi_of_epi_map ((ObjectProperty.ι _).epi_of_epi_map he)

/-- The underlying abelian group of the free cover is flat over `ℤ`. -/
lemma flatCoverAction_flat (X : ContinuousGModule.{v, w} G) :
    Module.Flat ℤ ((flatCoverAction.{v, w} G X).obj.obj.V) := by
  show Module.Flat ℤ (X.obj.obj.V →₀ ℤ)
  exact Module.Flat.finsupp _

/-- Continuous discrete `G`-modules whose underlying abelian group is flat over `ℤ`, i.e.
torsion free. -/
def flatUnderlyingProperty :
    ObjectProperty (ContinuousGModule.{v, w} G) :=
  fun X => Module.Flat ℤ X.obj.obj.V

/-- Every continuous discrete `G`-module is covered by one with flat underlying group. -/
lemma flatUnderlyingProperty_epi_cover
    (X : ContinuousGModule.{v, w} G) :
    ∃ (Y : ContinuousGModule.{v, w} G)
      (f : Y ⟶ X), flatUnderlyingProperty.{v, w} G Y ∧ Epi f :=
  ⟨flatCoverAction.{v, w} G X, flatCoverActionAugmentation.{v, w} G X,
    flatCoverAction_flat.{v, w} G X, flatCoverActionAugmentation_epi.{v, w} G X⟩

/-- A subobject of a continuous discrete `G`-module with flat underlying group again has flat
underlying group. -/
lemma flatUnderlyingProperty_subobject
    {X Y : ContinuousGModule.{v, w} G} (f : X ⟶ Y) [Mono f]
    (hY : flatUnderlyingProperty.{v, w} G Y) : flatUnderlyingProperty.{v, w} G X := by
  show Module.Flat ℤ X.obj.obj.V
  have : Module.Flat ℤ Y.obj.obj.V := hY
  have : Module.IsTorsionFree ℤ Y.obj.obj.V := Module.Flat.isTorsionFree
  have hf : Function.Injective ((continuousGModuleUnderlying.{v, w} G).map f).hom :=
    (ModuleCat.mono_iff_injective _).mp (Functor.map_mono _ f)
  have : Module.IsTorsionFree ℤ X.obj.obj.V :=
    Function.Injective.moduleIsTorsionFree f.hom.hom.hom.hom hf
      fun r x => (f.hom.hom.hom.hom).map_smul r x
  infer_instance

end FlatCover

section Acyclicity

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G]

/-- **Extension of scalars is left exact on sequences with flat quotient.** If a short exact
sequence of continuous discrete `G`-modules has flat third term, then `R ⊗[ℤ] -` keeps its
first map a monomorphism. -/
lemma continuousModuleExtendScalars_map_mono_of_flat
    (S : ShortComplex (ContinuousGModule.{v, max u v w} G))
    (hS : S.ShortExact) (hflat : flatUnderlyingProperty.{v, max u v w} G S.X₃) :
    Mono ((continuousModuleExtendScalars.{u, v, w} R G).map S.f) := by
  have hT : (S.map (continuousGModuleUnderlying.{v, max u v w} G)).ShortExact :=
    hS.map_of_exact _
  have hf : Function.Injective (S.map (continuousGModuleUnderlying.{v, max u v w} G)).f.hom :=
    (ModuleCat.mono_iff_injective _).mp hT.mono_f
  have hg : Function.Surjective (S.map (continuousGModuleUnderlying.{v, max u v w} G)).g.hom :=
    (ModuleCat.epi_iff_surjective _).mp hT.epi_g
  have hexact :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hT.exact
  have hflatT : Module.Flat ℤ (S.map (continuousGModuleUnderlying.{v, max u v w} G)).X₃ := hflat
  have hlin := LinearMap.lTensor_injective_of_exact_of_flat _ hg _ hf hexact
    ((ModuleCat.restrictScalars (Int.castRingHom R)).obj (ModuleCat.of R R))
  have hmono : Mono ((continuousModuleUnderlyingZ.{u, v, max u v w} R G).map
      ((continuousModuleExtendScalars.{u, v, w} R G).map S.f)) :=
    (ModuleCat.mono_iff_injective _).2 hlin
  exact (continuousModuleUnderlyingZ.{u, v, max u v w} R G).mono_of_mono_map hmono

end Acyclicity

section Corepresentation

/-- The identification of `ULift ℤ` with `ℤ` as a `ℤ`-module. -/
abbrev uliftIntEquiv : ULift.{w} ℤ ≃ₗ[ℤ] ℤ := ULift.moduleEquiv

/-- Multiplication by a vector of a `ℤ`-module, as a `ℤ`-linear map out of `ULift ℤ`. -/
def uliftIntSpan (N : Type w) [AddCommGroup N] [Module ℤ N] (y : N) :
    ULift.{w} ℤ →ₗ[ℤ] N :=
  (LinearMap.toSpanSingleton ℤ N y).comp (uliftIntEquiv.{w}).toLinearMap

/-- A linear map carries multiplication by a vector to multiplication by its image. -/
lemma uliftIntSpan_map (N P : Type w) [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (ψ : N →ₗ[ℤ] P) (y : N) (n : ULift.{w} ℤ) :
    ψ (uliftIntSpan N y n) = uliftIntSpan P (ψ y) n := by
  simp [uliftIntSpan, LinearMap.toSpanSingleton_apply]

/-- Multiplication by a vector commutes with an endomorphism fixing it. -/
lemma uliftIntSpan_fixed (N : Type w) [AddCommGroup N] [Module ℤ N]
    (φ : N →ₗ[ℤ] N) (y : N) (hy : φ y = y) (n : ULift.{w} ℤ) :
    φ (uliftIntSpan N y n) = uliftIntSpan N y n := by
  rw [uliftIntSpan_map N N φ y n, hy]

/-- Multiplication by a vector sends `1` to that vector. -/
lemma uliftIntSpan_up_one (N : Type w) [AddCommGroup N] [Module ℤ N] (y : N) :
    uliftIntSpan N y (ULift.up 1) = y :=
  LinearMap.toSpanSingleton_apply_one ℤ N y

/-- Multiplication by a vector is additive in the vector. -/
lemma uliftIntSpan_add (N : Type w) [AddCommGroup N] [Module ℤ N] (y z : N)
    (n : ULift.{w} ℤ) :
    uliftIntSpan N (y + z) n = uliftIntSpan N y n + uliftIntSpan N z n := by
  simp [uliftIntSpan, LinearMap.toSpanSingleton_apply, smul_add]

/-- Multiplication by `1` is the identity of `ULift ℤ`. -/
lemma uliftIntSpan_one (n : ULift.{w} ℤ) :
    uliftIntSpan (ULift.{w} ℤ) (ULift.up 1) n = n := by
  apply ULift.ext
  simp [uliftIntSpan, LinearMap.toSpanSingleton_apply]

/-- A `ℤ`-linear map out of `ULift ℤ` is multiplication by the image of `1`. -/
lemma uliftIntSpan_eq (N : Type w) [AddCommGroup N] [Module ℤ N]
    (φ : ULift.{w} ℤ →ₗ[ℤ] N) (n : ULift.{w} ℤ) :
    uliftIntSpan N (φ (ULift.up 1)) n = φ n := by
  rw [← uliftIntSpan_map (ULift.{w} ℤ) N φ (ULift.up 1) n, uliftIntSpan_one]

variable (G : Type v) [Group G] [TopologicalSpace G]

/-- `ℤ` with the trivial `G`-action, as a continuous discrete `G`-module. -/
def trivialIntegerModule : ContinuousGModule.{v, w} G :=
  ⟨⟨Action.trivial G (ModuleCat.of.{w} ℤ (ULift.{w} ℤ)), by
      rw [Action.isContinuous_def, continuous_prod_of_discrete_right]
      exact fun _ => continuous_const⟩, ⟨rfl⟩⟩

/-- An invariant vector is fixed by every group element. -/
lemma rho_apply_invariant {M : ContinuousGModule.{v, w} G}
    (x : (continuousGModuleInvariants.{v, w} G).obj M) (g : G) :
    (M.obj.obj.ρ g).hom x.val = x.val := x.property g

/-- The morphism of continuous discrete `G`-modules out of the trivial module `ℤ` given by
multiplication by an invariant vector. -/
def invariantHom {M : ContinuousGModule.{v, w} G}
    (x : (continuousGModuleInvariants.{v, w} G).obj M) :
    trivialIntegerModule.{v, w} G ⟶ M :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (uliftIntSpan (M.obj.obj.V : Type w) x.val)
      comm := fun g => ModuleCat.hom_ext (LinearMap.ext fun n =>
        (uliftIntSpan_fixed (M.obj.obj.V : Type w) (M.obj.obj.ρ g).hom x.val
          (rho_apply_invariant G x g) n).symm) })

/-- The invariants of a continuous discrete `G`-module `M` are additively equivalent to the
morphisms from the trivial module `ℤ` to `M`, an invariant vector `x` corresponding to
multiplication by `x`. -/
def invariantsHomAddEquiv (M : ContinuousGModule.{v, w} G) :
    (continuousGModuleInvariants.{v, w} G).obj M ≃+
      (trivialIntegerModule.{v, w} G ⟶ M) where
  toFun x := invariantHom.{v, w} G x
  invFun f := ⟨f.hom.hom.hom.hom (ULift.up 1), fun g =>
    (ConcreteCategory.congr_hom (f.hom.hom.comm g) (ULift.up 1)).symm⟩
  left_inv x := Subtype.ext (uliftIntSpan_up_one (M.obj.obj.V : Type w) x.val)
  right_inv f := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun n =>
      uliftIntSpan_eq (M.obj.obj.V : Type w) f.hom.hom.hom.hom n
  map_add' x y := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun n =>
      uliftIntSpan_add (M.obj.obj.V : Type w) x.val y.val n

/-- Taking invariants of a continuous discrete `G`-module is corepresented by the trivial
module `ℤ`, naturally in the module. -/
def invariantsCorepresentation :
    continuousGModuleInvariants.{v, w} G ≅
      preadditiveCoyoneda.obj (op (trivialIntegerModule.{v, w} G)) :=
  NatIso.ofComponents (fun M => (invariantsHomAddEquiv.{v, w} G M).toAddCommGrpIso)
    (fun {M N} f => by
      ext x
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun n =>
        (uliftIntSpan_map (M.obj.obj.V : Type w) (N.obj.obj.V : Type w)
          f.hom.hom.hom.hom x.val n).symm)

end Corepresentation

section Comparison

variable (R : Type u) [CommRing R] (G : Type v) [Group G] [TopologicalSpace G]

/-- The `R`-module of invariants of a continuous discrete `R`-`G`-module, read as an abelian
group, is the group of invariants of the underlying continuous discrete `G`-module. -/
def invariantsForgetIso :
    continuousModuleInvariants.{u, v, max u v w} R G ⋙
        forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w} ≅
      continuousModuleForget.{u, v, max u v w} R G ⋙
        continuousGModuleInvariants.{v, max u v w} G :=
  NatIso.ofComponents
    (fun _ => by
      change AddCommGrpCat.of _ ≅ AddCommGrpCat.of _
      exact Iso.refl _)
    (fun _ => by
      ext _
      rfl)

/-- Continuous group cohomology of continuous discrete `R`-`G`-modules commutes, naturally in the
module, with forgetting the `R`-module structure. -/
@[stacks 0DVD]
def continuousModuleCohomologyForgetIso [IsTopologicalGroup G]
    [HasDerivedCategory.{d} (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)]
    [HasDerivedCategory.{d} (ModuleCat.{max u v w} R)] (i : ℕ) :
    cohomologyFunctor.{d, u, v, w} R G i ⋙
        forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w} ≅
      continuousModuleForget.{u, v, max u v w} R G ⋙
        continuousGroupCohomologyFunctor.{v, max u v w} G i := by
  letI := HasDerivedCategory.standard
    (ContinuousGModule.{v, max u v w} G)
  letI := HasDerivedCategory.standard AddCommGrpCat.{max u v w}
  letI : EnoughInjectives (ContinuousGModule.{v, max u v w} G) :=
    continuousGModuleEnoughInjectives.{v, max u v w} G
  letI : HasExt.{max u v w}
      (ContinuousGModule.{v, max u v w} G) :=
    hasExt_of_enoughInjectives.{max u v w, max u v w, max (max (u + 1) (v + 1)) (w + 1)}
      (ContinuousGModule.{v, max u v w} G)
  letI : HasExt.{max u v w}
      (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) :=
    hasExt_of_enoughInjectives.{max u v w, max u v w, max (max (u + 1) (v + 1)) (w + 1)}
      (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)
  have : PreservesFiniteLimits
      (continuousGModuleInvariants.{v, max u v w} G) :=
    preservesFiniteLimits_of_natIso
      (invariantsCorepresentation.{v, max u v w} G).symm
  have hsub : ∀ {X Y : ContinuousGModule.{v, max u v w} G}
      (f : X ⟶ Y), Mono f → flatUnderlyingProperty.{v, max u v w} G Y →
        flatUnderlyingProperty.{v, max u v w} G X := by
    intro X Y f hf hY
    have := hf
    exact flatUnderlyingProperty_subobject.{v, max u v w} G f hY
  have hvan : ∀ (I : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) [Injective I]
      (n : ℕ) (e : Abelian.Ext (trivialIntegerModule.{v, max u v w} G)
        ((continuousModuleForget.{u, v, max u v w} R G).obj I) (n + 1)), e = 0 := by
    intro I _ n e
    exact ModuleSheafCohomology.ext_eq_zero_of_adjunction
      (continuousModuleExtendScalars.{u, v, w} R G)
      (continuousModuleForget.{u, v, max u v w} R G)
      (continuousModuleExtendForgetAdj.{u, v, w} R G)
      (flatUnderlyingProperty.{v, max u v w} G) hsub
      (flatUnderlyingProperty_epi_cover.{v, max u v w} G)
      (continuousModuleExtendScalars_map_mono_of_flat.{u, v, w} R G) I n _
      (Module.Flat.of_linearEquiv uliftIntEquiv.{max u v w}) e
  exact
    Functor.isoWhiskerRight
        (Stacks.DerivedIndexing.rightDerivedIso
          (continuousModuleInvariants.{u, v, max u v w} R G) i).symm
        (forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}) ≪≫
      (Functor.rightDerivedCompIso (continuousModuleInvariants.{u, v, max u v w} R G)
        (forget₂ (ModuleCat.{max u v w} R) AddCommGrpCat.{max u v w}) i).symm ≪≫
      Functor.rightDerivedIsoOfNatIso (invariantsForgetIso.{u, v, w} R G) i ≪≫
      ModuleSheafCohomology.comparisonIso
        (continuousModuleForget.{u, v, max u v w} R G)
        (continuousGModuleInvariants.{v, max u v w} G)
        (trivialIntegerModule.{v, max u v w} G)
        (invariantsCorepresentation.{v, max u v w} G)
        ((continuousModuleExtendScalars.{u, v, w} R G).obj
          (trivialIntegerModule.{v, max u v w} G))
        (Stacks.Cohomology.ExtComparison.compPreadditiveCoyonedaIso
          (continuousModuleExtendForgetAdj.{u, v, w} R G)
          (trivialIntegerModule.{v, max u v w} G)).symm
        hvan i ≪≫
      Functor.isoWhiskerLeft (continuousModuleForget.{u, v, max u v w} R G)
        (Stacks.DerivedIndexing.rightDerivedIso
          (continuousGModuleInvariants.{v, max u v w} G) i)

end Comparison

end Stacks.ContinuousCohomology

end
