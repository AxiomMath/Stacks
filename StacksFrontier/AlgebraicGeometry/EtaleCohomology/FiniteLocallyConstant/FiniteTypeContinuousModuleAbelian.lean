module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.Basic
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.UnibranchContinuousModules

/-!
# The abelian structure on finite modules with a continuous action

Let `R` be a ring and `G` a topological group. The finite type `R`-`G`-modules
`Stacks.GroupCohomology.FiniteTypeContinuousModule` are the full subcategory of the `R`-`G`-modules
of Stacks Tag 04JP, `Stacks.Injectives.ContinuousModule`, whose underlying `R`-module is finitely
generated. The ambient category is abelian, by `Stacks.ContinuousCohomology.abelian`, and this
file equips the subcategory with the structure it inherits:

* it is preadditive, hence its hom sets are abelian groups, for every ring `R`;
* over a Noetherian ring it is closed under subobjects, quotients and finite products, hence
  abelian, with finite limits and finite colimits.

A finite ring is Noetherian, so both apply to the group ring `F_ℓ[K]` of a finite group over a
finite field, which is the case needed to read the dictionary of Stacks Tag 0A3R between finite
locally constant sheaves and finite modules with a continuous monodromy action as an equivalence
of abelian categories.

## Main results

* `ModuleCat.isClosedUnderSubobjects_isFG` and its companions — the finitely generated modules
  contain zero and are closed under quotients, finite products and, over a Noetherian ring,
  subobjects. Closure under isomorphisms is already available as
  `Stacks.GroupCohomology.isClosedUnderIsomorphisms_moduleCatIsFG`; it is declared there as a
  `local instance`, so this file re-enables it with `attribute [local instance]` rather than
  restating it.
* `Stacks.GroupCohomology.additive_continuousModuleToModuleCat`,
  `Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat` and
  `Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat` — the functor
  taking an `R`-`G`-module to its underlying `R`-module is exact.
* `Stacks.GroupCohomology.preadditive_finiteTypeContinuousModule` — the finite type
  `R`-`G`-modules are preadditive.
* `Stacks.GroupCohomology.abelian_finiteTypeContinuousModule` — over a Noetherian ring they are
  abelian, and
  `Stacks.GroupCohomology.preservesFiniteLimits_finiteTypeContinuousModuleι` with its colimit
  companion say that their inclusion into all `R`-`G`-modules is exact.
* `Stacks.GroupCohomology.additive_of_preservesBinaryProducts` — consequently a functor out of
  them which preserves binary products and zero morphisms is additive, which is the form in which
  `CategoryTheory.Functor.additive_of_preserves_binary_products` is applied to the dictionary.

## Implementation notes

The closure conditions are proved for the *inverse image* property
`Stacks.GroupCohomology.continuousModuleIsFG`, so they reduce by Mathlib's generic instances for
`CategoryTheory.ObjectProperty.inverseImage` to two separate inputs: that the finitely generated
modules are closed under subobjects, quotients and finite products, and that
`Stacks.Injectives.continuousModuleUnderlying` preserves monomorphisms, epimorphisms and
finite products. Closure under extensions, the remaining condition of a Serre subcategory, is not
needed, because `CategoryTheory.ObjectProperty.FullSubcategory` is already abelian once the
property contains zero and is closed under isomorphisms, subobjects, quotients and finite
products.

Exactness of the underlying-module functor is assembled by hand rather than found by instance
search. The functor is a composite of two full subcategory inclusions with
`CategoryTheory.Action.forget`, and an inclusion `CategoryTheory.ObjectProperty.ι` is only known
to preserve finite limits through `CategoryTheory.ObjectProperty.preservesKernels_ι`, which is a
lemma rather than an instance. The two halves are therefore combined explicitly by
`CategoryTheory.Limits.comp_preservesFiniteLimits` and
`CategoryTheory.Limits.comp_preservesFiniteColimits`, and additivity is read off the underlying
linear maps, so that none of these proofs has to identify the composite with
`Stacks.Injectives.continuousModuleUnderlying` by a typeclass search at the other spelling: as
the implementation notes of `Stacks.ContinuousCohomology.fullSubcategoryAbelian` record,
`Stacks.Injectives.ContinuousModule` supplies its `CategoryTheory.HasForget₂` instance by a `let`
in its own body, so instance search does not unify the two spellings of the property cutting out
the discrete modules even though they are `rfl`-equal.

The closure instances for `ModuleCat.isFG` are placed here rather than beside that definition
because this is the module that needs them; only `Stacks.ConstantSheaf.isFG_of_isZero`,
`Stacks.ConstantSheaf.isFG_kernel` and `Stacks.ConstantSheaf.isFG_cokernel` existed before, and
they are statements about a named zero object, kernel and cokernel rather than closure classes.

## References

* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP)
* [Stacks Project, Tag 0A3R](https://stacks.math.columbia.edu/tag/0A3R)
* [Stacks Project, Tag 0GIY](https://stacks.math.columbia.edu/tag/0GIY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

open scoped Stacks.DiscreteModuleTopology

universe u v w

attribute [local instance] Stacks.GroupCohomology.isClosedUnderIsomorphisms_moduleCatIsFG

namespace ModuleCat

variable (R : Type u) [Ring R]

/-- The zero module is finitely generated. -/
instance containsZero_isFG : (ModuleCat.isFG.{w} R).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, (ModuleCat.isFG_iff _).mpr ?_⟩
    have : Subsingleton ((0 : ModuleCat.{w} R) : Type w) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_zero _)
    infer_instance

/-- Over a Noetherian ring a submodule of a finitely generated module is finitely generated. -/
instance isClosedUnderSubobjects_isFG [IsNoetherianRing R] :
    (ModuleCat.isFG.{w} R).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f _ hY := by
    have hY' : Module.Finite R (Y : Type w) := hY
    exact (ModuleCat.isFG_iff X).mpr (Module.Finite.of_injective
      (ModuleCat.Hom.hom f) ((ModuleCat.mono_iff_injective f).mp inferInstance))

/-- A quotient of a finitely generated module is finitely generated. -/
instance isClosedUnderQuotients_isFG : (ModuleCat.isFG.{w} R).IsClosedUnderQuotients where
  prop_of_epi {X Y} f _ hX := by
    have hX' : Module.Finite R (X : Type w) := hX
    exact (ModuleCat.isFG_iff Y).mpr (Module.Finite.of_surjective
      (ModuleCat.Hom.hom f) ((ModuleCat.epi_iff_surjective f).mp inferInstance))

/-- A finite product of finitely generated modules is finitely generated: the product is the
module of sections of the family, and `Module.Finite.pi` applies. -/
instance isClosedUnderFiniteProducts_isFG :
    (ModuleCat.isFG.{w} R).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := ⟨by
    rintro X ⟨p⟩
    have hfin : ∀ j : J, Module.Finite R (p.diag.obj ⟨j⟩ : Type w) :=
      fun j ↦ p.prop_diag_obj ⟨j⟩
    have e : X ≅ ModuleCat.of R (∀ j : J, (p.diag.obj ⟨j⟩ : Type w)) :=
      IsLimit.conePointUniqueUpToIso p.isLimit (limit.isLimit p.diag) ≪≫
        HasLimit.isoOfNatIso Discrete.natIsoFunctor ≪≫ ModuleCat.piIsoPi _
    exact (ModuleCat.isFG.{w} R).prop_of_iso e.symm
      ((ModuleCat.isFG_iff _).mpr Module.Finite.pi)⟩

end ModuleCat

namespace Stacks.GroupCohomology

variable (R : Type u) [Ring R] (G : Type v) [Group G] [TopologicalSpace G]

/-- The inclusion of an abelian full subcategory preserves finite limits. -/
private theorem preservesFiniteLimits_ι_of_abelian {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderFiniteProducts] : PreservesFiniteLimits P.ι :=
  have := P.preservesKernels_ι
  Functor.preservesFiniteLimits_of_preservesKernels P.ι

/-- The inclusion of an abelian full subcategory preserves finite colimits. -/
private theorem preservesFiniteColimits_ι_of_abelian {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderFiniteProducts] : PreservesFiniteColimits P.ι :=
  have := P.preservesCokernels_ι
  Functor.preservesFiniteColimits_of_preservesCokernels P.ι

/-- The functor taking an `R`-`G`-module to its underlying `R`-module is additive. -/
theorem additive_continuousModuleToModuleCat :
    (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G).Additive :=
  { map_add := by
      intros
      apply ModuleCat.hom_ext
      rfl }

/-- The functor taking an `R`-`G`-module to its underlying `R`-module preserves finite limits:
each of the two full subcategory inclusions it is composed of preserves kernels, and
`CategoryTheory.Action.forget` preserves all limits. -/
theorem preservesFiniteLimits_continuousModuleToModuleCat :
    PreservesFiniteLimits (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G) := by
  have : PreservesFiniteLimits (Action.forget (ModuleCat.{w} R) G) := inferInstance
  have := preservesFiniteLimits_ι_of_abelian
    (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G))
  have := preservesFiniteLimits_ι_of_abelian
    (Action.IsContinuous (V := ModuleCat.{w} R) (G := G))
  have : PreservesFiniteLimits
      (ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) ⋙
        Action.forget (ModuleCat.{w} R) G) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits
    (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)))
    (ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) ⋙
      Action.forget (ModuleCat.{w} R) G)

/-- The functor taking an `R`-`G`-module to its underlying `R`-module preserves finite colimits,
by the cokernel half of the argument for
`Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat`. -/
theorem preservesFiniteColimits_continuousModuleToModuleCat :
    PreservesFiniteColimits (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G) := by
  have : PreservesFiniteColimits (Action.forget (ModuleCat.{w} R) G) := inferInstance
  have := preservesFiniteColimits_ι_of_abelian
    (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G))
  have := preservesFiniteColimits_ι_of_abelian
    (Action.IsContinuous (V := ModuleCat.{w} R) (G := G))
  have : PreservesFiniteColimits
      (ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) ⋙
        Action.forget (ModuleCat.{w} R) G) :=
    comp_preservesFiniteColimits _ _
  exact comp_preservesFiniteColimits
    (ObjectProperty.ι (ContAction.IsDiscrete (V := ModuleCat.{w} R) (G := G)))
    (ObjectProperty.ι (Action.IsContinuous (V := ModuleCat.{w} R) (G := G)) ⋙
      Action.forget (ModuleCat.{w} R) G)

/-- A monomorphism of `R`-`G`-modules is injective on underlying modules. -/
theorem preservesMonomorphisms_continuousModuleToModuleCat :
    (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G).PreservesMonomorphisms := by
  have := preservesFiniteLimits_continuousModuleToModuleCat.{u, v, w} R G
  infer_instance

/-- An epimorphism of `R`-`G`-modules is surjective on underlying modules. -/
theorem preservesEpimorphisms_continuousModuleToModuleCat :
    (Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G).PreservesEpimorphisms := by
  have := preservesFiniteColimits_continuousModuleToModuleCat.{u, v, w} R G
  infer_instance

/-- The zero `R`-`G`-module is of finite type. -/
instance containsZero_continuousModuleIsFG :
    (continuousModuleIsFG.{u, v, w} R G).ContainsZero where
  exists_zero := by
    have := additive_continuousModuleToModuleCat.{u, v, w} R G
    refine ⟨0, isZero_zero _, (ModuleCat.isFG_iff _).mpr ?_⟩
    have : Subsingleton
        (((Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G).obj 0 :
          ModuleCat.{w} R) : Type w) :=
      ModuleCat.isZero_iff_subsingleton.mp
        ((Stacks.Injectives.continuousModuleUnderlying.{u, v, w} R G).map_isZero (isZero_zero _))
    infer_instance

/-- Over a Noetherian ring a subobject of a finite type `R`-`G`-module is of finite type. -/
instance isClosedUnderSubobjects_continuousModuleIsFG [IsNoetherianRing R] :
    (continuousModuleIsFG.{u, v, w} R G).IsClosedUnderSubobjects := by
  have := preservesMonomorphisms_continuousModuleToModuleCat.{u, v, w} R G
  infer_instance

/-- A quotient of a finite type `R`-`G`-module is of finite type. -/
instance isClosedUnderQuotients_continuousModuleIsFG :
    (continuousModuleIsFG.{u, v, w} R G).IsClosedUnderQuotients := by
  have := preservesEpimorphisms_continuousModuleToModuleCat.{u, v, w} R G
  infer_instance

/-- A finite product of finite type `R`-`G`-modules is of finite type. -/
instance isClosedUnderFiniteProducts_continuousModuleIsFG :
    (continuousModuleIsFG.{u, v, w} R G).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    have := preservesFiniteLimits_continuousModuleToModuleCat.{u, v, w} R G
    infer_instance

/-- **Finite modules with a continuous action form a preadditive category**, with the hom sets of
the ambient category of `R`-`G`-modules; in particular each hom set is an abelian group. -/
instance preadditive_finiteTypeContinuousModule :
    Preadditive (FiniteTypeContinuousModule.{u, v, w} R G) :=
  Preadditive.fullSubcategory _

/-- **Over a Noetherian ring, finite modules with a continuous action form an abelian
category.** -/
instance abelian_finiteTypeContinuousModule [IsNoetherianRing R] :
    Abelian (FiniteTypeContinuousModule.{u, v, w} R G) :=
  inferInstance

/-- Over a Noetherian ring the inclusion of the finite type `R`-`G`-modules into all
`R`-`G`-modules preserves finite limits. -/
theorem preservesFiniteLimits_finiteTypeContinuousModuleι [IsNoetherianRing R] :
    PreservesFiniteLimits (finiteTypeContinuousModuleι.{u, v, w} R G) :=
  have {X Y : FiniteTypeContinuousModule.{u, v, w} R G} (f : X ⟶ Y) :=
    ObjectProperty.preservesKernels_ι (continuousModuleIsFG.{u, v, w} R G) f
  Functor.preservesFiniteLimits_of_preservesKernels
    (finiteTypeContinuousModuleι.{u, v, w} R G)

/-- Over a Noetherian ring the inclusion of the finite type `R`-`G`-modules into all
`R`-`G`-modules preserves finite colimits. -/
theorem preservesFiniteColimits_finiteTypeContinuousModuleι [IsNoetherianRing R] :
    PreservesFiniteColimits (finiteTypeContinuousModuleι.{u, v, w} R G) :=
  have {X Y : FiniteTypeContinuousModule.{u, v, w} R G} (f : X ⟶ Y) :=
    ObjectProperty.preservesCokernels_ι (continuousModuleIsFG.{u, v, w} R G) f
  Functor.preservesFiniteColimits_of_preservesCokernels
    (finiteTypeContinuousModuleι.{u, v, w} R G)

/-- A functor out of the finite type `R`-`G`-modules preserving binary products and zero
morphisms is additive. This is
`CategoryTheory.Functor.additive_of_preserves_binary_products` applied to
`Stacks.GroupCohomology.preadditive_finiteTypeContinuousModule`, for which it is enough that the
finite type `R`-`G`-modules have binary products; the Noetherian hypothesis is what provides
them. -/
theorem additive_of_preservesBinaryProducts [IsNoetherianRing R] {D : Type*} [Category D]
    [Preadditive D] (F : FiniteTypeContinuousModule.{u, v, w} R G ⥤ D)
    [PreservesLimitsOfShape (Discrete WalkingPair) F] [F.PreservesZeroMorphisms] :
    F.Additive :=
  Functor.additive_of_preserves_binary_products F

end Stacks.GroupCohomology

end
