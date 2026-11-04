module

public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.Identity
public import StacksFrontier.CategoryTheory.Sites.Modules.CoarserTopology
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModuleHigherDirectImageSheafification

/-!
# Coarsening a topology as a morphism of ringed sites

Let `(C, J, 𝒪)` be a ringed site and let `J' ≤ J` be a coarser topology on `C`. Then `𝒪` is a
sheaf for `J'` as well, so `(C, J', 𝒪)` is again a ringed site, and the identity functor of `C`
presents a morphism of ringed sites

`ε : (C_J, 𝒪) ⟶ (C_{J'}, 𝒪)`

whose structure map is the identity. This file builds `ε`, identifies its direct and inverse
images of sheaves of modules with `SheafOfModules.ofLE` and `SheafOfModules.sheafifyOfLE`, and
uses the universal property of the derived direct image `Rε_*` in the `SheafOfModules.ofLE`
spelling, which is the one in which the higher direct images of a coarsening are computed.

## Main definitions

* `CategoryTheory.Functor.isMorphismOfSites_id_of_le`: the identity functor is a morphism of
  sites from a topology to any coarser one.
* `AlgebraicGeometry.RingedSite.coarseningHom`: the morphism of ringed sites `ε`.
* `AlgebraicGeometry.RingedSite.pushforwardToposCoarseningHomIso`: `ε_*` is
  `SheafOfModules.ofLE`.
* `AlgebraicGeometry.RingedSite.pullbackToposCoarseningHomIso`: `ε^*` is
  `SheafOfModules.sheafifyOfLE`.

## Main results

* `AlgebraicGeometry.RingedSite.preservesFiniteLimits_pullbackTopos_coarseningHom` and
  `preservesFiniteColimits_pullbackTopos_coarseningHom`: `ε^*` is exact, so the derived pullback
  `Lε^*` exists
  (`AlgebraicGeometry.RingedSite.hasLeftDerivedFunctor_pullbackOnHomotopy_coarseningHom`).
* `Stacks.Cohomology.CompareTopologies.isZero_homology_derivedPushforwardCoarsening_obj`:
  `Hᵖ(Rε_*(M[0])) = 0` whenever the cohomology `H^p_J(U, M)` vanishes on a family of objects
  which `J'`-covers every object of `C`.

## Implementation notes

The two coherence isomorphisms which separate `ε_*` from `SheafOfModules.ofLE` — restriction
along `Functor.op (𝟭 C)` on the site, and restriction of scalars along the identity of the
presheaf of rings — are both the identity: `Functor.op (𝟭 C)` is the identity functor of `Cᵒᵖ`
and restriction of scalars along an identity ring map does not change a module. So the two
functors have the same values on the nose and the comparison is the identity natural
transformation. The two `rfl` lemmas `pushforwardTopos_coarseningHom_obj_val` and
`pushforwardTopos_coarseningHom_map_val` record this.

The inverse image is not definitional: `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos` is a
*chosen* left adjoint of the direct image, so it is identified with
`SheafOfModules.sheafifyOfLE` by uniqueness of left adjoints, transported along the direct-image
comparison.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace CategoryTheory.Functor

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
/-- **The identity functor is a morphism of sites from a topology to any coarser one.** It is
continuous because a `J'`-covering sieve is a `J`-covering sieve, and the functor it induces on
sheaves of sets is left exact because the identity functor is representably flat. -/
theorem isMorphismOfSites_id_of_le {C : Type u} [SmallCategory C]
    (J J' : GrothendieckTopology C) (h : J' ≤ J) :
    (𝟭 C).IsMorphismOfSites J' J := by
  have := Functor.isContinuous_id_of_le J' J h
  rw [Functor.isMorphismOfSites_iff_preservesFiniteLimits]
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits (𝟭 C) (Type u) J' J

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (S : RingedSite.{u, u, u}) {J' : GrothendieckTopology S.C} (h : J' ≤ S.J)

/-- **The comparison morphism of ringed sites of a topology and a coarser one.** The underlying
functor is the identity of `C`, which is a morphism of sites from `J'` to `J`, and the structure
map is the identity of `𝒪`, which is a sheaf for both topologies. -/
def coarseningHom : RingedSite.Hom S (S.ofLe h) where
  u := 𝟭 S.C
  isMorphismOfSites := Functor.isMorphismOfSites_id_of_le S.J J' h
  fsharp := 𝟙 _

/-- The underlying functor of `ε` is the identity functor of `C`. -/
@[simp]
theorem coarseningHom_u : (S.coarseningHom h).u = 𝟭 S.C := rfl

/-- `ε_*` does not change the underlying presheaf of modules. -/
theorem pushforwardTopos_coarseningHom_obj_val
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) :
    ((S.coarseningHom h).toRingedToposSiteHom.pushforwardTopos.obj M).val = M.val := rfl

/-- `ε_*` does not change the morphisms of underlying presheaves of modules. -/
theorem pushforwardTopos_coarseningHom_map_val
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)}
    (φ : M ⟶ N) :
    ((S.coarseningHom h).toRingedToposSiteHom.pushforwardTopos.map φ).val = φ.val := rfl

/-- **`ε_*` is `SheafOfModules.ofLE`.** Both read a `J`-sheaf of modules as a `J'`-sheaf of
modules with the same underlying presheaf of modules: the direct image inserts restriction along
`Functor.op (𝟭 C)` and restriction of scalars along the identity of the presheaf of rings, and
both of those are the identity. -/
def pushforwardToposCoarseningHomIso :
    (S.coarseningHom h).toRingedToposSiteHom.pushforwardTopos ≅
      SheafOfModules.ofLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) :=
  Iso.refl _

section Pullback

variable [HasSheafify S.J AddCommGrpCat.{u}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`ε^*` is `SheafOfModules.sheafifyOfLE`**, the `J`-sheafification of the underlying presheaf
of modules. The inverse image is a chosen left adjoint of `ε_*`, and `SheafOfModules.ofLE` has
`SheafOfModules.sheafifyOfLE` as a left adjoint, so the two agree by uniqueness of left
adjoints. -/
def pullbackToposCoarseningHomIso :
    (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos ≅
      SheafOfModules.sheafifyOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) :=
  Adjunction.leftAdjointUniq
    (S.coarseningHom h).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    ((SheafOfModules.sheafifyOfLEAdjunction.{u, u, u, u} h
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O)).ofNatIsoRight
      (S.pushforwardToposCoarseningHomIso h).symm)

/-- `ε^*` preserves finite limits: it forgets to the underlying presheaf of modules and then
`J`-sheafifies, and both steps are left exact. -/
instance preservesFiniteLimits_pullbackTopos_coarseningHom :
    PreservesFiniteLimits (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos := by
  refine @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    (S.pullbackToposCoarseningHomIso h).symm ?_
  have : PreservesFiniteLimits
      (SheafOfModules.forgetOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.forget.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf S.O).ofLE h)))
  exact comp_preservesFiniteLimits
    (SheafOfModules.forgetOfLE.{u, u, u, u} h (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
    (PresheafOfModules.sheafification.{u} (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf S.O).obj))

/-- `ε^*` preserves finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_pullbackTopos_coarseningHom :
    PreservesFiniteColimits (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos :=
  have : PreservesColimitsOfSize.{0, 0}
      (S.coarseningHom h).toRingedToposSiteHom.pullbackTopos :=
    Adjunction.leftAdjoint_preservesColimits
      (S.coarseningHom h).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
  inferInstance

/-- **The derived pullback `Lε^*` exists**, because `ε^*` is exact. -/
theorem hasLeftDerivedFunctor_pullbackOnHomotopy_coarseningHom
    [HasDerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.ringedTopos.O))] :
    (pullbackOnHomotopy.{u} (S.coarseningHom h).toRingedToposSiteHom).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf S.O).ofLE h))
        (ComplexShape.up ℤ)) :=
  pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact.{u}
    (S.coarseningHom h).toRingedToposSiteHom

end Pullback

end AlgebraicGeometry.RingedSite

namespace Stacks.Cohomology.CompareTopologies

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable (S : RingedSite.{u, u, u}) {J' : GrothendieckTopology S.C} (h : J' ≤ S.J)
  [HasSheafify S.J AddCommGrpCat.{u}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))]
  [J'.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]

/-- **`Hᵖ(Rε_*(M[0])) = 0` for the coarsening morphism `ε` of ringed sites.** If every object of
`C` has a `J'`-covering by members of a family `B` and the cohomology `H^p_J(U, M)` vanishes for
every `U` in `B`, then the degree-`p` cohomology of `Rε_*` applied to `M` placed in degree `0`
vanishes. No positivity of `p` is needed. -/
theorem isZero_homology_derivedPushforwardCoarsening_obj (p : ℕ)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) (B : Set S.C)
    (hB : ∀ U : S.C, ∃ 𝒰 : PreZeroHypercover.{u} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : S.C, B U →
      IsZero (Stacks.Cohomology.moduleCohomology
        (Stacks.SheafOfModules.Tensor.ringSheaf S.O) U p M)) :
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf S.O).ofLE h)) (p : ℤ)).obj
      ((derivedPushforward.{u} (S.coarseningHom h).toRingedToposSiteHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) 0).obj M))) := by
  have := SheafOfModules.isGrothendieckAbelianU (Stacks.SheafOfModules.Tensor.ringSheaf S.O)
  exact @ModuleHigherDirectImage.isZero_homology_derivedPushforward_singleFunctor_obj
    S.C _ S.J J' h (Stacks.SheafOfModules.Tensor.ringSheaf S.O) _ _ _ _ _ _ _ _ _
    (derivedPushforward.{u} (S.coarseningHom h).toRingedToposSiteHom)
    (derivedPushforwardUnit.{u} (S.coarseningHom h).toRingedToposSiteHom)
    (@Functor.instIsRightDerivedFunctorTotalRightDerivedTotalRightDerivedUnit _ _ _ _ _ _
      (pushforwardOnHomotopy.{u} (S.coarseningHom h).toRingedToposSiteHom)
      (DerivedCategory.Qh (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.O))
        (ComplexShape.up ℤ))
      DerivedCategory.instIsLocalizationHomotopyCategoryIntUpQhQuasiIso
      (pushforward_hasRightDerivedFunctor (S.coarseningHom h).toRingedToposSiteHom)) p M B hB hvan

end Stacks.Cohomology.CompareTopologies

end
