module

public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekQuasiFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.CohomologicalDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperDirectImage

/-!
# Finite direct image on the big étale site, for abelian sheaves

Let `B` be a big étale site and `f : T ⟶ S` a morphism of it with `f` finite. This file proves
two facts about abelian sheaves:

* the base change map `π_S⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_T⁻¹` of the big and small étale sites
  is an isomorphism of functors on abelian sheaves — this is Stacks 0DDJ (1) for abelian
  sheaves and a finite morphism, with Stacks 0959 in place of proper base change;
* the direct image `f_{big,*}` of abelian sheaves on the big étale sites is exact, as in the proof
  of Stacks 0DDJ (4).

## Main definitions

* `AlgebraicGeometry.bigEtaleAbelianProjectionAdjunction` — the adjunction `π_S⁻¹ ⊣ π_{S,*}` on
  abelian sheaves, `π_S⁻¹` being the sheaf pullback along the inclusion of the small étale site.

## Main results

* `AlgebraicGeometry.isIso_bigSmallEtaleBaseChange_abelian_of_isFinite` — the abelian base
  change map is an isomorphism for `f` finite.
* `AlgebraicGeometry.isZero_of_forall_isZero_bigEtaleRestriction_obj` and
  `AlgebraicGeometry.epi_of_forall_epi_bigEtaleRestriction_map` — the restrictions to the small
  étale sites of the objects of the big étale site detect zero objects and epimorphisms.
* `AlgebraicGeometry.bigEtaleAbelianPushforward_preservesFiniteColimits_of_isFinite` — the big
  direct image along a finite morphism is right exact, hence exact.
* `AlgebraicGeometry.bigEtaleAbelianProjectionPullback_preservesFiniteLimits` — `π_S⁻¹` is exact,
  Stacks 0DDI, recorded as instances.

## References

* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 075A](https://stacks.math.columbia.edu/tag/075A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

/-- The adjunction `π_S⁻¹ ⊣ π_{S,*}` of the projection from the big étale topos over `S` to the
small étale topos of `S`, on abelian sheaves: `π_S⁻¹` is the sheaf pullback along the inclusion
of the small étale site, `π_{S,*}` restriction along it. -/
public abbrev bigEtaleAbelianProjectionAdjunction (S : B.Scheme) :
    (SmallEtale.inclusion B S.obj S.property).sheafPullback AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property) ⊣
      bigEtaleProjectionPushforward B AddCommGrpCat.{u + 1} S :=
  (SmallEtale.inclusion B S.obj S.property).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B S.obj S.property) (BigEtaleOver.topology B S.obj S.property)

variable {T S : B.Scheme} (f : T ⟶ S)

/-- **Stacks 0DDJ (1) for abelian sheaves and a finite morphism.** For `f` finite the base change
map `π_S⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_T⁻¹` of abelian sheaves is an isomorphism. -/
public theorem isIso_bigSmallEtaleBaseChange_abelian_of_isFinite [IsFinite (B.inclusion.map f)] :
    IsIso (bigSmallEtaleBaseChange B AddCommGrpCat.{u + 1} f
      (bigEtaleAbelianProjectionAdjunction B T) (bigEtaleAbelianProjectionAdjunction B S)) :=
  let : ∀ {X Y : B.Scheme} (k : X ⟶ Y), ((smallEtaleBaseChange B k).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint := fun k =>
    ((smallEtaleBaseChange B k).sheafAdjunctionContinuous AddCommGrpCat.{u + 1} _ _).isRightAdjoint
  isIso_bigSmallEtaleBaseChange_of_forall_isIso_mateEquiv B AddCommGrpCat.{u + 1} f _ _ fun U =>
    SmallEtale.isIso_mateEquiv_symm_boundedBaseChangeMate_of_isFinite B f U.hom
      ((Over.pullback f).obj U).hom (bigEtaleFibreFst B f U)
      ((bigEtaleFibreSquare_isPullback B f U).map B.inclusion) pullback.condition.symm

/-! ### Restriction to the small étale sites detects zero objects and epimorphisms -/

section Detection

variable (S : B.Scheme)

/-- Restriction of abelian sheaves to the small étale site of an object `U` of the big étale site
over `S` is a left adjoint: the functor `i_U` is cocontinuous as well as continuous. -/
public instance bigEtaleRestriction_isLeftAdjoint (U : BigEtaleOver B S.obj S.property) :
    (bigEtaleRestriction B AddCommGrpCat.{u + 1} S U).IsLeftAdjoint :=
  ((smallEtaleToBigEtaleFunctor B U.left S U.hom).sheafAdjunctionCocontinuous
    AddCommGrpCat.{u + 1} (SmallEtale.topology B U.left.obj U.left.property)
    (BigEtaleOver.topology B S.obj S.property)).isLeftAdjoint

/-- **The restrictions to the small étale sites detect zero objects.** An abelian sheaf on the big
étale site over `S` whose restriction to the small étale site of every object `U` is zero is
zero. -/
public theorem isZero_of_forall_isZero_bigEtaleRestriction_obj
    {Z : Sheaf (BigEtaleOver.topology B S.obj S.property) AddCommGrpCat.{u + 1}}
    (h : ∀ U : BigEtaleOver B S.obj S.property,
      IsZero ((bigEtaleRestriction B AddCommGrpCat.{u + 1} S U).obj Z)) :
    IsZero Z := by
  have : IsIso (0 : Z ⟶ Z) :=
    isIso_of_forall_isIso_bigEtaleRestriction_map B AddCommGrpCat.{u + 1} _ fun U => by
      rw [(h U).eq_of_src ((bigEtaleRestriction B AddCommGrpCat.{u + 1} S U).map 0) (𝟙 _)]
      infer_instance
  exact IsZero.of_mono_zero Z Z

/-- **The restrictions to the small étale sites detect epimorphisms.** A morphism of abelian
sheaves on the big étale site over `S` whose restriction to the small étale site of every object
`U` is an epimorphism is an epimorphism. -/
public theorem epi_of_forall_epi_bigEtaleRestriction_map
    {F G : Sheaf (BigEtaleOver.topology B S.obj S.property) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (h : ∀ U : BigEtaleOver B S.obj S.property,
      Epi ((bigEtaleRestriction B AddCommGrpCat.{u + 1} S U).map φ)) :
    Epi φ := by
  refine Preadditive.epi_of_isZero_cokernel φ
    (isZero_of_forall_isZero_bigEtaleRestriction_obj B S fun U => ?_)
  have := h U
  exact (isZero_cokernel_of_epi ((bigEtaleRestriction B AddCommGrpCat.{u + 1} S U).map φ)).of_iso
    (PreservesCokernel.iso (bigEtaleRestriction B AddCommGrpCat.{u + 1} S U) φ)

end Detection

/-! ### The big direct image along a finite morphism is exact -/

section Exactness

/-- **The big direct image along a finite morphism preserves epimorphisms.** For `f` finite, the
direct image `f_{big,*}` of abelian sheaves on the big étale sites preserves epimorphisms. -/
public instance bigEtaleAbelianPushforward_preservesEpimorphisms_of_isFinite
    [IsFinite (B.inclusion.map f)] :
    ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property)).PreservesEpimorphisms where
  preserves {F G} φ _ := by
    refine epi_of_forall_epi_bigEtaleRestriction_map B S _ fun U => ?_
    have : IsFinite (B.inclusion.map (bigEtaleFibreFst B f U)) :=
      MorphismProperty.of_isPullback ((bigEtaleFibreSquare_isPullback B f U).map B.inclusion)
        inferInstance
    have := ((exactFunctor_iff _).mp
      (SmallEtale.etalePushforward_exact_of_isFinite.{u} B (bigEtaleFibreFst B f U))).2
    have hnat := (bigEtaleRestrictionDirectImageSquare B AddCommGrpCat.{u + 1} f U).naturality φ
    have hrw : (bigEtaleRestriction B AddCommGrpCat.{u + 1} S U).map
        (((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (BigEtaleOver.topology B S.obj S.property)
          (BigEtaleOver.topology B T.obj T.property)).map φ) =
        inv ((bigEtaleRestrictionDirectImageSquare B AddCommGrpCat.{u + 1} f U).app F) ≫
          (B.smallPushforward (bigEtaleFibreFst B f U) AddCommGrpCat.{u + 1}).map
            ((bigEtaleRestriction B AddCommGrpCat.{u + 1} T ((Over.pullback f).obj U)).map φ) ≫
          (bigEtaleRestrictionDirectImageSquare B AddCommGrpCat.{u + 1} f U).app G := by
      rw [IsIso.eq_inv_comp]
      exact hnat.symm
    rw [hrw]
    have : Epi ((B.smallPushforward (bigEtaleFibreFst B f U) AddCommGrpCat.{u + 1}).map
        ((bigEtaleRestriction B AddCommGrpCat.{u + 1} T ((Over.pullback f).obj U)).map φ)) :=
      Functor.map_epi _ _
    exact epi_comp _ _

/-- The big direct image of abelian sheaves along `f`, restriction along `Over.pullback f`, is
additive. -/
public instance overPullbackSheafPushforward_additive :
    ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property)).Additive where
  map_add := by intros; rfl

/-- **The big direct image along a finite morphism is right exact.** For `f` finite, the direct
image `f_{big,*}` of abelian sheaves on the big étale sites preserves finite colimits; being a
right adjoint, it is therefore exact. -/
public theorem bigEtaleAbelianPushforward_preservesFiniteColimits_of_isFinite
    [IsFinite (B.inclusion.map f)] :
    PreservesFiniteColimits ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology B S.obj S.property) (BigEtaleOver.topology B T.obj T.property)) := by
  have : ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigEtaleOver.topology B S.obj S.property)
      (BigEtaleOver.topology B T.obj T.property)).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

end Exactness

/-! ### Exactness of the inverse image `π_S⁻¹` -/

section InverseImage

/-- The inverse image `π_S⁻¹` of abelian sheaves from the small étale site of `S` to the big
étale site over `S` preserves finite limits, Stacks 0DDI. -/
public instance bigEtaleAbelianProjectionPullback_preservesFiniteLimits (S : B.Scheme) :
    PreservesFiniteLimits ((SmallEtale.inclusion B S.obj S.property).sheafPullback
      AddCommGrpCat.{u + 1} (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)) :=
  ((exactFunctor_iff _).mp (projectionPullback_exact.{u, 0} B S.obj S.property)).1

/-- The inverse image `π_S⁻¹` of abelian sheaves preserves finite colimits, being a left
adjoint. -/
public instance bigEtaleAbelianProjectionPullback_preservesFiniteColimits (S : B.Scheme) :
    PreservesFiniteColimits ((SmallEtale.inclusion B S.obj S.property).sheafPullback
      AddCommGrpCat.{u + 1} (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)) :=
  ((exactFunctor_iff _).mp (projectionPullback_exact.{u, 0} B S.obj S.property)).2

/-- The inverse image `π_S⁻¹` of abelian sheaves is additive. -/
public instance bigEtaleAbelianProjectionPullback_additive (S : B.Scheme) :
    ((SmallEtale.inclusion B S.obj S.property).sheafPullback AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (BigEtaleOver.topology B S.obj S.property)).Additive :=
  Functor.additive_of_preserves_binary_products _

end InverseImage

end AlgebraicGeometry

end
