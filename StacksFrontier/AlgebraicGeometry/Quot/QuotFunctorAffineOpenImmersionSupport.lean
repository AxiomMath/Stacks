module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAffineOpenImmersionPushforward
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorSupportLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModuleConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotientPreimage

/-!
# The direct images among the quotients, along an affine open immersion

Let `π : X ⟶ Y` be an affine open immersion of algebraic spaces which are separated and of finite
presentation over an algebraic space `B`, let `F` be a quasi-coherent `𝒪_X`-module and write
`G = π_*F`.  Over a test scheme `T` of `B`, a member `G_T ⟶ Q` of `Quot_{G/Y/B}(T)` is the
direct image `G_T ≅ π_{T,*}F_T ⟶ π_{T,*}Q'` of a member `F_T ⟶ Q'` of `Quot_{F/X/B}(T)` exactly
when `Supp(Q) ⊆ |X_T|`.

* If `Q = π_{T,*}Q'`, then the support of `Q'` is proper over `T`, so its image in `|Y_T|` is
  closed (Stacks 0CZG, `Y_T` being separated over `T`), and `π_{T,*}Q'` is supported in it.
* Conversely, if `Supp(Q) ⊆ |X_T|`, the restriction `F_T ≅ π_T^*π_{T,*}F_T ≅ π_T^*G_T ⟶ π_T^*Q`
  is a member of `Quot_{F/X/B}(T)`: restriction to an open subspace preserves quasi-coherence,
  finite presentation and flatness over `T`, and it preserves proper support of a module
  supported in the open subspace.  Its direct image is `Q` again, because the unit
  `Q ⟶ π_{T,*}π_T^*Q` is a monomorphism, `Q` being supported in `X_T`.

## Main definitions

* `AlgebraicGeometry.Space.QuotPushforwardSituation.directImageBaseChangeIso`: the base change
  isomorphism `G_T ≅ π_{T,*}F_T` of Stacks 07U8.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.restrictionQuotient`: the restriction to
  `X_T` of a quotient of `G_T`, recorded by its kernel.

## Main results

* `AlgebraicGeometry.Space.QuotPushforwardSituation.supportedInSource_directImageQuotient`: a
  direct image is supported in `X_T`.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.restrictionQuotient_mem`: the restriction of
  a member of `Quot_{G/Y/B}(T)` supported in `X_T` is a member of `Quot_{F/X/B}(T)`.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.directImageQuotient_restrictionQuotient`:
  its direct image is the quotient one started from.
* `AlgebraicGeometry.Space.QuotPushforwardSituation.directImageQuotient_injective`: the direct
  image of quotients is injective.
* `QuotPushforwardSituation.exists_directImageQuotient_iff_supportedInSource`: the
  characterization of the direct images by the support condition.

## References

* [Stacks Project, Tag 0DP2](https://stacks.math.columbia.edu/tag/0DP2)
* [Stacks Project, Tag 0CZG](https://stacks.math.columbia.edu/tag/0CZG)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- The modules here have their sections in the universe of the schemes, which the ambient-universe
-- abelian structure of `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` cannot describe; left
-- in place it is selected ahead of `SheafOfModules.instAbelian` and leaves the module universe
-- of the subobjects and cokernels below unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Separatedness of the base change** (Stacks 03KL): the projection `X_T ⟶ T` of a quotient
situation is separated when the morphism of the situation is. -/
theorem QuotSituation.isSeparated_projection (D : QuotSituation B S hS)
    (hsep : IsSeparated B S hS D.f.hom) (T : SchemesOver D.Y) :
    IsSeparated B S hS (D.projection T).hom := by
  have : (closedImmersionPresheafProperty B S hS).IsStableUnderBaseChange :=
    isClosedImmersion_isStableUnderBaseChange B S hS
  have : (closedImmersionPresheafProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.IsStableUnderBaseChange.diagonal
    (P := closedImmersionPresheafProperty B S hS)).of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS
        (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom)) hsep

namespace QuotPushforwardSituation

variable (D : QuotPushforwardSituation B S hS)

/-- The base change map `G_T ⟶ π_{T,*}F_T` of Stacks 07U8 is an isomorphism, `π` being affine and
`F` quasi-coherent. -/
theorem isIso_directImageBaseChange_app (T : SchemesOver D.base) :
    IsIso ((D.directImageBaseChange T).app D.F) := by
  have e : moduleBaseChangeMap D.π (baseChangeProjection D.structureY T) (D.baseChangeOfMap T)
      (baseChangeProjection D.structureX T) (D.isPullback_baseChangeOfMap T).flip.w =
        D.directImageBaseChange T := rfl
  have h : IsIso ((moduleBaseChangeMap D.π (baseChangeProjection D.structureY T)
      (D.baseChangeOfMap T) (baseChangeProjection D.structureX T)
      (D.isPullback_baseChangeOfMap T).flip.w).app D.F) :=
    isIso_moduleBaseChangeMap_app_of_isAffineHom (D.isPullback_baseChangeOfMap T).flip D.affine
      D.F D.quasicoherent
  rw [← e]
  exact h

/-- The base change isomorphism `G_T ≅ π_{T,*}F_T` of Stacks 07U8. -/
def directImageBaseChangeIso (T : SchemesOver D.base) :
    D.directImageSituation.baseChangeModule T ≅
      (modulePushforward B S hS (D.baseChangeOfMap T)).obj (D.sourceSituation.baseChangeModule T) :=
  @asIso _ _ _ _ ((D.directImageBaseChange T).app D.F) (D.isIso_directImageBaseChange_app T)

/-! ### Direct images are supported in the open subspace -/

/-- **A direct image is supported in `X_T`.**  The quotient of `G_T` by the direct image of a
member `K'` of `Quot_{F/X/B}(T)` embeds in `π_{T,*}(F_T/K')`, whose support lies in the image of
the support of `F_T/K'`; that image lies in `|X_T|`, and it is closed because the support of
`F_T/K'` is proper over `T` and `Y_T` is separated over `T` (Stacks 0CZG). -/
theorem supportedInSource_directImageQuotient (T : SchemesOver D.base)
    (K' : Subobject (D.sourceSituation.baseChangeModule T))
    (hK' : K' ∈ D.sourceSituation.properlySupportedQuotients T) :
    D.SupportedInSource (schemeTargetAffinePushforwardQuasicoherent B S hS) T
      (D.directImageQuotient T K') := by
  have hm := Abelian.mono_cokernelKernelSubobjectDesc
    (Functor.conjQuotientProjectionOfHom (D.directImageBaseChange T) K')
  have hmono : Mono ((SheafOfModules.toSheaf _).map (Abelian.cokernelKernelSubobjectDesc
      (Functor.conjQuotientProjectionOfHom (D.directImageBaseChange T) K'))) :=
    preserves_mono_of_preservesLimit _ _
  refine (@supportOfSheaf_subset_of_mono B S hS (D.directImageSituation.space T).1
    (D.directImageSituation.space T).2 _ _ _ hmono).trans ?_
  exact supportOfSheaf_modulePushforward_subset_range_of_hasProperSupport B S hS
    (D.baseChangeOfMap T) (D.directImageSituation.projection T) (D.sourceSituation.projection T)
    (D.baseChangeOfMap_comp_inclusion T) (D.directImageSituation.isLocallyOfFiniteType_projection T)
    (D.sourceSituation.isLocallyOfFiniteType_projection T)
    (D.directImageSituation.isSeparated_projection D.separatedY T) _ hK'.2

/-! ### The restriction of a quotient supported in the open subspace -/

/-- The direct image along the base change of the open immersion is full and faithful
(Stacks 03LV). -/
theorem full_faithful_pushforward (hπ : IsOpenImmersion B S hS D.π.hom) (T : SchemesOver D.base) :
    (modulePushforward B S hS (D.baseChangeOfMap T)).Full ∧
      (modulePushforward B S hS (D.baseChangeOfMap T)).Faithful :=
  ⟨(D.fullyFaithfulPushforwardOfIsOpenImmersion hπ T).full,
    (D.fullyFaithfulPushforwardOfIsOpenImmersion hπ T).faithful⟩

/-- **The restriction to `X_T` of a quotient of `G_T`**, recorded by its kernel: the kernel of
the quotient map `F_T ≅ π_T^*π_{T,*}F_T ≅ π_T^*G_T ⟶ π_T^*(G_T/K)`, through the base change
isomorphism `G_T ≅ π_{T,*}F_T`. -/
def restrictionQuotient (hπ : IsOpenImmersion B S hS D.π.hom) (T : SchemesOver D.base)
    (K : Subobject (D.directImageSituation.baseChangeModule T)) :
    Subobject (D.sourceSituation.baseChangeModule T) :=
  have := (D.full_faithful_pushforward hπ T).1
  have := (D.full_faithful_pushforward hπ T).2
  (modulePullbackAdjunction B S hS (D.baseChangeOfMap T)).preimageQuotient
    (D.directImageBaseChangeIso T) K

/-- The quotient of `F_T` by the restriction of a quotient of `G_T` is the restriction
`π_T^*(G_T/K)` of that quotient. -/
def restrictionQuotientCokernelIso (hπ : IsOpenImmersion B S hS D.π.hom) (T : SchemesOver D.base)
    (K : Subobject (D.directImageSituation.baseChangeModule T)) :
    D.sourceSituation.quotientModule T (D.restrictionQuotient hπ T K) ≅
      (modulePullback B S hS (D.baseChangeOfMap T)).obj
        (D.directImageSituation.quotientModule T K) :=
  have := (D.full_faithful_pushforward hπ T).1
  have := (D.full_faithful_pushforward hπ T).2
  (modulePullbackAdjunction B S hS (D.baseChangeOfMap T)).preimageQuotientCokernelIso
    (D.directImageBaseChangeIso T) K

/-- **The restriction of a member of `Quot_{G/Y/B}(T)` supported in `X_T` is a member of
`Quot_{F/X/B}(T)`.**  Its quotient is `π_T^*Q`, which is quasi-coherent (Stacks 03GA), of finite
presentation (Stacks 03DO), flat over `T` because `π_T` is flat (Stacks 05VY), and has support
proper over `T` because `Q` does and is supported in the open subspace. -/
theorem restrictionQuotient_mem (hπ : IsOpenImmersion B S hS D.π.hom) (T : SchemesOver D.base)
    (K : Subobject (D.directImageSituation.baseChangeModule T))
    (hK : K ∈ D.directImageSituation.properlySupportedQuotients T)
    (hsupp : D.SupportedInSource (schemeTargetAffinePushforwardQuasicoherent B S hS) T K) :
    D.restrictionQuotient hπ T K ∈ D.sourceSituation.properlySupportedQuotients T := by
  have hj : IsOpenImmersion B S hS (D.baseChangeOfMap T).hom :=
    D.isOpenImmersion_baseChangeOfMap hπ T
  have hcomm : D.baseChangeOfMap T ≫ D.directImageSituation.projection T =
      D.sourceSituation.projection T :=
    D.baseChangeOfMap_comp_inclusion T
  have hflat : IsFlatOver B S hS (D.sourceSituation.space T).2
      (D.sourceSituation.projection T).hom
      ((modulePullback B S hS (D.baseChangeOfMap T)).obj
        (D.directImageSituation.quotientModule T K)) := by
    have := isFlatOver_comp_modulePullback_of_isFlat B S hS (D.baseChangeOfMap T)
      (D.directImageSituation.projection T) (D.directImageSituation.quotientModule T K) hK.1.1.1
      (isFlat_of_isEtale B S hS (isEtale_of_isOpenImmersion B S hS hj)) hK.1.1.2
    rwa [hcomm] at this
  refine (D.sourceSituation.mem_properlySupportedQuotients_iff T _).2
    (QuotSituation.IsQuotModule.of_iso (D.restrictionQuotientCokernelIso hπ T K).symm
      ⟨isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (D.baseChangeOfMap T) _ hK.1.1.1, hflat,
        isFinitePresentationOnSite_modulePullback B S hS (D.baseChangeOfMap T) _ hK.1.2,
        hasProperSupport_modulePullback_of_isOpenImmersion B S hS (D.baseChangeOfMap T) hj
          (D.directImageSituation.projection T) (D.sourceSituation.projection T) hcomm
          (D.directImageSituation.isLocallyOfFiniteType_projection T)
          (D.sourceSituation.isLocallyOfFiniteType_projection T) _ hK.2 hsupp⟩)

/-- **The direct image of the restriction of a quotient supported in `X_T` is that quotient.**
The unit `Q ⟶ π_{T,*}π_T^*Q` is a monomorphism because `Q` is supported in `X_T`, so the kernel
of `G_T ⟶ Q ⟶ π_{T,*}π_T^*Q` is the kernel of `G_T ⟶ Q`. -/
theorem directImageQuotient_restrictionQuotient (hπ : IsOpenImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) (K : Subobject (D.directImageSituation.baseChangeModule T))
    (hsupp : D.SupportedInSource (schemeTargetAffinePushforwardQuasicoherent B S hS) T K) :
    D.directImageQuotient T (D.restrictionQuotient hπ T K) = K := by
  obtain ⟨_, _⟩ := D.full_faithful_pushforward hπ T
  exact Adjunction.conjSubobjectOfHom_preimageQuotient
    (modulePullbackAdjunction B S hS (D.baseChangeOfMap T)) (D.directImageBaseChange T)
    (D.isIso_directImageBaseChange_app T) K
    (mono_modulePullbackAdjunction_unit_app B S hS (D.baseChangeOfMap T)
      (D.isOpenImmersion_baseChangeOfMap hπ T) _ hsupp)

/-- **The restriction of a direct image is the quotient one started from**: restriction is exact
and a left inverse of the direct image (Stacks 03LV). -/
theorem restrictionQuotient_directImageQuotient (hπ : IsOpenImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) (K' : Subobject (D.sourceSituation.baseChangeModule T)) :
    D.restrictionQuotient hπ T (D.directImageQuotient T K') = K' := by
  obtain ⟨_, _⟩ := D.full_faithful_pushforward hπ T
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS (D.baseChangeOfMap T)
    (isFlat_of_isEtale B S hS (isEtale_of_isOpenImmersion B S hS
      (D.isOpenImmersion_baseChangeOfMap hπ T)))
  exact Adjunction.preimageQuotient_conjSubobjectOfHom
    (modulePullbackAdjunction B S hS (D.baseChangeOfMap T)) (D.directImageBaseChange T)
    (D.isIso_directImageBaseChange_app T) K'

/-- **The direct image of quotients along an affine open immersion is injective.** -/
theorem directImageQuotient_injective (hπ : IsOpenImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) : Function.Injective (D.directImageQuotient T) := fun K₁ K₂ hK => by
  rw [← D.restrictionQuotient_directImageQuotient hπ T K₁,
    ← D.restrictionQuotient_directImageQuotient hπ T K₂, hK]

/-- **The direct images among the members of `Quot_{G/Y/B}(T)` are those supported in `X_T`.** -/
theorem exists_directImageQuotient_iff_supportedInSource (hπ : IsOpenImmersion B S hS D.π.hom)
    (T : SchemesOver D.base) (K : Subobject (D.directImageSituation.baseChangeModule T))
    (hK : K ∈ D.directImageSituation.properlySupportedQuotients T) :
    (∃ K' ∈ D.sourceSituation.properlySupportedQuotients T, D.directImageQuotient T K' = K) ↔
      D.SupportedInSource (schemeTargetAffinePushforwardQuasicoherent B S hS) T K := by
  constructor
  · rintro ⟨K', hK', rfl⟩
    exact D.supportedInSource_directImageQuotient T K' hK'
  · intro hsupp
    exact ⟨D.restrictionQuotient hπ T K, D.restrictionQuotient_mem hπ T K hK hsupp,
      D.directImageQuotient_restrictionQuotient hπ T K hsupp⟩

end QuotPushforwardSituation

end AlgebraicGeometry.Space

end
