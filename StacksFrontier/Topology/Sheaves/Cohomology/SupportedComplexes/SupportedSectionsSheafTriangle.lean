module

public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.UnboundedTriangle
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupport
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# The triangle of sections supported on a closed subset

Let `Z` be a closed subset of a ringed space `X` and let `j : U = X ∖ Z ⟶ X` be the inclusion
of the open complement.  For a sheaf of modules `ℱ` on `X` the subsheaf of sections supported
on `Z` is the kernel of restriction to `U`, and for an *injective* sheaf of modules restriction
to `U` is moreover surjective, so

`0 ⟶ i_* ℋ_Z(ℐ) ⟶ ℐ ⟶ j_*(ℐ|_U) ⟶ 0`

is short exact.  Deriving this sequence turns it into a distinguished triangle

`i_* Rℋ_Z(K) ⟶ K ⟶ Rj_*(K|_U) ⟶ (i_* Rℋ_Z(K))⟦1⟧`

in the unbounded derived category of `𝒪_X`-modules, natural in `K`.

## Main definitions

* `Stacks.Cohomology.SupportedComplexes.supportedSectionsSubsheafInclusion`: the inclusion of
  the subsheaf of sections supported on `Z`, as a natural transformation into the identity.
* `Stacks.Cohomology.SupportedComplexes.supportedSectionsRestrictPushShortComplex`: the short
  complex `i_* ℋ_Z(ℱ) ⟶ ℱ ⟶ j_*(ℱ|_U)`.

## Main results

* `Stacks.Cohomology.SupportedComplexes.supportedSectionsRestrictPushShortExact`: that short
  complex is short exact at an injective sheaf of modules.
* `Stacks.Cohomology.SupportedComplexes.exists_derivedSupportedSectionsTriangle`: **Stacks
  0G72**, the distinguished triangle in the unbounded derived category, whose two canonical
  maps and connecting map are natural transformations of functors, hence functorial in `K`.

## Implementation notes

The functor `ℱ ↦ i_* ℋ_Z(ℱ)` is the endofunctor
`Stacks.SheafOfModules.SupportedSections.supportedSectionsFunctor` of `Mod(𝒪_X)` whose value
is the subsheaf of sections supported on `Z`; it agrees with the composite of the functor
`ℋ_Z` of sections supported on `Z`, with values in `𝒪_X|_Z`-modules, and pushforward along the
inclusion of `Z`, by the isomorphism
`supportedSectionsOnClosedFunctor_comp_modulePushforward_iso`.  The functor `ℱ ↦ j_*(ℱ|_U)` is
`Stacks.Cohomology.RestrictionCover.restrictPush`, restriction to `U` followed by pushforward.

Identifying the first functor as the kernel of the second is the only sheaf-level computation:
for `Z` closed, a section over `W` has support inside `Z ∩ W` exactly when it restricts to
zero on `W ∖ Z`, because a section all of whose germs vanish is zero.  Surjectivity of
restriction to `U` on an injective sheaf of modules is [Stacks, Tag 01EA].  Short exactness is
checked on sections over each open set and transported to sheaves of modules by the joint
faithfulness of the evaluation functors, exactly as for the Mayer--Vietoris sequence of
[Stacks, Tag 01EB].

Rather than fixing models for the two derived functors, the triangle is stated for arbitrary
functors on the unbounded derived category equipped with `Functor.IsRightDerivedFunctor` data,
so it applies to every choice of them; the two canonical maps are pinned down by their
composites with the supplied comparison maps.  The derived input is
`Stacks.Cohomology.RestrictionCover.derivedTriangleOfShortExactOnInjectives`: the functorial
K-injective resolution of [Stacks, Tag 079P] has injective terms, so applying the three
functors to it degreewise gives a short exact sequence of complexes, hence a distinguished
triangle, which is transported to the chosen derived functors.

## References

* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Lemma 20.8.1 (Tag 01EA)](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Definition 17.5.1 (Tag 0G6N)](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Lemma 20.26.4 (Tag 079P)](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Pretriangulated
open ExtensionByZeroModules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.RestrictionCover
open Stacks.Cohomology.SectionsWithSupport (openComplement)
open Stacks.SheafOfModules.SupportedSections

universe u

namespace Stacks.Cohomology.SupportedComplexes

attribute [local instance] HasDerivedCategory.standard

/-! ### The subsheaf of supported sections as the kernel of restriction -/

/-- Sections supported on a subset form an additive endofunctor of the sheaves of modules:
addition of morphisms is computed on sections, where the subsheaf is a submodule. -/
instance supportedSectionsFunctor_additive_endo (X : RingedSpace.{u, u}) (Z : Set X.carrier) :
    (supportedSectionsFunctor X Z).Additive where
  map_add := by
    intro M N f g
    apply _root_.SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext s
    exact Subtype.ext rfl

/-- The inclusion of the subsheaf of sections supported on `Z`, as a natural transformation
into the identity functor. -/
def supportedSectionsSubsheafInclusion (X : RingedSpace.{u, u}) (Z : Set X.carrier) :
    supportedSectionsFunctor X Z ⟶
      Functor.id (_root_.SheafOfModules.{u} (structureSheafRing X)) where
  app M := supportedSectionsSheafι Z M
  naturality _ _ f := supportedSectionsSheafι_naturality Z f

/-- For a closed subset `Z`, a section over `W` has support inside `Z ∩ W` exactly when it
restricts to zero on an open subset of `W` whose points are precisely the points of `W`
outside `Z`. -/
private theorem restrict_eq_zero_iff_suppSection_subset (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (M : _root_.SheafOfModules.{u} (structureSheafRing X))
    {W W' : Opens X.carrier} (i : W' ⟶ W)
    (hW' : ∀ x : X.carrier, x ∈ W' ↔ x ∈ W ∧ x ∉ Z) (s : M.val.obj (op W)) :
    M.val.presheaf.map i.op s = 0 ↔
      (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules M).suppSection W s ⊆
        Z ∩ (W : Set X.carrier) := by
  rw [← AlgebraicGeometry.SheafOfModules.mem_supportedSections_moduleSheaf_iff
    (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules M) Z W s]
  constructor
  · intro hs x hxW hxZ
    have h := TopCat.Presheaf.germ_res_apply M.val.presheaf i x ((hW' x).2 ⟨hxW, hxZ⟩) s
    rw [hs, map_zero] at h
    exact h.symm
  · intro hs
    exact TopCat.Presheaf.restrict_eq_zero_of_germ_eq_zero M.isSheaf i s fun x hx =>
      hs x (i.le hx) ((hW' x).1 hx).2

/-- The points of `W` meeting the open complement of `Z` are exactly the points of `W` outside
`Z`. -/
private theorem mem_openIntersection_openComplement_iff (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) (W : Opens X.carrier) (x : X.carrier) :
    x ∈ (openIntersection (openComplement Z hZ)).obj W ↔ x ∈ W ∧ x ∉ Z := by
  have hAW : (openIntersection (openComplement Z hZ)).obj W = W ⊓ openComplement Z hZ := by
    simp [openIntersection]
  rw [hAW]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- A section over an open set is killed by the unit `ℱ ⟶ j_*(ℱ|_U)` exactly when it is a
section supported on `Z`. -/
private theorem unit_app_val_app_eq_zero_iff_mem_range (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) (M : _root_.SheafOfModules.{u} (structureSheafRing X))
    (W : Opens X.carrier) (s : M.val.obj (op W)) :
    ((jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit.app M).val.app (op W)
        s = 0 ↔ s ∈ Set.range ((supportedSectionsSheafι Z M).val.app (op W)) := by
  rw [jStarAdjunction_unit_app_val_app (structureSheafRing X) (openComplement Z hZ) M (op W) s,
    mem_supportedSectionsSheafι_range_iff]
  exact restrict_eq_zero_iff_suppSection_subset X Z M
    ((openComplement Z hZ).isOpenEmbedding.isOpenMap.adjunction.counit.app W)
    (mem_openIntersection_openComplement_iff X Z hZ W) s

/-- Restricting a section supported on `Z` to the complement of `Z` gives zero. -/
theorem supportedSectionsSubsheafInclusion_comp_unit (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z) :
    supportedSectionsSubsheafInclusion X Z ≫
        (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit = 0 := by
  ext M W s
  exact (unit_app_val_app_eq_zero_iff_mem_range X Z hZ M (unop W) _).2 ⟨s, rfl⟩

/-- The short complex `i_* ℋ_Z(ℱ) ⟶ ℱ ⟶ j_*(ℱ|_U)` of a sheaf of modules on `X`: the
inclusion of the sections supported on `Z`, followed by restriction to the complement of
`Z`. -/
def supportedSectionsRestrictPushShortComplex (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    ShortComplex (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
  ShortComplex.mk ((supportedSectionsSubsheafInclusion X Z).app M)
    ((jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit.app M)
    (NatTrans.congr_app (supportedSectionsSubsheafInclusion_comp_unit X Z hZ) M)

/-- Short exactness of the short complex on sections over an open set, at an injective sheaf
of modules: the first map is the inclusion of a submodule, exactness in the middle says that
a section restricting to zero outside `Z` is supported on `Z`, and surjectivity of the second
map is [Stacks, Tag 01EA]. -/
private lemma supportedSectionsRestrictPushEvaluationShortExact (X : RingedSpace.{u, u})
    (Z : Set X.carrier) (hZ : IsClosed Z)
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) [Injective M] (W : Opens X.carrier) :
    ((supportedSectionsRestrictPushShortComplex X Z hZ M).map
      (SheafOfModules.evaluation (structureSheafRing X) (op W))).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
      (unit_app_val_app_eq_zero_iff_mem_range X Z hZ M W)
  · exact (ModuleCat.mono_iff_injective _).2 fun a b hab =>
      (supportedSectionsSheaf Z M).2.2.1 (op W) hab
  · refine (ModuleCat.epi_iff_surjective _).2 ?_
    intro z
    have hle : (openIntersection (openComplement Z hZ)).obj W ≤ W :=
      ((openComplement Z hZ).isOpenEmbedding.isOpenMap.adjunction.counit.app W).le
    obtain ⟨y, hy⟩ :=
      Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective
        (structureSheafRing X) M hle z
    refine ⟨y, ?_⟩
    refine Eq.trans (jStarAdjunction_unit_app_val_app (structureSheafRing X) (openComplement Z hZ) M
      (op W) y) ?_
    rwa [show (openComplement Z hZ).isOpenEmbedding.isOpenMap.adjunction.counit.app W =
        homOfLE hle from Subsingleton.elim _ _]

/-- **Short exactness at an injective sheaf of modules.**  For an injective `ℐ` the sequence
`0 ⟶ i_* ℋ_Z(ℐ) ⟶ ℐ ⟶ j_*(ℐ|_U) ⟶ 0` is short exact; this is the sheaf-level input to the
distinguished triangle. -/
@[sga "2 I 1.9" "(F), special case"]
theorem supportedSectionsRestrictPushShortExact (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z) (M : _root_.SheafOfModules.{u} (structureSheafRing X)) [Injective M] :
    (supportedSectionsRestrictPushShortComplex X Z hZ M).ShortExact := by
  let E : Opens X.carrier → (((Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) :=
    fun W => (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op W)
  have hfaith : JointlyFaithful E := by
    constructor
    intro A B f g h
    ext W x
    exact congrArg (fun f => f x) (h W.unop)
  have hreflect : JointlyReflectIsomorphisms E := hfaith.jointlyReflectsIsomorphisms
  let F : _root_.SheafOfModules.{u} (structureSheafRing X) ⥤
      ((Opens X.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
    SheafOfModules.toSheaf (structureSheafRing X) ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier
  have : (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier).Faithful :=
    TopCat.Sheaf.forgetFaithful AddCommGrpCat.{u} X.carrier
  have : F.Faithful := ⟨fun h => (SheafOfModules.toSheaf (structureSheafRing X)).map_injective
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier).map_injective h)⟩
  have : F.PreservesZeroMorphisms := ⟨by
    intro A B
    ext W x
    rfl⟩
  have : ∀ W, PreservesFiniteLimits (E W) := fun W =>
    preservesFiniteLimits_of_preservesFiniteLimitsOfSize (E W) fun J hJ => by
      dsimp [E]
      infer_instance
  have : ∀ W, PreservesFiniteColimits (E W) := fun W =>
    preservesFiniteColimits_of_preservesFiniteColimitsOfSize (E W) fun J hJ => by
      dsimp [E]
      infer_instance
  have hpresheaf : ((supportedSectionsRestrictPushShortComplex X Z hZ M).map F).ShortExact := by
    rw [JointlyReflectIsomorphisms.shortExact_iff hreflect]
    intro W
    exact (supportedSectionsRestrictPushEvaluationShortExact X Z hZ M W).map_of_exact
      (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op W))) AddCommGrpCat.{u})
  exact CategoryTheory.ShortExact.reflects_shortExact_of_faithful F hpresheaf

/-! ### The functorial distinguished triangle -/

/-- The identity functor of the derived category is a right derived functor of the identity
functor applied degreewise: the comparison is an isomorphism, so nothing has to be derived. -/
instance identityIsRightDerivedFunctorOfMapHomotopy (X : RingedSpace.{u, u}) :
    (Functor.id (DerivedCategory (_root_.SheafOfModules.{u}
      (structureSheafRing X)))).IsRightDerivedFunctor
      (Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ (Functor.id _)
    (Functor.isoWhiskerRight (homotopyIdentityIso (structureSheafRing X)).symm DerivedCategory.Qh)

/-- The canonical map from a right derived functor of `ℱ ↦ i_* ℋ_Z(ℱ)` to the identity, induced
by the inclusion of the subsheaf of sections supported on `Z`. -/
def derivedSupportedSectionsToId (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (aH : (supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    RH ⟶ Functor.id (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :=
  derivedRestrictionTransition (structureSheafRing X) _ _ RH (Functor.id _) aH
    (Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh)
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory
      (supportedSectionsSubsheafInclusion X Z) (ComplexShape.up ℤ)) DerivedCategory.Qh)

/-- The canonical map is determined by its composite with the derived units. -/
lemma derivedSupportedSectionsToId_fac (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (RH : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (aH : (supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    aH ≫ Functor.whiskerLeft DerivedCategory.Qh (derivedSupportedSectionsToId X Z RH aH) =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory
        (supportedSectionsSubsheafInclusion X Z) (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh :=
  (derivedRestrictionTransition_fac (structureSheafRing X) _ _ RH (Functor.id _) aH
    (Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh)
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory
      (supportedSectionsSubsheafInclusion X Z) (ComplexShape.up ℤ))
        DerivedCategory.Qh)).symm

/-- The canonical map from the identity to a right derived functor of `ℱ ↦ j_*(ℱ|_U)`, induced
by restriction to the open complement of `Z`. -/
def idToDerivedRestrictPush (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)
    (RJ : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (aJ : (restrictPush (structureSheafRing X) (openComplement Z hZ)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RJ)
    [RJ.IsRightDerivedFunctor aJ
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    (Functor.id (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) :
      DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
        DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) ⟶ RJ :=
  derivedRestrictionTransition (structureSheafRing X) _ _ (Functor.id _) RJ
    (Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh) aJ
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory
      (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit (ComplexShape.up ℤ))
        DerivedCategory.Qh)

/-- The canonical map is determined by its composite with the derived units. -/
lemma idToDerivedRestrictPush_fac (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z)
    (RJ : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (aJ : (restrictPush (structureSheafRing X) (openComplement Z hZ)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RJ)
    [RJ.IsRightDerivedFunctor aJ
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh ≫
        Functor.whiskerLeft DerivedCategory.Qh (idToDerivedRestrictPush X Z hZ RJ aJ) =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory
        (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫ aJ :=
  (derivedRestrictionTransition_fac (structureSheafRing X) _ _ (Functor.id _) RJ
    (Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh) aJ
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory
      (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit (ComplexShape.up ℤ))
        DerivedCategory.Qh)).symm

/-- **Stacks 0G72.** Let `Z` be a closed subset of a ringed space `X` and `j : U = X ∖ Z ⟶ X`
the inclusion of the complement.  For arbitrary right derived functors `RH` of
`ℱ ↦ i_* ℋ_Z(ℱ)` and `RJ` of `ℱ ↦ j_*(ℱ|_U)` on the unbounded derived category of
`𝒪_X`-modules, the two canonical maps `RH ⟶ 𝟭` and `𝟭 ⟶ RJ` extend to a connecting map `δ`
making `RH(K) ⟶ K ⟶ RJ(K) ⟶ RH(K)⟦1⟧` a distinguished triangle for every `K`.  All three maps
are natural transformations of functors, so the triangle is functorial in `K`. -/
@[stacks 0G72]
theorem exists_derivedSupportedSectionsTriangle (X : RingedSpace.{u, u}) (Z : Set X.carrier)
    (hZ : IsClosed Z)
    (RH RJ : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)))
    (aH : (supportedSectionsFunctor X Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RH)
    (aJ : (restrictPush (structureSheafRing X) (openComplement Z hZ)).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RJ)
    [RH.IsRightDerivedFunctor aH
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))]
    [RJ.IsRightDerivedFunctor aJ
      (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ))] :
    ∃ δ : RJ ⟶ RH ⋙ shiftFunctor
        (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) (1 : ℤ),
      ∀ K, Triangle.mk ((derivedSupportedSectionsToId X Z RH aH).app K)
          ((idToDerivedRestrictPush X Z hZ RJ aJ).app K) (δ.app K) ∈
        distTriang (DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))) := by
  obtain ⟨δ, hδ⟩ := derivedTriangleOfShortExactOnInjectives (structureSheafRing X)
    (supportedSectionsFunctor X Z) (Functor.id _)
    (restrictPush (structureSheafRing X) (openComplement Z hZ))
    (supportedSectionsSubsheafInclusion X Z)
    (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit
    (supportedSectionsSubsheafInclusion_comp_unit X Z hZ)
    (fun I _ => supportedSectionsRestrictPushShortExact X Z hZ I)
    RH (Functor.id _) RJ
    (resolutionDerivedIso (structureSheafRing X) (supportedSectionsFunctor X Z) RH aH)
    (resolutionDerivedIso (structureSheafRing X) (Functor.id _) (Functor.id _)
      (Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh))
    (resolutionDerivedIso (structureSheafRing X)
      (restrictPush (structureSheafRing X) (openComplement Z hZ)) RJ aJ)
    (derivedSupportedSectionsToId X Z RH aH) (idToDerivedRestrictPush X Z hZ RJ aJ)
    (fun K => resolutionDerivedIso_fac (structureSheafRing X)
      (F := supportedSectionsFunctor X Z) (G := Functor.id _) (RF := RH)
      (RG := Functor.id _) aH
      (Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh)
      (supportedSectionsSubsheafInclusion X Z) (derivedSupportedSectionsToId X Z RH aH)
      (derivedSupportedSectionsToId_fac X Z RH aH) K)
    (fun K => resolutionDerivedIso_fac (structureSheafRing X)
      (F := Functor.id _) (G := restrictPush (structureSheafRing X) (openComplement Z hZ))
      (RF := Functor.id _) (RG := RJ)
      (Functor.whiskerRight (homotopyIdentityIso (structureSheafRing X)).hom DerivedCategory.Qh) aJ
      (jStarAdjunction (openComplement Z hZ) (structureSheafRing X)).unit
      (idToDerivedRestrictPush X Z hZ RJ aJ)
      (idToDerivedRestrictPush_fac X Z hZ RJ aJ) K)
  exact ⟨δ, hδ⟩

end Stacks.Cohomology.SupportedComplexes

end
