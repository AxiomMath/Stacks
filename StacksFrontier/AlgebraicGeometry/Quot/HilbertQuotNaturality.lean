module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotObjectwise
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit

/-!
# Naturality in the test scheme of the comparison of the Hilbert and Quot functors

Let `f : X ⟶ Y` be a morphism of algebraic spaces of finite presentation. A family `Z ⊆ X_T`
classified by the Hilbert functor of `f` determines the quotient of `F_T` by its defining ideal
sheaf `𝓘_Z` (Stacks 0D00). The Hilbert functor restricts a family by taking the inverse image
`Z' = Z ×_{X_T} X_{T'}` of its closed subspace (`CategoryTheory.Subfunctor.preimage`), while the
Quot functor restricts a quotient by pulling it back
(`AlgebraicGeometry.Space.QuotientSituation.quotientPullback`), which records the pulled-back
quotient *by its kernel*. This file proves that the kernel of `g^*(F_T/𝓘_Z)` is `𝓘_{Z'}`, for
`g : X_{T'} ⟶ X_T` the transition map of base changes, so that the comparison of the two functors
is natural in the test scheme. No flatness is assumed.

## Main definitions

* `AlgebraicGeometry.Space.structureSheafTestSchemeMap`: a morphism of schemes over the functor of
  points of `Y`, read as a morphism of test schemes of the Quot situation.
* `AlgebraicGeometry.Space.baseChangeIdealSheafMap`: the map `g^*𝓘_Z ⟶ 𝓘_{g⁻¹(Z)}` of
  Stacks 04CP at the transition map of base changes.

## Main results

* `AlgebraicGeometry.Space.quotientPullback_subobject_definingIdealSheaf`: the pullback of the
  quotient `F_T/𝓘_Z` is the quotient by the defining ideal sheaf of the inverse image `g⁻¹(Z)`.
* `AlgebraicGeometry.Space.quotientPullback_hilbertFamilySubobject`: naturality of the forward
  map of Stacks 0D00, the same statement for the base change of a family classified by the
  Hilbert functor.
* `AlgebraicGeometry.Space.structureModulePullbackMap_comp_baseChangeComparison`: the comparison
  of base changes of the Quot situation is compatible with the identification `F_T ≅ 𝒪_{X_T}`.
* `baseChangeIdealSheafMap_comp_definingIdealSheaf_ι_comp_baseChangeComparison`: the map of
  Stacks 04CP, the inclusion of the upper ideal sheaf and the comparison, in terms of the inverse
  image of the lower inclusion.
* `AlgebraicGeometry.Space.relativeMap_structureSheafTestSchemeMap`: the transition map of the
  Quot situation is the transition map `X_{T'} ⟶ X_T` the Hilbert functor is stated with.
* `AlgebraicGeometry.Space.preservesFiniteColimits_spaceModulePullback`: the inverse image of
  `𝒪`-modules is right exact.
* `AlgebraicGeometry.Space.epi_map_comp_baseChangeIdealSheafMap`: the map
  `g^*𝓘_Z ⟶ 𝓘_{g⁻¹(Z)}`, precomposed with the inverse image of an isomorphism, is an
  epimorphism.

## Implementation notes

Since the Quot functor records the pulled-back quotient by its kernel, naturality needs only that
`g^*𝓘_Z ⟶ 𝓘_{Z'}` be an *epimorphism*: the kernel of `g^*` applied to `F_T ↠ F_T/𝓘_Z` is the
image of `g^*𝓘_Z`, by right exactness of `g^*`, and an epimorphism onto `𝓘_{Z'}` makes that image
`𝓘_{Z'}`. The epimorphism is `AlgebraicGeometry.Space.epi_idealSheafMap`, the surjectivity
clause of Stacks 04CQ at the fibre product square. Injectivity of `g^*𝓘_Z ⟶ 𝓘_{Z'}`, which
requires flatness of `g`, is not needed, and neither is a base-change comparison for direct
images.

One spelling is used for each object: the transition map is always
`AlgebraicGeometry.Space.baseChangeMap f h`, the base change `X_T` is always
`AlgebraicGeometry.Space.baseChangeSpace f (structureSheafTestScheme T)`, and the identification
`F_T ≅ 𝒪_{X_T}` is always `AlgebraicGeometry.Space.baseChangeModuleIsoStructureSheaf`. The two
spellings of that identification are crossed only by rewriting with
`AlgebraicGeometry.Space.baseChangeModuleIsoStructureSheaf_eq_modulePullbackUnitIso`, an equation
of isomorphisms: comparing the two spellings beneath `CategoryTheory.Iso.hom` by unification
unfolds the heavy definitions.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- Left in place, this instance is selected ahead of `SheafOfModules.instAbelian` and leaves the
-- module universe of every subobject and cokernel below unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-! ### The morphism of test schemes -/

/-- A morphism of schemes over the functor of points of `Y`, read as a morphism of test schemes of
a quotient situation on `Y`, the morphism of presheaves it commutes with being wrapped as a
morphism of algebraic spaces as in `AlgebraicGeometry.Space.structureSheafTestScheme`. -/
def structureSheafTestSchemeMap {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T) :
    (structureSheafTestScheme T' : SchemesOver Y) ⟶ structureSheafTestScheme T :=
  CostructuredArrow.homMk g.left (ObjectProperty.hom_ext _ g.w)

variable (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)

/-- **The transition map of the Quot situation is the transition map of base changes the Hilbert
functor is stated with.** Both are the morphism `X_{T'} ⟶ X_T` determined by the two
projections, the Quot side taken as `CategoryTheory.IsPullback.lift` of the fibre product of
algebraic spaces and the Hilbert side as `CategoryTheory.Limits.pullback.lift` of the fibre
product of presheaves. -/
theorem relativeMap_structureSheafTestSchemeMap {T T' : SchemesOverPresheaf B S hS Y}
    (g : T' ⟶ T) :
    baseChangeMap f (structureSheafTestSchemeMap g) =
      ObjectProperty.homMk (schemeBaseChangeMap f g) := by
  refine baseChange_hom_ext f ?_ ?_
  · refine Eq.trans (baseChangeMap_comp_projection f (structureSheafTestSchemeMap g)) ?_
    exact (ObjectProperty.hom_ext _ (schemeBaseChangeMap_fst f g)).symm
  · refine Eq.trans (baseChangeMap_comp_inclusion f (structureSheafTestSchemeMap g)) ?_
    exact (ObjectProperty.hom_ext _ (schemeBaseChangeMap_snd f g)).symm

/-! ### Naturality of the subobject cut out by a closed subspace -/

/-- **The inverse image of `𝒪`-modules preserves finite colimits**, being a left adjoint by the
adjunction half of Stacks 03LU. -/
theorem preservesFiniteColimits_spaceModulePullback {Xu Xd : AlgebraicSpaces B S hS}
    (q : Xu ⟶ Xd) : PreservesFiniteColimits (modulePullback B S hS q) :=
  have := (modulePullbackAdjunction B S hS q).leftAdjoint_preservesColimits
  inferInstance

section Preimage

variable (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
  {T T' : SchemesOverPresheaf B S hS Y}
  (h : (structureSheafTestScheme T' : SchemesOver Y) ⟶ structureSheafTestScheme T)
  (Zd : ClosedSubspaces B S hS (baseChangeSpace f (structureSheafTestScheme T)).1)

/-- **The map `g^*𝓘_Z ⟶ 𝓘_{g⁻¹(Z)}` of Stacks 04CP for the transition map of base changes**, at
the fibre product square whose upper closed subspace is the inverse image of `Z` of
Stacks 083Q. -/
abbrev baseChangeIdealSheafMap :
    (modulePullback B S hS (baseChangeMap f h)).obj
        (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T))
          Zd).toSheafOfModules ⟶
      (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T'))
        (preimageSubspace B S hS (baseChangeMap f h) Zd)).toSheafOfModules :=
  idealSheafMap B S hS
    (preimageSubspace B S hS (baseChangeMap f h) Zd) Zd (baseChangeMap f h)
    (preimageProjection B S hS (baseChangeMap f h) Zd)
    (conormalEtaleRestrictionSquare B S hS (baseChangeMap f h) Zd)

/-- The identification `F_T ≅ 𝒪_{X_T}` of the Quot situation of `𝒪_X/X/B` is the identification
of [Stacks Project, Tag 03LU] along the projection `X_T ⟶ X`. -/
theorem baseChangeModuleIsoStructureSheaf_eq_modulePullbackUnitIso
    (W : SchemesOverPresheaf B S hS Y) :
    baseChangeModuleIsoStructureSheaf f hf W =
      modulePullbackUnitIso B S hS (baseChangeProjection f (structureSheafTestScheme W)) :=
  rfl

/-- **The comparison of base changes of the Quot situation of `𝒪_X/X/B` is compatible with the
identification `F_T ≅ 𝒪_{X_T}`.** Transporting a submodule of `𝒪_{X_{T'}}` into `F_{T'}` and
then across the comparison `F_{T'} ≅ (X_{T'} ⟶ X_T)^*F_T` is pulling back along `X_{T'} ⟶ X_T`
the transport of a submodule of `𝒪_{X_T}` into `F_T`, corrected by `g^*𝒪_{X_T} ≅ 𝒪_{X_{T'}}`. -/
theorem structureModulePullbackMap_comp_baseChangeComparison :
    (modulePullbackUnitIso B S hS (baseChangeMap f h)).hom ≫
        (baseChangeModuleIsoStructureSheaf f hf T').inv ≫
        (modulePullbackTriangle B S hS (baseChangeMap_comp_projection f h)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X)) =
      (modulePullback B S hS (baseChangeMap f h)).map
        (baseChangeModuleIsoStructureSheaf f hf T).inv := by
  simp only [baseChangeModuleIsoStructureSheaf_eq_modulePullbackUnitIso]
  exact modulePullbackUnitIso_hom_comp_inv_comp_modulePullbackTriangle_hom_app B S hS
    (baseChangeMap f h) (baseChangeProjection f (structureSheafTestScheme T))
    (baseChangeMap_comp_projection f h)

/-- **The map of Stacks 04CP for the transition map of base changes, followed by the inclusion of
the upper ideal sheaf, is the inverse image of the lower inclusion** read through
`g^*𝒪_{X_T} ⟶ 𝒪_{X_{T'}}`, at the fibre product square of Stacks 083Q. -/
theorem baseChangeIdealSheafMap_comp_definingIdealSheaf_ι :
    baseChangeIdealSheafMap f h Zd ≫
        (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T'))
          (preimageSubspace B S hS (baseChangeMap f h) Zd)).ι =
      (modulePullback B S hS (baseChangeMap f h)).map
          (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T)) Zd).ι ≫
        structureModulePullbackMap B S hS (baseChangeMap f h) :=
  idealSheafMap_comp_definingIdealSheaf_ι B S hS
    (preimageSubspace B S hS (baseChangeMap f h) Zd) Zd (baseChangeMap f h)
    (preimageProjection B S hS (baseChangeMap f h) Zd)
    (conormalEtaleRestrictionSquare B S hS (baseChangeMap f h) Zd)

/-- **The map of Stacks 04CP, the inclusion of the upper ideal sheaf and the comparison of base
changes, in terms of the inverse image of the lower inclusion.** The two ways of landing
`g^*𝓘_Z` inside `g^*F_T` — through `𝓘_{g⁻¹(Z)} ⊆ 𝒪_{X_{T'}} ≅ F_{T'}` and the comparison, or as
the inverse image of `𝓘_Z ⊆ 𝒪_{X_T} ≅ F_T` — agree. -/
theorem baseChangeIdealSheafMap_comp_definingIdealSheaf_ι_comp_baseChangeComparison :
    baseChangeIdealSheafMap f h Zd ≫
        (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T'))
          (preimageSubspace B S hS (baseChangeMap f h) Zd)).ι ≫
        (baseChangeModuleIsoStructureSheaf f hf T').inv ≫
        (modulePullbackTriangle B S hS (baseChangeMap_comp_projection f h)).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X)) =
      (modulePullback B S hS (baseChangeMap f h)).map
          (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T)) Zd).ι ≫
        (modulePullback B S hS (baseChangeMap f h)).map
          (baseChangeModuleIsoStructureSheaf f hf T).inv :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans (eq_whisker (baseChangeIdealSheafMap_comp_definingIdealSheaf_ι f h Zd) _)
      (Eq.trans (Category.assoc _ _ _)
        (whisker_eq _
          (Eq.trans
            (eq_whisker (structureModulePullbackMap_eq_modulePullbackUnitIso_hom B S hS
              (baseChangeMap f h)) _)
            (structureModulePullbackMap_comp_baseChangeComparison f hf h)))))

variable (K : Subobject ((structureSheafQuotSituation f hf).baseChangeModule
    (structureSheafTestScheme T)))
  (κ : (K : Modules.{u, u} B S hS
      ((structureSheafQuotSituation f hf).space (structureSheafTestScheme T)).1
      ((structureSheafQuotSituation f hf).space (structureSheafTestScheme T)).2) ≅
    (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T))
      Zd).toSheafOfModules)

/-- The image under `g^*` of the arrow of a subobject identified with the defining ideal sheaf,
split along that identification. -/
theorem modulePullback_map_arrow_eq
    (hκ : κ.inv ≫ K.arrow =
      (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T)) Zd).ι ≫
        (baseChangeModuleIsoStructureSheaf f hf T).inv) :
    (modulePullback B S hS (baseChangeMap f h)).map K.arrow =
      (modulePullback B S hS (baseChangeMap f h)).map κ.hom ≫
        ((modulePullback B S hS (baseChangeMap f h)).map
            (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T)) Zd).ι ≫
          (modulePullback B S hS (baseChangeMap f h)).map
            (baseChangeModuleIsoStructureSheaf f hf T).inv) := by
  rw [(Iso.inv_comp_eq κ).mp hκ]
  exact ((modulePullback B S hS (baseChangeMap f h)).map_comp _ _).trans
    (congrArg (fun t ↦
      (modulePullback B S hS (baseChangeMap f h)).map κ.hom ≫ t)
      ((modulePullback B S hS (baseChangeMap f h)).map_comp _ _))

/-- The map of Stacks 04CP for the transition map of base changes, precomposed with the
identification of the underlying object of a subobject with the defining ideal sheaf, is an
epimorphism, by the surjectivity clause of Stacks 04CQ at the fibre product square. -/
theorem epi_map_comp_baseChangeIdealSheafMap :
    Epi ((modulePullback B S hS (baseChangeMap f h)).map κ.hom ≫
      baseChangeIdealSheafMap f h Zd) :=
  epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom ((modulePullback B S hS
      (baseChangeMap f h)).mapIso κ)))
    (epi_idealSheafMap B S hS (baseChangeMap f h) Zd)

/-- **Naturality of the subobject cut out by a closed subspace of the base change.** Pulling
back the quotient `F_T/𝓘_Z` along a morphism `T' ⟶ T` of test schemes gives the quotient of
`F_{T'}` by the defining ideal sheaf of the inverse image `g⁻¹(Z) = Z ×_{X_T} X_{T'}`. -/
theorem quotientPullback_subobject_definingIdealSheaf :
    (structureSheafQuotSituation f hf).quotientPullback h (definingIdealSubobject f hf T Zd) =
      definingIdealSubobject f hf T' (preimageSubspace B S hS (baseChangeMap f h) Zd) := by
  have := preservesFiniteColimits_spaceModulePullback (baseChangeMap f h)
  have := mono_definingIdealArrow f hf T Zd
  let e := Subobject.underlyingIso (definingIdealArrow f hf T Zd)
  refine Functor.conjSubobject_eq_mk_of_epi
    (modulePullbackTriangle B S hS (baseChangeMap_comp_projection f h))
    (M := SheafOfModules.unit (structureRingSheaf B S hS X))
    (definingIdealSubobject f hf T Zd)
    (definingIdealArrow f hf T' (preimageSubspace B S hS (baseChangeMap f h) Zd))
    (mono_definingIdealArrow f hf T' (preimageSubspace B S hS (baseChangeMap f h) Zd))
    ((modulePullback B S hS (baseChangeMap f h)).map e.hom ≫ baseChangeIdealSheafMap f h Zd)
    (epi_map_comp_baseChangeIdealSheafMap f hf h Zd (definingIdealSubobject f hf T Zd) e) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ ?_)
    (modulePullback_map_arrow_eq f hf h Zd (definingIdealSubobject f hf T Zd) e
      (underlyingIso_inv_comp_definingIdealSubobject_arrow f hf T Zd)).symm
  exact Eq.trans (whisker_eq _ (Category.assoc _ _ _))
    (baseChangeIdealSheafMap_comp_definingIdealSheaf_ι_comp_baseChangeComparison f hf h Zd)

end Preimage

/-! ### Naturality for a family classified by the Hilbert functor -/

variable (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)

/-- The inverse image of the closed subspace of a Hilbert family along the transition map of the
Quot situation is the closed subspace of its base change. -/
theorem preimageSubspace_eq_baseChange_closedSubspace
    {T T' : SchemesOverPresheaf B S hS Y} (g : T' ⟶ T) (z : HilbertFamily f T) :
    preimageSubspace B S hS (baseChangeMap f (structureSheafTestSchemeMap g))
        ⟨z.Z, z.closed⟩ =
      ⟨(z.baseChange g).Z, (z.baseChange g).closed⟩ :=
  Subtype.ext (congrArg z.Z.preimage
    (congrArg (fun m ↦ m.hom) (relativeMap_structureSheafTestSchemeMap f g)))

/-- **Naturality in the test scheme of the forward map of Stacks 0D00.** The quotient of
`F_{T'}` attached to the base change of a family classified by the Hilbert functor is the
pullback of the quotient of `F_T` attached to the family. -/
theorem quotientPullback_hilbertFamilySubobject {T T' : SchemesOverPresheaf B S hS Y}
    (g : T' ⟶ T) (z : HilbertFamily f T) :
    (structureSheafQuotSituation f hf).quotientPullback (structureSheafTestSchemeMap g)
        (hilbertFamilySubobject f hf T z) =
      hilbertFamilySubobject f hf T' (z.baseChange g) :=
  Eq.trans
    (quotientPullback_subobject_definingIdealSheaf f hf (structureSheafTestSchemeMap g)
      ⟨z.Z, z.closed⟩)
    (congrArg (definingIdealSubobject f hf T')
      (preimageSubspace_eq_baseChange_closedSubspace f g z))

end AlgebraicGeometry.Space

end
