module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleDerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringSimplicialObjectModuleCohomologicalDescentUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsInitial
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived

/-!
# Derived sections over `X` along a hypercovering of `X` by a simplicial object of the site

Let `C` be a site with fibre products, given by a pretopology `P`, let `X` be an object of `C`,
let `O_C` be a sheaf of commutative rings on `C` and let `a : U ⟶ X` be a hypercovering of `X` in
`C` by a simplicial object `U` of `C`. With `O_X = O_C|_{C/X}`, `O = a⁻¹O_X` on the total site
`(C/U)_total` and `a : (Sh((C/U)_total), O) ⟶ (Sh(C/X), O_X)` the ringed augmentation, there is
a canonical isomorphism

`RΓ(X, E) = RΓ((C/U)_total, La^*E)`

of functors on the unbounded derived category `D(O_C)`. Here `RΓ(X, -)` takes values in
`D(O_C(X))`, and the right hand side, which lives in `D(Γ((C/U)_total, O))`, is read in
`D(O_C(X))` through restriction of scalars along the canonical ring map
`O_C(X) ⟶ Γ(C/X, O_X) ⟶ Γ((C/U)_total, O)` (`totalSectionsRingHom`).

## Main definitions

All names below are in the namespace `CategoryTheory.SimplicialSemiRepresentable`.

* `derivedModuleSectionsOverObject`: `RΓ(X, -)`, valued in `D(O_C(X))`.
* `derivedTotalGlobalSections`: `RΓ((C/K)_total, -)`, valued in `D(Γ((C/K)_total, O))`.
* `totalSectionsRingHom`: the ring map `O_C(X) ⟶ Γ((C/K)_total, O)`.
* `derivedModuleSectionsOverObjectIsoOfIsHypercovering`: `RΓ(X, E) = RΓ((C/K)_total, La^*E)` for
  a hypercovering `K` of `X`.
* `derivedModuleSectionsOverObjectIsoOfIsHypercoveringAugmentation`:
  `RΓ(X, E) = RΓ((C/U)_total, La^*E)` for a hypercovering `a : U ⟶ X` by a simplicial object.

## Main results

* `derivedModuleSectionsOverObjectIsoOfIsHypercovering_hom_app`: the forward map of
  `derivedModuleSectionsOverObjectIsoOfIsHypercovering` is the canonical one.
* `derivedModuleSectionsOverObjectIsoOfIsHypercoveringAugmentation_hom_app`: the forward map of
  `derivedModuleSectionsOverObjectIsoOfIsHypercoveringAugmentation` is the canonical one:
  `RΓ(X, -)` of the derived unit `E|_X ⟶ Ra_*La^*(E|_X)`, between the two comparisons of derived
  functors.

## Implementation notes

The slice category of modules has two spellings that are definitionally but not reducibly equal:
`SheafOfModules ((ringSheaf O_C).over X)`, the target of restriction, and
`SheafOfModules (ringSheaf (O_C.over X))`, the module category of the ringed topos the
augmentation maps to. Instance search does not cross them, so the one place where a functor on the
first is composed with a functor out of the second (`derivedPushforwardModuleSectionsAtIdIso`)
supplies the two additivity instances explicitly.

## References

* [Stacks Project, Tag 0DAD](https://stacks.math.columbia.edu/tag/0DAD)
* [Stacks Project, Tag 0DA6](https://stacks.math.columbia.edu/tag/0DA6)
* [Stacks Project, Tag 0DA1](https://stacks.math.columbia.edu/tag/0DA1)
* [Stacks Project, Tag 0DA5](https://stacks.math.columbia.edu/tag/0DA5)
* [Stacks Project, Tag 0DAC](https://stacks.math.columbia.edu/tag/0DAC)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 0D9X](https://stacks.math.columbia.edu/tag/0D9X)
* [Stacks Project, Section 85.21 (Tag 09X8)](https://stacks.math.columbia.edu/tag/09X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering Stacks.Cohomology.SiteModules

attribute [local instance]
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentWEqualsLocallyBijectiveTotal
  CategoryTheory.SimplicialSiteSituation.objectModuleDescentHasWeakSheafifyComponent

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open CategoryTheory.SimplicialSiteSituation SemiRepresentable

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))
  (OC : Sheaf P.toGrothendieck CommRingCat.{u})

/-- The ringed site `(C, O_C)`. -/
abbrev ringedSite : RingedSite.{u, u, u} := ⟨C, P.toGrothendieck, OC⟩

/-- The ring `O_C(X)` of sections of the structure sheaf over `X`. -/
abbrev sectionsRing (X : C) : RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf OC).obj.obj (op X)

/-- The structure sheaf `O_X = O_C|_{C/X}` of the slice site, as a sheaf of rings. -/
abbrev sliceRingSheaf (X : C) : Sheaf (P.toGrothendieck.over X) RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf OC).over X

/-- `Γ(X, -)`: sections over `X` of a sheaf of `O_C`-modules, as an `O_C(X)`-module. -/
abbrev moduleSectionsOverObject :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC) ⥤
      ModuleCat.{u} (sectionsRing P OC X) :=
  SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf OC) (op X)

/-- Sections at the final object `id_X` of `C/X`, as an `O_C(X)`-module. -/
abbrev moduleSectionsAtId :
    SheafOfModules.{u} (sliceRingSheaf P OC X) ⥤ ModuleCat.{u} (sectionsRing P OC X) :=
  SheafOfModules.evaluation (sliceRingSheaf P OC X) (op (Over.mk (𝟙 X)))

/-- Sections at `id_X` form an additive functor. -/
instance additive_moduleSectionsAtId : (moduleSectionsAtId (X := X) P OC).Additive where
  map_add := rfl

/-- The identity of `X` is an initial object of `(C/X)ᵒᵖ`. -/
def isInitialOpMkId (X : C) : IsInitial (op (Over.mk (𝟙 X))) := Over.mkIdTerminal.op

/-- The ring map `O_C(X) ⟶ Γ(C/X, O_X)`, the inverse of evaluation of a global section at the final
object `id_X`: a section over `X` is the family of its restrictions. -/
def sectionsRingToGlobal : sectionsRing P OC X →+* GlobalSectionRing (sliceRingSheaf P OC X) :=
  (globalSectionRingEquivInitial (sliceRingSheaf P OC X) (op (Over.mk (𝟙 X)))
    (isInitialOpMkId X)).symm.toRingHom

/-- Global sections on `C/X` of a sheaf of `O_X`-modules are its sections at `id_X`. -/
def sectionsAtIdEquiv (M : SheafOfModules.{u} (sliceRingSheaf P OC X)) :
    GlobalSections (sliceRingSheaf P OC X) M ≃ M.val.obj (op (Over.mk (𝟙 X))) :=
  globalSectionsEquivInitial (sliceRingSheaf P OC X) M (op (Over.mk (𝟙 X))) (isInitialOpMkId X)

/-- Sections at `id_X` of a sheaf of `O_X`-modules are its global sections on `C/X`, as
`O_C(X)`-modules. -/
def sectionsAtIdLinearEquiv (M : SheafOfModules.{u} (sliceRingSheaf P OC X)) :
    ((ModuleCat.restrictScalars (sectionsRingToGlobal P OC)).obj
      ((globalSectionsFunctor.{u, u, u, u} (sliceRingSheaf P OC X)).obj M)) ≃ₗ[sectionsRing P OC X]
      ((moduleSectionsAtId P OC).obj M) where
  toFun s := sectionsAtIdEquiv P OC M s
  invFun m := (sectionsAtIdEquiv P OC M).symm m
  left_inv := (sectionsAtIdEquiv P OC M).left_inv
  right_inv := (sectionsAtIdEquiv P OC M).right_inv
  map_add' _ _ := rfl
  map_smul' a s := by
    rw [ModuleCat.restrictScalars.smul_def]
    exact congrArg
      (fun r : (sliceRingSheaf P OC X).obj.obj (op (Over.mk (𝟙 X))) =>
        r • (sectionsAtIdEquiv P OC M) s)
      ((globalSectionRingEquivInitial (sliceRingSheaf P OC X) (op (Over.mk (𝟙 X)))
        (isInitialOpMkId X)).apply_symm_apply a)

/-- Sections at `id_X` are global sections on `C/X`, read over `O_C(X)`. -/
def moduleSectionsAtIdIso :
    globalSectionsFunctor.{u, u, u, u} (sliceRingSheaf P OC X) ⋙
        ModuleCat.restrictScalars (sectionsRingToGlobal P OC) ≅
      moduleSectionsAtId P OC :=
  NatIso.ofComponents (fun M => (sectionsAtIdLinearEquiv P OC M).toModuleIso) (fun _ => by ext; rfl)

/-- The ringed topos `(Sh((C/K)_total), O)` of the total site of `K`. -/
abbrev totalTopos : RingedTopos.{u, u, u} :=
  (situation (P.toGrothendieck.over X) K).totalRingedTopos
    (hypercoveringObjectRingedAugmentation P K OC).O

/-- The ringed topos `(Sh(C/X), O_X)` of the slice site. -/
abbrev sliceTopos : RingedTopos.{u, u, u} :=
  (hypercoveringObjectRingedAugmentation P K OC).augmentationRingedTopos

/-- The ringed augmentation `a : (Sh((C/K)_total), O) ⟶ (Sh(C/X), O_X)`. -/
abbrev augmentationHom : RingedToposHom (totalTopos P K OC) (sliceTopos P K OC) :=
  (hypercoveringObjectRingedAugmentation P K OC).totalRingedHom

/-- The ring map `Γ(C/X, O_X) ⟶ Γ((C/K)_total, O)` induced by the augmentation. -/
abbrev augmentationGlobalSectionsRingHom :
    GlobalSectionRing (sliceRingSheaf P OC X) →+*
      GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf (totalTopos P K OC).O) :=
  globalSectionsRingHom (X := totalTopos P K OC) (Y := sliceTopos P K OC)
    (augmentationHom P K OC).toModulesHom

/-- The ring map `O_C(X) ⟶ Γ((C/K)_total, O)`: restriction to `C/X` followed by the map on global
sections induced by the augmentation. -/
def totalSectionsRingHom :
    sectionsRing P OC X →+*
      GlobalSectionRing (Stacks.SheafOfModules.Tensor.ringSheaf (totalTopos P K OC).O) :=
  (augmentationGlobalSectionsRingHom P K OC).comp (sectionsRingToGlobal P OC)

/-- `totalSectionsRingHom` is the composite of its two factors. -/
lemma totalSectionsRingHom_eq :
    totalSectionsRingHom P K OC =
      (augmentationGlobalSectionsRingHom P K OC).comp
        (sectionsRingToGlobal P OC) := rfl

/-- Restriction of scalars along `O_C(X) ⟶ Γ((C/K)_total, O)` is restriction along its two
factors. -/
def restrictScalarsTotalSectionsRingHomIso :
    ModuleCat.restrictScalars (augmentationGlobalSectionsRingHom P K OC) ⋙
        ModuleCat.restrictScalars (sectionsRingToGlobal P OC) ≅
      ModuleCat.restrictScalars (totalSectionsRingHom P K OC) :=
  (ModuleCat.restrictScalarsComp' (sectionsRingToGlobal P OC)
    (augmentationGlobalSectionsRingHom P K OC) (totalSectionsRingHom P K OC)
    (totalSectionsRingHom_eq P K OC)).symm

/-- The underived identity `Γ(C/X, a_*F) = Γ((C/K)_total, F)` of `Γ(C/X, O_X)`-modules, for the
direct image of the ringed augmentation. -/
def pushforwardGlobalSectionsIso :
    RingedToposHom.pushforwardModules (X := totalTopos P K OC) (Y := sliceTopos P K OC)
        (augmentationHom P K OC) ⋙
        globalSectionsFunctor.{u, u, u, u} (sliceRingSheaf P OC X) ≅
      globalSectionsFunctor.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (totalTopos P K OC).O) ⋙
        ModuleCat.restrictScalars (augmentationGlobalSectionsRingHom P K OC) :=
  Functor.isoWhiskerRight (augmentationHom P K OC).toModulesPushforwardIso.symm _ ≪≫
    globalSectionsPushforwardIso (X := totalTopos P K OC) (Y := sliceTopos P K OC)
      (augmentationHom P K OC).toModulesHom

/-- **The underived identity `Γ(X, a_*F) = Γ((C/K)_total, F)` of `O_C(X)`-modules**, the right
hand side read through restriction of scalars along `O_C(X) ⟶ Γ((C/K)_total, O)`. -/
def pushforwardModuleSectionsAtIdIso :
    RingedToposHom.pushforwardModules (X := totalTopos P K OC) (Y := sliceTopos P K OC)
        (augmentationHom P K OC) ⋙ moduleSectionsAtId P OC ≅
      globalSectionsFunctor.{u, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (totalTopos P K OC).O) ⋙
        ModuleCat.restrictScalars (totalSectionsRingHom P K OC) :=
  Functor.isoWhiskerLeft _ (moduleSectionsAtIdIso P OC).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pushforwardGlobalSectionsIso P K OC) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (restrictScalarsTotalSectionsRingHomIso P K OC)

variable (X) in
/-- `RΓ(X, -) : D(O_C) ⥤ D(O_C(X))`, the total right derived functor of sections over `X`. -/
abbrev derivedModuleSectionsOverObject :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC)) ⥤
      DerivedCategory (ModuleCat.{u} (sectionsRing P OC X)) :=
  Stacks.DerivedFunctor.totalRightDerived (moduleSectionsOverObject (X := X) P OC)

/-- `RΓ((C/K)_total, -) : D(O) ⥤ D(Γ((C/K)_total, O))`. -/
abbrev derivedTotalGlobalSections :
    DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (totalTopos P K OC).O)) ⥤
      DerivedCategory (ModuleCat.{u} (GlobalSectionRing
        (Stacks.SheafOfModules.Tensor.ringSheaf (totalTopos P K OC).O))) :=
  Stacks.DerivedFunctor.totalRightDerived
    (globalSectionsFunctor.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (totalTopos P K OC).O))

variable (X) in
/-- `RΓ(C/X, -) : D(O_X) ⥤ D(O_C(X))`, the total right derived functor of sections at the final
object `id_X` of `C/X`. -/
abbrev derivedModuleSectionsAtId :
    DerivedCategory (SheafOfModules.{u} (sliceRingSheaf P OC X)) ⥤
      DerivedCategory (ModuleCat.{u} (sectionsRing P OC X)) :=
  Stacks.DerivedFunctor.totalRightDerived (moduleSectionsAtId (X := X) P OC)

/-- Sections over `X` are sections at `id_X` of the restriction to `C/X`. -/
def moduleSectionsOverObjectIsoRestriction :
    SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf OC) X ⋙
        moduleSectionsAtId P OC ≅ moduleSectionsOverObject P OC :=
  Iso.refl _

/-- `RΓ(X, E) = RΓ(C/X, E|_X)`, at the level of `O_C(X)`-modules: restriction to `C/X` is exact
and preserves K-injective complexes, and sections over `X` are sections at `id_X` of the
restriction. -/
def derivedModuleSectionsOverObjectIsoRestriction :
    derivedModuleSectionsOverObject P X OC ≅
      Stacks.Cohomology.Localization.derivedRestriction (ringedSite P OC) X ⋙
        derivedModuleSectionsAtId P X OC :=
  (Stacks.Cohomology.LerayUnbounded.derivedCompIso
    (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf OC) X)
    (moduleSectionsAtId P OC) (moduleSectionsOverObject P OC)
    (moduleSectionsOverObjectIsoRestriction P OC)
    (fun I hI => @Stacks.Cohomology.Localization.isKInjective_over _ _ P.toGrothendieck
      (Stacks.SheafOfModules.Tensor.ringSheaf OC) X I hI)).symm

/-- **The derived identity `RΓ(X, Ra_*F) = RΓ((C/K)_total, F)` of `O_C(X)`-modules**, with
sections over `X` read at the final object `id_X` of `C/X`. -/
def derivedPushforwardModuleSectionsAtIdIso :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward
        (X := totalTopos P K OC) (Y := sliceTopos P K OC) (augmentationHom P K OC) ⋙
        derivedModuleSectionsAtId P X OC ≅
      derivedTotalGlobalSections P K OC ⋙
        (ModuleCat.restrictScalars (totalSectionsRingHom P K OC)).mapDerivedCategory :=
  @Stacks.Cohomology.LerayUnbounded.derivedCompIso _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ (by exact (inferInstance : (RingedToposHom.pushforwardModules (X := totalTopos P K OC)
        (Y := sliceTopos P K OC) (augmentationHom P K OC)).Additive))
      (moduleSectionsAtId P OC) (by exact additive_moduleSectionsAtId P OC) _ _
      (pushforwardModuleSectionsAtIdIso P K OC)
      (RingedToposHom.isKInjective_pushforwardModules (augmentationHom P K OC)) ≪≫
    (Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso _ _).symm

/-- `RΓ(C/X, E) = RΓ((C/K)_total, La^*E)` of `O_C(X)`-modules, for a hypercovering `K` of `X`: the
derived unit `E ⟶ Ra_*La^*E` is invertible, and `RΓ(C/X, -) ∘ Ra_*` is `RΓ((C/K)_total, -)`. -/
def derivedModuleSectionsAtIdPullbackIsoOfIsHypercovering (hK : IsHypercovering P K) :
    derivedModuleSectionsAtId P X OC ≅
      (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
          (X := totalTopos P K OC) (Y := sliceTopos P K OC) (augmentationHom P K OC)).functor ⋙
        derivedTotalGlobalSections P K OC ⋙
          (ModuleCat.restrictScalars (totalSectionsRingHom P K OC)).mapDerivedCategory :=
  have := RingedToposHom.isIso_derivedPullbackPushforwardUnit (augmentationHom P K OC)
    (isIso_pullbackAdjPushforwardModules_unit_over P K OC hK)
    (pullbackComputesDerivedPushforward_of_isHypercovering P K OC hK)
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (RingedToposHom.derivedPullbackPushforwardUnit (augmentationHom P K OC)))
      (derivedModuleSectionsAtId P X OC) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (derivedPushforwardModuleSectionsAtIdIso P K OC)

/-- Let `C` be a site with fibre products, given by a pretopology `P`, let `X` be an object of
`C`, let `O_C` be a sheaf of commutative rings on `C` and let `K` be a hypercovering of `X` (a
simplicial object of `SR(C, X)` whose degree-zero family covers `X` and whose matching maps
`K_{n+1} ⟶ (cosk_n sk_n K)_{n+1}` are covering). With `O_X = O_C|_{C/X}`, `O = a⁻¹O_X` on the
total site `(C/K)_total` and `a : (Sh((C/K)_total), O) ⟶ (Sh(C/X), O_X)` the ringed
augmentation, there is a canonical isomorphism

`RΓ(X, E) = RΓ((C/K)_total, La^*E)`

naturally in `E` in the unbounded derived category `D(O_C)`. Here `RΓ(X, -)` is the total right
derived functor of sections over `X`, with values in `D(O_C(X))`; `La^*E` is `La^*` of the
restriction of `E` to `C/X` (the target of `a` being `(Sh(C/X), O_X)`); and
`RΓ((C/K)_total, -)`, with values in `D(Γ((C/K)_total, O))`, is read in `D(O_C(X))` through the
canonical ring map `O_C(X) ⟶ Γ((C/K)_total, O)` (`totalSectionsRingHom`). -/
@[stacks 0DA6]
def derivedModuleSectionsOverObjectIsoOfIsHypercovering (hK : IsHypercovering P K) :
    derivedModuleSectionsOverObject P X OC ≅
      Stacks.Cohomology.Localization.derivedRestriction (ringedSite P OC) X ⋙
        (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
          (X := totalTopos P K OC) (Y := sliceTopos P K OC) (augmentationHom P K OC)).functor ⋙
        derivedTotalGlobalSections P K OC ⋙
          (ModuleCat.restrictScalars (totalSectionsRingHom P K OC)).mapDerivedCategory :=
  derivedModuleSectionsOverObjectIsoRestriction P OC ≪≫
    Functor.isoWhiskerLeft _ (derivedModuleSectionsAtIdPullbackIsoOfIsHypercovering P K OC hK)

/-- The forward map of `derivedModuleSectionsOverObjectIsoOfIsHypercovering` at `E` is
`RΓ(C/X, -)` of the derived unit `E|_X ⟶ Ra_*La^*(E|_X)` of the ringed augmentation, between the
comparison `RΓ(X, E) = RΓ(C/X, E|_X)` and the factorisation
`RΓ(C/X, Ra_*-) = RΓ((C/K)_total, -)`. -/
@[stacks 0DA6 "the forward map of the isomorphism is the canonical one: RΓ(C/X, -) of the derived \
unit E|_X ⟶ Ra_*La^*(E|_X), between RΓ(X, E) = RΓ(C/X, E|_X) and the factorisation of Tag 08J6"]
theorem derivedModuleSectionsOverObjectIsoOfIsHypercovering_hom_app (hK : IsHypercovering P K)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC))) :
    (derivedModuleSectionsOverObjectIsoOfIsHypercovering P K OC hK).hom.app E =
      (derivedModuleSectionsOverObjectIsoRestriction P OC).hom.app E ≫
        (derivedModuleSectionsAtId P X OC).map
          ((RingedToposHom.derivedPullbackPushforwardUnit (augmentationHom P K OC)).app
            ((Stacks.Cohomology.Localization.derivedRestriction (ringedSite P OC) X).obj E)) ≫
        (derivedPushforwardModuleSectionsAtIdIso P K OC).hom.app
          ((RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
            (X := totalTopos P K OC) (Y := sliceTopos P K OC) (augmentationHom P K OC)).functor.obj
              ((Stacks.Cohomology.Localization.derivedRestriction (ringedSite P OC) X).obj E)) := by
  simp only [derivedModuleSectionsOverObjectIsoOfIsHypercovering,
    derivedModuleSectionsAtIdPullbackIsoOfIsHypercovering, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp]
  exact congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (Category.id_comp _))

section SimplicialObject

variable (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)

/-- Let `C` be a site with fibre products, `X` an object of `C`, `O_C` a sheaf of commutative rings
on `C` and `a : U ⟶ X` a hypercovering of `X` in `C` by a simplicial object `U` of `C`. With
`O_X = O_C|_{C/X}`, `O = a⁻¹O_X` on the total site `(C/U)_total` and
`a : (Sh((C/U)_total), O) ⟶ (Sh(C/X), O_X)` the ringed augmentation, there is a canonical
isomorphism

`RΓ(X, E) = RΓ((C/U)_total, La^*E)`

naturally in `E` in the unbounded derived category `D(O_C)`. Here `RΓ(X, -)` takes values in
`D(O_C(X))`, `La^*E` is `La^*` of the restriction of `E` to `C/X`, and the right hand side, which
lives in `D(Γ((C/U)_total, O))`, is read in `D(O_C(X))` through the canonical ring map
`O_C(X) ⟶ Γ((C/U)_total, O)` (`totalSectionsRingHom`).

This is `derivedModuleSectionsOverObjectIsoOfIsHypercovering` for the hypercovering of `X` by
semi-representable objects with one summand in each degree that `a` determines
(`IsHypercoveringAugmentation.isHypercovering`). -/
@[stacks 0DAD]
def derivedModuleSectionsOverObjectIsoOfIsHypercoveringAugmentation
    (h : IsHypercoveringAugmentation P U a) :
    derivedModuleSectionsOverObject P X OC ≅
      Stacks.Cohomology.Localization.derivedRestriction (ringedSite P OC) X ⋙
        (RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
          (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
          (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)
          (augmentationHom P (associatedSimplicialObject.{u} U a) OC)).functor ⋙
        derivedTotalGlobalSections P (associatedSimplicialObject.{u} U a) OC ⋙
          (ModuleCat.restrictScalars
            (totalSectionsRingHom P (associatedSimplicialObject.{u} U a) OC)).mapDerivedCategory :=
  derivedModuleSectionsOverObjectIsoOfIsHypercovering P (associatedSimplicialObject.{u} U a) OC
    (h.isHypercovering P U a)

/-- At every `E` of `D(O_C)` the forward map of
`derivedModuleSectionsOverObjectIsoOfIsHypercoveringAugmentation` is `RΓ(C/X, -)` of the derived
unit `E|_X ⟶ Ra_*La^*(E|_X)` of the ringed augmentation, preceded by the comparison
`RΓ(X, E) = RΓ(C/X, E|_X)` and followed by the factorisation
`RΓ(C/X, Ra_*-) = RΓ((C/U)_total, -)`. -/
@[stacks 0DAD "the forward map of the isomorphism is the canonical one: RΓ(C/X, -) of the derived \
unit E|_X ⟶ Ra_*La^*(E|_X), between RΓ(X, E) = RΓ(C/X, E|_X) and the factorisation of Tag 08J6"]
theorem derivedModuleSectionsOverObjectIsoOfIsHypercoveringAugmentation_hom_app
    (h : IsHypercoveringAugmentation P U a)
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC))) :
    (derivedModuleSectionsOverObjectIsoOfIsHypercoveringAugmentation P OC U a h).hom.app E =
      (derivedModuleSectionsOverObjectIsoRestriction P OC).hom.app E ≫
        (derivedModuleSectionsAtId P X OC).map
          ((RingedToposHom.derivedPullbackPushforwardUnit
            (augmentationHom P (associatedSimplicialObject.{u} U a) OC)).app
            ((Stacks.Cohomology.Localization.derivedRestriction (ringedSite P OC) X).obj E)) ≫
        (derivedPushforwardModuleSectionsAtIdIso P (associatedSimplicialObject.{u} U a) OC).hom.app
          ((RingedToposHom.leftDerivedPullbackOfIsIsoFSharp
            (X := totalTopos P (associatedSimplicialObject.{u} U a) OC)
            (Y := sliceTopos P (associatedSimplicialObject.{u} U a) OC)
            (augmentationHom P (associatedSimplicialObject.{u} U a) OC)).functor.obj
              ((Stacks.Cohomology.Localization.derivedRestriction (ringedSite P OC) X).obj E)) :=
  derivedModuleSectionsOverObjectIsoOfIsHypercovering_hom_app P _ OC (h.isHypercovering P U a) E

end SimplicialObject

end CategoryTheory.SimplicialSemiRepresentable
