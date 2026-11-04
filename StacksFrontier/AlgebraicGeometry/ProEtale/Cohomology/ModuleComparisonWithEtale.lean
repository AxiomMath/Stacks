module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowExactEquivalence
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.ConstructibleComparison
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.LocallyConstantComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModuleSheafAcyclicity
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleConstantSheaf

/-!
# Comparison of étale and pro-étale derived categories of sheaves of modules

Let `X` be a scheme, `Λ` a ring and `ε : X_proétale → X_étale` the comparison morphism of sites,
with inverse image `ε⁻¹` and direct image `ε_*` on sheaves of `Λ`-modules. The inverse image is
exact and fully faithful (Stacks 099T), and it does not change cohomology: for a sheaf of
`Λ`-modules `ℱ` on `X_étale` the higher direct images `R^q ε_*(ε⁻¹ℱ)` vanish, and for
`K ∈ D⁺(X_étale, Λ)` the map `K ⟶ Rε_* ε⁻¹ K` is an isomorphism — the form of Stacks 099V for
sheaves of `Λ`-modules. Consequently `ε⁻¹` is fully faithful on `D⁺(X_étale, Λ)`.

When `Λ` is Noetherian, `ε⁻¹` restricts to an equivalence between the bounded below complexes
whose cohomology sheaves are locally constant of finite type on the two sites (Stacks 099Z): the
locally constant sheaves of finite type are those of finite presentation, and on them `ε⁻¹` is an
equivalence (Stacks 099Y). In the same way `ε⁻¹` restricts to an equivalence between the bounded
below complexes with constructible cohomology sheaves (Stacks 09AL), constructible sheaves on the
two sites corresponding to each other under `ε⁻¹` (Stacks 09AK).

## Main definitions

* `AlgebraicGeometry.Scheme.etaleInverseImageAdjunction`: the adjunction `ε⁻¹ ⊣ ε_*` on sheaves
  of `Λ`-modules.
* `AlgebraicGeometry.ProEtale.etaleInverseImageDerivedLocallyConstant`: the functor
  `ε⁻¹ : D⁺_flc(X_étale, Λ) ⥤ D⁺_flc(X_proétale, Λ)`.
* `AlgebraicGeometry.ProEtale.etaleInverseImageDerivedConstructible`: the functor
  `ε⁻¹ : D⁺_c(X_étale, Λ) ⥤ D⁺_c(X_proétale, Λ)`.

## Main results

* `AlgebraicGeometry.Scheme.rightAcyclic_etaleInverseImage_obj`: `ε⁻¹ℱ` is right acyclic for
  `ε_*`, for every sheaf of `Λ`-modules `ℱ` on `X_étale`.
* `AlgebraicGeometry.Scheme.isIso_etaleInverseImageAdjunction_unit_app_and_isZero_rightDerived`:
  `ε_* ε⁻¹ ℱ = ℱ` and `R^q ε_*(ε⁻¹ℱ) = 0` for `q > 0` (Stacks 099V (1) for `Λ`-modules).
* `AlgebraicGeometry.Scheme.isIso_etaleInverseImageAdjunction_rightDerivedFunctorPlus_unit`:
  `K ⟶ Rε_* ε⁻¹ K` is an isomorphism for `K ∈ D⁺(X_étale, Λ)` (Stacks 099V (2) for
  `Λ`-modules).
* `AlgebraicGeometry.Scheme.isWeakSerreClass_etaleInverseImage_essImage`: the essential image `𝒞`
  of `ε⁻¹` is a weak Serre subcategory (Stacks 09B1 (1)).
* `AlgebraicGeometry.Scheme.exists_equivalence_etaleInverseImage_derivedCategoryPlus`:
  `ε⁻¹ : D⁺(X_étale, Λ) ≌ D⁺_𝒞(X_proétale, Λ)` with quasi-inverse `Rε_*` (Stacks 09B1 (2)), the
  equivalence being `AlgebraicGeometry.Scheme.etaleInverseImageDerivedEquivalence`.
* `AlgebraicGeometry.ProEtale.isEquivalence_etaleInverseImageDerivedLocallyConstant`:
  **Stacks 099Z**.
* `AlgebraicGeometry.ProEtale.isEquivalence_etaleInverseImageDerivedConstructible`:
  **Stacks 09AL**.

## Implementation notes

The vanishing of `R^q ε_*(ε⁻¹ℱ)` is reduced to the case of abelian sheaves, Stacks 099V
(`AlgebraicGeometry.ProEtale.isIso_unit_app_and_isZero_rightDerived_epsilonDirectImage`): the
underlying abelian sheaf of `ε⁻¹ℱ` is the inverse image of an abelian sheaf, and higher direct
images of sheaves of modules are computed on underlying abelian sheaves, the underlying abelian
sheaf of an injective sheaf of modules being acyclic for `ε_*`
(`Stacks.Cohomology.ModuleSheaf.rightAcyclic_sheafPushforwardContinuous_of_forget₂`).

`D_flc(X, Λ)` is `DerivedCategoryB.derivedCategoryBPlus` of the class
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf`: the bounded below objects of the
derived category all of whose cohomology sheaves are locally constant of finite type; `ε⁻¹` on
the derived category is `ε⁻¹` applied termwise, `CategoryTheory.Functor.mapDerivedCategory`.
`D_c` is the same construction for the constructible sheaves,
`AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` and
`AlgebraicGeometry.ProEtale.IsConstructibleModuleSheaf'`. Both equivalences are instances of
`DerivedCategoryB.isEquivalence_mapDerivedCategoryBPlus`.

## References

* [Stacks Project, Tag 099T](https://stacks.math.columbia.edu/tag/099T)
* [Stacks Project, Tag 099V](https://stacks.math.columbia.edu/tag/099V)
* [Stacks Project, Tag 099Y](https://stacks.math.columbia.edu/tag/099Y)
* [Stacks Project, Tag 099Z](https://stacks.math.columbia.edu/tag/099Z)
* [Stacks Project, Tag 09AK](https://stacks.math.columbia.edu/tag/09AK)
* [Stacks Project, Tag 09AL](https://stacks.math.columbia.edu/tag/09AL)
* [Stacks Project, Tag 09B1](https://stacks.math.columbia.edu/tag/09B1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe w v u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u}) (Λ : Type v) [Ring Λ]

/-- Sheaves of `Λ`-modules on the small étale site of `X` admit sheafification. -/
local instance : HasSheafify X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ) :=
  (Scheme.comparisonSheafification_exists.{u, w, v} X Λ).1

/-- Sheaves of `Λ`-modules on the small pro-étale site of `X` admit sheafification. -/
local instance : HasSheafify (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ) :=
  (Scheme.comparisonSheafification_exists.{u, w, v} X Λ).2

/-! ### Exactness of the inverse image -/

/-- The left Kan extension along the inclusion of the small étale category into the small
pro-étale category is left exact on presheaves of `Λ`-modules: the comma categories computing
the extension pointwise are filtered, and filtered colimits of modules commute with finite
limits. -/
theorem preservesFiniteLimits_lan_etaleToProetale_moduleCat :
    PreservesFiniteLimits (X.etaleToProetale.op.lan :
      (X.Etaleᵒᵖ ⥤ ModuleCat.{max (u + 1) v w} Λ) ⥤ _) := by
  have : RepresentablyFlat X.etaleToProetale := flat_of_preservesFiniteLimits _
  have (Y : X.ProEtᵒᵖ) : HasColimitsOfShape (CostructuredArrow X.etaleToProetale.op Y)
      (ModuleCat.{max (u + 1) v w} Λ) :=
    hasColimitsOfShape_of_essentiallySmall.{max (u + 1) v w} _ _
  exact Stacks.Topology.lan_preservesFiniteLimits_of_flat _ (fun Y ↦ inferInstance)

/-- The inverse image `ε⁻¹` of sheaves of `Λ`-modules preserves finite limits. -/
instance : PreservesFiniteLimits (Scheme.etaleInverseImage.{u, w, v} X Λ) :=
  have := preservesFiniteLimits_lan_etaleToProetale_moduleCat.{w} X Λ
  have := Functor.sheafPullbackConstruction.preservesFiniteLimits X.etaleToProetale
    (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)
  preservesFiniteLimits_of_natIso (Functor.sheafPullbackConstruction.sheafPullbackIso
    X.etaleToProetale (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology
      (Scheme.ProEt.topology X))

/-- **The inverse image `ε⁻¹ ⊣ ε_*` on sheaves of `Λ`-modules.** -/
abbrev etaleInverseImageAdjunction :
    Scheme.etaleInverseImage.{u, w, v} X Λ ⊣ Scheme.etaleDirectImage.{u, w, v} X Λ :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
    (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The inverse image `ε⁻¹` of sheaves of `Λ`-modules preserves finite colimits. -/
instance : PreservesFiniteColimits (Scheme.etaleInverseImage.{u, w, v} X Λ) :=
  have := (etaleInverseImageAdjunction.{w} X Λ).isLeftAdjoint
  inferInstance

/-- The direct image `ε_*` of sheaves of `Λ`-modules preserves finite limits. -/
instance : PreservesFiniteLimits (Scheme.etaleDirectImage.{u, w, v} X Λ) :=
  have := (etaleInverseImageAdjunction.{w} X Λ).isRightAdjoint
  inferInstance

/-! ### Stacks 099V for sheaves of modules -/

attribute [local instance]
  Functor.hasRightDerivedFunctor_mapHomotopyCategoryPlus_of_enoughInjectives

/-- **The inverse image `ε⁻¹ℱ` of a sheaf of `Λ`-modules is right acyclic for `ε_*`.** Its
underlying abelian sheaf is the inverse image of an abelian sheaf, which is right acyclic for the
direct image of abelian sheaves by Stacks 099V, and higher direct images of sheaves of modules are
computed on underlying abelian sheaves. -/
theorem rightAcyclic_etaleInverseImage_obj
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ)) :
    (Scheme.etaleDirectImage.{u, w, v} X Λ).rightAcyclic
      ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj F) := by
  have := ProEtale.instHasSheafifyEtaleSmallEtaleTopologyAddCommGrpCat_stacksFrontier.{max v w, u} X
  have := ProEtale.hasSheafify_proetale.{u, max v w} X
  have := ProEtale.isGrothendieckAbelian_sheaf_proetale.{max v w, u} X
  have := ProEtale.enoughInjectives_sheaf_proetale.{max v w, u} X
  have : PreservesFiniteLimits (ProEtale.epsilonDirectImage.{u, max v w} X) :=
    have := (ProEtale.epsilonAdjunction.{u, max v w} X).isRightAdjoint
    inferInstance
  refine Stacks.Cohomology.ModuleSheaf.rightAcyclic_sheafPushforwardContinuous_of_forget₂.{
    max (u + 1) w, v, u, u + 1, u, u + 1} X.etaleToProetale Λ _ ?_
  obtain ⟨G, ⟨e⟩⟩ := (Scheme.etaleInverseImage_essImage_iff_forget₂.{w, v} X Λ _).1
    ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj_mem_essImage F)
  have := ProEtale.instEnoughInjectivesSheafEtaleSmallEtaleTopologyAddCommGrpCat_stacksFrontier.{
    max v w, u} X
  have : (ProEtale.epsilonDirectImage.{u, max v w} X).Additive :=
    (ProEtale.epsilonAdjunction.{u, max v w} X).right_adjoint_additive
  have : (ProEtale.epsilonInverseImage.{u, max v w} X).Additive :=
    (ProEtale.epsilonAdjunction.{u, max v w} X).left_adjoint_additive
  have := ProEtale.isIso_epsilonAdjunction_unit.{max v w, u} X
  have : PreservesFiniteLimits (ProEtale.epsilonInverseImage.{u, max v w} X) :=
    Scheme.preservesFiniteLimits_of_etaleToProetale_adjunction.{max v w, u} X
      (ProEtale.epsilonAdjunction.{u, max v w} X)
  have : PreservesFiniteColimits (ProEtale.epsilonInverseImage.{u, max v w} X) :=
    have := (ProEtale.epsilonAdjunction.{u, max v w} X).isLeftAdjoint
    inferInstance
  have : (ProEtale.epsilonInverseImage.{u, max v w} X).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have h := (ProEtale.epsilonAdjunction.{u, max v w} X).rightAcyclic_obj_of_isIso_unit
    (fun I _ ↦ ProEtale.rightAcyclic_epsilonInverseImage_obj_of_injective.{max v w, u} X I) G
  exact ObjectProperty.prop_of_iso _ e h

/-- **Stacks 099V (1) for sheaves of `Λ`-modules.** For a sheaf of `Λ`-modules `ℱ` on `X_étale`,
`Rε_*(ε⁻¹ℱ) = ℱ`: the adjunction map `ℱ ⟶ ε_* ε⁻¹ ℱ` is an isomorphism and the higher direct
images `R^q ε_*(ε⁻¹ℱ)`, `q > 0`, vanish. -/
theorem isIso_etaleInverseImageAdjunction_unit_app_and_isZero_rightDerived
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ)) :
    IsIso ((etaleInverseImageAdjunction.{w} X Λ).unit.app F) ∧
      ∀ q : ℕ, 0 < q → IsZero (((Scheme.etaleDirectImage.{u, w, v} X Λ).rightDerived q).obj
        ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj F)) := by
  refine ⟨inferInstance, fun q hq ↦ ?_⟩
  have hF := rightAcyclic_etaleInverseImage_obj.{w} X Λ F
  rw [((Scheme.etaleDirectImage.{u, w, v} X Λ).rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    _).2 inferInstance] at hF
  exact (hF q (by exact_mod_cast hq)).of_iso ((Stacks.DerivedIndexing.rightDerivedIso _ q).app _)

/-- **Stacks 099V (2) for sheaves of `Λ`-modules.** For `K ∈ D⁺(X_étale, Λ)` the map
`K ⟶ Rε_* ε⁻¹ K` is an isomorphism: the unit of the derived adjunction `ε⁻¹ ⊣ Rε_*` on bounded
below derived categories is invertible. Here `ε⁻¹` on `D⁺` is the right derived functor of the
exact functor `ε⁻¹`, that is, `ε⁻¹` applied termwise. -/
theorem isIso_etaleInverseImageAdjunction_rightDerivedFunctorPlus_unit :
    IsIso (etaleInverseImageAdjunction.{w} X Λ).rightDerivedFunctorPlus.unit :=
  (etaleInverseImageAdjunction.{w} X Λ).isIso_rightDerivedFunctorPlus_unit
    (fun I _ ↦ rightAcyclic_etaleInverseImage_obj.{w} X Λ I)

/-! ### Stacks 09B1 -/

/-- **Stacks 09B1 (1).** The essential image of the fully faithful functor
`ε⁻¹ : Mod(X_étale, Λ) ⥤ Mod(X_proétale, Λ)` is a weak Serre subcategory: `ε_*` is exact on a
short exact sequence whose first term comes from `X_étale`, because `R¹ε_* ε⁻¹ = 0`. -/
theorem isWeakSerreClass_etaleInverseImage_essImage :
    (Scheme.etaleInverseImage.{u, w, v} X Λ).essImage.IsWeakSerreClass :=
  (etaleInverseImageAdjunction.{w} X Λ).isWeakSerreClass_essImage
    ((etaleInverseImageAdjunction.{w} X Λ).shortExact_map_of_isZero_rightDerived_one fun A ↦
      (isIso_etaleInverseImageAdjunction_unit_app_and_isZero_rightDerived.{w} X Λ A).2 1 one_pos)

/-- The equivalence of `D⁺(X_étale, Λ)` with `D⁺_𝒞(X_proétale, Λ)`, where `𝒞` is the essential
image of `ε⁻¹`: its functor is `ε⁻¹` applied termwise and its quasi-inverse is `Rε_*`. -/
def etaleInverseImageDerivedEquivalence :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ)) ≌
      (DerivedCategoryB.plusEssImage (Scheme.etaleInverseImage.{u, w, v} X Λ)).FullSubcategory :=
  DerivedCategoryB.plusEquivalenceEssImage _ (etaleInverseImageAdjunction.{w} X Λ)
    (fun I _ ↦ rightAcyclic_etaleInverseImage_obj.{w} X Λ I)

/-- **Stacks 09B1 (2).** Let `𝒞` be the essential image of `ε⁻¹` on sheaves of `Λ`-modules.
Then `ε⁻¹` defines an equivalence of `D⁺(X_étale, Λ)` with `D⁺_𝒞(X_proétale, Λ)`, the bounded
below objects of `D(X_proétale, Λ)` whose cohomology sheaves lie in `𝒞`, with quasi-inverse
`Rε_*`. Here `ε⁻¹` on `D⁺` is `ε⁻¹` applied termwise and `Rε_*` is the right derived functor of
`ε_*`. -/
theorem exists_equivalence_etaleInverseImage_derivedCategoryPlus :
    ∃ e : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ)) ≌
        (DerivedCategoryB.plusEssImage (Scheme.etaleInverseImage.{u, w, v} X Λ)).FullSubcategory,
      e.functor ⋙ (DerivedCategoryB.plusEssImage (Scheme.etaleInverseImage.{u, w, v} X Λ)).ι =
          (Scheme.etaleInverseImage.{u, w, v} X Λ).mapDerivedCategoryPlus ∧
        e.inverse = (DerivedCategoryB.plusEssImage (Scheme.etaleInverseImage.{u, w, v} X Λ)).ι ⋙
          (Scheme.etaleDirectImage.{u, w, v} X Λ).rightDerivedFunctorPlus :=
  ⟨etaleInverseImageDerivedEquivalence.{w} X Λ, rfl, rfl⟩

end Scheme

/-! ### Stacks 099Z -/

namespace ProEtale

variable (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ]

attribute [local instance] hasSheafify_proEt_moduleCat hasSheafify_etale_moduleCat

/-- **Inverse image preserves local constancy of finite type** over a Noetherian ring, along
`ε`: such sheaves are of finite presentation. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_etaleInverseImage
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ))
    (hG : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      X.smallEtaleTopology Λ G) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology X) Λ ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj G) := by
  rw [← isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf]
    at hG ⊢
  exact isFinitePresentationLocallyConstantModuleSheaf_etaleInverseImage G hG

/-- **Every locally constant sheaf of finite type on `X_proétale` comes from one on `X_étale`**,
over a Noetherian ring (Stacks 099Y). -/
theorem exists_isFiniteTypeLocallyConstantModuleSheaf_etaleInverseImage_iso
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (Scheme.ProEt.topology X) Λ F) :
    ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ),
      IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v} X.smallEtaleTopology Λ G ∧
        Nonempty ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj G ≅ F) := by
  rw [← isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf]
    at hF
  obtain ⟨G, ⟨e⟩⟩ := etaleInverseImage_essImage_of_isFinitePresentationLocallyConstant F hF
  refine ⟨G, ?_, ⟨e⟩⟩
  rw [← isFinitePresentationLocallyConstantModuleSheaf_iff_isFiniteTypeLocallyConstantModuleSheaf]
  exact isFinitePresentationLocallyConstantModuleSheaf_of_etaleInverseImage G
    (ObjectProperty.prop_of_iso _ e.symm hF)

/-- **The inverse image `ε⁻¹ : D⁺_flc(X_étale, Λ) ⥤ D⁺_flc(X_proétale, Λ)`**: `ε⁻¹` applied
termwise to a bounded below complex of sheaves of `Λ`-modules on `X_étale` whose cohomology
sheaves are locally constant of finite type. -/
def etaleInverseImageDerivedLocallyConstant :
    (DerivedCategoryB.derivedCategoryBPlus (IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1,
        max v w, v} X.smallEtaleTopology Λ)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBPlus (IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1,
        max v w, v} (Scheme.ProEt.topology X) Λ)).FullSubcategory :=
  DerivedCategoryB.mapDerivedCategoryBPlus (Scheme.etaleInverseImage.{u, w, v} X Λ) _ _
    (isFiniteTypeLocallyConstantModuleSheaf_etaleInverseImage.{w} X Λ)

/-- **Stacks 099Z.** Let `X` be a scheme and `Λ` a Noetherian ring. Let `D_flc(X_étale, Λ)`,
resp. `D_flc(X_proétale, Λ)`, be the full subcategory of `D(X_étale, Λ)`, resp.
`D(X_proétale, Λ)`, of the complexes whose cohomology sheaves are locally constant sheaves of
`Λ`-modules of finite type. Then `ε⁻¹ : D⁺_flc(X_étale, Λ) ⥤ D⁺_flc(X_proétale, Λ)` is an
equivalence of categories.

Locally constant of finite type is `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf`,
`D⁺_flc` is `DerivedCategoryB.derivedCategoryBPlus` of it, and `ε⁻¹` is applied termwise. The
proof combines Stacks 099V for sheaves of `Λ`-modules (`ε⁻¹` is fully faithful on `D⁺`) with
Stacks 099Y (every locally constant sheaf of finite type on `X_proétale` comes from `X_étale`). -/
theorem isEquivalence_etaleInverseImageDerivedLocallyConstant :
    (etaleInverseImageDerivedLocallyConstant.{w} X Λ).IsEquivalence :=
  DerivedCategoryB.isEquivalence_mapDerivedCategoryBPlus _ _ _ _
    (Scheme.etaleInverseImageAdjunction.{w} X Λ)
    (fun I _ ↦ Scheme.rightAcyclic_etaleInverseImage_obj.{w} X Λ I)
    (exists_isFiniteTypeLocallyConstantModuleSheaf_etaleInverseImage_iso.{w} X Λ)

/-! ### Stacks 09AL -/

/-- **Every constructible sheaf of `Λ`-modules on `X_proétale` comes from a constructible one on
`X_étale`** (Stacks 09AK). -/
theorem exists_isConstructibleEtaleModuleSheaf_etaleInverseImage_iso
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} Λ))
    (hF : IsConstructibleModuleSheaf'.{u, v, w} X Λ F) :
    ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ),
      Scheme.IsConstructibleEtaleModuleSheaf.{u, v, w} X Λ G ∧
        Nonempty ((Scheme.etaleInverseImage.{u, w, v} X Λ).obj G ≅ F) := by
  obtain ⟨G, ⟨e⟩⟩ := etaleInverseImage_essImage_of_isConstructibleModuleSheaf' F hF
  exact ⟨G, (isConstructibleModuleSheaf'_etaleInverseImage_iff G).1
    (ObjectProperty.prop_of_iso _ e.symm hF), ⟨e⟩⟩

/-- **The inverse image `ε⁻¹ : D⁺_c(X_étale, Λ) ⥤ D⁺_c(X_proétale, Λ)`**: `ε⁻¹` applied
termwise to a bounded below complex of sheaves of `Λ`-modules on `X_étale` whose cohomology
sheaves are constructible. -/
def etaleInverseImageDerivedConstructible :
    (DerivedCategoryB.derivedCategoryBPlus
        (Scheme.IsConstructibleEtaleModuleSheaf.{u, v, w} X Λ)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryBPlus
        (IsConstructibleModuleSheaf'.{u, v, w} X Λ)).FullSubcategory :=
  DerivedCategoryB.mapDerivedCategoryBPlus (Scheme.etaleInverseImage.{u, w, v} X Λ) _ _
    fun G hG ↦ (isConstructibleModuleSheaf'_etaleInverseImage_iff G).2 hG

/-- **Stacks 09AL.** Let `X` be a scheme and `Λ` a Noetherian ring. Let `D_c(X_étale, Λ)`, resp.
`D_c(X_proétale, Λ)`, be the full subcategory of `D(X_étale, Λ)`, resp. `D(X_proétale, Λ)`, of
the complexes whose cohomology sheaves are constructible sheaves of `Λ`-modules. Then
`ε⁻¹ : D⁺_c(X_étale, Λ) ⥤ D⁺_c(X_proétale, Λ)` is an equivalence of categories.

Constructibility is `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` on `X_étale` and
`AlgebraicGeometry.ProEtale.IsConstructibleModuleSheaf'` (Stacks 09AJ) on `X_proétale`, `D⁺_c` is
`DerivedCategoryB.derivedCategoryBPlus` of it, and `ε⁻¹` is applied termwise. The proof combines
Stacks 099V for sheaves of `Λ`-modules (`ε⁻¹` is fully faithful on `D⁺`) with Stacks 09AK
(every constructible sheaf on `X_proétale` comes from a constructible sheaf on `X_étale`). -/
theorem isEquivalence_etaleInverseImageDerivedConstructible :
    (etaleInverseImageDerivedConstructible.{w} X Λ).IsEquivalence :=
  DerivedCategoryB.isEquivalence_mapDerivedCategoryBPlus _ _ _ _
    (Scheme.etaleInverseImageAdjunction.{w} X Λ)
    (fun I _ ↦ Scheme.rightAcyclic_etaleInverseImage_obj.{w} X Λ I)
    (exists_isConstructibleEtaleModuleSheaf_etaleInverseImage_iso.{w} X Λ)

end ProEtale

end AlgebraicGeometry

end
