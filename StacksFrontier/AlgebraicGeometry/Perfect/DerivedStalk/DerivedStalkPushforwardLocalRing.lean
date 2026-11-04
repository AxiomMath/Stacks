module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedStalkPushforwardComponents

/-!
# The derived stalk of a derived pushforward, below `DerivedCategory.Q`

For a closed immersion of schemes `i : Z ⟶ X` and `z : Z`,
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` computes the derived stalk
at `i z` of `Ri_* K` over the local ring `𝒪_{X,i z}`; it is a six-fold composite of isomorphisms
of functors.  This file computes its component at `DerivedCategory.Q.obj C`: it is the comparison
`Ri_* ≅ i_*` and the factorization of `i_*` under the derived stalk, then the factorization of the
stalk functor at `i z`, then `DerivedCategory.Q` of the *degreewise* germ map
`AlgebraicGeometry.restrictScalarsStalkPushforwardMap`, then the two factorizations of
`(−)_z ⋙ restrictScalars (i^♯_z)` read backwards.

So the derived computation is the underived one, conjugated by the comparisons of each derived
functor with its degreewise model.

## Main results

* `AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing_hom_app`: the component
  at a free object, as the composite of the components of the four nontrivial rungs.
* `AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing_hom_app_Q`: **the
  component at a complex**, as above.
* `StacksDraft.DerivedStalkComponentChase.localRingComponentChase`: the diagram chase behind it,
  at free objects and morphisms of an arbitrary category.

## Implementation notes

The equation mixes `AlgebraicGeometry.Scheme.Modules X` with
`CategoryTheory.SheafOfModules (structureSheafRing X.toRingedSpace)`, and the `RingCat`-valued
stalk of the ring sheaf with the local ring; in each pair the two spellings are definitionally but
not *reducibly* equal, so a goal of that shape is not type-correct at the transparency at which
`rw`, `simp` and `conv` check their motives.  The diagram chase is therefore stated at free objects
and morphisms of an arbitrary category, as
`StacksDraft.DerivedStalkComponentChase.localRingComponentChase`, and applied once by `exact`.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.PerfectComplexTriangles

noncomputable section

namespace StacksDraft.DerivedStalkComponentChase

variable {C : Type*} [Category C]

/-- A diagram chase in an arbitrary category: if `ψ = A ≫ B ≫ Cc ≫ D` and the morphisms satisfy
the factorization, commutation and cancellation identities `h₁`–`h₁₄`, then
`ψ = t1 ≫ t2 ≫ b₁ ≫ t4 ≫ t5 ≫ D₄`. -/
theorem localRingComponentChase
    {O₀ O₁ O₂ O₆ P₁ P₂ P₃ U₁ U₂ U₃ U₄ U₅ T₂ T₃ T₄ Z₅ V₃ Y₁ Y₂ G₁ : C}
    {ψ : O₀ ⟶ O₆} {A : O₀ ⟶ P₁} {B : P₁ ⟶ P₂} {Cc : P₂ ⟶ P₃} {D : P₃ ⟶ O₆}
    {B₁ : P₁ ⟶ U₁} {B₂ : U₁ ⟶ U₂} {B₃ : U₂ ⟶ U₃} {B₄ : U₃ ⟶ U₄} {B₅ : U₄ ⟶ U₅}
    {B₆ : U₅ ⟶ P₂}
    {D₁ : P₃ ⟶ Z₅} {D₂ : Z₅ ⟶ T₄} {D₃ : T₄ ⟶ V₃} {D₄ : V₃ ⟶ O₆}
    {t1 : O₀ ⟶ O₁} {t2 : O₁ ⟶ O₂} {S : O₂ ⟶ U₂} {Bρ : P₁ ⟶ U₂} {Fρ : O₀ ⟶ O₂}
    {b₁ : O₂ ⟶ Y₁} {b₂ : Y₁ ⟶ Y₂} {b₃ : Y₂ ⟶ U₃} {b₄ : U₃ ⟶ U₂}
    {CBIG : U₅ ⟶ Z₅} {E₁ : Z₅ ⟶ P₃}
    {c₁ : U₅ ⟶ U₄} {c₂ : U₄ ⟶ T₂} {c₃ : T₂ ⟶ T₃} {c₄ : T₃ ⟶ T₄} {c₅ : T₄ ⟶ Z₅}
    {cc₂ : U₃ ⟶ Y₂} {Qb : Y₂ ⟶ T₂} {Qa : T₃ ⟶ G₁}
    {t4 : Y₁ ⟶ G₁} {t5 : G₁ ⟶ V₃}
    (h₀ : ψ = A ≫ B ≫ Cc ≫ D)
    (h₁ : B = B₁ ≫ B₂ ≫ B₃ ≫ B₄ ≫ B₅ ≫ B₆)
    (h₂ : A ≫ Bρ = Fρ ≫ S) (h₂' : Bρ = B₁ ≫ B₂) (h₂'' : Fρ = t1 ≫ t2)
    (h₃ : S = b₁ ≫ b₂ ≫ b₃ ≫ b₄)
    (h₄ : b₄ ≫ B₃ = CategoryStruct.id U₃)
    (h₅ : B₆ ≫ Cc = CBIG ≫ E₁)
    (h₆ : CBIG = c₁ ≫ c₂ ≫ c₃ ≫ c₄ ≫ c₅)
    (h₇ : B₅ ≫ c₁ = CategoryStruct.id U₄)
    (h₈ : D = D₁ ≫ D₂ ≫ D₃ ≫ D₄)
    (h₉ : E₁ ≫ D₁ = CategoryStruct.id Z₅)
    (h₁₀ : c₅ ≫ D₂ = CategoryStruct.id T₄)
    (h₁₁ : c₄ ≫ D₃ = Qa ≫ t5)
    (h₁₂ : B₄ ≫ c₂ = cc₂ ≫ Qb)
    (h₁₃ : b₃ ≫ cc₂ = CategoryStruct.id Y₂)
    (h₁₄ : b₂ ≫ Qb ≫ c₃ ≫ Qa = t4) :
    ψ = t1 ≫ t2 ≫ b₁ ≫ t4 ≫ t5 ≫ D₄ := by
  have hA : A ≫ B₁ ≫ B₂ = t1 ≫ t2 ≫ S := by rw [← h₂', h₂, h₂'', Category.assoc]
  rw [h₀, h₁, h₈]
  simp only [Category.assoc]
  rw [reassoc_of% hA, h₃]
  simp only [Category.assoc]
  rw [reassoc_of% h₄, reassoc_of% h₅, h₆]
  simp only [Category.assoc]
  rw [reassoc_of% h₇, reassoc_of% h₉, reassoc_of% h₁₀, reassoc_of% h₁₁, reassoc_of% h₁₂,
    reassoc_of% h₁₃, reassoc_of% h₁₄]

end StacksDraft.DerivedStalkComponentChase

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] additive_restrictScalarsRingSheafStalk
  preservesFiniteLimits_restrictScalarsRingSheafStalk
  preservesFiniteColimits_restrictScalarsRingSheafStalk
  preservesFiniteLimits_restrictScalars_stalkRingMap'
  preservesFiniteColimits_restrictScalars_stalkRingMap'

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] (z : Z)

/-- The component of `derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` at a free object, as
the composite of the components of its four nontrivial rungs: the spelling comparison at `i z`,
the derived stalk of `Ri_*` in the `RingCat` spelling under restriction of scalars along
`ringCatStalkRingEquiv`, the germ square, and the spelling comparison at `z` read backwards. -/
theorem derivedStalkDerivedPushforwardIsoOfSchemesLocalRing_hom_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    (derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app K =
      (derivedStalkSpellingFunctorIsoOfRingSheaf (i.toLRSHom.toShHom.hom.base z)).hom.app
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            i.toLRSHom.toShHom).obj K) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (ringCatStalkRingEquiv
              (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom).mapDerivedCategory.map
          ((Stacks.ClosedImmersion.derivedStalkDerivedPushforwardIsoOfSchemes i z).hom.app K) ≫
        (restrictScalarsStalkMapSquareDerivedIso i z).hom.app
          ((AlgebraicGeometry.SheafOfModules.derivedStalkFunctor
            (structureSheafRing Z.toRingedSpace) z).obj K) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory.map
          ((derivedStalkSpellingFunctorIsoOfRingSheaf z).inv.app K) :=
  (rfl : (derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app K =
      _ ≫ CategoryStruct.id _ ≫ _ ≫ CategoryStruct.id _ ≫ _ ≫ CategoryStruct.id _ ≫ _).trans
    (StacksDraft.DerivedStalkComponentChase.comp_id_comp₄ _ _ _ _)

/-- **The derived stalk of a derived pushforward along a closed immersion, at a complex.**  For a
closed immersion of schemes `i : Z ⟶ X`, a point `z` of `Z` and a cochain complex `C` of
`𝒪_Z`-modules, the component of
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` at
`DerivedCategory.Q.obj C` is the comparison `Ri_* ≅ i_*` followed by the factorization of `i_*`,
both under the derived stalk at `i z`, then the factorization of the stalk functor at `i z`, then
`DerivedCategory.Q` of the *degreewise* germ map `Stacks.ModuleSkyscraper.pushStalkMap`, then the
two factorizations of `(−)_z ⋙ restrictScalars (i^♯_z)` read backwards. -/
theorem derivedStalkDerivedPushforwardIsoOfSchemesLocalRing_hom_app_Q
    (C : CochainComplex Z.Modules ℤ) :
    (derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app
        (DerivedCategory.Q.obj C) =
      (AlgebraicGeometry.derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z)).map
          ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
            i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj C)) ≫
        (AlgebraicGeometry.derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z)).map
          ((modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app C) ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X
            (i.toLRSHom.toShHom.hom.base z)).mapDerivedCategoryFactors.hom.app
          (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (Stacks.ModuleSkyscraper.pushStalkMap i z) (ComplexShape.up ℤ)).app C) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategoryFactors.inv.app
          (((Stacks.ModuleSkyscraper.modulesStalkFunctor Z z).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj C) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory.map
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor Z
            z).mapDerivedCategoryFactors.inv.app C) := by
  have h₀ := derivedStalkDerivedPushforwardIsoOfSchemesLocalRing_hom_app i z
    (DerivedCategory.Q.obj C)
  have h₁ := (congrArg (fun t => (ModuleCat.restrictScalars.{u, u, u}
        (ringCatStalkRingEquiv
          (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom).mapDerivedCategory.map t)
      (Stacks.ClosedImmersion.derivedStalkDerivedPushforwardIso_hom_app_Q
        i.toLRSHom.toShHom z
        (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i).isInducing C)).trans
    (StacksDraft.DerivedStalkComponentChase.map_comp₆ _ _ _ _ _ _ _)
  have h₂ := ((derivedStalkSpellingFunctorIsoOfRingSheaf
      (i.toLRSHom.toShHom.hom.base z)).hom.naturality
    ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
        i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj C) ≫
      (modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app C)).symm
  have h₂' := StacksDraft.DerivedStalkComponentChase.comp_map_comp₂
    (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X.toRingedSpace)
      (i.toLRSHom.toShHom.hom.base z))
    (ModuleCat.restrictScalars.{u, u, u}
      (ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom).mapDerivedCategory
    ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
      i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj C))
    ((modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app C)
  have h₂'' := StacksDraft.DerivedStalkComponentChase.map_comp₂
    (AlgebraicGeometry.derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z))
    ((Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategory
      i.toLRSHom.toShHom).hom.app (DerivedCategory.Q.obj C))
    ((modulePushforward i.toLRSHom.toShHom).mapDerivedCategoryFactors.hom.app C)
  have h₃ := derivedStalkSpellingFunctorIsoOfRingSheaf_hom_app_Q
    (i.toLRSHom.toShHom.hom.base z)
    (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
  have h₄ := StacksDraft.DerivedStalkComponentChase.map_inv_hom
    (ModuleCat.restrictScalars.{u, u, u}
      (ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom).mapDerivedCategory
    _ _ (Iso.inv_hom_id_app
      (modulesRingCatStalkFunctor (i.toLRSHom.toShHom.hom.base z)).mapDerivedCategoryFactors
      (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj C))
  have h₅ := (restrictScalarsStalkMapSquareDerivedIso i z).hom.naturality
    ((modulesRingCatStalkFunctor z).mapDerivedCategoryFactors.inv.app C)
  have h₆ := restrictScalarsStalkMapSquareDerivedIso_hom_app_Q i z
    (((modulesRingCatStalkFunctor z).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
  have h₇ := StacksDraft.DerivedStalkComponentChase.map_inv_hom
    (ModuleCat.restrictScalars.{u, u, u}
      (ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom).mapDerivedCategory
    _ _ (Iso.inv_hom_id_app
      (ModuleCat.restrictScalars.{u, u, u}
        (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom).mapDerivedCategoryFactors
      (((modulesRingCatStalkFunctor z).mapHomologicalComplex (ComplexShape.up ℤ)).obj C))
  have h₈ := (congrArg (fun t => (ModuleCat.restrictScalars.{u, u, u}
        (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory.map t)
      (derivedStalkSpellingFunctorIsoOfRingSheaf_inv_app_Q z C)).trans
    (StacksDraft.DerivedStalkComponentChase.map_comp₄ _ _ _ _ _).symm
  have h₉ := StacksDraft.DerivedStalkComponentChase.map_map_inv_hom
    (ModuleCat.restrictScalars.{u, u, u}
      (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory
    (ModuleCat.restrictScalars.{u, u, u}
      (ringCatStalkRingEquiv z).symm.toRingHom).mapDerivedCategory
    _ _ (Iso.inv_hom_id_app (modulesRingCatStalkFunctor z).mapDerivedCategoryFactors C)
  have h₁₀ := StacksDraft.DerivedStalkComponentChase.map_inv_hom
    (ModuleCat.restrictScalars.{u, u, u}
      (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory
    _ _ (Iso.inv_hom_id_app
      (ModuleCat.restrictScalars.{u, u, u}
        (ringCatStalkRingEquiv z).symm.toRingHom).mapDerivedCategoryFactors
      (((modulesRingCatStalkFunctor z).mapHomologicalComplex (ComplexShape.up ℤ)).obj C))
  have h₁₁ := ((ModuleCat.restrictScalars.{u, u, u}
      (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategoryFactors.inv.naturality
    ((NatIso.mapHomologicalComplex (modulesRingCatStalkFunctorIso z)
      (ComplexShape.up ℤ)).hom.app C)).symm
  have h₁₂ := (ModuleCat.restrictScalars.{u, u, u}
      (ringCatStalkRingEquiv
        (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom).mapDerivedCategoryFactors.hom.naturality
    ((NatIso.mapHomologicalComplex
      (Stacks.ClosedImmersion.stalkPushforwardModuleFunctorIso i.toLRSHom.toShHom z
        (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i).isInducing)
      (ComplexShape.up ℤ)).hom.app C)
  have h₁₃ := Iso.inv_hom_id_app
    (ModuleCat.restrictScalars.{u, u, u}
      (ringCatStalkRingEquiv
        (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom).mapDerivedCategoryFactors
    (((modulesRingCatStalkFunctor (i.toLRSHom.toShHom.hom.base z)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj C))
  have h₁₄ := (StacksDraft.DerivedStalkComponentChase.map_comp₄ DerivedCategory.Q _ _ _ _).trans
    (congrArg (fun t => DerivedCategory.Q.map t) (derivedStalkPushforwardTail i z C))
  exact StacksDraft.DerivedStalkComponentChase.localRingComponentChase h₀ h₁ h₂ h₂' h₂'' h₃ h₄ h₅
    h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄

end AlgebraicGeometry

end

end
