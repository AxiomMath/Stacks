module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationModulePullback
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationCartesianModule
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentTransitionComparison
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleBarLowerShriek
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleResolution
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# The resolution of the pullback of a module along a ringed augmentation

Let `A` be a ringed augmentation of a simplicial-site situation `S` towards a ringed site
`(D, K, O_D)` as in Stacks 0D9D, with total morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` and component morphisms `a_n = a ∘ g_n`. For a sheaf of
`O_D`-modules `G` the lower shriek images `g_{n!}(a_n^*G)` of Stacks 0D72 carry an exact complex

`… ⟶ g_{2!}(a_2^*G) ⟶ g_{1!}(a_1^*G) ⟶ g_{0!}(a_0^*G) ⟶ a^*G ⟶ 0`

of sheaves of `O`-modules on the total site, whose differentials are the alternating sums of the
canonical face maps.

That assertion is recorded here as
`CategoryTheory.SimplicialSiteSituation.RingedAugmentation.ModuleResolution`, and it is proved
for every coefficient module `G` by the simplex-coefficient resolution `n ↦ B_n(a^*G)` of
`a^*G`. For the structure sheaf `O_D` read as a module over itself it is also obtained from the
resolution of the structure sheaf of Stacks 0D9B, since `a^*O_D = O` and `a_n^*O_D = O_n`.

## Main definitions

Names below are in the namespace
`CategoryTheory.SimplicialSiteSituation.RingedAugmentation`.

* `totalPullbackModule` and `componentPullbackModule`: the pullbacks `a^*G` and `a_n^*G` of a
  sheaf of `O_D`-modules along the total and the component morphisms of ringed topoi.
* `resolutionTerm`: the term `g_{n!}(a_n^*G)` of the complex.
* `ModuleResolution`: the exact complex of Stacks 0D7C as a structure — a chain complex of
  sheaves of `O`-modules whose term in degree `n` is `g_{n!}(a_n^*G)`, carrying a simplicial
  structure indexed by the simplex maps whose alternating-face differentials are those of the
  complex, together with an augmentation onto `a^*G`, exactness in every positive degree,
  exactness at the augmentation and epimorphy of the augmentation.
* `ModuleResolution.ofCoefficientIso`: an isomorphism of coefficient modules carries a
  resolution over.
* `componentPullbackModuleIsoLiteralRestriction`: `a_n^*G` is the literal restriction of `a^*G`
  to the degree-`n` component.
* `moduleBarSheafIsoResolutionTerm`: the degree-`n` term of the simplex-coefficient resolution of
  `a^*G` is `g_{n!}(a_n^*G)`.
* `simplexModuleResolution`: the resolution of Stacks 0D7C for an arbitrary coefficient module.

## Main results

* `nonempty_moduleResolution_unit`: the resolution for the structure sheaf of the augmentation
  site as the coefficient module.
* `totalPullbackModule_isCartesianModule`: `a^*G` is cartesian in the literal presentation of
  restriction to the components (Stacks 0D7H (3)).
* `nonempty_moduleResolution_of_iso_unit`: **Stacks 0D7C**, the resolution exists for every
  coefficient module.

## Implementation notes

The complex is indexed by `ℕ` with `g_{n!}(a_n^*G)` in index `n`, and the augmentation is a
separate field rather than the term in index `-1`, which is the indexing of the resolution of
Stacks 0D9B that this file consumes.

The differentials are pinned by `faceMap_id`, `faceMap_comp` and `differential_eq`: the terms of
the complex carry a simplicial structure indexed by the simplex maps, and the differentials are
the alternating-face differentials of that simplicial object. Without those three fields a chain
complex with the stated terms and arbitrary differentials would satisfy the structure.

The augmentation is left unpinned, as in the source, which asserts only that an exact complex of
the displayed shape exists. Pinning it to the adjunct of
the canonical comparison `a_0^*G ≅ g_0^*(a^*G)` of
`CategoryTheory.SimplicialSiteSituation.RingedAugmentation.componentPullbackModulesIso` would
need the comparison of the pullback of sheaves of modules along the component morphism of ringed
topoi with the literal restriction of
`CategoryTheory.SimplicialSiteSituation.componentModuleRestriction`, whose left adjoint `g_{n!}`
is; that comparison is not available for sheaves of modules in this development, see the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModulePullbackRestriction.lean`.

Lower shriek is `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriek`, the left
adjoint of restriction of sheaves of modules to a component, and it is applied to `a_n^*G`
because the sheaf of rings it is taken over — the restriction of `O` to the degree-`n`
component — is the structure sheaf of the component ringed topos on the nose, which is
`CategoryTheory.SimplicialSiteSituation.componentRingSheaf_structureRingSheaf`. Coefficients
therefore sit at the universe of the situation, as they do for that left adjoint.

## The general coefficient module

For a general coefficient module the identification of the degree-`n` term of the
simplex-coefficient resolution of `a^*G` with `g_{n!}(a_n^*G)` is
`moduleBarSheafIsoResolutionTerm`: `a^*G` is cartesian
(`totalPullbackModule_isCartesianModule`), so the comparison `moduleBarLowerShriekMap` of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleBarLowerShriek.lean` is an
isomorphism at it.

## References

* [Stacks Project, Tag 0D7C](https://stacks.math.columbia.edu/tag/0D7C)
* [Stacks Project, Section 85.11 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
* [Stacks Project, Tag 0D9B](https://stacks.math.columbia.edu/tag/0D9B)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-! ### The face maps of the resolution of the structure sheaf are simplicial

The maps `CategoryTheory.SimplicialSiteSituation.SimplicialModuleResolution.faceMap` of the
resolution of Stacks 0D9B are the relabelling maps of the explicit free model, so they compose
contravariantly in the simplex map. -/

section FaceMaps

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})

private theorem simplexIndicesMap_id (n : SimplexCategory) :
    simplexIndicesMap.{u, u} S (𝟙 n) = 𝟙 (simplexIndices.{u, u} S n) := by
  simp [simplexIndicesMap, simplexIndices]

private theorem simplexIndicesMap_comp {m n k : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ k) :
    simplexIndicesMap.{u, u} S (φ ≫ ψ) =
      simplexIndicesMap.{u, u} S ψ ≫ simplexIndicesMap.{u, u} S φ := by
  simp only [simplexIndicesMap, op_comp, Functor.map_comp,
    Functor.whiskerRight_comp, Functor.whiskerLeft_comp]
  rfl

private theorem componentFreeMap_id (n : SimplexCategory) :
    componentFreeMap S O (𝟙 n) = 𝟙 (componentFreePresheaf S O n) := by
  rw [componentFreeMap, simplexIndicesMap_id S n]
  exact (PresheafOfModules.free O.obj).map_id _

private theorem componentFreeMap_comp {m n k : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ k) :
    componentFreeMap S O (φ ≫ ψ) = componentFreeMap S O ψ ≫ componentFreeMap S O φ := by
  rw [componentFreeMap, componentFreeMap, componentFreeMap, simplexIndicesMap_comp S φ ψ]
  exact (PresheafOfModules.free O.obj).map_comp _ _

variable {S O}

/-- The face map of an identity simplex map is the identity. -/
private theorem faceMap_id (R : SimplicialModuleResolution S O) (n : ℕ) :
    R.faceMap (𝟙 ⦋n⦌) = 𝟙 (R.complex.X n) := by
  apply (SheafOfModules.forget O).map_injective
  change (R.degreeIso n).hom ≫ componentFreeMap S O (𝟙 ⦋n⦌) ≫ (R.degreeIso n).inv = _
  rw [componentFreeMap_id S O ⦋n⦌, Category.id_comp, Iso.hom_inv_id]
  exact ((SheafOfModules.forget O).map_id _).symm

/-- The face maps compose contravariantly in the simplex map. -/
private theorem faceMap_comp (R : SimplicialModuleResolution S O) {m n k : ℕ}
    (φ : ⦋m⦌ ⟶ ⦋n⦌) (ψ : ⦋n⦌ ⟶ ⦋k⦌) :
    R.faceMap (φ ≫ ψ) = R.faceMap ψ ≫ R.faceMap φ := by
  apply (SheafOfModules.forget O).map_injective
  change (R.degreeIso k).hom ≫ componentFreeMap S O (φ ≫ ψ) ≫ (R.degreeIso m).inv =
    ((R.degreeIso k).hom ≫ componentFreeMap S O ψ ≫ (R.degreeIso n).inv) ≫
      ((R.degreeIso n).hom ≫ componentFreeMap S O φ ≫ (R.degreeIso m).inv)
  rw [componentFreeMap_comp S O φ ψ]
  simp [Category.assoc]

end FaceMaps

namespace RingedAugmentation

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

/-- The pullback `a^*G` of a sheaf of `O_D`-modules along the total morphism of ringed topoi of
a ringed augmentation. -/
def totalPullbackModule (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.O) :=
  (A.totalRingedHom.toModulesHom.pullbackModules).obj G

/-- The pullback `a_n^*G` of a sheaf of `O_D`-modules along the morphism of ringed topoi
`a_n = a ∘ g_n` of the simplicial degree `n`. -/
def componentPullbackModule (n : SimplexCategory)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD)) :
    SheafOfModules.{u} (S.componentRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf A.O) n) :=
  ((A.componentRingedHom n).toModulesHom.pullbackModules).obj G

/-- The term `g_{n!}(a_n^*G)` of the resolution of Stacks 0D7C: the lower shriek image of
Stacks 0D72 of the pullback of `G` to the degree-`n` component. -/
def resolutionTerm (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) A.OD))
    (n : ℕ) :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) A.O) :=
  (componentModuleLowerShriek S
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) A.O) ⦋n⦌).obj
    (A.componentPullbackModule ⦋n⦌ G)

/-- An exact complex of sheaves of `O`-modules on the total site resolving `a^*G` by the lower
shriek images `g_{n!}(a_n^*G)`: a chain complex whose term in degree `n` is `g_{n!}(a_n^*G)`,
whose differentials are the alternating sums of a family of face maps indexed by the simplex
maps, augmented onto `a^*G`, exact in every positive degree and at the augmentation, the
augmentation being an epimorphism. -/
structure ModuleResolution
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) A.OD)) where
  /-- The chain complex, with `g_{n!}(a_n^*G)` in degree `n`. -/
  complex : ChainComplex
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) A.O)) ℕ
  /-- In degree `n` the complex is `g_{n!}(a_n^*G)`. -/
  degreeIso (n : ℕ) : complex.X n ≅ A.resolutionTerm G n
  /-- The map of the complex attached to a simplex map `φ : [m] ⟶ [n]`. -/
  faceMap {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) : complex.X n ⟶ complex.X m
  /-- The map attached to an identity simplex map is the identity. -/
  faceMap_id (n : ℕ) : faceMap (𝟙 ⦋n⦌) = 𝟙 (complex.X n)
  /-- The maps compose contravariantly in the simplex map, so the terms of the complex together
  with these maps form a simplicial object. -/
  faceMap_comp {m n k : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) (ψ : ⦋n⦌ ⟶ ⦋k⦌) :
    faceMap (φ ≫ ψ) = faceMap ψ ≫ faceMap φ
  /-- The differential is the alternating sum of the maps attached to the standard cofaces, so
  the complex is the alternating-face complex of that simplicial object. -/
  differential_eq (n : ℕ) :
    complex.d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • faceMap (SimplexCategory.δ i)
  /-- The augmentation `g_{0!}(a_0^*G) ⟶ a^*G` of the complex. -/
  augmentation : complex.X 0 ⟶ A.totalPullbackModule G
  /-- The augmentation annihilates the first differential, so the augmented complex is a
  complex. -/
  augmentation_comp : complex.d 1 0 ≫ augmentation = 0
  /-- The complex is exact in every positive degree. -/
  exact_positive (n : ℕ) (hn : 0 < n) : complex.ExactAt n
  /-- The complex is exact at the augmentation. -/
  exact_zero :
    (ShortComplex.mk (complex.d 1 0) augmentation augmentation_comp).Exact
  /-- The augmentation is an epimorphism, so the complex ends in `a^*G ⟶ 0`. -/
  augmentation_epi : Epi augmentation

/-- The pullback of the structure sheaf of the augmentation site along the morphism of ringed
topoi of the simplicial degree `n` is the structure sheaf of that component: `a_n^*O_D = O_n`. -/
def componentPullbackModuleUnitIso (n : SimplexCategory) :
    SheafOfModules.unit (S.componentRingSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) A.O) n) ≅
      A.componentPullbackModule n
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf A.augmentationRingedTopos.O)) :=
  pullbackModulesObjUnitIso (A.componentRingedHom n).toModulesHom

/-- The pullback of the structure sheaf of the augmentation site along the total morphism of
ringed topoi is the structure sheaf of the total site: `a^*O_D = O`. -/
def totalPullbackModuleUnitIso :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf A.O) ≅
      A.totalPullbackModule (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf A.augmentationRingedTopos.O)) :=
  pullbackModulesObjUnitIso A.totalRingedHom.toModulesHom

/-- The resolution of the structure sheaf of Stacks 0D9B has `g_{n!}(a_n^*O_D)` in degree `n`:
its term there is `g_{n!}O_n`, and `a_n^*O_D = O_n`. -/
def unitResolutionDegreeIso
    (R : S.SimplicialModuleResolutionActual
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) A.O)) (n : ℕ) :
    R.complex.X n ≅
      A.resolutionTerm (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf A.augmentationRingedTopos.O)) n :=
  eqToIso (R.lowerShriekDegreeEq n) ≪≫
    (componentModuleLowerShriek S
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) A.O) ⦋n⦌).mapIso
      (A.componentPullbackModuleUnitIso ⦋n⦌)

/-- The resolution of Stacks 0D7C for the structure sheaf of the augmentation site as the
coefficient module. Both pullbacks of the structure sheaf are structure sheaves, `a^*O_D = O` and
`a_n^*O_D = O_n`, so the complex is the resolution `… ⟶ g_{1!}O_1 ⟶ g_{0!}O_0 ⟶ O ⟶ 0` of
Stacks 0D9B read through those two identifications. -/
theorem nonempty_moduleResolution_unit :
    Nonempty (A.ModuleResolution
      (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf A.augmentationRingedTopos.O))) := by
  obtain ⟨R⟩ := nonempty_simplicialModuleResolution S (Stacks.SheafOfModules.Tensor.ringSheaf A.O)
  have hcomp : R.complex.d 1 0 ≫
      (R.augmentation ≫ A.totalPullbackModuleUnitIso.hom) = 0 := by
    rw [← Category.assoc, R.augmentation_comp, Limits.zero_comp]
  refine ⟨{ complex := R.complex
            degreeIso := A.unitResolutionDegreeIso R
            faceMap := fun φ => R.toSimplicialModuleResolution.faceMap φ
            faceMap_id := faceMap_id R.toSimplicialModuleResolution
            faceMap_comp := fun φ ψ => faceMap_comp R.toSimplicialModuleResolution φ ψ
            differential_eq := R.toSimplicialModuleResolution.differential_eq_sum_faceMap
            augmentation := R.augmentation ≫ A.totalPullbackModuleUnitIso.hom
            augmentation_comp := hcomp
            exact_positive := R.exact_positive
            exact_zero := ?_
            augmentation_epi := ?_ }⟩
  · have e :
        ShortComplex.mk (R.complex.d 1 0) R.augmentation R.augmentation_comp ≅
          ShortComplex.mk (R.complex.d 1 0)
            (R.augmentation ≫ A.totalPullbackModuleUnitIso.hom) hcomp :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) A.totalPullbackModuleUnitIso
        (by simp) (by simp)
    exact ShortComplex.exact_of_iso e R.exact_zero
  · have hepi : Epi R.augmentation := R.augmentation_epi
    exact epi_comp _ _

/-- An isomorphism of coefficient modules carries `a_n^*G` to `a_n^*G'`. -/
def componentPullbackModuleMapIso (n : SimplexCategory)
    {G G' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) A.OD)}
    (e : G ≅ G') :
    A.componentPullbackModule n G ≅ A.componentPullbackModule n G' :=
  ((A.componentRingedHom n).toModulesHom.pullbackModules).mapIso e

/-- An isomorphism of coefficient modules carries `a^*G` to `a^*G'`. -/
def totalPullbackModuleMapIso
    {G G' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) A.OD)}
    (e : G ≅ G') : A.totalPullbackModule G ≅ A.totalPullbackModule G' :=
  (A.totalRingedHom.toModulesHom.pullbackModules).mapIso e

/-- An isomorphism of coefficient modules carries the term `g_{n!}(a_n^*G)` of the resolution to
the term `g_{n!}(a_n^*G')`. -/
def resolutionTermMapIso
    {G G' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) A.OD)}
    (e : G ≅ G') (n : ℕ) : A.resolutionTerm G n ≅ A.resolutionTerm G' n :=
  (componentModuleLowerShriek S
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology)) A.O) ⦋n⦌).mapIso
    (A.componentPullbackModuleMapIso ⦋n⦌ e)

/-- A resolution of `a^*G` is a resolution of `a^*G'` for an isomorphic coefficient module `G'`:
the complex is unchanged, the identification of its terms and its augmentation being composed
with the images of the isomorphism. -/
def ModuleResolution.ofCoefficientIso
    {G G' : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) A.OD)}
    (R : A.ModuleResolution G) (e : G ≅ G') : A.ModuleResolution G' where
  complex := R.complex
  degreeIso n := R.degreeIso n ≪≫ A.resolutionTermMapIso e n
  faceMap φ := R.faceMap φ
  faceMap_id n := R.faceMap_id n
  faceMap_comp φ ψ := R.faceMap_comp φ ψ
  differential_eq n := R.differential_eq n
  augmentation := R.augmentation ≫ (A.totalPullbackModuleMapIso e).hom
  augmentation_comp := by
    rw [← Category.assoc, R.augmentation_comp, Limits.zero_comp]
  exact_positive := R.exact_positive
  exact_zero := by
    have hiso :
        ShortComplex.mk (R.complex.d 1 0) R.augmentation R.augmentation_comp ≅
          ShortComplex.mk (R.complex.d 1 0)
            (R.augmentation ≫ (A.totalPullbackModuleMapIso e).hom)
            (by rw [← Category.assoc, R.augmentation_comp, Limits.zero_comp]) :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (A.totalPullbackModuleMapIso e)
        (by simp) (by simp)
    exact ShortComplex.exact_of_iso hiso R.exact_zero
  augmentation_epi := by
    have hepi : Epi R.augmentation := R.augmentation_epi
    exact epi_comp _ _

/-- The pullback `a^*G` of a sheaf of `O_D`-modules along the ringed augmentation is a cartesian
sheaf of `O`-modules: every transition `f_φ^*((a^*G)|_m) ⟶ (a^*G)|_n` between its literal
restrictions to the components is an isomorphism. -/
theorem totalPullbackModule_isCartesianModule
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD)) :
    S.IsCartesianModule A.O (A.totalPullbackModule G) := by
  intro m n φ
  have : IsIso ((S.moduleFiberTransition A.O φ).app (A.totalPullbackModule G)) :=
    A.isCartesianModule_pullbackModules G φ
  exact S.isIso_fiberTransitionModules_of_isIso_moduleFiberTransition A.O φ
    (A.totalPullbackModule G) (S.moduleFiberTransition_comp_restrictionIso A.O φ _)

/-- The pullback `a_n^*G` along the morphism of ringed topoi of degree `n` is isomorphic to the
literal restriction of `a^*G` to the degree-`n` component. -/
def componentPullbackModuleIsoLiteralRestriction (n : SimplexCategory)
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD)) :
    A.componentPullbackModule n G ≅
      (S.componentModuleRestriction (S.totalRingSheaf A.O) n).obj (A.totalPullbackModule G) :=
  (A.componentPullbackModulesIso n).app G ≪≫
    (componentPullbackModulesRestrictionIso S A.O n).app (A.totalPullbackModule G)

/-- The degree-`n` term of the simplex-coefficient resolution of `a^*G` is isomorphic to
`g_{n!}(a_n^*G)`. -/
def moduleBarSheafIsoResolutionTerm
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD)) (n : ℕ) :
    moduleBarSheaf (A.totalPullbackModule G) ⦋n⦌ ≅ A.resolutionTerm G n :=
  (@asIso _ _ _ _ (moduleBarLowerShriekMap A.O (A.totalPullbackModule G) ⦋n⦌)
      (isIso_moduleBarLowerShriekMap A.O _ (A.totalPullbackModule_isCartesianModule G) ⦋n⦌)).symm ≪≫
    (S.componentModuleLowerShriek (S.totalRingSheaf A.O) ⦋n⦌).mapIso
      (A.componentPullbackModuleIsoLiteralRestriction ⦋n⦌ G).symm

/-- The resolution of Stacks 0D7C for a sheaf of `O_D`-modules `G`: the simplex-coefficient
resolution of `a^*G`, whose degree-`n` term is identified with `g_{n!}(a_n^*G)`, whose
differentials are the alternating sums of its face maps, and which is augmented onto `a^*G`. -/
def simplexModuleResolution (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD)) :
    A.ModuleResolution G where
  complex := moduleBarComplex (A.totalPullbackModule G)
  degreeIso n := A.moduleBarSheafIsoResolutionTerm G n
  faceMap φ := (moduleBarSimplicial (A.totalPullbackModule G)).map φ.op
  faceMap_id _ := (moduleBarSimplicial (A.totalPullbackModule G)).map_id _
  faceMap_comp φ ψ := (moduleBarSimplicial (A.totalPullbackModule G)).map_comp ψ.op φ.op
  differential_eq n := AlgebraicTopology.alternatingFaceMapComplex_obj_d _ n
  augmentation := (moduleBarAugmented (A.totalPullbackModule G)).hom.app (Opposite.op ⦋0⦌)
  augmentation_comp := moduleBarComplex_d_comp_augmentation _
  exact_positive := moduleBarComplex_exactAt _
  exact_zero := moduleBarComplex_exact_zero _
  augmentation_epi := moduleBarAugmentation_epi _

/-- **Stacks 0D7C.** With the notation of Stacks 0D9D, for a sheaf of `O_D`-modules `G` the
lower shriek images `g_{n!}(a_n^*G)` of Stacks 0D72 carry an exact complex

`… ⟶ g_{2!}(a_2^*G) ⟶ g_{1!}(a_1^*G) ⟶ g_{0!}(a_0^*G) ⟶ a^*G ⟶ 0`

of sheaves of `O`-modules on the total site, with differentials the alternating sums of the
canonical face maps. The complex is `simplexModuleResolution`, the simplex-coefficient
resolution of `a^*G`. -/
@[stacks 0D7C "for an arbitrary coefficient module, by the simplex-coefficient resolution"]
theorem nonempty_moduleResolution_of_iso_unit
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf A.OD)) :
    Nonempty (A.ModuleResolution G) :=
  ⟨A.simplexModuleResolution G⟩

end RingedAugmentation

end CategoryTheory.SimplicialSiteSituation

end
