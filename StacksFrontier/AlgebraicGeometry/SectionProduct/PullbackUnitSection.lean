module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.UnitScalar
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pulling back a global section, read as a morphism out of the monoidal unit

Let `j : Y' ⟶ Y` be a morphism of schemes. A global section of an `𝒪_Y`-module `M` is described
in two ways in this development, and the two carry different notions of pullback:

* as an element of `Γ(M, ⊤)`, whose pullback is `AlgebraicGeometry.pullbackSectionHom`, the unit
  of the adjunction `j^* ⊣ j_*` evaluated on sections;
* as a morphism `𝟙_ Y.Modules ⟶ M` out of the monoidal unit, which `j^*` carries to a morphism
  `j^*(𝟙_ Y.Modules) ⟶ j^*M` and so, after the structure-sheaf comparison of Stacks Tag 01CD,
  to a morphism `𝟙_ Y'.Modules ⟶ j^*M`.

This file identifies them.

## Main definitions

* `Stacks.PullbackUnitSection.unitPullbackHom` and `unitPullbackIso`: **the comparison
  `j^*𝒪_{Y'} ≅ 𝒪_Y`**, `Stacks.PullbackAlgebra.unitComparison` retyped at the monoidal unit of
  `Stacks.SheafInternalHom.schemeMonoidalCategory` by the counit of sheafification
  `Stacks.SectionRingGeometric.unitComparison`.
* `Stacks.PullbackUnitSection.unitPullback`: the inverse of that comparison, i.e. the morphism
  `𝟙_ Y'.Modules ⟶ j^*(𝟙_ Y.Modules)` through which `j^*` takes a morphism out of the unit again
  to a morphism out of the unit.

## Main results

* `Stacks.PullbackUnitSection.globalSection_unitPullback`: the global section of the comparison
  is the pullback of the global section of the identity, which is the degree zero case and the
  whole content of the bridge.
* `Stacks.PullbackUnitSection.pullbackSectionHom_globalSection`: **the bridge.** For
  `f : 𝟙_ Y.Modules ⟶ M`, the pullback of the global section of `f` is the global section of
  `unitPullback j ≫ j^*f`.
* `Stacks.PullbackUnitSection.pullbackSectionHom_app`: pulling a section back commutes with
  applying a morphism of modules, at the `Scheme.Modules.Hom.app` spelling of the action on
  sections.

## Implementation notes

The degree zero case is `Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit` at the unit
section: the structure-sheaf comparison carries the pullback of `1` to `j^♯ 1 = 1`. Three
spellings have to be crossed to say so. The monoidal unit of
`Stacks.SheafInternalHom.schemeMonoidalCategory` is the sheafification of the presheaf unit while
`Stacks.PullbackAlgebra.unitComparison` is stated for `SheafOfModules.unit`, which is the
discrepancy `Stacks.SectionRingGeometric.unitComparison` measures; the pullback functor is spelled
`AlgebraicGeometry.Scheme.Modules.pullback` here and
`RingedSpaceModuleAdjunction.modulePullback` there; and `AlgebraicGeometry.pullbackSectionHom`
restricts along `⊤ ≤ j^{-1}⊤`, a morphism of opens which is the identity because the homomorphisms
of a poset are unique. Each pair is equal by `rfl` and not syntactically, so — following the
discipline of `StacksFrontier/AlgebraicGeometry/SectionProduct/MonoidalUnitBridge.lean` — the
crossings happen inside proofs given by `:=` or `exact`, which are defeq-tolerant, rather than in
a `rw` whose motive is checked at a lower transparency.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory Category MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SectionProduct (globalSection)
open Stacks.SectionRingGeometric (unitComparison unitModule unitOne)

universe u

namespace Stacks.PullbackUnitSection

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y)

/-! ### Pulling a section back commutes with a morphism of modules -/

/-- **Pulling a section back commutes with applying a morphism of modules**, at the
`AlgebraicGeometry.Scheme.Modules.Hom.app` spelling of the action on sections. This is
`AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality`. -/
theorem pullbackSectionHom_app {M N : Y.Modules} (g : M ⟶ N) (U : Y.Opens) (V : Y'.Opens)
    (h : V ≤ j ⁻¹ᵁ U) (x : Γ(M, U)) :
    pullbackSectionHom j N U V h (g.app U x) =
      ((Scheme.Modules.pullback j).map g).app V (pullbackSectionHom j M U V h x) :=
  (Scheme.Modules.pullbackSection_naturality j g U V h x).symm

/-! ### The comparison at the monoidal unit -/

/-- **The pullback of the structure sheaf is the structure sheaf**,
`Stacks.PullbackAlgebra.pullbackUnitIso` with its type ascribed at the `Scheme.Modules` spelling
of the module pullback and the `Stacks.SectionRingGeometric.unitModule` spelling of the free
rank-one sheaf. The two spellings are equal by `rfl`; the ascription is what lets the action on
sections be written `Scheme.Modules.Hom.app`. -/
@[ega "IV 8.5.1" "more general"]
def unitRingedIso :
    (Scheme.Modules.pullback j).obj (unitModule Y) ≅ unitModule Y' :=
  Stacks.PullbackAlgebra.pullbackUnitIso j.toLRSHom.toShHom

/-- **The structure-sheaf comparison of Stacks Tag 01CD, at the monoidal unit**:
`j^*(𝟙_ Y.Modules) ≅ 𝟙_ Y'.Modules`. It is `unitRingedIso`, conjugated at both ends by the counit
of sheafification which compares the monoidal unit with `SheafOfModules.unit`. -/
def unitPullbackIso : (Scheme.Modules.pullback j).obj (𝟙_ Y.Modules) ≅ 𝟙_ Y'.Modules :=
  (Scheme.Modules.pullback j).mapIso (unitComparison Y) ≪≫ unitRingedIso j ≪≫
    (unitComparison Y').symm

/-- The forward direction of that comparison. -/
def unitPullbackHom :
    (Scheme.Modules.pullback j).obj (𝟙_ Y.Modules) ⟶ 𝟙_ Y'.Modules :=
  (unitPullbackIso j).hom

/-- The forward comparison `unitPullbackHom` is an isomorphism. -/
instance isIso_unitPullbackHom : IsIso (unitPullbackHom j) :=
  ⟨(unitPullbackIso j).inv, (unitPullbackIso j).hom_inv_id, (unitPullbackIso j).inv_hom_id⟩

/-- `unitPullbackHom`, unfolded: `j^*` of the counit comparison at `Y`, then `unitRingedIso`,
then the inverse counit comparison at `Y'`. -/
theorem unitPullbackHom_eq :
    unitPullbackHom j =
      (Scheme.Modules.pullback j).map (unitComparison Y).hom ≫
        (unitRingedIso j).hom ≫ (unitComparison Y').inv :=
  rfl

/-- **The morphism out of the monoidal unit through which `j^*` carries a global section**: the
inverse of the structure-sheaf comparison. -/
def unitPullback : 𝟙_ Y'.Modules ⟶ (Scheme.Modules.pullback j).obj (𝟙_ Y.Modules) :=
  (unitPullbackIso j).inv

/-- `unitPullback` is a right inverse of `unitPullbackHom`. -/
@[simp] theorem unitPullback_comp_unitPullbackHom :
    unitPullback j ≫ unitPullbackHom j = 𝟙 (𝟙_ Y'.Modules) :=
  (unitPullbackIso j).inv_hom_id

/-! ### The bridge -/

/-- The global section of a morphism out of the monoidal unit is the image of the global section
of the identity. -/
theorem globalSection_eq_app (M : Y.Modules) (f : 𝟙_ Y.Modules ⟶ M) :
    globalSection Y M f = f.app ⊤ (globalSection Y (𝟙_ Y.Modules) (𝟙 (𝟙_ Y.Modules))) :=
  rfl

/-- The global section of the identity of the monoidal unit is the unit section, read through the
counit of sheafification. -/
theorem globalSection_id (X : Scheme.{u}) :
    globalSection X (𝟙_ X.Modules) (𝟙 (𝟙_ X.Modules)) =
      (unitComparison X).inv.app ⊤ (unitOne X) := by
  change Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv X _ _ = _
  rw [Stacks.SectionRingGeometric.schemeGlobalSectionsAddEquiv_apply, Category.comp_id]

/-- The image of the unit section under the counit of sheafification is the global section of the
identity of the monoidal unit. -/
theorem unitComparison_hom_app_globalSection :
    (unitComparison Y).hom.app ⊤ (globalSection Y (𝟙_ Y.Modules) (𝟙 (𝟙_ Y.Modules))) =
      unitOne Y :=
  (congrArg (fun z => (unitComparison Y).hom.app ⊤ z) (globalSection_id Y)).trans
    (congrFun (congrArg (fun φ => (ConcreteCategory.hom (Scheme.Modules.Hom.app φ ⊤) : _ → _))
      (unitComparison Y).inv_hom_id) (unitOne Y))

/-- **Pulling a global section back is the unit of the adjunction**, the restriction along
`⊤ ≤ j^{-1}⊤` being an identity because the homomorphisms of a poset are unique. -/
theorem pullbackSectionHom_top_eq (M : Y.Modules)
    (h : (⊤ : Y'.Opens) ≤ j ⁻¹ᵁ (⊤ : Y.Opens)) (x : Γ(M, ⊤)) :
    pullbackSectionHom j M ⊤ ⊤ h x =
      Stacks.RingedSpace.pullbackUnit j.toLRSHom.toShHom M (op ⊤) x := by
  change ((Scheme.Modules.pullback j).obj M).presheaf.map _ _ = _
  rw [show (homOfLE h).op = 𝟙 _ from Subsingleton.elim _ _]
  simp
  rfl

/-- **The structure-sheaf comparison carries the pullback of the unit section to the unit
section.** This is `Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit` at `1`, the structure
morphism of `j` being a ring map. -/
theorem unitRingedIso_hom_app_unitOne
    (h : (⊤ : Y'.Opens) ≤ j ⁻¹ᵁ (⊤ : Y.Opens)) :
    (unitRingedIso j).hom.app ⊤
        (pullbackSectionHom j (unitModule Y) ⊤ ⊤ h (unitOne Y)) = unitOne Y' := by
  refine Eq.trans (congrArg (fun z => (unitRingedIso j).hom.app ⊤ z)
    (pullbackSectionHom_top_eq j (unitModule Y) h (unitOne Y))) ?_
  refine Eq.trans
    (Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit j.toLRSHom.toShHom (op ⊤) 1) ?_
  change Stacks.RingedSpace.sharp j.toLRSHom.toShHom (op ⊤) (1 : Γ(Y, ⊤)) = (1 : Γ(Y', ⊤))
  exact map_one _

/-- **The global section of the comparison is the pullback of the unit section.** This is the
degree zero case of the bridge, and the whole of its content: the structure-sheaf comparison of
Stacks Tag 01CD carries the pullback of `1` to `1`. -/
theorem globalSection_unitPullback :
    globalSection Y' ((Scheme.Modules.pullback j).obj (𝟙_ Y.Modules)) (unitPullback j) =
      pullbackSectionHom j (𝟙_ Y.Modules) ⊤ ⊤ (by simp)
        (globalSection Y (𝟙_ Y.Modules) (𝟙 (𝟙_ Y.Modules))) := by
  have hinj : Function.Injective
      (ConcreteCategory.hom (Scheme.Modules.Hom.app (unitPullbackHom j) ⊤) : _ → _) :=
    (ConcreteCategory.bijective_of_isIso _).1
  refine hinj ?_
  change (unitPullbackHom j).app ⊤ _ = (unitPullbackHom j).app ⊤ _
  rw [← Stacks.SectionProduct.globalSection_comp _ _ (unitPullback j) (unitPullbackHom j),
    unitPullback_comp_unitPullbackHom, unitPullbackHom_eq]
  change globalSection Y' (𝟙_ Y'.Modules) (𝟙 (𝟙_ Y'.Modules)) =
    (unitComparison Y').inv.app ⊤
      ((unitRingedIso j).hom.app ⊤
        (((Scheme.Modules.pullback j).map (unitComparison Y).hom).app ⊤ _))
  rw [← pullbackSectionHom_app j (unitComparison Y).hom ⊤ ⊤ (by simp),
    unitComparison_hom_app_globalSection]
  exact (globalSection_id Y').trans
    (congrArg (fun z => (unitComparison Y').inv.app ⊤ z)
      (unitRingedIso_hom_app_unitOne j _).symm)

/-- **The bridge: the pullback of a global section is the global section of the pullback.** For a
morphism of schemes `j : Y' ⟶ Y`, an `𝒪_Y`-module `M` and a morphism `f : 𝟙_ Y.Modules ⟶ M` out
of the monoidal unit, the pullback along `j` of the global section of `f` — the unit of
`j^* ⊣ j_*` evaluated on sections — is the global section of the morphism `j^*f` out of the
monoidal unit, read there through the structure-sheaf comparison of Stacks Tag 01CD. -/
theorem pullbackSectionHom_globalSection (M : Y.Modules) (f : 𝟙_ Y.Modules ⟶ M) :
    pullbackSectionHom j M ⊤ ⊤ (by simp) (globalSection Y M f) =
      globalSection Y' ((Scheme.Modules.pullback j).obj M)
        (unitPullback j ≫ (Scheme.Modules.pullback j).map f) := by
  rw [Stacks.SectionProduct.globalSection_comp _ _ (unitPullback j)
      ((Scheme.Modules.pullback j).map f),
    globalSection_unitPullback j, globalSection_eq_app M f]
  exact pullbackSectionHom_app j f ⊤ ⊤ (by simp) _

end Stacks.PullbackUnitSection

end
