module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FiberNeighborhoods
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ModuleRestrictionVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SubsetSectionsOfCoeff
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.FlatBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.NativeCohomologyCocones
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
public import StacksFrontier.Topology.Sheaves.Modules.PullbackUnderlyingSheaf

/-!
# Proper base change in topology

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces which is closed and separated, and
let `y` be a point of `Y` whose fibre `f⁻¹(y)` is quasi-compact. This file proves
[Stacks, Tag 09V5]: for every bounded below complex `E` of `𝒪_X`-modules the canonical
base-change morphism

`(Rf_* E)_y ⟶ RΓ(f⁻¹(y), E|_{f⁻¹(y)})`

of [Stacks, Tag 02N7] is an isomorphism in the bounded below derived category of
`𝒪_{Y,y}`-modules, naturally in `E`.

## Main definitions

* `Stacks.Cohomology.ProperBaseChange.constMapSections`: for a morphism `k` of ringed spaces
  whose underlying map is constant with value `y`, global sections on the source as modules over
  `𝒪_{Y,y}`.
* `Stacks.Cohomology.ProperBaseChange.constMapStalkSections`: the comparison from the stalk at
  `y` of a direct image along such a `k` to those global sections.
* `Stacks.Cohomology.ProperBaseChange.fiberSections`: sections on the fibre `f⁻¹(y)` as modules
  over `𝒪_{Y,y}`.
* `Stacks.Cohomology.ProperBaseChange.fiberRestrictionMap`: the underived comparison
  `f_* ⋙ (-)_y ⟶ (-)|_{f⁻¹(y)} ⋙ Γ(f⁻¹(y), -)`.
* `Stacks.Cohomology.ProperBaseChange.properBaseChangeMap`: its descent to bounded below derived
  categories, the base-change morphism of [Stacks, Tag 02N7] for the fibre square.

## Main results

* `Stacks.Cohomology.ProperBaseChange.fiberRestrictionMap_germ`: the underived comparison sends
  the germ at `y` of a section over `f⁻¹(V)` to its restriction to the fibre.
* `Stacks.Cohomology.ProperBaseChange.isIso_fiberRestrictionMap_app`: the underived comparison is
  an isomorphism, which is the degree-zero case.
* `Stacks.Cohomology.ProperBaseChange.fiberSections_rightAcyclic`: sections on the fibre are
  acyclic on the restriction of an injective sheaf of modules.
* `Stacks.Cohomology.ProperBaseChange.isIso_properBaseChangeMap`: the base-change morphism
  `(Rf_* E)_y ⟶ RΓ(f⁻¹(y), E|_{f⁻¹(y)})` is an isomorphism, [Stacks, Tag 09V5].

## References

* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open AlgebraicGeometry RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.ProperBaseChange

universe u

noncomputable section

/-! ### Direct image along a constant map -/

section ConstMap

variable {X Y : RingedSpace.{u, u}} (k : X ⟶ Y) (y : Y) (hy : ∀ z : X, k.hom.base z = y)

/-- The coefficient homomorphism `𝒪_{Y,y} ⟶ Γ(X, 𝒪_X)` of a morphism of ringed spaces whose
underlying map is constant with value `y`: restrict the germ of a section of `𝒪_Y` at `y` along
the structure map. -/
def constMapCoefficients :
    TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier) (structureSheafRing Y).obj y ⟶
      (structureSheafRing X).obj.obj (op ⊤) :=
  Stacks.Topology.stalkToSectionsOfConstant k.hom.base y hy
    (structureSheafRing Y).obj (structureSheafRing X).obj (structureSheafHom k).hom

/-- The coefficient homomorphism on germs: the germ of `r` over `U` goes to the restriction to
`X` of the image of `r` under the structure map. -/
theorem constMapCoefficients_germ (U : Opens Y.carrier) (hU : y ∈ U)
    (r : (structureSheafRing Y).obj.obj (op U)) :
    (ConcreteCategory.hom (constMapCoefficients k y hy))
        ((ConcreteCategory.hom (TopCat.Presheaf.germ (structureSheafRing Y).obj U y hU)) r) =
      (ConcreteCategory.hom ((structureSheafRing X).obj.map
        (Stacks.Topology.topToPreimageOfConstant k.hom.base y hy U hU).op))
          ((ConcreteCategory.hom ((structureSheafHom k).hom.app (op U))) r) :=
  congrArg (fun g => (ConcreteCategory.hom g) r)
    (Stacks.Topology.stalkToSectionsOfConstant_germ k.hom.base y hy
      (structureSheafRing Y).obj (structureSheafRing X).obj (structureSheafHom k).hom U hU)

/-- Global sections on the source of a constant morphism, as modules over the stalk of the
structure sheaf of the target at the value of the map. -/
def constMapSections :
    _root_.SheafOfModules.{u} (structureSheafRing X) ⥤
      ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
        (structureSheafRing Y).obj y) :=
  _root_.SheafOfModules.evaluation (structureSheafRing X) (op ⊤) ⋙
    ModuleCat.restrictScalars (constMapCoefficients k y hy).hom

/-- The underlying additive map of the comparison from the stalk of a direct image along a
constant map to global sections. -/
def constMapStalkUnderlying (N : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((modulePushforward k).obj N).val.presheaf y ⟶
      N.val.presheaf.obj (op ⊤) :=
  Stacks.Topology.stalkToSectionsOfConstant k.hom.base y hy
    ((modulePushforward k).obj N).val.presheaf N.val.presheaf (𝟙 _)

/-- **The comparison on germs.** Composed with the germ map over `U`, the comparison is
restriction from `k⁻¹(U) = X` to `X`, which is the identity on sections. -/
theorem germ_comp_constMapStalkUnderlying (N : _root_.SheafOfModules.{u} (structureSheafRing X))
    (U : Opens Y.carrier) (hU : y ∈ U) :
    TopCat.Presheaf.germ ((modulePushforward k).obj N).val.presheaf U y hU ≫
        constMapStalkUnderlying k y hy N =
      N.val.presheaf.map
        (Stacks.Topology.topToPreimageOfConstant k.hom.base y hy U hU).op :=
  (Stacks.Topology.stalkToSectionsOfConstant_germ k.hom.base y hy
    ((modulePushforward k).obj N).val.presheaf N.val.presheaf (𝟙 _) U hU).trans
      (Category.id_comp _)

/-- The comparison on germs, on elements: the germ at `y` of a section of `k_* N` over `U`, which
is a section of `N` over `k⁻¹(U) = X`, goes to that section. -/
theorem constMapStalkUnderlying_germ (N : _root_.SheafOfModules.{u} (structureSheafRing X))
    (U : Opens Y.carrier) (hU : y ∈ U)
    (s : ((modulePushforward k).obj N).val.obj (op U)) :
    (ConcreteCategory.hom (constMapStalkUnderlying k y hy N))
        ((ConcreteCategory.hom
          (TopCat.Presheaf.germ ((modulePushforward k).obj N).val.presheaf U y hU)) s) =
      (ConcreteCategory.hom (N.val.presheaf.map
        (Stacks.Topology.topToPreimageOfConstant k.hom.base y hy U hU).op)) s :=
  ConcreteCategory.congr_hom (germ_comp_constMapStalkUnderlying k y hy N U hU) s

/-- The comparison is semilinear on germs: a scalar multiple of a section over `U` restricts to
the corresponding multiple over `X`. -/
theorem constMapStalkUnderlying_germ_smul (N : _root_.SheafOfModules.{u} (structureSheafRing X))
    (U : Opens Y.carrier) (hU : y ∈ U) (r : (structureSheafRing Y).obj.obj (op U))
    (s : ((modulePushforward k).obj N).val.obj (op U)) :
    letI : Module (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
        (structureSheafRing Y).obj y) (N.val.presheaf.obj (op ⊤)) :=
      Module.compHom _ (constMapCoefficients k y hy).hom
    (ConcreteCategory.hom (constMapStalkUnderlying k y hy N))
        ((ConcreteCategory.hom
          (TopCat.Presheaf.germ ((modulePushforward k).obj N).val.presheaf U y hU)) (r • s)) =
      (ConcreteCategory.hom (constMapCoefficients k y hy))
          ((ConcreteCategory.hom (TopCat.Presheaf.germ (structureSheafRing Y).obj U y hU)) r) •
        (ConcreteCategory.hom (constMapStalkUnderlying k y hy N))
          ((ConcreteCategory.hom
            (TopCat.Presheaf.germ ((modulePushforward k).obj N).val.presheaf U y hU)) s) := by
  let : Module (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
      (structureSheafRing Y).obj y) (N.val.presheaf.obj (op ⊤)) :=
    Module.compHom _ (constMapCoefficients k y hy).hom
  rw [constMapStalkUnderlying_germ, constMapCoefficients_germ, constMapStalkUnderlying_germ]
  exact PresheafOfModules.map_smul N.val
    (Stacks.Topology.topToPreimageOfConstant k.hom.base y hy U hU).op
    ((ConcreteCategory.hom ((structureSheafHom k).hom.app (op U))) r) s

/-- The comparison is semilinear over the coefficient homomorphism. -/
theorem constMapStalkUnderlying_smul (N : _root_.SheafOfModules.{u} (structureSheafRing X))
    (r : TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier) (structureSheafRing Y).obj y)
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((modulePushforward k).obj N).val.presheaf y) :
    letI : Module (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
        (structureSheafRing Y).obj y) (N.val.presheaf.obj (op ⊤)) :=
      Module.compHom _ (constMapCoefficients k y hy).hom
    (ConcreteCategory.hom (constMapStalkUnderlying k y hy N)) (r • m) =
      (ConcreteCategory.hom (constMapCoefficients k y hy)) r •
        (ConcreteCategory.hom (constMapStalkUnderlying k y hy N)) m := by
  let : Module (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
      (structureSheafRing Y).obj y) (N.val.presheaf.obj (op ⊤)) :=
    Module.compHom _ (constMapCoefficients k y hy).hom
  obtain ⟨U₁, hU₁, r₀, hr⟩ := TopCat.Presheaf.exists_germ_eq (structureSheafRing Y).obj r
  obtain ⟨U₂, hU₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq
    ((modulePushforward k).obj N).val.presheaf m
  have hW : y ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
  have hr0 : (ConcreteCategory.hom (TopCat.Presheaf.germ (structureSheafRing Y).obj (U₁ ⊓ U₂) y hW))
      ((ConcreteCategory.hom
        ((structureSheafRing Y).obj.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op)) r₀) = r :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans hr
  have hm' : (ConcreteCategory.hom
        (TopCat.Presheaf.germ ((modulePushforward k).obj N).val.presheaf (U₁ ⊓ U₂) y hW))
      ((ConcreteCategory.hom (((modulePushforward k).obj N).val.map
        (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op)) m₀) = m :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans hm
  have hsmul := PresheafOfModules.germ_ringCat_smul ((modulePushforward k).obj N).val y
    (U₁ ⊓ U₂) hW
    ((ConcreteCategory.hom
      ((structureSheafRing Y).obj.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op)) r₀)
    ((ConcreteCategory.hom (((modulePushforward k).obj N).val.map
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op)) m₀)
  rw [hr0, hm'] at hsmul
  rw [← hsmul, ← hr0, ← hm']
  exact constMapStalkUnderlying_germ_smul k y hy N (U₁ ⊓ U₂) hW
    ((ConcreteCategory.hom
      ((structureSheafRing Y).obj.map (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)).op)) r₀)
    ((ConcreteCategory.hom (((modulePushforward k).obj N).val.map
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)).op)) m₀)

/-- The comparison from the stalk at `y` of a direct image along a constant map to global
sections, as a map of `𝒪_{Y,y}`-modules. -/
def constMapStalkLinear (N : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) y).obj
        ((modulePushforward k).obj N) ⟶
      (constMapSections k y hy).obj N := by
  letI : Module (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
      (structureSheafRing Y).obj y)
      ((_root_.SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).obj N) :=
    Module.compHom _ (constMapCoefficients k y hy).hom
  exact ModuleCat.ofHom
    { toFun := ConcreteCategory.hom (constMapStalkUnderlying k y hy N)
      map_add' := map_add (ConcreteCategory.hom (constMapStalkUnderlying k y hy N))
      map_smul' := constMapStalkUnderlying_smul k y hy N }

/-- **The comparison from the stalk of a direct image along a constant map to global sections**,
natural in the sheaf of modules. -/
def constMapStalkSections :
    modulePushforward k ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) y ⟶
      constMapSections k y hy where
  app N := constMapStalkLinear k y hy N
  naturality M N g := by
    have hunder : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map
            ((modulePushforward k).map g).val) ≫
        constMapStalkUnderlying k y hy N =
        constMapStalkUnderlying k y hy M ≫
          ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map g.val).app (op ⊤) := by
      refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
      have e1 := TopCat.Presheaf.stalkFunctor_map_germ_assoc U y hU
        ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map
          ((modulePushforward k).map g).val) (constMapStalkUnderlying k y hy N)
      have e2 := germ_comp_constMapStalkUnderlying k y hy N U hU
      have e3 := germ_comp_constMapStalkUnderlying k y hy M U hU
      have e4 := ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map g.val).naturality
        (Stacks.Topology.topToPreimageOfConstant k.hom.base y hy U hU).op
      exact e1.trans
        ((congrArg (fun t => ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map
            ((modulePushforward k).map g).val).app (op U) ≫ t) e2).trans
          (e4.symm.trans
            ((congrArg (fun t => t ≫
                ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map g.val).app (op ⊤))
              e3).symm.trans (Category.assoc _ _ _))))
    exact ModuleCat.hom_ext (LinearMap.ext fun m => ConcreteCategory.congr_hom hunder m)

end ConstMap



/-! ### The fibre of a morphism at a point -/

section Fiber

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (y : Y)

/-- The composite `f⁻¹(y) ⟶ X ⟶ Y` is constant with value `y`. -/
theorem fiberMap_const :
    ∀ z : (Stacks.Topology.fiberRingedSpace f y).carrier,
      (ConcreteCategory.hom (Stacks.Topology.fiberι f y ≫ f).hom.base) z = y :=
  fun z => z.property

/-- The coefficient homomorphism `𝒪_{Y,y} ⟶ Γ(f⁻¹(y), 𝒪_{f⁻¹(y)})`: restrict a germ at `y` to
the fibre. -/
abbrev fiberCoefficients :
    TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier) (structureSheafRing Y).obj y ⟶
      (structureSheafRing (Stacks.Topology.fiberRingedSpace f y)).obj.obj (op ⊤) :=
  constMapCoefficients (Stacks.Topology.fiberι f y ≫ f) y (fiberMap_const f y)

/-- **Sections on the fibre `f⁻¹(y)`, as modules over `𝒪_{Y,y}`.** -/
abbrev fiberSections :
    _root_.SheafOfModules.{u} (structureSheafRing (Stacks.Topology.fiberRingedSpace f y)) ⥤
      ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
        (structureSheafRing Y).obj y) :=
  constMapSections (Stacks.Topology.fiberι f y ≫ f) y (fiberMap_const f y)

/-- Restriction of a direct image to the fibre: the unit of the restriction/direct-image
adjunction for the fibre, followed by the identification of the two composite direct images of
[Stacks, Tag 0097]. -/
def fiberRestrictionModuleMap :
    modulePushforward f ⟶ modulePullback (Stacks.Topology.fiberι f y) ⋙
      modulePushforward (Stacks.Topology.fiberι f y ≫ f) :=
  (Functor.leftUnitor (modulePushforward f)).inv ≫
    Functor.whiskerRight
      (modulePullbackPushforwardAdjunction (Stacks.Topology.fiberι f y)).unit
      (modulePushforward f) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (modulePullback (Stacks.Topology.fiberι f y))
      (RingedSpaceModuleAdjunction.modulePushforwardComp
        (Stacks.Topology.fiberι f y) f).hom

/-- **The comparison from the stalk of a direct image at `y` to sections on the fibre.** -/
def fiberRestrictionMap :
    modulePushforward f ⋙ AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) y ⟶
      modulePullback (Stacks.Topology.fiberι f y) ⋙ fiberSections f y :=
  Functor.whiskerRight (fiberRestrictionModuleMap f y)
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) y) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (modulePullback (Stacks.Topology.fiberι f y))
      (constMapStalkSections (Stacks.Topology.fiberι f y ≫ f) y (fiberMap_const f y))

/-- Restriction to the fibre of a section over the inverse image of a neighbourhood of `y`. -/
def fiberSectionRestriction (M : _root_.SheafOfModules.{u} (structureSheafRing X))
    (V : Opens Y.carrier) (hV : y ∈ V) :
    M.val.presheaf.obj (op ((opensMap f).obj V)) ⟶
      ((modulePullback (Stacks.Topology.fiberι f y)).obj M).val.presheaf.obj (op ⊤) :=
  ((PresheafOfModules.toPresheaf (structureSheafRing X).obj).map
      ((modulePullbackPushforwardAdjunction (Stacks.Topology.fiberι f y)).unit.app M).val).app
      (op ((opensMap f).obj V)) ≫
    ((modulePullback (Stacks.Topology.fiberι f y)).obj M).val.presheaf.map
      (Stacks.Topology.topToPreimageOfConstant (Stacks.Topology.fiberι f y ≫ f).hom.base y
        (fiberMap_const f y) V hV).op

/-- The underlying additive map of the comparison, composed with the germ map over `V`, is
restriction of sections to the fibre. -/
theorem germ_comp_fiberRestrictionUnderlying (M : _root_.SheafOfModules.{u} (structureSheafRing X))
    (V : Opens Y.carrier) (hV : y ∈ V) :
    TopCat.Presheaf.germ ((modulePushforward f).obj M).val.presheaf V y hV ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map
            ((fiberRestrictionModuleMap f y).app M).val) ≫
          constMapStalkUnderlying (Stacks.Topology.fiberι f y ≫ f) y (fiberMap_const f y)
            ((modulePullback (Stacks.Topology.fiberι f y)).obj M)) =
      fiberSectionRestriction f y M V hV := by
  have e1 := TopCat.Presheaf.stalkFunctor_map_germ_assoc V y hV
    ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map
      ((fiberRestrictionModuleMap f y).app M).val)
    (constMapStalkUnderlying (Stacks.Topology.fiberι f y ≫ f) y (fiberMap_const f y)
      ((modulePullback (Stacks.Topology.fiberι f y)).obj M))
  have e2 := germ_comp_constMapStalkUnderlying (Stacks.Topology.fiberι f y ≫ f) y
    (fiberMap_const f y) ((modulePullback (Stacks.Topology.fiberι f y)).obj M) V hV
  exact e1.trans (congrArg (fun t =>
    ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map
      ((fiberRestrictionModuleMap f y).app M).val).app (op V) ≫ t) e2)

/-- **The comparison is restriction of sections.** It sends the germ at `y` of a section of `M`
over `f⁻¹(V)` to the restriction of that section to the fibre `f⁻¹(y)`. -/
theorem fiberRestrictionMap_germ (M : _root_.SheafOfModules.{u} (structureSheafRing X))
    (V : Opens Y.carrier) (hV : y ∈ V)
    (s : ((modulePushforward f).obj M).val.obj (op V)) :
    (ConcreteCategory.hom ((fiberRestrictionMap f y).app M))
        ((ConcreteCategory.hom
          (TopCat.Presheaf.germ ((modulePushforward f).obj M).val.presheaf V y hV)) s) =
      (ConcreteCategory.hom (fiberSectionRestriction f y M V hV)) s :=
  ConcreteCategory.congr_hom (germ_comp_fiberRestrictionUnderlying f y M V hV) s


/-- **Restriction to the fibre, read through the topological inverse image.** The canonical
restriction of a section of the underlying abelian sheaf to the fibre, followed by the comparison
of the topological and module inverse images, is restriction of sections of the module. -/
theorem ambientSection_comp_pullbackUnderlyingSheafMap
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) (V : Opens Y.carrier) (hV : y ∈ V) :
    Stacks.Topology.ambientSection (Stacks.Topology.fiberι f y).hom.base
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj M)
          (Stacks.Topology.topToPreimageOfConstant (Stacks.Topology.fiberι f y ≫ f).hom.base y
            (fiberMap_const f y) V hV).le ≫
        (Stacks.RingedSpace.pullbackUnderlyingSheafMap
          (Stacks.Topology.fiberι f y) M).hom.app (op ⊤) =
      fiberSectionRestriction f y M V hV := by
  have hfac := congrArg (fun t => CategoryTheory.InducedCategory.Hom.hom t)
    (Stacks.RingedSpace.pullbackUnderlyingSheafMap_fac (Stacks.Topology.fiberι f y) M)
  have hfacapp := congrArg
    (fun t => NatTrans.app t (op ((opensMap f).obj V))) hfac
  have hnat := (Stacks.RingedSpace.pullbackUnderlyingSheafMap
      (Stacks.Topology.fiberι f y) M).hom.naturality
    (Stacks.Topology.topToPreimageOfConstant (Stacks.Topology.fiberι f y ≫ f).hom.base y
      (fiberMap_const f y) V hV).op
  refine Eq.trans (congrArg (fun z => z ≫ (Stacks.RingedSpace.pullbackUnderlyingSheafMap
      (Stacks.Topology.fiberι f y) M).hom.app (op ⊤))
    (Stacks.Topology.ambientSection_eq (Stacks.Topology.fiberι f y).hom.base
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj M) _)) ?_
  refine Eq.trans (Stacks.Topology.assoc_congr _ _ _ _ _ hnat) ?_
  exact congrArg (fun z => z ≫ ((modulePullback (Stacks.Topology.fiberι f y)).obj
    M).val.presheaf.map (Stacks.Topology.topToPreimageOfConstant
      (Stacks.Topology.fiberι f y ≫ f).hom.base y (fiberMap_const f y) V hV).op) hfacapp


/-- The comparison of the topological and module inverse images along the fibre inclusion is an
isomorphism. -/
private theorem isIso_pullbackUnderlyingSheafMap_fiberι
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    IsIso (Stacks.RingedSpace.pullbackUnderlyingSheafMap (Stacks.Topology.fiberι f y) M) :=
  Stacks.RingedSpace.isIso_pullbackUnderlyingSheafMap _ _ (fun x =>
    RingedSpace.isIso_stalkMap_inverseImageProjection X _ x)

/-- **The comparison is an isomorphism in degree zero.** For a closed separated morphism with
quasi-compact fibre over `y`, the stalk at `y` of `f_* M` is the module of sections of `M` on the
fibre. -/
theorem isIso_fiberRestrictionMap_app
    (hclosed : IsClosedMap (ConcreteCategory.hom f.hom.base))
    (hsep : IsSeparatedMap (ConcreteCategory.hom f.hom.base))
    (hcompact : IsCompact ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y)))
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    IsIso ((fiberRestrictionMap f y).app M) := by
  have hfinal : (Stacks.Topology.preimageNeighborhoodFunctor f.hom.base y).Final :=
    Stacks.Topology.preimageNeighborhoodFunctor_final f.hom.base y hclosed
  have hphi := isIso_pullbackUnderlyingSheafMap_fiberι f y M
  have hphihom : IsIso (Stacks.RingedSpace.pullbackUnderlyingSheafMap
      (Stacks.Topology.fiberι f y) M).hom := by
    refine ⟨⟨(inv (Stacks.RingedSpace.pullbackUnderlyingSheafMap
      (Stacks.Topology.fiberι f y) M)).hom, ?_, ?_⟩⟩
    · exact congrArg (fun t => CategoryTheory.InducedCategory.Hom.hom t)
        (IsIso.hom_inv_id (Stacks.RingedSpace.pullbackUnderlyingSheafMap
          (Stacks.Topology.fiberι f y) M))
    · exact congrArg (fun t => CategoryTheory.InducedCategory.Hom.hom t)
        (IsIso.inv_hom_id (Stacks.RingedSpace.pullbackUnderlyingSheafMap
          (Stacks.Topology.fiberι f y) M))
  have hphiapp : IsIso ((Stacks.RingedSpace.pullbackUnderlyingSheafMap
      (Stacks.Topology.fiberι f y) M).hom.app (op ⊤)) :=
    NatIso.isIso_app_of_isIso _ _
  have hsec : IsIso (Stacks.Topology.subsetSectionsMap
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj M)
      ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y))) :=
    Stacks.Topology.isIso_subsetSectionsMap _ _ hcompact
      (Stacks.Topology.fiberPairwiseSeparated f y hsep)
  let r : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((modulePushforward f).obj M).val.presheaf y ⟶
      ((modulePullback (Stacks.Topology.fiberι f y)).obj M).val.presheaf.obj (op ⊤) :=
    colimit.pre (Stacks.Topology.neighborhoodSections
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj M)
        ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y)))
        (Stacks.Topology.preimageNeighborhoodFunctor f.hom.base y) ≫
      Stacks.Topology.subsetSectionsMap
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj M)
        ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y)) ≫
      (Stacks.RingedSpace.pullbackUnderlyingSheafMap
        (Stacks.Topology.fiberι f y) M).hom.app (op ⊤)
  have h1 : IsIso (colimit.pre (Stacks.Topology.neighborhoodSections
      ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj M)
      ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y)))
      (Stacks.Topology.preimageNeighborhoodFunctor f.hom.base y)) := inferInstance
  have hr : IsIso r := IsIso.comp_isIso' h1 (IsIso.comp_isIso' hsec hphiapp)
  have hunder : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map
          ((fiberRestrictionModuleMap f y).app M).val) ≫
      constMapStalkUnderlying (Stacks.Topology.fiberι f y ≫ f) y (fiberMap_const f y)
        ((modulePullback (Stacks.Topology.fiberι f y)).obj M) = r := by
    refine TopCat.Presheaf.stalk_hom_ext _ fun V hV => ?_
    refine (germ_comp_fiberRestrictionUnderlying f y M V hV).trans ?_
    refine (ambientSection_comp_pullbackUnderlyingSheafMap f y M V hV).symm.trans ?_
    refine Eq.trans ?_ (Stacks.Topology.reassoc_four _ _ _ _).symm
    refine congrArg (fun z => z ≫ (Stacks.RingedSpace.pullbackUnderlyingSheafMap
      (Stacks.Topology.fiberι f y) M).hom.app (op ⊤)) ?_
    refine Eq.trans ?_ (congrArg (fun z => z ≫ Stacks.Topology.subsetSectionsMap
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj M)
        ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y)))
      (colimit.ι_pre _ (Stacks.Topology.preimageNeighborhoodFunctor f.hom.base y)
        (op (⟨V, hV⟩ : OpenNhds y)))).symm
    have hdesc : colimit.ι (Stacks.Topology.neighborhoodSections
            ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj M)
            ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y)))
            ((Stacks.Topology.preimageNeighborhoodFunctor f.hom.base y).obj
              (op (⟨V, hV⟩ : OpenNhds y))) ≫
          Stacks.Topology.subsetSectionsMap
            ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj M)
            ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y)) =
        Stacks.Topology.ambientSection (Stacks.Topology.fiberι f y).hom.base
          ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj M)
          (Stacks.Topology.topToPreimageOfConstant (Stacks.Topology.fiberι f y ≫ f).hom.base y
            (fiberMap_const f y) V hV).le := colimit.ι_desc _ _
    exact hdesc.symm
  have hre : ∀ m, (ConcreteCategory.hom ((fiberRestrictionMap f y).app M)) m =
      (ConcreteCategory.hom r) m := fun m => ConcreteCategory.congr_hom hunder m
  have hb := ConcreteCategory.bijective_of_isIso r
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab => ?_, fun c => ?_⟩
  · exact hb.1 ((hre a).symm.trans (hab.trans (hre b)))
  · obtain ⟨m, hm⟩ := hb.2 c
    exact ⟨m, (hre m).trans hm⟩

end Fiber



/-! ### Exactness of sections on the source of a constant map -/

section Exactness

variable {X Y : RingedSpace.{u, u}} (k : X ⟶ Y) (y : Y) (hy : ∀ z : X, k.hom.base z = y)

/-- Restriction of scalars along a ring homomorphism is exact: a short complex of modules is
exact if and only if the underlying sequence of maps is. -/
theorem exact_restrictScalars {R S : Type u} [Ring R] [Ring S] (φ : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} φ) ∧
      PreservesFiniteColimits (ModuleCat.restrictScalars.{u} φ) :=
  ((Functor.exact_tfae (ModuleCat.restrictScalars.{u} φ)).out 2 4).mp fun K hK => by
    rwa [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hK ⊢

/-- The global sections functor `constMapSections k y hy` is additive. -/
instance constMapSections_additive : (constMapSections k y hy).Additive := by
  dsimp only [constMapSections]
  infer_instance

/-- The global sections functor `constMapSections k y hy` preserves finite limits. -/
instance preservesFiniteLimits_constMapSections :
    PreservesFiniteLimits (constMapSections k y hy) := by
  have := (exact_restrictScalars (constMapCoefficients k y hy).hom).1
  dsimp only [constMapSections]
  infer_instance

end Exactness

/-! ### The comparison on bounded below derived categories -/

section Derived

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (y : Y)

/-- **Taking stalks at `y` is computed degreewise on bounded below derived categories.** The
stalk functor on sheaves of modules is exact, so its derived-functor unit is invertible. -/
def stalkPlusComparison :
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
        y).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙
        (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
            y).rightDerivedFunctorPlus :=
  have := Stacks.Cohomology.FlatBaseChange.enoughInjectives_ringSheaf Y
  have : PreservesFiniteColimits
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) y) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have := Stacks.Cohomology.BaseChange.exactUnit_isIso
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) y)
  asIso (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
    y).rightDerivedFunctorPlusUnith

/-- **Restriction to the fibre is computed degreewise on bounded below derived categories.**
Module pullback along the inclusion of a subspace with the restricted structure sheaf is exact,
so its derived-functor unit is invertible. -/
def fiberPullbackPlusComparison :
    (modulePullback (Stacks.Topology.fiberι f y)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙
        (modulePullback (Stacks.Topology.fiberι f y)).rightDerivedFunctorPlus :=
  have := Stacks.Cohomology.FlatBaseChange.enoughInjectives_ringSheaf X
  have := RingedSpaceModuleAdjunction.preservesFiniteLimits_inverseImageModulePullback X
    (Stacks.subsetInclusion X.carrier ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y)))
  have := preservesFiniteColimits_modulePullback (Stacks.Topology.fiberι f y)
  have := Stacks.Cohomology.BaseChange.exactUnit_isIso
    (modulePullback (Stacks.Topology.fiberι f y))
  asIso (modulePullback (Stacks.Topology.fiberι f y)).rightDerivedFunctorPlusUnith

/-- **The base-change morphism of [Stacks, Tag 02N7] for the fibre square**: the descent of
`fiberRestrictionMap` to bounded below derived categories: the unique morphism whose composite
with the derived-functor unit of `Rf_*` is the degreewise comparison
(`Stacks.Cohomology.BaseChange.derived_fac`). -/
def properBaseChangeMap :
    (modulePushforward f).rightDerivedFunctorPlus ⋙
        (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y)
            y).rightDerivedFunctorPlus ⟶
      (modulePullback (Stacks.Topology.fiberι f y)).rightDerivedFunctorPlus ⋙
        (fiberSections f y).rightDerivedFunctorPlus :=
  have := Stacks.Cohomology.FlatBaseChange.enoughInjectives_ringSheaf X
  have := Stacks.Cohomology.FlatBaseChange.enoughInjectives_ringSheaf Y
  have := Stacks.Cohomology.FlatBaseChange.enoughInjectives_ringSheaf
    (Stacks.Topology.fiberRingedSpace f y)
  Stacks.Cohomology.BaseChange.derived (modulePushforward f) (fiberSections f y)
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) y)
    (modulePullback (Stacks.Topology.fiberι f y))
    (fiberRestrictionMap f y) (stalkPlusComparison (Y := Y) y)

end Derived


/-! ### Invertibility of a descended base-change morphism -/

section Criterion

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- A transformation which is invertible on every term of a bounded below complex is invertible
after applying it degreewise on the bounded below homotopy category. -/
theorem isIso_mapPlus_app_of_components
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E H : A ⥤ B) [E.Additive] [H.Additive] (τ : E ⟶ H)
    {K : HomotopyCategory.Plus A}
    (hτ : ∀ n : ℤ, IsIso (τ.app (K.obj.as.X n))) :
    IsIso ((Stacks.Cohomology.BaseChange.mapPlus τ).app K) := by
  have : ∀ n : ℤ, IsIso (((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app
      K.obj.as).f n) := hτ
  have hcomplex : IsIso ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app K.obj.as) :=
    HomologicalComplex.Hom.isIso_of_components _
  have hhom : IsIso ((τ.mapHomotopyCategory (ComplexShape.up ℤ)).app K.obj) := by
    show IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app K.obj.as))
    infer_instance
  have : IsIso ((HomotopyCategory.Plus.ι B).map
    ((Stacks.Cohomology.BaseChange.mapPlus τ).app K)) := hhom
  exact isIso_of_reflects_iso _ (HomotopyCategory.Plus.ι B)

/-- **A descended base-change morphism is invertible when the underived comparison is invertible
at every injective object and the lower-right functor is acyclic on the images of injectives.** -/
theorem isIso_baseChangeDerived
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
    (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
    (τ : F ⋙ G ⟶ G' ⋙ F') (hτ : ∀ M : A, Injective M → IsIso (τ.app M))
    (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)
    [IsIso G'.rightDerivedFunctorPlusUnith]
    (hacyclic : ∀ M : A, Injective M → F'.rightAcyclic (G'.obj M)) :
    IsIso (Stacks.Cohomology.BaseChange.derived F F' G G' τ e) := by
  have hK (K : HomotopyCategory.Plus A) (hinj : ∀ n, Injective (K.obj.as.X n)) :
      IsIso ((Stacks.Cohomology.BaseChange.onHomotopy F F' G G' τ e).app K) := by
    have : IsIso ((Stacks.Cohomology.BaseChange.mapPlus τ).app K) :=
      isIso_mapPlus_app_of_components _ _ τ (fun n => hτ _ (hinj n))
    have htot : IsIso (((F'.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app
          (G'.mapHomotopyCategoryPlus.obj K)) :=
      Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic F'
        (G'.mapHomotopyCategoryPlus.obj K).obj.as
        ((HomotopyCategory.plus_quotient_obj_iff _).1
          (G'.mapHomotopyCategoryPlus.obj K).property)
        (fun n => hacyclic (K.obj.as.X n) (hinj n))
    have : IsIso (F'.rightDerivedFunctorPlusUnith.app
        (G'.mapHomotopyCategoryPlus.obj K)) := by
      rw [← Functor.rightDerived_fac_app _
        ((F'.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
          DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C))
        (HomotopyCategory.Plus.quasiIso C) F'.rightDerivedFunctorPlus
        F'.rightDerivedFunctorPlusUnith]
      have : IsIso (Functor.rightDerivedDesc _
          ((F'.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
            DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C))
          (HomotopyCategory.Plus.quasiIso C) F'.rightDerivedFunctorPlus
            F'.rightDerivedFunctorPlusUnith) :=
        (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 inferInstance
      infer_instance
    dsimp only [Stacks.Cohomology.BaseChange.onHomotopy, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  unfold Stacks.Cohomology.BaseChange.derived
  rw [← Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc,
    (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_iff_isIso]
  exact fun K => hK _ (fun _ => inferInstance)

end Criterion

/-! ### Acyclicity of sections on the fibre, and the theorem -/

section Acyclicity

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- For an exact additive functor `G`, the right derived functors of `F ⋙ G` are `G` applied to
those of `F`. -/
def rightDerivedCompObjIso {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C] [HasInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive] [G.PreservesHomology] (M : A) (p : ℕ) :
    G.obj ((F.rightDerived p).obj M) ≅ ((F ⋙ G).rightDerived p).obj M := by
  unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
    HomotopyCategory.homologyFunctor
  exact ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((injectiveResolutions A).obj M).as).sc p).mapHomologyIso G).symm

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (y : Y)

/-- **Sections on the fibre are acyclic on the restriction of an injective sheaf of modules.**
For a separated morphism with quasi-compact fibre over `y`, the higher right derived functors of
`fiberSections f y` vanish on the restriction to the fibre of an injective sheaf of modules. -/
theorem fiberSections_rightAcyclic
    (hsep : IsSeparatedMap (ConcreteCategory.hom f.hom.base))
    (hcompact : IsCompact ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y)))
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) [Injective M] :
    (fiberSections f y).rightAcyclic
      ((modulePullback (Stacks.Topology.fiberι f y)).obj M) := by
  have hinj := Stacks.Cohomology.FlatBaseChange.enoughInjectives_ringSheaf
    (Stacks.Topology.fiberRingedSpace f y)
  have hT1 := (exact_restrictScalars (fiberCoefficients f y).hom).1
  have hT2 := (exact_restrictScalars (fiberCoefficients f y).hom).2
  have hTh : (ModuleCat.restrictScalars (fiberCoefficients f y).hom).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived]
  intro p hp
  have hvanish := Stacks.Topology.isZero_cohomologyPresheaf_pullback_toSheaf_of_injective
    (structureSheafRing X) M hcompact (Stacks.Topology.fiberPairwiseSeparated f y hsep) p hp
  have hphi := isIso_pullbackUnderlyingSheafMap_fiberι f y M
  have hsec0 : IsZero (((Stacks.Cohomology.SpectralLimit.sections
        (Stacks.Topology.fiberRingedSpace f y).carrier ⊤).rightDerived p).obj
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
        (Stacks.subsetInclusion X.carrier
          ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y)))).obj
        ((_root_.SheafOfModules.toSheaf (structureSheafRing X)).obj M))) :=
    hvanish.of_iso (Stacks.Cohomology.SpectralLimit.cohomologyIsoRightDerivedSections _ p ⊤).symm
  have hsec : IsZero (((Stacks.Cohomology.SpectralLimit.sections
        (Stacks.Topology.fiberRingedSpace f y).carrier ⊤).rightDerived p).obj
      ((_root_.SheafOfModules.toSheaf
          (structureSheafRing (Stacks.Topology.fiberRingedSpace f y))).obj
        ((modulePullback (Stacks.Topology.fiberι f y)).obj M))) :=
    hsec0.of_iso (((Stacks.Cohomology.SpectralLimit.sections
      (Stacks.Topology.fiberRingedSpace f y).carrier ⊤).rightDerived p).mapIso
        (asIso (Stacks.RingedSpace.pullbackUnderlyingSheafMap
          (Stacks.Topology.fiberι f y) M))).symm
  have hGN : IsZero ((forget₂ (ModuleCat.{u}
        ((structureSheafRing (Stacks.Topology.fiberRingedSpace f y)).obj.obj (op ⊤)))
        AddCommGrpCat.{u}).obj
      (((_root_.SheafOfModules.evaluation
          (structureSheafRing (Stacks.Topology.fiberRingedSpace f y)) (op ⊤)).rightDerived p).obj
        ((modulePullback (Stacks.Topology.fiberι f y)).obj M))) := by
    refine hsec.of_iso ?_
    exact (Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso
      (structureSheafRing (Stacks.Topology.fiberRingedSpace f y)) ⊤ p).app
        ((modulePullback (Stacks.Topology.fiberι f y)).obj M)
  have hN : IsZero ((((_root_.SheafOfModules.evaluation
      (structureSheafRing (Stacks.Topology.fiberRingedSpace f y)) (op ⊤))).rightDerived p).obj
      ((modulePullback (Stacks.Topology.fiberι f y)).obj M)) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    refine (forget₂ (ModuleCat.{u} ((structureSheafRing
      (Stacks.Topology.fiberRingedSpace f y)).obj.obj (op ⊤))) AddCommGrpCat.{u}).map_injective ?_
    exact hGN.eq_of_src _ _
  exact ((ModuleCat.restrictScalars (fiberCoefficients f y).hom).map_isZero hN).of_iso
    (rightDerivedCompObjIso _ _ _ p).symm

/-- **Proper base change in topology.** For a closed separated morphism of ringed
spaces `f : X ⟶ Y` and a point `y` of `Y` with quasi-compact fibre, the canonical base-change
morphism from the stalk at `y` of the derived direct image to the derived sections on the fibre
is an isomorphism: for every bounded below complex `E` of `𝒪_X`-modules,

`(Rf_* E)_y = RΓ(f⁻¹(y), E|_{f⁻¹(y)})`

in the bounded below derived category of `𝒪_{Y,y}`-modules, naturally in `E`. -/
@[stacks 09V5]
theorem isIso_properBaseChangeMap
    (hclosed : IsClosedMap (ConcreteCategory.hom f.hom.base))
    (hsep : IsSeparatedMap (ConcreteCategory.hom f.hom.base))
    (hcompact : IsCompact ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y))) :
    IsIso (properBaseChangeMap f y) := by
  have h1 := Stacks.Cohomology.FlatBaseChange.enoughInjectives_ringSheaf X
  have h2 := Stacks.Cohomology.FlatBaseChange.enoughInjectives_ringSheaf Y
  have h3 := Stacks.Cohomology.FlatBaseChange.enoughInjectives_ringSheaf
    (Stacks.Topology.fiberRingedSpace f y)
  have he := RingedSpaceModuleAdjunction.preservesFiniteLimits_inverseImageModulePullback X
    (Stacks.subsetInclusion X.carrier ((ConcreteCategory.hom f.hom.base) ⁻¹' ({y} : Set Y)))
  have he' := preservesFiniteColimits_modulePullback (Stacks.Topology.fiberι f y)
  have hunit :
      IsIso (modulePullback (Stacks.Topology.fiberι f y)).rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso
      (modulePullback (Stacks.Topology.fiberι f y))
  exact isIso_baseChangeDerived (modulePushforward f) (fiberSections f y)
    (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Y) y)
    (modulePullback (Stacks.Topology.fiberι f y))
    (fiberRestrictionMap f y)
    (fun M _ => isIso_fiberRestrictionMap_app f y hclosed hsep hcompact M)
    (stalkPlusComparison (Y := Y) y)
    (fun M _ => fiberSections_rightAcyclic f y hsep hcompact M)

end Acyclicity


end

end Stacks.Cohomology.ProperBaseChange

end
