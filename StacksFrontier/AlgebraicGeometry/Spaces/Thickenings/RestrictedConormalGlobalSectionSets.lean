module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationTensorExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSectionSets
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ConormalInverseImageGlobalSectionSets
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRestrictionModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedFirstOrderExtension
public import StacksFrontier.Deformation.ToposThickening.AlgebraExtensionBaseProblem

/-!
# Global sections of sheaves of sets along an étale restriction

For an étale morphism `a : U ⟶ X` of algebraic spaces, the inverse image of modules `a^*` is étale
restriction (Stacks 03LW, `AlgebraicGeometry.Space.modulePullbackIsoEtaleRestrictionModule`).
This file records how that identification acts on global sections, on underlying sheaves of sets:
the pulled-back section `a^*w` of an `𝒪_X`-module, read in the étale restriction, is the image of
`w` along `a⁻¹` followed by the comparison `a⁻¹ ≅ (restriction)` of Stacks 03LQ. Applied to the
conormal module of a first-order thickening `Z ⊆ X` and `ρ : U ≅ Z`, it reads the kernel inclusion
of the restricted extension `0 → 𝒞_{Z/X}|_U → (ι⁻¹𝒪_X)|_U → 𝒪_U → 0` on the class `ρ^*ι^*s` of a
global section `s` of the ideal of `Z`.

## Main results

* The pulled-back global section `a^*w`, read in the étale restriction, on underlying sheaves of
  sets, and the same followed by the restriction of a morphism out of the underlying sheaf of
  sets.
* `AlgebraicGeometry.Space.ringOneHom_comp_map_comp_firstOrderAlgebraExtension_inclSheafSets`:
  the kernel inclusion of the extension of a first-order thickening is `𝒞_{Z/X} ⟶ ι⁻¹𝒪_X`.

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace Stacks.SheafOfModules

variable {C D : Type*} [Category C] [Category D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  {R' : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})] in
/-- Along an equality of ring maps `φ = ψ`, the comparison of the two pushforwards of modules is
the identity on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_eqToHom_pushforward_app
    {φ ψ : R' ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (h : φ = ψ)
    (p : _root_.SheafOfModules.pushforward.{u} φ = _root_.SheafOfModules.pushforward.{u} ψ)
    (N : _root_.SheafOfModules.{u} R) :
    (Sheaf.moduleSheafFunctor R').map ((eqToHom p).app N) =
      𝟙 ((Sheaf.moduleSheafFunctor R').obj ((_root_.SheafOfModules.pushforward.{u} φ).obj N)) := by
  subst h
  simp

end Stacks.SheafOfModules

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [HasTerminal C] [HasTerminal D]

/-- A chase through the image of global sections along `Φ` and a natural transformation
`e : Φ ⟶ Ψ`: if `r ≫ m` is `Φ(x₁ ≫ x₂)` read through `e` and `x₁ ≫ x₂ ≫ i = y`, then
`r ≫ m ≫ Ψ(i)` is `Φ(y)` read through `e`. -/
theorem comp_comp_map_eq_globalSectionMap_comp_app (Φ : C ⥤ D) [IsIso (terminalComparison Φ)]
    {Ψ : C ⥤ D} (e : Φ ⟶ Ψ) {P : D} {L N A : C} {r : ⊤_ D ⟶ P} {m : P ⟶ Ψ.obj N}
    {x₁ : ⊤_ C ⟶ L} {x₂ : L ⟶ N} {i : N ⟶ A} {y : ⊤_ C ⟶ A}
    (h₁ : r ≫ m = Φ.globalSectionMap (x₁ ≫ x₂) ≫ e.app N) (h₃ : x₁ ≫ x₂ ≫ i = y) :
    r ≫ m ≫ Ψ.map i = Φ.globalSectionMap y ≫ e.app A := by
  rw [← Category.assoc, h₁, Category.assoc, ← e.naturality, ← Category.assoc,
    globalSectionMap_comp, Category.assoc, h₃]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules Stacks.SheafOfModules.ChangeOfRings
  Stacks.Sheaves.FinitePresentation Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The unit of extension of scalars followed by Stacks 03LW is the comparison of Stacks 03LQ**,
on underlying sheaves of sets. -/
theorem moduleSheafFunctor_map_extendScalarsFSharpAdjunction_unit_comp_modulePullbackIsoEtaleModulePullback
    {U X : AlgebraicSpaces B S hS} (a : U ⟶ X) (ha : IsEtale B S hS a.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) :
    (moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposModulesHom B S hS a).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))).map
        ((extendScalarsFSharpAdjunction B S hS a).unit.app
          ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS a).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O)).obj
            N)) ≫
      (moduleSheafFunctor (structureRingSheaf B S hS U)).map
        ((modulePullbackIsoEtaleModulePullback B S hS a ha).hom.app N) =
      (smallToposMorphismTypeU_inverseImageIso B S hS a ha).hom.app
        ((moduleSheafFunctor (structureRingSheaf B S hS X)).obj N) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ?_))
  ext m
  exact modulePullbackIsoEtaleModulePullback_unit_app B S hS a ha N V m

/-- **The identification of Stacks 03LW with étale restriction is that with étale pullback**, on
underlying sheaves of sets: the two differ by the comparison of two pushforwards along equal ring
maps. -/
theorem moduleSheafFunctor_map_modulePullbackIsoEtaleRestrictionModule_hom_app
    {U X : AlgebraicSpaces B S hS} (a : U ⟶ X) (ha : IsEtale B S hS a.hom)
    (N : Modules.{u, u} B S hS X.1 X.2) :
    (moduleSheafFunctor (structureRingSheaf B S hS U)).map
        ((modulePullbackIsoEtaleRestrictionModule B S hS a ha).hom.app N) =
      (moduleSheafFunctor (structureRingSheaf B S hS U)).map
        ((modulePullbackIsoEtaleModulePullback B S hS a ha).hom.app N) := by
  have he := Stacks.SheafOfModules.moduleSheafFunctor_map_eqToHom_pushforward_app
    (J := SmallEtale.topology B S hS U.1) (K := SmallEtale.topology B S hS X.1)
    (F := smallEtalePostcomp B S hS a ha)
    (R := (sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)
    (forget₂_map_etaleRestrictionStructureSheafIso_inv B S hS a ha).symm
    (etaleRestrictionModule_eq_etaleModulePullback B S hS a ha).symm N
  exact (Functor.map_comp _ _ _).trans ((congrArg (_ ≫ ·) he).trans (Category.comp_id _))

/-- **A pulled-back global section, read in the étale restriction**: for `a : U ⟶ X` étale and a
global section `w` of an `𝒪_X`-module `N`, the unit section followed by `a^*w` and
`a^*N ≅ N|_U` (Stacks 03LW) is the image of `w` along `a⁻¹` followed by the comparison
`a⁻¹ ≅ (restriction)` of Stacks 03LQ, on underlying sheaves of sets. -/
theorem ringOneHom_comp_map_modulePullbackGlobalSection_comp_modulePullbackIsoEtaleRestrictionModule_hom_app
    {U X : AlgebraicSpaces B S hS} (a : U ⟶ X) (ha : IsEtale B S hS a.hom)
    {N : Modules.{u, u} B S hS X.1 X.2}
    (w : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ N) :
    ringOneHom (structureRingSheaf B S hS U) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS U)).map
          (modulePullbackGlobalSection B S hS a w ≫
            (modulePullbackIsoEtaleRestrictionModule B S hS a ha).hom.app N) =
      (smallEtaleRingedToposModulesHom B S hS a).toToposHom.inverseImage.globalSectionMap
          (ringOneHom (structureRingSheaf B S hS X) ≫
            (moduleSheafFunctor (structureRingSheaf B S hS X)).map w) ≫
        (smallToposMorphismTypeU_inverseImageIso B S hS a ha).hom.app
          ((moduleSheafFunctor (structureRingSheaf B S hS X)).obj N) := by
  refine (congrArg (ringOneHom (structureRingSheaf B S hS U) ≫ ·)
    ((moduleSheafFunctor (structureRingSheaf B S hS U)).map_comp
      (modulePullbackGlobalSection B S hS a w)
      ((modulePullbackIsoEtaleRestrictionModule B S hS a ha).hom.app N))).trans ?_
  refine (congrArg (fun t ↦ ringOneHom (structureRingSheaf B S hS U) ≫
      (moduleSheafFunctor (structureRingSheaf B S hS U)).map
        (modulePullbackGlobalSection B S hS a w) ≫ t)
    (moduleSheafFunctor_map_modulePullbackIsoEtaleRestrictionModule_hom_app B S hS a ha N)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (moduleSheafFunctor (structureRingSheaf B S hS U)).map
      ((modulePullbackIsoEtaleModulePullback B S hS a ha).hom.app N))
    (ringOneHom_comp_map_modulePullbackGlobalSection B S hS a w)).trans ?_
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    (moduleSheafFunctor_map_extendScalarsFSharpAdjunction_unit_comp_modulePullbackIsoEtaleModulePullback
      B S hS a ha N))

/-- For `a : U ⟶ X` étale, a global section `w` of an `𝒪_X`-module `N` and a morphism `j` from
the underlying sheaf of sets of `N` to a sheaf of sets `T`, the pulled-back section `a^*w` read in
the étale restriction and followed by the restriction of `j` is the image along `a⁻¹` of any
global section `y` of `T` equal to the unit section followed by `w` and `j`, followed by the
comparison `a⁻¹ ≅ (restriction)` of Stacks 03LQ. -/
theorem ringOneHom_comp_map_modulePullbackGlobalSection_comp_modulePullbackIsoEtaleRestrictionModule_hom_app_comp_map
    {U X : AlgebraicSpaces B S hS} (a : U ⟶ X) (ha : IsEtale B S hS a.hom)
    {N : Modules.{u, u} B S hS X.1 X.2}
    (w : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ N)
    {T : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (j : (moduleSheafFunctor (structureRingSheaf B S hS X)).obj N ⟶ T)
    {y : ⊤_ (Sheaf (SmallEtale.topology B S hS X.1) (Type u)) ⟶ T}
    (hy : ringOneHom (structureRingSheaf B S hS X) ≫
      (moduleSheafFunctor (structureRingSheaf B S hS X)).map w ≫ j = y) :
    ringOneHom (structureRingSheaf B S hS U) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS U)).map
          (modulePullbackGlobalSection B S hS a w ≫
            (modulePullbackIsoEtaleRestrictionModule B S hS a ha).hom.app N) ≫
        (smallEtaleSetRestriction B S hS a ha).map j =
      (smallEtaleRingedToposModulesHom B S hS a).toToposHom.inverseImage.globalSectionMap y ≫
        (smallToposMorphismTypeU_inverseImageIso B S hS a ha).hom.app T :=
  CategoryTheory.Functor.comp_comp_map_eq_globalSectionMap_comp_app _ _
    (ringOneHom_comp_map_modulePullbackGlobalSection_comp_modulePullbackIsoEtaleRestrictionModule_hom_app
      B S hS a ha w) hy

/-- The kernel inclusion of the extension of a first-order thickening is
`𝒞_{Z/X} ⟶ i⁻¹𝒪_X`, on global sections of underlying sheaves of sets. -/
theorem ringOneHom_comp_map_comp_firstOrderAlgebraExtension_inclSheafSets
    {X Y : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
    (hZ : IsFirstOrderThickening B S hS X Z.1) (g : X ⟶ Y)
    (w : SheafOfModules.unit (structureRingSheaf B S hS
      (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) ⟶ conormalModule B S hS X Z) :
    ringOneHom (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS
          (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))).map w ≫
        (firstOrderAlgebraExtension B S hS Z hZ g).inclSheafSets =
      ringOneHom (structureRingSheaf B S hS (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) ≫
        (moduleSheafFunctor (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS X Z))).map
          ((SheafOfModules.restrictScalars (structureSharpRingInverseImage B S hS
              (subspaceInclusion B S hS X Z))).map w ≫
            conormalInverseImageι B S hS Z hZ) :=
  hom_ext_sections fun _ _ ↦ firstOrderAlgebraExtension_incl B S hS Z hZ g _

end AlgebraicGeometry.Space

end
