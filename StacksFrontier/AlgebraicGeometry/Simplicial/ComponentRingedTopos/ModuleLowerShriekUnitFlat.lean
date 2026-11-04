module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ComponentRestrictionTensor
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaSituation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.UliftTransport

/-!
# Lower shriek of the structure sheaf from a simplicial component is flat

Let `S` be a simplicial-site situation, `O` a sheaf of commutative rings on its total site and
`g_n` the inclusion of the degree-`n` simplicial component. The sheaf of `O`-modules

`g_{n!}O_n`

obtained by applying lower shriek of modules to the structure sheaf of the component ringed topos
is a **flat** sheaf of modules on the total site: tensoring with it is an exact endofunctor of
`Mod(O)`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isFlat_componentModuleLowerShriek_unit`: `g_{n!}O_n`
  is a flat sheaf of `O`-modules.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 03EU](https://stacks.math.columbia.edu/tag/03EU)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D74](https://stacks.math.columbia.edu/tag/0D74)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat hasWeakSheafifyComponent
  wEqualsLocallyBijectiveComponent

/-- For a simplicial-site situation `S` with a sheaf of commutative rings `O` on its total site,
the module lower shriek `g_{n!}O_n` of the structure sheaf of the degree-`n` component is a flat
sheaf of `O`-modules: tensoring with it is an exact endofunctor of `Mod(O)`. -/
theorem isFlat_componentModuleLowerShriek_unit (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) (n : SimplexCategory) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (S.totalRingedTopos O).O)
      ((S.componentModuleLowerShriek (S.totalRingSheaf O) n).obj
        (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n))) := by
  have hunit : ∀ m : SimplexCategory,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
          (O := (S.componentRingedTopos O m).O)
        (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) m)) := by
    intro m
    let : HasSheafify (S.componentTopology m) AddCommGrpCat.{u} :=
      GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} (S.componentTopology m)
    exact Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
      (Y := { C := S.component m, J := S.componentTopology m
              O := (S.componentRingedTopos O m).O })
  have hres : ∀ m : SimplexCategory,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
          (O := (S.componentRingedTopos O m).O)
        ((S.componentModuleRestriction (S.totalRingSheaf O) m).obj
          ((S.componentModuleLowerShriek (S.totalRingSheaf O) n).obj
            (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))) := by
    intro m
    have hG : ∀ i : Discrete (n ⟶ m),
        AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
            (O := (S.componentRingedTopos O m).O)
          ((Discrete.functor (fun φ : n ⟶ m => S.transitionPullbackModules' O φ) ⋙
            (evaluation _ _).obj
              (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n))).obj i) :=
      fun i => Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize
        ((S.componentRingedTopos O m).O)
        (pullbackModulesObjUnitIso (S.transitionRingedToposHom O i.as).toModulesHom) (hunit m)
    let : Abelian (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (S.componentRingedTopos O m).O)) :=
      AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules _
    let : HasFiniteBiproducts (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (S.componentRingedTopos O m).O)) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    have hcol := Stacks.SheafOfModules.FlatCoproduct.isFlat_colimit_ofSize
      ((S.componentRingedTopos O m).O) _ hG
    refine Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize
      ((S.componentRingedTopos O m).O) ?_ hcol
    exact (colimitObjIsoColimitCompEvaluation _ _).symm ≪≫
      ((S.moduleSumFormula O n m).app _).symm
  set F₀ := (S.componentModuleLowerShriek (S.totalRingSheaf O) n).obj
    (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n))
  refine (exactFunctor_iff _).2 ⟨?_,
    Stacks.SheafOfModules.FlatSheafification.sheafTensorRight_preservesFiniteColimits
      S.totalTopology _ _⟩
  refine S.preservesFiniteLimits_of_forall_componentModuleRestriction (S.totalRingSheaf O) _
    fun m => ?_
  have e₁ : (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O).flip.obj F₀ ⋙
        S.componentModulesRestriction O m ≅
      S.componentModulesRestriction O m ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O).flip.obj
          ((S.componentModulesRestriction O m).obj F₀) := by
    refine Iso.trans ?_ (Iso.trans (Functor.isoWhiskerLeft
      (Functor.prod' (𝟭 _) ((Functor.const _).obj F₀))
      (S.componentRestrictionTensorIso O m)) ?_)
    · refine NatIso.ofComponents (fun A => Iso.refl _) (fun {A A'} g => ?_)
      have X₁ :
          ((Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O).flip.obj F₀ ⋙
              S.componentModulesRestriction O m).map g =
            (Functor.prod' (𝟭 _) ((Functor.const _).obj F₀) ⋙
              (Functor.uncurry.obj
                  (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O) ⋙
                S.componentModulesRestriction O m)).map g :=
        (rfl :
            ((Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O).flip.obj F₀ ⋙
                S.componentModulesRestriction O m).map g =
              (S.componentModulesRestriction O m).map
                (((Stacks.SheafOfModules.Tensor.sheafTensor
                  (S.totalRingedTopos O).O).map g).app F₀)).trans
          ((congrArg (fun q => (S.componentModulesRestriction O m).map q)
              ((congrArg (fun q => ((Stacks.SheafOfModules.Tensor.sheafTensor
                      (S.totalRingedTopos O).O).map g).app F₀ ≫ q)
                  (Functor.map_id ((Stacks.SheafOfModules.Tensor.sheafTensor
                    (S.totalRingedTopos O).O).obj A') F₀)).trans
                (Category.comp_id _)).symm).trans
            (rfl :
              (S.componentModulesRestriction O m).map
                  (((Stacks.SheafOfModules.Tensor.sheafTensor
                        (S.totalRingedTopos O).O).map g).app F₀ ≫
                    ((Stacks.SheafOfModules.Tensor.sheafTensor
                      (S.totalRingedTopos O).O).obj A').map (𝟙 F₀)) =
                (Functor.prod' (𝟭 _) ((Functor.const _).obj F₀) ⋙
                  (Functor.uncurry.obj
                      (Stacks.SheafOfModules.Tensor.sheafTensor (S.totalRingedTopos O).O) ⋙
                    S.componentModulesRestriction O m)).map g))
      exact (Category.comp_id _).trans (X₁.trans (Category.id_comp _).symm)
    · refine NatIso.ofComponents (fun A => Iso.refl _) (fun {A A'} g => ?_)
      have X₂ :
          (Functor.prod' (𝟭 _) ((Functor.const _).obj F₀) ⋙
              ((S.componentModulesRestriction O m).prod (S.componentModulesRestriction O m) ⋙
                Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  (S.componentRingedTopos O m).O))).map g =
            (S.componentModulesRestriction O m ⋙
              (Stacks.SheafOfModules.Tensor.sheafTensor
                  (S.componentRingedTopos O m).O).flip.obj
                ((S.componentModulesRestriction O m).obj F₀)).map g :=
        (rfl :
            (Functor.prod' (𝟭 _) ((Functor.const _).obj F₀) ⋙
                ((S.componentModulesRestriction O m).prod (S.componentModulesRestriction O m) ⋙
                  Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                    (S.componentRingedTopos O m).O))).map g =
              ((Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O).map
                    ((S.componentModulesRestriction O m).map g)).app
                  ((S.componentModulesRestriction O m).obj F₀) ≫
                ((Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O).obj
                  ((S.componentModulesRestriction O m).obj A')).map
                    ((S.componentModulesRestriction O m).map (𝟙 F₀))).trans
          (((congrArg (fun q =>
                  ((Stacks.SheafOfModules.Tensor.sheafTensor
                        (S.componentRingedTopos O m).O).map
                      ((S.componentModulesRestriction O m).map g)).app
                    ((S.componentModulesRestriction O m).obj F₀) ≫
                  ((Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O).obj
                    ((S.componentModulesRestriction O m).obj A')).map q)
                (Functor.map_id (S.componentModulesRestriction O m) F₀)).trans
              ((congrArg (fun q =>
                    ((Stacks.SheafOfModules.Tensor.sheafTensor
                          (S.componentRingedTopos O m).O).map
                        ((S.componentModulesRestriction O m).map g)).app
                      ((S.componentModulesRestriction O m).obj F₀) ≫ q)
                  (Functor.map_id ((Stacks.SheafOfModules.Tensor.sheafTensor
                      (S.componentRingedTopos O m).O).obj
                    ((S.componentModulesRestriction O m).obj A'))
                    ((S.componentModulesRestriction O m).obj F₀))).trans
                (Category.comp_id _))).trans
            (rfl :
              ((Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O).map
                    ((S.componentModulesRestriction O m).map g)).app
                  ((S.componentModulesRestriction O m).obj F₀) =
                (S.componentModulesRestriction O m ⋙
                  (Stacks.SheafOfModules.Tensor.sheafTensor
                      (S.componentRingedTopos O m).O).flip.obj
                    ((S.componentModulesRestriction O m).obj F₀)).map g))
      exact (Category.comp_id _).trans (X₂.trans (Category.id_comp _).symm)
  let : PreservesFiniteLimits (S.componentModulesRestriction O m) :=
    S.componentModulesRestriction_preservesFiniteLimits O m
  let : PreservesFiniteLimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O).flip.obj
        ((S.componentModulesRestriction O m).obj F₀)) :=
    (hres m).1
  let : PreservesFiniteLimits (S.componentModulesRestriction O m ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O).flip.obj
        ((S.componentModulesRestriction O m).obj F₀)) :=
    comp_preservesFiniteLimits (S.componentModulesRestriction O m)
      ((Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O).flip.obj
        ((S.componentModulesRestriction O m).obj F₀))
  exact preservesFiniteLimits_of_natIso
    (F := S.componentModulesRestriction O m ⋙
      (Stacks.SheafOfModules.Tensor.sheafTensor (S.componentRingedTopos O m).O).flip.obj
        ((S.componentModulesRestriction O m).obj F₀)) e₁.symm

end CategoryTheory.SimplicialSiteSituation

end
