module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDirectImageForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.DerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage

/-!
# Proper base change for sheaves of modules on bounded below derived categories

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes with `f` proper, and `Λ` a ring. For every object `K` of
`D⁺(X_étale, Λ)` with torsion cohomology sheaves the base change map
`g^{-1} Rf_* K ⟶ Rf'_* (g')^{-1} K` of sheaves of `Λ`-modules is an isomorphism. This is the
form of the proper base change theorem [Stacks, Tag 0DDE] used for `Rf_!` in [Stacks, Tag 0F7L].

The proof reduces to the abelian statement. Represent `K` by a bounded below complex `I` of
injective sheaves of `Λ`-modules and choose a quasi-isomorphism `i : (g')^{-1} I ⟶ L` onto a
bounded below complex of injectives. The base change map at `K` is then invertible as soon as the
morphism of complexes `g^{-1} f_* I ⟶ f'_* (g')^{-1} I ⟶ f'_* L` is a quasi-isomorphism
(`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_app_of_quasiIso`). Forgetting the
module structures, which is exact and conservative, this morphism becomes the abelian degreewise
comparison followed by `f'_*` of a quasi-isomorphism; the underlying abelian sheaves of injective
sheaves of modules are acyclic for direct images, so it is a quasi-isomorphism by the abelian
proper base change theorem
(`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_of_isProper`).

## Main results

* `isIso_etaleModuleDerivedBaseChange_app_of_isIso_etaleAbelianDerivedBaseChange`:
  in every coefficient universe, the module base change map is invertible at a complex of
  injectives as soon as the abelian one is invertible at its underlying complex.
* `isIso_etaleModuleDerivedBaseChange_of_isProper`: proper base change for
  bounded below complexes of sheaves of modules with torsion cohomology.

## Implementation notes

The kernel compares the abelian statements (proved in files whose universe variables are `u, v`)
with terms built here only when both carry the same spelling of universe levels and instances.
The coefficient universe is therefore called `w`, which instance resolution orders after `u` as
the abelian files do with `v`; two instances that the abelian files do not use are switched off;
and the base change maps and the comparisons of the forgetful functors are turned into variables
(`generalize`) before the generic statement is applied, so that the kernel never unfolds them.

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

/- The abelian base change statements this file instantiates find the sheafification of abelian
presheaves on small étale sites through `AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology`;
the general instance `Stacks.SheafOfModules.coefficientSheafification` would give the categories of
abelian sheaves built here a different (propositionally equal) instance argument, and the kernel
compares terms with different spellings by unfolding them. -/
attribute [-instance] Stacks.SheafOfModules.coefficientSheafification

/- Likewise the abelian statements see the additivity of direct image as
`Stacks.EtaleCohomology.additive_etaleAbelianDirectImage`. -/
attribute [-instance] Stacks.EtaleCohomology.etaleAbelianDirectImage_additive

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type w) [Ring Λ]

/-- A sheaf of `Λ`-modules is torsion exactly when its underlying abelian sheaf is: both say
that every local section is locally annihilated by a positive integer. -/
theorem isTorsionEtaleModule_iff_torsionSheafProperty {X : Scheme.{u}}
    (M : EtaleModules.{u, w} Λ X) :
    IsTorsionEtaleModule.{u, w} Λ X M ↔
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
        ((etaleModuleForgetAb.{u, w} Λ X).obj M) :=
  Iff.rfl

/-- The cohomology sheaves of the underlying complex of abelian sheaves of a complex of sheaves of
`Λ`-modules are the underlying abelian sheaves of its cohomology sheaves. -/
def etaleModuleForgetHomologyIso {X : Scheme.{u}}
    (I : CochainComplex (EtaleModules.{u, w} Λ X) ℤ) (m : ℤ) :
    (DerivedCategory.homologyFunctor _ m).obj (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) ≅
      (etaleModuleForgetAb.{u, w} Λ X).obj (I.homology m) :=
  (DerivedCategory.homologyFunctor _ m).mapIso ((DerivedCategory.quotientCompQhIso _).app _) ≪≫
    (DerivedCategory.homologyFunctorFactors _ m).app _ ≪≫
      (I.sc m).mapHomologyIso (etaleModuleForgetAb.{u, w} Λ X)

/-- Direct image commutes with forgetting the module structure: the underlying abelian sheaf of
`f_* M` is `f_*` of the underlying abelian sheaf of `M`, on the nose. -/
def etaleModuleForgetDirectImageIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleModuleForgetAb.{u, w} Λ X ⋙ etaleAbelianDirectImage.{u, w} f ≅
      etaleModuleDirectImage.{u, w} Λ f ⋙ etaleModuleForgetAb.{u, w} Λ Y :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- `Stacks.EtaleCohomology.etaleModuleForgetInverseImageIso_comp_map_etaleModuleBaseChange`
read through `Stacks.EtaleCohomology.etaleModuleForgetDirectImageIso`. -/
theorem etaleModuleForgetDirectImageIso_comp_map_etaleModuleBaseChange
    {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (M : EtaleModules.{u, w} Λ X) :
    (etaleAbelianInverseImage.{u, w} g).map
        ((etaleModuleForgetDirectImageIso.{u, w} Λ f).hom.app M) ≫
      (etaleModuleForgetInverseImageIso.{u, w} Λ g).hom.app
        ((etaleModuleDirectImage.{u, w} Λ f).obj M) ≫
      (etaleModuleForgetAb.{u, w} Λ Y').map ((etaleModuleBaseChange Λ f f' g g' h.symm).app M) =
    (etaleAbelianBaseChange.{u, w} f g g' f' h).app
        ((etaleModuleForgetAb.{u, w} Λ X).obj M) ≫
      (etaleAbelianDirectImage.{u, w} f').map
        ((etaleModuleForgetInverseImageIso.{u, w} Λ g').hom.app M) ≫
      (etaleModuleForgetDirectImageIso.{u, w} Λ f').hom.app
        ((etaleModuleInverseImage.{u, w} Λ g').obj M) := by
  have h₁ : (etaleAbelianInverseImage.{u, w} g).map
      ((etaleModuleForgetDirectImageIso.{u, w} Λ f).hom.app M) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  have h₂ : (etaleModuleForgetDirectImageIso.{u, w} Λ f').hom.app
      ((etaleModuleInverseImage.{u, w} Λ g').obj M) = 𝟙 _ := rfl
  refine (congrArg (· ≫ _) h₁).trans ((Category.id_comp _).trans
    ((etaleModuleForgetInverseImageIso_comp_map_etaleModuleBaseChange.{u, w} Λ f f' g g' h
      M).trans ((Category.comp_id _).symm.trans (congrArg (fun t =>
        (etaleAbelianBaseChange.{u, w} f g g' f' h).app
          ((etaleModuleForgetAb.{u, w} Λ X).obj M) ≫
        (etaleAbelianDirectImage.{u, w} f').map
          ((etaleModuleForgetInverseImageIso.{u, w} Λ g').hom.app M) ≫ t) h₂.symm))))

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms in
/-- `Stacks.Cohomology.DerivedBaseChangeResolution.isIso_derivedBaseChangePlus_app_of_forget` for
the étale functors, with the abelian base change map `αa` and the comparisons `σ, τ, τ', σ'` of
the forgetful functors with direct and inverse image as variables: if the abelian comparison
through a resolution `i : (g')^{-1} I ⟶ L` is a quasi-isomorphism and the forgetful functors carry
the module comparison to the abelian one (`hP`), the module base change map is invertible at `I`.
Stating it with these as variables lets the kernel check the generic lemma's hypotheses without
unfolding the comparisons. -/
theorem isIso_etaleModuleDerivedBaseChange_app_of_forget
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (w : f' ≫ g = g' ≫ f)
    (αa : etaleAbelianDirectImage.{u, w} f ⋙ etaleAbelianInverseImage.{u, w} g ⟶
      etaleAbelianInverseImage.{u, w} g' ⋙ etaleAbelianDirectImage.{u, w} f')
    (σ : etaleModuleForgetAb.{u, w} Λ X ⋙ etaleAbelianDirectImage.{u, w} f ≅
      etaleModuleDirectImage.{u, w} Λ f ⋙ etaleModuleForgetAb.{u, w} Λ Y)
    (τ : etaleModuleForgetAb.{u, w} Λ Y ⋙ etaleAbelianInverseImage.{u, w} g ≅
      etaleModuleInverseImage.{u, w} Λ g ⋙ etaleModuleForgetAb.{u, w} Λ Y')
    (τ' : etaleModuleForgetAb.{u, w} Λ X ⋙ etaleAbelianInverseImage.{u, w} g' ≅
      etaleModuleInverseImage.{u, w} Λ g' ⋙ etaleModuleForgetAb.{u, w} Λ X')
    (σ' : etaleModuleForgetAb.{u, w} Λ X' ⋙ etaleAbelianDirectImage.{u, w} f' ≅
      etaleModuleDirectImage.{u, w} Λ f' ⋙ etaleModuleForgetAb.{u, w} Λ Y')
    (hP : ∀ M : EtaleModules.{u, w} Λ X,
      (etaleAbelianInverseImage.{u, w} g).map (σ.hom.app M) ≫
          τ.hom.app ((etaleModuleDirectImage.{u, w} Λ f).obj M) ≫
            (etaleModuleForgetAb.{u, w} Λ Y').map ((etaleModuleBaseChange Λ f f' g g' w).app M) =
        αa.app ((etaleModuleForgetAb.{u, w} Λ X).obj M) ≫
          (etaleAbelianDirectImage.{u, w} f').map (τ'.hom.app M) ≫
            σ'.hom.app ((etaleModuleInverseImage.{u, w} Λ g').obj M))
    (I : CochainComplex.Plus (EtaleModules.{u, w} Λ X)) [∀ n, Injective (I.obj.X n)]
    (L : CochainComplex.Plus (EtaleModules.{u, w} Λ X')) [∀ n, Injective (L.obj.X n)]
    (i : (etaleModuleInverseImage.{u, w} Λ g').mapCochainComplexPlus.obj I ⟶ L)
    (hi : QuasiIso i.hom)
    (hy : QuasiIso
      ((NatTrans.mapHomologicalComplex αa (ComplexShape.up ℤ)).app
          (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            I.obj) ≫
        ((etaleAbelianDirectImage.{u, w} f').mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex τ' (ComplexShape.up ℤ)).hom.app I.obj ≫
            ((etaleModuleForgetAb.{u, w} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).map
              i.hom))) :
    IsIso ((etaleModuleDerivedBaseChange.{u, w} Λ f f' g g' w).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj I))) :=
  have := etaleModules_enoughInjectives.{u, w} Λ X
  have := etaleModules_enoughInjectives.{u, w} Λ X'
  Stacks.Cohomology.DerivedBaseChangeResolution.isIso_derivedBaseChangePlus_app_of_forget
    _ αa τ' I L i hi ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hy) σ τ σ' hP

/-- Forgetting the module structure preserves strict boundedness below of a complex. -/
private theorem isStrictlyGE_forget_obj {X : Scheme.{u}}
    (I : CochainComplex (EtaleModules.{u, w} Λ X) ℤ) (n : ℤ) (h : I.IsStrictlyGE n) :
    CochainComplex.IsStrictlyGE
      (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) n :=
  (CochainComplex.isStrictlyGE_iff _ n).2 fun m hm =>
    (etaleModuleForgetAb.{u, w} Λ X).map_isZero ((CochainComplex.isStrictlyGE_iff I n).1 h m hm)

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms in
/-- **The abelian base change comparison on the underlying complexes of a resolution.** Let `I` be
a bounded below complex of injective sheaves of `Λ`-modules on `X_étale`, `i : (g')^{-1} I ⟶ L` a
quasi-isomorphism onto a bounded below complex of injectives, and suppose the abelian base change
map is invertible at the underlying complex `U(I)`. Then the abelian comparison at `U(I)` followed
by `f'_*` of `(g')^{-1} U(I) ≅ U((g')^{-1} I) ⟶ U(L)` is a quasi-isomorphism
(`Stacks.EtaleCohomology.isIso_Q_map_etaleAbelianBaseChange_comp_of_quasiIso`; the underlying
abelian sheaves of injective sheaves of modules are acyclic for direct images). -/
theorem quasiIso_etaleAbelianBaseChange_comp_etaleModuleForget_of_isIso
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g)
    (I : CochainComplex.Plus (EtaleModules.{u, w} Λ X)) [∀ n, Injective (I.obj.X n)]
    (L : CochainComplex.Plus (EtaleModules.{u, w} Λ X')) [∀ n, Injective (L.obj.X n)]
    (i : (etaleModuleInverseImage.{u, w} Λ g').mapCochainComplexPlus.obj I ⟶ L)
    (hi : QuasiIso i.hom)
    (hbc : IsIso ((etaleAbelianDerivedBaseChange.{u, w} f g g' f' sq.w).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I.obj))))) :
    QuasiIso
      ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, w} f g g' f' sq.w)
          (ComplexShape.up ℤ)).app
          (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            I.obj) ≫
        ((etaleAbelianDirectImage.{u, w} f').mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex (etaleModuleForgetInverseImageIso.{u, w} Λ g')
              (ComplexShape.up ℤ)).hom.app I.obj ≫
            ((etaleModuleForgetAb.{u, w} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).map
              i.hom)) := by
  obtain ⟨n₀, hn₀⟩ := I.property
  obtain ⟨n₀', hn₀'⟩ := L.property
  have hKU : CochainComplex.plus _
      (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj) :=
    ⟨n₀, isStrictlyGE_forget_obj Λ _ n₀ hn₀⟩
  have hKU' : CochainComplex.plus _
      (((etaleModuleForgetAb.{u, w} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj) :=
    ⟨n₀', isStrictlyGE_forget_obj Λ _ n₀' hn₀'⟩
  have hac : ∀ m : ℤ, (etaleAbelianDirectImage.{u, w} f).rightAcyclic
      ((((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        I.obj).X m) := fun m =>
    rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj.{u, w} Λ f (I.obj.X m)
  have hac' : ∀ m : ℤ, (etaleAbelianDirectImage.{u, w} f').rightAcyclic
      ((((etaleModuleForgetAb.{u, w} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        L.obj).X m) := fun m =>
    rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj.{u, w} Λ f' (L.obj.X m)
  have hq : QuasiIso ((NatIso.mapHomologicalComplex
      (etaleModuleForgetInverseImageIso.{u, w} Λ g') (ComplexShape.up ℤ)).hom.app I.obj ≫
      ((etaleModuleForgetAb.{u, w} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom) :=
    quasiIso_comp (hφ := inferInstance)
      (hφ' := HomologicalComplex.quasiIso_map_of_preservesHomology i.hom
        (etaleModuleForgetAb.{u, w} Λ X')) _ _
  have hy := isIso_Q_map_etaleAbelianBaseChange_comp_of_quasiIso.{u, w} f g g' f' sq.w
    (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj) hKU
    hac (((etaleModuleForgetAb.{u, w} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj)
    hKU' hac' ((NatIso.mapHomologicalComplex
      (etaleModuleForgetInverseImageIso.{u, w} Λ g') (ComplexShape.up ℤ)).hom.app I.obj ≫
      ((etaleModuleForgetAb.{u, w} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).map i.hom) hbc
  -- the statement carries the spelling of this file; as variables, the base change map and the
  -- comparison of inverse images are compared with themselves
  generalize etaleAbelianBaseChange.{u, w} f g g' f' sq.w = αa at hy ⊢
  generalize etaleModuleForgetInverseImageIso.{u, w} Λ g' = τ' at hy ⊢
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 hy

/-- **The module base change map at a complex of injectives, from the abelian one.** Let `I` be a
bounded below complex of injective sheaves of `Λ`-modules on `X_étale` and `i : (g')^{-1} I ⟶ L`
a quasi-isomorphism onto a bounded below complex of injectives. If the abelian base change map is
invertible at the underlying complex of abelian sheaves of `I`, then the module base change map
is invertible at `I`: forgetting the module structures carries the module comparison through the
resolution to the abelian one
(`Stacks.EtaleCohomology.quasiIso_etaleAbelianBaseChange_comp_etaleModuleForget_of_isIso`,
`Stacks.EtaleCohomology.etaleModuleForgetDirectImageIso_comp_map_etaleModuleBaseChange`). -/
theorem isIso_etaleModuleDerivedBaseChange_app_of_isIso_etaleAbelianDerivedBaseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g)
    (I : CochainComplex.Plus (EtaleModules.{u, w} Λ X)) [∀ n, Injective (I.obj.X n)]
    (L : CochainComplex.Plus (EtaleModules.{u, w} Λ X')) [∀ n, Injective (L.obj.X n)]
    (i : (etaleModuleInverseImage.{u, w} Λ g').mapCochainComplexPlus.obj I ⟶ L)
    (hi : QuasiIso i.hom)
    (hbc : IsIso ((etaleAbelianDerivedBaseChange.{u, w} f g g' f' sq.w).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I.obj))))) :
    IsIso ((etaleModuleDerivedBaseChange.{u, w} Λ f f' g g' sq.w.symm).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj I))) := by
  have hy := quasiIso_etaleAbelianBaseChange_comp_etaleModuleForget_of_isIso Λ f sq I L i hi hbc
  have hP := etaleModuleForgetDirectImageIso_comp_map_etaleModuleBaseChange.{u, w} Λ f f' g g' sq.w
  -- the base change map and the comparisons enter `hy` and `hP` with differently spelled
  -- implicit arguments; as variables they are compared with themselves, so that the kernel
  -- never unfolds them
  generalize etaleAbelianBaseChange.{u, w} f g g' f' sq.w = αa at hy hP
  generalize etaleModuleForgetInverseImageIso.{u, w} Λ g' = τ' at hy hP
  generalize etaleModuleForgetInverseImageIso.{u, w} Λ g = τ at hP
  generalize etaleModuleForgetDirectImageIso.{u, w} Λ f = σ at hP
  generalize etaleModuleForgetDirectImageIso.{u, w} Λ f' = σ' at hP
  exact isIso_etaleModuleDerivedBaseChange_app_of_forget Λ f f' g g' sq.w.symm αa σ τ τ' σ' hP
    I L i hi hy

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ]

/-- **Proper base change on complexes of injective sheaves of modules.** Let `f` be proper and the
square cartesian, `I` a bounded below complex of injective sheaves of `Λ`-modules on `X_étale` with
torsion cohomology sheaves and `i : (g')^{-1} I ⟶ L` a quasi-isomorphism onto a bounded below
complex of injectives. Then the base change map is invertible at `I`, by the abelian proper base
change theorem at the underlying complex of abelian sheaves of `I`. -/
theorem isIso_etaleModuleDerivedBaseChange_app_of_injective_of_isProper {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g)
    (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) [∀ n, Injective (I.obj.X n)]
    (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ X')) [∀ n, Injective (L.obj.X n)]
    (i : (etaleModuleInverseImage.{u, 0} Λ g').mapCochainComplexPlus.obj I ⟶ L)
    (hi : QuasiIso i.hom) (hT : ∀ n, IsTorsionEtaleModule.{u, 0} Λ X (I.obj.homology n)) :
    IsIso ((etaleModuleDerivedBaseChange.{u, 0} Λ f f' g g' sq.w.symm).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj I))) := by
  obtain ⟨n₀, hn₀⟩ := I.property
  have hE : (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((etaleModuleForgetAb.{u, 0} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        I.obj))).IsGE n₀ := by
    have := isStrictlyGE_forget_obj.{u, 0} Λ I.obj n₀ hn₀
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((DerivedCategory.quotientCompQhIso _).symm.app _) n₀
  have hT' : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleModuleForgetAb.{u, 0} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I.obj))) := fun m =>
    Stacks.Torsion.torsionSheafProperty_of_iso X.smallEtaleTopology
      (etaleModuleForgetHomologyIso.{u, 0} Λ I.obj m).symm (hT m)
  exact isIso_etaleModuleDerivedBaseChange_app_of_isIso_etaleAbelianDerivedBaseChange.{u, 0} Λ f sq
    I L i hi (isIso_etaleAbelianDerivedBaseChange_of_isProper f sq _ n₀ hE hT')

/-- **Proper base change for sheaves of modules** ([Stacks, Tag 0DDE], with coefficients in a
ring `Λ`). Let `f : X ⟶ Y` be proper and `X' = Y' ×_Y X` with projections `f'` and `g'`. For
every `K ∈ D⁺(X_étale, Λ)` with torsion cohomology sheaves the base change map
`g^{-1} Rf_* K ⟶ Rf'_* (g')^{-1} K` is an isomorphism. -/
theorem isIso_etaleModuleDerivedBaseChange_of_isProper {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (hK : isTorsionPlus.{u, 0} Λ X K) :
    IsIso ((etaleModuleDerivedBaseChange.{u, 0} Λ f f' g g' sq.w.symm).app K) := by
  have := etaleModules_enoughInjectives.{u, 0} Λ X
  have := etaleModules_enoughInjectives.{u, 0} Λ X'
  obtain ⟨n, hn⟩ := K.property
  have : K.IsGE n := (K.isGE_ι_obj_iff n).1 hn
  obtain ⟨L₀, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  -- a bounded below complex of injectives representing `K`, as an opaque variable
  obtain ⟨I, hI, ⟨e'⟩⟩ : ∃ (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
      (_ : ∀ m, Injective (I.obj.X m)),
      Nonempty (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj I) ≅ K) :=
    ⟨(InjectiveObject.ι (EtaleModules.{u, 0} Λ X)).mapCochainComplexPlus.obj L₀,
      fun m => (L₀.obj.X m).property,
      ⟨Functor.preimageIso (F := DerivedCategory.Plus.ι)
        (X := DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient _).obj
          ((InjectiveObject.ι (EtaleModules.{u, 0} Λ X)).mapCochainComplexPlus.obj L₀)))
        (Y := DerivedCategory.Plus.Q.obj
          ((InjectiveObject.ι (EtaleModules.{u, 0} Λ X)).mapCochainComplexPlus.obj L₀))
        ((DerivedCategory.quotientCompQhIso _).app _) ≪≫ e⟩⟩
  refine (NatTrans.isIso_app_iff_of_iso _ e').1 ?_
  obtain ⟨n₁, hn₁⟩ := ((etaleModuleInverseImage.{u, 0} Λ g').mapCochainComplexPlus.obj I).property
  obtain ⟨L₁, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective
    ((etaleModuleInverseImage.{u, 0} Λ g').mapCochainComplexPlus.obj I) n₁
  -- a resolution of `(g')⁻¹ I` by a bounded below complex of injectives, as opaque variables
  obtain ⟨L, hL, i', hi'⟩ : ∃ (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ X'))
      (_ : ∀ m, Injective (L.obj.X m))
      (i' : (etaleModuleInverseImage.{u, 0} Λ g').mapCochainComplexPlus.obj I ⟶ L),
      QuasiIso i'.hom :=
    ⟨(InjectiveObject.ι (EtaleModules.{u, 0} Λ X')).mapCochainComplexPlus.obj L₁,
      fun m => (L₁.obj.X m).property, i, hi⟩
  have hT : ∀ m, IsTorsionEtaleModule Λ X (I.obj.homology m) := fun m =>
    IsTorsionEtaleModule.of_iso Λ X
      ((DerivedCategory.Plus.homologyFunctor _ m).mapIso e'.symm ≪≫
        (DerivedCategory.homologyFunctor _ m).mapIso
          ((DerivedCategory.quotientCompQhIso _).app I.obj) ≪≫
        (DerivedCategory.homologyFunctorFactors _ m).app I.obj) (hK m)
  exact isIso_etaleModuleDerivedBaseChange_app_of_injective_of_isProper Λ f sq I L i' hi' hT

end Stacks.EtaleCohomology

end
