module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChangeUnboundedResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper base change on the unbounded derived category, for bounded below torsion complexes

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes with `f` proper, and `Λ` a commutative ring. For every object `E`
of the unbounded derived category `D(X_étale, Λ)` which is bounded below and has torsion cohomology
sheaves, the base change map `g^{-1} Rf_* E ⟶ Rf'_* (g')^{-1} E` on unbounded derived categories
(`Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded`) is an isomorphism. This is
[Stacks, Tag 0DDE] read on the unbounded base change map.

The proof is that of `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isProper`.
Represent `E` by a bounded below complex `I` of injective sheaves of `Λ`-modules and choose a
quasi-isomorphism `i : (g')^{-1} I ⟶ L` onto a bounded below complex of injectives. Forgetting
the module structures and applying the abelian proper base change theorem, the morphism of
complexes `g^{-1} f_* I ⟶ f'_* (g')^{-1} I ⟶ f'_* L` is a quasi-isomorphism; as `I` and `L` are
K-injective, the unbounded base change map at `I` is then invertible
(`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isIso_Q_map`).

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isGE_of_isProper`.

## Implementation notes

As in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange`
the coefficient universe is called `w` and instances are switched off, so that the abelian
statements are compared with the terms built here in one spelling. The underived base change map
`Stacks.EtaleCohomology.etaleModuleBaseChange`, the abelian one and the comparisons of the
forgetful functors are turned into variables (`generalize`) before statements proved in another
spelling of the instances are applied, so that the kernel never unfolds them.

## References

* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] Stacks.SheafOfModules.coefficientSheafification

attribute [-instance] Stacks.EtaleCohomology.etaleAbelianDirectImage_additive

/- The statements imported from `ModuleDerivedProperBaseChange` find the sheafification of
presheaves of modules on small étale sites through
`AlgebraicGeometry.Scheme.hasSheafify_smallEtaleTopology`; the instances below, visible through the
imports of this file, would give the inverse image functors built here a different spelling. -/
attribute [-instance] AlgebraicGeometry.RingedSite.moduleHasSheafify
attribute [-instance] Stacks.EtaleCohomology.hasSheafifyEtale
  Stacks.EtaleCohomology.hasWeakSheafifyOverEtale

universe u w

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type w) [CommRing Λ]

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms in
/-- `Stacks.Cohomology.DerivedBaseChangeResolution.isIso_Q_map_natTrans_comp_of_forget` for the
étale functors, with the module base change map `αm`, the abelian one `αa` and the comparisons
`σ, τ, τ', σ'` of the forgetful functors with direct and inverse image as variables: if the
abelian comparison through a resolution `i : (g')^{-1} I ⟶ L` is a quasi-isomorphism and the
forgetful functors carry `αm` to `αa` (`hP`), the module comparison through `i` is a
quasi-isomorphism. -/
theorem isIso_Q_map_etaleModuleBaseChange_comp_of_forget
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (αm : etaleModuleDirectImage.{u, w} Λ f ⋙ etaleModuleInverseImage.{u, w} Λ g ⟶
      etaleModuleInverseImage.{u, w} Λ g' ⋙ etaleModuleDirectImage.{u, w} Λ f')
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
            (etaleModuleForgetAb.{u, w} Λ Y').map (αm.app M) =
        αa.app ((etaleModuleForgetAb.{u, w} Λ X).obj M) ≫
          (etaleAbelianDirectImage.{u, w} f').map (τ'.hom.app M) ≫
            σ'.hom.app ((etaleModuleInverseImage.{u, w} Λ g').obj M))
    (I : CochainComplex.Plus (EtaleModules.{u, w} Λ X))
    (L : CochainComplex.Plus (EtaleModules.{u, w} Λ X'))
    (i : (etaleModuleInverseImage.{u, w} Λ g').mapCochainComplexPlus.obj I ⟶ L)
    (hy : QuasiIso
      ((NatTrans.mapHomologicalComplex αa (ComplexShape.up ℤ)).app
          (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            I.obj) ≫
        ((etaleAbelianDirectImage.{u, w} f').mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatIso.mapHomologicalComplex τ' (ComplexShape.up ℤ)).hom.app I.obj ≫
            ((etaleModuleForgetAb.{u, w} Λ X').mapHomologicalComplex (ComplexShape.up ℤ)).map
              i.hom))) :
    IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex αm (ComplexShape.up ℤ)).app I.obj ≫
        ((etaleModuleDirectImage.{u, w} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map
          i.hom)) :=
  Stacks.Cohomology.DerivedBaseChangeResolution.isIso_Q_map_natTrans_comp_of_forget
    αm αa σ τ τ' σ' hP I L i ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hy)

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms in
/-- **The module comparison through a resolution, from the abelian base change map.** Let `I` be
a bounded below complex of injective sheaves of `Λ`-modules on `X_étale` and
`i : (g')^{-1} I ⟶ L` a quasi-isomorphism onto a bounded below complex of injectives. If the
abelian base change map is invertible at the underlying complex of abelian sheaves of `I`, then
`g^{-1} f_* I ⟶ f'_* (g')^{-1} I ⟶ f'_* L` is a quasi-isomorphism. The underived base change map
enters as a variable `αm` equal to `Stacks.EtaleCohomology.etaleModuleBaseChange`. -/
theorem isIso_Q_map_etaleModuleBaseChange_comp_of_isIso_etaleAbelianDerivedBaseChange
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g)
    (I : CochainComplex.Plus (EtaleModules.{u, w} Λ X)) [∀ n, Injective (I.obj.X n)]
    (L : CochainComplex.Plus (EtaleModules.{u, w} Λ X')) [∀ n, Injective (L.obj.X n)]
    (i : (etaleModuleInverseImage.{u, w} Λ g').mapCochainComplexPlus.obj I ⟶ L)
    (hi : QuasiIso i.hom)
    (hbc : IsIso ((etaleAbelianDerivedBaseChange.{u, w} f g g' f' sq.w).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleModuleForgetAb.{u, w} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I.obj)))))
    (αm : etaleModuleDirectImage.{u, w} Λ f ⋙ etaleModuleInverseImage.{u, w} Λ g ⟶
      etaleModuleInverseImage.{u, w} Λ g' ⋙ etaleModuleDirectImage.{u, w} Λ f')
    (hαm : αm = etaleModuleBaseChange.{u, w} Λ f f' g g' sq.w.symm) :
    IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex αm (ComplexShape.up ℤ)).app I.obj ≫
        ((etaleModuleDirectImage.{u, w} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map
          i.hom)) := by
  subst hαm
  have hy := quasiIso_etaleAbelianBaseChange_comp_etaleModuleForget_of_isIso Λ f sq I L i hi hbc
  have hP := etaleModuleForgetDirectImageIso_comp_map_etaleModuleBaseChange.{u, w} Λ f f' g g' sq.w
  -- the base change maps and the comparisons enter `hy`, `hP` and the statement with differently
  -- spelled implicit arguments; as variables they are compared with themselves, so that the
  -- kernel never unfolds them
  generalize etaleModuleBaseChange.{u, w} Λ f f' g g' sq.w.symm = αm at hP ⊢
  generalize etaleAbelianBaseChange.{u, w} f g g' f' sq.w = αa at hy hP
  generalize etaleModuleForgetInverseImageIso.{u, w} Λ g' = τ' at hy hP
  generalize etaleModuleForgetInverseImageIso.{u, w} Λ g = τ at hP
  generalize etaleModuleForgetDirectImageIso.{u, w} Λ f = σ at hP
  generalize etaleModuleForgetDirectImageIso.{u, w} Λ f' = σ' at hP
  exact isIso_Q_map_etaleModuleBaseChange_comp_of_forget Λ f f' g g' αm αa σ τ τ' σ' hP I L i hy

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ]

/-- A bounded below complex receives a quasi-isomorphism into a K-injective bounded below complex
of injectives. -/
private theorem exists_quasiIso_isKInjective_injective {A : Type*} [Category A] [Abelian A]
    [EnoughInjectives A] (C : CochainComplex.Plus A) :
    ∃ (L : CochainComplex.Plus A) (_ : ∀ m, Injective (L.obj.X m)) (_ : L.obj.IsKInjective)
      (i : C ⟶ L), QuasiIso i.hom := by
  obtain ⟨n, hn⟩ := C.property
  obtain ⟨L₁, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective C n
  have hL : ∀ m, Injective (((InjectiveObject.ι A).mapCochainComplexPlus.obj L₁).obj.X m) :=
    fun m => (L₁.obj.X m).property
  obtain ⟨d, _⟩ := ((InjectiveObject.ι A).mapCochainComplexPlus.obj L₁).property
  exact ⟨_, hL, CochainComplex.isKInjective_of_injective _ d, i, hi⟩

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms in
/-- **The module comparison through a resolution, for torsion complexes and `f` proper.** Let `I`
be a bounded below complex of injective sheaves of `Λ`-modules on `X_étale` with torsion
cohomology sheaves and `i : (g')^{-1} I ⟶ L` a quasi-isomorphism onto a bounded below complex of
injectives. Then `g^{-1} f_* I ⟶ f'_* (g')^{-1} I ⟶ f'_* L` is a quasi-isomorphism, by the
abelian proper base change theorem at the underlying complex of abelian sheaves of `I`. The
underived base change map enters as a variable `αm` equal to
`Stacks.EtaleCohomology.etaleModuleBaseChange`. -/
@[sga "4 XVII 4.3.2" "(ii), special case"]
theorem isIso_Q_map_etaleModuleBaseChange_comp_of_isProper {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g)
    (I : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) [∀ n, Injective (I.obj.X n)]
    (L : CochainComplex.Plus (EtaleModules.{u, 0} Λ X')) [∀ n, Injective (L.obj.X n)]
    (i : (etaleModuleInverseImage.{u, 0} Λ g').mapCochainComplexPlus.obj I ⟶ L)
    (hi : QuasiIso i.hom) (hT : ∀ n, IsTorsionEtaleModule.{u, 0} Λ X (I.obj.homology n))
    (αm : etaleModuleDirectImage.{u, 0} Λ f ⋙ etaleModuleInverseImage.{u, 0} Λ g ⟶
      etaleModuleInverseImage.{u, 0} Λ g' ⋙ etaleModuleDirectImage.{u, 0} Λ f')
    (hαm : αm = etaleModuleBaseChange.{u, 0} Λ f f' g g' sq.w.symm) :
    IsIso (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex αm (ComplexShape.up ℤ)).app I.obj ≫
        ((etaleModuleDirectImage.{u, 0} Λ f').mapHomologicalComplex (ComplexShape.up ℤ)).map
          i.hom)) := by
  obtain ⟨n₀, hn₀⟩ := I.property
  have hE : (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((etaleModuleForgetAb.{u, 0} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        I.obj))).IsGE n₀ := by
    have : CochainComplex.IsStrictlyGE
        (((etaleModuleForgetAb.{u, 0} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I.obj) n₀ :=
      (CochainComplex.isStrictlyGE_iff _ n₀).2 fun m hm =>
        (etaleModuleForgetAb.{u, 0} Λ X).map_isZero
          ((CochainComplex.isStrictlyGE_iff I.obj n₀).1 hn₀ m hm)
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((DerivedCategory.quotientCompQhIso _).symm.app _) n₀
  have hT' : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleModuleForgetAb.{u, 0} Λ X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          I.obj))) := fun m =>
    Stacks.Torsion.torsionSheafProperty_of_iso X.smallEtaleTopology
      (etaleModuleForgetHomologyIso.{u, 0} Λ I.obj m).symm (hT m)
  exact isIso_Q_map_etaleModuleBaseChange_comp_of_isIso_etaleAbelianDerivedBaseChange.{u, 0} Λ f
    sq I L i hi (isIso_etaleAbelianDerivedBaseChange_of_isProper f sq _ n₀ hE hT') αm hαm

/-- **Proper base change on the unbounded derived category, for bounded below torsion complexes**
([Stacks, Tag 0DDE], read on `Stacks.EtaleCohomology.etaleModuleDerivedBaseChangeUnbounded`). Let
`f : X ⟶ Y` be proper and `X' = Y' ×_Y X` with projections `f'` and `g'`. For every object `E` of
`D(X_étale, Λ)` which is bounded below and has torsion cohomology sheaves, the base change map
`g^{-1} Rf_* E ⟶ Rf'_* (g')^{-1} E` is an isomorphism. -/
@[sga "4 XVII 4.3.2" "variant (ii)", sga "4 XVII 5.2.7" "(ii), special case"]
theorem isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isGE_of_isProper
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (sq : IsPullback g' f' f g) (E : DerivedCategory (EtaleModules.{u, 0} Λ X)) (a : ℤ)
    (hE : E.IsGE a)
    (hT : ∀ n, IsTorsionEtaleModule.{u, 0} Λ X ((DerivedCategory.homologyFunctor _ n).obj E)) :
    IsIso ((etaleModuleDerivedBaseChangeUnbounded.{u, 0} Λ f g g' f' sq.w).app E) := by
  have := etaleModules_enoughInjectives.{u, 0} Λ X
  have := etaleModules_enoughInjectives.{u, 0} Λ X'
  obtain ⟨K, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE E a
  obtain ⟨I, hI, hIK, j, hj⟩ := exists_quasiIso_isKInjective_injective
    (⟨K, a, inferInstance⟩ : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
  have : QuasiIso j.hom := hj
  have e' : DerivedCategory.Q.obj I.obj ≅ E := (asIso (DerivedCategory.Q.map j.hom)).symm ≪≫ e.symm
  refine (NatTrans.isIso_app_iff_of_iso _ e').1 ?_
  obtain ⟨L, hL, hLK, i', hi'⟩ := exists_quasiIso_isKInjective_injective
    ((etaleModuleInverseImage.{u, 0} Λ g').mapCochainComplexPlus.obj I)
  have hTI : ∀ m, IsTorsionEtaleModule Λ X (I.obj.homology m) := fun m =>
    IsTorsionEtaleModule.of_iso Λ X
      ((DerivedCategory.homologyFunctor _ m).mapIso e'.symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ m).app I.obj) (hT m)
  -- the underived base change map enters both statements as an opaque variable, so that the
  -- kernel compares them without unfolding it
  obtain ⟨β, hβ⟩ : ∃ β, β = etaleModuleBaseChange.{u, 0} Λ f f' g g' sq.w.symm := ⟨_, rfl⟩
  exact isIso_etaleModuleDerivedBaseChangeUnbounded_app_of_isIso_Q_map.{u, 0} Λ f g g' f' sq.w
    β hβ I.obj hIK L.obj hLK i'.hom hi'
    (isIso_Q_map_etaleModuleBaseChange_comp_of_isProper Λ f sq I L i' hi' hTI β hβ)

end Stacks.EtaleCohomology

end
