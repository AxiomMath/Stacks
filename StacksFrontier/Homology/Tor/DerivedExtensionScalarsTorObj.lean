module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTor

/-!
# Derived extension of scalars of a module is `Tor`

For `R → R'` a homomorphism of commutative rings and `M` an `R`-module, the `i`-th left derived
functor of extension of scalars, read back over `R`, is `Tor_i^R(R', M)`: extension of scalars
followed by restriction is tensoring with `R'`, and restriction of scalars is exact.

Combined with `RingTheory.TorIndependence.derivedExtensionSingleIsoLeftDerived` this gives

`H^{-i}(ext^L_{R → R'}(M[0])) ≅ Tor_i^R(R', M)`, naturally in `M`.

## Main definitions

* `RingTheory.TorIndependence.baseModule`: `R'` read as an `R`-module along `R → R'`.
* `RingTheory.TorIndependence.extendRestrictIsoTensorLeft`: extension of scalars followed by
  restriction of scalars is tensoring with that `R`-module.
* `RingTheory.TorIndependence.leftDerivedExtendRestrictIsoTor`: the `i`-th left derived functor
  of extension of scalars, read over `R`, is `Tor_i^R(R', ·)`.
* `RingTheory.TorIndependence.derivedExtensionSingleIsoTor`: the natural isomorphism
  `H^{-i}(ext^L_{R → R'}(M[0])) ≅ Tor_i^R(R', M)` of `R`-modules.

## Implementation notes

The `R`-module `R'` appears in two guises. As `RingTheory.TorIndependence.baseModule`, that is
`(ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')`, it is the `R`-module
the carrier of `ModuleCat.extendScalars` is a tensor product with, and `extend ⋙ restrict` is
`tensorLeft` of it by `Iso.refl`. As `ModuleCat.of R R'` it is the first argument of `Tor`; the
two are identified by `RingTheory.TorIndependence.baseModuleIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u w v₁ v₂ u₁ u₂

namespace RingTheory.TorIndependence

/-! ### Left derived functors on a chosen projective resolution -/

section LeftDerived

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Abelian C] [HasProjectiveResolutions C] [Abelian D]

/-- The `i`-th left derived functor of `F` at `M`, read as the homology of `F` applied to a
projective resolution of `M`. This is
`CategoryTheory.ProjectiveResolution.isoLeftDerivedObj` with its source written as a homology
rather than as the homology functor applied to a complex. -/
def leftDerivedHomologyIso (F : C ⥤ D) [F.Additive] {M : C} (P : ProjectiveResolution M)
    (i : ℕ) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i).obj P.complex ≅
      (F.leftDerived i).obj M :=
  (P.isoLeftDerivedObj F i).symm

/-- `leftDerivedHomologyIso` is natural in `M`, along a morphism `φ` of projective resolutions
lifting `g : M ⟶ N`. -/
theorem leftDerivedHomologyIso_hom_naturality (F : C ⥤ D) [F.Additive] {M N : C} (g : M ⟶ N)
    (P : ProjectiveResolution M) (P' : ProjectiveResolution N) (φ : P.complex ⟶ P'.complex)
    (comm : φ.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ g) (i : ℕ) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i).map φ ≫
        (leftDerivedHomologyIso F P' i).hom =
      (leftDerivedHomologyIso F P i).hom ≫ (F.leftDerived i).map g :=
  (ProjectiveResolution.isoLeftDerivedObj_inv_naturality g P P' φ comm F i).symm

end LeftDerived

/-! ### Extension of scalars followed by restriction -/

section ExtendRestrict

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/-- `R'` read as an `R`-module along `R → R'`. This is the guise of `R'` in which it appears
inside `ModuleCat.extendScalars`. -/
abbrev baseModule (R R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] :
    ModuleCat.{u} R :=
  (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).obj (ModuleCat.of R' R')

/-- **Extension of scalars followed by restriction of scalars is tensoring with `R'`.** With
`R'` read as an `R`-module by restriction of scalars, the two functors are the same: the carrier
of `ModuleCat.extendScalars` is by definition the tensor product with that `R`-module, and the
`R`-action of restriction of scalars is the one it carries. -/
def extendRestrictIsoTensorLeft :
    ModuleCat.extendScalars.{u, u, u} (algebraMap R R') ⋙
        ModuleCat.restrictScalars.{u, u, u} (algebraMap R R') ≅
      tensorLeft (baseModule R R') :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- `R'` read as an `R`-module along `R → R'` is `R'` with its `R`-algebra module structure: the
identity map, `R`-linear by `Algebra.smul_def`. -/
def restrictSelfLinearEquiv :
    ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).obj
      (ModuleCat.of R' R')) ≃ₗ[R] R' :=
  { AddEquiv.refl R' with
    map_smul' := fun r a => (Algebra.smul_def (R := R) (A := R') r a).symm }

/-- The same identification, as an isomorphism of `R`-modules. -/
def baseModuleIso : baseModule R R' ≅ ModuleCat.of R R' :=
  LinearEquiv.toModuleIso (restrictSelfLinearEquiv (R := R) (R' := R'))

end ExtendRestrict

/-! ### `Tor` from a projective resolution -/

section Tor

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/-- Mathlib's `Tor` in the first variable is the left derived functor of tensoring. -/
theorem tor_obj_eq (X : ModuleCat.{u} R) (i : ℕ) :
    (Tor (ModuleCat.{u} R) i).obj X = (tensorLeft X).leftDerived i :=
  rfl

/-- Restriction of scalars commutes with the homology of complexes, degreewise: it is exact. -/
def restrictHomologyIso (i : ℕ) :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.down ℕ) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) i ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R') (ComplexShape.down ℕ) i ⋙
        ModuleCat.restrictScalars.{u, u, u} (algebraMap R R') :=
  StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')) (ComplexShape.down ℕ) i

/-- The identification of `extend ⋙ restrict` with `tensorLeft R'`, read on the homology of
complexes. -/
def extendRestrictHomologyIso (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.down ℕ) ⋙
        (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.down ℕ)) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) i ≅
      (tensorLeft (baseModule R R')).mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) i :=
  Functor.isoWhiskerRight
    (Functor.mapHomologicalComplexCompIso (extendRestrictIsoTensorLeft (R := R) (R' := R'))
      (ComplexShape.down ℕ)) _

/-- **The `i`-th left derived functor of extension of scalars, read over `R`, is
`Tor_i^R(R', ·)`**, computed on a projective resolution. -/
def leftDerivedExtendRestrictIsoTorOfResolution {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (i : ℕ) :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).obj
        (((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).leftDerived i).obj M) ≅
      ((tensorLeft (baseModule R R')).leftDerived i).obj M :=
  (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).mapIso
      (leftDerivedHomologyIso (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')) P i).symm ≪≫
    (restrictHomologyIso (R := R) (R' := R') i).symm.app
      (((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex) ≪≫
    (extendRestrictHomologyIso (R := R) (R' := R') i).app P.complex ≪≫
    leftDerivedHomologyIso (tensorLeft (baseModule R R')) P i

/-- The identification is natural in `M`, along any lift of `g` to the two chosen
resolutions. -/
theorem leftDerivedExtendRestrictIsoTorOfResolution_hom_naturality {M N : ModuleCat.{u} R}
    (g : M ⟶ N) (P : ProjectiveResolution M) (P' : ProjectiveResolution N)
    (φ : P.complex ⟶ P'.complex) (comm : φ.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ g) (i : ℕ) :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
          (((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).leftDerived i).map g) ≫
        (leftDerivedExtendRestrictIsoTorOfResolution P' i).hom =
      (leftDerivedExtendRestrictIsoTorOfResolution P i).hom ≫
        ((tensorLeft (baseModule R R')).leftDerived i).map g := by
  have k1 : (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
        (((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).leftDerived i).map g) ≫
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
        (leftDerivedHomologyIso
          (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')) P' i).inv =
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
        (leftDerivedHomologyIso
          (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')) P i).inv ≫
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
        (((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.down ℕ) ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R')
            (ComplexShape.down ℕ) i).map φ) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    refine congrArg _ ?_
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    exact (leftDerivedHomologyIso_hom_naturality
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')) g P P' φ comm i).symm
  have k2 := (restrictHomologyIso (R := R) (R' := R') i).inv.naturality
    (((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.down ℕ)).map φ)
  have k3 := (extendRestrictHomologyIso (R := R) (R' := R') i).hom.naturality φ
  dsimp only [leftDerivedExtendRestrictIsoTorOfResolution, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [reassoc_of% k1, reassoc_of% k2, reassoc_of% k3]
  exact congrArg _ <| congrArg _ <| congrArg _
    (leftDerivedHomologyIso_hom_naturality (tensorLeft (baseModule R R')) g P P' φ comm i)

/-- **The `i`-th left derived functor of extension of scalars, read over `R`, is
`Tor_i^R(R', ·)`.** -/
def leftDerivedExtendRestrictIsoTor (i : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).leftDerived i ⋙
        ModuleCat.restrictScalars.{u, u, u} (algebraMap R R') ≅
      (Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R') :=
  NatIso.ofComponents
    (fun M => leftDerivedExtendRestrictIsoTorOfResolution (ProjectiveResolution.of M) i)
    (fun {M N} g => leftDerivedExtendRestrictIsoTorOfResolution_hom_naturality g
      (ProjectiveResolution.of M) (ProjectiveResolution.of N)
      (ProjectiveResolution.lift g _ _) (ProjectiveResolution.lift_commutes_zero g _ _) i) ≪≫
    (Tor (ModuleCat.{u} R) i).mapIso (baseModuleIso (R := R) (R' := R'))

/-! ### Derived extension of scalars and `Tor` -/

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- **The cohomology of a derived extension of scalars is `Tor`.** For every `i`,

`H^{-i}(ext^L_{R → R'}(M[0])) ≅ Tor_i^R(R', M)`,

naturally in `M`, the left-hand side being read over `R` by restriction of scalars. -/
def derivedExtensionSingleIsoTor (i : ℕ) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
          (totalDerivedExtensionScalars.{u, u, u, w, w} (algebraMap R R')).functor ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))) ⋙
        ModuleCat.restrictScalars.{u, u, u} (algebraMap R R') ≅
      (Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R') :=
  Functor.isoWhiskerRight
      (derivedExtensionSingleIsoLeftDerived (algebraMap R R') i)
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')) ≪≫
    leftDerivedExtendRestrictIsoTor i

end Tor

end RingTheory.TorIndependence

end
