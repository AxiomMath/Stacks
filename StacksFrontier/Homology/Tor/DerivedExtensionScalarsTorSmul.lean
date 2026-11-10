module

public import StacksFrontier.Algebra.Homology.LeftDerivedNatTransLinear
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTorObj

/-!
# The `R'`-action on `Tor` as functoriality in the first variable

For `R → R'` a homomorphism of commutative rings and `M` an `R`-module, the degree `-i`
cohomology of the derived extension of scalars of `M[0]` is an `R'`-module, and
`RingTheory.TorIndependence.derivedExtensionSingleIsoTor` identifies it, read over `R`, with
`Tor_i^R(R', M)`. Mathlib's `Tor` carries no `R'`-action; what plays its part is functoriality
of `Tor_i^R(·, M)` in its *first* variable, at multiplication by `r` on `R'`, and
`RingTheory.TorIndependence.derivedExtensionSingleIsoTor` matches the two.

## Main definitions

* `RingTheory.TorIndependence.mulByBase` and `RingTheory.TorIndependence.mulByAlg`:
  multiplication by `r : R'` on `R'` read as an `R`-module, in the two guises of `R'` that
  `RingTheory.TorIndependence.leftDerivedExtendRestrictIsoTor` passes through.

## Main results

* `RingTheory.TorIndependence.restrictScalars_map_smul_id`: the `R'`-action on an extension of
  scalars, read over `R`, is tensoring multiplication by `r` with the identity.
* `RingTheory.TorIndependence.leftDerivedExtendRestrictIsoTor_smul` and
  `RingTheory.TorIndependence.derivedExtensionSingleIsoTor_smul`: the identification with `Tor`
  carries the ambient `R'`-action to functoriality of `Tor` in its first variable.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u w

namespace RingTheory.TorIndependence

section Base

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/-- Multiplication by `r : R'` on `R'` read as an `R`-module along `R → R'`, that is on
`RingTheory.TorIndependence.baseModule`. It is the restriction of scalars of multiplication by
`r` on `R'` as an `R'`-module, so it is a scalar multiple of an identity before restriction. -/
def mulByBase (r : R') : baseModule R R' ⟶ baseModule R R' :=
  (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map (r • 𝟙 (ModuleCat.of R' R'))

/-- Multiplication by `r : R'` on `R'` read as an `R`-module through its `R`-algebra
structure. -/
def mulByAlg (r : R') : ModuleCat.of R R' ⟶ ModuleCat.of R R' :=
  ModuleCat.ofHom
    { toFun := fun x => r * x
      map_add' := fun x y => mul_add r x y
      map_smul' := fun s x => by
        simp only [RingHom.id_apply, Algebra.smul_def]
        ring }

/-- The two guises of multiplication by `r` on `R'` agree under
`RingTheory.TorIndependence.baseModuleIso`: on carriers that isomorphism is the identity. -/
theorem mulByBase_comp_baseModuleIso (r : R') :
    mulByBase (R := R) r ≫ (baseModuleIso (R := R) (R' := R')).hom =
      (baseModuleIso (R := R) (R' := R')).hom ≫ mulByAlg (R := R) r := by
  ext x
  rfl

/-- **The `R'`-action on an extension of scalars, read over `R`, is tensoring multiplication by
`r` with the identity.** Both sides send `s ⊗ n` to `(r * s) ⊗ n`. -/
theorem restrictScalars_map_smul_id (r : R') (N : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
        (r • 𝟙 ((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).obj N)) =
      ((tensoringLeft (ModuleCat.{u} R)).map (mulByBase (R := R) r)).app N :=
  ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl)

end Base

/-! ### A natural transformation read on a chosen projective resolution -/

section Resolution

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  [Abelian C] [HasProjectiveResolutions C] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]

/-- `CategoryTheory.ProjectiveResolution.leftDerived_app_eq` as a commuting square for
`RingTheory.TorIndependence.leftDerivedHomologyIso`. -/
theorem leftDerivedHomologyIso_hom_natTrans (α : F ⟶ G) {M : C} (P : ProjectiveResolution M)
    (i : ℕ) :
    (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i).map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) ≫
        (leftDerivedHomologyIso G P i).hom =
      (leftDerivedHomologyIso F P i).hom ≫ (NatTrans.leftDerived α i).app M := by
  dsimp only [leftDerivedHomologyIso, Iso.symm_hom]
  rw [ProjectiveResolution.leftDerived_app_eq α P i, Iso.inv_hom_id_assoc]

/-- The same square written with the inverses. -/
theorem leftDerivedHomologyIso_inv_natTrans (α : F ⟶ G) {M : C} (P : ProjectiveResolution M)
    (i : ℕ) :
    (NatTrans.leftDerived α i).app M ≫ (leftDerivedHomologyIso G P i).inv =
      (leftDerivedHomologyIso F P i).inv ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i).map
          ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) := by
  dsimp only [leftDerivedHomologyIso, Iso.symm_inv]
  rw [ProjectiveResolution.leftDerived_app_eq α P i, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- A scalar multiple of an identity, read on a chosen projective resolution: on both sides the
scalar acts through the ambient linear structure. -/
theorem leftDerivedHomologyIso_inv_smul_id {R : Type*} [Semiring R] [Linear R D]
    (F : C ⥤ D) [F.Additive] (r : R) {M : C} (P : ProjectiveResolution M) (i : ℕ) :
    (r • 𝟙 ((F.leftDerived i).obj M)) ≫ (leftDerivedHomologyIso F P i).inv =
      (leftDerivedHomologyIso F P i).inv ≫
        (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) i).map
          (r • 𝟙 ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)) := by
  have h := leftDerivedHomologyIso_inv_natTrans (r • 𝟙 F) P i
  rw [NatTrans.leftDerived_smul_id, NatTrans.app_smul, NatTrans.id_app,
    NatTrans.mapHomologicalComplex_smul, NatTrans.mapHomologicalComplex_id,
    NatTrans.app_smul, NatTrans.id_app] at h
  exact h

end Resolution

/-! ### The comparison of the two actions on a complex -/

/-- A functor carries an equation between composites to the equation between its images. -/
private theorem functor_map_comp_congr {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {X Y Z W : C} {f : X ⟶ Y} {g : Y ⟶ W} {f' : X ⟶ Z} {g' : Z ⟶ W}
    (h : f ≫ g = f' ≫ g') : F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, ← F.map_comp, h]

section Chain

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

/-- **The `R'`-action on the degreewise extension of scalars of a complex, read over `R`, is
the degreewise tensor of multiplication by `r` with the identity.** -/
theorem extendRestrict_smul_id_square (r : R')
    (K : HomologicalComplex (ModuleCat.{u} R) (ComplexShape.down ℕ)) :
    ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.down ℕ)).map
        (r • 𝟙 (((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj K)) ≫
      (Functor.mapHomologicalComplexCompIso
        (extendRestrictIsoTensorLeft (R := R) (R' := R')) (ComplexShape.down ℕ)).hom.app K =
    (Functor.mapHomologicalComplexCompIso
        (extendRestrictIsoTensorLeft (R := R) (R' := R')) (ComplexShape.down ℕ)).hom.app K ≫
      (NatTrans.mapHomologicalComplex
        ((tensoringLeft (ModuleCat.{u} R)).map (mulByBase (R := R) r))
        (ComplexShape.down ℕ)).app K := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  change (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
        (r • 𝟙 ((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).obj (K.X n))) ≫ 𝟙 _ =
      𝟙 _ ≫ ((tensoringLeft (ModuleCat.{u} R)).map (mulByBase (R := R) r)).app (K.X n)
  rw [Category.comp_id, Category.id_comp, restrictScalars_map_smul_id]

/-- **The `R'`-action on the `i`-th left derived functor of extension of scalars is
functoriality of `Tor` in its first variable at multiplication by `r`**, computed on a chosen
projective resolution. -/
theorem leftDerivedExtendRestrictIsoTorOfResolution_smul (r : R') (i : ℕ)
    {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
          (r • 𝟙 (((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).leftDerived i).obj M)) ≫
        (leftDerivedExtendRestrictIsoTorOfResolution (R := R) (R' := R') P i).hom =
      (leftDerivedExtendRestrictIsoTorOfResolution (R := R) (R' := R') P i).hom ≫
        (NatTrans.leftDerived
          ((tensoringLeft (ModuleCat.{u} R)).map (mulByBase (R := R) r)) i).app M := by
  have k1 := functor_map_comp_congr (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R'))
    (leftDerivedHomologyIso_inv_smul_id
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')) r P i)
  have k2 := (restrictHomologyIso (R := R) (R' := R') i).inv.naturality
    (r • 𝟙 (((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex))
  dsimp only [Functor.comp_map] at k2
  have k3 := functor_map_comp_congr
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) i)
    (extendRestrict_smul_id_square (R := R) (R' := R') r P.complex)
  have k4 := leftDerivedHomologyIso_hom_natTrans
    ((tensoringLeft (ModuleCat.{u} R)).map (mulByBase (R := R) r)) P i
  dsimp only [leftDerivedExtendRestrictIsoTorOfResolution, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, extendRestrictHomologyIso, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  simp only [Category.assoc]
  rw [reassoc_of% k1, reassoc_of% k2, reassoc_of% k3, k4]

/-- The transport of `Tor` along `RingTheory.TorIndependence.baseModuleIso`, with its source
written as the left derived functor of tensoring rather than as a value of `Tor`. -/
def baseModuleTransport (i : ℕ) :
    (tensorLeft (baseModule R R')).leftDerived i ⟶
      (Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R') :=
  (Tor (ModuleCat.{u} R) i).map (baseModuleIso (R := R) (R' := R')).hom

/-- The component of `RingTheory.TorIndependence.leftDerivedExtendRestrictIsoTor` at `M`: the
chain through the chosen projective resolution of `M`, then the transport along
`RingTheory.TorIndependence.baseModuleIso`. -/
theorem leftDerivedExtendRestrictIsoTor_hom_app (i : ℕ) (M : ModuleCat.{u} R) :
    (leftDerivedExtendRestrictIsoTor (R := R) (R' := R') i).hom.app M =
      (leftDerivedExtendRestrictIsoTorOfResolution (R := R) (R' := R')
          (ProjectiveResolution.of M) i).hom ≫
        (baseModuleTransport (R := R) (R' := R') i).app M :=
  rfl

/-- **The identification of the derived extension of scalars with `Tor` carries the `R'`-action
to functoriality of `Tor` in its first variable.** -/
theorem leftDerivedExtendRestrictIsoTor_smul (r : R') (i : ℕ) (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
          (r • 𝟙 (((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).leftDerived i).obj M)) ≫
        (leftDerivedExtendRestrictIsoTor (R := R) (R' := R') i).hom.app M =
      (leftDerivedExtendRestrictIsoTor (R := R) (R' := R') i).hom.app M ≫
        ((Tor (ModuleCat.{u} R) i).map (mulByAlg (R := R) r)).app M := by
  have h1 := leftDerivedExtendRestrictIsoTorOfResolution_smul (R := R) (R' := R') r i
    (ProjectiveResolution.of M)
  have hmap : NatTrans.leftDerived
          ((tensoringLeft (ModuleCat.{u} R)).map (mulByBase (R := R) r)) i ≫
        baseModuleTransport (R := R) (R' := R') i =
      baseModuleTransport (R := R) (R' := R') i ≫
        (Tor (ModuleCat.{u} R) i).map (mulByAlg (R := R) r) :=
    functor_map_comp_congr (Tor (ModuleCat.{u} R) i)
      (mulByBase_comp_baseModuleIso (R := R) (R' := R') r)
  have h2 := congrArg (fun ψ => NatTrans.app ψ M) hmap
  simp only [NatTrans.comp_app] at h2
  rw [leftDerivedExtendRestrictIsoTor_hom_app, ← Category.assoc, h1, Category.assoc, h2,
    ← Category.assoc]

/-! ### Derived extension of scalars of `M[0]` -/

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- The component of `RingTheory.TorIndependence.derivedExtensionSingleIsoTor` at `M`. -/
theorem derivedExtensionSingleIsoTor_hom_app (i : ℕ) (M : ModuleCat.{u} R) :
    (derivedExtensionSingleIsoTor (R := R) (R' := R') i).hom.app M =
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
          ((derivedExtensionSingleIsoLeftDerived (algebraMap R R') i).hom.app M) ≫
        (leftDerivedExtendRestrictIsoTor (R := R) (R' := R') i).hom.app M :=
  rfl

/-- **The identification `RingTheory.TorIndependence.derivedExtensionSingleIsoTor` carries the
ambient `R'`-action at `M[0]` to functoriality of `Tor` in its first variable.** -/
theorem derivedExtensionSingleIsoTor_smul (r : R') (i : ℕ) (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')).map
          (r • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
            (totalDerivedExtensionScalars.{u, u, u, w, w} (algebraMap R R')).functor ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).obj M)) ≫
        (derivedExtensionSingleIsoTor (R := R) (R' := R') i).hom.app M =
      (derivedExtensionSingleIsoTor (R := R) (R' := R') i).hom.app M ≫
        ((Tor (ModuleCat.{u} R) i).map (mulByAlg (R := R) r)).app M := by
  have hsq := functor_map_comp_congr (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R'))
    (show (r • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
          (totalDerivedExtensionScalars.{u, u, u, w, w} (algebraMap R R')).functor ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).obj M)) ≫
        (derivedExtensionSingleIsoLeftDerived (algebraMap R R') i).hom.app M =
      (derivedExtensionSingleIsoLeftDerived (algebraMap R R') i).hom.app M ≫
        (r • 𝟙 (((ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).leftDerived i).obj M)) by
      rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id])
  rw [derivedExtensionSingleIsoTor_hom_app, ← Category.assoc, hsq, Category.assoc,
    leftDerivedExtendRestrictIsoTor_smul, ← Category.assoc]

end Chain

end RingTheory.TorIndependence

end
