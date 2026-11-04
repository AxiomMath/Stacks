module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.Homology.HomotopyCategory.QuasiIsoAlongExactFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayPreimageSectionsQuasiIso

/-!
# Linear derived global sections of a derived pushforward

Let
```
X' --i--> X
|         |
f'        f
v         v
Spec A' --> Spec A
```
be a commutative square of schemes, the bottom arrow being `Spec` of a ring map `φ : A ⟶ A'`.
Then `RΓ(X, Ri_* M) = RΓ(X', M)` as objects of `D(A)`, the right-hand side being read over `A`
by restriction of scalars along `φ`:

`Ri_* ⋙ RΓ_A(X, -) ≅ RΓ_{A'}(X', -) ⋙ (φ^*)`

as functors `D(𝒪_{X'}) ⥤ D(A)`. This is the Leray isomorphism [Stacks, Tag 0D5W] with the
linear structures of both sides taken into account.

## Main definitions

* `AlgebraicGeometry.pushforwardGlobalSectionsOverRestrictScalarsIso` — the underived
  identification `Γ_A(X, i_* -) ≅ φ^* Γ_{A'}(X', -)`.
* `AlgebraicGeometry.derivedGlobalSectionsOverPushforwardRestrictScalarsIso` — the derived
  identification, for every model of the derived categories and every right derived functor
  `Ri_*` of `i_*`.
* `AlgebraicGeometry.derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso` — the same
  for the derived pushforward
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` of ringed spaces, at the
  standard model where that functor is defined.

## Main results

* `AlgebraicGeometry.isIso_derivedGlobalSectionsOverUnit_app_pushforward` — the direct image of
  a K-injective complex computes `RΓ_A(X, -)`, for every model.
* `AlgebraicGeometry.derivedGlobalSectionsOverPushforwardRestrictScalarsIso_fac` — the equation
  characterizing the derived identification through the units of the derived functors.

## Implementation notes

Both functors are right derived functors of `Γ_A(X, i_* -) ≅ φ^* Γ_{A'}(X', -)`, and the
identification is the induced isomorphism of right derived functors.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w₁ w₂ w₃ w₄ u

namespace AlgebraicGeometry

variable {A A' : Type u} [CommRing A] [CommRing A'] {X X' : Scheme.{u}}
  (i : X' ⟶ X) (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (φ : A →+* A')

/-- The two ring maps `A ⟶ Γ(X', 𝒪_{X'})` of the square agree. -/
theorem globalSectionsOver_ringHom_comp_eq (h : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ)) :
    (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop) ≫ i.appTop).hom =
      ((Scheme.ΓSpecIso (.of A')).inv ≫ f'.appTop).hom.comp φ := by
  have h' := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h'
  rw [Category.assoc, h', ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- **Global sections of a direct image.** `Γ_A(X, i_* ℱ) = Γ(X', ℱ)` read over `A` through
`A ⟶ Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})`, which by the commutativity of the square is
`φ^* Γ_{A'}(X', ℱ)`. -/
def pushforwardGlobalSectionsOverRestrictScalarsIso
    (h : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ)) :
    Scheme.Modules.pushforward i ⋙ globalSectionsOver f ≅
      globalSectionsOver f' ⋙ ModuleCat.restrictScalars φ :=
  Functor.isoWhiskerLeft (SheafOfModules.evaluation X'.ringCatSheaf (op ⊤))
    (ModuleCat.restrictScalarsComp' φ ((Scheme.ΓSpecIso (.of A')).inv ≫ f'.appTop).hom
      (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop) ≫ i.appTop).hom
      (globalSectionsOver_ringHom_comp_eq i f f' φ h))

/-- The functor `Γ_A(X, i_* -)` is additive. -/
instance : (Scheme.Modules.pushforward i ⋙ globalSectionsOver f).Additive where
  map_add := rfl

/-- The functor `φ^* Γ_{A'}(X', -)` is additive. -/
instance : (globalSectionsOver f' ⋙ ModuleCat.restrictScalars φ).Additive where
  map_add := rfl

/-! ### The derived identification -/

section Derived

variable [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} X'.Modules]
  [HasDerivedCategory.{w₃} (ModuleCat.{u} A)] [HasDerivedCategory.{w₄} (ModuleCat.{u} A')]

/-- A right derived unit on the homotopy category of `Y.Modules` is invertible at a K-injective
complex. -/
private theorem isIso_unit_app_of_isKInjective {Y : Scheme.{u}} {H : Type*} [Category H]
    [HasDerivedCategory.{w₁} Y.Modules]
    (F : HomotopyCategory Y.Modules (ComplexShape.up ℤ) ⥤ H)
    (RF : DerivedCategory Y.Modules ⥤ H) (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))]
    (I : CochainComplex Y.Modules ℤ) (hI : I.IsKInjective) :
    IsIso (α.app ((HomotopyCategory.quotient Y.Modules (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective F
    (Scheme.Modules.exists_quasiIso_isKInjective Y)).2 DerivedCategory.Qh RF α I hI

omit [HasDerivedCategory X'.Modules] in
/-- **The direct image of a K-injective complex computes `RΓ_A(X, -)`**, at every model of the
derived categories: for a K-injective complex `I` of `𝒪_{X'}`-modules, the unit of
`RΓ_A(X, -)` is invertible at `i_* I`. -/
theorem isIso_derivedGlobalSectionsOverUnit_app_pushforward
    (I : CochainComplex X'.Modules ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedGlobalSectionsOverUnit f).app
      (((Scheme.Modules.pushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient X'.Modules (ComplexShape.up ℤ)).obj I))) := by
  obtain ⟨J, g, hJ, hg⟩ := Scheme.Modules.exists_quasiIso_isKInjective X
    (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  let s : ((Scheme.Modules.pushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient X'.Modules (ComplexShape.up ℤ)).obj I) ⟶
      (HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj J :=
    (HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).map g
  have hs : HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ) s :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff g).2 hg
  have hpre :=
    Stacks.Cohomology.DerivedSectionsLeray.quasiIso_preimageSections_map_pushforward_of_isKInjective
      i.toLRSHom.toShHom f.toLRSHom.toShHom ⊤ I hI J hJ s hs
  have hres := Functor.quasiIso_mapHomotopyCategory_map (ComplexShape.up ℤ)
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom) _ hpre
  have hΓ : HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
      (((globalSectionsOver f).mapHomotopyCategory (ComplexShape.up ℤ)).map s) :=
    ((HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoOfNatIso (Functor.mapHomotopyCategoryCompIso (Iso.refl
        (Stacks.Cohomology.DerivedSectionsLeray.preimageSections f.toLRSHom.toShHom ⊤ ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom)) (ComplexShape.up ℤ))
        (Arrow.mk s))).1 hres
  have h₁ := isIso_unit_app_of_isKInjective (homotopyGlobalSectionsOver f)
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f) J hJ
  have : IsIso (DerivedCategory.Qh.map s) := Localization.inverts DerivedCategory.Qh _ s hs
  have : IsIso (DerivedCategory.Qh.map
      (((globalSectionsOver f).mapHomotopyCategory (ComplexShape.up ℤ)).map s)) :=
    (DerivedCategory.isIso_Qh_map_iff _).2 hΓ
  have h₂ : IsIso ((homotopyGlobalSectionsOver f).map s ≫
      (derivedGlobalSectionsOverUnit f).app
        ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj J)) := by
    dsimp only [homotopyGlobalSectionsOver, Functor.comp_map]
    infer_instance
  rw [(derivedGlobalSectionsOverUnit f).naturality s] at h₂
  have : IsIso ((DerivedCategory.Qh ⋙ derivedGlobalSectionsOver f).map s) := by
    dsimp only [Functor.comp_map]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h₂

variable (Ri : DerivedCategory X'.Modules ⥤ DerivedCategory X.Modules)
  (αi : (Scheme.Modules.pushforward i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ri)

/-- The comparison exhibiting `Ri_* ⋙ RΓ_A(X, -)` as a right derived functor of
`Γ_A(X, i_* -)`: the unit of `RΓ_A(X, -)` at a direct image, followed by the image of the unit
`αi` of `Ri_*`. -/
def derivedGlobalSectionsOverPushforwardUnit :
    (Scheme.Modules.pushforward i ⋙ globalSectionsOver f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ (Ri ⋙ derivedGlobalSectionsOver f) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (Scheme.Modules.pushforward i ⋙ globalSectionsOver f)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft ((Scheme.Modules.pushforward i).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedGlobalSectionsOverUnit f) ≫
    Functor.whiskerRight αi (derivedGlobalSectionsOver f)

/-- `Ri_* ⋙ RΓ_A(X, -)` is a right derived functor of `Γ_A(X, i_* -)`, for every right derived
functor `Ri_*` of `i_*` and every model. -/
theorem isRightDerivedFunctor_derivedGlobalSectionsOverPushforward
    [Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ))] :
    (Ri ⋙ derivedGlobalSectionsOver f).IsRightDerivedFunctor
      (derivedGlobalSectionsOverPushforwardUnit i f Ri αi)
      (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ (Scheme.Modules.exists_quasiIso_isKInjective X') DerivedCategory.Qh _ _ fun I hI => by
      have := isIso_derivedGlobalSectionsOverUnit_app_pushforward i f I hI
      have := isIso_unit_app_of_isKInjective _ Ri αi I hI
      dsimp only [derivedGlobalSectionsOverPushforwardUnit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance

/-- The comparison exhibiting `RΓ_{A'}(X', -) ⋙ φ^*` as a right derived functor of
`φ^* Γ_{A'}(X', -)`: the unit of `RΓ_{A'}(X', -)`, followed by the exact functor `φ^*`. -/
def derivedGlobalSectionsOverRestrictScalarsUnit :
    (globalSectionsOver f' ⋙ ModuleCat.restrictScalars φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        (derivedGlobalSectionsOver f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (globalSectionsOver f' ⋙ ModuleCat.restrictScalars φ)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    Functor.whiskerLeft ((globalSectionsOver f').mapHomotopyCategory (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars φ).mapDerivedCategoryFactorsh.inv ≫
    Functor.whiskerRight (derivedGlobalSectionsOverUnit f')
      (ModuleCat.restrictScalars φ).mapDerivedCategory

/-- `RΓ_{A'}(X', -) ⋙ φ^*` is a right derived functor of `φ^* Γ_{A'}(X', -)`. -/
theorem isRightDerivedFunctor_derivedGlobalSectionsOverRestrictScalars :
    (derivedGlobalSectionsOver f' ⋙
        (ModuleCat.restrictScalars φ).mapDerivedCategory).IsRightDerivedFunctor
      (derivedGlobalSectionsOverRestrictScalarsUnit f' φ)
      (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ (Scheme.Modules.exists_quasiIso_isKInjective X') DerivedCategory.Qh _ _ fun I hI => by
      have := isIso_unit_app_of_isKInjective _ (derivedGlobalSectionsOver f')
        (derivedGlobalSectionsOverUnit f') I hI
      dsimp only [derivedGlobalSectionsOverRestrictScalarsUnit, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app]
      infer_instance

/-- **`RΓ_A(X, Ri_* M) = φ^* RΓ_{A'}(X', M)`, naturally in `M`** ([Stacks, Tag 0D5W] with the
linear structures). For a commutative square `i ≫ f = f' ≫ Spec φ`, every model of the derived
categories and every right derived functor `Ri_*` of `i_*`, the two functors
`D(𝒪_{X'}) ⥤ D(A)` are isomorphic: both are right derived functors of
`Γ_A(X, i_* -) ≅ φ^* Γ_{A'}(X', -)` (`pushforwardGlobalSectionsOverRestrictScalarsIso`), and
this is the isomorphism they induce. -/
def derivedGlobalSectionsOverPushforwardRestrictScalarsIso
    [Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ))]
    (h : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ)) :
    Ri ⋙ derivedGlobalSectionsOver f ≅
      derivedGlobalSectionsOver f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory :=
  have := isRightDerivedFunctor_derivedGlobalSectionsOverPushforward i f Ri αi
  have := isRightDerivedFunctor_derivedGlobalSectionsOverRestrictScalars f' φ
  Functor.rightDerivedNatIso _ _ (derivedGlobalSectionsOverPushforwardUnit i f Ri αi)
    (derivedGlobalSectionsOverRestrictScalarsUnit f' φ)
    (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight (Stacks.Homology.mapHomotopyCategoryIso
      (pushforwardGlobalSectionsOverRestrictScalarsIso i f f' φ h) (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- The equation characterizing `derivedGlobalSectionsOverPushforwardRestrictScalarsIso`: on the
units of the two right derived functors it is the underived identification
`Γ_A(X, i_* -) ≅ φ^* Γ_{A'}(X', -)`. -/
theorem derivedGlobalSectionsOverPushforwardRestrictScalarsIso_fac
    [Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ))]
    (h : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ)) :
    derivedGlobalSectionsOverPushforwardUnit i f Ri αi ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (derivedGlobalSectionsOverPushforwardRestrictScalarsIso i f f' φ Ri αi h).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory
          (pushforwardGlobalSectionsOverRestrictScalarsIso i f f' φ h).hom (ComplexShape.up ℤ))
          DerivedCategory.Qh ≫
        derivedGlobalSectionsOverRestrictScalarsUnit f' φ := by
  have := isRightDerivedFunctor_derivedGlobalSectionsOverPushforward i f Ri αi
  have := isRightDerivedFunctor_derivedGlobalSectionsOverRestrictScalars f' φ
  exact Functor.rightDerivedNatTrans_fac (Ri ⋙ derivedGlobalSectionsOver f)
    (derivedGlobalSectionsOver f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory)
    (derivedGlobalSectionsOverPushforwardUnit i f Ri αi)
    (derivedGlobalSectionsOverRestrictScalarsUnit f' φ)
    (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ)) _

end Derived

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`RΓ_A(X, Ri_* M) = φ^* RΓ_{A'}(X', M)` for the derived pushforward of ringed spaces.**
`derivedGlobalSectionsOverPushforwardRestrictScalarsIso` for `Ri_*` the derived pushforward
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward` along `i` (the `Ri_*` of
[Stacks, Tag 0A1J] and of [Stacks, Tag 08EU] in this library), at the standard model of the
derived categories, which is the only model at which that functor is defined. -/
def derivedGlobalSectionsOverDerivedPushforwardRestrictScalarsIso
    (h : i ≫ f = f' ≫ Spec.map (CommRingCat.ofHom φ)) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom :
        DerivedCategory X'.Modules ⥤ DerivedCategory X.Modules) ⋙ derivedGlobalSectionsOver f ≅
      derivedGlobalSectionsOver f' ⋙ (ModuleCat.restrictScalars φ).mapDerivedCategory :=
  let Ri : DerivedCategory X'.Modules ⥤ DerivedCategory X.Modules :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom
  let αi : (Scheme.Modules.pushforward i).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Ri :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit i.toLRSHom.toShHom
  haveI : Ri.IsRightDerivedFunctor αi (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ)) :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isRightDerivedFunctor_of_isIso_app_isKInjective
      _ (Scheme.Modules.exists_quasiIso_isKInjective X') DerivedCategory.Qh _ _ fun I hI =>
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.isIso_derivedPushforwardUnit_app_of_isKInjective
          i.toLRSHom.toShHom I hI
  derivedGlobalSectionsOverPushforwardRestrictScalarsIso i f f' φ Ri αi h

end AlgebraicGeometry

end
