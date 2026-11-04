module

public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.System
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionComplexLevel
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTildeComposition
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.LimitHomDescent.ComplexCocycle

/-!
# Derived pullback of an associated complex along a map of spectra

For a ring map `f : R ⟶ A` and a K-flat complex `C` of `R`-modules, the derived pullback along
`Spec f` of the derived sheafification of `C` is the derived sheafification of the extension of
scalars `A ⊗_R C`:

`Θ_f(C) : L(Spec f)^*(C̃) ≅ (A ⊗_R C)~`.

It is built from the comparison of the derived pullback with the degreewise pullback, which is
invertible at the K-flat complex `C̃`, and from the degreewise isomorphism of Stacks 01I9. This
file proves that `Θ` is natural in `C` and that it satisfies the cocycle identity along a
factorisation `f ≫ β = f'`.

## Main definitions

* `Stacks.LimitHomDescent.Affine.Θ`: the isomorphism above.
* `Stacks.LimitHomDescent.Affine.extComp`: `A' ⊗_A (A ⊗_R C) ≅ A' ⊗_R C`, degreewise.

## Main results

* `Stacks.LimitHomDescent.Affine.Θ_naturality`: naturality in `C`.
* `Stacks.LimitHomDescent.Affine.Θ_cocycle`: the cocycle identity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback (schemeFactorIso schemeFactorHom)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.LimitHomDescent.Affine

variable {R A A' : CommRingCat.{u}}

/-- Extension of scalars along a ring map is an additive functor. -/
instance extendScalars_additive (f : R ⟶ A) :
    (ModuleCat.extendScalars.{u, u, u} f.hom).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom).left_adjoint_additive

/-- Extension of scalars along `f`, degreewise on complexes. -/
abbrev ext (f : R ⟶ A) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  (ModuleCat.extendScalars.{u, u, u} f.hom).mapHomologicalComplex (ComplexShape.up ℤ)

variable (f : R ⟶ A)

/-- Extension of scalars along `f` sends a K-flat complex of `R`-modules to a K-flat complex of
`A`-modules. -/
theorem kFlat_ext (C : CochainComplex (ModuleCat.{u} R) ℤ) (hC : C.KFlat) :
    ((ext f).obj C).KFlat :=
  CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u, u, u} f.hom C hC

/-- The comparison of the derived pullback along `Spec f` with the degreewise pullback is an
isomorphism at the associated complex of a K-flat complex `C`. -/
theorem isIso_tildeDerivedPullbackComparison_app (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (hC : C.KFlat) :
    IsIso ((StandardModel.tildeDerivedPullbackComparison R A f).app C) := by
  have h1 : IsIso ((StandardModel.tildeDerivedPullbackFactor R A f).hom.app C) :=
    ((StandardModel.tildeDerivedPullbackFactor R A f).app C).isIso_hom
  dsimp only [StandardModel.tildeDerivedPullbackComparison]
  rw [NatTrans.comp_app]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ h1 ?_
  exact StandardModel.isIso_derivedPullbackComplexComparison_app_of_kFlat
    (Spec.map f).toLRSHom.toShHom _ (Stacks.TildeStalk.kFlatTilde R C hC)

/-- **`L(Spec f)^*(C̃) ≅ (A ⊗_R C)~`** for a K-flat complex `C` of `R`-modules. -/
def Θ (C : CochainComplex (ModuleCat.{u} R) ℤ) (hC : C.KFlat) :
    (StandardModel.specDerivedPullback f).obj
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj C)) ≅
      (tilde.functor A).mapDerivedCategory.obj (DerivedCategory.Q.obj ((ext f).obj C)) :=
  @asIso _ _ _ _ ((StandardModel.tildeDerivedPullbackComparison R A f).app C)
      (isIso_tildeDerivedPullbackComparison_app f C hC) ≪≫
    (StandardModel.tildePullbackComplexCompQIso R A f).app C ≪≫
    ((tilde.functor A).mapDerivedCategoryFactors.app ((ext f).obj C)).symm

/-- **`Θ` is natural in the complex.** -/
theorem Θ_naturality {C C' : CochainComplex (ModuleCat.{u} R) ℤ} (hC : C.KFlat) (hC' : C'.KFlat)
    (h : C ⟶ C') :
    (StandardModel.specDerivedPullback f).map
        ((tilde.functor R).mapDerivedCategory.map (DerivedCategory.Q.map h)) ≫
        (Θ f C' hC').hom =
      (Θ f C hC).hom ≫
        (tilde.functor A).mapDerivedCategory.map (DerivedCategory.Q.map ((ext f).map h)) := by
  have n1 := (StandardModel.tildeDerivedPullbackComparison R A f).naturality h
  have n2 := (StandardModel.tildePullbackComplexCompQIso R A f).hom.naturality h
  have n3 := (tilde.functor A).mapDerivedCategoryFactors.inv.naturality ((ext f).map h)
  simp only [Functor.comp_map] at n1 n2 n3
  simp only [Θ, Iso.trans_hom, asIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
  rw [reassoc_of% n1, reassoc_of% n2, n3]

variable (β : A ⟶ A')

/-- `Spec β ≫ Spec f = Spec (f ≫ β)`. -/
theorem spec_comp' : Spec.map β ≫ Spec.map f = Spec.map (f ≫ β) := (Spec.map_comp f β).symm

/-- The comparison of the two spellings of the factorisation of the pullback along
`Spec (f ≫ β)`. -/
theorem pullbackSpecMapCompIso_eq :
    (Scheme.Modules.pullbackComp (Spec.map β) (Spec.map f) ≪≫
        Scheme.Modules.pullbackCongr (spec_comp' f β)).symm =
      pullbackSpecMapCompIso R A A' f β := by
  ext : 2
  simp only [pullbackSpecMapCompIso, Scheme.Modules.pullbackCongr, Iso.symm_hom, Iso.trans_inv,
    Iso.trans_hom, eqToIso.inv, eqToIso.hom]

/-- `A' ⊗_A (A ⊗_R C) ≅ A' ⊗_R C`, degreewise. -/
def extComp (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (ext β).obj ((ext f).obj C) ≅ (ext (f ≫ β)).obj C :=
  (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f.hom β.hom).symm
    (ComplexShape.up ℤ)).app C

/-- `Θ_f(C)` is the composite of the factorisation of the derived sheafification, the comparison
of the derived pullback with the degreewise pullback, the degreewise isomorphism
`tildePullbackComplexIso`, and the inverse factorisation. -/
theorem Θ_hom_eq (C : CochainComplex (ModuleCat.{u} R) ℤ) (hC : C.KFlat) :
    (Θ f C hC).hom =
      (StandardModel.specDerivedPullback f).map
          ((tilde.functor R).mapDerivedCategoryFactors.hom.app C) ≫
        (StandardModel.derivedPullbackComplexComparison (Spec.map f).toLRSHom.toShHom).app
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((AlgebraicGeometry.tildePullbackComplexIso R A f).hom.app C) ≫
        (tilde.functor A).mapDerivedCategoryFactors.inv.app ((ext f).obj C) := by
  simp only [Θ, StandardModel.tildeDerivedPullbackComparison,
    StandardModel.tildeDerivedPullbackFactor, StandardModel.tildePullbackComplexCompQIso,
    Iso.trans_hom, asIso_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, Category.comp_id, Category.assoc]
  rfl

/-- `tildePullbackComplexIso R A f` is the degreewise extension `cxIso` of
`pullbackTildeIso R A f`. -/
theorem tildePullbackComplexIso_eq (f : R ⟶ A) :
    AlgebraicGeometry.tildePullbackComplexIso R A f =
      cxIso (ComplexShape.up ℤ) (pullbackTildeIso R A f) :=
  rfl

/-- **The cocycle of Stacks 01I9 on complexes.** -/
theorem tildePullbackComplexIso_comp (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (NatTrans.mapHomologicalComplex (pullbackSpecMapCompIso R A A' f β).inv
        (ComplexShape.up ℤ)).app (((tilde.functor R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C) ≫
        (AlgebraicGeometry.tildePullbackComplexIso R A' (f ≫ β)).hom.app C =
      ((Scheme.Modules.pullback (Spec.map β)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((AlgebraicGeometry.tildePullbackComplexIso R A f).hom.app C) ≫
        (AlgebraicGeometry.tildePullbackComplexIso A A' β).hom.app ((ext f).obj C) ≫
        ((tilde.functor A').mapHomologicalComplex (ComplexShape.up ℤ)).map
          (extComp f β C).hom := by
  rw [tildePullbackComplexIso_eq, tildePullbackComplexIso_eq, tildePullbackComplexIso_eq]
  exact cxIso_cocycle (ComplexShape.up ℤ) (pullbackSpecMapCompIso R A A' f β)
    (pullbackTildeIso R A f) (pullbackTildeIso A A' β) (pullbackTildeIso R A' (f ≫ β))
    (ModuleCat.extendScalarsComp f.hom β.hom) (pullbackTildeIso_comp R A A' f β) C

/-- The diagram chase behind the cocycle of `Θ`, with every object and morphism a variable. -/
theorem Θ_cocycle_chase {𝒞' 𝒞 : Type*} [Category* 𝒞'] [Category* 𝒞] (L : 𝒞' ⥤ 𝒞)
    {P0 P1 P2 P3 P4 : 𝒞'} {T0 T1 T2 T3 T4 U2 U3 U4 U5 : 𝒞}
    (a : P0 ⟶ P1) (b : P1 ⟶ P2) (c : P2 ⟶ P3) (d : P3 ⟶ P4) (d' : P4 ⟶ P3)
    (θ0 : L.obj P0 ⟶ T0) (θ1 : L.obj P1 ⟶ T1) (θ1inv : T1 ⟶ L.obj P1)
    (L'm : T0 ⟶ T1) (c' : T1 ⟶ T2) (t' : T2 ⟶ T3) (m' : T3 ⟶ T4)
    (cβ2 : L.obj P2 ⟶ U2) (cβ3 : L.obj P3 ⟶ U3) (Qβtf : U2 ⟶ U3)
    (Qtβ : U3 ⟶ U4) (mU : U4 ⟶ U5) (dTe : U5 ⟶ T4) (QE : T2 ⟶ U2) (QEinv : U2 ⟶ T2)
    (Qte : U4 ⟶ T3)
    (pin : c' ≫ QE = θ1inv ≫ L.map b ≫ cβ2) (hcx : QEinv ≫ t' = Qβtf ≫ Qtβ ≫ Qte)
    (nθ : L.map a ≫ θ1 = θ0 ≫ L'm) (nc : L.map c ≫ cβ3 = cβ2 ≫ Qβtf)
    (nm : Qte ≫ m' = mU ≫ dTe)
    (hθ : θ1 ≫ θ1inv = 𝟙 _) (hE : QE ≫ QEinv = 𝟙 _) (hm : d ≫ d' = 𝟙 _) :
    θ0 ≫ L'm ≫ c' ≫ t' ≫ m' =
      L.map (a ≫ b ≫ c ≫ d) ≫ (L.map d' ≫ cβ3 ≫ Qtβ ≫ mU) ≫ dTe := by
  have e1 : c' ≫ t' = θ1inv ≫ L.map b ≫ cβ2 ≫ Qβtf ≫ Qtβ ≫ Qte := by
    calc c' ≫ t' = c' ≫ (QE ≫ QEinv) ≫ t' := by rw [hE, Category.id_comp]
      _ = (c' ≫ QE) ≫ QEinv ≫ t' := by simp only [Category.assoc]
      _ = _ := by rw [pin, hcx]; simp only [Category.assoc]
  have hm' : L.map d ≫ L.map d' = 𝟙 _ := by rw [← L.map_comp, hm, L.map_id]
  simp only [L.map_comp, Category.assoc]
  rw [← reassoc_of% nθ, reassoc_of% e1, reassoc_of% hθ, nm, reassoc_of% hm', reassoc_of% nc]

/-- **The cocycle of `Θ`.** Along the factorisation `Spec β ≫ Spec f = Spec (f ≫ β)`, the
comparison isomorphism of Stacks 0D5S followed by `Θ_{f ≫ β}` is `Θ_f` pulled back along
`Spec β`, followed by `Θ_β` and the identification `A' ⊗_A (A ⊗_R C) ≅ A' ⊗_R C`. -/
theorem Θ_cocycle (C : CochainComplex (ModuleCat.{u} R) ℤ) (hC : C.KFlat) :
    (schemeFactorIso (Spec.map β) (Spec.map f) (Spec.map (f ≫ β)) (spec_comp' f β)).hom.app
        ((tilde.functor R).mapDerivedCategory.obj (DerivedCategory.Q.obj C)) ≫
          (Θ (f ≫ β) C hC).hom =
      (pb (Spec.map β)).map (Θ f C hC).hom ≫ (Θ β ((ext f).obj C) (kFlat_ext f C hC)).hom ≫
        (tilde.functor A').mapDerivedCategory.map (DerivedCategory.Q.map (extComp f β C).hom) := by
  -- the pinning of the comparison of Stacks 0D5S on complexes
  have pin := StandardModel.derivedPullbackComplexComparison_comp_schemeFactorIso
    (Spec.map β) (Spec.map f) (Spec.map (f ≫ β)) (spec_comp' f β)
    (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
  rw [pullbackSpecMapCompIso_eq] at pin
  have hcx := tildePullbackComplexIso_comp f β C
  have nθ := (schemeFactorIso (Spec.map β) (Spec.map f) (Spec.map (f ≫ β))
    (spec_comp' f β)).hom.naturality ((tilde.functor R).mapDerivedCategoryFactors.hom.app C)
  have nc := (StandardModel.derivedPullbackComplexComparison
    (Spec.map β).toLRSHom.toShHom).naturality
      ((AlgebraicGeometry.tildePullbackComplexIso R A f).hom.app C)
  have nm := (tilde.functor A').mapDerivedCategoryFactors.inv.naturality (extComp f β C).hom
  simp only [Functor.comp_map] at nθ nc nm
  rw [Θ_hom_eq, Θ_hom_eq, Θ_hom_eq]
  have hE : DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (pullbackSpecMapCompIso R A A' f β)
        (ComplexShape.up ℤ)).hom.app (((tilde.functor R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (pullbackSpecMapCompIso R A A' f β).inv
        (ComplexShape.up ℤ)).app (((tilde.functor R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C)) = 𝟙 _ := by
    exact (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex
      (pullbackSpecMapCompIso R A A' f β) (ComplexShape.up ℤ)).app _)).hom_inv_id
  have hcxQ := congrArg DerivedCategory.Q.map hcx
  simp only [Functor.map_comp] at hcxQ
  refine (Θ_cocycle_chase (pb (Spec.map β)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    pin hcxQ nθ nc nm
    (Iso.hom_inv_id_app (schemeFactorIso (Spec.map β) (Spec.map f) (Spec.map (f ≫ β))
      (spec_comp' f β)) _) hE
    (Iso.inv_hom_id_app (tilde.functor A).mapDerivedCategoryFactors _)).trans ?_
  rfl

end Stacks.LimitHomDescent.Affine

end
