module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DualPushforwardBaseChangeTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexDerived

/-!
# The perfect-stage computation of Stacks 0DKL

Let `X' = X ×_Y Y'` be a cartesian square of algebraic spaces, `V` the quasi-compact
neighbourhood of the support of `𝒢^•` and `g'⁻¹V` its preimage. On `g'⁻¹V` the coefficient
`(g'|)^*(𝒢^•|_V) ⊗^L L(f'|)^*(ℱ'[i])` is the complex `(g'|)^*(𝒢^•|_V) ⊗ (f'|)^*ℱ'` shifted by
`i`, for `𝒢^•|_V` bounded and flat over `Y`. With it, a perfect approximation `P` of `E` on `V`
and an approximation `Lₙ` of `L` give
`Ext^i_{Y'}(Lg^*L, ℱ') ≅ Ext^i_{X'}(L(g')^*E, (g')^*𝒢^• ⊗ (f')^*ℱ')` for `i` small enough.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `derivedTensorPullbackSingleShiftIso`: `𝒢^• ⊗^L Lf^*(ℱ[0][i]) ≅ (𝒢^• ⊗ f^*ℱ)[i]` for `𝒢^•`
  bounded with terms flat over `Y`.
* `baseChangeStageCoefficientIso`: the same isomorphism on the preimage neighbourhood `g'⁻¹V`.
* `baseChangeStageExt`: the perfect-stage isomorphism of `Ext` groups of Stacks 0DKL.

## Main results

* `baseChangeStageExt_naturality`: `baseChangeStageExt` is natural in `ℱ'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **`𝒢^• ⊗^L Lf^*(ℱ[0][i]) ≅ (𝒢^• ⊗ f^*ℱ)[i]`** for `𝒢^•` bounded with terms flat over `Y`, as
an isomorphism of functors of the module `ℱ`: the shift commutes with `Lf^*` and with
`𝒢^• ⊗^L -`, and the remaining comparison is the one of Stacks 0A1M
(`AlgebraicGeometry.Space.isIso_tensorPullbackComplexNatTrans_app_single`). -/
def derivedTensorPullbackSingleShiftNatIso (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (a b : ℤ) (hGb : ∀ q : ℤ, q < a ∨ b < q → IsZero (G.X q))
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x) (i : ℤ) :
    DerivedCategory.singleFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0 ⋙
        shiftFunctor _ i ⋙ smallEtaleDerivedModulePullback B S hS f ⋙
          (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G) ≅
      CochainComplex.singleFunctor (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0 ⋙
        tensorPullbackComplex f G ⋙ DerivedCategory.Q ⋙ shiftFunctor _ i :=
  haveI : IsIso (Functor.whiskerLeft (CochainComplex.singleFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0)
        (tensorPullbackComplexNatTrans f G)) :=
    haveI : ∀ F, IsIso ((Functor.whiskerLeft (CochainComplex.singleFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0)
          (tensorPullbackComplexNatTrans f G)).app F) :=
      fun F => isIso_tensorPullbackComplexNatTrans_app_single a b hGb hG F
    NatIso.isIso_of_isIso_app _
  Functor.isoWhiskerLeft (DerivedCategory.singleFunctor _ 0)
      ((smallEtaleDerivedModulePullback B S hS f ⋙
        (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)).commShiftIso i) ≪≫
    Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ _ 0)
      ((smallEtaleDerivedModulePullback B S hS f ⋙
        (smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)) ⋙ shiftFunctor _ i) ≪≫
    Functor.isoWhiskerRight (asIso (Functor.whiskerLeft (CochainComplex.singleFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0)
        (tensorPullbackComplexNatTrans f G))) (shiftFunctor _ i)

/-- **`𝒢^• ⊗^L Lf^*(ℱ[0][i]) ≅ (𝒢^• ⊗ f^*ℱ)[i]`** for `𝒢^•` bounded with terms flat over `Y`,
the component of `AlgebraicGeometry.Space.derivedTensorPullbackSingleShiftNatIso`. -/
def derivedTensorPullbackSingleShiftIso (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (a b : ℤ) (hGb : ∀ q : ℤ, q < a ∨ b < q → IsZero (G.X q))
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ) :
    ((smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)).obj
        ((smallEtaleDerivedModulePullback B S hS f).obj
          (((DerivedCategory.singleFunctor _ 0).obj F)⟦i⟧)) ≅
      (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj
        ((CochainComplex.singleFunctor _ 0).obj F)))⟦i⟧ :=
  (derivedTensorPullbackSingleShiftNatIso f G a b hGb hG i).app F

attribute [local irreducible] derivedTensorPullbackSingleShiftNatIso in
/-- **`derivedTensorPullbackSingleShiftIso` is natural in the module `ℱ`.** -/
theorem derivedTensorPullbackSingleShiftIso_hom_naturality (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (a b : ℤ) (hGb : ∀ q : ℤ, q < a ∨ b < q → IsZero (G.X q))
    (hG : ∀ n x, IsFlatOverAtGeometricPoint B S hS f (G.X n) x)
    {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (q : F ⟶ F') (i : ℤ) :
    ((smallEtaleDerivedTensor B S hS X).obj (DerivedCategory.Q.obj G)).map
        ((smallEtaleDerivedModulePullback B S hS f).map
          (((DerivedCategory.singleFunctor _ 0).map q)⟦i⟧')) ≫
        (derivedTensorPullbackSingleShiftIso f G a b hGb hG F' i).hom =
      (derivedTensorPullbackSingleShiftIso f G a b hGb hG F i).hom ≫
        (DerivedCategory.Q.map ((tensorPullbackComplex f G).map
          ((CochainComplex.singleFunctor _ 0).map q)))⟦i⟧' :=
  (derivedTensorPullbackSingleShiftNatIso f G a b hGb hG i).hom.naturality q

section Stage

variable {X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  {Uo : Subfunctor X.1} {V : Subfunctor X.1}
  (hsq : IsElementaryDistinguishedSquare B S hS X.2 Uo V.ι)
  {Uo' : Subfunctor X'.1}
  (hsq' : IsElementaryDistinguishedSquare B S hS X'.2 Uo' (V.preimage g'.hom).ι)

/-- The two spellings of the pullback of `𝒢^•|_V` to the preimage neighbourhood, via
`modulePullback` and via `pullbackComplexSmallEtale`, give isomorphic functors
`(g'|)^*(𝒢^•|_V) ⊗^L -`. -/
def baseChangeStagePullbackTensorIso
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (smallEtaleDerivedTensor B S hS (edsEtale B S hS hsq')).obj
        (DerivedCategory.Q.obj (((modulePullback B S hS
          (edsEtalePreimageHom hsq g' hsq')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))) ≅
      (smallEtaleDerivedTensor B S hS (edsEtale B S hS hsq')).obj (DerivedCategory.Q.obj
        ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))) :=
  let Fp := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS (edsEtale B S hS hsq'))
    (Y := smallEtaleRingedTopos B S hS (edsEtale B S hS hsq))
    (smallEtaleRingedToposHom B S hS (edsEtalePreimageHom hsq g' hsq')).toModulesHom
  let Gp : type_of% Fp := modulePullback B S hS (edsEtalePreimageHom hsq g' hsq')
  haveI : Gp.Additive := modulePullback_additive (edsEtalePreimageHom hsq g' hsq')
  (smallEtaleDerivedTensor B S hS _).mapIso (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (F := Fp) (G := Gp)
        (pullbackModulesIsoModulePullback B S hS (edsEtalePreimageHom hsq g' hsq'))
          (ComplexShape.up ℤ)).app
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).symm)

/-- **The coefficient of the perfect-stage computation**: on the preimage neighbourhood `g'⁻¹V`,
`(g'|)^*(𝒢^•|_V) ⊗^L L(f'|)^*(ℱ'[i]) ≅ ((g'|)^*(𝒢^•|_V) ⊗ (f'|)^*ℱ')[i]`, the first pullback
taken in the spelling `modulePullback` of the base change of Stacks 0A1K. -/
def baseChangeStageCoefficientIso (f' : X' ⟶ Y')
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (a b : ℤ) (hGab : ∀ q : ℤ, q < a ∨ b < q → IsZero (((pullbackComplexSmallEtale
      (edsEtalePreimageHom hsq g' hsq')).obj ((pullbackComplexSmallEtale
        (edsEtaleHom B S hS hsq)).obj G)).X q))
    (hGfl : ∀ n x, IsFlatOverAtGeometricPoint B S hS (edsEtaleHom B S hS hsq' ≫ f')
      (((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).X n) x)
    (F' : Modules.{u, u} B S hS Y'.1 Y'.2) (i : ℤ) :
    asModulesObj (edsEtale B S hS hsq') (((smallEtaleDerivedTensor B S hS _).obj
          (DerivedCategory.Q.obj (((modulePullback B S hS
            (edsEtalePreimageHom hsq g' hsq')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))).obj
          ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq' ≫ f')).obj
            (((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧))) ≅
        (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq' ≫ f')
        ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
          ((CochainComplex.singleFunctor _ 0).obj F'))⟦i⟧ :=
  (baseChangeStagePullbackTensorIso hsq hsq' G).app _ ≪≫
    derivedTensorPullbackSingleShiftIso (edsEtaleHom B S hS hsq' ≫ f') _ a b hGab hGfl F' i

attribute [local irreducible] derivedTensorPullbackSingleShiftIso
  baseChangeStagePullbackTensorIso in
/-- **`baseChangeStageCoefficientIso` is natural in the module `ℱ'`.** -/
theorem baseChangeStageCoefficientIso_hom_naturality (f' : X' ⟶ Y')
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (a b : ℤ) (hGab : ∀ q : ℤ, q < a ∨ b < q → IsZero (((pullbackComplexSmallEtale
      (edsEtalePreimageHom hsq g' hsq')).obj ((pullbackComplexSmallEtale
        (edsEtaleHom B S hS hsq)).obj G)).X q))
    (hGfl : ∀ n x, IsFlatOverAtGeometricPoint B S hS (edsEtaleHom B S hS hsq' ≫ f')
      (((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).X n) x)
    {F' F'' : Modules.{u, u} B S hS Y'.1 Y'.2} (q : F' ⟶ F'') (i : ℤ) :
    (show asModulesObj (edsEtale B S hS hsq') (((smallEtaleDerivedTensor B S hS _).obj
          (DerivedCategory.Q.obj (((modulePullback B S hS
            (edsEtalePreimageHom hsq g' hsq')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))).obj
          ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq' ≫ f')).obj
            (((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧))) ⟶
        asModulesObj (edsEtale B S hS hsq') (((smallEtaleDerivedTensor B S hS _).obj
          (DerivedCategory.Q.obj (((modulePullback B S hS
            (edsEtalePreimageHom hsq g' hsq')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))).obj
          ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq' ≫ f')).obj
            (((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F'')⟦i⟧)))
      from ((smallEtaleDerivedTensor B S hS _).obj
          (DerivedCategory.Q.obj (((modulePullback B S hS
            (edsEtalePreimageHom hsq g' hsq')).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))).map
          ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq' ≫ f')).map
            ((shiftFunctor (DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2)) i).map
              ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).map q)))) ≫
        (baseChangeStageCoefficientIso hsq hsq' f' G a b hGab hGfl F'' i).hom =
      (baseChangeStageCoefficientIso hsq hsq' f' G a b hGab hGfl F' i).hom ≫
        (shiftFunctor (DerivedCategory (Modules.{u, u} B S hS
          (edsEtale B S hS hsq').1 (edsEtale B S hS hsq').2)) i).map
          (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq' ≫ f')
            ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
              ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).map
                ((CochainComplex.singleFunctor _ 0).map q))) := by
  have n1 := (baseChangeStagePullbackTensorIso hsq hsq' G).hom.naturality
    ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq' ≫ f')).map
      ((shiftFunctor (DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2)) i).map
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).map q)))
  have n2 : ((smallEtaleDerivedTensor B S hS _).obj (DerivedCategory.Q.obj
        ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))).map
        ((smallEtaleDerivedModulePullback B S hS (edsEtaleHom B S hS hsq' ≫ f')).map
          ((shiftFunctor (DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2)) i).map
            ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).map q))) ≫
        (derivedTensorPullbackSingleShiftIso (edsEtaleHom B S hS hsq' ≫ f') _ a b hGab hGfl
          F'' i).hom =
      (derivedTensorPullbackSingleShiftIso (edsEtaleHom B S hS hsq' ≫ f') _ a b hGab hGfl
          F' i).hom ≫
        (shiftFunctor (DerivedCategory (Modules.{u, u} B S hS
          (edsEtale B S hS hsq').1 (edsEtale B S hS hsq').2)) i).map
          (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq' ≫ f')
            ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
              ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).map
                ((CochainComplex.singleFunctor _ 0).map q))) :=
    derivedTensorPullbackSingleShiftIso_hom_naturality (edsEtaleHom B S hS hsq' ≫ f') _
      a b hGab hGfl q i
  exact comp_comp_eq_of_comm₂ n1 n2

/-- **The perfect-stage computation of the base change of `Ext` (Stacks 0DKL).** Let `L` receive
`ι : Lₙ ⟶ L`, an isomorphism on `Hʲ` for `j > s_L`, with `Lₙ ≅ (Rf_V*(P^∨ ⊗^L 𝒢^•|_V))^∨` for a
perfect `P` on the neighbourhood `V` of the support of `𝒢^•` and a map `c : P ⟶ E|_V` which is
an isomorphism on `Hʲ` for `j > s_E`. Then for `ℱ'` quasi-coherent on `Y'` and `i` small enough,
`Ext^i_{Y'}(Lg^*L, ℱ') ≅ Ext^i_{X'}(L(g')^*E, (g')^*𝒢^• ⊗ (f')^*ℱ')`. -/
def baseChangeStageExt (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (hfqs : IsQuasiSeparated B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i →
      IsZero (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G).X i))
    (hq : ∀ n,
      (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G).X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS (edsEtale B S hS hsq).2 (edsEtaleHom B S hS hsq ≫ f).hom
      (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G).X n))
    (a b : ℤ) (hGab : ∀ q : ℤ, q < a ∨ b < q → IsZero (((pullbackComplexSmallEtale
      (edsEtalePreimageHom hsq g' hsq')).obj ((pullbackComplexSmallEtale
        (edsEtaleHom B S hS hsq)).obj G)).X q))
    (hGfl : ∀ n x, IsFlatOverAtGeometricPoint B S hS (edsEtaleHom B S hS hsq' ≫ f')
      (((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).X n) x)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (P : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (hP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2) P)
    (c : P ⟶ (edsEtaleRestrict B S hS hsq).obj E) (sE : ℤ)
    (hc : ∀ j : ℤ, sE < j → IsIso ((DerivedCategory.homologyFunctor _ j).map c))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((smallEtaleDerivedModulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).obj
        (((smallEtaleDerivedTensor B S hS _).obj (smallEtaleDerivedDual B S hS _ P)).obj
          (DerivedCategory.Q.obj ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))))
    (Ln L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (ι : Ln ⟶ L) (sL : ℤ)
    (hι : ∀ j : ℤ, sL < j → IsIso ((DerivedCategory.homologyFunctor _ j).map ι))
    (eL : Ln ≅ smallEtaleDerivedDual B S hS Y
      ((smallEtaleDerivedModulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).obj
        (((smallEtaleDerivedTensor B S hS _).obj (smallEtaleDerivedDual B S hS _ P)).obj
          (DerivedCategory.Q.obj ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))))
    (F' : Modules.{u, u} B S hS Y'.1 Y'.2) (hF' : F'.IsQuasicoherentOnSite)
    (hN : CohomologySupportedOn B S hS X'.1 X'.2 (edsComplementPoints B S hS Uo')
      (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G)
        ((CochainComplex.singleFunctor _ 0).obj F')))
    (ha : (show DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq'))) from
      tensorPullbackComplexDerived (edsEtaleHom B S hS hsq' ≫ f')
      ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
          ((CochainComplex.singleFunctor _ 0).obj F')).IsGE a)
    (i : ℤ) (hiL : i + sL + 2 ≤ 0) (hiE : i + sE + 2 ≤ a) :
    (asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧) ≃+
      (asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E) ⟶
        (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G)
          ((CochainComplex.singleFunctor _ 0).obj F'))⟦i⟧) :=
  (towerStageBaseChangeExt (isPullback_edsEtalePreimageHom_comp hsq g' hsq' sq) hfqc hfqs P hP
      _ hGb hq hfl hK Ln L ι sL hι eL F' hF' i hiL).trans <|
  (homAddEquivOfIsoTarget (C := DerivedCategory (Modules.{u, u} B S hS
      (edsEtale B S hS hsq').1 (edsEtale B S hS hsq').2)) _
    (baseChangeStageCoefficientIso hsq hsq' f' G a b hGab hGfl F' i)).trans <|
  (baseChangeRestrictApproximationExt hsq g' hsq' G E P c sE hc _ hN a ha i hiE).symm

attribute [local irreducible] towerStageBaseChangeExt baseChangeStageCoefficientIso
  baseChangeRestrictApproximationExt in
/-- `baseChangeStageExt` is the composite of `towerStageBaseChangeExt`, composition with
`baseChangeStageCoefficientIso` and the inverse of `baseChangeRestrictApproximationExt`. -/
theorem baseChangeStageExt_apply (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (hfqs : IsQuasiSeparated B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i →
      IsZero (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G).X i))
    (hq : ∀ n,
      (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G).X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS (edsEtale B S hS hsq).2 (edsEtaleHom B S hS hsq ≫ f).hom
      (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G).X n))
    (a b : ℤ) (hGab : ∀ q : ℤ, q < a ∨ b < q → IsZero (((pullbackComplexSmallEtale
      (edsEtalePreimageHom hsq g' hsq')).obj ((pullbackComplexSmallEtale
        (edsEtaleHom B S hS hsq)).obj G)).X q))
    (hGfl : ∀ n x, IsFlatOverAtGeometricPoint B S hS (edsEtaleHom B S hS hsq' ≫ f')
      (((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).X n) x)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (P : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (hP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2) P)
    (c : P ⟶ (edsEtaleRestrict B S hS hsq).obj E) (sE : ℤ)
    (hc : ∀ j : ℤ, sE < j → IsIso ((DerivedCategory.homologyFunctor _ j).map c))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((smallEtaleDerivedModulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).obj
        (((smallEtaleDerivedTensor B S hS _).obj (smallEtaleDerivedDual B S hS _ P)).obj
          (DerivedCategory.Q.obj ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))))
    (Ln L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (ι : Ln ⟶ L) (sL : ℤ)
    (hι : ∀ j : ℤ, sL < j → IsIso ((DerivedCategory.homologyFunctor _ j).map ι))
    (eL : Ln ≅ smallEtaleDerivedDual B S hS Y
      ((smallEtaleDerivedModulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).obj
        (((smallEtaleDerivedTensor B S hS _).obj (smallEtaleDerivedDual B S hS _ P)).obj
          (DerivedCategory.Q.obj ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))))
    (F' : Modules.{u, u} B S hS Y'.1 Y'.2) (hF' : F'.IsQuasicoherentOnSite)
    (hN : CohomologySupportedOn B S hS X'.1 X'.2 (edsComplementPoints B S hS Uo')
      (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G)
        ((CochainComplex.singleFunctor _ 0).obj F')))
    (ha : (show DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq'))) from
      tensorPullbackComplexDerived (edsEtaleHom B S hS hsq' ≫ f')
      ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
          ((CochainComplex.singleFunctor _ 0).obj F')).IsGE a)
    (i : ℤ) (hiL : i + sL + 2 ≤ 0) (hiE : i + sE + 2 ≤ a)
    (e : asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧) :
    baseChangeStageExt hsq hsq' sq hfqc hfqs G hGb hq hfl a b hGab hGfl E P hP c sE hc hK Ln L ι
        sL hι eL F' hF' hN ha i hiL hiE e =
      (baseChangeRestrictApproximationExt hsq g' hsq' G E P c sE hc _ hN a ha i hiE).symm
        (towerStageBaseChangeExt (isPullback_edsEtalePreimageHom_comp hsq g' hsq' sq) hfqc hfqs
            P hP _ hGb hq hfl hK Ln L ι sL hι eL F' hF' i hiL e ≫
          (baseChangeStageCoefficientIso hsq hsq' f' G a b hGab hGfl F' i).hom) :=
  rfl

attribute [local irreducible] towerStageBaseChangeExt baseChangeStageCoefficientIso
  baseChangeRestrictApproximationExt in
/-- **The perfect-stage computation of the base change of `Ext` is natural in `ℱ'`.** -/
theorem baseChangeStageExt_naturality (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (hfqs : IsQuasiSeparated B S hS (edsEtaleHom B S hS hsq ≫ f).hom)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i →
      IsZero (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G).X i))
    (hq : ∀ n,
      (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G).X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS (edsEtale B S hS hsq).2 (edsEtaleHom B S hS hsq ≫ f).hom
      (((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G).X n))
    (a b : ℤ) (hGab : ∀ q : ℤ, q < a ∨ b < q → IsZero (((pullbackComplexSmallEtale
      (edsEtalePreimageHom hsq g' hsq')).obj ((pullbackComplexSmallEtale
        (edsEtaleHom B S hS hsq)).obj G)).X q))
    (hGfl : ∀ n x, IsFlatOverAtGeometricPoint B S hS (edsEtaleHom B S hS hsq' ≫ f')
      (((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).X n) x)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (P : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (hP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2) P)
    (c : P ⟶ (edsEtaleRestrict B S hS hsq).obj E) (sE : ℤ)
    (hc : ∀ j : ℤ, sE < j → IsIso ((DerivedCategory.homologyFunctor _ j).map c))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((smallEtaleDerivedModulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).obj
        (((smallEtaleDerivedTensor B S hS _).obj (smallEtaleDerivedDual B S hS _ P)).obj
          (DerivedCategory.Q.obj ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))))
    (Ln L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (ι : Ln ⟶ L) (sL : ℤ)
    (hι : ∀ j : ℤ, sL < j → IsIso ((DerivedCategory.homologyFunctor _ j).map ι))
    (eL : Ln ≅ smallEtaleDerivedDual B S hS Y
      ((smallEtaleDerivedModulePushforward B S hS (edsEtaleHom B S hS hsq ≫ f)).obj
        (((smallEtaleDerivedTensor B S hS _).obj (smallEtaleDerivedDual B S hS _ P)).obj
          (DerivedCategory.Q.obj ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)))))
    {F' F'' : Modules.{u, u} B S hS Y'.1 Y'.2} (hF' : F'.IsQuasicoherentOnSite)
    (hF'' : F''.IsQuasicoherentOnSite) (q : F' ⟶ F'')
    (hN : CohomologySupportedOn B S hS X'.1 X'.2 (edsComplementPoints B S hS Uo')
      (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G)
        ((CochainComplex.singleFunctor _ 0).obj F')))
    (ha : (show DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq'))) from
      tensorPullbackComplexDerived (edsEtaleHom B S hS hsq' ≫ f')
      ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
          ((CochainComplex.singleFunctor _ 0).obj F')).IsGE a)
    (hN'' : CohomologySupportedOn B S hS X'.1 X'.2 (edsComplementPoints B S hS Uo')
      (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G)
        ((CochainComplex.singleFunctor _ 0).obj F'')))
    (ha'' : (show DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq'))) from
      tensorPullbackComplexDerived (edsEtaleHom B S hS hsq' ≫ f')
      ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))
          ((CochainComplex.singleFunctor _ 0).obj F'')).IsGE a)
    (i : ℤ) (hiL : i + sL + 2 ≤ 0) (hiE : i + sE + 2 ≤ a)
    (e : asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧) :
    baseChangeStageExt hsq hsq' sq hfqc hfqs G hGb hq hfl a b hGab hGfl E P hP c sE hc hK Ln L ι
        sL hι eL F'' hF'' hN'' ha'' i hiL hiE
        (e ≫ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).map q)⟦i⟧') =
      baseChangeStageExt hsq hsq' sq hfqc hfqs G hGb hq hfl a b hGab hGfl E P hP c sE hc hK Ln L ι
          sL hι eL F' hF' hN ha i hiL hiE e ≫
        (DerivedCategory.Q.map
          ((tensorPullbackComplex f' ((pullbackComplexSmallEtale g').obj G)).map
            ((CochainComplex.singleFunctor _ 0).map q)))⟦i⟧' := by
  have hT := towerStageBaseChangeExt_naturality
    (isPullback_edsEtalePreimageHom_comp hsq g' hsq' sq) hfqc hfqs P hP _ hGb hq hfl hK Ln L ι sL
    hι eL hF' hF'' q i hiL e
  have hC := baseChangeStageCoefficientIso_hom_naturality hsq hsq' f' G a b hGab hGfl q i
  have hTC := comp_eq_of_eq_comp_of_comm hT hC
  have hR := baseChangeRestrictApproximationExt_naturality hsq g' hsq' G E P c sE hc
    ((CochainComplex.singleFunctor _ 0).map q) hN hN'' a ha ha'' i hiE
    ((baseChangeRestrictApproximationExt hsq g' hsq' G E P c sE hc _ hN a ha i hiE).symm
      (towerStageBaseChangeExt (isPullback_edsEtalePreimageHom_comp hsq g' hsq' sq) hfqc hfqs
          P hP _ hGb hq hfl hK Ln L ι sL hι eL F' hF' i hiL e ≫
        (baseChangeStageCoefficientIso hsq hsq' f' G a b hGab hGfl F' i).hom))
  refine (baseChangeStageExt_apply hsq hsq' sq hfqc hfqs G hGb hq hfl a b hGab hGfl E P hP c sE
      hc hK Ln L ι sL hι eL F'' hF'' hN'' ha'' i hiL hiE _).trans
    (Eq.trans ?_ (congrArg (· ≫ _) (baseChangeStageExt_apply hsq hsq' sq hfqc hfqs G hGb hq hfl a
      b hGab hGfl E P hP c sE hc hK Ln L ι sL hι eL F' hF' hN ha i hiL hiE e)).symm)
  refine (baseChangeRestrictApproximationExt hsq g' hsq' G E P c sE hc _ hN'' a ha'' i
    hiE).injective ?_
  exact (AddEquiv.apply_symm_apply _ _).trans (hTC.trans
    ((congrArg (· ≫ _) (AddEquiv.apply_symm_apply _ _)).symm.trans hR.symm))

end Stage

end AlgebraicGeometry.Space

end
