module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DualPushforwardBaseChangeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtCoefficientBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator

/-!
# `Ext` out of the base change of a homotopy colimit of duals of perfect stages

Let `L` be an object of `D(𝒪_Y)` receiving a map `ι : Lₙ ⟶ L` which is an isomorphism on `Hʲ`
for `j > s`, where `Lₙ ≅ K^∨` for `K = Rf_*(P^∨ ⊗^L 𝒢^•)` perfect (the situation of the stages
of the tower defining the complex `L` of Stacks 08JR (B)). For a cartesian square
`X' = X ×_Y Y'` with `f` quasi-compact and quasi-separated, a quasi-coherent `ℱ'` on `Y'` and
`i + s + 2 ≤ 0`,

`Ext^i(Lg^*L, ℱ') ≅ Hom(L(g')^*P, (g')^*𝒢^• ⊗^L L(f')^*(ℱ'[i]))`.

## Main definitions

* `AlgebraicGeometry.Space.towerStageBaseChangeExt`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **`Ext` into a single module does not see the derived pullback of a morphism which is an
isomorphism in high degrees**, in the spelling `Modules Y'.1 Y'.2` of the coefficient modules. -/
theorem bijective_comp_smallEtaleDerivedModulePullback_shiftedHom_single (g : Y' ⟶ Y)
    {P L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (c : P ⟶ L) (s : ℤ)
    (hc : ∀ j : ℤ, s < j → IsIso ((DerivedCategory.homologyFunctor _ j).map c))
    (F : Modules.{u, u} B S hS Y'.1 Y'.2) (i : ℤ) (hi : i + s + 2 ≤ 0) :
    Function.Bijective (fun e : asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F)⟦i⟧ =>
      (show asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj P) ⟶
          asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) from
        (smallEtaleDerivedModulePullback B S hS g).map c) ≫ e) := by
  have : (show DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y'))
      from (DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F).IsGE 0 :=
    (inferInstance : ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj
      F).IsGE 0)
  exact bijective_comp_smallEtaleDerivedModulePullback_shiftedHom g c s hc _ 0 i hi

/-- **`Ext` out of the base change of `L`, computed on a perfect stage.** If `ι : Lₙ ⟶ L` is an
isomorphism on `Hʲ` for `j > s` and `Lₙ ≅ K^∨` with `K = Rf_*(P^∨ ⊗^L 𝒢^•)` perfect, then for
`f` quasi-compact and quasi-separated, `ℱ'` quasi-coherent on `Y'` and `i + s + 2 ≤ 0`,
`Ext^i(Lg^*L, ℱ') ≅ Hom(L(g')^*P, (g')^*𝒢^• ⊗^L L(f')^*(ℱ'[i]))`. -/
def towerStageBaseChangeExt (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) P)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((smallEtaleDerivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
          (DerivedCategory.Q.obj G))))
    (Ln L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (ι : Ln ⟶ L) (s : ℤ)
    (hι : ∀ j : ℤ, s < j → IsIso ((DerivedCategory.homologyFunctor _ j).map ι))
    (eL : Ln ≅ smallEtaleDerivedDual B S hS Y ((smallEtaleDerivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
          (DerivedCategory.Q.obj G))))
    (F' : Modules.{u, u} B S hS Y'.1 Y'.2) (hF' : F'.IsQuasicoherentOnSite) (i : ℤ)
    (hi : i + s + 2 ≤ 0) :
    (asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧) ≃+
      (asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj P) ⟶
        asModulesObj X' (((smallEtaleDerivedTensor B S hS X').obj (DerivedCategory.Q.obj
          (((modulePullback B S hS g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G))).obj
            ((smallEtaleDerivedModulePullback B S hS f').obj
              (((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj
                F')⟦i⟧)))) :=
  (AddEquiv.ofBijective (Preadditive.leftComp
      (C := DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2)) _
      (show asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj Ln) ⟶
          asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) from
        (smallEtaleDerivedModulePullback B S hS g).map ι))
    (bijective_comp_smallEtaleDerivedModulePullback_shiftedHom_single g ι s hι F' i hi)).trans
  <| (homAddEquivOfIsoSource (C := DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2))
    (show asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj Ln) ≅
        asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj
          (smallEtaleDerivedDual B S hS Y ((smallEtaleDerivedModulePushforward B S hS f).obj
            (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
              (DerivedCategory.Q.obj G))))) from
      (smallEtaleDerivedModulePullback B S hS g).mapIso eL) _).trans
  <| dualPushforwardBaseChangeHomAddEquiv sq hfqc hfqs P hP G hGb hq hfl hK _
    (qcohDerived_shift _ i (derivedCategoryB_singleFunctor_obj B S hS Y'.1 Y'.2 F' hF'))

attribute [local irreducible] dualPushforwardBaseChangeHomNatIso in
/-- **`towerStageBaseChangeExt` is natural in the quasi-coherent coefficient `ℱ'`.** -/
theorem towerStageBaseChangeExt_naturality (sq : IsPullback g' f' f g)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (hP : RingedSite.IsPerfect (smallEtaleRingedSite B S hS X.1 X.2) P)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hfl : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2)
      ((smallEtaleDerivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
          (DerivedCategory.Q.obj G))))
    (Ln L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (ι : Ln ⟶ L) (s : ℤ)
    (hι : ∀ j : ℤ, s < j → IsIso ((DerivedCategory.homologyFunctor _ j).map ι))
    (eL : Ln ≅ smallEtaleDerivedDual B S hS Y ((smallEtaleDerivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj (smallEtaleDerivedDual B S hS X P)).obj
          (DerivedCategory.Q.obj G))))
    {F' F'' : Modules.{u, u} B S hS Y'.1 Y'.2} (hF' : F'.IsQuasicoherentOnSite)
    (hF'' : F''.IsQuasicoherentOnSite) (q : F' ⟶ F'') (i : ℤ) (hi : i + s + 2 ≤ 0)
    (e : asModulesObj Y' ((smallEtaleDerivedModulePullback B S hS g).obj L) ⟶
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj F')⟦i⟧) :
    towerStageBaseChangeExt sq hfqc hfqs P hP G hGb hq hfl hK Ln L ι s hι eL F'' hF'' i hi
        (e ≫ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).map q)⟦i⟧') =
      towerStageBaseChangeExt sq hfqc hfqs P hP G hGb hq hfl hK Ln L ι s hι eL F' hF' i hi e ≫
        (show asModulesObj X' (((smallEtaleDerivedTensor B S hS X').obj (DerivedCategory.Q.obj
            (((modulePullback B S hS g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G))).obj
              ((smallEtaleDerivedModulePullback B S hS f').obj
                (((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj
                  F')⟦i⟧))) ⟶
            asModulesObj X' (((smallEtaleDerivedTensor B S hS X').obj (DerivedCategory.Q.obj
            (((modulePullback B S hS g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G))).obj
              ((smallEtaleDerivedModulePullback B S hS f').obj
                (((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).obj
                  F'')⟦i⟧))) from
          ((smallEtaleDerivedTensor B S hS X').obj (DerivedCategory.Q.obj
            (((modulePullback B S hS g').mapHomologicalComplex (ComplexShape.up ℤ)).obj G))).map
              ((smallEtaleDerivedModulePullback B S hS f').map
                ((shiftFunctor (DerivedCategory (Modules.{u, u} B S hS Y'.1 Y'.2)) i).map
                  ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).map
                    q)))) := by
  let φ := ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).map q)⟦i⟧'
  let N : (qcohDerivedSheafOfModules Y').FullSubcategory :=
    ⟨_, qcohDerived_shift _ i (derivedCategoryB_singleFunctor_obj B S hS Y'.1 Y'.2 F' hF')⟩
  let N' : (qcohDerivedSheafOfModules Y').FullSubcategory :=
    ⟨_, qcohDerived_shift _ i (derivedCategoryB_singleFunctor_obj B S hS Y'.1 Y'.2 F'' hF'')⟩
  let qN : N ⟶ N' := ObjectProperty.homMk φ
  have h := dualPushforwardBaseChangeHomNatIso_naturality sq hfqc hfqs P hP G hGb hq hfl hK qN
    ((smallEtaleDerivedModulePullback B S hS g).map eL.inv ≫
      (smallEtaleDerivedModulePullback B S hS g).map ι ≫ e)
  have e1 : towerStageBaseChangeExt sq hfqc hfqs P hP G hGb hq hfl hK Ln L ι s hι eL F'' hF''
      i hi (e ≫ ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) 0).map q)⟦i⟧') =
      ((dualPushforwardBaseChangeHomNatIso sq hfqc hfqs P hP G hGb hq hfl hK).hom.app N').hom
        ((smallEtaleDerivedModulePullback B S hS g).map eL.inv ≫
          (smallEtaleDerivedModulePullback B S hS g).map ι ≫ e ≫ qN.hom) :=
    rfl
  have e2 : ((smallEtaleDerivedModulePullback B S hS g).map eL.inv ≫
      (smallEtaleDerivedModulePullback B S hS g).map ι ≫ e ≫ qN.hom) =
      ((smallEtaleDerivedModulePullback B S hS g).map eL.inv ≫
        (smallEtaleDerivedModulePullback B S hS g).map ι ≫ e) ≫ qN.hom :=
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm
  rw [e1, e2, h]
  rfl

end AlgebraicGeometry.Space

end
