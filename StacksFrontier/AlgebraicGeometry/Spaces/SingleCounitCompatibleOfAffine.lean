module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSingleCounitCompatible
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposPushforwardSingleUnit

/-!
# The derived counit against a map into an affine direct image, in degree zero: the proof

For an affine morphism `f : X ⟶ Y` of algebraic spaces, a quasi-coherent `𝒪_X`-module `M` and a
map `a : G ⟶ f_*M` whose transpose `f^*G ⟶ M` is an isomorphism, the map
`Lf^*(G[0]) ⟶ Lf^*((f_*M)[0]) ≅ Lf^*Rf_*(M[0]) ⟶ M[0]` is the comparison
`Lf^*(G[0]) ⟶ (f^*G)[0]` followed by an isomorphism (Stacks 0FPI in degree `0`). This is
`AlgebraicGeometry.Space.SingleCounitCompatible`, proved here as
`AlgebraicGeometry.Space.singleCounitCompatible`.

## Main results

* `Stacks.DerivedSingleCounit.exists_single_counit_comparison_of_singleUnit`: the statement for
  abstract data. The canonical map `(f_*M)[0] ⟶ Rf_*(M[0])` is given as a morphism `x`,
  with a formula expressing it through `Stacks.DerivedFunctor.singleUnit` of a second
  direct image `F = w`.
* `AlgebraicGeometry.Space.singleCounitCompatible`: the statement for an affine morphism of
  algebraic spaces.

## Implementation notes

The statement of `AlgebraicGeometry.Space.SingleCounitCompatible` mixes the site and the topos
spellings of the module categories. The abstract lemma is applied with the morphism `x` of
that statement as it stands. Its formula is proved factor by factor. The site map
`AlgebraicGeometry.Space.modulePushforwardSingleToDerived` is rewritten into the topos map
`AlgebraicGeometry.Space.smallEtaleToposPushforwardSingleUnit` by `NatTrans.congr_app` of a
comparison of natural transformations, at the module `M` shared by both sides. This keeps every
identification between the two spellings at the level of natural transformations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DerivedSingleCounit

variable {A Bc : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Category Bc] [Abelian Bc] [HasDerivedCategory Bc]

/-- **`Stacks.DerivedSingleCounit.exists_single_counit_comparison` with the canonical map given
through `Stacks.DerivedFunctor.singleUnit`.** The composite `a[0] ≫ (canonical map)` is a
morphism `x = φ₁ ≫ φ₂ ≫ φ₃`. Here `φ₁` is `a[0]`, `φ₂` the identification
`(w M)[0] ≅ (F M)[0]` along `F = w`, and `φ₃` the unit `(F M)[0] ⟶ R(M[0])` of `R` as a right
derived functor of `F`. -/
theorem exists_single_counit_comparison_of_singleUnit (F w : A ⥤ Bc) [F.Additive] [w.Additive]
    (hF : F = w) (P mp : Bc ⥤ A) (hP : P.Additive) (hmp : mp.Additive) (adjT : P ⊣ F)
    (adjM : mp ⊣ w) (L : DerivedCategory Bc ⥤ DerivedCategory A)
    (R : DerivedCategory A ⥤ DerivedCategory Bc) (adjD : L ⊣ R)
    (u : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    (cmp : DerivedCategory.Qh ⋙ L ⟶ P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (h0 : ∀ K, L.map (u.app K) ≫ adjD.counit.app (DerivedCategory.Qh.obj K) =
      cmp.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((adjT.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K))
    {G : Bc} {M : A} (a : G ⟶ w.obj M) (ha : IsIso ((adjM.homEquiv _ _).symm a))
    (i₁ : (DerivedCategory.singleFunctor Bc 0).obj G ⟶ (DerivedCategory.singleFunctor Bc 0).obj G)
    (hi₁ : i₁ = 𝟙 _)
    (i₂ : R.obj ((DerivedCategory.singleFunctor A 0).obj M) ⟶
      R.obj ((DerivedCategory.singleFunctor A 0).obj M)) (hi₂ : i₂ = 𝟙 _)
    (x : (DerivedCategory.singleFunctor Bc 0).obj G ⟶
      R.obj ((DerivedCategory.singleFunctor A 0).obj M))
    (φ₁ : (DerivedCategory.singleFunctor Bc 0).obj G ⟶
      (DerivedCategory.singleFunctor Bc 0).obj (w.obj M))
    (φ₂ : (DerivedCategory.singleFunctor Bc 0).obj (w.obj M) ⟶
      (DerivedCategory.singleFunctor Bc 0).obj (F.obj M))
    (φ₃ : (DerivedCategory.singleFunctor Bc 0).obj (F.obj M) ⟶
      R.obj ((DerivedCategory.singleFunctor A 0).obj M))
    (hx : x = φ₁ ≫ φ₂ ≫ φ₃)
    (hφ₁ : φ₁ = (DerivedCategory.singleFunctor Bc 0).map a)
    (hφ₂ : φ₂ =
      (Functor.isoWhiskerRight (eqToIso hF) (DerivedCategory.singleFunctor Bc 0)).inv.app M)
    (hφ₃ : φ₃ = (Stacks.DerivedFunctor.singleUnit F R u).app M) :
    ∃ v : DerivedCategory.Q.obj ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G)) ≅
        (DerivedCategory.singleFunctor A 0).obj M,
      L.map (i₁ ≫ x ≫ i₂) ≫ adjD.counit.app ((DerivedCategory.singleFunctor A 0).obj M) =
      L.map ((DerivedCategory.singleFunctorIsoCompQ Bc 0).hom.app G) ≫
        (L.map ((DerivedCategory.quotientCompQhIso Bc).inv.app
            ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G)) ≫
          cmp.app ((HomotopyCategory.quotient Bc (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G)) ≫
          (DerivedCategory.quotientCompQhIso A).hom.app
            ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single Bc (ComplexShape.up ℤ) 0).obj G))) ≫ v.hom := by
  subst hx hφ₁ hφ₂ hφ₃ hF
  obtain ⟨v, hv⟩ := exists_single_counit_comparison F F rfl P mp hP hmp adjT adjM L R adjD u cmp h0
    rfl u (by simp) a ha i₁ hi₁ i₂ hi₂
  refine ⟨v, ?_⟩
  rw [← hv]
  simp [Stacks.DerivedFunctor.singleUnit]

end Stacks.DerivedSingleCounit

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  AlgebraicGeometry.Space.modules_abelian
attribute [local instance] HasDerivedCategory.standard SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- `a[0]` in the site spelling, read through `AlgebraicGeometry.Space.spaceToToposDerived`, is
`a[0]` in the topos spelling. -/
theorem spaceToToposDerived_map_spaceDerivedSingle (Y : AlgebraicSpaces B S hS)
    {G G' : Modules.{u, u} B S hS Y.1 Y.2} (a : G ⟶ G') :
    (spaceToToposDerived Y).map ((spaceDerivedSingle B S hS Y 0).map a) =
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) 0).map a :=
  rfl

/-- **Stacks 0FPI in degree `0` for an affine morphism of algebraic spaces**: for an affine
`f : X ⟶ Y`, a quasi-coherent `𝒪_X`-module `M` and a map `a : G ⟶ f_*M` whose transpose
`f^*G ⟶ M` is an isomorphism, `AlgebraicGeometry.Space.SingleCounitCompatible` holds: the map
`Lf^*(G[0]) ⟶ Lf^*((f_*M)[0]) ≅ Lf^*Rf_*(M[0]) ⟶ M[0]` is the comparison
`Lf^*(G[0]) ⟶ (f^*G)[0]` followed by an isomorphism. -/
theorem singleCounitCompatible (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    {G : Modules.{u, u} B S hS Y.1 Y.2} (a : G ⟶ (modulePushforward B S hS f).obj M)
    (ha : IsIso (((modulePullbackAdjunction B S hS f).homEquiv _ _).symm a)) :
    SingleCounitCompatible f hf M hM a := by
  have e₀ : (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS f hf M hM).inv =
      (modulePushforwardSingleToDerived B S hS f).app M := rfl
  have e₁ : modulePushforwardSingleToDerived B S hS f =
      (Functor.isoWhiskerRight
        (@eqToIso (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X) ⥤
          SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) _ _ _
          (pushforwardModules_eq_modulePushforward B S hS f))
        (@DerivedCategory.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) _
          (SheafOfModules.instAbelian _) (HasDerivedCategory.standard _) 0)).inv ≫
        @Stacks.DerivedFunctor.singleUnit
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) _
          (SheafOfModules.instAbelian _) (HasDerivedCategory.standard _)
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) _
          (SheafOfModules.instAbelian _) (HasDerivedCategory.standard _)
          (smallEtaleRingedToposHom B S hS f).pushforwardModules
          (RingedToposHom.pullbackAdjPushforwardModules
            (smallEtaleRingedToposHom B S hS f)).right_adjoint_additive
          (Stacks.Cohomology.DerivedPushforward.derivedPushforward
            (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
            (smallEtaleRingedToposHom B S hS f))
          ((Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy
            (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
            (smallEtaleRingedToposHom B S hS f)).totalRightDerivedUnit DerivedCategory.Qh
              (Stacks.Cohomology.DerivedPushforward.sourceQuasiIso
                (smallEtaleRingedTopos B S hS X))) :=
    (modulePushforwardSingleToRightDerived_eq_singleUnit B S hS f _ _).trans
      (Stacks.DerivedFunctor.singleUnit_eqToHom_comp _ _
        (hw₁ := modulePushforward_additive B S hS f)
        (hw₂ := (RingedToposHom.pullbackAdjPushforwardModules
          (smallEtaleRingedToposHom B S hS f)).right_adjoint_additive)
        (pushforwardModules_eq_modulePushforward B S hS f) _ _ _)
  have e₂ := (NatTrans.congr_app e₁ M).trans (NatTrans.comp_app _ _ M)
  unfold SingleCounitCompatible
  refine Exists.elim (@Stacks.DerivedSingleCounit.exists_single_counit_comparison_of_singleUnit
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) _ (SheafOfModules.instAbelian _)
    (HasDerivedCategory.standard _) _ (SheafOfModules.instAbelian _) (HasDerivedCategory.standard _)
    (smallEtaleRingedToposHom B S hS f).pushforwardModules (modulePushforward B S hS f)
    (RingedToposHom.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHom B S hS f)).right_adjoint_additive
    (modulePushforward_additive B S hS f) (pushforwardModules_eq_modulePushforward B S hS f)
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules (modulePullback B S hS f)
    (RingedToposHom.pullbackModules_additive (smallEtaleRingedToposHom B S hS f))
    (modulePullback_additive f)
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS f))
    (modulePullbackAdjunction B S hS f) (smallEtaleDerivedModulePullback B S hS f)
    (Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f))
    (smallEtaleDerivedModuleAdjunction B S hS f) _
    (smallEtaleDerivedModulePullbackComparison B S hS f)
    (smallEtaleDerivedModuleAdjunction_counit_fac B S hS f) G M a ha
    ((singleSpaceToToposIso Y).inv.app G) (singleSpaceToToposIso_inv_app Y G)
    ((derivedPushforwardSpaceToToposIso f).hom.app ((spaceDerivedSingle B S hS X 0).obj M))
    (derivedPushforwardSpaceToToposIso_hom_app f _)
    ((spaceToToposDerived Y).map ((spaceDerivedSingle B S hS Y 0).map a ≫
      (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS f hf M hM).inv)) _ _ _
    ((congrArg (fun t => (spaceToToposDerived Y).map ((spaceDerivedSingle B S hS Y 0).map a ≫ t))
        (e₀.trans e₂)).trans (((spaceToToposDerived Y).map_comp _ _).trans
          (congrArg (_ ≫ ·) ((spaceToToposDerived Y).map_comp _ _))))
    (spaceToToposDerived_map_spaceDerivedSingle Y a)
    (spaceToToposDerived_map Y _) (spaceToToposDerived_map Y _))
    (fun v hv => ⟨v, hv⟩)

end AlgebraicGeometry.Space
