module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorIndependentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryCone

/-!
# A section of `H^{-1}(a'(𝒪_{Y'}))` from a split epimorphism `Rf'_*(𝒪_{X'}[1]) ⟶ 𝒪_{Y'}`

Let `f' : X' ⟶ Y'` be the base change of a morphism of finite presentation `f : X ⟶ Y` to an affine
`Y'`, flat, and let `a'` be the right adjoint of `Rf'_*` (Stacks 0E55). Assume `a'(𝒪_{Y'}) ≅ M[1]`
for a flat `𝒪_{X'}`-module `M`, and that a map `π : Rf'_*(𝒪_{X'}[1]) ⟶ 𝒪_{Y'}` is a split
epimorphism. Under the adjunction `Rf'_* ⊣ a'`, `π` is the trace of a map `𝒪_{X'}[1] ⟶ a'(𝒪_{Y'})`,
that is of a section `σ` of `M`. The restriction of `σ` to every base change `X'' ⟶ Z` of `f'`
with `𝒪_Z ≠ 0` is nonzero: otherwise, by the naturality of the base change map
`Lj^*Rf'_* ⟶ Rf''_*L(j')^*` (Stacks 07A7) and its invertibility for flat `f'` (Stacks 0A1K), the
pullback `Lj^*π` of the split epimorphism `π` would vanish, and with it `Lj^*𝒪_{Y'} = 𝒪_Z`.

This is the duality step of the genus one case of the proof of [Stacks, Tag 0E6Y].

## Main results

* `AlgebraicGeometry.C1764Prereq.exists_section_ne_zero_of_isSplitEpi`: the section `σ`.

## References

* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0E5X](https://stacks.math.columbia.edu/tag/0E5X)
* [Stacks Project, Tag 0E55](https://stacks.math.columbia.edu/tag/0E55)
* [Stacks Project, Tag 0A1K](https://stacks.math.columbia.edu/tag/0A1K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

-- global `HasDerivedCategory` instances in scope compete with the standard model in which the
-- derived functors used here are stated
attribute [-instance] AlgebraicGeometry.RingedSpace.hasDerivedCategoryOXMod
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
  AlgebraicGeometry.SmallEtale.hasDerivedCategory_smallEtaleRingedSite
  Stacks.DerivedQCoh.hasDerivedCategoryQuasicoherent

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

namespace C1764Prereq

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure sheaf placed in degree `-1`, `𝒪_X[1]`, as an object of `D_QCoh(𝒪_X)`. -/
def structureSheafShifted (X : AlgebraicSpaces B S hS) :
    Space.QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 :=
  ⟨(DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS X.1 X.2) (-1)).obj
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B S hS X.1 X.2).O))),
    DerivedCategoryB.derivedCategoryB_singleFunctor_obj _
      (Space.isWeakSerre_isQuasicoherentOnSite X) (-1)
      (SheafOfModules.isQuasicoherentOnSite_unit _)⟩

/-- A morphism whose composite with an isomorphism vanishes is zero. -/
private theorem eq_zero_of_comp_eq_zero_of_isIso {C : Type*} [Category C] [Preadditive C]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (hg : IsIso g) (h : f ≫ g = 0) : f = 0 :=
  (@Preadditive.IsIso.comp_right_eq_zero _ _ _ _ _ _ _ _ hg).1 h

/-- A map of complexes into a K-flat complex with flat terms whose degreewise pullback vanishes
has vanishing derived pullback: the comparison `Lf^* ⟶ f^*` is natural and invertible at the
target. -/
private theorem derivedPullback_map_Qh_map_eq_zero {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {K L : CochainComplex (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y)) ℤ}
    (c : K ⟶ L) (hL : Space.smallEtaleModuleKFlat B S hS Y
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L))
    (hc : ((Space.smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules
      |>.mapHomologicalComplex (ComplexShape.up ℤ)).map c = 0) :
    (Space.smallEtaleDerivedModulePullback B S hS f).map
      (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map c)) = 0 := by
  have hiso := Space.isIso_smallEtaleDerivedModulePullbackComparison_app B S hS f _ hL
  have h3 := (Space.smallEtaleDerivedModulePullbackComparison B S hS f).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map c)
  have key : (Space.smallEtaleModulePullbackOnHomotopy B S hS f).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map c) = 0 := by
    have e : (Space.smallEtaleModulePullbackOnHomotopy B S hS f).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map c) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((Space.smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules
          |>.mapHomologicalComplex (ComplexShape.up ℤ)).map c)) := rfl
    refine e.trans ((congrArg (fun y => DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map y)) hc).trans ?_)
    simp only [Functor.map_zero]
  rw [key, comp_zero] at h3
  exact eq_zero_of_comp_eq_zero_of_isIso hiso h3

/-- A map of modules into a flat module whose pullback vanishes has vanishing derived pullback in
every degree: if `φ : M ⟶ N` with `N` flat and `f^*φ = 0`, then `Lf^*(φ[-i]) = 0`. -/
private theorem derivedPullback_map_singleFunctor_map_eq_zero {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) {M N : SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y)}
    (φ : M ⟶ N) (i : ℤ)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (Space.smallEtaleRingedTopos B S hS Y).O) N)
    (hφ : ((Space.smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).map φ = 0) :
    (Space.smallEtaleDerivedModulePullback B S hS f).map
        ((DerivedCategory.singleFunctor _ i).map φ) = 0 := by
  let c := (CochainComplex.singleFunctor
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y)) i).map φ
  have hc : ((Space.smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules
      |>.mapHomologicalComplex (ComplexShape.up ℤ)).map c = 0 := by
    let F := (Space.smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules
    have h :=
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) i).hom.naturality φ
    simp only [Functor.comp_map] at h
    rwa [hφ, Functor.map_zero, comp_zero, ← Iso.app_hom, ← Iso.eq_comp_inv, zero_comp] at h
  have hflat : ∀ j : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (Space.smallEtaleRingedTopos B S hS Y).O)
      (((CochainComplex.singleFunctor _ i).obj N).X j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
        (HomologicalComplex.singleObjXSelf _ _ N).symm hN
    · exact Space.isFlat_of_isZero B S hS (HomologicalComplex.isZero_single_obj_X _ i N j hj)
  have : ((CochainComplex.singleFunctor _ i).obj N).IsStrictlyLE i := by
    dsimp only [CochainComplex.singleFunctor]
    infer_instance
  have hzero := derivedPullback_map_Qh_map_eq_zero f c
    (Space.smallEtaleModuleKFlat_of_isStrictlyLE B S hS Y _ i hflat) hc
  have h1 := (DerivedCategory.singleFunctorIsoCompQ
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y)) i).hom.naturality φ
  have h2 := (DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y))).hom.naturality c
  simp only [Functor.comp_map] at h1 h2
  have h5 : (DerivedCategory.singleFunctor _ i).map φ =
      (DerivedCategory.singleFunctorIsoCompQ
          (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y)) i).hom.app M ≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y))).inv.app
            ((CochainComplex.singleFunctor _ i).obj M) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map c) ≫
            (DerivedCategory.quotientCompQhIso
              (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y))).hom.app
                ((CochainComplex.singleFunctor _ i).obj N) ≫
              (DerivedCategory.singleFunctorIsoCompQ
                (SheafOfModules.{u} (Space.ringedToposStructureRingSheaf B S hS Y)) i).inv.app
                  N := by
    rw [reassoc_of% h2, Iso.inv_hom_id_app_assoc, ← reassoc_of% h1, Iso.hom_inv_id_app,
      Category.comp_id]
  rw [h5]
  simp only [Functor.map_comp, hzero, zero_comp, comp_zero]

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A section of `M ≅ H^{-1}(a'(𝒪_{Y'}))` from a split epimorphism `Rf'_*(𝒪_{X'}[1]) ⟶ 𝒪_{Y'}`,
nonzero on every base change with nonzero structure sheaf.** For a cartesian square with `f` of
finite presentation, `Y'` affine and `f'` flat, an isomorphism `a'(𝒪_{Y'}) ≅ M[1]` with `M` flat,
and a split epimorphism `π : Rf'_*(𝒪_{X'}[1]) ⟶ 𝒪_{Y'}`, there is `σ : 𝒪_{X'} ⟶ M` whose pullback
to the base change `W = X' ×_{Y'} Z` along every `j : Z ⟶ Y'` with `𝒪_Z ≠ 0` is nonzero. -/
theorem exists_section_ne_zero_of_isSplitEpi {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    (hfp : Space.IsFinitePresentation B S hS f.hom) (hY' : Space.IsAffineSpace B S hS Y'.1)
    (hfl' : Space.IsFlat B S hS f'.hom) (M : Space.Modules.{u, u} B S hS X'.1 X'.2)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (Space.smallEtaleRingedTopos B S hS X').O) M)
    (e : ((Space.affineBaseChangeRightAdjoint hZ sq hfp hY').obj
        (Space.derivedStructureSheaf B S hS Y'.1 Y'.2)).obj ≅
      (DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS X'.1 X'.2) (-1)).obj M)
    (π : (Space.derivedModulePushforward B S hS f').obj (structureSheafShifted X').obj ⟶
      (Space.derivedStructureSheaf B S hS Y'.1 Y'.2).obj) (hπ : IsSplitEpi π) :
    ∃ σ : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B S hS X'.1 X'.2).O)) ⟶ M,
      ∀ ⦃Z W : AlgebraicSpaces B S hS⦄ (q : W ⟶ X') (f'' : W ⟶ Z) (j : Z ⟶ Y'),
        IsPullback q f'' f' j → ¬ IsZero (Space.derivedStructureSheaf B S hS Z.1 Z.2).obj →
          (Space.modulePullback B S hS q).map σ ≠ 0 := by
  obtain ⟨φ, hφ⟩ :=
    Space.exists_affineBaseChangeTrace_comp hZ sq hfp hY' (structureSheafShifted X') π
  refine ⟨(DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS X'.1 X'.2) (-1)).preimage
    (φ ≫ e.hom), ?_⟩
  intro Z W q f'' j sq₂ hne hσ
  set σ := (DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS X'.1 X'.2) (-1)).preimage
    (φ ≫ e.hom)
  have hσ' :
      ((Space.smallEtaleRingedToposHom B S hS q).toModulesHom.pullbackModules).map σ = 0 := by
    rw [Space.pullbackModules_smallEtaleRingedToposHom]
    exact hσ
  have h1 : (Space.smallEtaleDerivedModulePullback B S hS q).map
      ((DerivedCategory.singleFunctor (Space.Modules.{u, u} B S hS X'.1 X'.2) (-1)).map σ) = 0 :=
    derivedPullback_map_singleFunctor_map_eq_zero q σ (-1) hM hσ'
  rw [Functor.map_preimage] at h1
  have h1' : (Space.smallEtaleDerivedModulePullback B S hS q).map φ ≫
      (Space.smallEtaleDerivedModulePullback B S hS q).map e.hom = 0 :=
    ((Space.smallEtaleDerivedModulePullback B S hS q).map_comp φ e.hom).symm.trans h1
  have h2 : (Space.smallEtaleDerivedModulePullback B S hS q).map φ = 0 :=
    eq_zero_of_comp_eq_zero_of_isIso
      (Iso.isIso_hom ((Space.smallEtaleDerivedModulePullback B S hS q).mapIso e)) h1'
  have hqc := Space.isQuasiCompact_of_isPullback_of_isFinitePresentation sq hfp
  have hqs := Space.isQuasiSeparated_of_isPullback_of_isFinitePresentation sq hfp
  have hbc := Space.isIso_smallEtaleDerivedBaseChangeMap_of_isFlat sq₂ hqc hqs hfl'
    (((Space.affineBaseChangeRightAdjoint hZ sq hfp hY').obj
      (Space.derivedStructureSheaf B S hS Y'.1 Y'.2)).obj)
    (((Space.affineBaseChangeRightAdjoint hZ sq hfp hY').obj
      (Space.derivedStructureSheaf B S hS Y'.1 Y'.2)).property)
  have hnat := Space.smallEtaleDerivedModuleBaseChangeMap_naturality B S hS f' j f'' q sq₂.w φ
  have hnat' : (Space.smallEtaleDerivedModulePullback B S hS j).map
      ((Space.derivedModulePushforward B S hS f').map φ) ≫
        Space.smallEtaleDerivedModuleBaseChangeMap B S hS f' j f'' q sq₂.w
          ((Space.affineBaseChangeRightAdjoint hZ sq hfp hY').obj
            (Space.derivedStructureSheaf B S hS Y'.1 Y'.2)).obj = 0 := by
    have : (Space.derivedModulePushforward B S hS f'').IsRightAdjoint :=
      ⟨_, ⟨Space.smallEtaleDerivedModuleAdjunction B S hS f''⟩⟩
    have : (Space.derivedModulePushforward B S hS f'').PreservesZeroMorphisms :=
      Functor.preservesZeroMorphisms_of_isRightAdjoint _
    refine hnat.trans ?_
    refine (congrArg (fun k => Space.smallEtaleDerivedModuleBaseChangeMap B S hS f' j f'' q sq₂.w
      (structureSheafShifted X').obj ≫ (Space.derivedModulePushforward B S hS f'').map k)
        h2).trans ?_
    exact (congrArg (fun k => Space.smallEtaleDerivedModuleBaseChangeMap B S hS f' j f'' q sq₂.w
      (structureSheafShifted X').obj ≫ k)
        ((Space.derivedModulePushforward B S hS f'').map_zero _ _)).trans comp_zero
  have h3 : (Space.smallEtaleDerivedModulePullback B S hS j).map
      ((Space.derivedModulePushforward B S hS f').map φ) = 0 :=
    eq_zero_of_comp_eq_zero_of_isIso hbc hnat'
  have h4 : (Space.smallEtaleDerivedModulePullback B S hS j).map π = 0 :=
    (congrArg (Space.smallEtaleDerivedModulePullback B S hS j).map hφ.symm).trans
      (((Space.smallEtaleDerivedModulePullback B S hS j).map_comp _ _).trans
        ((congrArg (· ≫ (Space.smallEtaleDerivedModulePullback B S hS j).map
          (Space.affineBaseChangeTrace hZ sq hfp hY')) h3).trans zero_comp))
  apply hne
  obtain ⟨⟨r, hr⟩⟩ := instIsSplitEpiMap π (Space.smallEtaleDerivedModulePullback B S hS j)
  have h5 : IsZero ((Space.smallEtaleDerivedModulePullback B S hS j).obj
      (Space.derivedStructureSheaf B S hS Y'.1 Y'.2).obj) := by
    rw [IsZero.iff_id_eq_zero, ← hr, h4, comp_zero]
  exact h5.of_iso (Space.smallEtaleDerivedModulePullbackUnitIso (B := B) (S := S) (hS := hS) j).symm

end C1764Prereq

end AlgebraicGeometry
