module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySingleCompIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardSingle

/-!
# `(f_* F)[0] ≅ Rf_*(F[0])` is compatible with composition

Let `j : X'' ⟶ X'` and `i : X' ⟶ X` be morphisms of ringed spaces along which the direct images
are exact, and let `k = j ≫ i`. The isomorphism
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardSingleIso` for `k` is the one
for `i` at `j_* F`, followed by `Ri_*` of the one for `j`, read through the composition
isomorphisms `j_* ⋙ i_* ≅ k_*` and `Rj_* ⋙ Ri_* ≅ Rk_*`.

## Main results

All in the namespace `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`:

* `derivedPushforwardSingleIso_comp_hom_app`: the compatibility at `k = j ≫ i`.
* `derivedPushforwardSingleIso_comp_hom_app_of_comp_eq`: the same, for `k` given together with a
  proof of `j ≫ i = k`.
* `singleComparison_comp_of_unit_comp`: the chase behind both, in bare categories.

## Implementation notes

The composition isomorphism for derived pushforward is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCompIso`, the uniqueness
isomorphism of right adjoints, transported along `j ≫ i = k` by `eqToIso`; for the direct images
it is `RingedSpaceModuleAdjunction.modulePushforwardComp`, transported the same way. Both live at
the standard model `HasDerivedCategory.standard`, the only model at which
`derivedPushforwardCompIso` is defined; it is installed for the one declaration only.

The proof is the factorization of the comparison along `k` through the comparisons along `i` and
`j`, `derivedPushforwardCompUnit_comp_derivedPushforwardCompIso` (in the namespace
`Stacks.Cohomology.DerivedPushforwardComposition`), together with naturality, and one identity of
cochain complexes concentrated in degree `0`, which follows from the composition and
naturality laws of `HomologicalComplex.singleMapHomologicalComplex`. The naturality chase is
carried out in bare categories (`singleComparison_comp_of_unit_comp`): run directly on the
ringed-space functors, a single rewrite exhausts the heartbeat budget on the `isDefEq` check.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

noncomputable section

section Abstract

variable {A₁ A₂ A₃ H₁ H₂ H₃ D₁ D₂ D₃ : Type*} [Category* A₁] [Category* A₂] [Category* A₃]
  [Category* H₁] [Category* H₂] [Category* H₃] [Category* D₁] [Category* D₂] [Category* D₃]
  {Pj : A₁ ⥤ A₂} {Pi : A₂ ⥤ A₃} {Pk : A₁ ⥤ A₃}
  {Hs₁ : A₁ ⥤ H₁} {Hs₂ : A₂ ⥤ H₂} {Hs₃ : A₃ ⥤ H₃}
  {Qh₁ : H₁ ⥤ D₁} {Qh₂ : H₂ ⥤ D₂} {Qh₃ : H₃ ⥤ D₃}
  {S₁ : A₁ ⥤ D₁} {S₂ : A₂ ⥤ D₂} {S₃ : A₃ ⥤ D₃}
  {Mj : H₁ ⥤ H₂} {Mi : H₂ ⥤ H₃} {Mk : H₁ ⥤ H₃}
  {Rj : D₁ ⥤ D₂} {Ri : D₂ ⥤ D₃} {Rk : D₁ ⥤ D₃}

/-- **The chase behind `derivedPushforwardSingleIso_comp_hom_app`, in bare categories.** Let
`(-)[0]` be presented on three abelian levels as `S_n ≅ Hs_n ⋙ Qh_n`, let the three direct images
`Pj`, `Pi`, `Pk` commute with `Hs` through `hsj`, `hsi`, `hsk`, and let `uj`, `ui`, `uk` be the
comparisons from the induced functors `Mj`, `Mi`, `Mk` on homotopy categories to the derived
functors `Rj`, `Ri`, `Rk`. If the comparison for `k` factors through those for `i` and `j` and the
two composition isomorphisms `cmp` and `ρ` (`hU`), and the commutation for `k` factors through
those for `i` and `j` and `ε` (`hH`), then the isomorphism `(Pk F)[0] ≅ Rk(F[0])` factors through
the ones for `i` and `j`. -/
theorem singleComparison_comp_of_unit_comp
    (σ₁ : S₁ ≅ Hs₁ ⋙ Qh₁) (σ₂ : S₂ ≅ Hs₂ ⋙ Qh₂) (σ₃ : S₃ ≅ Hs₃ ⋙ Qh₃)
    (hsj : Hs₁ ⋙ Mj ≅ Pj ⋙ Hs₂) (hsi : Hs₂ ⋙ Mi ≅ Pi ⋙ Hs₃) (hsk : Hs₁ ⋙ Mk ≅ Pk ⋙ Hs₃)
    (uj : Mj ⋙ Qh₂ ⟶ Qh₁ ⋙ Rj) (ui : Mi ⋙ Qh₃ ⟶ Qh₂ ⋙ Ri) (uk : Mk ⋙ Qh₃ ⟶ Qh₁ ⋙ Rk)
    (cmp : Mj ⋙ Mi ≅ Mk) (ρ : Rj ⋙ Ri ≅ Rk) (F : A₁) (ε : Pk.obj F ⟶ Pi.obj (Pj.obj F))
    (hU : Qh₃.map (cmp.inv.app (Hs₁.obj F)) ≫ ui.app (Mj.obj (Hs₁.obj F)) ≫
        Ri.map (uj.app (Hs₁.obj F)) ≫ ρ.hom.app (Qh₁.obj (Hs₁.obj F)) = uk.app (Hs₁.obj F))
    (hH : hsk.inv.app F ≫ cmp.inv.app (Hs₁.obj F) =
      Hs₃.map ε ≫ hsi.inv.app (Pj.obj F) ≫ Mi.map (hsj.inv.app F)) :
    σ₃.hom.app (Pk.obj F) ≫ Qh₃.map (hsk.inv.app F) ≫ uk.app (Hs₁.obj F) ≫
        Rk.map (σ₁.inv.app F) =
      S₃.map ε ≫ (σ₃.hom.app (Pi.obj (Pj.obj F)) ≫ Qh₃.map (hsi.inv.app (Pj.obj F)) ≫
          ui.app (Hs₂.obj (Pj.obj F)) ≫ Ri.map (σ₂.inv.app (Pj.obj F))) ≫
        Ri.map (σ₂.hom.app (Pj.obj F) ≫ Qh₂.map (hsj.inv.app F) ≫ uj.app (Hs₁.obj F) ≫
          Rj.map (σ₁.inv.app F)) ≫ ρ.hom.app (S₁.obj F) := by
  have hn := ui.naturality (hsj.inv.app F)
  have hρ := ρ.hom.naturality (σ₁.inv.app F)
  have hσ := σ₃.hom.naturality ε
  simp only [Functor.comp_map, Functor.comp_obj] at hn hρ hσ
  rw [← hU]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hρ, ← Ri.map_comp_assoc (σ₂.inv.app (Pj.obj F)), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, ← reassoc_of% hn, reassoc_of% hσ]
  have hQ : Qh₃.map (hsk.inv.app F) ≫ Qh₃.map (cmp.inv.app (Hs₁.obj F)) =
      Qh₃.map (Hs₃.map ε) ≫ Qh₃.map (hsi.inv.app (Pj.obj F)) ≫
        Qh₃.map (Mi.map (hsj.inv.app F)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hH]
  rw [reassoc_of% hQ]

end Abstract

variable {X'' X' X : RingedSpace.{u, u}} (j : X'' ⟶ X') (i : X' ⟶ X)

/-- The identity of cochain complexes behind `derivedPushforwardSingleIso_comp_hom_app`: the
comparison of `(-)[0]` with `k_*`, followed by the composition isomorphism of the direct images,
is the comparison for `i` at `j_* F` followed by `i_*` of the comparison for `j`. -/
private theorem singleMapHomologicalComplex_modulePushforwardComp
    (F : SheafOfModules.{u} (structureSheafRing X'')) :
    (HomologicalComplex.singleMapHomologicalComplex (modulePushforward (j ≫ i))
        (ComplexShape.up ℤ) 0).inv.app F ≫
      (NatTrans.mapHomologicalComplex (modulePushforwardComp j i).inv (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) =
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        ((modulePushforwardComp j i).inv.app F) ≫
      (HomologicalComplex.singleMapHomologicalComplex (modulePushforward i)
        (ComplexShape.up ℤ) 0).inv.app ((modulePushforward j).obj F) ≫
      ((modulePushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward j)
          (ComplexShape.up ℤ) 0).inv.app F) := by
  have hN := HomologicalComplex.singleMapHomologicalComplex_natTrans (ComplexShape.up ℤ)
    (modulePushforwardComp j i).inv 0 F
  have hC := HomologicalComplex.singleMapHomologicalComplex_comp (c := ComplexShape.up ℤ)
    (modulePushforward j) (modulePushforward i) 0 F
  have hI : (HomologicalComplex.singleMapHomologicalComplex
      (modulePushforward j ⋙ modulePushforward i) (ComplexShape.up ℤ) 0).app F =
      ((modulePushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward j)
            (ComplexShape.up ℤ) 0).app F) ≪≫
        (HomologicalComplex.singleMapHomologicalComplex (modulePushforward i)
          (ComplexShape.up ℤ) 0).app ((modulePushforward j).obj F) :=
    Iso.ext hC.symm
  have hC' := congrArg Iso.inv hI
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at hC'
  rw [← hC', ← cancel_mono ((HomologicalComplex.singleMapHomologicalComplex
    (modulePushforward j ⋙ modulePushforward i) (ComplexShape.up ℤ) 0).hom.app F),
    Category.assoc, hN, Iso.inv_hom_id_app_assoc, Category.assoc, Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

/-- The identity of the homotopy category behind `derivedPushforwardSingleIso_comp_hom_app`: the
commutation of `k_*` with `(-)[0]`, followed by the composition isomorphism of the induced
functors, is the commutation for `i` at `j_* F` followed by `i_*` of the commutation for `j`. -/
private theorem mapHomotopyCategorySingleFunctorIso_modulePushforwardComp
    (F : SheafOfModules.{u} (structureSheafRing X'')) :
    ((modulePushforward (j ≫ i)).mapHomotopyCategorySingleFunctorIso 0).inv.app F ≫
      (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp j i) (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.singleFunctor _ 0).obj F) =
    (HomotopyCategory.singleFunctor _ 0).map ((modulePushforwardComp j i).inv.app F) ≫
      ((modulePushforward i).mapHomotopyCategorySingleFunctorIso 0).inv.app
        ((modulePushforward j).obj F) ≫
      ((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((modulePushforward j).mapHomotopyCategorySingleFunctorIso 0).inv.app F) := by
  have h1 : (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp j i)
      (ComplexShape.up ℤ)).inv.app ((HomotopyCategory.singleFunctor _ 0).obj F) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (modulePushforwardComp j i).inv (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)) := rfl
  have h2 : (HomotopyCategory.singleFunctor _ 0).map ((modulePushforwardComp j i).inv.app F) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          ((modulePushforwardComp j i).inv.app F)) := rfl
  have h3 : ((modulePushforward i).mapHomotopyCategory (ComplexShape.up ℤ)).map
      (((modulePushforward j).mapHomotopyCategorySingleFunctorIso 0).inv.app F) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((modulePushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward j)
            (ComplexShape.up ℤ) 0).inv.app F)) := by
    rw [Functor.mapHomotopyCategorySingleFunctorIso_inv_app]
    exact Functor.mapHomotopyCategory_map _ _
  rw [h1, h2, h3, Functor.mapHomotopyCategorySingleFunctorIso_inv_app,
    Functor.mapHomotopyCategorySingleFunctorIso_inv_app]
  refine ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).symm.trans
    (((congrArg (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (singleMapHomologicalComplex_modulePushforwardComp j i F))).trans
      (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).trans ?_))
  exact congrArg (_ ≫ ·) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _)

attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`((j ≫ i)_* F)[0] ≅ R(j ≫ i)_*(F[0])` factors.** For morphisms of ringed spaces
`j : X'' ⟶ X'` and `i : X' ⟶ X` along which the direct images, and the direct image along
`j ≫ i`, are exact, the isomorphism `derivedPushforwardSingleIso` for `j ≫ i` at a module `F` on
`X''` is: the composition isomorphism `((j ≫ i)_* F)[0] ≅ (i_* j_* F)[0]` of the direct images
(`RingedSpaceModuleAdjunction.modulePushforwardComp`), then the isomorphism for `i` at `j_* F`,
then `Ri_*` of the isomorphism for `j` at `F`, then the composition isomorphism
`Ri_*(Rj_*(F[0])) ≅ R(j ≫ i)_*(F[0])` of the derived pushforwards (`derivedPushforwardCompIso`).

`derivedPushforwardSingleIso_comp_hom_app_of_comp_eq` is the same statement for a morphism `k`
given with a proof of `j ≫ i = k`. Stated at the standard model `HasDerivedCategory.standard`, the
model of `derivedPushforwardCompIso`, installed for this declaration only. -/
theorem derivedPushforwardSingleIso_comp_hom_app
    [PreservesFiniteColimits (modulePushforward j)] [PreservesFiniteColimits (modulePushforward i)]
    [PreservesFiniteColimits (modulePushforward (j ≫ i))]
    (F : SheafOfModules.{u} (structureSheafRing X'')) :
    (derivedPushforwardSingleIso (j ≫ i)).hom.app F =
      (DerivedCategory.singleFunctor _ 0).map ((modulePushforwardComp j i).inv.app F) ≫
        (derivedPushforwardSingleIso i).hom.app ((modulePushforward j).obj F) ≫
        (derivedPushforward i).map ((derivedPushforwardSingleIso j).hom.app F) ≫
        (derivedPushforwardCompIso j i).hom.app ((DerivedCategory.singleFunctor _ 0).obj F) := by
  have hU : (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        (modulePushforwardComp j i) (ComplexShape.up ℤ)).inv.app
          ((HomotopyCategory.singleFunctor _ 0).obj F)) ≫
      (derivedPushforwardUnit i).app (((modulePushforward j).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj ((HomotopyCategory.singleFunctor _ 0).obj F)) ≫
      (derivedPushforward i).map ((derivedPushforwardUnit j).app
        ((HomotopyCategory.singleFunctor _ 0).obj F))) ≫
      (derivedPushforwardCompIso j i).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.singleFunctor _ 0).obj F)) =
      (derivedPushforwardUnit (j ≫ i)).app ((HomotopyCategory.singleFunctor _ 0).obj F) :=
    DerivedPushforwardComposition.derivedPushforwardCompUnit_comp_derivedPushforwardCompIso
      j i ((HomotopyCategory.singleFunctor _ 0).obj F)
  simp only [Category.assoc] at hU
  have hH := mapHomotopyCategorySingleFunctorIso_modulePushforwardComp j i F
  simp only [derivedPushforwardSingleIso_hom_app]
  exact singleComparison_comp_of_unit_comp (DerivedCategory.singleFunctorIsoCompQh _ 0)
    (DerivedCategory.singleFunctorIsoCompQh _ 0) (DerivedCategory.singleFunctorIsoCompQh _ 0)
    ((modulePushforward j).mapHomotopyCategorySingleFunctorIso 0)
    ((modulePushforward i).mapHomotopyCategorySingleFunctorIso 0)
    ((modulePushforward (j ≫ i)).mapHomotopyCategorySingleFunctorIso 0)
    (derivedPushforwardUnit j) (derivedPushforwardUnit i) (derivedPushforwardUnit (j ≫ i))
    (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp j i) (ComplexShape.up ℤ))
    (derivedPushforwardCompIso j i) F ((modulePushforwardComp j i).inv.app F) hU hH


attribute [local instance 10000] HasDerivedCategory.standard in
/-- **`(k_* F)[0] ≅ Rk_*(F[0])` along a composite `k = j ≫ i`.** For morphisms of ringed spaces
`j : X'' ⟶ X'` and `i : X' ⟶ X` along which the direct images are exact, and `k` with
`j ≫ i = k` along which the direct image is exact too, the isomorphism
`derivedPushforwardSingleIso` for `k` at a module `F` on `X''` is: the composition isomorphism
`(k_* F)[0] ≅ (i_* j_* F)[0]` of the direct images, then the isomorphism for `i` at `j_* F`, then
`Ri_*` of the isomorphism for `j` at `F`, then the composition isomorphism
`Ri_*(Rj_*(F[0])) ≅ Rk_*(F[0])` of the derived pushforwards.

The two composition isomorphisms are `RingedSpaceModuleAdjunction.modulePushforwardComp` and
`derivedPushforwardCompIso`, each transported along `j ≫ i = k` by `eqToIso`; at `k = j ≫ i` this
is `derivedPushforwardSingleIso_comp_hom_app`. Stated at the standard model
`HasDerivedCategory.standard`, the model of `derivedPushforwardCompIso`, installed for this
declaration only. -/
theorem derivedPushforwardSingleIso_comp_hom_app_of_comp_eq (k : X'' ⟶ X) (hk : j ≫ i = k)
    [PreservesFiniteColimits (modulePushforward j)] [PreservesFiniteColimits (modulePushforward i)]
    [PreservesFiniteColimits (modulePushforward k)]
    (F : SheafOfModules.{u} (structureSheafRing X'')) :
    (derivedPushforwardSingleIso k).hom.app F =
      (DerivedCategory.singleFunctor _ 0).map
          ((modulePushforwardComp j i ≪≫
            eqToIso (congrArg (fun h : X'' ⟶ X => modulePushforward h) hk)).inv.app F) ≫
        (derivedPushforwardSingleIso i).hom.app ((modulePushforward j).obj F) ≫
        (derivedPushforward i).map ((derivedPushforwardSingleIso j).hom.app F) ≫
        (derivedPushforwardCompIso j i ≪≫
          eqToIso (congrArg (fun h : X'' ⟶ X => derivedPushforward h) hk)).hom.app
            ((DerivedCategory.singleFunctor _ 0).obj F) := by
  subst hk
  simp only [eqToIso_refl, Iso.trans_refl]
  exact derivedPushforwardSingleIso_comp_hom_app j i F

end

end Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

end
