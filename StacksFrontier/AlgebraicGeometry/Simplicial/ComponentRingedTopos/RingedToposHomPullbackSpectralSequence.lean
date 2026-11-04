module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationPullbackCohomologySpectralSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyAlongAcyclicDirectImage

/-!
# The cohomology spectral sequence of a module pulled back to a simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE) with a sheaf of rings `O` on its total site,
and let `f : (Sh(C_total), O) ⟶ (Sh(D), O_D)` be any morphism of ringed topoi, with component
morphisms `f_p = f ∘ g_p : (Sh(C_p), O_p) ⟶ (Sh(D), O_D)`, where `g_p` is the morphism of
Stacks 0D72. For a sheaf of `O_D`-modules `F` the spectral sequence of Stacks 0D7E, applied to
`f^*F` placed in degree zero, has first page

`E_1^{p,q} = H^q(C_p, f_p^*F)`,

and it converges to `H^{p+q}(C_total, f^*F)`. If moreover `F ⟶ Rf_*(f^*F)` is an isomorphism, that
is if the unit `F ⟶ f_*f^*F` is invertible and the higher direct images of `f^*F` vanish, then
`H^n(D, F) = H^n(C_total, f^*F)` and the spectral sequence converges to `H^{p+q}(D, F)`.

Here `H^q(C, -)` is the `q`-th right derived functor of global sections of the underlying abelian
sheaf, `AlgebraicGeometry.RingedTopos.moduleGlobalSections`, and the abutment is indexed by all
integers and is zero in negative degrees.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.ringedToposHomPullbackSpectralSequence`: the spectral
  sequence, as a functor of the sheaf of `O_D`-modules `F`.
* `CategoryTheory.SimplicialSiteSituation.ringedToposHomPullbackSpectralSequencePageOneIso`: its
  first page `E_1^{p,q} = H^q(C_p, f_p^*F)`, naturally in `F`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isZero_ringedToposHomPullbackSpectralSequence_page_one`:
  the first page vanishes outside the first quadrant.
* `CategoryTheory.SimplicialSiteSituation.abutsTo_ringedToposHomPullbackSpectralSequence_total`:
  convergence to `H^{p+q}(C_total, f^*F)`.
* `CategoryTheory.SimplicialSiteSituation.abutsTo_ringedToposHomPullbackSpectralSequence`:
  convergence to `H^{p+q}(D, F)` when `F ⟶ Rf_*(f^*F)` is an isomorphism.

## References

* [Stacks Project, Tag 0D7E](https://stacks.math.columbia.edu/tag/0D7E)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  {Y : RingedTopos.{u, u, u}} [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  (f : RingedToposHom (S.totalRingedTopos O) Y)

/-- Restriction of sheaves of modules from the total site to the component `C_p` is additive. -/
local instance (O : Sheaf S.totalTopology RingCat.{u}) (p : SimplexCategory) :
    (componentModuleRestriction S O p).Additive := ⟨rfl⟩

/-- Restriction of sheaves of modules from the total site to the component `C_p` preserves finite
limits. -/
local instance (O : Sheaf S.totalTopology RingCat.{u}) (p : SimplexCategory) :
    PreservesFiniteLimits (componentModuleRestriction S O p) :=
  (componentModuleRestriction_exact O p).1

/-- Restriction of sheaves of modules from the total site to the component `C_p` preserves finite
colimits. -/
local instance (O : Sheaf S.totalTopology RingCat.{u}) (p : SimplexCategory) :
    PreservesFiniteColimits (componentModuleRestriction S O p) :=
  (componentModuleRestriction_exact O p).2

attribute [local instance] HasDerivedCategory.standard

/-- The spectral sequence of a module pulled back to a simplicial site, as a functor of the sheaf
of `O_D`-modules `F`: the spectral sequence of Stacks 0D7E for the pullback `f^*F` placed in
degree zero, along a morphism of ringed topoi `f : (Sh(C_total), O) ⟶ (Sh(D), O_D)`. -/
def ringedToposHomPullbackSpectralSequence :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      CohomologicalSpectralSequence AddCommGrpCat.{u} 1 :=
  f.toModulesHom.pullbackModules ⋙
    DerivedCategory.Plus.singleFunctor _ 0 ⋙
      moduleCohomologySpectralSequence S
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)

/-- The identification `E_1^{p,q} = H^q(C_p, f_p^*F)` of the first page, natural in `F`, where
`f_p = f ∘ g_p` is the composite with the morphism `g_p` of Stacks 0D72. -/
def ringedToposHomPullbackSpectralSequencePageOneIso (p q : ℕ) :
    ringedToposHomPullbackSpectralSequence S O f ⋙
        (CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{u} _ 1 1 le_rfl ⋙
          HomologicalComplex.eval AddCommGrpCat.{u} _ ((p : ℤ), (q : ℤ))) ≅
      (f.comp (componentRingedToposHom S O ⦋p⦌)).toModulesHom.pullbackModules ⋙
        (S.componentRingedTopos O ⦋p⦌).moduleGlobalSections.rightDerived q :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft f.toModulesHom.pullbackModules
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
          (moduleCohomologySpectralSequencePageOneIso S
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O) p q)) ≪≫
    Functor.isoWhiskerLeft f.toModulesHom.pullbackModules
      (singleComponentCohomologyIso _ p q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((RingedToposHom.pullbackModulesCompIso
      (componentRingedToposHom S O ⦋p⦌) f ≪≫
      Functor.isoWhiskerLeft _ (componentPullbackModulesRestrictionIso S O ⦋p⦌)).symm) _

/-- The first page vanishes outside the first quadrant. -/
theorem isZero_ringedToposHomPullbackSpectralSequence_page_one
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero ((((ringedToposHomPullbackSpectralSequence S O f).obj F).page 1 le_rfl).X (p, q)) := by
  by_cases hp : p < 0
  · exact isZero_moduleCohomologySpectralSequence_page_one S
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O) _ p q hp
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp hp)
    let X := f.toModulesHom.pullbackModules.obj F
    refine IsZero.of_iso ?_ ((moduleCohomologySpectralSequencePageOneIso S
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O) m q).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj X))
    refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q).mapIso
      ((SheafOfModules.toSheaf (componentRingSheaf S
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O) ⦋m⦌) ⋙
        Sheaf.Γ (S.componentTopology ⦋m⦌) AddCommGrpCat.{u}).rightDerivedFunctorPlus.mapIso
        ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (componentModuleRestriction S
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O) ⦋m⦌) 0).app X)))
    have : ((componentModuleRestriction S
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O) ⦋m⦌ ⋙
        DerivedCategory.Plus.singleFunctor _ 0).obj X).IsGE 0 :=
      (inferInstance : ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((componentModuleRestriction S
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O) ⦋m⦌).obj X)).IsGE 0)
    have := Functor.isGE_rightDerivedFunctorPlus_obj
      (SheafOfModules.toSheaf (componentRingSheaf S
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O) ⦋m⦌) ⋙
        Sheaf.Γ (S.componentTopology ⦋m⦌) AddCommGrpCat.{u})
      ((componentModuleRestriction S
          (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O) ⦋m⦌ ⋙
        DerivedCategory.Plus.singleFunctor _ 0).obj X) 0
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q (h.resolve_left hp)

/-- The spectral sequence converges to `H^{p+q}(C_total, f^*F)`. -/
theorem abutsTo_ringedToposHomPullbackSpectralSequence_total
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    CategoryTheory.SpectralSequence.AbutsTo ((ringedToposHomPullbackSpectralSequence S O f).obj F)
      (fun n => if 0 ≤ n then
        ((S.totalRingedTopos O).moduleGlobalSections.rightDerived n.toNat).obj
          (f.toModulesHom.pullbackModules.obj F)
        else AddCommGrpCat.of PUnit.{u + 1}) :=
  (abutsTo_moduleCohomologySpectralSequence S
    (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (f.toModulesHom.pullbackModules.obj F))).of_iso fun n =>
    Stacks.DerivedIndexing.homologyRightDerivedFunctorPlusSingleIso _ _ n

/-- The spectral sequence converges to `H^{p+q}(D, F)` as soon as `F ⟶ Rf_*(f^*F)` is an
isomorphism, that is, the unit `F ⟶ f_*f^*F` is invertible and the higher direct images of `f^*F`
vanish. -/
theorem abutsTo_ringedToposHomPullbackSpectralSequence
    [HasWeakSheafify S.totalTopology AddCommGrpCat.{u}]
    [S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify Y.J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf Y.J AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf Y.J AddCommGrpCat.{u})]
    [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hunit : IsIso ((RingedToposHom.pullbackAdjPushforwardModules f).unit.app F))
    (hvanish : ∀ q, 0 < q → IsZero ((f.pushforwardModules.rightDerived q).obj
      (f.toModulesHom.pullbackModules.obj F))) :
    CategoryTheory.SpectralSequence.AbutsTo ((ringedToposHomPullbackSpectralSequence S O f).obj F)
      (fun n => if 0 ≤ n then (Y.moduleGlobalSections.rightDerived n.toNat).obj F
        else AddCommGrpCat.of PUnit.{u + 1}) :=
  (abutsTo_ringedToposHomPullbackSpectralSequence_total S O f F).of_nonempty_iso fun n => by
    split_ifs
    · exact ⟨(f.rightDerivedModuleGlobalSectionsPullbackIso F hunit hvanish n.toNat).symm⟩
    · exact ⟨Iso.refl _⟩

end CategoryTheory.SimplicialSiteSituation

end
