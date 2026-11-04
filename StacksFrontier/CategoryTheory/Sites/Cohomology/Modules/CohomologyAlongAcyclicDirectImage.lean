module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalenceModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringModuleDerivedGlobalSections
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdditivityOfDirectAndInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.LerayCollapse
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardGlobalSections

/-!
# Cohomology of a pullback along a morphism of ringed topoi with acyclic direct image

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi of small sites. Global sections
are unchanged by the direct image, `Γ(D, f_*M) = Γ(C, M)` (Cohomology on Sites, Remark 08J6,
underived), and the direct image of an injective module is acyclic for global sections
(Stacks 072Z). Hence if `R^q f_*M = 0` for `q > 0` the cohomology of `M` on `C` is the cohomology
of `f_*M` on `D` (Stacks 0733, part (1)). Applied to `M = f^*F` for a sheaf of `O_D`-modules `F`
such that `F ⟶ Rf_*(f^*F)` is an isomorphism, this gives

`H^n(D, F) = H^n(C, f^*F)`.

This is the form in which a cohomological descent statement `F = Rf_*f^*F` is read on cohomology
groups. It applies in particular to an equivalence of ringed topoi, for which every unit is
invertible and every higher direct image vanishes.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.pushforwardModulesToSheafIso`: the underlying abelian sheaf
  of `f_*M` is the abelian direct image of the underlying abelian sheaf of `M`.
* `AlgebraicGeometry.RingedToposHom.pushforwardModuleGlobalSectionsIso`:
  `Γ(D, f_* -) ≅ Γ(C, -)` on sheaves of modules, with values in abelian groups.
* `AlgebraicGeometry.RingedToposHom.rightDerivedModuleGlobalSectionsIsoOfAcyclic`:
  `H^n(C, M) = H^n(D, f_*M)` when the higher direct images of `M` vanish.
* `AlgebraicGeometry.RingedToposHom.rightDerivedModuleGlobalSectionsPullbackIso`:
  `H^n(D, F) = H^n(C, f^*F)` when the unit `F ⟶ f_*f^*F` is invertible and the higher direct
  images of `f^*F` vanish.
* `AlgebraicGeometry.RingedToposHom.rightDerivedModuleGlobalSectionsPullbackIsoOfIsEquivalence`:
  `H^n(D, -) ≅ H^n(C, f^* -)`, naturally, along an equivalence of ringed topoi.

## Main results

* `RingedToposHom.isZero_rightDerived_moduleGlobalSections_pushforwardModules_of_injective`:
  the direct image of an injective module has no higher cohomology on `D`.

## Implementation notes

Cohomology `H^n(-, M)` of a sheaf of modules is the `n`-th right derived functor, in Mathlib's
sense, of global sections of the underlying abelian sheaf,
`AlgebraicGeometry.RingedTopos.moduleGlobalSections`.

## References

* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  (f : RingedToposHom X Y)

/-- **The underlying abelian sheaf of a direct image of modules is the abelian direct image of the
underlying abelian sheaf**: on underlying sheaves of sets the direct image of modules is the
direct image of the morphism of topoi. -/
def pushforwardModulesToSheafIso [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    f.pushforwardModules ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙
        Stacks.Topos.AbelianPushforward.abelianPushforward X.J f.toToposHom := by
  haveI : HasBinaryBiproducts (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  exact @Stacks.Cohomology.abelianSheafNatIsoOfUnderlying _ _ _ _ _ _ _ _ _ inferInstance
    ⟨fun {_ _ g h} =>
      ((Stacks.Topos.AbelianPushforward.abelianPushforward X.J f.toToposHom).congr_map
        ((SheafOfModules.toSheaf _).map_add (f := g) (g := h))).trans
          ((Stacks.Topos.AbelianPushforward.abelianPushforward X.J f.toToposHom).map_add)⟩
    (Iso.refl _)

section

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`Γ(D, f_*M) = Γ(C, M)`**, naturally in the sheaf of `O_C`-modules `M`, with the module
structure forgotten: the underlying abelian sheaf of `f_*M` is the abelian direct image of that
of `M`, and global sections of an abelian direct image along a morphism of topoi are global
sections on the source (Cohomology on Sites, Remark 08J6, underived). -/
def pushforwardModuleGlobalSectionsIso :
    f.pushforwardModules ⋙ Y.moduleGlobalSections ≅ X.moduleGlobalSections :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight f.pushforwardModulesToSheafIso (Sheaf.Γ Y.J AddCommGrpCat.{u}) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.Topos.AbelianPushforward.abelianPushforwardΓIso X.J f.toToposHom)

/-- The direct image of sheaves of modules is left exact, being a right adjoint. -/
instance preservesFiniteLimits_pushforwardModules :
    PreservesFiniteLimits f.pushforwardModules :=
  haveI : PreservesLimitsOfSize.{0, 0} f.pushforwardModules :=
    (pullbackAdjPushforwardModules f).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- **The direct image of an injective module has no higher cohomology** (Stacks 072Z): for an
injective sheaf of `O_C`-modules `Z`, `H^n(D, f_*Z) = 0` for `n > 0`. -/
theorem isZero_rightDerived_moduleGlobalSections_pushforwardModules_of_injective
    [HasSheafify Y.J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf Y.J AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf Y.J AddCommGrpCat.{u})]
    [HasInjectiveResolutions (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hZ : Injective Z) (n : ℕ) (hn : 0 < n) :
    IsZero ((Y.moduleGlobalSections.rightDerived n).obj (f.pushforwardModules.obj Z)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  have h := Stacks.Cohomology.isZero_rightDerived_moduleGlobalSections_of_isTotallyAcyclic
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    ((Stacks.Sheaves.RingedToposModules.pushforwardModules f.toModulesHom).obj Z)
    (Stacks.Cohomology.Leray.isTotallyAcyclic_pushforward_injective _ Z hZ) m
  simpa using h.of_iso ((Y.moduleGlobalSections.rightDerived (m + 1)).mapIso
    (f.toModulesPushforwardIso.app Z).symm)

variable [HasSheafify Y.J AddCommGrpCat.{u}] [HasExt.{u} (Sheaf Y.J AddCommGrpCat.{u})]
  [HasInjectiveResolutions (Sheaf Y.J AddCommGrpCat.{u})]
  [HasInjectiveResolutions (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

/-- **`H^n(C, M) = H^n(D, f_*M)` when the higher direct images of `M` vanish** (Stacks 0733,
part (1)): the direct image of an injective resolution of `M` is a resolution of `f_*M` by objects
acyclic for global sections on `D`, so it computes the cohomology of `f_*M`. -/
def rightDerivedModuleGlobalSectionsIsoOfAcyclic
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hM : ∀ q, 0 < q → IsZero ((f.pushforwardModules.rightDerived q).obj M))
    (n : ℕ) :
    (X.moduleGlobalSections.rightDerived n).obj M ≅
      (Y.moduleGlobalSections.rightDerived n).obj (f.pushforwardModules.obj M) :=
  haveI : HasInjectiveResolutions
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) := inferInstance
  ((ModuleSheafCohomology.rightDerivedIso (pushforwardModuleGlobalSectionsIso f) n).app M).symm ≪≫
    Stacks.RightDerivedComp.objIsoOfAcyclicImage f.pushforwardModules Y.moduleGlobalSections hM
      (fun Z hZ q hq =>
        isZero_rightDerived_moduleGlobalSections_pushforwardModules_of_injective f Z hZ q hq) n

/-- **`H^n(D, F) = H^n(C, f^*F)`** for a sheaf of `O_D`-modules `F` such that the unit
`F ⟶ f_*f^*F` is invertible and the higher direct images of `f^*F` vanish, that is, such that
`F ⟶ Rf_*(f^*F)` is an isomorphism. -/
def rightDerivedModuleGlobalSectionsPullbackIso
    [HasInjectiveResolutions (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hunit : IsIso ((pullbackAdjPushforwardModules f).unit.app F))
    (hvanish : ∀ q, 0 < q → IsZero ((f.pushforwardModules.rightDerived q).obj
      (f.toModulesHom.pullbackModules.obj F)))
    (n : ℕ) :
    (Y.moduleGlobalSections.rightDerived n).obj F ≅
      (X.moduleGlobalSections.rightDerived n).obj (f.toModulesHom.pullbackModules.obj F) :=
  (Y.moduleGlobalSections.rightDerived n).mapIso
      (asIso ((pullbackAdjPushforwardModules f).unit.app F)) ≪≫
    (rightDerivedModuleGlobalSectionsIsoOfAcyclic f _ hvanish n).symm

end

section Equivalence

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]

/-- **Global sections are unchanged by the pullback along an equivalence of ringed topoi**:
`Γ(D, -) ≅ Γ(C, f^* -)`, since `f^*` is a quasi-inverse of `f_*` and `Γ(D, f_* -) = Γ(C, -)`. -/
def moduleGlobalSectionsPullbackIsoOfIsEquivalence :
    Y.moduleGlobalSections ≅ f.toModulesHom.pullbackModules ⋙ X.moduleGlobalSections :=
  haveI : IsIso (pullbackAdjPushforwardModules f).unit :=
    (pullbackAdjPushforwardModules f).unit_isIso_of_L_fully_faithful
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (asIso (pullbackAdjPushforwardModules f).unit) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (pushforwardModuleGlobalSectionsIso f)

/-- **Cohomology is unchanged by the pullback along an equivalence of ringed topoi**:
`H^n(D, -) ≅ H^n(C, f^* -)`, naturally, since `f^*` is an equivalence of the categories of
modules carrying global sections to global sections. -/
def rightDerivedModuleGlobalSectionsPullbackIsoOfIsEquivalence
    [HasInjectiveResolutions (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasInjectiveResolutions (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
    (n : ℕ) :
    Y.moduleGlobalSections.rightDerived n ≅
      f.toModulesHom.pullbackModules ⋙ X.moduleGlobalSections.rightDerived n :=
  haveI : f.toModulesHom.pullbackModules.asEquivalence.functor.Additive :=
    (pullbackAdjPushforwardModules f).left_adjoint_additive
  ModuleSheafCohomology.rightDerivedIso (moduleGlobalSectionsPullbackIsoOfIsEquivalence f) n ≪≫
    f.toModulesHom.pullbackModules.asEquivalence.compRightDerivedIso X.moduleGlobalSections n

end Equivalence

end AlgebraicGeometry.RingedToposHom

end
