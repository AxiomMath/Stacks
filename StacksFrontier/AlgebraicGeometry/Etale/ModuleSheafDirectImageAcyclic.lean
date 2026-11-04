module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekProperDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekDerivedTorsion
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedLowerShriekCompactification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.CompactGenerationOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of sheaves of `Λ`-modules on the small étale sites of a big étale site

Let `B` be a big étale site, `h : Y ⟶ Z` a morphism of it and `Λ` a ring. The direct image of
sheaves of `Λ`-modules on the small étale sites is the `Λ`-linear lift
`AlgebraicGeometry.SmallEtale.etalePushforwardMod` of the direct image of abelian sheaves. This
file shows that its higher direct images are computed on the underlying abelian sheaves:

`R^q h_*(M)_ab = R^q h_*(M_ab)`.

The input is [Stacks, Tag 03FD]: the underlying abelian sheaf of an injective sheaf of
`Λ`-modules is acyclic for direct image. It is read through the identification of sheaves of
`Λ`-modules with sheaves of modules over the constant sheaf of rings `Λ̲`, as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing` for Mathlib's small
étale sites.

The application is to the direct image with compact support: for `h` proper, `f` and `f ≫ h`
locally quasi-finite and `M` a torsion sheaf of `Λ`-modules, `R^q h_*(f_! M) = 0` for `q > 0`
([Stacks, Tag 0F7G], [Stacks, Tag 0F7B]).

## Main definitions

* `AlgebraicGeometry.SmallEtale.moduleSheafConstantRing`: the constant sheaf of rings `Λ̲`.
* `AlgebraicGeometry.SmallEtale.moduleSheafConstantRingEquivalence`: sheaves of `Λ`-modules are
  sheaves of modules over `Λ̲`.
* `AlgebraicGeometry.SmallEtale.rightDerivedEtalePushforwardModForgetIso`: the comparison
  `R^q h_* ⋙ forget ≅ forget ⋙ R^q h_*`.

## Main results

* `SmallEtale.isZero_rightDerived_etalePushforward_forgetModuleSheaf_of_injective`:
  [Stacks, Tag 03FD] for direct images on the small étale sites of a big étale site.
* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforwardMod_fShriekMod`:
  `R^q h_*(f_! M) = 0` for `q > 0`, for sheaves of `Λ`-modules.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.ConstantRing

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (Λ : Type u) [Ring Λ]

attribute [local instance] SmallEtale.isGrothendieckAbelian_sheaf_succ

/-- Sheaves of `Λ`-modules on the small étale site of an object of a big étale site form a
Grothendieck abelian category, at the coefficient universe of the objects of the site. -/
instance isGrothendieckAbelian_moduleSheaf_succ (S : B.Scheme) :
    IsGrothendieckAbelian.{u + 1} (ModuleSheaf.{u, u, u} B S Λ) :=
  isGrothendieckAbelian_moduleSheaf.{u, u, u} B S Λ

section ConstantRing

variable (X : B.Scheme)

/-- Sheafification of presheaves of rings on the small étale site of an object of a big étale
site, with rings in the universe of the objects of the site. -/
instance hasSheafify_topology_ringCat :
    HasSheafify (SmallEtale.topology B X.obj X.property) RingCat.{u + 1} :=
  Stacks.Cohomology.hasSheafify_ringCat.{u + 1, u + 1, u} (SmallEtale.topology B X.obj X.property)

/-- On the small étale site of an object of a big étale site, sheafification of presheaves of
rings inverts exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_topology_ringCat :
    (SmallEtale.topology B X.obj X.property).WEqualsLocallyBijective RingCat.{u + 1} :=
  Stacks.Cohomology.wEqualsLocallyBijective_ringCat.{u + 1, u + 1, u}
    (SmallEtale.topology B X.obj X.property)

/-- Abelian sheaves on the small étale site of an object of a big étale site: sheafification
inverts exactly the locally bijective morphisms. -/
instance wEqualsLocallyBijective_topology_addCommGrp (S : B.Scheme) :
    (SmallEtale.topology B S.obj S.property).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, u}

/-- The constant sheaf of rings `Λ̲` on the small étale site of an object of a big étale site,
lifted to the coefficient universe of `AlgebraicGeometry.SmallEtale.ModuleSheaf`. -/
abbrev moduleSheafConstantRing : Sheaf (SmallEtale.topology B X.obj X.property) RingCat.{u + 1} :=
  sheafifiedConstRing (SmallEtale.topology B X.obj X.property) (ULift.{u + 1} Λ)

/-- Changing the coefficients along `ModuleCat Λ ≌ ModuleCat (ULift Λ)`, which does not change
the underlying abelian groups. -/
abbrev moduleSheafULiftCoefficientEquivalence :
    ModuleSheaf.{u, u, u} B X Λ ≌
      Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} (ULift.{u + 1} Λ)) :=
  Sheaf.coefficientEquivalence (A := ModuleCat.{u + 1} Λ)
    (B := ModuleCat.{u + 1} (ULift.{u + 1} Λ)) (SmallEtale.topology B X.obj X.property)
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1}
      (ULift.ringEquiv : ULift.{u + 1} Λ ≃+* Λ))

/-- **Sheaves of `Λ`-modules on the small étale site of an object of a big étale site are sheaves
of modules over the constant sheaf of rings `Λ̲`.** -/
def moduleSheafConstantRingEquivalence :
    ModuleSheaf.{u, u, u} B X Λ ≌ SheafOfModules.{u + 1} (moduleSheafConstantRing B Λ X) :=
  (moduleSheafULiftCoefficientEquivalence B Λ X).trans
    (sheafifiedConstRingModulesEquivalence.{u + 1, u + 1}
      (SmallEtale.topology B X.obj X.property) (ULift.{u + 1} Λ))

/-- Changing the coefficients along `ModuleCat Λ ≌ ModuleCat (ULift Λ)` does not change the
underlying abelian sheaves. -/
def moduleSheafULiftCoefficientCompForget :
    (moduleSheafULiftCoefficientEquivalence B Λ X).functor ⋙
        sheafCompose (SmallEtale.topology B X.obj X.property)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} Λ)) AddCommGrpCat.{u + 1}) ≅
      forgetModuleSheaf.{u, u, u} B X Λ :=
  NatIso.ofComponents
    (fun F => (fullyFaithfulSheafToPresheaf (SmallEtale.topology B X.obj X.property) _).preimageIso
      (NatIso.ofComponents (fun _ => Iso.refl _) (by intro U V g; rfl)))
    (by intro F G φ; rfl)

/-- The equivalence `ModuleSheaf B X Λ ≌ SheafOfModules Λ̲` is compatible with forgetting the
module structure. -/
def moduleSheafConstantRingEquivalenceFunctorCompToSheaf :
    (moduleSheafConstantRingEquivalence B Λ X).functor ⋙
        SheafOfModules.toSheaf (moduleSheafConstantRing B Λ X) ≅
      forgetModuleSheaf.{u, u, u} B X Λ :=
  Functor.associator (moduleSheafULiftCoefficientEquivalence B Λ X).functor
      (sheafifiedConstRingModulesEquivalence.{u + 1, u + 1}
        (SmallEtale.topology B X.obj X.property) (ULift.{u + 1} Λ)).functor
      (SheafOfModules.toSheaf (moduleSheafConstantRing B Λ X)) ≪≫
    Functor.isoWhiskerLeft _
      (sheafifiedConstRingModulesEquivalenceFunctorCompToSheaf.{u + 1, u + 1}
        (SmallEtale.topology B X.obj X.property) (ULift.{u + 1} Λ)) ≪≫
    moduleSheafULiftCoefficientCompForget B Λ X

end ConstantRing

/-- `Ext` groups of abelian sheaves on the small étale site of an object of a big étale site. -/
instance hasExt_topology_addCommGrp (S : B.Scheme) :
    HasExt.{u + 1} (Sheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, u}

variable {X Y Z : B.Scheme}

/-- **[Stacks, Tag 03FD] on the small étale sites of a big étale site.** The underlying abelian
sheaf of an injective sheaf of `Λ`-modules has no higher direct images: through the equivalence
with sheaves of modules over `Λ̲` this is
`Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ`. -/
theorem isZero_rightDerived_etalePushforward_forgetModuleSheaf_of_injective (h : Y ⟶ Z)
    (I : ModuleSheaf.{u, u, u} B Y Λ) [Injective I] (q : ℕ) :
    IsZero (((etalePushforward.{u, u + 1} B h).rightDerived (q + 1)).obj
      ((forgetModuleSheaf.{u, u, u} B Y Λ).obj I)) := by
  let E := moduleSheafConstantRingEquivalence B Λ Y
  have : Injective (E.functor.obj I) := (E.map_injective_iff I).2 inferInstance
  have h' :=
    Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ.{u, u,
      u + 1, u, u + 1}
      (SmallEtale.topology B Z.obj Z.property) (SmallEtale.topology B Y.obj Y.property)
      (smallEtaleBaseChange B h) (moduleSheafConstantRing B Λ Y) (E.functor.obj I) q
  exact h'.of_iso (((etalePushforward.{u, u + 1} B h).rightDerived (q + 1)).mapIso
    ((moduleSheafConstantRingEquivalenceFunctorCompToSheaf B Λ Y).app I).symm)

/-- **Higher direct images of sheaves of `Λ`-modules are computed on underlying abelian
sheaves**: `R^q h_* ⋙ forget ≅ forget ⋙ R^q h_*`. Forgetting the module structure is exact and
carries injectives to `h_*`-acyclic abelian sheaves
(`isZero_rightDerived_etalePushforward_forgetModuleSheaf_of_injective`). -/
def rightDerivedEtalePushforwardModForgetIso (h : Y ⟶ Z) (q : ℕ) :
    (etalePushforwardMod B Λ h).rightDerived q ⋙ forgetModuleSheaf.{u, u, u} B Z Λ ≅
      forgetModuleSheaf.{u, u, u} B Y Λ ⋙ (etalePushforward.{u, u + 1} B h).rightDerived q :=
  letI := HasDerivedCategory.standard (ModuleSheaf.{u, u, u} B Y Λ)
  letI := HasDerivedCategory.standard (Sheaf (SmallEtale.topology B Y.obj Y.property)
    AddCommGrpCat.{u + 1})
  letI := HasDerivedCategory.standard (Sheaf (SmallEtale.topology B Z.obj Z.property)
    AddCommGrpCat.{u + 1})
  haveI := preservesFiniteLimits_forgetModuleSheaf.{u, u, u} B Y Λ
  haveI := preservesFiniteLimits_forgetModuleSheaf.{u, u, u} B Z Λ
  haveI : PreservesFiniteColimits (forgetModuleSheaf.{u, u, u} B Y Λ) :=
    haveI := preservesColimitsOfSize_forgetModuleSheaf.{u, u, u} B Y Λ
    PreservesColimitsOfSize.preservesFiniteColimits _
  haveI : PreservesFiniteColimits (forgetModuleSheaf.{u, u, u} B Z Λ) :=
    haveI := preservesColimitsOfSize_forgetModuleSheaf.{u, u, u} B Z Λ
    PreservesColimitsOfSize.preservesFiniteColimits _
  haveI : (forgetModuleSheaf.{u, u, u} B Z Λ).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _ (Iso.refl _) q ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic
      (forgetModuleSheaf.{u, u, u} B Y Λ) (etalePushforward.{u, u + 1} B h)
      (fun I _ ↦ (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2
        fun p hp ↦ by
          obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
          exact isZero_rightDerived_etalePushforward_forgetModuleSheaf_of_injective B Λ h I q) q

/-- A sheaf of `Λ`-modules whose underlying abelian sheaf is zero is zero. -/
theorem isZero_of_isZero_forgetModuleSheaf {M : ModuleSheaf.{u, u, u} B Z Λ}
    (hM : IsZero ((forgetModuleSheaf.{u, u, u} B Z Λ).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  exact (forgetModuleSheaf.{u, u, u} B Z Λ).map_injective (by simpa using hM.eq_of_src _ _)

/-- **`R^q h_*(f_! M) = 0` for `q > 0`, for sheaves of `Λ`-modules.** Let `f : X ⟶ Y` and
`h : Y ⟶ Z` be morphisms of a big étale site with `f` and `f ≫ h` locally quasi-finite and `h`
proper, and let `M` be a torsion sheaf of `Λ`-modules on `X_étale`. Then the higher direct images
along `h` of the direct image with compact support `f_! M` vanish. On underlying abelian sheaves
(`rightDerivedEtalePushforwardModForgetIso`) this is
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_etalePushforward_fShriekFunctor`. -/
@[sga "4½ Arcata 4.6.1" "special case"]
theorem isZero_rightDerived_etalePushforwardMod_fShriekMod (f : X ⟶ Y) (h : Y ⟶ Z)
    [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
    [IsProper (B.inclusion.map h)] [LocallyQuasiFinite (B.inclusion.map (f ≫ h))]
    (M : ModuleSheaf.{u, u, u} B X Λ) (hM : moduleTorsionSheafProperty.{u, u, u} B X Λ M)
    (q : ℕ) (hq : 0 < q) :
    IsZero (((etalePushforwardMod B Λ h).rightDerived q).obj
      ((etaleModuleLift B Λ (fShriekFunctor.{u, u} B f)).obj M)) :=
  isZero_of_isZero_forgetModuleSheaf B Λ
    ((isZero_rightDerived_etalePushforward_fShriekFunctor B f h _ hM q hq).of_iso
      ((rightDerivedEtalePushforwardModForgetIso B Λ h q).app _))

end AlgebraicGeometry.SmallEtale

end
