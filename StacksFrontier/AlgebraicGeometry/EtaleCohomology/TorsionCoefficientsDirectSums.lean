module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimensionDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HigherDirectImageDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectSumsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksFrontier.AlgebraicGeometry.SheafifyCommRing.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleSheafSideConditions
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CoefficientEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.CategoryTheory.Sites.SheafComposeColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology and direct sums with torsion coefficients

[Stacks, Tag 0F11]: let `n ≥ 1` be an integer.

1. If `f : X ⟶ Y` is a quasi-compact and quasi-separated morphism of schemes with
   `cd(f) < ∞`, then `Rf_* : D(X_étale, ℤ/nℤ) ⟶ D(Y_étale, ℤ/nℤ)` commutes with direct sums.
2. If `X` is a quasi-compact and quasi-separated scheme with `cd(X) < ∞`, then
   `RΓ(X, -) : D(X_étale, ℤ/nℤ) ⟶ D(ℤ/nℤ)` commutes with direct sums.

The argument of the source is
`Stacks.EtaleCohomology.preservesColimitsOfShape_of_finiteCohomologicalDimension_directImage`
and its global sections analogue, which take as inputs a uniform degree above which the higher
direct images (resp. the cohomology groups) of every sheaf of `ℤ/nℤ`-modules vanish, and the
fact that these higher direct images (resp. cohomology groups) commute with direct sums. This
file proves both inputs from the hypotheses of the source.

## Main results

* `Stacks.EtaleCohomology.rightDerivedEtaleModuleDirectImageForgetIso` and
  `Stacks.EtaleCohomology.rightDerivedEtaleModuleGlobalSectionsForgetIso`: the higher direct
  images and the cohomology of a sheaf of `Λ`-modules, `Λ` commutative, are those of its
  underlying abelian sheaf.
* `Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage`
  and `preservesColimitsOfShape_discrete_rightDerived_etaleModuleGlobalSections`: for `f` (resp.
  `X`) quasi-compact and quasi-separated, `R^q f_*` (resp. `H^q(X, -)`) on sheaves of
  `Λ`-modules commutes with direct sums.
* `Stacks.EtaleCohomology.exists_isZero_rightDerived_etaleModuleDirectImage_zmod` and
  `exists_isZero_rightDerived_etaleModuleGlobalSections_zmod`: `cd(f) < ∞` (resp.
  `cd(X) < ∞`) bounds the higher direct images (resp. the cohomology) of every sheaf of
  `ℤ/nℤ`-modules, `n ≥ 1`.
* `Stacks.EtaleCohomology.preservesColimitsOfShape_derivedDirectImage_zmod` — **Tag 0F11 (1)**.
* `Stacks.EtaleCohomology.preservesColimitsOfShape_derivedGlobalSections_zmod` — **Tag 0F11
  (2)**.
* `Stacks.EtaleCohomology.preservesColimitsOfShape_derivedDirectImage_of_natCast_eq_zero` and
  `Stacks.EtaleCohomology.preservesColimitsOfShape_derivedGlobalSections_of_natCast_eq_zero` —
  **Tag 0F11 (1) and (2)** for every commutative coefficient ring `Λ` in which `n = 0` for some
  `n ≥ 1`, which contains the case `Λ = ℤ/nℤ` of the source. Their inputs are
  `Stacks.EtaleCohomology.exists_isZero_rightDerived_etaleModuleDirectImage_of_natCast_eq_zero`
  and `exists_isZero_rightDerived_etaleModuleGlobalSections_of_natCast_eq_zero`.

## Implementation notes

*From modules to abelian sheaves.* The cohomological dimensions `cd(f)` (Tag 0F0Z) and `cd(X)`
(Tag 0F0Q) are defined by the vanishing of the cohomology of torsion *abelian* sheaves, while
the derived functors of the statement are those of sheaves of `ℤ/nℤ`-modules. The bridge is that
the underlying abelian sheaf of an injective sheaf of `Λ`-modules is acyclic for the abelian
direct image and for abelian global sections (the acyclicity behind [Stacks, Tag 03FD]), so that
forgetting the module structure commutes with taking higher direct images and cohomology
(`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic`, [Stacks, Tag 015M]). The
acyclicity is proved in
`StacksFrontier/CategoryTheory/Sites/Cohomology/HigherDirectImage/InjectiveModuleSheafAcyclicity.lean`
for sheaves of modules over a sheaf of rings; it is transported to sheaves valued in
`ModuleCat Λ` through the equivalence
`Stacks.ConstantSheaf.constantSheafModuleEquivalence` with sheaves of modules over the constant
sheaf of rings, after lifting `Λ` to the coefficient universe along `ULift.ringEquiv`.

*Direct sums.* Forgetting the module structure preserves colimits and reflects isomorphisms, so
it reflects direct sums, and on underlying abelian sheaves the higher direct images and the
cohomology commute with direct sums by
`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage`
and `Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale`.

*Universes.* The coefficients are `ModuleCat.{u + 1} (ℤ/nℤ)` for a scheme in `Scheme.{u}`,
the universe in which `cd(f)` and `cd(X)` are defined, and direct sums are indexed by types in
`Type (u + 1)`.

## References

* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
* [Stacks Project, Tag 0F0Z](https://stacks.math.columbia.edu/tag/0F0Z)
* [Stacks Project, Tag 0F0Q](https://stacks.math.columbia.edu/tag/0F0Q)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology

universe z u

namespace Stacks.EtaleCohomology

/-- Sheafification of abelian presheaves on the small étale site, with coefficients in the
universe of its objects. -/
local instance hasSheafify_smallEtale_objectUniverse (Z : Scheme.{u}) :
    HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Stacks.ModuleSheaf.hasSheafify_addCommGrpCat.{u + 1} _

/-- `Ext` groups of abelian sheaves on the small étale site, with coefficients in the universe of
its objects, exist in that universe. -/
local instance hasExt_smallEtale_objectUniverse (Z : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, u}

section Forget

variable (Λ : Type) [Ring Λ] (X : Scheme.{u})

attribute [local instance] moduleCat_hasLimitsOfSize

/-- Postcomposition with the forgetful functor from `Λ`-modules to abelian groups carries sheaves
on the small étale site to sheaves. -/
instance hasSheafCompose_forget₂_etaleModules :
    X.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ _

/-- Postcomposition with the forgetful functor from `Λ`-modules to abelian groups commutes with
sheafification on the small étale site. -/
instance preservesSheafification_forget₂_etaleModules :
    X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  Stacks.ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ _

/-- The underlying abelian sheaf of a sheaf of `Λ`-modules on the small étale site. -/
abbrev etaleModuleForget :
    EtaleModules.{u, 0} Λ X ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- The underlying abelian sheaf functor is additive. -/
instance etaleModuleForget_additive : (etaleModuleForget Λ X).Additive where
  map_add := by intros; rfl

/-- The underlying abelian sheaf functor preserves every colimit that the categories of
presheaves have: the forgetful functor of modules preserves colimits and sheafification. -/
instance etaleModuleForget_preservesColimitsOfShape (K : Type (u + 1)) [SmallCategory K] :
    PreservesColimitsOfShape K (etaleModuleForget Λ X) := by
  let : PreservesColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ
  exact preservesColimitsOfShape_sheafCompose _ _ K

/-- The underlying abelian sheaf functor is right exact. -/
instance etaleModuleForget_preservesFiniteColimits :
    PreservesFiniteColimits (etaleModuleForget Λ X) := by
  let : PreservesColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ
  exact ⟨fun K _ _ => preservesColimitsOfShape_sheafCompose _ _ K⟩

/-- The underlying abelian sheaf functor is left exact: limits of sheaves are computed on
presheaves, where it is postcomposition with a limit preserving functor. -/
instance etaleModuleForget_preservesFiniteLimits :
    PreservesFiniteLimits (etaleModuleForget Λ X) := by
  refine ⟨fun K _ _ => ?_⟩
  have : PreservesLimitsOfShape K (etaleModuleForget Λ X ⋙
      sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfShape_of_natIso (F := sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
      (Iso.refl _)
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- A sheaf of `Λ`-modules whose underlying abelian sheaf is zero is zero. -/
theorem isZero_of_isZero_etaleModuleForget_obj {F : EtaleModules.{u, 0} Λ X}
    (h : IsZero ((etaleModuleForget Λ X).obj F)) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  apply (etaleModuleForget Λ X).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_of_src _ _

/-- The underlying abelian sheaf functor reflects colimits of every shape of the universe of the
objects of the site: it reflects isomorphisms and preserves those colimits. -/
instance etaleModuleForget_reflectsColimitsOfShape (K : Type (u + 1)) [SmallCategory K] :
    ReflectsColimitsOfShape K (etaleModuleForget Λ X) :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms

end Forget

section Torsion

/-- The underlying abelian sheaf of a sheaf of `Λ`-modules is torsion when `n = 0` in `Λ` for some
`n ≥ 1`. -/
private theorem torsionSheafProperty_etaleModuleForget_obj_aux (Λ : Type) [Ring Λ]
    (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0) (X : Scheme.{u}) (F : EtaleModules.{u, 0} Λ X) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((etaleModuleForget Λ X).obj F) :=
  fun U x => ⟨⊤, X.smallEtaleTopology.top_mem U, fun V g _ => ⟨n, hn, by
    show n • ((F.obj.map g.op).hom x : F.obj.obj (op V)) = 0
    rw [← Nat.cast_smul_eq_nsmul Λ, hΛ, zero_smul]⟩⟩

/-- **The underlying abelian sheaf of a sheaf of `ℤ/nℤ`-modules is torsion**, for `n ≥ 1`: every
section is annihilated by `n`. -/
theorem torsionSheafProperty_etaleModuleForget_obj (n : ℕ) (hn : 0 < n) (X : Scheme.{u})
    (F : EtaleModules.{u, 0} (ZMod n) X) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((etaleModuleForget (ZMod n) X).obj F) :=
  torsionSheafProperty_etaleModuleForget_obj_aux _ n hn (ZMod.natCast_self n) X F

end Torsion

section Acyclicity

variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **The underlying abelian sheaf of an injective sheaf of `Λ`-modules is, up to isomorphism, the
underlying abelian sheaf of an injective sheaf of modules over a sheaf of rings.** -/
theorem exists_injective_sheafOfModules_toSheaf_iso (I : EtaleModules.{u, 0} Λ X)
    [Injective I] :
    ∃ (R : Sheaf X.smallEtaleTopology RingCat.{u + 1}) (M : SheafOfModules.{u + 1} R),
      Injective M ∧
        Nonempty ((SheafOfModules.toSheaf R).obj M ≅ (etaleModuleForget Λ X).obj I) := by
  let e₀ : ModuleCat.{u + 1} Λ ≌ ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv ULift.ringEquiv
  let : X.smallEtaleTopology.HasSheafCompose e₀.functor :=
    hasSheafCompose_of_preservesLimitsOfSize _
  let : X.smallEtaleTopology.HasSheafCompose e₀.inverse :=
    hasSheafCompose_of_preservesLimitsOfSize _
  let E₁ := Sheaf.coefficientEquivalence X.smallEtaleTopology e₀
  let : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} Λ)) :=
    etaleModules_hasSheafify.{u, u + 1} (ULift.{u + 1} Λ) X
  let : X.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} Λ)) AddCommGrpCat.{u + 1}) :=
    Stacks.ModuleSheaf.hasSheafCompose_forget₂.{u + 1} (ULift.{u + 1} Λ) _
  let E₂ := Stacks.ConstantSheaf.constantSheafModuleEquivalence X.smallEtaleTopology
    (R := ULift.{u + 1} Λ)
  refine ⟨_, E₂.functor.obj (E₁.functor.obj I),
    (E₂.map_injective_iff _).2 ((E₁.map_injective_iff _).2 inferInstance), ⟨?_⟩⟩
  refine Stacks.ConstantSheaf.sheafOfModulesOfConstantRingIso X.smallEtaleTopology
    (Stacks.ConstantSheaf.constantRingSheafMap X.smallEtaleTopology (ULift.{u + 1} Λ))
    (E₁.functor.obj I) ≪≫ ?_
  exact (fullyFaithfulSheafToPresheaf _ _).preimageIso (Iso.refl _)

end Acyclicity

section DirectImage

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (Λ : Type) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The underlying abelian sheaf of an injective sheaf of `Λ`-modules is acyclic for the direct
image of abelian sheaves.** -/
theorem rightAcyclic_etaleAbelianDirectImage_etaleModuleForget_obj (I : EtaleModules.{u, 0} Λ X)
    [Injective I] :
    (etaleAbelianDirectImage.{u, 0} f).rightAcyclic ((etaleModuleForget Λ X).obj I) := by
  refine (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2 ?_
  intro p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  obtain ⟨R, M, hM, ⟨e⟩⟩ := exists_injective_sheafOfModules_toSheaf_iso Λ X I
  exact IsZero.of_iso
    (InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ.{u, u, u + 1, u, u + 1}
      Y.smallEtaleTopology X.smallEtaleTopology (smallEtaleBaseChange f) R M q)
    (((etaleAbelianDirectImage.{u, 0} f).rightDerived (q + 1)).mapIso e.symm)

/-- **Higher direct images of a sheaf of `Λ`-modules and of its underlying abelian sheaf agree**:
`R^q f_* ⋙ forget ≅ forget ⋙ R^q f_*`. -/
def rightDerivedEtaleModuleDirectImageForgetIso (q : ℕ) :
    (etaleModuleDirectImage.{u, 0} Λ f).rightDerived q ⋙ etaleModuleForget Λ Y ≅
      etaleModuleForget Λ X ⋙ (etaleAbelianDirectImage.{u, 0} f).rightDerived q :=
  have : (etaleModuleForget Λ Y).PreservesHomology := Functor.preservesHomologyOfExact _
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (etaleModuleDirectImage.{u, 0} Λ f)
      (etaleModuleForget Λ Y)
      (etaleModuleForget Λ X ⋙ etaleAbelianDirectImage.{u, 0} f) (Iso.refl _) q ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _
      (fun I _ => rightAcyclic_etaleAbelianDirectImage_etaleModuleForget_obj Λ f I) q


/-- **Higher direct images of sheaves of `Λ`-modules commute with direct sums** along a
quasi-compact and quasi-separated morphism: forgetting the module structure reflects direct sums,
and on underlying abelian sheaves this is
`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage`. -/
theorem preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage
    [QuasiCompact f] [QuasiSeparated f] (q : ℕ) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) ((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q) := by
  have : PreservesColimitsOfShape (Discrete I)
      ((etaleAbelianDirectImage.{u, 0} f).rightDerived q) :=
    preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage.{0} f q I
  have : PreservesColimitsOfShape (Discrete I)
      ((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q ⋙ etaleModuleForget Λ Y) :=
    preservesColimitsOfShape_of_natIso (rightDerivedEtaleModuleDirectImageForgetIso Λ f q).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (etaleModuleForget Λ Y)

end DirectImage

section GlobalSections

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type) [CommRing Λ] (X : Scheme.{u})

/-- Taking global sections commutes with forgetting the module structure: both are sections over
the terminal object of the small étale site. -/
def etaleModuleGlobalSectionsForgetIso :
    etaleModuleGlobalSections.{u, 0} Λ X ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      etaleModuleForget Λ X ⋙ Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerRight (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ) terminalIsTerminal) _ ≪≫
    Functor.isoWhiskerLeft (etaleModuleForget Λ X)
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).symm

/-- **The underlying abelian sheaf of an injective sheaf of `Λ`-modules is acyclic for global
sections**: its cohomology is that of an injective sheaf of modules over a sheaf of rings, which
vanishes in positive degrees ([Stacks, Tag 03FD]). -/
theorem rightAcyclic_Γ_etaleModuleForget_obj (I : EtaleModules.{u, 0} Λ X) [Injective I] :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightAcyclic
      ((etaleModuleForget Λ X).obj I) := by
  refine (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2 ?_
  intro p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  obtain ⟨R, M, hM, ⟨e⟩⟩ := exists_injective_sheafOfModules_toSheaf_iso Λ X I
  refine IsZero.of_iso
    (Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_rightDerived_sections_toSheaf_succ.{u}
      X.smallEtaleTopology R M (⊤_ X.Etale) q) ?_
  exact (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived (q + 1)).mapIso
      e.symm) ≪≫
    (ModuleSheafCohomology.rightDerivedIso (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology
      AddCommGrpCat.{u + 1} terminalIsTerminal) (q + 1)).app _

/-- **The cohomology of a sheaf of `Λ`-modules and of its underlying abelian sheaf agree**:
`H^q(X, -) ⋙ forget ≅ forget ⋙ H^q(X, -)`. -/
def rightDerivedEtaleModuleGlobalSectionsForgetIso (q : ℕ) :
    (etaleModuleGlobalSections.{u, 0} Λ X).rightDerived q ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      etaleModuleForget Λ X ⋙ (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q :=
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (etaleModuleGlobalSections.{u, 0} Λ X)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      (etaleModuleForget Λ X ⋙ Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (etaleModuleGlobalSectionsForgetIso Λ X) q ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _
      (fun I _ => rightAcyclic_Γ_etaleModuleForget_obj Λ X I) q

/-- **The cohomology of sheaves of `Λ`-modules on a quasi-compact and quasi-separated scheme
commutes with direct sums**: forgetting the module structure reflects direct sums, and on
underlying abelian sheaves this is
`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale`. -/
theorem preservesColimitsOfShape_discrete_rightDerived_etaleModuleGlobalSections
    [CompactSpace X] [QuasiSeparatedSpace X] (q : ℕ) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      ((etaleModuleGlobalSections.{u, 0} Λ X).rightDerived q) := by
  have : PreservesColimitsOfShape (Discrete I)
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q) :=
    preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale.{0} X q I
  have : PreservesColimitsOfShape (Discrete I)
      ((etaleModuleGlobalSections.{u, 0} Λ X).rightDerived q ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesColimitsOfShape_of_natIso (rightDerivedEtaleModuleGlobalSectionsForgetIso Λ X q).symm
  have : PreservesColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ
  have : ReflectsColimitsOfShape (Discrete I)
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

end GlobalSections

section Torsion

variable (n : ℕ) (hn : 0 < n) {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- A uniform degree above which the higher direct images of every sheaf of `Λ`-modules vanish,
when `n = 0` in `Λ` for some `n ≥ 1`. -/
private theorem exists_isZero_rightDerived_etaleModuleDirectImage_aux
    (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hcd : f.etaleCohomologicalDimension < ⊤) :
    ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, 0} Λ X,
      IsZero (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj F) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hcd.ne
  refine ⟨d + 1, fun q hq F => isZero_of_isZero_etaleModuleForget_obj _ _ ?_⟩
  refine IsZero.of_iso ?_ ((rightDerivedEtaleModuleDirectImageForgetIso Λ f q).app F)
  refine f.isZero_rightDerived_etaleAbelianDirectImage _
    (torsionSheafProperty_etaleModuleForget_obj_aux Λ n hn hΛ X F) q ?_
  rw [← hd]
  exact_mod_cast hq

include hn in
/-- **Finite cohomological dimension of `f` bounds the higher direct images of every sheaf of
`ℤ/nℤ`-modules**, for `n ≥ 1`. The cohomological dimension `cd(f)` of [Stacks, Tag 0F0Z] is
defined by vanishing on torsion abelian sheaves; a sheaf of `ℤ/nℤ`-modules is torsion, and its
higher direct images are those of its underlying abelian sheaf. -/
theorem exists_isZero_rightDerived_etaleModuleDirectImage_zmod
    (hcd : f.etaleCohomologicalDimension < ⊤) :
    ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, 0} (ZMod n) X,
      IsZero (((etaleModuleDirectImage.{u, 0} (ZMod n) f).rightDerived q).obj F) :=
  exists_isZero_rightDerived_etaleModuleDirectImage_aux _ n hn (ZMod.natCast_self n) f hcd

/-- **[Stacks, Tag 0F11] (1).** Let `n ≥ 1` and let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of schemes with `cd(f) < ∞`. Then the unbounded derived direct image
`Rf_* : D(X_étale, ℤ/nℤ) ⟶ D(Y_étale, ℤ/nℤ)` commutes with direct sums.

Here `cd(f)` is `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension`, Tag 0F0Z, and
`Rf_*` is any unbounded right derived functor of the direct image of sheaves of `ℤ/nℤ`-modules.
The two inputs of the argument of the source are proved: the uniform vanishing of the higher
direct images on sheaves of `ℤ/nℤ`-modules is
`Stacks.EtaleCohomology.exists_isZero_rightDerived_etaleModuleDirectImage_zmod`, and their
commuting with direct sums (Tag 09Z1 for a constant system) is
`Stacks.EtaleCohomology.preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage`. -/
@[stacks 0F11 "(1): Rf_* : D(X_étale, ℤ/nℤ) ⟶ D(Y_étale, ℤ/nℤ) commutes with direct sums for
f quasi-compact and quasi-separated with cd(f) < ∞, n ≥ 1"]
theorem preservesColimitsOfShape_derivedDirectImage_zmod
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hcd : f.etaleCohomologicalDimension < ⊤) (n : ℕ) (hn : 0 < n)
    [HasDerivedCategory.{z} (EtaleModules.{u, 0} (ZMod n) X)]
    [HasDerivedCategory.{z} (EtaleModules.{u, 0} (ZMod n) Y)]
    (RF : DerivedCategory (EtaleModules.{u, 0} (ZMod n) X) ⥤
      DerivedCategory (EtaleModules.{u, 0} (ZMod n) Y))
    (α : (etaleModuleDirectImage.{u, 0} (ZMod n) f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (EtaleModules.{u, 0} (ZMod n) X) (ComplexShape.up ℤ))]
    (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) RF :=
  preservesColimitsOfShape_of_finiteCohomologicalDimension_directImage (ZMod n) f
    (exists_isZero_rightDerived_etaleModuleDirectImage_zmod n hn f hcd)
    (fun q I =>
      preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage (ZMod n) f q I)
    RF α I

end Torsion

section TorsionGlobalSections

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

variable (n : ℕ) (hn : 0 < n) (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]

/-- A uniform degree above which the cohomology of every sheaf of `Λ`-modules vanishes, when
`n = 0` in `Λ` for some `n ≥ 1`. -/
private theorem exists_isZero_rightDerived_etaleModuleGlobalSections_aux
    (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : Scheme.etaleCohomologicalDimension X < ⊤) :
    ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, 0} Λ X,
      IsZero (((etaleModuleGlobalSections.{u, 0} Λ X).rightDerived q).obj F) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hcd.ne
  refine ⟨d + 1, fun q hq F => ?_⟩
  have h : IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q).obj
      ((etaleModuleForget Λ X).obj F)) := by
    refine (Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}
      X.smallEtaleTopology _ q).1 ?_
    refine Scheme.isEtaleCohomologyBound_etaleCohomologicalDimension X _
      (torsionSheafProperty_etaleModuleForget_obj_aux Λ n hn hΛ X F) q ?_
    rw [← hd]
    exact_mod_cast hq
  rw [IsZero.iff_id_eq_zero]
  apply (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.of_iso h
    ((rightDerivedEtaleModuleGlobalSectionsForgetIso Λ X q).app F)).eq_of_src _ _

include hn in
/-- **Finite cohomological dimension of `X` bounds the cohomology of every sheaf of
`ℤ/nℤ`-modules**, for `n ≥ 1`. The cohomological dimension `cd(X)` of [Stacks, Tag 0F0Q] is
defined by vanishing on torsion abelian sheaves; a sheaf of `ℤ/nℤ`-modules is torsion, and its
cohomology is that of its underlying abelian sheaf. -/
theorem exists_isZero_rightDerived_etaleModuleGlobalSections_zmod
    (hcd : Scheme.etaleCohomologicalDimension X < ⊤) :
    ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, 0} (ZMod n) X,
      IsZero (((etaleModuleGlobalSections.{u, 0} (ZMod n) X).rightDerived q).obj F) :=
  exists_isZero_rightDerived_etaleModuleGlobalSections_aux _ n hn (ZMod.natCast_self n) X hcd

include hn in
/-- **[Stacks, Tag 0F11] (2).** Let `n ≥ 1` and let `X` be a quasi-compact and quasi-separated
scheme with `cd(X) < ∞`. Then the unbounded derived global sections
`RΓ(X, -) : D(X_étale, ℤ/nℤ) ⟶ D(ℤ/nℤ)` commute with direct sums.

Here `cd(X)` is `AlgebraicGeometry.Scheme.etaleCohomologicalDimension`, Tag 0F0Q, and
`RΓ(X, -)` is any unbounded right derived functor of global sections of sheaves of
`ℤ/nℤ`-modules. The two inputs of the argument of the source are proved: the uniform vanishing of
the cohomology of sheaves of `ℤ/nℤ`-modules is
`Stacks.EtaleCohomology.exists_isZero_rightDerived_etaleModuleGlobalSections_zmod`, and its
commuting with direct sums is
`preservesColimitsOfShape_discrete_rightDerived_etaleModuleGlobalSections`. -/
@[stacks 0F11 "(2): RΓ(X, -) : D(X_étale, ℤ/nℤ) ⟶ D(ℤ/nℤ) commutes with direct sums for X
quasi-compact and quasi-separated with cd(X) < ∞, n ≥ 1"]
theorem preservesColimitsOfShape_derivedGlobalSections_zmod
    (hcd : Scheme.etaleCohomologicalDimension X < ⊤)
    [HasDerivedCategory.{z} (EtaleModules.{u, 0} (ZMod n) X)]
    [HasDerivedCategory.{z} (ModuleCat.{u + 1} (ZMod n))]
    (RF : DerivedCategory (EtaleModules.{u, 0} (ZMod n) X) ⥤
      DerivedCategory (ModuleCat.{u + 1} (ZMod n)))
    (α : (etaleModuleGlobalSections.{u, 0} (ZMod n) X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (EtaleModules.{u, 0} (ZMod n) X) (ComplexShape.up ℤ))]
    (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) RF :=
  preservesColimitsOfShape_of_finiteCohomologicalDimension_globalSections (ZMod n) X
    (exists_isZero_rightDerived_etaleModuleGlobalSections_zmod n hn X hcd)
    (fun q I =>
      preservesColimitsOfShape_discrete_rightDerived_etaleModuleGlobalSections (ZMod n) X q I)
    RF α I

end TorsionGlobalSections

section TorsionRing

/-! ### A coefficient ring killed by an integer `n ≥ 1`

The two parts of [Stacks, Tag 0F11] for a commutative coefficient ring `Λ` in which `n = 0` for
some `n ≥ 1`. The ring `ℤ/nℤ` of the source is such a ring, and nothing in the argument uses more
than that every sheaf of `Λ`-modules is a torsion abelian sheaf.
-/

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- **The underlying abelian sheaf of a sheaf of `Λ`-modules is torsion** when `n = 0` in `Λ` for
some `n ≥ 1`: every section is annihilated by `n`. -/
theorem torsionSheafProperty_etaleModuleForget_obj_of_natCast_eq_zero (Λ : Type) [Ring Λ]
    (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0) (X : Scheme.{u}) (F : EtaleModules.{u, 0} Λ X) :
    Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology
      ((etaleModuleForget Λ X).obj F) :=
  torsionSheafProperty_etaleModuleForget_obj_aux Λ n hn hΛ X F

/-- **Finite cohomological dimension of `f` bounds the higher direct images of every sheaf of
`Λ`-modules**, when `n = 0` in `Λ` for some `n ≥ 1`: such a sheaf is torsion, and its higher
direct images are those of its underlying abelian sheaf. -/
theorem exists_isZero_rightDerived_etaleModuleDirectImage_of_natCast_eq_zero
    (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hcd : f.etaleCohomologicalDimension < ⊤) :
    ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, 0} Λ X,
      IsZero (((etaleModuleDirectImage.{u, 0} Λ f).rightDerived q).obj F) :=
  exists_isZero_rightDerived_etaleModuleDirectImage_aux Λ n hn hΛ f hcd

/-- **Finite cohomological dimension of `X` bounds the cohomology of every sheaf of
`Λ`-modules**, when `n = 0` in `Λ` for some `n ≥ 1`: such a sheaf is torsion, and its
cohomology is that of its underlying abelian sheaf. -/
theorem exists_isZero_rightDerived_etaleModuleGlobalSections_of_natCast_eq_zero
    (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : Scheme.etaleCohomologicalDimension X < ⊤) :
    ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, 0} Λ X,
      IsZero (((etaleModuleGlobalSections.{u, 0} Λ X).rightDerived q).obj F) :=
  exists_isZero_rightDerived_etaleModuleGlobalSections_aux Λ n hn hΛ X hcd

/-- **[Stacks, Tag 0F11] (1).** Let `n ≥ 1` and let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of schemes with `cd(f) < ∞`. Then
`Rf_* : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` commutes with direct sums, for every commutative ring `Λ`
in which `n = 0`; the source's case is `Λ = ℤ/nℤ`.

Here `cd(f)` is `AlgebraicGeometry.Scheme.Hom.etaleCohomologicalDimension`, [Stacks, Tag 0F0Z],
and `Rf_*` is any unbounded right derived functor `RF` of the direct image of sheaves of
`Λ`-modules on the small étale sites, with derivation unit `α`, in any model of the two derived
categories. -/
@[stacks 0F11 "(1)"]
theorem preservesColimitsOfShape_derivedDirectImage_of_natCast_eq_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hcd : f.etaleCohomologicalDimension < ⊤)
    (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    [HasDerivedCategory.{z} (EtaleModules.{u, 0} Λ X)]
    [HasDerivedCategory.{z} (EtaleModules.{u, 0} Λ Y)]
    (RF : DerivedCategory (EtaleModules.{u, 0} Λ X) ⥤ DerivedCategory (EtaleModules.{u, 0} Λ Y))
    (α : (etaleModuleDirectImage.{u, 0} Λ f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ))]
    (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) RF :=
  preservesColimitsOfShape_of_finiteCohomologicalDimension_directImage Λ f
    (exists_isZero_rightDerived_etaleModuleDirectImage_of_natCast_eq_zero Λ n hn hΛ f hcd)
    (fun q I => preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage Λ f q I)
    RF α I

/-- **[Stacks, Tag 0F11] (2).** Let `n ≥ 1` and let `X` be a quasi-compact and quasi-separated
scheme with `cd(X) < ∞`. Then `RΓ(X, -) : D(X_étale, Λ) ⟶ D(Λ)` commutes with direct sums, for
every commutative ring `Λ` in which `n = 0`; the source's case is `Λ = ℤ/nℤ`.

Here `cd(X)` is `AlgebraicGeometry.Scheme.etaleCohomologicalDimension`, [Stacks, Tag 0F0Q], and
`RΓ(X, -)` is any unbounded right derived functor `RF` of the global sections of sheaves of
`Λ`-modules on the small étale site, with derivation unit `α`, in any model of the two derived
categories. -/
@[stacks 0F11 "(2)"]
theorem preservesColimitsOfShape_derivedGlobalSections_of_natCast_eq_zero
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (hcd : Scheme.etaleCohomologicalDimension X < ⊤)
    (Λ : Type) [CommRing Λ] (n : ℕ) (hn : 0 < n) (hΛ : (n : Λ) = 0)
    [HasDerivedCategory.{z} (EtaleModules.{u, 0} Λ X)]
    [HasDerivedCategory.{z} (ModuleCat.{u + 1} Λ)]
    (RF : DerivedCategory (EtaleModules.{u, 0} Λ X) ⥤ DerivedCategory (ModuleCat.{u + 1} Λ))
    (α : (etaleModuleGlobalSections.{u, 0} Λ X).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ))]
    (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) RF :=
  preservesColimitsOfShape_of_finiteCohomologicalDimension_globalSections Λ X
    (exists_isZero_rightDerived_etaleModuleGlobalSections_of_natCast_eq_zero Λ n hn hΛ X hcd)
    (fun q I => preservesColimitsOfShape_discrete_rightDerived_etaleModuleGlobalSections Λ X q I)
    RF α I

end TorsionRing

end Stacks.EtaleCohomology

end
