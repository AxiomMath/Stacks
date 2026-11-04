module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafModules
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.Homology.DerivedLinear

/-!
# Étale cohomology of a sheaf of `Λ`-modules is the cohomology of its underlying abelian sheaf

Let `Λ` be a ring, `X` a scheme and `F` a sheaf of `Λ`-modules on the small étale site of `X`.
The cohomology `H^q(X, F)` computed in the category of sheaves of `Λ`-modules, viewed as an
abelian group, is the cohomology `H^q(X, F_ab)` of the underlying abelian sheaf, naturally in `F`.
This is the case of [Stacks, Tag 03FD] for the constant sheaf of rings `Λ̲` on the small étale
site, read on Mathlib's right derived functors.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleGlobalSectionsForgetAbIso`: global sections followed by
  forgetting the module structure is forgetting followed by global sections of abelian sheaves.
* `Stacks.EtaleCohomology.etaleModuleCohomologyForgetIso`: the natural isomorphism
  `H^q(X, F)_ab ≅ H^q(X, F_ab)`.

## Main results

* `Stacks.EtaleCohomology.rightAcyclic_Γ_etaleModuleForgetAb_obj`: the underlying abelian sheaf of
  an injective sheaf of `Λ`-modules is acyclic for global sections.

## Implementation notes

Forgetting the module structure is exact, so the right derived functors of `Γ ∘ forget` split as
`forget` followed by the right derived functors of `Γ` as soon as `forget` carries injective
sheaves of `Λ`-modules to `Γ`-acyclic abelian sheaves
(`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic`). That acyclicity is
`Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_rightDerived_sections_toSheaf_succ`, the
torsion-free acyclicity behind Tag 03FD proved on a site whose objects need not form a small type,
applied at the final object `X ⟶ X` of the small étale site and transported along the equivalence
`Stacks.EtaleCohomology.etaleModuleSheafEquivalence` with sheaves of modules over `Λ̲`. The other
two steps are exactness of `forget₂ : ModuleCat Λ ⥤ Ab` (`Functor.rightDerivedCompIso`) and the
identification of the two global sections functors at the final object.

The small-site statement `ModuleSheafCohomology.globalSectionsComparisonIso` does not apply: it
asks for a small site with modules in the universe of the site, while the small étale site of
`X : Scheme.{u}` has objects in `Type (u + 1)` and morphisms in `Type u`.

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] (X : Scheme.{u})

attribute [local instance] Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp

/-- The global sections functor on abelian sheaves on the small étale site is additive. -/
local instance : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Global sections commute with forgetting the module structure**: global sections of a sheaf
of `Λ`-modules, viewed as an abelian group, are the global sections of its underlying abelian
sheaf. Both are the sections over the final object `X ⟶ X` of the small étale site. -/
def etaleModuleGlobalSectionsForgetAbIso :
    etaleModuleGlobalSections.{u, r} Λ X ⋙
        forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r} ≅
      etaleModuleForgetAb.{u, r} Λ X ⋙ Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r} :=
  Functor.isoWhiskerRight
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
        (etaleSiteTerminalIsTerminal X)) _ ≪≫
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) :
      (sheafSections X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj
          (op (etaleSiteTerminal X)) ⋙
          forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r} ≅
        etaleModuleForgetAb.{u, r} Λ X ⋙
          (sheafSections X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj
            (op (etaleSiteTerminal X))) ≪≫
    Functor.isoWhiskerLeft _
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}
        (etaleSiteTerminalIsTerminal X)).symm

/-- **The underlying abelian sheaf of an injective sheaf of `Λ`-modules is acyclic for global
sections.** Through the equivalence with sheaves of modules over the constant sheaf of rings
`Λ̲`, this is the acyclicity of [Stacks, Tag 03FD] at the final object of the small étale site. -/
theorem rightAcyclic_Γ_etaleModuleForgetAb_obj (I : EtaleModules.{u, r} Λ X) [Injective I] :
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightAcyclic
      ((etaleModuleForgetAb.{u, r} Λ X).obj I) := by
  refine (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived _ _).2 fun p hp => ?_
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  let E := etaleModuleSheafEquivalence.{u, r} Λ X
  have : Injective (E.functor.obj I) := E.symm.toAdjunction.map_injective I inferInstance
  exact (Cohomology.InjectiveModuleSheafAcyclicity.isZero_rightDerived_sections_toSheaf_succ.{r}
      X.smallEtaleTopology (etaleConstantRingSheaf.{u, r} Λ X) (E.functor.obj I)
      (etaleSiteTerminal X) q).of_iso <|
    (Functor.rightDerivedIsoOfNatIso
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}
        (etaleSiteTerminalIsTerminal X)) (q + 1)).app _ ≪≫
    (((sheafSections X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).obj
      (op (etaleSiteTerminal X))).rightDerived (q + 1)).mapIso
      ((etaleModuleSheafEquivalenceFunctorCompToSheaf.{u, r} Λ X).app I).symm

/-- **[Stacks, Tag 03FD] on the small étale site.** The cohomology `H^q(X, F)` of a sheaf of
`Λ`-modules on the small étale site of `X`, viewed as an abelian group, is the cohomology
`H^q(X, F_ab)` of its underlying abelian sheaf, naturally in `F`. -/
def etaleModuleCohomologyForgetIso (q : ℕ) :
    (etaleModuleGlobalSections.{u, r} Λ X).rightDerived q ⋙
        forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r} ≅
      etaleModuleForgetAb.{u, r} Λ X ⋙
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q :=
  have : (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (Functor.rightDerivedCompIso _ _ q).symm ≪≫
    Functor.rightDerivedIsoOfNatIso (etaleModuleGlobalSectionsForgetAbIso.{u, r} Λ X) q ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _
      (fun I _ => rightAcyclic_Γ_etaleModuleForgetAb_obj.{u, r} Λ X I) q

section Linear

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- Global sections of sheaves of `Λ`-modules on the small étale site are `Λ`-linear, being
sections over the final object. -/
instance etaleModuleGlobalSections_linear :
    Functor.Linear Λ (etaleModuleGlobalSections.{u, r} Λ X) :=
  Functor.linear_of_iso Λ
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
      (etaleSiteTerminalIsTerminal X)).symm

/-- **The action of a scalar on `H^q(X, F)`, read on the underlying abelian sheaf.** Under
`Stacks.EtaleCohomology.etaleModuleCohomologyForgetIso`, multiplication by `a ∈ Λ` on the
cohomology of a sheaf of `Λ`-modules `F` is the map induced on the cohomology of `F_ab` by
multiplication by `a` on `F`. -/
theorem etaleModuleCohomologyForgetIso_hom_app_smul (q : ℕ) (F : EtaleModules.{u, r} Λ X)
    (a : Λ) (x : ((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).obj F) :
    (etaleModuleCohomologyForgetIso.{u, r} Λ X q).hom.app F (a • x) =
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q).map
        ((etaleModuleForgetAb.{u, r} Λ X).map (a • 𝟙 F))
        ((etaleModuleCohomologyForgetIso.{u, r} Λ X q).hom.app F x) := by
  have := Stacks.DerivedLinear.rightDerived_linear (R := Λ) (etaleModuleGlobalSections.{u, r} Λ X) q
  have hx : a • x =
      (((etaleModuleGlobalSections.{u, r} Λ X).rightDerived q).map (a • 𝟙 F)).hom x := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    rfl
  rw [hx]
  exact congrArg (fun φ => φ x)
    ((etaleModuleCohomologyForgetIso.{u, r} Λ X q).hom.naturality (a • 𝟙 F))

end Linear

end Stacks.EtaleCohomology

end
