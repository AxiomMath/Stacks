module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.FirstCohomologyAndExtensions
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonInDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
import StacksCore.Tactic.StacksAttribute

/-!
# First cohomology of a ringed space classifies extensions of the structure sheaf

Let `(X, O_X)` be a ringed space and `F` a sheaf of `O_X`-modules. An extension
`0 → F → E → O_X → 0` in `Mod(O_X)` has a class in `H^1(X, F)`, namely the image of the unit
global section `1 ∈ Γ(X, O_X)` under the connecting map of the extension. This file proves that
this assignment is an isomorphism of abelian groups `Ext^1_{Mod(O_X)}(O_X, F) ≅ H^1(X, F)`,
characterises it by that formula, and shows it is natural in `F`.

The ringed space is encoded by its structure sheaf, a `RingCat`-valued sheaf on the site of
opens of `X`, exactly as in Tag 01E3, so the result is the specialisation of the ringed-site
statement of Tag 03F1 to the site of opens. The only work is the change of cohomology
presentation: Tag 03F1 uses the right derived functors of the global sections of the whole site,
valued in modules over `Γ(X, O_X)`, whereas `H^n(X, -)` of Tag 01E3 is the right derived functor
of sections over the top open, valued in abelian groups. A section of a module sheaf over the
whole site is its value over the top open, and forgetting the module structure is exact, so the
two cohomology functors agree in every degree.

## Main definitions

* `Stacks.Cohomology.SpaceModules.globalSectionsIsoSectionsTop`: the global sections of a sheaf
  of modules on a space are its sections over the top open.
* `Stacks.Cohomology.SpaceModules.cohomologyIsoSiteCohomology`: `H^n(X, -)` of Tag 01E3 is the
  cohomology of the site of opens of Tag 071H, after forgetting the module structure.
* `Stacks.Cohomology.SpaceModules.connectingMap`: the connecting map
  `H^n(X, F₃) ⟶ H^{n+1}(X, F₁)` of a short exact sequence of sheaves of modules.
* `Stacks.Cohomology.SpaceModules.oneCohomologyClass`: the class of `1 ∈ Γ(X, O_X)` in
  `H^0(X, O_X)`.

## Main results

* `Stacks.Cohomology.SpaceModules.extOneEquivFirstCohomology`: the canonical additive
  equivalence `Ext^1(O_X, F) ≃+ H^1(X, F)`.
* `Stacks.Cohomology.SpaceModules.extOneEquivFirstCohomology_extClass`: it sends the class of
  an extension to the connecting image of the unit global section.
* `Stacks.Cohomology.SpaceModules.extOneEquivFirstCohomology_unique`: that formula determines
  it uniquely.
* `Stacks.Cohomology.SpaceModules.extOneEquivFirstCohomology_naturality`: it is natural in the
  coefficient module sheaf.

## Implementation notes

The connecting maps of `H^*(X, -)` are transported from the universal cohomological `δ`-functor
`Stacks.Cohomology.SiteModules.universalCohomologyDeltaFunctor` of Tag 071H along
`cohomologyIsoSiteCohomology`; the degree-zero normalisation used is the canonical map
`CategoryTheory.Functor.toRightDerivedZero`, which is what makes
`extOneEquivFirstCohomology_unique` a genuine uniqueness statement.

## References

* [Stacks Project, Tag 0B3A](https://stacks.math.columbia.edu/tag/0B3A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.SpaceModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

variable {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Modules over the ring `Γ(X, O_X)` of global sections of the structure sheaf, viewed as
abelian groups. The cohomology of Tag 071H is valued in the former and `H^n(X, -)` of Tag 01E3
in the latter. -/
abbrev forgetGlobalSectionsModule :
    ModuleCat.{u} (RingCat.sectionsSubring R.obj) ⥤ AddCommGrpCat.{u} :=
  forget₂ _ _

/-- A compatible family of sections of a sheaf of modules over all opens of `X` is the same
thing as a single section over the top open: the top open is terminal, so its value determines
every other one. -/
def globalSectionsIsoSectionsTop :
    SiteModules.globalSectionsFunctor R ⋙ forgetGlobalSectionsModule R ≅ secF R ⊤ :=
  NatIso.ofComponents (fun M => (AddEquiv.ofBijective
    (AddMonoidHom.mk' (fun s : M.sections => s.eval (op ⊤)) (fun _ _ => rfl))
    ⟨fun s t h => by
      apply Subtype.ext
      funext U
      have hs := M.val.sections_property s (homOfLE (le_top : U.unop ≤ ⊤)).op
      have ht := M.val.sections_property t (homOfLE (le_top : U.unop ≤ ⊤)).op
      exact hs.symm.trans ((congrArg (M.val.map _) h).trans ht),
     fun x => ⟨M.val.sectionsMk (fun U => M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op x)
        (by
          intro U V i
          rw [← M.val.map_comp_apply]
          congr 2), by
        change M.val.map (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op x = x
        change M.val.map (𝟙 (op (⊤ : Opens X))) x = x
        exact congrArg (fun f => f x) (M.val.map_id _)⟩⟩).toAddCommGrpIso)
    (by intro M N f; ext s; rfl)

/-- The unit global section of the structure sheaf is `1 ∈ Γ(X, O_X)`. -/
theorem globalSectionsIsoSectionsTop_hom_app_unit :
    (globalSectionsIsoSectionsTop R).hom.app (SheafOfModules.unit R)
        (SheafOfModules.unitHomEquiv (SheafOfModules.unit R) (𝟙 _)) =
      (1 : R.obj.obj (op (⊤ : Opens X))) := rfl

/-- The cohomology `H^n(X, -)` of a ringed space is the cohomology of the site of its opens of
Tag 071H, with the module structure over `Γ(X, O_X)` forgotten. -/
def cohomologyIsoSiteCohomology (n : ℕ) :
    SiteModules.cohomologyFunctor R n ⋙ forgetGlobalSectionsModule R ≅ Hfunctor R ⊤ n :=
  ModuleComparison.rightDerivedCompIso _ _ _ (globalSectionsIsoSectionsTop R) n

/-- The class of the unit section `1 ∈ Γ(X, O_X)` in `H^0(X, O_X)`, taken through the canonical
map from ordinary global sections to the zeroth right derived functor. -/
def oneCohomologyClass : Hgroup R ⊤ 0 (SheafOfModules.unit R) :=
  (secF R ⊤).toRightDerivedZero.app (SheafOfModules.unit R)
    (1 : R.obj.obj (op (⊤ : Opens X)))

/-- The connecting map of a short exact sequence of sheaves of modules for the cohomology of the
site of opens, read on the cohomology functors of Tag 071H themselves. -/
def siteConnectingMap {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) (n : ℕ) :
    (SiteModules.cohomologyFunctor R n).obj S.X₃ ⟶
      (SiteModules.cohomologyFunctor R (n + 1)).obj S.X₁ :=
  (eqToHom (SiteModules.universalCohomologyDeltaFunctor_functor R n).symm).app S.X₃ ≫
    (SiteModules.universalCohomologyDeltaFunctor R).δ hS n ≫
      (eqToHom (SiteModules.universalCohomologyDeltaFunctor_functor R (n + 1))).app S.X₁

/-- The connecting map `H^n(X, F₃) ⟶ H^{n+1}(X, F₁)` of the long exact cohomology sequence of a
short exact sequence `0 → F₁ → F₂ → F₃ → 0` of sheaves of `O_X`-modules. -/
def connectingMap {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) (n : ℕ) :
    Hgroup R ⊤ n S.X₃ ⟶ Hgroup R ⊤ (n + 1) S.X₁ :=
  (cohomologyIsoSiteCohomology R n).inv.app S.X₃ ≫
    (forgetGlobalSectionsModule R).map (siteConnectingMap R hS n) ≫
      (cohomologyIsoSiteCohomology R (n + 1)).hom.app S.X₁

/-- In degree zero the comparison with the cohomology of the site of opens carries the global
section `1` of the structure sheaf to its class in `H^0(X, O_X)`. -/
theorem cohomologyIsoSiteCohomology_zero_apply_one :
    (cohomologyIsoSiteCohomology R 0).hom.app (SheafOfModules.unit R)
        ((SiteModules.globalSectionsFunctor R).toRightDerivedZero.app
          (SheafOfModules.unit R)
          (SheafOfModules.unitHomEquiv (SheafOfModules.unit R) (𝟙 _))) =
      oneCohomologyClass R := by
  refine Eq.trans ?_ (Eq.trans (ConcreteCategory.congr_hom
    (DerivedCompTransport.rightDerivedCompIso_hom_app_zero
      (SiteModules.globalSectionsFunctor R) (forgetGlobalSectionsModule R) (secF R ⊤)
      (globalSectionsIsoSectionsTop R) (SheafOfModules.unit R))
    (SheafOfModules.unitHomEquiv (SheafOfModules.unit R) (𝟙 _))) ?_) <;> rfl

/-- The class of `1 ∈ Γ(X, O_X)` in `H^0(X, O_X)`, read back on the cohomology of the site of
opens, is the degree-zero class of the unit global section. -/
theorem cohomologyIsoSiteCohomology_zero_inv_oneCohomologyClass :
    (cohomologyIsoSiteCohomology R 0).inv.app (SheafOfModules.unit R) (oneCohomologyClass R) =
      (SiteModules.globalSectionsFunctor R).toRightDerivedZero.app (SheafOfModules.unit R)
        (SheafOfModules.unitHomEquiv (SheafOfModules.unit R) (𝟙 _)) := by
  conv_lhs => rw [← cohomologyIsoSiteCohomology_zero_apply_one R]
  exact ConcreteCategory.congr_hom
    ((cohomologyIsoSiteCohomology R 0).hom_inv_id_app (SheafOfModules.unit R)) _

/-- The connecting map of the site, applied to the degree-zero class of a global section, is the
degree-zero normalisation of Tag 071H followed by the `δ`-functor connecting map. -/
theorem forgetGlobalSectionsModule_map_siteConnectingMap_apply
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    (s : (SiteModules.globalSectionsFunctor R).obj S.X₃) :
    (forgetGlobalSectionsModule R).map (siteConnectingMap R hS 0)
        ((SiteModules.globalSectionsFunctor R).toRightDerivedZero.app S.X₃ s) =
      (eqToHom (SiteModules.universalCohomologyDeltaFunctor_functor R 1)).app S.X₁
        ((SiteModules.universalCohomologyDeltaFunctor R).δ hS 0
          ((SiteModules.cohomologyZeroMap R).app S.X₃ s)) := rfl

/-- **Stacks 0B3A.** For a ringed space `(X, O_X)` and a sheaf of `O_X`-modules `F`, first
extensions of the structure sheaf by `F` are canonically first cohomology. -/
@[stacks 0B3A "canonical bijection"]
def extOneEquivFirstCohomology (M : SheafOfModules.{u} R) :
    Abelian.Ext (SheafOfModules.unit R) M 1 ≃+ Hgroup R ⊤ 1 M :=
  (SiteModules.extOneEquivFirstCohomology R M).trans
    (Iso.addCommGroupIsoToAddEquiv ((cohomologyIsoSiteCohomology R 1).app M))

/-- The identification is the site-level one followed by the comparison isomorphism. -/
private theorem extOneEquivFirstCohomology_apply (M : SheafOfModules.{u} R)
    (ξ : Abelian.Ext (SheafOfModules.unit R) M 1) :
    extOneEquivFirstCohomology R M ξ =
      (cohomologyIsoSiteCohomology R 1).hom.app M (SiteModules.extOneEquivFirstCohomology R M ξ) :=
  rfl

/-- **Stacks 0B3A.** The class of the extension `0 → F → E → O_X → 0` goes to the image of the
unit global section `1 ∈ Γ(X, O_X)` under the connecting morphism of the extension. -/
@[stacks 0B3A "image of an extension"]
theorem extOneEquivFirstCohomology_extClass (M E : SheafOfModules.{u} R) (f : M ⟶ E)
    (g : E ⟶ SheafOfModules.unit R) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) :
    extOneEquivFirstCohomology R M hS.extClass =
      connectingMap R hS 0 (oneCohomologyClass R) := by
  have hB := forgetGlobalSectionsModule_map_siteConnectingMap_apply R hS
    (SheafOfModules.unitHomEquiv (SheafOfModules.unit R) (𝟙 _) :
      (SiteModules.globalSectionsFunctor R).obj (SheafOfModules.unit R))
  rw [extOneEquivFirstCohomology_apply]
  show _ = (cohomologyIsoSiteCohomology R 1).hom.app M
      ((forgetGlobalSectionsModule R).map (siteConnectingMap R hS 0)
        ((cohomologyIsoSiteCohomology R 0).inv.app (SheafOfModules.unit R)
          (oneCohomologyClass R)))
  rw [cohomologyIsoSiteCohomology_zero_inv_oneCohomologyClass R,
    SiteModules.extOneEquivFirstCohomology_extClass R M E f g w hS]
  exact congrArg (fun y => (cohomologyIsoSiteCohomology R 1).hom.app M y) hB.symm

/-- **Stacks 0B3A.** The connecting-image formula determines the identification uniquely. -/
@[stacks 0B3A "uniqueness"]
theorem extOneEquivFirstCohomology_unique (M : SheafOfModules.{u} R)
    (e : Abelian.Ext (SheafOfModules.unit R) M 1 ≃+ Hgroup R ⊤ 1 M)
    (he : ∀ (E : SheafOfModules.{u} R) (f : M ⟶ E)
      (g : E ⟶ SheafOfModules.unit R) (w : f ≫ g = 0)
      (hS : (ShortComplex.mk f g w).ShortExact),
      e hS.extClass = connectingMap R hS 0 (oneCohomologyClass R)) :
    e = extOneEquivFirstCohomology R M := by
  ext ξ
  obtain ⟨E, f, g, w, hS, hξ⟩ :=
    (Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum
      (SheafOfModules.{u} R) (SheafOfModules.unit R) M).1 ξ
  rw [← hξ]
  exact (he E f g w hS).trans (extOneEquivFirstCohomology_extClass R M E f g w hS).symm

/-- **Stacks 0B3A.** The identification is natural in the coefficient module sheaf. -/
@[stacks 0B3A "naturality"]
theorem extOneEquivFirstCohomology_naturality {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (e : Abelian.Ext (SheafOfModules.unit R) M 1) :
    extOneEquivFirstCohomology R N
        ((Abelian.Ext.mk₀ f).postcomp (SheafOfModules.unit R) (Nat.add_zero 1) e) =
      (Hfunctor R ⊤ 1).map f (extOneEquivFirstCohomology R M e) := by
  have hnat := ConcreteCategory.congr_hom
    ((cohomologyIsoSiteCohomology R 1).hom.naturality f)
    (SiteModules.extOneEquivFirstCohomology R M e :
      (SiteModules.cohomologyFunctor R 1 ⋙ forgetGlobalSectionsModule R).obj M)
  simp only [CategoryTheory.comp_apply] at hnat
  rw [extOneEquivFirstCohomology_apply R N, SiteModules.extOneEquivFirstCohomology_naturality R f e]
  exact hnat

end Stacks.Cohomology.SpaceModules

end
