module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.SiteCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.TerminalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedGlobalSectionsOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits
public import StacksFrontier.AlgebraicGeometry.RecoveryAux.DerivedFunctorCoproducts

/-!
# The derived direct image to the point commutes with direct sums

Let `X` be a quasi-compact and quasi-separated scheme with `cd(X) < ∞` and let `Λ` be a torsion
ring. For the structure morphism `π : (Sh(X_étale), Λ̲) ⟶ (Sh(pt), Λ)` of
`Stacks.EtaleCohomology.ProjectionFormulaConstant.toPoint`, the unbounded derived direct image
`Rπ_* = RΓ(X, -)` commutes with direct sums. This is [Stacks, Tag 0F11] (2).

The argument is the source's: the higher direct images `R^qπ_*` vanish above `cd(X)` on every
sheaf of `Λ̲`-modules and commute with direct sums, so
`Stacks.DerivedFunctor.Coproducts.preservesCoproductsOfShape_of_finiteCohomologicalDimension`
applies. Both inputs are read off the abelian cohomology of the underlying abelian sheaf: on the
point, sections over the point is an equivalence of sheaves of modules with modules, and the
sections over the point of `π_* M` are the sections of `M` over `X`
(`Stacks.EtaleCohomology.ProjectionFormulaConstant.pushforwardSectionsIso`, through
`Stacks.Cohomology.LerayOfToposHom.pushforwardModulesCompGlobalSectionsIso`); the underlying
abelian sheaf of an injective sheaf of modules is acyclic for sections over `X` (the acyclicity
behind [Stacks, Tag 03FD]); and the cohomology of an abelian sheaf on the model of the site is
étale cohomology (`Stacks.EtaleCohomology.ProjectionFormulaConstant.rightDerivedΓSiteIso`). The
underlying abelian sheaf of a sheaf of `Λ̲`-modules is killed by the additive order of `1` in
`Λ`, hence is torsion, so `cd(X)` bounds its cohomology.

## Main results

* `Stacks.EtaleCohomology.ProjectionFormulaConstant.rightDerivedPushforwardIso`: `R^qπ_*`, read on
  sections over the point, is the étale cohomology of the underlying abelian sheaf.
* `exists_isZero_rightDerived_pushforwardToPoint`: for `cd(X) < ∞` and `Λ` torsion, `R^qπ_*`
  vanishes for `q` large, uniformly in the sheaf of modules.
* `preservesColimitsOfShape_rightDerived_pushforwardToPoint`: each `R^qπ_*` commutes with direct
  sums.
* `preservesColimitsOfShape_derivedPushforward_toPoint`: `Rπ_*` commutes with direct sums.

## References

* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
* [Stacks Project, Tag 0F12](https://stacks.math.columbia.edu/tag/0F12)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.RingedToposHom
open Stacks.EtaleCohomology.EtaleCoefficients
open Stacks.Cohomology.SiteModules
open Stacks.Cohomology.InjectiveModuleSheafAcyclicity
open Stacks.PointRingedSite (ev pt)

universe u

namespace Stacks.EtaleCohomology.ProjectionFormulaConstant

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The underlying abelian group of the sections over the point. -/
abbrev pointSections : SheafOfModules.{u + 1} (pointRing Λ) ⥤ AddCommGrpCat.{u + 1} :=
  ev Λ ⋙ forget₂ (ModuleCat.{u + 1} (pointScalars Λ)) AddCommGrpCat.{u + 1}

/-- The point is a terminal object of its site. -/
def ptIsTerminal : IsTerminal (pt Λ) :=
  IsTerminal.ofUniqueHom (fun Y => eqToHom (by rcases Y with ⟨⟨⟩⟩; rfl))
    (fun Y m => by rcases m with ⟨⟨h⟩⟩; rfl)

/-- Global sections on the point, as abelian groups, are the sections over the point. -/
def globalSectionsPointIso :
    globalSectionsFunctor (pointRing Λ) ⋙ forget₂ _ AddCommGrpCat.{u + 1} ≅ pointSections Λ :=
  globalSectionsForgetIsoOfIsTerminal (pointRing Λ) (ptIsTerminal Λ) ≪≫
    NatIso.ofComponents (fun M => Iso.refl ((pointSections Λ).obj M)) (fun f => by ext; rfl)


/-- The structure sheaf of rings of the étale ringed topos. -/
abbrev etaleRing := Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O

/-- Restriction of scalars does not change the underlying abelian group. -/
def restrictScalarsForgetIso {R S : Type (u + 1)} [Ring R] [Ring S] (f : R →+* S) :
    ModuleCat.restrictScalars.{u + 1} f ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{u + 1} ≅
      forget₂ (ModuleCat S) AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents (fun M => Iso.refl ((forget₂ (ModuleCat S) AddCommGrpCat.{u + 1}).obj M))
    (fun g => by ext; rfl)

/-- **The sections over the point of the direct image of a sheaf of modules on the étale site
are its sections over `X`**, as abelian groups. -/
def pushforwardSectionsIso :
    pushforwardModules (X := ringedTopos Λ X) (Y := pointRingedTopos Λ) (toPoint Λ X) ⋙
        pointSections Λ ≅
      SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X) ⋙
        (sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op (terminal X)) :=
  Functor.isoWhiskerLeft _ (globalSectionsPointIso Λ).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Stacks.Cohomology.LerayOfToposHom.pushforwardModulesCompGlobalSectionsIso.{u + 1, u + 1,
        u + 1, u + 1, 0, 0} (toPoint Λ X)) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (restrictScalarsForgetIso _) ≪≫
    globalSectionsForgetIsoOfIsTerminal (etaleRing Λ X) (terminalIsTerminal X)


/-- The degreewise direct image of sheaves of modules to the point. -/
abbrev pushforwardToPoint :=
  pushforwardModules (X := ringedTopos Λ X) (Y := pointRingedTopos Λ) (toPoint Λ X)

/-- The direct image to the point preserves finite limits. -/
instance : PreservesFiniteLimits (pushforwardToPoint Λ X) :=
  pushforwardModules_preservesFiniteLimits (toPoint Λ X)

/-- The direct image to the point is additive. -/
instance : (pushforwardToPoint Λ X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Passing from a sheaf of modules over the étale ringed topos to its underlying abelian sheaf
preserves finite colimits. -/
instance : PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X)) :=
  ⟨fun _ _ _ => SheafOfModules.preservesColimitsOfShape_toSheaf _⟩

/-- Sections over the point preserve finite colimits. -/
instance : PreservesFiniteColimits (pointSections Λ) := by
  have := ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} (pointScalars Λ)
  exact comp_preservesFiniteColimits _ _

/-- Sections over the point preserve finite limits. -/
instance : PreservesFiniteLimits (pointSections Λ) :=
  comp_preservesFiniteLimits _ _

/-- Sections over the point preserve homology. -/
instance : (pointSections Λ).PreservesHomology := Functor.preservesHomologyOfExact _

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- The underlying abelian sheaf of an injective sheaf of modules is acyclic for the sections
over `X`. -/
theorem rightAcyclic_sections_toSheaf (I : SheafOfModules.{u + 1} (etaleRing Λ X))
    (_ : Injective I) :
    ((sheafSections (topology X) AddCommGrpCat.{u + 1}).obj (op (terminal X))).rightAcyclic
      ((SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X)).obj I) := by
  refine (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2 ?_
  intro p hp
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by lia⟩
  exact isZero_rightDerived_sections_toSheaf_succ.{0, u + 1, u + 1} (topology X) (etaleRing Λ X) I
    (terminal X) q

/-- **The higher direct images to the point, read on sections over the point, are the étale
cohomology groups of the underlying abelian sheaf.** -/
def rightDerivedPushforwardIso (q : ℕ) :
    (pushforwardToPoint Λ X).rightDerived q ⋙ pointSections Λ ≅
      SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X) ⋙ (siteSheafEquiv X).functor ⋙
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q :=
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ (pointSections Λ) _
      (pushforwardSectionsIso Λ X) q ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _
      (rightAcyclic_sections_toSheaf Λ X) q ≪≫
    Functor.isoWhiskerLeft _ (Functor.rightDerivedIsoOfNatIso
      (Sheaf.ΓNatIsoSheafSections (topology X) _ (terminalIsTerminal X)).symm q ≪≫
        rightDerivedΓSiteIso X q)


/-! ### Torsion coefficients -/

/-- A natural number vanishing in `Λ` vanishes in every ring of sections of the structure sheaf
of the étale ringed topos. -/
theorem natCast_etaleRing_eq_zero {n : ℕ} (hn : (n : Λ) = 0) (U : (Site X)ᵒᵖ) :
    (n : (etaleRing Λ X).obj.obj U) = 0 := by
  have h0 : (n : RingCat.sectionsSubring (pointRing Λ).obj) = 0 := Subtype.ext (funext fun _ => hn)
  simpa only [map_natCast, map_zero] using congr_arg (fun r => globalSectionEval (etaleRing Λ X) U
    (Stacks.Cohomology.LerayOfToposHom.toposGlobalSectionsRingHom (toPoint Λ X) r)) h0

/-- The underlying abelian sheaf of a sheaf of modules over the étale ringed topos is killed by
every natural number vanishing in `Λ`. -/
theorem nsmul_id_toSheaf_eq_zero {n : ℕ} (hn : (n : Λ) = 0)
    (M : SheafOfModules.{u + 1} (etaleRing Λ X)) :
    n • 𝟙 ((SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X)).obj M) = 0 := by
  ext U x
  let y : M.val.obj U := x
  change n • y = 0
  rw [← Nat.cast_smul_eq_nsmul ((etaleRing Λ X).obj.obj U), natCast_etaleRing_eq_zero Λ X hn,
    zero_smul]

/-! ### Sections over the point reflect what is needed -/

/-- A sheaf of modules on the point whose sections over the point vanish is zero. -/
theorem isZero_of_isZero_pointSections {M : SheafOfModules.{u + 1} (pointRing Λ)}
    (h : IsZero ((pointSections Λ).obj M)) : IsZero M :=
  (IsZero.iff_id_eq_zero _).2 ((pointSections Λ).map_injective (h.eq_of_src _ _))

/-- Sections over the point preserve coproducts. -/
instance (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) (pointSections Λ) := by
  have := ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u + 1, u + 1} (pointScalars Λ)
  infer_instance

/-- Sections over the point reflect coproducts. -/
instance (I : Type (u + 1)) : ReflectsColimitsOfShape (Discrete I) (pointSections Λ) :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms

/-! ### Finite cohomological dimension and direct sums for the direct image to the point -/

section QCQS

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- **The higher direct images to the point commute with direct sums.** -/
theorem preservesColimitsOfShape_rightDerived_pushforwardToPoint (q : ℕ) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) ((pushforwardToPoint Λ X).rightDerived q) := by
  have : PreservesColimitsOfShape (Discrete I) (SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X)) :=
    SheafOfModules.preservesColimitsOfShape_toSheaf _
  have := preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale.{0} X q I
  have : PreservesColimitsOfShape (Discrete I)
      ((pushforwardToPoint Λ X).rightDerived q ⋙ pointSections Λ) :=
    preservesColimitsOfShape_of_natIso (rightDerivedPushforwardIso Λ X q).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (pointSections Λ)

/-- **Finite cohomological dimension of `X` and torsion coefficients bound the higher direct
images to the point.** -/
theorem exists_isZero_rightDerived_pushforwardToPoint
    (hcd : Scheme.etaleCohomologicalDimension X < ⊤) (hΛ : IsAddTorsion Λ) :
    ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ M : SheafOfModules.{u + 1} (etaleRing Λ X),
      IsZero (((pushforwardToPoint Λ X).rightDerived q).obj M) := by
  obtain ⟨d, hd⟩ := exists_isZero_rightDerived_Γ_site X hcd
  have h1 := hΛ (1 : Λ)
  refine ⟨d + 1, fun q hq M => isZero_of_isZero_pointSections Λ ?_⟩
  refine IsZero.of_iso ?_ ((rightDerivedPushforwardIso Λ X q).app M)
  refine IsZero.of_iso (hd q (by lia) _ (addOrderOf (1 : Λ)) h1.addOrderOf_pos
    (nsmul_id_toSheaf_eq_zero Λ X ?_ M)) ((rightDerivedΓSiteIso X q).app _).symm
  rw [← nsmul_one]
  exact addOrderOf_nsmul_eq_zero 1

/-- **The derived direct image to the point commutes with direct sums:** `RΓ(X, -)` commutes
with direct sums when `X` is quasi-compact and quasi-separated with `cd(X) < ∞` and `Λ` is a
torsion ring. This is [Stacks, Tag 0F11] (2). -/
theorem preservesColimitsOfShape_derivedPushforward_toPoint
    (hcd : Scheme.etaleCohomologicalDimension X < ⊤) (hΛ : IsAddTorsion Λ)
    (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      (Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := ringedTopos Λ X)
        (Y := pointRingedTopos Λ) (toPoint Λ X)) := by
  obtain ⟨d, hd⟩ := exists_isZero_rightDerived_pushforwardToPoint Λ X hcd hΛ
  exact Stacks.DerivedFunctor.Coproducts.preservesCoproductsOfShape_of_finiteCohomologicalDimension
    _ _ (pushforwardToPoint Λ X) d hd (preservesColimitsOfShape_rightDerived_pushforwardToPoint Λ X)
    _ ((Stacks.Cohomology.DerivedPushforward.pushforwardOnHomotopy
      (toPoint Λ X)).totalRightDerivedUnit DerivedCategory.Qh _) I

end QCQS

end Stacks.EtaleCohomology.ProjectionFormulaConstant
