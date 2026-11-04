module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectSumsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.DerivedCollapse
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.LerayDegreewise
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Étale cohomology on the small model of the small étale site

Abelian sheaves on `Stacks.EtaleCohomology.EtaleCoefficients.Site X`, the small model of the
small étale site of a scheme `X`, are abelian sheaves on Mathlib's small étale site, and their
cohomology is étale cohomology. Consequently, for `X` quasi-compact and quasi-separated,
cohomology on the model commutes with direct sums ([Stacks, Tag 03Q5]), and if `cd(X) < ∞` it
vanishes above `cd(X)` on abelian sheaves killed by an integer `n ≥ 1` ([Stacks, Tag 0F0Q]).

## Main definitions

* `Stacks.EtaleCohomology.ProjectionFormulaConstant.siteSheafEquiv`: abelian sheaves on the
  model are abelian sheaves on the small étale site.
* `Stacks.EtaleCohomology.ProjectionFormulaConstant.rightDerivedΓSiteIso`: the cohomology of an
  abelian sheaf on the model is the étale cohomology of the corresponding abelian sheaf.

## Main results

* `Stacks.EtaleCohomology.ProjectionFormulaConstant.preservesColimitsOfShape_rightDerived_Γ_site`:
  for `X` quasi-compact and quasi-separated, cohomology on the model commutes with direct sums.
* `Stacks.EtaleCohomology.ProjectionFormulaConstant.exists_isZero_rightDerived_Γ_site`: if
  `cd(X) < ∞`, cohomology on the model of abelian sheaves killed by an integer `n ≥ 1` vanishes in
  all large enough degrees.

## References

* [Stacks Project, Tag 0F0Q](https://stacks.math.columbia.edu/tag/0F0Q)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology.EtaleCoefficients

universe u

namespace Stacks.EtaleCohomology.ProjectionFormulaConstant

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

variable (X : Scheme.{u})

/-- **Abelian sheaves on the small model of the small étale site are abelian sheaves on the
small étale site.** The inverse functor is restriction along the comparison
`Stacks.EtaleCohomology.EtaleCoefficients.toEtale`. -/
abbrev siteSheafEquiv :
    Sheaf (topology X) AddCommGrpCat.{u + 1} ≌ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (sheafEquiv X AddCommGrpCat.{u + 1}).symm

/-- The inverse of `siteSheafEquiv` is additive. -/
instance : (siteSheafEquiv X).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor of `siteSheafEquiv` is additive. -/
instance : (siteSheafEquiv X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- `Ext` groups of abelian sheaves on the small model exist in its universe. -/
instance : HasExt.{u + 1} (Sheaf (topology X) AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u + 1, u + 1}

/-- Global sections on the model are global sections on the small étale site. -/
def globalSectionsRestrictionIso :
    (siteSheafEquiv X).inverse ⋙ Sheaf.Γ (topology X) AddCommGrpCat.{u + 1} ≅
      Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoSheafSections _ _ (terminalIsTerminal X)) ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl) ≪≫
    (Sheaf.ΓNatIsoSheafSections _ _ ((terminalIsTerminal X).isTerminalObj (toEtale X) _)).symm

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The cohomology of an abelian sheaf on the model is the étale cohomology of the
corresponding abelian sheaf on the small étale site.** -/
def rightDerivedΓSiteIso (q : ℕ) :
    (Sheaf.Γ (topology X) AddCommGrpCat.{u + 1}).rightDerived q ≅
      (siteSheafEquiv X).functor ⋙
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q :=
  have hac : ∀ I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}, Injective I →
      (Sheaf.Γ (topology X) AddCommGrpCat.{u + 1}).rightAcyclic
        ((siteSheafEquiv X).inverse.obj I) := by
    intro I hI
    have : Injective ((siteSheafEquiv X).inverse.obj I) :=
      ((siteSheafEquiv X).symm.map_injective_iff I).2 hI
    refine (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2 ?_
    intro p hp
    obtain ⟨p, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    exact Functor.isZero_rightDerived_obj_injective_succ _ _ _
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (siteSheafEquiv X).unitIso _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _ hac q).symm ≪≫
        Functor.rightDerivedIsoOfNatIso (globalSectionsRestrictionIso X) q)

/-- An additive functor carries an object whose identity is killed by `n` to one with the same
property. -/
private theorem nsmul_id_eq_zero_of_map {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (G : C ⥤ D) [G.Additive] {Y : C} {n : ℕ} (h : n • 𝟙 Y = 0) :
    n • 𝟙 (G.obj Y) = 0 := by
  rw [← G.map_id, ← G.map_nsmul, h, G.map_zero]

/-- An abelian sheaf whose identity is killed by `n` has all its sections killed by `n`. -/
theorem nsmul_eq_zero_of_nsmul_id {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {F : Sheaf J AddCommGrpCat.{u}} {n : ℕ} (h : n • 𝟙 F = 0) (U : Cᵒᵖ) (x : F.obj.obj U) :
    n • x = 0 := by
  have h' := nsmul_id_eq_zero_of_map (sheafToPresheaf J AddCommGrpCat.{u}) h
  simpa [NatTrans.app_nsmul] using congr_arg (fun f => (f.app U).hom x) h'

/-- The equivalence of sheaf categories carries an abelian sheaf killed by `n` to one killed by
`n`. -/
theorem siteSheafEquiv_functor_nsmul_id {N : Sheaf (topology X) AddCommGrpCat.{u + 1}} {n : ℕ}
    (h : n • 𝟙 N = 0) : n • 𝟙 ((siteSheafEquiv X).functor.obj N) = 0 :=
  nsmul_id_eq_zero_of_map _ h

/-- `Ext` groups of abelian sheaves on the small étale site exist in the universe of its
objects. -/
instance hasExt_smallEtale_objectUniverse :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, u}

section QCQS

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- **The cohomology of abelian sheaves on the model commutes with direct sums**, `X` being
quasi-compact and quasi-separated. -/
theorem preservesColimitsOfShape_rightDerived_Γ_site (q : ℕ) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      ((Sheaf.Γ (topology X) AddCommGrpCat.{u + 1}).rightDerived q) := by
  have := preservesColimitsOfShape_discrete_rightDerived_Γ_smallEtale.{0} X q I
  exact preservesColimitsOfShape_of_natIso (rightDerivedΓSiteIso X q).symm

/-- **Finite cohomological dimension bounds the cohomology of torsion abelian sheaves on the
model**: if `cd(X) < ∞`, there is `d` such that `H^q(N) = 0` for every `q > d` and every abelian
sheaf `N` on the model killed by an integer `n ≥ 1`. -/
theorem exists_isZero_rightDerived_Γ_site
    (hcd : Scheme.etaleCohomologicalDimension X < ⊤) :
    ∃ d : ℕ, ∀ q : ℕ, d < q → ∀ (N : Sheaf (topology X) AddCommGrpCat.{u + 1}) (n : ℕ),
      0 < n → n • 𝟙 N = 0 →
        IsZero (((Sheaf.Γ (topology X) AddCommGrpCat.{u + 1}).rightDerived q).obj N) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hcd.ne
  refine ⟨d, fun q hq N n hn hN => IsZero.of_iso ?_ ((rightDerivedΓSiteIso X q).app N)⟩
  have hN' := siteSheafEquiv_functor_nsmul_id X hN
  refine (Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}
    X.smallEtaleTopology _ q).1 ?_
  refine Scheme.isEtaleCohomologyBound_etaleCohomologicalDimension X _
    (fun U x => ⟨⊤, X.smallEtaleTopology.top_mem U, fun V g _ =>
      ⟨n, hn, nsmul_eq_zero_of_nsmul_id hN' _ _⟩⟩) q ?_
  rw [← hd]
  exact_mod_cast hq

end QCQS

end Stacks.EtaleCohomology.ProjectionFormulaConstant
