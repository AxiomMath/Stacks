module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProjectionFormulaConstant.SiteCohomology

/-!
# `Rf_*` on `D(X_étale, Λ)` commutes with direct sums (Stacks 0F11 (1))

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `cd(f) < ∞`, and
let `Λ` be a torsion ring. Then the derived direct image
`Rf_* : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` of `Stacks.EtaleCohomology.EtaleCoefficients` commutes with
direct sums. This is [Stacks, Tag 0F11] (1), read on the ringed topos `(X_étale, Λ̲)` of
`Stacks.EtaleCohomology.EtaleCoefficients.ringedTopos` on which the Künneth chain is built; the
proof of [Stacks, Tag 0F1N] uses it at `Rh_*` and `Rg_*`.

## The proof

The source's: `Rf_*` is the derived functor of `f_*`, which has finite cohomological dimension
and whose higher direct images commute with direct sums, so
`Stacks.DerivedFunctor.Coproducts.preservesCoproductsOfShape_of_finiteCohomologicalDimension`
applies. Both inputs are read on underlying abelian sheaves:

* forgetting the module structure commutes with the direct image, and the underlying abelian
  sheaf of an injective sheaf of modules is acyclic for the abelian direct image (the acyclicity
  behind [Stacks, Tag 03FD]); so `R^q f_*` of a sheaf of `Λ̲`-modules is `R^q f_*` of its
  underlying abelian sheaf (`rightDerivedPushforwardToposToSheafIso`);
* abelian sheaves on the small model of the étale site are abelian sheaves on `X.Etale`,
  compatibly with direct images (`siteAbelianDirectImageIso`), so the higher direct images on
  the model are those of `Stacks.EtaleCohomology.etaleAbelianDirectImage`
  (`rightDerivedSiteAbelianDirectImageIso`);
* there they commute with direct sums for `f` quasi-compact and quasi-separated
  ([Stacks, Tag 09Z1]), and vanish above `cd(f)` on torsion sheaves ([Stacks, Tag 0F0Z]); the
  underlying abelian sheaf of a sheaf of `Λ̲`-modules is killed by the additive order of `1` in
  `Λ`.

## Main results

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `preservesColimitsOfShape_rightDerived_pushforwardTopos` — `R^q f_*` commutes with direct sums.
* `exists_isZero_rightDerived_pushforwardTopos` — `R^q f_* = 0` for `q > cd(f)`.
* `preservesColimitsOfShape_pushforward` — **[Stacks, Tag 0F11] (1) on `D(X_étale, Λ)`.**

## References

* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
* [Stacks Project, Tag 0F0Z](https://stacks.math.columbia.edu/tag/0F0Z)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.EtaleCohomology.ProjectionFormulaConstant (etaleRing siteSheafEquiv)

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Abelian direct images on the small models -/

/-- **The direct image of abelian sheaves along `f`, on the small models** of the étale sites:
restriction along base change `baseChange f`. -/
abbrev siteAbelianDirectImage :
    Sheaf (topology X) AddCommGrpCat.{u + 1} ⥤ Sheaf (topology Y) AddCommGrpCat.{u + 1} :=
  (baseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1} (topology Y) (topology X)

/-- Forgetting the module structure commutes with the direct image: the underlying abelian sheaf
of `f_*M` is the direct image of the underlying abelian sheaf of `M`. -/
def pushforwardToposToSheafIso :
    (ringedToposHom Λ f).pushforwardTopos ⋙ SheafOfModules.toSheaf.{u + 1} (etaleRing Λ Y) ≅
      SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X) ⋙ siteAbelianDirectImage f :=
  Iso.refl _

/-- The base change of the small model of `Y` to `X`, read through the comparison with the small
étale site of `Y`, is base change on the small étale sites followed by the comparison. -/
def fromEtaleCompBaseChangeIso :
    fromEtale Y ⋙ baseChange f ≅ smallEtaleBaseChange f ⋙ fromEtale X :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (equiv Y).unitIso.symm (smallEtaleBaseChange f ⋙ fromEtale X) ≪≫
    Functor.leftUnitor _

/-- Base change on the small étale sites followed by the comparison with the small model of `X`
is continuous. -/
instance : (smallEtaleBaseChange f ⋙ fromEtale X).IsContinuous (smallEtaleTopology Y)
    (topology X) :=
  Functor.isContinuous_comp _ _ _ (smallEtaleTopology X) _

/-- **The direct images on the small models are the direct images on the small étale sites**,
through the equivalences `siteSheafEquiv` of abelian sheaves on the two. -/
def siteAbelianDirectImageIso :
    siteAbelianDirectImage f ⋙ (siteSheafEquiv Y).functor ≅
      (siteSheafEquiv X).functor ⋙ etaleAbelianDirectImage.{u, 0} f :=
  Functor.sheafPushforwardContinuousComp' (fromEtaleCompBaseChangeIso f) AddCommGrpCat.{u + 1}
      (smallEtaleTopology Y) (topology Y) (topology X) ≪≫
    (Functor.sheafPushforwardContinuousComp (smallEtaleBaseChange f) (fromEtale X)
      AddCommGrpCat.{u + 1} (smallEtaleTopology Y) (smallEtaleTopology X) (topology X)).symm

/-! ### Higher direct images of sheaves of modules -/

/-- The direct image `f_*` of sheaves of `Λ̲`-modules preserves finite limits. -/
instance : PreservesFiniteLimits (ringedToposHom Λ f).pushforwardTopos :=
  have := (ringedToposHom Λ f).pullbackPushforwardAdjunctionTopos.rightAdjoint_preservesLimits
  inferInstance

/-- The direct image `f_*` of sheaves of `Λ̲`-modules is additive. -/
instance : (ringedToposHom Λ f).pushforwardTopos.Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The underlying abelian sheaf of an injective sheaf of `Λ̲`-modules is acyclic for the
abelian direct image (the acyclicity behind [Stacks, Tag 03FD]). -/
theorem rightAcyclic_siteAbelianDirectImage_toSheaf (I : SheafOfModules.{u + 1} (etaleRing Λ X))
    (_ : Injective I) :
    (siteAbelianDirectImage f).rightAcyclic
      ((SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X)).obj I) := by
  refine (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2
    fun p hp => ?_
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_higherDirectImage_toSheaf_succ.{0}
    (topology Y) (topology X) (baseChange f) (etaleRing Λ X) I q

/-- Forgetting the module structure of a sheaf of `Λ̲`-modules preserves homology. -/
instance : (SheafOfModules.toSheaf.{u + 1} (etaleRing Λ Y)).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The equivalence `siteSheafEquiv Y` of abelian sheaves preserves homology. -/
instance : (siteSheafEquiv Y).functor.PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- **The higher direct images of a sheaf of `Λ̲`-modules are those of its underlying abelian
sheaf.** -/
def rightDerivedPushforwardToposToSheafIso (q : ℕ) :
    (ringedToposHom Λ f).pushforwardTopos.rightDerived q ⋙
        SheafOfModules.toSheaf.{u + 1} (etaleRing Λ Y) ≅
      SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X) ⋙ (siteAbelianDirectImage f).rightDerived q :=
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _ (pushforwardToposToSheafIso Λ f)
      q ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _
      (rightAcyclic_siteAbelianDirectImage_toSheaf Λ f) q

/-- **The higher direct images on the small models are those on the small étale sites.** -/
def rightDerivedSiteAbelianDirectImageIso (q : ℕ) :
    (siteAbelianDirectImage f).rightDerived q ⋙ (siteSheafEquiv Y).functor ≅
      (siteSheafEquiv X).functor ⋙ (etaleAbelianDirectImage.{u, 0} f).rightDerived q :=
  have hac : ∀ I : Sheaf (topology X) AddCommGrpCat.{u + 1}, Injective I →
      (etaleAbelianDirectImage.{u, 0} f).rightAcyclic ((siteSheafEquiv X).functor.obj I) := by
    intro I hI
    have : Injective ((siteSheafEquiv X).functor.obj I) :=
      ((siteSheafEquiv X).map_injective_iff I).2 hI
    refine (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).2
      fun p hp => ?_
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    exact Functor.isZero_rightDerived_obj_injective_succ _ _ _
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _ (siteAbelianDirectImageIso f) q ≪≫
    Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic _ _ hac q

/-- The underlying abelian sheaf on the small étale site of a sheaf of `Λ̲`-modules. -/
abbrev etaleToSheaf (X : Scheme.{u}) :
    SheafOfModules.{u + 1} (etaleRing Λ X) ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X) ⋙ (siteSheafEquiv X).functor

/-- **`R^q f_*` of a sheaf of `Λ̲`-modules, read on the small étale site, is `R^q f_*` of its
underlying abelian sheaf there.** -/
def rightDerivedPushforwardToposIso (q : ℕ) :
    (ringedToposHom Λ f).pushforwardTopos.rightDerived q ⋙ etaleToSheaf Λ Y ≅
      etaleToSheaf Λ X ⋙ (etaleAbelianDirectImage.{u, 0} f).rightDerived q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedPushforwardToposToSheafIso Λ f q) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedSiteAbelianDirectImageIso f q) ≪≫
    (Functor.associator _ _ _).symm

/-- Taking the underlying abelian sheaf on the small étale site commutes with direct sums. -/
instance (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) (etaleToSheaf Λ X) :=
  have : PreservesColimitsOfShape (Discrete I)
      (SheafOfModules.toSheaf.{u + 1} (etaleRing Λ X)) :=
    SheafOfModules.preservesColimitsOfShape_toSheaf _
  inferInstance

/-- Taking the underlying abelian sheaf on the small étale site reflects direct sums. -/
instance (I : Type (u + 1)) : ReflectsColimitsOfShape (Discrete I) (etaleToSheaf Λ X) :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms

/-- A sheaf of `Λ̲`-modules whose underlying abelian sheaf on the small étale site is zero is
zero. -/
theorem isZero_of_isZero_etaleToSheaf_obj {M : SheafOfModules.{u + 1} (etaleRing Λ X)}
    (h : IsZero ((etaleToSheaf Λ X).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply (etaleToSheaf Λ X).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_of_src _ _

/-- **The higher direct images of sheaves of `Λ̲`-modules commute with direct sums** along a
quasi-compact and quasi-separated morphism ([Stacks, Tag 09Z1] on underlying abelian sheaves). -/
theorem preservesColimitsOfShape_rightDerived_pushforwardTopos [QuasiCompact f]
    [QuasiSeparated f] (q : ℕ) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I)
      ((ringedToposHom Λ f).pushforwardTopos.rightDerived q) := by
  have := preservesColimitsOfShape_discrete_rightDerived_etaleAbelianDirectImage.{0} f q I
  have : PreservesColimitsOfShape (Discrete I)
      ((ringedToposHom Λ f).pushforwardTopos.rightDerived q ⋙ etaleToSheaf Λ Y) :=
    preservesColimitsOfShape_of_natIso (rightDerivedPushforwardToposIso Λ f q).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ (etaleToSheaf Λ Y)

/-- **Finite cohomological dimension of `f` and torsion coefficients bound the higher direct
images**: `R^q f_* M = 0` for every sheaf of `Λ̲`-modules `M` and every `q > cd(f)`. -/
theorem exists_isZero_rightDerived_pushforwardTopos [QuasiCompact f] [QuasiSeparated f]
    (hcd : f.etaleCohomologicalDimension < ⊤) (hΛ : IsAddTorsion Λ) :
    ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ M : SheafOfModules.{u + 1} (etaleRing Λ X),
      IsZero (((ringedToposHom Λ f).pushforwardTopos.rightDerived q).obj M) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hcd.ne
  have hm : ((addOrderOf (1 : Λ) : ℕ) : Λ) = 0 :=
    (nsmul_one _).symm.trans (addOrderOf_nsmul_eq_zero 1)
  refine ⟨d + 1, fun q hq M => isZero_of_isZero_etaleToSheaf_obj Λ ?_⟩
  refine IsZero.of_iso ?_ ((rightDerivedPushforwardToposIso Λ f q).app M)
  have hM := Stacks.EtaleCohomology.ProjectionFormulaConstant.siteSheafEquiv_functor_nsmul_id X
    (Stacks.EtaleCohomology.ProjectionFormulaConstant.nsmul_id_toSheaf_eq_zero Λ X hm M)
  refine f.isZero_rightDerived_etaleAbelianDirectImage _
    (fun U x => ⟨⊤, X.smallEtaleTopology.top_mem U, fun V g _ => ⟨_, (hΛ 1).addOrderOf_pos,
      Stacks.EtaleCohomology.ProjectionFormulaConstant.nsmul_eq_zero_of_nsmul_id hM _ _⟩⟩) q ?_
  rw [← hd]
  exact_mod_cast hq

/-- **[Stacks, Tag 0F11] (1) on `D(X_étale, Λ)`.** Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of schemes with `cd(f) < ∞` and let `Λ` be a torsion ring. Then
`Rf_* : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` commutes with direct sums. -/
theorem preservesColimitsOfShape_pushforward [QuasiCompact f] [QuasiSeparated f]
    (hcd : f.etaleCohomologicalDimension < ⊤) (hΛ : IsAddTorsion Λ) (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) (pushforward Λ f) := by
  obtain ⟨d, hd⟩ := exists_isZero_rightDerived_pushforwardTopos Λ f hcd hΛ
  exact Stacks.DerivedFunctor.Coproducts.preservesCoproductsOfShape_of_finiteCohomologicalDimension
    _ _ (ringedToposHom Λ f).pushforwardTopos d hd
    (preservesColimitsOfShape_rightDerived_pushforwardTopos Λ f) _
    (derivedPushforwardUnit (ringedToposHom Λ f)) I

end Stacks.EtaleCohomology.EtaleCoefficients
