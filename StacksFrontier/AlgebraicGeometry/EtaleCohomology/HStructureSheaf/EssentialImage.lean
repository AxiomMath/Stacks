module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.TwoGeneratorSquares
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# `𝒪^{perf}` is in the essential image of `Rε_*` (Stacks 0EWT)

Let `p` be a prime number and `S` a scheme over `𝔽_p`. On the underlying category of a big h site
over `S` consider the sheaf `𝒪^{perf} = colim_F 𝒪` of the fppf topology, the colimit in the
category of fppf sheaves of rings of the Frobenius system `𝒪 →^F 𝒪 →^F ⋯`
(`AlgebraicGeometry.BigHOver.isColimitPerfectionCocone`). It is the fppf sheaf underlying the h
sheaf `X ↦ Γ(Xᵃʷⁿ, 𝒪)` (`AlgebraicGeometry.BigHOver.awnRingSheaf`), so the identity functor is a
comparison of ringed sites `ε : ((Sch/S)_h, 𝒪^{perf}) ⟶ ((Sch/S)_{fppf}, 𝒪^{perf})`. Stacks 0EWT
says that `𝒪^{perf}`, viewed as an object of the derived category of the fppf site, is in the
essential image of `Rε_*`.

## Main results

* `AlgebraicGeometry.BigHOver.essImage_singleFunctor_perfectionModule`: **Stacks 0EWT**.
* `AlgebraicGeometry.BigHOver.topology_hasSheafify_addCommGrpCat` and its companions: abelian
  sheaves in the module universe admit sheafification for the h and the fppf topologies, so the
  statement carries no hypothesis on the site.

## Implementation notes

The derived categories are those of sheaves of `𝒪^{perf}`-modules, with module universe `u + 1`,
as in the statements of Stacks 0EWQ and 0EWR in this library: `𝒪^{perf}` is regarded as a module
over itself, placed in degree zero (`AlgebraicGeometry.BigHOver.perfectionModule`, the free
module of rank one with its sections raised to the module universe of the site).

The proof is that of the source. By the criterion of Stacks 0EWR it suffices that the canonical map
`c` of Stacks 0F16 at `𝒪^{perf}` is a quasi-isomorphism along every almost blow up square of the
shapes of More on Flatness, Examples 0EVG and 0EVH. Along such a square the higher fppf cohomology
of `𝒪^{perf}` vanishes on the four corners — on affine objects by Čech vanishing on standard fppf
coverings (the Čech complex of `colim_F 𝒪` is the colimit of the Čech complexes of `𝒪`, exact by
Stacks 03FJ; this is the role of Stacks 0739 and 03DW in the source), and on the modification and
the exceptional corner of Example 0EVH by Mayer–Vietoris for their two standard affine charts —
and the sequence `0 ⟶ 𝒪^{perf}(X) ⟶ 𝒪^{perf}(Z) ⊕ 𝒪^{perf}(X') ⟶ 𝒪^{perf}(E) ⟶ 0` is short exact,
as in the proof of More on Flatness, Lemma 0EVK: on the left and in the middle because `𝒪^{perf}`
is an h sheaf, on the right because `𝒪^{perf}(Z) ⟶ 𝒪^{perf}(E)` is onto. Then `c` is a
quasi-isomorphism (`Stacks.MayerVietoris.CanonicalMapOfComplexes.quasiIso_cSquare_of_shortExact`).

## References

* [Stacks Project, Tag 0EWT](https://stacks.math.columbia.edu/tag/0EWT)
* [Stacks Project, Tag 0EWR](https://stacks.math.columbia.edu/tag/0EWR)
* [Stacks Project, Tag 0EVK](https://stacks.math.columbia.edu/tag/0EVK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigHOver

-- See `StacksFrontier.AlgebraicGeometry.EtaleCohomology.HStructureSheaf.AffineAcyclic`.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

-- `AlgebraicGeometry.EssImageIffAffineAlmostBlowUpFamilyBigH`
-- (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/AlmostBlowUp/
-- AlmostBlowUpFamilyCriterion.lean:102`),
-- the form of Stacks 0EWR, is stated over the standard model of the derived category, through
-- `Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData`.
attribute [local instance] HasDerivedCategory.standard

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sheafification of abelian sheaves in the module universe

Abelian sheaves with values in the universe `u + 1` of the objects of the big h category admit
sheafification, for the h and for the fppf topology, and sheafification inverts exactly the
locally bijective maps; so sheaves of modules in that universe form an abelian category and the
derived categories below exist with no hypothesis on the site. -/

/-- Abelian sheaves in the universe of the objects of the site admit sheafification for the h
topology. -/
instance topology_hasSheafify_addCommGrpCat :
    HasSheafify (BigHOver.topology B S hS) AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, 0}

/-- For the h topology, sheafification of abelian sheaves in the universe of the objects of the
site inverts exactly the locally bijective maps. -/
instance topology_wEqualsLocallyBijective_addCommGrpCat :
    (BigHOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, 0}

/-- Abelian sheaves in the universe of the objects of the site admit sheafification for the
fppf topology. -/
instance fppfTopology_hasSheafify_addCommGrpCat :
    HasSheafify (BigHOver.fppfTopology B S hS) AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, 0}

/-- For the fppf topology, sheafification of abelian sheaves in the universe of the objects of the
site inverts exactly the locally bijective maps. -/
instance fppfTopology_wEqualsLocallyBijective_addCommGrpCat :
    (BigHOver.fppfTopology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, 0}

/-! ### Stacks 0EWT -/

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)

include hSp in
/-- **Stacks 0EWT.** Let `p` be a prime number and let `S` be a scheme over `𝔽_p`. Consider the
sheaf `𝒪^{perf} = colim_F 𝒪` on `(Sch/S)_{fppf}`. Then `𝒪^{perf}` is in the essential image of
`Rε_* : D((Sch/S)_h) ⟶ D((Sch/S)_{fppf})`.

Here `(Sch/S)_h` is a big h site over `S` and `(Sch/S)_{fppf}` its underlying category with the
fppf topology. `𝒪^{perf}` is the colimit of the Frobenius system of fppf sheaves of rings
(`AlgebraicGeometry.BigHOver.isColimitPerfectionCocone`); it is an h sheaf, so the identity is a
comparison of ringed sites `ε : ((Sch/S)_h, 𝒪^{perf}) ⟶ ((Sch/S)_{fppf}, 𝒪^{perf})`, and `Rε_*` is
any right derived functor of its direct image on sheaves of modules, with its unit `η`. The object
is `𝒪^{perf}` regarded as a module over itself and placed in degree zero. -/
@[stacks 0EWT]
theorem essImage_singleFunctor_perfectionModule
    (Rε : DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (bigHRingedSite B S hS (awnRingSheaf B S hS)).O)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((bigHRingedSite B S hS (awnRingSheaf B S hS)).ofLe
          (BigHOver.fppfTopology_le_topology B S hS)).O)))
    (η : (Stacks.Sites.CoarserTopology.modulePushforward.{u + 1, u + 1, u, u}
          (BigHOver.fppfTopology_le_topology B S hS)
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (bigHRingedSite B S hS (awnRingSheaf B S hS)).O)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
    [Rε.IsRightDerivedFunctor η (HomotopyCategory.quasiIso
      (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (bigHRingedSite B S hS (awnRingSheaf B S hS)).O))
        (ComplexShape.up ℤ))] :
    Rε.essImage ((DerivedCategory.singleFunctor _ 0).obj (perfectionModule B S hS)) := by
  have : HasExt.{u + 1} (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1}) :=
    Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp.{u + 1, u, 0}
  have : EnoughInjectives (Sheaf (fppfTopology B S hS) AddCommGrpCat.{u + 1}) :=
    Stacks.Cohomology.SiteModules.site_enoughInjectives_addCommGrp.{u + 1, u, 0}
  have : EnoughInjectives (SheafOfModules.{u + 1} (perfectionRing B S hS)) :=
    SheafOfModules.enoughInjectives_of_univLE.{u + 1, u, u + 1, u} (perfectionRing B S hS)
  let Rs := injectiveResolution (perfectionModule B S hS)
  have hge : ((DerivedCategory.singleFunctor (SheafOfModules.{u + 1} (perfectionRing B S hS))
      0).obj (perfectionModule B S hS)).IsGE 0 := inferInstance
  refine (essImage_iff_forall_isCSquareIso_generatorAlmostBlowUp_fppf_bigH.{u, u + 1, u} B S hS
    (awnRingSheaf B S hS) Rε η _ ⟨0, hge⟩).mpr fun sq ↦ ?_
  refine (Stacks.MayerVietoris.CanonicalMapOfComplexes.isCSquareIso_singleFunctor_obj_iff
    sq.square (perfectionModule B S hS) Rs).mpr ?_
  rcases sq.isGeneratorModel with h | h
  · exact quasiIso_cSquare_perfectionModule_of_oneGenerator p hSp sq h Rs
  · exact quasiIso_cSquare_perfectionModule_of_twoGenerator p hSp sq h Rs

end AlgebraicGeometry.BigHOver
