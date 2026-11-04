module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleBigFppfUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffinePresentedModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleHigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSumNaturality.ComponentCohomology

/-!
# Higher direct images along `h` of pulled back quasi-coherent modules

Let `a : U → X` be an augmentation of a simplicial algebraic space and
`h : (Sh((Spaces/U)_{fppf,total}), 𝒪_{big,total}) ⟶ (Sh(U_{spaces,étale}), 𝒪_U)` the morphism of
ringed topoi of Stacks 0DHC. For a quasi-coherent `𝒪_U`-module `G` the higher direct images
`R^p h_*(h^*G)` vanish for `p > 0`. This is the content of `G = Rh_*h^*G` in the proof of
Stacks 0DHE: in each degree `n` it is Stacks 0DGP for `h_n = a_{U_n}` at `G|_{U_n}`, carried to
the total site by Stacks 0DH1 / 0DBZ.

The argument is the one of Stacks 072W and 015C for the continuous functor `u` of `h`: every
object `V/U_n` of `U_{spaces,étale}` is covered by affine `W` over which `G|_{U_n}` is presented,
the cohomology of `h^*G` over `W/U_n` on the total site is that of its restriction to
`(Spaces/U_n)_fppf` (Stacks 0DBZ), that restriction is the pullback of `G|_{U_n}` along the
degree-`n` morphism of `h` (the degree square of `h` is Guitart exact), and the latter is
`a_{U_n}^*(G|_{U_n})` up to an identification of the source rings, whose cohomology vanishes
over `W` (Stacks 0DGP).

## Main results

In the namespace `AlgebraicGeometry.RingedToposSiteHom`:

* `nonempty_toSheaf_pullbackTopos_ofStructureMap_iso_simplicialBigFppfTotalAcyclic`: changing
  the source ring along an isomorphism does not change the underlying abelian sheaf of a
  pullback.

In the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`:

* `isZero_sheafCohomology_componentFunctor_obj`: Stacks 0DBZ as a vanishing statement.
* `isZero_sheafCohomology_bigFppfTotal_pullbackModules`.
* `isZero_rightDerived_bigFppfTotal_pushforward_pullbackModules`: `R^p h_*(h^*G) = 0` for
  `p > 0`.

## References

* [Stacks Project, Tag 0DHE](https://stacks.math.columbia.edu/tag/0DHE)
* [Stacks Project, Tag 0DH1](https://stacks.math.columbia.edu/tag/0DH1)
* [Stacks Project, Tag 0DGP](https://stacks.math.columbia.edu/tag/0DGP)
* [Stacks Project, Tag 0DBZ](https://stacks.math.columbia.edu/tag/0DBZ)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.RingedToposSiteHom

section RingIso

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O₁ O₂ : Sheaf J CommRingCat.{u}} (e : O₁ ≅ O₂) {Y : RingedTopos.{u, u, u}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (v : Y.C ⥤ C) [v.IsContinuous Y.J J]
  (φ₁ : Y.O ⟶ (v.sheafPushforwardContinuous CommRingCat.{u} Y.J J).obj O₁)
  (φ₂ : Y.O ⟶ (v.sheafPushforwardContinuous CommRingCat.{u} Y.J J).obj O₂)
  (h : φ₂ = φ₁ ≫ (v.sheafPushforwardContinuous CommRingCat.{u} Y.J J).map e.hom)
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
include e h in
/-- **Changing the source ring along an isomorphism does not change the underlying abelian sheaf
of a pullback**: for `φ₂ = φ₁ ≫ v_*(e)`, the pullbacks `f_1^*G` and `f_2^*G` have isomorphic
underlying abelian sheaves. -/
theorem nonempty_toSheaf_pullbackTopos_ofStructureMap_iso_simplicialBigFppfTotalAcyclic
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    Nonempty ((SheafOfModules.toSheaf _).obj
        ((ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).pullbackTopos.obj G) ≅
      (SheafOfModules.toSheaf _).obj
        ((ofStructureMapRingedToposSiteHomRingIso v O₂ φ₂).pullbackTopos.obj G)) := by
  let eqv := restrictScalarsEquivalenceRingedToposSiteHomRingIso J
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).mapIso e)
  let i : (ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).pullbackTopos ⋙ eqv.functor ≅
      (ofStructureMapRingedToposSiteHomRingIso v O₂ φ₂).pullbackTopos :=
    Adjunction.leftAdjointUniq
      ((ofStructureMapRingedToposSiteHomRingIso v O₁ φ₁).pullbackPushforwardAdjunctionTopos.comp
        eqv.toAdjunction)
      (Adjunction.ofNatIsoRight
        (ofStructureMapRingedToposSiteHomRingIso v O₂ φ₂).pullbackPushforwardAdjunctionTopos
        (pushforwardTopos_ofStructureMap_iso_ringedToposSiteHomRingIso e v φ₁ φ₂ h))
  exact ⟨Iso.refl _ ≪≫ (SheafOfModules.toSheaf _).mapIso (i.app G)⟩

end RingIso

end AlgebraicGeometry.RingedToposSiteHom

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

section Component

/-- Sheaf cohomology vanishing transfers along an isomorphism of abelian sheaves. -/
private theorem isZero_H'_of_iso {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    {F F' : Sheaf J AddCommGrpCat.{u}} (i : F ≅ F') {p : ℕ} {V : C}
    (h : IsZero (Sheaf.H'.{w} F' p V)) : IsZero (Sheaf.H'.{w} F p V) :=
  IsZero.of_iso h (((Sheaf.cohomologyPresheafFunctor _ p).mapIso i).app (op V))

/-- **Stacks 0DBZ, read as a vanishing statement.** Cohomology on the total site of a
simplicial-site situation over an object of degree `n` vanishes as soon as the cohomology of the
restriction to degree `n` vanishes there; the component topology may be given by any topology
equal to it. -/
theorem isZero_sheafCohomology_componentFunctor_obj (C : SimplicialSiteSituation.{u})
    (n : SimplexCategory)
    (K : GrothendieckTopology (C.component n)) (hK : C.componentTopology n = K)
    {_ : HasSheafify C.totalTopology AddCommGrpCat.{u}} {_ : HasSheafify K AddCommGrpCat.{u}}
    {_ : HasExt.{w} (Sheaf C.totalTopology AddCommGrpCat.{u})}
    {_ : HasExt.{w} (Sheaf K AddCommGrpCat.{u})}
    [(SimplicialSiteSituation.componentFunctor C n).IsContinuous K C.totalTopology]
    (F : Sheaf C.totalTopology AddCommGrpCat.{u}) (p : ℕ) (V : C.component n)
    (h : IsZero (Sheaf.H'.{w}
      (((SimplicialSiteSituation.componentFunctor C n).sheafPushforwardContinuous
        AddCommGrpCat.{u} K C.totalTopology).obj F) p V)) :
    IsZero (Sheaf.H'.{w} F p ((SimplicialSiteSituation.componentFunctor C n).obj V)) := by
  subst hK
  refine IsZero.of_iso ?_ (Stacks.Cohomology.SimplicialComponent.cohomologyObj_iso_component.{w}
    C n V F p)
  exact isZero_H'_of_iso
    ((Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous _ _ _ _).app F) h

end Component


variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {U : SimplicialObject T.Spaces} {X : T.Spaces}
  (a : U ⟶ (SimplicialObject.const T.Spaces).obj X)

section Degree

attribute [local instance] slicesι_isContinuous slicesι_isCocontinuous

variable (n : SimplexCategory)

/-- **Higher cohomology of the degree-`n` pullback vanishes on affine objects** over which the
module is presented. The degree-`n` morphism of `h` is `a_{U_n}` up to the identification
`degreeRingIso` of the source rings, which does not change the underlying abelian sheaves, and
for `a_{U_n}` this is the vanishing used for Stacks 0DGP. -/
theorem isZero_sheafCohomology_degreeRingedSiteHom_pullbackTopos
    (G : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).J)
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)))
        (degreeInclusion U n)).O))
    (W : SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n)))
    (hW : SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem (U.obj (op n)) W)
    (hG : (G.over W).HasGlobalPresentation) (p : ℕ) (hp : 0 < p)
    [HasExt.{w} (Sheaf (BigFppfSpaceOver.topology T (U.obj (op n))) AddCommGrpCat.{u + 1})] :
    IsZero (Sheaf.H'.{w} ((SheafOfModules.toSheaf _).obj
      ((degreeRingedSiteHom a n).toRingedToposSiteHom.pullbackTopos.obj G)) p
        ((SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))).obj W)) := by
  open RingedToposSiteHom in
  obtain ⟨i⟩ := nonempty_toSheaf_pullbackTopos_ofStructureMap_iso_simplicialBigFppfTotalAcyclic
    (degreeRingIso a n)
    (Y := RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
      ((ringedSite U).restrictRestrictionSquarePullbackMate
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))) (degreeInclusion U n)))
    (SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))) (degreeStructureMap a n)
    (BigFppfSpaceSite.spacesEtaleRestrictionStructureIso T (U.obj (op n))).hom
    (spacesEtaleRestrictionStructureIso_hom_eq a n) G
  have h₂ : IsZero (Sheaf.H'.{w} ((SheafOfModules.toSheaf _).obj
      ((BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T
        (U.obj (op n))).toRingedToposSiteHom.pullbackTopos.obj G)) p
      ((SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))).obj W)) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have := @BigFppfSpaceSite.isZero_H'_of_hasGlobalPresentation _ _ _
      _ _ hW (BigFppfSpaceSite.hasGlobalPresentation_over_pullback G W hG) (q + 1) hp
    exact Stacks.Cohomology.ModuleDirectImageOnACover.isZero_sheafCohomology_chgUniv _ _ _ _ this
  exact isZero_H'_of_iso i h₂

/-- **Higher cohomology of `h^*G` on the total site vanishes over `W/U_n`** for an affine `W`
étale over `U_n` over which `G|_{U_n}` is presented: by Stacks 0DBZ it is cohomology on
`(Spaces/U_n)_fppf` of the restriction of `h^*G` to degree `n`, which is the degree-`n` pullback
of `G|_{U_n}` because the degree square of `h` is Guitart exact (Stacks 0DH0). -/
theorem isZero_sheafCohomology_bigFppfTotal_pullbackModules
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O))
    (W : SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n)))
    (hW : SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem (U.obj (op n)) W)
    (hG : (((degreeRestrictModules n).obj G).over W).HasGlobalPresentation) (p : ℕ) (hp : 0 < p)
    [HasExt.{w} (Sheaf (SimplicialOver.totalTopology T.topology U) AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (BigFppfSpaceOver.topology T (U.obj (op n))) AddCommGrpCat.{u + 1})] :
    IsZero (Sheaf.H'.{w} ((SheafOfModules.toSheaf _).obj
      ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1} (bigFppfTotalRingedSiteHom a).ringedToposHom.toModulesHom).obj G)) p
      ((toBigFppfTotal U).obj ((degreeInclusion U n).obj W))) := by
  let f := (bigFppfTotalRingedSiteHom a)
  let g := degreeRingedSiteHom a n
  let α := (f.restrictPullbackMateRestrictionSquarePullbackMate
    (BigFppfSpaceOver.topology T (U.obj (op n)))
    (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))) (slicesι U n)
    (degreeInclusion U n) g (degreeHomSquare a n) (degreeRingedSiteHom_fsharp_compat a n))
  have := f.isIso_restrictPullbackMate_restrictionSquarePullbackMate
    (BigFppfSpaceOver.topology T (U.obj (op n)))
    (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))) (slicesι U n)
    (degreeInclusion U n) g (degreeHomSquare a n) (degreeRingedSiteHom_fsharp_compat a n)
  let β : Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1} g.ringedToposHom.toModulesHom ≅ g.toRingedToposSiteHom.pullbackTopos :=
    Adjunction.leftAdjointUniq
      ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        g.ringedToposHom).ofNatIsoRight g.pushforwardToposIso)
      g.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
  have h₁ := isZero_sheafCohomology_degreeRingedSiteHom_pullbackTopos.{w} a n
    ((degreeRestrictModules n).obj G) W hW hG p hp
  have h₂ : IsZero (Sheaf.H'.{w} (((slicesι U n).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (BigFppfSpaceOver.topology T (U.obj (op n))) (SimplicialOver.totalTopology T.topology U)).obj
        ((SheafOfModules.toSheaf _).obj
          ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
            u + 1, u + 1, u + 1} f.ringedToposHom.toModulesHom).obj G))) p
      ((SpacesEtale.inclusion T.schemeSite S T.scheme_mem (U.obj (op n))).obj W)) :=
    isZero_H'_of_iso ((SheafOfModules.toSheaf _).mapIso
      ((asIso (α.natTrans.app G)).symm ≪≫ β.app _)) h₁
  have : ((SimplicialOver.situation T.topology U).componentFunctor n).IsContinuous
      (BigFppfSpaceOver.topology T (U.obj (op n)))
      (SimplicialOver.situation T.topology U).totalTopology := slicesι_isContinuous U n
  exact isZero_sheafCohomology_componentFunctor_obj.{w} (SimplicialOver.situation T.topology U) n
    (BigFppfSpaceOver.topology T (U.obj (op n)))
    (SimplicialOver.componentTopology_eq T.topology U n) _ p _ h₂

/-- The affine objects of `(U_n)_{spaces,étale}` over `V` over which the restriction of `G` to
degree `n` has a global presentation. -/
def degreePresentedAffinePresieve
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O))
    (V : SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n))) : Presieve V :=
  fun W _ ↦ SpacesEtale.IsAffineScheme T.schemeSite S T.scheme_mem (U.obj (op n)) W ∧
    (((degreeRestrictModules n).obj G).over W).HasGlobalPresentation

/-- For a quasi-coherent `G` these affine objects cover every object of `(U_n)_{spaces,étale}`. -/
theorem generate_degreePresentedAffinePresieve_mem
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O))
    [G.IsQuasicoherentOnSite] (V : SpacesEtale T.schemeSite S T.scheme_mem (U.obj (op n))) :
    Sieve.generate (degreePresentedAffinePresieve n G V) ∈
      SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n)) V := by
  obtain ⟨I, Vi, fi, hcov, hpres⟩ :=
    (isQuasicoherentOnSite_degreeRestrictModules_obj n G).locally_hasGlobalPresentation V
  refine (SpacesEtale.topology T.schemeSite S T.scheme_mem _).superset_covering ?_
    ((SpacesEtale.topology T.schemeSite S T.scheme_mem _).bind_covering hcov
      (fun Y _ _ ↦ SpacesEtale.generate_affineSchemePresieve_mem T.schemeSite S
        T.scheme_mem _ Y))
  rintro Z _ ⟨Y, g, z, hz, hg, rfl⟩
  obtain ⟨Z', z₁, z₂, hz₂, rfl⟩ := hz
  obtain ⟨i⟩ := hz₂
  obtain ⟨Z'', g₁, g₂, hg₂, rfl⟩ := hg
  refine ⟨Z'', g₁, g₂ ≫ z₁ ≫ fi i, ⟨hg₂, ?_⟩, by simp⟩
  exact SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} _ (g₂ ≫ z₁) (hpres i)

/-- Sheaves of modules on `U_{spaces,étale}` form an abelian category, read at the universes of
its ringed topos. -/
noncomputable local instance abelian_ringedSiteModules :
    Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (ringedSite U)).O)) :=
  inferInstance

/-- Sheaves of modules on `(Spaces/U)_{fppf,total}` form an abelian category, read at the
universes of its ringed topos. -/
noncomputable local instance abelian_bigFppfTotalModules :
    Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfTotalRingedSite a)).O)) :=
  inferInstance

/-- Sheaves of modules on `(Spaces/U)_{fppf,total}` have enough injectives. -/
local instance enoughInjectives_bigFppfTotalModules :
    EnoughInjectives (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfTotalRingedSite a)).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

/-- The direct image along `h` is additive. -/
local instance additive_bigFppfTotal_pushforwardTopos :
    (bigFppfTotalRingedSiteHom a).toRingedToposSiteHom.pushforwardTopos.Additive :=
  RingedToposSiteHom.pushforwardTopos_additive.{u + 1} _

/-- **The higher direct images along `h` of `h^*G` vanish for a quasi-coherent `𝒪_U`-module `G`**
(Stacks 0DH1 with Stacks 0DGP in each degree): `R^p h_*(h^*G) = 0` for `p > 0`. Every object
`V/U_n` of `U_{spaces,étale}` is covered by affine `W` over which `G|_{U_n}` is presented, and
over these the cohomology of `h^*G` vanishes by
`isZero_sheafCohomology_bigFppfTotal_pullbackModules`; the criterion of Stacks 072W and 015C then
applies to the continuous functor `u` of `h`. -/
theorem isZero_rightDerived_bigFppfTotal_pushforward_pullbackModules
    (G : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (ringedSite U).O))
    [G.IsQuasicoherentOnSite] (p : ℕ) (hp : 0 < p) :
    IsZero (((bigFppfTotalRingedSiteHom a).toRingedToposSiteHom.pushforwardTopos.rightDerived p).obj
        ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
          u + 1, u + 1, u + 1} (bigFppfTotalRingedSiteHom a).ringedToposHom.toModulesHom).obj
            G)) := by
  have := Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse
    (Sheaf (SimplicialOver.totalTopology T.topology U) AddCommGrpCat.{u + 1})
  have := (bigFppfTotalRingedSiteHom a).toRingedToposSiteHom.isContinuous
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve.{
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (bigFppfTotalRingedSiteHom a).toRingedToposSiteHom.u _ _
    (bigFppfTotalRingedSiteHom a).toRingedToposSiteHom.fSharpRing p _ (fun V ↦ ?_)
  obtain ⟨m, V₀⟩ := V
  refine ⟨(Presieve.map (degreeInclusion U m) (degreePresentedAffinePresieve m G V₀) :
      Presieve ((degreeInclusion U m).obj V₀)), ?_, fun W g hg ↦ ?_⟩
  · have hmem := functorPushforward_degreeInclusion_mem
      (generate_degreePresentedAffinePresieve_mem m G V₀)
    rw [← Sieve.generate_map_eq_functorPushforward] at hmem
    exact hmem
  · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rcases hg with ⟨hY⟩
    have := Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse
      (Sheaf (BigFppfSpaceOver.topology T (U.obj (op m))) AddCommGrpCat.{u + 1})
    open Stacks.Cohomology.ModuleDirectImageOnACover in
    exact isZero_rightDerived_evaluation_of_isZero_H'_chgUniv
      _ _ _ q _ (isZero_sheafCohomology_bigFppfTotal_pullbackModules.{u + 1} a m G _ hY.1 hY.2
        (q + 1) (Nat.succ_pos q))

end Degree

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
