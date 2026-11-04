module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientPresentationLift
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RestrictOverConservative

/-!
# The presentation of an affine ambient scheme lifted to the localised small crystalline site

Let `B` be an object of the small crystalline site of a global crystalline situation whose ambient
scheme is affine and let `F` be a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules on
`Cris(X/S)`.  The restriction `F_{T'}` of `F` to the ambient scheme `T'` of `B` is a quasi-coherent
module on an affine scheme, hence has a global presentation

  `⊕_{K₀} 𝒪_{T'} ⟶ ⊕_{I₀} 𝒪_{T'} ⟶ F_{T'} ⟶ 0`

with index types in `Type u`.  This file carries that presentation onto the localised site
`Cris(X/S)/B`, producing two morphisms between the crystalline coproducts and the universe lift of
the module whose composite vanishes and whose restriction to `T'` is the given presentation.

It is the small-site form of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.RestrictOverPresentationLift`;
[Stacks, Tag 07IT] is stated for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)` alike, and a sheaf of
modules on `Cris(X/S)` is in general not the restriction of one on `CRIS(X/S)`.  The index types
are kept in the form `ULift.{u + 1} I₀` of a universe lift of a type in `Type u`, which is what
lets the restricted cofork be recognised as a universe lift of a cofork of sheaves of modules at
the module universe `u`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
  `.isColimitRestrictOverCrystallineCoproductCofan`
  — the restriction of a crystalline coproduct to the ambient scheme of an object over the base is
  a coproduct of copies of the universe lift of the structure sheaf of that ambient scheme.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
  `.bijective_moduleRestrictionSheafOver_map_crystallineCoproduct`
  — **restriction to the ambient scheme of `B` is bijective on morphisms out of a crystalline
  coproduct.**
* `Crystalline.GlobalCrystallineSituation.SmallSite`
  `.exists_crystallineCoproduct_cokernelCofork_restrictOver`
  — **the presentation of the affine ambient scheme of `B`, placed on `Cris(X/S)/B`**, with index
  types that are universe lifts of types in `Type u`.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

namespace CohomologyRestriction

variable (B : CrystallineThickening S)

/-- Restriction to the ambient scheme of an object over the base carries a vanishing composite to
a vanishing composite, being a functor which preserves zero morphisms. -/
theorem moduleRestrictionSheafOver_map_comp_eq_zero {A : CrystallineThickening S} (h : A ⟶ B)
    {Q P N : SheafOfModules.{u + 1} ((structureSheaf S).over B)} {a : Q ⟶ P} {b : P ⟶ N}
    (hab : a ≫ b = 0) :
    (moduleRestrictionSheafOverFunctor.{u + 1} h).map a ≫
        (moduleRestrictionSheafOverFunctor.{u + 1} h).map b = 0 := by
  rw [← Functor.map_comp, hab]
  exact (moduleRestrictionSheafOverFunctor.{u + 1} h).map_zero _ _

/-- **The restriction of a crystalline coproduct to the ambient scheme of an object over the base
is a coproduct of copies of the universe lift of the structure sheaf of that ambient scheme**, over
the same index type. -/
noncomputable def isColimitRestrictOverCrystallineCoproductCofan (I : Type (u + 1))
    {A : CrystallineThickening S} (h : A ⟶ B) :
    IsColimit (Cofan.mk
        ((moduleRestrictionSheafOverFunctor.{u + 1} h).obj
          (CrystallineThickening.crystallineCoproduct B I))
        (fun i => (moduleRestrictionSheafOverFunctor.{u + 1} h).map
          (CrystallineThickening.crystallineCoproductι B I i)) :
      Cofan fun _ : I => SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
        (SheafOfModules.unit (Thickening.ringRestrictionSheaf A.obj))) := by
  haveI := preservesColimitsOfSize_moduleRestrictionSheafOverFunctor.{u} h
  exact isColimitCofanMkObjOfIsColimit
    (show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
        SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf A.obj) from
      moduleRestrictionSheafOverFunctor.{u + 1} h)
    _ (CrystallineThickening.crystallineCoproductι B I)
    (CrystallineThickening.isColimitCrystallineCoproductCofan B I)

/-- The universe lift of the sections of a sheaf of modules on the Zariski site of the ambient
scheme of an object, at the module universe `u + 1` at which a global presentation on a localised
small crystalline site is read. -/
noncomputable abbrev ambientUliftFunctor (A : CrystallineThickening S) :
    SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj) ⥤
      SheafOfModules.{u + 1} (Thickening.ringRestrictionSheaf A.obj) :=
  SheafOfModules.uliftForPresentationFunctor.{u, u, u, u, u + 1}

/-- Sheafification of `AddCommGrpCat`-valued presheaves on the Zariski site of the ambient scheme
of an object exists at the module universes `u` and `u + 1`, and the sheafification equivalences
are the local bijections; so the universe lift of the sections there preserves colimits of size
`u`. -/
theorem preservesColimitsOfSize_ambientUliftFunctor (A : CrystallineThickening S) :
    PreservesColimitsOfSize.{u, u} (ambientUliftFunctor A) := by
  have _ : HasSheafify (Opens.grothendieckTopology ↥A.obj.thickening.target.scheme)
      AddCommGrpCat.{u} := GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      (Opens.grothendieckTopology ↥A.obj.thickening.target.scheme) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} _
  have _ : HasSheafify (Opens.grothendieckTopology ↥A.obj.thickening.target.scheme)
      AddCommGrpCat.{u + 1} := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      (Opens.grothendieckTopology ↥A.obj.thickening.target.scheme) AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _
  exact SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor.{u, u, u, u, u + 1}

/-- The universe lift of the sections on the Zariski site of the ambient scheme of an object
preserves finite colimits; see
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`
`.preservesColimitsOfSize_ambientUliftFunctor`. -/
theorem preservesFiniteColimits_ambientUliftFunctor (A : CrystallineThickening S) :
    PreservesFiniteColimits (ambientUliftFunctor A) := by
  have := preservesColimitsOfSize_ambientUliftFunctor A
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- **The restriction to the ambient scheme of `B` carries the greatest open of that scheme to a
terminal object of the localised small crystalline site.** -/
noncomputable def isTerminal_restrictOverFunctorObjTop :
    IsTerminal ((restrictOverFunctor (𝟙 B)).obj (⊤ : B.obj.thickening.target.scheme.Opens)) :=
  IsTerminal.ofIso (Over.mkIdTerminal (X := B))
    (restrictOverFunctorObjTopIso B (Over.mk (𝟙 B))).symm

/-- **The global section attached to the restriction of a morphism out of the universe lift of the
structure sheaf is the global section attached to the morphism itself**, read over the image of the
greatest open of the ambient scheme of `B`.  The two readings agree on the nose. -/
theorem uliftUnitHomEquiv_moduleRestrictionSheafOver_map
    (Z : SheafOfModules.{u + 1} ((structureSheaf S).over B))
    (φ : CrystallineThickening.uliftUnitOver B ⟶ Z) :
    SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
        (isTerminalTop (α := B.obj.thickening.target.scheme.Opens))
        ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj Z)
        ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ) =
      SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
        (isTerminal_restrictOverFunctorObjTop B) Z φ :=
  rfl

/-- **Restriction to the ambient scheme of `B` is bijective on morphisms out of the universe lift
of the structure sheaf of the localised small crystalline site.** -/
theorem bijective_moduleRestrictionSheafOver_map_uliftUnit
    (Z : SheafOfModules.{u + 1} ((structureSheaf S).over B)) :
    Function.Bijective
      (fun φ : CrystallineThickening.uliftUnitOver B ⟶ Z ↦
        (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ) := by
  have hcomp : (fun φ : CrystallineThickening.uliftUnitOver B ⟶ Z ↦
      SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
        (isTerminalTop (α := B.obj.thickening.target.scheme.Opens))
        ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj Z)
        ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ)) =
      fun φ ↦ SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
        (isTerminal_restrictOverFunctorObjTop B) Z φ :=
    funext fun φ ↦ uliftUnitHomEquiv_moduleRestrictionSheafOver_map B Z φ
  have hright : Function.Bijective
      (fun ψ : SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
            (SheafOfModules.unit (Thickening.ringRestrictionSheaf B.obj)) ⟶
          (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj Z ↦
        SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
          (isTerminalTop (α := B.obj.thickening.target.scheme.Opens))
          ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj Z) ψ) :=
    (SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1} _ _).bijective
  have hleft : Function.Bijective
      (fun φ : CrystallineThickening.uliftUnitOver B ⟶ Z ↦
        SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
          (isTerminal_restrictOverFunctorObjTop B) Z φ) :=
    (SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
      (isTerminal_restrictOverFunctorObjTop B) Z).bijective
  rw [← hcomp] at hleft
  exact (hright.of_comp_iff' _).1 hleft

/-- **Two morphisms out of a crystalline coproduct with the same restriction to the ambient scheme
of `B` are equal.** -/
theorem eq_of_moduleRestrictionSheafOver_map_eq_crystallineCoproduct {I : Type (u + 1)}
    {Z : SheafOfModules.{u + 1} ((structureSheaf S).over B)}
    {φ ψ : CrystallineThickening.crystallineCoproduct B I ⟶ Z}
    (h : (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ =
      (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map ψ) :
    φ = ψ := by
  have key : ∀ i : I, (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map
        (CrystallineThickening.crystallineCoproductι B I i ≫ φ) =
      (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map
        (CrystallineThickening.crystallineCoproductι B I i ≫ ψ) := by
    intro i
    rw [Functor.map_comp, Functor.map_comp, h]
  refine Cofan.IsColimit.hom_ext
    (CrystallineThickening.isColimitCrystallineCoproductCofan B I) _ _ fun i ↦ ?_
  simp only [Limits.cofan_mk_inj]
  exact (bijective_moduleRestrictionSheafOver_map_uliftUnit B Z).injective (key i)

/-- **Every morphism out of the restriction to the ambient scheme of `B` of a crystalline
coproduct is the restriction of a morphism out of that coproduct.** -/
theorem exists_moduleRestrictionSheafOver_map_eq_crystallineCoproduct (I : Type (u + 1))
    (Z : SheafOfModules.{u + 1} ((structureSheaf S).over B))
    (ψ : (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj
        (CrystallineThickening.crystallineCoproduct B I) ⟶
      (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj Z) :
    ∃ φ : CrystallineThickening.crystallineCoproduct B I ⟶ Z,
      (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ = ψ := by
  choose φ hφ using fun i : I ↦
    (bijective_moduleRestrictionSheafOver_map_uliftUnit B Z).surjective
      ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map
        (CrystallineThickening.crystallineCoproductι B I i) ≫ ψ)
  have hfac : ∀ i : I, CrystallineThickening.crystallineCoproductι B I i ≫
      Cofan.IsColimit.desc (CrystallineThickening.isColimitCrystallineCoproductCofan B I) φ =
        φ i := by
    intro i
    have hi := Cofan.IsColimit.fac
      (CrystallineThickening.isColimitCrystallineCoproductCofan B I) φ i
    simpa only [Limits.cofan_mk_inj] using hi
  have key : ∀ i : I, (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map
          (CrystallineThickening.crystallineCoproductι B I i) ≫
        (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map
          (Cofan.IsColimit.desc
            (CrystallineThickening.isColimitCrystallineCoproductCofan B I) φ) =
      (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map
        (CrystallineThickening.crystallineCoproductι B I i) ≫ ψ := by
    intro i
    rw [← Functor.map_comp, hfac i]
    exact hφ i
  exact ⟨Cofan.IsColimit.desc (CrystallineThickening.isColimitCrystallineCoproductCofan B I) φ,
    Cofan.IsColimit.hom_ext
      (isColimitRestrictOverCrystallineCoproductCofan B I (𝟙 B)) _ _ key⟩

/-- **Restriction to the ambient scheme of `B` is bijective on morphisms out of a crystalline
coproduct.** -/
theorem bijective_moduleRestrictionSheafOver_map_crystallineCoproduct (I : Type (u + 1))
    (Z : SheafOfModules.{u + 1} ((structureSheaf S).over B)) :
    Function.Bijective
      (fun φ : CrystallineThickening.crystallineCoproduct B I ⟶ Z ↦
        (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ) :=
  ⟨fun _ _ h ↦ eq_of_moduleRestrictionSheafOver_map_eq_crystallineCoproduct B h,
    fun ψ ↦ exists_moduleRestrictionSheafOver_map_eq_crystallineCoproduct B I Z ψ⟩

end CohomologyRestriction

/-- **The presentation of the affine ambient scheme of `B`, placed on the localised small
crystalline site `Cris(X/S)/B`.**  For a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules on
`Cris(X/S)` and an object whose ambient scheme is affine there are two morphisms between the
crystalline coproducts and the universe lift of the module, with index types the universe lifts of
types in `Type u`, whose composite vanishes and whose restriction to that ambient scheme is a
cokernel. -/
theorem exists_crystallineCoproduct_cokernelCofork_restrictOver
    {M : SheafOfModules.{u} (structureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (B : CrystallineThickening S) [IsAffine B.obj.thickening.target.scheme] :
    ∃ (I₀ K₀ : Type u)
      (a : CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} K₀) ⟶
        CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} I₀))
      (b : CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} I₀) ⟶
        SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B))
      (hab : a ≫ b = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((CohomologyRestriction.moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map b)
        (CohomologyRestriction.moduleRestrictionSheafOver_map_comp_eq_zero B (𝟙 B) hab))) := by
  obtain ⟨I₀, K₀, P₀, Q₀, ι₀, κ₀, ⟨hP₀⟩, ⟨hQ₀⟩, α₀, β₀, hαβ₀, ⟨hβ₀⟩⟩ :=
    (SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation
      (CohomologyRestriction.moduleRestrictionSheaf M B)).2
      (hasGlobalPresentation_moduleRestrictionSheaf_of_isAffine hlqc B)
  have := CohomologyRestriction.preservesColimitsOfSize_ambientUliftFunctor B
  have := CohomologyRestriction.preservesFiniteColimits_ambientUliftFunctor B
  have eIso : ∀ (J : Type u) (P : SheafOfModules.{u} (Thickening.ringRestrictionSheaf B.obj))
      (ι : J → (SheafOfModules.unit (Thickening.ringRestrictionSheaf B.obj) ⟶ P))
      (_ : IsColimit (Cofan.mk P ι)),
      (CohomologyRestriction.moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj
        (CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} J)) ≅
      (CohomologyRestriction.ambientUliftFunctor B).obj P := fun J P ι hP ↦
    IsColimit.coconePointUniqueUpToIso
      (CohomologyRestriction.isColimitRestrictOverCrystallineCoproductCofan B
        (ULift.{u + 1} J) (𝟙 B))
      (isColimit_cofan_ulift _
        (isColimitCofanMkObjOfIsColimit (CohomologyRestriction.ambientUliftFunctor B) _ ι hP))
  let eP := eIso I₀ P₀ ι₀ hP₀
  let eQ := eIso K₀ Q₀ κ₀ hQ₀
  have eN : (CohomologyRestriction.ambientUliftFunctor B).obj
        (CohomologyRestriction.moduleRestrictionSheaf M B) ≅
      (CohomologyRestriction.moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B)) :=
    (CohomologyRestriction.ambientUliftFunctor B).mapIso
      (CohomologyRestriction.moduleRestrictionSheafOverIso M (𝟙 B)).symm
  have hTαβ : (CohomologyRestriction.ambientUliftFunctor B).map α₀ ≫
      (CohomologyRestriction.ambientUliftFunctor B).map β₀ = 0 := by
    rw [← Functor.map_comp, hαβ₀]
    exact (CohomologyRestriction.ambientUliftFunctor B).map_zero _ _
  have hTβ : IsColimit (CokernelCofork.ofπ
      ((CohomologyRestriction.ambientUliftFunctor B).map β₀) hTαβ) :=
    isColimitCoforkMapOfIsColimit' (CohomologyRestriction.ambientUliftFunctor B) hαβ₀ hβ₀
  have ha' : (eQ.hom ≫ (CohomologyRestriction.ambientUliftFunctor B).map α₀ ≫ eP.inv) ≫ eP.hom =
      eQ.hom ≫ (CohomologyRestriction.ambientUliftFunctor B).map α₀ := by
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hab' : (eQ.hom ≫ (CohomologyRestriction.ambientUliftFunctor B).map α₀ ≫ eP.inv) ≫
      eP.hom ≫ (CohomologyRestriction.ambientUliftFunctor B).map β₀ = 0 := by
    rw [← Category.assoc, ha', Category.assoc, hTαβ, comp_zero]
  have hstep := isColimitCokernelCoforkOfIsoDomain hTαβ hTβ eQ eP ha' hab'
  have hab'' : (eQ.hom ≫ (CohomologyRestriction.ambientUliftFunctor B).map α₀ ≫ eP.inv) ≫
      (eP.hom ≫ (CohomologyRestriction.ambientUliftFunctor B).map β₀) ≫ eN.hom = 0 := by
    rw [← Category.assoc
      (eQ.hom ≫ (CohomologyRestriction.ambientUliftFunctor B).map α₀ ≫ eP.inv)
      (eP.hom ≫ (CohomologyRestriction.ambientUliftFunctor B).map β₀) eN.hom, hab', zero_comp]
  have hstep' : IsColimit (CokernelCofork.ofπ
      ((eP.hom ≫ (CohomologyRestriction.ambientUliftFunctor B).map β₀) ≫ eN.hom) hab'') :=
    hstep.ofIsoColimit (Cofork.ext eN (by simp))
  obtain ⟨a, ha⟩ :=
    CohomologyRestriction.exists_moduleRestrictionSheafOver_map_eq_crystallineCoproduct B
      (ULift.{u + 1} K₀)
      (CrystallineThickening.crystallineCoproduct B (ULift.{u + 1} I₀))
      (eQ.hom ≫ (CohomologyRestriction.ambientUliftFunctor B).map α₀ ≫ eP.inv)
  obtain ⟨b, hb⟩ :=
    CohomologyRestriction.exists_moduleRestrictionSheafOver_map_eq_crystallineCoproduct B
      (ULift.{u + 1} I₀)
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B))
      ((eP.hom ≫ (CohomologyRestriction.ambientUliftFunctor B).map β₀) ≫ eN.hom)
  have hab : a ≫ b = 0 := by
    refine CohomologyRestriction.eq_of_moduleRestrictionSheafOver_map_eq_crystallineCoproduct
      B ?_
    rw [Functor.map_comp, ha, hb, hab'', Functor.map_zero]
  exact ⟨I₀, K₀, a, b, hab, ⟨isColimitCokernelCoforkOfEq ha.symm hb.symm hstep'⟩⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
