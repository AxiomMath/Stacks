module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientPresentationLift
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.RestrictOverConservative

/-!
# The presentation of an affine ambient scheme lifted to the localised crystalline site

Let `B` be an object of the big crystalline site of a global crystalline situation whose ambient
scheme is affine and let `F` be a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules.  The
restriction `F_{T'}` of `F` to the ambient scheme `T'` of `B` is a quasi-coherent module on an
affine scheme, hence has a global presentation

  `⊕_{K₀} 𝒪_{T'} ⟶ ⊕_{I₀} 𝒪_{T'} ⟶ F_{T'} ⟶ 0`

with index types in `Type u`.  This file carries that presentation onto the localised crystalline
site `CRIS(X/S)/B`: it produces two morphisms

  `a : ∐_{K₀} 𝒪_{X/S} ⟶ ∐_{I₀} 𝒪_{X/S}`  and  `b : ∐_{I₀} 𝒪_{X/S} ⟶ F`

of sheaves of modules there, between the crystalline coproducts of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionCoproducts` and the
universe lift of the module, whose composite vanishes and whose restriction to the ambient scheme
of `B` is the given presentation.

`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientPresentationLift` performs the
same lift along the family of ambient restrictions that goes through the slice of the opens at the
greatest open.  The two differences that matter for the direction (2) ⇒ (1) of
[Stacks, Tag 07IT] are that the restriction used here is the one carrying the `f`-map of
[Stacks, Tag 07IQ] at an arbitrary module universe, and that the index types are kept in the form
`ULift.{u + 1} I₀` of a universe lift of a type in `Type u`, which is what lets the restricted
cofork be recognised as a universe lift of a cofork of sheaves of modules at the module universe
`u`.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening`
  `.isColimitRestrictOverCrystallineCoproductCofan`
  — the restriction of a crystalline coproduct to the ambient scheme of an object over the base is
  a coproduct of copies of the universe lift of the structure sheaf of that ambient scheme.
* `Crystalline.GlobalCrystallineSituation.Thickening`
  `.bijective_moduleRestrictionSheafOver_map_crystallineCoproduct`
  — **restriction to the ambient scheme of `B` is bijective on morphisms out of a crystalline
  coproduct.**
* `Crystalline.GlobalCrystallineSituation.exists_crystallineCoproduct_cokernelCofork_restrictOver`
  — **the presentation of the affine ambient scheme of `B`, placed on `CRIS(X/S)/B`**, with index
  types that are universe lifts of types in `Type u`.

## Implementation notes

The global presentation of `F_{T'}` is taken in the single-universe form
`SheafOfModules.IsPresentedByGlobalSections`, which on the Zariski site of a scheme over
`Scheme.{u}` is equivalent to `SheafOfModules.HasGlobalPresentation` by
`SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation`; that is the form whose
coproducts are indexed by `Type u` and whose summands are the structure sheaf itself rather than a
universe lift of it.  The passage to the module universe `u + 1` is then one application of
`SheafOfModules.uliftForPresentationFunctor`, which preserves the coproducts and the cokernel, and
one reindexing of the two index types by `CategoryTheory.Limits.isColimit_cofan_ulift`.

Lifting the two morphisms to `CRIS(X/S)/B` is bijectivity of restriction on morphisms out of a
crystalline coproduct, which is assembled summand by summand from the case of a single summand;
there it is `SheafOfModules.uliftUnitHomEquiv` read at two terminal objects of the same category,
the terminal object of `CRIS(X/S)/B` and the image of the greatest open of the ambient scheme of
`B`, which is terminal because the structure morphism of the restriction to the greatest open is
an isomorphism.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

variable (B : Thickening S)

/-- Restriction to the ambient scheme of an object over the base carries a vanishing composite to
a vanishing composite, being a functor which preserves zero morphisms. -/
theorem moduleRestrictionSheafOver_map_comp_eq_zero {A : Thickening S} (h : A ⟶ B)
    {Q P N : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)} {a : Q ⟶ P}
    {b : P ⟶ N} (hab : a ≫ b = 0) :
    (moduleRestrictionSheafOverFunctor.{u + 1} h).map a ≫
        (moduleRestrictionSheafOverFunctor.{u + 1} h).map b = 0 := by
  rw [← Functor.map_comp, hab]
  exact (moduleRestrictionSheafOverFunctor.{u + 1} h).map_zero _ _

/-- **The restriction of a crystalline coproduct to the ambient scheme of an object over the base
is a coproduct of copies of the universe lift of the structure sheaf of that ambient scheme**, over
the same index type.  Restriction preserves colimits of size `u + 1` and carries the universe lift
of the structure sheaf of the localised crystalline site to that of the Zariski site on the
nose. -/
noncomputable def isColimitRestrictOverCrystallineCoproductCofan (I : Type (u + 1))
    {A : Thickening S} (h : A ⟶ B) :
    IsColimit (Cofan.mk
        ((moduleRestrictionSheafOverFunctor.{u + 1} h).obj (crystallineCoproduct B I))
        (fun i => (moduleRestrictionSheafOverFunctor.{u + 1} h).map
          (crystallineCoproductι B I i)) :
      Cofan fun _ : I => SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
        (SheafOfModules.unit A.ringRestrictionSheaf)) := by
  have := preservesColimitsOfSize_moduleRestrictionSheafOverFunctor.{u} h
  exact isColimitCofanMkObjOfIsColimit
    (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
        SheafOfModules.{u + 1} A.ringRestrictionSheaf from
      moduleRestrictionSheafOverFunctor.{u + 1} h)
    _ (crystallineCoproductι B I) (isColimitCrystallineCoproductCofan B I)

/-- **The restriction to the ambient scheme of `B` carries the greatest open of that scheme to a
terminal object of the localised crystalline site.**  Its image is the restriction of `B` to the
whole of its ambient scheme, which is isomorphic to `B` itself, and `B` with its identity is
terminal in `CRIS(X/S)/B`. -/
noncomputable def isTerminal_restrictOverFunctorObjTop :
    IsTerminal ((restrictOverFunctor (𝟙 B)).obj (⊤ : B.thickening.target.scheme.Opens)) :=
  IsTerminal.ofIso (Over.mkIdTerminal (X := B))
    (restrictOverFunctorObjTopIso B (Over.mk (𝟙 B))).symm

/-- **The global section attached to the restriction of a morphism out of the universe lift of the
structure sheaf is the global section attached to the morphism itself**, read over the image of the
greatest open of the ambient scheme of `B`.  Restriction along a functor of sites is evaluation at
the image of the object, the comparison of structure sheaves is the identity, and the generating
section matches, so the two readings agree on the nose. -/
theorem uliftUnitHomEquiv_moduleRestrictionSheafOver_map
    (Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B))
    (φ : uliftUnitOver B ⟶ Z) :
    SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
        (isTerminalTop (α := B.thickening.target.scheme.Opens))
        ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj Z)
        ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ) =
      SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
        (isTerminal_restrictOverFunctorObjTop B) Z φ :=
  rfl

/-- **Restriction to the ambient scheme of `B` is bijective on morphisms out of the universe lift
of the structure sheaf of the localised crystalline site.**  A morphism out of that lift is its
value at the generating section over a terminal object, and the restriction hits a terminal
object; so the two readings are two bijections with the same composite. -/
theorem bijective_moduleRestrictionSheafOver_map_uliftUnit
    (Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)) :
    Function.Bijective
      (fun φ : uliftUnitOver B ⟶ Z ↦
        (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ) := by
  have hcomp : (fun φ : uliftUnitOver B ⟶ Z ↦
      SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
        (isTerminalTop (α := B.thickening.target.scheme.Opens))
        ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj Z)
        ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ)) =
      fun φ ↦ SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
        (isTerminal_restrictOverFunctorObjTop B) Z φ :=
    funext fun φ ↦ uliftUnitHomEquiv_moduleRestrictionSheafOver_map B Z φ
  have hright : Function.Bijective
      (fun ψ : SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
            (SheafOfModules.unit B.ringRestrictionSheaf) ⟶
          (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj Z ↦
        SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1}
          (isTerminalTop (α := B.thickening.target.scheme.Opens))
          ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj Z) ψ) :=
    (SheafOfModules.uliftUnitHomEquiv.{u, u, u, u + 1} _ _).bijective
  have hleft : Function.Bijective
      (fun φ : uliftUnitOver B ⟶ Z ↦
        SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
          (isTerminal_restrictOverFunctorObjTop B) Z φ) :=
    (SheafOfModules.uliftUnitHomEquiv.{u + 1, u, u, u + 1}
      (isTerminal_restrictOverFunctorObjTop B) Z).bijective
  rw [← hcomp] at hleft
  exact (hright.of_comp_iff' _).1 hleft

/-- **Two morphisms out of a crystalline coproduct with the same restriction to the ambient scheme
of `B` are equal.**  A morphism out of the coproduct is determined by its composites with the
inclusions of the summands, and on each summand restriction is injective. -/
theorem eq_of_moduleRestrictionSheafOver_map_eq_crystallineCoproduct {I : Type (u + 1)}
    {Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)}
    {φ ψ : crystallineCoproduct B I ⟶ Z}
    (h : (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ =
      (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map ψ) :
    φ = ψ := by
  have key : ∀ i : I, (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map
        (crystallineCoproductι B I i ≫ φ) =
      (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map
        (crystallineCoproductι B I i ≫ ψ) := by
    intro i
    rw [Functor.map_comp, Functor.map_comp, h]
  refine Cofan.IsColimit.hom_ext (isColimitCrystallineCoproductCofan B I) _ _ fun i ↦ ?_
  simp only [Limits.cofan_mk_inj]
  exact (bijective_moduleRestrictionSheafOver_map_uliftUnit B Z).injective (key i)

/-- **Every morphism out of the restriction to the ambient scheme of `B` of a crystalline
coproduct is the restriction of a morphism out of that coproduct.**  Each composite with the
restriction of an inclusion of a summand is the restriction of a morphism out of the summand, and
those assemble through the universal property of the coproduct. -/
theorem exists_moduleRestrictionSheafOver_map_eq_crystallineCoproduct (I : Type (u + 1))
    (Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B))
    (ψ : (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj (crystallineCoproduct B I) ⟶
      (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj Z) :
    ∃ φ : crystallineCoproduct B I ⟶ Z,
      (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ = ψ := by
  choose φ hφ using fun i : I ↦
    (bijective_moduleRestrictionSheafOver_map_uliftUnit B Z).surjective
      ((moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map (crystallineCoproductι B I i) ≫ ψ)
  have hfac : ∀ i : I, crystallineCoproductι B I i ≫
      Cofan.IsColimit.desc (isColimitCrystallineCoproductCofan B I) φ = φ i := by
    intro i
    have hi := Cofan.IsColimit.fac (isColimitCrystallineCoproductCofan B I) φ i
    simpa only [Limits.cofan_mk_inj] using hi
  have key : ∀ i : I, (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map
          (crystallineCoproductι B I i) ≫
        (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map
          (Cofan.IsColimit.desc (isColimitCrystallineCoproductCofan B I) φ) =
      (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map (crystallineCoproductι B I i) ≫ ψ := by
    intro i
    rw [← Functor.map_comp, hfac i]
    exact hφ i
  exact ⟨Cofan.IsColimit.desc (isColimitCrystallineCoproductCofan B I) φ,
    Cofan.IsColimit.hom_ext
      (isColimitRestrictOverCrystallineCoproductCofan B I (𝟙 B)) _ _ key⟩

/-- **Restriction to the ambient scheme of `B` is bijective on morphisms out of a crystalline
coproduct.**  This is the statement with which the two presenting morphisms of a global
presentation chosen on the affine ambient scheme of `B` are lifted to the localised crystalline
site. -/
theorem bijective_moduleRestrictionSheafOver_map_crystallineCoproduct (I : Type (u + 1))
    (Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)) :
    Function.Bijective
      (fun φ : crystallineCoproduct B I ⟶ Z ↦
        (moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map φ) :=
  ⟨fun _ _ h ↦ eq_of_moduleRestrictionSheafOver_map_eq_crystallineCoproduct B h,
    fun ψ ↦ exists_moduleRestrictionSheafOver_map_eq_crystallineCoproduct B I Z ψ⟩

/-- The universe lift of the sections of a sheaf of modules on the Zariski site of the ambient
scheme of an object, at the module universe `u + 1` at which a global presentation on a localised
crystalline site is read.  It is reducible so that the restrictions to the ambient schemes, which
carry a universe lift on the crystalline site to this one on the nose, are recognised as its
values. -/
noncomputable abbrev ambientUliftFunctor (A : Thickening S) :
    SheafOfModules.{u} A.ringRestrictionSheaf ⥤ SheafOfModules.{u + 1} A.ringRestrictionSheaf :=
  SheafOfModules.uliftForPresentationFunctor.{u, u, u, u, u + 1}

/-- Sheafification of `AddCommGrpCat`-valued presheaves on the Zariski site of the ambient scheme
of an object exists at the module universes `u` and `u + 1`, and the sheafification equivalences
are the local bijections; so the universe lift of the sections there preserves colimits of size
`u` and finite colimits. -/
theorem preservesColimitsOfSize_ambientUliftFunctor (A : Thickening S) :
    PreservesColimitsOfSize.{u, u} (ambientUliftFunctor A) := by
  have _ : HasSheafify (Opens.grothendieckTopology ↥A.thickening.target.scheme)
      AddCommGrpCat.{u} := GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      (Opens.grothendieckTopology ↥A.thickening.target.scheme) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} _
  have _ : HasSheafify (Opens.grothendieckTopology ↥A.thickening.target.scheme)
      AddCommGrpCat.{u + 1} := GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      (Opens.grothendieckTopology ↥A.thickening.target.scheme) AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _
  exact SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor.{u, u, u, u, u + 1}

/-- The universe lift of the sections on the Zariski site of the ambient scheme of an object
preserves finite colimits; see
`Crystalline.GlobalCrystallineSituation.Thickening.preservesColimitsOfSize_ambientUliftFunctor`. -/
theorem preservesFiniteColimits_ambientUliftFunctor (A : Thickening S) :
    PreservesFiniteColimits (ambientUliftFunctor A) := by
  have := preservesColimitsOfSize_ambientUliftFunctor A
  exact PreservesColimitsOfSize.preservesFiniteColimits _

end Thickening

/-- **The presentation of the affine ambient scheme of `B`, placed on the localised crystalline
site `CRIS(X/S)/B`.**  For a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules and an object
`(U', T', δ')` whose ambient scheme is affine there are two morphisms

  `a : ∐_{K₀} 𝒪_{X/S} ⟶ ∐_{I₀} 𝒪_{X/S}`  and  `b : ∐_{I₀} 𝒪_{X/S} ⟶ F`

of sheaves of modules on `CRIS(X/S)/(U', T', δ')`, with index types the universe lifts of types in
`Type u`, whose composite vanishes and whose restriction to the ambient scheme `T'` is a
cokernel.

The presentation of `F_{T'}` itself is [Stacks, Tag 03DX] on the affine `T'`, in the shape
`Crystalline.GlobalCrystallineSituation.hasGlobalPresentation_moduleRestrictionSheaf_of_isAffine`
gives it; the universe lift of the sections carries it to the module universe `u + 1`, the
crystalline coproducts replace its two coproducts, and restriction to `T'` is bijective on
morphisms out of those. -/
theorem exists_crystallineCoproduct_cokernelCofork_restrictOver
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (B : Thickening S) [IsAffine B.thickening.target.scheme] :
    ∃ (I₀ K₀ : Type u)
      (a : Thickening.crystallineCoproduct B (ULift.{u + 1} K₀) ⟶
        Thickening.crystallineCoproduct B (ULift.{u + 1} I₀))
      (b : Thickening.crystallineCoproduct B (ULift.{u + 1} I₀) ⟶
        SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B))
      (hab : a ≫ b = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((Thickening.moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).map b)
        (Thickening.moduleRestrictionSheafOver_map_comp_eq_zero B (𝟙 B) hab))) := by
  obtain ⟨I₀, K₀, P₀, Q₀, ι₀, κ₀, ⟨hP₀⟩, ⟨hQ₀⟩, α₀, β₀, hαβ₀, ⟨hβ₀⟩⟩ :=
    (SheafOfModules.isPresentedByGlobalSections_iff_hasGlobalPresentation
      (Thickening.moduleRestrictionSheaf M B)).2
      (hasGlobalPresentation_moduleRestrictionSheaf_of_isAffine hlqc B)
  have := Thickening.preservesColimitsOfSize_ambientUliftFunctor B
  have := Thickening.preservesFiniteColimits_ambientUliftFunctor B
  have lift : ∀ (J : Type u) (P : SheafOfModules.{u} B.ringRestrictionSheaf)
      (ι : ∀ j : J, SheafOfModules.unit B.ringRestrictionSheaf ⟶ P),
      IsColimit (Cofan.mk P ι) →
      Nonempty ((Thickening.moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj
        (Thickening.crystallineCoproduct B (ULift.{u + 1} J)) ≅
        (Thickening.ambientUliftFunctor B).obj P) := fun J P ι hP ↦
    ⟨IsColimit.coconePointUniqueUpToIso
      (Thickening.isColimitRestrictOverCrystallineCoproductCofan B (ULift.{u + 1} J) (𝟙 B))
      (isColimit_cofan_ulift _
        (isColimitCofanMkObjOfIsColimit (Thickening.ambientUliftFunctor B) _ ι hP) :
        IsColimit (Cofan.mk ((Thickening.ambientUliftFunctor B).obj P)
          (fun j : ULift.{u + 1} J ↦ (Thickening.ambientUliftFunctor B).map (ι j.down))))⟩
  obtain ⟨eP⟩ := lift I₀ P₀ ι₀ hP₀
  obtain ⟨eQ⟩ := lift K₀ Q₀ κ₀ hQ₀
  have eN : (Thickening.ambientUliftFunctor B).obj (Thickening.moduleRestrictionSheaf M B) ≅
      (Thickening.moduleRestrictionSheafOverFunctor.{u + 1} (𝟙 B)).obj
        (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B)) :=
    (Thickening.ambientUliftFunctor B).mapIso
      (Thickening.moduleRestrictionSheafOverIso M (𝟙 B)).symm
  have hTαβ : (Thickening.ambientUliftFunctor B).map α₀ ≫
      (Thickening.ambientUliftFunctor B).map β₀ = 0 := by
    rw [← Functor.map_comp, hαβ₀]
    exact (Thickening.ambientUliftFunctor B).map_zero _ _
  have hTβ : IsColimit (CokernelCofork.ofπ ((Thickening.ambientUliftFunctor B).map β₀) hTαβ) :=
    isColimitCoforkMapOfIsColimit' (Thickening.ambientUliftFunctor B) hαβ₀ hβ₀
  have ha' : (eQ.hom ≫ (Thickening.ambientUliftFunctor B).map α₀ ≫ eP.inv) ≫ eP.hom =
      eQ.hom ≫ (Thickening.ambientUliftFunctor B).map α₀ := by
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hab' : (eQ.hom ≫ (Thickening.ambientUliftFunctor B).map α₀ ≫ eP.inv) ≫
      eP.hom ≫ (Thickening.ambientUliftFunctor B).map β₀ = 0 := by
    rw [← Category.assoc, ha', Category.assoc, hTαβ, comp_zero]
  have hstep := isColimitCokernelCoforkOfIsoDomain hTαβ hTβ eQ eP ha' hab'
  have hab'' : (eQ.hom ≫ (Thickening.ambientUliftFunctor B).map α₀ ≫ eP.inv) ≫
      (eP.hom ≫ (Thickening.ambientUliftFunctor B).map β₀) ≫ eN.hom = 0 := by
    rw [← Category.assoc (eQ.hom ≫ (Thickening.ambientUliftFunctor B).map α₀ ≫ eP.inv)
      (eP.hom ≫ (Thickening.ambientUliftFunctor B).map β₀) eN.hom, hab', zero_comp]
  have hstep' : IsColimit (CokernelCofork.ofπ
      ((eP.hom ≫ (Thickening.ambientUliftFunctor B).map β₀) ≫ eN.hom) hab'') :=
    hstep.ofIsoColimit (Cofork.ext eN (by simp))
  obtain ⟨a, ha⟩ :=
    Thickening.exists_moduleRestrictionSheafOver_map_eq_crystallineCoproduct B
      (ULift.{u + 1} K₀) (Thickening.crystallineCoproduct B (ULift.{u + 1} I₀))
      (eQ.hom ≫ (Thickening.ambientUliftFunctor B).map α₀ ≫ eP.inv)
  obtain ⟨b, hb⟩ :=
    Thickening.exists_moduleRestrictionSheafOver_map_eq_crystallineCoproduct B
      (ULift.{u + 1} I₀)
      (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B))
      ((eP.hom ≫ (Thickening.ambientUliftFunctor B).map β₀) ≫ eN.hom)
  have hab : a ≫ b = 0 := by
    refine Thickening.eq_of_moduleRestrictionSheafOver_map_eq_crystallineCoproduct B ?_
    rw [Functor.map_comp, ha, hb, hab'', Functor.map_zero]
  exact ⟨I₀, K₀, a, b, hab, ⟨isColimitCokernelCoforkOfEq ha.symm hb.symm hstep'⟩⟩

end Crystalline.GlobalCrystallineSituation

end
