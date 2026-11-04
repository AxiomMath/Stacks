module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionCoproducts
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionLift

/-!
# Coproducts of copies of the structure sheaf on a localised small crystalline site

This is the small-site counterpart of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionCoproducts`.
[Stacks, Tag 07IT] is stated for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)` alike, and a sheaf of
modules on `Cris(X/S)` is in general not the restriction of one on `CRIS(X/S)`, so the coproducts
and the identification of their ambient restrictions are repeated here.  The site-generic
cokernel transport
`CategoryTheory.Limits.isColimitCokernelCoforkOfIsoDomain` is imported and reused.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.uliftUnitOver` — the
  universe lift of the structure sheaf of the localised small crystalline site, at the module
  universe `u + 1` at which a global presentation on that site is read.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.crystallineCoproduct` —
  the coproduct of `I` copies of that lift, and
  `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.crystallineCoproductι`
  its inclusions.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.hasColimitsOfShape_discrete_sheafOfModules_over`
  — sheaves of modules on a localised small crystalline site have coproducts indexed by any type
  of the universe `u + 1`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.isColimitCrystallineCoproductCofan`
  — the cofan of the inclusions is a colimit.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.isColimitPushforwardCrystallineCoproductCofan`
  — **the ambient restriction of the crystalline coproduct is a coproduct of copies of the
  universe lift of the structure sheaf of the Zariski site of the ambient scheme**, over the same
  index type.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.pushforwardCrystallineCoproductIso`
  — **the transport**, with
  `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.pushforwardCrystallineCoproductIso_hom`
  for the compatibility with the two families of inclusions.
* `Crystalline.GlobalCrystallineSituation.SmallSite`
  `.exists_cokernelCofork_pushforward_crystallineCoproduct`
  — **the presentation carried onto the crystalline coproducts** on the small site.

## Implementation notes

The proofs are the big site's, with the structure sheaf of `Cris(X/S)` in place of that of
`CRIS(X/S)` and with the sheaf of rings of the Zariski site of the ambient scheme taken, as
throughout the small-site files, to be the big site's
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf` at the underlying
object.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace SmallSite

namespace CrystallineThickening

variable (B : CrystallineThickening S)

/-- Sheafification of `AddCommGrpCat.{u + 1}`-valued presheaves on a localised small crystalline
site exists.  The objects of that site lie one universe above the sections, so this is not
Mathlib's size-matched instance; it is
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat`, which holds in every universe of
sections containing the site. -/
theorem hasSheafify_over_addCommGrpCat_succ :
    HasSheafify ((smallTopology S).over B) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- On a localised small crystalline site the sheafification equivalences for
`AddCommGrpCat.{u + 1}`-valued presheaves are the local bijections. -/
theorem wEqualsLocallyBijective_over_addCommGrpCat_succ :
    ((smallTopology S).over B).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _

/-- **Sheaves of `𝒪_{X/S}`-modules on a localised small crystalline site have coproducts indexed
by any type of the universe `u + 1`**, the universe in which a global presentation on that site is
indexed. -/
theorem hasColimitsOfShape_discrete_sheafOfModules_over (I : Type (u + 1)) :
    HasColimitsOfShape (Discrete I) (SheafOfModules.{u + 1} ((structureSheaf S).over B)) :=
  have := hasSheafify_over_addCommGrpCat_succ B
  have := wEqualsLocallyBijective_over_addCommGrpCat_succ B
  inferInstance

attribute [local instance] hasColimitsOfShape_discrete_sheafOfModules_over

/-- The universe lift of the structure sheaf of a localised small crystalline site, read at the
module universe `u + 1` at which a global presentation on that site is read. -/
noncomputable abbrev uliftUnitOver : SheafOfModules.{u + 1} ((structureSheaf S).over B) :=
  SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
    (SheafOfModules.unit ((structureSheaf S).over B))

/-- **The coproduct of `I` copies of the universe lift of the structure sheaf of a localised small
crystalline site.** -/
noncomputable def crystallineCoproduct (I : Type (u + 1)) :
    SheafOfModules.{u + 1} ((structureSheaf S).over B) :=
  ∐ fun _ : I => uliftUnitOver B

/-- The inclusion of the `i`-th summand of
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.crystallineCoproduct`. -/
noncomputable def crystallineCoproductι (B : CrystallineThickening S) (I : Type (u + 1)) (i : I) :
    uliftUnitOver B ⟶ crystallineCoproduct B I :=
  Sigma.ι (fun _ : I => uliftUnitOver B) i

/-- **The cofan of the inclusions of
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.crystallineCoproduct` is a
colimit.** -/
noncomputable def isColimitCrystallineCoproductCofan (B : CrystallineThickening S)
    (I : Type (u + 1)) :
    IsColimit (Cofan.mk (crystallineCoproduct B I) (crystallineCoproductι B I)) :=
  coproductIsCoproduct fun _ : I => uliftUnitOver B

/-- **The ambient restriction of the crystalline coproduct is a coproduct of copies of the
universe lift of the structure sheaf of the Zariski site of the ambient scheme**, over the same
index type.  As on the big site this is colimit-preservation of the restriction together with the
identification of the two universe lifts of the structure sheaves, which holds on the nose. -/
noncomputable def isColimitPushforwardCrystallineCoproductCofan (I : Type (u + 1)) (X : Over B) :
    IsColimit (Cofan.mk
        ((SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).obj
          (crystallineCoproduct B I))
        (fun i => (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map
          (crystallineCoproductι B I i)) :
      Cofan fun _ : I => SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
        (SheafOfModules.unit ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤))) := by
  haveI := preservesColimitsOfSize_pushforward_ambientOverStructureHom B X
  exact isColimitCofanMkObjOfIsColimit
    (show SheafOfModules.{u + 1} ((structureSheaf S).over B) ⥤
        SheafOfModules.{u + 1} ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤) from
      SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X))
    _ (crystallineCoproductι B I) (isColimitCrystallineCoproductCofan B I)

/-- **The transport: two coproducts of the universe lift of the structure sheaf of the Zariski
site of the ambient scheme over the same index type are isomorphic.**  One of them is the ambient
restriction of
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening.crystallineCoproduct`; the
other is any coproduct given in advance, in particular the one a global presentation of the
restricted module supplies. -/
noncomputable def pushforwardCrystallineCoproductIso {I : Type (u + 1)} (X : Over B)
    {P : SheafOfModules.{u + 1} ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤)}
    {ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
      (SheafOfModules.unit ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤)) ⟶ P}
    (hP : IsColimit (Cofan.mk P ι)) :
    (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).obj
        (crystallineCoproduct B I) ≅ P :=
  IsColimit.coconePointUniqueUpToIso
    (isColimitPushforwardCrystallineCoproductCofan B I X) hP

/-- The comparison of
`Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
`.pushforwardCrystallineCoproductIso`
matches up the two families of inclusions. -/
theorem pushforwardCrystallineCoproductIso_hom {I : Type (u + 1)} (X : Over B)
    {P : SheafOfModules.{u + 1} ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤)}
    {ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
      (SheafOfModules.unit ((Thickening.ringRestrictionSheaf X.left.obj).over ⊤)) ⟶ P}
    (hP : IsColimit (Cofan.mk P ι)) (i : I) :
    (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map
          (crystallineCoproductι B I i) ≫
        (pushforwardCrystallineCoproductIso B X hP).hom =
      ι i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitPushforwardCrystallineCoproductCofan B I X) hP ⟨i⟩

/-- The ambient restriction, at the identity of `B`, of the coproduct of `I` copies of the
universe lift of the structure sheaf of the localised small crystalline site. -/
noncomputable abbrev pushforwardCrystallineCoproduct (I : Type (u + 1)) :=
  (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj
    (crystallineCoproduct B I)

end CrystallineThickening

/-- **The global presentation of an ambient restriction, carried onto the crystalline
coproducts, on the small site.**  For a locally quasi-coherent crystal in `𝒪_{X/S}`-modules on
`Cris(X/S)` and an object `(U', T', δ')` with affine ambient scheme, the ambient restriction at
the identity of `(U', T', δ')` of the universe lift of the module is presented by the ambient
restrictions of two coproducts of copies of the universe lift of the structure sheaf of
`Cris(X/S)/(U', T', δ')`.  This is the small-site form of
`Crystalline.GlobalCrystallineSituation.exists_cokernelCofork_pushforward_crystallineCoproduct`. -/
theorem exists_cokernelCofork_pushforward_crystallineCoproduct
    {M : SheafOfModules.{u} (structureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) (B : CrystallineThickening S)
    [IsAffine B.obj.thickening.target.scheme] :
    ∃ (I K : Type (u + 1))
      (a : CrystallineThickening.pushforwardCrystallineCoproduct B K ⟶
        CrystallineThickening.pushforwardCrystallineCoproduct B I)
      (b : CrystallineThickening.pushforwardCrystallineCoproduct B I ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u + 1, u}
          ((SheafOfModules.pushforward.{u + 1}
            (CrystallineThickening.ambientOverStructureHom B (Over.mk (𝟙 B)))).obj
            (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B))))
      (hab : a ≫ b = 0), Nonempty (IsColimit (CokernelCofork.ofπ b hab)) := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ :=
    hasGlobalPresentation_pushforward_ambientOverStructureHom hlqc hcrys B (Over.mk (𝟙 B))
  set eP := CrystallineThickening.pushforwardCrystallineCoproductIso B (Over.mk (𝟙 B)) hP
  set eQ := CrystallineThickening.pushforwardCrystallineCoproductIso B (Over.mk (𝟙 B)) hQ
  have ha' : (eQ.hom ≫ a ≫ eP.inv) ≫ eP.hom = eQ.hom ≫ a := by
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hab' : (eQ.hom ≫ a ≫ eP.inv) ≫ eP.hom ≫ b = 0 := by
    rw [← Category.assoc, ha', Category.assoc, hab, comp_zero]
  exact ⟨I, K, eQ.hom ≫ a ≫ eP.inv, eP.hom ≫ b, hab',
    ⟨isColimitCokernelCoforkOfIsoDomain hab hb eQ eP ha' hab'⟩⟩

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
