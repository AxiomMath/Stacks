module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionLift

/-!
# Coproducts of copies of the structure sheaf on a localised crystalline site

Let `B` be an object of the big crystalline site of a global crystalline situation and let
`CRIS(X/S)/B` be the localisation of the site at it.  This file builds, for an arbitrary index
type `I`, the coproduct of `I` copies of the universe lift of the structure sheaf of
`CRIS(X/S)/B`, and identifies its ambient restrictions: the restriction along the ambient
restriction attached to an object `X` of `CRIS(X/S)/B` is again a coproduct of `I` copies of the
universe lift of the structure sheaf of the Zariski site of the ambient scheme of `X`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.uliftUnitOver` — the universe lift of the
  structure sheaf of the localised crystalline site, at the module universe `u + 1`.
* `Crystalline.GlobalCrystallineSituation.Thickening.crystallineCoproduct` — the coproduct of `I`
  copies of that lift, and
  `Crystalline.GlobalCrystallineSituation.Thickening.crystallineCoproductι` its inclusions.

## Main results

* `CategoryTheory.Limits.isColimitCokernelCoforkOfIsoDomain` — a cokernel is carried along
  isomorphisms of the source and of the target of the morphism it is a cokernel of.
* `Crystalline.GlobalCrystallineSituation.Thickening`
  `.hasColimitsOfShape_discrete_sheafOfModules_over`
  — sheaves of modules on a localised crystalline site have coproducts indexed by any type of the
  universe `u + 1`.
* `Crystalline.GlobalCrystallineSituation.Thickening.isColimitCrystallineCoproductCofan` — the
  cofan of the inclusions is a colimit.
* `Crystalline.GlobalCrystallineSituation.Thickening.isColimitPushforwardCrystallineCoproductCofan`
  — the ambient restriction of the crystalline coproduct is a coproduct of copies of the
  universe lift of the structure sheaf of the Zariski site of the ambient scheme, over the same
  index type.
* `Crystalline.GlobalCrystallineSituation.Thickening.pushforwardCrystallineCoproductIso` — the
  ambient restriction of the crystalline coproduct is isomorphic to any other
  coproduct of copies of the universe lift of the structure sheaf of the Zariski site over the
  same index type, and
  `Crystalline.GlobalCrystallineSituation.Thickening.pushforwardCrystallineCoproductIso_hom` says
  the comparison matches the two families of inclusions.
* `Crystalline.GlobalCrystallineSituation.exists_cokernelCofork_pushforward_crystallineCoproduct`
  — for a locally quasi-coherent crystal and an object with affine ambient scheme, the global
  presentation of the ambient restriction of the module over the identity of `B` can be taken to
  have for its two coproducts the ambient restrictions of two crystalline coproducts.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace CategoryTheory.Limits

/-- If `b : P ⟶ N` is a cokernel of `a : Q ⟶ P` and `a' : Q' ⟶ P'` is identified with `a` by
isomorphisms `eQ : Q' ≅ Q` and `eP : P' ≅ P`, then `eP.hom ≫ b` is a cokernel of `a'`. -/
noncomputable def isColimitCokernelCoforkOfIsoDomain {D : Type*} [Category* D]
    [HasZeroMorphisms D] {Q P N Q' P' : D} {a : Q ⟶ P} {b : P ⟶ N} (hab : a ≫ b = 0)
    (hb : IsColimit (CokernelCofork.ofπ b hab)) (eQ : Q' ≅ Q) (eP : P' ≅ P) {a' : Q' ⟶ P'}
    (ha' : a' ≫ eP.hom = eQ.hom ≫ a) (hab' : a' ≫ eP.hom ≫ b = 0) :
    IsColimit (CokernelCofork.ofπ (eP.hom ≫ b) hab') := by
  have key : ∀ {Z : D} (g : P' ⟶ Z), a' ≫ g = 0 → a ≫ eP.inv ≫ g = 0 := by
    intro Z g hg
    refine (cancel_epi eQ.hom).mp ?_
    rw [comp_zero, ← Category.assoc, ← ha', Category.assoc, Iso.hom_inv_id_assoc, hg]
  have hdesc : ∀ {Z : D} (g : P' ⟶ Z) (hg : a' ≫ g = 0),
      b ≫ hb.desc (CokernelCofork.ofπ (eP.inv ≫ g) (key g hg)) = eP.inv ≫ g := fun g hg ↦ by
    simpa using Cofork.IsColimit.π_desc
      (t := CokernelCofork.ofπ (eP.inv ≫ g) (key g hg)) hb
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {_} g hg ↦ hb.desc (CokernelCofork.ofπ (eP.inv ≫ g) (key g hg)))
    (fun {_} g hg ↦ ?_) (fun {_} g hg m hm ↦ ?_)
  · rw [Category.assoc, hdesc g hg, Iso.hom_inv_id_assoc]
  · refine Cofork.IsColimit.hom_ext hb ?_
    simp only [Cofork.π_ofπ]
    rw [hdesc g hg, ← hm, Category.assoc, Iso.inv_hom_id_assoc]

end CategoryTheory.Limits

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

variable (B : Thickening S)

/-- Sheafification of `AddCommGrpCat.{u + 1}`-valued presheaves on a localised crystalline site
exists. -/
theorem hasSheafify_over_addCommGrpCat_succ :
    HasSheafify ((topology S).over B) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- On a localised crystalline site the sheafification equivalences for
`AddCommGrpCat.{u + 1}`-valued presheaves are the local bijections. -/
theorem wEqualsLocallyBijective_over_addCommGrpCat_succ :
    ((topology S).over B).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _

/-- Sheaves of `𝒪_{X/S}`-modules on a localised crystalline site have coproducts indexed by any
type of the universe `u + 1`. -/
theorem hasColimitsOfShape_discrete_sheafOfModules_over (I : Type (u + 1)) :
    HasColimitsOfShape (Discrete I)
      (SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)) :=
  have := hasSheafify_over_addCommGrpCat_succ B
  have := wEqualsLocallyBijective_over_addCommGrpCat_succ B
  inferInstance

attribute [local instance] hasColimitsOfShape_discrete_sheafOfModules_over

/-- The universe lift of the structure sheaf of a localised crystalline site, at the module
universe `u + 1`. -/
noncomputable abbrev uliftUnitOver :
    SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) :=
  SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
    (SheafOfModules.unit ((crystallineStructureSheaf S).over B))

/-- The coproduct of `I` copies of the universe lift of the structure sheaf of a localised
crystalline site. -/
noncomputable def crystallineCoproduct (I : Type (u + 1)) :
    SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) :=
  ∐ fun _ : I => uliftUnitOver B

/-- The inclusion of the `i`-th summand of
`Crystalline.GlobalCrystallineSituation.Thickening.crystallineCoproduct`. -/
noncomputable def crystallineCoproductι (B : Thickening S) (I : Type (u + 1)) (i : I) :
    uliftUnitOver B ⟶ crystallineCoproduct B I :=
  Sigma.ι (fun _ : I => uliftUnitOver B) i

/-- The cofan of the inclusions of
`Crystalline.GlobalCrystallineSituation.Thickening.crystallineCoproduct` is a colimit. -/
noncomputable def isColimitCrystallineCoproductCofan (B : Thickening S) (I : Type (u + 1)) :
    IsColimit (Cofan.mk (crystallineCoproduct B I) (crystallineCoproductι B I)) :=
  coproductIsCoproduct fun _ : I => uliftUnitOver B

/-- The ambient restriction of the crystalline coproduct is a coproduct of copies of the
universe lift of the structure sheaf of the Zariski site of the ambient scheme, over the same
index type. -/
noncomputable def isColimitPushforwardCrystallineCoproductCofan (I : Type (u + 1)) (X : Over B) :
    IsColimit (Cofan.mk
        ((SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).obj
          (crystallineCoproduct B I))
        (fun i => (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map
          (crystallineCoproductι B I i)) :
      Cofan fun _ : I => SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
        (SheafOfModules.unit ((X.left.ringRestrictionSheaf).over ⊤))) := by
  haveI := preservesColimitsOfSize_pushforward_ambientOverStructureHom B X
  exact isColimitCofanMkObjOfIsColimit
    (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
        SheafOfModules.{u + 1} ((X.left.ringRestrictionSheaf).over ⊤) from
      SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X))
    _ (crystallineCoproductι B I) (isColimitCrystallineCoproductCofan B I)

/-- The ambient restriction of
`Crystalline.GlobalCrystallineSituation.Thickening.crystallineCoproduct` is isomorphic to any
coproduct `P` of `I` copies of the universe lift of the structure sheaf of the Zariski site of the
ambient scheme. -/
noncomputable def pushforwardCrystallineCoproductIso {I : Type (u + 1)} (X : Over B)
    {P : SheafOfModules.{u + 1} ((X.left.ringRestrictionSheaf).over ⊤)}
    {ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
      (SheafOfModules.unit ((X.left.ringRestrictionSheaf).over ⊤)) ⟶ P}
    (hP : IsColimit (Cofan.mk P ι)) :
    (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).obj
        (crystallineCoproduct B I) ≅ P :=
  IsColimit.coconePointUniqueUpToIso
    (isColimitPushforwardCrystallineCoproductCofan B I X) hP

/-- The comparison of
`Crystalline.GlobalCrystallineSituation.Thickening.pushforwardCrystallineCoproductIso` matches up
the two families of inclusions. -/
theorem pushforwardCrystallineCoproductIso_hom {I : Type (u + 1)} (X : Over B)
    {P : SheafOfModules.{u + 1} ((X.left.ringRestrictionSheaf).over ⊤)}
    {ι : ∀ _ : I, SheafOfModules.uliftForPresentation.{u, u, u, u, u + 1}
      (SheafOfModules.unit ((X.left.ringRestrictionSheaf).over ⊤)) ⟶ P}
    (hP : IsColimit (Cofan.mk P ι)) (i : I) :
    (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map
          (crystallineCoproductι B I i) ≫
        (pushforwardCrystallineCoproductIso B X hP).hom =
      ι i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitPushforwardCrystallineCoproductCofan B I X) hP ⟨i⟩

/-- The ambient restriction, at the identity of `B`, of the coproduct of `I` copies of the
universe lift of the structure sheaf of the localised crystalline site. -/
noncomputable abbrev pushforwardCrystallineCoproduct (I : Type (u + 1)) :=
  (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj
    (crystallineCoproduct B I)

end Thickening

/-- For a locally quasi-coherent crystal in `𝒪_{X/S}`-modules and an object `(U', T', δ')` with
affine ambient scheme, the ambient restriction at the identity of `(U', T', δ')` of the universe
lift of the module is presented by the ambient restrictions of two coproducts of copies of the
universe lift of the structure sheaf of `CRIS(X/S)/(U', T', δ')`. -/
theorem exists_cokernelCofork_pushforward_crystallineCoproduct
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) (B : Thickening S) [IsAffine B.thickening.target.scheme] :
    ∃ (I K : Type (u + 1))
      (a : Thickening.pushforwardCrystallineCoproduct B K ⟶
        Thickening.pushforwardCrystallineCoproduct B I)
      (b : Thickening.pushforwardCrystallineCoproduct B I ⟶
        SheafOfModules.uliftForPresentation.{u, u, u, u + 1, u}
          ((SheafOfModules.pushforward.{u + 1}
            (Thickening.ambientOverStructureHom B (Over.mk (𝟙 B)))).obj
            (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B))))
      (hab : a ≫ b = 0), Nonempty (IsColimit (CokernelCofork.ofπ b hab)) := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ :=
    hasGlobalPresentation_pushforward_ambientOverStructureHom hlqc hcrys B (Over.mk (𝟙 B))
  set eP := Thickening.pushforwardCrystallineCoproductIso B (Over.mk (𝟙 B)) hP
  set eQ := Thickening.pushforwardCrystallineCoproductIso B (Over.mk (𝟙 B)) hQ
  have ha' : (eQ.hom ≫ a ≫ eP.inv) ≫ eP.hom = eQ.hom ≫ a := by simp
  have hab' : (eQ.hom ≫ a ≫ eP.inv) ≫ eP.hom ≫ b = 0 := by
    rw [← Category.assoc, ha', Category.assoc, hab, comp_zero]
  exact ⟨I, K, eQ.hom ≫ a ≫ eP.inv, eP.hom ≫ b, hab',
    ⟨isColimitCokernelCoforkOfIsoDomain hab hb eQ eP ha' hab'⟩⟩

end Crystalline.GlobalCrystallineSituation

end
