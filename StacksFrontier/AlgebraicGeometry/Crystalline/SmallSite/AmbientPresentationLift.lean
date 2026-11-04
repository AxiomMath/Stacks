module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientPresentationLift
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AmbientRestrictionCoproducts

/-!
# Lifting the presenting morphisms of a presentation to a localised small crystalline site

For an object `B` of the small crystalline site `Cris(X/S)`, restriction along the ambient
restriction at the identity of `B` is bijective on morphisms out of a crystalline coproduct.  When
the ambient scheme of `B` is affine, the two presenting morphisms of a presentation of a locally
quasi-coherent crystal by crystalline coproducts therefore lift to the localised site
`Cris(X/S)/B`.

## Main results

* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.bijective_pushforward_map_crystallineCoproduct`
  — **restriction along the ambient restriction at the identity of `B` is bijective on morphisms
  out of a crystalline coproduct**, with
  `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.eq_of_pushforward_map_eq_crystallineCoproduct`
  and
  `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.exists_pushforward_map_eq_crystallineCoproduct`
  for its two halves.
* `Crystalline.GlobalCrystallineSituation.SmallSite.CrystallineThickening`
  `.exists_hom_pushforward_isColimitCokernelCofork`
  — **the two presenting morphisms of a presentation of the ambient restriction at the identity of
  `B` by the ambient restrictions of two crystalline coproducts lift to the localised small
  crystalline site**, and their composite vanishes there.
* `Crystalline.GlobalCrystallineSituation.SmallSite`
  `.exists_crystallineCoproduct_cokernelCofork_pushforward`
  — **the presenting morphisms of the presentation of a locally quasi-coherent crystal placed on
  the localised small crystalline site**.

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

/-- Restriction along an ambient restriction carries a vanishing composite to a vanishing
composite. -/
theorem pushforward_ambientOverStructureHom_map_comp_eq_zero (X : Over B)
    {Q P N : SheafOfModules.{u + 1} ((structureSheaf S).over B)} {a : Q ⟶ P}
    {b : P ⟶ N} (hab : a ≫ b = 0) :
    (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map a ≫
        (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map b = 0 := by
  rw [← Functor.map_comp, hab, Functor.map_zero]

/-- Two morphisms out of the universe lift of the structure sheaf of a localised small crystalline
site with the same ambient restriction at the identity of `B` are equal. -/
theorem eq_of_pushforward_map_eq_uliftUnitOver
    {Z : SheafOfModules.{u + 1} ((structureSheaf S).over B)} {φ ψ : uliftUnitOver B ⟶ Z}
    (h : (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ =
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map ψ) :
    φ = ψ :=
  (bijective_pushforward_map_uliftUnit B Z).injective h

/-- Every morphism out of the ambient restriction at the identity of `B` of the universe lift of
the structure sheaf is the ambient restriction of a morphism out of that lift. -/
theorem exists_pushforward_map_eq_uliftUnitOver
    (Z : SheafOfModules.{u + 1} ((structureSheaf S).over B))
    (χ : (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj (uliftUnitOver B) ⟶
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj Z) :
    ∃ φ : uliftUnitOver B ⟶ Z,
      (SheafOfModules.pushforward.{u + 1}
        (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ = χ :=
  (bijective_pushforward_map_uliftUnit B Z).surjective χ

/-- **Two morphisms out of a crystalline coproduct with the same ambient restriction at the
identity of `B` are equal.** -/
theorem eq_of_pushforward_map_eq_crystallineCoproduct {I : Type (u + 1)}
    {Z : SheafOfModules.{u + 1} ((structureSheaf S).over B)}
    {φ ψ : crystallineCoproduct B I ⟶ Z}
    (h : (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ =
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map ψ) :
    φ = ψ :=
  Cofan.IsColimit.hom_ext (isColimitCrystallineCoproductCofan B I) _ _ fun _ ↦
    eq_of_pushforward_map_eq_uliftUnitOver B (by rw [Functor.map_comp, Functor.map_comp, h])

/-- **Every morphism out of the ambient restriction at the identity of `B` of a crystalline
coproduct is the ambient restriction of a morphism out of that coproduct.** -/
theorem exists_pushforward_map_eq_crystallineCoproduct (I : Type (u + 1))
    (Z : SheafOfModules.{u + 1} ((structureSheaf S).over B))
    (ψ : (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj (crystallineCoproduct B I) ⟶
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj Z) :
    ∃ φ : crystallineCoproduct B I ⟶ Z,
      (SheafOfModules.pushforward.{u + 1}
        (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ = ψ := by
  choose φ hφ using fun i : I ↦ exists_pushforward_map_eq_uliftUnitOver B Z
    ((SheafOfModules.pushforward.{u + 1}
      (ambientOverStructureHom B (Over.mk (𝟙 B)))).map (crystallineCoproductι B I i) ≫ ψ)
  have hfac : ∀ i : I, crystallineCoproductι B I i ≫
      Cofan.IsColimit.desc (isColimitCrystallineCoproductCofan B I) φ = φ i := fun i ↦ by
    simpa only [Limits.cofan_mk_inj] using
      Cofan.IsColimit.fac (isColimitCrystallineCoproductCofan B I) φ i
  exact ⟨Cofan.IsColimit.desc (isColimitCrystallineCoproductCofan B I) φ,
    Cofan.IsColimit.hom_ext
      (isColimitPushforwardCrystallineCoproductCofan B I (Over.mk (𝟙 B))) _ _ fun i ↦
        (Functor.map_comp _ _ _).symm.trans ((congrArg _ (hfac i)).trans (hφ i))⟩

/-- **Restriction along the ambient restriction at the identity of `B` is bijective on morphisms
out of a crystalline coproduct.** -/
theorem bijective_pushforward_map_crystallineCoproduct (I : Type (u + 1))
    (Z : SheafOfModules.{u + 1} ((structureSheaf S).over B)) :
    Function.Bijective
      (fun φ : crystallineCoproduct B I ⟶ Z ↦
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ) :=
  ⟨fun _ _ h ↦ eq_of_pushforward_map_eq_crystallineCoproduct B h,
    fun ψ ↦ exists_pushforward_map_eq_crystallineCoproduct B I Z ψ⟩

/-- **The two presenting morphisms of a presentation of the ambient restriction at the identity of
`B` by the ambient restrictions of two crystalline coproducts lift to the localised small
crystalline site.**  Their composite vanishes, their ambient restrictions are `a₀` and `b₀`, and
the ambient restriction of the lifted cofork is again a cokernel. -/
theorem exists_hom_pushforward_isColimitCokernelCofork {I K : Type (u + 1)}
    {Z : SheafOfModules.{u + 1} ((structureSheaf S).over B)}
    {a₀ : (SheafOfModules.pushforward.{u + 1}
        (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj (crystallineCoproduct B K) ⟶
      (SheafOfModules.pushforward.{u + 1}
        (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj (crystallineCoproduct B I)}
    {b₀ : (SheafOfModules.pushforward.{u + 1}
        (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj (crystallineCoproduct B I) ⟶
      (SheafOfModules.pushforward.{u + 1}
        (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj Z}
    (hab₀ : a₀ ≫ b₀ = 0) (hb₀ : IsColimit (CokernelCofork.ofπ b₀ hab₀)) :
    ∃ (a : crystallineCoproduct B K ⟶ crystallineCoproduct B I)
      (b : crystallineCoproduct B I ⟶ Z) (hab : a ≫ b = 0),
      (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map a = a₀ ∧
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map b = b₀ ∧
        Nonempty (IsColimit (CokernelCofork.ofπ
          ((SheafOfModules.pushforward.{u + 1}
            (ambientOverStructureHom B (Over.mk (𝟙 B)))).map b)
          (pushforward_ambientOverStructureHom_map_comp_eq_zero B (Over.mk (𝟙 B)) hab))) := by
  obtain ⟨a, ha⟩ :=
    exists_pushforward_map_eq_crystallineCoproduct B K (crystallineCoproduct B I) a₀
  obtain ⟨b, hb⟩ := exists_pushforward_map_eq_crystallineCoproduct B I Z b₀
  have hab : a ≫ b = 0 := by
    refine eq_of_pushforward_map_eq_crystallineCoproduct B ?_
    rw [Functor.map_comp, ha, hb, hab₀, Functor.map_zero]
  exact ⟨a, b, hab, ha, hb, ⟨isColimitCokernelCoforkOfEq ha.symm hb.symm hb₀⟩⟩

end CrystallineThickening

/-- **The presenting morphisms of the presentation of a locally quasi-coherent crystal, placed on
the localised small crystalline site.**  For a locally quasi-coherent crystal in
`𝒪_{X/S}`-modules on `Cris(X/S)` and an object `(U', T', δ')` with affine ambient scheme there are
two morphisms of sheaves of modules on `Cris(X/S)/(U', T', δ')`, between the crystalline
coproducts and the universe lift of the module, whose composite vanishes and whose ambient
restriction at the identity of `(U', T', δ')` is a cokernel. -/
theorem exists_crystallineCoproduct_cokernelCofork_pushforward
    {M : SheafOfModules.{u} (structureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) (B : CrystallineThickening S)
    [IsAffine B.obj.thickening.target.scheme] :
    ∃ (I K : Type (u + 1))
      (a : CrystallineThickening.crystallineCoproduct B K ⟶
        CrystallineThickening.crystallineCoproduct B I)
      (b : CrystallineThickening.crystallineCoproduct B I ⟶
        SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B))
      (hab : a ≫ b = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((SheafOfModules.pushforward.{u + 1}
          (CrystallineThickening.ambientOverStructureHom B (Over.mk (𝟙 B)))).map b)
        (CrystallineThickening.pushforward_ambientOverStructureHom_map_comp_eq_zero B
          (Over.mk (𝟙 B)) hab))) := by
  obtain ⟨I, K, a₀, b₀, hab₀, ⟨hb₀⟩⟩ :=
    exists_cokernelCofork_pushforward_crystallineCoproduct hlqc hcrys B
  have hab₀' : a₀ ≫ b₀ ≫ (SheafOfModules.uliftForPresentationSuccSelfIso _).hom = 0 := by
    rw [← Category.assoc, hab₀, zero_comp]
  have hb₀' : IsColimit (CokernelCofork.ofπ
      (b₀ ≫ (SheafOfModules.uliftForPresentationSuccSelfIso _).hom) hab₀') :=
    hb₀.ofIsoColimit (Cofork.ext (SheafOfModules.uliftForPresentationSuccSelfIso _) (by simp))
  obtain ⟨a, b, hab, -, -, hcolim⟩ :=
    CrystallineThickening.exists_hom_pushforward_isColimitCokernelCofork B hab₀' hb₀'
  exact ⟨I, K, a, b, hab, hcolim⟩

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
