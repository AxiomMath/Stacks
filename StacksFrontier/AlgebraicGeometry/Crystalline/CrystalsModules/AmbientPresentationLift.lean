module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientRestrictionCoproducts

/-!
# Lifting the presenting morphisms of a presentation to a localised crystalline site

Let `B` be an object of the big crystalline site of a global crystalline situation and let
`CRIS(X/S)/B` be the localisation of the site at it.  By
`Crystalline.GlobalCrystallineSituation.exists_cokernelCofork_pushforward_crystallineCoproduct`
the ambient restriction at the identity of `B` of the universe lift of a locally quasi-coherent
crystal is presented by the ambient restrictions of two coproducts of copies of the universe lift
of the structure sheaf of `CRIS(X/S)/B` — but the two presenting morphisms of that presentation
are morphisms on the Zariski site of the ambient scheme of `B`, while the presentation of the
module itself has to be assembled on `CRIS(X/S)/B`.

This file lifts them.  Restriction along the ambient restriction at the identity of `B` is
bijective on morphisms out of the universe lift of the structure sheaf
(`Crystalline.GlobalCrystallineSituation.Thickening.bijective_pushforward_map_uliftUnit`), hence
bijective on morphisms out of a coproduct of copies of that lift, and the two presenting
morphisms have unique preimages on the localised crystalline site.  Their composite vanishes
because its image under restriction does.

## Main definitions

* `SheafOfModules.uliftForPresentationSuccSelfIso` — the universe lift by the universe of the site
  of a sheaf of modules whose sections already lie one universe above it is the sheaf itself.
* `Crystalline.GlobalCrystallineSituation.toTerminalOver` — the structure morphism of an object
  of a localised site, read as a morphism to its terminal object.

## Main results

* `CategoryTheory.Limits.isColimitCokernelCoforkOfEq` — a cokernel cofork is recognised through
  equalities of the two morphisms it is built from.
* `Crystalline.GlobalCrystallineSituation.Thickening`
  `.bijective_pushforward_map_crystallineCoproduct`
  — **restriction along the ambient restriction at the identity of `B` is bijective on morphisms
  out of a crystalline coproduct**, with
  `Crystalline.GlobalCrystallineSituation.Thickening`
  `.eq_of_pushforward_map_eq_crystallineCoproduct`
  and
  `Crystalline.GlobalCrystallineSituation.Thickening`
  `.exists_pushforward_map_eq_crystallineCoproduct`
  for its two halves.
* `Crystalline.GlobalCrystallineSituation.Thickening`
  `.exists_hom_pushforward_isColimitCokernelCofork`
  — **the two presenting morphisms of a presentation of the ambient restriction at the identity of
  `B` by the ambient restrictions of two crystalline coproducts lift to the localised crystalline
  site**, uniquely, and their composite vanishes there.
* `Crystalline.GlobalCrystallineSituation`
  `.exists_crystallineCoproduct_cokernelCofork_pushforward`
  — **the presenting morphisms of the presentation of a locally quasi-coherent crystal placed on
  the localised crystalline site**: two morphisms between the crystalline coproducts and the
  universe lift of the module whose composite vanishes and whose ambient restriction at the
  identity of `B` is a cokernel.

## Implementation notes

The bijection on morphisms out of a coproduct is assembled summand by summand: a morphism out of
the coproduct is a family of morphisms out of the summands
(`Crystalline.GlobalCrystallineSituation.Thickening.isColimitCrystallineCoproductCofan`), its
restriction is the corresponding family of restrictions
(`Crystalline.GlobalCrystallineSituation.Thickening`
`.isColimitPushforwardCrystallineCoproductCofan`),
and on each summand restriction is bijective.  The vanishing of the composite of the two lifts is
the injectivity half: both the composite and the zero morphism restrict to the same thing.

The target of the lifted presentation is the universe lift
`SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}` of the module, which is the target a
global presentation on the localised crystalline site asks for.  Its ambient restriction carries
one further lift by `ULift.{u}` in the presentation that
`Crystalline.GlobalCrystallineSituation.exists_cokernelCofork_pushforward_crystallineCoproduct`
supplies, because a global presentation on the Zariski site of the ambient scheme lifts the module
it presents by the universe of that site; `SheafOfModules.uliftForPresentationSuccSelfIso`
absorbs it, the module being already at the module universe `u + 1`.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace CategoryTheory.Limits

/-- **A cokernel cofork is recognised through equalities of the two morphisms it is built from.**
If `b : P ⟶ N` is a cokernel of `a : Q ⟶ P` then so is any `b'` equal to it, as a cokernel of any
`a'` equal to `a`.

This is what carries a cokernel along the *definitional* identifications that a lifted
presentation produces: the lift of a morphism is equal to it after restriction, not identical to
it, and the two vanishing hypotheses are proofs of the same proposition. -/
noncomputable def isColimitCokernelCoforkOfEq {D : Type*} [Category* D] [HasZeroMorphisms D]
    {Q P N : D} {a a' : Q ⟶ P} {b b' : P ⟶ N} {hab : a ≫ b = 0} {hab' : a' ≫ b' = 0}
    (ha : a = a') (hb : b = b') (h : IsColimit (CokernelCofork.ofπ b hab)) :
    IsColimit (CokernelCofork.ofπ b' hab') := by
  subst ha
  subst hb
  exact h

end CategoryTheory.Limits

namespace SheafOfModules

/-- **The universe lift of the sections of a sheaf of modules by the universe of the site is the
sheaf itself when its sections already lie one universe above the site.**  This is
`SheafOfModules.uliftForPresentationSelfIso'` at the universes at which a global presentation on
a localised crystalline site is read: the extra `ULift.{u}` that a global presentation on a site
with objects, morphisms and coefficient rings in `Type u` puts on the module it presents is no
extra lift at all once that module is at the module universe `u + 1`. -/
noncomputable def uliftForPresentationSuccSelfIso {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} (N : SheafOfModules.{u + 1} R) :
    uliftForPresentation.{u, u, u, u + 1, u} N ≅ N :=
  uliftForPresentationSelfIso'.{u, u, u, u + 1, u} N

end SheafOfModules

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **The structure morphism of an object of a localised site, read as a morphism to the terminal
object of that site**: for `X` over `B`, the morphism `X ⟶ (B, 𝟙 B)` of `Over B` given by the
structure morphism of `X`.  It is used for the localised big and small crystalline sites. -/
noncomputable abbrev toTerminalOver {C : Type*} [Category C] (B : C) (X : Over B) :
    X ⟶ Over.mk (𝟙 B) :=
  Over.homMk X.hom (Category.comp_id X.hom)

namespace Thickening

variable (B : Thickening S)

/-- Restriction along an ambient restriction carries a vanishing composite to a vanishing
composite, being a functor which preserves zero morphisms. -/
theorem pushforward_ambientOverStructureHom_map_comp_eq_zero (X : Over B)
    {Q P N : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)} {a : Q ⟶ P}
    {b : P ⟶ N} (hab : a ≫ b = 0) :
    (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map a ≫
        (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map b = 0 := by
  rw [← Functor.map_comp, hab]
  exact (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map_zero _ _

/-- Two morphisms out of the universe lift of the structure sheaf of a localised crystalline site
with the same ambient restriction at the identity of `B` are equal.  This is the injectivity half
of `Crystalline.GlobalCrystallineSituation.Thickening.bijective_pushforward_map_uliftUnit`. -/
theorem eq_of_pushforward_map_eq_uliftUnitOver
    {Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)}
    {φ ψ : uliftUnitOver B ⟶ Z}
    (h : (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ =
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map ψ) :
    φ = ψ :=
  (bijective_pushforward_map_uliftUnit B Z).injective h

/-- Every morphism out of the ambient restriction at the identity of `B` of the universe lift of
the structure sheaf is the ambient restriction of a morphism out of that lift.  This is the
surjectivity half of
`Crystalline.GlobalCrystallineSituation.Thickening.bijective_pushforward_map_uliftUnit`. -/
theorem exists_pushforward_map_eq_uliftUnitOver
    (Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B))
    (χ : (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj (uliftUnitOver B) ⟶
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).obj Z) :
    ∃ φ : uliftUnitOver B ⟶ Z,
      (SheafOfModules.pushforward.{u + 1}
        (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ = χ :=
  (bijective_pushforward_map_uliftUnit B Z).surjective χ

/-- **Two morphisms out of a crystalline coproduct with the same ambient restriction at the
identity of `B` are equal.**  A morphism out of the coproduct is determined by its composites with
the inclusions of the summands, and on each summand restriction is injective. -/
theorem eq_of_pushforward_map_eq_crystallineCoproduct {I : Type (u + 1)}
    {Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)}
    {φ ψ : crystallineCoproduct B I ⟶ Z}
    (h : (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ =
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map ψ) :
    φ = ψ := by
  have key : ∀ i : I, (SheafOfModules.pushforward.{u + 1}
        (ambientOverStructureHom B (Over.mk (𝟙 B)))).map (crystallineCoproductι B I i ≫ φ) =
      (SheafOfModules.pushforward.{u + 1}
        (ambientOverStructureHom B (Over.mk (𝟙 B)))).map
          (crystallineCoproductι B I i ≫ ψ) := by
    intro i
    rw [Functor.map_comp, Functor.map_comp, h]
  refine Cofan.IsColimit.hom_ext (isColimitCrystallineCoproductCofan B I) _ _ fun i ↦ ?_
  simp only [Limits.cofan_mk_inj]
  exact eq_of_pushforward_map_eq_uliftUnitOver B (key i)

/-- **Every morphism out of the ambient restriction at the identity of `B` of a crystalline
coproduct is the ambient restriction of a morphism out of that coproduct.**  Each composite with
the restriction of an inclusion of a summand is the restriction of a morphism out of the summand,
and those assemble through the universal property of the coproduct; the morphism so obtained has
the right restriction because the restricted inclusions make the restricted coproduct a
coproduct. -/
theorem exists_pushforward_map_eq_crystallineCoproduct (I : Type (u + 1))
    (Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B))
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
      Cofan.IsColimit.desc (isColimitCrystallineCoproductCofan B I) φ = φ i := by
    intro i
    have hi := Cofan.IsColimit.fac (isColimitCrystallineCoproductCofan B I) φ i
    simpa only [Limits.cofan_mk_inj] using hi
  have key : ∀ i : I, (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map (crystallineCoproductι B I i) ≫
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map
            (Cofan.IsColimit.desc (isColimitCrystallineCoproductCofan B I) φ) =
      (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map (crystallineCoproductι B I i) ≫ ψ := by
    intro i
    rw [← Functor.map_comp, hfac i, hφ i]
  exact ⟨Cofan.IsColimit.desc (isColimitCrystallineCoproductCofan B I) φ,
    Cofan.IsColimit.hom_ext
      (isColimitPushforwardCrystallineCoproductCofan B I (Over.mk (𝟙 B))) _ _ key⟩

/-- **Restriction along the ambient restriction at the identity of `B` is bijective on morphisms
out of a crystalline coproduct.**  This is the statement with which the two presenting morphisms
of a global presentation chosen on the affine ambient scheme of `B` are lifted to the localised
crystalline site. -/
theorem bijective_pushforward_map_crystallineCoproduct (I : Type (u + 1))
    (Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)) :
    Function.Bijective
      (fun φ : crystallineCoproduct B I ⟶ Z ↦
        (SheafOfModules.pushforward.{u + 1}
          (ambientOverStructureHom B (Over.mk (𝟙 B)))).map φ) :=
  ⟨fun _ _ h ↦ eq_of_pushforward_map_eq_crystallineCoproduct B h,
    fun ψ ↦ exists_pushforward_map_eq_crystallineCoproduct B I Z ψ⟩

/-- **The two presenting morphisms of a presentation of the ambient restriction at the identity of
`B` by the ambient restrictions of two crystalline coproducts lift to the localised crystalline
site.**  Their composite vanishes and their ambient restrictions are the two morphisms one
started from, so the restricted cofork is again a cokernel; the lifts are unique by
`Crystalline.GlobalCrystallineSituation.Thickening`
`.bijective_pushforward_map_crystallineCoproduct`.

This is the step of the direction (2) ⇒ (1) of [Stacks, Tag 07IT] at which the presentation
leaves the Zariski site of the ambient scheme: from here on the two coproducts, the two morphisms
between them and the presented module all live on `CRIS(X/S)/B`, and what is still to be proved is
that the cofork is a cokernel there. -/
theorem exists_hom_pushforward_isColimitCokernelCofork {I K : Type (u + 1)}
    {Z : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)}
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

end Thickening

/-- **The presenting morphisms of the presentation of a locally quasi-coherent crystal, placed on
the localised crystalline site.**  For a locally quasi-coherent crystal in `𝒪_{X/S}`-modules and
an object `(U', T', δ')` with affine ambient scheme there are two morphisms

  `a : ∐ 𝒪_{X/S}|_K ⟶ ∐ 𝒪_{X/S}|_I`  and  `b : ∐ 𝒪_{X/S}|_I ⟶ F`

of sheaves of modules on `CRIS(X/S)/(U', T', δ')`, between the crystalline coproducts and the
universe lift of the module, whose composite vanishes and whose ambient restriction at the
identity of `(U', T', δ')` is a cokernel.

`Crystalline.GlobalCrystallineSituation.exists_cokernelCofork_pushforward_crystallineCoproduct`
supplies such a pair after restriction;
`Crystalline.GlobalCrystallineSituation.Thickening.exists_hom_pushforward_isColimitCokernelCofork`
lifts it, and `SheafOfModules.uliftForPresentationSuccSelfIso` absorbs the extra lift by
`ULift.{u}` that a global presentation on the Zariski site of the ambient scheme puts on the
module it presents.

What remains for the direction (2) ⇒ (1) of [Stacks, Tag 07IT] is to see that the cofork of `b` is
a cokernel on `CRIS(X/S)/(U', T', δ')` itself and not merely after restriction at the identity,
which is what
`Crystalline.GlobalCrystallineSituation.Thickening.isColimitCokernelCoforkOfForallAmbientOver`
asks of *every* ambient restriction. -/
theorem exists_crystallineCoproduct_cokernelCofork_pushforward
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) (B : Thickening S) [IsAffine B.thickening.target.scheme] :
    ∃ (I K : Type (u + 1))
      (a : Thickening.crystallineCoproduct B K ⟶ Thickening.crystallineCoproduct B I)
      (b : Thickening.crystallineCoproduct B I ⟶
        SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1} (M.over B))
      (hab : a ≫ b = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ
        ((SheafOfModules.pushforward.{u + 1}
          (Thickening.ambientOverStructureHom B (Over.mk (𝟙 B)))).map b)
        (Thickening.pushforward_ambientOverStructureHom_map_comp_eq_zero B
          (Over.mk (𝟙 B)) hab))) := by
  obtain ⟨I, K, a₀, b₀, hab₀, ⟨hb₀⟩⟩ :=
    exists_cokernelCofork_pushforward_crystallineCoproduct hlqc hcrys B
  have hab₀' : a₀ ≫ b₀ ≫ (SheafOfModules.uliftForPresentationSuccSelfIso _).hom = 0 := by
    rw [← Category.assoc, hab₀, zero_comp]
  have hb₀' : IsColimit (CokernelCofork.ofπ
      (b₀ ≫ (SheafOfModules.uliftForPresentationSuccSelfIso _).hom) hab₀') :=
    hb₀.ofIsoColimit (Cofork.ext (SheafOfModules.uliftForPresentationSuccSelfIso _) (by simp))
  obtain ⟨a, b, hab, -, -, hcolim⟩ :=
    Thickening.exists_hom_pushforward_isColimitCokernelCofork B hab₀' hb₀'
  exact ⟨I, K, a, b, hab, hcolim⟩

end Crystalline.GlobalCrystallineSituation

end
