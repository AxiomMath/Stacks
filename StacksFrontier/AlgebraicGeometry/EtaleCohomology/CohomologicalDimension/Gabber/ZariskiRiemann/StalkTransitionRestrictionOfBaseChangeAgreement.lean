module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.StalkTransitionStrictHenselizationRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StrictHenselizationCriterionCommSq
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.BoundaryRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.UnboundedHigherBaseChangeComparison

/-!
# The stalk transition along a refinement is restriction, from the agreement of base change maps

Let `π : Y' ⟶ Y` be a refinement of proper models of `η = Spec (Frac B)`, `s` a geometric point
of `Y'` and `s₀ = s ≫ π`. The stalk transition
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition` is the stalk at
`s` of the base change map of the square `𝟙 ≫ j = j' ≫ π` built from the *unbounded* derived base
change map (`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange`).
The stalk formula of Stacks 03Q9 for a commutative square
(`AlgebraicGeometry.higherBaseChangeStalkHom_comp_higherDirectImageStalkIso_hom`) is about the
*bounded below* one (`Stacks.EtaleCohomology.higherBaseChangeMapAb`). This file states that the
two agree (`Stacks.EtaleCohomology.UnboundedHigherBaseChangeAgreement`) and proves from it the
statement `AlgebraicGeometry.Scheme.ZariskiRiemann.StalkTransitionStrictHenselizationRestriction`.

The class `ξ` on `P_Y = η ×_Y Spec 𝒪^{sh}_{Y, s₀}` attached to a germ `γ` is the image of `γ`
under the isomorphism `AlgebraicGeometry.higherDirectImageStalkIso` of Stacks 03Q9
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkStrictHenselizationClass`). If `ξ`
dies under restriction along `ρ_m : P_{Y'} ⟶ P_Y`, then by the stalk formula the image of `γ`
under the stalk of the bounded below base change map dies under the isomorphism of Stacks 03Q9 on
`Y'`, so it is zero, and by the agreement so is the stalk transition of `γ`.

## Main definitions

* `Stacks.EtaleCohomology.UnboundedHigherBaseChangeAgreement`: the unbounded and the bounded below
  base change maps on higher direct images agree (a statement).
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkStrictHenselizationClass`: the class
  on `P_Y` of a germ of `R^q j_* F`.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyPullback_eq_zero_of_restrictionMap_eq_zero`: a class
  whose restriction (in the inverse image `Stacks.EtaleCohomology.etaleAbelianInverseImage`) dies
  also dies under every pull back map along the same morphism.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition_apply_eq_zero`:
  the stalk transition kills a germ whose class dies on `P_{Y'}`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.stalkTransitionRestriction_of_agreement`
  — `StalkTransitionStrictHenselizationRestriction` from `UnboundedHigherBaseChangeAgreement`.
* `Stacks.EtaleCohomology.unboundedHigherBaseChangeAgreement` and
  `AlgebraicGeometry.Scheme.ZariskiRiemann.stalkTransitionStrictHenselizationRestriction`: both
  statements hold.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **The unbounded and the bounded below base change maps on higher direct images agree** (a
statement). For a commutative square `h ≫ f = e ≫ g` of schemes, an abelian sheaf `F` on
`T_étale` and `q : ℕ`, the degree-`q` base change map `f⁻¹ Rᵠ g_* F ⟶ Rᵠ h_* e⁻¹ F` built from
the unbounded derived base change map
(`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange`) is the one of
[Stacks, Tag 0F02] built from the bounded below derived base change map
(`Stacks.EtaleCohomology.higherBaseChangeMapAb`), read through the identification
`Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleAbelianInverseImage` of the two inverse
images at the source and at the target. -/
def UnboundedHigherBaseChangeAgreement : Prop :=
  ∀ {X' Y S T : Scheme.{u}} (f : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
    (w : h ≫ f = e ≫ g) (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (q : ℕ),
    (smallEtalePullbackAbIsoEtaleAbelianInverseImage f).hom.app
        (((smallEtalePushforwardAb g).rightDerived q).obj F) ≫
      etaleAbelianInverseImageRightDerivedDirectImageBaseChange g f e h w.symm F q =
    (higherBaseChangeMapAb f g h e w q).app F ≫
      ((smallEtalePushforwardAb h).rightDerived q).map
        ((smallEtalePullbackAbIsoEtaleAbelianInverseImage e).hom.app F)

/-- **The unbounded and the bounded below base change maps on higher direct images agree**:
`Stacks.EtaleCohomology.UnboundedHigherBaseChangeAgreement` holds, by
`etaleAbelianInverseImageRightDerivedDirectImageBaseChange_eq_higherBaseChangeMapAb`. -/
theorem unboundedHigherBaseChangeAgreement : UnboundedHigherBaseChangeAgreement.{u} :=
  fun f g h e w F q =>
    etaleAbelianInverseImageRightDerivedDirectImageBaseChange_eq_higherBaseChangeMapAb f g h e w F q

attribute [local instance high] ConstantTransport.hasExt_sheaf_smallEtaleTopology

/-- **A class killed by restriction is killed by every pull back along the same morphism.** For
`i : Y ⟶ X`, an isomorphism `ι : A ≅ A'` of abelian sheaves on `X_étale` and a class
`y ∈ H^q(X, A)`, if the restriction along `i` of the transported class `ι y ∈ H^q(X, A')` vanishes,
then `y` vanishes under the pull back map along `i` attached to any `ψ : i⁻¹ A ⟶ G`: both are read
off the image of `y` under the exact inverse image along `i`, in its two isomorphic spellings. -/
theorem etaleCohomologyPullback_eq_zero_of_restrictionMap_eq_zero {X Y : Scheme.{u}}
    (i : Y ⟶ X) {A A' : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (ι : A ≅ A')
    {G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} (ψ : (smallEtalePullbackAb i).obj A ⟶ G)
    {q : ℕ} (y : Sheaf.H.{u + 1} A q)
    (hy : etaleCohomologyRestrictionMap.{u, 0, u + 1} i A' q
      (y.comp (Ext.mk₀ ι.hom) (add_zero q)) = 0) :
    etaleCohomologyPullback i ψ q y = 0 := by
  let L := etaleAbelianInverseImage.{u, 0} i
  let κ := (etaleAbelianInverseImageConstantIso.{u, 0} i).app (AddCommGrpCat.of (ULift ℤ))
  rw [etaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    at hy
  have h1 : (y.mapExactFunctor L).comp (Ext.mk₀ (L.map ι.hom)) (add_zero q) = 0 := by
    have h := congrArg (fun z => (Ext.mk₀ κ.hom).comp z (zero_add q)) hy
    simp only [Ext.comp_zero] at h
    rwa [Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id, Ext.mk₀_id_comp] at h
  have h2 : y.mapExactFunctor L = 0 := by
    have h := congrArg (fun z => z.comp (Ext.mk₀ (L.map ι.inv)) (add_zero q)) h1
    simp only [Ext.zero_comp] at h
    rwa [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, ← L.map_comp, Iso.hom_inv_id,
      L.map_id, Ext.comp_mk₀_id] at h
  have h3 : y.mapExactFunctor (smallEtalePullbackAb i) = 0 :=
    (Stacks.ExtFunctorial.mapExactFunctor_eq_zero_iff_of_iso
      (smallEtalePullbackAbIsoInverseImage i) y).2 h2
  rw [etaleCohomologyPullback_apply, h3, Ext.zero_comp, Ext.comp_zero]

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology

namespace ProperModel

variable {B : Type u} [CommRing B] [IsDomain B]

/-- **The class on `P_Y` of a germ of `R^q j_* F`.** For a geometric point `s₀ : Spec Ω ⟶ Y` of a
proper model and a germ `γ` of `R^q j_* F` at `s₀`, the image of `γ` in
`H^q(P_Y, F|)`, `P_Y = η ×_Y Spec 𝒪^{sh}_{Y, s₀}`, under the isomorphism of Stacks 03Q9
`AlgebraicGeometry.higherDirectImageStalkIso`, read in the inverse image
`Stacks.EtaleCohomology.etaleAbelianInverseImage`. -/
def stalkStrictHenselizationClass (M : ProperModel B)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s₀ : Spec (.of Ω) ⟶ M.Y)
    (γ : (smallEtaleStalkAb s₀).obj (((smallEtalePushforwardAb M.j).rightDerived q).obj F)) :
    Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (strictHenselizationBaseChangeToSource (BigEtaleSite.containing M.Y)
          (BigEtaleSite.contains_containing M.Y) M.j (geometricPointOf s₀))).obj F) q :=
  Ext.comp ((higherDirectImageStalkIso (BigEtaleSite.containing M.Y)
      (BigEtaleSite.contains_containing M.Y) M.j (geometricPointOf s₀) q F).hom γ)
    (Ext.mk₀ ((smallEtalePullbackAbIsoInverseImage
      (strictHenselizationBaseChangeToSource (BigEtaleSite.containing M.Y)
        (BigEtaleSite.contains_containing M.Y) M.j (geometricPointOf s₀))).hom.app F))
    (add_zero q)

omit [IsDomain B] in
/-- **The stalk transition, through the bounded below base change map.** Under
`Stacks.EtaleCohomology.UnboundedHigherBaseChangeAgreement`, the stalk transition at `s` along a
refinement is the stalk at `s` of the bounded below base change map of the square
`𝟙 ≫ j = j' ≫ π` (`Stacks.EtaleCohomology.higherBaseChangeMapAb`), followed by the
identification of the two inverse images along `𝟙`. -/
theorem Refinement.stalkTransition_eq_higherBaseChangeMapAb
    (hagree : UnboundedHigherBaseChangeAgreement.{u}) {M' M : ProperModel B}
    (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y) :
    φ.stalkTransition F q s =
      ((smallEtaleStalkPullbackAbIso φ.π s).app
          (((smallEtalePushforwardAb M.j).rightDerived q).obj F)).inv ≫
        (smallEtaleStalkAb s).map
          ((higherBaseChangeMapAb φ.π M.j M'.j (𝟙 _) (by rw [Category.id_comp, φ.fac]) q).app F ≫
            ((smallEtalePushforwardAb M'.j).rightDerived q).map
              ((smallEtalePullbackAbIsoEtaleAbelianInverseImage (𝟙 _)).hom.app F)) := by
  rw [← hagree φ.π M.j M'.j (𝟙 _) (by rw [Category.id_comp, φ.fac]) F q]
  rfl

omit [IsDomain B] in
/-- **The stalk transition kills a germ whose class dies on `P_{Y'}`.** Under
`Stacks.EtaleCohomology.UnboundedHigherBaseChangeAgreement`: let `π : Y' ⟶ Y` be a refinement,
`s` a geometric point of `Y'`, `m : 𝒪^{sh}_{Y, π s} → 𝒪^{sh}_{Y', s}` a local homomorphism over
`π` compatible with the canonical geometric points, and `γ` a germ of `R^q j_* F` at `π s`. If the
class of `γ` on `P_Y`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkStrictHenselizationClass`) dies
under restriction along `ρ_m : P_{Y'} ⟶ P_Y`, then the stalk transition of `γ` vanishes. By
the stalk formula of Stacks 03Q9 for the square `𝟙 ≫ j = j' ≫ π`
(`AlgebraicGeometry.higherBaseChangeStalkHom_comp_higherDirectImageStalkIso_hom`) the image of
`γ` under the stalk of the bounded below base change map is carried by the isomorphism of 03Q9
on `Y'` to the pull back of the class along `ρ_m`, which vanishes. -/
theorem Refinement.stalkTransition_apply_eq_zero
    (hagree : UnboundedHigherBaseChangeAgreement.{u}) {M' M : ProperModel B}
    (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y)
    (m : ↥(etaleLocalRing (BigEtaleSite.containing M.Y) M.Y
        (BigEtaleSite.contains_containing M.Y) (geometricPointOf (s ≫ φ.π))) →+*
      ↥(etaleLocalRing (BigEtaleSite.containing M'.Y) M'.Y
        (BigEtaleSite.contains_containing M'.Y) (geometricPointOf s)))
    (hm : strictHenselizationToBase (BigEtaleSite.containing M'.Y) M'.Y
        (BigEtaleSite.contains_containing M'.Y) (geometricPointOf s) ≫ φ.π =
      Spec.map (CommRingCat.ofHom m) ≫ strictHenselizationToBase (BigEtaleSite.containing M.Y)
        M.Y (BigEtaleSite.contains_containing M.Y) (geometricPointOf (s ≫ φ.π)))
    (hpt : geometricPointToStrictHenselization (BigEtaleSite.containing M'.Y) M'.Y
        (BigEtaleSite.contains_containing M'.Y) (geometricPointOf s) ≫
        Spec.map (CommRingCat.ofHom m) =
      geometricPointToStrictHenselization (BigEtaleSite.containing M.Y) M.Y
        (BigEtaleSite.contains_containing M.Y) (geometricPointOf (s ≫ φ.π)))
    (γ : (smallEtaleStalkAb (s ≫ φ.π)).obj
      (((smallEtalePushforwardAb M.j).rightDerived q).obj F))
    (hres : etaleCohomologyRestrictionMap.{u, 0, u + 1}
        (φ.strictHenselizationBaseChangeMap (s ≫ φ.π) s m hm) _ q
        (M.stalkStrictHenselizationClass F q (s ≫ φ.π) γ) = 0) :
    φ.stalkTransition F q s γ = 0 := by
  have w : M'.j ≫ φ.π = 𝟙 _ ≫ M.j := by rw [Category.id_comp, φ.fac]
  have key := higherBaseChangeStalkHom_comp_higherDirectImageStalkIso_hom
    (BigEtaleSite.containing M'.Y) (BigEtaleSite.containing M.Y)
    (BigEtaleSite.contains_containing M'.Y) (BigEtaleSite.contains_containing M.Y) w
    (geometricPointOf s) (Spec.map (CommRingCat.ofHom m)) hm.symm hpt q F
  have hpull := etaleCohomologyPullback_eq_zero_of_restrictionMap_eq_zero
    (strictHenselizationBaseChangeSquareMap (BigEtaleSite.containing M'.Y)
      (BigEtaleSite.containing M.Y) (BigEtaleSite.contains_containing M'.Y)
      (BigEtaleSite.contains_containing M.Y) w (geometricPointOf s)
      (Spec.map (CommRingCat.ofHom m)) hm.symm)
    ((smallEtalePullbackAbIsoInverseImage
      (strictHenselizationBaseChangeToSource (BigEtaleSite.containing M.Y)
        (BigEtaleSite.contains_containing M.Y) M.j (geometricPointOf (s ≫ φ.π)))).app F)
    ((strictHenselizationBaseChangeSquarePullbackHom (BigEtaleSite.containing M'.Y)
      (BigEtaleSite.containing M.Y) (BigEtaleSite.contains_containing M'.Y)
      (BigEtaleSite.contains_containing M.Y) w (geometricPointOf s)
      (Spec.map (CommRingCat.ofHom m)) hm.symm).app F)
    ((higherDirectImageStalkIso (BigEtaleSite.containing M.Y)
      (BigEtaleSite.contains_containing M.Y) M.j (geometricPointOf (s ≫ φ.π)) q F).hom γ) hres
  have h0 : (higherDirectImageStalkIso (BigEtaleSite.containing M'.Y)
      (BigEtaleSite.contains_containing M'.Y) M'.j (geometricPointOf s) q
      ((smallEtalePullbackAb (𝟙 _)).obj F)).hom
        (((higherBaseChangeStalkHom φ.π M.j M'.j (𝟙 _) w s).app q).app F γ) = 0 :=
    (ConcreteCategory.comp_apply _ _ γ).symm.trans
      ((ConcreteCategory.congr_hom key γ).trans ((ConcreteCategory.comp_apply _ _ γ).trans hpull))
  have hb : ((higherBaseChangeStalkHom φ.π M.j M'.j (𝟙 _) w s).app q).app F γ = 0 := by
    have hinj := ((ConcreteCategory.isIso_iff_bijective
      (higherDirectImageStalkIso (BigEtaleSite.containing M'.Y)
        (BigEtaleSite.contains_containing M'.Y) M'.j (geometricPointOf s) q
        ((smallEtalePullbackAb (𝟙 _)).obj F)).hom).1 inferInstance).1
    exact hinj (h0.trans (map_zero _).symm)
  have hb' : (smallEtaleStalkAb s).map
      ((higherBaseChangeMapAb φ.π M.j M'.j (𝟙 _) w q).app F)
        (((smallEtaleStalkPullbackAbIso φ.π s).app
          (((smallEtalePushforwardAb M.j).rightDerived q).obj F)).inv γ) = 0 := hb
  rw [Refinement.stalkTransition_eq_higherBaseChangeMapAb hagree φ F q s, Functor.map_comp]
  exact (congrArg (ConcreteCategory.hom ((smallEtaleStalkAb s).map
    (((smallEtalePushforwardAb M'.j).rightDerived q).map
      ((smallEtalePullbackAbIsoEtaleAbelianInverseImage (𝟙 _)).hom.app F)))) hb').trans
    (map_zero _)

end ProperModel

/-- **The stalk transition is restriction along the strict henselizations**
(`AlgebraicGeometry.Scheme.ZariskiRiemann.StalkTransitionStrictHenselizationRestriction`), from
the agreement `Stacks.EtaleCohomology.UnboundedHigherBaseChangeAgreement` of the unbounded and
the bounded below base change maps. The class `ξ` of a germ `γ` is its image under the
isomorphism of Stacks 03Q9
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.stalkStrictHenselizationClass`), and the
implication is
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition_apply_eq_zero`. -/
theorem stalkTransitionRestriction_of_agreement
    (hagree : UnboundedHigherBaseChangeAgreement.{u}) :
    StalkTransitionStrictHenselizationRestriction.{u} := by
  intro B _ _ F q M Ω _ _ s₀ γ
  refine ⟨M.stalkStrictHenselizationClass F q s₀ γ, ?_⟩
  intro M' φ s h m hm hpt hres
  subst h
  rw [eqToHom_refl, Category.id_comp]
  exact φ.stalkTransition_apply_eq_zero hagree F q s m hm hpt γ hres

/-- **The stalk transition is restriction along the strict henselizations** (Stacks 03Q9,
compatibility clause, in kernel form):
`AlgebraicGeometry.Scheme.ZariskiRiemann.StalkTransitionStrictHenselizationRestriction` holds.
It is `AlgebraicGeometry.Scheme.ZariskiRiemann.stalkTransitionRestriction_of_agreement` with
`Stacks.EtaleCohomology.unboundedHigherBaseChangeAgreement`. -/
theorem stalkTransitionStrictHenselizationRestriction :
    StalkTransitionStrictHenselizationRestriction.{u} :=
  stalkTransitionRestriction_of_agreement unboundedHigherBaseChangeAgreement

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
