module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHomSiteAgreement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackPointwiseExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence

/-!
# Quasi-coherent modules across an equivalence of categories fibred in groupoids

Let `F : 𝒜 ⥤ ℬ` be a 1-morphism of categories fibred in groupoids over `(Sch/S)_{fppf}`, strictly
over the base (`F ⋙ q = p`), whose underlying functor is an equivalence of categories.  This is
the situation of the isomorphism `f_can : [U/R] ⟶ 𝒳` of Stacks 04WY, through which Sheaves on
Stacks, Section 06WU, identifies `QCoh(𝒪_𝒳)` with `QCoh(𝒪_{[U/R]})`.

Such an `F` is a dense subsite inclusion for the two fppf topologies, so the inverse image of
sheaves of modules along `F` (`Stacks.RelativeCech.moduleInverseImage`, restriction of scalars
along the identification of the structure sheaves) is an equivalence by the Comparison Lemma, and
it preserves and reflects quasi-coherence.  It restricts to an equivalence of the categories of
quasi-coherent modules.

The restriction of an inverse image to the small étale site of an algebraic space is computed by
composing: for a 1-morphism `x : 𝒰 ⥤ 𝒜` from a category representable by an algebraic space `U`
and a vertical 2-isomorphism `x ⋙ F ≅ g`, the restriction `x^*(F^*ℱ)|_{U_étale}` is isomorphic to
`g^*ℱ|_{U_étale}`.

## Main results

* `AlgebraicGeometry.Stack.FibredEquivalence.isDenseSubsite`: an equivalence over the base is a
  dense subsite inclusion for the fppf topologies.
* `AlgebraicGeometry.Stack.FibredEquivalence.isEquivalence_moduleInverseImage`: the inverse image
  of sheaves of modules along it is an equivalence.
* `AlgebraicGeometry.Stack.FibredEquivalence.isQuasicoherentOnSite_moduleInverseImage_obj` and
  `AlgebraicGeometry.Stack.FibredEquivalence.isQuasicoherentOnSite_of_moduleInverseImage_obj`:
  the inverse image preserves and reflects quasi-coherence.
* `AlgebraicGeometry.Stack.FibredEquivalence.quasicoherentEquivalence`:
  `QCoh(𝒪_ℬ) ≌ QCoh(𝒪_𝒜)`.
* `AlgebraicGeometry.Stack.FibredEquivalence.nonempty_iso_etaleRestrictedModuleInverseImage`:
  `x^*(F^*ℱ)|_{U_étale} ≅ g^*ℱ|_{U_étale}` for a vertical 2-isomorphism `x ⋙ F ≅ g`.

## References

* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
* [Stacks Project, Tag 06WU](https://stacks.math.columbia.edu/tag/06WU)
* [Stacks Project, Tag 03A0](https://stacks.math.columbia.edu/tag/03A0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w w' v₀ w₀

namespace AlgebraicGeometry.Stack.FibredEquivalence

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒜 : Type v} [Category.{w} 𝒜] {ℬ : Type v} [Category.{w'} ℬ]
  (p : 𝒜 ⥤ BigFppfOver B S hS) (q : ℬ ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (F : 𝒜 ⥤ ℬ)

private theorem eqToHom_comp_eqToHom_eq_id {C : Type*} [Category C] {X Y : C} (h₁ : X = Y)
    (h₂ : Y = X) : eqToHom h₁ ≫ eqToHom h₂ = 𝟙 X := by
  simp

private theorem eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {X Y Z T : C} (h₁ : X = Y)
    (h₂ : Y = Z) (h₃ : Z = T) (h : X = T) :
    (eqToHom h₁ ≫ eqToHom h₂) ≫ eqToHom h₃ = eqToHom h := by
  simp

/-- The inverse of an isomorphism lifting an identity is sent to an `eqToHom` by the functor. -/
private theorem map_inv_eq_eqToHom {C D : Type*} [Category C] [Category D] (P : C ⥤ D)
    {X Y : C} (e : X ≅ Y) {a : D} (h : P.IsHomLift (𝟙 a) e.hom) :
    P.map e.inv = eqToHom ((IsHomLift.codomain_eq P (𝟙 a) e.hom).trans
      (IsHomLift.domain_eq P (𝟙 a) e.hom).symm) := by
  have h2 : P.map e.hom ≫ P.map e.inv = 𝟙 _ := by
    rw [← Functor.map_comp]; simp
  rw [← cancel_epi (P.map e.hom), h2, IsHomLift.fac' P (𝟙 a) e.hom]
  simp

/-- The identification of the structure sheaf of `𝒜` with the inverse image of that of `ℬ`
is, on sections over `X`, pullback of regular functions along the identification
`q(F(X)) = p(X)`. -/
theorem ringStructureSheafCoreHom_hom_app (hF : F ⋙ q = p) (X : 𝒜ᵒᵖ) :
    (ringStructureSheafCoreHom B S hS p q F (B.baseTopology .fppf) hp hq hF
      (B.baseTopology_le_topology .fppf)).hom.app X =
      (BigFppfOver.structureSheaf B S hS).obj.map (eqToHom (Functor.congr_obj hF X.unop)).op := by
  subst hF
  exact ((BigFppfOver.structureSheaf B S hS).obj.map_id _).symm

section Equivalence

variable [F.IsEquivalence]

include hp hq in
/-- **An equivalence over the base is a dense subsite inclusion** for the two fppf topologies:
it is full, faithful and cover-dense, and a sieve covers in the inherited topology exactly when
its image in the base covers. -/
theorem isDenseSubsite (hF : F ⋙ q = p) :
    F.IsDenseSubsite (BigFppfOver.associatedTopology B S hS p .fppf)
      (BigFppfOver.associatedTopology B S hS q .fppf) := by
  subst hF
  exact Functor.isDenseSubsite_inheritedTopology (F ⋙ q) (𝟭 _) F q
    (BigFppfOver.baseOverTopology B S hS .fppf) (BigFppfOver.baseOverTopology B S hS .fppf)
    hp hq
    { functorPushforward_mem_iff := fun {_ R} => by
        rw [Sieve.functorPushforward_id]; exact Iff.rfl }
    (fun y R => by
      rw [Sieve.functorPushforward_id, ← Sieve.functorPushforward_comp]
      exact Iff.rfl)
    inferInstance

/-- **The inverse image of sheaves of modules along an equivalence over the base is an
equivalence**, by the Comparison Lemma for the dense subsite inclusion `F`. -/
theorem isEquivalence_moduleInverseImage (hF : F ⋙ q = p) :
    (Stacks.RelativeCech.moduleInverseImage.{u, v, v, w, w', u} B S hS p q hp hq F hF
      .fppf).IsEquivalence := by
  subst hF
  have := isDenseSubsite (F ⋙ q) q hp hq F rfl
  exact FibredDenseSubsite.isEquivalence_moduleRestriction q hq F
    (BigFppfOver.associatedTopology B S hS (F ⋙ q) .fppf)
    (BigFppfOver.associatedTopology B S hS q .fppf)
    (FibredSite.ringStructureSheafCore B S hS q hq .fppf)

/-- **The inverse image along an equivalence over the base reflects quasi-coherence**: the
inverse image is restriction to a dense subsite, along which quasi-coherence descends. -/
theorem isQuasicoherentOnSite_of_moduleInverseImage_obj (hF : F ⋙ q = p)
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS q hq .fppf))
    (h : ((Stacks.RelativeCech.moduleInverseImage.{u, v, v, w, w', u} B S hS p q hp hq F hF
      .fppf).obj M).IsQuasicoherentOnSite) : M.IsQuasicoherentOnSite := by
  subst hF
  have := isDenseSubsite (F ⋙ q) q hp hq F rfl
  exact FibredDenseSubsite.isQuasicoherentOnSite_of_moduleRestriction (F ⋙ q) q hp hq F
    (BigFppfOver.associatedTopology B S hS (F ⋙ q) .fppf)
    (BigFppfOver.associatedTopology B S hS q .fppf)
    (FibredSite.ringStructureSheafCore B S hS q hq .fppf) M h

omit [F.IsEquivalence] in
/-- **The inverse image along an equivalence over the base preserves quasi-coherence.**  For a
quasi-inverse `G` over the base with a vertical counit `G ⋙ F ≅ 𝟭`, the restriction along the
dense subsite inclusion `G` of the inverse image `F^*ℱ` is isomorphic to `ℱ`, so `F^*ℱ` is
quasi-coherent as soon as `ℱ` is. -/
theorem isQuasicoherentOnSite_moduleInverseImage_obj (hF : F ⋙ q = p)
    (G : ℬ ⥤ 𝒜) [G.IsEquivalence] (hG : G ⋙ p = q) (ε : G ⋙ F ≅ 𝟭 ℬ)
    (hε : ∀ y, q.IsHomLift (𝟙 (q.obj ((G ⋙ F).obj y))) (ε.hom.app y))
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS q hq .fppf))
    (hM : M.IsQuasicoherentOnSite) :
    ((Stacks.RelativeCech.moduleInverseImage.{u, v, v, w, w', u} B S hS p q hp hq F hF
      .fppf).obj M).IsQuasicoherentOnSite := by
  subst hG
  let : p.IsFibered := hp.isFibered
  let : (G ⋙ p).IsFibered := hq.isFibered
  have := isDenseSubsite (G ⋙ p) p hq hp G rfl
  let := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS .fppf)).1
  refine FibredDenseSubsite.isQuasicoherentOnSite_of_moduleRestriction (G ⋙ p) p hq hp G
    (BigFppfOver.associatedTopology B S hS (G ⋙ p) .fppf)
    (BigFppfOver.associatedTopology B S hS p .fppf)
    (FibredSite.ringStructureSheafCore B S hS p hp .fppf) _ ?_
  let ψ := ringStructureSheafCoreHom B S hS p (G ⋙ p) F (B.baseTopology .fppf) hp hq hF
    (B.baseTopology_le_topology .fppf)
  let : (G ⋙ F).IsContinuous (BigFppfOver.associatedTopology B S hS (G ⋙ p) .fppf)
      (BigFppfOver.associatedTopology B S hS (G ⋙ p) .fppf) :=
    Functor.isContinuous_comp G F _ (BigFppfOver.associatedTopology B S hS p .fppf) _
  let φ₁ : FibredSite.ringStructureSheafCore B S hS (G ⋙ p) hq .fppf ⟶
      ((G ⋙ F).sheafPushforwardContinuous RingCat.{u}
        (BigFppfOver.associatedTopology B S hS (G ⋙ p) .fppf)
        (BigFppfOver.associatedTopology B S hS (G ⋙ p) .fppf)).obj
        (FibredSite.ringStructureSheafCore B S hS (G ⋙ p) hq .fppf) :=
    𝟙 _ ≫ (G.sheafPushforwardContinuous RingCat.{u}
      (BigFppfOver.associatedTopology B S hS (G ⋙ p) .fppf)
      (BigFppfOver.associatedTopology B S hS p .fppf)).map ψ
  have hring : φ₁ ≫ (Functor.sheafPushforwardContinuousNatTrans ε.symm.hom RingCat.{u}
        (BigFppfOver.associatedTopology B S hS (G ⋙ p) .fppf)
        (BigFppfOver.associatedTopology B S hS (G ⋙ p) .fppf)).app
        (FibredSite.ringStructureSheafCore B S hS (G ⋙ p) hq .fppf) =
      𝟙 (FibredSite.ringStructureSheafCore B S hS (G ⋙ p) hq .fppf) := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun Y => ?_))
    obtain ⟨y⟩ := Y
    have hc : (G ⋙ p).map (ε.inv.app y) = _ := map_inv_eq_eqToHom (G ⋙ p) (ε.app y) (hε y)
    change (𝟙 _ ≫ ψ.hom.app (op (G.obj y))) ≫
        (BigFppfOver.structureSheaf B S hS).obj.map ((G ⋙ p).map (ε.inv.app y)).op = 𝟙 _
    rw [Category.id_comp, ringStructureSheafCoreHom_hom_app, hc]
    simp only [eqToHom_op, eqToHom_map]
    exact eqToHom_comp_eqToHom_eq_id _ _
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((SheafOfModules.pushforwardComp (F := G) (G := F) (𝟙 _) ψ).app M ≪≫
      (SheafOfModules.pushforwardNatIso φ₁ ε.symm).app M ≪≫
      (SheafOfModules.pushforwardCongr hring).app M ≪≫
      (SheafOfModules.pushforwardId _).app M).symm hM

/-- **`QCoh(𝒪_ℬ) ≌ QCoh(𝒪_𝒜)`** along an equivalence `F : 𝒜 ⥤ ℬ` over the base: the inverse image
of sheaves of modules, restricted to the quasi-coherent ones. -/
noncomputable def quasicoherentEquivalence (hF : F ⋙ q = p)
    (G : ℬ ⥤ 𝒜) [G.IsEquivalence] (hG : G ⋙ p = q) (ε : G ⋙ F ≅ 𝟭 ℬ)
    (hε : ∀ y, q.IsHomLift (𝟙 (q.obj ((G ⋙ F).obj y))) (ε.hom.app y)) :
    FibredSite.quasicoherentModules.{u, v, w', u} B S hS q hq ≌
      FibredSite.quasicoherentModules.{u, v, w, u} B S hS p hp :=
  haveI := isEquivalence_moduleInverseImage p q hp hq F hF
  @Equivalence.congrFullSubcategory _ _ _ _ _ _
    (Stacks.RelativeCech.moduleInverseImage.{u, v, v, w, w', u} B S hS p q hp hq F hF
      .fppf).asEquivalence
    ⟨fun e h => SheafOfModules.IsQuasicoherentOnSite.of_iso e h⟩
    (funext fun M => propext ⟨isQuasicoherentOnSite_of_moduleInverseImage_obj p q hp hq F hF M,
      isQuasicoherentOnSite_moduleInverseImage_obj p q hp hq F hF G hG ε hε M⟩)

end Equivalence

section Restriction

variable {U : AlgebraicSpaces B S hS} {𝒰 : Type v₀} [Category.{w₀} 𝒰]
  (p𝒰 : 𝒰 ⥤ BigFppfOver B S hS) (hp𝒰 : p𝒰.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p𝒰 (presheafOfCategories (U.1 ⋙ typeToCat)).p)

/-- **Restriction of an inverse image to the small étale site of an algebraic space.**  Let
`x : 𝒰 ⥤ 𝒜` be a 1-morphism from a category representable by an algebraic space `U`, and let
`α : x ⋙ F ≅ g` be a vertical 2-isomorphism.  Then `x^*(F^*ℱ)|_{U_étale} ≅ g^*ℱ|_{U_étale}`. -/
theorem nonempty_iso_etaleRestrictedModuleInverseImage (hF : F ⋙ q = p)
    (x : 𝒰 ⥤ 𝒜) (hx : p𝒰.IsFibredOneMorphism p x) (g : 𝒰 ⥤ ℬ)
    (hg : p𝒰.IsFibredOneMorphism q g) (α : x ⋙ F ≅ g)
    (hα : ∀ X, q.IsHomLift (𝟙 (p𝒰.obj X)) (α.hom.app X))
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS q hq .fppf)) :
    Nonempty (Space.etaleRestrictedModuleInverseImage B S hS p𝒰 p hp𝒰 hp eU x hx
        (FibredSite.restrictSiteModules B S hS p hp .etale
          ((Stacks.RelativeCech.moduleInverseImage.{u, v, v, w, w', u} B S hS p q hp hq F hF
            .fppf).obj M)) ≅
      Space.etaleRestrictedModuleInverseImage B S hS p𝒰 q hp𝒰 hq eU g hg
        (FibredSite.restrictSiteModules B S hS q hq .etale M)) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
    (BigFppfOver.baseOverTopology B S hS .etale)).1
  let := Space.etaleChartToFibred_isContinuous B S hS p𝒰 p hp𝒰 eU x hx
  let := Space.etaleChartToFibred_isContinuous B S hS p𝒰 q hp𝒰 eU g hg
  let ψ : FibredSite.ringStructureSheafCore B S hS p hp .etale ⟶
      (F.sheafPushforwardContinuous RingCat.{u} (BigFppfOver.associatedTopology B S hS p .etale)
        (BigFppfOver.associatedTopology B S hS q .etale)).obj
        (FibredSite.ringStructureSheafCore B S hS q hq .etale) :=
    ⟨(ringStructureSheafCoreHom B S hS p q F (B.baseTopology .fppf) hp hq hF
      (B.baseTopology_le_topology .fppf)).hom⟩
  let e := Space.etaleChartToFibred B S hS p𝒰 eU x
  let : (e ⋙ F).IsContinuous (Space.SmallEtale.topology B S hS U.obj)
      (BigFppfOver.associatedTopology B S hS q .etale) :=
    Functor.isContinuous_comp _ _ _ (BigFppfOver.associatedTopology B S hS p .etale) _
  let φx := Space.etaleChartStructureHom B S hS p𝒰 p hp𝒰 hp eU x hx
  let φg := Space.etaleChartStructureHom B S hS p𝒰 q hp𝒰 hq eU g hg
  let α' : Space.etaleChartToFibred B S hS p𝒰 eU g ≅ e ⋙ F :=
    (Functor.isoWhiskerLeft (Space.restrictionFunctor B S hS U.1 p𝒰 eU) α).symm ≪≫
      (Functor.associator _ x F).symm
  let φ₁ : Space.structureRingSheaf B S hS U ⟶
      ((e ⋙ F).sheafPushforwardContinuous RingCat.{u} (Space.SmallEtale.topology B S hS U.obj)
        (BigFppfOver.associatedTopology B S hS q .etale)).obj
        (FibredSite.ringStructureSheafCore B S hS q hq .etale) :=
    φx ≫ (e.sheafPushforwardContinuous RingCat.{u} (Space.SmallEtale.topology B S hS U.obj)
      (BigFppfOver.associatedTopology B S hS p .etale)).map ψ
  have hring : φ₁ ≫ (Functor.sheafPushforwardContinuousNatTrans α'.hom RingCat.{u}
        (Space.SmallEtale.topology B S hS U.obj)
        (BigFppfOver.associatedTopology B S hS q .etale)).app
        (FibredSite.ringStructureSheafCore B S hS q hq .etale) = φg := by
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W => ?_))
    obtain ⟨W⟩ := W
    let a := (Space.restrictionFunctor B S hS U.1 p𝒰 eU).obj W
    have hc : q.map (α.inv.app a) = _ := map_inv_eq_eqToHom q (α.app a) (hα a)
    have h1 : q.map (α'.hom.app W) = q.map (α.inv.app a) := by simp [α', a]
    change (φx.hom.app (op W) ≫ (ringStructureSheafCoreHom B S hS p q F (B.baseTopology .fppf)
        hp hq hF (B.baseTopology_le_topology .fppf)).hom.app (op (e.obj W))) ≫
        (BigFppfOver.structureSheaf B S hS).obj.map (q.map (α'.hom.app W)).op = φg.hom.app (op W)
    rw [Space.etaleChartStructureHom_app, Space.etaleChartStructureHom_app,
      ringStructureSheafCoreHom_hom_app, h1, hc]
    simp only [eqToHom_op, eqToHom_map]
    exact eqToHom_comp_comp_eqToHom _ _ _ _
  have h1 : Space.etaleRestrictedModuleInverseImage B S hS p𝒰 p hp𝒰 hp eU x hx
        (FibredSite.restrictSiteModules B S hS p hp .etale
          ((Stacks.RelativeCech.moduleInverseImage.{u, v, v, w, w', u} B S hS p q hp hq F hF
            .fppf).obj M)) =
      (SheafOfModules.pushforward φx).obj ((SheafOfModules.pushforward ψ).obj
        (FibredSite.restrictSiteModules B S hS q hq .etale M)) := rfl
  have h2 : Space.etaleRestrictedModuleInverseImage B S hS p𝒰 q hp𝒰 hq eU g hg
        (FibredSite.restrictSiteModules B S hS q hq .etale M) =
      (SheafOfModules.pushforward φg).obj
        (FibredSite.restrictSiteModules B S hS q hq .etale M) := rfl
  rw [h1, h2]
  exact ⟨(SheafOfModules.pushforwardComp φx ψ).app _ ≪≫
    (SheafOfModules.pushforwardNatIso φ₁ α').app _ ≪≫ (SheafOfModules.pushforwardCongr hring).app _⟩

end Restriction

end AlgebraicGeometry.Stack.FibredEquivalence

end
