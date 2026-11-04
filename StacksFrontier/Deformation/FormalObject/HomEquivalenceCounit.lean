module

public import StacksFrontier.Deformation.FormalObject.HomEquivalence
public import StacksFrontier.Deformation.FormalObject.HomEquivalenceUnit

/-!
# The counit of the completion adjunction on hom categories (Stacks 06HA)

For a category `p` cofibered in groupoids over Artinian local algebras and a category `q`
cofibered in groupoids over complete local algebras, restricting a morphism from `q` to the
formal objects of `p` along the inclusion of Artinian algebras, comparing by Tag 06SJ,
completing the result and precomposing with the unit recovers the original morphism.

## Main results

* `Deformation.completionHomCounitIso`: **Stacks 06HA**, the counit isomorphism
  `completionHomInverse ⋙ completionHomForward ≅ Functor.id`.

## Implementation notes

At an object `Y` and a level `n` the composite is the image under the restricted morphism of
the chosen pushforward of `Y` to the `n`-th adic truncation of its base.  Since the maximal
ideal of that truncation has vanishing `(n + 1)`-st power, the comparison of Tag 06SJ
evaluates it at level `n`, and the chosen inclusion of `Y` into the pushforward becomes an
isomorphism at level `n` because it lies over an isomorphism of Artinian algebras.  The
counit component is the resulting composite.

## References

* [Stacks Project, Tag 06HA](https://stacks.math.columbia.edu/tag/06HA)
-/

@[expose] public section

namespace Deformation

/-! ### Vanishing powers in adic truncations -/

section
open CategoryTheory IsLocalRing

universe u v w uG vG

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

namespace HomEquivalenceCounit

/-- The `(n + 1)`-st power of the maximal ideal of the `n`-th adic truncation vanishes. -/
public theorem maximalIdeal_adicTruncation_pow_eq_bot
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    maximalIdeal (AdicTruncation.obj R n) ^ (n + 1) = ⊥ := by
  let f : R →+* AdicTruncation.obj R n := (adicQuotientMap R n).hom.toRingHom
  rw [← IsLocalRing.map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
  exact fun _ hx => Ideal.Quotient.eq_zero_iff_mem.mpr hx

variable {G : Type uG} [Category.{vG} G]
  (q : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k) (hq : IsCofiberedInGroupoids q)

/-- The `n`-th adic truncation of a chosen adic quotient map is the canonical quotient map of
the `n`-th truncation itself. -/
public theorem adicTruncation_map_baseMap (Y : G) (n : ℕ) :
    (AdicTruncation.functor n).map ((adicPushforwardChoice q hq).baseMap Y n) =
      artinianAdicQuotient ((AdicTruncation.functor n).obj (q.obj Y)) n := by
  refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun x => ?_)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := AdicTruncation.ideal (q.obj Y) n) x
  rfl

/-- The `n`-th adic truncation of a chosen adic quotient map is an isomorphism. -/
public theorem adicTruncation_map_baseMap_isIso (Y : G) (n : ℕ) :
    IsIso ((AdicTruncation.functor n).map ((adicPushforwardChoice q hq).baseMap Y n)) := by
  rw [adicTruncation_map_baseMap q hq Y n]
  exact artinianAdicQuotient_isIso _ n (maximalIdeal_adicTruncation_pow_eq_bot (q.obj Y) n)

/-- Transport of objects in a restricted category acts by transport on the underlying
objects. -/
public theorem restriction_eqToHom_obj {X Y : Restriction q} (h : X = Y) :
    (eqToHom h).obj = eqToHom (congrArg Restriction.obj h) := by
  cases h
  rfl

/-- The level-`n` component of the unit on a morphism, transported to the chosen
pushforwards. -/
public noncomputable def unitMap {Y Y' : G} (u : Y ⟶ Y') (n : ℕ) :
    (adicPushforwardChoice q hq).level Y n ⟶ (adicPushforwardChoice q hq).level Y' n :=
  eqToHom ((completionUnit q hq).level Y n).symm ≫
    ((completionUnit q hq).functor.map u).app n ≫
    eqToHom ((completionUnit q hq).level Y' n)

/-- The chosen inclusions are natural for the unit. -/
public theorem inclusion_comp_unitMap {Y Y' : G} (u : Y ⟶ Y') (n : ℕ) :
    (adicPushforwardChoice q hq).inclusion Y n ≫ (unitMap q hq u n).obj =
      u ≫ (adicPushforwardChoice q hq).inclusion Y' n := by
  simpa [unitMap, HomEquivalenceUnit.restriction_comp_obj, restriction_eqToHom_obj,
    Category.assoc] using (completionUnit q hq).map u n

/-- The transition map of the unit, transported to the chosen pushforwards. -/
public noncomputable def unitTransition (Y : G) (n : ℕ) :
    (adicPushforwardChoice q hq).level Y (n + 1) ⟶
      (adicPushforwardChoice q hq).level Y n :=
  eqToHom ((completionUnit q hq).level Y (n + 1)).symm ≫
    ((completionUnit q hq).functor.obj Y).transition n ≫
    eqToHom ((completionUnit q hq).level Y n)

/-- The chosen inclusions are compatible with the transition maps of the unit. -/
public theorem inclusion_comp_unitTransition (Y : G) (n : ℕ) :
    (adicPushforwardChoice q hq).inclusion Y (n + 1) ≫ (unitTransition q hq Y n).obj =
      (adicPushforwardChoice q hq).inclusion Y n := by
  simpa [unitTransition, HomEquivalenceUnit.restriction_comp_obj, restriction_eqToHom_obj,
    Category.assoc] using (completionUnit q hq).transition Y n

end HomEquivalenceCounit

end

/-! ### The counit -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF uG vG

-- Objects of a based category are reached through `CategoryTheory.BasedCategory.ofFunctor`,
-- which the default transparency setting does not see through, so the proofs below cannot
-- identify the two spellings of an object without this option.
set_option backward.isDefEq.respectTransparency false

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
  (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
variable {G : Type uG} [Category.{vG} G]
  (q : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)

namespace HomEquivalenceCounit

variable (hp : IsCofiberedInGroupoids p) (hq : IsCofiberedInGroupoids q)
  (ψ : BasedFunctor (BasedCategory.ofFunctor q)
    (BasedCategory.ofFunctor (FormalObject.projection (p := p))))

/-- The Artinian base of the restricted pullback of the chosen pushforward at level `n` has
vanishing `(m + 1)`-st power of its maximal ideal for every `m ≥ n`. -/
public theorem pullback_maximalIdeal_pow_eq_bot (Y : G) {n m : ℕ} (hnm : n ≤ m) :
    maximalIdeal ((restrictedPullbackMap p q hp ψ).obj
        ((adicPushforwardChoice q hq).level Y n)).fst ^ (m + 1) = ⊥ :=
  maximalIdeal_pow_succ_eq_bot_of_le _ hnm
    (maximalIdeal_adicTruncation_pow_eq_bot (q.obj Y) n)

/-- The transition map of the unit is its transport to the chosen pushforwards. -/
public theorem unitTransition_eq' (Y : G) (n : ℕ) :
    ((completionUnit q hq).functor.obj Y).transition n = unitTransition q hq Y n := by
  simp [unitTransition]

/-- The level-`n` component of the unit on a morphism is its transport to the chosen
pushforwards. -/
public theorem unitMap_eq' {Y Y' : G} (u : Y ⟶ Y') (n : ℕ) :
    ((completionUnit q hq).functor.map u).app n = unitMap q hq u n := by
  simp [unitMap]

/-- The base map of the image under `ψ` of a chosen inclusion, expressed through the chosen
adic quotient map. -/
private theorem map_inclusion_base_eq (Y : G) (n : ℕ)
    [q.IsHomLift ((adicPushforwardChoice q hq).baseMap Y n)
      ((adicPushforwardChoice q hq).inclusion Y n)] :
    (ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).base =
      eqToHom (ψ.w_obj Y) ≫
        (eqToHom (IsHomLift.domain_eq q ((adicPushforwardChoice q hq).baseMap Y n)
            ((adicPushforwardChoice q hq).inclusion Y n)) ≫
          (adicPushforwardChoice q hq).baseMap Y n ≫
          eqToHom (IsHomLift.codomain_eq q ((adicPushforwardChoice q hq).baseMap Y n)
            ((adicPushforwardChoice q hq).inclusion Y n)).symm) ≫
        eqToHom (ψ.w_obj (((adicPushforwardChoice q hq).level Y n).obj)).symm := by
  refine (Functor.congr_hom ψ.w _).trans ?_
  have h2 := IsHomLift.fac' q ((adicPushforwardChoice q hq).baseMap Y n)
    ((adicPushforwardChoice q hq).inclusion Y n)
  exact congrArg (fun f => eqToHom (ψ.w_obj Y) ≫ f ≫ _) h2

/-- The base map of the image under `ψ` of a chosen inclusion is an isomorphism after
truncation. -/
public theorem map_inclusion_base_truncation_isIso (Y : G) (n : ℕ) :
    IsIso ((AdicTruncation.functor n).map
      ((ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).base)) := by
  have := (adicPushforwardChoice q hq).inclusion_lift Y n
  rw [map_inclusion_base_eq p q hq ψ Y n]
  simp only [Functor.map_comp, eqToHom_map]
  have := adicTruncation_map_baseMap_isIso q hq Y n
  infer_instance

include hp in
/-- The level-`n` component of the image under `ψ` of a chosen inclusion is an
isomorphism. -/
public theorem map_inclusion_app_isIso (Y : G) (n : ℕ) :
    IsIso ((ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).app n) := by
  have := map_inclusion_base_truncation_isIso p q hq ψ Y n
  exact isIso_of_isCofiberedInGroupoids_of_base_isIso hp _ _
    ((ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).app_lift n)

/-- The level-`n` component of the image under `ψ` of a chosen inclusion, as an
isomorphism. -/
public noncomputable def inclusionLevelIso (Y : G) (n : ℕ) :
    (ψ.obj Y).level n ≅
      (ψ.obj (((adicPushforwardChoice q hq).level Y n).obj)).level n :=
  haveI := map_inclusion_app_isIso p q hp hq ψ Y n
  asIso ((ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).app n)

/-- The forward direction of `inclusionLevelIso` is the level-`n` component itself. -/
@[simp]
public theorem inclusionLevelIso_hom (Y : G) (n : ℕ) :
    (inclusionLevelIso p q hp hq ψ Y n).hom =
      (ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).app n := rfl

/-- Evaluation of the comparison of Tag 06SJ at a stabilized level is the evaluation leg. -/
public theorem objIsoLevel_hom_eq_evaluationLeg
    (X : CategoricalPullback (restrictionCompletionEquivalence p hp).inclusion
      (FormalObject.projection (p := p))) (n : ℕ)
    (hn : maximalIdeal X.fst ^ (n + 1) = ⊥) :
    ((restrictionCompletionEquivalence p hp).objIsoLevel X n hn).hom =
      FormalEvaluation.evaluationLeg p hp X n := by
  rw [FormalEvaluation.evaluationLeg_atLevel p hp X n hn]
  rfl

/-- Evaluation of the comparison of Tag 06SJ lies over the composite of the canonical
quotient map with the comparison of bases. -/
public theorem objIsoLevel_isHomLift
    (X : CategoricalPullback (restrictionCompletionEquivalence p hp).inclusion
      (FormalObject.projection (p := p))) (n : ℕ)
    (hn : maximalIdeal X.fst ^ (n + 1) = ⊥) :
    p.IsHomLift (FormalEvaluation.evaluationBaseLeg X n)
      ((restrictionCompletionEquivalence p hp).objIsoLevel X n hn).hom := by
  rw [objIsoLevel_hom_eq_evaluationLeg p hp X n hn]
  exact FormalEvaluation.evaluationLeg_lift p hp X n

/-- The evaluation leg of the restricted pullback of a chosen pushforward is the truncation
of the image under `ψ` of the chosen inclusion. -/
public theorem evaluationBaseLeg_eq (Y : G) (n : ℕ)
    (h : ((restrictedPullbackMap p q hp ψ).obj
          ((adicPushforwardChoice q hq).level Y n)).fst =
      (AdicTruncation.functor n).obj ((ψ.obj Y).base)) :
    FormalEvaluation.evaluationBaseLeg
        ((restrictedPullbackMap p q hp ψ).obj
          ((adicPushforwardChoice q hq).level Y n)) n =
      eqToHom h ≫ (AdicTruncation.functor n).map
        ((ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).base) := by
  have := (adicPushforwardChoice q hq).inclusion_lift Y n
  rw [map_inclusion_base_eq p q hq ψ Y n]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [adicTruncation_map_baseMap q hq Y n]
  have hiso : ((restrictedPullbackMap p q hp ψ).obj
        ((adicPushforwardChoice q hq).level Y n)).iso.hom =
      eqToHom ((((adicPushforwardChoice q hq).level Y n).obj_eq).symm.trans
        (ψ.w_obj (((adicPushforwardChoice q hq).level Y n).obj)).symm) := rfl
  simp only [FormalEvaluation.evaluationBaseLeg, artinianAdicQuotient, hiso, eqToHom_map]
  rfl

/-- The level-`n` component of the counit at `Y`: evaluate the comparison of Tag 06SJ at
level `n`, then invert the chosen inclusion there. -/
public noncomputable def levelHom (Y : G) (n : ℕ) :
    (restrictionCompletionEquivalence p hp).can.obj
        ((restrictedPullbackMap p q hp ψ).obj
          ((adicPushforwardChoice q hq).level Y n)) ⟶
      (ψ.obj Y).level n :=
  ((restrictionCompletionEquivalence p hp).objIsoLevel
      ((restrictedPullbackMap p q hp ψ).obj
        ((adicPushforwardChoice q hq).level Y n)) n
      (pullback_maximalIdeal_pow_eq_bot p q hp hq ψ Y le_rfl)).hom ≫
    (inclusionLevelIso p q hp hq ψ Y n).inv

/-- `levelHom` unfolds to the evaluation of Tag 06SJ followed by the inverse of the chosen
inclusion. -/
public theorem levelHom_eq (Y : G) (n : ℕ) :
    levelHom p q hp hq ψ Y n =
      ((restrictionCompletionEquivalence p hp).objIsoLevel
        ((restrictedPullbackMap p q hp ψ).obj
          ((adicPushforwardChoice q hq).level Y n)) n
        (pullback_maximalIdeal_pow_eq_bot p q hp hq ψ Y le_rfl)).hom ≫
      (inclusionLevelIso p q hp hq ψ Y n).inv := rfl

/-- The level-`n` component of the counit lies over the identity: its image under `p` is the
transport along the identification of the two Artinian bases. -/
public theorem levelHom_map_eq (Y : G) (n : ℕ)
    (h : p.obj ((restrictionCompletionEquivalence p hp).can.obj
          ((restrictedPullbackMap p q hp ψ).obj
            ((adicPushforwardChoice q hq).level Y n))) =
      p.obj ((ψ.obj Y).level n)) :
    p.map (levelHom p q hp hq ψ Y n) = eqToHom h := by
  have hAA : ((restrictedPullbackMap p q hp ψ).obj
        ((adicPushforwardChoice q hq).level Y n)).fst =
      (AdicTruncation.functor n).obj ((ψ.obj Y).base) :=
    (congrArg (AdicTruncation.functor n).obj (ψ.w_obj Y)).symm
  have := objIsoLevel_isHomLift p hp
    ((restrictedPullbackMap p q hp ψ).obj ((adicPushforwardChoice q hq).level Y n)) n
    (pullback_maximalIdeal_pow_eq_bot p q hp hq ψ Y le_rfl)
  have := map_inclusion_base_truncation_isIso p q hq ψ Y n
  have : p.IsHomLift (asIso ((AdicTruncation.functor n).map
      ((ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).base))).hom
      (inclusionLevelIso p q hp hq ψ Y n).hom :=
    (ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).app_lift n
  have := IsHomLift.inv_lift_inv p (asIso ((AdicTruncation.functor n).map
      ((ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).base)))
    (inclusionLevelIso p q hp hq ψ Y n)
  have key : FormalEvaluation.evaluationBaseLeg
        ((restrictedPullbackMap p q hp ψ).obj
          ((adicPushforwardChoice q hq).level Y n)) n ≫
      (asIso ((AdicTruncation.functor n).map
        ((ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).base))).inv =
      eqToHom hAA := by
    rw [evaluationBaseLeg_eq p q hp hq ψ Y n hAA, asIso_inv, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have hlift : p.IsHomLift (eqToHom hAA) (levelHom p q hp hq ψ Y n) := by
    rw [levelHom_eq, ← key]
    exact IsHomLift.comp p _ _ _ _
  have := hlift
  rw [IsHomLift.fac' p (eqToHom hAA) (levelHom p q hp hq ψ Y n)]
  simp only [eqToHom_trans]

/-- The base of the comparison of Tag 06SJ applied to the restricted pullback agrees with the
base of the level of `ψ.obj Y`. -/
public theorem can_obj_base_eq (Y : G) (n : ℕ) :
    p.obj ((restrictionCompletionEquivalence p hp).can.obj
        ((restrictedPullbackMap p q hp ψ).obj
          ((adicPushforwardChoice q hq).level Y n))) =
      p.obj ((ψ.obj Y).level n) := by
  have hw : (ψ.obj Y).base = q.obj Y := ψ.w_obj Y
  rw [(ψ.obj Y).level_eq n, hw]
  exact Functor.congr_obj (restrictionCompletionEquivalence_can_comp_eq p hp) _

/-- Composition of morphisms of formal objects acts levelwise. -/
public theorem formalObject_comp_app {X Y Z : FormalObject p} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) : (f ≫ g).app n = f.app n ≫ g.app n := rfl

/-- The formal-object component of the restricted pullback of an object. -/
public theorem restrictedPullbackMap_obj_snd (X : Restriction q) :
    ((restrictedPullbackMap p q hp ψ).obj X).snd = ψ.obj X.obj := rfl

/-- The formal-object component of the restricted pullback of a morphism. -/
public theorem restrictedPullbackMap_map_snd {X Y : Restriction q} (g : X ⟶ Y) :
    ((restrictedPullbackMap p q hp ψ).map g).snd = ψ.map g.obj := rfl

/-- Composition of morphisms of formal objects acts on the bases. -/
public theorem formalObject_comp_base {X Y Z : FormalObject p} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base := rfl

/-- The level components of the counit are natural in the morphism being restricted. -/
public theorem levelHom_natTrans
    {φ χ : BasedFunctor (BasedCategory.ofFunctor q)
      (BasedCategory.ofFunctor (FormalObject.projection (p := p)))} (t : φ ⟶ χ)
    (Y : G) (n : ℕ) :
    (restrictionCompletionEquivalence p hp).can.map
        ((restrictedPullbackNatTrans p q hp t).toNatTrans.app
          ((adicPushforwardChoice q hq).level Y n)) ≫ levelHom p q hp hq χ Y n =
      levelHom p q hp hq φ Y n ≫ (t.toNatTrans.app Y).app n := by
  have hnat := (restrictionCompletionEquivalence p hp).objIsoLevel_naturality
    (X := (restrictedPullbackMap p q hp φ).obj ((adicPushforwardChoice q hq).level Y n))
    (Y := (restrictedPullbackMap p q hp χ).obj ((adicPushforwardChoice q hq).level Y n))
    ((restrictedPullbackNatTrans p q hp t).toNatTrans.app
      ((adicPushforwardChoice q hq).level Y n)) n
    (pullback_maximalIdeal_pow_eq_bot p q hp hq φ Y le_rfl)
    (pullback_maximalIdeal_pow_eq_bot p q hp hq χ Y le_rfl)
  have step2 : (inclusionLevelIso p q hp hq φ Y n).hom ≫
      ((restrictedPullbackNatTrans p q hp t).toNatTrans.app
        ((adicPushforwardChoice q hq).level Y n)).snd.app n =
      (t.toNatTrans.app Y).app n ≫ (inclusionLevelIso p q hp hq χ Y n).hom := by
    have h : (φ.map ((adicPushforwardChoice q hq).inclusion Y n)).app n ≫
        (t.toNatTrans.app (((adicPushforwardChoice q hq).level Y n).obj)).app n =
      (t.toNatTrans.app Y).app n ≫
        (χ.map ((adicPushforwardChoice q hq).inclusion Y n)).app n := by
      rw [← formalObject_comp_app, ← formalObject_comp_app,
        t.toNatTrans.naturality ((adicPushforwardChoice q hq).inclusion Y n)]
    exact h
  rw [levelHom_eq, levelHom_eq]
  simp only [← Category.assoc]
  rw [hnat]
  simp only [Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp]
  calc (inclusionLevelIso p q hp hq φ Y n).hom ≫
        ((restrictedPullbackNatTrans p q hp t).toNatTrans.app
          ((adicPushforwardChoice q hq).level Y n)).snd.app n ≫
        (inclusionLevelIso p q hp hq χ Y n).inv
      = ((inclusionLevelIso p q hp hq φ Y n).hom ≫
          ((restrictedPullbackNatTrans p q hp t).toNatTrans.app
            ((adicPushforwardChoice q hq).level Y n)).snd.app n) ≫
        (inclusionLevelIso p q hp hq χ Y n).inv := by simp only [Category.assoc]
    _ = ((t.toNatTrans.app Y).app n ≫ (inclusionLevelIso p q hp hq χ Y n).hom) ≫
        (inclusionLevelIso p q hp hq χ Y n).inv := by rw [step2]
    _ = (t.toNatTrans.app Y).app n := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The level components of the counit are compatible with the transition maps. -/
public theorem levelHom_transition (Y : G) (n : ℕ) :
    ((completionHomInverse p q hp).obj ψ).map (unitTransition q hq Y n) ≫
        levelHom p q hp hq ψ Y n =
      levelHom p q hp hq ψ Y (n + 1) ≫ (ψ.obj Y).transition n := by
  have hmapeq : ((completionHomInverse p q hp).obj ψ).map (unitTransition q hq Y n) =
      (restrictionCompletionEquivalence p hp).can.map
        ((restrictedPullbackMap p q hp ψ).map (unitTransition q hq Y n)) := rfl
  have hnat := (restrictionCompletionEquivalence p hp).objIsoLevel_naturality
    ((restrictedPullbackMap p q hp ψ).map (unitTransition q hq Y n)) (n + 1)
    (pullback_maximalIdeal_pow_eq_bot p q hp hq ψ Y (n := n + 1) le_rfl)
    (pullback_maximalIdeal_pow_eq_bot p q hp hq ψ Y (Nat.le_succ n))
  have htr := (restrictionCompletionEquivalence p hp).objIsoLevel_transition
    ((restrictedPullbackMap p q hp ψ).obj ((adicPushforwardChoice q hq).level Y n)) n
    (pullback_maximalIdeal_pow_eq_bot p q hp hq ψ Y le_rfl)
    (pullback_maximalIdeal_pow_eq_bot p q hp hq ψ Y (Nat.le_succ n))
  have step2 : (inclusionLevelIso p q hp hq ψ Y (n + 1)).hom ≫
      ((restrictedPullbackMap p q hp ψ).map (unitTransition q hq Y n)).snd.app (n + 1) ≫
        ((restrictedPullbackMap p q hp ψ).obj
          ((adicPushforwardChoice q hq).level Y n)).snd.transition n =
      (ψ.obj Y).transition n ≫ (inclusionLevelIso p q hp hq ψ Y n).hom := by
    calc (inclusionLevelIso p q hp hq ψ Y (n + 1)).hom ≫
          ((restrictedPullbackMap p q hp ψ).map (unitTransition q hq Y n)).snd.app (n + 1) ≫
          ((restrictedPullbackMap p q hp ψ).obj
            ((adicPushforwardChoice q hq).level Y n)).snd.transition n
        = (ψ.map ((adicPushforwardChoice q hq).inclusion Y (n + 1)) ≫
              ψ.map ((unitTransition q hq Y n).obj)).app (n + 1) ≫
            (ψ.obj (((adicPushforwardChoice q hq).level Y n).obj)).transition n := by
          rw [formalObject_comp_app]
          simp only [Category.assoc]
          rfl
      _ = (ψ.map ((adicPushforwardChoice q hq).inclusion Y (n + 1) ≫
              (unitTransition q hq Y n).obj)).app (n + 1) ≫
            (ψ.obj (((adicPushforwardChoice q hq).level Y n).obj)).transition n := by
          rw [ψ.toFunctor.map_comp]
      _ = (ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).app (n + 1) ≫
            (ψ.obj (((adicPushforwardChoice q hq).level Y n).obj)).transition n := by
          rw [inclusion_comp_unitTransition q hq Y n]
      _ = (ψ.obj Y).transition n ≫ (inclusionLevelIso p q hp hq ψ Y n).hom :=
          ((ψ.map ((adicPushforwardChoice q hq).inclusion Y n)).naturality n).symm
  rw [hmapeq, levelHom_eq, levelHom_eq, ← htr]
  simp only [← Category.assoc]
  rw [hnat]
  simp only [Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp]
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    step2 =≫ (inclusionLevelIso p q hp hq ψ Y n).inv

/-- The complete local algebra underlying the composite at `Y` is the one underlying
`ψ.obj Y`. -/
public theorem counitSource_base (Y : G) :
    ((completionMap ((completionHomInverse p q hp).obj ψ)).obj
        ((completionUnit q hq).functor.obj Y)).base = (ψ.obj Y).base :=
  (completionMap_obj_base _ _).trans
    ((Functor.congr_obj (completionUnit q hq).comp_projection Y).trans (ψ.w_obj Y).symm)

/-- Level `n` of the composite at `Y` is the comparison of Tag 06SJ applied to the restricted
pullback of the chosen pushforward. -/
public theorem counitSource_level (Y : G) (n : ℕ) :
    ((completionMap ((completionHomInverse p q hp).obj ψ)).obj
        ((completionUnit q hq).functor.obj Y)).level n =
      (restrictionCompletionEquivalence p hp).can.obj
        ((restrictedPullbackMap p q hp ψ).obj
          ((adicPushforwardChoice q hq).level Y n)) :=
  (completionMap_obj_level _ _ n).trans
    (congrArg ((completionHomInverse p q hp).obj ψ).obj
      ((completionUnit q hq).level Y n))

/-- The component of the counit at `Y`, as a morphism of formal objects. -/
public noncomputable def counitHom (Y : G) :
    (completionMap ((completionHomInverse p q hp).obj ψ)).obj
        ((completionUnit q hq).functor.obj Y) ⟶ ψ.obj Y where
  base := eqToHom (counitSource_base p q hp hq ψ Y)
  app n := eqToHom (counitSource_level p q hp hq ψ Y n) ≫ levelHom p q hp hq ψ Y n
  app_lift n := by
    refine IsHomLift.of_fac' p _ _
      (((completionMap ((completionHomInverse p q hp).obj ψ)).obj
        ((completionUnit q hq).functor.obj Y)).level_eq n)
      ((ψ.obj Y).level_eq n) ?_
    rw [Functor.map_comp, eqToHom_map,
      levelHom_map_eq p q hp hq ψ Y n (can_obj_base_eq p q hp hq ψ Y n), eqToHom_map]
    simp only [eqToHom_trans]
  naturality n := by
    rw [completionMap_obj_transition, unitTransition_eq' q hq Y n]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [levelHom_transition p q hp hq ψ Y n]

/-- The level components of the counit are natural in the object. -/
public theorem levelHom_naturality {Y Y' : G} (u : Y ⟶ Y') (n : ℕ) :
    ((completionHomInverse p q hp).obj ψ).map (unitMap q hq u n) ≫
        levelHom p q hp hq ψ Y' n =
      levelHom p q hp hq ψ Y n ≫ (ψ.map u).app n := by
  have hmapeq : ((completionHomInverse p q hp).obj ψ).map (unitMap q hq u n) =
      (restrictionCompletionEquivalence p hp).can.map
        ((restrictedPullbackMap p q hp ψ).map (unitMap q hq u n)) := rfl
  have hnat := (restrictionCompletionEquivalence p hp).objIsoLevel_naturality
    ((restrictedPullbackMap p q hp ψ).map (unitMap q hq u n)) n
    (pullback_maximalIdeal_pow_eq_bot p q hp hq ψ Y le_rfl)
    (pullback_maximalIdeal_pow_eq_bot p q hp hq ψ Y' le_rfl)
  have step2 : (inclusionLevelIso p q hp hq ψ Y n).hom ≫
      ((restrictedPullbackMap p q hp ψ).map (unitMap q hq u n)).snd.app n =
      (ψ.map u).app n ≫ (inclusionLevelIso p q hp hq ψ Y' n).hom := by
    calc (inclusionLevelIso p q hp hq ψ Y n).hom ≫
          ((restrictedPullbackMap p q hp ψ).map (unitMap q hq u n)).snd.app n
        = (ψ.map ((adicPushforwardChoice q hq).inclusion Y n) ≫
            ψ.map ((unitMap q hq u n).obj)).app n := rfl
      _ = (ψ.map ((adicPushforwardChoice q hq).inclusion Y n ≫
            (unitMap q hq u n).obj)).app n := by rw [ψ.toFunctor.map_comp]
      _ = (ψ.map (u ≫ (adicPushforwardChoice q hq).inclusion Y' n)).app n := by
          rw [inclusion_comp_unitMap q hq u n]
      _ = (ψ.map u ≫ ψ.map ((adicPushforwardChoice q hq).inclusion Y' n)).app n := by
          rw [ψ.toFunctor.map_comp]
      _ = (ψ.map u).app n ≫ (inclusionLevelIso p q hp hq ψ Y' n).hom := rfl
  rw [hmapeq, levelHom_eq, levelHom_eq]
  simp only [← Category.assoc]
  rw [hnat]
  simp only [Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp, ← Category.assoc, step2, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The counit components are natural in the object. -/
public theorem counitHom_naturality {Y Y' : G} (u : Y ⟶ Y') :
    (completionMap ((completionHomInverse p q hp).obj ψ)).map
        ((completionUnit q hq).functor.map u) ≫ counitHom p q hp hq ψ Y' =
      counitHom p q hp hq ψ Y ≫ ψ.map u := by
  refine FormalObject.Hom.ext ?_ ?_
  · have h1 := completionMap_map_base ((completionHomInverse p q hp).obj ψ)
      ((completionUnit q hq).functor.map u)
    have h2 : ((completionUnit q hq).functor.map u).base =
        eqToHom (Functor.congr_obj (completionUnit q hq).comp_projection Y) ≫ q.map u ≫
          eqToHom (Functor.congr_obj (completionUnit q hq).comp_projection Y').symm :=
      Functor.congr_hom (completionUnit q hq).comp_projection u
    have h3 : (ψ.map u).base =
        eqToHom (ψ.w_obj Y) ≫ q.map u ≫ eqToHom (ψ.w_obj Y').symm :=
      Functor.congr_hom ψ.w u
    show ((completionMap ((completionHomInverse p q hp).obj ψ)).map
          ((completionUnit q hq).functor.map u)).base ≫
        eqToHom (counitSource_base p q hp hq ψ Y') =
      eqToHom (counitSource_base p q hp hq ψ Y) ≫ (ψ.map u).base
    rw [h1, h2, h3]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  · intro n
    show ((completionMap ((completionHomInverse p q hp).obj ψ)).map
          ((completionUnit q hq).functor.map u)).app n ≫
        (eqToHom (counitSource_level p q hp hq ψ Y' n) ≫ levelHom p q hp hq ψ Y' n) =
      (eqToHom (counitSource_level p q hp hq ψ Y n) ≫ levelHom p q hp hq ψ Y n) ≫
        (ψ.map u).app n
    rw [completionMap_map_app, unitMap_eq' q hq u n]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [levelHom_naturality p q hp hq ψ u n]

/-- Each counit component is an isomorphism. -/
public theorem counitHom_isIso (Y : G) : IsIso (counitHom p q hp hq ψ Y) := by
  have hlift : (FormalObject.projection (p := p)).IsHomLift
      (eqToHom (counitSource_base p q hp hq ψ Y)) (counitHom p q hp hq ψ Y) := by
    refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  exact isIso_of_isCofiberedInGroupoids_of_base_isIso
    (formalObjectProjection_isCofiberedInGroupoids p hp) _ _ hlift

/-- Each counit component lies over the identity of the base. -/
public theorem counitHom_isHomLift (Y : G) :
    (FormalObject.projection (p := p)).IsHomLift (𝟙 (q.obj Y))
      (counitHom p q hp hq ψ Y) := by
  refine IsHomLift.of_fac' _ _ _
    ((completionMap_obj_base ((completionHomInverse p q hp).obj ψ)
      ((completionUnit q hq).functor.obj Y)).trans
      (Functor.congr_obj (completionUnit q hq).comp_projection Y))
    (ψ.w_obj Y) ?_
  show (counitHom p q hp hq ψ Y).base = _
  simp only [Category.id_comp, eqToHom_trans]
  rfl

/-- The counit at `ψ`: the composite of the two directions of Tag 06HA at `ψ` is
isomorphic to `ψ`. -/
public noncomputable def counitIso :
    (completionHomInverse p q hp ⋙ completionHomForward p q hq).obj ψ ≅ ψ :=
  haveI : ∀ Y : G, IsIso (counitHom p q hp hq ψ Y) := counitHom_isIso p q hp hq ψ
  CategoryTheory.BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun Y => asIso (counitHom p q hp hq ψ Y))
      (fun u => counitHom_naturality p q hp hq ψ u))
    (fun Y => counitHom_isHomLift p q hp hq ψ Y)

/-- The components of the counit are the chosen morphisms of formal objects. -/
public theorem counitIso_hom_app (Y : G) :
    (counitIso p q hp hq ψ).hom.toNatTrans.app Y = counitHom p q hp hq ψ Y := rfl

end HomEquivalenceCounit

open HomEquivalenceCounit

variable (hp : IsCofiberedInGroupoids p) (hq : IsCofiberedInGroupoids q)

/-- Restricting a morphism from `q` to the formal objects of `p` along the inclusion of
Artinian local algebras, comparing by Tag 06SJ, completing the result and precomposing with
the unit recovers the original morphism, naturally in that morphism. -/
public noncomputable def completionHomCounitIso :
    completionHomInverse p q hp ⋙ completionHomForward p q hq ≅ Functor.id _ :=
  NatIso.ofComponents (fun φ => counitIso p q hp hq φ) (by
    intro φ χ t
    apply BasedNatTrans.homCategory.ext
    apply NatTrans.ext
    funext Y
    have hc : ((completionHomInverse p q hp ⋙
          completionHomForward p q hq).map t).toNatTrans.app Y =
        (completionNatTrans ((completionHomInverse p q hp).map t)).toNatTrans.app
          ((completionUnit q hq).functor.obj Y) := rfl
    refine FormalObject.Hom.ext ?_ ?_
    · have hb : (t.toNatTrans.app Y).base =
          eqToHom (φ.w_obj Y) ≫ eqToHom (χ.w_obj Y).symm :=
        basedNatTrans_app_over t Y
      change (((completionHomInverse p q hp ⋙
            completionHomForward p q hq).map t).toNatTrans.app Y ≫
          counitHom p q hp hq χ Y).base =
        (counitHom p q hp hq φ Y ≫ t.toNatTrans.app Y).base
      rw [formalObject_comp_base, formalObject_comp_base, hc,
        completionNatTrans_app_base, hb]
      change (eqToHom _ ≫ eqToHom _) ≫ eqToHom (counitSource_base p q hp hq χ Y) =
        eqToHom (counitSource_base p q hp hq φ Y) ≫ eqToHom _ ≫ eqToHom _
      simp only [eqToHom_trans]
    · intro n
      change (((completionHomInverse p q hp ⋙
            completionHomForward p q hq).map t).toNatTrans.app Y ≫
          counitHom p q hp hq χ Y).app n =
        (counitHom p q hp hq φ Y ≫ t.toNatTrans.app Y).app n
      rw [formalObject_comp_app, formalObject_comp_app, hc,
        completionNatTrans_app_level]
      change (eqToHom _ ≫ ((completionHomInverse p q hp).map t).toNatTrans.app
            (((completionUnit q hq).functor.obj Y).level n) ≫ eqToHom _) ≫
          (eqToHom (counitSource_level p q hp hq χ Y n) ≫ levelHom p q hp hq χ Y n) =
        (eqToHom (counitSource_level p q hp hq φ Y n) ≫ levelHom p q hp hq φ Y n) ≫
          (t.toNatTrans.app Y).app n
      have hs : ((completionHomInverse p q hp).map t).toNatTrans.app
            (((completionUnit q hq).functor.obj Y).level n) =
          (restrictionCompletionEquivalence p hp).can.map
            ((restrictedPullbackNatTrans p q hp t).toNatTrans.app
              ((adicPushforwardChoice q hq).level Y n)) := rfl
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [hs, levelHom_natTrans p q hp hq t Y n])

end

end Deformation

end
