module

public import StacksFrontier.Deformation.FormalObject.HomEquivalence

/-!
# The unit of the hom equivalence (Stacks 06HA)

For a category cofibered in groupoids over complete local algebras and one over Artinian
local algebras, the hom category of morphisms out of the restriction is compared with the
hom category of morphisms into the completion.  This file constructs the unit of that
comparison: the identity of the first hom category is naturally isomorphic to the
composite of the two comparison functors.

## Main definitions

* `Deformation.HomEquivalenceUnit.unitHom` is the unit arrow of Tag 06HA at an object of
  the restriction, evaluated at a level: the chosen pushforward arrow together with the
  adic quotient map of the Artinian base.
* `Deformation.HomEquivalenceUnit.unitComponent` is the resulting component of the unit,
  obtained by composing with the inverse of the evaluation comparison of Tag 06SJ.

## Main results

* `Deformation.completionHomUnitIso`: **Stacks 06HA** (the unit of the hom equivalence).

## Implementation notes

Over an Artinian base the maximal-adic filtration vanishes from some level on, and from
that level the unit arrow is an isomorphism: its base component is the quotient by the
zero ideal, and the cofibered hypothesis upgrades an arrow over an isomorphism to an
isomorphism.  The component of the unit is therefore defined at the least such level,
`vanishingIndex`, and is shown to be independent of the level chosen; naturality in the
object is then checked at a common level, and naturality in the morphism at the level of
the single object involved.

## References

* [Stacks Project, Tag 06HA](https://stacks.math.columbia.edu/tag/06HA)
* [Stacks Project, Tag 06SJ](https://stacks.math.columbia.edu/tag/06SJ)
-/

@[expose] public section

namespace Deformation

namespace HomEquivalenceUnit

/-! ### Adic quotient maps on an Artinian base -/

section
open CategoryTheory IsLocalRing

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- On an Artinian local algebra the adic quotient map of complete local algebras is the
image of the Artinian one. -/
public theorem adicQuotientMap_eq_map (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (m : ℕ) :
    adicQuotientMap (artinianToComplete.obj A) m =
      artinianToComplete.map (artinianAdicQuotient A m) := by
  apply CompleteLocalAlgCat.Hom.ext
  rfl

/-- The compatibility, over an identification of the complete base, between the Artinian
adic quotient map and the adic quotient map of complete local algebras. -/
public theorem eqToHom_comp_map_artinianAdicQuotient
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (h : R = artinianToComplete.obj A) (m : ℕ)
    {T : ArtinianLocalAlgCat.{u, v, w} Λ k} {S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (e₀ : R = R)
    (e₁ : (AdicTruncation.functor m).obj (artinianToComplete.obj A) = T)
    (e₂ : artinianToComplete.obj ((AdicTruncation.functor m).obj R) = S)
    (e₃ : S = artinianToComplete.obj T) :
    eqToHom h ≫ artinianToComplete.map (artinianAdicQuotient A m ≫ eqToHom e₁) =
      (eqToHom e₀ ≫ adicQuotientMap R m ≫ eqToHom e₂) ≫ eqToHom e₃ := by
  subst h
  subst e₁
  subst e₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (adicQuotientMap_eq_map A m).symm

/-- Once a power of the maximal ideal vanishes, the adic quotient map of the associated
complete local algebra is an isomorphism. -/
public theorem adicQuotientMap_isIso {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k} (h : R = artinianToComplete.obj A) (m : ℕ)
    (hm : maximalIdeal A ^ (m + 1) = ⊥) : IsIso (adicQuotientMap R m) := by
  subst h
  have := artinianAdicQuotient_isIso A m hm
  rw [adicQuotientMap_eq_map]
  infer_instance

/-- Transported along an identification of the complete base, the Artinian adic quotient
maps are compatible with the adic transition maps. -/
public theorem artinianAdicQuotient_transition
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (h : R = artinianToComplete.obj A) (n : ℕ)
    {T : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (e₁ : (AdicTruncation.functor (n + 1)).obj (artinianToComplete.obj A) =
      (AdicTruncation.functor (n + 1)).obj R)
    (e₂ : (AdicTruncation.functor n).obj R = T)
    (e₃ : (AdicTruncation.functor n).obj (artinianToComplete.obj A) = T) :
    artinianAdicQuotient A (n + 1) ≫ eqToHom e₁ ≫
        AdicTruncation.transition R n ≫ eqToHom e₂ =
      artinianAdicQuotient A n ≫ eqToHom e₃ := by
  subst h
  subst e₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact _root_.Deformation.artinianAdicQuotient_transition A n

/-- Transported along identifications of the complete bases, the Artinian adic quotient
maps are natural. -/
public theorem artinianAdicQuotient_naturality
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k} {R S : CompleteLocalAlgCat.{u, v, w} Λ k}
    (hR : R = artinianToComplete.obj A) (hS : S = artinianToComplete.obj B)
    (a : A ⟶ B) {c : R ⟶ S}
    (hc : eqToHom hR ≫ artinianToComplete.map a = c ≫ eqToHom hS) (n : ℕ)
    {T : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (e₁ : (AdicTruncation.functor n).obj (artinianToComplete.obj A) =
      (AdicTruncation.functor n).obj R)
    (e₂ : (AdicTruncation.functor n).obj S = T)
    (e₃ : (AdicTruncation.functor n).obj (artinianToComplete.obj B) = T) :
    artinianAdicQuotient A n ≫ eqToHom e₁ ≫
        (AdicTruncation.functor n).map c ≫ eqToHom e₂ =
      a ≫ artinianAdicQuotient B n ≫ eqToHom e₃ := by
  subst hR
  subst hS
  subst e₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hc ⊢
  subst hc
  exact _root_.Deformation.artinianAdicQuotient_naturality a n

/-- The maximal-adic filtration vanishes at every level beyond `vanishingIndex`. -/
public theorem maximalIdeal_pow_succ_eq_bot_of_vanishingIndex_le
    (A : ArtinianLocalAlgCat.{u, v, w} Λ k) {m : ℕ} (h : vanishingIndex A ≤ m) :
    maximalIdeal A ^ (m + 1) = ⊥ :=
  maximalIdeal_pow_succ_eq_bot_of_le A h (vanishingIndex_spec A)

/-- A family of arrows into the levels of a formal object that is compatible with the
transition maps is compatible with the composite transition maps. -/
private theorem comp_formalLevelTransition_eq
    {F : Type*} [Category F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (W : FormalObject p) {C : F} (f : ∀ m, C ⟶ W.level m)
    (hf : ∀ n, f (n + 1) ≫ W.transition n = f n) {m n : ℕ} (hnm : n ≤ m) :
    f m ≫ FormalEvaluation.formalLevelTransition W m n hnm = f n := by
  induction m, hnm using Nat.le_induction with
  | base => rw [FormalEvaluation.formalLevelTransition_id, Category.comp_id]
  | succ m hnm ih =>
      rw [FormalEvaluation.formalLevelTransition_succ _ hnm (Nat.le_succ_of_le hnm),
        ← Category.assoc, hf, ih]

end

/-! ### Isomorphisms of the restricted category -/

section
open CategoryTheory IsLocalRing

universe u v w uG vG

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {G : Type uG} [Category.{vG} G] {q : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}

/-- The inverse of a morphism of the restricted category both of whose components are
isomorphisms. -/
public noncomputable def restrictionInv {X Y : Restriction q} (f : X ⟶ Y)
    [IsIso f.obj] [IsIso f.base] : Y ⟶ X where
  obj := inv f.obj
  base := inv f.base
  comm := by
    rw [Functor.map_inv, Functor.map_inv]
    calc
      eqToHom Y.obj_eq ≫ inv (artinianToComplete.map f.base) =
          inv (q.map f.obj) ≫ (q.map f.obj ≫ eqToHom Y.obj_eq) ≫
            inv (artinianToComplete.map f.base) := by
        simp
      _ = inv (q.map f.obj) ≫ (eqToHom X.obj_eq ≫ artinianToComplete.map f.base) ≫
            inv (artinianToComplete.map f.base) := by rw [← f.comm]
      _ = inv (q.map f.obj) ≫ eqToHom X.obj_eq := by simp

/-- Composition in the restricted category composes the underlying objects. -/
public theorem restriction_comp_obj {X Y Z : Restriction q} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).obj = f.obj ≫ g.obj := rfl

/-- The identity of the restricted category has the identity as underlying object. -/
public theorem restriction_id_obj (X : Restriction q) :
    Restriction.Hom.obj (𝟙 X) = 𝟙 X.obj := rfl

/-- A morphism of the restricted category both of whose components are isomorphisms is an
isomorphism. -/
public theorem restriction_isIso {X Y : Restriction q} (f : X ⟶ Y)
    [IsIso f.obj] [IsIso f.base] : IsIso f :=
  ⟨restrictionInv f,
    Restriction.Hom.ext (IsIso.hom_inv_id (f := f.obj)) (IsIso.hom_inv_id (f := f.base)),
    Restriction.Hom.ext (IsIso.inv_hom_id (f := f.obj)) (IsIso.inv_hom_id (f := f.base))⟩

end

/-! ### The unit on an Artinian base -/

section
open CategoryTheory IsLocalRing

universe u v w uG vG

-- Objects of a based category are reached through `BasedCategory.ofFunctor`, and the two legs of
-- the pullback object through `restrictedPullbackMap` applied to `unitBasedFunctor` composed with
-- the completion, so the instance arguments below are only type-correct once those unfold.  The
-- same block is used throughout the construction of `completionNatTrans` and of the two hom
-- functors.
attribute [local implicit_reducible] BasedCategory.ofFunctor completionUnit
  restrictedPullbackMap unitBasedFunctor BasedFunctor.comp

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {G : Type uG} [Category.{vG} G] (q : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)
  (hq : IsCofiberedInGroupoids q)

/-- The formal object of the restriction attached to an object by the unit of Tag 06HA. -/
public noncomputable abbrev unitObj (X : G) :
    FormalObject (Restriction.projection (p := q)) :=
  (completionUnit q hq).functor.obj X

/-- The chosen arrow from an object to the underlying object of the level-`m` piece of its
unit. -/
public noncomputable def unitIncl (X : G) (m : ℕ) : X ⟶ ((unitObj q hq X).level m).obj :=
  (adicPushforwardChoice q hq).inclusion X m

/-- The chosen arrow lies over the adic quotient map. -/
public theorem unitIncl_lift (X : G) (m : ℕ) :
    q.IsHomLift (adicQuotientMap (q.obj X) m) (unitIncl q hq X m) :=
  (adicPushforwardChoice q hq).inclusion_lift X m

/-- Over an Artinian base the chosen arrow is an isomorphism, once the maximal-adic
filtration has vanished. -/
public theorem unitIncl_isIso {X : G} {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (h : q.obj X = artinianToComplete.obj A) (m : ℕ)
    (hm : maximalIdeal A ^ (m + 1) = ⊥) : IsIso (unitIncl q hq X m) := by
  have hbase : IsIso (adicQuotientMap (q.obj X) m) := adicQuotientMap_isIso h m hm
  exact isIso_of_isCofiberedInGroupoids_of_base_isIso hq _ _ (unitIncl_lift q hq X m)

/-- The chosen arrows are compatible with the transition maps of the unit. -/
public theorem unitIncl_transition (X : G) (n : ℕ) :
    unitIncl q hq X (n + 1) ≫ ((unitObj q hq X).transition n).obj = unitIncl q hq X n := by
  have h₁ : eqToHom (congrArg Restriction.obj
      ((completionUnit q hq).level X (n + 1)).symm) = 𝟙 _ := rfl
  have h₂ : eqToHom (congrArg Restriction.obj
      ((completionUnit q hq).level X n)) = 𝟙 _ := rfl
  have h := (completionUnit q hq).transition X n
  rwa [h₁, h₂, Category.id_comp, Category.comp_id] at h

/-- The chosen arrows are natural. -/
public theorem unitIncl_map {X Y : G} (f : X ⟶ Y) (n : ℕ) :
    unitIncl q hq X n ≫ (((completionUnit q hq).functor.map f).app n).obj =
      f ≫ unitIncl q hq Y n := by
  have h₁ : eqToHom (congrArg Restriction.obj
      ((completionUnit q hq).level X n).symm) = 𝟙 _ := rfl
  have h₂ : eqToHom (congrArg Restriction.obj
      ((completionUnit q hq).level Y n)) = 𝟙 _ := rfl
  have h := (completionUnit q hq).map f n
  rwa [h₁, h₂, Category.id_comp, Category.comp_id] at h

/-- The chosen arrows are compatible with the composite transition maps of the unit. -/
public theorem unitIncl_levelTransition (X : G) {m n : ℕ} (hnm : n ≤ m) :
    unitIncl q hq X m ≫
        (FormalEvaluation.formalLevelTransition (unitObj q hq X) m n hnm).obj =
      unitIncl q hq X n := by
  induction m, hnm using Nat.le_induction with
  | base =>
      rw [FormalEvaluation.formalLevelTransition_id, restriction_id_obj,
        Category.comp_id]
  | succ m hnm ih =>
      rw [FormalEvaluation.formalLevelTransition_succ _ hnm (Nat.le_succ_of_le hnm),
        restriction_comp_obj, ← Category.assoc, unitIncl_transition, ih]

/-- The base of the level-`m` piece of the unit is the `m`-th adic truncation. -/
public theorem unitObj_level_base_eq (X : Restriction q) (m : ℕ) :
    (AdicTruncation.functor m).obj (artinianToComplete.obj X.base) =
      ((unitObj q hq X.obj).level m).base :=
  (congrArg (AdicTruncation.functor m).obj X.obj_eq.symm).trans
    ((unitObj q hq X.obj).level_eq m).symm

/-- The comparison from an Artinian base to the base of the level-`m` piece of its unit. -/
public noncomputable def unitBase (X : Restriction q) (m : ℕ) :
    X.base ⟶ ((unitObj q hq X.obj).level m).base :=
  artinianAdicQuotient X.base m ≫ eqToHom (unitObj_level_base_eq q hq X m)

/-- The defining formula for `unitBase`. -/
public theorem unitBase_eq (X : Restriction q) (m : ℕ) :
    unitBase q hq X m =
      artinianAdicQuotient X.base m ≫ eqToHom (unitObj_level_base_eq q hq X m) := rfl

/-- The base comparison is an isomorphism once the maximal-adic filtration has vanished. -/
public theorem unitBase_isIso (X : Restriction q) (m : ℕ)
    (hm : maximalIdeal X.base ^ (m + 1) = ⊥) : IsIso (unitBase q hq X m) := by
  have hq' : IsIso (artinianAdicQuotient X.base m) :=
    artinianAdicQuotient_isIso X.base m hm
  rw [unitBase_eq]
  infer_instance

/-- The transition maps of the unit act on bases by the adic transition maps. -/
public theorem unitObj_transition_base (X : G) (n : ℕ) :
    ((unitObj q hq X).transition n).base =
      eqToHom ((unitObj q hq X).level_eq (n + 1)) ≫
        AdicTruncation.transition (q.obj X) n ≫
          eqToHom ((unitObj q hq X).level_eq n).symm := by
  have hlift := (unitObj q hq X).transition_lift n
  exact IsHomLift.fac' (Restriction.projection (p := q))
    ((AdicTruncation.transitionNat n).app (unitObj q hq X).base)
    ((unitObj q hq X).transition n)

/-- The unit acts on bases of level pieces by the adic truncations of the base map. -/
public theorem unitObj_map_app_base {X Y : G} (f : X ⟶ Y) (n : ℕ) :
    (((completionUnit q hq).functor.map f).app n).base =
      eqToHom ((unitObj q hq X).level_eq n) ≫
        (AdicTruncation.functor n).map (q.map f) ≫
          eqToHom ((unitObj q hq Y).level_eq n).symm := by
  have hlift := ((completionUnit q hq).functor.map f).app_lift n
  exact IsHomLift.fac' (Restriction.projection (p := q))
    ((AdicTruncation.functor n).map ((completionUnit q hq).functor.map f).base)
    (((completionUnit q hq).functor.map f).app n)

/-- The base comparisons are compatible with the transition maps of the unit. -/
public theorem unitBase_transition (X : Restriction q) (n : ℕ) :
    unitBase q hq X (n + 1) ≫ ((unitObj q hq X.obj).transition n).base =
      unitBase q hq X n := by
  rw [unitObj_transition_base, unitBase_eq, unitBase_eq]
  simp only [Category.assoc, eqToHom_trans_assoc]
  exact artinianAdicQuotient_transition X.base X.obj_eq n
    (congrArg (AdicTruncation.functor (n + 1)).obj X.obj_eq.symm)
    ((((completionUnit q hq).functor.obj X.obj).level_eq n).symm)
    (unitObj_level_base_eq q hq X n)

/-- The base comparisons are natural. -/
public theorem unitBase_naturality {X Y : Restriction q} (f : X ⟶ Y) (n : ℕ) :
    unitBase q hq X n ≫ (((completionUnit q hq).functor.map f.obj).app n).base =
      f.base ≫ unitBase q hq Y n := by
  rw [unitObj_map_app_base, unitBase_eq, unitBase_eq]
  simp only [Category.assoc, eqToHom_trans_assoc]
  exact artinianAdicQuotient_naturality X.obj_eq Y.obj_eq f.base f.comm n
    (congrArg (AdicTruncation.functor n).obj X.obj_eq.symm)
    ((((completionUnit q hq).functor.obj Y.obj).level_eq n).symm)
    (unitObj_level_base_eq q hq Y n)

/-- The unit of Tag 06HA, evaluated on an Artinian base at level `m`: the chosen arrow
together with the adic quotient map of the base. -/
public noncomputable def unitHom (X : Restriction q) (m : ℕ) :
    X ⟶ (unitObj q hq X.obj).level m where
  obj := unitIncl q hq X.obj m
  base := unitBase q hq X m
  comm := by
    have hlift := unitIncl_lift q hq X.obj m
    rw [unitBase_eq, IsHomLift.fac' q (adicQuotientMap (q.obj X.obj) m)
      (unitIncl q hq X.obj m)]
    exact eqToHom_comp_map_artinianAdicQuotient X.base X.obj_eq m rfl
      (unitObj_level_base_eq q hq X m)
      (IsHomLift.codomain_eq q (adicQuotientMap (q.obj X.obj) m)
        (unitIncl q hq X.obj m)).symm
      ((unitObj q hq X.obj).level m).obj_eq

/-- At a level where the maximal-adic filtration vanishes, the unit is an isomorphism over
an Artinian base. -/
public theorem unitHom_isIso (X : Restriction q) (m : ℕ)
    (hm : maximalIdeal X.base ^ (m + 1) = ⊥) : IsIso (unitHom q hq X m) := by
  have h₁ : IsIso (unitHom q hq X m).obj := unitIncl_isIso q hq X.obj_eq m hm
  have h₂ : IsIso (unitHom q hq X m).base := unitBase_isIso q hq X m hm
  exact restriction_isIso _

/-- The unit is compatible with the transition maps. -/
public theorem unitHom_transition (X : Restriction q) (n : ℕ) :
    unitHom q hq X (n + 1) ≫ (unitObj q hq X.obj).transition n = unitHom q hq X n :=
  Restriction.Hom.ext (unitIncl_transition q hq X.obj n) (unitBase_transition q hq X n)

/-- The unit is compatible with the composite transition maps. -/
public theorem unitHom_levelTransition (X : Restriction q) {m n : ℕ} (hnm : n ≤ m) :
    unitHom q hq X m ≫
        FormalEvaluation.formalLevelTransition (unitObj q hq X.obj) m n hnm =
      unitHom q hq X n := by
  exact comp_formalLevelTransition_eq _ (unitHom q hq X) (unitHom_transition q hq X) hnm

/-- The unit is natural. -/
public theorem unitHom_naturality {X Y : Restriction q} (f : X ⟶ Y) (n : ℕ) :
    unitHom q hq X n ≫ ((completionUnit q hq).functor.map f.obj).app n =
      f ≫ unitHom q hq Y n :=
  Restriction.Hom.ext (unitIncl_map q hq f.obj n) (unitBase_naturality q hq f n)

end

/-! ### Composite transition maps -/

section
open CategoryTheory IsLocalRing

universe u v w uA vA uB vB

-- Objects of a based category are reached through `BasedCategory.ofFunctor`, and the two legs of
-- the pullback object through `restrictedPullbackMap` applied to `unitBasedFunctor` composed with
-- the completion, so the instance arguments below are only type-correct once those unfold.
attribute [local implicit_reducible] BasedCategory.ofFunctor completionUnit
  restrictedPullbackMap unitBasedFunctor BasedFunctor.comp

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
variable {a : A ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
  {b : B ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- Completion of a morphism of cofibered categories applies the morphism to every
composite transition map. -/
public theorem formalLevelTransition_completionMap
    (φ : BasedFunctor (BasedCategory.ofFunctor a) (BasedCategory.ofFunctor b))
    (W : FormalObject a) {m n : ℕ} (hnm : n ≤ m) :
    FormalEvaluation.formalLevelTransition ((completionMap φ).obj W) m n hnm =
      eqToHom (completionMap_obj_level φ W m) ≫
        φ.map (FormalEvaluation.formalLevelTransition W m n hnm) ≫
          eqToHom (completionMap_obj_level φ W n).symm := by
  induction m, hnm using Nat.le_induction with
  | base =>
      rw [FormalEvaluation.formalLevelTransition_id,
        FormalEvaluation.formalLevelTransition_id]
      simp
  | succ m hnm ih =>
      rw [FormalEvaluation.formalLevelTransition_succ _ hnm (Nat.le_succ_of_le hnm),
        FormalEvaluation.formalLevelTransition_succ _ hnm (Nat.le_succ_of_le hnm),
        ih, completionMap_obj_transition, Functor.map_comp]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end

section
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F] (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
  (hp : IsCofiberedInGroupoids p)

/-- The evaluation legs of Tag 06SJ are compatible with the composite transition maps. -/
public theorem evaluationLeg_levelTransition
    (Z : CategoricalPullback artinianToComplete (FormalObject.projection (p := p)))
    {m n : ℕ} (hnm : n ≤ m) :
    FormalEvaluation.evaluationLeg p hp Z m ≫
        FormalEvaluation.formalLevelTransition Z.snd m n hnm =
      FormalEvaluation.evaluationLeg p hp Z n := by
  exact comp_formalLevelTransition_eq _ (FormalEvaluation.evaluationLeg p hp Z)
    (FormalEvaluation.evaluationLeg_transition p hp Z) hnm

/-- At a level where the maximal-adic filtration vanishes, the evaluation leg of Tag 06SJ
is the comparison isomorphism. -/
public theorem evaluationLeg_eq_objIsoLevel
    (Z : CategoricalPullback artinianToComplete (FormalObject.projection (p := p)))
    (m : ℕ) (hm : maximalIdeal Z.fst ^ (m + 1) = ⊥) :
    FormalEvaluation.evaluationLeg p hp Z m =
      ((restrictionCompletionEquivalence p hp).objIsoLevel Z m hm).hom :=
  FormalEvaluation.evaluationLeg_atLevel p hp Z m hm

/-- At a level where the maximal-adic filtration vanishes, the evaluation leg of Tag 06SJ
is an isomorphism. -/
public theorem evaluationLeg_isIso
    (Z : CategoricalPullback artinianToComplete (FormalObject.projection (p := p)))
    (m : ℕ) (hm : maximalIdeal Z.fst ^ (m + 1) = ⊥) :
    IsIso (FormalEvaluation.evaluationLeg p hp Z m) := by
  rw [evaluationLeg_eq_objIsoLevel p hp Z m hm]
  exact Iso.isIso_hom _

/-- The inverse comparison isomorphisms of Tag 06SJ at two stabilized levels agree through
the composite transition map. -/
public theorem levelTransition_comp_objIsoLevel_inv
    (Z : CategoricalPullback artinianToComplete (FormalObject.projection (p := p)))
    {m n : ℕ} (hnm : n ≤ m) (hm : maximalIdeal Z.fst ^ (m + 1) = ⊥)
    (hn : maximalIdeal Z.fst ^ (n + 1) = ⊥) :
    FormalEvaluation.formalLevelTransition Z.snd m n hnm ≫
        ((restrictionCompletionEquivalence p hp).objIsoLevel Z n hn).inv =
      ((restrictionCompletionEquivalence p hp).objIsoLevel Z m hm).inv := by
  rw [Iso.comp_inv_eq, Iso.eq_inv_comp]
  exact FormalEvaluation.evaluationIsoAtLevel_coherence p hp Z hnm hm hn

/-- The inverse comparison isomorphisms of Tag 06SJ intertwine the comparison functor with
the level components. -/
public theorem objIsoLevel_inv_comp_can_map
    {Z W : CategoricalPullback artinianToComplete (FormalObject.projection (p := p))}
    (f : Z ⟶ W) (m : ℕ) (hZ : maximalIdeal Z.fst ^ (m + 1) = ⊥)
    (hW : maximalIdeal W.fst ^ (m + 1) = ⊥) :
    ((restrictionCompletionEquivalence p hp).objIsoLevel Z m hZ).inv ≫
        (restrictionCompletionEquivalence p hp).can.map f =
      f.snd.app m ≫ ((restrictionCompletionEquivalence p hp).objIsoLevel W m hW).inv := by
  rw [Iso.inv_comp_eq,
    ← reassoc_of% (restrictionCompletionEquivalence p hp).objIsoLevel_naturality f m hZ hW]
  simp

end

/-! ### The legs of the unit -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF uG vG

-- Objects of a based category are reached through `BasedCategory.ofFunctor`, and the two legs of
-- the pullback object through `restrictedPullbackMap` applied to `unitBasedFunctor` composed with
-- the completion, so the instance arguments below are only type-correct once those unfold.
attribute [local implicit_reducible] BasedCategory.ofFunctor completionUnit
  restrictedPullbackMap unitBasedFunctor BasedFunctor.comp

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
  (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
variable {G : Type uG} [Category.{vG} G]
  (q : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k) (hq : IsCofiberedInGroupoids q)

/-- The leg of the unit at level `m`: a morphism applied to the unit, read in the
completion. -/
public noncomputable def unitLeg
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) (m : ℕ) :
    φ.obj X ⟶ ((completionMap φ).obj (unitObj q hq X.obj)).level m :=
  φ.map (unitHom q hq X m) ≫
    eqToHom (completionMap_obj_level φ (unitObj q hq X.obj) m).symm

/-- The legs of the unit are compatible with the composite transition maps. -/
public theorem unitLeg_levelTransition
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) {m n : ℕ} (hnm : n ≤ m) :
    unitLeg p q hq φ X m ≫
        FormalEvaluation.formalLevelTransition
          ((completionMap φ).obj (unitObj q hq X.obj)) m n hnm =
      unitLeg p q hq φ X n := by
  simp only [unitLeg]
  rw [formalLevelTransition_completionMap φ (unitObj q hq X.obj) hnm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← Functor.map_comp, unitHom_levelTransition]

/-- At a level where the maximal-adic filtration vanishes, the leg of the unit is an
isomorphism. -/
public theorem unitLeg_isIso
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) (m : ℕ)
    (hm : maximalIdeal X.base ^ (m + 1) = ⊥) :
    IsIso (unitLeg p q hq φ X m) := by
  have h : IsIso (unitHom q hq X m) := unitHom_isIso q hq X m hm
  have h' : IsIso (φ.map (unitHom q hq X m)) := Functor.map_isIso _ _
  rw [unitLeg]
  infer_instance

/-- The legs of the unit are natural in the object. -/
public theorem unitLeg_naturality
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) {X Y : Restriction q} (f : X ⟶ Y) (n : ℕ) :
    unitLeg p q hq φ X n ≫
        ((completionMap φ).map ((completionUnit q hq).functor.map f.obj)).app n =
      φ.map f ≫ unitLeg p q hq φ Y n := by
  simp only [unitLeg]
  rw [completionMap_map_app]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← Functor.map_comp, unitHom_naturality, Functor.map_comp,
    Category.assoc]

/-- The legs of the unit are natural in the morphism. -/
public theorem unitLeg_naturality_two
    {φ χ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)} (t : φ ⟶ χ) (X : Restriction q) (n : ℕ) :
    unitLeg p q hq φ X n ≫
        ((completionNatTrans t).toNatTrans.app (unitObj q hq X.obj)).app n =
      t.toNatTrans.app X ≫ unitLeg p q hq χ X n := by
  simp only [unitLeg]
  rw [completionNatTrans_app_level]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, t.toNatTrans.naturality (unitHom q hq X n), Category.assoc]

end

/-! ### The components of the unit -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w uF vF uG vG

-- Objects of a based category are reached through `BasedCategory.ofFunctor`, and the two legs of
-- the pullback object through `restrictedPullbackMap` applied to `unitBasedFunctor` composed with
-- the completion, so the instance arguments below are only type-correct once those unfold.
attribute [local implicit_reducible] BasedCategory.ofFunctor completionUnit
  restrictedPullbackMap unitBasedFunctor BasedFunctor.comp

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
  (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
variable {G : Type uG} [Category.{vG} G]
  (q : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)
variable (hp : IsCofiberedInGroupoids p) (hq : IsCofiberedInGroupoids q)

/-- The object of the categorical pullback that the composite of the two hom functors
attaches to a morphism and an object of the restriction. -/
public noncomputable abbrev pullbackObj
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) :
    CategoricalPullback artinianToComplete (FormalObject.projection (p := p)) :=
  (restrictedPullbackMap p q hp ((unitBasedFunctor q hq).comp (completionMap φ))).obj X

/-- The component of the unit computed at level `m`. -/
public noncomputable def unitComponentAt
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) (m : ℕ)
    (hm : maximalIdeal X.base ^ (m + 1) = ⊥) :
    φ.obj X ⟶ (restrictionCompletionEquivalence p hp).can.obj
      (pullbackObj p q hp hq φ X) :=
  unitLeg p q hq φ X m ≫
    ((restrictionCompletionEquivalence p hp).objIsoLevel
      (pullbackObj p q hp hq φ X) m hm).inv

/-- The component of the unit does not depend on the level at which it is computed. -/
public theorem unitComponentAt_independent
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) {m n : ℕ} (hnm : n ≤ m)
    (hm : maximalIdeal X.base ^ (m + 1) = ⊥)
    (hn : maximalIdeal X.base ^ (n + 1) = ⊥) :
    unitComponentAt p q hp hq φ X m hm = unitComponentAt p q hp hq φ X n hn := by
  rw [unitComponentAt, unitComponentAt, ← unitLeg_levelTransition p q hq φ X hnm,
    Category.assoc]
  exact congrArg (fun z => unitLeg p q hq φ X m ≫ z)
    (levelTransition_comp_objIsoLevel_inv p hp (pullbackObj p q hp hq φ X)
      hnm hm hn).symm

/-- The component of the unit of Tag 06HA at an object of the restriction. -/
public noncomputable def unitComponent
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) :
    φ.obj X ⟶ (restrictionCompletionEquivalence p hp).can.obj
      (pullbackObj p q hp hq φ X) :=
  unitComponentAt p q hp hq φ X (vanishingIndex X.base) (vanishingIndex_spec X.base)

/-- The component of the unit is computed by any level at which the maximal-adic
filtration has vanished. -/
public theorem unitComponent_eq
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) (m : ℕ)
    (hm : maximalIdeal X.base ^ (m + 1) = ⊥) (hvm : vanishingIndex X.base ≤ m) :
    unitComponent p q hp hq φ X = unitComponentAt p q hp hq φ X m hm :=
  (unitComponentAt_independent p q hp hq φ X hvm hm (vanishingIndex_spec X.base)).symm

/-- The component of the unit is an isomorphism. -/
public theorem unitComponent_isIso
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) :
    IsIso (unitComponent p q hp hq φ X) := by
  have h : IsIso (unitLeg p q hq φ X (vanishingIndex X.base)) :=
    unitLeg_isIso p q hq φ X _ (vanishingIndex_spec X.base)
  rw [unitComponent, unitComponentAt]
  infer_instance

/-- Naturality of the components of the unit at a level, from naturality of the legs. -/
private theorem comp_unitComponentAt_eq
    {φ χ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)} {X Y : Restriction q} {m : ℕ}
    (hX : maximalIdeal X.base ^ (m + 1) = ⊥) (hY : maximalIdeal Y.base ^ (m + 1) = ⊥)
    (g : pullbackObj p q hp hq φ X ⟶ pullbackObj p q hp hq χ Y) (u : φ.obj X ⟶ χ.obj Y)
    (hnat : unitLeg p q hq φ X m ≫ g.snd.app m = u ≫ unitLeg p q hq χ Y m) :
    u ≫ unitComponentAt p q hp hq χ Y m hY =
      unitComponentAt p q hp hq φ X m hX ≫ (restrictionCompletionEquivalence p hp).can.map g := by
  rw [unitComponentAt, unitComponentAt, Category.assoc,
    objIsoLevel_inv_comp_can_map p hp g _ hX hY]
  simp only [← Category.assoc, hnat]

/-- The components of the unit are natural in the object of the restriction. -/
public theorem unitComponent_naturality
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) {X Y : Restriction q} (f : X ⟶ Y)
    (g : pullbackObj p q hp hq φ X ⟶ pullbackObj p q hp hq φ Y)
    (hg : g.snd = (completionMap φ).map ((completionUnit q hq).functor.map f.obj)) :
    φ.map f ≫ unitComponent p q hp hq φ Y =
      unitComponent p q hp hq φ X ≫
        (restrictionCompletionEquivalence p hp).can.map g := by
  have hmX : maximalIdeal X.base ^ (max (vanishingIndex X.base)
      (vanishingIndex Y.base) + 1) = ⊥ :=
    maximalIdeal_pow_succ_eq_bot_of_vanishingIndex_le X.base (le_max_left _ _)
  have hmY : maximalIdeal Y.base ^ (max (vanishingIndex X.base)
      (vanishingIndex Y.base) + 1) = ⊥ :=
    maximalIdeal_pow_succ_eq_bot_of_vanishingIndex_le Y.base (le_max_right _ _)
  rw [unitComponent_eq p q hp hq φ X _ hmX (le_max_left _ _),
    unitComponent_eq p q hp hq φ Y _ hmY (le_max_right _ _)]
  exact comp_unitComponentAt_eq p q hp hq hmX hmY g _
    (hg ▸ unitLeg_naturality p q hq φ f _)

/-- The components of the unit are natural in the morphism. -/
public theorem unitComponent_naturality_two
    {φ χ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)} (t : φ ⟶ χ) (X : Restriction q)
    (g : pullbackObj p q hp hq φ X ⟶ pullbackObj p q hp hq χ X)
    (hg : g.snd = (completionNatTrans t).toNatTrans.app (unitObj q hq X.obj)) :
    t.toNatTrans.app X ≫ unitComponent p q hp hq χ X =
      unitComponent p q hp hq φ X ≫
        (restrictionCompletionEquivalence p hp).can.map g := by
  exact comp_unitComponentAt_eq p q hp hq (vanishingIndex_spec X.base)
    (vanishingIndex_spec X.base) g _
    (hg ▸ unitLeg_naturality_two p q hq t X _)

/-- The base leg of Tag 06SJ at the pullback object is the Artinian adic quotient map. -/
public theorem evaluationBaseLeg_pullbackObj
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) (m : ℕ)
    (d : artinianToComplete.obj X.base = (pullbackObj p q hp hq φ X).snd.base) :
    FormalEvaluation.evaluationBaseLeg (pullbackObj p q hp hq φ X) m =
      artinianAdicQuotient X.base m ≫
        eqToHom (congrArg (AdicTruncation.functor m).obj d) := by
  simp only [FormalEvaluation.evaluationBaseLeg]
  rw [show (pullbackObj p q hp hq φ X).iso.hom = eqToHom d from rfl, eqToHom_map]
  rfl

/-- The base leg of Tag 06SJ at the pullback object is the base comparison of the unit. -/
public theorem evaluationBaseLeg_eq_unitBase
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) (m : ℕ)
    (c : ((unitObj q hq X.obj).level m).base =
      (AdicTruncation.functor m).obj (pullbackObj p q hp hq φ X).snd.base) :
    FormalEvaluation.evaluationBaseLeg (pullbackObj p q hp hq φ X) m =
      unitBase q hq X m ≫ eqToHom c := by
  rw [evaluationBaseLeg_pullbackObj p q hp hq φ X m
      (X.obj_eq.symm.trans
        (((unitBasedFunctor q hq).comp (completionMap φ)).w_obj X.obj).symm),
    unitBase_eq]
  simp only [Category.assoc, eqToHom_trans]

/-- Every component of the unit lies over the identity of the Artinian base. -/
public theorem unitComponent_isHomLift
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) :
    p.IsHomLift (𝟙 X.base) (unitComponent p q hp hq φ X) := by
  have hm : maximalIdeal X.base ^ (vanishingIndex X.base + 1) = ⊥ :=
    vanishingIndex_spec X.base
  have h0 : (BasedCategory.ofFunctor (Restriction.projection (p := q))).p.IsHomLift
      (unitBase q hq X (vanishingIndex X.base))
      (unitHom q hq X (vanishingIndex X.base)) :=
    IsHomLift.map (p := Restriction.projection (p := q))
      (unitHom q hq X (vanishingIndex X.base))
  have h1 : p.IsHomLift (unitBase q hq X (vanishingIndex X.base))
      (φ.map (unitHom q hq X (vanishingIndex X.base))) :=
    BasedFunctor.preserves_isHomLift φ _ _
  have hA : p.IsHomLift
      (FormalEvaluation.evaluationBaseLeg (pullbackObj p q hp hq φ X)
        (vanishingIndex X.base))
      (unitLeg p q hq φ X (vanishingIndex X.base)) := by
    rw [evaluationBaseLeg_eq_unitBase p q hp hq φ X (vanishingIndex X.base)
      (((unitObj q hq X.obj).level_eq (vanishingIndex X.base)).trans
        (congrArg (AdicTruncation.functor (vanishingIndex X.base)).obj
          (completionMap_obj_base φ (unitObj q hq X.obj)).symm)), unitLeg]
    infer_instance
  have hB : p.IsHomLift
      (FormalEvaluation.evaluationBaseLeg (pullbackObj p q hp hq φ X)
        (vanishingIndex X.base))
      (((restrictionCompletionEquivalence p hp).objIsoLevel
        (pullbackObj p q hp hq φ X) (vanishingIndex X.base) hm).hom) := by
    rw [← evaluationLeg_eq_objIsoLevel p hp (pullbackObj p q hp hq φ X) _ hm]
    exact FormalEvaluation.evaluationLeg_lift p hp (pullbackObj p q hp hq φ X) _
  have hisoBase : IsIso (FormalEvaluation.evaluationBaseLeg
      (pullbackObj p q hp hq φ X) (vanishingIndex X.base)) :=
    IsHomLift.isIso_of_lift_isIso p _
      (((restrictionCompletionEquivalence p hp).objIsoLevel
        (pullbackObj p q hp hq φ X) (vanishingIndex X.base) hm).hom)
  have hB' : p.IsHomLift
      (asIso (FormalEvaluation.evaluationBaseLeg (pullbackObj p q hp hq φ X)
        (vanishingIndex X.base))).hom
      (((restrictionCompletionEquivalence p hp).objIsoLevel
        (pullbackObj p q hp hq φ X) (vanishingIndex X.base) hm).hom) := hB
  have hinv : p.IsHomLift
      (inv (FormalEvaluation.evaluationBaseLeg (pullbackObj p q hp hq φ X)
        (vanishingIndex X.base)))
      (((restrictionCompletionEquivalence p hp).objIsoLevel
        (pullbackObj p q hp hq φ X) (vanishingIndex X.base) hm).inv) :=
    IsHomLift.inv_lift_inv p
      (asIso (FormalEvaluation.evaluationBaseLeg (pullbackObj p q hp hq φ X)
        (vanishingIndex X.base))) _
  have hcomp := IsHomLift.comp p
    (FormalEvaluation.evaluationBaseLeg (pullbackObj p q hp hq φ X)
      (vanishingIndex X.base))
    (inv (FormalEvaluation.evaluationBaseLeg (pullbackObj p q hp hq φ X)
      (vanishingIndex X.base)))
    (unitLeg p q hq φ X (vanishingIndex X.base))
    (((restrictionCompletionEquivalence p hp).objIsoLevel
      (pullbackObj p q hp hq φ X) (vanishingIndex X.base) hm).inv)
  rw [IsIso.hom_inv_id] at hcomp
  rw [unitComponent, unitComponentAt]
  exact hcomp

end

end HomEquivalenceUnit

/-! ### The unit of the hom equivalence of Tag 06HA -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing HomEquivalenceUnit

universe u v w uF vF uG vG

-- Objects of a based category are reached through `BasedCategory.ofFunctor`, and the two legs of
-- the pullback object through `restrictedPullbackMap` applied to `unitBasedFunctor` composed with
-- the completion, so the instance arguments below are only type-correct once those unfold.
attribute [local implicit_reducible] BasedCategory.ofFunctor completionUnit
  restrictedPullbackMap unitBasedFunctor BasedFunctor.comp

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
  (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
variable {G : Type uG} [Category.{vG} G]
  (q : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)

/-- The component of the unit of Tag 06HA, as an isomorphism. -/
public noncomputable def unitComponentIso
    (hp : IsCofiberedInGroupoids p) (hq : IsCofiberedInGroupoids q)
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) (X : Restriction q) :
    φ.obj X ≅ (restrictionCompletionEquivalence p hp).can.obj
      (pullbackObj p q hp hq φ X) :=
  @asIso _ _ _ _ (unitComponent p q hp hq φ X) (unitComponent_isIso p q hp hq φ X)

/-- The unit of Tag 06HA at a morphism, as a natural isomorphism of underlying
functors. -/
public noncomputable def unitNatIso
    (hp : IsCofiberedInGroupoids p) (hq : IsCofiberedInGroupoids q)
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) :
    φ.toFunctor ≅
      ((completionHomForward p q hq ⋙ completionHomInverse p q hp).obj φ).toFunctor :=
  NatIso.ofComponents (fun X => unitComponentIso p q hp hq φ X) (fun f =>
    unitComponent_naturality p q hp hq φ f
      ((restrictedPullbackMap p q hp
        ((unitBasedFunctor q hq).comp (completionMap φ))).map f) rfl)

/-- The unit of Tag 06HA at a morphism, as a based natural isomorphism. -/
public noncomputable def unitBasedNatIso
    (hp : IsCofiberedInGroupoids p) (hq : IsCofiberedInGroupoids q)
    (φ : BasedFunctor (BasedCategory.ofFunctor (Restriction.projection (p := q)))
      (BasedCategory.ofFunctor p)) :
    φ ≅ (completionHomForward p q hq ⋙ completionHomInverse p q hp).obj φ :=
  BasedNatIso.mkNatIso (unitNatIso p q hp hq φ)
    (fun X => unitComponent_isHomLift p q hp hq φ X)

/-- **Stacks Project, Tag 06HA (hom equivalence, unit).**  The identity of the hom category
of morphisms out of a restricted cofibered category is naturally isomorphic to the
composite of completion followed by restriction and the canonical comparison of Tag 06SJ.
On an object of the restriction, the component is the unit arrow of Tag 06HA, which is an
isomorphism once the maximal-adic filtration of the Artinian base has vanished. -/
public noncomputable def completionHomUnitIso
    (hp : IsCofiberedInGroupoids p) (hq : IsCofiberedInGroupoids q) :
    Functor.id _ ≅ completionHomForward p q hq ⋙ completionHomInverse p q hp :=
  NatIso.ofComponents (fun φ => unitBasedNatIso p q hp hq φ) (fun t =>
    BasedNatTrans.homCategory.ext _ _ (NatTrans.ext (funext fun X =>
      unitComponent_naturality_two p q hp hq t X
      ((restrictedPullbackNatTrans p q hp
        (BasedCategory.whiskerLeft (unitBasedFunctor q hq)
          (completionNatTrans t))).toNatTrans.app X) rfl)))

end

end Deformation

end
