module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.ExactSequence

/-!
# The descended cap operation along an envelope

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a
morphism of schemes locally of finite type over `S`, let `g : Y' ⟶ Y` be an envelope and write
`X' = X ×_Y Y'`. For a bivariant class `c' ∈ A^p(X' ⟶ Y')`, the proof of Stacks 0GUC defines the
cap operation of the descended class on a test scheme `t : T ⟶ Y` by

  `c ∩ β = h_*(c' ∩ β')`,

where `β'` is any class on `Y' ×_Y T` pushing forward to `β` along the envelope `Y' ×_Y T ⟶ T`
(Stacks 0GU7, 0GU8) and `h : X' ×_{Y'} (Y' ×_Y T) ⟶ X ×_Y T` is the induced proper morphism. This
file builds that operation, proves that it is well defined exactly when the two restrictions
`res₁(c')` and `res₂(c')` of the tag agree, and proves the proper-pushforward and the
flat-pullback conditions of Stacks 0B76 for it.

## Main definitions

* `Stacks.Chow.envelopeDescentMap` — the morphism `X' ×_{Y'} T₀ ⟶ X ×_Y T` attached to a proper
  `e : T₀ ⟶ T` with `e ≫ t` factoring through `g` as `m ≫ g`; it is a base change of `e`.
* `Stacks.Chow.envelopeDescentPush` — the operation `γ ↦ h_*(c' ∩ γ)` attached to such a
  factorization, and `Stacks.Chow.envelopeLiftPush` the pushforward `e_*`.
* `Stacks.Chow.envelopeFibreSquareMap` — the morphism `f'' : X' ×_X X' ⟶ Y' ×_Y Y'`, with the
  identifications `Stacks.Chow.envelopeFibreSquareFstIso` and
  `Stacks.Chow.envelopeFibreSquareSndIso` of `X' ×_X X'` with the fibre products of `f'` along
  the two projections `Y' ×_Y Y' ⟶ Y'`.
* `Stacks.Chow.envelopeDescentRes₁`, `Stacks.Chow.envelopeDescentRes₂` — the two restrictions
  `res₁(c'), res₂(c') ∈ A^p(X' ×_X X' ⟶ Y' ×_Y Y')` of Stacks 0GUC.
* `Stacks.Chow.envelopeDescentCap` — the descended cap operation.

## Main results

* `Stacks.Chow.envelopeDescentPush_eq_of_res_eq` — the agreement of the two restrictions,
  evaluated at a test scheme `T₀ ⟶ Y' ×_Y Y'`.
* `Stacks.Chow.envelopeDescentPush_eq_of_envelopeLiftPush_eq` — the descended operation is well
  defined.
* `Stacks.Chow.envelopeDescentCap_envelopeLiftPush` — `c ∩ e_* γ = h_*(c' ∩ γ)` for every proper
  `e` factoring through `g`, not only for the base change of `g`.
* `Stacks.Chow.envelopeDescentCap_proper_naturality`,
  `Stacks.Chow.envelopeDescentCap_flat_naturality` — conditions (1) and (2) of Stacks 0B76.

## References

* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0GU7](https://stacks.math.columbia.edu/tag/0GU7)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Proper pushforward with the canonical instance of Stacks 02S2 -/

/-- Proper pushforward on Chow groups along a morphism proper over the base, with the instance of
Stacks 02S2 supplied by `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence`. -/
abbrev chowPush (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B) [IsProper u]
    (hu : u ≫ sB = sA) (k : ℤ) : chowGroup C sA k →+ chowGroup C sB k :=
  properChowPushforward C sA sB u hu k
    (properPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)

section ChowPush

variable (C : ChowSituation.{u}) {A B D : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]

/-- Proper pushforward is functorial. -/
theorem chowPush_comp (u : A ⟶ B) [IsProper u] (v : B ⟶ D) [IsProper v] (w : A ⟶ D) [IsProper w]
    (huv : u ≫ v = w) (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (hw : w ≫ sD = sA) (k : ℤ)
    (α : chowGroup C sA k) :
    chowPush C sB sD v hv k (chowPush C sA sB u hu k α) = chowPush C sA sD w hw k α :=
  (properChowPushforward_comp_apply C sA sB sD u v w huv hu hv hw k _ _ _ α).symm

/-- Proper pushforward along two equal morphisms agrees. -/
theorem chowPush_congr {u u' : A ⟶ B} [IsProper u] [IsProper u'] (h : u = u')
    (hu : u ≫ sB = sA) (hu' : u' ≫ sB = sA) (k : ℤ) (α : chowGroup C sA k) :
    chowPush C sA sB u hu k α = chowPush C sA sB u' hu' k α := by
  subst h
  rfl

/-- Proper pushforward along the identity is the identity. -/
theorem chowPush_id (k : ℤ) (α : chowGroup C sA k) :
    chowPush C sA sA (𝟙 A) (Category.id_comp sA) k α = α :=
  chowPushforwardOfIso_id C sA k α

/-- Proper pushforward after a pushforward along an isomorphism is proper pushforward along the
composite. -/
theorem chowPush_chowPushforwardOfIso (u : A ⟶ B) [IsIso u] (v : B ⟶ D) [IsProper v]
    (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (huv : (u ≫ v) ≫ sD = sA) (k : ℤ)
    (α : chowGroup C sA k) :
    chowPush C sB sD v hv k (chowPushforwardOfIso C sA sB u hu k α) =
      chowPush C sA sD (u ≫ v) huv k α :=
  chowPush_comp C sA sB sD u v (u ≫ v) rfl hu hv huv k α

/-- Pushing a class forward along the transport between two equal closed subschemes and back
again changes nothing. -/
theorem chowPushforwardOfIso_eqToHom_cancel {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J)
    (q : X ⟶ C.S) [LocallyOfFiniteType q] [LocallyOfFiniteType (I.subschemeι ≫ q)]
    [LocallyOfFiniteType (J.subschemeι ≫ q)] (k : ℤ)
    (h₁ : eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ (J.subschemeι ≫ q) =
      I.subschemeι ≫ q)
    (h₂ : eqToHom (congrArg Scheme.IdealSheafData.subscheme h.symm) ≫ (I.subschemeι ≫ q) =
      J.subschemeι ≫ q)
    (x : chowGroup C (I.subschemeι ≫ q) k) :
    chowPushforwardOfIso C _ _ (eqToHom (congrArg Scheme.IdealSheafData.subscheme h.symm)) h₂ k
        (chowPushforwardOfIso C _ _ (eqToHom (congrArg Scheme.IdealSheafData.subscheme h)) h₁ k
          x) = x := by
  subst h
  show chowPushforwardOfIso C _ _ (𝟙 _) _ k (chowPushforwardOfIso C _ _ (𝟙 _) _ k x) = x
  rw [chowPushforwardOfIso_id C _ k, chowPushforwardOfIso_id C _ k]

/-- A proper pushforward followed by two pushforwards along isomorphisms is the proper
pushforward along the composite. -/
theorem chowPushforwardOfIso_chowPushforwardOfIso_chowPush {E : Scheme.{u}} (sE : E ⟶ C.S)
    [LocallyOfFiniteType sE] (u : A ⟶ B) [IsProper u] (v : B ⟶ D) [IsIso v] (w : D ⟶ E) [IsIso w]
    (hu : u ≫ sB = sA) (hv : v ≫ sD = sB) (hw : w ≫ sE = sD) (huvw : (u ≫ v ≫ w) ≫ sE = sA)
    (k : ℤ) (α : chowGroup C sA k) :
    chowPushforwardOfIso C sD sE w hw k (chowPushforwardOfIso C sB sD v hv k
        (chowPush C sA sB u hu k α)) = chowPush C sA sE (u ≫ v ≫ w) huvw k α := by
  have h1 := chowPush_comp C sA sB sD u v (u ≫ v) rfl hu hv (by rw [Category.assoc, hv, hu]) k α
  have h2 := chowPush_comp C sA sD sE (u ≫ v) w (u ≫ v ≫ w) (Category.assoc _ _ _)
    (by rw [Category.assoc, hv, hu]) hw huvw k α
  exact (congrArg (chowPush C sD sE w hw k) h1).trans h2

/-- The transport between two equal closed subschemes commutes with structure morphisms. -/
theorem subschemeι_eqToHom_comp_structure {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J)
    (q : X ⟶ C.S) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ (J.subschemeι ≫ q) =
      I.subschemeι ≫ q := by
  rw [← Category.assoc, subschemeι_eqToHom h]

end ChowPush

/-! ### The comparison morphism of a factorization through the envelope -/

section Maps

variable {X Y Y' T T₀ : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (t : T ⟶ Y) (e : T₀ ⟶ T)
  (m : T₀ ⟶ Y') (hm : m ≫ g = e ≫ t)

/-- For a test scheme `t : T ⟶ Y` and a morphism `e : T₀ ⟶ T` whose composite with `t` factors
as `m ≫ g` through `g : Y' ⟶ Y`, the morphism `X' ×_{Y'} T₀ ⟶ X ×_Y T` induced by `e`, where
`X' = X ×_Y Y'`. -/
def envelopeDescentMap : pullback (pullback.snd f g) m ⟶ pullback f t :=
  pullback.lift (pullback.fst (pullback.snd f g) m ≫ pullback.fst f g)
    (pullback.snd (pullback.snd f g) m ≫ e) (by
      rw [Category.assoc, pullback.condition (f := f) (g := g), ← Category.assoc,
        pullback.condition (f := pullback.snd f g) (g := m), Category.assoc, hm,
        Category.assoc])

/-- The comparison morphism followed by the first projection to `X` is the projection
`X' ×_{Y'} T₀ ⟶ X' ⟶ X`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentMap_fst :
    envelopeDescentMap f g t e m hm ≫ pullback.fst f t =
      pullback.fst (pullback.snd f g) m ≫ pullback.fst f g :=
  pullback.lift_fst _ _ _

/-- The comparison morphism followed by the second projection to `T` is the projection
`X' ×_{Y'} T₀ ⟶ T₀` followed by `e`. -/
@[reassoc (attr := simp)]
theorem envelopeDescentMap_snd :
    envelopeDescentMap f g t e m hm ≫ pullback.snd f t = pullback.snd (pullback.snd f g) m ≫ e :=
  pullback.lift_snd _ _ _

/-- The comparison morphism is a base change of `e`. -/
theorem isPullback_envelopeDescentMap :
    IsPullback (pullback.snd (pullback.snd f g) m) (envelopeDescentMap f g t e m hm) e
      (pullback.snd f t) := by
  have houter : IsPullback (envelopeDescentMap f g t e m hm ≫ pullback.fst f t)
      (pullback.snd (pullback.snd f g) m) f (e ≫ t) := by
    rw [envelopeDescentMap_fst, ← hm]
    exact (IsPullback.of_hasPullback (pullback.snd f g) m).paste_horiz
      (IsPullback.of_hasPullback f g)
  exact (houter.of_right (envelopeDescentMap_snd f g t e m hm)
    (IsPullback.of_hasPullback f t)).flip

/-- The comparison morphism is proper when `e` is. -/
instance [IsProper e] : IsProper (envelopeDescentMap f g t e m hm) :=
  MorphismProperty.of_isPullback (isPullback_envelopeDescentMap f g t e m hm)
    (P := @IsProper) inferInstance

/-- Precomposing the comparison morphism with a base change of `φ : T₁ ⟶ T₀` gives the comparison
morphism of `φ ≫ e`. -/
theorem baseChangeMapOfEq_comp_envelopeDescentMap {T₁ : Scheme.{u}} (φ : T₁ ⟶ T₀) (m₁ : T₁ ⟶ Y')
    (hm₁ : φ ≫ m = m₁) (hm' : m₁ ≫ g = (φ ≫ e) ≫ t) :
    baseChangeMapOfEq (pullback.snd f g) m φ m₁ hm₁ ≫ envelopeDescentMap f g t e m hm =
      envelopeDescentMap f g t (φ ≫ e) m₁ hm' := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- Postcomposing the comparison morphism with a base change `T₂ ×_Y X ⟶ T ×_Y X` of a morphism
`r : T₂ ⟶ T` of test schemes gives the comparison morphism of `e ≫ r`. -/
theorem envelopeDescentMap_comp_baseChange {T₂ : Scheme.{u}} (t₂ : T₂ ⟶ Y) (r : T ⟶ T₂)
    (r' : pullback f t ⟶ pullback f t₂) (hr₁ : r' ≫ pullback.fst f t₂ = pullback.fst f t)
    (hr₂ : r' ≫ pullback.snd f t₂ = pullback.snd f t ≫ r) (hm' : m ≫ g = (e ≫ r) ≫ t₂) :
    envelopeDescentMap f g t e m hm ≫ r' = envelopeDescentMap f g t₂ (e ≫ r) m hm' := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, hr₁]; simp
  · rw [Category.assoc, hr₂]; simp

end Maps

/-! ### The fibre square `X' ×_X X' ⟶ Y' ×_Y Y'` -/

section FibreSquare

variable {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The morphism `f'' : X' ×_X X' ⟶ Y' ×_Y Y'` induced by `f' : X' ⟶ Y'`, where
`X' = X ×_Y Y'`. -/
abbrev envelopeFibreSquareMap :
    pullback (pullback.fst f g) (pullback.fst f g) ⟶ pullback g g :=
  pullback.map (pullback.fst f g) (pullback.fst f g) g g (pullback.snd f g) (pullback.snd f g) f
    pullback.condition pullback.condition

/-- The comparison `X' ×_{Y'} (Y' ×_Y Y') ⟶ X' ×_X X'` along the first projection
`a : X' ×_X X' ⟶ X'`. -/
def envelopeFibreSquareFstHom :
    pullback (pullback.snd f g) (pullback.fst g g) ⟶
      pullback (pullback.fst f g) (pullback.fst f g) :=
  pullback.lift (pullback.fst (pullback.snd f g) (pullback.fst g g))
    (pullback.lift (pullback.fst (pullback.snd f g) (pullback.fst g g) ≫ pullback.fst f g)
      (pullback.snd (pullback.snd f g) (pullback.fst g g) ≫ pullback.snd g g) (by
        rw [Category.assoc, pullback.condition (f := f) (g := g), ← Category.assoc,
          pullback.condition (f := pullback.snd f g) (g := pullback.fst g g), Category.assoc,
          pullback.condition (f := g) (g := g), Category.assoc]))
    (pullback.lift_fst _ _ _).symm

/-- The inverse comparison `X' ×_X X' ⟶ X' ×_{Y'} (Y' ×_Y Y')`. -/
def envelopeFibreSquareFstInv :
    pullback (pullback.fst f g) (pullback.fst f g) ⟶
      pullback (pullback.snd f g) (pullback.fst g g) :=
  pullback.lift (pullback.fst (pullback.fst f g) (pullback.fst f g))
    (envelopeFibreSquareMap f g) (by simp [pullback.lift_fst])

/-- The comparison `X' ×_{Y'} (Y' ×_Y Y') ⟶ X' ×_X X'` along the second projection
`b : X' ×_X X' ⟶ X'`. -/
def envelopeFibreSquareSndHom :
    pullback (pullback.snd f g) (pullback.snd g g) ⟶
      pullback (pullback.fst f g) (pullback.fst f g) :=
  pullback.lift
    (pullback.lift (pullback.fst (pullback.snd f g) (pullback.snd g g) ≫ pullback.fst f g)
      (pullback.snd (pullback.snd f g) (pullback.snd g g) ≫ pullback.fst g g) (by
        rw [Category.assoc, pullback.condition (f := f) (g := g), ← Category.assoc,
          pullback.condition (f := pullback.snd f g) (g := pullback.snd g g), Category.assoc,
          ← pullback.condition (f := g) (g := g), Category.assoc]))
    (pullback.fst (pullback.snd f g) (pullback.snd g g))
    (pullback.lift_fst _ _ _)

/-- The inverse comparison `X' ×_X X' ⟶ X' ×_{Y'} (Y' ×_Y Y')` along the second projection. -/
def envelopeFibreSquareSndInv :
    pullback (pullback.fst f g) (pullback.fst f g) ⟶
      pullback (pullback.snd f g) (pullback.snd g g) :=
  pullback.lift (pullback.snd (pullback.fst f g) (pullback.fst f g))
    (envelopeFibreSquareMap f g) (by simp)

/-- The identification `X' ×_{Y'} (Y' ×_Y Y') ≅ X' ×_X X'`, the fibre product on the left taken
along the first projection `p : Y' ×_Y Y' ⟶ Y'`. -/
def envelopeFibreSquareFstIso :
    pullback (pullback.snd f g) (pullback.fst g g) ≅
      pullback (pullback.fst f g) (pullback.fst f g) where
  hom := envelopeFibreSquareFstHom f g
  inv := envelopeFibreSquareFstInv f g
  hom_inv_id := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;>
      simp [envelopeFibreSquareFstHom, envelopeFibreSquareFstInv, pullback.lift_fst,
        pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.condition]
  inv_hom_id := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;>
      simp [envelopeFibreSquareFstHom, envelopeFibreSquareFstInv, pullback.lift_fst,
        pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.condition]

/-- The identification `X' ×_{Y'} (Y' ×_Y Y') ≅ X' ×_X X'`, the fibre product on the left taken
along the second projection `q : Y' ×_Y Y' ⟶ Y'`. -/
def envelopeFibreSquareSndIso :
    pullback (pullback.snd f g) (pullback.snd g g) ≅
      pullback (pullback.fst f g) (pullback.fst f g) where
  hom := envelopeFibreSquareSndHom f g
  inv := envelopeFibreSquareSndInv f g
  hom_inv_id := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;>
      simp [envelopeFibreSquareSndHom, envelopeFibreSquareSndInv, pullback.lift_fst,
        pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.condition]
  inv_hom_id := by
    refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_ <;>
      simp [envelopeFibreSquareSndHom, envelopeFibreSquareSndInv, pullback.lift_fst,
        pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.condition]

/-- Under `envelopeFibreSquareFstIso`, the morphism `f''` becomes the second projection
`X' ×_{Y'} (Y' ×_Y Y') ⟶ Y' ×_Y Y'`. -/
@[reassoc (attr := simp)]
theorem envelopeFibreSquareFstIso_hom_map :
    (envelopeFibreSquareFstIso f g).hom ≫ envelopeFibreSquareMap f g =
      pullback.snd (pullback.snd f g) (pullback.fst g g) := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp [envelopeFibreSquareFstIso, envelopeFibreSquareFstHom, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.condition]

/-- Under `envelopeFibreSquareSndIso`, the morphism `f''` becomes the second projection
`X' ×_{Y'} (Y' ×_Y Y') ⟶ Y' ×_Y Y'`. -/
@[reassoc (attr := simp)]
theorem envelopeFibreSquareSndIso_hom_map :
    (envelopeFibreSquareSndIso f g).hom ≫ envelopeFibreSquareMap f g =
      pullback.snd (pullback.snd f g) (pullback.snd g g) := by
  refine pullback.hom_ext ?_ ?_ <;>
    simp [envelopeFibreSquareSndIso, envelopeFibreSquareSndHom, pullback.lift_fst,
      pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.condition]

/-- The inverse of `envelopeFibreSquareFstIso` followed by the projection to `X'` is the first
projection `a : X' ×_X X' ⟶ X'`. -/
@[reassoc (attr := simp)]
theorem envelopeFibreSquareFstIso_inv_fst :
    (envelopeFibreSquareFstIso f g).inv ≫ pullback.fst (pullback.snd f g) (pullback.fst g g) =
      pullback.fst (pullback.fst f g) (pullback.fst f g) := by
  simp [envelopeFibreSquareFstIso, envelopeFibreSquareFstInv, pullback.lift_fst]

/-- `envelopeFibreSquareFstIso` followed by the first projection `a : X' ×_X X' ⟶ X'` is the
projection `X' ×_{Y'} (Y' ×_Y Y') ⟶ X'`. -/
@[reassoc (attr := simp)]
theorem envelopeFibreSquareFstIso_hom_fst :
    (envelopeFibreSquareFstIso f g).hom ≫ pullback.fst (pullback.fst f g) (pullback.fst f g) =
      pullback.fst (pullback.snd f g) (pullback.fst g g) := by
  simp [envelopeFibreSquareFstIso, envelopeFibreSquareFstHom, pullback.lift_fst]

/-- `envelopeFibreSquareSndIso` followed by the second projection `b : X' ×_X X' ⟶ X'` is the
projection `X' ×_{Y'} (Y' ×_Y Y') ⟶ X'`. -/
@[reassoc (attr := simp)]
theorem envelopeFibreSquareSndIso_hom_snd :
    (envelopeFibreSquareSndIso f g).hom ≫ pullback.snd (pullback.fst f g) (pullback.fst f g) =
      pullback.fst (pullback.snd f g) (pullback.snd g g) := by
  simp [envelopeFibreSquareSndIso, envelopeFibreSquareSndHom, pullback.lift_snd]

/-- `envelopeFibreSquareSndIso` followed by `a : X' ×_X X' ⟶ X'` and `X' ⟶ X` agrees with the
projection `X' ×_{Y'} (Y' ×_Y Y') ⟶ X'` followed by `X' ⟶ X`. -/
@[reassoc (attr := simp)]
theorem envelopeFibreSquareSndIso_hom_fst_fst :
    (envelopeFibreSquareSndIso f g).hom ≫ pullback.fst (pullback.fst f g) (pullback.fst f g) ≫
        pullback.fst f g =
      pullback.fst (pullback.snd f g) (pullback.snd g g) ≫ pullback.fst f g := by
  simp [envelopeFibreSquareSndIso, envelopeFibreSquareSndHom, pullback.lift_fst,
    pullback.lift_fst_assoc]

/-- The morphism `f''` is locally of finite type when `f` is. -/
instance [LocallyOfFiniteType f] : LocallyOfFiniteType (envelopeFibreSquareMap f g) := by
  rw [← Iso.inv_hom_id_assoc (envelopeFibreSquareFstIso f g) (envelopeFibreSquareMap f g),
    envelopeFibreSquareFstIso_hom_map]
  infer_instance

end FibreSquare

/-! ### Changing the structure morphism of the target -/

/-- A bivariant class for `f : X ⟶ Y`, read against a structure morphism of `Y` equal to the
given one. -/
def BivariantClass.congrBase {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}}
    {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY sY' : Y ⟶ C.S} [LocallyOfFiniteType sY]
    [LocallyOfFiniteType sY'] {f : X ⟶ Y} [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}
    (h : sY = sY') (hf' : f ≫ sY' = sX) (c : BivariantClass C G sX sY f hf p) :
    BivariantClass C G sX sY' f hf' p := by
  subst h
  exact c

/-- Capping with `c.congrBase h hf'` is capping with `c` after identifying the Chow groups of `T`
over the equal structure morphisms `t ≫ sY'` and `t ≫ sY`. -/
theorem BivariantClass.congrBase_cap {C : ChowSituation.{u}} {G : GysinSystem C}
    {X Y : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY sY' : Y ⟶ C.S}
    [LocallyOfFiniteType sY] [LocallyOfFiniteType sY'] {f : X ⟶ Y} [LocallyOfFiniteType f]
    {hf : f ≫ sY = sX} {p : ℤ} (h : sY = sY') (hf' : f ≫ sY' = sX)
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sY') k) :
    (c.congrBase h hf').cap t k α = c.cap t k (chowGroupCongr C (by rw [h]) k α) := by
  subst h
  rfl

/-! ### The two restrictions of the descent condition -/

section Restrictions

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (g : Y' ⟶ Y) [IsProper g] (p : ℤ)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f] [IsProper g] in
include hf in
/-- The morphism `f'' : X' ×_X X' ⟶ Y' ×_Y Y'` commutes with the structure morphisms over the
base, that of `Y' ×_Y Y'` taken through the first projection. -/
theorem envelopeFibreSquareMap_comp_structureMorphism :
    envelopeFibreSquareMap f g ≫ (pullback.fst g g ≫ (g ≫ sY)) =
      pullback.fst (pullback.fst f g) (pullback.fst f g) ≫ (pullback.fst f g ≫ sX) := by
  rw [← Category.assoc, pullback.lift_fst, Category.assoc,
    pullbackSnd_comp_structureMorphism_eq C sX sY f hf g]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f] [IsProper g] in
include hf in
/-- The morphism `f''` commutes with the structure morphisms over the base, that of
`Y' ×_Y Y'` taken through the second projection. -/
theorem envelopeFibreSquareMap_comp_structureMorphism' :
    envelopeFibreSquareMap f g ≫ (pullback.snd g g ≫ (g ≫ sY)) =
      pullback.fst (pullback.fst f g) (pullback.fst f g) ≫ (pullback.fst f g ≫ sX) := by
  rw [← pullback.condition_assoc]
  exact envelopeFibreSquareMap_comp_structureMorphism C sX sY f hf g

/-- **The first restriction `res₁(c')` of Stacks 0GUC.** The restriction (Stacks 0F9Z) of a
bivariant class `c' ∈ A^p(X' ⟶ Y')` along the first projection `p : Y' ×_Y Y' ⟶ Y'`, that is,
for the cartesian square formed by `a : X' ×_X X' ⟶ X'`, `f'`, `p` and
`f'' : X' ×_X X' ⟶ Y' ×_Y Y'`; it lies in `A^p(X' ×_X X' ⟶ Y' ×_Y Y')`. -/
def envelopeDescentRes₁ (hgys : G.IsNaturalUnderBaseChangeIso)
    (c' : BivariantClass C G (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) p) :
    BivariantClass C G
      (pullback.fst (pullback.fst f g) (pullback.fst f g) ≫ (pullback.fst f g ≫ sX))
      (pullback.fst g g ≫ (g ≫ sY)) (envelopeFibreSquareMap f g)
      (envelopeFibreSquareMap_comp_structureMorphism C sX sY f hf g) p :=
  bivariantTransport C G _ _ _ _
    (pullbackSnd_comp_structureMorphism_eq C _ _ _
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) (pullback.fst g g))
    _ (envelopeFibreSquareMap_comp_structureMorphism C sX sY f hf g)
    (envelopeFibreSquareFstIso f g) (envelopeFibreSquareFstIso_hom_map f g) p hgys
    (bivariantRestriction C G _ _ _ _ (pullback.fst g g) p hgys c')

/-- **The second restriction `res₂(c')` of Stacks 0GUC.** The restriction of `c'` along the
second projection `q : Y' ×_Y Y' ⟶ Y'`, that is, for the cartesian square formed by
`b : X' ×_X X' ⟶ X'`, `f'`, `q` and `f''`, read in the same group `A^p(X' ×_X X' ⟶ Y' ×_Y Y')`
as `res₁(c')`. -/
def envelopeDescentRes₂ (hgys : G.IsNaturalUnderBaseChangeIso)
    (c' : BivariantClass C G (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) p) :
    BivariantClass C G
      (pullback.fst (pullback.fst f g) (pullback.fst f g) ≫ (pullback.fst f g ≫ sX))
      (pullback.fst g g ≫ (g ≫ sY)) (envelopeFibreSquareMap f g)
      (envelopeFibreSquareMap_comp_structureMorphism C sX sY f hf g) p :=
  (bivariantTransport C G _ _ _ _
    (pullbackSnd_comp_structureMorphism_eq C _ _ _
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) (pullback.snd g g))
    _ (envelopeFibreSquareMap_comp_structureMorphism' C sX sY f hf g)
    (envelopeFibreSquareSndIso f g) (envelopeFibreSquareSndIso_hom_map f g) p hgys
    (bivariantRestriction C G _ _ _ _ (pullback.snd g g) p hgys c')).congrBase
      (by rw [← pullback.condition_assoc])
      (envelopeFibreSquareMap_comp_structureMorphism C sX sY f hf g)

end Restrictions

/-! ### Capping upstairs and pushing down -/

section Push

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (g : Y' ⟶ Y) [IsProper g] (p : ℤ)
  (c' : BivariantClass C G (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
    (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) p)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f] [IsProper g] in
/-- The comparison morphism commutes with the structure morphisms over the base. -/
theorem envelopeDescentMap_comp_structureMorphism {T T₀ : Scheme.{u}} (t : T ⟶ Y) (e : T₀ ⟶ T)
    (m : T₀ ⟶ Y') (hm : m ≫ g = e ≫ t) :
    envelopeDescentMap f g t e m hm ≫ (pullback.fst f t ≫ sX) =
      pullback.fst (pullback.snd f g) m ≫ (pullback.fst f g ≫ sX) := by
  simp

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType f] [IsProper g] in
/-- The structure morphisms of `T₀` read through `e` and through `m` agree. -/
theorem envelopeDescent_comp_structureMorphism {T T₀ : Scheme.{u}} (t : T ⟶ Y) (e : T₀ ⟶ T)
    (m : T₀ ⟶ Y') (hm : m ≫ g = e ≫ t) : e ≫ (t ≫ sY) = m ≫ (g ≫ sY) := by
  rw [← Category.assoc, ← hm, Category.assoc]

/-- The operation `γ ↦ e'_*(c' ∩ γ)` attached to a factorization `m ≫ g = e ≫ t` of a proper
morphism `e : T₀ ⟶ T` to a test scheme: cap with `c'` on the test scheme `m : T₀ ⟶ Y'` and push
forward along the comparison morphism `X' ×_{Y'} T₀ ⟶ X ×_Y T`. -/
def envelopeDescentPush {T T₀ : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (e : T₀ ⟶ T)
    [IsProper e] (m : T₀ ⟶ Y') [LocallyOfFiniteType m] (hm : m ≫ g = e ≫ t) (k : ℤ) :
    chowGroup C (m ≫ (g ≫ sY)) k →+ chowGroup C (pullback.fst f t ≫ sX) (k - p) :=
  (chowPush C _ _ (envelopeDescentMap f g t e m hm)
    (envelopeDescentMap_comp_structureMorphism C sX f g t e m hm) (k - p)).comp (c'.cap m k)

/-- The pushforward `e_* : A_k(T₀) ⟶ A_k(T)` of such a factorization. -/
abbrev envelopeLiftPush {T T₀ : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (e : T₀ ⟶ T)
    [IsProper e] (m : T₀ ⟶ Y') [LocallyOfFiniteType m] (hm : m ≫ g = e ≫ t) (k : ℤ) :
    chowGroup C (m ≫ (g ≫ sY)) k →+ chowGroup C (t ≫ sY) k :=
  chowPush C _ _ e (envelopeDescent_comp_structureMorphism C sY g t e m hm) k

/-- The value of `envelopeDescentPush` at `γ` is the pushforward along the comparison morphism
of `c' ∩ γ`. -/
theorem envelopeDescentPush_apply {T T₀ : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    (e : T₀ ⟶ T) [IsProper e] (m : T₀ ⟶ Y') [LocallyOfFiniteType m] (hm : m ≫ g = e ≫ t) (k : ℤ)
    (γ : chowGroup C (m ≫ (g ≫ sY)) k) :
    envelopeDescentPush C G sX sY f hf g p c' t e m hm k γ =
      chowPush C _ _ (envelopeDescentMap f g t e m hm)
        (envelopeDescentMap_comp_structureMorphism C sX f g t e m hm) (k - p) (c'.cap m k γ) :=
  rfl

/-- The descended operation is unchanged by replacing `e` and `m` by equal morphisms. -/
theorem envelopeDescentPush_congr {T T₀ : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    {e e' : T₀ ⟶ T} [IsProper e] [IsProper e'] {m m' : T₀ ⟶ Y'} [LocallyOfFiniteType m]
    [LocallyOfFiniteType m']
    (he : e = e') (hmm : m = m') (hm : m ≫ g = e ≫ t) (hm' : m' ≫ g = e' ≫ t) (k : ℤ)
    (hq : m ≫ (g ≫ sY) = m' ≫ (g ≫ sY)) (γ : chowGroup C (m ≫ (g ≫ sY)) k) :
    envelopeDescentPush C G sX sY f hf g p c' t e m hm k γ =
      envelopeDescentPush C G sX sY f hf g p c' t e' m' hm' k (chowGroupCongr C hq k γ) := by
  subst he
  subst hmm
  rfl

/-- The lifting pushforward is unchanged by replacing `e` and `m` by equal morphisms. -/
theorem envelopeLiftPush_congr {T T₀ : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    {e e' : T₀ ⟶ T} [IsProper e] [IsProper e'] {m m' : T₀ ⟶ Y'} [LocallyOfFiniteType m]
    [LocallyOfFiniteType m']
    (he : e = e') (hmm : m = m') (hm : m ≫ g = e ≫ t) (hm' : m' ≫ g = e' ≫ t) (k : ℤ)
    (hq : m ≫ (g ≫ sY) = m' ≫ (g ≫ sY)) (γ : chowGroup C (m ≫ (g ≫ sY)) k) :
    envelopeLiftPush C sY g t e m hm k γ =
      envelopeLiftPush C sY g t e' m' hm' k (chowGroupCongr C hq k γ) := by
  subst he
  subst hmm
  rfl

/-- **The descended operation commutes with proper pushforward upstairs.** For a proper
`φ : T₁ ⟶ T₀`, pushing a class forward along `φ` and then applying the operation of `(e, m)` is
the operation of `(φ ≫ e, φ ≫ m)`. -/
theorem envelopeDescentPush_chowPush {T T₀ T₁ : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    (e : T₀ ⟶ T) [IsProper e] (m : T₀ ⟶ Y') [LocallyOfFiniteType m] (hm : m ≫ g = e ≫ t)
    (φ : T₁ ⟶ T₀) [IsProper φ]
    (k : ℤ) (γ : chowGroup C ((φ ≫ m) ≫ (g ≫ sY)) k) :
    envelopeDescentPush C G sX sY f hf g p c' t e m hm k
        (chowPush C _ _ φ (by simp [Category.assoc]) k γ) =
      envelopeDescentPush C G sX sY f hf g p c' t (φ ≫ e) (φ ≫ m)
        (by rw [Category.assoc, hm, Category.assoc]) k γ := by
  have sq := isPullback_bivariantBaseChangeMap (pullback.snd f g) m φ
  have hfst : bivariantBaseChangeMap (pullback.snd f g) m φ ≫ pullback.fst (pullback.snd f g) m =
      pullback.fst (pullback.snd f g) (φ ≫ m) := by simp [bivariantBaseChangeMap]
  have hnat := c'.proper_naturality m φ (bivariantBaseChangeMap (pullback.snd f g) m φ) sq hfst k
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _) γ
  rw [envelopeDescentPush_apply, envelopeDescentPush_apply]
  refine (congrArg (chowPush C _ _ (envelopeDescentMap f g t e m hm)
    (envelopeDescentMap_comp_structureMorphism C sX f g t e m hm) (k - p)) hnat).trans ?_
  exact chowPush_comp C _ _ _ _ _ _ (by
    rw [← baseChangeMapOfEq_comp_envelopeDescentMap f g t e m hm φ (φ ≫ m) rfl]
    rfl) _ _ _ _ _

/-- **The descent condition, pointwise.** If the two restrictions `res₁(c')` and `res₂(c')`
agree, then for two factorizations `m₁ ≫ g = e ≫ t = m₂ ≫ g` of one proper morphism `e` to a test
scheme the two descended operations agree. -/
theorem envelopeDescentPush_eq_of_res_eq (hgys : G.IsNaturalUnderBaseChangeIso)
    (hres : envelopeDescentRes₁ C G sX sY f hf g p hgys c' =
      envelopeDescentRes₂ C G sX sY f hf g p hgys c')
    {T T₀ : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (e : T₀ ⟶ T) [IsProper e]
    (m₁ m₂ : T₀ ⟶ Y') [LocallyOfFiniteType m₁] [LocallyOfFiniteType m₂]
    (h₁ : m₁ ≫ g = e ≫ t) (h₂ : m₂ ≫ g = e ≫ t) (k : ℤ)
    (hq : m₁ ≫ (g ≫ sY) = m₂ ≫ (g ≫ sY)) (γ : chowGroup C (m₁ ≫ (g ≫ sY)) k) :
    envelopeDescentPush C G sX sY f hf g p c' t e m₁ h₁ k γ =
      envelopeDescentPush C G sX sY f hf g p c' t e m₂ h₂ k (chowGroupCongr C hq k γ) := by
  set w : T₀ ⟶ pullback g g := pullback.lift m₁ m₂ (h₁.trans h₂.symm) with hw
  have hw₁ : w ≫ pullback.fst g g = m₁ := pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd g g = m₂ := pullback.lift_snd _ _ _
  have : LocallyOfFiniteType w := by
    have : LocallyOfFiniteType (w ≫ pullback.fst g g) := by rw [hw₁]; infer_instance
    exact locallyOfFiniteType_of_comp w (pullback.fst g g)
  have hw₁' : (w ≫ pullback.fst g g) ≫ g = e ≫ t := by rw [hw₁, h₁]
  have hw₂' : (w ≫ pullback.snd g g) ≫ g = e ≫ t := by rw [hw₂, h₂]
  set i₁ := pullbackLeftPullbackSndIso (pullback.snd f g) (pullback.fst g g) w with hi₁
  set i₂ := pullbackLeftPullbackSndIso (pullback.snd f g) (pullback.snd g g) w with hi₂
  set τ₁ := transportPullbackIso (pullback.snd (pullback.snd f g) (pullback.fst g g))
    (envelopeFibreSquareMap f g) (envelopeFibreSquareFstIso f g)
    (envelopeFibreSquareFstIso_hom_map f g) w with hτ₁
  set τ₂ := transportPullbackIso (pullback.snd (pullback.snd f g) (pullback.snd g g))
    (envelopeFibreSquareMap f g) (envelopeFibreSquareSndIso f g)
    (envelopeFibreSquareSndIso_hom_map f g) w with hτ₂
  set H₁ := envelopeDescentMap f g t e (w ≫ pullback.fst g g) hw₁' with hH₁
  set H₂ := envelopeDescentMap f g t e (w ≫ pullback.snd g g) hw₂' with hH₂
  set K := τ₁.inv ≫ i₁.hom ≫ H₁ with hK
  have hK₁ : i₁.inv ≫ τ₁.hom ≫ K = H₁ := by simp [hK]
  have hK₂ : i₂.inv ≫ τ₂.hom ≫ K = H₂ := by
    refine pullback.hom_ext ?_ ?_
    · simp [hK, hH₁, hH₂, hτ₁, hτ₂, hi₁, hi₂]
    · simp [hK, hH₁, hH₂, hτ₁, hτ₂, hi₁, hi₂]
  have hKs : K ≫ (pullback.fst f t ≫ sX) = pullback.fst (envelopeFibreSquareMap f g) w ≫
      (pullback.fst (pullback.fst f g) (pullback.fst f g) ≫ (pullback.fst f g ≫ sX)) := by
    simp [hK, hH₁, hτ₁, hi₁]
  have hwq : m₁ ≫ (g ≫ sY) = w ≫ (pullback.fst g g ≫ (g ≫ sY)) := by
    rw [← Category.assoc w, hw₁]
  have hcap := congrArg (fun c ↦ chowPush C _ _ K hKs (k - p) (c.cap w k
    (chowGroupCongr C hwq k γ))) hres
  unfold envelopeDescentRes₂ at hcap
  rw [BivariantClass.congrBase_cap] at hcap
  change chowPush C _ _ K hKs (k - p) (chowPushforwardOfIso C _ _ τ₁.hom _ (k - p)
      (chowPushforwardOfIso C _ _ i₁.inv _ (k - p) (c'.cap (w ≫ pullback.fst g g) k
        (chowGroupCongr C (Category.assoc w (pullback.fst g g) (g ≫ sY)).symm k
          (chowGroupCongr C hwq k γ))))) =
    chowPush C _ _ K hKs (k - p) (chowPushforwardOfIso C _ _ τ₂.hom _ (k - p)
      (chowPushforwardOfIso C _ _ i₂.inv _ (k - p) (c'.cap (w ≫ pullback.snd g g) k
        (chowGroupCongr C (Category.assoc w (pullback.snd g g) (g ≫ sY)).symm k
          (chowGroupCongr C _ k (chowGroupCongr C hwq k γ)))))) at hcap
  rw [chowPush_chowPushforwardOfIso, chowPush_chowPushforwardOfIso,
    chowPush_chowPushforwardOfIso, chowPush_chowPushforwardOfIso,
    chowGroupCongr_chowGroupCongr, chowGroupCongr_chowGroupCongr,
    chowGroupCongr_chowGroupCongr] at hcap
  · rw [chowPush_congr C _ _ hK₁ _
        (envelopeDescentMap_comp_structureMorphism C sX f g t e _ hw₁') (k - p),
      chowPush_congr C _ _ hK₂ _
        (envelopeDescentMap_comp_structureMorphism C sX f g t e _ hw₂') (k - p)] at hcap
    rw [envelopeDescentPush_congr C G sX sY f hf g p c' t rfl hw₁.symm h₁ hw₁' k
        (by rw [hw₁]) γ,
      envelopeDescentPush_congr C G sX sY f hf g p c' t rfl hw₂.symm h₂ hw₂' k
        (by rw [hw₂]) (chowGroupCongr C hq k γ), chowGroupCongr_chowGroupCongr]
    exact hcap
  all_goals simp [hK, hH₁, hτ₁, hi₁, hτ₂, hi₂]

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType f] in
/-- Every class on a test scheme `T` lifts along the base change `Y' ×_Y T ⟶ T` of an
envelope. -/
theorem exists_envelopeLiftPush_eq (hgE : IsEnvelope g) {T : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (k : ℤ) (β : chowGroup C (t ≫ sY) k) :
    ∃ β' : chowGroup C (pullback.fst g t ≫ (g ≫ sY)) k,
      envelopeLiftPush C sY g t (pullback.snd g t) (pullback.fst g t) pullback.condition k β' =
        β := by
  have henv : IsEnvelope (pullback.snd g t) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {A B : Scheme.{u}} (q : A ⟶ B) ↦ IsEnvelope q)
      (IsPullback.of_hasPullback g t) hgE
  obtain ⟨β', hβ'⟩ := envelope_chow_surjective C (t ≫ sY) (pullback.snd g t) henv k
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ rfl k) β
  have hT : pullback.snd g t ≫ (t ≫ sY) = pullback.fst g t ≫ (g ≫ sY) :=
    envelopeDescent_comp_structureMorphism C sY g t _ _ pullback.condition
  refine ⟨chowGroupCongr C hT k β', ?_⟩
  have key := properChowPushforward_chowGroupCongr C hT (rfl : t ≫ sY = t ≫ sY)
    (pullback.snd g t) rfl (envelopeDescent_comp_structureMorphism C sY g t _ _ pullback.condition)
    k (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ k)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ k) β'
  exact key.symm.trans hβ'

/-- **Well-definedness of the descended operation, at the canonical lift.** Two classes on
`Y' ×_Y T` with the same pushforward to `T` have the same descended image. -/
theorem envelopeDescentPush_canonical_eq (hgys : G.IsNaturalUnderBaseChangeIso)
    (hres : envelopeDescentRes₁ C G sX sY f hf g p hgys c' =
      envelopeDescentRes₂ C G sX sY f hf g p hgys c')
    (hgE : IsEnvelope g) {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ)
    (β₁ β₂ : chowGroup C (pullback.fst g t ≫ (g ≫ sY)) k)
    (h : envelopeLiftPush C sY g t (pullback.snd g t) (pullback.fst g t) pullback.condition k β₁ =
      envelopeLiftPush C sY g t (pullback.snd g t) (pullback.fst g t) pullback.condition k β₂) :
    envelopeDescentPush C G sX sY f hf g p c' t (pullback.snd g t) (pullback.fst g t)
        pullback.condition k β₁ =
      envelopeDescentPush C G sX sY f hf g p c' t (pullback.snd g t) (pullback.fst g t)
        pullback.condition k β₂ := by
  set gt := pullback.snd g t with hgt
  set ut := pullback.fst g t with hut
  have hT : ut ≫ (g ≫ sY) = gt ≫ (t ≫ sY) :=
    (envelopeDescent_comp_structureMorphism C sY g t _ _ pullback.condition).symm
  have hcd : IsCompletelyDecomposed gt :=
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {A B : Scheme.{u}} (q : A ⟶ B) ↦ IsEnvelope q)
      (IsPullback.of_hasPullback g t) hgE).isCompletelyDecomposed
  rw [← sub_eq_zero, ← map_sub]
  set δ := β₁ - β₂ with hδ
  have hδ0 : chowPush C (gt ≫ (t ≫ sY)) (t ≫ sY) gt rfl k (chowGroupCongr C hT k δ) = 0 := by
    have h0 : envelopeLiftPush C sY g t gt ut pullback.condition k δ = 0 := by
      rw [hδ, map_sub, h, sub_self]
    have key := properChowPushforward_chowGroupCongr C hT (rfl : t ≫ sY = t ≫ sY) gt
      (envelopeDescent_comp_structureMorphism C sY g t _ _ pullback.condition) rfl k
      (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ k)
      (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ k) δ
    exact key.symm.trans h0
  obtain ⟨γ, hγ⟩ := (envelope_chow_exact C (t ≫ sY) gt k hcd _).1 hδ0
  set P := pullback.fst gt gt with hP
  set Q := pullback.snd gt gt with hQ
  have hPe : (P ≫ ut) ≫ g = (P ≫ gt) ≫ t := by
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hQe : (Q ≫ ut) ≫ g = (P ≫ gt) ≫ t := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← pullback.condition,
      Category.assoc]
  have hPq : P ≫ gt ≫ (t ≫ sY) = (P ≫ ut) ≫ (g ≫ sY) := by
    rw [Category.assoc, hT]
  have hQq : P ≫ gt ≫ (t ≫ sY) = (Q ≫ ut) ≫ (g ≫ sY) := by
    rw [Category.assoc Q, hT, ← Category.assoc P, ← Category.assoc Q,
      show P ≫ gt = Q ≫ gt from pullback.condition]
  have hδ' : δ = chowGroupCongr C hT.symm k (chowGroupCongr C hT k δ) := by
    rw [chowGroupCongr_chowGroupCongr]; rfl
  have hpush (R : pullback gt gt ⟶ pullback g t) [IsProper R]
      (hR : R ≫ (gt ≫ (t ≫ sY)) = P ≫ gt ≫ (t ≫ sY))
      (hRq : P ≫ gt ≫ (t ≫ sY) = (R ≫ ut) ≫ (g ≫ sY)) :
      chowGroupCongr C hT.symm k (chowPush C _ _ R hR k γ) =
        chowPush C ((R ≫ ut) ≫ (g ≫ sY)) (ut ≫ (g ≫ sY)) R (by simp [Category.assoc]) k
          (chowGroupCongr C hRq k γ) :=
    properChowPushforward_chowGroupCongr C hRq hT.symm R hR _ k _ _ γ
  rw [hδ', hγ, map_sub, map_sub,
    hpush P rfl hPq, hpush Q (pullback_snd_comp_eq_pullback_fst_comp gt (t ≫ sY)) hQq,
    envelopeDescentPush_chowPush, envelopeDescentPush_chowPush,
    envelopeDescentPush_eq_of_res_eq C G sX sY f hf g p c' hgys hres t (P ≫ gt) (P ≫ ut)
      (Q ≫ ut) hPe hQe k (by rw [← hPq, hQq]),
    envelopeDescentPush_congr C G sX sY f hf g p c' t
      (show P ≫ gt = Q ≫ gt from pullback.condition) rfl hQe
      (by rw [Category.assoc, pullback.condition, Category.assoc]) k rfl,
    chowGroupCongr_chowGroupCongr, chowGroupCongr_chowGroupCongr, sub_self]

/-- **Reduction to the canonical lift.** For a proper `e : T₀ ⟶ T` factoring through `g` as
`m ≫ g = e ≫ t`, every class `γ` on `T₀` has a class `β'` on `Y' ×_Y T` with the same pushforward
to `T` and the same descended image, for the canonical factorization of `Y' ×_Y T ⟶ T`. -/
theorem exists_canonical_envelopeDescentPush {T T₀ : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (e : T₀ ⟶ T) [IsProper e] (m : T₀ ⟶ Y') [LocallyOfFiniteType m]
    (hm : m ≫ g = e ≫ t) (k : ℤ) (γ : chowGroup C (m ≫ (g ≫ sY)) k) :
    ∃ β' : chowGroup C (pullback.fst g t ≫ (g ≫ sY)) k,
      envelopeLiftPush C sY g t (pullback.snd g t) (pullback.fst g t) pullback.condition k β' =
        envelopeLiftPush C sY g t e m hm k γ ∧
      envelopeDescentPush C G sX sY f hf g p c' t (pullback.snd g t) (pullback.fst g t)
          pullback.condition k β' =
        envelopeDescentPush C G sX sY f hf g p c' t e m hm k γ := by
  set φ : T₀ ⟶ pullback g t := pullback.lift m e hm with hφ
  have hφ₁ : φ ≫ pullback.fst g t = m := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ pullback.snd g t = e := pullback.lift_snd _ _ _
  have : IsProper φ := MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated) φ
    (pullback.snd g t) inferInstance (by rw [hφ₂]; infer_instance)
  have hq : m ≫ (g ≫ sY) = (φ ≫ pullback.fst g t) ≫ (g ≫ sY) := by rw [hφ₁]
  have hcond : (φ ≫ pullback.fst g t) ≫ g = (φ ≫ pullback.snd g t) ≫ t := by
    rw [Category.assoc, pullback.condition, Category.assoc]
  refine ⟨chowPush C _ _ φ (by simp [Category.assoc]) k (chowGroupCongr C hq k γ), ?_, ?_⟩
  · rw [chowPush_comp C _ _ _ φ (pullback.snd g t) (φ ≫ pullback.snd g t) rfl _ _
      (envelopeDescent_comp_structureMorphism C sY g t _ _ hcond) k]
    · show envelopeLiftPush C sY g t (φ ≫ pullback.snd g t) (φ ≫ pullback.fst g t) hcond k
        (chowGroupCongr C hq k γ) = _
      rw [envelopeLiftPush_congr C sY g t hφ₂ hφ₁ hcond hm k hq.symm, chowGroupCongr_chowGroupCongr]
      rfl
  · rw [envelopeDescentPush_chowPush,
      envelopeDescentPush_congr C G sX sY f hf g p c' t hφ₂ hφ₁ _ hm k hq.symm,
      chowGroupCongr_chowGroupCongr]
    rfl

/-- **Well-definedness of the descended operation.** Two factorizations through `g` of proper
morphisms to a test scheme, together with classes having the same pushforward to the test scheme,
have the same descended image. -/
theorem envelopeDescentPush_eq_of_envelopeLiftPush_eq (hgys : G.IsNaturalUnderBaseChangeIso)
    (hres : envelopeDescentRes₁ C G sX sY f hf g p hgys c' =
      envelopeDescentRes₂ C G sX sY f hf g p hgys c')
    (hgE : IsEnvelope g) {T T₁ T₂ : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    (e₁ : T₁ ⟶ T) [IsProper e₁] (m₁ : T₁ ⟶ Y') [LocallyOfFiniteType m₁] (h₁ : m₁ ≫ g = e₁ ≫ t)
    (e₂ : T₂ ⟶ T) [IsProper e₂] (m₂ : T₂ ⟶ Y') [LocallyOfFiniteType m₂] (h₂ : m₂ ≫ g = e₂ ≫ t)
    (k : ℤ) (γ₁ : chowGroup C (m₁ ≫ (g ≫ sY)) k) (γ₂ : chowGroup C (m₂ ≫ (g ≫ sY)) k)
    (h : envelopeLiftPush C sY g t e₁ m₁ h₁ k γ₁ = envelopeLiftPush C sY g t e₂ m₂ h₂ k γ₂) :
    envelopeDescentPush C G sX sY f hf g p c' t e₁ m₁ h₁ k γ₁ =
      envelopeDescentPush C G sX sY f hf g p c' t e₂ m₂ h₂ k γ₂ := by
  obtain ⟨β₁, hl₁, hd₁⟩ :=
    exists_canonical_envelopeDescentPush C G sX sY f hf g p c' t e₁ m₁ h₁ k γ₁
  obtain ⟨β₂, hl₂, hd₂⟩ :=
    exists_canonical_envelopeDescentPush C G sX sY f hf g p c' t e₂ m₂ h₂ k γ₂
  rw [← hd₁, ← hd₂]
  exact envelopeDescentPush_canonical_eq C G sX sY f hf g p c' hgys hres hgE t k β₁ β₂
    (by rw [hl₁, hl₂, h])

end Push

/-! ### The descended cap operation -/

section Cap

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Y' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (g : Y' ⟶ Y) [IsProper g] (p : ℤ)
  (c' : BivariantClass C G (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
    (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g) p)
  (hgys : G.IsNaturalUnderBaseChangeIso)
  (hres : envelopeDescentRes₁ C G sX sY f hf g p hgys c' =
    envelopeDescentRes₂ C G sX sY f hf g p hgys c')
  (hgE : IsEnvelope g)

/-- **The cap operation `c ∩ -` of Stacks 0GUC.** On a test scheme `t : T ⟶ Y`, a class `β` is
lifted to `β'` on `Y' ×_Y T` along the envelope `Y' ×_Y T ⟶ T`, and `c ∩ β = h_*(c' ∩ β')`. -/
def envelopeDescentCap {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ) :
    chowGroup C (t ≫ sY) k →+ chowGroup C (pullback.fst f t ≫ sX) (k - p) :=
  (QuotientAddGroup.lift
      (envelopeLiftPush C sY g t (pullback.snd g t) (pullback.fst g t) pullback.condition k).ker
      (envelopeDescentPush C G sX sY f hf g p c' t (pullback.snd g t) (pullback.fst g t)
        pullback.condition k) (fun β hβ ↦ by
          rw [AddMonoidHom.mem_ker] at hβ ⊢
          have := envelopeDescentPush_canonical_eq C G sX sY f hf g p c' hgys hres hgE t k β 0
            (by rw [hβ, map_zero])
          rwa [map_zero] at this)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (fun β ↦ exists_envelopeLiftPush_eq C sY g hgE t k β)).symm.toAddMonoidHom

/-- **The defining property of the descended cap operation.** For any proper `e : T₀ ⟶ T` with
`e ≫ t` factoring through `g` as `m ≫ g`, `c ∩ e_* γ = h_*(c' ∩ γ)`. -/
theorem envelopeDescentCap_envelopeLiftPush {T T₀ : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (e : T₀ ⟶ T) [IsProper e] (m : T₀ ⟶ Y') [LocallyOfFiniteType m]
    (hm : m ≫ g = e ≫ t) (k : ℤ) (γ : chowGroup C (m ≫ (g ≫ sY)) k) :
    envelopeDescentCap C G sX sY f hf g p c' hgys hres hgE t k
        (envelopeLiftPush C sY g t e m hm k γ) =
      envelopeDescentPush C G sX sY f hf g p c' t e m hm k γ := by
  obtain ⟨β', hl, hd⟩ := exists_canonical_envelopeDescentPush C G sX sY f hf g p c' t e m hm k γ
  rw [← hl, ← hd]
  have hsurj := fun β ↦ exists_envelopeLiftPush_eq C sY g hgE t k β
  have h1 : (QuotientAddGroup.quotientKerEquivOfSurjective _ hsurj).symm
      (envelopeLiftPush C sY g t (pullback.snd g t) (pullback.fst g t) pullback.condition k β') =
      QuotientAddGroup.mk β' := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  unfold envelopeDescentCap
  rw [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h1, QuotientAddGroup.lift_mk]

/-- **Stacks 0B76 (1) for the descended cap operation.** -/
theorem envelopeDescentCap_proper_naturality {T T' : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [IsProper h] (h' : pullback f (h ≫ t) ⟶ pullback f t)
    (sq : IsPullback (pullback.snd f (h ≫ t)) h' h (pullback.snd f t))
    (hfst : h' ≫ pullback.fst f t = pullback.fst f (h ≫ t)) (k : ℤ) :
    letI : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    ∀ (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ t) ≫ sY) (t ≫ sY) h
        (by simp [Category.assoc]) k)
      (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
        (pullback.fst f (h ≫ t) ≫ sX) (pullback.fst f t ≫ sX) h'
        (by rw [← Category.assoc, hfst]) (k - p))
      (α : chowGroup C ((h ≫ t) ≫ sY) k),
      envelopeDescentCap C G sX sY f hf g p c' hgys hres hgE t k
          (properChowPushforward C ((h ≫ t) ≫ sY) (t ≫ sY) h (by simp [Category.assoc]) k hfac
            α) =
        properChowPushforward C (pullback.fst f (h ≫ t) ≫ sX) (pullback.fst f t ≫ sX) h'
          (by rw [← Category.assoc, hfst]) (k - p) hfac'
          (envelopeDescentCap C G sX sY f hf g p c' hgys hres hgE (h ≫ t) k α) := by
  let : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
  intro hfac hfac' α
  obtain ⟨β', rfl⟩ := exists_envelopeLiftPush_eq C sY g hgE (h ≫ t) k α
  have hm : pullback.fst g (h ≫ t) ≫ g = (pullback.snd g (h ≫ t) ≫ h) ≫ t := by
    rw [pullback.condition, Category.assoc]
  have hlift : properChowPushforward C ((h ≫ t) ≫ sY) (t ≫ sY) h (by simp [Category.assoc]) k
      hfac (envelopeLiftPush C sY g (h ≫ t) (pullback.snd g (h ≫ t)) (pullback.fst g (h ≫ t))
        pullback.condition k β') =
      envelopeLiftPush C sY g t (pullback.snd g (h ≫ t) ≫ h) (pullback.fst g (h ≫ t)) hm k β' :=
    chowPush_comp C _ _ _ _ _ _ rfl _ _ _ k β'
  rw [hlift, envelopeDescentCap_envelopeLiftPush, envelopeDescentCap_envelopeLiftPush,
    envelopeDescentPush_apply, envelopeDescentPush_apply]
  show _ = chowPush C _ _ h' _ (k - p) _
  rw [chowPush_comp C _ _ _ _ h' _
    (envelopeDescentMap_comp_baseChange f g (h ≫ t) _ _ _ t h h' hfst sq.w.symm hm)]

/-- A base change of a flat morphism of finite type and relative dimension `r` is again flat, of
finite type and of relative dimension `r`. -/
private theorem locallyOfFiniteType_and_flat_and_relativeDimension_of_isPullback
    {A B D E : Scheme.{u}} {a : A ⟶ B} {b : A ⟶ D} {c : B ⟶ E} {d : D ⟶ E} (sq : IsPullback a b c d)
    [LocallyOfFiniteType c] [Flat c] {r : ℕ} (hr : AlgebraicGeometry.RelativeDimension c r) :
    ∃ _ : LocallyOfFiniteType b, Flat b ∧ AlgebraicGeometry.RelativeDimension b r :=
  have : LocallyOfFiniteType b := MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) ‹_›
  ⟨this, MorphismProperty.of_isPullback sq (P := @Flat) ‹_›,
    AlgebraicGeometry.RelativeDimension.of_isPullback sq hr⟩

omit [LocallyOfFiniteType f] [IsProper g] in
/-- The square formed by the comparison morphisms over a flat morphism `h : T' ⟶ T` of test
schemes is cartesian. -/
theorem isPullback_envelopeDescentMap_flat {T T' : Scheme.{u}} (t : T ⟶ Y) (h : T' ⟶ T)
    (h' : pullback f (h ≫ t) ⟶ pullback f t)
    (sq : IsPullback (pullback.snd f (h ≫ t)) h' h (pullback.snd f t))
    (hfst : h' ≫ pullback.fst f t = pullback.fst f (h ≫ t)) :
    IsPullback
      (bivariantBaseChangeMap (pullback.snd f g) (pullback.fst g t)
        (pullback.fst (pullback.snd g t) h))
      (envelopeDescentMap f g (h ≫ t) (pullback.snd (pullback.snd g t) h)
        (pullback.fst (pullback.snd g t) h ≫ pullback.fst g t)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc]))
      (envelopeDescentMap f g t (pullback.snd g t) (pullback.fst g t) pullback.condition) h' := by
  set ĥ := pullback.fst (pullback.snd g t) h
  set w₂ := pullback.snd (pullback.snd g t) h
  have s₁ := (isPullback_bivariantBaseChangeMap (pullback.snd f g) (pullback.fst g t) ĥ).flip
  have s₂ := IsPullback.of_hasPullback (pullback.snd g t) h
  have hs := s₁.paste_vert s₂
  refine IsPullback.of_bot ?_ ?_ sq.flip
  · rw [envelopeDescentMap_snd, envelopeDescentMap_snd]
    exact hs
  · refine pullback.hom_ext ?_ ?_
    · simp [Category.assoc, hfst, bivariantBaseChangeMap]
    · simp only [Category.assoc, envelopeDescentMap_snd]
      rw [← sq.w, envelopeDescentMap_snd_assoc]
      simp [bivariantBaseChangeMap, pullback.condition]

/-- **Stacks 0B76 (2) for the descended cap operation.** -/
theorem envelopeDescentCap_flat_naturality {T T' : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (h' : pullback f (h ≫ t) ⟶ pullback f t)
    (sq : IsPullback (pullback.snd f (h ≫ t)) h' h (pullback.snd f t))
    (hfst : h' ≫ pullback.fst f t = pullback.fst f (h ≫ t)) (k : ℤ) :
    letI : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    letI : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    ∀ (hr' : AlgebraicGeometry.RelativeDimension h' r)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ t) ≫ sY) (t ≫ sY) h
        (by simp [Category.assoc]) r hr k)
      (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
        (pullback.fst f (h ≫ t) ≫ sX) (pullback.fst f t ≫ sX) h'
        (by rw [← Category.assoc, hfst]) r hr' (k - p))
      (α : chowGroup C (t ≫ sY) k),
      HEq
        (envelopeDescentCap C G sX sY f hf g p c' hgys hres hgE (h ≫ t) (k + (r : ℤ))
          (flatPullbackChow C ((h ≫ t) ≫ sY) (t ≫ sY) h (by simp [Category.assoc]) r hr k
            hfac α))
        (flatPullbackChow C (pullback.fst f (h ≫ t) ≫ sX) (pullback.fst f t ≫ sX) h'
          (by rw [← Category.assoc, hfst]) r hr' (k - p) hfac'
          (envelopeDescentCap C G sX sY f hf g p c' hgys hres hgE t k α)) := by
  obtain ⟨_, _, -⟩ := locallyOfFiniteType_and_flat_and_relativeDimension_of_isPullback sq hr
  intro hr' hfac hfac' α
  obtain ⟨β', rfl⟩ := exists_envelopeLiftPush_eq C sY g hgE t k α
  set g₁ := pullback.snd g t with hg₁
  set t₁ := pullback.fst g t with ht₁
  set ĥ := pullback.fst g₁ h with hĥ
  set w₂ := pullback.snd g₁ h with hw₂
  have hsq₀ : IsPullback ĥ w₂ g₁ h := IsPullback.of_hasPullback g₁ h
  obtain ⟨_, _, hĥr⟩ :=
    locallyOfFiniteType_and_flat_and_relativeDimension_of_isPullback hsq₀.flip hr
  have hm₂ : (ĥ ≫ t₁) ≫ g = w₂ ≫ (h ≫ t) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hsq₀.w, Category.assoc]
  have hdown := properPushforwardFlatPullbackBaseChange C (t₁ ≫ (g ≫ sY))
    ((ĥ ≫ t₁) ≫ (g ≫ sY)) (t ≫ sY) ((h ≫ t) ≫ sY) g₁
    (envelopeDescent_comp_structureMorphism C sY g t _ _ pullback.condition) w₂
    (envelopeDescent_comp_structureMorphism C sY g (h ≫ t) _ _ hm₂) ĥ (by simp [Category.assoc])
    h (by simp [Category.assoc]) hsq₀ r hĥr hr k
    (flatPullbackDescends C _ _ _ _ r hĥr k) hfac
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ k)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _) β'
  have hl : flatPullbackChow C ((h ≫ t) ≫ sY) (t ≫ sY) h (by simp [Category.assoc]) r hr k hfac
      (envelopeLiftPush C sY g t g₁ t₁ pullback.condition k β') =
      envelopeLiftPush C sY g (h ≫ t) w₂ (ĥ ≫ t₁) hm₂ (k + (r : ℤ))
        (flatPullbackChow C ((ĥ ≫ t₁) ≫ (g ≫ sY)) (t₁ ≫ (g ≫ sY)) ĥ (by simp [Category.assoc])
          r hĥr k (flatPullbackDescends C _ _ _ _ r hĥr k) β') := hdown
  rw [hl, envelopeDescentCap_envelopeLiftPush, envelopeDescentCap_envelopeLiftPush,
    envelopeDescentPush_apply, envelopeDescentPush_apply]
  have sqX := isPullback_bivariantBaseChangeMap (pullback.snd f g) t₁ ĥ
  have hfstX : bivariantBaseChangeMap (pullback.snd f g) t₁ ĥ ≫
      pullback.fst (pullback.snd f g) t₁ = pullback.fst (pullback.snd f g) (ĥ ≫ t₁) := by
    simp [bivariantBaseChangeMap]
  obtain ⟨_, _, hĥr'⟩ :=
    locallyOfFiniteType_and_flat_and_relativeDimension_of_isPullback sqX hĥr
  have hflat := c'.flat_naturality t₁ ĥ r hĥr (bivariantBaseChangeMap (pullback.snd f g) t₁ ĥ)
    sqX hfstX k hĥr' (flatPullbackDescends C _ _ _ _ r hĥr k)
    (flatPullbackDescends C _ _ _ _ r hĥr' (k - p)) β'
  have hup := properPushforwardFlatPullbackBaseChange C
    (pullback.fst (pullback.snd f g) t₁ ≫ (pullback.fst f g ≫ sX))
    (pullback.fst (pullback.snd f g) (ĥ ≫ t₁) ≫ (pullback.fst f g ≫ sX))
    (pullback.fst f t ≫ sX) (pullback.fst f (h ≫ t) ≫ sX)
    (envelopeDescentMap f g t g₁ t₁ pullback.condition)
    (envelopeDescentMap_comp_structureMorphism C sX f g t _ _ _)
    (envelopeDescentMap f g (h ≫ t) w₂ (ĥ ≫ t₁) hm₂)
    (envelopeDescentMap_comp_structureMorphism C sX f g (h ≫ t) _ _ _)
    (bivariantBaseChangeMap (pullback.snd f g) t₁ ĥ) (by rw [← Category.assoc, hfstX])
    h' (by rw [← Category.assoc, hfst])
    (isPullback_envelopeDescentMap_flat f g t h h' sq hfst) r hĥr' hr' (k - p)
    (flatPullbackDescends C _ _ _ _ r hĥr' (k - p)) hfac'
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
    (c'.cap t₁ k β')
  refine HEq.trans ?_ (heq_of_eq hup.symm)
  exact heq_map_index (by omega) hflat (fun n ↦ chowPush C _ _
    (envelopeDescentMap f g (h ≫ t) w₂ (ĥ ≫ t₁) hm₂)
    (envelopeDescentMap_comp_structureMorphism C sX f g (h ≫ t) _ _ _) n)


end Cap

end Stacks.Chow

end
