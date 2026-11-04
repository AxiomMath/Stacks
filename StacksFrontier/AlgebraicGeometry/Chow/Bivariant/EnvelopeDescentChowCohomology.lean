module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescentExistence
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.IdentityRule
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBase

/-!
# Descent of Chow cohomology classes along an envelope

Let `f : Y ⟶ X` be an envelope (Stacks 0GU5) of schemes locally of finite type over the base of
chapter 42 of the Stacks Project, with projections `pr₁, pr₂ : Y ×_X Y ⟶ Y`. A class
`c' ∈ A^p(Y)` whose operations at `t ≫ pr₁` and at `t ≫ pr₂` agree for every test scheme
`t : T ⟶ Y ×_X Y` is the restriction (Stacks 0B7F) of a unique class `c ∈ A^p(X)`. This is
Stacks 0GUC for the identity of `X`, read on the restriction map of Chow cohomology.

## Main definitions

* `Stacks.Chow.BivariantClass.isoCap` — for a bivariant class for an isomorphism `v : A ⟶ W`, the
  cap operation on a test scheme `t : T ⟶ W` followed by the pushforward along the isomorphism
  `A ×_W T ⟶ T`.

## Main results

* `Stacks.Chow.BivariantClass.eq_of_isoCap_eq` — a class for an isomorphism is determined by these
  operations.
* `Stacks.Chow.BivariantClass.isoCap_bivariantTransport`,
  `Stacks.Chow.BivariantClass.isoCap_bivariantRestriction_heq` — transport does not change them,
  and the operation of a restriction along `h` on `t` is the operation of the class on `t ≫ h`.
* `Stacks.Chow.existsUnique_chowCohomologyRestriction_eq_of_isEnvelope` — the descent.

## References

* [Stacks Project, Tag 0GUC](https://stacks.math.columbia.edu/tag/0GUC)
* [Stacks Project, Tag 0GUD](https://stacks.math.columbia.edu/tag/0GUD)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The operation of a class for an isomorphism on the test schemes -/

section IsoCap

variable (C : ChowSituation.{u}) (G : GysinSystem C) {A W : Scheme.{u}} (sA : A ⟶ C.S)
  [LocallyOfFiniteType sA] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (v : A ⟶ W)
  [LocallyOfFiniteType v] [IsIso v] (hv : v ≫ sW = sA) {p : ℤ}

/-- The operation on the test schemes of a bivariant class `c` for an isomorphism `v : A ⟶ W`:
on `t : T ⟶ W`, cap with `c` into the Chow group of `A ×_W T` and push forward along the
isomorphism `A ×_W T ⟶ T`. -/
def BivariantClass.isoCap (c : BivariantClass C G sA sW v hv p) {T : Scheme.{u}} (t : T ⟶ W)
    [LocallyOfFiniteType t] (k : ℤ) : chowGroup C (t ≫ sW) k →+ chowGroup C (t ≫ sW) (k - p) :=
  (chowPushforwardOfIso C (pullback.fst v t ≫ sA) (t ≫ sW) (pullback.snd v t)
    (pullbackSnd_comp_structureMorphism hv t) (k - p)).comp (c.cap t k)

/-- The operation of `c` on `t : T ⟶ W` sends `α` to the pushforward along the isomorphism
`A ×_W T ⟶ T` of the cap of `c` with `α`. -/
theorem BivariantClass.isoCap_apply (c : BivariantClass C G sA sW v hv p) {T : Scheme.{u}}
    (t : T ⟶ W) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sW) k) :
    c.isoCap C G sA sW v hv t k α =
      chowPushforwardOfIso C (pullback.fst v t ≫ sA) (t ≫ sW) (pullback.snd v t)
        (pullbackSnd_comp_structureMorphism hv t) (k - p) (c.cap t k α) :=
  rfl

/-- **A class for an isomorphism is determined by its operations on the test schemes.** -/
theorem BivariantClass.eq_of_isoCap_eq {c d : BivariantClass C G sA sW v hv p}
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ W) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sW) k), c.isoCap C G sA sW v hv t k α = d.isoCap C G sA sW v hv t k α) :
    c = d :=
  BivariantClass.ext C G sA sW v hv p fun t _ k α ↦
    chowPushforwardOfIso_injective C _ _ _ _ (k - p) (h t k α)

/-- For the identity of `A`, the operation is that of `Stacks.Chow.BivariantClass.idRule`. -/
theorem BivariantClass.isoCap_id (c : BivariantClass C G sA sA (𝟙 A) (Category.id_comp sA) p)
    {T : Scheme.{u}} (t : T ⟶ A) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sA) k) :
    c.isoCap C G sA sA (𝟙 A) (Category.id_comp sA) t k α = c.idRule C sA G t k α :=
  rfl

/-- The operation of a class does not depend on the presentation of the structure morphism of
the target, up to heterogeneous equality. -/
theorem BivariantClass.isoCap_congrBase_heq {sW' : W ⟶ C.S} [LocallyOfFiniteType sW']
    (hW : sW = sW') (hv' : v ≫ sW' = sA) (c : BivariantClass C G sA sW v hv p) {T : Scheme.{u}}
    (t : T ⟶ W) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sW') k)
    (α' : chowGroup C (t ≫ sW) k) (hα : α ≍ α') :
    (c.congrBase hW hv').isoCap C G sA sW' v hv' t k α ≍ c.isoCap C G sA sW v hv t k α' := by
  subst hW
  cases hα
  rfl

variable {B : Scheme.{u}} (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : B ⟶ W)
  [LocallyOfFiniteType u] [IsIso u] (hu : u ≫ sW = sB) (θ : A ≅ B) (hθ : θ.hom ≫ u = v)

/-- **Transport does not change the operation.** -/
theorem BivariantClass.isoCap_bivariantTransport (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sA sW v hv p) {T : Scheme.{u}} (t : T ⟶ W) [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ sW) k) :
    (bivariantTransport C G sA sB sW v hv u hu θ hθ p hgys c).isoCap C G sB sW u hu t k α =
      c.isoCap C G sA sW v hv t k α := by
  rw [BivariantClass.isoCap_apply, bivariantTransport_cap, bivariantTransportCap_apply,
    chowPushforwardOfIso_comp_apply, BivariantClass.isoCap_apply]
  exact chowPushforwardOfIso_congr_apply C _ _ _ _ (transportPullbackIso_hom_snd v u θ hθ t) _ _
    (k - p) _

end IsoCap

section IsoCapRestriction

variable (C : ChowSituation.{u}) (G : GysinSystem C) {A W W' : Scheme.{u}} (sA : A ⟶ C.S)
  [LocallyOfFiniteType sA] (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (v : A ⟶ W)
  [LocallyOfFiniteType v] [IsIso v] (hv : v ≫ sW = sA) {p : ℤ} (h : W' ⟶ W)
  [LocallyOfFiniteType h]

/-- **The operation of a restriction.** For a class `c` for an isomorphism `v : A ⟶ W` and
`h : W' ⟶ W`, the operation of the restriction of `c` along `h` (Stacks 0F9Z) on a test scheme
`t : T ⟶ W'` is the operation of `c` on `t ≫ h`. -/
theorem BivariantClass.isoCap_bivariantRestriction_heq (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : BivariantClass C G sA sW v hv p) {T : Scheme.{u}} (t : T ⟶ W') [LocallyOfFiniteType t]
    (k : ℤ) (α : chowGroup C (t ≫ (h ≫ sW)) k) (α' : chowGroup C ((t ≫ h) ≫ sW) k)
    (hα : α ≍ α') :
    (bivariantRestriction C G sA sW v hv h p hgys c).isoCap C G (pullback.fst v h ≫ sA) (h ≫ sW)
        (pullback.snd v h) (pullbackSnd_comp_structureMorphism_eq C sA sW v hv h) t k α ≍
      c.isoCap C G sA sW v hv (t ≫ h) k α' := by
  have hα' : chowGroupCongr C (Category.assoc t h sW).symm k α = α' :=
    eq_of_heq ((chowGroupCongr_heq C _ k α).trans hα)
  rw [BivariantClass.isoCap_apply, bivariantRestriction_cap, bivariantRestrictionCap_apply, hα',
    chowPushforwardOfIso_comp_apply, BivariantClass.isoCap_apply,
    chowPushforwardOfIso_congr_apply C _ _ _ (pullback.snd v (t ≫ h))
      (pullbackLeftPullbackSndIso_inv_snd_snd v h t) _
      (by rw [← Category.assoc t h sW]; exact pullbackSnd_comp_structureMorphism hv (t ≫ h))]
  exact chowPushforwardOfIso_heq _ _ _ rfl (Category.assoc t h sW).symm rfl HEq.rfl

end IsoCapRestriction

/-! ### Descent of Chow cohomology classes -/

section Descent

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (f : Y ⟶ X) [LocallyOfFiniteType f] (p : ℤ)

/-- A Chow cohomology class `c' ∈ A^p(Y)` read as a bivariant class for the base change
`X ×_X Y ⟶ Y` of the identity of `X` along `f : Y ⟶ X`: its transport along the canonical
isomorphism `Y ≅ X ×_X Y`. -/
def chowCohomologyDescentInput
    (c' : chowCohomologyComponent C (gysinSystemOfInvertible C) (f ≫ sX) p) :
    BivariantClass C (gysinSystemOfInvertible C) (pullback.fst (𝟙 X) f ≫ sX) (f ≫ sX)
      (pullback.snd (𝟙 X) f)
      (pullbackSnd_comp_structureMorphism_eq C sX sX (𝟙 X) (Category.id_comp sX) f) p :=
  bivariantTransport C (gysinSystemOfInvertible C) (f ≫ sX) (pullback.fst (𝟙 X) f ≫ sX) (f ≫ sX)
    (𝟙 Y) (Category.id_comp _) (pullback.snd (𝟙 X) f)
    (pullbackSnd_comp_structureMorphism_eq C sX sX (𝟙 X) (Category.id_comp sX) f)
    (identityBaseChangeIso f).symm (by simp) p
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c'

/-- The operation of the descent input on a test scheme is that of the class itself. -/
theorem isoCap_chowCohomologyDescentInput
    (c' : chowCohomologyComponent C (gysinSystemOfInvertible C) (f ≫ sX) p) {T : Scheme.{u}}
    (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    (chowCohomologyDescentInput C sX f p c').isoCap C (gysinSystemOfInvertible C)
        (pullback.fst (𝟙 X) f ≫ sX) (f ≫ sX) (pullback.snd (𝟙 X) f)
        (pullbackSnd_comp_structureMorphism_eq C sX sX (𝟙 X) (Category.id_comp sX) f) t k α =
      c'.idRule C (f ≫ sX) (gysinSystemOfInvertible C) t k α :=
  BivariantClass.isoCap_bivariantTransport C _ _ _ _ _ _ _ _ _ _ _ c' t k α

/-- The restriction along `f` of Chow cohomology classes, read through the descent input:
`res(c) = c'` exactly when the restriction of `c` to `X ×_X Y ⟶ Y` is the descent input of
`c'`. -/
theorem chowCohomologyRestriction_eq_iff
    (c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p)
    (c' : chowCohomologyComponent C (gysinSystemOfInvertible C) (f ≫ sX) p) :
    chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c = c' ↔
      bivariantRestriction C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) f p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c =
        chowCohomologyDescentInput C sX f p c' := by
  constructor
  · rintro rfl
    refine BivariantClass.eq_of_isoCap_eq C _ _ _ _ _ fun t _ k α ↦ ?_
    rw [isoCap_chowCohomologyDescentInput, ← BivariantClass.isoCap_id]
    exact (BivariantClass.isoCap_bivariantTransport C _ _ _ _ _ _ _ _ _ _
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) _ t k α).symm
  · intro h
    refine BivariantClass.eq_of_isoCap_eq C _ _ _ _ _ fun t _ k α ↦ ?_
    refine (BivariantClass.isoCap_bivariantTransport C _ _ _ _ _ _ _ _ _ _
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (bivariantRestriction C _ _ _ _ _ _ _
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c) t k α).trans ?_
    rw [h, isoCap_chowCohomologyDescentInput]
    rfl

variable {f}

/-- The morphism `X' ×_X X' ⟶ Y ×_X Y` of the descent condition of Stacks 0GUC, for the identity
of `X` and an arbitrary `f : Y ⟶ X`, is an isomorphism. -/
instance isIso_envelopeFibreSquareMap_id : IsIso (envelopeFibreSquareMap (𝟙 X) f) := by
  rw [← Iso.inv_hom_id_assoc (envelopeFibreSquareFstIso (𝟙 X) f) (envelopeFibreSquareMap (𝟙 X) f),
    envelopeFibreSquareFstIso_hom_map]
  infer_instance

/-- The operation of the transport of the restriction of the descent input of `c'` along
`h : W' ⟶ Y` on a test scheme `t : T ⟶ W'` is that of `c'` on `t ≫ h`. -/
private theorem isoCap_transport_restriction_descentInput_heq
    (c' : chowCohomologyComponent C (gysinSystemOfInvertible C) (f ≫ sX) p) {W' B : Scheme.{u}}
    (h : W' ⟶ Y) [LocallyOfFiniteType h] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : B ⟶ W')
    [LocallyOfFiniteType u] [IsIso u] (hu : u ≫ (h ≫ (f ≫ sX)) = sB)
    (θ : pullback (pullback.snd (𝟙 X) f) h ≅ B) (hθ : θ.hom ≫ u = pullback.snd _ h)
    {T : Scheme.{u}} (t : T ⟶ W') [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ (h ≫ (f ≫ sX))) k) (α' : chowGroup C ((t ≫ h) ≫ (f ≫ sX)) k)
    (hα : α ≍ α') :
    (bivariantTransport C (gysinSystemOfInvertible C) _ sB _ _ _ u hu θ hθ p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (bivariantRestriction C (gysinSystemOfInvertible C) _ _ _ _ h p
          (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
          (chowCohomologyDescentInput C sX f p c'))).isoCap C (gysinSystemOfInvertible C) sB _ u
        hu t k α ≍
      c'.idRule C (f ≫ sX) (gysinSystemOfInvertible C) (t ≫ h) k α' := by
  rw [BivariantClass.isoCap_bivariantTransport]
  refine (BivariantClass.isoCap_bivariantRestriction_heq C _ _ _ _ _ _ _ _ t k α α' hα).trans ?_
  rw [isoCap_chowCohomologyDescentInput]

/-- The descent condition of Stacks 0GUC for the descent input of `c'`, on the operation of its
first restriction: on a test scheme `t : T ⟶ Y ×_X Y`, it operates as `c'` does on `t ≫ pr₁`. -/
theorem isoCap_envelopeDescentRes₁_heq [IsProper f]
    (c' : chowCohomologyComponent C (gysinSystemOfInvertible C) (f ≫ sX) p) {T : Scheme.{u}}
    (t : T ⟶ pullback f f) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ (pullback.fst f f ≫ (f ≫ sX))) k)
    (α' : chowGroup C ((t ≫ pullback.fst f f) ≫ (f ≫ sX)) k) (hα : α ≍ α') :
    (envelopeDescentRes₁ C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (chowCohomologyDescentInput C sX f p c')).isoCap C (gysinSystemOfInvertible C) _ _
        (envelopeFibreSquareMap (𝟙 X) f)
        (envelopeFibreSquareMap_comp_structureMorphism C sX sX (𝟙 X) (Category.id_comp sX) f)
        t k α ≍
      c'.idRule C (f ≫ sX) (gysinSystemOfInvertible C) (t ≫ pullback.fst f f) k α' := by
  unfold envelopeDescentRes₁
  exact isoCap_transport_restriction_descentInput_heq C sX p c' _ _ _ _ _ _ t k α α' hα

/-- The descent condition of Stacks 0GUC for the descent input of `c'`, on the operation of its
second restriction: on a test scheme `t : T ⟶ Y ×_X Y`, it operates as `c'` does on `t ≫ pr₂`. -/
theorem isoCap_envelopeDescentRes₂_heq [IsProper f]
    (c' : chowCohomologyComponent C (gysinSystemOfInvertible C) (f ≫ sX) p) {T : Scheme.{u}}
    (t : T ⟶ pullback f f) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ (pullback.fst f f ≫ (f ≫ sX))) k)
    (α' : chowGroup C ((t ≫ pullback.snd f f) ≫ (f ≫ sX)) k) (hα : α ≍ α') :
    (envelopeDescentRes₂ C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (chowCohomologyDescentInput C sX f p c')).isoCap C (gysinSystemOfInvertible C) _ _
        (envelopeFibreSquareMap (𝟙 X) f)
        (envelopeFibreSquareMap_comp_structureMorphism C sX sX (𝟙 X) (Category.id_comp sX) f)
        t k α ≍
      c'.idRule C (f ≫ sX) (gysinSystemOfInvertible C) (t ≫ pullback.snd f f) k α' := by
  have hW : pullback.snd f f ≫ (f ≫ sX) = pullback.fst f f ≫ (f ≫ sX) := by
    rw [← pullback.condition_assoc]
  have hα'' : chowGroupCongr C (congrArg (t ≫ ·) hW.symm) k α ≍ α' :=
    (chowGroupCongr_heq C _ k α).trans hα
  unfold envelopeDescentRes₂
  refine (BivariantClass.isoCap_congrBase_heq C _ _ _ _ _ hW _ _ t k α _
    (chowGroupCongr_heq C (congrArg (t ≫ ·) hW.symm) k α).symm).trans ?_
  exact isoCap_transport_restriction_descentInput_heq C sX p c' _ _ _ _ _ _ t k _ α' hα''

/-- **Descent of Chow cohomology classes along an envelope.** Let `f : Y ⟶ X` be an envelope
and let `c' ∈ A^p(Y)` be a class whose operations on `t ≫ pr₁` and `t ≫ pr₂` agree for every
test scheme `t : T ⟶ Y ×_X Y`. Then there is a unique `c ∈ A^p(X)` whose restriction along `f`
is `c'`. This is Stacks 0GUC for the identity of `X`. -/
theorem existsUnique_chowCohomologyRestriction_eq_of_isEnvelope (envelope : IsEnvelope f)
    (c' : chowCohomologyComponent C (gysinSystemOfInvertible C) (f ≫ sX) p)
    (hc' : ∀ {T : Scheme.{u}} (t : T ⟶ pullback f f) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C ((t ≫ pullback.fst f f) ≫ (f ≫ sX)) k)
      (β : chowGroup C ((t ≫ pullback.snd f f) ≫ (f ≫ sX)) k), α ≍ β →
        c'.idRule C (f ≫ sX) (gysinSystemOfInvertible C) (t ≫ pullback.fst f f) k α ≍
          c'.idRule C (f ≫ sX) (gysinSystemOfInvertible C) (t ≫ pullback.snd f f) k β) :
    ∃! c : chowCohomologyComponent C (gysinSystemOfInvertible C) sX p,
      chowCohomologyRestriction C (gysinSystemOfInvertible C) sX f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c = c' := by
  have : IsProper f := envelope.isProper
  have hres : envelopeDescentRes₁ C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX)
        f p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (chowCohomologyDescentInput C sX f p c') =
      envelopeDescentRes₂ C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) f p
        (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
        (chowCohomologyDescentInput C sX f p c') := by
    refine BivariantClass.eq_of_isoCap_eq C _ _ _ _ _ fun t _ k α ↦ eq_of_heq ?_
    have hW : t ≫ (pullback.fst f f ≫ (f ≫ sX)) = (t ≫ pullback.snd f f) ≫ (f ≫ sX) := by
      rw [Category.assoc, ← pullback.condition_assoc]
    refine (isoCap_envelopeDescentRes₁_heq C sX p c' t k α
      (chowGroupCongr C (Category.assoc _ _ _).symm k α) (chowGroupCongr_heq C _ k α).symm).trans
      ?_
    refine (hc' t k _ (chowGroupCongr C hW k α)
      ((chowGroupCongr_heq C _ k α).trans (chowGroupCongr_heq C _ k α).symm)).trans ?_
    exact (isoCap_envelopeDescentRes₂_heq C sX p c' t k α _
      (chowGroupCongr_heq C hW k α).symm).symm
  obtain ⟨c, hc, huniq⟩ := existsUnique_bivariantRestriction_eq_of_isEnvelope C sX sX (𝟙 X)
    (Category.id_comp sX) f envelope p (chowCohomologyDescentInput C sX f p c') hres
  exact ⟨c, (chowCohomologyRestriction_eq_iff C sX f p c c').2 hc,
    fun d hd ↦ huniq d ((chowCohomologyRestriction_eq_iff C sX f p d c').1 hd)⟩

end Descent

end Stacks.Chow

end
