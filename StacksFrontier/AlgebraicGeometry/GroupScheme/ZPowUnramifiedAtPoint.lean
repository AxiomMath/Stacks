module

public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Unramified
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import StacksCore.Tactic.StacksAttribute

/-!
# Multiplication by an invertible integer on a commutative group scheme is unramified

Let `G` be a commutative group scheme over a scheme `S`, let `x` be a point of `G` and let `n` be
a natural number invertible in the residue field `κ(x)`. Then multiplication by `n` on `G` is
unramified at `x`.

## Main results

* `AlgebraicGeometry.spec_doubleDualNumber_hom_ext`: a morphism out of `Spec κ[ε₁, ε₂]` is
  determined by its restrictions along the two inclusions of `Spec κ[ε]`.
* `AlgebraicGeometry.dualNumberOver.eq_mul_inv_mul_of_glue`: if two `κ[ε]`-points `θ` and `η` of
  a group object with the same reduction glue to a `κ[ε₁, ε₂]`-point, then the pullback of that
  point along the sum map `ε₁, ε₂ ↦ ε` is `θ * w⁻¹ * η`, with `w` the common constant point.
* `AlgebraicGeometry.unramifiedAt_zpow_id_left_of_isUnit`: multiplication by `n` on a commutative
  group scheme is unramified at every point whose residue field has `n` invertible.

## Implementation notes

A tangent vector of `G/S` at `x` is a morphism `θ : Spec κ(x)[ε] ⟶ G` over `S` reducing to `x`,
so it is an element of the group `T ⟶ G` of morphisms out of `T = Spec κ(x)[ε]` in `Over S`.
Write `w` for the constant point `T ⟶ Spec κ(x) ⟶ G` at `x`. The map `θ ↦ θ * w⁻¹` turns the
addition of tangent vectors (which is defined by gluing two tangent vectors along
`Spec κ[ε₁, ε₂]` and pulling back along `ε₁, ε₂ ↦ ε`) into the group law: this is
`eq_mul_inv_mul_of_glue`, whose proof is that `p₁^* θ * w⁻¹ * p₂^* η` glues `θ` and `η`, and a
morphism out of `Spec κ[ε₁, ε₂]` is determined by its two restrictions
(`spec_doubleDualNumber_hom_ext`, from the injectivity of
`κ[ε₁, ε₂] ⟶ κ[ε] × κ[ε]`). Nothing about the group object beyond its being a group object enters
there.

If `θ` is moreover a tangent vector of `G` *over* `[n]`, that is `θ ≫ [n]` is constant, then
`θ ^ n = θ ≫ [n] = w ≫ [n] = w ^ n`, so in a commutative group `(θ * w⁻¹) ^ n = 1`; since
`θ ↦ θ * w⁻¹` is an injective homomorphism from the tangent space, `n • θ = 0`, and `n` being
invertible in `κ(x)` gives `θ = 0`. So the tangent space of `G` over `[n]` at `x` is trivial,
which is unramifiedness at `x` by
`AlgebraicGeometry.subsingleton_dottedTangentArrow_iff_unramifiedAt`.

## References

* [Stacks Project, Tag 0BFH](https://stacks.math.columbia.edu/tag/0BFH)
* [Stacks Project, Tag 0BF5](https://stacks.math.columbia.edu/tag/0BF5)
* [Stacks Project, Tag 0B2G](https://stacks.math.columbia.edu/tag/0B2G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

section DoubleDualNumber

variable (κ : Type u) [Field κ]

/-- The homomorphism `κ[ε] ⟶ κ[ε₁, ε₂]` sending `ε` to `ε₁`. -/
def firstDualNumberEmbedding : DualNumber κ →ₐ[κ] DoubleDualNumber κ :=
  TrivSqZeroExt.map (LinearMap.inl κ κ κ)

/-- The homomorphism `κ[ε] ⟶ κ[ε₁, ε₂]` sending `ε` to `ε₂`. -/
def secondDualNumberEmbedding : DualNumber κ →ₐ[κ] DoubleDualNumber κ :=
  TrivSqZeroExt.map (LinearMap.inr κ κ κ)

/-- The structure morphism `Spec κ[ε₁, ε₂] ⟶ Spec κ`. -/
noncomputable def doubleDualNumberToBase :
    Spec (.of (DoubleDualNumber κ)) ⟶ Spec (.of κ) :=
  Spec.map (CommRingCat.ofHom (algebraMap κ (DoubleDualNumber κ)))

/-- The closed point `Spec κ ⟶ Spec κ[ε]`. -/
noncomputable def dualNumberClosedPointOf : Spec (.of κ) ⟶ Spec (.of (DualNumber κ)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ))

/-- The ring `κ[ε₁, ε₂]` is a local ring. -/
instance : IsLocalRing (DoubleDualNumber κ) :=
  IsLocalRing.of_nonunits_add (by
    intro a b ha hb
    simp only [mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
      not_not, TrivSqZeroExt.fst_add] at ha hb ⊢
    rw [ha, hb, add_zero])

variable {κ}

private lemma specToEquiv_comp {X : Scheme.{u}} {R R' : CommRingCat.{u}} [IsLocalRing R]
    [IsLocalRing R'] (g : Spec R ⟶ X) (φ : R ⟶ R') [IsLocalHom φ.hom] :
    SpecToEquivOfLocalRing X R' (Spec.map φ ≫ g) =
      ⟨g (closedPoint R), Scheme.stalkClosedPointTo g ≫ φ, inferInstance⟩ := by
  conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk g]
  rw [← Category.assoc, ← Spec.map_comp]
  exact (SpecToEquivOfLocalRing X R').apply_symm_apply ⟨_, _, inferInstance⟩

/-- **A morphism out of `Spec κ[ε₁, ε₂]` is determined by its restrictions along the two
inclusions of `Spec κ[ε]`.** The ring `κ[ε₁, ε₂]` is local and embeds into `κ[ε] × κ[ε]` by the two
projections, and a morphism out of the spectrum of a local ring is a point together with a local
homomorphism out of its stalk. -/
theorem spec_doubleDualNumber_hom_ext {X : Scheme.{u}}
    {g₁ g₂ : Spec (.of (DoubleDualNumber κ)) ⟶ X}
    (h₁ : firstDualNumberInclusion κ ≫ g₁ = firstDualNumberInclusion κ ≫ g₂)
    (h₂ : secondDualNumberInclusion κ ≫ g₁ = secondDualNumberInclusion κ ≫ g₂) : g₁ = g₂ := by
  have hfs : Function.Surjective (CommRingCat.ofHom
      (firstDualNumberProjection κ : DoubleDualNumber κ →+* DualNumber κ)).hom := by
    intro z
    refine ⟨TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr (z.snd, 0), ?_⟩
    simp only [firstDualNumberProjection, ConcreteCategory.hom_ofHom, RingHom.coe_coe, map_add,
      TrivSqZeroExt.map_inl, TrivSqZeroExt.map_inr, LinearMap.fst_apply, DualNumber.inr_eq_smul_eps]
    ext <;> simp
  have hss : Function.Surjective (CommRingCat.ofHom
      (secondDualNumberProjection κ : DoubleDualNumber κ →+* DualNumber κ)).hom := by
    intro z
    refine ⟨TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr (0, z.snd), ?_⟩
    simp only [secondDualNumberProjection, ConcreteCategory.hom_ofHom, RingHom.coe_coe, map_add,
      TrivSqZeroExt.map_inl, TrivSqZeroExt.map_inr, LinearMap.snd_apply, DualNumber.inr_eq_smul_eps]
    ext <;> simp
  have : IsLocalHom (CommRingCat.ofHom
      (firstDualNumberProjection κ : DoubleDualNumber κ →+* DualNumber κ)).hom :=
    IsLocalHom.of_surjective _ hfs
  have : IsLocalHom (CommRingCat.ofHom
      (secondDualNumberProjection κ : DoubleDualNumber κ →+* DualNumber κ)).hom :=
    IsLocalHom.of_surjective _ hss
  have e₁ := congrArg (SpecToEquivOfLocalRing X (.of (DualNumber κ))) h₁
  have e₂ := congrArg (SpecToEquivOfLocalRing X (.of (DualNumber κ))) h₂
  simp only [firstDualNumberInclusion, secondDualNumberInclusion] at e₁ e₂
  rw [specToEquiv_comp, specToEquiv_comp] at e₁ e₂
  obtain ⟨hx, hψ₁⟩ := SpecToEquivOfLocalRing_eq_iff.mp e₁
  obtain ⟨_hx', hψ₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp e₂
  apply (SpecToEquivOfLocalRing X (.of (DoubleDualNumber κ))).injective
  refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨hx, ?_⟩
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  refine TrivSqZeroExt.ext ?_ (Prod.ext ?_ ?_)
  · have k := congrArg (fun φ => TrivSqZeroExt.fst (φ.hom a)) hψ₁
    change TrivSqZeroExt.fst (firstDualNumberProjection κ ((Scheme.stalkClosedPointTo g₁).hom a)) =
      TrivSqZeroExt.fst (firstDualNumberProjection κ
        (((X.presheaf.stalkCongr _).hom ≫ Scheme.stalkClosedPointTo g₂).hom a)) at k
    unfold firstDualNumberProjection at k
    rw [TrivSqZeroExt.fst_map, TrivSqZeroExt.fst_map] at k
    exact k
  · have k := congrArg (fun φ => TrivSqZeroExt.snd (φ.hom a)) hψ₁
    change TrivSqZeroExt.snd (firstDualNumberProjection κ ((Scheme.stalkClosedPointTo g₁).hom a)) =
      TrivSqZeroExt.snd (firstDualNumberProjection κ
        (((X.presheaf.stalkCongr _).hom ≫ Scheme.stalkClosedPointTo g₂).hom a)) at k
    unfold firstDualNumberProjection at k
    rw [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map] at k
    exact k
  · have k := congrArg (fun φ => TrivSqZeroExt.snd (φ.hom a)) hψ₂
    change TrivSqZeroExt.snd (secondDualNumberProjection κ ((Scheme.stalkClosedPointTo g₁).hom a)) =
      TrivSqZeroExt.snd (secondDualNumberProjection κ
        (((X.presheaf.stalkCongr _).hom ≫ Scheme.stalkClosedPointTo g₂).hom a)) at k
    unfold secondDualNumberProjection at k
    rw [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map] at k
    exact k

end DoubleDualNumber

/-! ### The dual numbers as objects over a base -/

section SpecIdentities

variable (κ : Type u) [Field κ]

private lemma specMap_ofHom_comp {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    (f : R' →+* R'') (g : R →+* R') :
    Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom g) =
      Spec.map (CommRingCat.ofHom (f.comp g)) := by
  rw [← Spec.map_comp]; rfl

private lemma specMap_ofHom_id {R : Type u} [CommRing R] :
    𝟙 (Spec (.of R)) = Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
  rw [← Spec.map_id]; rfl

/-- The first inclusion `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]` commutes with the structure morphisms to
`Spec κ`. -/
lemma firstDualNumberInclusion_toBase :
    firstDualNumberInclusion κ ≫ doubleDualNumberToBase κ = dualNumberToBase κ := by
  dsimp only [firstDualNumberInclusion, doubleDualNumberToBase, dualNumberToBase]
  rw [specMap_ofHom_comp]; congr 1; ext z <;> simp [firstDualNumberProjection,
    TrivSqZeroExt.algebraMap_eq_inl]

/-- The second inclusion `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]` commutes with the structure morphisms to
`Spec κ`. -/
lemma secondDualNumberInclusion_toBase :
    secondDualNumberInclusion κ ≫ doubleDualNumberToBase κ = dualNumberToBase κ := by
  dsimp only [secondDualNumberInclusion, doubleDualNumberToBase, dualNumberToBase]
  rw [specMap_ofHom_comp]; congr 1; ext z <;> simp [secondDualNumberProjection,
    TrivSqZeroExt.algebraMap_eq_inl]

/-- The sum map `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]` commutes with the structure morphisms to
`Spec κ`. -/
lemma sumDualNumberMap_toBase :
    sumDualNumberMap κ ≫ doubleDualNumberToBase κ = dualNumberToBase κ := by
  dsimp only [sumDualNumberMap, doubleDualNumberToBase, dualNumberToBase]
  rw [specMap_ofHom_comp]; congr 1; ext z <;> simp [sumDualNumberProjection,
    TrivSqZeroExt.algebraMap_eq_inl]

/-- The first projection `Spec κ[ε₁, ε₂] ⟶ Spec κ[ε]`, `ε ↦ ε₁`, commutes with the structure
morphisms to `Spec κ`. -/
lemma firstEmbedding_toBase :
    Spec.map (CommRingCat.ofHom (firstDualNumberEmbedding κ : _ →+* _)) ≫ dualNumberToBase κ =
      doubleDualNumberToBase κ := by
  dsimp only [doubleDualNumberToBase, dualNumberToBase]
  rw [specMap_ofHom_comp]; congr 1; ext z <;> simp [firstDualNumberEmbedding,
    TrivSqZeroExt.algebraMap_eq_inl]

/-- The second projection `Spec κ[ε₁, ε₂] ⟶ Spec κ[ε]`, `ε ↦ ε₂`, commutes with the structure
morphisms to `Spec κ`. -/
lemma secondEmbedding_toBase :
    Spec.map (CommRingCat.ofHom (secondDualNumberEmbedding κ : _ →+* _)) ≫ dualNumberToBase κ =
      doubleDualNumberToBase κ := by
  dsimp only [doubleDualNumberToBase, dualNumberToBase]
  rw [specMap_ofHom_comp]; congr 1; ext z <;> simp [secondDualNumberEmbedding,
    TrivSqZeroExt.algebraMap_eq_inl]

/-- The closed point `Spec κ ⟶ Spec κ[ε]` is a section of the structure morphism. -/
lemma closedPointOf_toBase : dualNumberClosedPointOf κ ≫ dualNumberToBase κ = 𝟙 _ := by
  dsimp only [dualNumberClosedPointOf, dualNumberToBase]
  rw [specMap_ofHom_comp, specMap_ofHom_id]; congr 1

/-- The first inclusion `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]` followed by the first projection is the
identity. -/
lemma firstInclusion_firstEmbedding :
    firstDualNumberInclusion κ ≫
      Spec.map (CommRingCat.ofHom (firstDualNumberEmbedding κ : _ →+* _)) = 𝟙 _ := by
  dsimp only [firstDualNumberInclusion]
  rw [specMap_ofHom_comp, specMap_ofHom_id]; congr 1; ext z <;> simp [firstDualNumberProjection,
    firstDualNumberEmbedding, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_map,
    TrivSqZeroExt.snd_map, RingHom.coe_coe]

/-- The second inclusion `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]` followed by the second projection is the
identity. -/
lemma secondInclusion_secondEmbedding :
    secondDualNumberInclusion κ ≫
      Spec.map (CommRingCat.ofHom (secondDualNumberEmbedding κ : _ →+* _)) = 𝟙 _ := by
  dsimp only [secondDualNumberInclusion]
  rw [specMap_ofHom_comp, specMap_ofHom_id]; congr 1; ext z <;> simp [secondDualNumberProjection,
    secondDualNumberEmbedding, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_map,
    TrivSqZeroExt.snd_map, RingHom.coe_coe]

/-- The sum map `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]` followed by the first projection is the
identity. -/
lemma sum_firstEmbedding :
    sumDualNumberMap κ ≫
      Spec.map (CommRingCat.ofHom (firstDualNumberEmbedding κ : _ →+* _)) = 𝟙 _ := by
  dsimp only [sumDualNumberMap]
  rw [specMap_ofHom_comp, specMap_ofHom_id]; congr 1; ext z <;> simp [sumDualNumberProjection,
    firstDualNumberEmbedding, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_map,
    TrivSqZeroExt.snd_map, RingHom.coe_coe]

/-- The sum map `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]` followed by the second projection is the
identity. -/
lemma sum_secondEmbedding :
    sumDualNumberMap κ ≫
      Spec.map (CommRingCat.ofHom (secondDualNumberEmbedding κ : _ →+* _)) = 𝟙 _ := by
  dsimp only [sumDualNumberMap]
  rw [specMap_ofHom_comp, specMap_ofHom_id]; congr 1; ext z <;> simp [sumDualNumberProjection,
    secondDualNumberEmbedding, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_map,
    TrivSqZeroExt.snd_map, RingHom.coe_coe]

/-- The first inclusion `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]` followed by the second projection factors
through the closed point `Spec κ ⟶ Spec κ[ε]`. -/
lemma firstInclusion_secondEmbedding :
    firstDualNumberInclusion κ ≫
      Spec.map (CommRingCat.ofHom (secondDualNumberEmbedding κ : _ →+* _)) =
      dualNumberToBase κ ≫ dualNumberClosedPointOf κ := by
  dsimp only [firstDualNumberInclusion, dualNumberToBase, dualNumberClosedPointOf]
  rw [specMap_ofHom_comp, specMap_ofHom_comp]; congr 1; ext z <;> simp [firstDualNumberProjection,
    secondDualNumberEmbedding, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_map,
    TrivSqZeroExt.snd_map, RingHom.coe_coe]

/-- The second inclusion `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]` followed by the first projection factors
through the closed point `Spec κ ⟶ Spec κ[ε]`. -/
lemma secondInclusion_firstEmbedding :
    secondDualNumberInclusion κ ≫
      Spec.map (CommRingCat.ofHom (firstDualNumberEmbedding κ : _ →+* _)) =
      dualNumberToBase κ ≫ dualNumberClosedPointOf κ := by
  dsimp only [secondDualNumberInclusion, dualNumberToBase, dualNumberClosedPointOf]
  rw [specMap_ofHom_comp, specMap_ofHom_comp]; congr 1; ext z <;> simp [secondDualNumberProjection,
    firstDualNumberEmbedding, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_map,
    TrivSqZeroExt.snd_map, RingHom.coe_coe]

end SpecIdentities

namespace dualNumberOver

variable {S : Scheme.{u}} {κ : Type u} [Field κ] (b : Spec (.of κ) ⟶ S)

/-- `Spec κ` over `S`. -/
noncomputable abbrev P : Over S := Over.mk b

/-- `Spec κ[ε]` over `S`, through `Spec κ`. -/
@[sga "3 II 4.7.1" "special case",
  sga "3 VIB 3.2" "special case",
  sga "3 VIIA 1.2.0" "special case"]
noncomputable abbrev T : Over S := Over.mk (dualNumberToBase κ ≫ b)

/-- `Spec κ[ε₁, ε₂]` over `S`, through `Spec κ`. -/
noncomputable abbrev D : Over S := Over.mk (doubleDualNumberToBase κ ≫ b)

/-- The first inclusion `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]`, over `S`. -/
noncomputable def inc₁ : T b ⟶ D b :=
  Over.homMk (firstDualNumberInclusion κ) (by
    change _ ≫ doubleDualNumberToBase κ ≫ b = dualNumberToBase κ ≫ b
    rw [← Category.assoc, firstDualNumberInclusion_toBase])

/-- The second inclusion `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]`, over `S`. -/
noncomputable def inc₂ : T b ⟶ D b :=
  Over.homMk (secondDualNumberInclusion κ) (by
    change _ ≫ doubleDualNumberToBase κ ≫ b = dualNumberToBase κ ≫ b
    rw [← Category.assoc, secondDualNumberInclusion_toBase])

/-- The sum map `Spec κ[ε] ⟶ Spec κ[ε₁, ε₂]`, `ε₁, ε₂ ↦ ε`, over `S`. -/
noncomputable def sum : T b ⟶ D b :=
  Over.homMk (sumDualNumberMap κ) (by
    change _ ≫ doubleDualNumberToBase κ ≫ b = dualNumberToBase κ ≫ b
    rw [← Category.assoc, sumDualNumberMap_toBase])

/-- The first projection `Spec κ[ε₁, ε₂] ⟶ Spec κ[ε]`, `ε ↦ ε₁`, over `S`. -/
noncomputable def pr₁ : D b ⟶ T b :=
  Over.homMk (Spec.map (CommRingCat.ofHom (firstDualNumberEmbedding κ : _ →+* _))) (by
    change _ ≫ dualNumberToBase κ ≫ b = doubleDualNumberToBase κ ≫ b
    rw [← Category.assoc, firstEmbedding_toBase])

/-- The second projection `Spec κ[ε₁, ε₂] ⟶ Spec κ[ε]`, `ε ↦ ε₂`, over `S`. -/
noncomputable def pr₂ : D b ⟶ T b :=
  Over.homMk (Spec.map (CommRingCat.ofHom (secondDualNumberEmbedding κ : _ →+* _))) (by
    change _ ≫ dualNumberToBase κ ≫ b = doubleDualNumberToBase κ ≫ b
    rw [← Category.assoc, secondEmbedding_toBase])

/-- The closed point `Spec κ ⟶ Spec κ[ε]`, over `S`. -/
@[sga "3 VIB 3.2" "special case"]
noncomputable def cl : P b ⟶ T b :=
  Over.homMk (dualNumberClosedPointOf κ) (by
    change _ ≫ dualNumberToBase κ ≫ b = b
    rw [← Category.assoc, closedPointOf_toBase, Category.id_comp])

/-- The structure morphism `Spec κ[ε] ⟶ Spec κ`, over `S`. -/
noncomputable def rt : T b ⟶ P b := Over.homMk (dualNumberToBase κ) rfl

/-- The structure morphism `Spec κ[ε₁, ε₂] ⟶ Spec κ`, over `S`. -/
noncomputable def rd : D b ⟶ P b := Over.homMk (doubleDualNumberToBase κ) rfl

/-- Over `S`, the first inclusion followed by the first projection is the identity of
`Spec κ[ε]`. -/
lemma inc₁_pr₁ : inc₁ b ≫ pr₁ b = 𝟙 _ := Over.OverMorphism.ext (firstInclusion_firstEmbedding κ)
/-- Over `S`, the second inclusion followed by the second projection is the identity of
`Spec κ[ε]`. -/
lemma inc₂_pr₂ : inc₂ b ≫ pr₂ b = 𝟙 _ := Over.OverMorphism.ext (secondInclusion_secondEmbedding κ)
/-- Over `S`, the sum map followed by the first projection is the identity of `Spec κ[ε]`. -/
lemma sum_pr₁ : sum b ≫ pr₁ b = 𝟙 _ := Over.OverMorphism.ext (sum_firstEmbedding κ)
/-- Over `S`, the sum map followed by the second projection is the identity of `Spec κ[ε]`. -/
lemma sum_pr₂ : sum b ≫ pr₂ b = 𝟙 _ := Over.OverMorphism.ext (sum_secondEmbedding κ)
/-- Over `S`, the first inclusion followed by the second projection is the constant map through
the closed point. -/
lemma inc₁_pr₂ : inc₁ b ≫ pr₂ b = rt b ≫ cl b := Over.OverMorphism.ext
    (firstInclusion_secondEmbedding κ)
/-- Over `S`, the second inclusion followed by the first projection is the constant map through
the closed point. -/
lemma inc₂_pr₁ : inc₂ b ≫ pr₁ b = rt b ≫ cl b := Over.OverMorphism.ext
    (secondInclusion_firstEmbedding κ)
/-- Over `S`, the first inclusion commutes with the structure morphisms to `Spec κ`. -/
lemma inc₁_rd : inc₁ b ≫ rd b = rt b := Over.OverMorphism.ext (firstDualNumberInclusion_toBase κ)
/-- Over `S`, the second inclusion commutes with the structure morphisms to `Spec κ`. -/
lemma inc₂_rd : inc₂ b ≫ rd b = rt b := Over.OverMorphism.ext (secondDualNumberInclusion_toBase κ)
/-- Over `S`, the sum map commutes with the structure morphisms to `Spec κ`. -/
lemma sum_rd : sum b ≫ rd b = rt b := Over.OverMorphism.ext (sumDualNumberMap_toBase κ)
/-- Over `S`, the first projection commutes with the structure morphisms to `Spec κ`. -/
lemma pr₁_rt : pr₁ b ≫ rt b = rd b := Over.OverMorphism.ext (firstEmbedding_toBase κ)
/-- Over `S`, the closed point is a section of the structure morphism `Spec κ[ε] ⟶ Spec κ`. -/
lemma cl_rt : cl b ≫ rt b = 𝟙 _ := Over.OverMorphism.ext (closedPointOf_toBase κ)

/-- Two morphisms out of `Spec κ[ε₁, ε₂]` over `S` agree as soon as their restrictions along the
two inclusions agree. -/
lemma D_hom_ext {Y : Over S} {g₁ g₂ : D b ⟶ Y} (h₁ : inc₁ b ≫ g₁ = inc₁ b ≫ g₂)
    (h₂ : inc₂ b ≫ g₁ = inc₂ b ≫ g₂) : g₁ = g₂ :=
  Over.OverMorphism.ext
      ((spec_doubleDualNumber_hom_ext (congrArg CommaMorphism.left h₁)
    (congrArg CommaMorphism.left h₂)))

variable {G : Over S} [GrpObj G]

/-- **The sum of two glued `κ[ε]`-points.** Let `θ₁` and `θ₂` be `κ[ε]`-points of a group object
`G` over `S` with the same reduction, and let `M` be a `κ[ε₁, ε₂]`-point restricting to `θ₁` and
`θ₂` along the two inclusions. Then the pullback of `M` along the sum map is `θ₁ * w⁻¹ * θ₂`, where
`w` is the constant point at the common reduction. -/
theorem eq_mul_inv_mul_of_glue {θ₁ θ₂ ζ : T b ⟶ G} {M : D b ⟶ G} (h₁ : inc₁ b ≫ M = θ₁)
    (h₂ : inc₂ b ≫ M = θ₂) (hσ : sum b ≫ M = ζ) (hc : cl b ≫ θ₁ = cl b ≫ θ₂) :
    ζ = θ₁ * (rt b ≫ cl b ≫ θ₁)⁻¹ * θ₂ := by
  have hM : M = (pr₁ b ≫ θ₁) * (rd b ≫ cl b ≫ θ₁)⁻¹ * (pr₂ b ≫ θ₂) := by
    apply D_hom_ext b
    · simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, inc₁_pr₁, inc₁_rd,
        inc₁_pr₂, Category.id_comp, h₁]
      simp only [Category.assoc, hc, inv_mul_cancel_right]
    · simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, inc₂_pr₂, inc₂_rd,
        inc₂_pr₁, Category.id_comp, h₂, mul_inv_cancel, one_mul]
  rw [← hσ, hM]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, sum_pr₁, sum_rd, sum_pr₂,
    Category.id_comp]

end dualNumberOver

/-! ### Tangent vectors as dual-number points of a group object -/

namespace TangentGroupObj

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] (x : G.left)

/-- The point `Spec κ(x) ⟶ S` under the point `x` of `G`. -/
noncomputable abbrev base : Spec (.of (G.left.residueField x)) ⟶ S :=
  Spec.map (G.hom.residueFieldMap x) ≫ S.fromSpecResidueField (G.hom.base x)

/-- The point `x` of `G`, as a morphism `Spec κ(x) ⟶ G` over `S`. -/
noncomputable def pt : dualNumberOver.P (base G x) ⟶ G :=
  Over.homMk (G.left.fromSpecResidueField x)
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField G.hom x).symm

/-- A tangent vector of `G/S` at `x`, as a `κ(x)[ε]`-point of `G` over `S`. -/
noncomputable def toHom (θ : DottedTangentArrow G.hom x) : dualNumberOver.T (base G x) ⟶ G :=
  Over.homMk θ.val (by rw [θ.2.2]; rfl)

omit [GrpObj G] in
/-- The underlying morphism of schemes of `toHom G x θ` is `θ`. -/
lemma toHom_left (θ : DottedTangentArrow G.hom x) : (toHom G x θ).left = θ.val := rfl

omit [GrpObj G] in
/-- A tangent vector at `x` restricts to the point `x` along the closed point of `Spec κ(x)[ε]`. -/
lemma cl_toHom (θ : DottedTangentArrow G.hom x) :
    dualNumberOver.cl (base G x) ≫ toHom G x θ = pt G x :=
  Over.OverMorphism.ext θ.2.1

omit [GrpObj G] in
/-- The zero tangent vector at `x` is the constant point `Spec κ(x)[ε] ⟶ Spec κ(x) ⟶ G`. -/
lemma toHom_zero : toHom G x 0 = dualNumberOver.rt (base G x) ≫ pt G x :=
  Over.OverMorphism.ext (dottedTangentArrowModule G.hom x).zero_apply

/-- The sum of tangent vectors `θ + χ` at `x` is the point `θ * w⁻¹ * χ`, where `w` is the
constant point at `x`. -/
lemma toHom_add (θ χ : DottedTangentArrow G.hom x) :
    toHom G x (θ + χ) =
      toHom G x θ * (dualNumberOver.rt (base G x) ≫ pt G x)⁻¹ * toHom G x χ := by
  obtain ⟨μ', h₁, h₂, hσ⟩ := (dottedTangentArrowModule G.hom x).add_apply θ χ
  have hμ : μ' ≫ G.hom = doubleDualNumberToBase _ ≫ base G x := by
    apply spec_doubleDualNumber_hom_ext
    · rw [← Category.assoc, h₁, θ.2.2, ← Category.assoc, firstDualNumberInclusion_toBase]; rfl
    · rw [← Category.assoc, h₂, χ.2.2, ← Category.assoc, secondDualNumberInclusion_toBase]; rfl
  let M : dualNumberOver.D (base G x) ⟶ G := Over.homMk μ' hμ
  have := dualNumberOver.eq_mul_inv_mul_of_glue (base G x) (θ₁ := toHom G x θ)
    (θ₂ := toHom G x χ) (ζ := toHom G x (θ + χ)) (M := M)
    (Over.OverMorphism.ext h₁) (Over.OverMorphism.ext h₂) (Over.OverMorphism.ext hσ.symm)
    (by rw [cl_toHom, cl_toHom])
  rw [this, cl_toHom]

omit [GrpObj G] in
/-- The map `toHom G x` from tangent vectors to `κ(x)[ε]`-points of `G` is injective. -/
lemma toHom_injective : Function.Injective (toHom G x) := by
  intro θ χ h
  exact Subtype.ext (congrArg CommaMorphism.left h)

/-- The tangent space of `G/S` at `x`, as a subgroup of the `κ(x)[ε]`-points of `G`: the map
`θ ↦ θ * w⁻¹`, with `w` the constant point at `x`, is an additive-to-multiplicative
homomorphism. -/
noncomputable def toGroupHom :
    Multiplicative (DottedTangentArrow G.hom x) →* (dualNumberOver.T (base G x) ⟶ G) where
  toFun θ := toHom G x θ.toAdd * (dualNumberOver.rt (base G x) ≫ pt G x)⁻¹
  map_one' := by
    change toHom G x 0 * _ = 1
    rw [toHom_zero, mul_inv_cancel]
  map_mul' θ χ := by
    change toHom G x (θ.toAdd + χ.toAdd) * _ = _
    rw [toHom_add]
    group

/-- The homomorphism `toGroupHom G x`, `θ ↦ θ * w⁻¹`, is injective. -/
lemma toGroupHom_injective : Function.Injective (toGroupHom G x) := by
  intro θ χ h
  have : toHom G x θ.toAdd = toHom G x χ.toAdd := mul_right_cancel h
  exact toHom_injective G x this

end TangentGroupObj

/-- **Multiplication by an invertible integer on a commutative group scheme is unramified.** Let
`G` be a commutative group scheme over `S`, locally of finite type, let `x` be a point of `G` and
let `n` be a natural number invertible in the residue field `κ(x)`. Then multiplication by `n`
is unramified at `x`.

A tangent vector `θ` of `G` over `[n]` at `x` is a `κ(x)[ε]`-point with `θ ^ n = w ^ n`, `w`
being the constant point at `x`; so `(θ * w⁻¹) ^ n = 1` in the commutative group of
`κ(x)[ε]`-points, and as `θ ↦ θ * w⁻¹` is an injective homomorphism from the tangent space of
`G/S`, `n • θ = 0` there, whence `θ = 0` because `n` is invertible in `κ(x)`. So the tangent
space of `G` over `[n]` at `x` is trivial, which is unramifiedness at `x`. -/
theorem unramifiedAt_zpow_id_left_of_isUnit {S : Scheme.{u}} (G : Over S) [GrpObj G]
    [IsCommMonObj G] [LocallyOfFiniteType G.hom] (n : ℕ) (x : G.left)
    (hn : IsUnit ((n : ℕ) : G.left.residueField x)) :
    UnramifiedAt ((𝟙 G : G ⟶ G) ^ (n : ℤ)).left x := by
  set F := ((𝟙 G : G ⟶ G) ^ (n : ℤ)).left with hFdef
  have hF : F ≫ G.hom = G.hom := Over.w ((𝟙 G : G ⟶ G) ^ (n : ℤ))
  have : LocallyOfFiniteType F := by
    have h : LocallyOfFiniteType (F ≫ G.hom) := by rw [hF]; infer_instance
    exact LocallyOfFiniteType.of_comp (f := F) (g := G.hom) h
  rw [← subsingleton_dottedTangentArrow_iff_unramifiedAt]
  refine ⟨fun θ χ => ?_⟩
  suffices key : ∀ ζ : DottedTangentArrow F x,
      ζ.val = (0 : DottedTangentArrow G.hom x).val by
    exact Subtype.ext ((key θ).trans (key χ).symm)
  intro ζ
  let ζ' := dottedTangentArrowOverBase F G.hom G.hom x hF ζ
  let w := dualNumberOver.rt (TangentGroupObj.base G x) ≫ TangentGroupObj.pt G x
  have hpow : TangentGroupObj.toHom G x ζ' ^ (n : ℤ) = w ^ (n : ℤ) := by
    have e1 : TangentGroupObj.toHom G x ζ' ^ (n : ℤ) =
        TangentGroupObj.toHom G x ζ' ≫ (𝟙 G : G ⟶ G) ^ (n : ℤ) := by
      rw [GrpObj.comp_zpow, Category.comp_id]
    have e2 : w ^ (n : ℤ) = w ≫ (𝟙 G : G ⟶ G) ^ (n : ℤ) := by
      rw [GrpObj.comp_zpow, Category.comp_id]
    rw [e1, e2]
    apply Over.OverMorphism.ext
    change ζ.val ≫ F = (dualNumberOver.rt _).left ≫ (TangentGroupObj.pt G x).left ≫ F
    rw [ζ.2.2]
    change _ = dualNumberToBase (G.left.residueField x) ≫ G.left.fromSpecResidueField x ≫ F
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField F x]
    rfl
  have hone : TangentGroupObj.toGroupHom G x (Multiplicative.ofAdd (n • ζ')) = 1 := by
    rw [ofAdd_nsmul, map_pow]
    change (TangentGroupObj.toHom G x ζ' * w⁻¹) ^ n = 1
    rw [mul_pow, inv_pow, ← zpow_natCast, hpow, zpow_natCast, mul_inv_cancel]
  have hzero : n • ζ' = 0 := by
    have := TangentGroupObj.toGroupHom_injective G x (hone.trans (map_one _).symm)
    exact this
  have hζ : ζ' = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (G.left.residueField x)] at hzero
    obtain ⟨u, hu⟩ := hn
    rw [← hu] at hzero
    have := congrArg (fun v => (↑u⁻¹ : G.left.residueField x) • v) hzero
    simpa [smul_smul] using this
  exact congrArg Subtype.val hζ

end AlgebraicGeometry

end
