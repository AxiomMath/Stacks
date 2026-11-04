module

public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Pushout.ClosedImmersionIntegral
public import StacksFrontier.AlgebraicGeometry.Variety.DimensionOne.Conductor

/-!
# Gluing a reduced scheme out of two affine closed subschemes

Let `X` be a reduced scheme which is set theoretically the union of two closed subschemes
`Z₁` and `Z₂`. This file provides the algebra and the affine geometry of the square

```
Z₁ ∩ Z₂ ---> Z₂
   |          |
   v          v
  Z₁  ----->  X
```

namely that it is *cocartesian* as well as cartesian, which is the form in which affineness of
`X` can be read off affineness of `Z₁` and `Z₂`.

Over an affine `X = Spec A` the two closed subschemes are cut out by ideals `I` and `J`, and
reducedness enters exactly once, through `Ideal.inf_eq_bot_of_zeroLocus_union_eq_univ`
([Stacks, Tag 09NW]): the zero loci cover, so `I ⊓ J = ⊥`. The ring-level consequence is that
`A` *is* the fibre product `A ⧸ J ×_{A ⧸ (I + J)} A ⧸ I`, and
[Stacks, Tag 0ET0] (`Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective`) upgrades
that cartesian square of rings to a cocartesian square *of all schemes*. That is the affine case
of the cocartesian-ness, and it is the content this file adds.

## Main results

* `Stacks.AffineClosedUnion.isPullback_quotientMk`: for `I ⊓ J = ⊥` the square of quotient maps
  `A → A ⧸ J`, `A → A ⧸ I` over `A ⧸ (I + J)` is cartesian in `CommRingCat`.
* `Stacks.AffineClosedUnion.isPushout_specMap_quotientMk`: hence `Spec A` is the **pushout** of
  `Spec (A ⧸ I) ← Spec (A ⧸ (I + J)) → Spec (A ⧸ J)` in the category of all schemes.
* `Stacks.AffineClosedUnion.isPushout_quotientFactor`,
  `Stacks.AffineClosedUnion.isPullback_specMap_quotientFactor`: `A ⧸ (I + J)` is the pushout of
  `A ⧸ I ← A → A ⧸ J`, so `Spec (A ⧸ (I + J))` is the scheme-theoretic intersection.
* `Stacks.AffineClosedUnion.ker_inf_ker_eq_bot`: the sheaf-level form of Tag 09NW — on a reduced
  scheme, two closed immersions whose ranges cover have `i₁.ker ⊓ i₂.ker = ⊥`, i.e. their
  scheme-theoretic union is the whole of `X`.
* `Stacks.AffineClosedUnion.isPushout_affineModel`: the affine model
  `Stacks.Pushout.affineModel` of Tag 0E25 is the pushout, in the category of all schemes, when
  all three schemes of the span are affine. This is the general-position form of Tag 0ET0 and
  the pushout companion of `Stacks.Pushout.isPullback_affineModel`.
* `Stacks.AffineClosedUnion.surjective_modelDesc`: the canonical comparison
  `Stacks.AffineClosedUnion.modelDesc` from that affine model to `X` is surjective as soon as the
  two closed subschemes cover `X` set theoretically.
* `Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_modelDesc`: if that comparison is a
  closed immersion then `X` is affine.

## Implementation notes

The affine model is *not* redefined here. The global pushout reuses
`Stacks.Pushout.affineModel` rather than a second copy, and `Stacks.AffineClosedUnion.model` is an
abbreviation for exactly that object.

`Stacks.AffineClosedUnion.model` takes the scheme-theoretic intersection as an abstract scheme
`W` together with a commuting square, rather than as `CategoryTheory.Limits.pullback i₁ i₂`.
Only commutativity is used, and over an affine base the convenient choice of `W` is
`Spec (A ⧸ (I + J))`, for which `isPullback_specMap_quotientFactor` supplies the cartesian
square.

`isAffine_of_isClosedImmersion_modelDesc` takes the closed-immersion hypothesis as an
*instance* binder, so that the statement becomes unconditional with no edit on the day that
property is proved. That hypothesis is undischarged here: what it asks for is that the
comparison is a closed immersion, its surjectivity being proved here, after which
`AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective` finishes because `X` is reduced.
It is not needed for the tag, and this file is not where the tag is proved. The ideal-sheaf form
`Stacks.AffineClosedUnion.isAffine_of_inf_eq_bot` of
`StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Global` reaches the same conclusion along a
different route — it exhibits the comparison as an isomorphism outright, by comparing the two
cocartesian squares — and it is that route which carries the reduced case up to the finite
family. The `@[stacks 09NL]` attribute sits on the two statements of
`StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Unconditional`, which hold with no reducedness
hypothesis and no hypothesis on global sections.

## References

* [Stacks Project, Tag 09NW](https://stacks.math.columbia.edu/tag/09NW)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 09NL](https://stacks.math.columbia.edu/tag/09NL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AffineClosedUnion

section Ring

variable {A : Type u} [CommRing A] (I J : Ideal A)

/-- The comparison map from `A` to the fibre product `A ⧸ J ×_{A ⧸ (I + J)} A ⧸ I` of the two
quotients over their common further quotient. -/
def quotientFibreProductHom :
    A →+* ↥((Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J)).pullback
      (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J))) where
  toFun a := ⟨(Ideal.Quotient.mk J a, Ideal.Quotient.mk I a), by
    simp [Ideal.Quotient.factor_mk]⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

/-- The comparison map to the fibre product of the two quotients is injective precisely because
the two ideals meet in zero. -/
theorem injective_quotientFibreProductHom (h : I ⊓ J = ⊥) :
    Function.Injective (quotientFibreProductHom I J) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have h1 : Ideal.Quotient.mk J a = 0 := congrArg (fun p => p.1.1) ha
  have h2 : Ideal.Quotient.mk I a = 0 := congrArg (fun p => p.1.2) ha
  have : a ∈ I ⊓ J :=
    ⟨Ideal.Quotient.eq_zero_iff_mem.mp h2, Ideal.Quotient.eq_zero_iff_mem.mp h1⟩
  simpa [h] using this

/-- The comparison map to the fibre product of the two quotients is surjective, for arbitrary
ideals: a compatible pair of classes is corrected to a single element by subtracting the
`J`-component of the difference of two lifts. -/
theorem surjective_quotientFibreProductHom :
    Function.Surjective (quotientFibreProductHom I J) := by
  rintro ⟨⟨x, y⟩, hxy⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) y
  rw [Stacks.Pushout.mem_pullback_iff] at hxy
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hxy
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hxy
  refine ⟨b - j, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change Ideal.Quotient.mk J (b - j) = Ideal.Quotient.mk J b
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    simpa using (Ideal.neg_mem_iff _).mpr hj
  · change Ideal.Quotient.mk I (b - j) = Ideal.Quotient.mk I a
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have hba : b - j - a = i := by linear_combination -hij
    rw [hba]; exact hi

/-- For ideals meeting in zero, `A` is isomorphic to the fibre product
`A ⧸ J ×_{A ⧸ (I + J)} A ⧸ I`. -/
noncomputable def quotientFibreProductIso (h : I ⊓ J = ⊥) :
    CommRingCat.of A ≅ CommRingCat.of
      ↥((Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J)).pullback
        (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J))) :=
  (RingEquiv.ofBijective (quotientFibreProductHom I J)
    ⟨injective_quotientFibreProductHom I J h,
      surjective_quotientFibreProductHom I J⟩).toCommRingCatIso

/-- **The cartesian square of quotients.** For ideals meeting in zero, the square of quotient
maps `A → A ⧸ J` and `A → A ⧸ I` over `A ⧸ (I + J)` is cartesian in `CommRingCat`. -/
theorem isPullback_quotientMk (h : I ⊓ J = ⊥) :
    IsPullback (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J)))
      (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J))) := by
  refine (Stacks.Pushout.isPullback_ofHom_pullback _ _).of_iso'
    (quotientFibreProductIso I J h) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · ext a; rfl
  · ext a; rfl
  · simp
  · simp

/-- **The cocartesian square of affine schemes, and the affine case of the cocartesian-ness
needed for [Stacks, Tag 09NL].** For ideals meeting in zero — in particular for a reduced `A`
whose two zero loci cover `Spec A`, by `Ideal.inf_eq_bot_of_zeroLocus_union_eq_univ` — the
scheme `Spec A` is the pushout of `Spec (A ⧸ I) ← Spec (A ⧸ (I + J)) → Spec (A ⧸ J)` in the
category of *all* schemes, not merely in affine schemes. -/
theorem isPushout_specMap_quotientMk (h : I ⊓ J = ⊥) :
    IsPushout (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
  Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective _ _ _ _
    (isPullback_quotientMk I J h) (Ideal.Quotient.factor_surjective (le_sup_left : I ≤ I ⊔ J))

/-- `A ⧸ (I + J)` is the pushout of `A ⧸ I ← A → A ⧸ J` in `CommRingCat`: a pair of maps out of
the two quotients agreeing on `A` kills `I` and `J`, hence `I + J`. No hypothesis on the
ideals. -/
theorem isPushout_quotientFactor :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J)))
      (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J))) := by
  have hsq : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
      CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J)) =
      CommRingCat.ofHom (Ideal.Quotient.mk J) ≫
      CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J)) := by
    ext a; simp
  have hcolim : IsColimit (PushoutCocone.mk
      (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J)))
      (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J))) hsq) := by
    refine PushoutCocone.isColimitAux' _ fun s => ?_
    have hc : ∀ a : A, s.inl.hom (Ideal.Quotient.mk I a)
        = s.inr.hom (Ideal.Quotient.mk J a) := fun a => by
      have := congrArg (fun f : CommRingCat.of A ⟶ s.pt => f.hom a) s.condition
      simpa using this
    have hker : ∀ a ∈ I ⊔ J, (s.inl.hom.comp (Ideal.Quotient.mk I)) a = 0 := by
      intro a ha
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp ha
      have hX : (s.inl.hom.comp (Ideal.Quotient.mk I)) x = 0 := by
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      have hY : (s.inl.hom.comp (Ideal.Quotient.mk I)) y = 0 := by
        simp only [RingHom.comp_apply, hc y]
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
      rw [← hxy, map_add, hX, hY, add_zero]
    refine ⟨CommRingCat.ofHom (Ideal.Quotient.lift (I ⊔ J)
      (s.inl.hom.comp (Ideal.Quotient.mk I)) hker), ?_, ?_, ?_⟩
    · exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => rfl))
    · exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext hc))
    · intro m hm _
      refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_))
      exact congrArg (fun f : CommRingCat.of (A ⧸ I) ⟶ s.pt => f.hom (Ideal.Quotient.mk I a)) hm
  exact IsPushout.of_isColimit hcolim

/-- **The scheme-theoretic intersection, affine case.** `Spec (A ⧸ (I + J))` is the fibre
product of `Spec (A ⧸ I)` and `Spec (A ⧸ J)` over `Spec A`. -/
theorem isPullback_specMap_quotientFactor :
    IsPullback (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.factor (le_sup_left : I ≤ I ⊔ J))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (le_sup_right : J ≤ I ⊔ J))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotientFactor I J)

end Ring

section SchemeLevel

variable {X Z₁ Z₂ : Scheme.{u}}

/-- The support of the kernel of a closed immersion is its range. -/
theorem support_ker_eq_range (i : Z₁ ⟶ X) [IsClosedImmersion i] :
    (i.ker.support : Set X) = Set.range i.base := by
  rw [Scheme.Hom.support_ker]
  exact i.isClosedEmbedding.isClosed_range.closure_eq

/-- **The sheaf-level form of [Stacks, Tag 09NW].** On a reduced scheme, two closed immersions
whose ranges cover have kernels meeting in zero: their scheme-theoretic union is the whole of
`X`. -/
theorem ker_inf_ker_eq_bot [IsReduced X] (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
    i₁.ker ⊓ i₂.ker = ⊥ := by
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  refine le_antisymm le_top ?_
  rw [← SetLike.coe_subset_coe]
  intro x _
  rcases (hcov ▸ Set.mem_univ x) with h | h
  · exact (Scheme.IdealSheafData.support_antitone inf_le_left) ((support_ker_eq_range i₁).ge h)
  · exact (Scheme.IdealSheafData.support_antitone inf_le_right) ((support_ker_eq_range i₂).ge h)

/-- **The affine model of [Stacks, Tag 0E25] is the pushout in the category of all schemes.**
For a span of affine schemes whose first leg is a closed immersion, the square cut out by
`Stacks.Pushout.affineModelInl` and `Stacks.Pushout.affineModelInr` is cocartesian. This is the
general-position form of [Stacks, Tag 0ET0], and the companion of the cartesian statement
`Stacks.Pushout.isPullback_affineModel`. -/
theorem isPushout_affineModel {W : Scheme.{u}} (i : W ⟶ Z₁) (j : W ⟶ Z₂)
    [IsAffine Z₁] [IsAffine Z₂] [IsAffine W] [IsClosedImmersion i] :
    IsPushout i j (Stacks.Pushout.affineModelInl i j) (Stacks.Pushout.affineModelInr i j) := by
  have H := Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective
    i.appTop j.appTop (CommRingCat.ofHom (j.appTop.hom.pullbackFst i.appTop.hom))
    (CommRingCat.ofHom (j.appTop.hom.pullbackSnd i.appTop.hom))
    (Stacks.Pushout.isPullback_ofHom_pullback j.appTop.hom i.appTop.hom)
    (Stacks.Pushout.surjective_appTop_of_isClosedImmersion i)
  refine H.of_iso' W.isoSpec Z₁.isoSpec Z₂.isoSpec (Iso.refl _)
    (Scheme.isoSpec_hom_naturality i) (Scheme.isoSpec_hom_naturality j) ?_ ?_
  · simp [Stacks.Pushout.affineModelInl]
  · simp [Stacks.Pushout.affineModelInr]

variable {W : Scheme.{u}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X) (iW₁ : W ⟶ Z₁) (iW₂ : W ⟶ Z₂)
  [IsAffine Z₁] [IsAffine Z₂] [IsAffine W] [IsClosedImmersion iW₁]

/-- The affine model of the union of two affine closed subschemes meeting in `W`. It is
`Stacks.Pushout.affineModel`, not a second copy of it. -/
noncomputable abbrev model : Scheme.{u} := Stacks.Pushout.affineModel iW₁ iW₂

/-- The canonical comparison morphism from the affine model of the union to `X`, obtained from
the universal property of the pushout applied to the two closed immersions. -/
noncomputable def modelDesc (w : iW₁ ≫ i₁ = iW₂ ≫ i₂) : model iW₁ iW₂ ⟶ X :=
  (isPushout_affineModel iW₁ iW₂).desc i₁ i₂ w

@[simp] theorem inl_modelDesc (w : iW₁ ≫ i₁ = iW₂ ≫ i₂) :
    Stacks.Pushout.affineModelInl iW₁ iW₂ ≫ modelDesc i₁ i₂ iW₁ iW₂ w = i₁ :=
  IsPushout.inl_desc _ _ _ _

@[simp] theorem inr_modelDesc (w : iW₁ ≫ i₁ = iW₂ ≫ i₂) :
    Stacks.Pushout.affineModelInr iW₁ iW₂ ≫ modelDesc i₁ i₂ iW₁ iW₂ w = i₂ :=
  IsPushout.inr_desc _ _ _ _

/-- The comparison morphism from the affine model is surjective as soon as the two closed
subschemes cover `X` set theoretically. -/
theorem surjective_modelDesc (w : iW₁ ≫ i₁ = iW₂ ≫ i₂)
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
    Surjective (modelDesc i₁ i₂ iW₁ iW₂ w) := by
  rw [surjective_iff]
  intro x
  rcases (hcov ▸ Set.mem_univ x) with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact ⟨(Stacks.Pushout.affineModelInl iW₁ iW₂).base z, by
      rw [← Scheme.Hom.comp_apply, inl_modelDesc]⟩
  · exact ⟨(Stacks.Pushout.affineModelInr iW₁ iW₂).base z, by
      rw [← Scheme.Hom.comp_apply, inr_modelDesc]⟩

/-- **The reduction of the reduced case of [Stacks, Tag 09NL] to one property of one
morphism.** If the comparison morphism from the affine model of the union is a closed immersion,
then a reduced scheme covered set theoretically by two affine closed subschemes is affine.

The closed-immersion hypothesis is undischarged: this is a reduction, not a proof of the tag,
and it is stated with an instance binder so that the statement becomes unconditional with no
edit once that property is available. The tag is carried by the statements of
`StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Unconditional`, which do not go through this
reduction. -/
theorem isAffine_of_isClosedImmersion_modelDesc [IsReduced X] (w : iW₁ ≫ i₁ = iW₂ ≫ i₂)
    [IsClosedImmersion (modelDesc i₁ i₂ iW₁ iW₂ w)]
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
    IsAffine X := by
  have : Surjective (modelDesc i₁ i₂ iW₁ iW₂ w) := surjective_modelDesc i₁ i₂ iW₁ iW₂ w hcov
  have : IsIso (modelDesc i₁ i₂ iW₁ iW₂ w) := isIso_of_isClosedImmersion_of_surjective _
  exact (IsAffine.iff_of_isIso (modelDesc i₁ i₂ iW₁ iW₂ w)).mp inferInstance

end SchemeLevel

end Stacks.AffineClosedUnion

end
