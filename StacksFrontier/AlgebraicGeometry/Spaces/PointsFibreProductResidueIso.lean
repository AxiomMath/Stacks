module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# Points of a fibre product over a point with trivial residue field extension

Let `q : A ⟶ C` be a morphism of schemes of the big fppf site and let `a` be a point of `A` at
which `q` induces an isomorphism of residue fields `κ(q(a)) ≅ κ(a)`, as an elementary étale
neighbourhood does at its distinguished point.  For a presheaf `W` with a morphism to `h_C`, the
points of the fibre product `P = W ×_{h_C} h_A` lying over `a` are determined by their images in
`|W|`: two points of `|P|` with the same image in `|W|` and the same image `a` in `|A|` are equal.

This is the injectivity half of the description of the points of a fibre product above a pair
of points, in the special case where one residue field extension is trivial; it needs no
hypothesis on `W`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.eq_of_comp_eq_of_isIso_residueFieldMap`: two morphisms from the
  spectrum of a field into a scheme `A`, both landing at a point `a` at which `q : A ⟶ C`
  induces an isomorphism of residue fields, agree as soon as they agree after composing with
  `q`.
* `AlgebraicGeometry.Space.eq_of_pointsMap_eq_of_isPullback_of_isIso_residueFieldMap`: the
  statement on the points of a fibre product above.

## Implementation notes

A morphism `Spec K ⟶ A` with image `a` is a field embedding `κ(a) ⟶ K` followed by
`Spec κ(a) ⟶ A`, by Mathlib's `AlgebraicGeometry.Scheme.SpecToEquivOfField`; composing with `q`
precomposes the embedding with the residue field map of `q` at `a`, which is invertible.

For the points of the fibre product, two field-valued representatives with the same image in
`|W|` have a common field-valued extension there.  Restricting both representatives to it gives
two sections of `P` over the same field spectrum with the same component in `W`; their
components in `h_A` are morphisms from that field spectrum to `A` with image `a` agreeing over
`C`, hence equal by the first result, and so the two sections are equal, being sections of a
fibre product of presheaves.  That section is the common extension of the two representatives.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Two field points of a scheme through a point with trivial residue extension are
determined by their composite.**  Let `q : A ⟶ C` induce an isomorphism of residue fields at
`a`, and let `m₁ m₂ : Spec K ⟶ A` both have image `a`.  If `m₁ ≫ q = m₂ ≫ q`, then
`m₁ = m₂`. -/
theorem Scheme.Hom.eq_of_comp_eq_of_isIso_residueFieldMap {A C : Scheme.{u}} (q : A ⟶ C)
    (a : A) [IsIso (q.residueFieldMap a)] {K : Type u} [Field K]
    {m₁ m₂ : Spec (CommRingCat.of K) ⟶ A} (h₁ : ∀ s, m₁ s = a) (h₂ : ∀ s, m₂ s = a)
    (hq : m₁ ≫ q = m₂ ≫ q) : m₁ = m₂ := by
  obtain ⟨φ₁, rfl⟩ := exists_residueFieldHom_comp_fromSpecResidueField m₁ a h₁
  obtain ⟨φ₂, rfl⟩ := exists_residueFieldHom_comp_fromSpecResidueField m₂ a h₂
  have key : ∀ φ : A.residueField a ⟶ CommRingCat.of K,
      (Spec.map φ ≫ A.fromSpecResidueField a) ≫ q =
        (Scheme.SpecToEquivOfField K C).symm ⟨q a, q.residueFieldMap a ≫ φ⟩ := by
    intro φ
    simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [key, key] at hq
  have hsig := (Scheme.SpecToEquivOfField K C).symm.injective hq
  have h : q.residueFieldMap a ≫ φ₁ = q.residueFieldMap a ≫ φ₂ :=
    eq_of_heq (Sigma.mk.inj hsig).2
  rw [cancel_epi] at h
  rw [h]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Two sections of a fibre product of presheaves with the same components are equal. -/
theorem eq_of_isPullback_app {P W Z C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {pW : P ⟶ W} {pZ : P ⟶ Z} {w : W ⟶ C} {z : Z ⟶ C} (sq : IsPullback pW pZ w z)
    {U : BigFppfOver B S hS} {s₁ s₂ : P.obj (Opposite.op U)}
    (hW : pW.app _ s₁ = pW.app _ s₂) (hZ : pZ.app _ s₁ = pZ.app _ s₂) : s₁ = s₂ := by
  refine yonedaEquiv.symm.injective (sq.hom_ext ?_ ?_)
  · apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hW]
  · apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hZ]

/-- The point of a represented presheaf cut out by a field-valued point is the image of the
closed point of the field spectrum under the morphism of schemes that point is. -/
theorem pointsToScheme_class_eq (A : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj A))
    (s : (BigFppfOver.toScheme B S hS).obj p.siteObject) :
    pointsToScheme B S hS A (p.class B S hS (yoneda.obj A)) =
      (BigFppfOver.toScheme B S hS).map p.value s := by
  rw [pointsToScheme_class]
  change (BigFppfOver.toScheme B S hS).map p.value (IsLocalRing.closedPoint p.carrier) = _
  congr 1
  exact @Subsingleton.elim _ (inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier))))
    _ _

/-- **The points of a fibre product over a point with trivial residue field extension are
determined by their images in the other factor.**  Let `P` be a fibre product of `w : W ⟶ h_C`
and `yoneda.map q : h_A ⟶ h_C`, for `q : A ⟶ C` a morphism of the site inducing an isomorphism
of residue fields at the point `a` of `A`.  Two points of `|P|` with the same image in `|W|` and
both lying over `a` are equal.

No hypothesis is made on `W`: this is a statement about field-valued points and common
extensions only. -/
theorem eq_of_pointsMap_eq_of_isPullback_of_isIso_residueFieldMap
    {P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {A C : BigFppfOver B S hS}
    {pW : P ⟶ W} {pA : P ⟶ yoneda.obj A} {w : W ⟶ yoneda.obj C} {q : A ⟶ C}
    (sq : IsPullback pW pA w (yoneda.map q)) (a : (BigFppfOver.toScheme B S hS).obj A)
    [IsIso (((BigFppfOver.toScheme B S hS).map q).residueFieldMap a)]
    {ξ₁ ξ₂ : points B S hS P} (hW : pointsMap B S hS P pW ξ₁ = pointsMap B S hS P pW ξ₂)
    (h₁ : pointsToScheme B S hS A (pointsMap B S hS P pA ξ₁) = a)
    (h₂ : pointsToScheme B S hS A (pointsMap B S hS P pA ξ₂) = a) : ξ₁ = ξ₂ := by
  obtain ⟨p₁, rfl⟩ := Quot.exists_rep ξ₁
  obtain ⟨p₂, rfl⟩ := Quot.exists_rep ξ₂
  -- A common extension of the two images in `|W|`.
  obtain ⟨r, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS W _ _).1 hW
  -- The two representatives restricted to it.
  set s₁ : P.obj (Opposite.op r.siteObject) := P.map f₁.op p₁.value
  set s₂ : P.obj (Opposite.op r.siteObject) := P.map f₂.op p₂.value
  have hWs₁ : pW.app _ s₁ = r.value := (NatTrans.naturality_apply pW f₁.op p₁.value).trans hf₁
  have hWs₂ : pW.app _ s₂ = r.value := (NatTrans.naturality_apply pW f₂.op p₂.value).trans hf₂
  -- The field-valued points of `P` they define.
  let mk : P.obj (Opposite.op r.siteObject) → FieldValuedPoint B S hS P := fun t =>
    { carrier := r.carrier, contained := r.contained, toBase := r.toBase, value := t }
  have hρ₁ : (mk s₁).class B S hS P = p₁.class B S hS P :=
    FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS P
      ⟨mk s₁, FieldValuedPoint.dominates_refl B S hS P (mk s₁), ⟨f₁, rfl⟩⟩
  have hρ₂ : (mk s₂).class B S hS P = p₂.class B S hS P :=
    FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS P
      ⟨mk s₂, FieldValuedPoint.dominates_refl B S hS P (mk s₂), ⟨f₂, rfl⟩⟩
  -- Their components in `h_A` are morphisms of the site landing at `a`.
  have hland : ∀ (ρ : FieldValuedPoint B S hS P),
      pointsToScheme B S hS A (pointsMap B S hS P pA (ρ.class B S hS P)) = a →
      ∀ s, (BigFppfOver.toScheme B S hS).map (pA.app _ ρ.value) s = a := by
    intro ρ hρ s
    rw [← hρ, pointsMap_class]
    exact (pointsToScheme_class_eq B S hS A (FieldValuedPoint.map B S hS P pA ρ) s).symm
  -- They agree over `C`.
  have hC : pA.app _ s₁ ≫ q = pA.app _ s₂ ≫ q := by
    have e₁ := congrFun (congrArg (fun φ => φ.app (Opposite.op r.siteObject)) sq.w) s₁
    have e₂ := congrFun (congrArg (fun φ => φ.app (Opposite.op r.siteObject)) sq.w) s₂
    simp only [NatTrans.comp_app_apply] at e₁ e₂
    change (yoneda.map q).app _ (pA.app _ s₁) = (yoneda.map q).app _ (pA.app _ s₂)
    rw [← e₁, ← e₂, hWs₁, hWs₂]
  have hA : pA.app _ s₁ = pA.app _ s₂ := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    refine Scheme.Hom.eq_of_comp_eq_of_isIso_residueFieldMap
      ((BigFppfOver.toScheme B S hS).map q) a (hland (mk s₁) (by rwa [hρ₁]))
      (hland (mk s₂) (by rwa [hρ₂])) ?_
    rw [← Functor.map_comp, ← Functor.map_comp, hC]
  have hs : s₁ = s₂ := eq_of_isPullback_app B S hS sq (hWs₁.trans hWs₂.symm) hA
  refine hρ₁.symm.trans (Eq.trans ?_ hρ₂)
  rw [hs]

end Space

end AlgebraicGeometry

end
