module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointResidualGerbeImplications

/-!
# The residual gerbe at a finite type point, from a quotient presentation of the point

Let `𝒳` be an algebraic stack over `S` and let `x ∈ |𝒳|` be a finite type point, so that, by
condition (1) of Stacks 06FX, there are a field `k` and a 1-morphism `u : Spec(k) ⟶ 𝒳` which is
locally of finite type and whose image on points is `{x}`. This module proves the implication
(1) ⟹ (3) of Stacks 06G3 — the residual gerbe of `𝒳` at `x` exists and its inclusion is locally
of finite type — granted that every such `u` factors, up to 2-isomorphism, as a surjective flat
1-morphism locally of finite presentation onto an algebraic stack followed by a fully faithful
1-morphism.

## Main definitions

* `AlgebraicGeometry.Stack.HasFullyFaithfulFiniteTypeFieldPointPresentations`: every
  locally-of-finite-type field-valued point factors through a fully faithful 1-morphism as above.

## Main results

* `AlgebraicGeometry.Stack.hasLocallyOfFiniteTypeResidualGerbeAt_of_hasPresentation`: condition
  (3) of Stacks 06G3 at a finite type point, granted such factorizations.
* `AlgebraicGeometry.Stack.existsLocallyOfFiniteTypeResidualGerbe_of_hasPresentation`: the
  implication (1) ⟹ (3) of Stacks 06G3 for every finite type point, granted such factorizations.

## References

* [Stacks Project, Tag 06FX](https://stacks.math.columbia.edu/tag/06FX)
* [Stacks Project, Tag 06G3](https://stacks.math.columbia.edu/tag/06G3)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Fully faithful factorizations of locally-of-finite-type field-valued points.** Every
1-morphism `u` to an algebraic stack over `S` from the algebraic stack of the spectrum of a field
which is locally of finite type factors, up to 2-isomorphism, as a surjective flat 1-morphism
locally of finite presentation onto an algebraic stack followed by a fully faithful 1-morphism. -/
abbrev HasFullyFaithfulFiniteTypeFieldPointPresentations : Prop :=
  ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (F : FieldSpectrum B S hS)
    (u : schemeStack.{u, w} B S hS F.base ⟶ 𝒳),
    AlgebraicStacks.IsLocallyOfFiniteType B S hS u →
      ∃ (𝒵 : AlgebraicStacks.{u, w} B S hS) (f : 𝒵 ⟶ 𝒳)
        (z : schemeStack.{u, w} B S hS F.base ⟶ 𝒵),
        (CatFiberedInGroupoids.homFunctor f.hom).Full ∧
          (CatFiberedInGroupoids.homFunctor f.hom).Faithful ∧
            AlgebraicStacks.IsLocallyOfFinitePresentation B S hS z ∧
              IsSurjective B S hS z ∧
                AlgebraicStacks.IsFlat B S hS z ∧ Nonempty (z ≫ f ≅ u)

/-- **Condition (3) of Stacks 06G3 at a finite type point, from the quotient presentation of the
point.** Let `𝒳` be an algebraic stack over `S` and let `x` be a finite type point of it. If every
locally-of-finite-type 1-morphism out of a field-spectrum stack factors as a surjective flat
1-morphism locally of finite presentation followed by a fully faithful one, then the residual
gerbe of `𝒳` at `x` exists and its inclusion is locally of finite type. -/
theorem hasLocallyOfFiniteTypeResidualGerbeAt_of_hasPresentation
    (hpres : HasFullyFaithfulFiniteTypeFieldPointPresentations.{u, w} B S hS)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (x : points B S hS 𝒳.val.val 𝒳.val.property)
    (hx : IsFiniteTypePoint.{u, w} B S hS 𝒳 x) :
    HasLocallyOfFiniteTypeResidualGerbeAt.{u, w} B S hS 𝒳 x := by
  obtain ⟨p, hpx, hplft⟩ := hx
  set F : FieldSpectrum B S hS :=
    { carrier := p.carrier, field := p.field, base := p.base, isSpec := p.isSpec } with hF
  set u : schemeStack.{u, w} B S hS F.base ⟶ 𝒳 :=
    fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p with hu
  have hsub : Subsingleton (points B S hS (schemeStack.{u, w} B S hS p.base).val.val
      (schemeStack.{u, w} B S hS p.base).val.property) :=
    subsingleton_points_fieldValuedPointBaseStack.{u, w} B S hS p
  have hkey : AlgebraicStacks.pointsMap B S hS u
      (pointClass B S hS (schemeStack.{u, w} B S hS p.base).val.val
        (schemeStack.{u, w} B S hS p.base).val.property p.atBase) = x :=
    (pointClass_fieldValuedPointMap_atBase B S hS 𝒳.val p).trans hpx
  have hurange : Set.range (AlgebraicStacks.pointsMap B S hS u) = {x} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hkey⟩, ?_⟩
    rintro - ⟨a, rfl⟩
    rwa [hsub.elim a (pointClass B S hS (schemeStack.{u, w} B S hS p.base).val.val
      (schemeStack.{u, w} B S hS p.base).val.property p.atBase)]
  obtain ⟨𝒵, f, z, hfull, hfaith, hzlfp, hzsurj, hzflat, ⟨α⟩⟩ := hpres 𝒳 F u hplft
  have hzf : AlgebraicStacks.IsLocallyOfFiniteType B S hS (z ≫ f) :=
    AlgebraicStacks.isLocallyOfFiniteType_of_twoIso B S hS
      (Bicategory.InducedBicategory.isoHom α.symm) hplft
  have himg : Set.range (AlgebraicStacks.pointsMap B S hS f) = {x} :=
    calc Set.range (AlgebraicStacks.pointsMap B S hS f)
        = Set.range (AlgebraicStacks.pointsMap B S hS f ∘ AlgebraicStacks.pointsMap B S hS z) :=
          (hzsurj.range_comp _).symm
      _ = Set.range (AlgebraicStacks.pointsMap B S hS (z ≫ f)) := by
          rw [AlgebraicStacks.pointsMap_comp]
      _ = Set.range (AlgebraicStacks.pointsMap B S hS u) := by
          rw [AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS α.hom]
      _ = {x} := hurange
  exact hasLocallyOfFiniteTypeResidualGerbeAt_of_full_of_faithful.{u, w} B S hS 𝒳 𝒵 f hfull
    hfaith F z hzlfp hzsurj hzflat hzf x himg

/-- **The implication (1) ⟹ (3) of Stacks 06G3, from the quotient presentation of a finite type
point.** If every locally-of-finite-type 1-morphism out of a field-spectrum stack factors as a
surjective flat 1-morphism locally of finite presentation followed by a fully faithful one, then
at every finite type point of `𝒳` the residual gerbe exists and its inclusion is locally of finite
type. -/
theorem existsLocallyOfFiniteTypeResidualGerbe_of_hasPresentation
    (hpres : HasFullyFaithfulFiniteTypeFieldPointPresentations.{u, w} B S hS)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    ExistsLocallyOfFiniteTypeResidualGerbeOfIsFiniteTypePoint.{u, w} B S hS 𝒳 :=
  fun x hx => hasLocallyOfFiniteTypeResidualGerbeAt_of_hasPresentation.{u, w} B S hS hpres 𝒳 x hx

end AlgebraicGeometry.Stack

end
