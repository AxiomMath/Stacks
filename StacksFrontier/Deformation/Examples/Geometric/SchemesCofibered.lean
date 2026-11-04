module

public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The deformation category of a scheme is cofibered in groupoids

`Deformation.Examples.flatSchemeFamilyProjection_cofiberedInGroupoids` says that flat families
of schemes over `𝒞_Λ` are cofibered in groupoids: a family can be base changed along any
morphism of the base, and an arrow out of it descends uniquely through that base change.  The
deformation category `Deformation.Examples.SchemeDeformationCategory` of a fixed scheme `X`
over the residue field is *not* formed as a slice of that category — it is a structure of its
own, carrying in addition the identification of the fibre over the closed point as a cartesian
square — so the statement does not follow from it, and nothing in the library had it.

This file supplies it.  The base change of a deformation is the base change of the family,
with its identification of the special fibre obtained from the universal property of the
fibre product: the closed point of `Spec B` maps to the closed point of `Spec A`
(`Deformation.Examples.residueSpecMap_naturality`), so the identification carried by the
original deformation and the structure morphism of `X` to `Spec B` agree over `Spec A` and
induce a morphism `X ⟶ P.scheme ×_{Spec A} Spec B`.  That morphism is cartesian over the
closed point of `Spec B` by cancelling the cartesian square of the base change, which is
`CategoryTheory.IsPullback.of_right`.

Both halves of the cofibered condition then follow exactly as for flat families, the extra
compatibility with the identification of the special fibre being forced: the two descended
morphisms into a fibre product agree because their composites with both projections do, which
is `CategoryTheory.IsPullback.hom_ext`.

## The use

`Deformation.full_of_exists_lift_of_isHomLift_id` reduces fullness of a morphism of categories
cofibered in groupoids to the arrows lying over an identity of the base, and it asks for the
cofibered condition on *both* projections.  For the source-forgetful functor of
[Stacks, Tag 0E3X] the upper one is
`Deformation.Examples.schemeMorphismDeformationCategoryProjection_cofiberedInGroupoids`; the
lower one is the theorem proved here.

## Main definitions

* `Deformation.Examples.baseChangeDeformation` — the base change of a deformation of a scheme
  along a morphism of `𝒞_Λ`.
* `Deformation.Examples.baseChangeDeformationHom` — the arrow onto it.

## Main results

* `Deformation.Examples.schemeDeformationCategoryProjection_cofiberedInGroupoids` — **the
  deformation category of a scheme is cofibered in groupoids.**

## Implementation notes

The proof is the proof of
`Deformation.Examples.flatSchemeFamilyProjection_cofiberedInGroupoids` with the two extra
fields threaded through, and is deliberately kept parallel to it: the existence half produces
the same base change and the same arrow, and the uniqueness half descends the same morphism
through the same cartesian square.  The only genuinely new step is the identification of the
special fibre of the base change, and the only input it needs about `𝒞_Λ` is that its
morphisms commute with the residue maps — which is what
`Deformation.Examples.residueSpecMap_naturality` records.

The base change is taken as Mathlib's `CategoryTheory.Limits.pullback` rather than as an
abstract cartesian square, so that `CategoryTheory.Limits.pullback.lift` is available for the
identification of the special fibre and `CategoryTheory.Limits.pullback.lift_fst` discharges
the compatibility of the arrow with it on the nose.

Flatness of the base change is `inferInstance`: flatness of morphisms of schemes is stable
under base change (`AlgebraicGeometry.Flat.isStableUnderBaseChange`), and the instance for the
second projection of a pullback fires once the flatness of the original family is in scope.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 06GJ](https://stacks.math.columbia.edu/tag/06GJ)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

section BaseChange

variable {X : Over (Spec (.of k))} (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
  {B : ArtinianLocalAlgCat.{u, u, u} Λ k} (g : P.base ⟶ B)

/-- **The base change of a deformation of a scheme along a morphism of `𝒞_Λ`.** The total space
is the fibre product `P.scheme ×_{Spec A} Spec B`, flat over `Spec B` because flatness is
stable under base change, and its fibre over the closed point of `Spec B` is again `X`: the
closed point of `Spec B` lies over the closed point of `Spec A`, so the identification carried
by `P` factors through the fibre product. -/
def baseChangeDeformation : SchemeDeformationCategory (Λ := Λ) (k := k) X :=
  haveI := P.flat
  { base := B
    scheme := pullback P.toBase (baseSpecMap g)
    toBase := pullback.snd P.toBase (baseSpecMap g)
    flat := inferInstance
    specialMap := pullback.lift P.specialMap (X.hom ≫ residueSpecMap B) (by
      rw [P.specialCartesian.w, Category.assoc, residueSpecMap_naturality])
    specialCartesian := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback P.toBase (baseSpecMap g))
      rw [pullback.lift_fst, residueSpecMap_naturality]
      exact P.specialCartesian }

/-- The base of the base change of a deformation along `g : A ⟶ B` is `B`. -/
@[simp]
theorem baseChangeDeformation_base : (baseChangeDeformation P g).base = B := rfl

/-- **The arrow of a deformation onto its base change.** Its component on total spaces is the
first projection of the fibre product, which is cartesian by construction and compatible with
the two identifications of the special fibre by the universal property that defines the
second. -/
def baseChangeDeformationHom : P ⟶ baseChangeDeformation P g where
  base := g
  map := pullback.fst P.toBase (baseSpecMap g)
  cartesian := IsPullback.of_hasPullback _ _
  special_compat := pullback.lift_fst _ _ _

/-- The arrow of a deformation onto its base change along `g` lies over `g`. -/
@[simp]
theorem baseChangeDeformationHom_base : (baseChangeDeformationHom P g).base = g := rfl

end BaseChange

/-- **The deformation category of a scheme is cofibered in groupoids.** A deformation can be
base changed along any morphism of `𝒞_Λ`
(`Deformation.Examples.baseChangeDeformation`), and an arrow out of a deformation descends
uniquely through that base change, because its component on total spaces is determined by the
universal property of the fibre product.

This is the lower half of the cofibered condition that
`Deformation.full_of_exists_lift_of_isHomLift_id` asks of the source-forgetful functor of
[Stacks, Tag 0E3X]. -/
@[stacks 0DY7 "cofibred_projection, for the deformation category of a scheme",
  sga "7 VI 1.1(c)" "more general"]
theorem schemeDeformationCategoryProjection_cofiberedInGroupoids
    (X : Over (Spec (.of k))) :
    IsCofiberedInGroupoids (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) := by
  let p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X
  show (p.op).IsFiberedInGroupoids
  refine ⟨?_, ?_⟩
  · intro V U f x hx
    cases hx
    let f₀ := f.unop
    let φ := baseChangeDeformationHom x.unop f₀
    refine ⟨Opposite.op (baseChangeDeformation x.unop f₀), φ.op, ?_⟩
    rw [show f = p.op.map φ.op from rfl]
    exact Functor.IsHomLift.map φ.op
  · intro x y z φ ψ f h
    have h₀ : φ.unop.base ≫ f.unop = ψ.unop.base := congrArg Quiver.Hom.unop h
    let χ₀ : y.unop ⟶ z.unop :=
      { base := f.unop
        map := φ.unop.cartesian.lift ψ.unop.map (z.unop.toBase ≫ baseSpecMap f.unop) (by
          rw [ψ.unop.cartesian.w, ← h₀, baseSpecMap_comp]
          simp)
        cartesian := by
          refine IsPullback.of_right ?_ (φ.unop.cartesian.lift_snd _ _ _) φ.unop.cartesian
          rw [φ.unop.cartesian.lift_fst, ← baseSpecMap_comp, h₀]
          exact ψ.unop.cartesian
        special_compat := by
          refine φ.unop.cartesian.hom_ext ?_ ?_
          · rw [Category.assoc, φ.unop.cartesian.lift_fst, ψ.unop.special_compat,
              φ.unop.special_compat]
          · rw [Category.assoc, φ.unop.cartesian.lift_snd, ← Category.assoc,
              z.unop.specialCartesian.w, Category.assoc, residueSpecMap_naturality,
              y.unop.specialCartesian.w] }
    refine ⟨χ₀.op, ⟨?_, ?_⟩, fun χ hχ => ?_⟩
    · constructor
    · exact Quiver.Hom.unop_inj
        (SchemeDeformationCategory.Hom.ext h₀ (φ.unop.cartesian.lift_fst _ _ _))
    · have hb : χ.unop.base = f.unop := congrArg Quiver.Hom.unop hχ.1
      apply Quiver.Hom.unop_inj
      refine SchemeDeformationCategory.Hom.ext hb (φ.unop.cartesian.hom_ext ?_ ?_)
      · exact (congrArg SchemeDeformationCategory.Hom.map (congrArg Quiver.Hom.unop hχ.2)).trans
          (φ.unop.cartesian.lift_fst _ _ _).symm
      · rw [χ.unop.cartesian.w, hb]
        exact (φ.unop.cartesian.lift_snd _ _ _).symm

end Deformation.Examples

end
