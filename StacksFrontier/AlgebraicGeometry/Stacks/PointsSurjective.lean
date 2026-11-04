module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative

/-!
# Surjectivity of a representable morphism of algebraic stacks on points (Stacks 04XI)

A 1-morphism of algebraic stacks over `S` which is representable by algebraic spaces is
surjective — in the sense of the relative property of Stacks 03YK applied to surjectivity of
morphisms of algebraic spaces — exactly when the map it induces on the point sets of Stacks 04XG
is surjective.

The comparison runs through surjectivity *on objects* in the sense of Stacks 06D4: Stacks 06D7
identifies that with the relative property, and the two implications proved here identify it with
surjectivity on points. A point of the target is represented by an object over the spectrum of a
field, so a lift of that object after a field extension is exactly a field-valued point of the
source whose image has a common refinement with the chosen one; conversely, a field-valued point
of the source whose image represents the given point supplies the lift, after transporting along
the strongly cartesian morphism over the comparison arrow.

## Main results

* `AlgebraicGeometry.Stack.pointsMap_surjective_of_isSurjectiveOnObjects` and
  `AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_pointsMap_surjective`: the two implications
  between surjectivity on objects (Stacks 06D4) and surjectivity of the map on points, neither of
  which needs the 1-morphism to be representable by algebraic spaces.
* `AlgebraicGeometry.Stack.pointsMap_surjective_iff_isRelativelySurjective`: **Stacks 04XI**.

## Implementation notes

Algebraicity of the source and the target is used only to produce the fibred-in-groupoids
witnesses that the point sets of Stacks 04XG are indexed by; they are read off
`AlgebraicGeometry.Stack.IsAlgebraicStack`, which is an existential over such a witness, by
`Classical.choose`. No presentation is chosen.

The backward implication produces its lift by the universal property of a strongly cartesian
morphism: the common refinement of the two field-valued points gives an arrow of the site, the
source lifts it to a cartesian morphism, its image in the target is cartesian because a
1-morphism of categories fibred in groupoids preserves cartesian morphisms, and the comparison
arrow factors through it by an isomorphism.

## References

* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- Surjectivity on objects of a 1-morphism of algebraic stacks implies surjectivity of the
induced map on points: a lift of a representative of the given point, after a field extension, is
a field-valued point of the source whose image refines it. -/
theorem pointsMap_surjective_of_isSurjectiveOnObjects
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴)
    (h : IsSurjectiveOnObjects B S hS 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor) :
    Function.Surjective
      (pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
        (Classical.choose 𝒴.property) f.hom.hom) := by
  intro z
  obtain ⟨q, rfl⟩ := Quotient.exists_rep z
  obtain ⟨V, ⟨k, hk, ⟨eV⟩⟩, g, x, hx, α, hα⟩ :=
    h q.base ⟨q.carrier, q.field, ⟨q.isSpec⟩⟩ q.obj q.over
  let p : FieldValuedPoint B S hS 𝒳.val.val :=
    { carrier := k, field := hk, base := V, isSpec := eV, obj := x, over := hx }
  refine ⟨pointClass B S hS 𝒳.val.val (Classical.choose 𝒳.property) p, ?_⟩
  rw [pointsMap_class]
  exact (class_eq_class_iff_hasCommonExtension B S hS 𝒴.val.val (Classical.choose 𝒴.property)
    (fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom p) q).2
    ⟨_, ⟨⟨𝟙 _⟩, ⟨by simpa [fieldValuedPointMap, p] using α⟩⟩⟩

/-- Surjectivity of the induced map on points implies surjectivity on objects: a field-valued
point of the source refining the given object gives, through the universal property of the
cartesian lift of the comparison arrow, an object of the source over a field object and a
morphism of the target to the given object. -/
theorem isSurjectiveOnObjects_of_pointsMap_surjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴)
    (h : Function.Surjective
      (pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
        (Classical.choose 𝒴.property) f.hom.hom)) :
    IsSurjectiveOnObjects B S hS 𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor := by
  intro U hU y hy
  obtain ⟨k, hk, ⟨eU⟩⟩ := hU
  let q : FieldValuedPoint B S hS 𝒴.val.val :=
    { carrier := k, field := hk, base := U, isSpec := eU, obj := y, over := hy }
  obtain ⟨z, hz⟩ := h (pointClass B S hS 𝒴.val.val (Classical.choose 𝒴.property) q)
  obtain ⟨p, rfl⟩ := Quotient.exists_rep z
  have heq :
      pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
        (Classical.choose 𝒴.property) f.hom.hom
        (pointClass B S hS 𝒳.val.val (Classical.choose 𝒳.property) p) =
      pointClass B S hS 𝒴.val.val (Classical.choose 𝒴.property) q := hz
  rw [pointsMap_class] at heq
  obtain ⟨r, ⟨α⟩, ⟨β⟩⟩ := (class_eq_class_iff_hasCommonExtension B S hS 𝒴.val.val
    (Classical.choose 𝒴.property) (fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom p) q).1 heq
  let hX := Classical.choose 𝒳.property
  let hY := Classical.choose 𝒴.property
  let g := 𝒴.val.val.p.map α
  obtain ⟨x, φ, hφ⟩ := hX.exists_lift g p.obj (f.hom.hom.w_obj p.obj).symm
  have hx : 𝒳.val.val.p.obj x = 𝒴.val.val.p.obj r.obj :=
    IsHomLift.domain_eq 𝒳.val.val.p g φ
  have hφImageCart : 𝒴.val.val.p.IsStronglyCartesian g (f.hom.hom.toFunctor.map φ) :=
    CatFiberedInGroupoids.isStronglyCartesian_map f.hom g φ
  have hαLift : 𝒴.val.val.p.IsHomLift g α :=
    IsHomLift.of_fac' 𝒴.val.val.p g α rfl rfl (by simp [g])
  obtain ⟨χ, hχ, -⟩ :=
    @Functor.IsStronglyCartesian.universal_property _ _ _ _ 𝒴.val.val.p
      (𝒴.val.val.p.obj r.obj)
      (𝒴.val.val.p.obj (fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom p).obj)
      (f.hom.hom.toFunctor.obj x) (f.hom.hom.toFunctor.obj p.obj)
      g (f.hom.hom.toFunctor.map φ) hφImageCart
      (𝒴.val.val.p.obj r.obj) r.obj (𝟙 (𝒴.val.val.p.obj r.obj)) g (by simp) α hαLift
  have : 𝒴.val.val.p.IsHomLift (𝟙 (𝒴.val.val.p.obj r.obj)) χ := hχ.1
  have : 𝒴.val.val.p.IsStronglyCartesian (𝟙 (𝒴.val.val.p.obj r.obj)) χ :=
    hY.isStronglyCartesian_homLift _ χ
  have : IsIso χ :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒴.val.val.p
      (𝟙 (𝒴.val.val.p.obj r.obj)) χ
  have : 𝒴.val.val.p.IsHomLift (𝟙 (𝒴.val.val.p.obj r.obj)) (inv χ) :=
    IsHomLift.lift_id_inv_isIso 𝒴.val.val.p (𝒴.val.val.p.obj r.obj) χ
  let g' : 𝒴.val.val.p.obj r.obj ⟶ U := 𝒴.val.val.p.map β ≫ eqToHom q.over
  have : 𝒴.val.val.p.IsHomLift g' β :=
    IsHomLift.of_fac' 𝒴.val.val.p g' β rfl q.over (by simp [g'])
  exact ⟨𝒴.val.val.p.obj r.obj, ⟨r.carrier, r.field,
    ⟨eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj r.over) ≪≫ r.isSpec⟩⟩,
    g', x, hx, inv χ ≫ β, IsHomLift.comp_lift_id_left 𝒴.val.val.p g' β (inv χ)⟩

/-- **Stacks 04XI.** A 1-morphism of algebraic stacks over `S` which is representable by
algebraic spaces is surjective — the relative property of Stacks 03YK at surjectivity of
morphisms of algebraic spaces — exactly when the map it induces on points is surjective. -/
@[stacks 04XI]
theorem pointsMap_surjective_iff_isRelativelySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    Function.Surjective
        (pointsMap B S hS 𝒳.val.val (Classical.choose 𝒳.property)
          (Classical.choose 𝒴.property) f.hom.hom) ↔
      HasRelativeProperty B S hS (Space.surjectiveMorphismProperty B S hS) f.hom hf := by
  have hRelative :
      IsSurjectiveOnObjects B S hS 𝒳.val.val.p 𝒴.val.val.p
          (CatFiberedInGroupoids.homFunctor f.hom) ↔
        HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
          (Space.surjectiveMorphismProperty B S hS) f.hom hf :=
    isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS f.hom hf
  exact ⟨fun hP ↦ hRelative.mp (isSurjectiveOnObjects_of_pointsMap_surjective B S hS f hP),
    fun hP ↦ pointsMap_surjective_of_isSurjectiveOnObjects B S hS f (hRelative.mpr hP)⟩

end AlgebraicGeometry.Stack

end
