module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise

/-!
# Monomorphisms of algebraic stacks are injective on points

A monomorphism of algebraic stacks induces an injective map between their sets of points.

## Main results

* `AlgebraicGeometry.Stack.pointsMap_injective_of_fullyFaithful`: a 1-morphism of algebraic
  stacks whose underlying functor is fully faithful induces an injective map on points.

## Implementation notes

A monomorphism of stacks is expressed by full faithfulness of the underlying functor, as in
Tag 04ZZ.

## References

* [Stacks Project, Tag 0500](https://stacks.math.columbia.edu/tag/0500)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

/-- A monomorphism of algebraic stacks induces an injective map on points. -/
@[stacks 0500]
public theorem pointsMap_injective_of_fullyFaithful
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴)
    [Functor.Full (CatFiberedInGroupoids.homFunctor f.hom)]
    [Functor.Faithful (CatFiberedInGroupoids.homFunctor f.hom)] :
    Function.Injective
      (pointsMap B S hS 𝒳.val.val
        (Classical.choose 𝒳.property) (Classical.choose 𝒴.property) f.hom.hom) := by
  let G := CatFiberedInGroupoids.homFunctor f.hom
  let pX := 𝒳.val.val.p
  let pY := 𝒴.val.val.p
  have hG : G ⋙ pY = pX := CatFiberedInGroupoids.homFunctor_comp_p f.hom
  have hX : pX.IsFiberedInGroupoids := Classical.choose 𝒳.property
  have hY : pY.IsFiberedInGroupoids := Classical.choose 𝒴.property
  intro a b hab
  refine Quotient.inductionOn₂ a b ?_ hab
  intro x y hxy
  rw [pointsMap_class, pointsMap_class,
    class_eq_class_iff_hasCommonExtension] at hxy
  obtain ⟨r, ⟨φ⟩, ⟨ψ⟩⟩ := hxy
  let fx : r.base ⟶ x.base :=
    eqToHom r.over.symm ≫ pY.map φ ≫
      eqToHom ((Functor.congr_obj hG x.obj).trans x.over)
  obtain ⟨z, χ, hχ⟩ := hX.exists_lift fx x.obj x.over
  have hz : pX.obj z = r.base := IsHomLift.domain_eq pX fx χ
  let s : FieldValuedPoint B S hS 𝒳.val.val :=
    { carrier := r.carrier
      field := r.field
      base := r.base
      isSpec := r.isSpec
      obj := z
      over := hz }
  have hGχ : pY.IsHomLift fx (G.map χ) :=
    (Functor.isHomLift_map_iff_of_comp_eq pX pY G hG fx χ).2 hχ
  have hφ : pY.IsHomLift fx φ :=
    IsHomLift.of_fac pY fx φ r.over ((Functor.congr_obj hG x.obj).trans x.over) rfl
  have hcartχ : pY.IsStronglyCartesian fx (G.map χ) := hY.isStronglyCartesian_homLift fx _
  have hcartφ : pY.IsStronglyCartesian fx φ := hY.isStronglyCartesian_homLift fx _
  have hrefl : fx = (Iso.refl r.base).hom ≫ fx := by simp
  set α : r.obj ≅ G.obj z :=
    @Functor.IsStronglyCartesian.domainIsoOfBaseIso _ _ _ _ pY
      r.base r.base x.base (G.obj z) r.obj (G.obj x.obj)
      fx fx (Iso.refl r.base) hrefl (G.map χ) φ hcartχ hcartφ with hαdef
  have hα : α.hom ≫ G.map χ = φ := by
    rw [hαdef, @Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom _ _ _ _ pY
      r.base r.base x.base (G.obj z) r.obj (G.obj x.obj)
      fx fx (Iso.refl r.base) hrefl (G.map χ) φ hcartχ hcartφ]
    exact @Functor.IsStronglyCartesian.fac _ _ _ _ pY
      r.base x.base (G.obj z) (G.obj x.obj) fx (G.map χ) hcartχ
      r.base r.obj (Iso.refl r.base).hom fx hrefl φ hφ
  obtain ⟨δ, -⟩ := Functor.Full.map_surjective (F := G) (α.symm.hom ≫ ψ)
  exact (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val.val hX x y).2 ⟨s, ⟨χ⟩, ⟨δ⟩⟩

end AlgebraicGeometry.Stack

end
