module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Points
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids

/-!
# Points of a 2-fibre product (Stacks 04XH)

Let `g : 𝒵 ⟶ 𝒴` and `f : 𝒳 ⟶ 𝒴` be 1-morphisms of categories fibred in groupoids over the
big fppf site of `S`, and let `P` be a 2-fibre product of that cospan. The canonical map

```text
|P| ⟶ |𝒵| ×_{|𝒴|} |𝒳|
```

is surjective: a point of `𝒵` and a point of `𝒳` with the same image in `|𝒴|` lift to a
point of `P`. This is the statement of **Stacks 04XH**.

## Main results

* `AlgebraicGeometry.Stack.exists_point_of_coneHom'`: the comparison form of the statement, whose
  hypothesis on the square is only that the canonical 2-fibre product square maps to it as a
  cone, with the universes of the three categories free.
* `AlgebraicGeometry.Stack.exists_point_of_coneHom`: the same with the universes of the three
  categories fixed.
* `AlgebraicGeometry.Stack.exists_point_of_isTwoFibreProduct`: **Stacks 04XH** for a 2-fibre
  product in the 2-category of categories fibred in groupoids.

## Implementation notes

The conclusion is stated elementwise, so no auxiliary definition of the set-theoretic fibre
product or of the canonical map into it is needed, and it applies to any 2-fibre-product
square rather than to a chosen model.

The proof is the one of the source. Represent the two points by field-valued points `z₀` of
`𝒵` and `x₀` of `𝒳`. Their images in `|𝒴|` agree, so by
`AlgebraicGeometry.Stack.class_eq_class_iff_hasCommonExtension` there is a field-valued point
`r` of `𝒴` with arrows `iz` to `g z₀` and `ix` to `f x₀`. Writing `R` for the base of `r`,
pull `z₀` and `x₀` back along the induced maps `R ⟶ base z₀` and `R ⟶ base x₀`, which is
possible because `𝒵` and `𝒳` are fibred in groupoids; this gives objects `z'` over `R` and
`x'` over `R` with arrows to `z₀` and `x₀`. The comparison of `g z'` and `f x'` with `r` is
obtained from the uniqueness clause of the fibred-in-groupoids property, and both comparisons
are isomorphisms because they lie over isomorphisms
(`CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso`). So `(R, z', x')` together
with the composite isomorphism `g z' ≅ f x'` is an object of the canonical 2-fibre product
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`, hence a field-valued point of
it, whose two projections represent the given points. Finally the canonical square maps to
`P` by terminality of `P`, and that 1-morphism carries the constructed point to one of `P`;
the two projection conditions are its comparison 2-cells, which do not move points by
`AlgebraicGeometry.Stack.pointClass_fieldValuedPointMap_eq_of_basedNatTrans`.

Terminality in the 2-category of *categories fibred in groupoids* is strictly stronger than
terminality in the full sub-2-category of algebraic stacks, so the statement for algebraic
stacks of the source does not follow from a theorem carrying that hypothesis. The content is
therefore separated out as `AlgebraicGeometry.Stack.exists_point_of_coneHom`, which assumes only
what the argument uses — a 1-morphism out of the apex of the canonical square together with two
comparison 2-cells. Terminality at either level supplies that much, since the apex of the
canonical square is itself an algebraic stack whenever the three corners are (Stacks 04TF); the
algebraic-stacks form is
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_point_of_isTwoFibreProduct` in
`StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange`.

## References

* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v t

/-- **The comparison form of Stacks 04XH, with the universes of the three categories free.**
A point of `𝒵` and a point of `𝒳` with the same image in `|𝒴|` lift to a point of a
2-commutative square `P` over the cospan `(g, f)`, as soon as the *canonical* 2-fibre product
square maps to `P` as a cone — that is, as soon as there are a 1-morphism `k` out of its apex and
2-cells comparing the two projections. Neither invertibility of the comparison 2-cells nor any
compatibility between them is needed. -/
theorem exists_point_of_coneHom'
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) t) (max u v)}
      (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f)
    (k : (CatFiberedInGroupoids.twoFibreProductSquare.{u, v, u + 1, t} g f).pt ⟶ P.pt)
    (ηfst :
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, v, u + 1, t} g f).fst ⟶ k ≫ P.fst)
    (ηsnd :
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, v, u + 1, t} g f).snd ⟶ k ≫ P.snd)
    (z : points B S hS 𝒵.val 𝒵.property) (x : points B S hS 𝒳.val 𝒳.property)
    (h : pointsMap B S hS 𝒵.val 𝒵.property 𝒴.property g.hom z =
      pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property f.hom x) :
    ∃ p : points B S hS P.pt.val P.pt.property,
      pointsMap B S hS P.pt.val P.pt.property 𝒵.property P.fst.hom p = z ∧
        pointsMap B S hS P.pt.val P.pt.property 𝒳.property P.snd.hom p = x := by
  classical
  obtain ⟨z₀, rfl⟩ := Quotient.exists_rep z
  obtain ⟨x₀, rfl⟩ := Quotient.exists_rep x
  rw [pointsMap_class, pointsMap_class] at h
  let Z := 𝒵.val
  let X := 𝒳.val
  let Y := 𝒴.val
  let F := g.hom
  let G := f.hom
  let zY := fieldValuedPointMap B S hS Z F z₀
  let xY := fieldValuedPointMap B S hS X G x₀
  obtain ⟨r, ⟨iz⟩, ⟨ix⟩⟩ :=
    (class_eq_class_iff_hasCommonExtension B S hS Y 𝒴.property zY xY).mp h
  let hZ : Z.p.IsFiberedInGroupoids := 𝒵.property
  let hX : X.p.IsFiberedInGroupoids := 𝒳.property
  let hY : Y.p.IsFiberedInGroupoids := 𝒴.property
  let R := Y.p.obj r.obj
  let bZ : R ⟶ Z.p.obj z₀.obj := Y.p.map iz ≫ eqToHom (BasedFunctor.w_obj F z₀.obj)
  let bX : R ⟶ X.p.obj x₀.obj := Y.p.map ix ≫ eqToHom (BasedFunctor.w_obj G x₀.obj)
  obtain ⟨z', φz, hφz⟩ := hZ.exists_lift bZ z₀.obj rfl
  obtain ⟨x', φx, hφx⟩ := hX.exists_lift bX x₀.obj rfl
  have hliftZ : Z.p.IsHomLift bZ φz := hφz
  have hliftX : X.p.IsHomLift bX φx := hφx
  have hFφ : Y.p.IsHomLift bZ (F.map φz) := BasedFunctor.preserves_isHomLift F bZ φz
  have hGφ : Y.p.IsHomLift bX (G.map φx) := BasedFunctor.preserves_isHomLift G bX φx
  have eZ : Y.p.obj (F.obj z') = R := IsHomLift.domain_eq Y.p bZ (F.map φz)
  have eX : Y.p.obj (G.obj x') = R := IsHomLift.domain_eq Y.p bX (G.map φx)
  let fZ : R ⟶ Y.p.obj (F.obj z') := eqToHom eZ.symm
  let fX : R ⟶ Y.p.obj (G.obj x') := eqToHom eX.symm
  have hcodZ : IsHomLift.codomain_eq Y.p bZ (F.map φz) = BasedFunctor.w_obj F z₀.obj :=
    Subsingleton.elim _ _
  have hcodX : IsHomLift.codomain_eq Y.p bX (G.map φx) = BasedFunctor.w_obj G x₀.obj :=
    Subsingleton.elim _ _
  have hbaseZ : fZ ≫ Y.p.map (F.map φz) = Y.p.map iz := by
    rw [IsHomLift.fac' Y.p bZ (F.map φz), hcodZ]
    simp only [fZ, bZ, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [Category.assoc, ← Category.comp_id (Y.p.map iz)]
    apply congrArg (fun k ↦ Y.p.map iz ≫ k)
    dsimp [zY, fieldValuedPointMap]
    rw [eqToHom_trans]
    simp
  have hbaseX : fX ≫ Y.p.map (G.map φx) = Y.p.map ix := by
    rw [IsHomLift.fac' Y.p bX (G.map φx), hcodX]
    simp only [fX, bX, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [Category.assoc, ← Category.comp_id (Y.p.map ix)]
    apply congrArg (fun k ↦ Y.p.map ix ≫ k)
    dsimp [xY, fieldValuedPointMap]
    rw [eqToHom_trans]
    simp
  obtain ⟨uZ, ⟨huZ, hcompZ⟩, -⟩ := hY.unique_lift (F.map φz) iz fZ hbaseZ
  obtain ⟨uX, ⟨huX, hcompX⟩, -⟩ := hY.unique_lift (G.map φx) ix fX hbaseX
  have hlZ : Y.p.IsHomLift fZ uZ := by rw [← huZ]; infer_instance
  have hlX : Y.p.IsHomLift fX uX := by rw [← huX]; infer_instance
  have hisoFZ : IsIso fZ := inferInstance
  have hisoFX : IsIso fX := inferInstance
  have hIsoZ : IsIso uZ := by
    have := hY.isStronglyCartesian_homLift fZ uZ
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := Y.p) (f := fZ) uZ
  have hIsoX : IsIso uX := by
    have := hY.isStronglyCartesian_homLift fX uX
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := Y.p) (f := fX) uX
  let isoZX : F.obj z' ≅ G.obj x' := (asIso uZ).symm ≪≫ asIso uX
  let qSquare := CatFiberedInGroupoids.twoFibreProductSquare.{u, v, u + 1, t} g f
  let qObj : TwoFibreProductOver Z.p X.p Y.p F.toFunctor G.toFunctor :=
    { base := R
      x := z'
      y := x'
      hx := IsHomLift.domain_eq Z.p bZ φz
      hy := IsHomLift.domain_eq X.p bX φx
      iso := isoZX
      vertical := by
        apply IsHomLift.of_fac' Y.p (𝟙 R) isoZX.hom eZ eX
        have hinvZ : Y.p.IsHomLift (inv fZ) (inv uZ) := by
          have hz : Y.p.IsHomLift (asIso fZ).hom (asIso uZ).hom := by
            simpa using (show Y.p.IsHomLift fZ uZ from inferInstance)
          exact IsHomLift.inv_lift_inv Y.p (asIso fZ) (asIso uZ)
        have hLiftIso : Y.p.IsHomLift (inv fZ ≫ fX) (inv uZ ≫ uX) :=
          IsHomLift.comp Y.p (inv fZ) fX (inv uZ) uX
        have hbaseIso : inv fZ ≫ fX = eqToHom eZ ≫ eqToHom eX.symm := by simp [fZ, fX]
        change Y.p.map (inv uZ ≫ uX) = eqToHom eZ ≫ eqToHom eX.symm
        rw [IsHomLift.fac' Y.p (inv fZ ≫ fX) (inv uZ ≫ uX)]
        simp [hbaseIso] }
  have hR : R = r.base := r.over
  let qPoint : FieldValuedPoint B S hS qSquare.pt.val :=
    { carrier := r.carrier
      base := R
      isSpec := eqToIso (congrArg (fun U ↦ (BigFppfOver.toScheme B S hS).obj U) hR) ≪≫ r.isSpec
      obj := qObj
      over := rfl }
  let qPointZ := fieldValuedPointMap B S hS qSquare.pt.val qSquare.fst.hom qPoint
  let qPointX := fieldValuedPointMap B S hS qSquare.pt.val qSquare.snd.hom qPoint
  have hzQ : pointClass B S hS Z hZ qPointZ = pointClass B S hS Z hZ z₀ := by
    apply (class_eq_class_iff_hasCommonExtension B S hS Z hZ qPointZ z₀).2
    refine ⟨qPointZ, ⟨𝟙 _⟩, ⟨?_⟩⟩
    change z' ⟶ z₀.obj
    exact φz
  have hxQ : pointClass B S hS X hX qPointX = pointClass B S hS X hX x₀ := by
    apply (class_eq_class_iff_hasCommonExtension B S hS X hX qPointX x₀).2
    refine ⟨qPointX, ⟨𝟙 _⟩, ⟨?_⟩⟩
    change x' ⟶ x₀.obj
    exact φx
  let H := k.hom
  let pPoint := fieldValuedPointMap B S hS qSquare.pt.val H qPoint
  have hAlphaZ : pointClass B S hS Z hZ qPointZ =
      pointClass B S hS Z hZ (fieldValuedPointMap B S hS P.pt.val P.fst.hom pPoint) := by
    have hη : BasedNatTrans qSquare.fst.hom (H.comp P.fst.hom) := ηfst.hom
    have hkey := pointClass_fieldValuedPointMap_eq_of_basedNatTrans B S hS
      qSquare.pt.val hZ hη qPoint
    simpa [qPointZ, pPoint, H, fieldValuedPointMap] using hkey
  have hAlphaX : pointClass B S hS X hX qPointX =
      pointClass B S hS X hX (fieldValuedPointMap B S hS P.pt.val P.snd.hom pPoint) := by
    have hη : BasedNatTrans qSquare.snd.hom (H.comp P.snd.hom) := ηsnd.hom
    have hkey := pointClass_fieldValuedPointMap_eq_of_basedNatTrans B S hS
      qSquare.pt.val hX hη qPoint
    simpa [qPointX, pPoint, H, fieldValuedPointMap] using hkey
  refine ⟨pointClass B S hS P.pt.val P.pt.property pPoint, ?_, ?_⟩
  · rw [pointsMap_class]
    exact hAlphaZ.symm.trans hzQ
  · rw [pointsMap_class]
    exact hAlphaX.symm.trans hxQ

/-- The comparison form of **Stacks 04XH**: a point of `𝒵` and a point of `𝒳` with the same
image in `|𝒴|` lift to a point of a 2-commutative square `P` over the cospan `(g, f)`, as soon
as the *canonical* 2-fibre product square maps to `P` as a cone — that is, as soon as there are a
1-morphism `k` out of its apex and 2-cells comparing the two projections. Neither invertibility
of the comparison 2-cells nor any compatibility between them is needed. -/
theorem exists_point_of_coneHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f)
    (k : (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).pt ⟶ P.pt)
    (ηfst :
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).fst ⟶ k ≫ P.fst)
    (ηsnd :
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f).snd ⟶ k ≫ P.snd)
    (z : points B S hS 𝒵.val 𝒵.property) (x : points B S hS 𝒳.val 𝒳.property)
    (h : pointsMap B S hS 𝒵.val 𝒵.property 𝒴.property g.hom z =
      pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property f.hom x) :
    ∃ p : points B S hS P.pt.val P.pt.property,
      pointsMap B S hS P.pt.val P.pt.property 𝒵.property P.fst.hom p = z ∧
        pointsMap B S hS P.pt.val P.pt.property 𝒳.property P.snd.hom p = x :=
  exists_point_of_coneHom'.{u, u, u + 1} B S hS P k ηfst ηsnd z x h

/-- **Points of a 2-fibre product of categories fibred in groupoids**: a point of `𝒵` and a
point of `𝒳` with the same image in `|𝒴|` lift to a point of any 2-fibre product of
`g : 𝒵 ⟶ 𝒴` and `f : 𝒳 ⟶ 𝒴`. -/
@[stacks 04XH "for a 2-fibre product of categories fibred in groupoids"]
theorem exists_point_of_isTwoFibreProduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (z : points B S hS 𝒵.val 𝒵.property) (x : points B S hS 𝒳.val 𝒳.property)
    (h : pointsMap B S hS 𝒵.val 𝒵.property 𝒴.property g.hom z =
      pointsMap B S hS 𝒳.val 𝒳.property 𝒴.property f.hom x) :
    ∃ p : points B S hS P.pt.val P.pt.property,
      pointsMap B S hS P.pt.val P.pt.property 𝒵.property P.fst.hom p = z ∧
        pointsMap B S hS P.pt.val P.pt.property 𝒳.property P.snd.hom p = x := by
  classical
  obtain ⟨α, -⟩ :=
    Quotient.exists_rep
      (hP.from (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g f))
  exact exists_point_of_coneHom B S hS P α.hom α.isoFst.hom α.isoSnd.hom z x h

end AlgebraicGeometry.Stack

end
