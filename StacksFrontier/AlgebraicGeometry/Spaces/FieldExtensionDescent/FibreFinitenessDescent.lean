module

public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.AlgebraicClosureSite

/-!
# Descending finiteness of the fibres on points along an extension of the ground field

Let `k ⊆ K` be an extension of fields whose spectra are objects of a big fppf site and let
`w : Y ⟶ Z` be a morphism of presheaves on the big fppf site over `Spec k`. If every fibre of
the base change of `w` to `K` on points is finite, then so is every fibre of `w`.

This is the second half of what the reduction to an algebraically closed field in the proof of
[Stacks, Tag 0AEM] has to carry back: the first is the factorization itself, which descends
because it is pinned down by an equation, and the second is the finiteness of the fibres of the
second factor, which is the property the contraction process establishes over the algebraically
closed field.

## Main results

* `AlgebraicGeometry.Space.finite_fibre_pointsMap_of_relocalizeRestrict`: **finiteness of the
  fibres on points descends along an extension of the ground field.**
* `AlgebraicGeometry.Space.finite_fibre_pointsMap_of_relocalizeRestrict_algebraicClosure`: the
  same for the algebraic closure of the ground field.

## Implementation notes

The fibre of `w` over a point `z` is shown to be contained in the image of *one* fibre of the
base change, namely the one over a point `z̄` of `Z_K` above `z`. Such a `z̄` exists because base
change is surjective on points,
`AlgebraicGeometry.Space.surjective_pointsOfRelocalizeRestrict_fieldExtension`, and the
containment is where the work is: given a point `y` of `Y` with `w(y) = z`, one has to produce a
point of `Y_K` above `y` whose image under `w_K` is `z̄` — not merely some point of `Z_K` above
`z`.

The two sides are brought together by the very fact that `w(y)` and `z` are the same point of
`Z`: a point of a presheaf on the site is a class of field-valued points under common
extension, so a field-valued representative of `w(y)` and the chosen representative of `z̄`,
read over `k`, admit a *common* field-valued extension `r` of `Z`. The field of `r` carries
both a `K`-structure, through the representative of `z̄`, and a section of `Y` restricted from
the representative of `y`; that is the point of `Y_K` wanted, and the two identities it has to
satisfy are the two domination relations of the common extension.

Presenting the spectrum of the field of `r` as an object of the site over `K` rather than over
`k` is `CategoryTheory.OverShriek.restrictReindex`, and the compatibility of the two
presentations is `CategoryTheory.OverShriek.restrictReindexIso_hom_comp`; without it the two
identities would have to be transported along an equality of objects of the site rather than
along an isomorphism.

## References

* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (k K : Type u) [Field k] [Field K]
  (hk : B.Contains (Spec (.of k))) (hK : B.Contains (Spec (.of K)))
  (g : B.obj hK ⟶ B.obj hk)

/-- **Finiteness of the fibres on points descends along an extension of the ground field.** Let
`w : Y ⟶ Z` be a morphism of presheaves on the big fppf site over `Spec k`. If every fibre of
the base change of `w` along a morphism `Spec K ⟶ Spec k` of the site is finite on points, then
every fibre of `w` is finite on points.

The fibre of `w` over `z` is contained in the image of the fibre of `w_K` over any point `z̄` of
`Z_K` above `z`. -/
theorem finite_fibre_pointsMap_of_relocalizeRestrict
    {Y Z : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u} (w : Y ⟶ Z)
    (hfib : ∀ z : points B (Spec (.of K)) hK ((OverShriek.relocalizeRestrict g).obj Z),
      {x : points B (Spec (.of K)) hK ((OverShriek.relocalizeRestrict g).obj Y) |
        pointsMap B (Spec (.of K)) hK ((OverShriek.relocalizeRestrict g).obj Y)
          ((OverShriek.relocalizeRestrict g).map w) x = z}.Finite)
    (z : points B (Spec (.of k)) hk Z) :
    {y : points B (Spec (.of k)) hk Y | pointsMap B (Spec (.of k)) hk Y w y = z}.Finite := by
  obtain ⟨zbar, hzbar⟩ :=
    surjective_pointsOfRelocalizeRestrict_fieldExtension B k K hk hK g Z z
  refine Set.Finite.subset ((hfib zbar).image
    (pointsOfRelocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk g Y)) ?_
  intro y hy
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  obtain ⟨q, rfl⟩ := Quot.exists_rep zbar
  -- `w(y)` and the chosen representative of `z̄`, read over `k`, are the same point of `Z`
  have hcls : (FieldValuedPoint.map B (Spec (.of k)) hk Y w p).class B (Spec (.of k)) hk Z =
      (FieldValuedPoint.ofRelocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk g Z
        q).class B (Spec (.of k)) hk Z := by
    refine Eq.trans ?_ hzbar.symm
    exact hy
  obtain ⟨r, ⟨σ, hσ⟩, ⟨τ, hτ⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B (Spec (.of k)) hk Z _ _).1 hcls
  -- present the spectrum of the field of `r` as an object of the site over `K`
  let τ' : r.siteObject ⟶ (Over.map g).obj q.siteObject := τ
  let V₁ : BigFppfOver B (Spec (.of K)) hK := OverShriek.restrictReindex g τ'
  let e : (Over.map g).obj V₁ ≅ r.siteObject := OverShriek.restrictReindexIso g τ'
  let ρ : V₁ ⟶ q.siteObject := OverShriek.restrictReindexSnd g τ'
  let x : FieldValuedPoint B (Spec (.of K)) hK ((OverShriek.relocalizeRestrict g).obj Y) :=
    { carrier := r.carrier
      field := r.field
      contained := r.contained
      toBase := B.inclusion.map V₁.hom
      value := Y.map (e.hom ≫ σ).op p.value }
  refine ⟨x.class B (Spec (.of K)) hK _, ?_, ?_⟩
  · -- the image of `x` under `w_K` is the chosen representative of `z̄`
    show (FieldValuedPoint.map B (Spec (.of K)) hK _
      ((OverShriek.relocalizeRestrict g).map w) x).class B (Spec (.of K)) hK _ =
        q.class B (Spec (.of K)) hK _
    refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B (Spec (.of K)) hK _ ?_
    refine ⟨_, FieldValuedPoint.dominates_refl B (Spec (.of K)) hK _ _, ⟨ρ, ?_⟩⟩
    have h₁ : Z.map ((Over.map g).map ρ).op q.value = Z.map e.hom.op r.value := by
      rw [← OverShriek.restrictReindexIso_hom_comp g τ', op_comp, Z.map_comp, types_comp_apply,
        show Z.map τ'.op q.value = r.value from hτ]
    have h₂ : Z.map (e.hom ≫ σ).op
        (FieldValuedPoint.map B (Spec (.of k)) hk Y w p).value =
          Z.map e.hom.op r.value := by
      rw [op_comp, Z.map_comp, types_comp_apply, hσ]
    have h₃ : w.app (op ((Over.map g).obj V₁)) (Y.map (e.hom ≫ σ).op p.value) =
        Z.map (e.hom ≫ σ).op (FieldValuedPoint.map B (Spec (.of k)) hk Y w p).value :=
      NatTrans.naturality_apply w (e.hom ≫ σ).op p.value
    exact h₁.trans (h₂.symm.trans h₃.symm)
  · -- and `x` lies above `y`
    show (FieldValuedPoint.ofRelocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk g Y
      x).class B (Spec (.of k)) hk Y = p.class B (Spec (.of k)) hk Y
    exact FieldValuedPoint.class_eq_class_of_hasCommonExtension B (Spec (.of k)) hk Y
      ⟨_, FieldValuedPoint.dominates_refl B (Spec (.of k)) hk Y _, ⟨e.hom ≫ σ, rfl⟩⟩

/-- `AlgebraicGeometry.Space.finite_fibre_pointsMap_of_relocalizeRestrict` for the algebraic
closure of the ground field: finiteness of the fibres on points established over `k̄` descends
to `k`. -/
theorem finite_fibre_pointsMap_of_relocalizeRestrict_algebraicClosure
    {Y Z : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u} (w : Y ⟶ Z)
    (hfib : ∀ z : points B (Spec (.of (AlgebraicClosure k)))
        (B.contains_spec_algebraicClosure k hk)
        ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj Z),
      {x : points B (Spec (.of (AlgebraicClosure k)))
          (B.contains_spec_algebraicClosure k hk)
          ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj Y) |
        pointsMap B (Spec (.of (AlgebraicClosure k)))
            (B.contains_spec_algebraicClosure k hk)
            ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).obj Y)
          ((OverShriek.relocalizeRestrict (algebraicClosureMap B k hk)).map w) x = z}.Finite)
    (z : points B (Spec (.of k)) hk Z) :
    {y : points B (Spec (.of k)) hk Y | pointsMap B (Spec (.of k)) hk Y w y = z}.Finite :=
  finite_fibre_pointsMap_of_relocalizeRestrict B k (AlgebraicClosure k) hk
    (B.contains_spec_algebraicClosure k hk) (algebraicClosureMap B k hk) w hfib z

end AlgebraicGeometry.Space

end
