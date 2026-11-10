module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects

/-!
# Surjectivity on objects against surjectivity on points (Stacks 06D4, 03ME)

Stacks 06D4 calls a 1-morphism of categories over the big fppf site of `S` *surjective on
objects* when every object over the spectrum of a field acquires a lift after passing to a field
extension; Stacks 03ME calls a morphism of algebraic spaces over `S` *surjective* when the
induced map on sets of points is surjective. For a 1-morphism between categories fibred in
groupoids *represented* by algebraic spaces the first implies the second, and that implication is
what the existential diagram criterion of Stacks 06FM — which states its surjectivity hypothesis
on objects — needs in order to be fed to the criteria of Stacks 06FA, which state theirs on
points.

## Main results

* `AlgebraicGeometry.Stack.isFieldObject_siteObject`: the site object of a field-valued point is
  a field object.
* `AlgebraicGeometry.Stack.exists_fieldValuedPoint_of_isFieldObject`: a section over a field
  object restricts to a field-valued point.
* `AlgebraicGeometry.Stack.isSurjective_representingMap_of_isSurjectiveOnObjects`: the
  implication described above.

## Implementation notes

The two notions are stated over different objects, and that is the only real content here.
`AlgebraicGeometry.Stack.IsFieldObject` asks for an *isomorphism* of the underlying scheme with
`Spec` of a field, while `AlgebraicGeometry.Space.FieldValuedPoint` records a section over an
object whose underlying scheme *is* such a spectrum. The transport is
`AlgebraicGeometry.Scheme.size_congr`: the spectrum has the same size as the scheme it is
isomorphic to, hence lies in the site, and the comparison isomorphism is a morphism of the site
over `S` once the structure morphism is taken to be the composite.

No declaration carries a `@[stacks]` attribute: Stacks 06D4 and 03ME tag the two definitions,
which are in the library, and the source states this implication only inside the proof of Stacks
06FM.

## References

* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The object of the big fppf site of `S` underlying a field-valued point of a presheaf is a
field object in the sense of Stacks 06D4: its underlying scheme *is* the spectrum of the field of
definition, so the required isomorphism is the identity. -/
theorem isFieldObject_siteObject
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (q : Space.FieldValuedPoint B S hS F) :
    IsFieldObject B S hS q.siteObject :=
  ⟨q.carrier, q.field, ⟨Iso.refl _⟩⟩

/-- **A section over a field object is dominated by a field-valued point.** A field object of the
big fppf site of `S` carries only an *isomorphism* of its underlying scheme with the spectrum of
a field, while a field-valued point of a presheaf is a section over an object whose underlying
scheme is that spectrum on the nose. Transporting along the isomorphism turns the one into the
other: the spectrum lies in the site because `AlgebraicGeometry.Scheme.size` is an isomorphism
invariant, its structure morphism is the composite with the given one, and the section restricts
along the comparison. -/
theorem exists_fieldValuedPoint_of_isFieldObject
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (V : BigFppfOver B S hS)
    (hV : IsFieldObject B S hS V) (s : F.obj (op V)) :
    ∃ (q : Space.FieldValuedPoint B S hS F) (g : q.siteObject ⟶ V),
      F.map g.op s = q.value := by
  obtain ⟨k, hk, ⟨ι⟩⟩ := hV
  let : Field k := hk
  have hk' : B.Contains (Spec (.of k)) := by
    change (Spec (CommRingCat.of k)).size < B.cutoff
    rw [← Scheme.size_congr ι]
    exact V.left.2
  let gS : (Spec (CommRingCat.of k)) ⟶ S := ι.inv ≫ V.hom.hom
  let W : BigFppfOver B S hS := Over.mk (⟨gS⟩ : B.obj hk' ⟶ B.obj hS)
  let g : W ⟶ V := Over.homMk (⟨ι.inv⟩ : B.obj hk' ⟶ V.left) (by ext; rfl)
  exact ⟨{ carrier := k, contained := hk', toBase := gS, value := F.map g.op s }, g, rfl⟩

/-- **Surjectivity on objects implies surjectivity on points**, for a 1-morphism between
categories fibred in groupoids represented by presheaves `F` and `G`: if `a` is surjective on
objects in the sense of Stacks 06D4, the induced morphism `F ⟶ G` of representing presheaves is
a surjective morphism of algebraic spaces in the sense of Stacks 03ME.

Given a field-valued point of `G`, its section is named by an object `y` of the target over the
corresponding field object; surjectivity on objects produces a field object `V`, a morphism
`V ⟶ W`, an object `x` of the source over `V` and a vertical-up-to-`g` morphism `a x ⟶ y`. The
section of `F` named by `x` then restricts to a field-valued point of `F` whose image under the
induced morphism is dominated by the given point, so the two define the same point of `G`. -/
theorem isSurjective_representingMap_of_isSurjectiveOnObjects
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒜 ⟶ 𝒞)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (ha : IsSurjectiveOnObjects B S hS 𝒜.val.p 𝒞.val.p
      (CatFiberedInGroupoids.homFunctor a)) :
    Space.IsSurjective B S hS (representingMap B S hS 𝒜 𝒞 F G eF eG a) := by
  intro p
  induction p using Quot.ind with
  | _ q =>
  have hy : 𝒞.val.p.obj (eG.inv.functor.obj
      (⟨q.siteObject, Discrete.mk q.value⟩ :
        (presheafOfCategories (G ⋙ typeToCat)).obj)) = q.siteObject :=
    Functor.congr_obj eG.inv.w _
  obtain ⟨V, hVfield, g, x, hx, α, hα⟩ := ha q.siteObject
    (isFieldObject_siteObject B S hS G q) _ hy
  obtain ⟨q', g', hq'⟩ := exists_fieldValuedPoint_of_isFieldObject B S hS F V hVfield
    (PresheafOfCategories.sectionOfObj eF x hx)
  refine ⟨q'.class B S hS F, ?_⟩
  rw [Space.pointsMap_class]
  refine Space.FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS G
    ⟨_, Space.FieldValuedPoint.dominates_refl B S hS G _, ⟨g' ≫ g, ?_⟩⟩
  have hax : 𝒞.val.p.obj ((CatFiberedInGroupoids.homFunctor a).obj x) = V :=
    (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p a) x).trans hx
  have hstep : (representingMap B S hS 𝒜 𝒞 F G eF eG a).app (op V)
      (PresheafOfCategories.sectionOfObj eF x hx) = G.map g.op q.value := by
    rw [morphismSpaceEquiv_app_sectionOfObj B S hS 𝒜 𝒞 F G eF eG
      ⟨CatFiberedInGroupoids.homFunctor a, CatFiberedInGroupoids.homFunctor_comp_p a⟩ x hx]
    rw [PresheafOfCategories.sectionOfObj_map eG hy hax g α hα]
    exact congrArg _ (PresheafOfCategories.sectionOfObj_inv_obj eG
      (⟨q.siteObject, Discrete.mk q.value⟩ :
        (presheafOfCategories (G ⋙ typeToCat)).obj))
  change G.map (g' ≫ g).op q.value =
    (representingMap B S hS 𝒜 𝒞 F G eF eG a).app (op q'.siteObject) q'.value
  rw [← hq']
  have hnat := congrFun (congrArg (fun t => TypeCat.homEquiv t)
    ((representingMap B S hS 𝒜 𝒞 F G eF eG a).naturality g'.op))
    (PresheafOfCategories.sectionOfObj eF x hx)
  simp only [TypeCat.homEquiv_apply, ConcreteCategory.comp_apply] at hnat
  rw [hnat, hstep, op_comp, G.map_comp, types_comp_apply]

end AlgebraicGeometry.Stack

end
