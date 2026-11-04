module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Points and quasi-compactness are invariant under an equivalence

A 1-morphism over the big fppf site of `S` whose underlying functor is essentially surjective is
surjective on the points of Stacks 04XG, and therefore carries quasi-compactness of an algebraic
stack (Stacks 04YB) forward. Specialised to the comparison 1-morphism between two 2-fibre products
of one cospan, this says that quasi-compactness of a 2-fibre product of algebraic stacks does not
depend on which 2-fibre product square it is read off.

## Main results

* `AlgebraicGeometry.Stack.pointsMap_surjective_of_essSurj`: a 1-morphism over the site with
  essentially surjective underlying functor is surjective on points.
* `AlgebraicGeometry.Stack.isQuasiCompactStack_of_essSurj`: quasi-compactness of an algebraic
  stack transports along such a 1-morphism.
* `AlgebraicGeometry.Stack.isQuasiCompactStack_of_isTwoFibreProduct`: any two 2-fibre products of
  one cospan of algebraic stacks are quasi-compact together.

## Implementation notes

No verticality is asked of the underlying functor beyond the strict commutation already carried by
a `CategoryTheory.BasedFunctor`, and in particular no `CategoryTheory.BasedCategory.Equivalence`
and no `CategoryTheory.Functor.IsEquivalenceOver` is needed. The reason is visible in the two
definitions involved: a `AlgebraicGeometry.Stack.FieldValuedPoint` carries its base object of the
site together with an *isomorphism* of its underlying scheme with a field spectrum, rather than an
equality; and `AlgebraicGeometry.Stack.FieldValuedPoint.HasCommonExtension` asks only for a third
field-valued point with *arrows* to the two given ones, with no condition on what those arrows do
to the base. So the essential-image isomorphism `F.obj x ≅ p.obj` of the underlying functor can be
used twice over: its image under the structure functor repairs the base identification, and the
isomorphism itself is the arrow exhibiting the common refinement.

Essential surjectivity is taken as an instance argument so that the hypothesis is discharged from
`CategoryTheory.Functor.IsEquivalence` by its own field
`CategoryTheory.Functor.IsEquivalence.essSurj`, which is the form in which
`AlgebraicGeometry.Stack.isEquivalence_of_isTwoFibreProduct_algebraicStacks` delivers it.

## References

* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v t v' t' w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A 1-morphism over the big fppf site whose underlying functor is essentially surjective is
surjective on points.**

Given a field-valued point `p` of the target, an object `x` of the source with an isomorphism
`α : F.obj x ≅ p.obj` is a field-valued point of the source over `𝒳.p.obj x`: its underlying
scheme is identified with the field spectrum of `p` by transporting `p`'s own identification along
the image of `α` under the structure functor. Its image under `F` and `p` then admit a common
refinement, namely that image itself, with `α` as the second arrow. -/
theorem pointsMap_surjective_of_essSurj
    {𝒳 : BasedCategory.{v, t} (BigFppfOver B S hS)}
    {𝒴 : BasedCategory.{v', t'} (BigFppfOver B S hS)}
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (F : 𝒳 ⥤ᵇ 𝒴) [F.toFunctor.EssSurj] :
    Function.Surjective (pointsMap B S hS 𝒳 h𝒳 h𝒴 F) := by
  intro y
  obtain ⟨p, rfl⟩ := Quotient.exists_rep y
  let x := F.toFunctor.objPreimage p.obj
  let α : F.toFunctor.obj x ≅ p.obj := F.toFunctor.objObjPreimageIso p.obj
  let e₀ : 𝒳.p.obj x ≅ p.base :=
    eqToIso (F.w_obj x).symm ≪≫ 𝒴.p.mapIso α ≪≫ eqToIso p.over
  let q : FieldValuedPoint B S hS 𝒳 :=
    { carrier := p.carrier
      base := 𝒳.p.obj x
      isSpec := (BigFppfOver.toScheme B S hS).mapIso e₀ ≪≫ p.isSpec
      obj := x
      -- `over` is a keyword token in this import closure (Mathlib's `name_poly_vars … over …`
      -- command), so the field name has to be escaped.
      «over» := rfl }
  exact ⟨Quotient.mk _ q, Quotient.sound ⟨_, ⟨𝟙 _⟩, ⟨α.hom⟩⟩⟩

variable {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **Quasi-compactness of an algebraic stack transports along a 1-morphism whose underlying
functor is essentially surjective.** Such a 1-morphism is surjective in the sense of Stacks 04ZS —
which is `AlgebraicGeometry.Stack.pointsMap_surjective_of_essSurj` at an unfolded abbreviation, so
no separate lemma is stated for it — and the target's point space is then the image of a compact
space under a continuous map. -/
theorem isQuasiCompactStack_of_essSurj (f : 𝒰 ⟶ 𝒳) [f.hom.hom.toFunctor.EssSurj]
    (h𝒰 : IsQuasiCompactStack B S hS 𝒰.val 𝒰.property) :
    IsQuasiCompactStack B S hS 𝒳.val 𝒳.property :=
  isQuasiCompactStack_of_isSurjective B S hS f h𝒰
    (pointsMap_surjective_of_essSurj B S hS _ _ f.hom.hom)

/-- **Any two 2-fibre products of one cospan of algebraic stacks are quasi-compact together.** The
comparison 1-morphism supplied by terminality of the second square has an underlying functor that
is an equivalence, by
`AlgebraicGeometry.Stack.isEquivalence_of_isTwoFibreProduct_algebraicStacks`, hence is essentially
surjective.

This is what makes quasi-compactness of a morphism of algebraic stacks (Stacks 050U) testable
against *any* 2-fibre product square of the cospan rather than only the canonical one. -/
theorem isQuasiCompactStack_of_isTwoFibreProduct {𝒰 𝒰' 𝒵 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒰 ⟶ 𝒵} {g : 𝒰' ⟶ 𝒵} {P Q : Bicategory.TwoCommSq f g}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hPqc : IsQuasiCompactStack B S hS P.pt.val P.pt.property) :
    IsQuasiCompactStack B S hS Q.pt.val Q.pt.property := by
  let a : Bicategory.TwoCommSq.PreHom P Q := Quotient.out (hQ.from P)
  have : a.hom.hom.hom.toFunctor.IsEquivalence :=
    isEquivalence_of_isTwoFibreProduct_algebraicStacks B S hS hP hQ a
  exact isQuasiCompactStack_of_essSurj B S hS a.hom hPqc

end AlgebraicGeometry.Stack

end
