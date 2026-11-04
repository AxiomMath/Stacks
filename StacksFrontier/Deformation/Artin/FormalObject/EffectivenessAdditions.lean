module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.Deformation.Artin.FormalObject.Effectiveness
public import StacksFrontier.RingTheory.Nilpotent.Ideal

/-!
# Formal effectiveness for square-zero systems
-/


@[expose] public section

namespace Deformation.Artin

section

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ u₃ v₁ v₂ v₃

end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

/-- **Hypothesis (4) of Artin's criterion [Stacks Project, Tag 0CXU], written out.**  A category
fibred in groupoids over the big fppf site of a locally Noetherian scheme has this property when
every compatible tower of objects over an affine open chart whose transition maps are surjective
with *square-zero* kernel is effective over the canonical cocone coming from the limit of the
tower of algebras.

This differs from `Deformation.Artin.IsStronglyFormallyEffective` in exactly one binder: where
that predicate asks the kernel of each `R_m → R_n` to be `Ideal.LocallyNilpotent`, this one asks
it to square to zero.  Square-zero is the strictly stronger condition on the kernel — it implies
locally nilpotent, by `Ideal.Nilpotent.locallyNilpotent`, and not conversely — so this predicate
quantifies over *fewer* systems and is therefore the strictly **weaker** property of the stack.
The implication between the two is recorded as
`Deformation.Artin.IsStronglyFormallyEffective.isSquareZeroFormallyEffective`.

The distinction is not cosmetic, and it is why this predicate exists.  Hypothesis (4) of
[Stacks Project, Tag 0CXU] reads "systems `(ξₙ)` as in Remark 98.20.2 where `Ker(R_m → R_n)` is
an ideal of square zero for all `m ≥ n` are effective"; so does the opening of
[Stacks Project, Tag 0D3X], "`R_n → R_m` is surjective with square zero kernel".  A tag whose
proof discharges hypothesis (4) therefore establishes *this* predicate, and establishing
`Deformation.Artin.IsStronglyFormallyEffective` instead would prove strictly more than such a
tag asserts.

Carrying no `@[stacks]` attribute is deliberate: this is the statement of a *hypothesis* of
Tag 0CXU and not the assertion of any tag, Tag 0CXU's own content being the implication from its
four hypotheses to openness of versality.  The precedent for writing a tag's statement out as a
reusable named predicate without registering it is
`AlgebraicGeometry.Space.ProperPushoutRS`. -/
public abbrev IsSquareZeroFormallyEffective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [IsLocallyNoetherian S] {X : Type v} [Category.{w} X]
    (p : X ⥤ BigFppfOver B S hS)
    (_hp : p.IsFiberedInGroupoids) : Prop :=
  ∀ (Λ : Type u) [CommRing Λ] (chart : Spec (.of Λ) ⟶ S) [IsOpenImmersion chart]
    (R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ) (cR : Cone R) (_hcR : IsLimit cR)
    (_hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
    (_hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j),
      RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
    (ξ : ℕ ⥤ X) (c : Cocone (ξ ⋙ p))
    (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj ((ξ ⋙ p).obj n) ≅
      Spec (.of (R.obj (.op n))))
    (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt)),
    (∀ {i j : ℕ} (f : i ⟶ j), (BigFppfOver.toScheme B S hS).map ((ξ ⋙ p).map f) ≫
      (e j).hom = (e i).hom ≫
        Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op) →
    (∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
      (e n).hom ≫
        Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op) →
    (eLimit.inv ≫ B.inclusion.map c.pt.hom =
      Scheme.Spec.map (CommRingCat.ofHom (algebraMap Λ cR.pt)).op ≫ chart) →
    IsEffectiveSystem p ξ c

end

end Deformation.Artin
