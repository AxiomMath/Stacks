module

public import StacksFrontier.CategoryTheory.Adjunction.ConjugateTransport

/-!
# The conjugated associativity cocycle, as an equality of isomorphisms

`CategoryTheory.Functor.compConj_cocycle_app` says that the associativity cocycle law for four
composition comparisons survives conjugation by isomorphisms of the six functors involved, at
a component.  This file records the same statement as an equality of *isomorphisms of
functors*.

## Main results

* `CategoryTheory.Functor.compConj_cocycle`: **the conjugated associativity pentagon**, as an
  equality of isomorphisms.

## Implementation notes

The two forms are not interchangeable in practice.  A client whose six functors are two
spellings of one category of `𝒪`-modules — `AlgebraicGeometry.Space.Modules` over a small
étale ringed site and sheaves of modules over the structure ring sheaf of the corresponding
ringed topos — can instantiate the componentwise form, since there the defeq between the two
spellings is decided once, at the size of a morphism.  Passing from the componentwise form to
the isomorphism form *at those functors* asks the kernel to decide it again under the binder
of `CategoryTheory.NatTrans.ext`, and it does not finish.  Proving the isomorphism form here,
where the functors are variables, and instantiating it in one application keeps the check at
the size of an isomorphism, which is where it does finish.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor

variable {A₀ A₁ A₂ A₃ : Type*} [Category* A₀] [Category* A₁] [Category* A₂] [Category* A₃]

/-- **The associativity cocycle law survives conjugation**, as an equality of isomorphisms of
functors.  This is `CategoryTheory.Functor.compConj_cocycle_app` assembled over all objects;
the hypothesis is the same cocycle law for the four unconjugated comparisons. -/
theorem compConj_cocycle
    {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {r r' : A₂ ⥤ A₃} {pq pq' : A₀ ⥤ A₂}
    {qr qr' : A₁ ⥤ A₃} {pqr pqr' : A₀ ⥤ A₃}
    (up : p ≅ p') (uq : q ≅ q') (ur : r ≅ r') (upq : pq ≅ pq') (uqr : qr ≅ qr')
    (upqr : pqr ≅ pqr') (P : p' ⋙ q' ≅ pq') (Q : q' ⋙ r' ≅ qr') (PQ : pq' ⋙ r' ≅ pqr')
    (QR : p' ⋙ qr' ≅ pqr')
    (h : ∀ N, r'.map (P.hom.app N) ≫ PQ.hom.app N = Q.hom.app (p'.obj N) ≫ QR.hom.app N) :
    isoWhiskerRight (compConj up uq upq P) r ≪≫ compConj upq ur upqr PQ =
      associator p q r ≪≫ isoWhiskerLeft p (compConj uq ur uqr Q) ≪≫
        compConj up uqr upqr QR :=
  by ext N; simpa using compConj_cocycle_app up uq ur upq uqr upqr P Q PQ QR h N

/-- The conjugated associativity pentagon, in the orientation that the pasting law of adjoint
mates consumes:  the short way round, read from `p ⋙ (q ⋙ r)`. -/
theorem compConj_cocycle'
    {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {r r' : A₂ ⥤ A₃} {pq pq' : A₀ ⥤ A₂}
    {qr qr' : A₁ ⥤ A₃} {pqr pqr' : A₀ ⥤ A₃}
    (up : p ≅ p') (uq : q ≅ q') (ur : r ≅ r') (upq : pq ≅ pq') (uqr : qr ≅ qr')
    (upqr : pqr ≅ pqr') (P : p' ⋙ q' ≅ pq') (Q : q' ⋙ r' ≅ qr') (PQ : pq' ⋙ r' ≅ pqr')
    (QR : p' ⋙ qr' ≅ pqr')
    (h : ∀ N, r'.map (P.hom.app N) ≫ PQ.hom.app N = Q.hom.app (p'.obj N) ≫ QR.hom.app N) :
    isoWhiskerLeft p (compConj uq ur uqr Q) ≪≫ compConj up uqr upqr QR =
      (associator p q r).symm ≪≫ isoWhiskerRight (compConj up uq upq P) r ≪≫
        compConj upq ur upqr PQ := by
  rw [compConj_cocycle up uq ur upq uqr upqr P Q PQ QR h]
  ext N; simp

/-- **The associativity pentagon at a component, from the pentagon as an equality of
isomorphisms.**  The two forms differ by moving one factor across an inverse;  this is the
shape in which the pasting argument
`Stacks.Cohomology.DerivedBaseChangePasting.squareComparison_horizontal` consumes the
pentagon, and the isomorphism form is the one that conjugation produces. -/
theorem pentagon_app_of_trans_assoc
    {F₀₁ : A₀ ⥤ A₁} {F₁₂ : A₁ ⥤ A₂} {F₂₃ : A₂ ⥤ A₃} {F₀₂ : A₀ ⥤ A₂} {F₁₃ : A₁ ⥤ A₃}
    {F₀₃ : A₀ ⥤ A₃}
    (α₀₁₂ : F₀₁ ⋙ F₁₂ ≅ F₀₂) (α₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃) (α₀₁₃ : F₀₁ ⋙ F₁₃ ≅ F₀₃)
    (α₀₂₃ : F₀₂ ⋙ F₂₃ ≅ F₀₃)
    (hp : (isoWhiskerRight α₀₁₂ F₂₃).symm ≪≫ associator F₀₁ F₁₂ F₂₃ ≪≫
        isoWhiskerLeft F₀₁ α₁₂₃ ≪≫ α₀₁₃ = α₀₂₃)
    (M : A₀) :
    α₁₂₃.hom.app (F₀₁.obj M) ≫ α₀₁₃.hom.app M =
      F₂₃.map (α₀₁₂.hom.app M) ≫ α₀₂₃.hom.app M := by
  have h := NatTrans.congr_app (congrArg Iso.hom hp) M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerRight_inv,
    Functor.whiskerRight_app, associator_hom_app, isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp] at h
  rw [← h, ← Functor.map_comp_assoc, α₀₁₂.hom_inv_id_app, Functor.map_id, Category.id_comp]

end CategoryTheory.Functor

end
