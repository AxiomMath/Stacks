module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Equivalences of categories over a base

A functor over `𝒞` preserving cartesian morphisms, a natural transformation whose components are
vertical, and an equivalence in the 2-category of categories fibred over `𝒞`.

`IsCartesianFunctorStrict` is superseded by `CategoryTheory.Functor.IsFibredOneMorphism` in
`StacksFrontier.CategoryTheory.FibredOneMorphism`, which asks for preservation of *strongly*
cartesian morphisms — the condition Stacks 4.33.9 (2) actually states. These declarations are
retained only because
`StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.FibreFunctors` still consumes
them; they should be deleted, and that file routed to `IsFibredOneMorphism`, when Tag02Y8 is
rewritten.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/-- A functor `F : 𝒮 ⥤ 𝒮'` between categories fibred over `𝒞` which strictly commutes over `𝒞`
and preserves cartesian morphisms. -/
@[sga "1 VI 5.2"]
structure IsCartesianFunctorStrict {𝒞 : Type*} [Category 𝒞]
    {𝒮 : Type*} [Category 𝒮] (p : 𝒮 ⥤ 𝒞)
    {𝒮' : Type*} [Category 𝒮'] (q : 𝒮' ⥤ 𝒞)
    (F : 𝒮 ⥤ 𝒮') : Prop where
  /-- `F` is a morphism *over* `𝒞`: structure functors commute strictly. -/
  comm : F ⋙ q = p
  /-- `F` preserves cartesian morphisms. -/
  map_isCartesian : ∀ {R S : 𝒞} {a b : 𝒮} (f : R ⟶ S) (φ : a ⟶ b)
    [p.IsHomLift f φ] [p.IsCartesian f φ],
    q.IsCartesian f (F.map φ)

/-- A natural transformation `η : F₁ ⟶ F₂` between functors `𝒮 ⥤ 𝒮'` over `𝒞` is a *2-morphism
over `𝒞`* when each component lies over an identity of the base. -/
@[sga "4 VI 6.0"]
def NatTrans.IsOver {𝒞 : Type*} [Category 𝒞]
    {𝒮 : Type*} [Category 𝒮]
    {𝒮' : Type*} [Category 𝒮'] (q : 𝒮' ⥤ 𝒞)
    {F₁ F₂ : 𝒮 ⥤ 𝒮'} (η : F₁ ⟶ F₂) : Prop :=
  ∀ X : 𝒮, ∃ h : q.obj (F₁.obj X) = q.obj (F₂.obj X),
    q.map (η.app X) = eqToHom h

/-- The inverse of a 2-isomorphism over `𝒞` is again a 2-morphism over `𝒞`: its image under the
structure functor is inverse to an `eqToHom`, hence is the opposite `eqToHom`. -/
theorem NatTrans.IsOver.inv {𝒞 : Type*} [Category 𝒞]
    {𝒮 : Type*} [Category 𝒮] {𝒮' : Type*} [Category 𝒮'] (q : 𝒮' ⥤ 𝒞)
    {F₁ F₂ : 𝒮 ⥤ 𝒮'} (η : F₁ ≅ F₂) (hη : NatTrans.IsOver q η.hom) :
    NatTrans.IsOver q η.inv := by
  intro X
  obtain ⟨h, he⟩ := hη X
  refine ⟨h.symm, ?_⟩
  have h2 : q.map (η.inv.app X) ≫ q.map (η.hom.app X) = 𝟙 _ := by
    rw [← Functor.map_comp]; simp
  rw [he] at h2
  rw [← Category.id_comp (eqToHom h.symm), ← h2, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- `F : 𝒮 ⥤ 𝒮'` is an equivalence in the 2-category of categories fibred over `𝒞`: a cartesian
functor over `𝒞` admitting a quasi-inverse cartesian functor whose unit and counit isomorphisms are
2-morphisms over `𝒞`. -/
structure IsFibredEquivalence {𝒞 : Type*} [Category 𝒞]
    {𝒮 : Type*} [Category 𝒮] (p : 𝒮 ⥤ 𝒞)
    {𝒮' : Type*} [Category 𝒮'] (q : 𝒮' ⥤ 𝒞)
    (F : 𝒮 ⥤ 𝒮') : Prop where
  /-- `F` is a cartesian functor over `𝒞`. -/
  isCartesianFunctor : IsCartesianFunctorStrict p q F
  /-- A quasi-inverse cartesian functor `G : 𝒮' ⥤ 𝒮` over `𝒞`, with `G ⋙ F ≅ 𝟭 𝒮'` and
  `F ⋙ G ≅ 𝟭 𝒮` both 2-morphisms over `𝒞`. -/
  exists_inverse :
    ∃ (G : 𝒮' ⥤ 𝒮), IsCartesianFunctorStrict q p G ∧
      (∃ η : G ⋙ F ≅ 𝟭 𝒮', NatTrans.IsOver q η.hom) ∧
      (∃ ε : F ⋙ G ≅ 𝟭 𝒮, NatTrans.IsOver p ε.hom)

end CategoryTheory
