module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LerayCoherenceSquare
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusNatIsoGlue

/-!
# Pasting two derived squares along a composition

`StacksFrontier/Algebra/Homology/DerivedCategory/LerayCoherenceSquare.lean` derives one square of
underived functors.  **This module pastes two of them.**  The data is a prism

* `a₁ : 𝒜 ⥤ ℬ`, `a₂ : ℬ ⥤ 𝒞`, `a₀ : 𝒜 ⥤ 𝒞` with `κ : a₀ ≅ a₁ ⋙ a₂`;
* `v₂ : 𝒜 ⥤ 𝒜'`, `v₁ : ℬ ⥤ ℬ'`, `v₀ : 𝒞 ⥤ 𝒞'`, the three vertical functors;
* `b₁ : 𝒜' ⥤ ℬ'`, `b₂ : ℬ' ⥤ 𝒞'`, `b₀ : 𝒜' ⥤ 𝒞'` with `π : b₁ ⋙ b₂ ≅ b₀`;
* commutations `s₁ : a₁ ⋙ v₁ ≅ v₂ ⋙ b₁`, `s₂ : a₂ ⋙ v₀ ≅ v₁ ⋙ b₂` and
  `s₀ : a₀ ⋙ v₀ ≅ v₂ ⋙ b₀` of the three squares,

together with the *underived* coherence saying that the commutation of the outer square is the
pasting of the commutations of the two inner ones.  The conclusion is the same statement for the
derived squares `Rs₁`, `Rs₂`, `Rs₀` obtained by transporting each commutation through two
instances of the comparison of [Stacks, Tag 015M], read through the composition isomorphisms
`Ra₀ ≅ Ra₁ ⋙ Ra₂` and `Rb₀ ≅ Rb₁ ⋙ Rb₂`.

This is the shape in which the composition functoriality of a derived comparison map is needed:
in [Stacks, Tag 07Q9] the `a`'s are the crystalline direct images of a composite cover, the
`v`'s are `u_{X/S, *}` and the `b`'s the Zariski direct images.

## Main results

* `Stacks.DerivedFunctor.derivedSquare_paste` — **the pasting**, as an identity of natural
  transformations.
* `Stacks.DerivedFunctor.derivedSquare_paste_app` — the same, read at an object and solved for
  the two composition isomorphisms, which is the form a comparison map consumes.

## The argument

`Stacks.DerivedFunctor.LeraySquare.derived_coherence` is applied to the *left* square `s₁` with
`q := a₂ ⋙ v₀`, `r := b₀`, `p := v₂ ⋙ b₀`, `eb := s₂.symm`, `ed := π`, `ec := Iso.refl` and
`ea := isoWhiskerRight κ.symm v₀ ≪≫ s₀`.  Its hypothesis is the underived coherence with the
commutation of the middle square moved across, and its conclusion is the identity sought, read
out of `R(v₂ ⋙ b₀)`.

Three structural properties of the invariance comparison turn that into the statement above —
it takes the identity to the identity, an inverse to the inverse and a composite to the
composite, which is `RightDerivedFunctorPlusNatIsoGlue.lean` — and two coherences move the
composition isomorphism of the `a`'s to the outside:
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_assoc` for the three-fold composite
`a₁ ⋙ a₂ ⋙ v₀`, and
`CategoryTheory.Functor.rightDerivedFunctorPlusComp_natIso_whiskerRight` for the passage from
`R((a₁ ⋙ a₂) ⋙ v₀)` to `R(a₀ ⋙ v₀)` along `κ`.

## Implementation notes

The five derived squares and the two composition isomorphisms are *arguments*, each with an
equation identifying it with the canonical composite.  A caller then supplies its own named
constructions together with `rfl`-level identifications, instead of having to rewrite its
statement into the canonical shape.

The associators are omitted, as in `LerayCoherenceSquare.lean`: `(F ⋙ G) ⋙ H` and
`F ⋙ (G ⋙ H)` are definitionally equal and `CategoryTheory.Functor.associator` is componentwise
the identity.

No `@[stacks]` attribute is placed: the source states none of this.

## References

* [Stacks, Tag 015M](https://stacks.math.columbia.edu/tag/015M), when the composition comparison
  is an isomorphism
* [Stacks, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2), the comparison transformation

Tags covered: none.
-/

@[expose] public noncomputable section

universe w₁ w₂ w₃ w₄ w₅ w₆ v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

open CategoryTheory CategoryTheory.Functor Limits

namespace Stacks.DerivedFunctor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- A commuting square of isomorphisms, read on the two inverse routes.  Both uses below rewrite
a commutation of composition comparisons into the form the computation consumes. -/
private lemma inv_comp_inv_of_comp {E : Type*} [Category* E] {P Q R S : E} (n : P ≅ Q)
    (A : Q ≅ S) (B : P ≅ R) (m : R ≅ S) (h : n.hom ≫ A.hom = B.hom ≫ m.hom) :
    m.inv ≫ B.inv = A.inv ≫ n.inv :=
  congrArg Iso.inv (Iso.ext h.symm : B ≪≫ m = n ≪≫ A)

/-- A commuting square with invertible vertical edges, solved for the two inverses. -/
private lemma solve_square {E : Type*} [Category* E] {W X Y Z : E} (α : W ≅ X) (f : X ⟶ Y)
    (g : W ⟶ Z) (β : Z ≅ Y) (h : α.hom ≫ f = g ≫ β.hom) : f ≫ β.inv = α.inv ≫ g := by
  rw [← cancel_epi α.hom, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

section Paste

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {A' : Type u₄} {B' : Type u₅} {C' : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Category.{v₄} A'] [Category.{v₅} B'] [Category.{v₆} C']
  [Abelian A] [Abelian B] [Abelian C] [Abelian A'] [Abelian B'] [Abelian C']
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B] [HasDerivedCategory.{w₃} C]
  [HasDerivedCategory.{w₄} A'] [HasDerivedCategory.{w₅} B'] [HasDerivedCategory.{w₆} C']
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] [EnoughInjectives A']
  [EnoughInjectives B']
  {a₁ : A ⥤ B} {a₂ : B ⥤ C} {a₀ : A ⥤ C}
  {v₂ : A ⥤ A'} {v₁ : B ⥤ B'} {v₀ : C ⥤ C'}
  {b₁ : A' ⥤ B'} {b₂ : B' ⥤ C'} {b₀ : A' ⥤ C'}
  [a₁.Additive] [a₂.Additive] [a₀.Additive] [v₂.Additive] [v₁.Additive] [v₀.Additive]
  [b₁.Additive] [b₂.Additive] [b₀.Additive]
  [a₁.PreservesInjectiveObjects] [a₂.PreservesInjectiveObjects] [a₀.PreservesInjectiveObjects]
  [v₂.PreservesInjectiveObjects] [v₁.PreservesInjectiveObjects]
  [b₁.PreservesInjectiveObjects]
  (κ : a₀ ≅ a₁ ⋙ a₂) (π : b₁ ⋙ b₂ ≅ b₀)
  (s₁ : a₁ ⋙ v₁ ≅ v₂ ⋙ b₁) (s₂ : a₂ ⋙ v₀ ≅ v₁ ⋙ b₂) (s₀ : a₀ ⋙ v₀ ≅ v₂ ⋙ b₀)

/-- The three-fold composition comparison, in the form the pasting consumes: the comparison for
`a₂ ⋙ v₀` inverted after the one for `a₁` against `a₂ ⋙ v₀` is the comparison for `a₁ ⋙ a₂`
inverted after the one for `a₁ ⋙ a₂` against `v₀`.  This is
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso_assoc` with two edges inverted. -/
private lemma paste_assoc :
    Functor.whiskerRight (rightDerivedFunctorPlusCompIso a₁ a₂).hom
          v₀.rightDerivedFunctorPlus ≫
        Functor.whiskerLeft a₁.rightDerivedFunctorPlus
          (rightDerivedFunctorPlusCompIso a₂ v₀).inv =
      (rightDerivedFunctorPlusCompIso (a₁ ⋙ a₂) v₀).inv ≫
        (rightDerivedFunctorPlusCompIso a₁ (a₂ ⋙ v₀)).hom :=
  solve_square (rightDerivedFunctorPlusCompIso (a₁ ⋙ a₂) v₀)
    (Functor.whiskerRight (rightDerivedFunctorPlusCompIso a₁ a₂).hom v₀.rightDerivedFunctorPlus)
    (rightDerivedFunctorPlusCompIso a₁ (a₂ ⋙ v₀)).hom
    (Functor.isoWhiskerLeft a₁.rightDerivedFunctorPlus
      (rightDerivedFunctorPlusCompIso a₂ v₀))
    (rightDerivedFunctorPlusCompIso_assoc a₁ a₂ v₀)

omit [HasDerivedCategory B] [EnoughInjectives B] in
/-- The passage from `R((a₁ ⋙ a₂) ⋙ v₀)` to `R(a₀ ⋙ v₀)` along `κ`, in the form the pasting
consumes.  This is
`CategoryTheory.Functor.rightDerivedFunctorPlusComp_natIso_whiskerRight` with two edges
inverted. -/
private lemma paste_kappa :
    Functor.whiskerRight (rightDerivedFunctorPlusNatIso κ).hom v₀.rightDerivedFunctorPlus ≫
        (rightDerivedFunctorPlusCompIso (a₁ ⋙ a₂) v₀).inv =
      (rightDerivedFunctorPlusCompIso a₀ v₀).inv ≫
        (rightDerivedFunctorPlusNatIso (Functor.isoWhiskerRight κ.symm v₀)).inv := by
  have h := inv_comp_inv_of_comp
    (rightDerivedFunctorPlusNatIso (Functor.isoWhiskerRight κ.symm v₀))
    (rightDerivedFunctorPlusCompIso a₀ v₀)
    (rightDerivedFunctorPlusCompIso (a₁ ⋙ a₂) v₀)
    (Functor.isoWhiskerRight (rightDerivedFunctorPlusNatIso κ.symm)
      v₀.rightDerivedFunctorPlus)
    (by
      rw [rightDerivedFunctorPlusCompIso_hom, rightDerivedFunctorPlusCompIso_hom]
      exact rightDerivedFunctorPlusComp_natIso_whiskerRight κ.symm v₀)
  rw [Functor.isoWhiskerRight_inv, rightDerivedFunctorPlusNatIso_symm, Iso.symm_inv] at h
  exact h

/-- **The pasting of two derived squares.**  Given the underived coherence `hund` — the
commutation of the middle square, then `b₂` of the commutation of the left square, then the
composition isomorphism of the `b`'s, is the composition isomorphism of the `a`'s inverted
followed by the commutation of the outer square — the same holds for the derived squares.

The five isomorphisms are arguments with their defining equations, so that a caller may supply
its own named constructions. -/
theorem derivedSquare_paste
    (d₁ : a₁.rightDerivedFunctorPlus ⋙ v₁.rightDerivedFunctorPlus ≅
      v₂.rightDerivedFunctorPlus ⋙ b₁.rightDerivedFunctorPlus)
    (d₂ : a₂.rightDerivedFunctorPlus ⋙ v₀.rightDerivedFunctorPlus ≅
      v₁.rightDerivedFunctorPlus ⋙ b₂.rightDerivedFunctorPlus)
    (d₀ : a₀.rightDerivedFunctorPlus ⋙ v₀.rightDerivedFunctorPlus ≅
      v₂.rightDerivedFunctorPlus ⋙ b₀.rightDerivedFunctorPlus)
    (γ : a₀.rightDerivedFunctorPlus ≅
      a₁.rightDerivedFunctorPlus ⋙ a₂.rightDerivedFunctorPlus)
    (θ : b₀.rightDerivedFunctorPlus ≅
      b₁.rightDerivedFunctorPlus ⋙ b₂.rightDerivedFunctorPlus)
    (hd₁ : d₁ = (rightDerivedFunctorPlusCompIso a₁ v₁).symm ≪≫
      rightDerivedFunctorPlusNatIso s₁ ≪≫ rightDerivedFunctorPlusCompIso v₂ b₁)
    (hd₂ : d₂ = (rightDerivedFunctorPlusCompIso a₂ v₀).symm ≪≫
      rightDerivedFunctorPlusNatIso s₂ ≪≫ rightDerivedFunctorPlusCompIso v₁ b₂)
    (hd₀ : d₀ = (rightDerivedFunctorPlusCompIso a₀ v₀).symm ≪≫
      rightDerivedFunctorPlusNatIso s₀ ≪≫ rightDerivedFunctorPlusCompIso v₂ b₀)
    (hγ : γ = rightDerivedFunctorPlusNatIso κ ≪≫ rightDerivedFunctorPlusCompIso a₁ a₂)
    (hθ : θ = (rightDerivedFunctorPlusNatIso π).symm ≪≫
      rightDerivedFunctorPlusCompIso b₁ b₂)
    (hund : ∀ X : A,
      s₂.hom.app (a₁.obj X) ≫ b₂.map (s₁.hom.app X) ≫ π.hom.app (v₂.obj X) =
        v₀.map (κ.inv.app X) ≫ s₀.hom.app X) :
    Functor.whiskerRight γ.hom v₀.rightDerivedFunctorPlus ≫
        Functor.whiskerLeft a₁.rightDerivedFunctorPlus d₂.hom ≫
        Functor.whiskerRight d₁.hom b₂.rightDerivedFunctorPlus =
      d₀.hom ≫ Functor.whiskerLeft v₂.rightDerivedFunctorPlus θ.hom := by
  subst hd₁ hd₂ hd₀ hγ hθ
  have hleray : ∀ X : A, s₂.symm.hom.app (a₁.obj X) ≫
      ((Functor.isoWhiskerRight κ.symm v₀ ≪≫ s₀ :
        a₁ ⋙ (a₂ ⋙ v₀) ≅ v₂ ⋙ b₀)).hom.app X =
      b₂.map (s₁.hom.app X) ≫ π.hom.app (v₂.obj X) ≫
        (Iso.refl (v₂ ⋙ b₀)).hom.app X := by
    intro X
    have h : s₂.inv.app (a₁.obj X) ≫ v₀.map (κ.inv.app X) ≫ s₀.hom.app X =
        b₂.map (s₁.hom.app X) ≫ π.hom.app (v₂.obj X) := by
      rw [← hund X, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    simpa using h
  have hcoh := Stacks.DerivedFunctor.LeraySquare.derived_coherence s₁
    ((Functor.isoWhiskerRight κ.symm v₀ ≪≫ s₀ :
      a₁ ⋙ (a₂ ⋙ v₀) ≅ v₂ ⋙ b₀)) s₂.symm (Iso.refl (v₂ ⋙ b₀)) π hleray
  simp only [Stacks.DerivedFunctor.LeraySquare.derivedLeft,
    Stacks.DerivedFunctor.LeraySquare.derivedLeftTail,
    Stacks.DerivedFunctor.LeraySquare.derivedSquare,
    Stacks.DerivedFunctor.LeraySquare.derivedRight,
    Stacks.DerivedFunctor.LeraySquare.derivedRightTail,
    rightDerivedFunctorPlusNatIso_refl, rightDerivedFunctorPlusNatIso_symm,
    rightDerivedFunctorPlusNatIso_trans, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_symm_eq, Iso.refl_symm, Iso.refl_hom, Functor.whiskerLeft_comp,
    Functor.whiskerRight_comp, Category.assoc, Category.id_comp] at hcoh
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.whiskerLeft_comp,
    Functor.whiskerRight_comp, Category.assoc]
  rw [← Category.assoc
      (Functor.whiskerRight (rightDerivedFunctorPlusCompIso a₁ a₂).hom
        v₀.rightDerivedFunctorPlus)
      (Functor.whiskerLeft a₁.rightDerivedFunctorPlus
        (rightDerivedFunctorPlusCompIso a₂ v₀).inv),
    paste_assoc]
  simp only [Category.assoc]
  rw [← Category.assoc
      (Functor.whiskerRight (rightDerivedFunctorPlusNatIso κ).hom
        v₀.rightDerivedFunctorPlus)
      (rightDerivedFunctorPlusCompIso (a₁ ⋙ a₂) v₀).inv,
    paste_kappa]
  simp only [Category.assoc]
  refine CategoryTheory.whisker_eq _ ?_
  rw [← hcoh, ← Category.assoc (rightDerivedFunctorPlusNatIso s₀).hom
      (rightDerivedFunctorPlusNatIso s₀).inv,
    Iso.hom_inv_id, Category.id_comp]

/-- **The pasting of two derived squares, read at an object and solved for the two composition
isomorphisms.**  This is the form a comparison map consumes: the derived commutation of the
middle square, then `Rb₂` of the derived commutation of the left square, then the composition
isomorphism of the `b`'s inverted, is the composition isomorphism of the `a`'s inverted followed
by the derived commutation of the outer square. -/
theorem derivedSquare_paste_app
    (d₁ : a₁.rightDerivedFunctorPlus ⋙ v₁.rightDerivedFunctorPlus ≅
      v₂.rightDerivedFunctorPlus ⋙ b₁.rightDerivedFunctorPlus)
    (d₂ : a₂.rightDerivedFunctorPlus ⋙ v₀.rightDerivedFunctorPlus ≅
      v₁.rightDerivedFunctorPlus ⋙ b₂.rightDerivedFunctorPlus)
    (d₀ : a₀.rightDerivedFunctorPlus ⋙ v₀.rightDerivedFunctorPlus ≅
      v₂.rightDerivedFunctorPlus ⋙ b₀.rightDerivedFunctorPlus)
    (γ : a₀.rightDerivedFunctorPlus ≅
      a₁.rightDerivedFunctorPlus ⋙ a₂.rightDerivedFunctorPlus)
    (θ : b₀.rightDerivedFunctorPlus ≅
      b₁.rightDerivedFunctorPlus ⋙ b₂.rightDerivedFunctorPlus)
    (hd₁ : d₁ = (rightDerivedFunctorPlusCompIso a₁ v₁).symm ≪≫
      rightDerivedFunctorPlusNatIso s₁ ≪≫ rightDerivedFunctorPlusCompIso v₂ b₁)
    (hd₂ : d₂ = (rightDerivedFunctorPlusCompIso a₂ v₀).symm ≪≫
      rightDerivedFunctorPlusNatIso s₂ ≪≫ rightDerivedFunctorPlusCompIso v₁ b₂)
    (hd₀ : d₀ = (rightDerivedFunctorPlusCompIso a₀ v₀).symm ≪≫
      rightDerivedFunctorPlusNatIso s₀ ≪≫ rightDerivedFunctorPlusCompIso v₂ b₀)
    (hγ : γ = rightDerivedFunctorPlusNatIso κ ≪≫ rightDerivedFunctorPlusCompIso a₁ a₂)
    (hθ : θ = (rightDerivedFunctorPlusNatIso π).symm ≪≫
      rightDerivedFunctorPlusCompIso b₁ b₂)
    (hund : ∀ X : A,
      s₂.hom.app (a₁.obj X) ≫ b₂.map (s₁.hom.app X) ≫ π.hom.app (v₂.obj X) =
        v₀.map (κ.inv.app X) ≫ s₀.hom.app X)
    (K : DerivedCategory.Plus A) :
    d₂.hom.app (a₁.rightDerivedFunctorPlus.obj K) ≫
        b₂.rightDerivedFunctorPlus.map (d₁.hom.app K) ≫
        θ.inv.app (v₂.rightDerivedFunctorPlus.obj K) =
      v₀.rightDerivedFunctorPlus.map (γ.inv.app K) ≫ d₀.hom.app K :=
  (Category.assoc _ _ _).symm.trans
    (solve_square (v₀.rightDerivedFunctorPlus.mapIso (γ.app K)) _ _
      (θ.app (v₂.rightDerivedFunctorPlus.obj K))
      (NatTrans.congr_app
        (derivedSquare_paste κ π s₁ s₂ s₀ d₁ d₂ d₀ γ θ hd₁ hd₂ hd₀ hγ hθ hund) K))

end Paste

end Stacks.DerivedFunctor

end
