module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The mate of an isomorphism of left adjoints

Let `L ⊣ R` be an adjunction between `A` and `B`, and let `T_A ⊣ H_A` and `T_B ⊣ H_B` be
adjunctions of endofunctors of `A` and of `B`.  An isomorphism `T_A ⋙ L ≅ L ⋙ T_B` of left
adjoints is carried by the mate correspondence to an isomorphism `H_B ⋙ R ≅ R ⋙ H_A` of the
right adjoints.  That is the content of this file, and it is the formal half of the
pushforward–internal-Hom identification: with `T` the tensor product by a module and `H` the
internal Hom out of it, the isomorphism of left adjoints is the comparison of Stacks 03EL and the
isomorphism of right adjoints is `f_* 𝓗om(f^*𝓕, -) ≅ 𝓗om(𝓕, f_* -)`.

The proof is the uniqueness of right adjoints: the two composites of adjunctions
`T_A ⋙ L ⊣ H_B ⋙ R` and `T_A ⋙ L ⊣ R ⋙ H_A` have the same left adjoint — the first after
transporting along the given isomorphism — so their right adjoints agree.

The isomorphism of left adjoints that the consumers have is an isomorphism of *bifunctors* —
Stacks 03EL compares the tensor product of a pair with the tensor product of the pair of images —
and what the mate correspondence consumes is its restriction to one variable.  The second half of
this file performs that restriction, for an arbitrary bifunctor and with the naturality coming
for free: `CategoryTheory.Functor.tensorRightOfBifunctor` is the bifunctor with its second
argument fixed, written as a composite with `CategoryTheory.Functor.prod'`, so that the
restriction of the comparison is a whiskering.

## Main definitions

* `CategoryTheory.Functor.tensorRightOfBifunctor`: a bifunctor with its second argument fixed.

## Main results

* `CategoryTheory.Adjunction.rightAdjointSquareIso`: the mate of an isomorphism of left
  adjoints.
* `CategoryTheory.Functor.prodConstIso`: fixing the second argument commutes with applying a
  functor in both arguments.
* `CategoryTheory.Functor.tensorRightOfBifunctorIso`: an isomorphism of bifunctors restricts to
  an isomorphism of their second-argument-fixed forms.
* `CategoryTheory.Functor.tensorRightOfBifunctorUncurryIso`: fixing the second argument of an
  uncurried bifunctor is flipping the curried one and evaluating.
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- **The mate of an isomorphism of left adjoints is an isomorphism of right adjoints.**  Given
an adjunction `L ⊣ R`, adjunctions `T_A ⊣ H_A` and `T_B ⊣ H_B` of endofunctors, and an
isomorphism `T_A ⋙ L ≅ L ⋙ T_B`, the right adjoints satisfy `H_B ⋙ R ≅ R ⋙ H_A`. -/
def rightAdjointSquareIso {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
    {TA HA : A ⥤ A} (adjA : TA ⊣ HA) {TB HB : B ⥤ B} (adjB : TB ⊣ HB)
    (e : TA ⋙ L ≅ L ⋙ TB) : HB ⋙ R ≅ R ⋙ HA :=
  rightAdjointUniq ((adj.comp adjB).ofNatIsoLeft e.symm) (adjA.comp adj)

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- **A bifunctor with its second argument fixed.**  Written as the composite with
`CategoryTheory.Functor.prod'` of the identity and a constant functor, so that a natural
transformation of bifunctors restricts to one of these by whiskering. -/
def tensorRightOfBifunctor (T : A × A ⥤ A) (M : A) : A ⥤ A :=
  Functor.prod' (𝟭 A) ((Functor.const A).obj M) ⋙ T

/-- **Fixing the second argument of a bifunctor commutes with applying a functor in both
arguments.**  On objects both sides are `(L P, L M)`; on morphisms the left-hand side has
`L.map (𝟙 M)` where the right-hand side has `𝟙 (L.obj M)`, and the functor law identifies them. -/
def prodConstIso (L : A ⥤ B) (M : A) :
    Functor.prod' (𝟭 A) ((Functor.const A).obj M) ⋙ Functor.prod L L ≅
      L ⋙ Functor.prod' (𝟭 B) ((Functor.const B).obj (L.obj M)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {P P'} f => by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    exact congrArg (fun z => ((L.map f, z) : ((L.obj P, L.obj M) : B × B) ⟶ (L.obj P', L.obj M)))
      (L.map_id M))

/-- **An isomorphism of bifunctors restricts to an isomorphism of their second-argument-fixed
forms**, with its naturality.  The restriction is a whiskering of the given isomorphism on one
side and of `CategoryTheory.Functor.prodConstIso` on the other. -/
def tensorRightOfBifunctorIso {T : A × A ⥤ A} {T' : B × B ⥤ B} (L : A ⥤ B)
    (e : T ⋙ L ≅ Functor.prod L L ⋙ T') (M : A) :
    tensorRightOfBifunctor T M ⋙ L ≅ L ⋙ tensorRightOfBifunctor T' (L.obj M) :=
  Functor.isoWhiskerLeft (Functor.prod' (𝟭 A) ((Functor.const A).obj M)) e ≪≫
    Functor.isoWhiskerRight (prodConstIso L M) T'

/-- **Fixing the second argument of an uncurried bifunctor is flipping it.**  For a curried
bifunctor `T`, `Functor.uncurry.obj T` with its second argument fixed at `M` is `T.flip.obj M`.
On objects the two agree on the nose; on a morphism `f` the left-hand side is
`(T.map f).app M ≫ (T.obj _).map (𝟙 M)`, and the functor law removes the second factor. -/
def tensorRightOfBifunctorUncurryIso (T : A ⥤ A ⥤ A) (M : A) :
    tensorRightOfBifunctor (CategoryTheory.Functor.uncurry.obj T) M ≅ T.flip.obj M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => (Category.comp_id _).trans (Eq.trans
    ((congrArg (fun z => _ ≫ z) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _))
    (Category.id_comp _).symm))

end CategoryTheory.Functor

end
