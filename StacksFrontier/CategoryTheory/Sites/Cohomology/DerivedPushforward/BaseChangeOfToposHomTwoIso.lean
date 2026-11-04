module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules
public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHom

/-!
# The derived base change map of a 2-commutative square of morphisms of ringed topoi

A diagram of ringed topoi commutes when its two composites are 2-isomorphic, not only when they
are equal. This file constructs the derived base change map for a square

```
                g'
  (Sh(C'), 𝒪_{C'}) --→ (Sh(C), 𝒪_C)
        |  f'                |  f
        v                    v
  (Sh(D'), 𝒪_{D'}) --→ (Sh(D), 𝒪_D)
                g
```

of morphisms of ringed topoi together with a 2-isomorphism `s : g ∘ f' ≅ f ∘ g'`, and shows that
it is the base change map of `Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedBaseChangeMap`
when `s` comes from an equality of the two composites.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.TwoIso.ofEq`: the 2-isomorphism of equal morphisms of
  ringed topoi.
* `derivedPullbackIsoOfTwoIso`: 2-isomorphic morphisms of ringed topoi have isomorphic derived
  pullbacks.
* `derivedPullbackCompIsoRightOfTwoIso`: `Lf^* ⋙ L(g')^*` identified with the derived pullback
  along `g ∘ f'`, through the 2-isomorphism of the square.
* `derivedBaseChangeSquareOfTwoIso`, `derivedBaseChangeMapOfTwoIso`: the base change morphism of
  functors `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*` and its component
  `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K`.

## Main results

* `derivedPullbackIsoOfTwoIso_refl`, `derivedPullbackIsoOfTwoIso_ofEq`: the derived pullback
  isomorphism of an identity 2-isomorphism is the identity, and that of an equality is
  `derivedPullbackCongr`.
* `derivedBaseChangeMapOfTwoIso_adjoint`, `derivedBaseChangeMapOfTwoIso_eq`,
  `derivedBaseChangeMapOfTwoIso_naturality`: the adjoint description, its transpose and
  naturality, as for a strictly commutative square.
* `derivedBaseChangeMapOfTwoIso_ofEq`: for the 2-isomorphism of an equality `g ∘ f' = f ∘ g'`
  the map is `derivedBaseChangeMap`.

## References

* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

namespace AlgebraicGeometry.RingedToposHom.TwoIso

universe v₁ u₁ w₁ v₂ u₂ w₂

variable {A : RingedTopos.{v₁, u₁, w₁}} {B : RingedTopos.{v₂, u₂, w₂}}
  [A.J.HasSheafCompose (forget RingCat.{w₁})]
  [B.J.HasSheafCompose (forget RingCat.{w₂})]
  [A.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w₂} RingCat.{w₂})]

/-- The 2-isomorphism between equal morphisms of ringed topoi: the identity, after substituting
the equality. -/
def ofEq {f g : RingedToposHom A B} (h : f = g) : TwoIso f g := by
  subst h
  exact refl f

/-- The 2-isomorphism of a reflexivity proof is the identity 2-isomorphism. -/
@[simp]
theorem ofEq_rfl (f : RingedToposHom A B) : ofEq (rfl : f = f) = refl f := rfl

/-- The inverse of the 2-isomorphism of an equality is the 2-isomorphism of the reversed
equality. -/
theorem symm_ofEq {f g : RingedToposHom A B} (h : f = g) : (ofEq h).symm = ofEq h.symm := by
  subst h
  rfl

variable [A.J.HasSheafCompose (forget AddCommGrpCat.{w₁})]
  [B.J.HasSheafCompose (forget AddCommGrpCat.{w₂})]

/-- The identity 2-isomorphism induces the identity of the direct images of sheaves of
modules. -/
@[simp]
theorem pushforwardModulesIso_refl (f : RingedToposHom A B) :
    (refl f).pushforwardModulesIso = Iso.refl (pushforwardModules f) := by
  refine Iso.ext (NatTrans.ext (funext fun F ↦ ?_))
  apply Stacks.Sheaves.RingedToposModules.hom_ext_moduleSheafFunctor
  rw [Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id]
  rfl

variable [HasWeakSheafify A.J AddCommGrpCat.{w₁}]
  [A.J.WEqualsLocallyBijective AddCommGrpCat.{w₁}]

/-- The identity 2-isomorphism induces the identity of the pullbacks of sheaves of modules. -/
@[simp]
theorem pullbackModulesIso_refl (f : RingedToposHom A B) :
    (refl f).pullbackModulesIso = Iso.refl f.toModulesHom.pullbackModules := by
  ext1
  rw [pullbackModulesIso, pushforwardModulesIso_refl]
  have : (pullbackAdjPushforwardModules f).ofNatIsoRight (Iso.refl _) =
      pullbackAdjPushforwardModules f := by
    ext M
    simp [Adjunction.ofNatIsoRight]
  rw [this, Adjunction.leftAdjointUniq_refl]
  rfl

end AlgebraicGeometry.RingedToposHom.TwoIso

namespace Stacks.Cohomology.DerivedBaseChangeOfToposHom

universe vC' uC' wC' vC uC wC vD' uD' wD' vD uD wD

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

noncomputable section

section TwoIsoCongr

variable {X' : RingedTopos.{vC', uC', wC'}} {Y : RingedTopos.{vD, uD, wD}}
  [X'.J.HasSheafCompose (forget RingCat.{wC'})] [Y.J.HasSheafCompose (forget RingCat.{wD})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [HasSheafify X'.J AddCommGrpCat.{wC'}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify Y.J AddCommGrpCat.{wD}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wD}]
  [HasSheafify X'.J (Type wC')] [HasSheafify Y.J (Type wD)]

/-- **2-isomorphic morphisms of ringed topoi have isomorphic derived pullbacks.** The isomorphism
is induced, on total left derived functors, by the isomorphism of the two pullbacks of sheaves of
modules (`AlgebraicGeometry.RingedToposHom.TwoIso.pullbackModulesIso`) carried to the homotopy
category and followed by localization. -/
def derivedPullbackIsoOfTwoIso {m₁ m₂ : RingedToposHom X' Y} (s : RingedToposHom.TwoIso m₁ m₂) :
    derivedPullback m₁ ≅ derivedPullback m₂ :=
  Functor.leftDerivedNatIso (derivedPullback m₁) (derivedPullback m₂)
    (derivedPullbackComparison m₁) (derivedPullbackComparison m₂) (quasiIsoTarget (Y := Y))
    (Functor.isoWhiskerRight
      (Stacks.Homology.mapHomotopyCategoryIso s.pullbackModulesIso (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- The derived pullback isomorphism of the identity 2-isomorphism is the identity. -/
@[simp]
theorem derivedPullbackIsoOfTwoIso_refl (m : RingedToposHom X' Y) :
    derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.refl m) = Iso.refl (derivedPullback m) := by
  have hτ : Functor.whiskerRight (NatTrans.mapHomotopyCategory
      (RingedToposHom.TwoIso.refl m).pullbackModulesIso.hom (ComplexShape.up ℤ))
      DerivedCategory.Qh = 𝟙 _ := by
    rw [RingedToposHom.TwoIso.pullbackModulesIso_refl, Iso.refl_hom,
      NatTrans.mapHomotopyCategory_id, Functor.whiskerRight_id']
  ext1
  exact (congrArg _ hτ).trans (Functor.leftDerivedNatTrans_id (derivedPullback m)
    (derivedPullbackComparison m) (quasiIsoTarget (Y := Y)))

/-- The derived pullback isomorphism of the 2-isomorphism of an equality of morphisms of ringed
topoi is `derivedPullbackCongr`. -/
theorem derivedPullbackIsoOfTwoIso_ofEq {m₁ m₂ : RingedToposHom X' Y} (h : m₁ = m₂) :
    derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.ofEq h) = derivedPullbackCongr h := by
  subst h
  exact derivedPullbackIsoOfTwoIso_refl m₁

end TwoIsoCongr

section Square

variable {X' : RingedTopos.{vC', uC', wC'}} {X : RingedTopos.{vC, uC, wC}}
  {Y' : RingedTopos.{vD', uD', wD'}} {Y : RingedTopos.{vD, uD, wD}}
  [X'.J.HasSheafCompose (forget RingCat.{wC'})] [X.J.HasSheafCompose (forget RingCat.{wC})]
  [Y'.J.HasSheafCompose (forget RingCat.{wD'})] [Y.J.HasSheafCompose (forget RingCat.{wD})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{wD'} RingCat.{wD'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [HasSheafify X'.J AddCommGrpCat.{wC'}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify X.J AddCommGrpCat.{wC}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify Y'.J AddCommGrpCat.{wD'}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{wD'}]
  [HasSheafify Y.J AddCommGrpCat.{wD}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wD}]
  [HasSheafify X'.J (Type wC')] [HasSheafify X.J (Type wC)]
  [HasSheafify Y'.J (Type wD')] [HasSheafify Y.J (Type wD)]
  [IsGrothendieckAbelian.{wC}
    (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))]
  [IsGrothendieckAbelian.{wC'}
    (SheafOfModules.{wC'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J)) X'.O))]
  (f : RingedToposHom X Y) (g' : RingedToposHom X' X)
  (f' : RingedToposHom X' Y') (g : RingedToposHom Y' Y)

/-- The iterated derived pullback `Lf^* ⋙ L(g')^*`, along the top and down the right of a
2-commutative square, identified with the derived pullback along `g ∘ f'`: the composition
isomorphism `derivedPullbackCompIso g' f` followed by the derived pullback isomorphism of the
inverse of the 2-isomorphism `s : g ∘ f' ≅ f ∘ g'`. -/
def derivedPullbackCompIsoRightOfTwoIso (s : RingedToposHom.TwoIso (g.comp f') (f.comp g')) :
    derivedPullback f ⋙ derivedPullback g' ≅ derivedPullback (g.comp f') :=
  derivedPullbackCompIso g' f ≪≫ derivedPullbackIsoOfTwoIso s.symm

omit [Y'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})] [HasSheafify Y'.J AddCommGrpCat.{wD'}]
  [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{wD'}] [HasSheafify Y'.J (Type wD')]
  [IsGrothendieckAbelian.{wC}
    (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))]
  [IsGrothendieckAbelian.{wC'}
    (SheafOfModules.{wC'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X'.J)) X'.O))] in
/-- For the 2-isomorphism of an equality of the two composites, the identification of
`Lf^* ⋙ L(g')^*` is the one of the strictly commutative square. -/
theorem derivedPullbackCompIsoRightOfTwoIso_ofEq (h : g.comp f' = f.comp g') :
    derivedPullbackCompIsoRightOfTwoIso f g' f' g (RingedToposHom.TwoIso.ofEq h) =
      derivedPullbackCompIsoRight f g' f' g h := by
  rw [derivedPullbackCompIsoRightOfTwoIso, RingedToposHom.TwoIso.symm_ofEq,
    derivedPullbackIsoOfTwoIso_ofEq]
  rfl

/-- **The derived base change morphism of functors** `Rf_* ⋙ Lg^* ⟶ L(g')^* ⋙ Rf'_*` attached
to a square of morphisms of ringed topoi commuting up to the 2-isomorphism
`s : g ∘ f' ≅ f ∘ g'`: the mate, under the derived adjunctions, of the comparison of the two
iterated derived pullbacks around the square. -/
def derivedBaseChangeSquareOfTwoIso (s : RingedToposHom.TwoIso (g.comp f') (f.comp g')) :
    TwoSquare (derivedPushforward f) (derivedPullback g') (derivedPullback g)
      (derivedPushforward f') :=
  Stacks.CategoryTheory.BaseChange.twoSquare (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIsoLeft f' g) (derivedPullbackCompIsoRightOfTwoIso f g' f' g s)

/-- **The base change map of a 2-commutative square.** For a square of morphisms of ringed topoi

```
                g'
  (Sh(C'), 𝒪_{C'}) --→ (Sh(C), 𝒪_C)
        |  f'                |  f
        v                    v
  (Sh(D'), 𝒪_{D'}) --→ (Sh(D), 𝒪_D)
                g
```

commuting up to a 2-isomorphism `s : g ∘ f' ≅ f ∘ g'`, and an object `K` of `D(𝒪_C)`, the canonical
base change map `Lg^* Rf_* K ⟶ Rf'_* L(g')^* K` in `D(𝒪_{D'})`.

It is adjoint under `L(f')^* ⊣ Rf'_*` to `L(g')^*` of the derived counit `Lf^* Rf_* K ⟶ K`,
after identifying the two iterated derived pullbacks with the derived pullback along `g ∘ f'` by
`derivedPullbackCompIso` and the 2-isomorphism (`derivedBaseChangeMapOfTwoIso_adjoint`). -/
def derivedBaseChangeMapOfTwoIso (s : RingedToposHom.TwoIso (g.comp f') (f.comp g'))
    (K : DerivedCategory
      (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) :
    (derivedPullback g).obj ((derivedPushforward f).obj K) ⟶
      (derivedPushforward f').obj ((derivedPullback g').obj K) :=
  Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIsoLeft f' g) (derivedPullbackCompIsoRightOfTwoIso f g' f' g s) K

/-- **The adjoint characterization** of the base change map of a 2-commutative square: under
`L(f')^* ⊣ Rf'_*` it is `L(g')^*` of the derived counit `Lf^* Rf_* K ⟶ K`, transported across
the two identifications of the iterated derived pullbacks with the derived pullback along
`g ∘ f'`. -/
@[simp]
theorem derivedBaseChangeMapOfTwoIso_adjoint
    (s : RingedToposHom.TwoIso (g.comp f') (f.comp g'))
    (K : DerivedCategory
      (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) :
    ((derivedAdjunction f').homEquiv
        ((derivedPullback g).obj ((derivedPushforward f).obj K))
        ((derivedPullback g').obj K)).symm
        (derivedBaseChangeMapOfTwoIso f g' f' g s K) =
      (derivedPullbackCompIsoLeft f' g).hom.app ((derivedPushforward f).obj K) ≫
        (derivedPullbackCompIsoRightOfTwoIso f g' f' g s).inv.app
          ((derivedPushforward f).obj K) ≫
        (derivedPullback g').map ((derivedAdjunction f).counit.app K) :=
  Stacks.CategoryTheory.BaseChange.homEquiv_symm_map (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIsoLeft f' g) (derivedPullbackCompIsoRightOfTwoIso f g' f' g s) K

/-- The base change map of a 2-commutative square as a transpose: it is the transpose, under
`L(f')^* ⊣ Rf'_*`, of the derived pullback along `g'` of the derived counit. -/
theorem derivedBaseChangeMapOfTwoIso_eq (s : RingedToposHom.TwoIso (g.comp f') (f.comp g'))
    (K : DerivedCategory
      (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) :
    derivedBaseChangeMapOfTwoIso f g' f' g s K =
      (derivedAdjunction f').homEquiv
        ((derivedPullback g).obj ((derivedPushforward f).obj K))
        ((derivedPullback g').obj K)
        ((derivedPullbackCompIsoLeft f' g).hom.app ((derivedPushforward f).obj K) ≫
          (derivedPullbackCompIsoRightOfTwoIso f g' f' g s).inv.app
            ((derivedPushforward f).obj K) ≫
          (derivedPullback g').map ((derivedAdjunction f).counit.app K)) :=
  Stacks.CategoryTheory.BaseChange.map_eq (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIsoLeft f' g) (derivedPullbackCompIsoRightOfTwoIso f g' f' g s) K

/-- The base change map of a 2-commutative square is natural in the object of `D(𝒪_C)`. -/
theorem derivedBaseChangeMapOfTwoIso_naturality
    (s : RingedToposHom.TwoIso (g.comp f') (f.comp g'))
    {K L : DerivedCategory
      (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))}
    (e : K ⟶ L) :
    (derivedPullback g).map ((derivedPushforward f).map e) ≫
        derivedBaseChangeMapOfTwoIso f g' f' g s L =
      derivedBaseChangeMapOfTwoIso f g' f' g s K ≫
        (derivedPushforward f').map ((derivedPullback g').map e) :=
  Stacks.CategoryTheory.BaseChange.map_naturality (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIsoLeft f' g) (derivedPullbackCompIsoRightOfTwoIso f g' f' g s) e

/-- **Agreement with the strictly commutative square.** For the 2-isomorphism of an equality
`g ∘ f' = f ∘ g'` of the two composites, the base change map of the 2-commutative square is the
base change map `derivedBaseChangeMap` of the commutative square. -/
theorem derivedBaseChangeMapOfTwoIso_ofEq (h : g.comp f' = f.comp g')
    (K : DerivedCategory
      (SheafOfModules.{wC} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) :
    derivedBaseChangeMapOfTwoIso f g' f' g (RingedToposHom.TwoIso.ofEq h) K =
      derivedBaseChangeMap f g' f' g h K := by
  rw [derivedBaseChangeMapOfTwoIso, derivedPullbackCompIsoRightOfTwoIso_ofEq]
  rfl

/-- The same agreement for the morphisms of functors. -/
theorem derivedBaseChangeSquareOfTwoIso_ofEq (h : g.comp f' = f.comp g') :
    derivedBaseChangeSquareOfTwoIso f g' f' g (RingedToposHom.TwoIso.ofEq h) =
      derivedBaseChangeSquare f g' f' g h := by
  rw [derivedBaseChangeSquareOfTwoIso, derivedPullbackCompIsoRightOfTwoIso_ofEq]
  rfl

end Square

end

end Stacks.Cohomology.DerivedBaseChangeOfToposHom

end
