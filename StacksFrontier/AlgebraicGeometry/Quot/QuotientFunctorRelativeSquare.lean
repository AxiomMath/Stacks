module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorThickening
public import StacksFrontier.Deformation.ToposThickening.RelativeBaseSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.Deformation.ToposThickening.RelativeBaseLeftFlatness

/-!
# The square of Situation 08M7 attached to a first order thickening of test schemes

In Situation 082M let `h : T ⟶ T'` be a first order thickening of schemes over `Y`. Remark 0CZU
works with the commutative square

```
  X_T  --i-->  X_{T'}
   |p            |f'
   v             v
   T   --t-->   T'
```

of algebraic spaces and the induced square of small étale ringed topoi (Stacks 03G8). The
morphisms of small étale ringed topoi are only pseudo-functorial, so the square of ringed topoi
commutes only up to the comparison isomorphisms of Stacks 03G8. This file records the comparison
`θ : f'_*i_*𝒪_{X_T} ≅ t_*p_*𝒪_{X_T}` of the two direct images of the structure sheaf, checks
that it is compatible with the structure maps, and so obtains the square of
`Deformation.ToposThickening.relBase_comm`, which commutes on the nose, with the base read on
the small étale topos of `X_{T'}`.

## Main definitions

* `AlgebraicGeometry.Space.squareRingNatIso`: the comparison `b_* ∘ a_* ≅ b'_* ∘ a'_*` of the
  direct images of sheaves of commutative rings along the two sides of a commutative square, and
  `AlgebraicGeometry.Space.squareRingIso`, its component at the structure sheaf.
* `AlgebraicGeometry.Space.QuotientSituation.relativeSquareIso`: the comparison `θ`.
* `AlgebraicGeometry.Space.QuotientSituation.relativeSquareLeft`: the morphism
  `f̃ : X_T ⟶ (X_{T'}, f'⁻¹t_*𝒪_T)`.
* `AlgebraicGeometry.Space.QuotientSituation.relativeSquareThickening`: the first order
  thickening `t̃ : (X_{T'}, f'⁻¹t_*𝒪_T) ⟶ (X_{T'}, f'⁻¹𝒪_{T'})`.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.relativeSquareIso_compat`: `θ` is compatible with the
  structure maps of `f' ∘ i` and `t ∘ p`.
* `AlgebraicGeometry.Space.QuotientSituation.relativeSquare_comm`: `f̃' ∘ i = t̃ ∘ f̃`.

## References

* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardCommRingCompIso
  pushforwardCommRingCompNatIso)
open Deformation.ToposThickening

universe u

/-- The component of a composite of natural isomorphisms through an equality of functors. -/
theorem CategoryTheory.Iso.trans_eqToIso_trans_hom_app {C D : Type*} [Category C] [Category D]
    {F₁ F₂ F₃ F₄ F₅ F₆ : C ⥤ D} (α : F₁ ≅ F₂) (β : F₂ ≅ F₃) (hF : F₃ = F₄) (γ : F₄ ≅ F₅)
    (δ : F₅ ≅ F₆) (O : C) :
    (α ≪≫ β ≪≫ eqToIso hF ≪≫ γ ≪≫ δ).hom.app O =
      α.hom.app O ≫ β.hom.app O ≫ eqToHom (Functor.congr_obj hF O) ≫ γ.hom.app O ≫
        δ.hom.app O := by
  subst hF
  simp

namespace AlgebraicGeometry.Space

section SquareRingIso

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X₁ X₂ X₂' X : AlgebraicSpaces B S hS} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X) (a' : X₁ ⟶ X₂')
  (b' : X₂' ⟶ X) (hab : a ≫ b = a' ≫ b')

/-- **The comparison `b_* ∘ a_* ≅ b'_* ∘ a'_*` of a commutative square of algebraic spaces**, on
sheaves of commutative rings, through the comparisons of Stacks 03G8 for `a ≫ b` and `a' ≫ b'`,
which agree. -/
def squareRingNatIso :
    pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS a).toToposHom ⋙
      pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS b).toToposHom ≅
    pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS a').toToposHom ⋙
      pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS b').toToposHom :=
  pushforwardCommRingCompNatIso (smallEtaleRingedToposHom B S hS a).toToposHom
      (smallEtaleRingedToposHom B S hS b).toToposHom ≪≫
    smallEtaleRingedToposHom_compRingIso B S hS a b ≪≫
    eqToIso (congrArg (fun r : X₁ ⟶ X => pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallEtaleRingedToposHom B S hS r).toToposHom) hab) ≪≫
    (smallEtaleRingedToposHom_compRingIso B S hS a' b').symm ≪≫
    (pushforwardCommRingCompNatIso (smallEtaleRingedToposHom B S hS a').toToposHom
      (smallEtaleRingedToposHom B S hS b').toToposHom).symm

/-- **The comparison `b_*a_*𝒪 ≅ b'_*a'_*𝒪` of a commutative square of algebraic spaces**: the
component of `AlgebraicGeometry.Space.squareRingNatIso` at the structure sheaf of `X₁`. -/
abbrev squareRingIso :
    (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS b).toToposHom).obj
      ((pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS a).toToposHom).obj (smallEtaleRingedTopos B S hS X₁).O) ≅
    (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS b').toToposHom).obj
      ((pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
        (smallEtaleRingedToposHom B S hS a').toToposHom).obj (smallEtaleRingedTopos B S hS X₁).O) :=
  (squareRingNatIso B S hS a b a' b' hab).app (smallEtaleRingedTopos B S hS X₁).O

/-- The comparison of a commutative square, as the composite of the comparisons of Stacks 03G8. -/
theorem squareRingIso_hom :
    (squareRingIso B S hS a b a' b' hab).hom =
      (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
        (smallEtaleRingedToposHom B S hS b).toToposHom (smallEtaleRingedTopos B S hS X₁).O).hom ≫
      (smallEtaleRingedToposHom_compRingIso B S hS a b).hom.app
        (smallEtaleRingedTopos B S hS X₁).O ≫
      eqToHom (congrArg (fun r : X₁ ⟶ X =>
        (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS r).toToposHom).obj (smallEtaleRingedTopos B S hS X₁).O)
            hab) ≫
      (smallEtaleRingedToposHom_compRingIso B S hS a' b').inv.app
        (smallEtaleRingedTopos B S hS X₁).O ≫
      (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a').toToposHom
        (smallEtaleRingedToposHom B S hS b').toToposHom (smallEtaleRingedTopos B S hS X₁).O).inv :=
  CategoryTheory.Iso.trans_eqToIso_trans_hom_app _ _ _ _ _ _

/-- **The comparison of a commutative square is compatible with the structure maps** of the two
composites (Stacks 03G8, compatibility with composition, for both of them). -/
theorem fSharp_comp_squareRingIso :
    (smallEtaleRingedToposHom B S hS b).fSharp ≫
        (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS b).toToposHom).map
            (smallEtaleRingedToposHom B S hS a).fSharp ≫
        (squareRingIso B S hS a b a' b' hab).hom =
      (smallEtaleRingedToposHom B S hS b').fSharp ≫
        (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS b').toToposHom).map
            (smallEtaleRingedToposHom B S hS a').fSharp := by
  rw [squareRingIso_hom]
  exact (fSharp_comp_compRingIso B S hS a b _).trans
    ((pushforwardCommRingFunctor_fSharp_comp_eqToHom_comp B S hS hab _).trans
      (fSharp_comp_compRingIso_inv B S hS a' b'))

end SquareRingIso

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.QuotientSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotientSituation B S hS) {T T' : SchemesOver D.Y} (h : T ⟶ T')

/-- The square of base changes commutes: `X_T ⟶ X_{T'} ⟶ T'` is `X_T ⟶ T ⟶ T'`. -/
theorem relativeMap_comp_projection :
    D.relativeMap h ≫ D.projection T' = D.projection T ≫ (schemeSpaceFunctor B S hS).map h.left :=
  baseChangeMap_comp_inclusion D.f h

/-- **The comparison `θ : f'_*i_*𝒪_{X_T} ≅ t_*p_*𝒪_{X_T}`** of the two direct images of the
structure sheaf of `X_T` to `T'`, through the comparisons of Stacks 03G8 for the two composites
`X_T ⟶ X_{T'} ⟶ T'` and `X_T ⟶ T ⟶ T'`, which agree. -/
abbrev relativeSquareIso :=
  squareRingIso B S hS (D.relativeMap h) (D.projection T') (D.projection T)
    ((schemeSpaceFunctor B S hS).map h.left) (D.relativeMap_comp_projection h)

/-- **`θ` is compatible with the structure maps** of `f' ∘ i` and `t ∘ p`. -/
theorem relativeSquareIso_compat :
    (smallEtaleRingedToposHom B S hS (D.projection T')).fSharp ≫
        (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS (D.projection T')).toToposHom).map
            (smallEtaleRingedToposHom B S hS (D.relativeMap h)).fSharp ≫
        (D.relativeSquareIso h).hom =
      (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left)).fSharp ≫
        (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left)).toToposHom).map
            (smallEtaleRingedToposHom B S hS (D.projection T)).fSharp :=
  fSharp_comp_squareRingIso B S hS (D.relativeMap h) (D.projection T') (D.projection T)
    ((schemeSpaceFunctor B S hS).map h.left) (D.relativeMap_comp_projection h)

/-- **The morphism `f̃ : X_T ⟶ (X_{T'}, f'⁻¹t_*𝒪_T)`** of the relative square: the morphism of
topoi of `X_T ⟶ X_{T'}`, with the structure map of `X_T ⟶ T` transported along `θ`. -/
abbrev relativeSquareLeft :=
  relBaseLeft (smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
    (smallEtaleRingedToposHom B S hS (D.projection T'))
    (smallEtaleRingedToposHom B S hS (D.projection T)) (D.relativeSquareIso h)

/-- **The thickening `t̃ : (X_{T'}, f'⁻¹t_*𝒪_T) ⟶ (X_{T'}, f'⁻¹𝒪_{T'})`** of the relative
square, the inverse image along `X_{T'} ⟶ T'` of `T ⊂ T'`. -/
abbrev relativeSquareThickening :=
  relBaseThickening (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
    (smallEtaleRingedToposHom B S hS (D.projection T'))

/-- **The relative square commutes on the nose: `f̃' ∘ i = t̃ ∘ f̃`.** -/
theorem relativeSquare_comm :
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T'))).comp
        (smallEtaleRingedToposHom B S hS (D.relativeMap h)) =
      (D.relativeSquareThickening h).comp (D.relativeSquareLeft h) :=
  relBase_comm (i := smallEtaleRingedToposHom B S hS (D.relativeMap h))
    (t := smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
    (f' := smallEtaleRingedToposHom B S hS (D.projection T'))
    (p := smallEtaleRingedToposHom B S hS (D.projection T)) (θ := D.relativeSquareIso h)
    (D.relativeSquareIso_compat h)

variable (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

/-- **`t̃` is a first order thickening**, with its square-zero ideal `f'⁻¹𝒥` (Stacks 08MB). -/
def relativeSquareThickeningFirstOrderThickening :
    FirstOrderThickening.{u, u + 1, u, u, u + 1, u} (D.relativeSquareThickening h) :=
  relBaseThickeningFirstOrderThickening
    (t := smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left))
    (f' := smallEtaleRingedToposHom B S hS (D.projection T'))
    (D.testSchemeFirstOrderThickening h hh)

end AlgebraicGeometry.Space.QuotientSituation

end
