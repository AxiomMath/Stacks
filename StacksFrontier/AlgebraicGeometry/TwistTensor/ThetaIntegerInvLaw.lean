module

public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.IntegerSnake
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaIntegerAssoc

/-!
# The inverse-law square for a comparison extended to negative degrees

`Stacks.AlgebraicGeometry.ThetaMul.thetaInt` compares two families of invertible modules — the
tensor powers of `𝒪_{U_d}(d)` and the `d`-divisible twists — and in a negative degree it is
*defined* as the comparison that the degree `m` comparison induces on the tensor inverses, by
`Stacks.Monoidal.isoOfTensorInverse`.  The identity that characterises such an extension is the
**inverse-law square**: the two comparisons in the degrees `-m` and `m`, tensored together, carry
the inverse law of the one family to the inverse law of the other.
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerAssoc.lean` records that square as the one
face of the multiplicativity statement that no arrangement of its square-chasing lemmas reaches
from the nonnegative degrees, and names
`Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp` as the identity that would prove it.

Two things stood between that identity and the square, and this file removes both.

The first is an instance.  `isoOfTensorInverse_tensorHom_comp` carries
`[(MonoidalCategory.tensorRight X).Faithful]`, which nothing in this repository discharges for a
tensor power of a module.  It is there only to let the snake hypothesis be used, and the inverse
law of `X` itself already gives that: `Stacks.Monoidal.whiskerRight_injective_of_tensorInverse`.

The second is the snake hypothesis — the compatibility of the two orders of the inverse law of
`L ^⊗ (-m)` — which `StacksFrontier/AlgebraicGeometry/TensorPowerAssoc/IntegerSnake.lean` now
supplies from the associativity constraint in an arbitrary integer tridegree.  So the square holds
for the integer tensor powers of any object with a two-sided tensor inverse whose own two inverse
laws are snake-compatible, which for an invertible sheaf of modules is free
(`AlgebraicGeometry.SheafOfModules.tensorInverse_snake`).

## Main results

* `Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso`: **the comparison of two tensor
  inverses is multiplicative against the inverse laws**, with no instance argument.  This is
  `Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp` with its faithfulness hypothesis replaced by
  the tensor inverse that discharges it.
* `Stacks.TensorPowers.TensorInverse.isoOfTensorInverse_addIso`: **the inverse-law square for the
  integer tensor powers**, with the snake hypothesis at the powers discharged and only the one at
  the base object left.

## Implementation notes

The two statements are in an abstract monoidal category, where the tensor powers are defined and
where `Stacks.TensorPowers.TensorInverse.addIso_snake` lives.  Nothing is said here about the
twists of `Proj` or about the modules of a scheme: carrying the square to
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt` means transporting it along the same chain the
associativity constraint is transported along in
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerAssoc.lean` — the localized monoidal
structure, its retyping, the tensor product sheaf of Stacks Tag 01CA, and the modules of a scheme
— and in the unitors that chain also passes through
`AlgebraicGeometry.SheafOfModules.unitIso`, the two localizations having different unit objects.

## References

* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)

## What this is for

The square at `Stacks.AlgebraicGeometry.ThetaMul.thetaInt` itself, and with it the
multiplicativity of `thetaInt` in an arbitrary integer bidegree: both are in
`StacksFrontier/AlgebraicGeometry/TwistTensor/ThetaIntegerBidegree.lean`, as
`Stacks.AlgebraicGeometry.ThetaMul.thetaInt_mul_neg_succ` and `thetaInt_mul`.

The route taken there is not the transport of `isoOfTensorInverse_addIso` to
`Stacks.Ample.tensorPowModuleAddIso` and
`Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen.twistMulIso`.  Since `thetaInt` in a
negative degree is `Stacks.Monoidal.isoOfTensorInverse` of the modules of the degree `d` open
*already*, `isoOfTensorInverse_tensorHom_comp_of_mulIso` applies to it directly, and the only
thing wanted at the modules of a scheme is the snake hypothesis — which
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_snake` proves by repeating the argument
of `Stacks.TensorPowers.TensorInverse.addIso_snake` there, the associativity constraint in an
arbitrary integer tridegree having been transported.  That is shorter than carrying the snake
across five structure maps and the two unit comparisons of the two localizations.

With the square in hand the multiplicativity is square-chasing: the bidegree `(n, 1)` for a
negative `n` by `Stacks.Monoidal.square_step_left`, and then every integer bidegree by an
induction over `ℤ` using `Stacks.AlgebraicGeometry.ThetaMul.square_step` upwards and
`square_step_left` downwards, both fed with
`Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_assoc_int` and
`Stacks.AlgebraicGeometry.ThetaMul.twistMulIso_assoc`.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory MonoidalCategory Stacks.TensorPowers

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **The comparison of two tensor inverses is multiplicative against the inverse laws**, with the
faithfulness instance of `Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp` replaced by the
tensor inverse that discharges it.

That lemma asks for `(MonoidalCategory.tensorRight X).Faithful`, and nothing in this repository
provides it for a tensor power of a module: the instance is there to let the snake hypothesis,
which speaks of both sides whiskered by `X`, be used on morphisms out of `X ⊗ A`.  But `hx'`
already exhibits `A` as a tensor inverse of `X`, and
`Stacks.Monoidal.whiskerRight_injective_of_tensorInverse` turns that into exactly the injectivity
needed.  So the hypothesis is free and this statement has no instance argument left. -/
theorem isoOfTensorInverse_tensorHom_comp_of_mulIso {A B X Y : C} (e : A ≅ B)
    (hx : A ⊗ X ≅ 𝟙_ C) (hx' : X ⊗ A ≅ 𝟙_ C) (hy : Y ⊗ B ≅ 𝟙_ C)
    (hsnake : hx'.hom ▷ X ≫ (λ_ X).hom =
      (α_ X A X).hom ≫ X ◁ hx.hom ≫ (ρ_ X).hom) :
    ((isoOfTensorInverse e hx hy).hom ⊗ₘ e.hom) ≫ hy.hom = hx'.hom := by
  refine whiskerRight_injective_of_tensorInverse hx' ?_
  refine (cancel_mono (λ_ X).hom).mp ?_
  rw [hsnake, MonoidalCategory.tensorHom_def, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  refine (cancel_mono (isoOfTensorInverse e hx hy).hom).mp ?_
  simp only [Category.assoc]
  rw [whiskerRight_isoOfTensorInverse e hx hy, ← Category.assoc,
    MonoidalCategory.associator_naturality_left]
  simp only [Category.assoc]
  rw [← Category.assoc ((isoOfTensorInverse e hx hy).hom ▷ (A ⊗ X)),
    ← MonoidalCategory.whisker_exchange]
  simp only [Category.assoc]
  rw [MonoidalCategory.rightUnitor_naturality]

end Stacks.Monoidal

namespace Stacks.TensorPowers.TensorInverse

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow
  Stacks.TensorPowers.intTensorPow

/-- **The inverse-law square for the integer tensor powers, abstractly.**  Let `p + q = 0`, let `e`
compare `L ^⊗ q` with an object `B` carrying a two-sided inverse law `hy` against `Y`, and let the
comparison `L ^⊗ p ≅ Y` be the one `e` induces on the tensor inverses by
`Stacks.Monoidal.isoOfTensorInverse`.  Then the two comparisons tensored together carry the
inverse law of the powers at `(p, q)` to the inverse law `hy`.

This is the identity that characterises a comparison family extended to negative degrees by
inverse-uniqueness, and it is the one square in a multiplicativity statement that is not reachable
from the squares in nonnegative degrees.  The snake hypothesis of
`Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso` is discharged by
`Stacks.TensorPowers.TensorInverse.addIso_snake`, so what is left of it is the
snake-compatibility of the two inverse laws of the *base* object — free for an invertible sheaf of
modules. -/
theorem isoOfTensorInverse_addIso {L : C} (h : TensorInverse L)
    (hs : (α_ L h.inv L).hom ≫ L ◁ h.mulIso'.hom ≫ (ρ_ L).hom =
      h.mulIso.hom ▷ L ≫ (λ_ L).hom) (p q : ℤ) (hpq : p + q = 0) {B Y : C}
    (e : intTensorPow L h.inv q ≅ B) (hy : Y ⊗ B ≅ 𝟙_ C) :
    ((Stacks.Monoidal.isoOfTensorInverse e
          (h.addIso q p ≪≫ reindex L h.inv (show q + p = 0 from by omega)) hy).hom ⊗ₘ
        e.hom) ≫ hy.hom =
      (h.addIso p q).hom ≫ (reindex L h.inv (show p + q = 0 from by omega)).hom :=
  Stacks.Monoidal.isoOfTensorInverse_tensorHom_comp_of_mulIso e _
    (h.addIso p q ≪≫ reindex L h.inv (show p + q = 0 from by omega)) hy
    (addIso_snake h hs p q hpq).symm

end Stacks.TensorPowers.TensorInverse

end
