module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealVanishing

/-!
# Functoriality of the conormal algebra of a morphism of algebraic spaces

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`.
This file constructs the canonical homomorphism of sheaves of graded `𝒪_Z`-algebras

`(i ≫ g)^*(⨁_{n ≥ 0} (𝓘')ⁿ) ⟶ 𝒞_{Z/X',*}`,

where `𝓘' = Ker(𝒪_{X'} ⟶ i'_*𝒪_{Z'})` is the kernel ideal sheaf of `i'` and `𝒞_{Z/X',*}` is the
conormal algebra `AlgebraicGeometry.Space.conormalAlgebra` of the composite `i ≫ g : Z ⟶ X'`.
Since `i ≫ g = f ≫ i'`, the source is the inverse image along `f ≫ i'` of the graded algebra of
the powers of `𝓘'`, so this is the half of the canonical map of
[Stacks Project, Tag 09RS] that only moves the *source* of the two immersions; see
`What is not proved` for the half that moves the ambient space, which is not carried here.

The construction is the one the source proof opens with.  The composite
`i'^♯ : 𝒪_{X'} ⟶ i'_*𝒪_{Z'}` kills a regular function exactly when that function vanishes on
every point of `Z'` above the chart, and `g ∘ i = i' ∘ f` factors through `Z'`, so every function
killed by `i'^♯` is killed by `(i ≫ g)^♯`; that is the containment of sheaves of ideals
`𝓘' ⊆ Ker((i ≫ g)^♯)` of `AlgebraicGeometry.Space.kernelIdealSheaf_le_comp`.  Containment of
sheaves of ideals passes to all their powers, and the graded algebra of the powers of a sheaf of
ideals is functorial in the sheaf of ideals — its multiplication is multiplication of sections of
the structure sheaf, so a containment is automatically multiplicative.  Pulling the resulting
homomorphism of graded `𝒪_{X'}`-algebras back along `i ≫ g` gives the homomorphism of graded
`𝒪_Z`-algebras above, the pullback of sheaves of graded algebras of Stacks 0FQX being a functor.

## Main definitions

* `SheafOfModules.reesGradedAlgebraHomOfLe`: the graded algebra of the powers of a sheaf of
  ideals is functorial in the sheaf of ideals, as a homomorphism of sheaves of graded algebras.
* `AlgebraicGeometry.Space.kernelIdealGradedAlgebraCompHom`: that homomorphism at the two
  sheaves of ideals a commutative square produces, `⨁ (𝓘')ⁿ ⟶ ⨁ Ker((i ≫ g)^♯)ⁿ`.
* `AlgebraicGeometry.Space.conormalAlgebraCompMap`: the homomorphism of sheaves of graded
  `𝒪_Z`-algebras `(i ≫ g)^*(⨁ (𝓘')ⁿ) ⟶ 𝒞_{Z/X',*}`.

## Main results

* `SheafOfModules.idealAt_pow_le`, `SheafOfModules.idealSheafPow_mono` and
  `SheafOfModules.idealSheafZPow_mono`: containment of sheaves of ideals passes to the powers,
  for natural and for integer exponents.
* `AlgebraicGeometry.Space.kernelIdealSheaf_le_comp`: **the arithmetic heart of the
  construction.** For a commutative square as above, the kernel ideal sheaf of `i'` is contained
  in the kernel ideal sheaf of `i ≫ g`.  This is the vanishing of the composite
  `g^{-1}𝓘' ⟶ 𝒪_X ⟶ i_*𝒪_Z` of the proof of [Stacks Project, Tag 09RS], read on `X'`: it is
  `AlgebraicGeometry.Space.kernelIdealSheaf_le_ker_of_lift` applied to the lift `W ⟶ Z ⟶ Z'` of
  an étale scheme chart `W` of `Z` above `Z ×_{X'} V`, which exists because the square commutes.
* `AlgebraicGeometry.Space.conormalAlgebraCompMap_app`: the degree-`n` component of the
  homomorphism is the inverse image along `i ≫ g` of the inclusion of the `n`-th powers.

## Implementation notes

**Why the statement is for arbitrary morphisms and not for immersions.**
`AlgebraicGeometry.Space.conormalAlgebra` is defined for an arbitrary morphism of algebraic
spaces, as the inverse image of the graded algebra of the powers of its kernel ideal sheaf, and
nothing below uses any property of `i`, `i'`, `f` or `g`.  This is the generality in which
`AlgebraicGeometry.Space.conormalAlgebraEtaleRestrictionPieceIso` carries the companion
Lemma 09RR of the same section, and it specialises to the immersions of Stacks 09RS.

**Why the source is spelled as an inverse image along the composite.**  The source of the map of
Stacks 09RS is `f^*𝒞_{Z'/X',*} = f^*(i')^*(⨁ (𝓘')ⁿ)`, an inverse image along `f` of an inverse
image along `i'`.  Rewriting that as an inverse image along the composite `f ≫ i' = i ≫ g` asks
for the Stacks 03LU composition comparison of inverse images to be an isomorphism of sheaves of
*graded algebras*.  The spelling below is the one that needs no comparison: the pullback functor
of sheaves of graded algebras is applied once, to the morphism `i ≫ g`.  The graded comparison
is available, as `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso`, and
`AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap` is the map below read through it; see
`What is not proved`.

**Containment of sheaves of ideals, not a morphism of modules.**  The homomorphism of graded
algebras is built from the containment `𝓘' ≤ Ker((i ≫ g)^♯)` through
`CategoryTheory.PresheafOfModules.Submodule.homOfLE`, so each of its degreewise components is an
inclusion of subsheaves of the structure sheaf and multiplicativity is an equality of underlying
sections — definitional, since the multiplication of
`SheafOfModules.reesGradedAlgebra` is multiplication of sections of the structure sheaf.

## What is not proved

* **The ambient half of Stacks 09RS is not carried as a map of graded algebras.**  The map of
  the source factors as `f^*𝒞_{Z'/X',*} ⟶ 𝒞_{Z/X',*} ⟶ 𝒞_{Z/X,*}`, and only the first factor is
  constructed here.  The second asks for `g^♯` to carry `Ker((i ≫ g)^♯)ⁿ` into `Ker(i^♯)ⁿ` chart
  by chart, which is
  `AlgebraicGeometry.Space.mem_idealSheafZPow_kernelIdealSheaf_chartDiagramPullback` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraAmbient.lean`: there the covering sieve
  `SheafOfModules.powSieve` is transported across the two small étale sites by the pointwise
  criterion for covering sieves of the small étale site, and not by the étale postcomposition of
  `AlgebraicGeometry.Space.powSieve_etaleRestriction`, which needs the chart of the source and
  the chart of the target to be the same object of the big fppf site.  That file builds the
  ambient factor degreewise, as `AlgebraicGeometry.Space.conormalAlgebraAmbientPieceMap`; its
  own `What is not proved` section records what is still missing for the degreewise family to be
  multiplicative, and so for the factor to be a homomorphism of sheaves of graded algebras.

* **The source is identified with `f^*𝒞_{Z'/X',*}` elsewhere, not here.**  That identification
  asks for the Stacks 03LU composition comparison to be an isomorphism of sheaves of *graded
  algebras*, which `AlgebraicGeometry.Space.modulePullbackCompIso` is not known to be.  The
  graded comparison is `AlgebraicGeometry.Space.gradedAlgebraPullbackCompIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleGradedAlgebraPullbackComp.lean`, and the first
  factor of Stacks 09RS with its source spelled as Stacks 09RS spells it is
  `AlgebraicGeometry.Space.conormalAlgebraPullbackCompMap` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraPullbackComp.lean`.  The spelling below
  is the one that needs no comparison.  The degreewise comparison of Stacks 09RR in the
  `What is not proved` section of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalAlgebraEtaleRestriction.lean` is a different
  comparison, and is not promoted by it.

## References

* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.GradedAlgebraPullback
  (toposPullbackGradedAlgebra toposPullbackGradedAlgebraFunctor)

namespace SheafOfModules

universe t v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Containment of sheaves of ideals passes to the powers -/

/-- Containment of the ideals of sections of two sheaves of ideals passes to their powers. -/
theorem idealAt_pow_le {I K : (unit R).Submodule} (h : I ≤ K) (X : Cᵒᵖ) (n : ℕ) :
    idealAt I X ^ n ≤ idealAt K X ^ n :=
  Ideal.pow_right_mono (h X) n

/-- **Containment of sheaves of ideals passes to their powers.**  Membership in the `n`-th power
is covering of the sieve of charts on which the section lies in the `n`-th power of the ideal of
sections, and that sieve grows with the sheaf of ideals. -/
theorem idealSheafPow_mono {I K : (unit R).Submodule} (h : I ≤ K) (n : ℕ) :
    idealSheafPow I n ≤ idealSheafPow K n :=
  fun _ _ hx => J.superset_covering (fun W _ hf => idealAt_pow_le h (op W) n hf) hx

/-- **Containment of sheaves of ideals passes to the integer-indexed family of powers.**  In
negative degrees both families are the zero sheaf of ideals. -/
theorem idealSheafZPow_mono {I K : (unit R).Submodule} (h : I ≤ K) (n : ℤ) :
    idealSheafZPow I n ≤ idealSheafZPow K n := by
  rcases le_or_gt 0 n with hn | hn
  · rw [idealSheafZPow_of_nonneg I hn, idealSheafZPow_of_nonneg K hn]
    exact idealSheafPow_mono h _
  · rw [idealSheafZPow_of_neg I hn, idealSheafZPow_of_neg K hn]

/-! ### Functoriality of the graded algebra of the powers of a sheaf of ideals -/

/-- **The graded algebra of the powers of a sheaf of ideals is functorial in the sheaf of
ideals.**  A containment `𝓘 ≤ 𝓚` induces a homomorphism of sheaves of graded algebras
`⨁_{n ≥ 0} 𝓘ⁿ ⟶ ⨁_{n ≥ 0} 𝓚ⁿ`, given in each degree by the inclusion of the `n`-th powers.

It preserves products of homogeneous local sections because both multiplications are
multiplication of sections of the structure sheaf and the inclusions do not change the
underlying section. -/
noncomputable def reesGradedAlgebraHomOfLe (I K : (unit R).Submodule)
    (hcomm : ∀ (X : Cᵒᵖ) (a b : ToType (R.obj.obj X)), a * b = b * a) (h : I ≤ K) :
    reesGradedAlgebra I hcomm ⟶ reesGradedAlgebra K hcomm where
  app n := ⟨PresheafOfModules.Submodule.homOfLE
    (Submodule.le_iff.mp (idealSheafZPow_mono h n))⟩
  map_mul _ _ _ _ _ := rfl

/-- In each degree `n`, the homomorphism `reesGradedAlgebraHomOfLe I K hcomm h` sends a local
section of `𝓘ⁿ` to the same section of the structure sheaf, viewed as a section of `𝓚ⁿ`. -/
@[simp]
theorem reesGradedAlgebraHomOfLe_app_coe (I K : (unit R).Submodule)
    (hcomm : ∀ (X : Cᵒᵖ) (a b : ToType (R.obj.obj X)), a * b = b * a) (h : I ≤ K) (n : ℤ)
    (X : Cᵒᵖ) (x : (reesPiece I n).val.obj X) :
    reesVal K (((reesGradedAlgebraHomOfLe I K hcomm h).app n).val.app X x) = reesVal I x :=
  rfl

end SheafOfModules

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X Z' X' : AlgebraicSpaces B S hS}

/-! ### The kernel ideal sheaf of a commutative square -/

/-- **A commutative square carries the kernel ideal sheaf of the lower edge into the kernel ideal
sheaf of the diagonal.**  Let `i ≫ g = f ≫ i'` be a commutative square of algebraic spaces.  Then
every regular function on an étale chart of `X'` killed by `i'^♯` is killed by `(i ≫ g)^♯`.

This is the vanishing of the composite `g^{-1}𝓘' ⟶ g^{-1}𝒪_{X'} ⟶ 𝒪_X ⟶ i_*𝒪_Z` of the proof of
[Stacks Project, Tag 09RS], read on `X'` rather than on `X`.  The kernel of `(i ≫ g)^♯` over a
chart `V` is computed chart by chart by
`AlgebraicGeometry.Space.mem_ker_structureSharp_iff`: it is the set of functions vanishing on
every étale scheme chart `W` of `Z` above `Z ×_{X'} V`.  Such a `W` maps to `Z`, hence through
`f` to `Z'`, compatibly with its map to `V` because the square commutes, so it is a scheme over
`V` lifting along `i'` and `AlgebraicGeometry.Space.kernelIdealSheaf_le_ker_of_lift` applies. -/
theorem kernelIdealSheaf_le_comp (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') :
    kernelIdealSheaf B S hS i' ≤ kernelIdealSheaf B S hS (i ≫ g) := by
  have hh : (i ≫ g).hom = f.hom ≫ i'.hom := by
    rw [← ObjectProperty.FullSubcategory.comp_hom, hsq]
  intro V s hs
  refine (mem_ker_structureSharp_iff B S hS (i ≫ g) V.unop s).2 fun j => ?_
  refine kernelIdealSheaf_le_ker_of_lift B S hS i' V.unop
    (chartBaseChangeMap B S hS (i ≫ g) V.unop j) (j.right.unop.1.hom ≫ f.hom) ?_ hs
  have hc : (unop j.right).1.hom ≫ (i ≫ g).hom =
      yoneda.map (chartBaseChangeMap B S hS (i ≫ g) V.unop j) ≫ (unop V).1.hom :=
    (chartDiagramOfIndex B S hS (i ≫ g) V.unop j).comm
  rw [← hc, hh]
  exact (Category.assoc _ _ _).symm

/-! ### The graded algebra map of a commutative square -/

/-- **The homomorphism of graded `𝒪_{X'}`-algebras of a commutative square.**  For a commutative
square `i ≫ g = f ≫ i'` of algebraic spaces, the containment of kernel ideal sheaves
`AlgebraicGeometry.Space.kernelIdealSheaf_le_comp` induces a homomorphism

`⨁_{n ≥ 0} (𝓘')ⁿ ⟶ ⨁_{n ≥ 0} Ker((i ≫ g)^♯)ⁿ`

of sheaves of graded algebras on the small étale site of `X'`. -/
noncomputable def kernelIdealGradedAlgebraCompHom (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') :
    kernelIdealGradedAlgebra B S hS i' ⟶ kernelIdealGradedAlgebra B S hS (i ≫ g) :=
  SheafOfModules.reesGradedAlgebraHomOfLe _ _ (structureRingSheaf_mul_comm B S hS X')
    (kernelIdealSheaf_le_comp B S hS i i' f g hsq)

/-- **The canonical map of conormal algebras of a commutative square, in the source variable.**
For a commutative square `i ≫ g = f ≫ i'` of algebraic spaces, the inverse image along
`i ≫ g = f ≫ i'` of the graded algebra of the powers of the kernel ideal sheaf of `i'` maps
canonically to the conormal algebra of `i ≫ g`:

`(i ≫ g)^*(⨁_{n ≥ 0} (𝓘')ⁿ) ⟶ 𝒞_{Z/X',*}`.

It is the pullback of sheaves of graded algebras of Stacks 0FQX applied to
`AlgebraicGeometry.Space.kernelIdealGradedAlgebraCompHom`, so it is multiplicative in every
degree without any further input.

This is the first of the two factors of the canonical map of [Stacks Project, Tag 09RS]; the
module documentation records that the second factor, which replaces the ambient space `X'` by
`X`, is not carried here, and that the source is not identified with `f^*𝒞_{Z'/X',*}`. -/
noncomputable def conormalAlgebraCompMap (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') :
    toposPullbackGradedAlgebra (X := smallEtaleRingedTopos B S hS Z)
        (Y := smallEtaleRingedTopos B S hS X')
        (smallEtaleRingedToposModulesHom B S hS (i ≫ g))
        (kernelIdealGradedAlgebra B S hS i') ⟶
      conormalAlgebra B S hS (i ≫ g) :=
  (toposPullbackGradedAlgebraFunctor (X := smallEtaleRingedTopos B S hS Z)
    (Y := smallEtaleRingedTopos B S hS X')
    (smallEtaleRingedToposModulesHom B S hS (i ≫ g))).map
      (kernelIdealGradedAlgebraCompHom B S hS i i' f g hsq)

/-- **The degree-`n` component of the canonical map** is the inverse image along `i ≫ g` of the
inclusion of the `n`-th power of the kernel ideal sheaf of `i'` into the `n`-th power of the
kernel ideal sheaf of `i ≫ g`. -/
theorem conormalAlgebraCompMap_app (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    (conormalAlgebraCompMap B S hS i i' f g hsq).app n =
      (modulePullback B S hS (i ≫ g)).map
        ((kernelIdealGradedAlgebraCompHom B S hS i i' f g hsq).app n) :=
  rfl

end AlgebraicGeometry.Space

end
