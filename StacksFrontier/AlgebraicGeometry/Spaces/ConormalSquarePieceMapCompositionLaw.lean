module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSquarePieceMapComposition
public import StacksFrontier.CategoryTheory.SquareMapComposition

/-!
# The composition law for the canonical map of a square of immersions

Let
```
Z₁ --i₁--→ X₁
|          |
f₁         g₁
↓          ↓
Z₂ --i₂--→ X₂
|          |
f₂         g₂
↓          ↓
Z₃ --i₃--→ X₃
```
be two commutative squares of algebraic spaces over a scheme `S` stacked vertically.  This file
proves the composition law of [Stacks Project, Tag 04G2] part (3) at the generality of
**immersions**: the canonical map `(f₁ ≫ f₂)^*𝒞_{Z₃/X₃} ⟶ 𝒞_{Z₁/X₁}` of
[Stacks Project, Tag 04CP] attached to the outer rectangle is the composition comparison of
[Stacks Project, Tag 03LU] for `f₁` and `f₂`, followed by the inverse image along `f₁` of the map
of the lower square, followed by the map of the upper square.

The same law for a square of closed subspaces and the defining ideal sheaves of
[Stacks Project, Tag 03MB] is `AlgebraicGeometry.Space.conormalMap_comp`; here it is stated for
`AlgebraicGeometry.Space.conormalMapOfImmersions`.

## Main definitions

* `AlgebraicGeometry.Space.kernelIdealZPowSquareMap`: the degree-`n` canonical map of a
  commutative square of arbitrary morphisms, written **wholly at the
  `AlgebraicGeometry.Space.kernelIdealSheafZPow` spelling** of the powers of the kernel ideal
  sheaves — the square comparison `AlgebraicGeometry.Space.squarePullbackCompIso` followed by the
  inverse image along `i` of `AlgebraicGeometry.Space.kernelIdealSquareMap`.
* `AlgebraicGeometry.Space.conormalModuleOfImmersionZPowIso`: the bridge of
  [Stacks Project, Tag 09RR] with its source written at that same spelling.

## Main results

* `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_comp`: the composition law at that spelling.
* `AlgebraicGeometry.Space.conormalMapOfImmersions_eq_kernelIdealZPowSquareMap`: the canonical map
  of [Stacks Project, Tag 04CP] for a square of immersions is that map conjugated by the bridge.
* `AlgebraicGeometry.Space.conormalMapOfImmersions_comp`: **the composition law for the canonical
  map of a square of immersions.**
* `AlgebraicGeometry.Space.conormalMapOfImmersions_comp_of_comm`: the same with the commutativity
  of the outer rectangle derived rather than assumed, which is **part (3) of
  [Stacks Project, Tag 04G2] at the generality the source states it**.

## Implementation notes

`AlgebraicGeometry.Space.kernelIdealSquareMap_comp` is the ideal-sheaf level of the law, under
the three commutativities alone, and `AlgebraicGeometry.Space.squarePullbackCompIso_paste` is the
comparison level, for arbitrary morphisms.  What is delicate is their assembly.

Assembled directly — the pasted natural transformation expanded one component at a time, the
two maps of ideal sheaves split off as a right factor, and the halves glued by
`CategoryTheory.eq_whisker` and `CategoryTheory.whisker_eq` — **every step is a kernel
deterministic timeout**, including a single application of
`Stacks.CategoryTheory.map_comp_split` and including the expansion of the pasting at a *variable*
module, where neither spelling of the degree-`n` piece of the conormal algebra occurs at all.
So the cause is not the two spellings `(conormalAlgebra i).piece n` and
`(modulePullback i).obj (kernelIdealSheafZPow i n).toSheafOfModules`: it is that each
intermediate statement written out at these morphisms presents the kernel with two applications
of `CategoryTheory.Functor.map`, or of `CategoryTheory.NatTrans.app`, whose implicit objects are
definitionally but not syntactically equal — and reducing those projections unfolds
`AlgebraicGeometry.Space.modulePullback` to its construction by sheafification.  No attribute
reaches the kernel, and splitting into more declarations does not help, because each split
introduces one more such statement.

The assembly is therefore done **once, generically**, as
`Stacks.CategoryTheory.square_map_comp` of
`StacksFrontier/CategoryTheory/SquareMapComposition.lean`, with every functor, natural isomorphism,
object and morphism a variable; at the instantiation below **no argument is a restatement** —
each of the five hypotheses is an existing lemma applied verbatim — and Lean does not recheck a
proved statement's internal definitional equalities.  The three canonical maps enter that lemma
as variables with their factorisations as hypotheses, so that the factorisation used here is
`AlgebraicGeometry.Space.kernelIdealZPowSquareMap_eq`, which is `rfl`.  With that, the law at
this spelling checks in seconds.

The passage from there to `AlgebraicGeometry.Space.conormalMapOfImmersions` is a **single**
conjugation, `Stacks.CategoryTheory.conjugate_comp_of`: a composition law survives conjugation by
isomorphisms, the two conjugating isomorphisms at the middle object cancelling and the leading
comparison moving across by its naturality.  The two spellings of the degree-one piece meet
exactly once, in `AlgebraicGeometry.Space.conormalModuleOfImmersionZPowIso`, which is the bridge
of [Stacks Project, Tag 09RR] with its source written at the second spelling — they are equal by
`AlgebraicGeometry.Space.conormalAlgebra_piece`, which holds by `rfl`, and naming the second
spelling pays for that equality once instead of once per occurrence.

Two further points of spelling make that conjugation fit.

* **The naturality of the leading comparison must be taken in the tail-carrying form**
  `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_naturality_comp`.  Restating it without
  its tail — a statement whose only proof step is one generic naturality lemma — is a `whnf`
  timeout on its own, which is why `Stacks.CategoryTheory.conjugate_comp_of` takes that
  hypothesis with the tail left free.
* **The bridge isomorphism's target must be spelled `immersionConormalModule`, not the body of
  that abbreviation.**  With it written as `(conormalAlgebraOfImmersion … ).piece 1` the
  conjugation is a `whnf` timeout, and with it written as
  `AlgebraicGeometry.Space.immersionConormalModule` the file checks in ten seconds — because
  `AlgebraicGeometry.Space.conormalMapOfImmersions` is typed in the abbreviation, so the leading
  comparison is read by `CategoryTheory.NatTrans.app` at one spelling on one side and the other
  on the other, and `CategoryTheory.NatTrans.app` depends on the object it is evaluated at.

No hypothesis beyond the three commutativities and the three immersions is used: nothing is
assumed about closedness, quasi-compactness or quasi-coherence, and the commutativity of the
outer rectangle is taken as a hypothesis of its own rather than assembled from the other two, so
that it is the same datum the two halves take.

## References

* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The degree-`n` square map at the `kernelIdealSheafZPow` spelling -/

section Square

variable {Z X Z' X' : AlgebraicSpaces B S hS}

/-- **The degree-`n` canonical map of a commutative square, written wholly at the
`AlgebraicGeometry.Space.kernelIdealSheafZPow` spelling.**  It is the square comparison
`AlgebraicGeometry.Space.squarePullbackCompIso` followed by the inverse image along `i` of the map
`AlgebraicGeometry.Space.kernelIdealSquareMap` of ideal sheaves, which is the shape
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_eq_comp` puts the canonical map of
[Stacks Project, Tag 04CP] into.

It is a definition of its own, rather than that right-hand side written out, so that the
composition law below is a single instantiation of a generic lemma with nothing restated; the
module documentation records why. -/
noncomputable def kernelIdealZPowSquareMap (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    (modulePullback B S hS f).obj
        ((modulePullback B S hS i').obj
          (kernelIdealSheafZPow B S hS i' n).toSheafOfModules) ⟶
      (modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules :=
  (squarePullbackCompIso B S hS i i' f g hsq).hom.app
      (kernelIdealSheafZPow B S hS i' n).toSheafOfModules ≫
    (modulePullback B S hS i).map (kernelIdealSquareMap B S hS i i' f g hsq n)

/-- `AlgebraicGeometry.Space.kernelIdealZPowSquareMap` written out: the factorisation that the
generic composition law takes as a hypothesis. -/
theorem kernelIdealZPowSquareMap_eq (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    kernelIdealZPowSquareMap B S hS i i' f g hsq n =
      (squarePullbackCompIso B S hS i i' f g hsq).hom.app
          (kernelIdealSheafZPow B S hS i' n).toSheafOfModules ≫
        (modulePullback B S hS i).map (kernelIdealSquareMap B S hS i i' f g hsq n) :=
  rfl

/-- **The bridge of [Stacks Project, Tag 09RR] between the conormal algebra of an immersion and
the powers of its own kernel ideal sheaf, with its source written at the
`AlgebraicGeometry.Space.kernelIdealSheafZPow` spelling.**

This is `AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` and nothing else: the two
spellings `(conormalAlgebra i).piece n` and
`(modulePullback i).obj (kernelIdealSheafZPow i n).toSheafOfModules` of its source are equal by
`AlgebraicGeometry.Space.conormalAlgebra_piece`, which holds by `rfl`.  Naming the second
spelling pays for that equality **once**, here. -/
noncomputable def conormalModuleOfImmersionZPowIso (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) :
    (modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i 1).toSheafOfModules ≅
      immersionConormalModule B S hS i hi :=
  conormalAlgebraOfImmersionPieceIso B S hS i hi 1

/-- **The canonical map of [Stacks Project, Tag 04CP] for a square of immersions is
`AlgebraicGeometry.Space.kernelIdealZPowSquareMap` in degree one, conjugated by the bridge
isomorphisms of the two immersions.**

This is `AlgebraicGeometry.Space.conormalMapOfImmersions_eq` with its middle factor put into the
`AlgebraicGeometry.Space.kernelIdealSheafZPow` spelling by
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_eq_comp`, and with the two conjugating
isomorphisms taken at `AlgebraicGeometry.Space.conormalModuleOfImmersionZPowIso`.  Every object
in the statement is then written at one spelling, which is what lets the composition law below be
a single conjugation. -/
theorem conormalMapOfImmersions_eq_kernelIdealZPowSquareMap (i : Z ⟶ X) (i' : Z' ⟶ X')
    (f : Z ⟶ Z') (g : X ⟶ X') (hi : IsImmersion B S hS i.hom)
    (hi' : IsImmersion B S hS i'.hom) (hsq : i ≫ g = f ≫ i') :
    conormalMapOfImmersions B S hS i i' f g hi hi' hsq =
      (modulePullback B S hS f).map
          (conormalModuleOfImmersionZPowIso B S hS i' hi').inv ≫
        kernelIdealZPowSquareMap B S hS i i' f g hsq 1 ≫
          (conormalModuleOfImmersionZPowIso B S hS i hi).hom :=
  (conormalMapOfImmersions_eq B S hS i i' f g hi hi' hsq).trans
    (whisker_eq _
      (eq_whisker (conormalAlgebraSquarePieceMap_eq_comp B S hS i i' f g hsq 1) _))

end Square

/-! ### The composition law -/

section Law

variable {Z₁ Z₂ Z₃ X₁ X₂ X₃ : AlgebraicSpaces B S hS} (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂)
    (i₃ : Z₃ ⟶ X₃) (f₁ : Z₁ ⟶ Z₂) (g₁ : X₁ ⟶ X₂) (f₂ : Z₂ ⟶ Z₃) (g₂ : X₂ ⟶ X₃)
    (hsq₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (hsq₂ : i₂ ≫ g₂ = f₂ ≫ i₃)
    (hsq : i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃)

/-- **The degree-`n` square map of two vertically stacked commutative squares composes**, at the
`AlgebraicGeometry.Space.kernelIdealSheafZPow` spelling.  For the outer rectangle the map is the
inverse composition comparison of [Stacks Project, Tag 03LU] for `f₁` and `f₂`, followed by the
inverse image along `f₁` of the map of the lower square, followed by the map of the upper square.

One instantiation of `Stacks.CategoryTheory.square_map_comp`: the pasting of the three square
comparisons is `AlgebraicGeometry.Space.squarePullbackCompIso_paste`, the composition law for the
maps of ideal sheaves is `AlgebraicGeometry.Space.kernelIdealSquareMap_comp`, and the three
factorisations are `AlgebraicGeometry.Space.kernelIdealZPowSquareMap_eq`.  Nothing is restated;
the module documentation records why that matters.

Only the three commutativities are used: nothing is assumed about immersions, closedness,
quasi-compactness or quasi-coherence. -/
theorem kernelIdealZPowSquareMap_comp (n : ℤ) :
    kernelIdealZPowSquareMap B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq n =
      (modulePullbackCompIso B S hS f₁ f₂).inv.app
          ((modulePullback B S hS i₃).obj
            (kernelIdealSheafZPow B S hS i₃ n).toSheafOfModules) ≫
        (modulePullback B S hS f₁).map
            (kernelIdealZPowSquareMap B S hS i₂ i₃ f₂ g₂ hsq₂ n) ≫
          kernelIdealZPowSquareMap B S hS i₁ i₂ f₁ g₁ hsq₁ n :=
  Stacks.CategoryTheory.square_map_comp
    (modulePullback B S hS i₁) (modulePullback B S hS i₂) (modulePullback B S hS i₃)
    (modulePullback B S hS f₁) (modulePullback B S hS f₂)
    (modulePullback B S hS (f₁ ≫ f₂)) (modulePullback B S hS g₁)
    (modulePullback B S hS g₂) (modulePullback B S hS (g₁ ≫ g₂))
    (squarePullbackCompIso B S hS i₁ i₂ f₁ g₁ hsq₁)
    (squarePullbackCompIso B S hS i₂ i₃ f₂ g₂ hsq₂)
    (squarePullbackCompIso B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq)
    (modulePullbackCompIso B S hS f₁ f₂) (modulePullbackCompIso B S hS g₁ g₂)
    (squarePullbackCompIso_paste B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hsq₁ hsq₂ hsq)
    (kernelIdealSquareMap B S hS i₁ i₂ f₁ g₁ hsq₁ n)
    (kernelIdealSquareMap B S hS i₂ i₃ f₂ g₂ hsq₂ n)
    (kernelIdealSquareMap B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq n)
    (kernelIdealSquareMap_comp B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hsq₁ hsq₂ hsq n)
    (kernelIdealZPowSquareMap_eq B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq n)
    (kernelIdealZPowSquareMap_eq B S hS i₁ i₂ f₁ g₁ hsq₁ n)
    (kernelIdealZPowSquareMap_eq B S hS i₂ i₃ f₂ g₂ hsq₂ n)

end Law

/-! ### Stacks 04CP: the composition law for a square of immersions -/

section ImmersionLaw

variable {Z₁ Z₂ Z₃ X₁ X₂ X₃ : AlgebraicSpaces B S hS} (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂)
    (i₃ : Z₃ ⟶ X₃) (f₁ : Z₁ ⟶ Z₂) (g₁ : X₁ ⟶ X₂) (f₂ : Z₂ ⟶ Z₃) (g₂ : X₂ ⟶ X₃)
    (hi₁ : IsImmersion B S hS i₁.hom) (hi₂ : IsImmersion B S hS i₂.hom)
    (hi₃ : IsImmersion B S hS i₃.hom)
    (hsq₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (hsq₂ : i₂ ≫ g₂ = f₂ ≫ i₃)
    (hsq : i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃)

/-- **The composition law for the canonical map of [Stacks Project, Tag 04CP] at the generality of
immersions.**  Given two vertically composable commutative squares of algebraic spaces over `S`
whose horizontal arrows are immersions, the canonical map
`(f₁ ≫ f₂)^*𝒞_{Z₃/X₃} ⟶ 𝒞_{Z₁/X₁}` of the outer rectangle is the composition comparison of
[Stacks Project, Tag 03LU] for the two vertical maps of sources, followed by the inverse image
along `f₁` of the map `f₂^*𝒞_{Z₃/X₃} ⟶ 𝒞_{Z₂/X₂}` of the lower square, followed by the map
`f₁^*𝒞_{Z₂/X₂} ⟶ 𝒞_{Z₁/X₁}` of the upper square.

This is the statement that `AlgebraicGeometry.Space.conormalMap_comp` makes for a square of
closed subspaces, at the generality the source states it.  It is one application of
`Stacks.CategoryTheory.conjugate_comp_of` — a composition law survives conjugation by
isomorphisms, the two bridge isomorphisms at the middle conormal module cancelling and the
leading comparison moving across by its naturality — in which every argument is an existing
lemma applied verbatim: the law at the `AlgebraicGeometry.Space.kernelIdealSheafZPow` spelling,
the naturality of the composition comparison of [Stacks Project, Tag 03LU], and the three
instances of `AlgebraicGeometry.Space.conormalMapOfImmersions_eq_kernelIdealZPowSquareMap`.
Nothing is restated, which is what the module documentation records as the condition for the
instantiation to cost nothing. -/
theorem conormalMapOfImmersions_comp :
    conormalMapOfImmersions B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hi₁ hi₃ hsq =
      (modulePullbackCompIso B S hS f₁ f₂).inv.app
          (immersionConormalModule B S hS i₃ hi₃) ≫
        (modulePullback B S hS f₁).map
            (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂) ≫
          conormalMapOfImmersions B S hS i₁ i₂ f₁ g₁ hi₁ hi₂ hsq₁ :=
  by
  refine Stacks.CategoryTheory.conjugate_comp_of (modulePullback B S hS f₁)
    ((modulePullback B S hS f₂).map
      (conormalModuleOfImmersionZPowIso B S hS i₃ hi₃).inv)
    (kernelIdealZPowSquareMap B S hS i₂ i₃ f₂ g₂ hsq₂ 1)
    (conormalModuleOfImmersionZPowIso B S hS i₂ hi₂)
    (kernelIdealZPowSquareMap B S hS i₁ i₂ f₁ g₁ hsq₁ 1)
    (conormalModuleOfImmersionZPowIso B S hS i₁ hi₁)
    ((modulePullback B S hS (f₁ ≫ f₂)).map
      (conormalModuleOfImmersionZPowIso B S hS i₃ hi₃).inv)
    ((modulePullbackCompIso B S hS f₁ f₂).inv.app
      ((modulePullback B S hS i₃).obj (kernelIdealSheafZPow B S hS i₃ 1).toSheafOfModules))
    ((modulePullbackCompIso B S hS f₁ f₂).inv.app (immersionConormalModule B S hS i₃ hi₃))
    (kernelIdealZPowSquareMap B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hsq 1) ?_ ?_ ?_ ?_ ?_
  · exact modulePullbackCompIso_inv_app_naturality_comp B S hS f₁ f₂
      (conormalModuleOfImmersionZPowIso B S hS i₃ hi₃).inv
  · exact kernelIdealZPowSquareMap_comp B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hsq₁ hsq₂ hsq 1
  · exact conormalMapOfImmersions_eq_kernelIdealZPowSquareMap B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂)
      hi₁ hi₃ hsq
  · exact conormalMapOfImmersions_eq_kernelIdealZPowSquareMap B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂
  · exact conormalMapOfImmersions_eq_kernelIdealZPowSquareMap B S hS i₁ i₂ f₁ g₁ hi₁ hi₂ hsq₁

end ImmersionLaw

/-! ### Stacks 04G2, part (3) -/

section ImmersionLawStacks

variable {Z₁ Z₂ Z₃ X₁ X₂ X₃ : AlgebraicSpaces B S hS} (i₁ : Z₁ ⟶ X₁) (i₂ : Z₂ ⟶ X₂)
    (i₃ : Z₃ ⟶ X₃) (f₁ : Z₁ ⟶ Z₂) (g₁ : X₁ ⟶ X₂) (f₂ : Z₂ ⟶ Z₃) (g₂ : X₂ ⟶ X₃)
    (hi₁ : IsImmersion B S hS i₁.hom) (hi₂ : IsImmersion B S hS i₂.hom)
    (hi₃ : IsImmersion B S hS i₃.hom)
    (hsq₁ : i₁ ≫ g₁ = f₁ ≫ i₂) (hsq₂ : i₂ ≫ g₂ = f₂ ≫ i₃)

include hsq₁ hsq₂ in
/-- **The outer rectangle of two vertically stacked commutative squares commutes.**  Stated so
that the composition law below asks for the two squares of the source's diagram and nothing
else. -/
theorem stackedSquare_comm : i₁ ≫ g₁ ≫ g₂ = (f₁ ≫ f₂) ≫ i₃ := by
  rw [← Category.assoc, hsq₁, Category.assoc, hsq₂, Category.assoc]

/-- **Stacks 04G2, part (3), at the generality the source states it.**  Let
```
Z₁ --i₁--→ X₁
|          |
f₁         g₁
↓          ↓
Z₂ --i₂--→ X₂
|          |
f₂         g₂
↓          ↓
Z₃ --i₃--→ X₃
```
be two commutative squares of algebraic spaces over `S` whose horizontal arrows are
**immersions**, stacked vertically.  Then the canonical map
`(f₁ ≫ f₂)^*𝒞_{Z₃/X₃} ⟶ 𝒞_{Z₁/X₁}` of [Stacks Project, Tag 04CP] attached to the outer rectangle
is the composition comparison of [Stacks Project, Tag 03LU] for `f₁` and `f₂`, followed by the
inverse image along `f₁` of the map `f₂^*𝒞_{Z₃/X₃} ⟶ 𝒞_{Z₂/X₂}` of the lower square, followed by
the map `f₁^*𝒞_{Z₂/X₂} ⟶ 𝒞_{Z₁/X₁}` of the upper square.

The hypotheses are exactly the source's: the three immersions and the two commutativities, the
commutativity of the outer rectangle being derived by
`AlgebraicGeometry.Space.stackedSquare_comm`.  Nothing is assumed about closedness,
quasi-compactness or quasi-coherence. -/
@[stacks 04G2 "part (3): the composition law for the canonical map of 04CP, for arbitrary \
immersions of algebraic spaces"]
theorem conormalMapOfImmersions_comp_of_comm :
    conormalMapOfImmersions B S hS i₁ i₃ (f₁ ≫ f₂) (g₁ ≫ g₂) hi₁ hi₃
        (stackedSquare_comm B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hsq₁ hsq₂) =
      (modulePullbackCompIso B S hS f₁ f₂).inv.app
          (immersionConormalModule B S hS i₃ hi₃) ≫
        (modulePullback B S hS f₁).map
            (conormalMapOfImmersions B S hS i₂ i₃ f₂ g₂ hi₂ hi₃ hsq₂) ≫
          conormalMapOfImmersions B S hS i₁ i₂ f₁ g₁ hi₁ hi₂ hsq₁ :=
  conormalMapOfImmersions_comp B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hi₁ hi₂ hi₃ hsq₁ hsq₂
    (stackedSquare_comm B S hS i₁ i₂ i₃ f₁ g₁ f₂ g₂ hsq₁ hsq₂)

end ImmersionLawStacks

end AlgebraicGeometry.Space

end
