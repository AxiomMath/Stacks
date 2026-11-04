module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraAmbientStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSquareComparisonSpacesUnit

/-!
# The map of kernel ideal sheaves of a commutative square, and the shape it gives the canonical map

Let
```
Z --i--→ X
|        |
f        g
↓        ↓
Z' -i'-→ X'
```
be a commutative square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
and write `𝓘 = Ker(i^♯)` and `𝓘' = Ker((i')^♯)`.  The canonical map of
[Stacks Project, Tag 04CP] is built in this development as
`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap`, a three-factor composite in which the
containment of ideal sheaves and the ambient pullback of regular functions sit on *opposite*
sides of the square comparison.  This file moves the containment across the comparison, so that
the two meet and the canonical map becomes

`f^*(i')^*((𝓘')ⁿ) ⟶ i^*g^*((𝓘')ⁿ) ⟶ i^*(𝓘ⁿ)`:

the square comparison followed by the inverse image along `i` of one map
`g^*((𝓘')ⁿ) ⟶ 𝓘ⁿ` of ideal sheaves.

That is exactly the shape the ringed-space map of [Stacks Project, Tag 01R4] has, where
`Stacks.ClosedImmersion.conormalSheafMap` is `Stacks.ClosedImmersion.pullbackCompIso` followed by
the pullback along `i` of `Stacks.ClosedImmersion.idealSheafMap`, and it is what part (2) of
[Stacks Project, Tag 04G2] needs in order to compare the two maps factor by factor.

## Main definitions

* `AlgebraicGeometry.Space.kernelIdealSquareMap`: the map `g^*((𝓘')ⁿ) ⟶ 𝓘ⁿ` of the square — the
  inverse image along `g` of the containment
  `AlgebraicGeometry.Space.kernelIdealSheaf_le_comp`, followed by the ambient map
  `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap`.  It is the spaces-side counterpart
  of `Stacks.ClosedImmersion.idealSheafMap`.

## Main results

* `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_eq_comp`: **the canonical map of the
  square is the square comparison followed by the inverse image along `i` of
  `AlgebraicGeometry.Space.kernelIdealSquareMap`.**
* `AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι`: **the map of ideal sheaves, read inside
  the structure sheaf** — followed by the inclusion `𝓘ⁿ ⊆ 𝒪_X` it is the inverse image along `g`
  of the inclusion `(𝓘')ⁿ ⊆ 𝒪_{X'}` composed with
  `AlgebraicGeometry.Space.structureModulePullbackMap`.  This is the mirror of
  `Stacks.ClosedImmersion.idealSheafMap_comp_ι`.
* `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_comp_map_ι`: **the canonical map read
  inside `i^*𝒪_X`**, the mirror of `Stacks.ClosedImmersion.conormalSheafMap_comp_pullback_ι`.
* `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_comp_map_ι_unit`: the same with the
  inclusions taken first and the square comparison read at the structure sheaf of `X'`.  That is
  the one object at which either square comparison can be described — see
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquareComparisonSpacesUnit.lean` — so it is the
  form in which part (2) of [Stacks Project, Tag 04G2] compares the two maps.

## Route

Moving the containment across the comparison is naturality of
`AlgebraicGeometry.Space.squarePullbackCompIso`, which is an isomorphism of functors; the
associativity is kept out of the geometric goal by
`CategoryTheory.map_comp_app_comp_of_naturality`, stated in an arbitrary category.  Reading the
composite inside the structure sheaf is
`AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap_comp_ι` together with the fact that the
containment is an inclusion of submodules of the unit module, so that composing it with the
inclusion of the larger one into `𝒪_{X'}` gives the inclusion of the smaller one.

## Implementation notes

Every step of the assembly is in term mode and every reassociation is an instantiation of a
lemma of `CategoryTheory` stated at variables.  That is forced, not stylistic: `rw` with
`CategoryTheory.Category.assoc` or `CategoryTheory.Functor.map_comp` against these goals reports
*did not find an occurrence of the pattern* with the note that the target is not type-correct at
`implicit` transparency, because the inverse image of modules on the small étale site is applied
to objects written as submodules of the unit module, and reconciling that with the category the
functor is declared on is past what `rw` will do.

Three places where the budget requires a declaration of its own:

* the degree-`n` component of `AlgebraicGeometry.Space.kernelIdealGradedAlgebraCompHom`, ascribed
  to the `AlgebraicGeometry.Space.kernelIdealSheafZPow` spelling of its source and target
  (`AlgebraicGeometry.Space.kernelIdealZPowCompHom`), and the same ascription carried through
  the canonical map (`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap_eq_compHom`, `rfl`).
  Leaving the graded-piece spelling to be reconciled inside the assembly exhausts the `isDefEq`
  budget;
* the naturality step `AlgebraicGeometry.Space.squarePullbackCompIso_hom_app_naturality_comp`,
  where the composite functor's action on a morphism is reconciled with the iterated one;
* the functoriality step `AlgebraicGeometry.Space.map_kernelIdealSquareMap_eq`.

And the containment itself, read inside the structure sheaf, is
`CategoryTheory.SheafOfModules.reesGradedAlgebraHomOfLe_app_comp_ι` — the same equation stated
with the site and the ring sheaf as variables, where it is `rfl`.  Written out at the small
étale site of an algebraic space and proved by `rfl` it is a **kernel** deterministic timeout.
With all of that, the file checks in half a second.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 09RS](https://stacks.math.columbia.edu/tag/09RS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory

/-- **Moving a map of objects across a natural transformation**, with the tail of the composite
left as a variable so that no associativity is done at the instantiation. -/
theorem map_comp_app_comp_of_naturality {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (Φ : F ⟶ G) {M N : C} (c : M ⟶ N) {V : D} (r : G.obj N ⟶ V) :
    F.map c ≫ Φ.app N ≫ r = Φ.app M ≫ G.map c ≫ r := by
  rw [← Category.assoc, Φ.naturality, Category.assoc]

/-- **Reassociating a two-step composite against a known value of its second factor.**  Stated
in an arbitrary category so that a consumer supplies the geometric terms and no associativity is
done at the instantiation; the implementation notes of this file record why that matters. -/
theorem comp_comp_eq_comp_of {C : Type*} [Category C] {U₀ U₁ U₂ U₃ V : C}
    (a : U₀ ⟶ U₁) (k : U₁ ⟶ U₂) (l : U₂ ⟶ V) (b : U₁ ⟶ U₃) (p : U₃ ⟶ V) (m : U₀ ⟶ U₃)
    (h₁ : k ≫ l = b ≫ p) (h₂ : a ≫ b = m) : (a ≫ k) ≫ l = m ≫ p := by
  rw [Category.assoc, h₁, ← Category.assoc, h₂]

/-- **Reassociating a two-step composite against a known value of its tail.**  Stated in an
arbitrary category, for the same reason as its neighbour. -/
theorem comp_comp_eq_comp_right {C : Type*} [Category C] {U₀ U₁ U₂ V : C}
    (a : U₀ ⟶ U₁) (b : U₁ ⟶ U₂) (c : U₂ ⟶ V) (d : U₁ ⟶ V) (h : b ≫ c = d) :
    (a ≫ b) ≫ c = a ≫ d := by
  rw [Category.assoc, h]

/-- A functor carries a known value of a composite to the composite of the images. -/
private theorem map_comp_eq_map_of_comp_eq {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) {X Y Z : C} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Z} (h : a ≫ b = c) :
    F.map a ≫ F.map b = F.map c := by
  rw [← F.map_comp, h]

end CategoryTheory

namespace SheafOfModules

universe t v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{t}}

/-- **The functoriality of the graded algebra of the powers of a sheaf of ideals, read inside the
structure sheaf.**  Its degree-`n` component is the inclusion of the `n`-th powers, so composing
it with the inclusion of the larger power into the unit module gives the inclusion of the
smaller one.

Stated generically, with the site and the ring sheaf as variables: the instantiation at the
small étale site of an algebraic space is then free, whereas writing the same equation out there
and proving it by `rfl` is a kernel deterministic timeout. -/
theorem reesGradedAlgebraHomOfLe_app_comp_ι (I K : (unit R).Submodule)
    (hcomm : ∀ (X : Cᵒᵖ) (a b : ToType (R.obj.obj X)), a * b = b * a) (h : I ≤ K) (n : ℤ) :
    (reesGradedAlgebraHomOfLe I K hcomm h).app n ≫ (idealSheafZPow K n).ι =
      (idealSheafZPow I n).ι :=
  rfl

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {Z X Z' X' : AlgebraicSpaces B S hS}

/-- **The containment of the powers of the two kernel ideal sheaves of a commutative square**,
as a morphism between the two submodules of the unit module.

This is the degree-`n` component of
`AlgebraicGeometry.Space.kernelIdealGradedAlgebraCompHom`, with its source and target written as
`AlgebraicGeometry.Space.kernelIdealSheafZPow` rather than as pieces of the graded algebra.  The
two spellings are definitionally equal, and naming the ascribed one pays for that once: the
implementation notes record that leaving it to be reconciled inside the assembly below exhausts
the `isDefEq` budget. -/
noncomputable def kernelIdealZPowCompHom (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    (kernelIdealSheafZPow B S hS i' n).toSheafOfModules ⟶
      (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules :=
  (kernelIdealGradedAlgebraCompHom B S hS i i' f g hsq).app n

/-- **The containment of the powers of the kernel ideal sheaves, read inside the structure
sheaf.**  It is an inclusion of submodules of the unit module, so composing it with the
inclusion of the larger one into the structure sheaf is the inclusion of the smaller one.

The proof is `CategoryTheory.SheafOfModules.reesGradedAlgebraHomOfLe_app_comp_ι` instantiated;
writing the equation out at this instance and proving it by `rfl` is a kernel deterministic
timeout, as the implementation notes record. -/
theorem kernelIdealZPowCompHom_comp_ι (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    kernelIdealZPowCompHom B S hS i i' f g hsq n ≫
        (kernelIdealSheafZPow B S hS (i ≫ g) n).ι =
      (kernelIdealSheafZPow B S hS i' n).ι :=
  SheafOfModules.reesGradedAlgebraHomOfLe_app_comp_ι _ _
    (structureRingSheaf_mul_comm B S hS X') (kernelIdealSheaf_le_comp B S hS i i' f g hsq) n

/-- **The map of kernel ideal sheaves attached to a commutative square.**  It is the inverse
image along `g` of the containment of the powers of the two kernel ideal sheaves, followed by the
ambient map `AlgebraicGeometry.Space.kernelIdealSheafZPowPullbackMap` of pullback of regular
functions along `g`.

This is the spaces-side counterpart of `Stacks.ClosedImmersion.idealSheafMap`, which packages
the same two steps into one `CategoryTheory.Limits.kernel.lift`; the characterising property of
both is their composite with the inclusion into the structure sheaf. -/
noncomputable def kernelIdealSquareMap (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    (modulePullback B S hS g).obj (kernelIdealSheafZPow B S hS i' n).toSheafOfModules ⟶
      (kernelIdealSheafZPow B S hS i n).toSheafOfModules :=
  (modulePullback B S hS g).map (kernelIdealZPowCompHom B S hS i i' f g hsq n) ≫
    kernelIdealSheafZPowPullbackMap B S hS i g n

/-- `AlgebraicGeometry.Space.kernelIdealSquareMap` written out. -/
theorem kernelIdealSquareMap_eq (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    kernelIdealSquareMap B S hS i i' f g hsq n =
      (modulePullback B S hS g).map (kernelIdealZPowCompHom B S hS i i' f g hsq n) ≫
        kernelIdealSheafZPowPullbackMap B S hS i g n :=
  rfl

/-- **The map of kernel ideal sheaves of a commutative square, read inside the structure
sheaf.**  Followed by the inclusion of the `n`-th power of `Ker(i^♯)` into `𝒪_X` it is the inverse
image along `g` of the inclusion of the `n`-th power of `Ker((i')^♯)` into `𝒪_{X'}`, read in
`𝒪_X` through `AlgebraicGeometry.Space.structureModulePullbackMap`.

This is the mirror of `Stacks.ClosedImmersion.idealSheafMap_comp_ι`, and it is what determines
the map: the inclusion of a sheaf of ideals into the structure sheaf is a monomorphism. -/
theorem kernelIdealSquareMap_comp_ι (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    kernelIdealSquareMap B S hS i i' f g hsq n ≫ (kernelIdealSheafZPow B S hS i n).ι =
      (modulePullback B S hS g).map (kernelIdealSheafZPow B S hS i' n).ι ≫
        structureModulePullbackMap B S hS g :=
  (eq_whisker (kernelIdealSquareMap_eq B S hS i i' f g hsq n)
      (kernelIdealSheafZPow B S hS i n).ι).trans
    (comp_comp_eq_comp_of _ _ _ _ _ _ (kernelIdealSheafZPowPullbackMap_comp_ι B S hS i g n)
      (map_comp_eq_map_of_comp_eq (modulePullback B S hS g)
        (kernelIdealZPowCompHom_comp_ι B S hS i i' f g hsq n)))

/-- `AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap` with its first factor written over
the ascribed containment `AlgebraicGeometry.Space.kernelIdealZPowCompHom`.  True by `rfl`; it is
a declaration of its own because reconciling the graded-piece spelling of the two ideal sheaves
with the `AlgebraicGeometry.Space.kernelIdealSheafZPow` spelling is what costs, and the
heartbeat budget is per declaration. -/
theorem conormalAlgebraSquarePieceMap_eq_compHom (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    conormalAlgebraSquarePieceMap B S hS i i' f g hsq n =
      (modulePullback B S hS f).map ((modulePullback B S hS i').map
          (kernelIdealZPowCompHom B S hS i i' f g hsq n)) ≫
        (squarePullbackCompIso B S hS i i' f g hsq).hom.app
            (kernelIdealSheafZPow B S hS (i ≫ g) n).toSheafOfModules ≫
          (modulePullback B S hS i).map (kernelIdealSheafZPowPullbackMap B S hS i g n) :=
  rfl

/-- Naturality of the square comparison, read at one object with the tail of the composite left
as a variable.  It is `CategoryTheory.map_comp_app_comp_of_naturality` at
`AlgebraicGeometry.Space.squarePullbackCompIso`; it is a declaration of its own because
reconciling the composite functor's action with the iterated one is what costs, and the budget is
per declaration. -/
theorem squarePullbackCompIso_hom_app_naturality_comp (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') {M N : Modules.{u, u} B S hS X'.1 X'.2} (c : M ⟶ N)
    {V : Modules.{u, u} B S hS Z.1 Z.2}
    (r : (modulePullback B S hS i).obj ((modulePullback B S hS g).obj N) ⟶ V) :
    (modulePullback B S hS f).map ((modulePullback B S hS i').map c) ≫
        (squarePullbackCompIso B S hS i i' f g hsq).hom.app N ≫ r =
      (squarePullbackCompIso B S hS i i' f g hsq).hom.app M ≫
        (modulePullback B S hS i).map ((modulePullback B S hS g).map c) ≫ r :=
  map_comp_app_comp_of_naturality (squarePullbackCompIso B S hS i i' f g hsq).hom c r

/-- The two factors of `AlgebraicGeometry.Space.kernelIdealSquareMap`, taken separately under
the inverse image along `i`, compose to the inverse image of the map itself.  Its own
declaration, so that the functoriality step and the assembly do not share a heartbeat budget. -/
theorem map_kernelIdealSquareMap_eq (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    (modulePullback B S hS i).map
          ((modulePullback B S hS g).map (kernelIdealZPowCompHom B S hS i i' f g hsq n)) ≫
        (modulePullback B S hS i).map (kernelIdealSheafZPowPullbackMap B S hS i g n) =
      (modulePullback B S hS i).map (kernelIdealSquareMap B S hS i i' f g hsq n) :=
  map_comp_eq_map_of_comp_eq (modulePullback B S hS i)
    (kernelIdealSquareMap_eq B S hS i i' f g hsq n).symm

/-- **The canonical map of [Stacks Project, Tag 04CP] in degree `n` is the square comparison
followed by the inverse image along `i` of one map of ideal sheaves.**

`AlgebraicGeometry.Space.conormalAlgebraSquarePieceMap` is defined with the containment of ideal
sheaves on the far side of the square comparison from the ambient map; naturality of
`AlgebraicGeometry.Space.squarePullbackCompIso` brings the two together, and what is left is
`AlgebraicGeometry.Space.kernelIdealSquareMap`.

The resulting shape is the one `Stacks.ClosedImmersion.conormalSheafMap` has on a ringed space:
the composition comparison of the square, followed by the pullback along `i` of the map of ideal
sheaves. -/
theorem conormalAlgebraSquarePieceMap_eq_comp (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    conormalAlgebraSquarePieceMap B S hS i i' f g hsq n =
      (squarePullbackCompIso B S hS i i' f g hsq).hom.app
          (kernelIdealSheafZPow B S hS i' n).toSheafOfModules ≫
        (modulePullback B S hS i).map (kernelIdealSquareMap B S hS i i' f g hsq n) :=
  (conormalAlgebraSquarePieceMap_eq_compHom B S hS i i' f g hsq n).trans
    ((squarePullbackCompIso_hom_app_naturality_comp B S hS i i' f g hsq
          (kernelIdealZPowCompHom B S hS i i' f g hsq n)
          ((modulePullback B S hS i).map
            (kernelIdealSheafZPowPullbackMap B S hS i g n))).trans
      (whisker_eq _ (map_kernelIdealSquareMap_eq B S hS i i' f g hsq n)))

/-- **The canonical map of [Stacks Project, Tag 04CP], read inside the structure sheaf.**  After
mapping both sides into `i^*𝒪_X` along the inverse images of the inclusions of the two sheaves of
ideals, the canonical map of the square becomes the square comparison
`AlgebraicGeometry.Space.squarePullbackCompIso` followed by the inverse image along `i` of the
characterising composite of `AlgebraicGeometry.Space.kernelIdealSquareMap_comp_ι`.

This is the mirror of `Stacks.ClosedImmersion.conormalSheafMap_comp_pullback_ι`, and it is the
sheaf-level description of the map that [Stacks Project, Tag 01R4] characterises on affine
charts. -/
theorem conormalAlgebraSquarePieceMap_comp_map_ι (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    conormalAlgebraSquarePieceMap B S hS i i' f g hsq n ≫
        (modulePullback B S hS i).map (kernelIdealSheafZPow B S hS i n).ι =
      (squarePullbackCompIso B S hS i i' f g hsq).hom.app
          (kernelIdealSheafZPow B S hS i' n).toSheafOfModules ≫
        (modulePullback B S hS i).map
          ((modulePullback B S hS g).map (kernelIdealSheafZPow B S hS i' n).ι ≫
            structureModulePullbackMap B S hS g) :=
  (eq_whisker (conormalAlgebraSquarePieceMap_eq_comp B S hS i i' f g hsq n)
      ((modulePullback B S hS i).map (kernelIdealSheafZPow B S hS i n).ι)).trans
    (comp_comp_eq_comp_right _ _ _ _
      (map_comp_eq_map_of_comp_eq (modulePullback B S hS i)
        (kernelIdealSquareMap_comp_ι B S hS i i' f g hsq n)))

/-- **The canonical map of [Stacks Project, Tag 04CP] read inside the structure sheaf, with the
square comparison moved to the unit module.**  The inclusions of the two sheaves of ideals are
taken first, and the square comparison is then read at the structure sheaf of `X'` — which is the
one object at which either square comparison can be described, and so the form in which part (2)
of [Stacks Project, Tag 04G2] compares this map with the ringed-space map of
[Stacks Project, Tag 01R4].

It is the previous statement with the inclusion carried across the comparison by naturality. -/
theorem conormalAlgebraSquarePieceMap_comp_map_ι_unit (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z')
    (g : X ⟶ X') (hsq : i ≫ g = f ≫ i') (n : ℤ) :
    conormalAlgebraSquarePieceMap B S hS i i' f g hsq n ≫
        (modulePullback B S hS i).map (kernelIdealSheafZPow B S hS i n).ι =
      (modulePullback B S hS f).map
            ((modulePullback B S hS i').map (kernelIdealSheafZPow B S hS i' n).ι) ≫
        (squarePullbackCompIso B S hS i i' f g hsq).hom.app
            (SheafOfModules.unit (structureRingSheaf B S hS X')) ≫
          (modulePullback B S hS i).map (structureModulePullbackMap B S hS g) :=
  (conormalAlgebraSquarePieceMap_comp_map_ι B S hS i i' f g hsq n).trans
    ((whisker_eq _ ((modulePullback B S hS i).map_comp
          ((modulePullback B S hS g).map (kernelIdealSheafZPow B S hS i' n).ι)
          (structureModulePullbackMap B S hS g))).trans
      (squarePullbackCompIso_hom_app_naturality_comp B S hS i i' f g hsq
        (kernelIdealSheafZPow B S hS i' n).ι
        ((modulePullback B S hS i).map (structureModulePullbackMap B S hS g))).symm)

end AlgebraicGeometry.Space

end
