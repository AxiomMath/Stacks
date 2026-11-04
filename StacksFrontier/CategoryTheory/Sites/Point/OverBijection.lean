module

public import Mathlib.CategoryTheory.Sites.Point.Over

/-! # Points of a localized site above a given point: the one-to-one correspondence

Let `(C, J)` be a site, let `p` be a point of `C` with fibre functor `u = p.fiber`, and let `U` be
an object of `C`.  Stacks 04H2 attaches to every `x ∈ u(U)` a point `q_x` of the localized site
`C/U` lying above `p`, whose fibre functor is
```
  v_x : (φ : V ⟶ U) ↦ {y ∈ u(V) | u(φ)(y) = x} ;
```
this is Mathlib's `CategoryTheory.GrothendieckTopology.Point.over`, built from the subfunctor
`FunctorToTypes.fromOverSubfunctor u x` of `Over.forget U ⋙ u`.  Stacks 04H3 asserts that
`x ↦ q_x` is a *one-to-one correspondence* between `u(U)` and the points of `C/U` lying over `p`.

Stacks' proof of 04H3 runs in two steps.  Given a point `q` of `C/U` with fibre functor `v` and
with `j_U ∘ q = p`, it first produces, for every `V/U`, a cartesian square of sets
```
  v(V/U) ---> u(V)
    |           | u(φ)
  v(U/U) ---> u(U)
```
(this is where the topos-theoretic hypothesis `j_U ∘ q = p` is used: the square of representables
is cartesian, sheafification is exact by Stacks 00WJ, `(j_U⁻¹h_V)^# = j_U⁻¹(h_V^#)` by
Stacks 00XM, `u(V) = p⁻¹(h_V^#)` by Stacks 00YA, and `q⁻¹` is exact); it then observes that
`v(U/U)` is a singleton because `U/U` is terminal in `C/U`, calls its image in `u(U)` the element
`x`, and reads off from the square that `v = v_x`.

The **second** step is what is proved here, in the form of a genuine bijection.  A point `q` of
`C/U` over `p` presents its fibre functor `v` as a *subfunctor* `S` of `Over.forget U ⋙ u` — the
top map of the square above is injective, being the base change of `v(U/U) ↪ u(U)` — and the two
facts the first step produces are exactly

1. `S.obj (U/U)` is a singleton, and
2. `S.obj W = u(W.hom) ⁻¹' S.obj (U/U)` for every `W` of `C/U` (the square is cartesian).

`FunctorToTypes.IsFromOver` is that conjunction, and `fromOverSubfunctorEquiv` is the bijection
```
  u(U) ≃ {S : Subfunctor (Over.forget U ⋙ u) // IsFromOver u U S} ,   x ↦ v_x ,
```
which is Stacks 04H3.  The bridge back to points is `Point.over_fiber_eq_toFunctor`: the fibre
functor of `q_x` *is* the functor underlying the subfunctor `v_x`; and `q_x` lies over `p` by
Stacks 04H2, formalized as `Point.sheafFiberOverIso` in
`StacksFrontier/CategoryTheory/Sites/Point/LocalizedPoint.lean`.

The **first** step is not formalized, and is the precise remaining obligation for 04H3: from an
isomorphism `j_U⁻¹ ⋙ q.sheafFiber ≅ p.sheafFiber` (the formalized meaning of `j_U ∘ q = p`, cf.
Stacks 04H2), produce a subfunctor `S ≤ Over.forget U ⋙ u` with `S.toFunctor = q.fiber` satisfying
`IsFromOver`.  The tag notes below say which half each declaration covers.

## Main results

* `CategoryTheory.FunctorToTypes.fromOverSubfunctor_obj`: the sections of `v_x`.
* `CategoryTheory.FunctorToTypes.IsFromOver`: the two conditions on a subfunctor of
  `Over.forget X ⋙ F` that the fibre functor of a point over `p` satisfies.
* `CategoryTheory.FunctorToTypes.fromOverSubfunctor_injective`: distinct elements of `u(U)` give
  distinct fibre functors, i.e. the correspondence of Stacks 04H2 is injective.
* `CategoryTheory.FunctorToTypes.exists_eq_fromOverSubfunctor`: every subfunctor satisfying
  `IsFromOver` is `v_x` for some `x`.
* `CategoryTheory.FunctorToTypes.fromOverSubfunctorEquiv` (Stacks 04H3): the resulting bijection.
* `CategoryTheory.GrothendieckTopology.Point.over_fiber_eq_toFunctor`: the fibre functor of the
  point `q_x = Φ.over x` of `C/U` is the functor underlying the subfunctor `v_x`.

Tags covered: 04H3.
-/

@[expose] public section

namespace CategoryTheory.FunctorToTypes

universe w v u
variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) (X : C)

/-- The conditions on a subfunctor `S` of `Over.forget X ⋙ F` saying that `S` is the fibre
functor of a point of `C/X` lying over the point of `C` with fibre functor `F`, in the shape in
which Stacks 04H3's proof produces them:

1. `S.obj (X/X)` is a singleton, `X/X` being the final object of `C/X`; and
2. for every `W = (φ : V ⟶ X)` the square
```
  S.obj W  ---> F.obj V
     |             | F.map φ
  S.obj (X/X) ---> F.obj X
```
is cartesian, i.e. `S.obj W` is the preimage of `S.obj (X/X)` under `F.map φ`. -/
def IsFromOver (S : Subfunctor (Over.forget X ⋙ F)) : Prop :=
  (∃ x : F.obj X, S.obj (Over.mk (𝟙 X)) = {x}) ∧
    ∀ W : Over X, S.obj W = F.map W.hom ⁻¹' S.obj (Over.mk (𝟙 X))

/-- The sections of `v_x = FunctorToTypes.fromOverSubfunctor F x` over an object `W = (φ : V ⟶ X)`
of `C/X` are the elements of `F.obj V` lying over `x`. -/
lemma fromOverSubfunctor_obj (x : F.obj X) (W : Over X) :
    (fromOverSubfunctor F x).obj W = F.map W.hom ⁻¹' ({x} : Set (F.obj X)) :=
  Set.ext fun y => (mem_fromOverSubfunctor_iff F x y).trans (by simp)

/-- The sections of `v_x` over the final object `X/X` of `C/X` form the singleton `{x}`: this is
the "`v(U/U)` is a singleton, with image `x` in `u(U)`" step of Stacks 04H3. -/
lemma fromOverSubfunctor_obj_id (x : F.obj X) :
    (fromOverSubfunctor F x).obj (Over.mk (𝟙 X)) = {x} := by
  rw [fromOverSubfunctor_obj]
  ext y
  simp

/-- The subfunctor `v_x = FunctorToTypes.fromOverSubfunctor F x` satisfies the two conditions of
`IsFromOver`; so the correspondence of Stacks 04H2 does land in the set that Stacks 04H3 puts in
bijection with `u(U)`. -/
lemma isFromOver_fromOverSubfunctor (x : F.obj X) : IsFromOver F X (fromOverSubfunctor F x) :=
  ⟨⟨x, fromOverSubfunctor_obj_id F X x⟩, fun W => by
    rw [fromOverSubfunctor_obj_id F X x, fromOverSubfunctor_obj]⟩

/-- **Stacks 04H3**, injectivity: distinct elements `x` of `u(U)` give distinct points `q_x` of
`C/U`, because `x` is recovered from `v_x` as the unique section over the final object `U/U`. -/
@[stacks 04H3 "injectivity of x ↦ q_x"]
lemma fromOverSubfunctor_injective :
    Function.Injective (fun x : F.obj X => fromOverSubfunctor F x) := fun x x' h => by
  have h' : ({x} : Set (F.obj X)) = {x'} := by
    rw [← fromOverSubfunctor_obj_id F X x, ← fromOverSubfunctor_obj_id F X x']
    exact congrArg (fun S : Subfunctor (Over.forget X ⋙ F) => S.obj (Over.mk (𝟙 X))) h
  exact Set.singleton_eq_singleton_iff.1 h'

/-- **Stacks 04H3**, surjectivity: a subfunctor of `Over.forget U ⋙ u` whose sections over the
final object `U/U` form a singleton `{x}` and whose cartesian squares hold is `v_x`.  This is
the last paragraph of Stacks' proof: "the top horizontal map gives a bijection
`v(V/U) → {y ∈ u(V) | y ↦ x}`". -/
@[stacks 04H3 "surjectivity of x ↦ q_x, from the cartesian squares v(V/U) = u(V) ×_{u(U)} v(U/U)"]
lemma exists_eq_fromOverSubfunctor {S : Subfunctor (Over.forget X ⋙ F)} (hS : IsFromOver F X S) :
    ∃ x : F.obj X, S = fromOverSubfunctor F x := by
  obtain ⟨⟨x, hx⟩, hcart⟩ := hS
  refine ⟨x, Subfunctor.ext (funext fun W => ?_)⟩
  rw [hcart W, hx, fromOverSubfunctor_obj]

/-- **Stacks 04H3.** The construction of Stacks 04H2 gives a one to one correspondence
```
  u(U) ≃ {S : Subfunctor (Over.forget U ⋙ u) // IsFromOver u U S} ,   x ↦ v_x ,
```
between the elements of `u(U)` and the subfunctors `S` of `Over.forget U ⋙ u` satisfying the two
conditions of `IsFromOver`.

WHAT THIS DOES *NOT* SAY. `IsFromOver` is the characterisation that Stacks' proof *derives* from
`j_U ∘ q = p`; that derivation is **not** formalized here, so this equivalence is not yet an
equivalence with "the fibre functors of the points of `C/U` lying over `p`". The missing step is
to produce, from an isomorphism `j_U⁻¹ ⋙ q.sheafFiber ≅ p.sheafFiber` (the formalized reading of
`j_U ∘ q = p`, cf. 04H2's `sheafFiberOverIso`), a subfunctor `S` with `IsFromOver u U S` and
`S.toFunctor = q.fiber`. That needs exactness of sheafification (00WJ), the identification
`(j_U⁻¹h_V)^# = j_U⁻¹(h_V^#)` (00XM) and `u(V) = p⁻¹(h_V^#)` (00YA), none of which is available in
this repository. Until it lands, 04H3 is covered only up to that identification. -/
@[stacks 04H3 "the correspondence u(U) ≃ subfunctors satisfying IsFromOver; the identification
  of those subfunctors with points of C/U over p is NOT proved (needs 00WJ, 00XM, 00YA)"]
noncomputable def fromOverSubfunctorEquiv :
    F.obj X ≃ { S : Subfunctor (Over.forget X ⋙ F) // IsFromOver F X S } :=
  Equiv.ofBijective (fun x => ⟨fromOverSubfunctor F x, isFromOver_fromOverSubfunctor F X x⟩)
    ⟨fun _ _ h => fromOverSubfunctor_injective F X (Subtype.ext_iff.1 h), fun S => by
      obtain ⟨x, hx⟩ := exists_eq_fromOverSubfunctor F X S.2
      exact ⟨x, Subtype.ext hx.symm⟩⟩

end CategoryTheory.FunctorToTypes

namespace CategoryTheory.GrothendieckTopology.Point

universe w v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [LocallySmall.{w} C]
  (Φ : Point.{w} J) {X : C} (x : Φ.fiber.obj X)

/-- The fibre functor of the point `q_x = Φ.over x` of the localized site `C/X` (Stacks 04H2) is
the functor underlying the subfunctor `v_x` of `Over.forget X ⋙ Φ.fiber` that Stacks 04H3 puts in
bijection with the elements of `Φ.fiber.obj X`.

That `q_x` lies over `Φ` is `Point.sheafFiberOverIso`, the second half of Stacks 04H2. -/
lemma over_fiber_eq_toFunctor :
    (Φ.over x).fiber = (FunctorToTypes.fromOverSubfunctor Φ.fiber x).toFunctor :=
  rfl

end CategoryTheory.GrothendieckTopology.Point
