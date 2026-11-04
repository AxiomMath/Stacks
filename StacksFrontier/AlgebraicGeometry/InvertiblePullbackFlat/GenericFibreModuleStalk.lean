module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreStalk
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula

/-!
# Modules on a fibre over a point whose local ring is a field

Let `f : X ⟶ Y` be a morphism of schemes, let `y` be a point of `Y` whose local ring is a
field, and let `ℒ` be a sheaf of `𝒪_X`-modules. The fibre `X_y` is cut out by the maximal
ideal of `𝒪_{Y, y}`, so over such a `y` it has the same local rings as `X`
(`AlgebraicGeometry.isIso_stalkMap_fiberι`). This file carries that identification across to
*modules*: the stalk of the restriction `ℒ|_{X_y}` at a point of the fibre is the stalk of `ℒ`
itself at the image point, canonically and compatibly with germs.

This is the **module-level half of the first paragraph of Stacks Tag 0BD7**, which reads a
trivializing section of `ℒ` on the generic fibre `X_ξ` as a meromorphic section of `ℒ` on `X`.
The ring-level half is `AlgebraicGeometry.isIso_stalkMap_fiberι_genericPoint`; what is added
here is the passage from it to the modules, which is Tag 0098 (the stalk of a pullback is a
base change) composed with the observation that base change along a *bijective* ring map does
nothing.

## Main definitions

* `TensorProduct.lidOfBijectiveAlgebraMap`: for an `R`-algebra `A` whose structure map is
  bijective, `A ⊗[R] M ≃ₗ[R] M`. This is the algebraic content of the passage from the ring
  identification to the module identification.
* `AlgebraicGeometry.stalkPullbackFiberιAddEquiv`: one chosen such isomorphism, so that the
  element of `ℒ`'s stalk produced from an element of the fibre stalk is a *function* of it.

## Main results

* `AlgebraicGeometry.base_genericPoint_eq_genericPoint`: a surjective morphism of irreducible
  schemes carries the generic point to the generic point.
* `AlgebraicGeometry.genericPoint_mem_range_fiberι_genericPoint`: consequently the generic
  fibre of such a morphism contains the generic point of the source, which is why a germ at
  the generic point can be read off the generic fibre at all.
* `AlgebraicGeometry.bijective_stalkMap_fiberι_of_mem`: the canonical map `𝒪_{X, x} ⟶ 𝒪_{X_y, x}`
  is bijective at an *arbitrary* point of the fibre over a `y` whose local ring is a field.
* `AlgebraicGeometry.exists_addEquiv_stalk_pullback_fiberι` and
  `AlgebraicGeometry.exists_addEquiv_stalk_pullback_fiberι_genericPoint`: the stalk of
  `ℒ|_{X_y}` at a point of the fibre is `ℒ`'s own stalk at the image point, by an isomorphism
  carrying the germ of a restricted section to the germ of that section — the second for the
  generic fibre of a morphism to an integral scheme, where the hypothesis on `y` is automatic.
* `AlgebraicGeometry.exists_addEquiv_smul_stalk_pullback_fiberι`: the same isomorphism with its
  scalar law, semilinear along the bijective stalk map. `Stacks.RingedSpace.pullbackStalkFormula`
  already supplies a `≃ₗ`; the additive statements above discard it.
* `AlgebraicGeometry.exists_addEquiv_germ_smul_stalk_pullback_fiberι`: both laws about **one**
  isomorphism. The two statements above each record only one of them, and a consumer that
  needs both cannot combine two existentials.
* `AlgebraicGeometry.span_eq_top_grpStalk_of_addEquiv_smul` and
  `AlgebraicGeometry.span_eq_top_grpStalk_stalkPullbackFiberιAddEquiv`: a *generator* of the
  fibre stalk gives a generator of `ℒ`'s stalk at the image point, **named**: it is the image
  of the given element under the isomorphism.
* `AlgebraicGeometry.span_eq_top_grpGerm_of_span_eq_top_grpGerm_pullbackUnit`: when the element
  of the fibre stalk is the germ of the restriction of a section `s` of `ℒ`, that named
  generator is the germ of `s` itself.
* `AlgebraicGeometry.exists_span_eq_top_stalk_pullback_fiberι` and
  `AlgebraicGeometry.exists_span_eq_top_stalk_pullback_fiberι_genericPoint`: the existential
  forms, which is what an earlier consumer asks for. An additive bijection alone cannot prove
  them, and they are what the first paragraph of Stacks Tag 0BD7 needs from a trivialization on
  the generic fibre.

## Implementation notes

`AlgebraicGeometry.bijective_stalkMap_fiberι` is stated at the point `f.asFiber x` of the
fibre `f.fiber (f x)`, which is the spelling its proof needs. A consumer holding a point of
`f.fiber y` for a *given* `y` cannot use it without transporting along an equality of points,
and that transport changes the fibre scheme itself. `bijective_stalkMap_fiberι_of_mem` removes
the obstacle rather than working around it: taking the image point `x` of the given `x₀` makes
`y` a variable that can be substituted away, after which `x₀` and `f.asFiber x` are points of
one and the same fibre and are equal because `f.fiberι y` is an embedding. No transport, and
no `eqToHom`, survives in the statement.

The module statement is given over `Stacks.SheafOfModules.TensorStalkRingedSpace.structureRingSheaf
  X.toRingedSpace` rather
than over `X.Modules`: the `Module` instance on a stalk is found by instance synthesis only at
the former spelling. For the same reason the two instances the proof supplies are written at
the spelling in which `Stacks.RingedSpace.pullbackStalkFormula` states its tensor product —
the base point read through `(f.fiberι y).toLRSHom.toShHom` — since instance search matches
syntactically and the two spellings of that point, while definitionally equal, are not the
same term. The conclusion is an additive isomorphism: the two sides are modules over
different rings, identified only through the ring isomorphism above, and the germ law recorded
alongside it is what consumers use.

**Why the generation statements are given in `∀`-form.** `Stacks.RingedSpace.pullbackStalkFormula`
asserts the *existence* of the comparison isomorphism, so the identifications here are
existential too. An existential generator is useless to the later paragraphs of Stacks Tag 0BD7:
they need the germ of one particular section to generate at every point of the generic fibre, and
two applications of an existential statement at two points produce two unrelated witnesses. The
statements are therefore arranged so that the generator is *named* —
`span_eq_top_grpStalk_of_addEquiv_smul` takes the isomorphism as a parameter and
`stalkPullbackFiberιAddEquiv` fixes one choice of it, after which the generator downstairs is a
function of the element upstairs and `span_eq_top_grpGerm_of_span_eq_top_grpGerm_pullbackUnit`
identifies it with the germ of a section when the element upstairs is a restricted germ. The
existential forms are kept, and are now one-line consequences, so their consumers are unchanged.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction Stacks.RingedSpace
open scoped TensorProduct

universe u

section TensorProduct

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]

/-- **Base change along a bijective ring map does nothing.** If the structure map of an
`R`-algebra `A` is bijective then `A ⊗[R] M` is `M`, for every `R`-module `M`. -/
noncomputable def TensorProduct.lidOfBijectiveAlgebraMap
    (h : Function.Bijective (algebraMap R A)) : A ⊗[R] M ≃ₗ[R] M :=
  (TensorProduct.congr (LinearEquiv.ofBijective (Algebra.linearMap R A) h).symm
    (LinearEquiv.refl R M)).trans (TensorProduct.lid R M)

/-- The identification of `A ⊗[R] M` with `M` sends `1 ⊗ m` to `m`. -/
theorem TensorProduct.lidOfBijectiveAlgebraMap_one_tmul
    (h : Function.Bijective (algebraMap R A)) (m : M) :
    TensorProduct.lidOfBijectiveAlgebraMap (R := R) (A := A) (M := M) h (1 ⊗ₜ[R] m) = m := by
  have h1 : (LinearEquiv.ofBijective (Algebra.linearMap R A) h).symm (1 : A) = (1 : R) := by
    refine (LinearEquiv.symm_apply_eq _).mpr ?_
    show (1 : A) = algebraMap R A 1
    rw [map_one]
  simp [TensorProduct.lidOfBijectiveAlgebraMap, h1]

end TensorProduct

namespace AlgebraicGeometry

/-- A surjective morphism of irreducible schemes carries the generic point of the source to the
generic point of the target: the image of a dense singleton is dense. -/
theorem base_genericPoint_eq_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] [IrreducibleSpace Y] (hsurj : Function.Surjective f.base) :
    f.base (genericPoint X) = genericPoint Y := by
  refine IsGenericPoint.eq ?_ (genericPoint_spec Y)
  have h := (genericPoint_spec X).image (f := f.base) f.base.hom.continuous
  rwa [Set.image_univ, hsurj.range_eq, closure_univ] at h

/-- The generic fibre of a surjective morphism of irreducible schemes contains the generic
point of the source. This is why a germ at the generic point of `X` may be read off the generic
fibre. -/
theorem genericPoint_mem_range_fiberι_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] [IrreducibleSpace Y] (hsurj : Function.Surjective f.base) :
    genericPoint X ∈ Set.range (f.fiberι (genericPoint Y)).base := by
  rw [f.range_fiberι (genericPoint Y)]
  exact base_genericPoint_eq_genericPoint f hsurj

/-- **The canonical map from a local ring of the source to a local ring of the fibre is
bijective at every point of a fibre over a point whose local ring is a field.**
`AlgebraicGeometry.bijective_stalkMap_fiberι` is the same statement at the point presented as
`f.asFiber x`; this is the form a consumer holding a point of `f.fiber y` can apply. -/
theorem bijective_stalkMap_fiberι_of_mem {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥) (x₀ : f.fiber y) :
    Function.Bijective ((f.fiberι y).stalkMap x₀).hom := by
  obtain ⟨x, hx₀⟩ : ∃ x : X, (f.fiberι y).base x₀ = x := ⟨_, rfl⟩
  have hx : f.base x = y := by
    have hmem : (f.fiberι y).base x₀ ∈ Set.range (f.fiberι y).base := Set.mem_range_self x₀
    rw [f.range_fiberι y] at hmem
    rw [← hx₀]; exact hmem
  subst hx
  have hx₀' : x₀ = f.asFiber x :=
    (f.fiberι (f.base x)).isEmbedding.injective (hx₀.trans (f.fiberι_asFiber x).symm)
  rw [hx₀']
  exact bijective_stalkMap_fiberι f x h

/-- **The module-level half of the first paragraph of Stacks Tag 0BD7, with both of its laws.**
Over a point `y` of the target whose local ring is a field, the stalk of the restriction of `ℒ`
to the fibre `X_y` at a point `x₀` of that fibre is the stalk of `ℒ` itself at the image of
`x₀`, by an additive isomorphism which both carries the germ of a restricted section to the
germ of that section and is semilinear along the bijective stalk map.

By Tag 0098 the left-hand side is `𝒪_{X_y, x₀} ⊗_{𝒪_{X, x₀}} ℒ_{x₀}`, and the ring map along
which that tensor product is taken is bijective by
`AlgebraicGeometry.bijective_stalkMap_fiberι_of_mem`, so the tensor product collapses.
`Stacks.RingedSpace.pullbackStalkFormula` already produces a `≃ₗ` over the fibre's local ring;
the scalar law is that structure, retained rather than discarded.

Both laws are stated about **one** isomorphism because the consumer needs both: the scalar law
is what carries a *generator* across, which an additive bijection alone cannot do, and the germ
law is what says *which* element the generator is. Two separate existential statements cannot be
combined. -/
theorem exists_addEquiv_germ_smul_stalk_pullback_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) (x₀ : f.fiber y) :
    ∃ e : grpStalk (f.fiber y).toRingedSpace
        ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀ ≃+
      grpStalk X.toRingedSpace L.val (((f.fiberι y).toLRSHom.toShHom).hom.base x₀),
      (∀ (V : Opens X) (hx : ((f.fiberι y).toLRSHom.toShHom).hom.base x₀ ∈ V)
          (s : L.val.obj (op V)),
        e (grpGerm (f.fiber y).toRingedSpace
            ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀
            ((opensMap (f.fiberι y).toLRSHom.toShHom).obj V) hx
            (pullbackUnit (f.fiberι y).toLRSHom.toShHom L (op V) s)) =
          grpGerm X.toRingedSpace L.val (((f.fiberι y).toLRSHom.toShHom).hom.base x₀) V hx s) ∧
      ∀ (c : ringStalk X.toRingedSpace (((f.fiberι y).toLRSHom.toShHom).hom.base x₀))
        (v : grpStalk (f.fiber y).toRingedSpace
          ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀),
        e (((((f.fiberι y).toLRSHom.toShHom).hom.stalkMap x₀).hom c) • v) = c • e v := by
  obtain ⟨e, he⟩ := pullbackStalkFormula (f.fiberι y).toLRSHom.toShHom L x₀
  let _inst : Algebra (ringStalk X.toRingedSpace ((((f.fiberι y).toLRSHom.toShHom).hom.base) x₀))
      (ringStalk (f.fiber y).toRingedSpace x₀) :=
    ((((f.fiberι y).toLRSHom.toShHom).hom.stalkMap x₀)).hom.toAlgebra
  refine ⟨e.toAddEquiv.trans
    (TensorProduct.lidOfBijectiveAlgebraMap
      (M := grpStalk X.toRingedSpace L.val ((((f.fiberι y).toLRSHom.toShHom).hom.base) x₀))
      (bijective_stalkMap_fiberι_of_mem f h x₀)).toAddEquiv, ?_, ?_⟩
  · intro V hx s
    show TensorProduct.lidOfBijectiveAlgebraMap _ (e _) = _
    rw [he V hx s]
    exact TensorProduct.lidOfBijectiveAlgebraMap_one_tmul _ _
  · intro c v
    show TensorProduct.lidOfBijectiveAlgebraMap _ (e _) = _
    rw [map_smul e]
    rw [show ((((f.fiberι y).toLRSHom.toShHom).hom.stalkMap x₀).hom c) =
        algebraMap (ringStalk X.toRingedSpace ((((f.fiberι y).toLRSHom.toShHom).hom.base) x₀))
          (ringStalk (f.fiber y).toRingedSpace x₀) c from rfl,
      algebraMap_smul]
    exact map_smul _ _ _

/-- **One chosen such isomorphism.**
`AlgebraicGeometry.exists_addEquiv_germ_smul_stalk_pullback_fiberι`
is existential — `Stacks.RingedSpace.pullbackStalkFormula`, which it rests on, is — so the
generator it produces downstairs is not a function of the element upstairs and two applications
at two points of the fibre give two unrelated witnesses. Fixing one choice makes it a function,
which is what the later paragraphs of Stacks Tag 0BD7 need: the germ of a *single* section must
generate at *every* point of the generic fibre. -/
noncomputable def stalkPullbackFiberιAddEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) (x₀ : f.fiber y) :
    grpStalk (f.fiber y).toRingedSpace
        ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀ ≃+
      grpStalk X.toRingedSpace L.val (((f.fiberι y).toLRSHom.toShHom).hom.base x₀) :=
  (exists_addEquiv_germ_smul_stalk_pullback_fiberι f h L x₀).choose

/-- `AlgebraicGeometry.stalkPullbackFiberιAddEquiv` carries the germ of the restriction of a
section `s` of `ℒ` to the germ of `s`. -/
theorem stalkPullbackFiberιAddEquiv_grpGerm {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) (x₀ : f.fiber y)
    (V : Opens X) (hx : ((f.fiberι y).toLRSHom.toShHom).hom.base x₀ ∈ V)
    (s : L.val.obj (op V)) :
    stalkPullbackFiberιAddEquiv f h L x₀
        (grpGerm (f.fiber y).toRingedSpace
          ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀
          ((opensMap (f.fiberι y).toLRSHom.toShHom).obj V) hx
          (pullbackUnit (f.fiberι y).toLRSHom.toShHom L (op V) s)) =
      grpGerm X.toRingedSpace L.val (((f.fiberι y).toLRSHom.toShHom).hom.base x₀) V hx s :=
  (exists_addEquiv_germ_smul_stalk_pullback_fiberι f h L x₀).choose_spec.1 V hx s

/-- `AlgebraicGeometry.stalkPullbackFiberιAddEquiv` is semilinear along the stalk map of the
fibre inclusion. -/
theorem stalkPullbackFiberιAddEquiv_stalkMap_smul {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) (x₀ : f.fiber y)
    (c : ringStalk X.toRingedSpace (((f.fiberι y).toLRSHom.toShHom).hom.base x₀))
    (v : grpStalk (f.fiber y).toRingedSpace
      ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀) :
    stalkPullbackFiberιAddEquiv f h L x₀
        (((((f.fiberι y).toLRSHom.toShHom).hom.stalkMap x₀).hom c) • v) =
      c • stalkPullbackFiberιAddEquiv f h L x₀ v :=
  (exists_addEquiv_germ_smul_stalk_pullback_fiberι f h L x₀).choose_spec.2 c v

/-- **The module-level half of the first paragraph of Stacks Tag 0BD7.** Over a point `y` of
the target whose local ring is a field, the stalk of the restriction of `ℒ` to the fibre `X_y`
at a point `x₀` of that fibre is the stalk of `ℒ` itself at the image of `x₀`, by an additive
isomorphism carrying the germ of a restricted section to the germ of that section.

The germ law alone, from
`AlgebraicGeometry.exists_addEquiv_germ_smul_stalk_pullback_fiberι`. -/
theorem exists_addEquiv_stalk_pullback_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) (x₀ : f.fiber y) :
    ∃ e : grpStalk (f.fiber y).toRingedSpace
        ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀ ≃+
      grpStalk X.toRingedSpace L.val ((f.fiberι y).base x₀),
      ∀ (V : Opens X) (hx : (f.fiberι y).base x₀ ∈ V) (s : L.val.obj (op V)),
        e (grpGerm (f.fiber y).toRingedSpace
            ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀
            ((opensMap (f.fiberι y).toLRSHom.toShHom).obj V) hx
            (pullbackUnit (f.fiberι y).toLRSHom.toShHom L (op V) s)) =
          grpGerm X.toRingedSpace L.val ((f.fiberι y).base x₀) V hx s :=
  ⟨stalkPullbackFiberιAddEquiv f h L x₀, stalkPullbackFiberιAddEquiv_grpGerm f h L x₀⟩

/-- **The generic fibre of a morphism to an integral scheme has the module stalks of the
source.** The case of `AlgebraicGeometry.exists_addEquiv_stalk_pullback_fiberι` that the first
paragraph of Stacks Tag 0BD7 uses: over the generic point of an integral target the hypothesis
on the local ring is automatic, the local ring there being the function field. -/
theorem exists_addEquiv_stalk_pullback_fiberι_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    (x₀ : f.fiber (genericPoint Y)) :
    ∃ e : grpStalk (f.fiber (genericPoint Y)).toRingedSpace
        ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀ ≃+
      grpStalk X.toRingedSpace L.val ((f.fiberι (genericPoint Y)).base x₀),
      ∀ (V : Opens X) (hx : (f.fiberι (genericPoint Y)).base x₀ ∈ V) (s : L.val.obj (op V)),
        e (grpGerm (f.fiber (genericPoint Y)).toRingedSpace
            ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀
            ((opensMap (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj V) hx
            (pullbackUnit (f.fiberι (genericPoint Y)).toLRSHom.toShHom L (op V) s)) =
          grpGerm X.toRingedSpace L.val ((f.fiberι (genericPoint Y)).base x₀) V hx s :=
  exists_addEquiv_stalk_pullback_fiberι f (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀

/-- **The same identification, with its scalar law.** The additive isomorphism of
`AlgebraicGeometry.exists_addEquiv_stalk_pullback_fiberι` is *semilinear* along the bijective
ring map `𝒪_{X, x} ⟶ 𝒪_{X_y, x₀}`: scaling by `c` upstairs and by its image downstairs agree.

This is not extra mathematics — `Stacks.RingedSpace.pullbackStalkFormula` already produces a
`≃ₗ` over the fibre's local ring, and the additive form above simply discards it. The scalar law
is what lets a *generator* be carried across, which an additive bijection alone cannot do, and
that is exactly what the first paragraph of Stacks Tag 0BD7 needs: it has a trivializing section
on the generic fibre and must conclude that its germ generates `ℒ` at the generic point.

The base point is written `((f.fiberι y).toLRSHom.toShHom).hom.base x₀` throughout rather than
`(f.fiberι y).base x₀`. The two are the same term — `rfl`, with a negative control in the same
shape that fires — but only the former finds the module structure on the tensor product that
`pullbackStalkFormula` states, instance search matching syntactically.

The scalar law alone, from
`AlgebraicGeometry.exists_addEquiv_germ_smul_stalk_pullback_fiberι`. -/
theorem exists_addEquiv_smul_stalk_pullback_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) (x₀ : f.fiber y) :
    ∃ e : grpStalk (f.fiber y).toRingedSpace
        ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀ ≃+
      grpStalk X.toRingedSpace L.val (((f.fiberι y).toLRSHom.toShHom).hom.base x₀),
      ∀ (c : ringStalk X.toRingedSpace (((f.fiberι y).toLRSHom.toShHom).hom.base x₀))
        (v : grpStalk (f.fiber y).toRingedSpace
          ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀),
        e (((((f.fiberι y).toLRSHom.toShHom).hom.stalkMap x₀).hom c) • v) = c • e v :=
  ⟨stalkPullbackFiberιAddEquiv f h L x₀, stalkPullbackFiberιAddEquiv_stalkMap_smul f h L x₀⟩

/-- **A generator on the fibre is a generator on the source, and the generator is the image of
the given element.** If `v` generates the stalk of `ℒ|_{X_y}` at a point of the fibre, then `e v`
generates the stalk of `ℒ` at the image point, for *any* `e` satisfying the scalar law.

`e` is a parameter rather than an existential witness: the later paragraphs of Stacks Tag 0BD7
need the generator to be a function of `v`, so that one section of `ℒ|_{X_ξ}` generating at every
point of the generic fibre yields *one* family of generators and not a family of unrelated
witnesses.

Both the bijection and its scalar law are needed: the bijection carries the generated submodule
onto everything, and the scalar law together with *surjectivity of the stalk map* — which is
part of `AlgebraicGeometry.bijective_stalkMap_fiberι_of_mem` — turns each coefficient upstairs
into a coefficient downstairs. -/
theorem span_eq_top_grpStalk_of_addEquiv_smul {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) (x₀ : f.fiber y)
    (e : grpStalk (f.fiber y).toRingedSpace
        ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀ ≃+
      grpStalk X.toRingedSpace L.val (((f.fiberι y).toLRSHom.toShHom).hom.base x₀))
    (hsmul : ∀ (c : ringStalk X.toRingedSpace (((f.fiberι y).toLRSHom.toShHom).hom.base x₀))
        (v : grpStalk (f.fiber y).toRingedSpace
          ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀),
        e (((((f.fiberι y).toLRSHom.toShHom).hom.stalkMap x₀).hom c) • v) = c • e v)
    (v : grpStalk (f.fiber y).toRingedSpace
      ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀)
    (hv : Submodule.span (ringStalk (f.fiber y).toRingedSpace x₀) {v} = ⊤) :
    Submodule.span (ringStalk X.toRingedSpace
      (((f.fiberι y).toLRSHom.toShHom).hom.base x₀)) {e v} = ⊤ := by
  refine eq_top_iff.2 fun w _ => ?_
  obtain ⟨u, hu⟩ := e.surjective w
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hv ▸ Submodule.mem_top (x := u))
  obtain ⟨c, hc⟩ := (bijective_stalkMap_fiberι_of_mem f h x₀).2 a
  -- `bijective_stalkMap_fiberι_of_mem` states the stalk map at the scheme-level spelling and
  -- `hsmul` at the `toShHom` one; the two are the same term, so `hc` retypes by `rfl`.
  have hca : ((((f.fiberι y).toLRSHom.toShHom).hom.stalkMap x₀).hom c) = a := hc
  refine Submodule.mem_span_singleton.2 ⟨c, ?_⟩
  rw [← hsmul c v, hca, ha, hu]

/-- The chosen-isomorphism case of `AlgebraicGeometry.span_eq_top_grpStalk_of_addEquiv_smul`: a
generator of the fibre stalk is carried to a generator of `ℒ`'s stalk by
`AlgebraicGeometry.stalkPullbackFiberιAddEquiv`. This is the `∀`-form of the statement, with the
generator named. -/
theorem span_eq_top_grpStalk_stalkPullbackFiberιAddEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) (x₀ : f.fiber y)
    (v : grpStalk (f.fiber y).toRingedSpace
      ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀)
    (hv : Submodule.span (ringStalk (f.fiber y).toRingedSpace x₀) {v} = ⊤) :
    Submodule.span (ringStalk X.toRingedSpace
        (((f.fiberι y).toLRSHom.toShHom).hom.base x₀))
      {stalkPullbackFiberιAddEquiv f h L x₀ v} = ⊤ :=
  span_eq_top_grpStalk_of_addEquiv_smul f h L x₀ _
    (stalkPullbackFiberιAddEquiv_stalkMap_smul f h L x₀) v hv

/-- **The generator is the germ of the section.** If the germ at `x₀` of the restriction of a
section `s` of `ℒ` to the fibre generates the fibre stalk, then the germ of `s` at the image of
`x₀` generates the stalk of `ℒ` there.

This is what the later paragraphs of Stacks Tag 0BD7 ask for: the obligation is about the germ
of the *given* meromorphic section, and no existential generator can discharge it. -/
theorem span_eq_top_grpGerm_of_span_eq_top_grpGerm_pullbackUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    {y : Y} (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) (x₀ : f.fiber y)
    (V : Opens X) (hx : ((f.fiberι y).toLRSHom.toShHom).hom.base x₀ ∈ V)
    (s : L.val.obj (op V))
    (hv : Submodule.span (ringStalk (f.fiber y).toRingedSpace x₀)
        {grpGerm (f.fiber y).toRingedSpace
          ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀
          ((opensMap (f.fiberι y).toLRSHom.toShHom).obj V) hx
          (pullbackUnit (f.fiberι y).toLRSHom.toShHom L (op V) s)} = ⊤) :
    Submodule.span (ringStalk X.toRingedSpace
        (((f.fiberι y).toLRSHom.toShHom).hom.base x₀))
      {grpGerm X.toRingedSpace L.val (((f.fiberι y).toLRSHom.toShHom).hom.base x₀) V hx s}
      = ⊤ := by
  rw [← stalkPullbackFiberιAddEquiv_grpGerm f h L x₀ V hx s]
  exact span_eq_top_grpStalk_stalkPullbackFiberιAddEquiv f h L x₀ _ hv

/-- **A generator on the fibre is a generator on the source.** The existential form of
`AlgebraicGeometry.span_eq_top_grpStalk_stalkPullbackFiberιAddEquiv`, which is what an earlier
consumer asks for. -/
theorem exists_span_eq_top_stalk_pullback_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) {y : Y}
    (h : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥)
    (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) (x₀ : f.fiber y)
    (v : grpStalk (f.fiber y).toRingedSpace
      ((pullbackFunctor (f.fiberι y).toLRSHom.toShHom).obj L).val x₀)
    (hv : Submodule.span (ringStalk (f.fiber y).toRingedSpace x₀) {v} = ⊤) :
    ∃ m : grpStalk X.toRingedSpace L.val (((f.fiberι y).toLRSHom.toShHom).hom.base x₀),
      Submodule.span (ringStalk X.toRingedSpace
        (((f.fiberι y).toLRSHom.toShHom).hom.base x₀)) {m} = ⊤ :=
  ⟨_, span_eq_top_grpStalk_stalkPullbackFiberιAddEquiv f h L x₀ v hv⟩

/-- The generic-fibre case of `AlgebraicGeometry.exists_span_eq_top_stalk_pullback_fiberι`: for
a morphism to an integral scheme the hypothesis on the local ring is automatic, the local ring
at the generic point being the function field. This is the step of the first paragraph of Stacks
Tag 0BD7 that reads a trivialization on the generic fibre as a generator of `ℒ` at the generic
point. -/
theorem exists_span_eq_top_stalk_pullback_fiberι_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegral Y] (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))
    (x₀ : f.fiber (genericPoint Y))
    (v : grpStalk (f.fiber (genericPoint Y)).toRingedSpace
      ((pullbackFunctor (f.fiberι (genericPoint Y)).toLRSHom.toShHom).obj L).val x₀)
    (hv : Submodule.span (ringStalk (f.fiber (genericPoint Y)).toRingedSpace x₀) {v} = ⊤) :
    ∃ m : grpStalk X.toRingedSpace L.val
      (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀),
      Submodule.span (ringStalk X.toRingedSpace
        (((f.fiberι (genericPoint Y)).toLRSHom.toShHom).hom.base x₀)) {m} = ⊤ :=
  exists_span_eq_top_stalk_pullback_fiberι f (maximalIdeal_stalk_genericPoint_eq_bot Y) L x₀ v hv

end AlgebraicGeometry

end
