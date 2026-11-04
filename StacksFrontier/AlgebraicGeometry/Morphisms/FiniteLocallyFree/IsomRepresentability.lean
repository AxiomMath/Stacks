module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.AffineRepresentability
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.RelativeMorphismFunctor

/-!
# The relative isomorphism functor of two schemes over a base

Let `Z` and `X` be two schemes over a scheme `S`. The relative morphism functor `Mor_S(Z, X)` of
Stacks 0BL2 (`AlgebraicGeometry.relativeHom`) sends a scheme `T` over `S` to the morphisms
`Z ×_S T ⟶ X` over `S`. Composition of relative morphisms makes the four functors
`Mor_S(Z, X)`, `Mor_S(X, Z)`, `Mor_S(Z, Z)` and `Mor_S(X, X)` into the data of a square, and the
*relative isomorphism functor* `Isom_S(Z, X)` is the fibre product of that square over the pair
of identity sections: a section of it over `T` is a pair of relative morphisms, one in each
direction, whose two composites are the identities.

This file constructs that fibre product on the *representing objects*. Given representing
objects for the four relative morphism functors — which Stacks 0BL3
(`Stacks.Morphisms.relativeHom_representableBy_affineHom`) supplies whenever `Z ⟶ S` is finite
locally free and `X ⟶ S` is affine, and symmetrically — the fibre product
`Stacks.Morphisms.relativeIsomObj` of the square represents `Isom_S(Z, X)`, and
`Stacks.Morphisms.relativeIsomObjEquiv` is the representing bijection.

## Main definitions

* `Stacks.Morphisms.relativeMorId`: the identity relative morphism, the first projection of
  `Z ×_S T`.
* `Stacks.Morphisms.relativeMorComp`: composition of relative morphisms, `Z ×_S T ⟶ X` with
  `X ×_S T ⟶ Y` giving `Z ×_S T ⟶ Y`.
* `Stacks.Morphisms.IsRelativeMorInverse`: two relative morphisms in opposite directions are
  mutually inverse when both composites are the identity relative morphism.
* `Stacks.Morphisms.relativeMorIdSection`: the identity section of `Mor_S(Z, Z)`, read on a
  representing object.
* `Stacks.Morphisms.relativeMorCompFst` and `Stacks.Morphisms.relativeMorCompSnd`: the two
  components of the comparison
  `Mor_S(Z, X) ×_S Mor_S(X, Z) ⟶ Mor_S(Z, Z) ×_S Mor_S(X, X)`, read on representing objects.
* `Stacks.Morphisms.relativeIsomObj`: the fibre product of the square, the object representing
  `Isom_S(Z, X)`.
* `Stacks.Morphisms.relativeIsomFst` and `Stacks.Morphisms.relativeIsomSnd`: the two relative
  morphisms a morphism into the fibre product names.
* `Stacks.Morphisms.relativeMorOverBase` and `Stacks.Morphisms.relativeMorOfOverBase`: a
  relative morphism read as a morphism of the two base changes over the test object, and back.

## Main results

* `Stacks.Morphisms.relativeIsomObjEquiv`: the morphisms `T ⟶ Isom_S(Z, X)` over `S` are exactly
  the mutually inverse pairs of relative morphisms at `T`, and
  `Stacks.Morphisms.relativeIsomObjEquivIso` restates that as: they are exactly the isomorphisms
  `Z ×_S T ≅ X ×_S T` over `T`.
* `Stacks.Morphisms.relativeIsomFst_comp` and `Stacks.Morphisms.relativeIsomSnd_comp`: the
  bijection is natural in `T`, each component being carried to its base change.
* `Stacks.Morphisms.relativeIsomObjLeftIso`: the scheme underlying the fibre product is a fibre
  product of schemes, which is what bounds its size.
* `Stacks.Morphisms.exists_representableBy_four`: for two finite locally free schemes over `S`
  all four relative morphism functors are representable, by Stacks 0BL3.
* `Stacks.Morphisms.relativeMorEquivOverBase`: the relative morphisms at `T` are exactly the
  morphisms `Z ×_S T ⟶ X ×_S T` over `T`, with
  `Stacks.Morphisms.relativeMorOverBase_relativeMorId` and
  `Stacks.Morphisms.relativeMorOverBase_relativeMorComp` saying that the identification carries
  the identity and the composition of relative morphisms to the identity and the composition of
  the slice.
* `Stacks.Morphisms.isRelativeMorInverse_iff`,
  `Stacks.Morphisms.isIso_relativeMorOverBase` and
  `Stacks.Morphisms.isRelativeMorInverse_relativeMorOfOverBase`: **a mutually inverse pair of
  relative morphisms is the same thing as an isomorphism of the two base changes over the test
  object**. This is the dictionary that identifies the fibre product constructed here with the
  functor of isomorphisms of two covers, which is the form criterion (2) of Stacks 045G asks
  for.

## Implementation notes

Everything is stated with the sections of the relative morphism functor written as
`(AlgebraicGeometry.relativeHom Z X).obj (Opposite.op T)` rather than as the morphisms
`Z ⨯ T ⟶ X` that they definitionally are, and the restriction maps are written as
`(AlgebraicGeometry.relativeHom Z X).map`. The two spellings are interchangeable by `rfl`, but
only the first makes the types match those of
`CategoryTheory.Functor.RepresentableBy.homEquiv` syntactically, so that the naturality equation
`CategoryTheory.Functor.RepresentableBy.homEquiv_comp` can be rewritten with.

The passage between the two spellings is made by the two identity functions
`Stacks.Morphisms.toMor` and `Stacks.Morphisms.ofMor` rather than by a type ascription. A type
ascription is enough to elaborate a term, but not to rewrite in one: the identification
`(AlgebraicGeometry.relativeHom Z X).obj (Opposite.op T) = (Z ⨯ T ⟶ X)` unfolds
`CategoryTheory.Limits.prod`, whose definition passes through `getLimitCone`, and that definition
is not exposed, so a goal mixing the two spellings is not type-correct at the `implicit`
transparency level that `rw` and `simp` work at. Naming the two coercions keeps every goal in one
spelling, and `Stacks.Morphisms.toMor_map`, `Stacks.Morphisms.toMor_relativeMorId` and
`Stacks.Morphisms.toMor_relativeMorComp` — all of them `rfl` — move a statement from the first
spelling to the second.

For the same reason `Stacks.Morphisms.relativeIsomObj` and
`Stacks.Morphisms.relativeIsomToPair` carry `implicit_reducible`: a morphism into
`Stacks.Morphisms.relativeIsomObj` has to be recognised as a morphism into the fibre product
before `CategoryTheory.Limits.pullback.condition` can be applied to it.

The identity relative morphism at `T` is the first projection `Z ×_S T ⟶ Z`, and
`Stacks.Morphisms.relativeMorComp_id_left` and
`Stacks.Morphisms.relativeMorComp_id_right` say that it is a two-sided identity for composition.
So an inverse pair is literally a pair whose composites are the identities, and no separate
`IsIso` condition appears; this is what makes the condition cut out by a fibre product.

The right-hand leg of the square is taken at the terminal object of the category of schemes over
`S`, which is `S` itself, rather than as a natural family of identity sections: the family
`Stacks.Morphisms.relativeMorIdSection` is constant in the sense of
`Stacks.Morphisms.comp_relativeMorIdSection`, so it factors through the terminal object, and
taking the fibre product against the terminal object is what makes the fibre product a single
object rather than a subfunctor.

## References

* [Stacks Project, Tag 0BL2](https://stacks.math.columbia.edu/tag/0BL2)
* [Stacks Project, Tag 0BL3](https://stacks.math.columbia.edu/tag/0BL3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Morphisms

variable {S : Scheme.{u}}

/-! ### Identity and composition of relative morphisms -/

section Comp

variable {Z X Y : Over S}

/-- A section of `Mor_S(Z, X)` over `T`, read as the morphism `Z ×_S T ⟶ X` over `S` that it
definitionally is. -/
def toMor {T : Over S} (a : (relativeHom Z X).obj (op T)) : Z ⨯ T ⟶ X := a

/-- A morphism `Z ×_S T ⟶ X` over `S`, read as the section of `Mor_S(Z, X)` over `T` that it
definitionally is. -/
def ofMor {T : Over S} (a : Z ⨯ T ⟶ X) : (relativeHom Z X).obj (op T) := a

/-- Reading a morphism as a section and back recovers the morphism. -/
@[simp]
theorem toMor_ofMor {T : Over S} (a : Z ⨯ T ⟶ X) : toMor (ofMor a) = a := rfl

/-- Reading a section as a morphism and back recovers the section. -/
@[simp]
theorem ofMor_toMor {T : Over S} (a : (relativeHom Z X).obj (op T)) : ofMor (toMor a) = a := rfl

/-- A section of `Mor_S(Z, X)` is determined by the morphism `Z ×_S T ⟶ X` it is. -/
theorem toMor_injective {T : Over S} :
    Function.Injective (toMor (Z := Z) (X := X) (T := T)) := fun a b h => by
  rw [← ofMor_toMor a, ← ofMor_toMor b, h]

/-- The restriction maps of `Mor_S(Z, X)` are base change along the morphism of the base. -/
@[simp]
theorem toMor_map {T T' : Over S} (h : T' ⟶ T) (a : (relativeHom Z X).obj (op T)) :
    toMor ((relativeHom Z X).map h.op a) = prod.map (𝟙 Z) h ≫ toMor a := rfl

/-- **The identity relative morphism.** The section of `Mor_S(Z, Z)` over `T` given by the first
projection of `Z ×_S T`. -/
def relativeMorId (Z T : Over S) : (relativeHom Z Z).obj (op T) :=
  ofMor (prod.fst : Z ⨯ T ⟶ Z)

/-- The identity relative morphism is the first projection `Z ×_S T ⟶ Z`. -/
@[simp]
theorem toMor_relativeMorId (Z T : Over S) :
    toMor (relativeMorId Z T) = (prod.fst : Z ⨯ T ⟶ Z) := rfl

/-- **Composition of relative morphisms.** A section of `Mor_S(Z, X)` over `T` and a section of
`Mor_S(X, Y)` over `T` compose to a section of `Mor_S(Z, Y)` over `T`, by lifting the first
through the projection to `T` and following with the second. -/
def relativeMorComp {T : Over S} (a : (relativeHom Z X).obj (op T))
    (b : (relativeHom X Y).obj (op T)) : (relativeHom Z Y).obj (op T) :=
  ofMor (prod.lift (toMor a) prod.snd ≫ toMor b)

/-- The composite of two relative morphisms is the lift of the first through the projection to
`T`, followed by the second. -/
@[simp]
theorem toMor_relativeMorComp {T : Over S} (a : (relativeHom Z X).obj (op T))
    (b : (relativeHom X Y).obj (op T)) :
    toMor (relativeMorComp a b) = prod.lift (toMor a) prod.snd ≫ toMor b := rfl

/-- The identity relative morphism is a left identity for composition. -/
theorem relativeMorComp_id_left {T : Over S} (a : (relativeHom Z X).obj (op T)) :
    relativeMorComp (relativeMorId Z T) a = a :=
  toMor_injective (by simp)

/-- The identity relative morphism is a right identity for composition. -/
theorem relativeMorComp_id_right {T : Over S} (a : (relativeHom Z X).obj (op T)) :
    relativeMorComp a (relativeMorId X T) = a :=
  toMor_injective (by simp)

/-- The identity relative morphisms are compatible with base change. -/
theorem relativeMorId_map {T T' : Over S} (h : T' ⟶ T) :
    (relativeHom Z Z).map h.op (relativeMorId Z T) = relativeMorId Z T' :=
  toMor_injective (by
    rw [toMor_map, toMor_relativeMorId, toMor_relativeMorId]
    simp)

/-- Base change commutes past the lifting that defines composition of relative morphisms. -/
theorem prod_map_comp_lift {T T' : Over S} (h : T' ⟶ T) (a : Z ⨯ T ⟶ X) :
    prod.map (𝟙 Z) h ≫ prod.lift a (prod.snd : Z ⨯ T ⟶ T) =
      prod.lift (prod.map (𝟙 Z) h ≫ a) (prod.snd : Z ⨯ T' ⟶ T') ≫ prod.map (𝟙 X) h := by
  refine prod.hom_ext ?_ ?_ <;> simp

/-- Composition of relative morphisms is compatible with base change. -/
theorem relativeMorComp_map {T T' : Over S} (h : T' ⟶ T)
    (a : (relativeHom Z X).obj (op T)) (b : (relativeHom X Y).obj (op T)) :
    (relativeHom Z Y).map h.op (relativeMorComp a b) =
      relativeMorComp ((relativeHom Z X).map h.op a) ((relativeHom X Y).map h.op b) :=
  toMor_injective (by
    rw [toMor_map, toMor_relativeMorComp, toMor_relativeMorComp, toMor_map, toMor_map,
      ← Category.assoc, prod_map_comp_lift, Category.assoc])

/-- Two relative morphisms in opposite directions are *mutually inverse* when both composites
are the identity relative morphism. -/
def IsRelativeMorInverse {T : Over S} (a : (relativeHom Z X).obj (op T))
    (b : (relativeHom X Z).obj (op T)) : Prop :=
  relativeMorComp a b = relativeMorId Z T ∧ relativeMorComp b a = relativeMorId X T

end Comp

/-! ### Relative morphisms as morphisms of base changes -/

section OverBase

variable {Z X Y : Over S}

/-- **A relative morphism, read as a morphism of the two base changes over the test object.**
A section of `Mor_S(Z, X)` over `T` is a morphism `Z ×_S T ⟶ X` over `S`; lifting it through the
projection to `T` makes it a morphism `Z ×_S T ⟶ X ×_S T` over `T`. -/
def relativeMorOverBase {T : Over S} (a : (relativeHom Z X).obj (op T)) :
    prodOverBase Z T ⟶ prodOverBase X T :=
  Over.homMk (prod.lift (toMor a) prod.snd) (by simp)

/-- The underlying morphism of `relativeMorOverBase a` is the lift of `a` through the projection
to `T`. -/
@[simp]
theorem relativeMorOverBase_left {T : Over S} (a : (relativeHom Z X).obj (op T)) :
    (relativeMorOverBase a).left = prod.lift (toMor a) prod.snd := rfl

/-- The identity relative morphism is the identity morphism of the base change. -/
@[simp]
theorem relativeMorOverBase_relativeMorId (Z T : Over S) :
    relativeMorOverBase (relativeMorId Z T) = 𝟙 (prodOverBase Z T) := by
  refine Over.OverMorphism.ext ?_
  simp

/-- Composition of relative morphisms is composition of the morphisms of base changes. -/
@[simp]
theorem relativeMorOverBase_relativeMorComp {T : Over S} (a : (relativeHom Z X).obj (op T))
    (b : (relativeHom X Y).obj (op T)) :
    relativeMorOverBase (relativeMorComp a b) =
      relativeMorOverBase a ≫ relativeMorOverBase b := by
  refine Over.OverMorphism.ext ?_
  rw [Over.comp_left, relativeMorOverBase_left, relativeMorOverBase_left,
    relativeMorOverBase_left, toMor_relativeMorComp]
  refine prod.hom_ext ?_ ?_ <;> simp

/-- A relative morphism is determined by the morphism of base changes it induces. -/
theorem relativeMorOverBase_injective {T : Over S} :
    Function.Injective (relativeMorOverBase (Z := Z) (X := X) (T := T)) := by
  intro a b h
  refine toMor_injective ?_
  have h' : (relativeMorOverBase a).left ≫ prod.fst =
      (relativeMorOverBase b).left ≫ prod.fst := by rw [h]
  simpa using h'

/-- **A morphism of the two base changes over the test object, read as a relative morphism.**
Composing with the projection to `X` forgets the second component, which the morphism being over
`T` determines. -/
def relativeMorOfOverBase {T : Over S} (e : prodOverBase Z T ⟶ prodOverBase X T) :
    (relativeHom Z X).obj (op T) :=
  ofMor (e.left ≫ prod.fst)

/-- A morphism of base changes over `T` is recovered from the relative morphism it determines. -/
@[simp]
theorem relativeMorOverBase_relativeMorOfOverBase {T : Over S}
    (e : prodOverBase Z T ⟶ prodOverBase X T) :
    relativeMorOverBase (relativeMorOfOverBase e) = e := by
  refine Over.OverMorphism.ext ?_
  rw [relativeMorOverBase_left, relativeMorOfOverBase, toMor_ofMor]
  refine prod.hom_ext ?_ ?_
  · simp
  · rw [prod.lift_snd]
    exact (Over.w e).symm

/-- A relative morphism is recovered from the morphism of base changes it induces. -/
@[simp]
theorem relativeMorOfOverBase_relativeMorOverBase {T : Over S}
    (a : (relativeHom Z X).obj (op T)) :
    relativeMorOfOverBase (relativeMorOverBase a) = a := by
  rw [relativeMorOfOverBase, relativeMorOverBase_left, prod.lift_fst, ofMor_toMor]

/-- **The relative morphisms are exactly the morphisms of the two base changes over the test
object.** -/
def relativeMorEquivOverBase (Z X T : Over S) :
    (relativeHom Z X).obj (op T) ≃ (prodOverBase Z T ⟶ prodOverBase X T) where
  toFun := relativeMorOverBase
  invFun := relativeMorOfOverBase
  left_inv := relativeMorOfOverBase_relativeMorOverBase
  right_inv := relativeMorOverBase_relativeMorOfOverBase

/-- **A mutually inverse pair of relative morphisms is a pair of mutually inverse morphisms of
the base changes over the test object.** -/
theorem isRelativeMorInverse_iff {T : Over S} (a : (relativeHom Z X).obj (op T))
    (b : (relativeHom X Z).obj (op T)) :
    IsRelativeMorInverse a b ↔
      (relativeMorOverBase a ≫ relativeMorOverBase b = 𝟙 (prodOverBase Z T) ∧
        relativeMorOverBase b ≫ relativeMorOverBase a = 𝟙 (prodOverBase X T)) := by
  rw [IsRelativeMorInverse, ← relativeMorOverBase_relativeMorComp,
    ← relativeMorOverBase_relativeMorComp, ← relativeMorOverBase_relativeMorId,
    ← relativeMorOverBase_relativeMorId]
  exact and_congr relativeMorOverBase_injective.eq_iff.symm
    relativeMorOverBase_injective.eq_iff.symm

/-- **The morphism of base changes attached to a mutually inverse pair is an isomorphism.** -/
theorem isIso_relativeMorOverBase {T : Over S} {a : (relativeHom Z X).obj (op T)}
    {b : (relativeHom X Z).obj (op T)} (hab : IsRelativeMorInverse a b) :
    IsIso (relativeMorOverBase a) :=
  ⟨relativeMorOverBase b, ((isRelativeMorInverse_iff a b).1 hab).1,
    ((isRelativeMorInverse_iff a b).1 hab).2⟩

/-- **An isomorphism of the two base changes over the test object is a mutually inverse pair of
relative morphisms.** -/
theorem isRelativeMorInverse_relativeMorOfOverBase {T : Over S}
    (e : prodOverBase Z T ⟶ prodOverBase X T) [IsIso e] :
    IsRelativeMorInverse (relativeMorOfOverBase e) (relativeMorOfOverBase (inv e)) := by
  rw [isRelativeMorInverse_iff, relativeMorOverBase_relativeMorOfOverBase,
    relativeMorOverBase_relativeMorOfOverBase]
  exact ⟨IsIso.hom_inv_id e, IsIso.inv_hom_id e⟩

end OverBase

/-! ### The identity section on a representing object -/

section IdSection

variable {Z V : Over S} (e : (relativeHom Z Z).RepresentableBy V)

/-- **The identity section of `Mor_S(Z, Z)`**, read on a representing object: the morphism
`T ⟶ V` naming the identity relative morphism at `T`. -/
def relativeMorIdSection (T : Over S) : T ⟶ V :=
  e.homEquiv.symm (relativeMorId Z T)

/-- The identity sections are compatible with base change: composing the identity section at `T`
with a morphism `T' ⟶ T` gives the identity section at `T'`. -/
theorem comp_relativeMorIdSection {T T' : Over S} (h : T' ⟶ T) :
    h ≫ relativeMorIdSection e T = relativeMorIdSection e T' := by
  rw [relativeMorIdSection, e.comp_homEquiv_symm, relativeMorIdSection, relativeMorId_map]

/-- The morphism naming the identity relative morphism names the identity relative morphism. -/
@[simp]
theorem homEquiv_relativeMorIdSection (T : Over S) :
    e.homEquiv (relativeMorIdSection e T) = relativeMorId Z T := by
  rw [relativeMorIdSection, Equiv.apply_symm_apply]

end IdSection

/-! ### The square and its fibre product -/

section Isom

variable {Z X W₁ W₂ V₁ V₂ : Over S}
  (e₁ : (relativeHom Z X).RepresentableBy W₁)
  (e₂ : (relativeHom X Z).RepresentableBy W₂)
  (e₃ : (relativeHom Z Z).RepresentableBy V₁)
  (e₄ : (relativeHom X X).RepresentableBy V₂)

/-- The universal relative morphism `Z ⟶ X` over the pair object `Mor_S(Z, X) ×_S Mor_S(X, Z)`,
the one named by the first projection. -/
def relativeMorUnivFst : (relativeHom Z X).obj (op (W₁ ⨯ W₂)) :=
  e₁.homEquiv (prod.fst : (W₁ ⨯ W₂ : Over S) ⟶ W₁)

/-- The universal relative morphism `X ⟶ Z` over the pair object `Mor_S(Z, X) ×_S Mor_S(X, Z)`,
the one named by the second projection. -/
def relativeMorUnivSnd : (relativeHom X Z).obj (op (W₁ ⨯ W₂)) :=
  e₂.homEquiv (prod.snd : (W₁ ⨯ W₂ : Over S) ⟶ W₂)

/-- The restriction of the universal relative morphism `Z ⟶ X` along a morphism into the pair
object is the relative morphism that morphism's first component names. -/
theorem map_relativeMorUnivFst {T : Over S} (t : T ⟶ W₁ ⨯ W₂) :
    (relativeHom Z X).map t.op (relativeMorUnivFst e₁) = e₁.homEquiv (t ≫ prod.fst) :=
  (e₁.homEquiv_comp t _).symm

/-- The restriction of the universal relative morphism `X ⟶ Z` along a morphism into the pair
object is the relative morphism that morphism's second component names. -/
theorem map_relativeMorUnivSnd {T : Over S} (t : T ⟶ W₁ ⨯ W₂) :
    (relativeHom X Z).map t.op (relativeMorUnivSnd e₂) = e₂.homEquiv (t ≫ prod.snd) :=
  (e₂.homEquiv_comp t _).symm

/-- The first component of the comparison
`Mor_S(Z, X) ×_S Mor_S(X, Z) ⟶ Mor_S(Z, Z) ×_S Mor_S(X, X)`, read on representing objects: it
names the composite of the two universal relative morphisms in the order `Z ⟶ X ⟶ Z`. -/
def relativeMorCompFst : (W₁ ⨯ W₂ : Over S) ⟶ V₁ :=
  e₃.homEquiv.symm (relativeMorComp (relativeMorUnivFst e₁) (relativeMorUnivSnd e₂))

/-- The second component of the comparison
`Mor_S(Z, X) ×_S Mor_S(X, Z) ⟶ Mor_S(Z, Z) ×_S Mor_S(X, X)`, read on representing objects: it
names the composite of the two universal relative morphisms in the order `X ⟶ Z ⟶ X`. -/
def relativeMorCompSnd : (W₁ ⨯ W₂ : Over S) ⟶ V₂ :=
  e₄.homEquiv.symm (relativeMorComp (relativeMorUnivSnd e₂) (relativeMorUnivFst e₁))

/-- A morphism into the pair object followed by the first component of the comparison names the
composite of the two relative morphisms its components name. -/
theorem homEquiv_comp_relativeMorCompFst {T : Over S} (t : T ⟶ W₁ ⨯ W₂) :
    e₃.homEquiv (t ≫ relativeMorCompFst e₁ e₂ e₃) =
      relativeMorComp (e₁.homEquiv (t ≫ prod.fst)) (e₂.homEquiv (t ≫ prod.snd)) := by
  rw [e₃.homEquiv_comp, relativeMorCompFst, Equiv.apply_symm_apply, relativeMorComp_map,
    map_relativeMorUnivFst, map_relativeMorUnivSnd]

/-- A morphism into the pair object followed by the second component of the comparison names the
composite of the two relative morphisms its components name, in the other order. -/
theorem homEquiv_comp_relativeMorCompSnd {T : Over S} (t : T ⟶ W₁ ⨯ W₂) :
    e₄.homEquiv (t ≫ relativeMorCompSnd e₁ e₂ e₄) =
      relativeMorComp (e₂.homEquiv (t ≫ prod.snd)) (e₁.homEquiv (t ≫ prod.fst)) := by
  rw [e₄.homEquiv_comp, relativeMorCompSnd, Equiv.apply_symm_apply, relativeMorComp_map,
    map_relativeMorUnivSnd, map_relativeMorUnivFst]

/-- **The object representing the relative isomorphism functor.** The fibre product of the
comparison `Mor_S(Z, X) ×_S Mor_S(X, Z) ⟶ Mor_S(Z, Z) ×_S Mor_S(X, X)` against the pair of
identity sections at the terminal object. -/
@[implicit_reducible]
def relativeIsomObj : Over S :=
  pullback (prod.lift (relativeMorCompFst e₁ e₂ e₃) (relativeMorCompSnd e₁ e₂ e₄))
    (prod.lift (relativeMorIdSection e₃ (⊤_ (Over S)))
      (relativeMorIdSection e₄ (⊤_ (Over S))))

/-- The morphism into the pair object underlying a morphism into the fibre product. -/
@[implicit_reducible]
def relativeIsomToPair {T : Over S} (t : T ⟶ relativeIsomObj e₁ e₂ e₃ e₄) : T ⟶ W₁ ⨯ W₂ :=
  t ≫ pullback.fst _ _

/-- The first component of a morphism `T ⟶ Isom_S(Z, X)`: the relative morphism `Z ⟶ X` it
names. -/
def relativeIsomFst {T : Over S} (t : T ⟶ relativeIsomObj e₁ e₂ e₃ e₄) :
    (relativeHom Z X).obj (op T) :=
  e₁.homEquiv (relativeIsomToPair e₁ e₂ e₃ e₄ t ≫ prod.fst)

/-- The second component of a morphism `T ⟶ Isom_S(Z, X)`: the relative morphism `X ⟶ Z` it
names. -/
def relativeIsomSnd {T : Over S} (t : T ⟶ relativeIsomObj e₁ e₂ e₃ e₄) :
    (relativeHom X Z).obj (op T) :=
  e₂.homEquiv (relativeIsomToPair e₁ e₂ e₃ e₄ t ≫ prod.snd)

/-- A morphism into the pair object satisfies the fibre product condition exactly when the two
relative morphisms its components name are mutually inverse. -/
private theorem comp_lift_eq_iff_isRelativeMorInverse {T : Over S} (t : T ⟶ W₁ ⨯ W₂)
    (s : T ⟶ ⊤_ (Over S)) :
    t ≫ prod.lift (relativeMorCompFst e₁ e₂ e₃) (relativeMorCompSnd e₁ e₂ e₄) =
        s ≫ prod.lift (relativeMorIdSection e₃ (⊤_ (Over S)))
          (relativeMorIdSection e₄ (⊤_ (Over S))) ↔
      IsRelativeMorInverse (e₁.homEquiv (t ≫ prod.fst)) (e₂.homEquiv (t ≫ prod.snd)) := by
  rw [prod.hom_ext_iff, IsRelativeMorInverse]
  simp only [Category.assoc, prod.lift_fst, prod.lift_snd, comp_relativeMorIdSection]
  rw [← e₃.homEquiv.injective.eq_iff, ← e₄.homEquiv.injective.eq_iff,
    homEquiv_comp_relativeMorCompFst, homEquiv_comp_relativeMorCompSnd,
    homEquiv_relativeMorIdSection, homEquiv_relativeMorIdSection]

/-- The two relative morphisms a morphism `T ⟶ Isom_S(Z, X)` names are mutually inverse: that is
the fibre product condition, read through the representing bijections. -/
theorem isRelativeMorInverse_relativeIsom {T : Over S} (t : T ⟶ relativeIsomObj e₁ e₂ e₃ e₄) :
    IsRelativeMorInverse (relativeIsomFst e₁ e₂ e₃ e₄ t) (relativeIsomSnd e₁ e₂ e₃ e₄ t) :=
  (comp_lift_eq_iff_isRelativeMorInverse e₁ e₂ e₃ e₄ _ (t ≫ pullback.snd _ _)).1 (by
    rw [relativeIsomToPair, Category.assoc, Category.assoc, pullback.condition])

/-- The morphism `T ⟶ Isom_S(Z, X)` named by a mutually inverse pair of relative morphisms. -/
def relativeIsomLift {T : Over S} (a : (relativeHom Z X).obj (op T))
    (b : (relativeHom X Z).obj (op T)) (hab : IsRelativeMorInverse a b) :
    T ⟶ relativeIsomObj e₁ e₂ e₃ e₄ :=
  pullback.lift (prod.lift (e₁.homEquiv.symm a) (e₂.homEquiv.symm b)) (terminal.from T) (by
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.lift_fst, Category.assoc, prod.lift_fst,
        comp_relativeMorIdSection]
      refine e₃.homEquiv.injective ?_
      rw [homEquiv_comp_relativeMorCompFst, homEquiv_relativeMorIdSection, prod.lift_fst,
        prod.lift_snd, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hab.1
    · rw [Category.assoc, prod.lift_snd, Category.assoc, prod.lift_snd,
        comp_relativeMorIdSection]
      refine e₄.homEquiv.injective ?_
      rw [homEquiv_comp_relativeMorCompSnd, homEquiv_relativeMorIdSection, prod.lift_fst,
        prod.lift_snd, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hab.2)

/-- The morphism into the pair object underlying the lift of a mutually inverse pair is the pair
of the two naming morphisms. -/
theorem relativeIsomToPair_relativeIsomLift {T : Over S} (a : (relativeHom Z X).obj (op T))
    (b : (relativeHom X Z).obj (op T)) (hab : IsRelativeMorInverse a b) :
    relativeIsomToPair e₁ e₂ e₃ e₄ (relativeIsomLift e₁ e₂ e₃ e₄ a b hab) =
      prod.lift (e₁.homEquiv.symm a) (e₂.homEquiv.symm b) :=
  pullback.lift_fst _ _ _

/-- The first component of the lift of a mutually inverse pair `(a, b)` is `a`. -/
@[simp]
theorem relativeIsomFst_relativeIsomLift {T : Over S} (a : (relativeHom Z X).obj (op T))
    (b : (relativeHom X Z).obj (op T)) (hab : IsRelativeMorInverse a b) :
    relativeIsomFst e₁ e₂ e₃ e₄ (relativeIsomLift e₁ e₂ e₃ e₄ a b hab) = a := by
  rw [relativeIsomFst, relativeIsomToPair_relativeIsomLift, prod.lift_fst,
    Equiv.apply_symm_apply]

/-- The second component of the lift of a mutually inverse pair `(a, b)` is `b`. -/
@[simp]
theorem relativeIsomSnd_relativeIsomLift {T : Over S} (a : (relativeHom Z X).obj (op T))
    (b : (relativeHom X Z).obj (op T)) (hab : IsRelativeMorInverse a b) :
    relativeIsomSnd e₁ e₂ e₃ e₄ (relativeIsomLift e₁ e₂ e₃ e₄ a b hab) = b := by
  rw [relativeIsomSnd, relativeIsomToPair_relativeIsomLift, prod.lift_snd,
    Equiv.apply_symm_apply]

/-- A morphism into the fibre product is determined by the two relative morphisms it names. -/
theorem relativeIsom_hom_ext {T : Over S} {t t' : T ⟶ relativeIsomObj e₁ e₂ e₃ e₄}
    (hfst : relativeIsomFst e₁ e₂ e₃ e₄ t = relativeIsomFst e₁ e₂ e₃ e₄ t')
    (hsnd : relativeIsomSnd e₁ e₂ e₃ e₄ t = relativeIsomSnd e₁ e₂ e₃ e₄ t') :
    t = t' := by
  rw [relativeIsomFst, relativeIsomFst] at hfst
  rw [relativeIsomSnd, relativeIsomSnd] at hsnd
  exact pullback.hom_ext
    (prod.hom_ext (e₁.homEquiv.injective hfst) (e₂.homEquiv.injective hsnd))
    (terminal.hom_ext _ _)

/-- **The fibre product represents the relative isomorphism functor.** The morphisms
`T ⟶ Isom_S(Z, X)` over `S` are exactly the mutually inverse pairs of relative morphisms at
`T`. -/
def relativeIsomObjEquiv (T : Over S) :
    (T ⟶ relativeIsomObj e₁ e₂ e₃ e₄) ≃
      {p : (relativeHom Z X).obj (op T) × (relativeHom X Z).obj (op T) //
        IsRelativeMorInverse p.1 p.2} where
  toFun t := ⟨(relativeIsomFst e₁ e₂ e₃ e₄ t, relativeIsomSnd e₁ e₂ e₃ e₄ t),
    isRelativeMorInverse_relativeIsom e₁ e₂ e₃ e₄ t⟩
  invFun p := relativeIsomLift e₁ e₂ e₃ e₄ p.1.1 p.1.2 p.2
  left_inv _ := relativeIsom_hom_ext e₁ e₂ e₃ e₄
    (relativeIsomFst_relativeIsomLift _ _ _ _ _ _ _)
    (relativeIsomSnd_relativeIsomLift _ _ _ _ _ _ _)
  right_inv _ := Subtype.ext (Prod.ext
    (relativeIsomFst_relativeIsomLift _ _ _ _ _ _ _)
    (relativeIsomSnd_relativeIsomLift _ _ _ _ _ _ _))

/-- The first component of the representing bijection is natural: precomposing a morphism into
the fibre product with `h : T' ⟶ T` base changes the relative morphism it names. -/
theorem relativeIsomFst_comp {T T' : Over S} (h : T' ⟶ T)
    (t : T ⟶ relativeIsomObj e₁ e₂ e₃ e₄) :
    relativeIsomFst e₁ e₂ e₃ e₄ (h ≫ t) =
      (relativeHom Z X).map h.op (relativeIsomFst e₁ e₂ e₃ e₄ t) := by
  simp only [relativeIsomFst, relativeIsomToPair, Category.assoc]
  exact e₁.homEquiv_comp h _

/-- The second component of the representing bijection is natural: precomposing a morphism into
the fibre product with `h : T' ⟶ T` base changes the relative morphism it names. -/
theorem relativeIsomSnd_comp {T T' : Over S} (h : T' ⟶ T)
    (t : T ⟶ relativeIsomObj e₁ e₂ e₃ e₄) :
    relativeIsomSnd e₁ e₂ e₃ e₄ (h ≫ t) =
      (relativeHom X Z).map h.op (relativeIsomSnd e₁ e₂ e₃ e₄ t) := by
  simp only [relativeIsomSnd, relativeIsomToPair, Category.assoc]
  exact e₂.homEquiv_comp h _

/-- **The fibre product represents the functor of isomorphisms of base changes.** The morphisms
`T ⟶ Isom_S(Z, X)` over `S` are exactly the isomorphisms `Z ×_S T ≅ X ×_S T` over `T`.

This is the form criterion (2) of Stacks 045G asks for: the fibre of the category of covers over
`T` has the isomorphisms of base changes as its morphisms. -/
def relativeIsomObjEquivIso (T : Over S) :
    (T ⟶ relativeIsomObj e₁ e₂ e₃ e₄) ≃ (prodOverBase Z T ≅ prodOverBase X T) where
  toFun t :=
    { hom := relativeMorOverBase (relativeIsomFst e₁ e₂ e₃ e₄ t)
      inv := relativeMorOverBase (relativeIsomSnd e₁ e₂ e₃ e₄ t)
      hom_inv_id :=
        ((isRelativeMorInverse_iff _ _).1 (isRelativeMorInverse_relativeIsom e₁ e₂ e₃ e₄ t)).1
      inv_hom_id :=
        ((isRelativeMorInverse_iff _ _).1 (isRelativeMorInverse_relativeIsom e₁ e₂ e₃ e₄ t)).2 }
  invFun e := relativeIsomLift e₁ e₂ e₃ e₄ (relativeMorOfOverBase e.hom)
    (relativeMorOfOverBase e.inv) (by
      rw [isRelativeMorInverse_iff, relativeMorOverBase_relativeMorOfOverBase,
        relativeMorOverBase_relativeMorOfOverBase]
      exact ⟨e.hom_inv_id, e.inv_hom_id⟩)
  left_inv t := relativeIsom_hom_ext e₁ e₂ e₃ e₄
    (by rw [relativeIsomFst_relativeIsomLift, relativeMorOfOverBase_relativeMorOverBase])
    (by rw [relativeIsomSnd_relativeIsomLift, relativeMorOfOverBase_relativeMorOverBase])
  right_inv e := Iso.ext (by
    change relativeMorOverBase (relativeIsomFst e₁ e₂ e₃ e₄ _) = e.hom
    rw [relativeIsomFst_relativeIsomLift, relativeMorOverBase_relativeMorOfOverBase])

/-! ### The scheme underlying the fibre product -/

/-- The scheme underlying the pair object is a fibre product of the two representing schemes. -/
def relativeMorPairLeftIso :
    (W₁ ⨯ W₂ : Over S).left ≅ pullback W₁.hom W₂.hom :=
  Over.prodLeftIsoPullback W₁ W₂

/-- **The scheme underlying the object representing `Isom_S(Z, X)` is a fibre product of
schemes.** This is what bounds its size: the forgetful functor to schemes preserves the fibre
product. -/
def relativeIsomObjLeftIso :
    (relativeIsomObj e₁ e₂ e₃ e₄).left ≅
      pullback
        ((Over.forget S).map
          (prod.lift (relativeMorCompFst e₁ e₂ e₃) (relativeMorCompSnd e₁ e₂ e₄)))
        ((Over.forget S).map
          (prod.lift (relativeMorIdSection e₃ (⊤_ (Over S)))
            (relativeMorIdSection e₄ (⊤_ (Over S))))) :=
  PreservesPullback.iso (Over.forget S) _ _

end Isom

/-! ### The hypotheses of Stacks 0BL3, four times -/

section OfFiniteLocallyFree

variable {Zs Xs : Scheme.{u}} (f : Zs ⟶ S) (g : Xs ⟶ S)

/-- **The four relative morphism functors of two finite locally free schemes over `S` are
representable.** Each of the four is an instance of Stacks 0BL3: a finite locally free morphism
is affine, so each ordered pair of the two has a finite locally free source and an affine
target. -/
theorem exists_representableBy_four [IsFiniteLocallyFree f] [IsFiniteLocallyFree g] :
    ∃ W₁ W₂ V₁ V₂ : Over S,
      Nonempty ((relativeHom (Over.mk f) (Over.mk g)).RepresentableBy W₁) ∧
      Nonempty ((relativeHom (Over.mk g) (Over.mk f)).RepresentableBy W₂) ∧
      Nonempty ((relativeHom (Over.mk f) (Over.mk f)).RepresentableBy V₁) ∧
      Nonempty ((relativeHom (Over.mk g) (Over.mk g)).RepresentableBy V₂) := by
  obtain ⟨W₁, -, h₁⟩ := relativeHom_representableBy_affineHom f g
  obtain ⟨W₂, -, h₂⟩ := relativeHom_representableBy_affineHom g f
  obtain ⟨V₁, -, h₃⟩ := relativeHom_representableBy_affineHom f f
  obtain ⟨V₂, -, h₄⟩ := relativeHom_representableBy_affineHom g g
  exact ⟨W₁, W₂, V₁, V₂, h₁, h₂, h₃, h₄⟩

end OfFiniteLocallyFree

end Stacks.Morphisms

end
