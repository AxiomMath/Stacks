module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic

/-!
# Morphisms to the moduli stack of elliptic curves and their fibre products

A morphism from a scheme `S` to the moduli stack `𝓜₁,₁` of elliptic curves is an elliptic curve
`(E, f, 0)` over `S`: a proper family, smooth of relative dimension one, whose fibres are
connected curves of genus one, together with a section of `f`. Two such morphisms, over `S` and
over `S'`, have a fibre product `S ×_{𝓜₁,₁} S'`, namely the scheme whose `T`-points are the
triples `(a, a', α)` consisting of morphisms `a : T ⟶ S` and `a' : T ⟶ S'` together with an
isomorphism `α : E ×_{S,a} T ⟶ E' ×_{S',a'} T` of elliptic curves over `T`. The morphism
`S ⟶ 𝓜₁,₁` is smooth when for every `S' ⟶ 𝓜₁,₁` the projection `S ×_{𝓜₁,₁} S' ⟶ S'` is a
smooth morphism of schemes.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily` is a family of schemes with a section,
  and `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.IsElliptic` is the condition that
  such a family is an elliptic curve, that is, a morphism to `𝓜₁,₁`.
* `AlgebraicGeometry.ModuliEllipticCurves.Comparison` is the set of triples `(a, a', α)`, and
  `AlgebraicGeometry.ModuliEllipticCurves.Comparison.IsBaseChange` is the relation that one such
  triple is the base change of another along a morphism of test schemes.
* `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons` is the universal property of the
  fibre product `S ×_{𝓜₁,₁} S'`.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.IsSmooth` is smoothness of a morphism
  `S ⟶ 𝓜₁,₁`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Comparison.isBaseChange_id`: a triple is its own base
  change along the identity.
* `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.fst_homEquiv` and
  `AlgebraicGeometry.ModuliEllipticCurves.RepresentsComparisons.snd_homEquiv`: the two morphisms
  of the triple classified by a `T`-point of `S ×_{𝓜₁,₁} S'` are its composites with the two
  projections.

## Implementation notes

The moduli stack is not an object here: a morphism `S ⟶ 𝓜₁,₁` is the elliptic curve over `S`
that classifies it, and the fibre product is characterised by its functor of points rather than
constructed, so smoothness quantifies over every scheme representing that functor. Naturality of
the classification is recorded by `Comparison.IsBaseChange`, whose two commuting triangles over
the bases are supplemented by a commuting square for the isomorphisms of families; the base
change of an isomorphism is pinned down by that square because the vertical maps are the
canonical projections of the pulled-back families. The fibre condition is the one the source
uses, that `H⁰` and `H¹` of the structure sheaf of a fibre are both one-dimensional over the
residue field of its point.

## References

* [Stacks Project, Tag 072J](https://stacks.math.columbia.edu/tag/072J)
* [Stacks Project, Tag 072L](https://stacks.math.columbia.edu/tag/072L)
* [Stacks Project, Tag 072P](https://stacks.math.columbia.edu/tag/072P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves

/-- A family of schemes over `S` together with a section of its structure morphism, that is, a
triple `(E, f, 0)`. -/
@[stacks 072J "the triple (E, f, 0)"]
structure PointedFamily (S : Scheme.{u}) where
  /-- The total space `E`. -/
  total : Scheme.{u}
  /-- The structure morphism `f : E ⟶ S`. -/
  map : total ⟶ S
  /-- The section `0 : S ⟶ E`. -/
  zero : S ⟶ total
  /-- The morphism `0` is a section of `f`. -/
  zero_map : zero ≫ map = 𝟙 S

namespace PointedFamily

/-- A pointed family is an elliptic curve when its structure morphism is proper and smooth of
relative dimension one and each of its fibres is a connected curve of genus one, that is, has
one-dimensional `H⁰` and `H¹`. -/
@[stacks 072J "an elliptic curve over S"]
def IsElliptic {S : Scheme.{u}} (E : PointedFamily S) : Prop :=
  IsProper E.map ∧ SmoothOfRelativeDimension 1 E.map ∧
    ∀ s : S, Module.finrank ↥(S.residueField s)
        (structureSheafCohomology (R := ↥(S.residueField s))
          (E.map.fiberToSpecResidueField s) 0) = 1 ∧
      genus (E.map.fiberToSpecResidueField s) = 1

/-- The base change `(E ×_{S,a} T, pr₂, (a ≫ 0, 1))` of a pointed family along `a : T ⟶ S`. -/
abbrev pullback {S T : Scheme.{u}} (E : PointedFamily S) (a : T ⟶ S) : PointedFamily T where
  total := Limits.pullback E.map a
  map := Limits.pullback.snd E.map a
  zero := Limits.pullback.lift (a ≫ E.zero) (𝟙 T)
    (by rw [Category.assoc, E.zero_map, Category.comp_id, Category.id_comp])
  zero_map := Limits.pullback.lift_snd _ _ _

/-- The canonical morphism `E ×_{S,b} U ⟶ E ×_{S,a} T` over `h : U ⟶ T`, for `b = h ≫ a`. -/
def pullbackMap {S T U : Scheme.{u}} (E : PointedFamily S) {a : T ⟶ S} {b : U ⟶ S}
    (h : U ⟶ T) (hb : b = h ≫ a) : (E.pullback b).total ⟶ (E.pullback a).total :=
  Limits.pullback.lift (Limits.pullback.fst E.map b) (Limits.pullback.snd E.map b ≫ h)
    (by subst hb; simp [Limits.pullback.condition])

/-- The canonical morphism of pulled-back families commutes with the projections to `E`. -/
@[simp]
theorem pullbackMap_fst {S T U : Scheme.{u}} (E : PointedFamily S) {a : T ⟶ S} {b : U ⟶ S}
    (h : U ⟶ T) (hb : b = h ≫ a) :
    E.pullbackMap h hb ≫ Limits.pullback.fst E.map a = Limits.pullback.fst E.map b :=
  Limits.pullback.lift_fst _ _ _

/-- The canonical morphism of pulled-back families lies over `h : U ⟶ T`. -/
@[simp]
theorem pullbackMap_snd {S T U : Scheme.{u}} (E : PointedFamily S) {a : T ⟶ S} {b : U ⟶ S}
    (h : U ⟶ T) (hb : b = h ≫ a) :
    E.pullbackMap h hb ≫ Limits.pullback.snd E.map a = Limits.pullback.snd E.map b ≫ h :=
  Limits.pullback.lift_snd _ _ _

/-- Base change along the identity is the identity of the pulled-back family. -/
@[simp]
theorem pullbackMap_id {S T : Scheme.{u}} (E : PointedFamily S) {a : T ⟶ S}
    (ha : a = 𝟙 T ≫ a) : E.pullbackMap (𝟙 T) ha = 𝟙 (E.pullback a).total := by
  refine Limits.pullback.hom_ext ?_ ?_ <;> simp

end PointedFamily

/-! ### Reindexing a pulled-back family along an equality of base morphisms -/

namespace PointedFamily

/-- Equal morphisms to the base pull a family back to the same family. -/
def pullbackIsoOfEq {S T : Scheme.{u}} (E : PointedFamily S) {a b : T ⟶ S} (h : a = b) :
    (E.pullback a).total ≅ (E.pullback b).total :=
  eqToIso (by rw [h])

/-- The inverse of `pullbackIsoOfEq h` is `pullbackIsoOfEq h.symm`. -/
@[simp]
theorem pullbackIsoOfEq_inv {S T : Scheme.{u}} (E : PointedFamily S) {a b : T ⟶ S} (h : a = b) :
    (E.pullbackIsoOfEq h).inv = (E.pullbackIsoOfEq h.symm).hom :=
  rfl

/-- Reindexing along `a = a` is the identity. -/
@[simp]
theorem pullbackIsoOfEq_self_hom {S T : Scheme.{u}} (E : PointedFamily S) {a : T ⟶ S} (h : a = a) :
    (E.pullbackIsoOfEq h).hom = 𝟙 _ :=
  rfl

/-- Reindexing along `a = b` commutes with the structure morphisms of the pulled-back families. -/
@[reassoc]
theorem pullbackIsoOfEq_hom_map {S T : Scheme.{u}} (E : PointedFamily S) {a b : T ⟶ S} (h : a = b) :
    (E.pullbackIsoOfEq h).hom ≫ (E.pullback b).map = (E.pullback a).map := by
  subst h; simp

/-- Reindexing along `a = b` carries the zero section over `a` to the zero section over `b`. -/
@[reassoc]
theorem zero_pullbackIsoOfEq_hom {S T : Scheme.{u}} (E : PointedFamily S) {a b : T ⟶ S}
    (h : a = b) :
    (E.pullback a).zero ≫ (E.pullbackIsoOfEq h).hom = (E.pullback b).zero := by
  subst h; simp

end PointedFamily

/-- A `T`-point of `S ×_{𝓜₁,₁} S'`: morphisms `a : T ⟶ S` and `a' : T ⟶ S'` together with an
isomorphism `α : E ×_{S,a} T ⟶ E' ×_{S',a'} T` of elliptic curves over `T`, that is, one
compatible with the structure morphisms and the sections. -/
@[stacks 072L "the triples (a, a', α)"]
structure Comparison {S S' : Scheme.{u}} (E : PointedFamily S) (E' : PointedFamily S')
    (T : Scheme.{u}) where
  /-- The morphism `a : T ⟶ S`. -/
  fst : T ⟶ S
  /-- The morphism `a' : T ⟶ S'`. -/
  snd : T ⟶ S'
  /-- The isomorphism `α` of the two families pulled back to `T`. -/
  iso : (E.pullback fst).total ≅ (E'.pullback snd).total
  /-- The isomorphism is a morphism over `T`. -/
  iso_map : iso.hom ≫ (E'.pullback snd).map = (E.pullback fst).map
  /-- The isomorphism carries the section of the first family to that of the second. -/
  zero_iso : (E.pullback fst).zero ≫ iso.hom = (E'.pullback snd).zero

namespace Comparison

/-- The triple `y` over `U` is the base change of the triple `x` over `T` along `h : U ⟶ T`
when the two morphisms to the bases compose with `h` and the two isomorphisms agree after the
canonical projections of the pulled-back families. -/
@[stacks 072L "pullback of the triples"]
def IsBaseChange {S S' T : Scheme.{u}} {E : PointedFamily S} {E' : PointedFamily S'}
    (x : Comparison E E' T) {U : Scheme.{u}} (h : U ⟶ T) (y : Comparison E E' U) : Prop :=
  ∃ hfst : y.fst = h ≫ x.fst, ∃ hsnd : y.snd = h ≫ x.snd,
    y.iso.hom ≫ E'.pullbackMap h hsnd = E.pullbackMap h hfst ≫ x.iso.hom

/-- A triple is its own base change along the identity. -/
theorem isBaseChange_id {S S' T : Scheme.{u}} {E : PointedFamily S} {E' : PointedFamily S'}
    (x : Comparison E E' T) : x.IsBaseChange (𝟙 T) x :=
  ⟨(Category.id_comp _).symm, (Category.id_comp _).symm, by
    rw [E.pullbackMap_id, E'.pullbackMap_id, Category.comp_id, Category.id_comp]⟩

end Comparison

/-! ### Comparing two triples -/

namespace Comparison

variable {S S' T : Scheme.{u}} {E : PointedFamily S} {E' : PointedFamily S'}

/-- Equal triples `(a, a', α)` have the same isomorphism, after the identification of the
pullbacks along their equal morphisms to the two bases. -/
theorem iso_congr {x y : Comparison E E' T} (h : x = y) :
    x.iso.hom ≫ (E'.pullbackIsoOfEq (congrArg Comparison.snd h)).hom =
      (E.pullbackIsoOfEq (congrArg Comparison.fst h)).hom ≫ y.iso.hom := by
  subst h
  simp

/-- Two triples `(a, a', α)` are equal as soon as their morphisms to the two bases are equal and
their isomorphisms agree after those identifications. -/
theorem ext_of_eq {x y : Comparison E E' T} (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd)
    (hiso : x.iso.hom ≫ (E'.pullbackIsoOfEq hsnd).hom =
      (E.pullbackIsoOfEq hfst).hom ≫ y.iso.hom) : x = y := by
  obtain ⟨a, b, i, hi₁, hi₂⟩ := x
  obtain ⟨a', b', i', hi₃, hi₄⟩ := y
  dsimp only at hfst hsnd hiso
  subst hfst
  subst hsnd
  obtain rfl : i = i' := Iso.ext (by simpa using hiso)
  rfl

end Comparison

/-- A scheme `P` is a fibre product `S ×_{𝓜₁,₁} S'` when its `T`-points are the triples
`(a, a', α)`, naturally in `T`. -/
@[stacks 072L "the scheme S ×_{M_{1,1}} S'"]
structure RepresentsComparisons {S S' : Scheme.{u}} (E : PointedFamily S)
    (E' : PointedFamily S') (P : Scheme.{u}) where
  /-- The classification of `T`-points of `P` by triples. -/
  homEquiv (T : Scheme.{u}) : (T ⟶ P) ≃ Comparison E E' T
  /-- The classification is natural in the test scheme. -/
  naturality {T U : Scheme.{u}} (h : U ⟶ T) (g : T ⟶ P) :
    (homEquiv T g).IsBaseChange h (homEquiv U (h ≫ g))

namespace RepresentsComparisons

variable {S S' P : Scheme.{u}} {E : PointedFamily S} {E' : PointedFamily S'}

/-- The two morphisms of the triple classified by a `T`-point are the composites of the point
with those of the triple classified by the identity of `P`. -/
private theorem fst_snd_homEquiv (r : RepresentsComparisons E E' P) {T : Scheme.{u}} (g : T ⟶ P) :
    (r.homEquiv T g).fst = g ≫ (r.homEquiv P (𝟙 P)).fst ∧
      (r.homEquiv T g).snd = g ≫ (r.homEquiv P (𝟙 P)).snd := by
  obtain ⟨hfst, hsnd, -⟩ := r.naturality g (𝟙 P)
  rw [Category.comp_id] at hfst hsnd
  exact ⟨hfst, hsnd⟩

/-- The first morphism of the triple classified by a `T`-point of `S ×_{𝓜₁,₁} S'` is its
composite with the projection to `S`. -/
theorem fst_homEquiv (r : RepresentsComparisons E E' P) {T : Scheme.{u}} (g : T ⟶ P) :
    (r.homEquiv T g).fst = g ≫ (r.homEquiv P (𝟙 P)).fst :=
  (fst_snd_homEquiv r g).1

/-- The second morphism of the triple classified by a `T`-point of `S ×_{𝓜₁,₁} S'` is its
composite with the projection to `S'`. -/
theorem snd_homEquiv (r : RepresentsComparisons E E' P) {T : Scheme.{u}} (g : T ⟶ P) :
    (r.homEquiv T g).snd = g ≫ (r.homEquiv P (𝟙 P)).snd :=
  (fst_snd_homEquiv r g).2

end RepresentsComparisons

/-- A morphism `S ⟶ 𝓜₁,₁`, that is, an elliptic curve over `S`, is smooth when for every
morphism `S' ⟶ 𝓜₁,₁` the projection `S ×_{𝓜₁,₁} S' ⟶ S'` is a smooth morphism of schemes. -/
@[stacks 072P]
def PointedFamily.IsSmooth {S : Scheme.{u}} (E : PointedFamily S) (_hE : E.IsElliptic) : Prop :=
  ∀ {S' : Scheme.{u}} (E' : PointedFamily S'), E'.IsElliptic →
    ∀ (P : Scheme.{u}) (r : RepresentsComparisons E E' P), Smooth (r.homEquiv P (𝟙 P)).snd

end AlgebraicGeometry.ModuliEllipticCurves
