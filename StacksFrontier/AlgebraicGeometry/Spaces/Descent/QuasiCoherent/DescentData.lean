module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# Descent data for quasi-coherent modules on algebraic spaces

Let `X` be an algebraic space and `(f i : Y i ⟶ X)` a family of algebraic spaces over it.  A
descent datum for quasi-coherent modules relative to that family consists of a quasi-coherent
module on each `Y i`, an isomorphism of the two inverse images on each pairwise fibre product
`Y i ×_X Y j`, and a cocycle condition relating the three isomorphisms attached to a triple
`i, j, k`.  Morphisms of descent data are families of module morphisms commuting with the
isomorphisms.  This is Stacks 04W3.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.pair` is the pairwise fibre product
  `Y i ×_X Y j`, with `pairFst` and `pairSnd` its two projections.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison` identifies the inverse image
  along a composite with the iterated inverse image.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn` is a pairwise isomorphism of a
  descent datum, read after pullback to a test space mapping compatibly to the two members.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum` is **Stacks 04W3, part (1)**, and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.Hom` is **part (2)**.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.category`: descent data for the
  family form a category, with componentwise identities and composition.

## Implementation notes

The cocycle condition is stated after pullback to an arbitrary algebraic space `T` equipped with
three compatible morphisms to members of the family, rather than on the triple fibre product
`Y i ×_X Y j ×_X Y k`.  Taking `T` to be that triple fibre product recovers the diagram of the
source, and the formulation avoids fixing an associativity convention for it.  The comparison
that transports a pairwise isomorphism to `T` is `pullbackComparison`, built from the
composition isomorphism `AlgebraicGeometry.Space.modulePullbackCompIso` of Stacks 03LU.

Quasi-coherence of the component modules is `SheafOfModules.IsQuasicoherentOnSite`, the
universe-flexible form of Stacks 03DL(6), as a field rather than as an instance argument,
matching `AlgebraicGeometry.Space.QuasicoherentSheaves`.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS}

/-- The fibre product `Y i ×_X Y j` of two members of a family of algebraic spaces over `X`. -/
abbrev pair (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X) (i j : I) :=
  AlgebraicSpaces.fiberProduct B S hS (f i) (f j)

/-- The first projection `Y i ×_X Y j ⟶ Y i`. -/
abbrev pairFst (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X) (i j : I) :
    pair B S hS Y f i j ⟶ Y i :=
  ObjectProperty.homMk (pullback.fst (f i).hom (f j).hom)

/-- The second projection `Y i ×_X Y j ⟶ Y j`. -/
abbrev pairSnd (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X) (i j : I) :
    pair B S hS Y f i j ⟶ Y j :=
  ObjectProperty.homMk (pullback.snd (f i).hom (f j).hom)

/-- The canonical identification of the inverse image of a module along a morphism `v` with the
iterated inverse image along a factorization `v = g ≫ p` of it. -/
def pullbackComparison {A P T : AlgebraicSpaces B S hS} (g : T ⟶ P) (p : P ⟶ A) (v : T ⟶ A)
    (hv : g ≫ p = v) (M : Modules.{u, u} B S hS A.1 A.2) :
    (modulePullback B S hS v).obj M ≅
      (modulePullback B S hS g).obj ((modulePullback B S hS p).obj M) :=
  (eqToIso (congrArg (fun q : T ⟶ A => (modulePullback B S hS q).obj M) hv)).symm ≪≫
    ((modulePullbackCompIso B S hS g p).app M).symm

/-- A pairwise isomorphism `φ i j` of a descent datum, read on a test space `T` equipped with a
morphism `v` to `Y i ×_X Y j` and the two composites `vi`, `vj` to the two members: the inverse
image of `φ i j` along `v`, with the comparisons of iterated inverse images on either side. -/
def transitionOn (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (F : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2)
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F j))
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ pair B S hS Y f i j)
    (vi : T ⟶ Y i) (vj : T ⟶ Y j) (hi : v ≫ pairFst B S hS Y f i j = vi)
    (hj : v ≫ pairSnd B S hS Y f i j = vj) :
    (modulePullback B S hS vi).obj (F i) ≅ (modulePullback B S hS vj).obj (F j) :=
  pullbackComparison B S hS v (pairFst B S hS Y f i j) vi hi (F i) ≪≫
    (modulePullback B S hS v).mapIso (φ i j) ≪≫
    (pullbackComparison B S hS v (pairSnd B S hS Y f i j) vj hj (F j)).symm

/-- **Stacks 04W3, part (1).**  A descent datum for quasi-coherent modules relative to a family
`(f i : Y i ⟶ X)` of algebraic spaces over `X`: a quasi-coherent module on each `Y i`, an
isomorphism of the two inverse images on each pairwise fibre product, and the cocycle
condition. -/
@[stacks 04W3 "part (1)"]
structure DescentDatum (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X) where
  /-- The module on the `i`-th member of the family. -/
  F : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2
  /-- Each member module is quasi-coherent. -/
  quasicoherent : ∀ i, (F i).IsQuasicoherentOnSite
  /-- The isomorphism of the two inverse images on the pairwise fibre product. -/
  transition : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F i) ≅
    (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F j)
  /-- The cocycle condition, after pullback to an arbitrary algebraic space mapping compatibly
  to three members of the family. -/
  cocycle : ∀ (i j k : I) (T : AlgebraicSpaces B S hS)
      (vi : T ⟶ Y i) (vj : T ⟶ Y j) (vk : T ⟶ Y k)
      (vij : T ⟶ pair B S hS Y f i j) (vjk : T ⟶ pair B S hS Y f j k)
      (vik : T ⟶ pair B S hS Y f i k)
      (hij₀ : vij ≫ pairFst B S hS Y f i j = vi)
      (hij₁ : vij ≫ pairSnd B S hS Y f i j = vj)
      (hjk₀ : vjk ≫ pairFst B S hS Y f j k = vj)
      (hjk₁ : vjk ≫ pairSnd B S hS Y f j k = vk)
      (hik₀ : vik ≫ pairFst B S hS Y f i k = vi)
      (hik₁ : vik ≫ pairSnd B S hS Y f i k = vk),
    transitionOn B S hS Y f F transition i j vij vi vj hij₀ hij₁ ≪≫
      transitionOn B S hS Y f F transition j k vjk vj vk hjk₀ hjk₁ =
      transitionOn B S hS Y f F transition i k vik vi vk hik₀ hik₁

/-- **Stacks 04W3, part (2).**  A morphism of descent data: a family of morphisms of the
component modules commuting with every pairwise isomorphism. -/
@[stacks 04W3 "part (2)"]
structure DescentDatum.Hom {Y : I → AlgebraicSpaces B S hS} {f : ∀ i, Y i ⟶ X}
    (D E : DescentDatum B S hS Y f) where
  /-- The morphism of the `i`-th component modules. -/
  app : ∀ i, D.F i ⟶ E.F i
  /-- Compatibility with the pairwise isomorphisms. -/
  naturality : ∀ i j,
    (modulePullback B S hS (pairFst B S hS Y f i j)).map (app i) ≫ (E.transition i j).hom =
      (D.transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS Y f i j)).map (app j)

namespace DescentDatum

variable {B S hS} {Y : I → AlgebraicSpaces B S hS} {f : ∀ i, Y i ⟶ X}

/-- Morphisms of descent data are determined by their components. -/
@[ext]
theorem Hom.ext {D E : DescentDatum B S hS Y f} {a b : Hom B S hS D E}
    (h : ∀ i, a.app i = b.app i) : a = b := by
  cases a
  cases b
  congr
  exact funext h

/-- The identity morphism of a descent datum. -/
def Hom.id (D : DescentDatum B S hS Y f) : Hom B S hS D D where
  app i := 𝟙 (D.F i)
  naturality i j := by simp

/-- Composition of morphisms of descent data, componentwise. -/
def Hom.comp {D E G : DescentDatum B S hS Y f} (a : Hom B S hS D E) (b : Hom B S hS E G) :
    Hom B S hS D G where
  app i := a.app i ≫ b.app i
  naturality i j := by
    simp only [Functor.map_comp, Category.assoc]
    rw [b.naturality, ← Category.assoc, a.naturality, Category.assoc]

/-- Descent data for quasi-coherent modules relative to a family of algebraic spaces over `X`
form a category. -/
instance category : Category (DescentDatum B S hS Y f) where
  Hom := Hom B S hS
  id := Hom.id
  comp := Hom.comp
  id_comp a := Hom.ext (fun i => Category.id_comp (a.app i))
  comp_id a := Hom.ext (fun i => Category.comp_id (a.app i))
  assoc a b c := Hom.ext (fun i => Category.assoc (a.app i) (b.app i) (c.app i))

/-- The components of the identity morphism of a descent datum are the identities. -/
@[simp]
theorem id_app (D : DescentDatum B S hS Y f) (i : I) : (𝟙 D : D ⟶ D).app i = 𝟙 (D.F i) := rfl

/-- Composition of morphisms of descent data is componentwise. -/
@[simp]
theorem comp_app {D E G : DescentDatum B S hS Y f} (a : D ⟶ E) (b : E ⟶ G) (i : I) :
    (a ≫ b).app i = a.app i ≫ b.app i := rfl

end DescentDatum

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
