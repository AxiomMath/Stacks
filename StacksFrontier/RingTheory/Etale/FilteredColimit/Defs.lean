module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Filtered colimits of étale algebras: definitions

An `R`-algebra is a *filtered colimit of étale `R`-algebras* when it is the
colimit of a filtered diagram every object of which is étale over `R`. This is
the property underlying the strict henselization.

The property is stated in three forms: for objects of `Under (CommRingCat.of R)`,
concretely through `Ring.DirectLimit`, and for a ring map into `CommAlgCat`. This file
also defines the strict fibres of the rectification argument and the total index category
`K` of the composition argument.

## Main definitions

* `IsFilteredColimitOfEtaleUnder`, `IsFilteredColimitOfEtale`,
  `IsFilteredColimitOfEtaleHom`: the three spellings.
* `Stage`, `SliceFibObj`, `SliceFibHom`: the strict fibres of the rectification.
* `LComposeAux.KData`, `KObj`, `KHom`, `Kdiagram`, `KSetup`: the total index
  category of the composition argument and its hypotheses.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **Filtered colimit of étale $R$-algebras.**
Let `R` be a commutative ring. An $R$-algebra `A : Under (CommRingCat.of R)`
*is a filtered colimit of etale $R$-algebras* when there exist a small filtered
category `J`, a diagram `F : J ⥤ Under (CommRingCat.of R)` whose every object
has an etale structure map, and a colimit cocone `c` whose apex is isomorphic to
`A` as an object of `Under (CommRingCat.of R)`. -/
def IsFilteredColimitOfEtaleUnder (R : Type) [CommRing R]
    (A : Under (CommRingCat.of R)) : Prop :=
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J)
    (F : J ⥤ Under (CommRingCat.of R)) (c : Limits.Cocone F),
    (∀ j, RingHom.Etale (F.obj j).hom.hom) ∧
    Nonempty (Limits.IsColimit c) ∧ Nonempty (c.pt ≅ A)


/-- An `R`-algebra `A` is a *filtered colimit of étale `R`-algebras* when there is a
nonempty directed index preorder `ι`, a directed system `(G i, f i j)` of commutative
`R`-algebras with `R`-algebra transition maps `f i j : G i →ₐ[R] G j` for `i ≤ j` and
with each `G i` étale over `R` (Mathlib's class `Algebra.Etale`, i.e. formally étale
and of finite presentation), such that `A` is `R`-algebra isomorphic to the colimit of
the system.

The colimit is taken to be the ring-level direct limit `Ring.DirectLimit G f`. Since
Mathlib does not endow `Ring.DirectLimit` with an `R`-algebra structure automatically,
the definition carries that structure as an explicit witness, together with the
compatibility condition that the canonical maps `Ring.DirectLimit.of i : G i → colim`
are `R`-algebra homomorphisms. That condition pins the structure down as the canonical
one, `algebraMap R colim r = of i (algebraMap R (G i) r)` for every `i`, so the
isomorphism `A ≃ₐ[R] colim` says exactly that `A` is the colimit in the category of
`R`-algebras. -/
def IsFilteredColimitOfEtale (R : Type u) [CommRing R] (A : Type u) [CommRing A]
    [Algebra R A] : Prop :=
  ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
    (G : ι → Type u) (_ : (i : ι) → CommRing (G i)) (_ : (i : ι) → Algebra R (G i))
    (f : (i j : ι) → i ≤ j → G i →ₐ[R] G j)
    (_ : DirectedSystem G (fun i j h => (f i j h : G i → G j)))
    (_ : Algebra R (Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)))),
    -- (1) each `G i` is étale over `R`
    (∀ i, Algebra.Etale R (G i)) ∧
    -- the carried algebra structure on the colimit is the natural one: the
    -- structure maps `of i` are `R`-algebra homomorphisms
    (∀ i, ∀ r : R,
      Ring.DirectLimit.of G (fun i j h => (f i j h : G i → G j)) i (algebraMap R (G i) r)
        = algebraMap R (Ring.DirectLimit G (fun i j h => (f i j h : G i → G j))) r) ∧
    -- (2) `A` is `R`-algebra isomorphic to the colimit
    Nonempty (A ≃ₐ[R] Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)))

/-- `A`, viewed as an `R`-algebra via the ring map `f : R →+* A`,
is a *filtered colimit of étale `R`-algebras* if there exist a small filtered
category `J` and a diagram `F : J ⥤ CommAlgCat R` with every object `F.obj j`
étale over `R`, together with a colimit cocone `c` for `F` whose apex is
isomorphic, as an `R`-algebra (i.e. in `CommAlgCat R`), to `A`. -/
def IsFilteredColimitOfEtaleHom {R : Type u} [CommRing R] {A : Type u} [CommRing A]
    (f : R →+* A) : Prop :=
  letI : Algebra R A := f.toAlgebra
  ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
    (F : J ⥤ CommAlgCat.{u} R)
    (_ : ∀ j, Algebra.Etale R (F.obj j))
    (c : Cocone F),
      Nonempty (c.pt ≅ CommAlgCat.of R A) ∧ Nonempty (IsColimit c)

/-! ### The strict fibres of the rectification argument -/

/-- The small type of étale "stages": a pair `(j', x : Idx j')`. -/
abbrev Stage (J : Type) [SmallCategory J] (Idx : J → Type) [∀ j, SmallCategory (Idx j)] :=
  Σ j' : J, Idx j'

/-- The étale algebra carried by a stage `s = ⟨j', x⟩`: namely `(Fib j').obj x`. -/
def stageObj {R : Type} [CommRing R] {J : Type} [SmallCategory J] {Idx : J → Type}
    [∀ j, SmallCategory (Idx j)] (Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)) (s : Stage J Idx) :
    Under (CommRingCat.of R) := (Fib s.fst).obj s.snd

/-- Objects of the strict fibre over `j`: an étale stage `s` together with a structure map
into `G.obj j`. -/
structure SliceFibObj {R : Type} [CommRing R] {J : Type} [SmallCategory J] {Idx : J → Type}
    [∀ j, SmallCategory (Idx j)] (G : J ⥤ Under (CommRingCat.of R))
    (Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)) (j : J) where
  /-- The étale stage. -/
  s : Stage J Idx
  /-- The structure map from the stage algebra into `G.obj j`. -/
  p : stageObj Fib s ⟶ G.obj j

/-- Morphisms of the strict fibre: a map `g` between the carried stage algebras over the
triangle. -/
structure SliceFibHom {R : Type} [CommRing R] {J : Type} [SmallCategory J] {Idx : J → Type}
    [∀ j, SmallCategory (Idx j)] {G : J ⥤ Under (CommRingCat.of R)}
    {Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)} {j : J} (a b : SliceFibObj G Fib j) where
  /-- The underlying map of stage algebras. -/
  g : stageObj Fib a.s ⟶ stageObj Fib b.s
  /-- The map `g` commutes with the structure maps into `G.obj j`. -/
  w : a.p = g ≫ b.p

namespace SliceFibHom
/-- Two morphisms of the strict fibre are equal when their underlying stage maps are. -/
@[ext] lemma ext {R : Type} [CommRing R] {J : Type} [SmallCategory J] {Idx : J → Type}
    [∀ j, SmallCategory (Idx j)] {G : J ⥤ Under (CommRingCat.of R)}
    {Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)} {j : J}
    {a b : SliceFibObj G Fib j} {f g : SliceFibHom a b} (h : f.g = g.g) : f = g := by
  cases f; cases g; simp_all
end SliceFibHom

/-- The strict fibre over `j` is a category, with morphisms the stage maps commuting with the
structure maps into `G.obj j`. -/
instance sliceFibCategory {R : Type} [CommRing R] {J : Type} [SmallCategory J] {Idx : J → Type}
    [∀ j, SmallCategory (Idx j)] {G : J ⥤ Under (CommRingCat.of R)}
    {Fib : ∀ j, Idx j ⥤ Under (CommRingCat.of R)} (j : J) :
    Category (SliceFibObj G Fib j) where
  Hom a b := SliceFibHom a b
  id a := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.g ≫ g.g, by rw [f.w, g.w]; simp [Category.assoc]⟩
  id_comp := by intro a b f; apply SliceFibHom.ext; simp
  comp_id := by intro a b f; apply SliceFibHom.ext; simp
  assoc := by intro a b c d f g h; apply SliceFibHom.ext; simp [Category.assoc]

namespace LComposeAux

universe v

variable {R : Type u} [CommRing R]

/-- The data of the total index category: an outer index category `I`, for each `i` an inner
index category `J i` and a diagram `F i : J i ⥤ CommAlgCat R`, an apex `T`, and maps
`φ i j : (F i).obj j ⟶ T`. -/
structure KData (R : Type u) [CommRing R] where
  /-- The outer index type. -/
  I : Type u
  /-- The category structure on `I`. -/
  instI : SmallCategory I
  /-- The inner index type over `i`. -/
  J : I → Type u
  /-- The category structure on each `J i`. -/
  instJ : ∀ i, SmallCategory (J i)
  /-- The inner diagram over `i`. -/
  F : ∀ i, J i ⥤ CommAlgCat.{u} R
  /-- The apex. -/
  T : CommAlgCat.{u} R
  /-- The structure map from `(F i).obj j` to the apex `T`. -/
  φ : ∀ (i : I) (j : J i), (F i).obj j ⟶ T

attribute [instance] KData.instI KData.instJ

variable {R : Type u} [CommRing R]

/-- Objects of the index category `K`: pairs `(i, j)`. -/
structure KObj (D : KData R) where
  /-- The outer index `i`. -/
  fst : D.I
  /-- The inner index `j` over `i`. -/
  snd : D.J fst

/-- Underlying étale algebra of a `K`-object `(i, j)`, namely `(F i).obj j`. -/
def Kalg {D : KData R} (k : KObj D) : CommAlgCat.{u} R := (D.F k.fst).obj k.snd

/-- The chosen structure map of a `K`-object to the apex `T`. -/
def Kphi {D : KData R} (k : KObj D) : Kalg k ⟶ D.T := D.φ k.fst k.snd

/-- Morphisms of `K`: algebra maps commuting with the structure maps to `T`
(i.e. morphisms in the slice `CommAlgCat R / T`). -/
structure KHom {D : KData R} (k k' : KObj D) where
  /-- The underlying algebra map. -/
  u : Kalg k ⟶ Kalg k'
  /-- The map `u` commutes with the structure maps to `T`. -/
  w : u ≫ Kphi k' = Kphi k

-- needed: without it `Kcat` fails: unsolved goals
set_option backward.isDefEq.respectTransparency false in
/-- `K` is a (small) category — a full subcategory of `CommAlgCat R / T`. All
functoriality is strict (no reindexing of inner indices is required). -/
instance Kcat (D : KData R) : Category (KObj D) where
  Hom k k' := KHom k k'
  id k := { u := 𝟙 _, w := by simp [Kphi] }
  comp f g := { u := f.u ≫ g.u, w := by rw [Category.assoc, g.w, f.w] }

/-- The diagram `H : K ⥤ CommAlgCat R`, `(i, j) ↦ (F i).obj j`. -/
def Kdiagram (D : KData R) : KObj D ⥤ CommAlgCat.{u} R where
  obj k := Kalg k
  map f := f.u
  map_id := by intro k; rfl
  map_comp := by intro a b c f g; rfl

-- needed: `Kcocone`'s `simp only [Category.comp_id]` argument only fires with defeq
-- ignoring transparency.
set_option backward.isDefEq.respectTransparency false in
/-- The structure cocone `Φ` on `H` with apex `T`, legs the maps `φ`. -/
def Kcocone (D : KData R) : Cocone (Kdiagram D) where
  pt := D.T
  ι := { app := Kphi
         naturality := by
           intro k k' f
           simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
           exact f.w }

/-- Hypotheses on `D : KData R`: `I` and the `J i` are filtered; `dcocone` is a colimit of a
diagram `G : D.I ⥤ CommAlgCat R` with apex `D.T`; each `ccocone i` is a colimit of `D.F i` with
apex isomorphic to `G.obj i` via `eC i`; the structure maps factor as
`φ i j = (ccocone i).ι.app j ≫ eC i ≫ dcocone.ι.app i`; and all objects are étale. -/
structure KSetup (D : KData R) where
  /-- The outer index category is filtered. -/
  filtI : IsFiltered D.I
  /-- Each inner index category is filtered. -/
  filtJ : ∀ i, IsFiltered (D.J i)
  /-- The outer diagram. -/
  G : D.I ⥤ CommAlgCat.{u} R
  /-- A cocone on the outer diagram. -/
  dcocone : Cocone G
  /-- The outer cocone is a colimit. -/
  hd : IsColimit dcocone
  /-- The apex of the outer cocone is `D.T`. -/
  hTd : dcocone.pt = D.T
  /-- A cocone on each inner diagram. -/
  ccocone : ∀ i, Cocone (D.F i)
  /-- Each inner cocone is a colimit. -/
  hc : ∀ i, IsColimit (ccocone i)
  /-- The apex of the inner cocone over `i` is isomorphic to `G.obj i`. -/
  eC : ∀ i, (ccocone i).pt ≅ G.obj i
  /-- The structure maps factor through the inner and outer cocones. -/
  hφ : ∀ (i : D.I) (j : D.J i),
      D.φ i j = (ccocone i).ι.app j ≫ (eC i).hom ≫ dcocone.ι.app i ≫ eqToHom hTd
  /-- Every object of every inner diagram is étale over `R`. -/
  hEt : ∀ (i : D.I) (j : D.J i), Algebra.Etale R ((D.F i).obj j)

end LComposeAux
