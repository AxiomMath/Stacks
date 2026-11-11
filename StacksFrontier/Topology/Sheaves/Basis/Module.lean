module

public import StacksFrontier.Topology.Sheaves.Basis.CofinalSheafCondition
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 009S — Presheaves and sheaves of `O`-modules on a basis

Stacks 009S defines presheaves and sheaves of `O`-modules on a basis `B` for the topology of a
space `X`, where `O` is a (pre)sheaf of rings on `B`.

Clause (1) is `PresheafOfModulesOnBasis`: a presheaf of abelian groups `F` on `B` together with an
`O(U)`-module structure on `F(U)` for each `U ∈ B`, compatible with restriction in the sense that
`res (r • m) = res r • res m`. Clause (2) is `PresheafOfModulesOnBasis.Hom`, a morphism of such
presheaves: a family of `O(U)`-linear maps `F(U) → G(U)` commuting with restriction. Clause (3) is
`SheafOfModulesOnBasis`: for a sheaf of rings `O` on `B` (`SheafOfRingsOnBasis`, a presheaf of
rings whose underlying presheaf of sets is a sheaf on `B`), a presheaf of `O`-modules on `B`
whose underlying presheaf of abelian groups satisfies the basis-sheaf condition
`PresheafOfModulesOnBasis.IsSheafOfAbGrps` — for every covering of `U ∈ B` by basis elements,
sections agreeing on every basis element contained in a pairwise intersection glue uniquely.

The ambient presheaf of rings is supplied here as `PresheafOfRingsOnBasis`, the structure of
Stacks 009H cut down to what 009S consumes: a commutative ring `O(U)` for each `U ∈ B` with
restriction ring homomorphisms satisfying the identity and composition laws.

The notion of a covering of `U` by basis elements used to state the sheaf condition is
`Stacks.SheafOnBasis.Covering`, from the 009L development. It is instantiated at
`Covering.{u, u}`, so the sheaf condition below quantifies over coverings indexed in universe `u`.
Widening it to `Covering.{u, v}` would *strengthen* the condition and so shrink the class of
sheaves of modules, which is a change to 009S's content rather than a deduplication.
-/

@[expose] public section

universe u w₁ w₂

open TopologicalSpace


variable {X : Type u} [TopologicalSpace X]

/-! ### Presheaf of rings on a basis (009H)

We define the minimal structure needed from Definition 009H of the Stacks project:
a presheaf of rings on a basis `B`. This is the data of a ring `O(U)` for each
`U ∈ B`, together with ring homomorphism restriction maps satisfying identity
and composition. -/

/-- A presheaf of rings on a basis `B` of the topology on `X`. -/
@[sga "3 I 3.1" "special case"]
structure PresheafOfRingsOnBasis (B : Set (Set X)) where
  /-- The ring of sections over each basis element. -/
  obj (U : Set X) (hU : U ∈ B) : Type w₁
  /-- Each `obj U hU` carries a commutative ring structure. -/
  ring (U : Set X) (hU : U ∈ B) : CommRing (obj U hU)
  /-- The restriction ring homomorphism for an inclusion `V ⊆ U` of basis elements. -/
  res {U V : Set X} (hU : U ∈ B) (hV : V ∈ B) (hVU : V ⊆ U) :
    letI := ring U hU; letI := ring V hV
    obj U hU →+* obj V hV
  /-- Restriction along the identity is the identity ring homomorphism. -/
  res_id {U : Set X} (hU : U ∈ B) :
    letI := ring U hU
    res hU hU (subset_refl U) = RingHom.id (obj U hU)
  /-- Restriction is functorial under composition of inclusions. -/
  res_comp {U V W : Set X} (hU : U ∈ B) (hV : V ∈ B) (hW : W ∈ B)
    (hVU : V ⊆ U) (hWV : W ⊆ V) :
    letI := ring U hU; letI := ring V hV; letI := ring W hW
    (res hV hW hWV).comp (res hU hV hVU) = res hU hW (hWV.trans hVU)

/-! ### Presheaf of O-modules on a basis (009S, part 1)

A presheaf of O-modules on B is given by a presheaf F of abelian groups on B
together with multiplication maps O(U) × F(U) → F(U) for each U ∈ B satisfying
the usual module axioms and compatible with restriction. -/

/-- A presheaf of `O`-modules on a basis `B` (Stacks 009S).

Given a presheaf of rings `O` on `B`, a presheaf of `O`-modules on `B` is
a presheaf `F` of abelian groups on `B` together with an `O(U)`-module
structure on `F(U)` for each `U ∈ B`, compatible with restriction in the
sense that `res(r • m) = (res r) • (res m)`. -/
@[stacks 009S "(1): presheaf of O-modules on a basis", sga "3 I 3.1" "special case"]
structure PresheafOfModulesOnBasis {B : Set (Set X)}
    (O : PresheafOfRingsOnBasis.{u, w₁} B) where
  /-- The abelian group of sections over each basis element. -/
  obj (U : Set X) (hU : U ∈ B) : Type w₂
  /-- Each `obj U hU` carries an additive commutative group structure. -/
  addCommGroup (U : Set X) (hU : U ∈ B) : AddCommGroup (obj U hU)
  /-- Each `obj U hU` is a module over `O.obj U hU`. -/
  module (U : Set X) (hU : U ∈ B) :
    letI := O.ring U hU; letI := addCommGroup U hU
    Module (O.obj U hU) (obj U hU)
  /-- The restriction map of the underlying presheaf of abelian groups. -/
  res {U V : Set X} (hU : U ∈ B) (hV : V ∈ B) (hVU : V ⊆ U) :
    letI := addCommGroup U hU; letI := addCommGroup V hV
    obj U hU →+ obj V hV
  /-- Restriction along the identity is the identity. -/
  res_id {U : Set X} (hU : U ∈ B) (s : obj U hU) :
    letI := addCommGroup U hU
    res hU hU (subset_refl U) s = s
  /-- Restriction is functorial under composition of inclusions. -/
  res_comp {U V W : Set X} (hU : U ∈ B) (hV : V ∈ B) (hW : W ∈ B)
    (hVU : V ⊆ U) (hWV : W ⊆ V) (s : obj U hU) :
    letI := addCommGroup U hU; letI := addCommGroup V hV; letI := addCommGroup W hW
    res hV hW hWV (res hU hV hVU s) = res hU hW (hWV.trans hVU) s
  /-- Restriction is compatible with scalar multiplication:
  `res(r • m) = (res r) • (res m)`. -/
  res_smul {U V : Set X} (hU : U ∈ B) (hV : V ∈ B) (hVU : V ⊆ U)
    (r : O.obj U hU) (m : obj U hU) :
    letI := O.ring U hU; letI := O.ring V hV
    letI := addCommGroup U hU; letI := addCommGroup V hV
    letI := module U hU; letI := module V hV
    res hU hV hVU (r • m) = O.res hU hV hVU r • res hU hV hVU m

/-! ### Morphisms of presheaves of O-modules on a basis (009S, part 2) -/

/-- A morphism of presheaves of `O`-modules on `B`.

A morphism `φ : F → G` is a family of `O(U)`-module homomorphisms
`φ(U) : F(U) → G(U)` commuting with restriction. -/
@[stacks 009S "(2): morphism of presheaves of O-modules on a basis"]
structure PresheafOfModulesOnBasis.Hom {B : Set (Set X)}
    {O : PresheafOfRingsOnBasis.{u, w₁} B}
    (F G : PresheafOfModulesOnBasis.{u, w₁, w₂} O) where
  /-- The component of the morphism at each basis element. -/
  app (U : Set X) (hU : U ∈ B) :
    letI := O.ring U hU
    letI := F.addCommGroup U hU; letI := F.module U hU
    letI := G.addCommGroup U hU; letI := G.module U hU
    F.obj U hU →ₗ[O.obj U hU] G.obj U hU
  /-- The components commute with restriction. -/
  naturality {U V : Set X} (hU : U ∈ B) (hV : V ∈ B) (hVU : V ⊆ U)
    (s : F.obj U hU) :
    letI := F.addCommGroup U hU; letI := F.addCommGroup V hV
    letI := G.addCommGroup U hU; letI := G.addCommGroup V hV
    G.res hU hV hVU (app U hU s) = app V hV (F.res hU hV hVU s)

/-! ### Sheaf of rings on a basis

A sheaf of rings on `B` is a presheaf of rings on `B` whose underlying presheaf of sets is a sheaf
on `B` in the sense of Stacks 009J (Stacks 009P with values in rings). This is the hypothesis on
`O` under which Stacks 009S (3) defines sheaves of `O`-modules. -/

/-- The underlying presheaf of sets of a presheaf of rings on `B`. -/
def PresheafOfRingsOnBasis.toPresheaf {B : Set (Set X)} (O : PresheafOfRingsOnBasis.{u, w₁} B) :
    Stacks.SheafOnBasis.Presheaf.{u, w₁} B where
  obj := O.obj
  res hU hV hVU := O.res hU hV hVU
  res_id hU s := by
    let := O.ring _ hU
    exact DFunLike.congr_fun (O.res_id hU) s
  res_comp hU hV hW hVU hWV s := by
    let := O.ring _ hU; let := O.ring _ hV; let := O.ring _ hW
    exact DFunLike.congr_fun (O.res_comp hU hV hW hVU hWV) s

/-- A presheaf of rings on `B` is a sheaf if its underlying presheaf of sets satisfies the sheaf
condition on `B`: for every covering of `U ∈ B` by members of `B`, every family of sections
agreeing on all members of `B` contained in pairwise intersections glues uniquely. -/
def PresheafOfRingsOnBasis.IsSheaf {B : Set (Set X)} (O : PresheafOfRingsOnBasis.{u, w₁} B) :
    Prop :=
  Stacks.SheafOnBasis.Presheaf.IsSheaf.{u, u, w₁} O.toPresheaf

/-- A sheaf of rings on a basis `B`: a presheaf of rings on `B` whose underlying presheaf of
sets is a sheaf on `B`. -/
structure SheafOfRingsOnBasis (B : Set (Set X)) where
  /-- The underlying presheaf of rings. -/
  val : PresheafOfRingsOnBasis.{u, w₁} B
  /-- The underlying presheaf of sets is a sheaf. -/
  isSheaf : val.IsSheaf

/-! ### Sheaf of O-modules on a basis (009S, part 3)

When O is a sheaf of rings on B, a sheaf of O-modules on B is a presheaf of
O-modules whose underlying presheaf of abelian groups is a sheaf. We use the
sheaf condition from Stacks 009J: for every covering of U ∈ B by basis
elements, sections that are compatible on all basis elements contained in
pairwise intersections glue uniquely. -/

/-- The sheaf condition for a presheaf of abelian groups on a basis:
for every covering of `U ∈ B` by basis elements, every family of sections
compatible on all basis elements `W ⊆ U_i ∩ U_j` glues uniquely. -/
@[ega "0 3.2.2"]
def PresheafOfModulesOnBasis.IsSheafOfAbGrps {B : Set (Set X)}
    {O : PresheafOfRingsOnBasis.{u, w₁} B}
    (F : PresheafOfModulesOnBasis.{u, w₁, w₂} O) : Prop :=
  ∀ (U : Set X) (hU : U ∈ B) (𝓤 : Stacks.SheafOnBasis.Covering.{u, u} B U)
    (s : ∀ i, F.obj (𝓤.fam i) (𝓤.mem i)),
    (∀ (i j : 𝓤.ι) (W : Set X) (hW : W ∈ B)
        (hWi : W ⊆ 𝓤.fam i) (hWj : W ⊆ 𝓤.fam j),
      (letI := F.addCommGroup (𝓤.fam i) (𝓤.mem i)
       letI := F.addCommGroup W hW
       F.res (𝓤.mem i) hW hWi (s i)) =
      (letI := F.addCommGroup (𝓤.fam j) (𝓤.mem j)
       letI := F.addCommGroup W hW
       F.res (𝓤.mem j) hW hWj (s j))) →
    ∃! t : F.obj U hU, ∀ i,
      (letI := F.addCommGroup U hU
       letI := F.addCommGroup (𝓤.fam i) (𝓤.mem i)
       F.res hU (𝓤.mem i) (𝓤.subset i) t) = s i

/-- A sheaf of `O`-modules on a basis `B` (Stacks 009S, part 3).

For a sheaf of rings `O` on `B`, a sheaf of `O`-modules on `B` is a presheaf of `O`-modules on
`B` whose underlying presheaf of abelian groups satisfies the sheaf condition. -/
@[stacks 009S "(3): sheaf of O-modules on a basis, for a sheaf of rings O",
  ega "0 3.2.2"]
structure SheafOfModulesOnBasis {B : Set (Set X)}
    (O : SheafOfRingsOnBasis.{u, w₁} B) where
  /-- The underlying presheaf of `O`-modules. -/
  val : PresheafOfModulesOnBasis.{u, w₁, w₂} O.val
  /-- The underlying presheaf of abelian groups is a sheaf. -/
  isSheaf : val.IsSheafOfAbGrps

