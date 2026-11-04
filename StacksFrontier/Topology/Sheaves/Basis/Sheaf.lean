module

public import Mathlib.Order.CompletePartialOrder
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
# Stacks 009J — Sheaves of sets on a basis

Stacks 009J defines sheaves of sets on a basis `B` for the topology of a space `X`.

`PresheafOnBasisOpenStruct` is the underlying presheaf datum, stated for `B : Set (Opens X)`:
a type of sections over each basis open together with restriction maps satisfying the identity
and composition laws. `IsSheafOnBasis` is the sheaf condition of the tag: for every basis open
`U`, every cover of `U` by basis opens `Uᵢ`, and every choice of covers of the intersections
`Uᵢ ⊓ Uⱼ` by basis opens `Vᵢⱼₖ`, a family of sections `sᵢ` agreeing on all the `Vᵢⱼₖ` glues to a
unique section over `U`. Note that the intersections `Uᵢ ⊓ Uⱼ` need not lie in `B`, which is why
the condition is phrased via the auxiliary covers rather than by restriction to intersections.

Clause (1) is `SheafOnBasis`, a presheaf on `B` bundled with that condition; clause (2) is
`SheafOnBasisHom`, a morphism of sheaves on `B`, which is by definition a morphism
`PresheafOnBasisHom` of the underlying presheaves.
-/

@[expose] public section

universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- A presheaf of sets on a set `B` of opens of `X`: a type of sections over each member of `B`
together with restriction maps along inclusions of members of `B`, functorially. -/
@[ega "0 3.2.1" "special case"]
structure PresheafOnBasisOpenStruct (B : Set (Opens X)) where
  /-- The type of sections over each member of `B`. -/
  obj : ∀ U : Opens X, U ∈ B → Type u
  /-- The restriction map along an inclusion `V ≤ U` of members of `B`. -/
  res : ∀ {U V : Opens X} (hU : U ∈ B) (hV : V ∈ B), V ≤ U →
      obj U hU → obj V hV
  /-- Restriction along the identity is the identity. -/
  res_id : ∀ {U : Opens X} (hU : U ∈ B) (s : obj U hU),
      res hU hU le_rfl s = s
  /-- Restriction is compatible with composition of inclusions. -/
  res_comp : ∀ {U V W : Opens X} (hU : U ∈ B) (hV : V ∈ B) (hW : W ∈ B)
      (hVU : V ≤ U) (hWV : W ≤ V) (s : obj U hU),
      res hV hW hWV (res hU hV hVU s) = res hU hW (hWV.trans hVU) s

-- `_hB` (that `B` is a basis) is part of the intended statement of the sheaf-on-basis
-- condition but is not consumed by the gluing property below.
/-- The sheaf condition on a basis `B`, as in Stacks 009J: for every `U ∈ B`, every cover of `U`
by basis opens `Uᵢ`, and every choice of covers `Uᵢ ⊓ Uⱼ = ⨆ₖ V i j k` of the pairwise
intersections by basis opens, a family of sections `sᵢ` over the `Uᵢ` that agree after restriction
to every `V i j k` glues to a unique section over `U`.  The auxiliary covers are needed because
`Uᵢ ⊓ Uⱼ` need not itself belong to `B`. -/
@[ega "0 3.2.2", sga "4½ Arcata 1.2.3" "more general"]
def IsSheafOnBasis {B : Set (Opens X)} (_hB : Opens.IsBasis B)
    (F : PresheafOnBasisOpenStruct B) : Prop :=
  ∀ ⦃U : Opens X⦄ (hU : U ∈ B)
    ⦃I : Type u⦄ (Uι : I → Opens X) (hUι : ∀ i, Uι i ∈ B)
    (hcover : U = ⨆ i, Uι i)
    ⦃J : I → I → Type u⦄ (V : ∀ i j, J i j → Opens X)
    (hV : ∀ i j (k : J i j), V i j k ∈ B)
    (hVcover : ∀ i j, (Uι i) ⊓ (Uι j) = ⨆ k, V i j k)
    (s : ∀ i, F.obj (Uι i) (hUι i)),
    (∀ i j (k : J i j),
        F.res (hUι i) (hV i j k)
            (have hle : V i j k ≤ Uι i ⊓ Uι j := by
                rw [hVcover i j]; exact le_iSup (V i j) k
              hle.trans inf_le_left) (s i)
        = F.res (hUι j) (hV i j k)
            (have hle : V i j k ≤ Uι i ⊓ Uι j := by
                rw [hVcover i j]; exact le_iSup (V i j) k
              hle.trans inf_le_right) (s j)) →
    ∃! t : F.obj U hU, ∀ i,
        F.res hU (hUι i)
          (hcover ▸ le_iSup Uι i) t = s i

/-- A sheaf of sets on a basis `B` (Stacks 009J (1)): a presheaf on `B` satisfying the
basis-sheaf condition. -/
@[stacks_fixed 009J "(1)", ega "0 3.2.2"]
structure SheafOnBasis {B : Set (Opens X)} (hB : Opens.IsBasis B) where
  /-- The underlying presheaf on `B`. -/
  toPresheaf : PresheafOnBasisOpenStruct B
  /-- The gluing axiom for covers of basis opens by basis opens. -/
  isSheaf : IsSheafOnBasis hB toPresheaf

/-- A morphism `F → G` of presheaves on a basis `B`: a map of sections over each basis open,
commuting with the restriction maps. -/
@[ega "0 3.2.3" "special case"]
structure PresheafOnBasisHom {B : Set (Opens X)}
    (F G : PresheafOnBasisOpenStruct B) where
  /-- The component of the morphism over each basis open. -/
  app : ∀ {U : Opens X} (hU : U ∈ B), F.obj U hU → G.obj U hU
  /-- The components commute with restriction. -/
  naturality : ∀ {U V : Opens X} (hU : U ∈ B) (hV : V ∈ B) (hVU : V ≤ U)
      (s : F.obj U hU),
      app hV (F.res hU hV hVU s) = G.res hU hV hVU (app hU s)

/-- A morphism of sheaves on a basis `B` (Stacks 009J (2)): by definition a morphism of the
underlying presheaves on `B`. -/
@[stacks 009J "(2)", ega "0 3.2.3" "special case"]
def SheafOnBasisHom {B : Set (Opens X)} {hB : Opens.IsBasis B}
    (F G : SheafOnBasis hB) : Type _ :=
  PresheafOnBasisHom F.toPresheaf G.toPresheaf

/-- The content of Stacks 009J recorded together: a sheaf on a basis satisfies the basis gluing
axiom, and morphisms out of it are exactly morphisms of the underlying presheaves on `B`. -/
theorem main_theorem009J
    {B : Set (Opens X)} (hB : Opens.IsBasis B) (F : SheafOnBasis hB) :
    IsSheafOnBasis hB F.toPresheaf ∧
    (∀ G : SheafOnBasis hB,
      SheafOnBasisHom F G = PresheafOnBasisHom F.toPresheaf G.toPresheaf) :=
  ⟨F.isSheaf, fun _ => rfl⟩

