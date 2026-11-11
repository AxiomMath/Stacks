module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep

/-!
# Complete dévissage of a module

A *complete dévissage* of a finite-type quasi-coherent `𝒪_X`-module `F` along `f : X ⟶ S` over
a point `s : S` is a finite succession of one-step dévissages. At each stage a finite
free module on the smooth scheme `Y` maps to the direct image of the module on the closed
subscheme, and that map becomes an isomorphism over the residue field of the generic point of
the fibre of `Y ⟶ S` over `s`. The next stage is a complete dévissage of the cokernel of that
map, along the structure morphism `Y ⟶ S`, and the last cokernel is zero. Stacks' notion
(Tag 05HH) has at least one stage, since its first condition asks for a one-step dévissage of
`F` itself; it is `AlgebraicGeometry.NonemptyCompleteDevissage`. The variant
`AlgebraicGeometry.CompleteDevissage` also admits, for the zero module, the empty succession with
no stages and no conditions imposed.

A complete dévissage *at a point* `x : X` is a complete dévissage over `f x` whose successive
one-step dévissages are pointed: the first at `x`, and each later one at the distinguished
point of the preceding smooth scheme. This is the notion of the source; it can only exist when
`x` lies in the support of the fibre module, so the zero module has none. The convenience notion
`AlgebraicGeometry.CompleteDevissageAt` adds the empty dévissage of the zero module at `x`, and
coincides with it for a nonzero module.

## Main definitions

* `AlgebraicGeometry.DevissageStage`: one stage of a complete dévissage — a one-step dévissage
  together with its free-module map and the generic-fibre isomorphism.
* `AlgebraicGeometry.DevissageStage.coker`: the cokernel of a stage's free-module map, the
  module dévissed by the next stage.
* `AlgebraicGeometry.DevissageChain`: the recursively indexed data of a finite nonempty chain
  of stages, including vanishing of the final cokernel.
* `AlgebraicGeometry.NonemptyCompleteDevissage`: a complete dévissage of `F/X/S` over `s` in
  the sense of Stacks, with at least one stage.
* `AlgebraicGeometry.CompleteDevissage`: the variant of a complete dévissage of `F/X/S` over `s`
  that also allows the empty dévissage of the zero module.
* `AlgebraicGeometry.PointedDevissageStage`: a stage identified with a one-step dévissage at a
  chosen point.
* `AlgebraicGeometry.PointedDevissageChain`: the compatible distinguished points at every stage
  of a chain.
* `AlgebraicGeometry.NonemptyCompleteDevissageAt`: a complete dévissage of `F/X/S` at `x`, as
  in the source: a nonempty chain of pointed stages.
* `AlgebraicGeometry.CompleteDevissageAt`: a complete dévissage of `F/X/S` at `x` under the
  zero-module convention, allowing also the empty dévissage of the zero module.

## Main results

* `AlgebraicGeometry.NonemptyCompleteDevissageAt.mem_fiber_support`: a complete dévissage at
  `x` forces `x` into the support of the fibre module.
* `AlgebraicGeometry.CompleteDevissageAt.toNonemptyCompleteDevissageAt`: for a nonzero module
  a complete dévissage at `x` under the zero-module convention is one in the sense of the
  source; the converse direction is the constructor `CompleteDevissageAt.nonempty`.

The vanishing consequences (`AlgebraicGeometry.NonemptyCompleteDevissageAt.not_isZero` and
`AlgebraicGeometry.nonempty_nonemptyCompleteDevissageAt_iff`) are in
`StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Support`.

## Implementation notes

The chain is inductive rather than indexed by `1, …, n`: `DevissageChain.last` represents its
final stage and `DevissageChain.more` appends the dévissage of the previous cokernel. A point of
the fibre is stored together with its generic-point property; its image in the lower scheme is
the source's `ξₖ`. Pulling the free-module map back to the spectrum of that point's residue
field expresses exactly the displayed isomorphism of residue-field fibres. The
quasi-coherence, finite-type and local finite-type witnesses needed to form the next one-step
dévissage are stored as proof data; they are consequences of the preceding stage, not extra
conditions.

The module dévissed by the next stage is named `AlgebraicGeometry.DevissageStage.coker`, a
reducible abbreviation for `CategoryTheory.Limits.cokernel stage.alpha`. The name is needed
rather than cosmetic: with the cokernel written out, the recursive occurrence of
`AlgebraicGeometry.DevissageChain` carries a `HasCokernel` instance argument among its indices,
and the automatic `SizeOf` instance for the family then fails to elaborate. Naming the index
makes it elaborate, and `coker` is reducible, so every statement below is the one obtained by
writing the cokernel out.

For a pointed chain, heterogeneous equality identifies the one-step dévissage at the current
point with the stage's underlying one-step dévissage, and likewise their distinguished target
points. This lets the next stage be indexed directly by that target point without changing the
common base point of the complete dévissage. The two constructors of
`AlgebraicGeometry.PointedDevissageChain` are the introduction API for the final and the
nonfinal stages.

The empty dévissage is a separate constructor of `AlgebraicGeometry.CompleteDevissage` and of
`AlgebraicGeometry.CompleteDevissageAt`, with the chain data factored out into
`AlgebraicGeometry.NonemptyCompleteDevissage` and
`AlgebraicGeometry.NonemptyCompleteDevissageAt`. Every statement about a dévissage that
mentions its stages — base change of a chain, restriction of a chain, the distinguished points
— is a statement about the nonempty notion, and is phrased there; the empty case carries no
stages to speak about. `Module.CompleteDevissageAt` is split the same way.

This is the geometric form of the dévissage. Its ring-theoretic counterpart ([Stacks, Tag 05HX] and
[Stacks, Tag 05HZ]) is `Module.CompleteDevissage`; the two are distinct notions and neither is
formulated in terms of the other.

## References

* [Stacks Project, Tag 05HH](https://stacks.math.columbia.edu/tag/05HH)
* [Stacks Project, Tag 05HI](https://stacks.math.columbia.edu/tag/05HI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A one-step dévissage with a free-module map which is an isomorphism on the generic
fibre. -/
structure DevissageStage {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] where
  /-- The underlying one-step dévissage. -/
  oneStep : OneStepDevissage f F s
  /-- The rank of the free module. -/
  rank : ℕ
  /-- The map from the free module to the finite pushforward. -/
  alpha : SheafOfModules.free (R := oneStep.Y.ringCatSheaf) (ULift.{u} (Fin rank)) ⟶
    (Scheme.Modules.pushforward oneStep.π).obj oneStep.G
  /-- The generic point of the distinguished fibre. -/
  genericPoint : oneStep.g.fiber s
  genericPoint_spec : IsGenericPoint genericPoint Set.univ
  /-- The free-module map induces an isomorphism over the residue field of the generic
  point. -/
  genericFiber_isIso : IsIso ((Scheme.Modules.pullback
    (oneStep.Y.fromSpecResidueField (oneStep.g.fiberι s genericPoint))).map alpha)

/-- The cokernel of the free-module map of a stage. It is a module on the stage's smooth
scheme, and is the module dévissed by the next stage. -/
abbrev DevissageStage.coker {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {s : S}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (stage : DevissageStage f F s) : stage.oneStep.Y.Modules := cokernel stage.alpha

/-- The recursively indexed data of a finite nonempty dévissage. -/
inductive DevissageChain {S : Scheme.{u}} (s : S) :
    (X : Scheme.{u}) → (f : X ⟶ S) → (F : X.Modules) → LocallyOfFiniteType f →
      F.IsQuasicoherent → F.IsFiniteType → Type (u + 1) where
  /-- The last stage: its free-module map has zero cokernel. -/
  | last {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {hl : LocallyOfFiniteType f}
      {hq : F.IsQuasicoherent} {ht : F.IsFiniteType}
      (stage : @DevissageStage X S f F s hl hq ht)
      (finalCokernel : IsZero stage.coker) : DevissageChain s X f F hl hq ht
  /-- A nonfinal stage followed by a complete dévissage of its cokernel. -/
  | more {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {hl : LocallyOfFiniteType f}
      {hq : F.IsQuasicoherent} {ht : F.IsFiniteType}
      (stage : @DevissageStage X S f F s hl hq ht)
      (cokernel_quasicoherent : stage.coker.IsQuasicoherent)
      (cokernel_finiteType : stage.coker.IsFiniteType)
      (base_locallyFiniteType : LocallyOfFiniteType stage.oneStep.g)
      (tail : DevissageChain s stage.oneStep.Y stage.oneStep.g stage.coker
        base_locallyFiniteType cokernel_quasicoherent cokernel_finiteType) :
      DevissageChain s X f F hl hq ht

/-- A complete dévissage of `F/X/S` over `s`: a finite chain of stages
`(Z_k, Y_k, i_k, π_k, G_k, α_k)_{k = 1, …, n}`, with `n ≥ 1`, whose first stage is a one-step
dévissage of `F/X/S` over `s`, whose `k`-th stage for `k ≥ 2` is a one-step dévissage of
`Coker(α_{k-1})/Y_{k-1}/S` over `s`, each `α_k` inducing an isomorphism over the residue field
of the generic point of `(Y_k)_s`, and with `Coker(α_n) = 0`. -/
@[stacks 05HH]
structure NonemptyCompleteDevissage {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S)
    [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType] where
  /-- The chain of stages. -/
  chain : DevissageChain s X f F hl hq ht

/-- The zero-extended variant of a complete dévissage of `F/X/S` over `s`: either the empty
dévissage, which exists precisely for the zero module, or a complete dévissage in the sense of
[Stacks, Tag 05HH], which is `AlgebraicGeometry.NonemptyCompleteDevissage`. Stacks' definition
has no empty dévissage; this variant adds it for the zero module. -/
inductive CompleteDevissage {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S)
    [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType] where
  /-- The empty dévissage, with no stages and no conditions imposed. It exists precisely for
  the zero module. -/
  | empty (isZero : IsZero F)
  /-- A finite nonempty chain of stages satisfying the conditions of the definition. -/
  | nonempty (data : NonemptyCompleteDevissage f F s)

/-- A zero-extended complete dévissage exists exactly when the module is zero or it has a
complete dévissage in the sense of [Stacks, Tag 05HH]. -/
lemma CompleteDevissage.nonempty_iff {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] :
    Nonempty (CompleteDevissage f F s) ↔
      IsZero F ∨ Nonempty (NonemptyCompleteDevissage f F s) := by
  refine ⟨fun ⟨D⟩ => ?_, fun h => h.elim (fun hF => ⟨.empty hF⟩) fun ⟨D⟩ => ⟨.nonempty D⟩⟩
  cases D with
  | empty hF => exact .inl hF
  | nonempty D => exact .inr ⟨D⟩

/-- A stage of a complete dévissage, equipped with the one-step dévissage at the current
distinguished point. -/
structure PointedDevissageStage {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (stage : DevissageStage f F s) where
  /-- The one-step dévissage at the current point. -/
  atPoint : OneStepDevissageAt f F x
  /-- It is the one-step dévissage underlying this stage. -/
  sameOneStep : HEq atPoint.toOneStepDevissage stage.oneStep
  /-- The target point, regarded as a point of this stage's target scheme. -/
  y : stage.oneStep.Y
  /-- This is the target point supplied by the pointed one-step dévissage. -/
  sameY : HEq atPoint.y y

/-- The compatible distinguished points in a nonempty complete dévissage. -/
inductive PointedDevissageChain {S : Scheme.{u}} (s : S) :
    (X : Scheme.{u}) → (f : X ⟶ S) → (F : X.Modules) → (hl : LocallyOfFiniteType f) →
      (hq : F.IsQuasicoherent) → (ht : F.IsFiniteType) → (x : X) →
      DevissageChain s X f F hl hq ht → Type (u + 1) where
  /-- The final stage is pointed at the current point. -/
  | last {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {hl : LocallyOfFiniteType f}
      {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} (x : X)
      (stage : @DevissageStage X S f F s hl hq ht)
      (finalCokernel : IsZero stage.coker)
      (pointed : @PointedDevissageStage X S f F s x hl hq ht stage) :
      PointedDevissageChain s X f F hl hq ht x (.last stage finalCokernel)
  /-- A pointed nonfinal stage is followed by a pointed dévissage at its distinguished target
  point. -/
  | more {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {hl : LocallyOfFiniteType f}
      {hq : F.IsQuasicoherent} {ht : F.IsFiniteType} (x : X)
      (stage : @DevissageStage X S f F s hl hq ht)
      (cokernel_quasicoherent : stage.coker.IsQuasicoherent)
      (cokernel_finiteType : stage.coker.IsFiniteType)
      (base_locallyFiniteType : LocallyOfFiniteType stage.oneStep.g)
      (chain : DevissageChain s stage.oneStep.Y stage.oneStep.g stage.coker
        base_locallyFiniteType cokernel_quasicoherent cokernel_finiteType)
      (pointed : @PointedDevissageStage X S f F s x hl hq ht stage)
      (tail : PointedDevissageChain s stage.oneStep.Y stage.oneStep.g stage.coker
        base_locallyFiniteType cokernel_quasicoherent cokernel_finiteType pointed.y chain) :
      PointedDevissageChain s X f F hl hq ht x
        (.more stage cokernel_quasicoherent cokernel_finiteType base_locallyFiniteType chain)

/-- A complete dévissage of `F/X/S` at `x`, as in the source: a nonempty complete dévissage
over the image of `x` whose first stage is a one-step dévissage at `x` and each later stage a
one-step dévissage at the distinguished point of the preceding smooth scheme. Its first stage
places `x` in the support of the fibre module
(`AlgebraicGeometry.NonemptyCompleteDevissageAt.mem_fiber_support`), so the zero module has
none. -/
@[stacks 05HI]
structure NonemptyCompleteDevissageAt {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType] where
  /-- The underlying nonempty complete dévissage over the image of `x`. -/
  toNonemptyCompleteDevissage : NonemptyCompleteDevissage f F (f x)
  /-- The sequence of compatible distinguished points. -/
  pointed : PointedDevissageChain (f x) X f F hl hq ht x toNonemptyCompleteDevissage.chain

/-- A complete dévissage of `F/X/S` at `x` under the zero-module convention: either the empty
dévissage, which exists precisely for the zero module and at every point, or a complete
dévissage at `x` in the sense of the source (`AlgebraicGeometry.NonemptyCompleteDevissageAt`).
The source has no empty dévissage; for a nonzero module the two notions agree
(`AlgebraicGeometry.nonempty_nonemptyCompleteDevissageAt_iff`). -/
inductive CompleteDevissageAt {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent] [ht : F.IsFiniteType] where
  /-- The empty dévissage, with no stages and no conditions imposed. It exists precisely for
  the zero module. -/
  | empty (isZero : IsZero F)
  /-- A nonempty chain of stages with compatible distinguished points. -/
  | nonempty (data : NonemptyCompleteDevissageAt f F x)

/-- The one-step dévissage at the base point carried by the first stage of a pointed chain. -/
def PointedDevissageChain.firstAtPoint {S : Scheme.{u}} {s : S} {X : Scheme.{u}} {f : X ⟶ S}
    {F : X.Modules} {hl : LocallyOfFiniteType f} {hq : F.IsQuasicoherent} {ht : F.IsFiniteType}
    {x : X} {c : DevissageChain s X f F hl hq ht} :
    PointedDevissageChain s X f F hl hq ht x c → @OneStepDevissageAt X S f F x hl hq ht
  | .last _ _ _ pointed => pointed.atPoint
  | .more _ _ _ _ _ _ pointed _ => pointed.atPoint

variable {X S : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {x : X}
  [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]

/-- A complete dévissage of `F/X/S` at `x` places `x` in the support of the fibre module
`F_s`, `s = f x`: its first stage is a one-step dévissage at `x`. -/
theorem NonemptyCompleteDevissageAt.mem_fiber_support (D : NonemptyCompleteDevissageAt f F x) :
    f.asFiber x ∈
      SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) :=
  D.pointed.firstAtPoint.mem_fiber_support

/-- For a nonzero module, a complete dévissage at `x` under the zero-module convention is one
in the sense of the source. -/
def CompleteDevissageAt.toNonemptyCompleteDevissageAt (hF : ¬ IsZero F) :
    CompleteDevissageAt f F x → NonemptyCompleteDevissageAt f F x
  | .empty h => absurd h hF
  | .nonempty D => D

end AlgebraicGeometry

end
