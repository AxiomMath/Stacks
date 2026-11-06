module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutation
public import StacksFrontier.RingTheory.ULiftRingModules

/-!
# Stacks 0DZ2 is false at every universe

`StacksFrontier.Deformation.Examples.Linear.NodalCubicRefutation` refutes
`Deformation.FlatModuleLiftBaseChangeStatement.{0}`: its counterexample rings are built from
`ZMod 2` and so live in `Type`. This file removes the restriction to universe zero. The six rings
of the counterexample are replaced by their `ULift`s, every hypothesis of Stacks 0DZ2 is
transported with the toolkit of `StacksFrontier.RingTheory.ULiftRingModules`, and the contradiction is
derived at universe `u`.

## What makes this work, and what does not

The tempting route — transport the *statement*, `Statement.{u} → Statement.{0}` — is obstructed,
and not by plumbing. The conclusion of 0DZ2 is an existential over a module in `Type u`, and a
`Type u` lift of a `Type 0` module is not in general the `ULift` of one; bringing it down would
need the lift to be finitely generated over `P'`, which is a Nakayama argument and is not
available from 0DZ2's own hypotheses. What does work is to instantiate `Statement.{u}` at the
lifted counterexample and derive the contradiction upstairs, because
`Deformation.Examples.ArtinSchreier.not_flat_lift_of_reduction` — the mathematical heart of layer
seventeen — is already polymorphic in the lift's type.

Two hypotheses carry all the content of the transport.

* **`hlocal`** is the one clause whose objects the statement forms itself: `Localization.Away g`
  for `g : ULift P'`, which the caller cannot choose. It is reached by
  `Stacks.ULiftTransport.isLocalization_away_ulift`, which identifies `ULift ((P')_g)` as *a*
  localization of `ULift P'` away from `g`, hence isomorphic to the one the statement names; the
  comparison equivalence is then carried across that isomorphism and up the universe by
  `Stacks.ULiftTransport.tensorUliftCongrOfRingEquiv`. This is
  `Deformation.Examples.ArtinSchreier.exists_local_lift_ulift`.
* **the failing conclusion** needs a `P'`-module lift in `Type u` to be impossible, which is
  `Deformation.Examples.ArtinSchreier.not_lift_of_tensorEquiv_ulift`: the reduction map
  `y ↦ e (1 ⊗ y)` of a putative lift is fed to layer seventeen after restricting its scalars
  from `ULift A'` to `A'`, and the kernel clause — `1 ⊗ y = 0` forces `y ∈ t · M'` — comes from
  `Stacks.ULiftTransport.eq_smul_of_tmul_eq_zero`, which is Mathlib's
  `TensorProduct.quotTensorEquivQuotSMul` read through the first isomorphism theorem so that it
  applies to an abstract `P` carrying the kernel identity rather than to a literal quotient.

## The rings are left abstract on purpose

Every lemma below that mentions a tensor product keeps its upper ring — `R₁`, `R₂`, `P`, `Q` —
as a type *variable*, and the main theorem instantiates it. This is not stylistic. Instance
search cannot find `Module PRed QRed` on these concrete rings inside its heartbeat budget, and
therefore cannot find `Module (ULift P) (ULift P ⊗[ULift P'] M')` either; with the ring abstract
the same searches are immediate, and — more importantly — the instances in the lemma's statement
are then the *same* generic terms that the quantified
`Deformation.FlatModuleLiftBaseChangeStatement` carries, so the two match without a defeq check.
Written at the concrete rings they do not match, and the unifier spends the whole declaration's
budget discovering it. The two places where a concrete `Module` could not be avoided are
declared as named local instances, `moduleUliftPRedQRed` and `algebraABaseNC`, each placed as
late in the file as it can be: a `Module` or `Algebra` on the *base* rings in scope makes
instance search resolve `SMul (ULift A') (ULift P')` through `ULift.smulLeft` rather than through
`Algebra.toSMul`, and the scalar towers of `Stacks.ULiftTransport.isScalarTower_ulift` then no
longer apply to what is in the goal.

## Main results

* `Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement_ulift`:
  **`¬ Deformation.FlatModuleLiftBaseChangeStatement.{u}`, for every `u`.**

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Deformation.Examples.MaurerCartanWindow
open Stacks.ULiftTransport
open scoped TensorProduct

universe u v

namespace Deformation.Examples.ArtinSchreier

/-! ### The local clause -/

/-- `(P)_ḡ`: the localization of `P` at the image of `g`, in `Type 0`. -/
abbrev PRedAway (g : PBase) : Type := Localization.Away (algebraMap PBase PRed g)

/-- `(P')_g` carried to universe `u`. -/
abbrev PAwayU (g : ULift.{u} PBase) : Type u := ULift.{u} (PAway g.down)

/-- `(P)_ḡ` carried to universe `u`. -/
abbrev PRedAwayU (g : ULift.{u} PBase) : Type u := ULift.{u} (PRedAway g.down)

/-- The localized map `R_g → S_{f g}` sends the image of `p` to the image of `p`. -/
private theorem awayMap_algebraMap_away {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (g p : R) :
    Localization.awayMap (algebraMap R S) g (algebraMap R (Localization.Away g) p) =
      algebraMap R (Localization.Away (algebraMap R S g)) p := by
  rw [show Localization.awayMap (algebraMap R S) g (algebraMap R (Localization.Away g) p) =
      algebraMap S (Localization.Away (algebraMap R S g)) (algebraMap R S p) from
    IsLocalization.map_eq _ p,
    ← IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S g))]

/-- **`hlocal` of Stacks 0DZ2 for the counterexample, at a general universe.** -/
theorem exists_local_lift_ulift (g : ULift.{u} PBase)
    (hg₀ : g.down ∈ Ideal.span {omegaP})
    (R₁ R₂ : Type u) [CommRing R₁] [CommRing R₂]
    [Algebra (ULift.{u} PBase) R₁] [IsLocalization.Away g R₁]
    [Algebra (ULift.{u} PRed) R₂]
    [IsLocalization.Away (algebraMap (ULift.{u} PBase) (ULift.{u} PRed) g) R₂]
    [Algebra R₁ R₂] [Algebra (ULift.{u} PBase) R₂]
    [IsScalarTower (ULift.{u} PBase) (ULift.{u} PRed) R₂]
    [Algebra (ULift.{u} ABase) R₁] [IsScalarTower (ULift.{u} ABase) (ULift.{u} PBase) R₁]
    (hcomp : ∀ p : ULift.{u} PBase,
      algebraMap R₁ R₂ (algebraMap (ULift.{u} PBase) R₁ p) = algebraMap (ULift.{u} PBase) R₂ p) :
    ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module R₁ L) (_ : Module (ULift.{u} ABase) L)
      (_ : IsScalarTower (ULift.{u} ABase) R₁ L),
      Module.Flat (ULift.{u} ABase) L ∧
        Nonempty ((R₂ ⊗[R₁] L) ≃ₗ[R₂] (R₂ ⊗[ULift.{u} PRed] (ULift.{u} NC))) := by
  have : IsScalarTower (ULift.{u} PBase) R₁ R₂ :=
    IsScalarTower.of_algebraMap_eq fun p => (hcomp p).symm
  -- the `Type 0` local lift, with the square it sits in
  let : Algebra (PAway g.down) (PRedAway g.down) :=
    (Localization.awayMap (algebraMap PBase PRed) g.down).toAlgebra
  have htow₀ : IsScalarTower PBase (PAway g.down) (PRedAway g.down) :=
    IsScalarTower.of_algebraMap_eq fun p => (awayMap_algebraMap_away g.down p).symm
  obtain ⟨L₀, _, _, _, _, hflat₀, ⟨E₀⟩⟩ := hlocal_nodal hg₀
  -- the two localizations of the lifted rings are the `ULift`s of the `Type 0` ones
  have hl1 : IsLocalization.Away g (PAwayU g) :=
    isLocalization_away_ulift.{u} g.down (PAway g.down)
  have γ₁ : PAwayU g ≃ₐ[ULift.{u} PBase] R₁ :=
    IsLocalization.algEquiv (Submonoid.powers g) _ _
  have hl2 : IsLocalization.Away (algebraMap (ULift.{u} PBase) (ULift.{u} PRed) g)
      (PRedAwayU g) :=
    isLocalization_away_ulift.{u} (algebraMap PBase PRed g.down) (PRedAway g.down)
  have γ₂ : PRedAwayU g ≃ₐ[ULift.{u} PRed] R₂ :=
    IsLocalization.algEquiv
      (Submonoid.powers (algebraMap (ULift.{u} PBase) (ULift.{u} PRed) g)) _ _
  let : Algebra (PRedAwayU g) R₂ := RingHom.toAlgebra (γ₂ : PRedAwayU g →+* R₂)
  let : Algebra (PAwayU g) R₂ :=
    RingHom.toAlgebra ((algebraMap R₁ R₂).comp (γ₁ : PAwayU g →+* R₁))
  let : Module R₁ (ULift.{u} L₀) :=
    Module.compHom _ (γ₁.symm : R₁ →+* PAwayU g)
  -- the towers the base changes need
  have := isScalarTower_ulift.{u} PBase (PAway g.down) (PRedAway g.down)
  have := isScalarTower_ulift.{u} PBase PRed (PRedAway g.down)
  have := isScalarTower_ulift.{u} ABase PBase (PAway g.down)
  have tPRS : IsScalarTower (ULift.{u} PRed) (PRedAwayU g) R₂ :=
    IsScalarTower.of_algebraMap_eq fun q => (γ₂.commutes q).symm
  have hext : (algebraMap (PAwayU g) R₂ : PAwayU g →+* R₂) =
      (algebraMap (PRedAwayU g) R₂).comp (algebraMap (PAwayU g) (PRedAwayU g)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) ?_
    ext p
    simp only [RingHom.coe_comp, Function.comp_apply]
    show algebraMap R₁ R₂ (γ₁ (algebraMap (ULift.{u} PBase) (PAwayU g) p)) = _
    rw [γ₁.commutes, ← IsScalarTower.algebraMap_apply (ULift.{u} PBase) R₁ R₂,
      ← IsScalarTower.algebraMap_apply (ULift.{u} PBase) (PAwayU g) (PRedAwayU g),
      IsScalarTower.algebraMap_apply (ULift.{u} PBase) (ULift.{u} PRed) (PRedAwayU g)]
    show _ = γ₂ (algebraMap (ULift.{u} PRed) (PRedAwayU g) _)
    rw [γ₂.commutes, ← IsScalarTower.algebraMap_apply (ULift.{u} PBase) (ULift.{u} PRed) R₂]
  have tS12 : IsScalarTower (PAwayU g) (PRedAwayU g) R₂ :=
    IsScalarTower.of_algebraMap_eq fun s => RingHom.congr_fun hext s
  have tAR1L : IsScalarTower (ULift.{u} ABase) R₁ (ULift.{u} L₀) :=
    IsScalarTower.of_algebraMap_smul fun a x => by
      show γ₁.symm (algebraMap (ULift.{u} ABase) R₁ a) • x = a • x
      rw [IsScalarTower.algebraMap_apply (ULift.{u} ABase) (ULift.{u} PBase) R₁ a,
        γ₁.symm.commutes, ← IsScalarTower.algebraMap_apply (ULift.{u} ABase)
          (ULift.{u} PBase) (PAwayU g), algebraMap_ulift_apply]
      exact ULift.ext (IsScalarTower.algebraMap_smul (PAway g.down) a.down x.down)
  exact ⟨ULift.{u} L₀, inferInstance, inferInstance, inferInstance, inferInstance,
    flat_ulift.{u} hflat₀,
    ⟨tensorUliftCongrOfRingEquiv γ₁.toRingEquiv (fun _ => rfl) (fun t x => by
      show t • x = γ₁.symm (γ₁ t) • x
      rw [AlgEquiv.symm_apply_apply]) E₀⟩⟩

/-- The structure map `P' → (P)_ḡ` factors through `(P')_g`, after `ULift`. This is the
compatibility `Deformation.Examples.ArtinSchreier.exists_local_lift_ulift` asks for, isolated so
that it is proved in its own declaration: it mentions no tensor product, so its statement costs
nothing to elaborate. -/
theorem awayMap_algebraMap_ulift (g p : ULift.{u} PBase) :
    Localization.awayMap (algebraMap (ULift.{u} PBase) (ULift.{u} PRed)) g
        (algebraMap (ULift.{u} PBase) (Localization.Away g) p) =
      algebraMap (ULift.{u} PBase)
        (Localization.Away (algebraMap (ULift.{u} PBase) (ULift.{u} PRed) g)) p := by
  exact awayMap_algebraMap_away g p

/-! ### The negative half at a general universe -/

/-- **`M = P/(x)` has no `A'`-flat `P'`-module lift, for a lift in any universe.** -/
theorem not_flat_lift_of_reduction_ulift {M' : Type v} [AddCommGroup M']
    [Module (ULift.{u} PBase) M'] [Module (ULift.{u} ABase) M']
    [IsScalarTower (ULift.{u} ABase) (ULift.{u} PBase) M']
    (hflat : Module.Flat (ULift.{u} ABase) M')
    (f : M' → NC)
    (hadd : ∀ y z : M', f (y + z) = f y + f z)
    (hsmul : ∀ (p : PBase) (y : M'), f ((ULift.up.{u} p) • y) = pBaseToNC p * f y)
    (hsurj : Function.Surjective f)
    (hkerf : ∀ y : M', f y = 0 → ∃ w : M', y = (ULift.up.{u} tauP) • w) : False := by
  let : Module PBase M' := Module.compHom M' (algebraMap PBase (ULift.{u} PBase))
  let : Module ABase M' := Module.compHom M' (algebraMap ABase (ULift.{u} ABase))
  have : IsScalarTower ABase PBase M' :=
    IsScalarTower.of_algebraMap_smul fun a y =>
      IsScalarTower.algebraMap_smul (ULift.{u} PBase) (ULift.up.{u} a) y
  have : Module.Flat ABase M' := flat_of_ulift_left.{u} ABase M' hflat
  exact not_flat_lift_of_reduction f hadd hsmul hsurj hkerf

/-! ### The contradiction from a lift -/

/-- **A lift of `M` over `P'` in any universe is impossible.** The reduction map
`y ↦ e (1 ⊗ y)` of the lift satisfies the four hypotheses of
`Deformation.Examples.ArtinSchreier.not_flat_lift_of_reduction_ulift`: additivity and
semilinearity come from `e`, surjectivity from the surjectivity of `P' → P` (every element of
`P ⊗_{P'} M'` is `1 ⊗ y`), and the kernel condition from
`Stacks.ULiftTransport.eq_smul_of_tmul_eq_zero`.

`P` is left abstract, with its three properties as hypotheses, rather than written as
`ULift P`: `Deformation.FlatModuleLiftBaseChangeStatement` quantifies over it, so instantiating
it at an abstract ring makes the instances of this statement the *same* generic terms the
quantified statement carries, and the two match without a search. Written at `ULift P` they would
not, and instance search cannot find `Module (ULift P) (ULift P ⊗[ULift P'] M')` on these
concrete rings within its heartbeat budget. -/
theorem not_lift_of_tensorEquiv_ulift {P : Type u} [CommRing P]
    [Algebra (ULift.{u} PBase) P] [Algebra P (ULift.{u} NC)]
    {M' : Type u} [AddCommGroup M'] [Module (ULift.{u} PBase) M']
    [Module (ULift.{u} ABase) M'] [IsScalarTower (ULift.{u} ABase) (ULift.{u} PBase) M']
    (hflat : Module.Flat (ULift.{u} ABase) M')
    (hsurj : Function.Surjective (algebraMap (ULift.{u} PBase) P))
    (hker : RingHom.ker (algebraMap (ULift.{u} PBase) P) = Ideal.span {ULift.up.{u} tauP})
    (hphi : ∀ p : PBase, algebraMap P (ULift.{u} NC)
      (algebraMap (ULift.{u} PBase) P (ULift.up.{u} p)) = ULift.up.{u} (pBaseToNC p))
    (e : (P ⊗[ULift.{u} PBase] M') ≃ₗ[P] (ULift.{u} NC)) :
    False := by
  have htmul : ∀ w : P ⊗[ULift.{u} PBase] M', ∃ y : M', w = 1 ⊗ₜ[ULift.{u} PBase] y := by
    refine fun w => TensorProduct.inductionOn w ?_ ?_
    · intro r y
      obtain ⟨p, rfl⟩ := hsurj r
      refine ⟨p • y, ?_⟩
      rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    · rintro w₁ w₂ ⟨y₁, rfl⟩ ⟨y₂, rfl⟩
      exact ⟨y₁ + y₂, (TensorProduct.tmul_add _ _ _).symm⟩
  have hsm : ∀ (p : PBase) (y : M'),
      e ((1 : P) ⊗ₜ[ULift.{u} PBase] ((ULift.up.{u} p) • y))
        = ULift.up.{u} (pBaseToNC p) * e (1 ⊗ₜ[ULift.{u} PBase] y) := by
    intro p y
    have h1 := e.map_smul (algebraMap (ULift.{u} PBase) P (ULift.up.{u} p))
      ((1 : P) ⊗ₜ[ULift.{u} PBase] y)
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
      TensorProduct.tmul_eq_smul_one_tmul, h1, Algebra.smul_def, hphi]
  refine not_flat_lift_of_reduction_ulift.{u} hflat
    (fun y => (e (1 ⊗ₜ[ULift.{u} PBase] y)).down) ?_ ?_ ?_ ?_
  · intro y z
    show (e ((1 : P) ⊗ₜ[ULift.{u} PBase] (y + z))).down = _
    rw [TensorProduct.tmul_add, map_add]
    rfl
  · intro p y
    show (e ((1 : P) ⊗ₜ[ULift.{u} PBase] ((ULift.up.{u} p) • y))).down = _
    rw [hsm p y]
    rfl
  · intro n
    obtain ⟨y, hy⟩ := htmul (e.symm (ULift.up.{u} n))
    refine ⟨y, ?_⟩
    show (e ((1 : P) ⊗ₜ[ULift.{u} PBase] y)).down = n
    rw [← hy, e.apply_symm_apply]
  · intro y hy
    have hy' : (e ((1 : P) ⊗ₜ[ULift.{u} PBase] y)).down = 0 := hy
    have h0 : (1 : P) ⊗ₜ[ULift.{u} PBase] y = 0 :=
      e.injective ((ULift.ext hy').trans (map_zero e).symm)
    exact eq_smul_of_tmul_eq_zero hsurj hker h0

/-! ### The lift on the `Q'` side -/

/-- `Q` as a `P`-module, named so that it can be written down. Instance search cannot find
`Module PRed QRed` on these concrete rings within its heartbeat budget, so neither can it find
`Module (ULift P) (ULift Q)` through `ULift.module`. This is the `Algebra.toModule` of the
`Algebra (ULift P) (ULift Q)` that `Deformation.FlatModuleLiftBaseChangeStatement` is
instantiated at, so a statement written with it matches the instantiated statement on the nose. -/
local instance moduleUliftPRedQRed : Module (ULift.{u} PRed) (ULift.{u} QRed) :=
  Algebra.toModule

/-- **The comparison of the two presentations of `N`, carried up a universe.** Layer sixteen's
`qLiftComparison` identifies `Q ⊗_{Q'} N'` with `Q ⧸ (x̄)·Q`, and layer eighteen's
`ncTensorComparison` identifies that with `Q ⊗_P M`; this is their composite, carried up by
`Stacks.ULiftTransport.tensorUliftCongr`. -/
def qLiftComparisonUlift :
    (ULift.{u} QRed ⊗[ULift.{u} QBase] ULift.{u} QLift) ≃ₗ[ULift.{u} QRed]
      (ULift.{u} QRed ⊗[ULift.{u} PRed] (ULift.{u} NC)) :=
  tensorUliftCongr.{u} (qLiftComparison.trans ncTensorComparison).toLinearEquiv

/-! ### The reduction `A' → A`, and the kernel identities -/

/-- `M = NC` as an `A'`-algebra through the reduction `redA`. This is the `Algebra A' A` of
Stacks 0DZ2 for the counterexample; the refutation at universe zero introduces it with a `letI`
inside its proof, and it is needed here to form `Algebra (ULift A') (ULift A)`. It is declared
only now because the lemmas above must be elaborated without it: with it in scope instance search
resolves `SMul (ULift A') (ULift Q')` differently, and their statements would then no longer
match the statement being instantiated. -/
local instance algebraABaseNC : Algebra ABase NC := redA.toAlgebra

/-- **`hnilA` of Stacks 0DZ2 for the lifted counterexample**: the kernel of `A' → A` is
nilpotent. -/
theorem isNilpotent_ker_ulift :
    IsNilpotent (RingHom.ker (algebraMap (ULift.{u} ABase) (ULift.{u} NC))) := by
  rw [ker_algebraMap_ulift.{u} ABase NC]
  exact isNilpotent_map_self_ulift.{u} ABase isNilpotent_ker_redA

/-- **`hkerP` of Stacks 0DZ2 for the lifted counterexample**: the kernel of `P' → P` is the
ideal generated by the image of the kernel of `A' → A`. -/
theorem ker_PBase_PRed_eq_map_ulift :
    RingHom.ker (algebraMap (ULift.{u} PBase) (ULift.{u} PRed)) =
      (RingHom.ker (algebraMap (ULift.{u} ABase) (ULift.{u} NC))).map
        (algebraMap (ULift.{u} ABase) (ULift.{u} PBase)) := by
  rw [ker_algebraMap_ulift.{u} PBase PRed, ker_algebraMap_ulift.{u} ABase NC,
    map_map_self_ulift.{u} ABase PBase, ker_PBase_PRed_eq_map,
    show RingHom.ker redA = RingHom.ker (algebraMap ABase NC) from rfl]

/-- **`hkerQ` of Stacks 0DZ2 for the lifted counterexample**: the same for `Q' → Q`. -/
theorem ker_QBase_QRed_eq_map_ulift :
    RingHom.ker (algebraMap (ULift.{u} QBase) (ULift.{u} QRed)) =
      (RingHom.ker (algebraMap (ULift.{u} ABase) (ULift.{u} NC))).map
        (algebraMap (ULift.{u} ABase) (ULift.{u} QBase)) := by
  rw [ker_algebraMap_ulift.{u} QBase QRed, ker_algebraMap_ulift.{u} ABase NC,
    map_map_self_ulift.{u} ABase QBase, ker_QBase_QRed_eq_map,
    show RingHom.ker redA = RingHom.ker (algebraMap ABase NC) from rfl]

/-- The kernel of `P' → P` after `ULift` is generated by the lifted `t`. -/
theorem ker_PBase_PRed_ulift :
    RingHom.ker (algebraMap (ULift.{u} PBase) (ULift.{u} PRed)) =
      Ideal.span {ULift.up.{u} tauP} := by
  rw [ker_algebraMap_ulift.{u} PBase PRed, ker_PBase_PRed, Ideal.map_span,
    Set.image_singleton]
  rfl

/-! ### The refutation at a general universe -/

/-- **Stacks 0DZ2, at the source's hypotheses and restricted to a finite module, is false at
every universe.** -/
theorem not_flatModuleLiftBaseChangeStatement_ulift :
    ¬ Deformation.FlatModuleLiftBaseChangeStatement.{u} := by
  intro h
  let : Module ABase PBase := Algebra.toModule
  let : Module ABase QBase := Algebra.toModule
  let : Module PBase QBase := Algebra.toModule
  let : Module PRed QRed := Algebra.toModule
  let : Module (ULift.{u} PRed) (ULift.{u} NC) := Algebra.toModule
  let : Module (ULift.{u} NC) (ULift.{u} NC) := Semiring.toModule
  have : IsScalarTower (ULift.{u} NC) (ULift.{u} PRed) (ULift.{u} NC) :=
    ⟨fun a p x => ULift.ext (smul_assoc a.down p.down x.down)⟩
  have : Module.Finite (ULift.{u} PRed) (ULift.{u} NC) := finite_ulift.{u} finite_NC
  have : Module.Flat (ULift.{u} NC) (ULift.{u} NC) := Module.Flat.self
  have := IsScalarTower.of_algebraMap_eq (R := ABase) (S := NC) (A := PRed)
    (fun a => algebraMap_ABase_PRed_eq a)
  have := isScalarTower_NC_PRed_QRed
  have := isNoetherianRing_ulift.{u} ABase
  have := isNoetherianRing_ulift.{u} NC
  have := isNoetherianRing_ulift.{u} PBase
  have := isNoetherianRing_ulift.{u} PRed
  have := isNoetherianRing_ulift.{u} QBase
  have := isNoetherianRing_ulift.{u} QRed
  have := isScalarTower_ulift.{u} ABase NC PRed
  have := isScalarTower_ulift.{u} ABase PBase PRed
  have := isScalarTower_ulift.{u} ABase PBase QBase
  have := isScalarTower_ulift.{u} ABase QBase QRed
  have := isScalarTower_ulift.{u} NC PRed QRed
  have := isScalarTower_ulift.{u} PBase PRed QRed
  have := isScalarTower_ulift.{u} PBase QBase QRed
  have key := h (ULift.{u} ABase) (ULift.{u} NC) (ULift.{u} PBase) (ULift.{u} PRed)
    (ULift.{u} QBase) (ULift.{u} QRed)
    (surjective_algebraMap_ulift.{u} ABase NC redA_surjective) isNilpotent_ker_ulift.{u}
    (surjective_algebraMap_ulift.{u} PBase PRed surjective_PBase_PRed)
    ker_PBase_PRed_eq_map_ulift.{u}
    (surjective_algebraMap_ulift.{u} QBase QRed surjective_QBase_QRed)
    ker_QBase_QRed_eq_map_ulift.{u}
    (flat_ulift.{u} flat_PBase) (flat_ulift.{u} flat_QBase_ABase)
    (flat_ulift.{u} flat_QBase_PBase) (flat_ulift.{u} flat_QRed_PRed)
    ((Ideal.span {omegaP}).map (algebraMap PBase (ULift.{u} PBase)))
    (bijective_quotientMap_ulift.{u} PBase QBase (Ideal.span {omegaP})
      bijective_quotientMap_omegaP)
    (ULift.{u} NC) ((ULift.{u} QRed) ⊗[ULift.{u} PRed] (ULift.{u} NC))
    ⟨LinearEquiv.refl _ _⟩
    (fun g hg => by
      let : Algebra (Localization.Away g)
          (Localization.Away (algebraMap (ULift.{u} PBase) (ULift.{u} PRed) g)) :=
        (Localization.awayMap (algebraMap (ULift.{u} PBase) (ULift.{u} PRed)) g).toAlgebra
      exact exists_local_lift_ulift g ((mem_map_self_ulift.{u} PBase _ g).1 hg)
        (Localization.Away g) _ (awayMap_algebraMap_ulift.{u} g))
  obtain ⟨M', _, _, _, _, hflatM, ⟨e⟩⟩ := key.2
    ⟨ULift.{u} QLift, inferInstance, inferInstance, inferInstance, inferInstance,
      flat_ulift.{u} flat_QLift, ⟨qLiftComparisonUlift.{u}⟩⟩
  exact not_lift_of_tensorEquiv_ulift.{u} hflatM
    (surjective_algebraMap_ulift.{u} PBase PRed surjective_PBase_PRed)
    ker_PBase_PRed_ulift.{u} (fun _ => rfl) e

end Deformation.Examples.ArtinSchreier

end
