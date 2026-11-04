module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Data.ZMod.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedGlobalSectionsExistence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local acyclicity of a morphism of schemes

Let `f : X ⟶ S` be a morphism of schemes, let `x` be a geometric point of `X` with image
`s = f(x)` in `S`, and let `t` be a geometric point of `Spec 𝒪^{sh}_{S,s}`. Pulling back the
strict henselization at `x` along `t` produces the *variety of vanishing cycles*

`F_{x,t} = t ×_{Spec 𝒪^{sh}_{S,s}} Spec 𝒪^{sh}_{X,x}`,

a scheme over `Spec 𝒪^{sh}_{X,x}` and hence over `X`. For an object `K` of the unbounded derived
category `D(X_étale)` of abelian sheaves on the small étale site of `X`, the stalk `K_x` is the
derived sections of `K` over the strictly henselian `Spec 𝒪^{sh}_{X,x}`, so pulling back
cohomology along the projection `F_{x,t} ⟶ Spec 𝒪^{sh}_{X,x}` gives a canonical map

`α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)`,

constructed as `AlgebraicGeometry.vanishingCyclesFibreMap`. This file defines the five notions of
local acyclicity of `f` that the vanishing of the varieties of vanishing cycles expresses: local
acyclicity at `x` relative to `K` asks that `α_{K,x,t}` be an isomorphism for every `t`, local
acyclicity relative to `K` asks this at every geometric point of `X`, the universal variants ask
it of every base change, and the absolute notions take for `K` the constant sheaf `ℤ/nℤ` for
every `n` invertible in the residue field of the geometric point. Concretely, local acyclicity
relative to a constant sheaf with value `M` says that `H^0(F_{x,t}, M) = M` and that the higher
cohomology of every variety of vanishing cycles vanishes.

## The universal notions and the big étale site

The strict henselizations, and hence the varieties of vanishing cycles, are formed inside a big
étale site `B` containing `X` and `S`; that site is a parameter of parts (1), (2) and (4), which
speak about one morphism. Parts (3) and (5), on the other hand, quantify over *every* morphism
`S' ⟶ S` of schemes, with no size restriction, so they fix no big étale site: they ask the
condition of the base change `X ×_S S' ⟶ S'` inside every big étale site that contains both of
its schemes. No base change is thereby excluded, and the condition is never void:
`AlgebraicGeometry.exists_bigEtaleSite_contains_pullback` produces, for any `f` and any
`g : S' ⟶ S`, a big étale site containing `X ×_S S'` and `S'`.

## Main definitions

* `AlgebraicGeometry.IsLocallyAcyclicAt` — part (1) of Tag 0GJP, local acyclicity at a geometric
  point relative to an object of `D(X_étale)`.
* `AlgebraicGeometry.IsLocallyAcyclicRelative` — part (2), local acyclicity relative to an object
  of `D(X_étale)`.
* `AlgebraicGeometry.IsUniversallyLocallyAcyclicRelative` — part (3), universal local acyclicity
  relative to an object of `D(X_étale)`.
* `AlgebraicGeometry.IsLocallyAcyclic` — part (4), local acyclicity, relative to the constant
  sheaves of order invertible in the residue field of the geometric point.
* `AlgebraicGeometry.IsUniversallyLocallyAcyclic` — part (5), universal local acyclicity.
* `Stacks.EtaleCohomology.smallEtaleConstantComplexAb` and
  `Stacks.EtaleCohomology.smallEtaleConstantZModComplex` — a constant abelian étale sheaf placed
  in degree zero of the unbounded derived category, and that complex for the value `ℤ/nℤ`.

## Main results

* `AlgebraicGeometry.localAcyclicity_iff_isIso_vanishingCyclesFibreMap` — **[Stacks, Tag
  0GJP]**, the whole definition: all five notions, each identified with the invertibility of the
  canonical maps `α` of Tag 0GJN that the source asks to be isomorphisms.
* `AlgebraicGeometry.exists_bigEtaleSite_contains_pullback` — every base change of `f` lies,
  together with its target, in some big étale site.

## References

* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
* [Stacks Project, Tag 0GJP](https://stacks.math.columbia.edu/tag/0GJP)
* [SGA 4½, Definition 2.12, page 242 and Definition (1.3), page 54]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Constant coefficients in the unbounded derived category -/

/-- The constant abelian sheaf with value `M` on the small étale site of a scheme `X`, viewed as
an object of `D(X_étale)` concentrated in degree zero. -/
def smallEtaleConstantComplexAb (X : Scheme.{u}) (M : Ab.{u + 1}) :
    smallEtaleDerivedCategory X :=
  (DerivedCategory.singleFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1}) 0).obj
    ((constantSheaf (smallEtaleTopology X) Ab.{u + 1}).obj M)

/-- The constant abelian étale sheaf with value `ℤ/nℤ` on a scheme `X`, viewed as an object of
`D(X_étale)` concentrated in degree zero. Étale cohomology of `X` has coefficients one universe
above the scheme, so the value is the universe lift of `ZMod n`. -/
@[sga "7 XXII 2.0" "partial"]
def smallEtaleConstantZModComplex (X : Scheme.{u}) (n : ℕ) : smallEtaleDerivedCategory X :=
  smallEtaleConstantComplexAb X (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Every base change lies in a big étale site -/

/-- **Every base change of a morphism of schemes lies, together with its target, in a big étale
site.** -/
public theorem exists_bigEtaleSite_contains_pullback {X S S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) :
    ∃ B : BigEtaleSite.{u}, B.Contains (pullback f g) ∧ B.Contains S' :=
  have := small_pair.{u} (pullback f g) S'
  ⟨BigEtaleSite.ofSet {pullback f g, S'},
    BigEtaleSite.contains_ofSet _ (by simp), BigEtaleSite.contains_ofSet _ (by simp)⟩

/-! ### Local acyclicity relative to an object of the derived category -/

/-- **Part (1) of [Stacks, Tag 0GJP].** A morphism of schemes `f : X ⟶ S` is *locally acyclic at
a geometric point `x` of `X` relative to* an object `K` of `D(X_étale)` if for every geometric
point `t` of `Spec 𝒪^{sh}_{S,f(x)}` the canonical map

`α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)`

to the derived sections of `K` on the variety of vanishing cycles `F_{x,t}` is an isomorphism.

The geometric point `t` is not assumed to be an algebraic geometric point of
`Spec 𝒪^{sh}_{S,f(x)}`, and `GeometricPoint` imposes no such condition. -/
@[sga "4½ Th_finitude 2.12"]
def IsLocallyAcyclicAt (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X)
    (hS : B.Contains S) (f : X ⟶ S) (K : smallEtaleDerivedCategory X) (x : GeometricPoint X) :
    Prop :=
  ∀ t : GeometricPoint (strictHenselization B S hS (x.map f)),
    IsIso ((vanishingCyclesFibreMap B hX hS f x t).app K)

/-- **Part (2) of [Stacks, Tag 0GJP].** A morphism of schemes `f : X ⟶ S` is *locally acyclic
relative to* an object `K` of `D(X_étale)` if it is locally acyclic relative to `K` at every
geometric point of `X`. -/
@[sga "4½ Th_finitude 2.12"]
def IsLocallyAcyclicRelative (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X)
    (hS : B.Contains S) (f : X ⟶ S) (K : smallEtaleDerivedCategory X) : Prop :=
  ∀ x : GeometricPoint X, IsLocallyAcyclicAt B hX hS f K x

/-- **Part (3) of [Stacks, Tag 0GJP].** A morphism of schemes `f : X ⟶ S` is *universally
locally acyclic relative to* an object `K` of `D(X_étale)` if for every morphism `g : S' ⟶ S` of
schemes the base change `X ×_S S' ⟶ S'` of `f` is locally acyclic relative to the inverse image
of `K` on `X ×_S S'`.

Every morphism `g : S' ⟶ S` of schemes is quantified over, and for each of them every big étale
site containing the base change and its target: local acyclicity of a morphism is a notion
relative to such a site, and no site contains all schemes. There always is one, by
`AlgebraicGeometry.exists_bigEtaleSite_contains_pullback`. -/
@[sga "4½ Th_finitude 2.12"]
def IsUniversallyLocallyAcyclicRelative {X S : Scheme.{u}} (f : X ⟶ S)
    (K : smallEtaleDerivedCategory X) : Prop :=
  ∀ (S' : Scheme.{u}) (g : S' ⟶ S) (B : BigEtaleSite.{u})
    (hX' : B.Contains (pullback f g)) (hS' : B.Contains S'),
    IsLocallyAcyclicRelative B hX' hS' (pullback.snd f g)
      ((smallEtaleDerivedPullbackAb (pullback.fst f g)).obj K)

/-! ### Local acyclicity with constant torsion coefficients -/

/-- **Part (4) of [Stacks, Tag 0GJP].** A morphism of schemes `f : X ⟶ S` is *locally acyclic* if
for every geometric point `x` of `X` and every positive `n` prime to the characteristic of the
residue field `κ(x)` it is locally acyclic at `x` relative to the constant sheaf with value
`ℤ/nℤ`.

Primality to the characteristic is spelled out: either `κ(x)` has characteristic zero, in which
case no condition on `n` beyond positivity is imposed, or `n` is coprime to that characteristic.
Together with `0 < n` this says exactly that `n` is invertible in `κ(x)`. -/
@[sga "4½ Arcata 5.1.3" "partial"]
def IsLocallyAcyclic (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X)
    (hS : B.Contains S) (f : X ⟶ S) : Prop :=
  ∀ (x : GeometricPoint X) (n : ℕ), 0 < n →
    (ringChar x.residueField = 0 ∨ n.Coprime (ringChar x.residueField)) →
      IsLocallyAcyclicAt B hX hS f (smallEtaleConstantZModComplex X n) x

/-- **Part (5) of [Stacks, Tag 0GJP].** A morphism of schemes `f : X ⟶ S` is *universally locally
acyclic* if for every morphism `g : S' ⟶ S` of schemes the base change `X ×_S S' ⟶ S'` of `f` is
locally acyclic.

As in `AlgebraicGeometry.IsUniversallyLocallyAcyclicRelative` the condition is asked of every
morphism `g : S' ⟶ S`, inside every big étale site containing the base change and its target;
`AlgebraicGeometry.exists_bigEtaleSite_contains_pullback` provides one for each `g`. -/
def IsUniversallyLocallyAcyclic {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ (S' : Scheme.{u}) (g : S' ⟶ S) (B : BigEtaleSite.{u})
    (hX' : B.Contains (pullback f g)) (hS' : B.Contains S'),
    IsLocallyAcyclic B hX' hS' (pullback.snd f g)

/-! ### The definition -/

/-- Let `f : X ⟶ S` be a morphism of schemes and let `K` be an object of `D(X_étale)`. The five
notions of the definition are, in terms of the canonical maps `α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)`
of [Stacks, Tag 0GJN]:

1. `f` is *locally acyclic at a geometric point `x` of `X` relative to `K`* when `α_{K,x,t}` is
   an isomorphism for every geometric point `t` of `Spec 𝒪^{sh}_{S,f(x)}`;
2. `f` is *locally acyclic relative to `K`* when that holds at every geometric point `x` of `X`;
3. `f` is *universally locally acyclic relative to `K`* when for every morphism `g : S' ⟶ S` of
   schemes the base change `X ×_S S' ⟶ S'` is locally acyclic relative to the inverse image of
   `K`;
4. `f` is *locally acyclic* when for every geometric point `x` of `X` and every positive integer
   `n` prime to the characteristic of `κ(x)` it is locally acyclic at `x` relative to the
   constant sheaf `ℤ/nℤ`;
5. `f` is *universally locally acyclic* when every base change of `f` is locally acyclic.

The geometric points `t` are not assumed to be algebraic geometric points of
`Spec 𝒪^{sh}_{S,f(x)}`: `GeometricPoint` asks only for a morphism from the spectrum of an
algebraically closed field.

The varieties of vanishing cycles are formed inside a big étale site, so clauses (1), (2) and
(4) carry one; clauses (3) and (5) quantify over all morphisms `g : S' ⟶ S` and over all big
étale sites containing `X ×_S S'` and `S'`, of which there is always at least one
(`AlgebraicGeometry.exists_bigEtaleSite_contains_pullback`). -/
@[stacks 0GJP]
public theorem localAcyclicity_iff_isIso_vanishingCyclesFibreMap (B : BigEtaleSite.{u})
    {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S)
    (K : smallEtaleDerivedCategory X) :
    (∀ x : GeometricPoint X, IsLocallyAcyclicAt B hX hS f K x ↔
        ∀ t : GeometricPoint (strictHenselization B S hS (x.map f)),
          IsIso ((vanishingCyclesFibreMap B hX hS f x t).app K)) ∧
      (IsLocallyAcyclicRelative B hX hS f K ↔
        ∀ (x : GeometricPoint X)
          (t : GeometricPoint (strictHenselization B S hS (x.map f))),
          IsIso ((vanishingCyclesFibreMap B hX hS f x t).app K)) ∧
      (IsUniversallyLocallyAcyclicRelative f K ↔
        ∀ (S' : Scheme.{u}) (g : S' ⟶ S) (B' : BigEtaleSite.{u})
          (hX' : B'.Contains (pullback f g)) (hS' : B'.Contains S')
          (x' : GeometricPoint (pullback f g))
          (t' : GeometricPoint
            (strictHenselization B' S' hS' (x'.map (pullback.snd f g)))),
          IsIso ((vanishingCyclesFibreMap B' hX' hS'
              (pullback.snd f g) x' t').app
            ((smallEtaleDerivedPullbackAb (pullback.fst f g)).obj K))) ∧
      (IsLocallyAcyclic B hX hS f ↔
        ∀ (x : GeometricPoint X) (n : ℕ), 0 < n →
          (ringChar x.residueField = 0 ∨ n.Coprime (ringChar x.residueField)) →
            ∀ t : GeometricPoint (strictHenselization B S hS (x.map f)),
              IsIso ((vanishingCyclesFibreMap B hX hS f x t).app
                (smallEtaleConstantZModComplex X n))) ∧
      (IsUniversallyLocallyAcyclic f ↔
        ∀ (S' : Scheme.{u}) (g : S' ⟶ S) (B' : BigEtaleSite.{u})
          (hX' : B'.Contains (pullback f g)) (hS' : B'.Contains S')
          (x' : GeometricPoint (pullback f g)) (n : ℕ), 0 < n →
          (ringChar x'.residueField = 0 ∨ n.Coprime (ringChar x'.residueField)) →
            ∀ t' : GeometricPoint
              (strictHenselization B' S' hS' (x'.map (pullback.snd f g))),
              IsIso ((vanishingCyclesFibreMap B' hX' hS'
                  (pullback.snd f g) x' t').app
                (smallEtaleConstantZModComplex (pullback f g) n))) :=
  ⟨fun _ => Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

end AlgebraicGeometry

end
