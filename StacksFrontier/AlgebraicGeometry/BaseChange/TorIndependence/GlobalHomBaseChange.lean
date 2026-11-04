module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.DerivedTildeTorAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.GlobalBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The global derived Hom comparison of a base-change square, and its Tor-dimension input

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes and let `M, K` be objects of `D(𝒪_X)`.  The derived internal
hom `R𝓗om_{𝒪_X}(M, K)` of Stacks 08DI carries a canonical comparison

`Lg^*(Rf_* R𝓗om_{𝒪_X}(M, K)) ⟶ Rf'_*(R𝓗om_{𝒪_{X'}}(L(g')^*M, L(g')^*K))`,

the derived base-change map of Stacks 08HY at `R𝓗om_{𝒪_X}(M, K)` followed by the derived direct
image along `f'` of the pullback comparison of Stacks 08I3.  When `S = Spec R` and `S' = Spec R'`
this module also shows that finite Tor dimension of `R'` over `R` makes `Lf^*((R')^~)` — the
complex Stacks 08IB identifies with `g'_*𝒪_{X'}` — of finite Tor dimension on `X`.

## Main definitions

* `AlgebraicGeometry.GlobalHomBaseChange.derivedHom`: `R𝓗om_{𝒪_X}(M, K)` on a scheme.
* `AlgebraicGeometry.GlobalHomBaseChange.map`: the canonical comparison displayed above.
* `AlgebraicGeometry.GlobalHomBaseChange.algebraComplex`: the `R`-algebra `R'` in degree zero.
* `AlgebraicGeometry.GlobalHomBaseChange.baseChangeStructureSheafComplex`: the object
  `Lf^*((R')^~)` of `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.GlobalHomBaseChange.hasFiniteTorDimension_baseChangeStructureSheafComplex`:
  if `R'` has finite Tor dimension over `R` then `Lf^*((R')^~)` has finite Tor dimension on `X`.
* `AlgebraicGeometry.GlobalHomBaseChange.isIso_map`: the comparison is invertible when both of
  its factors are.

## References

* [Stacks Project, Tag 0AA7](https://stacks.math.columbia.edu/tag/0AA7)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08E9](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Tag 09U8](https://stacks.math.columbia.edu/tag/09U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.DerivedInternalHomPullback

namespace AlgebraicGeometry.GlobalHomBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

-- The derived pullback and the derived internal hom name the structure sheaf of a ringed space
-- differently, by `structureSheafRing` and by `Stacks.SheafOfModules.Tensor.ringSheaf`; the two
-- are the same sheaf of rings by `rfl`, and the statements below mix them.
-- `structureSheafRing` is `@[instance_reducible]`, so it is already unfolded both by instance
-- search and at `implicit` transparency, but its reduct stops at an explicit-constructor
-- projection while `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`;
-- these two Mathlib definitions are the gap between them.  They are needed here because
-- `derivedPullbackSheafHomMap` is applied to objects named at the `Modules` spelling.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X X' S S' : Scheme.{u}}

/-- `R𝓗om_{𝒪_X}(M, K)`, the derived internal hom of Stacks 08DI on a scheme. -/
public abbrev derivedHom (X : Scheme.{u}) (M K : DerivedCategory X.Modules) :
    DerivedCategory X.Modules :=
  ((Stacks.SheafOfModules.derivedSheafHom X.toRingedSpace.sheaf).obj (op M)).obj K

/-- **The canonical comparison**
`Lg^*(Rf_* R𝓗om_{𝒪_X}(M, K)) ⟶ Rf'_*(R𝓗om_{𝒪_{X'}}(L(g')^*M, L(g')^*K))`
attached to a commutative square of schemes: the derived base-change map of Stacks 08HY at the
derived internal hom, followed by the derived direct image along `f'` of the pullback comparison
of Stacks 08I3.  Over affine bases its derived global sections are the map of Stacks 0AA7. -/
public def map (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (M K : DerivedCategory X.Modules) :
    (derivedPullback g.toLRSHom.toShHom).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj (derivedHom X M K)) ⟶
      (derivedPushforward f'.toLRSHom.toShHom).obj
        (derivedHom X' ((derivedPullback g'.toLRSHom.toShHom).obj M)
          ((derivedPullback g'.toLRSHom.toShHom).obj K)) :=
  derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
      g.toLRSHom.toShHom (comp_toShHom_of_comm w) (derivedHom X M K) ≫
    (derivedPushforward f'.toLRSHom.toShHom).map
      (derivedPullbackSheafHomMap g'.toLRSHom.toShHom M K)

/-- **The canonical comparison is invertible when both of its factors are**: the derived
base-change map of Stacks 08HY at `R𝓗om_{𝒪_X}(M, K)` and the pullback comparison of
Stacks 08I3. -/
public theorem isIso_map (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (w : g' ≫ f = f' ≫ g) (M K : DerivedCategory X.Modules)
    (hbc : IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom
      f.toLRSHom.toShHom g.toLRSHom.toShHom (comp_toShHom_of_comm w) (derivedHom X M K)))
    (hhom : IsIso (derivedPullbackSheafHomMap g'.toLRSHom.toShHom M K)) :
    IsIso (map f g f' g' w M K) := by
  have := hbc
  have := @Functor.map_isIso _ _ _ _ _ _ (derivedPushforward f'.toLRSHom.toShHom) _ hhom
  rw [map]
  infer_instance

/-! ### Finite Tor dimension of the base-changed structure sheaf

If `R'` has finite Tor dimension over `R`, then `g'_*𝒪_{X'}`, which Stacks 08IB identifies with
`Lf^*(g_*𝒪_{S'})`, has finite Tor dimension on `X`.
-/

/-- **The `R`-algebra `R'` placed in degree zero**, as an object of `D(R)`. -/
public abbrev algebraComplex (R R' : CommRingCat.{u}) (φ : R ⟶ R') :
    DerivedCategory (ModuleCat.{u} R) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
    (letI : Algebra R R' := φ.hom.toAlgebra; ModuleCat.of R R')

/-- **The complex `Lf^*((R')^~)` of `D(𝒪_X)`.**  For `f : X ⟶ Spec R` and an `R`-algebra `R'`
this is the derived pullback along `f` of the sheaf on `Spec R` associated with `R'`.  For the
cartesian square over `g = Spec(φ)`, Stacks 08IB identifies it with `g'_*𝒪_{X'}`. -/
public abbrev baseChangeStructureSheafComplex (R R' : CommRingCat.{u}) (φ : R ⟶ R')
    (f : X ⟶ Spec R) :
    DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) :=
  (derivedPullback f.toLRSHom.toShHom).obj
    ((tilde.functor R).mapDerivedCategory.obj (algebraComplex R R' φ))

/-- **Finite Tor dimension of `R'` over `R` passes to `Lf^*((R')^~)` on `X`.**

The hypothesis is Stacks 0652 (2) for the complex `R'[0]`, which is Stacks 0652 (4) for the
`R`-module `R'`: the statement that `R'` has finite Tor dimension over `R`. -/
public theorem hasFiniteTorDimension_baseChangeStructureSheafComplex (R R' : CommRingCat.{u})
    (φ : R ⟶ R') (f : X ⟶ Spec R)
    (hφ : StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical R
      (algebraComplex R R' φ)) :
    Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension X.toRingedSpace
      (baseChangeStructureSheafComplex R R' φ f) :=
  let ⟨a, b, hab⟩ := (hasFiniteTorDimension_tilde_iff (algebraComplex R R' φ)).2 hφ
  ⟨a, b, Stacks.Cohomology.TorAmplitude.Pullback.hasTorAmplitude_derivedPullback
    f.toLRSHom.toShHom _ a b hab⟩

end AlgebraicGeometry.GlobalHomBaseChange

end
