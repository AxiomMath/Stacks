module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection
public import StacksFrontier.RingTheory.DividedPowers.Extend

/-!
# Pairs with a completed connection

Let `p` be a prime, let `D` be a commutative ring and let `Ω` be a `D`-module equipped with a map
`d : D → Ω` playing the role of a derivation.  In the crystalline setting `D` is the `p`-adically
completed divided power envelope of a polynomial presentation, `Ω = Ω_D` is the `p`-adically
completed module of divided power differentials, and `d` is the induced differential.  This file
states the four conditions imposed on a pair `(M, ∇)` in the crystalline comparison of Tag 07JG:

* `M` is a `p`-adically complete `D`-module;
* `∇ : M → M ⊗̂_D Ω` is a connection, that is `∇ (f m) = f • ∇ m + m ⊗ d f`;
* `∇` is integrable;
* `∇` is topologically quasi-nilpotent: writing `∇ m = ∑ θ_i m ⬝ d x_i` for coordinate operators
  `θ_i : M → M`, for every `m` only finitely many pairs `(i, k)` with `k ≥ 1` have
  `θ_i^k m ∉ p M`.

Here `M ⊗̂_D Ω` is the `p`-adic completion of `M ⊗_D Ω`.  A connection in the sense of Tag 07I0
takes values in the uncompleted tensor product `M ⊗_D Ω`, so it is a special case of the present
notion but not the same notion; the comparison is `Crystalline.CompletedConnection.ofConnection`.

## Main definitions

* `Crystalline.CompletedTensor` — the completed tensor product `M ⊗̂_D Ω`, with the canonical map
  `Crystalline.toCompletedTensor` from `M ⊗_D Ω`.
* `Crystalline.pSmul` — the submodule `p M` of a `D`-module `M`.
* `Crystalline.IsPAdicallyComplete` — `p`-adic completeness of a `D`-module.
* `Crystalline.CompletedConnection` — a connection with values in `M ⊗̂_D Ω`.
* `Crystalline.IsCoordinateExpansion` — the coordinate operators `θ_i` of such a connection.
* `Crystalline.IsIntegrable` — integrability, expressed by commutation of the coordinate
  operators.
* `Crystalline.IsTopologicallyQuasiNilpotent` — topological quasi-nilpotence.
* `Crystalline.Pair` — a module together with a connection satisfying all four conditions, and
  `Crystalline.PairHom` the horizontal maps between two such.

## Main results

* `Crystalline.CompletedConnection.leibniz` — the Leibniz rule for a completed connection.
* `Crystalline.CompletedConnection.ofConnection` — a connection in the sense of Tag 07I0,
  composed with the canonical map to the completion, is a completed connection.
* `Crystalline.instCategoryPair` — pairs and their horizontal maps form a category.

## Implementation notes

The completion `M ⊗̂_D Ω` is taken for the ideal `p D`, so that it is Mathlib's
`AdicCompletion` and the functoriality of `⊗̂` is `AdicCompletion.map`; this is what the
horizontal maps between pairs use.  The topology `Crystalline.completedTensorTopology` is the
`p`-adic topology on that completion, and it is the topology in which the coordinate expansion
`∇ m = ∑ θ_i m ⬝ d x_i` converges, so the expansion is stated as a `HasSum`.

Integrability of a connection in the sense of Tag 07I0 is the vanishing of the curvature of the
degree-one extension of an uncompleted connection, which is unavailable for a connection with
values in the completion.  `Crystalline.IsIntegrable` is instead the equivalent condition in the
coordinates `x_i`: the coordinate operators commute.  Integrability and topological
quasi-nilpotence are stated in the universally quantified form of Tags 07JD and 07JE, over all
families of operators realizing the coordinate expansion; since `Ω` is in the application the
`p`-adic completion of the free module on the differentials `d x_i`, such a family always exists,
and the `Pair` structure records its existence so that the two conditions are not vacuous.

The exponent `k` in topological quasi-nilpotence is positive because `θ_i^0` is the identity, so
admitting `k = 0` would force `M = p M`, hence `M = 0`, as soon as there are infinitely many
coordinates.

## References

* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w uA uI uM

namespace Crystalline

/-! ### The completed tensor product -/

section CompletedConnections

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega]

/-- The completed tensor product `M ⊗̂_D Ω`: the `p`-adic completion of `M ⊗_D Ω`. -/
public abbrev CompletedTensor (M : Type w) [AddCommGroup M] [Module D M] : Type (max v w) :=
  AdicCompletion (DividedPowers.pAdicIdeal (A := D) p) (M ⊗[D] Omega)

/-- The canonical map `M ⊗_D Ω → M ⊗̂_D Ω`. -/
public noncomputable abbrev toCompletedTensor (M : Type w) [AddCommGroup M] [Module D M] :
    (M ⊗[D] Omega) →ₗ[D] CompletedTensor p D Omega M :=
  AdicCompletion.of (DividedPowers.pAdicIdeal (A := D) p) (M ⊗[D] Omega)

/-- The submodule `p M` of a `D`-module `M`. -/
public abbrev pSmul (M : Type w) [AddCommGroup M] [Module D M] : Submodule D M :=
  DividedPowers.pAdicIdeal (A := D) p • (⊤ : Submodule D M)

/-- The `p`-adic topology on the completed tensor product, in which the coordinate expansion of
a completed connection converges. -/
public noncomputable abbrev completedTensorTopology (M : Type w) [AddCommGroup M] [Module D M] :
    TopologicalSpace (CompletedTensor p D Omega M) :=
  Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p) (CompletedTensor p D Omega M)

/-! ### `p`-adically complete modules -/

/-- A `D`-module is `p`-adically complete when it is complete and separated for the `p`-adic
filtration, that is for the ideal `p D`. -/
@[stacks 07JB]
public def IsPAdicallyComplete (M : Type w) [AddCommGroup M] [Module D M] : Prop :=
  IsAdicComplete (DividedPowers.pAdicIdeal (A := D) p) M

/-! ### Connections with values in the completed tensor product -/

/-- A connection `∇ : M → M ⊗̂_D Ω` relative to a map `d : D → Ω`: an additive map satisfying the
Leibniz rule `∇ (f m) = f • ∇ m + m ⊗ d f`. -/
@[stacks 07JC]
public structure CompletedConnection (d : D → Omega) (M : Type w) [AddCommGroup M]
    [Module D M] where
  /-- The underlying map of a completed connection. -/
  toFun : M → CompletedTensor p D Omega M
  /-- A completed connection is additive. -/
  map_add' : ∀ m n : M, toFun (m + n) = toFun m + toFun n
  /-- The Leibniz rule for a completed connection. -/
  leibniz' : ∀ (f : D) (m : M),
    toFun (f • m) = f • toFun m + toCompletedTensor p D Omega M (m ⊗ₜ[D] d f)

namespace CompletedConnection

variable {p D Omega} {d : D → Omega} {M : Type w} [AddCommGroup M] [Module D M]

/-- A completed connection coerces to its underlying function. -/
public instance : CoeFun (CompletedConnection p D Omega d M)
    (fun _ ↦ M → CompletedTensor p D Omega M) where
  coe nabla := nabla.toFun

/-- Completed connections are additive. -/
public theorem map_add (nabla : CompletedConnection p D Omega d M) (m n : M) :
    nabla (m + n) = nabla m + nabla n :=
  nabla.map_add' m n

/-- The Leibniz rule for a completed connection. -/
public theorem leibniz (nabla : CompletedConnection p D Omega d M) (f : D) (m : M) :
    nabla (f • m) = f • nabla m + toCompletedTensor p D Omega M (m ⊗ₜ[D] d f) :=
  nabla.leibniz' f m

/-- Two completed connections agreeing on every element are equal. -/
@[ext] public theorem ext {nabla nabla' : CompletedConnection p D Omega d M}
    (h : ∀ m, nabla m = nabla' m) : nabla = nabla' := by
  cases nabla; cases nabla'; congr 1; exact funext h

/-- A connection in the sense of Tag 07I0, which takes values in the uncompleted tensor product
`M ⊗_D Ω`, becomes a completed connection relative to `d = π ∘ d_{D/A}` by composing with the
canonical map to the completion. -/
public noncomputable def ofConnection {A : Type uA} [CommRing A] [Algebra A D]
    {pi : Ω[D⁄A] →ₗ[D] Omega} (nabla : Connection A D pi M) :
    CompletedConnection p D Omega (fun x ↦ pi (KaehlerDifferential.D A D x)) M where
  toFun m := toCompletedTensor p D Omega M (nabla m)
  map_add' m n := by
    simp only [Connection.map_add]
    exact (toCompletedTensor p D Omega M).map_add _ _
  leibniz' f m := by
    simp only [Connection.leibniz]
    rw [(toCompletedTensor p D Omega M).map_add,
      (toCompletedTensor p D Omega M).map_smul]

end CompletedConnection

/-! ### Coordinate operators, integrability and quasi-nilpotence -/

variable {ι : Type uI}

/-- The coordinate operators of a completed connection relative to a family `d x_i` of
differentials: the identity `∇ m = ∑ θ_i m ⬝ d x_i`, the sum converging `p`-adically. -/
public def IsCoordinateExpansion (dx : ι → Omega) {d : D → Omega} {M : Type w}
    [AddCommGroup M] [Module D M] (nabla : CompletedConnection p D Omega d M)
    (theta : ι → (M → M)) : Prop :=
  letI := completedTensorTopology p D Omega M
  ∀ m : M, HasSum (fun i ↦ toCompletedTensor p D Omega M (theta i m ⊗ₜ[D] dx i)) (nabla m)

/-- A completed connection is integrable when its coordinate operators commute. -/
@[stacks 07JD "integrability in the coordinates x_i: the coordinate operators commute"]
public def IsIntegrable (dx : ι → Omega) {d : D → Omega} {M : Type w} [AddCommGroup M]
    [Module D M] (nabla : CompletedConnection p D Omega d M) : Prop :=
  ∀ theta : ι → (M → M), IsCoordinateExpansion p D Omega dx nabla theta →
    ∀ i j, theta i ∘ theta j = theta j ∘ theta i

/-- A completed connection is topologically quasi-nilpotent when, writing
`∇ m = ∑ θ_i m ⬝ d x_i`, for every `m` only finitely many pairs `(i, k)` with `k ≥ 1` satisfy
`θ_i^k m ∉ p M`. -/
@[stacks 07JE "corrected to k ≥ 1: admitting k = 0 would force M = p M"]
public def IsTopologicallyQuasiNilpotent (dx : ι → Omega) {d : D → Omega} {M : Type w}
    [AddCommGroup M] [Module D M] (nabla : CompletedConnection p D Omega d M) : Prop :=
  ∀ theta : ι → (M → M), IsCoordinateExpansion p D Omega dx nabla theta →
    ∀ m : M, {q : ι × ℕ | q.2 ≠ 0 ∧ (theta q.1)^[q.2] m ∉ pSmul p D M}.Finite

/-! ### The category of pairs -/

variable (dx : ι → Omega) (d : D → Omega)

/-- A pair `(M, ∇)` consisting of a `p`-adically complete `D`-module and an integrable,
topologically quasi-nilpotent connection with values in `M ⊗̂_D Ω`. -/
public structure Pair where
  /-- The underlying module `M`. -/
  carrier : Type uM
  /-- Its additive group structure. -/
  [addCommGroup : AddCommGroup carrier]
  /-- Its `D`-module structure. -/
  [module : Module D carrier]
  /-- The module is `p`-adically complete. -/
  isPAdicallyComplete : IsPAdicallyComplete p D carrier
  /-- The connection `∇ : M → M ⊗̂_D Ω`. -/
  nabla : CompletedConnection p D Omega d carrier
  /-- The connection admits coordinate operators for the chosen family of differentials. -/
  hasCoordinateOperators : ∃ theta : ι → (carrier → carrier),
    IsCoordinateExpansion p D Omega dx nabla theta
  /-- The connection is integrable. -/
  isIntegrable : IsIntegrable p D Omega dx nabla
  /-- The connection is topologically quasi-nilpotent. -/
  isTopologicallyQuasiNilpotent : IsTopologicallyQuasiNilpotent p D Omega dx nabla

attribute [instance] Pair.addCommGroup Pair.module

/-- A morphism of pairs: a horizontal `D`-linear map, that is one commuting with the
connections. -/
@[ext] public structure PairHom (P Q : Pair p D Omega dx d) where
  /-- The underlying `D`-linear map. -/
  toLinearMap : P.carrier →ₗ[D] Q.carrier
  /-- Horizontality: the map commutes with the two connections. -/
  horizontal : ∀ m : P.carrier, Q.nabla (toLinearMap m) =
    AdicCompletion.map (DividedPowers.pAdicIdeal (A := D) p)
      (TensorProduct.map toLinearMap (LinearMap.id (R := D) (M := Omega))) (P.nabla m)

/-- Pairs and their horizontal maps form a category. -/
public instance : Category (Pair p D Omega dx d) where
  Hom P Q := PairHom p D Omega dx d P Q
  id P := ⟨LinearMap.id, by intro m; simp⟩
  comp {P Q R} f g := ⟨g.toLinearMap ∘ₗ f.toLinearMap, fun m => by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [g.horizontal, f.horizontal, AdicCompletion.map_comp_apply, ← TensorProduct.map_comp]
    simp⟩
  id_comp f := by apply PairHom.ext; simp
  comp_id f := by apply PairHom.ext; simp
  assoc f g h := by apply PairHom.ext; simp [LinearMap.comp_assoc]

end CompletedConnections

end Crystalline

end
