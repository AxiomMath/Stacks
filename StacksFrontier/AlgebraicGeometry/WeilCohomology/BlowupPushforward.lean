module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.PoincareDuality
public import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward of the unit class along a blowup

Let `b : X' ⟶ X` be the blowup of a nonempty equidimensional smooth projective `k`-scheme of
dimension `d` in a nowhere dense smooth centre, so that `X'` is again smooth projective of
dimension `d`. Then `b_*(1) = 1`, equivalently `∫_{X'} ∘ b^* = ∫_X` on `H^{2d}(X)(d)`.

The argument compares the degree-zero Künneth components of the two diagonal classes. Writing
`γ([Δ_X]) = ∑_i η_i` with `η_i ∈ H^i(X) ⊗_F H^{2d - i}(X)(d)`, the normalization of the trace
map reads `(1 ⊗ ∫_X)(η_0) = 1`. Restricting to a closed point `x'` of `X'` off the exceptional
divisor whose residue field is separable over `k` identifies the images of `η_0` and of the
corresponding component `η'_0` for `X'` inside `H^0(x') ⊗_F H^{2d}(X')(d)`; since `H^0(X')` is
the cohomology of the spectrum of `Γ(X, 𝒪_X)` and therefore injects into `H^0(x')`, this forces
`(b^* ⊗ b^*)(η_0) = η'_0`. Contracting that identity against `∫_{X'}` and using injectivity of
`b^*` on `H^0` shows that `∫_{X'} ∘ b^*` satisfies the normalization characterizing `∫_X`, whence
the two agree and `b_*(1) = 1`.

## Main definitions

* `Stacks.WeilCohomology.tensorContractRight`: contraction of the right-hand factor of a tensor
  product against a linear functional, `η ↦ (1 ⊗ μ)(η)`.

## Main results

* `Stacks.WeilCohomology.pullback_kunnethComponent_eq`: two Künneth components with the same
  image after a further injective restriction are exchanged by pullback.
* `Stacks.WeilCohomology.integration_comp_pullback_eq_integration`: the trace map of the blowup,
  precomposed with pullback, is the trace map of the base.
* `Stacks.WeilCohomology.pushforwardOne_blowup`: the Poincaré-dual pushforward along the blowup
  carries the unit class to the unit class.

## Implementation notes

The statements isolate the part of the data `(D0)`, `(D1)`, `(D2')` and of the conditions `(A1)`
through `(A8)` that this argument consumes. The coefficient spaces are `A = H^0(X)`,
`A' = H^0(X')`, `P = H^0(x')` for the chosen closed point, and `T = H^{2d}(X)(d)`,
`T' = H^{2d}(X')(d)`; the Tate twists and the cohomological degrees are therefore already
incorporated into the module types, and no degree casts intervene. The maps `pullbackZero`,
`pullbackTop` and `restrict` are `b^*` in degree `0` and in degree `2d`, and the restriction of a
degree-zero class to the point. The classes `η` and `η'` are the degree-zero Künneth components
of `γ([Δ_X])` and `γ([Δ_{X'}])`, which exist by `(A5)` and `(A1)`.

The hypotheses then read as follows. `pullbackZero_injective` is `(A7)`. Injectivity of
`restrict` is `(A8)`, which identifies `H^0(X')` with the cohomology of the spectrum of the
finite separable extension `Γ(X, 𝒪_X)` of `k`, followed by Tag 0FVS, which is
`Stacks.WeilCohomology.injective_pullback_of_separable`; the closed point with separable residue
field exists by Tag 056U. The two `normalization` hypotheses are the degree-zero part of `(A6)`.
`restrict_eq` is the comparison of the pullbacks of the two diagonal classes along the square
relating `x' × X' ⟶ X' × X'` and `x × X ⟶ X × X`, which rests on compatibility of the cycle
class map with pullback. `nondegenerate` is the nondegeneracy of the degree-zero component of
the diagonal class, the statement that a trace map satisfying the normalization of `(A6)` is
unique; it is the content of Remark 45.14.6, Tag 0FIK. Finally `pairing` and `pairing'` are the
cup-product trace pairings in complementary degrees and `pairing.IsPerfPair` is Poincaré duality
for the base, which is how the pushforward exists at all.

Neither the reduction to a connected, hence irreducible, `X` nor the identification
`Γ(X, 𝒪_X) = Γ(X', 𝒪_{X'})` appears: both serve only to produce the data above. In particular
the statements hold for any morphism whose cohomological data satisfy these identities, and are
therefore more general than the source's rather than weaker.

## References

* [Stacks Project, Tag 0FIS](https://stacks.math.columbia.edu/tag/0FIS)
-/

@[expose] public section

universe uF uA uA' uP uT uT'

open scoped TensorProduct

namespace Stacks.WeilCohomology

variable {F : Type uF} [Field F]

/-- Over a field, tensoring an injective linear map with the identity stays injective, because
an injective map of vector spaces admits a left inverse. -/
private theorem injective_map_id_of_injective
    {A : Type uA} [AddCommGroup A] [Module F A] {P : Type uP} [AddCommGroup P] [Module F P]
    (T : Type uT) [AddCommGroup T] [Module F T]
    {restrict : A →ₗ[F] P} (h : Function.Injective restrict) :
    Function.Injective (TensorProduct.map restrict (LinearMap.id (R := F) (M := T))) := by
  obtain ⟨s, hs⟩ := restrict.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr h)
  intro x y hxy
  have h2 := congrArg (TensorProduct.map s (LinearMap.id (R := F) (M := T))) hxy
  simpa [TensorProduct.map_map, hs] using h2

/-- Contraction of the right-hand factor of `A ⊗_F T` against a linear functional `μ` on `T`,
that is `η ↦ (1 ⊗ μ)(η)`. For `η` the Künneth component of a diagonal class this sends a
candidate trace map to the class that the normalization `(A6)` demands be the unit. -/
noncomputable def tensorContractRight
    {A : Type uA} [AddCommGroup A] [Module F A] {T : Type uT} [AddCommGroup T] [Module F T]
    (μ : T →ₗ[F] F) : A ⊗[F] T →ₗ[F] A :=
  (TensorProduct.rid F A).toLinearMap ∘ₗ LinearMap.lTensor A μ

@[simp]
theorem tensorContractRight_tmul
    {A : Type uA} [AddCommGroup A] [Module F A] {T : Type uT} [AddCommGroup T] [Module F T]
    (μ : T →ₗ[F] F) (a : A) (t : T) :
    tensorContractRight μ (a ⊗ₜ[F] t) = μ t • a := by
  simp [tensorContractRight]

/-- Contraction is natural: contracting the image of `η` under `f ⊗ g` against `μ` is the image
under `f` of the contraction of `η` against `μ ∘ g`. -/
theorem tensorContractRight_map
    {A : Type uA} [AddCommGroup A] [Module F A] {A' : Type uA'} [AddCommGroup A'] [Module F A']
    {T : Type uT} [AddCommGroup T] [Module F T] {T' : Type uT'} [AddCommGroup T'] [Module F T']
    (f : A →ₗ[F] A') (g : T →ₗ[F] T') (μ : T' →ₗ[F] F) (η : A ⊗[F] T) :
    tensorContractRight μ (TensorProduct.map f g η) = f (tensorContractRight (μ ∘ₗ g) η) := by
  induction η using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp
  | add x y hx hy => simp [hx, hy]

variable {A : Type uA} [AddCommGroup A] [Module F A]
  {A' : Type uA'} [AddCommGroup A'] [Module F A']
  {P : Type uP} [AddCommGroup P] [Module F P]
  {T : Type uT} [AddCommGroup T] [Module F T]
  {T' : Type uT'} [AddCommGroup T'] [Module F T']

/-- If the degree-zero Künneth components `η` of `γ([Δ_X])` and `η'` of `γ([Δ_{X'}])` have the
same image in `H^0(x') ⊗_F H^{2d}(X')(d)`, and restriction to the point is injective on
`H^0(X')`, then `η` already maps to `η'` under `b^* ⊗ b^*`. -/
theorem pullback_kunnethComponent_eq
    (pullbackZero : A →ₗ[F] A') (pullbackTop : T →ₗ[F] T') (restrict : A' →ₗ[F] P)
    (η : A ⊗[F] T) (η' : A' ⊗[F] T')
    (restrict_injective : Function.Injective restrict)
    (restrict_eq : TensorProduct.map (restrict ∘ₗ pullbackZero) pullbackTop η =
      TensorProduct.map restrict LinearMap.id η') :
    TensorProduct.map pullbackZero pullbackTop η = η' := by
  apply injective_map_id_of_injective T' restrict_injective
  rw [TensorProduct.map_map, LinearMap.id_comp]
  exact restrict_eq

/-- **Stacks Project, Tag 0FIS.** For a blowup `b : X' ⟶ X` of a nonempty equidimensional smooth
projective scheme of dimension `d` in a nowhere dense smooth centre, integration over `X'` after
pullback is integration over `X`: both satisfy the normalization `(1 ⊗ ∫)(η) = 1` of `(A6)`
against the degree-zero Künneth component of the diagonal class of `X`, which determines the
trace map. -/
@[stacks 0FIS "integration agrees with integration after pullback to the blowup"]
theorem integration_comp_pullback_eq_integration
    (pullbackZero : A →ₗ[F] A') (pullbackTop : T →ₗ[F] T') (restrict : A' →ₗ[F] P)
    (one : A) (one' : A') (integration : T →ₗ[F] F) (integration' : T' →ₗ[F] F)
    (η : A ⊗[F] T) (η' : A' ⊗[F] T')
    (restrict_injective : Function.Injective restrict)
    (pullbackZero_injective : Function.Injective pullbackZero)
    (pullbackZero_one : pullbackZero one = one')
    (restrict_eq : TensorProduct.map (restrict ∘ₗ pullbackZero) pullbackTop η =
      TensorProduct.map restrict LinearMap.id η')
    (normalization : tensorContractRight integration η = one)
    (normalization' : tensorContractRight integration' η' = one')
    (nondegenerate : Function.Injective fun μ : T →ₗ[F] F => tensorContractRight μ η) :
    integration' ∘ₗ pullbackTop = integration := by
  have hstep : TensorProduct.map pullbackZero pullbackTop η = η' :=
    pullback_kunnethComponent_eq pullbackZero pullbackTop restrict η η'
      restrict_injective restrict_eq
  apply nondegenerate
  change tensorContractRight (integration' ∘ₗ pullbackTop) η = tensorContractRight integration η
  apply pullbackZero_injective
  rw [← tensorContractRight_map pullbackZero pullbackTop integration' η, hstep,
    normalization', normalization, pullbackZero_one]

/-- **Stacks Project, Tag 0FIS.** For a blowup `b : X' ⟶ X` of a nonempty equidimensional smooth
projective scheme of dimension `d` in a nowhere dense smooth centre, the Poincaré-dual
pushforward carries the unit class of `X'` to the unit class of `X`: `b_*(1) = 1`. -/
@[stacks 0FIS]
theorem pushforwardOne_blowup
    (pullbackZero : A →ₗ[F] A') (pullbackTop : T →ₗ[F] T') (restrict : A' →ₗ[F] P)
    (one : A) (one' : A') (integration : T →ₗ[F] F) (integration' : T' →ₗ[F] F)
    (pairing : T →ₗ[F] A →ₗ[F] F) [pairing.IsPerfPair] (pairing' : T' →ₗ[F] A' →ₗ[F] F)
    (η : A ⊗[F] T) (η' : A' ⊗[F] T')
    (restrict_injective : Function.Injective restrict)
    (pullbackZero_injective : Function.Injective pullbackZero)
    (pullbackZero_one : pullbackZero one = one')
    (restrict_eq : TensorProduct.map (restrict ∘ₗ pullbackZero) pullbackTop η =
      TensorProduct.map restrict LinearMap.id η')
    (normalization : tensorContractRight integration η = one)
    (normalization' : tensorContractRight integration' η' = one')
    (nondegenerate : Function.Injective fun μ : T →ₗ[F] F => tensorContractRight μ η)
    (pairing_one : ∀ β, pairing β one = integration β)
    (pairing_one' : ∀ β, pairing' β one' = integration' β) :
    poincareDualPushforward pairing' pairing pullbackTop one' = one := by
  have htr : integration' ∘ₗ pullbackTop = integration :=
    integration_comp_pullback_eq_integration pullbackZero pullbackTop restrict one one'
      integration integration' η η' restrict_injective pullbackZero_injective
      pullbackZero_one restrict_eq normalization normalization' nondegenerate
  apply (LinearMap.IsPerfPair.bijective_right pairing).injective
  apply LinearMap.ext
  intro β
  change pairing β _ = pairing β _
  rw [pair_poincareDualPushforward, pairing_one', pairing_one, ← htr]
  rfl

end Stacks.WeilCohomology

end
