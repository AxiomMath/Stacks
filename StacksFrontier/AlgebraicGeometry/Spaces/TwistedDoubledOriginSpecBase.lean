module

public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginNotScheme

/-!
# Part (7) of Stacks 03FN: the twisted doubled origin over the ground field

So far the example has been read over `S = Spec k[x]`.  Part (7) reads it over `Spec k`
instead: `X` is a finite type algebraic space over `Spec k`, its base change `X_{k'}` along
`Spec k' ⟶ Spec k` is a scheme, and `X` itself is not.

The base change is the one part (6) already computed.  Indeed the chart `U = Spec k'[x]` *is*
the base change of the base along `Spec k' ⟶ Spec k`, because `k'[x] = k[x] ⊗_k k'`, so

    `X_{k'} = X ×_{Spec k} Spec k' = X ×_S (S ×_{Spec k} Spec k') = X ×_S U = X'`,

and `X'` is the affine line over `k'` with zero doubled by
`AlgebraicGeometry.TwistedDoubledOrigin.exists_isIso_baseChangePresheaf`.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.specBase`: the structure morphism `S ⟶ Spec k` of
  the base.
* `AlgebraicGeometry.TwistedDoubledOrigin.specExtension`: the morphism
  `Spec k' ⟶ Spec k` of the quadratic Galois extension, the covering of the closing claim.
* `AlgebraicGeometry.TwistedDoubledOrigin.coverToSpecExtension`: the structure morphism
  `U ⟶ Spec k'` of the chart.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.isPullback_coverMap_specExtension`: **the chart is
  the base change of the base along `Spec k' ⟶ Spec k`**, which is `k'[x] = k[x] ⊗_k k'` on
  spectra.
* `AlgebraicGeometry.TwistedDoubledOrigin.baseChange_specExtension_isScheme_and_not_isScheme`:
  **Stacks 03FN, part (7)**.

## Implementation notes

`Polynomial.algebra`, which makes `k'[x]` a `k[x]`-algebra, is a local instance here, as in
`StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginSelfProduct`; with it the
`Algebra.IsPushout k k' k[x] k'[x]` instance of Mathlib's `PolynomialAlgebra` file names the
base-change fact, and `AlgebraicGeometry.isPullback_SpecMap_of_isPushout` turns it into the
Cartesian square of spectra.  The structure morphism `algebraMap k[x] k'[x]` of that instance
is the coefficient map `Polynomial.mapRingHom (algebraMap k k')`, so the square's lower
horizontal edge is literally
`AlgebraicGeometry.TwistedDoubledOrigin.coverMap`.

Part (7) is stated as the conjunction of that Cartesian square with the two results it
combines, rather than by re-forming the base change over a big fppf site of `Spec k`: the
Cartesian square is exactly the statement that the presheaf
`AlgebraicGeometry.TwistedDoubledOrigin.baseChangePresheaf` — formed over `S` — *is* the base
change `X_{k'}` over `Spec k`, so no second site is needed and part (6) is reused unchanged.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

attribute [local instance] Polynomial.algebra

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The structure morphism `S = Spec k[x] ⟶ Spec k` of the base. -/
def specBase : base k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))

/-- The morphism `Spec k' ⟶ Spec k` of the quadratic Galois extension. This is the one-member
covering the closing claim of the example is about. -/
def specExtension : Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- The structure morphism `U = Spec k'[x] ⟶ Spec k'` of the chart. -/
def coverToSpecExtension : cover K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))

/-- **The chart is the base change of the base along `Spec k' ⟶ Spec k`**: the square

    `U ⟶ Spec k'`, `U ⟶ S`, `S ⟶ Spec k`, `Spec k' ⟶ Spec k`

is Cartesian, because `k'[x]` is the base change `k[x] ⊗_k k'` of the polynomial ring. -/
theorem isPullback_coverMap_specExtension :
    IsPullback (coverMap k K) (coverToSpecExtension K) (specBase k) (specExtension k K) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout k K (Polynomial k) (Polynomial K))).flip

variable [FiniteDimensional k K] [IsGalois k K]

/-- **Stacks 03FN, part (7).** Read over `Spec k` rather than over `S`, the base change
`X_{k'} = X ×_{Spec k} Spec k'` of the twisted doubled origin is a scheme — the affine line
over `k'` with zero doubled — while `X` itself is not a scheme.

The three conjuncts are: the chart `U` is the base change `S ×_{Spec k} Spec k'` of the base,
so that `X ×_{Spec k} Spec k'` is the presheaf `X ×_S U` of part (6); that presheaf is the
functor of points of the affine line over `k'` with zero doubled, which is part (6); and `X`
is not the functor of points of any scheme over the base, which is the `not_scheme` clause.
Together they say that `X_{k'}` is a scheme and `X` is not. -/
@[stacks 03FN "part (7): X over Spec k, with X_{k'} a scheme but X not a scheme"]
theorem baseChange_specExtension_isScheme_and_not_isScheme
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) (B : BigFppfSite.{u})
    (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    IsPullback (coverMap k K) (coverToSpecExtension K) (specBase k) (specExtension k K) ∧
      (∃ χ : baseChangePresheaf k K B hS hdegree σ hσ ⟶
          (pointsFunctor k B hS).obj (doubledOverBase k K), IsIso χ) ∧
      ¬ ∃ Y : Over (base k),
        Nonempty ((quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj ≅
          Stacks.Groupoids.points (Over.post B.inclusion) Y) :=
  ⟨isPullback_coverMap_specExtension k K,
    exists_isIso_baseChangePresheaf k K B hS hdegree σ hσ,
    quadraticGaloisTwistedDoubledOrigin_not_representable k K hdegree σ hσ B hS⟩

end AlgebraicGeometry.TwistedDoubledOrigin

end
