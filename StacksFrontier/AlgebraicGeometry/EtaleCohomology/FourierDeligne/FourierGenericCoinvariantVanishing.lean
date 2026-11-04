module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionKernel

/-!
# Generic vanishing of the top cohomology of the Fourier transform (statement)

Let `k` be a finite field, `Λ` a finite commutative ring in which `q = #k` is invertible, `ψ` an
additive character of `k` with values in `Λ` and `∑ ψ = 0`, and `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L_ψ)`
the Fourier transform on `D⁺(𝔸¹_k, Λ)`. For a sheaf `H` on `𝔸¹_k` which is locally constant with
finite values on a nonempty open `V`, the sheaf `H²(Φ(H[0]))` is **punctual**: it vanishes on a
nonempty open of `𝔸¹_k`.

Its stalk at a geometric point `t̄` is `H²_c(𝔸¹_t̄, H ⊗ L_ψ(x t))`, which only sees `H|_V`, and is
the module of coinvariants `(H_η̄ ⊗ L_ψ(x t))_{π₁(V_t̄)}`. Filtering `H_η̄` by simple modules over
the residue fields of `Λ`, a simple factor contributes only if it is the inverse of `L_ψ(x t)`;
the sheaves `L_ψ(x t)` modulo a maximal ideal are pairwise non-isomorphic on `V_t̄` (the residue
character of `ψ` is nontrivial because `q` is a unit and `∑ ψ = 0`), so each factor contributes
for at most one `t̄`, and `H²(Φ(H[0]))` is a constructible sheaf with only finitely many nonzero
closed-point stalks.

This is the input (L2) of the single-level argument for the irreducibility of the Fourier
transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH). It is stated
here as a proposition so that it can be proved independently of its consumers.

## Main definitions

* `Stacks.EtaleCohomology.FourierGenericCoinvariantVanishingInput`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so does the
statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **(L2) `H²` of the Fourier transform of a generically lisse sheaf is punctual**: for `H` on
`𝔸¹_k` locally constant with finite values on a nonempty open `V`, `H²(Φ(H[0]))` vanishes on a
nonempty open `U` of `𝔸¹_k`, `Φ` the Fourier transform for an additive character `ψ` with
`∑ ψ = 0` and coefficients in a finite ring in which `#k` is a unit (generic vanishing of the
geometric coinvariants `(H_η̄ ⊗ L_ψ(x t))_{π₁(V_t̄)}`). -/
def FourierGenericCoinvariantVanishingInput : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
    (B : BigEtaleSite.{u})
    (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj
      (cover k (Polynomial k) Polynomial.X)),
    ∑ a : k, ψ a = 0 → IsUnit (Fintype.card k : Λ) →
    ∀ (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
      (H : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) {V : Scheme.{u}}
      (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V],
      Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
        (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj H) →
      ∃ (U : Scheme.{u}) (jU : U ⟶ Spec (.of (Polynomial k))), IsOpenImmersion jU ∧
        Nonempty U ∧ IsZero ((etaleModuleInverseImage.{u, 0} Λ jU).obj
          ((DerivedCategory.Plus.homologyFunctor _ 2).obj
            ((fourierTransform k Λ ψ B p₀ j).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj H))))

end Stacks.EtaleCohomology

end
