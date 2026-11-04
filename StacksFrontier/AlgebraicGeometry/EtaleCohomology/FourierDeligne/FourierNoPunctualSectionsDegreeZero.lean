module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionKernel

/-!
# The Fourier transform of a sheaf without punctual sections has no `H⁰` (statement)

Let `k` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k` with
values in `Λ` and `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L_ψ)` the Fourier transform on `D⁺(𝔸¹_k, Λ)`. Let
`H` be a sheaf on `𝔸¹_k` and `j : V ⟶ 𝔸¹_k` a nonempty open such that `j⁻¹ H` is locally constant
with finite values and the unit `H ⟶ j_* j⁻¹ H` is a monomorphism (`H` has no sections supported
off `V`). Then `H⁰(Φ(H[0])) = 0`.

Route. By proper base change the vanishing is checked on the geometric fibres `𝔸¹_Ω` of `pr₂`
(`Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_geometricFibres`), where the
integrand is `g⁻¹ H ⊗ L'` for `g : 𝔸¹_Ω ⟶ 𝔸¹_k` and a locally free `L'` of rank one. A compactly
supported section vanishes near the boundary, hence on a nonempty étale open, hence on the
connected dense open `V_Ω` where the integrand is locally constant; it then vanishes provided the
integrand has no sections supported off `V_Ω`
(`Stacks.EtaleCohomology.isZero_homology_zero_derivedLowerShriek_of_mono_unit`). That last point
is the injectivity of the base-change map `g⁻¹ j_* M ⟶ j'_* g'⁻¹ M` on `𝔸¹_Ω` (`M = j⁻¹ H`), which
is proved through germs: a germ of `g⁻¹ j_* M` at a geometric point is the germ of a section `m` of
`M` over `U ∩ V` for an étale neighbourhood `U`, chosen connected so that `U ∩ V` is connected
(`U` is normal), and if the pull-back of `m` vanishes near the point then `m` vanishes at one
geometric point of `U ∩ V`, hence everywhere since `M` is locally constant. Tag 0EYS does not
apply, because `g` is the base change of `Spec Ω ⟶ Spec k`, which is not of finite presentation.

This is the input (L1) of the single-level argument for the irreducibility of the Fourier
transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), for the
quotients `Q ⊆ j_* Q_V` of that argument; the locally free case is
`Stacks.EtaleCohomology.isZero_homology_zero_fourierTransform_of_isLocallyFreeEtaleModule`. It is
stated here as a proposition so that it can be proved independently of its consumers.

## Main definitions

* `Stacks.EtaleCohomology.FourierNoPunctualSectionsDegreeZeroInput`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so does the
statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **(L1) `H⁰(Φ(H[0])) = 0` for a sheaf `H` on `𝔸¹_k` without sections supported off a nonempty
open `V` on which it is locally constant with finite values**: the unit `H ⟶ j_* j⁻¹ H` is a
monomorphism and `j⁻¹ H` is locally constant. -/
def FourierNoPunctualSectionsDegreeZeroInput : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
    (B : BigEtaleSite.{u})
    (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj
      (cover k (Polynomial k) Polynomial.X))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (H : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) {V : Scheme.{u}}
    (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V],
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj H) →
    Mono ((etaleModuleInverseImageAdj.{u, 0} Λ jV).unit.app H) →
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj H)))

end Stacks.EtaleCohomology

end
