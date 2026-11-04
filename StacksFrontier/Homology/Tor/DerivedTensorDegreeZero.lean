module

public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate

/-!
# The degree-zero cohomology of the derived tensor product of two modules

Let `A` be a commutative ring and let `M` and `N` be `A`-modules. Placing both in degree zero
and forming the canonical derived tensor product of [Stacks, Tag 0BYI] gives an object of the
derived category of `A`-modules whose cohomology in degree zero is the ordinary tensor product
`M ⊗_A N`.

This is the degree-zero case of the identification of `H^{-i}(M[0] ⊗^L_A N[0])` with
`Tor_i^A(M, N)`. In that generality the two sides are computed from projective resolutions of
different variables, so the comparison needs Tor balancing, [Stacks, Tag 00M1]. In degree zero
no balancing is needed: the zeroth left derived functor of a right exact functor is the functor
itself.

## Main definitions

* `Stacks.DerivedTensor.tensorModuleRightIsoTensorLeft`: the commutativity isomorphism
  `- ⊗_A N ≅ N ⊗_A -`, through which `- ⊗_A N` inherits right exactness.

## Main results

* `Stacks.DerivedTensor.homologyZeroIsoTensorProduct`:
  `H⁰(M[0] ⊗^L_A N[0]) ≅ M ⊗_A N` as `A`-modules.
* `Stacks.DerivedTensor.subsingleton_tensorProduct_of_isZero`: hence the vanishing of that
  cohomology module is the vanishing of `M ⊗_A N`.
* `Stacks.DerivedTensor.subsingleton_tensorProduct_symm_of_isZero`: the same with the factors of
  the ordinary tensor product written in the other order.

## Implementation notes

The proof takes a projective resolution `Q` of `M`, views it as the bounded above cochain complex
`Q.cochainComplex` of flat modules, and runs
`StacksDraft.TorAmplitude.certifiedTensorHomologyIsoOfFlat` at the canonical certificate of
`StacksFrontier.Homology.TorAmplitude.CanonicalCertificate`: that replaces the derived tensor
product by the termwise tensor complex. Since `Q.cochainComplex` is by definition the extension
by zero of the chain complex `Q.complex`, and an additive functor commutes with extension by zero
(`CategoryTheory.Functor.mapExtendIso`), the degree-zero cohomology of the termwise tensor
complex is the degree-zero homology of `(- ⊗ N)` applied to `Q.complex`, which is the zeroth left
derived functor of `- ⊗ N` at `M`, which is `M ⊗ N` because `- ⊗ N` preserves finite colimits.

Right exactness of `- ⊗_A N` is obtained from right exactness of `N ⊗_A -`, which Mathlib knows
for the monoidal structure on `ModuleCat`, through `tensorModuleRightIsoTensorLeft`.

### The step of Tag 0ECC that this covers

In the proof of [Stacks, Tag 0ECC] the conclusion of the spectral-sequence step
`Stacks.SpectralSequence.isZero_derivedTensorHomology_zero_singleHomology_zero` is the vanishing
of `H⁰(H⁰(RΓ(V, 𝒪_V))[0] ⊗^L_A A/𝔪)`, while the hypothesis of the final step
`Stacks.PuncturedSpectrum.isAffine_of_subsingleton_quotTensor_globalSections` is the vanishing of
`A/𝔪 ⊗_A Γ(V, 𝒪_V)`. The results below are the link between the two. No tag is claimed for
them: on their own they state no step of the source, only the identification of two notations for
the same module.

## References

* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 00M1](https://stacks.math.columbia.edu/tag/00M1)
* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor StacksDraft.TorAmplitude

universe u

namespace Stacks.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-! ### Right exactness of tensoring on the right -/

/-- Tensoring on the right by `N` is tensoring on the left by `N`, through the commutativity of
the tensor product of modules. -/
def tensorModuleRightIsoTensorLeft (N : ModuleCat.{u} A) :
    tensorModuleRight N ≅ tensorLeft N :=
  NatIso.ofComponents (fun X => (TensorProduct.comm A X N).toModuleIso)
    (by
      intro X Y f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      ext x y
      rfl)

/-- Tensoring on the right by a module is right exact. -/
instance preservesFiniteColimits_tensorModuleRight (N : ModuleCat.{u} A) :
    PreservesFiniteColimits (tensorModuleRight N) :=
  preservesFiniteColimits_of_natIso (tensorModuleRightIsoTensorLeft A N).symm

/-! ### The degree-zero cohomology -/

/-- **`H⁰(M[0] ⊗^L_A N[0]) ≅ M ⊗_A N`.** The degree-zero cohomology of the canonical derived
tensor product of two modules placed in degree zero is their ordinary tensor product. -/
def homologyZeroIsoTensorProduct (M N : ModuleCat.{u} A) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (((canonicalDerivedTensorProductFunctor A).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)) ≅
      ModuleCat.of A (TensorProduct A M N) := by
  let Q := ProjectiveResolution.of M
  let P := Q.cochainComplex
  let F := tensorModuleRight N
  have hbounded : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨0, fun i hi => CochainComplex.isZero_of_isStrictlyLE P 0 i hi⟩
  have hflat : ∀ i : ℤ, Module.Flat A (P.X i) := by
    intro i
    have : Module.Projective A (P.X i) := ModuleCat.projective_of_module_projective _
    infer_instance
  -- The projective resolution represents `M[0]` in the derived category.
  let eQ : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M :=
    asIso (DerivedCategory.Q.map Q.π') ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M).symm
  let eRep := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).mapIso
    (((canonicalDerivedTensorProductFunctor A).mapIso eQ).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N))
  -- The derived tensor product of a bounded above flat complex is the termwise tensor complex.
  let eTermwise := certifiedTensorHomologyIsoOfFlat
    (canonicalTensorComparison A) (canonicalTensorIsLeftDerived A) P hbounded hflat N 0
  -- The termwise tensor complex is the extension by zero of `F` applied to `Q.complex`.
  let eExtend := (HomologicalComplex.homologyFunctor (ModuleCat.{u} A)
      (ComplexShape.up ℤ) 0).mapIso (F.mapExtendIso Q.complex ComplexShape.embeddingDownNat)
  let eDegree := HomologicalComplex.extendHomologyIso
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex)
    ComplexShape.embeddingDownNat (j := 0) (j' := 0) (by simp)
  -- Degree-zero homology of that complex is the zeroth left derived functor of `F` at `M`.
  exact eRep.symm ≪≫ eTermwise ≪≫ eExtend ≪≫ eDegree ≪≫ (Q.isoLeftDerivedObj F 0).symm ≪≫
    (Functor.leftDerivedZeroIsoSelf F).app M

/-- **The vanishing of `H⁰(M[0] ⊗^L_A N[0])` is the vanishing of `M ⊗_A N`.** -/
theorem subsingleton_tensorProduct_of_isZero (M N : ModuleCat.{u} A)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (((canonicalDerivedTensorProductFunctor A).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)))) :
    Subsingleton (TensorProduct A M N) :=
  ModuleCat.isZero_iff_subsingleton.mp (h.of_iso (homologyZeroIsoTensorProduct A M N).symm)

/-- `Stacks.DerivedTensor.subsingleton_tensorProduct_of_isZero` with the factors of the ordinary
tensor product written in the other order. -/
theorem subsingleton_tensorProduct_symm_of_isZero (M N : ModuleCat.{u} A)
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (((canonicalDerivedTensorProductFunctor A).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)))) :
    Subsingleton (TensorProduct A N M) :=
  (TensorProduct.comm A M N).toEquiv.subsingleton_congr.mp
    (subsingleton_tensorProduct_of_isZero A M N h)

end Stacks.DerivedTensor

end
