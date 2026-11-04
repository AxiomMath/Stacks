module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGEIsoOfCohomologyIsomorphisms
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatOpcycles
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# A bounded-below approximation of an object of finite Tor amplitude is a representative

Let `(C, O)` be a ringed site, let `T` be a derived tensor product on `D(O)` and let `E` be an
object of `D(O)` with Tor amplitude in `[n + 1, b]`. Suppose `E` is represented by a complex
`Ecpx` which receives a map `α : P ⟶ Ecpx` from a complex `P` of flat `O`-modules concentrated
in degrees `[n, b]`, and suppose `α` is an isomorphism on cohomology in every degree `> n`. Then

* the canonical truncation `τ_{≥ n+1}P` *represents* `E`, and
* its lowest term `Coker(P^n ⟶ P^{n+1})` is a flat `O`-module.

This is the local core of Stacks 08G7: in the source's notation `n = a - 1`, `P = E^\bullet` is
the strictly perfect complex produced by `(a-1)`-pseudo-coherence after replacing it by
`σ_{≥ a-1}E^\bullet`, and the two conclusions are "the complex
`E' ⟶ E^{a+1} ⟶ … ⟶ E^b` is quasi-isomorphic to `E`" and "`E'` is flat", for
`E' = Coker(E^{a-1} ⟶ E^a)`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.exists_iso_truncGE_and_isFlat_opcycles`: the two
  conclusions above.

## Implementation notes

The two conclusions come from the two halves of the argument, which are proved separately and
are both free of the hypotheses the other needs.

The identification of `τ_{≥ n+1}P` with `E` is pure derived-category formalism:
`CochainComplex.exists_iso_Q_truncGE_of_isIso_homologyMap`, which needs only that the target be
`≥ n + 1` for the canonical t-structure — and that is the Tor-amplitude hypothesis read through
the unit law, `Stacks.SheafOfModules.DerivedTensorProduct.isGE_of_hasTorAmplitude`. In
particular neither the flatness of the terms of `P` nor its boundedness enters there.

The flatness of the lowest term is
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_opcycles_of_hasTorAmplitude_truncGE`, whose
Tor-amplitude hypothesis is about `τ_{≥ n+1}P` rather than about `E`; the first conclusion is
what transports it.

A single integer `b` bounds both the degrees of `P` and the Tor amplitude of `E`. That is no
restriction: Tor amplitude in an interval holds in every larger interval
(`Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.mono`) and so does a strict upper
bound on the degrees (`CochainComplex.isStrictlyLE_of_le`), so a caller holding two different
bounds passes their maximum.

## References

* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
* [Stacks Project, Tag 08G0](https://stacks.math.columbia.edu/tag/08G0)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Y : RingedSite.{u, v, max u v}}
  [HasSheafify Y.J AddCommGrpCat.{max u v}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, max u v} Y)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max u v, max u v, max u v}
    Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, max u v} Y) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **A bounded complex of flat `O`-modules which approximates an object of Tor amplitude
`[n + 1, b]` above degree `n` represents it after canonical truncation, with flat lowest term.**

Let `E` be an object of `D(O)` of Tor amplitude in `[n + 1, b]`, represented by a complex `Ecpx`,
and let `α : P ⟶ Ecpx` be a morphism from a complex `P` of flat `O`-modules concentrated in
degrees `[n, b]` which is an isomorphism on cohomology in every degree `> n`. Then `τ_{≥ n+1}P`
represents `E`, and its term in degree `n + 1`, the cokernel of `P^n ⟶ P^{n+1}`, is flat.

This is the local core of Stacks 08G7, with `n = a - 1`. -/
theorem exists_iso_truncGE_and_isFlat_opcycles (T : DerivedTensorProduct.{u, v, max u v, d} Y)
    (E : RingedSite.DerivedModules.{u, v, max u v, d} Y) (n b : ℤ)
    (Ecpx : CochainComplex (RingedSite.Modules.{u, v, max u v} Y) ℤ)
    (eE : DerivedCategory.Q.obj Ecpx ≅ E)
    (P : CochainComplex (RingedSite.Modules.{u, v, max u v} Y) ℤ)
    [P.IsStrictlyGE n] [P.IsStrictlyLE b]
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O) (P.X i))
    (α : P ⟶ Ecpx)
    (hα : ∀ i : ℤ, n + 1 ≤ i → IsIso (HomologicalComplex.homologyMap α i))
    (hamp : HasTorAmplitude T E (n + 1) b) :
    Nonempty (DerivedCategory.Q.obj (P.truncGE (n + 1)) ≅ E) ∧
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, max u v, max u v} (O := Y.O)
        (P.opcycles (n + 1)) := by
  have hEGE : E.IsGE (n + 1) := isGE_of_hasTorAmplitude T E hamp
  have hGE : (DerivedCategory.Q.obj Ecpx).IsGE (n + 1) :=
    DerivedCategory.TStructure.t.isGE_of_iso eE.symm (n + 1)
  obtain ⟨e⟩ := CochainComplex.exists_iso_Q_truncGE_of_isIso_homologyMap (n + 1) α hα
  refine ⟨⟨e ≪≫ eE⟩, isFlat_opcycles_of_hasTorAmplitude_truncGE T P n b hflat ?_⟩
  exact HasTorAmplitude.of_iso (e ≪≫ eE).symm hamp

end Stacks.SheafOfModules.DerivedTensorProduct

end
