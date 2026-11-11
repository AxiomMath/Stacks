module

public import StacksFrontier.AlgebraicGeometry.Perfect.Morphism
public import StacksFrontier.Homology.TorAmplitude.CompositionCanonical
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation

/-!
# Restriction of scalars along an affine chart of a perfect morphism

Let `f : X ⟶ S` be a perfect morphism of schemes, let `V ⊆ S` and `U ⊆ f^{-1}V` be affine opens
and let `K` be a complex of `Γ(X, U)`-modules of finite Tor dimension over `Γ(X, U)`. Then `K`,
read as a complex of `Γ(S, V)`-modules, has finite Tor dimension over `Γ(S, V)`.

This is [Stacks, Tag 066K] applied to the chart ring map `Γ(S, V) ⟶ Γ(X, U)`, whose target has
finite Tor dimension over its source because that is the defining condition of
`AlgebraicGeometry.Perfect`. It is the ring-level content of the affine case of the Tor-dimension
half of [Stacks, Tag 08EV]: over affine charts the derived direct image is derived restriction of
scalars ([Stacks, Tag 0A9F]), and this is the statement that derived restriction of scalars
preserves finite Tor dimension when the chart ring map is perfect.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_restrictScalars_of_hasTorAmplitudeIn`:
  **[Stacks, Tag 0B66] with `L = B[0]` at an arbitrary interval.** If `B` placed in degree zero
  has Tor amplitude in `[c, d]` over `A` and `K` has Tor amplitude in `[a, b]` over `B`, then `K`
  has Tor amplitude in `[a + c, b + d]` over `A`. Quantified over the certified derived tensor
  product, as [Stacks, Tag 0B66] is in this tree.
* `StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_restrictScalars_of_hasTorAmplitudeCanonical`
  and `StacksDraft.TorAmplitude.hasFiniteTorDimensionCanonical_restrictScalars`: the same at the
  canonical derived tensor product, and its existential form.
* `AlgebraicGeometry.hasFiniteTorDimensionCanonical_restrictScalars_appLE`: **the chart statement
  for a perfect morphism.** Over the chart ring map `f.appLE V U` of a perfect `f`, derived
  restriction of scalars carries finite Tor dimension to finite Tor dimension.

## Implementation notes

[Stacks, Tag 066K] is already in this tree, as
`StacksDraft.TorAmplitude.hasTorAmplitudeIn_restrictScalars_of_torDimensionLE`, but only with the
interval of `B` over `A` in the normalised form `[-d, 0]` that the source's phrase "Tor dimension
at most `d`" fixes. `AlgebraicGeometry.Perfect` asks only that `Γ(X, U)` have *finite* Tor
dimension over `Γ(S, V)` — `StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension`, an interval
`[c, d]` with no sign condition on `d` — so the normalised form cannot be fed from it without a
separate argument that the upper end of an interval for a module placed in degree zero may be
taken to be `0`. The general-interval form below avoids that argument entirely: it is
[Stacks, Tag 0B66] at `L = B[0]`, by the right unitor of the certified derived tensor product,
with the two intervals left as they are, which is the same proof the `[-d, 0]` form is obtained
by.

The two rings and the carriers of the complex live in one universe, and the ring map is an
`Algebra` instance, as in `StacksDraft.TorAmplitude.hasTorAmplitudeIn_derivedTensor`. The chart
statement needs no more: `f.appLE V U` makes `Γ(X, U)` a `Γ(S, V)`-algebra and both rings are
sections of structure sheaves of schemes in the same universe.

## References

* [Stacks Project, Tag 066K](https://stacks.math.columbia.edu/tag/066K)
* [Stacks Project, Tag 0B66](https://stacks.math.columbia.edu/tag/0B66)
* [Stacks Project, Tag 0687](https://stacks.math.columbia.edu/tag/0687)
* [Stacks Project, Tag 067H](https://stacks.math.columbia.edu/tag/067H)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
-/

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.TorAmplitude

universe u

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- **[Stacks, Tag 0B66] with `L = B[0]`, at an arbitrary interval.** Let `A → B` be a map of
commutative rings, let `K` be a complex of `B`-modules with Tor amplitude in `[a, b]` over `B`,
and assume that `B` placed in degree zero has Tor amplitude in `[c, d]` over `A`. Then `K`, after
restriction of scalars, has Tor amplitude in `[a + c, b + d]` over `A`.

This is `hasTorAmplitudeIn_derivedTensor` at `L = B[0]`: the right unitor of the certified derived
tensor product identifies `K ⊗_B^L B[0]` with `K`. Taking `[c, d] = [-d, 0]` gives
[Stacks, Tag 066K], which is
`hasTorAmplitudeIn_restrictScalars_of_torDimensionLE`; the point of the general interval is that
finite Tor dimension of `B` over `A` supplies an interval with no sign condition on its upper
end.

Like the statements it is built from this is quantified over the certified bifunctor over each of
`A` and `B` and carries no `@[stacks]` attribute; the endpoint at the canonical derived tensor
product is `hasTorAmplitudeCanonical_restrictScalars_of_hasTorAmplitudeCanonical` below. -/
public theorem hasTorAmplitudeIn_restrictScalars_of_hasTorAmplitudeIn
    (TA : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (TB : CochainComplex.DerivedTensor.DerivedTensorProduct B)
    (comparisonB : ∀ N : ModuleCat.{u} B,
      DerivedCategory.Q ⋙ TB.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedB : ∀ N : ModuleCat.{u} B,
      (TB.tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N)).IsLeftDerivedFunctor
          (comparisonB N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (a b c d : ℤ)
    (hB : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TA)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))) c d)
    (hK : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TB)
      (DerivedCategory.Q.obj K) a b) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TA)
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)) (a + c) (b + d) := by
  set L := (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)
  let RD := (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory
  let eQL : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B) ≅
      DerivedCategory.Q.obj L :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} B) 0).app (ModuleCat.of B B)
  have hL : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TA)
      (RD.obj (DerivedCategory.Q.obj L)) c d :=
    hasTorAmplitudeIn_of_iso _
      ((((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of B B)).symm ≪≫ RD.mapIso eQL) hB
  let eU : (TB.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj K :=
    ((TB.tensor.obj (DerivedCategory.Q.obj K)).mapIso eQL).symm ≪≫
      TB.rightUnitor.app (DerivedCategory.Q.obj K)
  exact hasTorAmplitudeIn_of_iso _ (RD.mapIso eU)
    (hasTorAmplitudeIn_derivedTensor A B TA TB comparisonB isLeftDerivedB K L a b c d hK hL)

/-- **[Stacks, Tag 0B66] with `L = B[0]`, at the canonical derived tensor product.** If `B` placed
in degree zero has Tor amplitude in `[c, d]` over `A` and `K` has Tor amplitude in `[a, b]` over
`B`, then `K`, after restriction of scalars, has Tor amplitude in `[a + c, b + d]` over `A`. -/
public theorem hasTorAmplitudeCanonical_restrictScalars_of_hasTorAmplitudeCanonical
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (a b c d : ℤ)
    (hB : HasTorAmplitudeCanonical A
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))) c d)
    (hK : HasTorAmplitudeCanonical B (DerivedCategory.Q.obj K) a b) :
    HasTorAmplitudeCanonical A
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)) (a + c) (b + d) :=
  (hasTorAmplitudeIn_canonical_iff A _ (a + c) (b + d)).mp
    (hasTorAmplitudeIn_restrictScalars_of_hasTorAmplitudeIn A B
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A)
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct B)
      (canonicalTensorComparison B) (canonicalTensorIsLeftDerived B) K a b c d
      ((hasTorAmplitudeIn_canonical_iff A _ c d).mpr hB)
      ((hasTorAmplitudeIn_canonical_iff B _ a b).mpr hK))

/-- **Derived restriction of scalars along a ring map of finite Tor dimension preserves finite Tor
dimension.** If `B`, as an `A`-module, has finite Tor dimension and `K` is a complex of
`B`-modules of finite Tor dimension over `B`, then `K`, read over `A`, has finite Tor dimension.

The two intervals are added, which is why the general-interval form above is what this is proved
from. -/
public theorem hasFiniteTorDimensionCanonical_restrictScalars
    (K : CochainComplex (ModuleCat.{u} B) ℤ)
    (hB : ∃ c d : ℤ, HasTorAmplitudeCanonical A
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))) c d)
    (hK : ∃ a b : ℤ, HasTorAmplitudeCanonical B (DerivedCategory.Q.obj K) a b) :
    ∃ a b : ℤ, HasTorAmplitudeCanonical A
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)) a b := by
  obtain ⟨c, d, hcd⟩ := hB
  obtain ⟨a, b, hab⟩ := hK
  exact ⟨a + c, b + d,
    hasTorAmplitudeCanonical_restrictScalars_of_hasTorAmplitudeCanonical A B K a b c d hcd hab⟩

end

end StacksDraft.TorAmplitude

namespace AlgebraicGeometry

open StacksDraft.TorAmplitude

universe u

attribute [local instance] HasDerivedCategory.standard

@[expose] public section

/-- **The chart statement of [Stacks, Tag 066K] for a perfect morphism of schemes.** Let
`f : X ⟶ S` be perfect, let `V ⊆ S` and `U ⊆ f^{-1}V` be affine opens and let `K` be a complex of
`Γ(X, U)`-modules of finite Tor dimension over `Γ(X, U)`. Then `K`, read as a complex of
`Γ(S, V)`-modules along the chart ring map `f.appLE V U`, has finite Tor dimension over
`Γ(S, V)`.

Perfectness of `f` says exactly that the chart ring map is a perfect ring map
([Stacks, Tag 067H] (2)), whose second clause is that `Γ(X, U)` has finite Tor dimension as a
`Γ(S, V)`-module; `hasFiniteTorDimensionCanonical_restrictScalars` does the rest. Only the
Tor clause of perfectness is used; the pseudo-coherence clause is not.

Over affine charts the derived direct image is derived restriction of scalars
([Stacks, Tag 0A9F]), so this is the ring-level content of the affine case of the Tor-dimension
half of [Stacks, Tag 08EV]. -/
theorem hasFiniteTorDimensionCanonical_restrictScalars_appLE {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.Perfect f] (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens)
    (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    ∀ K : CochainComplex (ModuleCat.{u} Γ(X, U)) ℤ,
      (∃ a b : ℤ, HasTorAmplitudeCanonical Γ(X, U) (DerivedCategory.Q.obj K) a b) →
        ∃ a b : ℤ, HasTorAmplitudeCanonical Γ(S, V)
          ((ModuleCat.restrictScalars
            (algebraMap Γ(S, V) Γ(X, U))).mapDerivedCategory.obj
              (DerivedCategory.Q.obj K)) a b := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  intro K hK
  refine hasFiniteTorDimensionCanonical_restrictScalars Γ(S, V) Γ(X, U) K ?_ hK
  have : Algebra.Perfect Γ(S, V) Γ(X, U) :=
    RingHom.perfect_algebraMap.mp (HasRingHomProperty.appLE @Perfect f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV)
  let D := canonicalCertifiedDerivedTensoring Γ(S, V)
  obtain ⟨c, d, hcd⟩ :=
    Algebra.Perfect.moduleHasFiniteTorDimension (B := Γ(X, U)) D.comparison D.isLeftDerived
  exact ⟨c, d, (hasTorAmplitudeIn_canonicalCertified_iff Γ(S, V) _ c d).mp hcd⟩

end

end AlgebraicGeometry
