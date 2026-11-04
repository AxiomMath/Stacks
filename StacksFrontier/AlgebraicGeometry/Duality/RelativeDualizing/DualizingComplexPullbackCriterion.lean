module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.UpperShriekCriterion
public import
  StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexSyntomicDescent

/-!
# Dualizing complexes and derived pullback along a syntomic or Gorenstein surjection

Let `f : X ⟶ Y` be a morphism of locally Noetherian schemes which is syntomic and surjective, or
a surjective flat local complete intersection morphism, or a surjective Gorenstein morphism of
finite type. [Stacks, Tag 0E4N] says that `K ∈ D_QCoh(𝒪_Y)` is a dualizing complex on `Y` if and
only if `Lf^*K` is a dualizing complex on `X`.

The proof reads the condition at a pair of affine opens `V ⊆ f⁻¹(U)` on which `f` is still
surjective, where it becomes [Stacks, Tag 0E4D] for the ring map `f.appLE U V`. For a Gorenstein
morphism the input that ring-level statement needs is that the fibre rings `κ(q) ⊗ Γ(X, V)` are
Gorenstein rings; this is `AlgebraicGeometry.Scheme.Hom.isGorensteinRing_fiber_appLE`: `Spec` of
`f.appLE U V` is Gorenstein at every point because `f` is, and Gorensteinness of
`Spec(B) → Spec(A)` at a prime is Gorensteinness of the matching local ring of the fibre ring.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isGorensteinRing_fiber_appLE` — the fibre rings of `f.appLE U V`
  of a Gorenstein morphism locally of finite type are Gorenstein rings.
* `Stacks.Duality.isDualizingComplex_iff_derivedPullback_of_syntomic_of_surjective` —
  [Stacks, Tag 0E4N] case (1).
* `Stacks.Duality.isDualizingComplex_iff_derivedPullback_of_flat_lci_of_surjective` —
  [Stacks, Tag 0E4N] case (2).
* `Stacks.Duality.isDualizingComplex_iff_derivedPullback_of_isGorenstein_of_surjective` —
  [Stacks, Tag 0E4N] case (3).

## Implementation notes

The statements live at `CategoryTheory.HasDerivedCategory.standard`, the model at which
`Stacks.Duality.HasDualizingModelOn` and the affine comparison of
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexSyntomicDescent` are
stated; see that file for why that model is forced.

## References

* [Stacks Project, Tag 0E4N](https://stacks.math.columbia.edu/tag/0E4N)
* [Stacks Project, Tag 0E4D](https://stacks.math.columbia.edu/tag/0E4D)
* [Stacks Project, Tag 0C04](https://stacks.math.columbia.edu/tag/0C04)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom

/-- **The fibre rings of a Gorenstein morphism at an affine pair are Gorenstein.** Let
`f : X ⟶ Y` be a Gorenstein morphism locally of finite type, and let `V ⊆ f⁻¹(U)` be affine
opens. For every prime `q` of `Γ(Y, U)` the fibre ring `κ(q) ⊗_{Γ(Y, U)} Γ(X, V)` of
`f.appLE U V` is a Gorenstein ring. -/
theorem isGorensteinRing_fiber_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hGor : IsGorenstein f (isLocallyNoetherian_fiber_of_locallyOfFiniteType f))
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) (q : Ideal Γ(Y, U)) [q.IsPrime] :
    letI : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
    letI : Algebra.FiniteType Γ(Y, U) Γ(X, V) := f.finiteType_appLE hU hV hVU
    letI := Algebra.FiniteType.isNoetherianRing q.ResidueField (q.Fiber Γ(X, V))
    Dualizing.IsGorensteinRing (q.Fiber Γ(X, V)) := by
  let R : Type u := Γ(Y, U)
  let B : Type u := Γ(X, V)
  let : Algebra R B := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType R B := f.finiteType_appLE hU hV hVU
  have : Flat f := Flat.of_stalkMap f fun x => (hGor x).1
  have : Module.Flat R B := f.flat_appLE hU hV hVU
  obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation (algebraMap R B)
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  let f' : Spec (.of B) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have : LocallyOfFiniteType f' :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let hf' := isLocallyNoetherian_fiber_of_locallyOfFiniteType f'
  have w : hV.fromSpec ≫ f = f' ≫ hU.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU).symm
  refine Stacks.Duality.isGorensteinRing_fiber_of_isGorensteinLocalRing_affineFiberPoint p
    (fun z => ?_) q
  let := Dualizing.isNoetherianRing_baseChange
    (PrimeSpectrum.comap (algebraMap R B) z).asIdeal.ResidueField p
  exact (isGorensteinAt_specMap_iff hf' z).mp
    ((isGorensteinAt_iff_of_comp_eq hV.fromSpec hU.fromSpec f f' w _ hf'
      (isLocallyNoetherian_fiber_of_locallyOfFiniteType _) z).mp (hGor _))

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.Duality

variable {X Y : Scheme.{u}}

/-- **Stacks Project, Tag 0E4N, case (1).** Let `f : X ⟶ Y` be a syntomic surjective morphism
of locally Noetherian schemes and let `K` be an object of `D_QCoh(𝒪_Y)`. Then `K` is a dualizing
complex on `Y` if and only if `Lf^*K` is a dualizing complex on `X`. -/
@[stacks 0E4N "case (1): f syntomic and surjective"]
theorem isDualizingComplex_iff_derivedPullback_of_syntomic_of_surjective [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Surjective f] (hf : Syntomic f)
    (K : DerivedCategory Y.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj K).IsQuasicoherent) :
    IsDualizingComplex K ↔
      IsDualizingComplex
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom).obj K) := by
  have : Flat f := ((syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism f).mp hf).1
  have : LocallyOfFinitePresentation f := AlgebraicGeometry.locallyOfFinitePresentation hf
  exact ⟨isDualizingComplex_derivedPullback_of_syntomic f hf K hK,
    isDualizingComplex_of_isDualizingComplex_derivedPullback f K hK⟩

/-- **Stacks Project, Tag 0E4N, case (2).** Let `f : X ⟶ Y` be a surjective flat local complete
intersection morphism of locally Noetherian schemes and let `K` be an object of `D_QCoh(𝒪_Y)`.
Then `K` is a dualizing complex on `Y` if and only if `Lf^*K` is a dualizing complex on `X`.

A flat local complete intersection morphism is syntomic ([Stacks, Tag 069K]), so this is
case (1). -/
@[stacks 0E4N "case (2): f a surjective flat local complete intersection morphism"]
theorem isDualizingComplex_iff_derivedPullback_of_flat_lci_of_surjective [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [Surjective f] [Flat f]
    (hlci : IsLocalCompleteIntersectionMorphism f) (K : DerivedCategory Y.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj K).IsQuasicoherent) :
    IsDualizingComplex K ↔
      IsDualizingComplex
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom).obj K) :=
  isDualizingComplex_iff_derivedPullback_of_syntomic_of_surjective f
    ((syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism f).mpr ⟨‹Flat f›, hlci⟩) K hK

/-- **Stacks Project, Tag 0E4N, case (3).** Let `f : X ⟶ Y` be a surjective Gorenstein morphism
of finite type of locally Noetherian schemes and let `K` be an object of `D_QCoh(𝒪_Y)`. Then `K`
is a dualizing complex on `Y` if and only if `Lf^*K` is a dualizing complex on `X`.

At an affine pair `V ⊆ f⁻¹(U)` on which `f` is still surjective, `f.appLE U V` is faithfully
flat of finite type with Gorenstein fibre rings (`Scheme.Hom.isGorensteinRing_fiber_appLE`), and
the ring-level statement is [Stacks, Tag 0E4D] case (3). -/
@[stacks 0E4N "case (3): f a surjective Gorenstein morphism of finite type"]
theorem isDualizingComplex_iff_derivedPullback_of_isGorenstein_of_surjective
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Surjective f] [QuasiCompact f]
    [LocallyOfFiniteType f]
    (hGor : Scheme.Hom.IsGorenstein f (isLocallyNoetherian_fiber_of_locallyOfFiniteType f))
    (K : DerivedCategory Y.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj K).IsQuasicoherent) :
    IsDualizingComplex K ↔
      IsDualizingComplex
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          f.toLRSHom.toShHom).obj K) := by
  have : Flat f := Flat.of_stalkMap f fun x => (hGor x).1
  have : LocallyOfFinitePresentation f := inferInstance
  refine ⟨fun hKd => isDualizingComplex_of_affineLocalAscent f (fun x => ?_) hKd,
    fun hLd => isDualizingComplex_of_isDualizingComplex_derivedPullback f K hK hLd⟩
  obtain ⟨U, V, hVU, hx, hy, hs⟩ := exists_affineOpens_surjective_resLE f x
  refine ⟨U, V, hx, hy, fun hmodel => ?_⟩
  have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  let _ : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Y, U.1) Γ(X, V.1) := f.finiteType_appLE U.2 V.2 hVU
  obtain ⟨M, h1, h2⟩ := exists_model_hasDualizingModelOn_iff f U.2 V.2 hVU K hK
  exact h2.2
    ((Dualizing.isDualizingComplex_iff_derivedExtensionScalars_of_gorensteinFibres_unconditional
      (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
        ⟨f.flat_appLE U.2 V.2 hVU, surjective_comap_appLE f U.2 V.2 hVU hs⟩)
      (fun q _ => f.isGorensteinRing_fiber_appLE hGor U.2 V.2 hVU q) M).mp (h1.1 hmodel))

end Stacks.Duality

end
