module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedCompactPerfect
import StacksCore.Tactic.StacksAttribute

/-!
# A perfect generator of `D_{QCoh,T}(𝒪_X)` classically generates `D_{perf,T}(𝒪_X)`

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S`, let `T ⊆ |X|`
be a closed subset with `|X| ∖ T` quasi-compact, and let `G` be a perfect object of
`D_{QCoh,T}(𝒪_X)` which is a generator of `D_{QCoh,T}(𝒪_X)`; one exists by Stacks 0AEC
(`AlgebraicGeometry.Space.exists_isPerfect_generator_of_supported`). Stacks 0GFD says that `G` is
a *classical* generator of `D_{perf,T}(𝒪_X)`: the triangulated envelope of `G` in
`D_{QCoh,T}(𝒪_X)` (the smallest strictly full, saturated, triangulated subcategory containing
`G`, Stacks 0ATG) consists exactly of the objects that are perfect in `D(𝒪_X)`, that is, it is
`D_{perf,T}(𝒪_X)`.

## The proof

The proof follows the source. `D_{QCoh,T}(𝒪_X)` is a triangulated category with direct sums (the
remark before Stacks 0AED,
`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentDerivedSupportedOn`);
its compact objects are its perfect objects (Stacks 0AED,
`AlgebraicGeometry.Space.isCompactObject_iff_isPerfect_of_supported`), so `G` is compact; and a
compact weak generator of such a category classically generates its compact objects (Derived
Categories, Stacks 09SR, in the form
`CategoryTheory.Pretriangulated.triangEnvelope_eq_isCompactObject_of_locallySmall`, which allows
the morphism universe `u + 1` of the model `HasDerivedCategory.standard` against direct sums
indexed by `Type u`). The generation hypothesis is read as a weak generator of `D_{QCoh,T}(𝒪_X)`
by `AlgebraicGeometry.Space.isWeakTriangulatedGenerator_singleton_quasicoherentDerivedSupportedOn`.

## Main results

* `AlgebraicGeometry.Space.triangEnvelope_singleton_eq_isPerfect_of_supported`: **Stacks 0GFD**.

## References

* [Stacks Project, Tag 0GFD](https://stacks.math.columbia.edu/tag/0GFD)
* [Stacks Project, Tag 0AEC](https://stacks.math.columbia.edu/tag/0AEC)
* [Stacks Project, Tag 0AED](https://stacks.math.columbia.edu/tag/0AED)
* [Stacks Project, Tag 09SR](https://stacks.math.columbia.edu/tag/09SR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `S` be a scheme, `X` a quasi-compact and quasi-separated algebraic space over `S`, and
`T ⊆ |X|` a closed subset such that `|X| ∖ T` is quasi-compact. Let `G` be a perfect object of
`D(𝒪_X)` lying in `D_{QCoh,T}(𝒪_X)` (quasi-coherent cohomology sheaves supported on `T`) which is
a generator of `D_{QCoh,T}(𝒪_X)`: an object `E` of `D_QCoh(𝒪_X)` supported on `T` with
`Hom(G[n], E) = 0` for all `n ∈ ℤ` is zero. Then `G` is a classical generator of
`D_{perf,T}(𝒪_X)`: the triangulated envelope of `G` in `D_{QCoh,T}(𝒪_X)` — the smallest strictly
full, saturated, triangulated subcategory containing `G` — is exactly the property of being
perfect in `D(𝒪_X)`. -/
@[stacks 0GFD]
theorem triangEnvelope_singleton_eq_isPerfect_of_supported (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (G : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hG : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect G)
    (hGq : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) G)
    (hGs : CohomologySupportedOn B S hS X.1 X.2 T G)
    (hgen : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      CohomologySupportedOn B S hS X.1 X.2 T E.obj →
        (∀ (n : ℤ) (g : G⟦n⟧ ⟶ E.obj), g = 0) → IsZero E.obj) :
    (ObjectProperty.singleton
        (⟨⟨G, hGq⟩, hGs⟩ : (quasicoherentDerivedSupportedOn X T).FullSubcategory)).triangEnvelope =
      fun K => (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K.obj.obj := by
  have := isGrothendieckAbelian_modules_ringUniverse B S hS X.1 X.2
  have := enoughInjectives_modules_ringUniverse B S hS X.1 X.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS X.1 X.2
  have := fun J : Type u =>
    isClosedUnderColimitsOfShape_quasicoherentDerivedSupportedOn X T hT J
  let G' : (quasicoherentDerivedSupportedOn X T).FullSubcategory := ⟨⟨G, hGq⟩, hGs⟩
  have hcp := isCompactObject_iff_isPerfect_of_supported X hXqc hXqs T hT hTc
  rw [triangEnvelope_eq_isCompactObject_of_locallySmall G' ((hcp G').2 hG)
    (isWeakTriangulatedGenerator_singleton_quasicoherentDerivedSupportedOn X T G' hgen)]
  funext K
  exact propext (hcp K)

end AlgebraicGeometry.Space

end
