module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedQuasicoherentDerived

/-!
# A generator of `D_{QCoh,T}(𝒪_X)` in the sense of Stacks 0AEC is a weak generator

Let `X` be an algebraic space over a scheme `S` and `T ⊆ |X|` a closed subset. Stacks 0AEC calls
an object `G` of `D_{QCoh,T}(𝒪_X)` a generator when an object `E` of `D_QCoh(𝒪_X)` supported on
`T` is zero as soon as `Hom(G[n], E) = 0` for all `n ∈ ℤ`, the morphisms taken in `D(𝒪_X)`. This
file reads that condition as `CategoryTheory.ObjectProperty.IsWeakTriangulatedGenerator`
(Stacks 09SJ (3)) inside the full subcategory `D_{QCoh,T}(𝒪_X)`, the form of the hypothesis of
Derived Categories, Stacks 09SR; see also Stacks 0AED and Stacks 0GFD.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedSupportedOnι`: the composite inclusion
  `D_{QCoh,T}(𝒪_X) ⥤ D_QCoh(𝒪_X) ⥤ D(𝒪_X)`.
* `AlgebraicGeometry.Space.isWeakTriangulatedGenerator_singleton_quasicoherentDerivedSupportedOn`:
  a generator in the sense of Stacks 0AEC is a weak generator of `D_{QCoh,T}(𝒪_X)`.

## References

* [Stacks Project, Tag 0AEC](https://stacks.math.columbia.edu/tag/0AEC)
* [Stacks Project, Tag 09SJ](https://stacks.math.columbia.edu/tag/09SJ)
* [Stacks Project, Tag 0GFD](https://stacks.math.columbia.edu/tag/0GFD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The composite inclusion `D_{QCoh,T}(𝒪_X) ⥤ D_QCoh(𝒪_X) ⥤ D(𝒪_X)`. -/
abbrev quasicoherentDerivedSupportedOnι (X : AlgebraicSpaces B S hS)
    (T : Set (points B S hS X.1)) :
    (quasicoherentDerivedSupportedOn X T).FullSubcategory ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
  (quasicoherentDerivedSupportedOn X T).ι ⋙ ObjectProperty.ι _

/-- **A generator in the sense of Stacks 0AEC is a weak generator of `D_{QCoh,T}(𝒪_X)`.** If an
object `E` of `D_QCoh(𝒪_X)` supported on `T` is zero as soon as `Hom(G[n], E) = 0` for all
`n ∈ ℤ`, then `G`, as an object of `D_{QCoh,T}(𝒪_X)`, is a weak generator of that category. -/
theorem isWeakTriangulatedGenerator_singleton_quasicoherentDerivedSupportedOn
    (X : AlgebraicSpaces B S hS) (T : Set (points B S hS X.1))
    (G : (quasicoherentDerivedSupportedOn X T).FullSubcategory)
    (hgen : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2,
      CohomologySupportedOn B S hS X.1 X.2 T E.obj →
        (∀ (n : ℤ) (g : G.obj.obj⟦n⟧ ⟶ E.obj), g = 0) → IsZero E.obj) :
    (ObjectProperty.singleton G).IsWeakTriangulatedGenerator := by
  rw [ObjectProperty.isWeakTriangulatedGenerator_iff]
  intro K hK
  let F := quasicoherentDerivedSupportedOnι X T
  have hF : F.FullyFaithful :=
    (quasicoherentDerivedSupportedOn X T).fullyFaithfulι.comp (ObjectProperty.fullyFaithfulι _)
  have hK' : ¬ IsZero K.obj.obj := fun h => hK (by
    rw [IsZero.iff_id_eq_zero]
    exact hF.map_injective (h.eq_of_src _ _))
  have h := mt (hgen K.obj K.property) hK'
  rw [forall_hom_shift_eq_zero_iff] at h
  push Not at h
  obtain ⟨m, g, hg⟩ := h
  refine ⟨G, (ObjectProperty.singleton_iff _ _).2 rfl, m,
    hF.preimage (g ≫ (F.commShiftIso m).inv.app K), fun h0 => hg ?_⟩
  have := congrArg F.map h0
  rw [hF.map_preimage, Functor.map_zero] at this
  rw [← cancel_mono ((F.commShiftIso m).inv.app K), this, zero_comp]

end AlgebraicGeometry.Space

end
