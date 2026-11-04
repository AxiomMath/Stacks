module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AlmostBlowUp.PrincipalCenterHDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.GeneratorModelRecognition
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.OneGeneratorSquareShape

/-!
# Recognizing an almost blowup square with a closed-immersion modification

Over an affine base, a closed immersion of finite presentation which is an isomorphism away from
a principal centre *is* the modification of an almost blowup square with that centre.  This is
the converse of Stacks 0EVG read as a recognition criterion, and it is what the induction of
Stacks 0EVI needs where a square is known to have the shape of Example 0EVG but is not yet known
to be an almost blowup square — in particular for the closed immersion between the modifications
of two almost blowup squares with the same centre, which Stacks 0EVB produces.

## Main results

* `AlgebraicGeometry.isAlmostBlowUpSquare_of_restrict_isIso`: the recognition criterion.
* `AlgebraicGeometry.isIso_restrict_of_over_iso`: restricting to an open is invariant under an
  isomorphism over the target.
* `AlgebraicGeometry.isIso_restrict_compl_support_comap`: being an isomorphism away from the
  centre passes to an arbitrary base change.

## Implementation notes

The shape of Example 0EVG is recorded twice in this development, as
`AlgebraicGeometry.IsOneGeneratorAlmostBlowUpModel` — the form conditions (3) and (4) of Stacks
0EVI are stated at — and as `AlgebraicGeometry.IsPrincipalCenterModelPair`, which is the form
`AlgebraicGeometry.exists_isAlmostBlowUpSquare_of_isPrincipalCenterModelPair` consumes.  The two
say the same thing: an isomorphism of the base with `Spec A` carrying the modification and the
centre to the model pair over `Spec A`.  The translation is
`AlgebraicGeometry.IsOneGeneratorAlmostBlowUpModel.isPrincipalCenterModelPair`, and the
recognition criterion is the composite of
`AlgebraicGeometry.isOneGeneratorAlmostBlowUpModel_of_restrict_isIso` with it, the centre coming
out as the given one because an ideal sheaf is determined by the closed subscheme it cuts out
(`AlgebraicGeometry.Scheme.IdealSheafData.eq_of_subschemeIso`).

The base change statement is proved on kernels: a closed immersion is an isomorphism over an open
exactly when its ideal sheaf has vanishing inverse image there, the kernel of a base change of a
closed immersion is the inverse image of its kernel, and the complement of the support of the
inverse-image centre is the inverse image of the complement of the support of the centre.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
* [Stacks Project, Tag 0EVB](https://stacks.math.columbia.edu/tag/0EVB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **A closed immersion of finite presentation over an affine base which is an isomorphism away
from a principal centre is the modification of an almost blowup square with that centre.**

This is the recognition criterion the induction of Stacks 0EVI uses: by
`AlgebraicGeometry.isOneGeneratorAlmostBlowUpModel_of_restrict_isIso` such a morphism has the
shape of Example 0EVG, and Stacks 0EVG makes the model square an almost blowup square. -/
public theorem isAlmostBlowUpSquare_of_restrict_isIso {X X' : Scheme.{u}} [IsAffine X]
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsClosedImmersion b] (hfp : FinitePresentation b)
    (hiso : IsIso (b ∣_ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens)))
    (t : Γ(X, ⊤)) (ht : I.ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {t}) :
    IsAlmostBlowUpSquare I b := by
  obtain ⟨I', hb', hcen⟩ := exists_isAlmostBlowUpSquare_of_isPrincipalCenterModelPair b
    I.subschemeι
    (isOneGeneratorAlmostBlowUpModel_of_restrict_isIso I b hfp hiso t ht).isPrincipalCenterModelPair
  obtain ⟨w⟩ := hcen
  have hII' : I = I' :=
    Scheme.IdealSheafData.eq_of_subschemeIso I I' ((Over.forget X).mapIso w) (Over.w w.hom)
  rw [hII']
  exact hb'

/-- Restricting to an open is invariant under an isomorphism over the target. -/
public theorem isIso_restrict_of_over_iso {X X' Y : Scheme.{u}} (f : X ⟶ Y) (g : X' ⟶ Y)
    (e : Over.mk f ≅ Over.mk g) (U : Y.Opens) (hfU : IsIso (f ∣_ U)) : IsIso (g ∣_ U) := by
  have := hfU
  let h : X' ⟶ X := e.inv.left
  have : IsIso h := inferInstanceAs (IsIso ((Over.forget Y).map e.inv))
  have hh : h ≫ f = g := e.inv.w
  rw [← hh, morphismRestrict_comp]
  exact IsIso.comp_isIso' (inferInstance : IsIso (h ∣_ f ⁻¹ᵁ U))
    (inferInstance : IsIso (f ∣_ U))

/-- **Being an isomorphism away from the centre passes to a base change.** If a closed immersion
is an isomorphism over the complement of the support of `I`, then its base change along any
morphism is an isomorphism over the complement of the support of the inverse image of `I`. -/
public theorem isIso_restrict_compl_support_comap {X X' Y : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsClosedImmersion b] [QuasiCompact b] (g : Y ⟶ X)
    (hiso : IsIso (b ∣_ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens))) :
    IsIso (pullback.fst g b ∣_
      (⟨(I.comap g).supportᶜ, (I.comap g).support.isClosed.isOpen_compl⟩ : Y.Opens)) := by
  have := hiso
  set V : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ with hV
  have hVV' : (⟨(I.comap g).supportᶜ, (I.comap g).support.isClosed.isOpen_compl⟩ : Y.Opens) =
      g ⁻¹ᵁ V := by
    refine TopologicalSpace.Opens.ext ?_
    change ((I.comap g).support : Set Y)ᶜ = g ⁻¹' ((I.support : Set X)ᶜ)
    rw [Set.preimage_compl, Scheme.IdealSheafData.support_comap]
    rfl
  rw [hVV', IsClosedImmersion.isIso_iff_ker_eq_bot,
    ker_morphismRestrict_eq_comap (pullback.fst g b) (g ⁻¹ᵁ V),
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion b g,
    ← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι g V,
    Scheme.IdealSheafData.comap_comp, ← ker_morphismRestrict_eq_comap b V,
    Scheme.Hom.ker_eq_bot_of_isIso, Scheme.IdealSheafData.comap_bot]

end AlgebraicGeometry

end
