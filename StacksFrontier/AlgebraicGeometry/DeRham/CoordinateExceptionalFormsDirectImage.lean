module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBundleFormsPushforward
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateExceptionalProjectiveBundle
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve

/-!
# Clause (2) of Stacks 0FUR on the exceptional divisor itself

Clause (2) of [Stacks, Tag 0FUR] is stated for the projective bundle `p : P = 𝐏^{n-1}_Z ⟶ Z`
(`Stacks.DeRham.isIso_coordinateBundleFormsDirectImage`). The source's situation identifies `P`
with the exceptional divisor `E` of the blowup, and the consumers of the tag (Tag 0FUU) work on
`E` with its morphism `E ⟶ Z` to the centre. This file transports the clause along the
identification `E ≅ P` over `Z` (`Stacks.DeRham.coordinateExceptionalIsoBundle`), for every
`n ≥ 1`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_formsDirectImageComparison_of_iso`: invertibility of the
  comparison map is invariant under an isomorphism of the source over the target.
* `Stacks.DeRham.isIso_coordinateExceptionalFormsDirectImage`: the comparison map
  `Ω^a_{Z/S} ⟶ (E ⟶ Z)_*Ω^a_{E/S}` is an isomorphism, `E ⟶ Z` being
  `AlgebraicGeometry.exceptionalDivisorToCentre` of the coordinate closed immersion.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **Invertibility of the comparison map on forms is invariant under an isomorphism of the
source over the target.** If `e : W ≅ P` carries `t : W ⟶ Z` to `q : P ⟶ Z` and the comparison
map of `q` is an isomorphism, so is that of `t`: by the composition law the map of
`e.hom ≫ q = t` is the map of `q` followed by `q_*` of the map of the isomorphism `e.hom`. -/
theorem isIso_formsDirectImageComparison_of_iso {W P Z S : Scheme.{u}} (e : W ≅ P)
    {q : P ⟶ Z} {t : W ⟶ Z} (h : e.hom ≫ q = t) (π : Z ⟶ S) (d : ℤ)
    (hq : IsIso (formsDirectImageComparison q π d)) :
    IsIso (formsDirectImageComparison t π d) := by
  subst h
  rw [formsDirectImageComparison_comp]
  have := isIso_formsDirectImageComparison_of_isIso e.hom (q ≫ π) d
  have : IsIso ((Scheme.Modules.pushforward q).map
      (formsDirectImageComparison e.hom (q ≫ π) d)) := Functor.map_isIso _ _
  exact IsIso.comp_isIso' hq (IsIso.comp_isIso' this
    (Iso.isIso_hom ((Scheme.Modules.pushforwardComp e.hom q).app _)))

end AlgebraicGeometry.Scheme.Hom

namespace Stacks.DeRham

attribute [local instance] Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion

variable (R : Type u) [CommRing R] (m : ℕ)

/-- The identification `E ≅ 𝐏^{n-1}_Z` lies over `exceptionalDivisorToCentre` of the coordinate
closed immersion: both morphisms `E ⟶ Z` become `E ⟶ L ⟶ X` after composing with `Z ⟶ X`. -/
theorem coordinateExceptionalIsoBundle_hom_exceptionalDivisorToCentre (k : ℕ) :
    (coordinateExceptionalIsoBundle R m k).hom ≫ coordinateBlowupBundleToCentre R m (k + 1) =
      exceptionalDivisorToCentre (Stacks.MoreMorphisms.coordinateEmbedding R m (k + 1)) := by
  refine (cancel_mono (Stacks.MoreMorphisms.coordinateEmbedding R m (k + 1))).mp ?_
  refine ((coordinateExceptionalIsoBundle_hom_toCentre R m k).symm ▸
    (coordinateExceptionalι_comp_blowupToAmbient R m (k + 1)).symm).trans ?_
  exact (exceptionalDivisorToCentre_comp _).symm

/-- The centre `Z ⟶ X ⟶ S` is the structure morphism of `𝐀^m_S`. -/
theorem coordinateEmbedding_comp_ambientToBase (n : ℕ) :
    Stacks.MoreMorphisms.coordinateEmbedding R m n ≫ coordinateAmbientToBase R m n =
      coordinateBlowupCentreToBase R m := by
  rw [Stacks.MoreMorphisms.coordinateEmbedding, ← Spec.map_comp]
  congr 1
  ext1
  exact RingHom.ext fun r => by simp [Stacks.MoreMorphisms.coordinateProjection]

/-- **[Stacks, Tag 0FUR], clause (2), on the exceptional divisor.** For every `n ≥ 1` and every
`a`, the comparison map `Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` is an isomorphism, where `E` is the
exceptional divisor of the blowup of `𝐀^{m+n}_S` along `Z = 𝐀^m_S` and
`p = exceptionalDivisorToCentre i : E ⟶ Z` for the coordinate closed immersion `i`. This is
`Stacks.DeRham.isIso_coordinateBundleFormsDirectImage`, transported along `E ≅ 𝐏^{n-1}_Z`. -/
theorem isIso_coordinateExceptionalFormsDirectImage (n : ℕ) (hn : 1 ≤ n) (a : ℕ) :
    IsIso (Scheme.Hom.formsDirectImageComparison
      (exceptionalDivisorToCentre (Stacks.MoreMorphisms.coordinateEmbedding R m n))
      (Stacks.MoreMorphisms.coordinateEmbedding R m n ≫ coordinateAmbientToBase R m n) a) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [coordinateEmbedding_comp_ambientToBase]
  exact Scheme.Hom.isIso_formsDirectImageComparison_of_iso (coordinateExceptionalIsoBundle R m k)
    (coordinateExceptionalIsoBundle_hom_exceptionalDivisorToCentre R m k) _ _
    (isIso_coordinateBundleFormsDirectImage R m (k + 1) a)

end Stacks.DeRham
