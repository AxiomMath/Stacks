module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne

/-!
# The blowup of the spectrum of a one-dimensional Noetherian local ring is finite over it

For a Noetherian local ring `R` of Krull dimension at most one and any quasi-coherent ideal sheaf
on `Spec R`, the blowup morphism is finite.

## Main results

* `AlgebraicGeometry.isFinite_of_isFinite_morphismRestrict_top`: a morphism whose restriction over
  the whole target is finite is finite.
* `AlgebraicGeometry.isIso_stalkMap_of_isIso_morphismRestrict`: a morphism which restricts to an
  isomorphism over an open induces isomorphisms on the stalks above that open.
* `AlgebraicGeometry.isAlgebraic_residueField_of_isIso_stalkMap`: an isomorphism on a stalk gives
  an algebraic extension of residue fields.
* `AlgebraicGeometry.isFinite_blowUpToBase_of_ringKrullDim_le_one`: the blowup of the spectrum of a
  one-dimensional Noetherian local ring in any quasi-coherent ideal sheaf is finite over it.

## Implementation notes

The blowup morphism is proper and, being an isomorphism over the complement of the centre, induces
an isomorphism of stalks at every generic point of the blowup, hence an algebraic extension of
residue fields there. Tag 0AB7 then makes it finite over a neighbourhood of the closed point, and
the only open of the spectrum of a local ring containing the closed point is everything.

## References

* [Stacks Project, Tag 0AB7](https://stacks.math.columbia.edu/tag/0AB7)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0BFM](https://stacks.math.columbia.edu/tag/0BFM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A morphism whose restriction over the whole target is finite is finite.** Finiteness is
Zariski-local on the target and `⊤` covers the target. -/
theorem isFinite_of_isFinite_morphismRestrict_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : IsFinite (f ∣_ (⊤ : Y.Opens))) : IsFinite f := by
  have hι : ∀ {Z : Scheme.{u}} (V : Z.Opens), V = ⊤ → IsIso V.ι := by
    rintro Z V rfl
    rw [← Scheme.topIso_hom]
    infer_instance
  have : IsIso (Scheme.Opens.ι (⊤ : Y.Opens)) := hι _ rfl
  have : IsIso (Scheme.Opens.ι (f ⁻¹ᵁ (⊤ : Y.Opens))) := hι _ (by simp)
  have h1 : IsFinite (Scheme.Opens.ι (f ⁻¹ᵁ (⊤ : Y.Opens)) ≫ f) := by
    rw [← morphismRestrict_ι]
    exact MorphismProperty.comp_mem @IsFinite _ _ h inferInstance
  simpa using MorphismProperty.comp_mem @IsFinite _ _
    (inferInstance : IsFinite (inv (Scheme.Opens.ι (f ⁻¹ᵁ (⊤ : Y.Opens))))) h1

/-- **A morphism restricting to an isomorphism over an open induces isomorphisms on the stalks at
the points above that open.** -/
theorem isIso_stalkMap_of_isIso_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    (hU : IsIso (f ∣_ U)) {x : X} (hx : x ∈ f ⁻¹ᵁ U) : IsIso (f.stalkMap x) :=
  (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
    (morphismRestrictStalkMap f U ⟨x, hx⟩)).mp
      (((isIso_iff_isIso_stalkMap (f ∣_ U)).mp hU).2 ⟨x, hx⟩)

/-- **An isomorphism on a stalk gives an algebraic extension of residue fields.** The induced map
of residue fields is then an isomorphism, in particular surjective. -/
theorem isAlgebraic_residueField_of_isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : IsIso (f.stalkMap x)) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x) := by
  let _ := (f.residueFieldMap x).hom.toAlgebra
  have : IsIso (f.residueFieldMap x) :=
    ((IsLocalRing.ResidueField.mapEquiv
      (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso).isIso_hom
  refine Algebra.isAlgebraic_iff_isIntegral.mpr (Algebra.isIntegral_of_surjective fun z => ?_)
  obtain ⟨w, rfl⟩ := (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.surjective z
  exact ⟨w, rfl⟩

/-- The stalk of the spectrum of a Noetherian local ring at its closed point is Noetherian: it is
the localization of the ring at its maximal ideal. -/
theorem isNoetherianRing_stalk_closedPoint (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    IsNoetherianRing ((Spec (CommRingCat.of R)).presheaf.stalk (IsLocalRing.closedPoint R)) := by
  have : IsNoetherianRing (Localization.AtPrime (IsLocalRing.maximalIdeal R)) :=
    IsLocalization.isNoetherianRing (IsLocalRing.maximalIdeal R).primeCompl _ inferInstance
  exact isNoetherianRing_of_ringEquiv _
    (Spec.stalkIso (CommRingCat.of R) (IsLocalRing.closedPoint R)).commRingCatIsoToRingEquiv.symm

/-- The stalk of the spectrum of a local ring at its closed point has the Krull dimension of the
ring. -/
theorem ringKrullDim_stalk_closedPoint (R : Type u) [CommRing R] [IsLocalRing R] :
    ringKrullDim ((Spec (CommRingCat.of R)).presheaf.stalk (IsLocalRing.closedPoint R)) =
      ringKrullDim R :=
  calc ringKrullDim ((Spec (CommRingCat.of R)).presheaf.stalk (IsLocalRing.closedPoint R))
      = ringKrullDim (Localization.AtPrime (IsLocalRing.maximalIdeal R)) :=
        ringKrullDim_eq_of_ringEquiv
          (Spec.stalkIso (CommRingCat.of R)
            (IsLocalRing.closedPoint R)).commRingCatIsoToRingEquiv
    _ = ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height (IsLocalRing.maximalIdeal R) _
    _ = ringKrullDim R := IsLocalRing.maximalIdeal_height_eq_ringKrullDim

/-- **The blowup of the spectrum of a Noetherian local ring of dimension at most one is finite over
it.** The blowup morphism is proper and an isomorphism over the complement of the centre, which
contains every generic point of the blowup, so Tag 0AB7 applies at the closed point; the
neighbourhood it produces is the whole spectrum. -/
theorem isFinite_blowUpToBase_of_ringKrullDim_le_one {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (hdim : ringKrullDim R ≤ 1)
    (I : (Spec (CommRingCat.of R)).IdealSheafData) :
    IsFinite (blowUpToBase I) := by
  have hiso : IsIso (blowUpToBase I ∣_
      (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : (Spec (CommRingCat.of R)).Opens)) :=
    isIso_blowUp_restrict_compl_support I
  have hgeneric : ∀ η : blowUp I, η ∈ genericPoints (blowUp I) →
      let := ((blowUpToBase I).residueFieldMap η).hom.toAlgebra
      Algebra.IsAlgebraic ((Spec (CommRingCat.of R)).residueField (blowUpToBase I η))
        ((blowUp I).residueField η) := by
    intro η hη
    refine isAlgebraic_residueField_of_isIso_stalkMap _ η
      (isIso_stalkMap_of_isIso_morphismRestrict _ hiso ?_)
    exact fun hmem => ((bijOn_genericPoints_blowUpToBase I).1 hη).2
      (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr hmem)
  have := isNoetherianRing_stalk_closedPoint R
  obtain ⟨V, hVmem, hVfin⟩ := exists_isFinite_morphismRestrict_of_ringKrullDim_stalk_le_one
    (blowUpToBase I) (IsLocalRing.closedPoint R)
    ((ringKrullDim_stalk_closedPoint R).trans_le hdim) (Or.inl hgeneric)
  exact isFinite_of_isFinite_morphismRestrict_top _
    (((IsLocalRing.closedPoint_mem_iff V).mp hVmem) ▸ hVfin)

end AlgebraicGeometry

end
