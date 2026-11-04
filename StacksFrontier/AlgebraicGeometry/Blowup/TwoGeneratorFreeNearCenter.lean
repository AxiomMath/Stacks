module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorAdicFreeLift
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorExceptionalImmersion
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorSupportedSections
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.IsomorphismAwayFromCenter
public import StacksFrontier.AlgebraicGeometry.TwoGeneratorProper
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Freeness of a bundle on the two-generator modification over a neighbourhood of the centre

Let `b : X' ⟶ Spec A` be the two-generator modification `X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁))` of
[Stacks, Example 0EVH], with exceptional line `E` lying over the centre `Z`. Since `b` is proper,
every open neighbourhood of `E` in `X'` contains `b ⁻¹ᵁ U` for an open neighbourhood `U` of `Z`.
Hence a finite locally free module `𝒢` on `X'` whose restriction to `E` is free of rank `r` is
free of rank `r` over the preimage of an open neighbourhood `U` of the centre, and `U` together
with the complement of the centre covers the base.

## Main definitions

* `Stacks.AlmostBlowUp.centerComplement`: the complement of the support of the centre, as an open
  of the base.

## Main results

* `AlgebraicGeometry.exists_opens_preimage_le_of_universallyClosed`: along a universally closed
  morphism, an open containing the preimage of a set contains the preimage of an open
  neighbourhood of that set.
* `AlgebraicGeometry.isIso_restrictFunctor_map_of_le`: a morphism of modules invertible over an
  open is invertible over a smaller one.
* `Stacks.AlmostBlowUp.exists_opens_center_preimage_le`: an open neighbourhood of the exceptional
  line in the modification contains the preimage of an open neighbourhood of the centre.
* `Stacks.AlmostBlowUp.exists_opens_center_isIso_restrict_hom_free`: over the preimage of an open
  neighbourhood of the centre, a finite locally free module on the modification whose restriction
  to the exceptional line is free of rank `r` is free of rank `r`.
* `Stacks.AlmostBlowUp.range_exceptionalToModification_eq_preimage_support`: the exceptional line
  is, on points, the preimage of the support of the centre.
* `Stacks.AlmostBlowUp.isIso_modificationToBase_restrict_centerComplement`: the modification maps
  isomorphically over the complement of the centre.
* `Stacks.AlmostBlowUp.exists_opens_cover_isIso_restrict_hom_free`: there is an open `U` of the
  base which together with the complement of the centre covers the base, such that `𝒢` is free
  of rank `r` over the preimage of `U`.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Let `b : X' ⟶ X` be universally closed. If every point of `X'` lying over `T` belongs to the
open `W`, then there is an open `U` of `X` containing `T` with `b ⁻¹ᵁ U ≤ W`. -/
@[ega "IV 15.5.10" "more general"]
theorem exists_opens_preimage_le_of_universallyClosed {X X' : Scheme.{u}} (b : X' ⟶ X)
    [UniversallyClosed b] (W : X'.Opens) (T : Set X)
    (hT : ∀ x' : X', b.base x' ∈ T → x' ∈ W) :
    ∃ U : X.Opens, T ⊆ (U : Set X) ∧ b ⁻¹ᵁ U ≤ W := by
  refine ⟨⟨(b.base '' (W : Set X')ᶜ)ᶜ, (b.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩,
    ?_, ?_⟩
  · rintro t ht ⟨x', hx', rfl⟩
    exact hx' (hT x' ht)
  · exact fun x' hx' => Classical.byContradiction fun hw => hx' ⟨x', hw, rfl⟩

/-- A morphism of modules whose restriction to an open `U` is an isomorphism restricts to an
isomorphism on every open `W ≤ U`. -/
theorem isIso_restrictFunctor_map_of_le {X : Scheme.{u}} {U W : X.Opens} (h : W ≤ U)
    {M N : X.Modules} (φ : M ⟶ N)
    (hφ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map φ) := by
  have e : Scheme.Modules.restrictFunctor W.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.restrictFunctor (X.homOfLE h) :=
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).symm ≪≫
      Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι
  exact (NatIso.isIso_map_iff e φ).mpr
    (Functor.map_isIso (Scheme.Modules.restrictFunctor (X.homOfLE h))
      ((Scheme.Modules.restrictFunctor U.ι).map φ))

end AlgebraicGeometry

namespace Stacks.AlmostBlowUp



attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- An open neighbourhood `W` of the exceptional line in the modification contains the preimage
of an open neighbourhood of the centre in the base. -/
theorem exists_opens_center_preimage_le
    (W : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Opens)
    (hW : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      Set.range (exceptionalToModification A f₁ f₂).base ⊆ (W : Set _)) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ U : (Spec (.of A)).Opens,
      Set.range (centerToBase A f₁ f₂).base ⊆ (U : Set _) ∧
        modificationToBase A f₁ f₂ ⁻¹ᵁ U ≤ W := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have := isProper_modificationToBase A f₁ f₂
  exact exists_opens_preimage_le_of_universallyClosed (modificationToBase A f₁ f₂) W _
    fun x' hx' => hW <| by
      rwa [range_eq_preimage_range_of_isPullback (twoGenerator_isPullback A f₁ f₂)]

/-- Let `G` be a finite locally free module on the modification whose pullback to the exceptional
line is free of rank `r`. Then there are an open neighbourhood `U` of the centre in the base and a
morphism `α : 𝒪^{⊕r} ⟶ G` which becomes an isomorphism after pullback to the exceptional line and
after restriction to the preimage of `U`. -/
theorem exists_opens_center_isIso_restrict_hom_free [IsNoetherianRing A] (r : ℕ)
    {G : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Modules}
    (hG : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    (e : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).obj G ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r))) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ (U : (Spec (.of A)).Opens) (α : (_root_.SheafOfModules.free
        (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
        (ULift.{u} (Fin r))) ⟶ G),
      Set.range (centerToBase A f₁ f₂).base ⊆ (U : Set _) ∧
        IsIso ((Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).map α) ∧
          IsIso ((Scheme.Modules.restrictFunctor
            (modificationToBase A f₁ f₂ ⁻¹ᵁ U).ι).map α) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  obtain ⟨α, hαi, -, W, hWE, hαW⟩ := exists_hom_free_isIso_near_exceptional A f₁ f₂ r hG e
  obtain ⟨U, hUZ, hUW⟩ := exists_opens_center_preimage_le A f₁ f₂ W hWE
  exact ⟨U, α, hUZ, hαi, isIso_restrictFunctor_map_of_le hUW α hαW⟩

/-! ### The exceptional line and the complement of the centre -/

/-- The image of the exceptional line in the modification is the preimage of the support of the
centre. -/
theorem range_exceptionalToModification_eq_preimage_support :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    Set.range (exceptionalToModification A f₁ f₂).base =
      modificationToBase A f₁ f₂ ⁻¹'
        ((centerIdealSheaf A f₁ f₂).support : Set (Spec (.of A))) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hrange : Set.range (exceptionalToModification A f₁ f₂).base =
      Set.range
        ((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).subschemeι.base := by
    rw [← exceptionalIsoComapSubscheme_hom_comp_subschemeι A f₁ f₂]
    have hfun : ((exceptionalIsoComapSubscheme A f₁ f₂).hom ≫
          ((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).subschemeι).base =
        ((centerIdealSheaf A f₁ f₂).comap (modificationToBase A f₁ f₂)).subschemeι.base ∘
          (exceptionalIsoComapSubscheme A f₁ f₂).hom.base :=
      funext fun y => Scheme.Hom.comp_apply _ _ y
    rw [hfun]
    exact (Scheme.homeoOfIso (exceptionalIsoComapSubscheme A f₁ f₂)).surjective.range_comp _
  rw [hrange, Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.support_comap]
  rfl

/-- The complement of the support of the centre, as an open of the base. -/
def centerComplement : (Spec (.of A)).Opens :=
  ⟨(centerIdealSheaf A f₁ f₂).supportᶜ, (centerIdealSheaf A f₁ f₂).support.isClosed.isOpen_compl⟩

/-- The modification restricts to an isomorphism over the complement of the centre. -/
theorem isIso_modificationToBase_restrict_centerComplement :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsIso (modificationToBase A f₁ f₂ ∣_ centerComplement A f₁ f₂) :=
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  AlgebraicGeometry.isIso_restrict_compl_support (centerIdealSheaf A f₁ f₂)
    (modificationToBase A f₁ f₂) (isAlmostBlowUpSquare_modificationToBase A f₁ f₂)

/-- Let `G` be a finite locally free module on the modification whose pullback to the exceptional
line is free of rank `r`. Then there are an open `U` of the base which together with
`Stacks.AlmostBlowUp.centerComplement` covers the base, and a morphism `α : 𝒪^{⊕r} ⟶ G` which
becomes an isomorphism after pullback to the exceptional line and after restriction to the
preimage of `U`. -/
theorem exists_opens_cover_isIso_restrict_hom_free [IsNoetherianRing A] (r : ℕ)
    {G : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Modules}
    (hG : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    (e : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).obj G ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r))) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ (U : (Spec (.of A)).Opens) (α : (_root_.SheafOfModules.free
        (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
        (ULift.{u} (Fin r))) ⟶ G),
      U ⊔ centerComplement A f₁ f₂ = ⊤ ∧
        IsIso ((Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).map α) ∧
          IsIso ((Scheme.Modules.restrictFunctor
            (modificationToBase A f₁ f₂ ⁻¹ᵁ U).ι).map α) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have := isProper_modificationToBase A f₁ f₂
  obtain ⟨α, hαi, -, W, hWE, hαW⟩ := exists_hom_free_isIso_near_exceptional A f₁ f₂ r hG e
  obtain ⟨U, hUZ, hUW⟩ := exists_opens_preimage_le_of_universallyClosed
    (modificationToBase A f₁ f₂) W ((centerIdealSheaf A f₁ f₂).support : Set (Spec (.of A)))
    fun x' hx' => hWE (by rwa [range_exceptionalToModification_eq_preimage_support A f₁ f₂])
  refine ⟨U, α, ?_, hαi, isIso_restrictFunctor_map_of_le hUW α hαW⟩
  exact top_le_iff.mp fun x _ =>
    (em (x ∈ ((centerIdealSheaf A f₁ f₂).support : Set (Spec (.of A))))).imp (fun hx => hUZ hx) id

end Stacks.AlmostBlowUp

end
