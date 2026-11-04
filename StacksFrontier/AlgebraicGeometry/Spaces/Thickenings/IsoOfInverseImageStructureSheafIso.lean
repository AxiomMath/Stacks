module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTransferOfInverseImageIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposIsoLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAffineCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.MorphismFromStructureMap

/-!
# Isomorphisms of algebraic spaces from an isomorphism of inverse images of structure sheaves

Let `i₁ : X ⟶ X'₁` and `i₂ : X ⟶ X'₂` be morphisms of algebraic spaces over `Spec ℤ` whose
morphisms of small étale topoi have equivalences as direct images — the inclusions of the same
space `X` into two thickenings, by Stacks 05ZM — and let `d : i₁⁻¹𝒪_{X'₁} ≅ i₂⁻¹𝒪_{X'₂}` be an
isomorphism of sheaves of commutative rings on `X_étale` compatible with the two maps
`i_j^♯ : i_j⁻¹𝒪_{X'_j} ⟶ 𝒪_X`. Then there is an isomorphism `f : X'₁ ≅ X'₂` with `i₁ ≫ f = i₂`,
inducing the isomorphism of small étale ringed topoi determined by `d`.

The isomorphism of ringed topoi is
`AlgebraicGeometry.RingedToposHom.transferOfInverseImageIso`; Stacks 05YZ produces `f` from it,
and Stacks 04M6 identifies `i₁ ≫ f` with `i₂`, both inducing morphisms 2-isomorphic to
`(i₂, i₂^♯)`.

## Main results

* `AlgebraicGeometry.Space.exists_iso_comp_eq_of_inverseImageStructureSheafIso`
* `AlgebraicGeometry.Space.exists_iso_comp_eq_of_etaleRestrictionIso`: the same, with the two
  inverse images read on `X` through isomorphisms `X ≅ Z_j` onto closed subspaces `Z_j ⊂ X'_j`,
  which is how the extension of a deformation is presented.

## References

* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))))
  {X X'₁ X'₂ : AlgebraicSpaces B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ}
  (i₁ : X ⟶ X'₁) (i₂ : X ⟶ X'₂)
  [(smallEtaleRingedToposHom B _ hZ i₁).toToposHom.pushforward.IsEquivalence]
  [(smallEtaleRingedToposHom B _ hZ i₂).toToposHom.pushforward.IsEquivalence]
  (d : inverseImageStructureSheaf B _ hZ i₁ ≅ inverseImageStructureSheaf B _ hZ i₂)

/-- **An isomorphism of the inverse images of the structure sheaves of two thickenings of `X`
gives an isomorphism of the thickenings under `X`.** -/
theorem exists_iso_comp_eq_of_inverseImageStructureSheafIso
    (hd : d.hom ≫ structureSharpInverseImage B _ hZ i₂ = structureSharpInverseImage B _ hZ i₁) :
    ∃ f : X'₁ ≅ X'₂, i₁ ≫ f.hom = i₂ ∧
      InducesSmallEtaleRingedToposHom B _ hZ f.hom
        (RingedToposHom.transferOfInverseImageIso (X := smallEtaleRingedTopos B _ hZ X)
          (Y₁ := smallEtaleRingedTopos B _ hZ X'₁) (Y₂ := smallEtaleRingedTopos B _ hZ X'₂)
          (smallEtaleRingedToposHom B _ hZ i₁)
          (smallEtaleRingedToposHom B _ hZ i₂) d) := by
  have := RingedToposHom.isEquivalence_transferOfInverseImageIso_pushforward
    (X := smallEtaleRingedTopos B _ hZ X) (Y₁ := smallEtaleRingedTopos B _ hZ X'₁)
    (Y₂ := smallEtaleRingedTopos B _ hZ X'₂) _ _ d
  have := RingedToposHom.isIso_transferOfInverseImageIso_fSharp
    (X := smallEtaleRingedTopos B _ hZ X) (Y₁ := smallEtaleRingedTopos B _ hZ X'₁)
    (Y₂ := smallEtaleRingedTopos B _ hZ X'₂) _ _ d
  obtain ⟨⟨f, ⟨s⟩, -⟩, hiso⟩ := existsUnique_spaceHom_twoIso_of_smallEtaleRingedToposIso B hZ
    (RingedToposHom.transferOfInverseImageIso (X := smallEtaleRingedTopos B _ hZ X)
          (Y₁ := smallEtaleRingedTopos B _ hZ X'₁) (Y₂ := smallEtaleRingedTopos B _ hZ X'₂)
          (smallEtaleRingedToposHom B _ hZ i₁)
      (smallEtaleRingedToposHom B _ hZ i₂) d)
  have := hiso f ⟨s⟩
  refine ⟨asIso f, ?_, ⟨s.symm⟩⟩
  exact eq_of_smallEtaleRingedToposHom_twoIso B _ hZ (i₁ ≫ f) i₂
    (((smallEtaleRingedToposHomCompTwoIso B _ hZ i₁ f).symm.trans
      (RingedToposHom.TwoIso.whiskerLeft (A := smallEtaleRingedTopos B _ hZ X)
        (B := smallEtaleRingedTopos B _ hZ X'₁) (C := smallEtaleRingedTopos B _ hZ X'₂)
        (smallEtaleRingedToposHom B _ hZ i₁) s.symm)).trans
      (RingedToposHom.transferOfInverseImageIsoCompTwoIso (X := smallEtaleRingedTopos B _ hZ X)
          (Y₁ := smallEtaleRingedTopos B _ hZ X'₁) (Y₂ := smallEtaleRingedTopos B _ hZ X'₂)
          _ _ d hd))

section EtaleRestriction

/-- A composite `c₁ ≫ e ≫ c₂⁻¹` of isomorphisms over `O` is over `O`. -/
theorem trans_trans_symm_hom_comp_eq_of_comp_eq {C : Type*} [Category C] {A A' P P' O : C}
    (c₁ : A ≅ P) (c₂ : A' ≅ P') (e : P ≅ P') (s₁ : A ⟶ O) (s₂ : A' ⟶ O) (r₁ : P ⟶ O)
    (r₂ : P' ⟶ O) (h₁ : c₁.hom ≫ r₁ = s₁) (h₂ : c₂.hom ≫ r₂ = s₂) (he : e.hom ≫ r₂ = r₁) :
    (c₁ ≪≫ e ≪≫ c₂.symm).hom ≫ s₂ = s₁ := by
  subst h₁ h₂ he
  simp

variable {Z₁ Z₂ : AlgebraicSpaces B (Spec (CommRingCat.of (ULift.{u} ℤ))) hZ}

/-- `j⁻¹𝒪_{X'}` restricted to `X` along an isomorphism `θ : X ≅ Z`, for `j : Z ⟶ X'`. -/
abbrev etaleRestrictedInverseImageStructureSheaf (θ : X ≅ Z₁) (j : Z₁ ⟶ X'₁) :=
  (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B _ hZ X.1)
    (smallEtalePostcomp B _ hZ θ.hom (isEtale_hom_of_iso B _ hZ θ))).obj
    (inverseImageStructureSheaf B _ hZ j)

/-- The reduction of `etaleRestrictedInverseImageStructureSheaf θ j` onto `𝒪_X`: the restriction
of `j^♯`, read on `X` through `θ⁻¹𝒪_Z ≅ 𝒪_X`. -/
abbrev etaleRestrictedInverseImageReduction (θ : X ≅ Z₁) (j : Z₁ ⟶ X'₁) :
    etaleRestrictedInverseImageStructureSheaf B hZ θ j ⟶ (smallEtaleRingedTopos B _ hZ X).O :=
  (Deformation.AlgebraExtension.ringRes (SmallEtale.topology B _ hZ X.1)
      (smallEtalePostcomp B _ hZ θ.hom (isEtale_hom_of_iso B _ hZ θ))).map
      (structureSharpInverseImage B _ hZ j) ≫
    (etaleRestrictionStructureSheafIso B _ hZ θ.hom (isEtale_hom_of_iso B _ hZ θ)).hom

/-- `(θ ≫ j)⁻¹𝒪_{X'}` is the restriction along `θ` of `j⁻¹𝒪_{X'}`. -/
abbrev etaleRestrictedInverseImageStructureSheafIso (θ : X ≅ Z₁) (j : Z₁ ⟶ X'₁) :
    inverseImageStructureSheaf B _ hZ (θ.hom ≫ j) ≅
      etaleRestrictedInverseImageStructureSheaf B hZ θ j :=
  (etaleRestrictionRingComparison B _ hZ θ.hom (isEtale_hom_of_iso B _ hZ θ) j).α

variable (θ₁ : X ≅ Z₁) (θ₂ : X ≅ Z₂) (j₁ : Z₁ ⟶ X'₁) (j₂ : Z₂ ⟶ X'₂)
  [(smallEtaleRingedToposHom B _ hZ (θ₁.hom ≫ j₁)).toToposHom.pushforward.IsEquivalence]
  [(smallEtaleRingedToposHom B _ hZ (θ₂.hom ≫ j₂)).toToposHom.pushforward.IsEquivalence]
  (e : etaleRestrictedInverseImageStructureSheaf B hZ θ₁ j₁ ≅
    etaleRestrictedInverseImageStructureSheaf B hZ θ₂ j₂)

/-- **Two thickenings `Z_j ⊂ X'_j` of spaces isomorphic to `X`, whose structure sheaves read on
`X` are isomorphic over `𝒪_X`, are isomorphic under `X`.** -/
theorem exists_iso_comp_eq_of_etaleRestrictionIso
    (he : e.hom ≫ etaleRestrictedInverseImageReduction B hZ θ₂ j₂ =
      etaleRestrictedInverseImageReduction B hZ θ₁ j₁) :
    ∃ f : X'₁ ≅ X'₂, (θ₁.hom ≫ j₁) ≫ f.hom = θ₂.hom ≫ j₂ ∧
      InducesSmallEtaleRingedToposHom B _ hZ f.hom
        (RingedToposHom.transferOfInverseImageIso (X := smallEtaleRingedTopos B _ hZ X)
          (Y₁ := smallEtaleRingedTopos B _ hZ X'₁) (Y₂ := smallEtaleRingedTopos B _ hZ X'₂)
          (smallEtaleRingedToposHom B _ hZ (θ₁.hom ≫ j₁))
          (smallEtaleRingedToposHom B _ hZ (θ₂.hom ≫ j₂))
          (etaleRestrictedInverseImageStructureSheafIso B hZ θ₁ j₁ ≪≫ e ≪≫
            (etaleRestrictedInverseImageStructureSheafIso B hZ θ₂ j₂).symm)) :=
  exists_iso_comp_eq_of_inverseImageStructureSheafIso B hZ _ _ _
    (trans_trans_symm_hom_comp_eq_of_comp_eq _ _ e _ _ _ _
      (etaleRestrictionRingComparison_α_hom_comp_reduction B _ hZ θ₁.hom
        (isEtale_hom_of_iso B _ hZ θ₁) j₁)
      (etaleRestrictionRingComparison_α_hom_comp_reduction B _ hZ θ₂.hom
        (isEtale_hom_of_iso B _ hZ θ₂) j₂) he)

end EtaleRestriction

end AlgebraicGeometry.Space

end
