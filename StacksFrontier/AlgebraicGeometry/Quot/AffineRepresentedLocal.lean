module

public import StacksFrontier.AlgebraicGeometry.Quot.AffineRepresentedOver
public import StacksFrontier.AlgebraicGeometry.Quot.AffineLocalRepresentability
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverFromAffineChartsAlgebraic

/-!
# Algebraic spaces affine over a base from bounded affine representations over affine schemes

A functor `R` on the test schemes over an algebraic space `Y` which is an fpqc sheaf, and whose
restriction to every affine test scheme `Z ⟶ Y` is represented by an affine scheme of size at most
`2 ^ 2 ^ max λ (size Z)` for one cardinal `λ` below the cutoff, is an algebraic space affine over
`Y`.

## Main results

* `AlgebraicGeometry.Space.isAffineAlgebraicSpaceOver_of_isAffineRepresentedOver`: an fpqc sheaf
  over `Y` represented over every affine test scheme by an affine scheme of uniformly bounded size
  is an algebraic space affine over `Y`.

## References

* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y : AlgebraicSpaces B S hS}

/-- An fpqc sheaf on the test schemes over `Y` represented over every affine test scheme `Z` by an
affine scheme of size at most `2 ^ 2 ^ max λ (size Z)`, with `λ` below the cutoff, is an algebraic
space affine over `Y`. -/
theorem isAffineAlgebraicSpaceOver_of_isAffineRepresentedOver
    (R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)) (hR : Presheaf.IsSheaf (fpqcTopology Y) R)
    {lam : Cardinal.{u}} (hlam : lam < B.cutoff)
    (hloc : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      IsAffineRepresentedOver Z.left
        ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max lam
          ((BigFppfOver.toScheme B S hS).obj Z.left).size)
        ((CostructuredArrow.map Z.hom).op ⋙ R)) :
    IsAffineAlgebraicSpaceOver Y R := by
  classical
  have hsmAff : ∀ Z : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj Z.left) →
      Small.{u} (R.obj (op Z)) := by
    intro Z hZ
    obtain ⟨W, w, -, -, ⟨ψ⟩⟩ := hloc Z hZ
    have e : R.obj (op Z) ≃ ULift.{u + 1}
        ((spacePointsOver ((schemeSpaceFunctor B S hS).map w)).obj
          (op (identityTest Z))) :=
      (R.mapIso (mapIdentityTestIso Z).op).toEquiv.symm.trans
        (ψ.app (op (identityTest Z))).toEquiv.symm
    exact small_map e
  have hsm : FunctorToTypes.Small.{u} R := fun X =>
    small_of_isSheaf_of_small_affine R hR hsmAff X.unop
  let R' := FunctorToTypes.shrink.{u} R
  let eR : R' ⋙ uliftFunctor.{u + 1, u} ≅ R :=
    NatIso.ofComponents (fun X => Equiv.toIso (Equiv.ulift.trans (equivShrink _).symm))
      (fun {X X'} f => by
        ext x
        exact (equivShrink (R.obj X')).symm_apply_apply _)
  have hR' : Presheaf.IsSheaf (fpqcTopology Y) R' := by
    rw [isSheaf_iff_isSheaf_of_type] at hR ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1 (Presieve.isSheaf_iso _ eR.symm hR)
  let H₀ := totalSpace R'
  let p₀ : H₀ ⟶ Y.1 := totalSpaceProj R'
  let e₀ : presheafPointsOver p₀ ≅ R' := presheafPointsOverTotalSpaceIso R'
  have hH₀ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) H₀ :=
    isSheaf_of_isSheaf_presheafPointsOver p₀ ((Presheaf.isSheaf_of_iso_iff e₀).2 hR')
  obtain ⟨U, a, hs, he⟩ := Y.2.exists_atlas
  have hμ : (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ max lam
      ((BigFppfOver.toScheme B S hS).obj U).size < B.cutoff :=
    B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit (max_lt hlam U.left.property))
  obtain ⟨hH₀alg, hπ⟩ := isAlgebraicSpace_and_presheaf_isAffineHom_of_atlas B S hS Y.2 hH₀ p₀ hs he
    hμ fun V u hu hV => by
      let Z : SchemesOver Y :=
        CostructuredArrow.mk (Y := V) (ObjectProperty.homMk (yoneda.map u ≫ a))
      obtain ⟨W, w, hW, hsW, ⟨ψ⟩⟩ := hloc Z hV
      let φ : spacePointsOver ((schemeSpaceFunctor B S hS).map w) ≅
          (CostructuredArrow.map Z.hom).op ⋙ presheafPointsOver p₀ :=
        isoOfIsoCompUliftFunctor (ψ ≪≫ Functor.isoWhiskerLeft _ eR.symm ≪≫
          (Functor.associator _ _ _).symm) ≪≫ Functor.isoWhiskerLeft _ e₀.symm
      exact ⟨W, pointsIsoToHom φ, w, isPullback_pointsIsoToHom φ, hW,
        hsW.trans <| power_le_power_left two_ne_zero <| power_le_power_left two_ne_zero <|
          max_le_max le_rfl <|
            Scheme.size_le_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map u)⟩
  exact ⟨⟨H₀, hH₀alg⟩, ObjectProperty.homMk p₀, isAffineHom_of_presheaf hπ,
    ⟨Functor.isoWhiskerRight (spacePointsOverIsoPresheafPointsOver
      (ObjectProperty.homMk p₀ : (⟨H₀, hH₀alg⟩ : AlgebraicSpaces B S hS) ⟶ Y) ≪≫ e₀) _ ≪≫ eR⟩⟩

end AlgebraicGeometry.Space

end
