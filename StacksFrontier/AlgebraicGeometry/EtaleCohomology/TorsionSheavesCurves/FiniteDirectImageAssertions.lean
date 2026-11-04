module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteDirectImageRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteBaseChangeAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.Reduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.SiteIsomorphism

/-!
# Stacks Tag 0A5D: the eight assertions pass to a finite direct image

Let `π : X ⟶ Y` be a finite morphism of schemes over a field `k` and `G` an abelian sheaf on
`X_étale`. If the eight assertions of Tag 03SC hold for `G` over `X`, they hold for `π_* G` over
`Y`, provided the torsion and constructibility conditions on `π_* G` pass back to `G`.

The cohomology of `π_* G` is that of `G` through the edge map, which is bijective since `π` is
integral (`Stacks.EtaleCohomology.bijective_edgeMap`). This gives the vanishing and finiteness
assertions; `Y` affine (resp. proper) makes `X` affine (resp. proper), `π` being finite. The base
change assertions transfer across the edge maps by
`Stacks.EtaleCohomology.bijective_restriction_directImage_iff`, the base change comparison being an
isomorphism by Tag 0959
(`Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback_succUniverse`),
both for the scalar extension `X_{k'} ⟶ X` and for the inclusion of an open of `Y`.

## Main results

* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_directImage`: Tag 0A5D.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) (π : X ⟶ Y)
  [IsFinite π]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The base change of `π` to the scalar extensions is a pullback of `π`. -/
theorem isPullback_scalarExtensionMap' (k' : Type u) [Field k'] [Algebra k k'] :
    IsPullback (scalarExtensionMap fY π k') (scalarExtensionFst k k' (π ≫ fY))
      (scalarExtensionFst k k' fY) π :=
  (isPullback_scalarExtension k' π fY).flip

/-- Bijectivity of restriction to a scalar extension transfers across a finite direct image. -/
theorem bijective_scalarExtension_directImage_iff
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (k' : Type u) [Field k'] [Algebra k k']
    [HasExt.{u + 1} (Sheaf (scalarExtension k k' fY).smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1}
      (Sheaf (scalarExtension k k' (π ≫ fY)).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (q : ℕ) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' fY) ((etaleAbelianDirectImage.{u, u + 1} π).obj G) q) ↔
      Function.Bijective (etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (scalarExtensionFst k k' (π ≫ fY)) G q) := by
  have sq := (isPullback_scalarExtensionMap' fY π k').flip
  have : IsFinite (scalarExtensionMap fY π k') :=
    MorphismProperty.of_isPullback sq inferInstance
  have := isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback_succUniverse π
    (scalarExtensionFst k k' fY) (scalarExtensionFst k k' (π ≫ fY)) (scalarExtensionMap fY π k') sq
  exact bijective_restriction_directImage_iff π (scalarExtensionFst k k' fY)
    (scalarExtensionFst k k' (π ≫ fY)) (scalarExtensionMap fY π k') sq.w G q

/-- **Stacks Tag 0A5D.** For `π : X ⟶ Y` finite over `k`, the eight assertions of Tag 03SC for an
abelian sheaf `G` on `X_étale` give them for `π_* G` on `Y_étale`, provided constructibility and
the two torsion conditions on `π_* G` pass back to `G`. -/
theorem of_directImage (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : TorsionCurveAssertions (π ≫ fY) G)
    (hc : IsConstructibleSmallEtaleSheaf ((etaleAbelianDirectImage.{u, u + 1} π).obj G) →
      IsConstructibleSmallEtaleSheaf G)
    (hp : ∀ p : ℕ, Stacks.Torsion.IsPrimePowerTorsion Y.smallEtaleTopology p
        ((etaleAbelianDirectImage.{u, u + 1} π).obj G) →
      Stacks.Torsion.IsPrimePowerTorsion X.smallEtaleTopology p G)
    (ht : Stacks.Torsion.IsPrimeToCharacteristicTorsion Y.smallEtaleTopology (ringExpChar k)
        ((etaleAbelianDirectImage.{u, u + 1} π).obj G) →
      Stacks.Torsion.IsPrimeToCharacteristicTorsion X.smallEtaleTopology (ringExpChar k) G) :
    TorsionCurveAssertions fY ((etaleAbelianDirectImage.{u, u + 1} π).obj G) := by
  let e : ∀ q, Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, u + 1} π).obj G) q ≃
      Sheaf.H.{u + 1} G q := fun q => Equiv.ofBijective _ (bijective_edgeMap π q G)
  refine
    { vanishing := fun q hq => (e q).subsingleton_congr.mpr (h.vanishing q hq)
      vanishing_of_isAffine := fun hY q hq => by
        have : IsAffine X := isAffine_of_isAffineHom π
        exact (e q).subsingleton_congr.mpr (h.vanishing_of_isAffine this q hq)
      vanishing_of_isPrimePowerTorsion := fun p hp' hp0 hF q hq =>
        (e q).subsingleton_congr.mpr (h.vanishing_of_isPrimePowerTorsion p hp' hp0 (hp p hF) q hq)
      finite_of_isPrimeToCharacteristicTorsion := fun hcF htF q =>
        (Equiv.finite_iff (e q)).mpr
          (h.finite_of_isPrimeToCharacteristicTorsion (hc hcF) (ht htF) q)
      finite_of_isProper := fun hf hcF q =>
        (Equiv.finite_iff (e q)).mpr (h.finite_of_isProper inferInstance (hc hcF) q)
      bijective_of_isPrimeToCharacteristicTorsion := fun htF k' _ _ _ _ q => by
        let : HasExt.{u + 1}
            (Sheaf (scalarExtension k k' (π ≫ fY)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
          hasExt_of_enoughInjectives.{u + 1} _
        exact (bijective_scalarExtension_directImage_iff fY π G k' q).2
          (h.bijective_of_isPrimeToCharacteristicTorsion (ht htF) k' q)
      bijective_of_isProper := fun hf k' _ _ _ _ q => by
        let : HasExt.{u + 1}
            (Sheaf (scalarExtension k k' (π ≫ fY)).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
          hasExt_of_enoughInjectives.{u + 1} _
        exact (bijective_scalarExtension_directImage_iff fY π G k' q).2
          (h.bijective_of_isProper inferInstance k' q)
      surjective_restriction := fun U _ => by
        let : HasExt.{u + 1}
            (Sheaf ((π ⁻¹ᵁ U : X.Opens) : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{u + 1}) :=
          hasExt_of_enoughInjectives.{u + 1} _
        have sq := (isPullback_morphismRestrict π U).flip
        have : IsFinite (π ∣_ U) :=
          MorphismProperty.of_isPullback sq inferInstance
        have := isIso_etaleAbelianBaseChange_of_isFinite_of_isPullback_succUniverse π U.ι
          (π ⁻¹ᵁ U).ι (π ∣_ U) sq
        exact (surjective_restriction_directImage_iff π U.ι (π ⁻¹ᵁ U).ι (π ∣_ U) sq.w G 2).2
          (h.surjective_restriction (π ⁻¹ᵁ U)) }

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end
