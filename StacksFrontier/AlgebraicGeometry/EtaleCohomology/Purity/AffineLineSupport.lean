module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineOrigin
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GlobalSectionsBaseChangeCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenBaseChange

/-!
# Abelian sheaves on the affine line supported at the origin

Let `k` be a separably closed field. An abelian sheaf `G` on `(𝐀¹_k)_étale` whose restriction to
`𝐆_m = 𝐀¹ ∖ {0}` vanishes is the direct image `0_* M` of the sheaf `M = 0⁻¹ G` on the small étale
site of `Spec k` (Stacks 095L), and sheaves on `(Spec k)_étale` are their global sections. So such
a `G` is determined by the abelian group `Γ(𝐀¹, G) = Γ(Spec k, M)`: it vanishes when that group
does, and it is the skyscraper `0_* M` with `Γ(Spec k, M) = Γ(𝐀¹, G)`.

## Main results

* `Stacks.EtaleCohomology.Purity.isIso_unit_origin_of_isZero_restriction`: `G ≅ 0_* 0⁻¹ G`.
* `Stacks.EtaleCohomology.Purity.isZero_of_isZero_restriction_of_isZero_sections`: `G = 0` when
  moreover `Γ(𝐀¹, G) = 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.Purity

variable (k : Type u) [Field k]

/-- The inclusion of the origin `Spec k → 𝐀¹_k` is a closed immersion. -/
instance : IsClosedImmersion (origin k) := isClosedImmersion_origin k

/-- **A sheaf on `𝐀¹` vanishing on `𝐆_m` is the direct image of its restriction to the
origin.** -/
theorem isIso_unit_origin_of_isZero_restriction
    (G : Sheaf (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hU : IsZero ((etaleRestriction.{u, 0} (punctured k).ι).obj G)) :
    IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (origin k)).unit.app G) := by
  obtain ⟨h, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, 0} (origin k)
    (punctured k).ι (range_punctured_ι k) G
  have hz : IsZero ((extensionByZero.{u, 0} (punctured k).ι).obj
      ((etaleRestriction.{u, 0} (punctured k).ι).obj G)) :=
    Functor.map_isZero _ hU
  have : Mono ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (origin k)).unit.app G) :=
    hS.exact.mono_g (hz.eq_of_src _ _)
  have : Epi ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (origin k)).unit.app G) := hS.epi_g
  exact isIso_of_mono_of_epi _

variable [IsSepClosed k]

/-- **A sheaf on `𝐀¹` vanishing on `𝐆_m` and without global sections is zero.** -/
theorem isZero_of_isZero_restriction_of_isZero_sections
    (G : Sheaf (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hU : IsZero ((etaleRestriction.{u, 0} (punctured k).ι).obj G))
    (hΓ : IsZero ((Sheaf.Γ (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1}).obj G)) :
    IsZero G := by
  have := isIso_unit_origin_of_isZero_restriction k G hU
  let M := (etaleAbelianInverseImage.{u, 0} (origin k)).obj G
  have hΓM : IsZero ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) :=
    hΓ.of_iso (((etaleAbelianDirectImageGammaIso.{u, 0} (origin k)).app M).symm ≪≫
      (Sheaf.Γ _ _).mapIso (asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0}
        (origin k)).unit.app G)).symm)
  let : MorphismProperty.ContainsIdentities (@Etale.{u}) := ⟨fun _ => inferInstance⟩
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 (Spec (.of k)))) :=
    MorphismProperty.Over.mkIdTerminal _ _
  have hΓM' : IsZero (((sheafSections (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk (𝟙 (Spec (.of k)))))).obj M) :=
    hΓM.of_iso ((Sheaf.ΓNatIsoSheafSections _ _ hT).app M).symm
  have := isEquivalence_sheafSections_final_of_isSepClosed k AddCommGrpCat.{u + 1}
  have hM : IsZero M := IsZero.of_full_of_faithful_of_isZero _ M hΓM'
  exact (Functor.map_isZero (etaleAbelianDirectImage.{u, 0} (origin k)) hM).of_iso
    (asIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (origin k)).unit.app G))

end Stacks.EtaleCohomology.Purity

end
