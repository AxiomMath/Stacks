module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism

/-!
# Inverse image of a constructible sheaf on Mathlib's small étale site

Stacks Tag 095G says that the inverse image of a constructible abelian sheaf along a morphism of
schemes is constructible. It is available on the small étale site of Tag 021B,
`AlgebraicGeometry.isConstructibleFiniteSheaf_pullback`. This file transports it to Mathlib's
small étale site, along `AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`, for a
morphism `g : Y ⟶ X` whose source lies in every big étale site containing `X`, for instance a
quasi-compact monomorphism such as a closed immersion.

## Main results

* `Stacks.EtaleCohomology.IsConstructibleEtaleSheafIn.inverseImage`: Tag 095G for a fixed big
  étale site containing both schemes.
* `Stacks.EtaleCohomology.IsConstructibleSmallEtaleSheaf.inverseImage_of_size_le`: Tag 095G when
  the source is no larger than the target.
* `Stacks.EtaleCohomology.IsConstructibleSmallEtaleSheaf.inverseImage_of_mono`: Tag 095G along a
  quasi-compact monomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {X Y : Scheme.{u}}

/-- Tag 095G on Mathlib's small étale site, for a morphism of a big étale site. -/
theorem isConstructibleAbelianSheaf_toBoundedSite_inverseImage (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (F : Sheaf S.obj.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleAbelianSheaf B S ((toBoundedSiteAb B S.property).obj F)) :
    IsConstructibleAbelianSheaf B T ((toBoundedSiteAb B T.property).obj
      ((etaleAbelianInverseImage.{u, u + 1} (B.inclusion.map f)).obj F)) := by
  have e := SmallEtale.sheafEquivPullbackBaseChangeIso B f AddCommGrpCat.{u + 1}
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)) AddCommGrpCat.{u + 1}
      S.obj.smallEtaleTopology T.obj.smallEtaleTopology)
    (Functor.sheafAdjunctionContinuous (AlgebraicGeometry.smallEtaleBaseChange B f)
      AddCommGrpCat.{u + 1} (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property))
  have hG := isConstructibleFiniteSheaf_pullback B f ((toBoundedSiteAb B S.property).obj F) hF
  refine isConstructibleAbelianSheaf_congr B T ?_ hG
  exact (SmallEtale.sheafEquiv B T.obj T.property AddCommGrpCat.{u + 1}).unitIso.app _ ≪≫
    (toBoundedSiteAb B T.property).mapIso (e.app _).symm ≪≫
    (toBoundedSiteAb B T.property).mapIso
      ((etaleAbelianInverseImage.{u, u + 1} (B.inclusion.map f)).mapIso
        ((SmallEtale.sheafEquiv B S.obj S.property AddCommGrpCat.{u + 1}).counitIso.app F))

/-- **Stacks Tag 095G, for a fixed big étale site.** If `B` contains `X` and `Y`, the inverse image
along `g : Y ⟶ X` of an abelian sheaf constructible with respect to `B` is constructible with
respect to `B`. -/
theorem IsConstructibleEtaleSheafIn.inverseImage (B : BigEtaleSite.{u}) (hX : B.Contains X)
    (hY : B.Contains Y) (g : Y ⟶ X) {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hF : IsConstructibleEtaleSheafIn B hX F) :
    IsConstructibleEtaleSheafIn B hY ((etaleAbelianInverseImage.{u, u + 1} g).obj F) :=
  isConstructibleAbelianSheaf_toBoundedSite_inverseImage B
    (S := B.obj X hX) (T := B.obj Y hY) (ObjectProperty.homMk g) F hF

/-- **Stacks Tag 095G, when the source is no larger than the target.** The inverse image of a
constructible abelian sheaf along `g : Y ⟶ X` is constructible, provided the size of `Y` is at
most that of `X`. -/
theorem IsConstructibleSmallEtaleSheaf.inverseImage_of_size_le (g : Y ⟶ X) (hsize : Y.size ≤ X.size)
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsConstructibleSmallEtaleSheaf F) :
    IsConstructibleSmallEtaleSheaf ((etaleAbelianInverseImage.{u, u + 1} g).obj F) := by
  obtain ⟨B, hX, hB⟩ := hF
  exact ⟨B, hsize.trans_lt hX, IsConstructibleEtaleSheafIn.inverseImage B hX _ g hB⟩

/-- **Stacks Tag 095G along a quasi-compact monomorphism**, for instance a closed immersion or a
quasi-compact open immersion. -/
theorem IsConstructibleSmallEtaleSheaf.inverseImage_of_mono (g : Y ⟶ X) [Mono g] [QuasiCompact g]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsConstructibleSmallEtaleSheaf F) :
    IsConstructibleSmallEtaleSheaf ((etaleAbelianInverseImage.{u, u + 1} g).obj F) :=
  inverseImage_of_size_le g (Scheme.size_le_of_mono_quasiCompact g) hF

end Stacks.EtaleCohomology

end
