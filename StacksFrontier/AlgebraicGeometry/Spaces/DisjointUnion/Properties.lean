module

public import StacksFrontier.AlgebraicGeometry.Spaces.DisjointUnion.Covering
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsRestrict
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback

/-!
# Perfectness on a disjoint union of algebraic spaces is checked on the summands

Let `Z` be the disjoint union of a family `X i` of algebraic spaces over `S`, with injections
`j i : X i ⟶ Z`. The injections form an étale covering of `Z`, so an object `K` of `D(𝒪_Z)` is
perfect, pseudo-coherent, or `Y`-perfect for a flat morphism `Z ⟶ Y` locally of finite
presentation, if and only if each restriction `L(j i)^* K` is.

## Main results

* `AlgebraicGeometry.Space.isPerfect_iff_forall_smallEtaleDerivedModulePullback`
* `AlgebraicGeometry.Space.isPseudoCoherent_iff_forall_smallEtaleDerivedModulePullback`
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_iff_forall_smallEtaleDerivedModulePullback`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] modules_abelian Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.Space.sheafTensor_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.sheafTensor_obj_additive_inverseImageRingedSite_over
  AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_inverseImageRingedSite_over
  Stacks.hasSheafCompose_forget₂_commRingCat RingedSite.sliceHasSheafify
  RingedSite.sliceWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {ι : Type u} {X : ι → AlgebraicSpaces B S hS} {Z : AlgebraicSpaces B S hS}
  {j : ∀ i, X i ⟶ Z}
  (hc : IsColimit (Cofan.mk ((algebraicSpacesToSheaf B S hS).obj Z)
    fun i => (algebraicSpacesToSheaf B S hS).map (j i)))

include hc in
/-- **Perfectness on a disjoint union is checked on the summands.** -/
theorem isPerfect_iff_forall_smallEtaleDerivedModulePullback
    (K : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :
    (smallEtaleRingedSite B S hS Z.1 Z.2).IsPerfect K ↔
      ∀ i : ι, (smallEtaleRingedSite B S hS (X i).1 (X i).2).IsPerfect
        ((smallEtaleDerivedModulePullback B S hS (j i)).obj K) :=
  ⟨fun h i => isPerfect_smallEtaleDerivedModulePullback (j i) K h, fun h =>
    isPerfect_of_forall_isPerfect_etaleRestrict B S hS X j (isEtale_cofanInj_of_isColimit hc)
      (exists_pointsMap_cofanInj_eq_of_isColimit hc) K fun i =>
        isPerfect_of_iso B S hS (h i) ((smallEtaleDerivedModulePullbackIsoEtale B S hS (j i)
          (isEtale_cofanInj_of_isColimit hc i)).app K)⟩

include hc in
/-- **Pseudo-coherence on a disjoint union is checked on the summands.** -/
theorem isPseudoCoherent_iff_forall_smallEtaleDerivedModulePullback
    (K : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :
    (smallEtaleRingedSite B S hS Z.1 Z.2).IsPseudoCoherent K ↔
      ∀ i : ι, (smallEtaleRingedSite B S hS (X i).1 (X i).2).IsPseudoCoherent
        ((smallEtaleDerivedModulePullback B S hS (j i)).obj K) :=
  ⟨fun h i => isPseudoCoherent_smallEtaleDerivedModulePullback (j i) K h, fun h =>
    (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ K).2 fun m =>
      isPseudoCoherentFrom_of_forall_etale X j (isEtale_cofanInj_of_isColimit hc)
        (exists_pointsMap_cofanInj_eq_of_isColimit hc) K m fun i =>
          (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom
            (smallEtaleRingedSite B S hS (X i).1 (X i).2) _).1 (h i) m⟩

include hc in
/-- **Relative perfectness on a disjoint union is checked on the summands.** Let `f : Z ⟶ Y` be
flat and locally of finite presentation, and for each `i` let `f i : X i ⟶ Y i` be flat and
locally of finite presentation with `j i ≫ f = f i ≫ b i` for an étale `b i : Y i ⟶ Y` (for
instance `Y = ⨆ i, Y i` and `X i = Z ×_Y Y i`). Then `K ∈ D(𝒪_Z)` is `Y`-perfect if and only if
each `L(j i)^* K` is `Y i`-perfect. -/
theorem isPerfectRelativeToCanonical_iff_forall_smallEtaleDerivedModulePullback
    {Y : AlgebraicSpaces B S hS} (f : Z ⟶ Y) (hfl : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) {Yi : ι → AlgebraicSpaces B S hS}
    (fi : ∀ i, X i ⟶ Yi i) (bi : ∀ i, Yi i ⟶ Y) (hfli : ∀ i, IsFlat B S hS (fi i).hom)
    (hlfpi : ∀ i, IsLocallyOfFinitePresentation B S hS (fi i).hom)
    (hb : ∀ i, IsEtale B S hS (bi i).hom) (w : ∀ i, j i ≫ f = fi i ≫ bi i)
    (K : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :
    IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp K ↔
      ∀ i : ι, IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS (fi i) (hfli i) (hlfpi i)
        ((smallEtaleDerivedModulePullback B S hS (j i)).obj K) :=
  ⟨fun h i => isPerfectRelativeToCanonical_smallEtaleDerivedModulePullback_of_isEtale (j i)
      (fi i) f (bi i) hfl hlfp (hfli i) (hlfpi i) (isEtale_cofanInj_of_isColimit hc i) (hb i) (w i)
      K h,
    fun h => isPerfectRelativeToCanonical_of_forall_isEtale f hfl hlfp j fi bi hfli hlfpi
      (isEtale_cofanInj_of_isColimit hc) (exists_pointsMap_cofanInj_eq_of_isColimit hc) hb w K h⟩

end AlgebraicGeometry.Space

end
