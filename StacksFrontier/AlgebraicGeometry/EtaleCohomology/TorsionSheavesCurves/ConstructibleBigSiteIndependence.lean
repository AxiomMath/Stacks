module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsClopen
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsite

/-!
# Constructibility does not depend on the big étale site

Constructibility of an abelian sheaf on Mathlib's small étale site of `X` is defined by reading the
sheaf on the size-bounded small étale site of a big étale site `B` containing `X` (Tag 021B). This
file shows that the choice of `B` does not matter, and deduces that constructibility on every big
étale site is inherited by inverse images.

## Main results

* `Stacks.EtaleCohomology.isFiniteLocallyConstant_sheafPullback_sheafEquiv_iff`: for a morphism
  `p : T ⟶ X` of a big étale site, the inverse image along `p` of a sheaf on `X` is finite locally
  constant on the site of Tag 021B exactly when it is so on Mathlib's site.
* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_of_contains`: constructibility read on
  one big étale site containing `X` implies it on any other.
* `Stacks.EtaleCohomology.IsConstructibleOnEveryBigSite.of_contains`: hence constructibility on
  one big étale site is constructibility on every big étale site.
* `Stacks.EtaleCohomology.IsConstructibleOnEveryBigSite.etaleAbelianInverseImage`: Tag 095G for
  constructibility on every big étale site.

## Implementation notes

A stratum of a constructible stratification is immersed in `X`, so it is a monomorphism into `X`
and lies below the cutoff of every big étale site containing `X`
(`AlgebraicGeometry.Scheme.size_lt_of_mono_of_isStrongPrelimit`); the stratification is therefore
one of the other site as well, and finite local constancy on a stratum is read on Mathlib's site of
the stratum, which does not involve `B`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- **Finite local constancy of an inverse image is the same on the two small étale sites.** For a
morphism `p : T ⟶ X` of a big étale site and an abelian sheaf `F` on Mathlib's small étale site of
`X`, the inverse image along `p` of `F` read on the site of Tag 021B is finite locally constant
exactly when `p^{-1} F` is finite locally constant on Mathlib's site of `T`. -/
theorem isFiniteLocallyConstant_sheafPullback_sheafEquiv_iff (B : BigEtaleSite.{u})
    {X T : B.Scheme} (p : T ⟶ X) (F : Sheaf X.obj.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B T.obj T.property)
        (((AlgebraicGeometry.smallEtaleBaseChange B p).sheafPullback AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B T.obj T.property)).obj
            ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).inverse.obj F)) ↔
      ConstantSheaf.IsFiniteLocallyConstant T.obj.smallEtaleTopology
        ((etaleAbelianInverseImage.{u, 0} (B.inclusion.map p)).obj F) := by
  let e := (SmallEtale.restrictionPullbackBaseChangeIso B AddCommGrpCat.{u + 1} p
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (B.inclusion.map p))
    (Functor.sheafAdjunctionContinuous _ _ _ _)).app F
  rw [SmallEtale.isFiniteLocallyConstant_abelian_iff_toEtaleSite B T.obj T.property]
  exact ⟨fun h ↦ ConstantSheaf.isFiniteLocallyConstant_congr _ e (hF := h),
    fun h ↦ ConstantSheaf.isFiniteLocallyConstant_congr _ e.symm (hF := h)⟩

/-- **Constructibility does not depend on the big étale site.** An abelian sheaf on Mathlib's
small étale site of `X` which is constructible when read on one big étale site containing `X` is
constructible when read on any other. -/
theorem isConstructibleEtaleAbelianSheaf_of_contains {B B' : BigEtaleSite.{u}} {X : Scheme.{u}}
    (hX : B.Contains X) (hX' : B'.Contains X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX F) :
    IsConstructibleEtaleAbelianSheaf.{u, 0} B' X hX' F := by
  intro U
  obtain ⟨s, hs⟩ := h U
  have hmono : ∀ i, Mono (B.inclusion.map (s.inclusion i)) := fun i ↦ by
    have := s.isImmersion i
    infer_instance
  let piece : Fin s.n → B'.Scheme := fun i ↦ ⟨(s.piece i).obj,
    have := hmono i
    Scheme.size_lt_of_mono_of_isStrongPrelimit B'.cutoff_isStrongPrelimit
      (B.inclusion.map (s.inclusion i)) hX'⟩
  let s' : ConstructibleStratification B' (B'.obj X hX') U.1 :=
    { n := s.n
      piece := piece
      inclusion := fun i ↦ ObjectProperty.homMk (B.inclusion.map (s.inclusion i))
      isImmersion := s.isImmersion
      contained := s.contained
      constructible := s.constructible
      pairwise_disjoint := s.pairwise_disjoint
      covers := s.covers }
  refine ⟨s', fun i ↦ ?_⟩
  exact (isFiniteLocallyConstant_sheafPullback_sheafEquiv_iff B' (s'.inclusion i) F).2
    ((isFiniteLocallyConstant_sheafPullback_sheafEquiv_iff B (s.inclusion i) F).1 (hs i))

/-- **Constructibility on one big étale site is constructibility on every big étale site.** -/
theorem IsConstructibleOnEveryBigSite.of_contains {B : BigEtaleSite.{u}} {X : Scheme.{u}}
    (hX : B.Contains X) {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (h : IsConstructibleEtaleAbelianSheaf.{u, 0} B X hX F) : IsConstructibleOnEveryBigSite F :=
  fun _ hX' _ _ ↦ isConstructibleEtaleAbelianSheaf_of_contains hX hX' F h

/-- **Tag 095G read through `AlgebraicGeometry.SmallEtale.sheafEquiv`.** For a morphism
`f : X ⟶ Y` of a big étale site, the inverse image on Mathlib's sites of a sheaf on `Y` which is
constructible on the site of Tag 021B is constructible there. -/
theorem isConstructibleFiniteSheaf_etaleAbelianInverseImage (B : BigEtaleSite.{u})
    {X Y : B.Scheme} (f : X ⟶ Y) (F : Sheaf Y.obj.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleFiniteSheaf B Y
      ((SmallEtale.sheafEquiv B Y.obj Y.property AddCommGrpCat.{u + 1}).inverse.obj F)) :
    IsConstructibleFiniteSheaf B X
      ((SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).inverse.obj
        ((etaleAbelianInverseImage.{u, 0} (B.inclusion.map f)).obj F)) := by
  have h := isConstructibleFiniteSheaf_pullback B f _ hF
  let e := (SmallEtale.restrictionPullbackBaseChangeIso B AddCommGrpCat.{u + 1} f
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (B.inclusion.map f))
    (Functor.sheafAdjunctionContinuous _ _ _ _)).app F
  intro U
  obtain ⟨s, hs⟩ := h U
  exact ⟨s, fun i ↦ ConstantSheaf.isFiniteLocallyConstant_congr _
    (((AlgebraicGeometry.smallEtaleBaseChange B (s.inclusion i)).sheafPullback
      AddCommGrpCat.{u + 1} (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).mapIso e) (hF := hs i)⟩

/-- **Tag 095G, for constructibility on every big étale site.** The inverse image of a sheaf
constructible on every big étale site along any morphism of schemes is constructible on every big
étale site. -/
theorem IsConstructibleOnEveryBigSite.etaleAbelianInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (hF : IsConstructibleOnEveryBigSite F) :
    IsConstructibleOnEveryBigSite ((etaleAbelianInverseImage.{u, 0} f).obj F) := by
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small ({X, Y} : Set Scheme.{u})
  have hX : B.Contains X := hB X (by simp)
  have hY : B.Contains Y := hB Y (by simp)
  exact IsConstructibleOnEveryBigSite.of_contains hX
    (isConstructibleFiniteSheaf_etaleAbelianInverseImage B
      (ObjectProperty.homMk f : B.obj X hX ⟶ B.obj Y hY) F (hF B hY))

end Stacks.EtaleCohomology
