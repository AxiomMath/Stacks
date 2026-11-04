module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.CoefficientHypotheses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StalkLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StalkLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StratificationSurgery
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointDomination
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Coefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Morphisms
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.PointFiber

/-!
# Stacks 09YS: constructibility of the loci of a map of constructible sheaves

This module carries the declarations that extend
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StalkLocus`,
which is the base text, unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe v w u

namespace AlgebraicGeometry

section WholeTag

universe r w₀

/- The module coefficients of part (3) need the localizations of a small étale site to admit
weak sheafification and the direct image between small étale sites to be a right adjoint, for the
predicate `IsConstructibleModuleSheaf` to be stated at all. Both are theorems at every coefficient
universe containing the site, and are made instances for this section only. For abelian groups
the two corresponding instances are found by instance search. -/
attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat

/-- **Stacks 09YS.** Let `X` be a quasi-compact quasi-separated scheme.

1. For a map `φ : F ⟶ G` of constructible sheaves of sets on the small étale site of `X`, each of
   the three sets of points of `X` at which the induced map of geometric stalks is surjective, is
   injective, or is isomorphic to a prescribed map of sets `m₀`, is constructible.
2. The support of a constructible abelian sheaf on the small étale site of `X` is constructible.
3. For `Λ` a Noetherian ring, the support of a constructible sheaf of `Λ`-modules on the small
   étale site of `X` is constructible.

Sheaves of sets have values in the universe `u + 1` of the site; abelian sheaves, resp. sheaves of
`Λ`-modules for `Λ : Type r`, have values in any universe containing that of the site, resp. that
of the site and of `Λ`. The statement has no hypothesis beyond the source's: every coefficient
condition the general parts `isConstructible_supportSheaf` and
`isConstructible_support_moduleSheaf` assume is proved at these universes inside the proof.

Part (1) is `isConstructible_setOf_surjective_etaleStalk_map`,
`isConstructible_setOf_injective_etaleStalk_map` and `isConstructible_setOf_etaleStalk_map_iso`,
part (2) is `isConstructible_supportSheaf` and part (3) is
`isConstructible_support_moduleSheaf`. -/
@[stacks 09YS "parts (1), (2) and (3), as the conjunction of the three constructibility claims"]
public theorem isConstructible_etaleStalk_map_loci_and_supports (B : BigEtaleSite.{u})
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] :
    (∀ (F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) (φ : F ⟶ G),
        IsConstructibleSetSheaf B X F → IsConstructibleSetSheaf B X G →
        IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
            Function.Surjective
              ((etaleStalkPresheafFunctor B X.obj X.property t (Type (u + 1))).map φ.hom)} ∧
          IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
            Function.Injective
              ((etaleStalkPresheafFunctor B X.obj X.property t (Type (u + 1))).map φ.hom)} ∧
          ∀ (A₀ : Type v) (C₀ : Type w₀) (m₀ : A₀ → C₀),
            IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
              ∃ (b : (etaleStalkPresheafFunctor B X.obj X.property t
                  (Type (u + 1))).obj F.obj ≃ A₀)
                (d : (etaleStalkPresheafFunctor B X.obj X.property t
                  (Type (u + 1))).obj G.obj ≃ C₀),
                ∀ z, d ((etaleStalkPresheafFunctor B X.obj X.property t
                  (Type (u + 1))).map φ.hom z) = m₀ (b z)}) ∧
      (∀ F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) w},
          IsConstructibleAbelianSheaf B X F →
            IsConstructible (supportSheaf B X.obj X.property F)) ∧
      ∀ (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
        (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r w} Λ)),
        IsConstructibleModuleSheaf B X Λ F →
          IsConstructible {x : X.obj | ∃ t : GeometricPoint X.obj, t.LiesOver x ∧
            ¬ IsZero (etaleStalk B X.obj X.property t F.obj)} := by
  refine ⟨fun F G φ hF hG => ⟨isConstructible_setOf_surjective_etaleStalk_map B X φ hF hG,
    isConstructible_setOf_injective_etaleStalk_map B X φ hF hG,
    fun A₀ C₀ m₀ => isConstructible_setOf_etaleStalk_map_iso B m₀ X φ hF hG⟩, ?_, ?_⟩
  · intro F hF
    let : ∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
        ((SmallEtale.topology B Z.obj Z.property).over V).WEqualsLocallyBijective
          AddCommGrpCat.{max (u + 1) w} := fun Z V =>
      wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall.{max (u + 1) w, u + 1, u} _
    exact isConstructible_supportSheaf.{max (u + 1) w, u} B X F hF
  · intro Λ _ _ F hF
    let : ∀ (Z : B.Scheme) (V : SmallEtale B Z.obj Z.property),
        ((SmallEtale.topology B Z.obj Z.property).over V).WEqualsLocallyBijective
          (ModuleCat.{max (u + 1) r w} Λ) := fun Z V =>
      Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, max r w, r} _ Λ
    let : PreservesColimits (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat) :=
      ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) r w, r,
        max (u + 1) r w, max (u + 1) r w} Λ
    let : PreservesFilteredColimitsOfSize.{max (u + 1) r w, max (u + 1) r w}
        (forget (ModuleCat.{max (u + 1) r w} Λ)) :=
      comp_preservesFilteredColimits
        (forget₂ (ModuleCat.{max (u + 1) r w} Λ) AddCommGrpCat) (forget AddCommGrpCat)
    exact isConstructible_support_moduleSheaf.{max (u + 1) r w, u, r} B X Λ F hF

end WholeTag

end AlgebraicGeometry

end
