module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.EtaleToposFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.AbelianSheaves
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedOfExactFunctor
public import StacksFrontier.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianPushforwardExact

/-!
# Inverse image to the big étale topos and derived direct image along a finite morphism

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `f : Y ⟶ X` a finite
morphism of its objects. Stacks 0DGD, part (3), says that
`π_X⁻¹ R f_{small,*} K = R f_{big,*} π_Y⁻¹ K` for every `K` in the unbounded derived category
of abelian sheaves on the spaces-étale site of `Y`.

## Main results

* `smallEtaleMorphism_pushforward_preservesEpimorphisms_of_isFinite`: for `f` finite, the
  small direct image of sheaves of sets preserves epimorphisms (Stacks 0A4K).
* `smallEtalePushforward_preservesFiniteColimits_of_isFinite` and
  `bigEtalePushforward_preservesFiniteColimits_of_isFinite`: both direct images of abelian
  sheaves are exact for `f` finite.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleAbelianPushforwardIso`: for `f` proper,
  `π_X⁻¹ ∘ f_{small,*} ≅ f_{big,*} ∘ π_Y⁻¹` on abelian sheaves (Stacks 0DGD, part (1)), granted
  Stacks 0A3U.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmallEtaleDerivedPushforwardIsoOfIsFinite`: for `f`
  finite, `π_X⁻¹ R f_{small,*} ≅ R f_{big,*} π_Y⁻¹` on unbounded derived categories (Stacks
  0DGD, part (3)), granted Stacks 0A3U.

## References

* [Stacks Project, Tag 0DGD](https://stacks.math.columbia.edu/tag/0DGD)
* [Stacks Project, Tag 0A4K](https://stacks.math.columbia.edu/tag/0A4K)
* [Stacks Project, Tag 0DGA](https://stacks.math.columbia.edu/tag/0DGA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard

/-! ### Exactness of the small direct image along a finite morphism -/

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `PreservesEpimorphisms` through the topos comparison is expensive
/-- **Stacks 0A4K, sheaves of sets, on the spaces-étale sites.** For a finite morphism
`f : Y ⟶ X` the direct image of sheaves of sets on the spaces-étale sites preserves
epimorphisms. -/
theorem smallEtaleMorphism_pushforward_preservesEpimorphisms_of_isFinite {X Y : T.Spaces}
    (f : Y ⟶ X)
    (hf : Space.IsFinite T.fppfSite S T.fppf_mem f.hom) :
    (smallEtaleMorphism T f).pushforward.PreservesEpimorphisms := by
  have := Space.smallEtalePushforward_preservesEpimorphisms_of_isFinite T.fppfSite S
    T.fppf_mem f hf
  have : ((smallEtaleMorphism T f).pushforward ⋙
      (Space.smallEtaleToposEquiv T.fppfSite S T.fppf_mem X).functor).PreservesEpimorphisms :=
    ⟨fun {_ _} φ _ => by
      have e := NatIso.naturality_1
        (Space.smallToposMorphism_comparison T.fppfSite S T.fppf_mem f) φ
      change Epi ((Functor.sheafPushforwardContinuous
        (Space.spacesBaseChange T.fppfSite S T.fppf_mem f).functor (Type (u + 1))
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) ⋙
        (Space.comparisonFunctor T.fppfSite S T.fppf_mem X).sheafPushforwardContinuous
          (Type (u + 1)) (Space.SmallEtale.topology T.fppfSite S T.fppf_mem X.obj)
          (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)).map φ)
      rw [← e]
      exact epi_comp' (IsIso.epi_of_iso _) (epi_comp' (Functor.map_epi _ _) (IsIso.epi_of_iso _))⟩
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects _
    (Space.smallEtaleToposEquiv T.fppfSite S T.fppf_mem X).functor

/-- **Stacks 0A4K, abelian sheaves, on the spaces-étale sites: surjectivity.** For a finite
morphism the direct image of abelian sheaves on the spaces-étale sites preserves
epimorphisms. -/
theorem abelianSmallEtalePushforward_preservesEpimorphisms_of_isFinite {X Y : T.Spaces}
    (f : Y ⟶ X)
    (hf : Space.IsFinite T.fppfSite S T.fppf_mem f.hom) :
    (smallEtalePushforward T f).PreservesEpimorphisms where
  preserves {F G} φ _ := by
    have h₁ := Stacks.Topos.AbelianPushforward.epi_sheafCompose_forget_map
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) φ
    have h₂ := (smallEtaleMorphism_pushforward_preservesEpimorphisms_of_isFinite T f hf).preserves
      ((sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        (forget Ab.{u + 1})).map φ)
    have : (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        (forget Ab.{u + 1})).ReflectsEpimorphisms :=
      Functor.reflectsEpimorphisms_of_faithful _
    exact (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      (forget Ab.{u + 1})).epi_of_epi_map h₂

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the homology-preservation instances of this direct image is expensive
/-- **Stacks 0A4K, abelian sheaves, on the spaces-étale sites: exactness.** For a finite morphism
the direct image of abelian sheaves on the spaces-étale sites preserves finite colimits. -/
theorem smallEtalePushforward_preservesFiniteColimits_of_isFinite {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsFinite T.fppfSite S T.fppf_mem f.hom) :
    PreservesFiniteColimits (smallEtalePushforward T f) := by
  have := abelianSmallEtalePushforward_preservesEpimorphisms_of_isFinite T f hf
  have := Functor.preservesHomology_of_preservesEpis_and_kernels (smallEtalePushforward T f)
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-! ### Exactness of the big direct image along a finite morphism -/

/-- **Stacks 0DF8 for abelian sheaves.** For a cartesian square `Y' = Y ×_X X'`, restricting the
big direct image along `f`, written as restriction along `Over.pullback f`, to the spaces-étale
site of `X'` is restricting to the spaces-étale site of `Y'` and taking the small direct image
along `f'`. -/
def bigEtaleAbelianRestrictionBaseChangeIso {X Y X' Y' : T.Spaces} (f : Y ⟶ X)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (h : IsPullback g' f' f g) :
    (Over.pullback f).sheafPushforwardContinuous Ab.{u + 1} (T.bigEtaleTopology X)
        (T.bigEtaleTopology Y) ⋙ smallEtaleRestriction T g ≅
      smallEtaleRestriction T g' ⋙ smallEtalePushforward T f' :=
  letI := Functor.isContinuous_comp (inclusionFunctor T g) (Over.pullback f)
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
    (T.bigEtaleTopology X) (T.bigEtaleTopology Y)
  letI := (Space.spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f').isContinuous
  letI := Functor.isContinuous_comp
    (Space.spacesBaseChange T.fppfSite S T.fppf_mem f').functor (inclusionFunctor T g')
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y')
    (T.bigEtaleTopology Y)
  Functor.sheafPushforwardContinuousIso (smallEtaleCartesianIndexIso T g' f' f g h) Ab.{u + 1}
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X') (T.bigEtaleTopology Y)

/-- An abelian sheaf on the big étale site of `X` whose restriction to the spaces-étale site of
every object `g : X' ⟶ X` is zero is zero. -/
theorem isZero_of_isZero_smallEtaleRestriction {X : T.Spaces}
    (C : Sheaf (T.bigEtaleTopology X) Ab.{u + 1})
    (hC : ∀ V : Over X, IsZero ((smallEtaleRestriction T V.hom).obj C)) : IsZero C := by
  have hP : IsZero C.obj := Functor.isZero _ fun V => by
    have h := ((sheafToPresheaf _ _).map_isZero (hC V.unop)).obj
      (op (Space.SpacesEtale.final T.fppfSite S T.fppf_mem V.unop.left))
    let e : (Over.map V.unop.hom).obj ((Space.SpacesEtale.inclusion T.fppfSite S T.fppf_mem
        V.unop.left).obj (Space.SpacesEtale.final T.fppfSite S T.fppf_mem V.unop.left)) ≅
        V.unop := Over.isoMk (Iso.refl _) (by simp [Space.SpacesEtale.final])
    exact h.of_iso (C.obj.mapIso e.op).symm
  rw [IsZero.iff_id_eq_zero]
  exact (sheafToPresheaf _ _).map_injective (hP.eq_of_src _ _)

set_option maxHeartbeats 800000 in
-- restriction of abelian sheaves along `Over.pullback f`: heavy elaboration and instance search
set_option synthInstance.maxHeartbeats 400000 in
/-- **The big direct image along a finite morphism is right exact: surjectivity.** For `f`
finite, restriction of abelian sheaves along `Over.pullback f` — the big étale direct image —
preserves epimorphisms. -/
theorem bigEtaleRestrictionPushforward_preservesEpimorphisms_of_isFinite {X Y : T.Spaces}
    (f : Y ⟶ X)
    (hf : Space.IsFinite T.fppfSite S T.fppf_mem f.hom) :
    ((Over.pullback f).sheafPushforwardContinuous Ab.{u + 1} (T.bigEtaleTopology X)
      (T.bigEtaleTopology Y)).PreservesEpimorphisms where
  preserves {M N} φ _ := by
    let P := (Over.pullback f).sheafPushforwardContinuous Ab.{u + 1} (T.bigEtaleTopology X)
      (T.bigEtaleTopology Y)
    apply Preadditive.epi_of_isZero_cokernel
    refine isZero_of_isZero_smallEtaleRestriction T _ fun V => ?_
    have sq := IsPullback.of_hasPullback f V.hom
    have hf' : Space.IsFinite T.fppfSite S T.fppf_mem (pullback.snd f V.hom).hom :=
      Space.isFinite_of_isPullback T.fppfSite S T.fppf_mem
        (AlgebraicSpaces.isPullback_hom T.fppfSite S T.fppf_mem sq) hf
    have := abelianSmallEtalePushforward_preservesEpimorphisms_of_isFinite T
      (pullback.snd f V.hom) hf'
    let e := bigEtaleAbelianRestrictionBaseChangeIso T f V.hom (pullback.fst f V.hom)
      (pullback.snd f V.hom) sq
    have h₁ : Epi ((smallEtaleRestriction T (pullback.fst f V.hom)).map φ) :=
      Functor.map_epi _ φ
    have : Epi ((smallEtaleRestriction T V.hom).map (P.map φ)) := by
      change Epi ((P ⋙ smallEtaleRestriction T V.hom).map φ)
      rw [← NatIso.naturality_2 e φ]
      exact epi_comp' (IsIso.epi_of_iso _)
        (epi_comp' (Functor.map_epi (smallEtalePushforward T (pullback.snd f V.hom)) _)
          (IsIso.epi_of_iso _))
    exact (isZero_cokernel_of_epi ((smallEtaleRestriction T V.hom).map (P.map φ))).of_iso
      (PreservesCokernel.iso (smallEtaleRestriction T V.hom) (P.map φ))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `PreservesFiniteColimits` of the big direct image is expensive
/-- **The big direct image along a finite morphism is right exact.** For `f` finite the direct
image of abelian sheaves on the big étale sites preserves finite colimits. -/
theorem bigEtalePushforward_preservesFiniteColimits_of_isFinite {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsFinite T.fppfSite S T.fppf_mem f.hom) :
    PreservesFiniteColimits (bigEtalePushforward T f) := by
  let P := (Over.pullback f).sheafPushforwardContinuous Ab.{u + 1} (T.bigEtaleTopology X)
      (T.bigEtaleTopology Y)
  have := bigEtaleRestrictionPushforward_preservesEpimorphisms_of_isFinite T f hf
  have : P.Additive := ⟨rfl⟩
  have := Functor.preservesHomology_of_preservesEpis_and_kernels P
  have : PreservesFiniteColimits P := Functor.preservesFiniteColimits_of_preservesHomology _
  exact preservesFiniteColimits_of_natIso
    ((Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso Ab.{u + 1}).symm

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `PreservesFiniteLimits` via the cocontinuous adjunction is expensive
/-- The direct image of abelian sheaves on the big étale sites preserves finite limits. -/
instance bigEtalePushforward_preservesFiniteLimits {X Y : T.Spaces} (f : Y ⟶ X) :
    PreservesFiniteLimits (bigEtalePushforward T f) :=
  have := ((Over.map f).sheafAdjunctionCocontinuous Ab.{u + 1} (T.bigEtaleTopology Y)
    (T.bigEtaleTopology X)).rightAdjoint_preservesLimits
  inferInstance

/-! ### Part (1) for abelian sheaves, and part (3) -/

attribute [local instance] bigToSmallAbelianInverseImage_additive

/-- **Stacks 0DGD, part (1), for abelian sheaves, granted Stacks 0A3U.** For a proper morphism
`f : Y ⟶ X`, `π_X⁻¹ ∘ f_{small,*} ≅ f_{big,*} ∘ π_Y⁻¹` on abelian sheaves. -/
def bigToSmallEtaleAbelianPushforwardIso {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w)) :
    smallEtalePushforward T f ⋙
        CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T X) ≅
      CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T Y) ⋙
        bigEtalePushforward T f := by
  have _ : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have := isIso_bigToSmallEtaleBaseChange T f hf h0A3U
  let P := (Over.pullback f).sheafPushforwardContinuous Ab.{u + 1} (T.bigEtaleTopology X)
      (T.bigEtaleTopology Y)
  refine ProEtale.liftSheafNatIso (T.bigEtaleTopology X) _ _ ?_
  refine ?_ ≪≫ Functor.isoWhiskerRight (Functor.isoWhiskerLeft
    (CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T Y))
    ((Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso Ab.{u + 1}).symm) _
  exact Functor.isoWhiskerLeft
    (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (forget Ab.{u + 1}))
    (asIso (bigToSmallEtaleBaseChange T f))

/-- **Stacks 0DGD, part (3), granted Stacks 0A3U.** Let `f : Y ⟶ X` be a finite morphism
of algebraic spaces of the big étale site. Then for every `K` in the unbounded derived category
of abelian sheaves on the spaces-étale site of `Y`, `π_X⁻¹ R f_{small,*} K ≅ R f_{big,*} π_Y⁻¹ K`,
naturally in `K`. -/
def bigToSmallEtaleDerivedPushforwardIsoOfIsFinite {X Y : T.Spaces} (f : Y ⟶ X)
    (hf : Space.IsFinite T.fppfSite S T.fppf_mem f.hom)
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w)) :
    ((smallEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
              (ComplexShape.up ℤ)) ⋙
        (CategoryTheory.Sites.abelianInverseImage
          (bigToSmallEtaleMorphism T X)).mapDerivedCategory ≅
      (CategoryTheory.Sites.abelianInverseImage
          (bigToSmallEtaleMorphism T Y)).mapDerivedCategory ⋙
        ((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1})
              (ComplexShape.up ℤ)) := by
  have := smallEtalePushforward_preservesFiniteColimits_of_isFinite T f hf
  have := bigEtalePushforward_preservesFiniteColimits_of_isFinite T f hf
  let iS := Stacks.Homology.rightDerivedIsoMapDerivedCategory (smallEtalePushforward T f)
    _ (((smallEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
          (ComplexShape.up ℤ)))
  let iB := Stacks.Homology.rightDerivedIsoMapDerivedCategory (bigEtalePushforward T f)
    _ (((bigEtalePushforward T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf (T.bigEtaleTopology Y) Ab.{u + 1})
          (ComplexShape.up ℤ)))
  exact Functor.isoWhiskerRight iS _ ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _).symm ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (bigToSmallEtaleAbelianPushforwardIso T f
        ((Space.isFinite_iff_isAffineHom_and_isProper T.fppfSite S T.fppf_mem Y.2 X.2 f.hom).mp
          hf).2 h0A3U) ≪≫
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.isoWhiskerLeft _ iB.symm

end AlgebraicGeometry.BigEtaleSpaceSite

end
