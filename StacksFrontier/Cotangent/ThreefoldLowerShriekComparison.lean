module

public import StacksFrontier.Cotangent.ThreefoldThirdLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 08QW: `Lg_{i,!} ∘ g_i⁻¹ = id` and `Lπ_! ∘ g_i⁻¹ = Lπ_{i,!}` for `i = 1, 2, 3`

Let `A → B → C` be ring maps, let `gᵢ` be the three morphisms of topoi of Tag 08QT out of the
site `C_{C/B/A}` of polynomial towers, and let `π`, `πᵢ` be the projections of the four sites to
the point. This file deduces the second half of Tag 08QW from the first, and registers the tag.

## Main results

* `Stacks.ChaoticSite.enoughProjectives_sheaf_bot_large`: abelian sheaves for the chaotic topology
  on a category with objects in `Type (u + 1)` and morphisms in `Type u` have enough projectives.
* `Stacks.ChaoticSite.derivedLowerShriekProjectionCompIsoOfEqBot`: if `Lg_! ∘ g⁻¹ = id` along a
  functor of chaotic sites, then `Lπ_! ∘ g⁻¹ = Lπ'_!` for the projections to the point.
* `CommAlgCat.derivedLowerShriekProjectionFirstIso`, `...SecondIso`, `...ThirdIso`:
  `Lπ_! ∘ gᵢ⁻¹ = Lπ_{i,!}`.
* `CommAlgCat.derivedLowerShriek_comp_inverseImage_polynomialTower`: **Tag 08QW**, all six
  identities.

## Implementation notes

The source's "hence" is the composition of derived lower shrieks: `π = πᵢ ∘ gᵢ`, so
`Lπ_! = Lπ_{i,!} ∘ Lg_{i,!}`, and then `Lπ_! ∘ gᵢ⁻¹ = Lπ_{i,!} ∘ Lg_{i,!} ∘ gᵢ⁻¹ = Lπ_{i,!}`. The
composition is obtained from the derived adjunctions `Lπ_! ⊣ π⁻¹`, `Lπ_{i,!} ⊣ πᵢ⁻¹` and
`Lg_{i,!} ⊣ gᵢ⁻¹` of Stacks 09T5, which exist because abelian sheaves on the four sites have enough
projectives, and the identity `π⁻¹ = gᵢ⁻¹ ∘ πᵢ⁻¹`, which holds on the nose.

## References

* [Stacks Project, Tag 08QW](https://stacks.math.columbia.edu/tag/08QW)
* [Stacks Project, Tag 08QT](https://stacks.math.columbia.edu/tag/08QT)
* [Stacks Project, Tag 08PD](https://stacks.math.columbia.edu/tag/08PD)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.ChaoticSite

attribute [local instance] HasDerivedCategory.standard

section Large

variable {𝒳 : Type (u + 1)} [Category.{u} 𝒳]

/-- Abelian presheaves on a category with objects in `Type (u + 1)` and morphisms in `Type u`
have enough projectives: the coproduct of the free presheaves on projective covers of the values
maps onto any presheaf. -/
instance enoughProjectives_presheaf_large :
    EnoughProjectives (𝒳ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  ⟨fun Z => ⟨⟨freeYonedaPresentationSrc Z, freeYonedaPresentation Z⟩⟩⟩

/-- Abelian sheaves for the chaotic topology on such a category have enough projectives. -/
instance enoughProjectives_sheaf_bot_large :
    EnoughProjectives (Sheaf (⊥ : GrothendieckTopology 𝒳) AddCommGrpCat.{u + 1}) :=
  (sheafBotEquivalence (C := 𝒳) AddCommGrpCat.{u + 1}).enoughProjectives_iff.2 inferInstance

section Comparison

variable {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴 : Type (u + 1)} [Category.{u} 𝒴] (ug : 𝒳 ⥤ 𝒴)

/-- **`Lπ_! ∘ g⁻¹ = Lπ'_!` for a functor of chaotic sites along which `Lg_! ∘ g⁻¹ = id`**, where
`π` and `π'` are the projections of the two sites to the point. The topologies are taken equal to
the chaotic ones rather than literally chaotic, as in
`Stacks.ChaoticSite.abelianDerivedLowerShriekInverseImageIso`. -/
def derivedLowerShriekProjectionCompIsoOfEqBot (J𝒳 : GrothendieckTopology 𝒳)
    (J𝒴 : GrothendieckTopology 𝒴) (Jpt : GrothendieckTopology (Discrete PUnit.{u + 2}))
    (h𝒳 : J𝒳 = ⊥) (h𝒴 : J𝒴 = ⊥) (hpt : Jpt = ⊥)
    [HasSheafify J𝒳 AddCommGrpCat.{u + 1}] [HasSheafify J𝒴 AddCommGrpCat.{u + 1}]
    [HasSheafify Jpt AddCommGrpCat.{u + 1}]
    [ug.IsContinuous J𝒳 J𝒴] [(Functor.star 𝒳).IsContinuous J𝒳 Jpt]
    [(Functor.star 𝒴).IsContinuous J𝒴 Jpt]
    (G : DerivedCategory (Sheaf J𝒴 AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf J𝒳 AddCommGrpCat.{u + 1}))
    (hmain : ∀ (Lg : DerivedCategory (Sheaf J𝒳 AddCommGrpCat.{u + 1}) ⥤
        DerivedCategory (Sheaf J𝒴 AddCommGrpCat.{u + 1}))
      (αg : DerivedCategory.Qh ⋙ Lg ⟶
        (ug.sheafPullback AddCommGrpCat.{u + 1} J𝒳 J𝒴).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      [Lg.IsLeftDerivedFunctor αg (HomotopyCategory.quasiIso
        (Sheaf J𝒳 AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))], G ⋙ Lg ≅ 𝟭 _)
    (L : DerivedCategory (Sheaf J𝒳 AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf Jpt AddCommGrpCat.{u + 1}))
    (α : DerivedCategory.Qh ⋙ L ⟶
      ((Functor.star 𝒳).sheafPullback AddCommGrpCat.{u + 1} J𝒳 Jpt).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
      (Sheaf J𝒳 AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
    (L' : DerivedCategory (Sheaf J𝒴 AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf Jpt AddCommGrpCat.{u + 1}))
    (α' : DerivedCategory.Qh ⋙ L' ⟶
      ((Functor.star 𝒴).sheafPullback AddCommGrpCat.{u + 1} J𝒴 Jpt).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L'.IsLeftDerivedFunctor α' (HomotopyCategory.quasiIso
      (Sheaf J𝒴 AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))] :
    G ⋙ L ≅ L' := by
  subst h𝒳
  subst h𝒴
  subst hpt
  have := preservesFiniteLimits_sheafPushforwardContinuous_bot AddCommGrpCat.{u + 1} ug
  have := preservesFiniteColimits_sheafPushforwardContinuous_bot AddCommGrpCat.{u + 1} ug
  have := preservesFiniteLimits_sheafPushforwardContinuous_bot AddCommGrpCat.{u + 1}
    (Functor.star 𝒳)
  have := preservesFiniteColimits_sheafPushforwardContinuous_bot AddCommGrpCat.{u + 1}
    (Functor.star 𝒳)
  have := preservesFiniteLimits_sheafPushforwardContinuous_bot AddCommGrpCat.{u + 1}
    (Functor.star 𝒴)
  have := preservesFiniteColimits_sheafPushforwardContinuous_bot AddCommGrpCat.{u + 1}
    (Functor.star 𝒴)
  have : PreservesColimitsOfSize.{0, 0} (ug.sheafPullback AddCommGrpCat.{u + 1} ⊥ ⊥) :=
    (ug.sheafAdjunctionContinuous AddCommGrpCat.{u + 1} ⊥ ⊥).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0}
      ((Functor.star 𝒳).sheafPullback AddCommGrpCat.{u + 1} ⊥ ⊥) :=
    Adjunction.leftAdjoint_preservesColimits
      ((Functor.star 𝒳).sheafAdjunctionContinuous AddCommGrpCat.{u + 1} ⊥ ⊥)
  have : PreservesColimitsOfSize.{0, 0}
      ((Functor.star 𝒴).sheafPullback AddCommGrpCat.{u + 1} ⊥ ⊥) :=
    Adjunction.leftAdjoint_preservesColimits
      ((Functor.star 𝒴).sheafAdjunctionContinuous AddCommGrpCat.{u + 1} ⊥ ⊥)
  have : HasExactColimitsOfShape ℕ (Sheaf (⊥ : GrothendieckTopology 𝒳) AddCommGrpCat.{u + 1}) :=
    HasExactColimitsOfShape.domain_of_functor ℕ (sheafToPresheaf ⊥ AddCommGrpCat.{u + 1})
  have : HasExactColimitsOfShape ℕ (Sheaf (⊥ : GrothendieckTopology 𝒴) AddCommGrpCat.{u + 1}) :=
    HasExactColimitsOfShape.domain_of_functor ℕ (sheafToPresheaf ⊥ AddCommGrpCat.{u + 1})
  have : HasExactColimitsOfShape ℕ (Sheaf (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2}))
      AddCommGrpCat.{u + 1}) :=
    HasExactColimitsOfShape.domain_of_functor ℕ (sheafToPresheaf ⊥ AddCommGrpCat.{u + 1})
  have hLg := CategoryHomology.hasPointwiseLeftDerivedFunctor_of_enoughProjectives
    (ug.sheafPullback AddCommGrpCat.{u + 1} ⊥ ⊥)
  let Lg := ((ug.sheafPullback AddCommGrpCat.{u + 1} ⊥ ⊥).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf (⊥ : GrothendieckTopology 𝒳) AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ))
  let αg := ((ug.sheafPullback AddCommGrpCat.{u + 1} ⊥ ⊥).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalLeftDerivedCounit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Sheaf (⊥ : GrothendieckTopology 𝒳) AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ))
  exact derivedLowerShriekCompInverseImageIso
    (ug.sheafAdjunctionContinuous AddCommGrpCat.{u + 1} ⊥ ⊥)
    ((Functor.star 𝒳).sheafAdjunctionContinuous AddCommGrpCat.{u + 1} ⊥ ⊥)
    ((Functor.star 𝒴).sheafAdjunctionContinuous AddCommGrpCat.{u + 1} ⊥ ⊥)
    (Iso.refl _) Lg αg G (hmain Lg αg) L α L' α'

end Comparison

end Large

end Stacks.ChaoticSite

namespace CommAlgCat

open Stacks.ChaoticSite

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
  {C : Type u} [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- The projection of `C_{C/B/A}` to the point is continuous. -/
instance polynomialTowerStar_isContinuous :
    (Functor.star (polynomialTowerSite A B C)).IsContinuous (polynomialTowerTopology A B C)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 2})) :=
  (polynomialTowerRingedPoint A B C).fibredSituation.isContinuous

/-- **Tag 08QW, `Lπ_! ∘ g₁⁻¹ = Lπ_{1,!}`.** For any left derived functors `L` of lower shriek
along `π : C_{C/B/A} ⥤ *` and `L₁` of lower shriek along `π₁ : C_{B/A} ⥤ *`, and any derived
functor `G` of inverse image along `g₁`, `G ⋙ L ≅ L₁`. -/
def derivedLowerShriekProjectionFirstIso
    (G : DerivedCategory (Sheaf (polynomialTopology A (towerBaseAlgebra A B))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Qh ⋙ G ≅
      ((polynomialTowerFirst A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (polynomialTopology A (towerBaseAlgebra A B))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))
        AddCommGrpCat.{u + 1}))
    (α : DerivedCategory.Qh ⋙ L ⟶
      ((Functor.star (polynomialTowerSite A B C)).sheafPullback AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
      (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
    (L₁ : DerivedCategory (Sheaf (polynomialTopology A (towerBaseAlgebra A B))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))
        AddCommGrpCat.{u + 1}))
    (α₁ : DerivedCategory.Qh ⋙ L₁ ⟶
      ((Functor.star (polynomialSite A (towerBaseAlgebra A B))).sheafPullback
        AddCommGrpCat.{u + 1} (polynomialTopology A (towerBaseAlgebra A B))
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L₁.IsLeftDerivedFunctor α₁ (HomotopyCategory.quasiIso
      (Sheaf (polynomialTopology A (towerBaseAlgebra A B)) AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ))] :
    G ⋙ L ≅ L₁ :=
  derivedLowerShriekProjectionCompIsoOfEqBot (polynomialTowerFirst A B C) _ _ _
    (polynomialTowerTopology_eq_bot A B C) (polynomialTopology_eq_bot A _)
    GrothendieckTopology.trivial_eq_bot G
    (fun Lg αg _ => derivedLowerShriekFirstInverseImageIso A B C Lg αg G e) L α L₁ α₁

/-- **Tag 08QW, `Lπ_! ∘ g₂⁻¹ = Lπ_{2,!}`.** For any left derived functors `L` of lower shriek
along `π : C_{C/B/A} ⥤ *` and `L₂` of lower shriek along `π₂ : C_{C/A} ⥤ *`, and any derived
functor `G` of inverse image along `g₂`, `G ⋙ L ≅ L₂`. -/
def derivedLowerShriekProjectionSecondIso
    (G : DerivedCategory (Sheaf (polynomialTopology A (towerTotalAlgebra A C))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Qh ⋙ G ≅
      ((polynomialTowerSecond A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (polynomialTopology A (towerTotalAlgebra A C))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))
        AddCommGrpCat.{u + 1}))
    (α : DerivedCategory.Qh ⋙ L ⟶
      ((Functor.star (polynomialTowerSite A B C)).sheafPullback AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
      (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
    (L₂ : DerivedCategory (Sheaf (polynomialTopology A (towerTotalAlgebra A C))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))
        AddCommGrpCat.{u + 1}))
    (α₂ : DerivedCategory.Qh ⋙ L₂ ⟶
      ((Functor.star (polynomialSite A (towerTotalAlgebra A C))).sheafPullback
        AddCommGrpCat.{u + 1} (polynomialTopology A (towerTotalAlgebra A C))
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L₂.IsLeftDerivedFunctor α₂ (HomotopyCategory.quasiIso
      (Sheaf (polynomialTopology A (towerTotalAlgebra A C)) AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ))] :
    G ⋙ L ≅ L₂ :=
  derivedLowerShriekProjectionCompIsoOfEqBot (polynomialTowerSecond A B C) _ _ _
    (polynomialTowerTopology_eq_bot A B C) (polynomialTopology_eq_bot A _)
    GrothendieckTopology.trivial_eq_bot G
    (fun Lg αg _ => derivedLowerShriekSecondInverseImageIso A B C Lg αg G e) L α L₂ α₂

/-- **Tag 08QW, `Lπ_! ∘ g₃⁻¹ = Lπ_{3,!}`.** For any left derived functors `L` of lower shriek
along `π : C_{C/B/A} ⥤ *` and `L₃` of lower shriek along `π₃ : C_{C/B} ⥤ *`, and any derived
functor `G` of inverse image along `g₃`, `G ⋙ L ≅ L₃`. -/
def derivedLowerShriekProjectionThirdIso
    (G : DerivedCategory (Sheaf (polynomialTopology B (towerRelativeAlgebra B C))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Qh ⋙ G ≅
      ((polynomialTowerThird A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (polynomialTopology B (towerRelativeAlgebra B C))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))
        AddCommGrpCat.{u + 1}))
    (α : DerivedCategory.Qh ⋙ L ⟶
      ((Functor.star (polynomialTowerSite A B C)).sheafPullback AddCommGrpCat.{u + 1}
        (polynomialTowerTopology A B C)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
      (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
    (L₃ : DerivedCategory (Sheaf (polynomialTopology B (towerRelativeAlgebra B C))
        AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))
        AddCommGrpCat.{u + 1}))
    (α₃ : DerivedCategory.Qh ⋙ L₃ ⟶
      ((Functor.star (polynomialSite B (towerRelativeAlgebra B C))).sheafPullback
        AddCommGrpCat.{u + 1} (polynomialTopology B (towerRelativeAlgebra B C))
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [L₃.IsLeftDerivedFunctor α₃ (HomotopyCategory.quasiIso
      (Sheaf (polynomialTopology B (towerRelativeAlgebra B C)) AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ))] :
    G ⋙ L ≅ L₃ :=
  derivedLowerShriekProjectionCompIsoOfEqBot (polynomialTowerThird A B C) _ _ _
    (polynomialTowerTopology_eq_bot A B C) (polynomialTopology_eq_bot B _)
    GrothendieckTopology.trivial_eq_bot G
    (fun Lg αg _ => derivedLowerShriekThirdInverseImageIso Lg αg G e) L α L₃ α₃


/-- **Stacks Project, Tag 08QW.** With notation as in Tag 08QT, `Lg_{i,!} ∘ g_i⁻¹ = id` for
`i = 1, 2, 3`, and hence also `Lπ_! ∘ g_i⁻¹ = Lπ_{i,!}` for `i = 1, 2, 3`.

Here `g₁`, `g₂`, `g₃` are the morphisms of topoi from `C_{C/B/A}` to `C_{B/A}`, `C_{C/A}` and
`C_{C/B}` induced by `u₁`, `u₂`, `u₃`, and `π`, `π₁`, `π₂`, `π₃` the projections of the four sites
to the point; all four sites carry the chaotic topology. The statement is about abelian sheaves on
the unbounded derived categories, for *every* left derived functor of each lower shriek and
*every* derived functor of each inverse image, so it does not depend on choices. The six parts
are `CommAlgCat.derivedLowerShriekFirstInverseImageIso`,
`CommAlgCat.derivedLowerShriekSecondInverseImageIso`,
`CommAlgCat.derivedLowerShriekThirdInverseImageIso`,
`CommAlgCat.derivedLowerShriekProjectionFirstIso`,
`CommAlgCat.derivedLowerShriekProjectionSecondIso` and
`CommAlgCat.derivedLowerShriekProjectionThirdIso`. -/
@[stacks 08QW]
theorem derivedLowerShriek_comp_inverseImage_polynomialTower :
    (∀ (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory
            (Sheaf (polynomialTopology A (towerBaseAlgebra A B)) AddCommGrpCat.{u + 1}))
      (α : DerivedCategory.Qh ⋙ L ⟶
        ((polynomialTowerFirst A B C).sheafPullback AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (polynomialTopology A (towerBaseAlgebra A B))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
        (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
      (G : DerivedCategory
          (Sheaf (polynomialTopology A (towerBaseAlgebra A B)) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
      (_ : DerivedCategory.Qh ⋙ G ≅
        ((polynomialTowerFirst A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (polynomialTopology A (towerBaseAlgebra A B))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      Nonempty (G ⋙ L ≅ 𝟭 _)) ∧
    (∀ (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory
            (Sheaf (polynomialTopology A (towerTotalAlgebra A C)) AddCommGrpCat.{u + 1}))
      (α : DerivedCategory.Qh ⋙ L ⟶
        ((polynomialTowerSecond A B C).sheafPullback AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (polynomialTopology A (towerTotalAlgebra A C))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
        (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
      (G : DerivedCategory
          (Sheaf (polynomialTopology A (towerTotalAlgebra A C)) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
      (_ : DerivedCategory.Qh ⋙ G ≅
        ((polynomialTowerSecond A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (polynomialTopology A (towerTotalAlgebra A C))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      Nonempty (G ⋙ L ≅ 𝟭 _)) ∧
    (∀ (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory
            (Sheaf (polynomialTopology B (towerRelativeAlgebra B C)) AddCommGrpCat.{u + 1}))
      (α : DerivedCategory.Qh ⋙ L ⟶
        ((polynomialTowerThird A B C).sheafPullback AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (polynomialTopology B (towerRelativeAlgebra B C))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
        (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
      (G : DerivedCategory
          (Sheaf (polynomialTopology B (towerRelativeAlgebra B C)) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
      (_ : DerivedCategory.Qh ⋙ G ≅
        ((polynomialTowerThird A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (polynomialTopology B (towerRelativeAlgebra B C))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      Nonempty (G ⋙ L ≅ 𝟭 _)) ∧
    (∀ (G : DerivedCategory
          (Sheaf (polynomialTopology A (towerBaseAlgebra A B)) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
      (_ : DerivedCategory.Qh ⋙ G ≅
        ((polynomialTowerFirst A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (polynomialTopology A (towerBaseAlgebra A B))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory
            (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2})) AddCommGrpCat.{u + 1}))
      (α : DerivedCategory.Qh ⋙ L ⟶
        ((Functor.star (polynomialTowerSite A B C)).sheafPullback AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
        (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
      (L' : DerivedCategory
          (Sheaf (polynomialTopology A (towerBaseAlgebra A B)) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory
            (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2})) AddCommGrpCat.{u + 1}))
      (α' : DerivedCategory.Qh ⋙ L' ⟶
        ((Functor.star (polynomialSite A (towerBaseAlgebra A B))).sheafPullback
          AddCommGrpCat.{u + 1} (polynomialTopology A (towerBaseAlgebra A B))
          (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      [L'.IsLeftDerivedFunctor α' (HomotopyCategory.quasiIso
        (Sheaf (polynomialTopology A (towerBaseAlgebra A B)) AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ))],
      Nonempty (G ⋙ L ≅ L')) ∧
    (∀ (G : DerivedCategory
          (Sheaf (polynomialTopology A (towerTotalAlgebra A C)) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
      (_ : DerivedCategory.Qh ⋙ G ≅
        ((polynomialTowerSecond A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (polynomialTopology A (towerTotalAlgebra A C))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory
            (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2})) AddCommGrpCat.{u + 1}))
      (α : DerivedCategory.Qh ⋙ L ⟶
        ((Functor.star (polynomialTowerSite A B C)).sheafPullback AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
        (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
      (L' : DerivedCategory
          (Sheaf (polynomialTopology A (towerTotalAlgebra A C)) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory
            (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2})) AddCommGrpCat.{u + 1}))
      (α' : DerivedCategory.Qh ⋙ L' ⟶
        ((Functor.star (polynomialSite A (towerTotalAlgebra A C))).sheafPullback
          AddCommGrpCat.{u + 1} (polynomialTopology A (towerTotalAlgebra A C))
          (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      [L'.IsLeftDerivedFunctor α' (HomotopyCategory.quasiIso
        (Sheaf (polynomialTopology A (towerTotalAlgebra A C)) AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ))],
      Nonempty (G ⋙ L ≅ L')) ∧
    (∀ (G : DerivedCategory
          (Sheaf (polynomialTopology B (towerRelativeAlgebra B C)) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}))
      (_ : DerivedCategory.Qh ⋙ G ≅
        ((polynomialTowerThird A B C).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (polynomialTopology B (towerRelativeAlgebra B C))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (L : DerivedCategory (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory
            (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2})) AddCommGrpCat.{u + 1}))
      (α : DerivedCategory.Qh ⋙ L ⟶
        ((Functor.star (polynomialTowerSite A B C)).sheafPullback AddCommGrpCat.{u + 1}
          (polynomialTowerTopology A B C)
          (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      [L.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso
        (Sheaf (polynomialTowerTopology A B C) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
      (L' : DerivedCategory
          (Sheaf (polynomialTopology B (towerRelativeAlgebra B C)) AddCommGrpCat.{u + 1}) ⥤
          DerivedCategory
            (Sheaf (GrothendieckTopology.trivial (Discrete PUnit.{u + 2})) AddCommGrpCat.{u + 1}))
      (α' : DerivedCategory.Qh ⋙ L' ⟶
        ((Functor.star (polynomialSite B (towerRelativeAlgebra B C))).sheafPullback
          AddCommGrpCat.{u + 1} (polynomialTopology B (towerRelativeAlgebra B C))
          (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapHomotopyCategory
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      [L'.IsLeftDerivedFunctor α' (HomotopyCategory.quasiIso
        (Sheaf (polynomialTopology B (towerRelativeAlgebra B C)) AddCommGrpCat.{u + 1})
        (ComplexShape.up ℤ))],
      Nonempty (G ⋙ L ≅ L')) :=
  ⟨fun L α _ G e => ⟨derivedLowerShriekFirstInverseImageIso A B C L α G e⟩,
    fun L α _ G e => ⟨derivedLowerShriekSecondInverseImageIso A B C L α G e⟩,
    fun L α _ G e => ⟨derivedLowerShriekThirdInverseImageIso L α G e⟩,
    fun G e L α _ L' α' _ => ⟨derivedLowerShriekProjectionFirstIso G e L α L' α'⟩,
    fun G e L α _ L' α' _ => ⟨derivedLowerShriekProjectionSecondIso G e L α L' α'⟩,
    fun G e L α _ L' α' _ => ⟨derivedLowerShriekProjectionThirdIso G e L α L' α'⟩⟩

end CommAlgCat

end
