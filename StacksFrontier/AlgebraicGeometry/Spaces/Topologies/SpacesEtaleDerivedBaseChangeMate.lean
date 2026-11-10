module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleCohomologyRestriction

/-!
# The derived base change map of algebraic spaces is a mate

Let `T` be a big étale site of algebraic spaces over a scheme `S` and let
```
Y' --g'--> Y
|f'        |f
v          v
X' --g---> X
```
be a cartesian square of its objects. The base change map
`g⁻¹ R f_* ⟶ R f'_* (g')⁻¹` of Stacks 0DG3,
`AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleDerivedBaseChange`, is built by descending the
abelian base change map along a derived-functor unit. This file identifies it with the mate,
under the derived adjunctions `f⁻¹ ⊣ R f_*` and `f'⁻¹ ⊣ R f'_*`, of an invertible comparison
`g⁻¹ ⋙ f'⁻¹ ⟶ f⁻¹ ⋙ (g')⁻¹` of the two composite derived inverse images, so that the formal
calculus of mates applies to it. This is the analogue for algebraic spaces of
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_eq_mateEquiv`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.spacesToposInverseImageSquare`: the comparison
  `g⁻¹ ⋙ f'⁻¹ ⟶ f⁻¹ ⋙ (g')⁻¹` of inverse images of sheaves of sets on the spaces-étale sites
  whose mate is the base change 2-cell `AlgebraicGeometry.Space.spacesToposBaseChangeSquare`.
* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleAbelianInverseImageSquare`: the same
  comparison for abelian sheaves.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleAbelianAdjunction_counit_forget`: the counit of
  the abelian adjunction `f⁻¹ ⊣ f_*` is the counit of the adjunction of sheaves of sets on
  underlying sheaves.
* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_spacesToposInverseImageSquare` and
  `AlgebraicGeometry.BigEtaleSpaceSite.isIso_spacesEtaleAbelianInverseImageSquare`: both
  comparisons are invertible.
* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleAbelianBaseChange_eq_mateEquiv`: the abelian
  base change map is the mate of the abelian comparison.
* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleDerivedBaseChange_eq_mateEquiv`: **the derived
  base change map is the mate of the derived comparison of the composite inverse images.**

## Implementation notes

The base change 2-cell of sheaves of sets is defined as the mate, across the two *vertical*
adjunctions `g⁻¹ ⊣ g_*` and `(g')⁻¹ ⊣ g'_*`, of the comparison of the two composite direct
images. Its mate across the two *horizontal* adjunctions, `spacesToposInverseImageSquare`, is
then the conjugate of that comparison (`CategoryTheory.iterated_mateEquiv_conjugateEquiv`),
hence invertible, the comparison of direct images being invertible. The abelian comparison is
its lift to abelian sheaves; that the abelian base change map is its mate is checked on
underlying sheaves of sets, where the units and counits of the abelian adjunctions are those of
the adjunctions of sheaves of sets. The derived statement is then the abstract
`Stacks.Homology.DerivedSquare.derivedSquare_mateEquiv`.

## References

* [Stacks Project, Tag 0DG3](https://stacks.math.columbia.edu/tag/0DG3)
* [Stacks Project, Tag 0DG5](https://stacks.math.columbia.edu/tag/0DG5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Homology.DerivedSquare (totalRightDerived totalRightDerivedUnit derivedTwoSquare)

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard smallEtaleAbelianInverseImage_additive

/-! ### The abelian adjunction on underlying sheaves of sets -/

section Forget

variable {X Y : T.Spaces} (f : Y ⟶ X)

/-- The unit of the abelian adjunction `f⁻¹ ⊣ f_*` is, on underlying sheaves of sets, the unit
of the adjunction of the morphism of topoi. -/
theorem smallEtaleAbelianAdjunction_unit_forget
    (G : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) :
    (sheafCompose _ (forget Ab.{u + 1})).map ((smallEtaleAbelianAdjunction T f).unit.app G) =
      (smallEtaleMorphism T f).adj.unit.app ((sheafCompose _ (forget Ab.{u + 1})).obj G) :=
  rfl

/-- The counit of the abelian adjunction `f⁻¹ ⊣ f_*` is, on underlying sheaves of sets, the
counit of the adjunction of the morphism of topoi: both are transposed to the identity by the
adjunction of sheaves of sets, by the triangle identities and the agreement of the units. -/
theorem smallEtaleAbelianAdjunction_counit_forget
    (G : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}) :
    (sheafCompose _ (forget Ab.{u + 1})).map ((smallEtaleAbelianAdjunction T f).counit.app G) =
      (smallEtaleMorphism T f).adj.counit.app ((sheafCompose _ (forget Ab.{u + 1})).obj G) := by
  let U := sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (forget Ab.{u + 1})
  let UX := sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (forget Ab.{u + 1})
  let adj := (smallEtaleMorphism T f).adj
  let c := UX.obj ((smallEtalePushforward T f).obj G)
  let φ : (smallEtaleMorphism T f).inverseImage.obj c ⟶ U.obj G :=
    U.map ((smallEtaleAbelianAdjunction T f).counit.app G)
  have h₁ : adj.unit.app c ≫ (smallEtaleMorphism T f).pushforward.map φ = 𝟙 c :=
    (UX.map_comp ((smallEtaleAbelianAdjunction T f).unit.app ((smallEtalePushforward T f).obj G))
      ((smallEtalePushforward T f).map ((smallEtaleAbelianAdjunction T f).counit.app G))).symm.trans
      ((congrArg UX.map ((smallEtaleAbelianAdjunction T f).right_triangle_components G)).trans
        (UX.map_id _))
  have h₂ : φ = (smallEtaleMorphism T f).inverseImage.map
      (adj.unit.app c ≫ (smallEtaleMorphism T f).pushforward.map φ) ≫
        adj.counit.app (U.obj G) :=
    (Category.id_comp φ).symm.trans <|
      (congrArg (· ≫ φ) (adj.left_triangle_components c).symm).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg ((smallEtaleMorphism T f).inverseImage.map (adj.unit.app c) ≫ ·)
        (adj.counit_naturality φ).symm).trans <| by
      rw [Functor.map_comp, Category.assoc]
  exact h₂.trans ((congrArg (fun t => (smallEtaleMorphism T f).inverseImage.map t ≫
      adj.counit.app (U.obj G)) h₁).trans
    ((congrArg (· ≫ adj.counit.app (U.obj G))
      ((smallEtaleMorphism T f).inverseImage.map_id c)).trans (Category.id_comp _)))

end Forget

/-! ### The comparison of the composite inverse images -/

section Square

variable {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')

/-- **The comparison of the two composite inverse images around a cartesian square**, for
sheaves of sets on the spaces-étale sites: the mate, across `f⁻¹ ⊣ f_*` and `f'⁻¹ ⊣ f'_*`, of
the base change 2-cell `AlgebraicGeometry.Space.spacesToposBaseChangeSquare`. -/
def spacesToposInverseImageSquare (sq : IsPullback g' f' f g) :
    TwoSquare (smallEtaleMorphism T g).inverseImage (smallEtaleMorphism T f).inverseImage
      (smallEtaleMorphism T f').inverseImage (smallEtaleMorphism T g').inverseImage :=
  (mateEquiv (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f)
    (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f')).symm
    (Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem g' f' f g sq)

/-- The comparison of the composite inverse images is invertible: it is conjugate to the
comparison of the two composite direct images. -/
instance isIso_spacesToposInverseImageSquare (sq : IsPullback g' f' f g) :
    IsIso (spacesToposInverseImageSquare T f g g' f' sq) := by
  have key := iterated_mateEquiv_conjugateEquiv
    (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f)
    (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f')
    (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g)
    (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g')
    (spacesToposInverseImageSquare T f g g' f' sq)
  have h₁ : mateEquiv (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f)
      (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f')
      (spacesToposInverseImageSquare T f g g' f' sq) =
      Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem g' f' f g sq :=
    Equiv.apply_symm_apply _ _
  have h₂ : mateEquiv (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g')
      (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g)
      (Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem g' f' f g sq) =
      Space.spacesPushforwardCompSquare T.fppfSite S T.fppf_mem g' f' f g sq.w :=
    Equiv.apply_symm_apply _ _
  have hc : conjugateEquiv
      ((Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f).comp
        (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g'))
      ((Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g).comp
        (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f'))
      (spacesToposInverseImageSquare T f g g' f' sq) =
      Space.spacesPushforwardCompSquare T.fppfSite S T.fppf_mem g' f' f g sq.w :=
    key.symm.trans ((congrArg (fun t => (mateEquiv
      (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g')
      (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g) t)) h₁).trans h₂)
  have : IsIso (Space.spacesPushforwardCompSquare T.fppfSite S T.fppf_mem g' f' f g sq.w) := by
    dsimp only [Space.spacesPushforwardCompSquare]
    infer_instance
  have : IsIso (conjugateEquiv
      ((Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f).comp
        (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g'))
      ((Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g).comp
        (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f'))
      (spacesToposInverseImageSquare T f g g' f' sq)) := by
    rw [hc]
    infer_instance
  exact conjugateEquiv_of_iso
    ((Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f).comp
      (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g'))
    ((Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g).comp
      (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f')) _

/-- **The comparison of the two composite inverse images around a cartesian square, for abelian
sheaves**: the lift of `AlgebraicGeometry.BigEtaleSpaceSite.spacesToposInverseImageSquare`, the
inverse image of abelian sheaves being computed on underlying sheaves of sets. -/
def spacesEtaleAbelianInverseImageSquare (sq : IsPullback g' f' f g) :
    TwoSquare (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g))
      (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T f))
      (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T f'))
      (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g')) :=
  haveI : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  ProEtale.liftSheafNatTrans (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y') _ _
    (Functor.whiskerLeft
      (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (forget Ab.{u + 1}))
      (spacesToposInverseImageSquare T f g g' f' sq))

/-- The comparison of the composite inverse images of abelian sheaves is invertible. -/
instance isIso_spacesEtaleAbelianInverseImageSquare (sq : IsPullback g' f' f g) :
    IsIso (spacesEtaleAbelianInverseImageSquare T f g g' f' sq) := by
  have : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : IsIso (Functor.whiskerLeft
      (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (forget Ab.{u + 1}))
      (spacesToposInverseImageSquare T f g g' f' sq)) := inferInstance
  exact @isIso_liftSheafNatTrans _ _ _ _ _ _ _ _ _ _ _ _ this

/-- **The abelian base change map is a mate**: the base change map
`f_* ⋙ g⁻¹ ⟶ (g')⁻¹ ⋙ f'_*` of abelian sheaves is the mate, across the abelian adjunctions
`f⁻¹ ⊣ f_*` and `f'⁻¹ ⊣ f'_*`, of the comparison of the composite inverse images. Both sides
are read on underlying sheaves of sets, where the units and counits of the abelian adjunctions
are those of the adjunctions of sheaves of sets. -/
theorem spacesEtaleAbelianBaseChange_eq_mateEquiv (sq : IsPullback g' f' f g) :
    spacesEtaleAbelianBaseChange T f g g' f' sq =
      (mateEquiv (smallEtaleAbelianAdjunction T f) (smallEtaleAbelianAdjunction T f')
        (spacesEtaleAbelianInverseImageSquare T f g g' f' sq)) := by
  ext G : 2
  apply (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
    (forget Ab.{u + 1})).map_injective
  have hL : (sheafCompose _ (forget Ab.{u + 1})).map
      ((spacesEtaleAbelianBaseChange T f g g' f' sq).app G) =
      (Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem g' f' f g sq).app
        ((sheafCompose _ (forget Ab.{u + 1})).obj G) := rfl
  have hm : Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem g' f' f g sq =
      mateEquiv (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f)
        (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem f')
        (spacesToposInverseImageSquare T f g g' f' sq) :=
    (Equiv.apply_symm_apply _ _).symm
  rw [hL, hm]
  exact congrArg (fun e => (smallEtaleMorphism T f').adj.unit.app
      ((smallEtaleMorphism T g).inverseImage.obj ((smallEtaleMorphism T f).pushforward.obj
        ((sheafCompose _ (forget Ab.{u + 1})).obj G))) ≫
    (smallEtaleMorphism T f').pushforward.map
      ((spacesToposInverseImageSquare T f g g' f' sq).app ((smallEtaleMorphism T f).pushforward.obj
        ((sheafCompose _ (forget Ab.{u + 1})).obj G))) ≫
    (smallEtaleMorphism T f').pushforward.map ((smallEtaleMorphism T g').inverseImage.map e))
    (smallEtaleAbelianAdjunction_counit_forget T f G).symm

/-- **The derived base change map of Stacks 0DG3 is a mate.** For a cartesian square
`Y' = Y ×_X X'` of algebraic spaces of the big étale site, the base change map
`g⁻¹ R f_* ⟶ R f'_* (g')⁻¹` on the unbounded derived categories of abelian sheaves on the
spaces-étale sites is the mate, under the derived adjunctions `f⁻¹ ⊣ R f_*` and
`f'⁻¹ ⊣ R f'_*`, of the derived comparison of the two composite inverse images, which is
invertible (`Stacks.Homology.DerivedSquare.isIso_derivedTwoSquare`). -/
theorem spacesEtaleDerivedBaseChange_eq_mateEquiv (sq : IsPullback g' f' f g) :
    spacesEtaleDerivedBaseChange T f g g' f' sq =
      (mateEquiv (smallEtaleDerivedAdjunction T f) (smallEtaleDerivedAdjunction T f')
        (derivedTwoSquare (spacesEtaleAbelianInverseImageSquare T f g g' f' sq))) := by
  have h := Stacks.Homology.DerivedSquare.derivedSquare_mateEquiv
    (smallEtaleAbelianAdjunction T f) (smallEtaleAbelianAdjunction T f')
    (spacesEtaleAbelianInverseImageSquare T f g g' f' sq)
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}))
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y') Ab.{u + 1}))
  have h₁ : spacesEtaleDerivedBaseChange T f g g' f' sq =
      Stacks.Homology.DerivedSquare.derivedSquare
        (mateEquiv (smallEtaleAbelianAdjunction T f) (smallEtaleAbelianAdjunction T f')
          (spacesEtaleAbelianInverseImageSquare T f g g' f' sq)) := by
    rw [spacesEtaleDerivedBaseChange, spacesEtaleAbelianBaseChange_eq_mateEquiv]
  exact h₁.trans h

end Square

end AlgebraicGeometry.BigEtaleSpaceSite

end
