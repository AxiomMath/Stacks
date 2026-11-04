module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic

/-!
# Pullback and pushforward of sheaves of algebras are adjoint

Let `g : T ⟶ S` be a morphism of schemes.  Pullback of algebra sheaves,
`Stacks.AffineAlgebraEquivalence.algebraPullback g`, sends an `𝒪_S`-algebra `A` to the
`𝒪_T`-algebra `g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T`.  This file proves that it is left adjoint to the direct
image of algebra sheaves, `B ↦ g_*B` with its `𝒪_S`-algebra structure through `g.c`.

This is the universal property of base change of algebras in the form in which the base-change
assertion of Stacks Tag 01SA is to be used: a morphism of `𝒪_T`-algebras out of
`g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` is the same thing as a morphism of `𝒪_S`-algebras `A ⟶ g_*B`.

## Main definitions

* `Stacks.AffineAlgebraEquivalence.algebraPushforward` is the direct image of algebra sheaves
  along `g`, namely `B ↦ g_*B` regarded as an `𝒪_S`-algebra through the comorphism `g.c`.
* `Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction` is the adjunction
  `algebraPullback g ⊣ algebraPushforward g`.

## Main results

* `Stacks.AffineAlgebraEquivalence.unit_comp_map_inverseImageStructureMap`: the structural map
  `g⁻¹𝒪_S ⟶ 𝒪_T` has the comorphism `g.c` as its adjunct, which is how it was defined.
* `Stacks.AffineAlgebraEquivalence.homEquiv_right`: the bijection of the adjunction, read on
  underlying sheaves of rings, is the bijection of the pullback--pushforward adjunction for
  sheaves of rings precomposed with the canonical map `g⁻¹A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T`.
* `Stacks.AffineAlgebraEquivalence.algebraPushforward_pushforwardAlgebra`: the direct image of
  `q_* 𝒪_Y` along `g` is `(q ≫ g)_* 𝒪_Y`, an equality of algebra sheaves.

## Implementation notes

The adjunction is not constructed by hand.  `algebraPullback g` is by definition the composite
`Under.post (g⁻¹) ⋙ Under.pushout (inverseImageStructureMap g)`, and both factors are left
adjoints in Mathlib: `CategoryTheory.Under.postAdjunctionLeft` for the first and
`CategoryTheory.Under.mapPushoutAdj` for the second.  Composing the two adjunctions gives
`Under.map (inverseImageStructureMap g) ⋙ Under.post g_* ⋙ Under.map (unit)` as the right
adjoint, and `rightIso` identifies that with `algebraPushforward g`; the identification is the
identity on underlying sheaves of rings and the two structure morphisms agree by
`unit_comp_map_inverseImageStructureMap`.

Several proofs are in term mode rather than by `rw`.  `TopCat.Sheaf CommRingCat X` is
`CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat`, whose morphisms are built by
`InducedCategory.Hom.mk`, and the anonymous constructor `⟨g.c⟩` for such a morphism is not
type-correct at instance transparency; a `rw` whose motive mentions it therefore fails with an
application type mismatch even though the statement elaborates.  `homEquiv_right` is closed by
`rfl` after unfolding the two hom-equivalences, because the direct image of sheaves of rings is
precomposition with the inverse-image functor on opens, for which functoriality holds
definitionally.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-- The direct image of algebra sheaves along `g : T ⟶ S`: the `𝒪_T`-algebra `B` is sent to
`g_*B`, an `𝒪_S`-algebra through the comorphism `g.c`. -/
public noncomputable def algebraPushforward :
    Stacks.RelativeSpec.AlgebraSheaf T ⥤ Stacks.RelativeSpec.AlgebraSheaf S :=
  Under.post (TopCat.Sheaf.pushforward CommRingCat g.base) ⋙ Under.map (⟨g.c⟩ :
    S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat g.base).obj T.sheaf)

/-- The direct image along `g` of the pushed-forward structure sheaf of `q : Y ⟶ T` is the
pushed-forward structure sheaf of `q ≫ g`. -/
public theorem algebraPushforward_pushforwardAlgebra {Y : Scheme.{u}} (q : Y ⟶ T) :
    (algebraPushforward g).obj (pushforwardAlgebra q) = pushforwardAlgebra (q ≫ g) :=
  rfl

/-- The structural map `g⁻¹ 𝒪_S ⟶ 𝒪_T` is adjoint to the comorphism `g.c`. -/
public theorem unit_comp_map_inverseImageStructureMap :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).unit.app S.sheaf ≫
        (TopCat.Sheaf.pushforward CommRingCat g.base).map (inverseImageStructureMap g) =
      (⟨g.c⟩ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat g.base).obj T.sheaf) :=
  Eq.trans
    (Adjunction.homEquiv_apply (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base)
      S.sheaf T.sheaf (inverseImageStructureMap g)).symm
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).homEquiv
      S.sheaf T.sheaf).apply_symm_apply _)

/-- The right adjoint produced by composing the two Mathlib adjunctions is the direct image of
algebra sheaves. -/
public noncomputable def rightIso :
    Under.map (inverseImageStructureMap g) ⋙
        Under.post (TopCat.Sheaf.pushforward CommRingCat g.base) ⋙
          Under.map ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).unit.app
            S.sheaf) ≅
      algebraPushforward g :=
  NatIso.ofComponents (fun B ↦ Under.isoMk (Iso.refl _)
    (Eq.trans (Category.comp_id _)
      (Eq.trans (congrArg (fun k ↦ (TopCat.Sheaf.pullbackPushforwardAdjunction
          CommRingCat g.base).unit.app S.sheaf ≫ k)
        ((TopCat.Sheaf.pushforward CommRingCat g.base).map_comp
          (inverseImageStructureMap g) B.hom))
        (Eq.trans (Category.assoc _ _ _).symm
          (congrArg (fun k ↦ k ≫ (TopCat.Sheaf.pushforward CommRingCat g.base).map B.hom)
            (unit_comp_map_inverseImageStructureMap g)))))) (by
    intro B B' f
    ext
    exact Eq.trans (Category.comp_id _) (Category.id_comp _).symm)

/-- **Base change of algebras is adjoint to direct image.** A morphism of `𝒪_T`-algebras
`g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ B` is the same thing as a morphism of `𝒪_S`-algebras `A ⟶ g_*B`. -/
public noncomputable def algebraPullbackPushforwardAdjunction :
    algebraPullback g ⊣ algebraPushforward g :=
  ((Under.postAdjunctionLeft (X := S.sheaf)
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base)).comp
    (Under.mapPushoutAdj (inverseImageStructureMap g))).ofNatIsoRight (rightIso g)

/-- The bijection of the adjunction, read on underlying sheaves of rings: it is the bijection
of the pullback--pushforward adjunction for sheaves of rings, applied to the restriction of the
given morphism along the canonical map `g⁻¹A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T`. -/
public theorem homEquiv_right (A : Stacks.RelativeSpec.AlgebraSheaf S)
    (Q : Stacks.RelativeSpec.AlgebraSheaf T) (u : (algebraPullback g).obj A ⟶ Q) :
    ((algebraPullbackPushforwardAdjunction g).homEquiv A Q u).right =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).homEquiv
        A.right Q.right (pushout.inl _ _ ≫ u.right) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rfl

end Stacks.AffineAlgebraEquivalence

end
