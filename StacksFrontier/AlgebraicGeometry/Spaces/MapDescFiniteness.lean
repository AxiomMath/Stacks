module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent

/-!
# From the represented base changes of the comparison of fibre products to its étale charts

Let `f : X ⟶ Z` and `g : Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` and let
`h : Z ⟶ T` be a third morphism. The two local finiteness assertions of part (1) of
Stacks 03KN concern the canonical comparison `X ×_Z Y ⟶ X ×_T Y`, and they are stated through
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` rather than through
`CategoryTheory.MorphismProperty.presheaf`. This file supplies the two steps that bridge the
gap: the passage from the relative morphism property of a morphism of presheaves to the
property of its étale charts, and the transport of a relative morphism property from the
absolute diagonal of `Z` to the comparison.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.LocallyOfFiniteType.respectsLeft_etale` and
  `AlgebraicGeometry.LocallyOfFiniteType.inf_locallyQuasiFinite_respectsLeft_etale`: being
  locally of finite type, and being locally of finite type and locally quasi-finite, absorb an
  étale morphism on the left.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_relative` deduces the chart condition of
  Stacks 03MJ from the relative morphism property, for a property of morphisms of schemes which
  is only assumed stable under precomposition with étale morphisms.
* `AlgebraicGeometry.Space.presheaf_mapDesc_of_presheaf_diag` transports a relative morphism
  property from the absolute diagonal of `Z` to the comparison.

## Implementation notes

The two local finiteness properties of a morphism of algebraic spaces are stated through
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`, whereas the magic square of Stacks 03KM
transports the relative morphism property `CategoryTheory.MorphismProperty.presheaf`. The
bridge between the two is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative`, whose hypotheses include
algebraicity of the source and the target and are therefore unavailable here: the assertions
of Stacks 03KN assume only that the common target `Z` is an algebraic space. Only the
easy direction of that equivalence is needed, and it uses none of those hypotheses — not
algebraicity, not stability under base change, not fppf locality on the target, and not
representability of the morphism. What it does use is that the morphism between the two étale
charts is itself étale, which is `AlgebraicGeometry.Space.etale_of_etale_charts`, and that the
tested property absorbs an étale morphism on the left. So
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_relative` below assumes only
`CategoryTheory.MorphismProperty.RespectsLeft` against `AlgebraicGeometry.Etale`, and the
`mpr` direction of `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative` is an
instance of it.

The relative property of the comparison is two base changes away from the absolute diagonal of
`Z`: the magic square `CategoryTheory.Limits.pullback_map_diagonal_isPullback` exhibits the
comparison as a base change of the relative diagonal of `h`, and
`AlgebraicGeometry.isPullback_pullbackDiagonal_diag` exhibits the relative diagonal as a base
change of the absolute one. Both steps use
`CategoryTheory.MorphismProperty.relative_isStableUnderBaseChange`, which needs no hypothesis
on the tested property, so the input is exactly Stacks 02X4, parts (1) and (4).

The tested property of `AlgebraicGeometry.Space.IsLocallyQuasiFinite` is the infimum of
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite`, and
`AlgebraicGeometry.locallyQuasiFinite_of_etale` supplies both components for an étale
morphism, which is what makes that infimum absorb an étale morphism on the left.

The assertions of Stacks 03KN themselves are stated elsewhere. The two local finiteness ones
are `AlgebraicGeometry.Space.isLocallyOfFiniteType_mapDesc'` and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_mapDesc'` in
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge`, which discharge the hypothesis of
`AlgebraicGeometry.Space.isLocallyOfFiniteType_mapDesc` and
`AlgebraicGeometry.Space.isLocallyQuasiFinite_mapDesc` in
`StacksFrontier.AlgebraicGeometry.Spaces.Diagonal`; the remaining ones, including
quasi-compactness of the comparison and the base-change stability of quasi-compactness of
Stacks 03HF, are in `StacksFrontier.AlgebraicGeometry.Spaces.MapDescent`.

## References

* [Stacks Project, Tag 03KN](https://stacks.math.columbia.edu/tag/03KN)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Absorbing an étale morphism on the left -/

/-- Local finite type of morphisms of schemes absorbs an étale morphism on the left. -/
theorem LocallyOfFiniteType.respectsLeft_etale :
    MorphismProperty.RespectsLeft
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u} : MorphismProperty Scheme.{u}) where
  precomp i hi p hp :=
    have : Etale i := hi
    have : LocallyOfFiniteType i := inferInstance
    have : LocallyOfFiniteType p := hp
    inferInstance

/-- Local quasi-finiteness of morphisms of schemes in the sense of Stacks 03XJ — local finite
type together with Mathlib's fibre condition — absorbs an étale morphism on the left. -/
theorem LocallyOfFiniteType.inf_locallyQuasiFinite_respectsLeft_etale :
    MorphismProperty.RespectsLeft
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (@Etale.{u} : MorphismProperty Scheme.{u}) where
  precomp i hi p hp :=
    have : Etale i := hi
    have hi' := locallyQuasiFinite_of_etale i
    have : LocallyOfFiniteType i := hi'.1
    have : LocallyQuasiFinite i := hi'.2
    have : LocallyOfFiniteType p := hp.1
    have : LocallyQuasiFinite p := hp.2
    ⟨inferInstance, inferInstance⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### From the relative morphism property to the chart condition -/

section Chart

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The relative morphism property `P.presheaf` is inherited along a pullback square. -/
private theorem presheaf_inverseImage_of_isPullback (P : MorphismProperty Scheme.{u})
    {A B' C D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : A ⟶ C} {f' : A ⟶ B'} {f : C ⟶ D}
    {g : B' ⟶ D} (hsq : IsPullback p f' f g)
    (hf : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f' :=
  (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback hsq hf

/-- **Stacks 03MJ**, the direction that needs no hypothesis beyond the tested property
absorbing an étale morphism on the left. A representable morphism of presheaves on the big
fppf site of `S` all of whose represented base changes have `P` has `P` on every commuting
square of étale scheme charts. -/
theorem holdsOnEveryEtaleChart_of_relative (P : MorphismProperty Scheme.{u})
    (hP : P.RespectsLeft (@Etale.{u} : MorphismProperty Scheme.{u})) (f : F ⟶ G)
    (hrel : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f) :
    HoldsOnEveryEtaleChart B S hS P f := by
  intro U V a b h ha hb hab
  have hx : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hrel.1.fst b) :=
    presheaf_inverseImage_of_isPullback B S hS _ (hrel.1.isPullback b).flip hb
  have hsx : yoneda.map (hrel.1.lift a h hab.symm) ≫ hrel.1.fst b = a :=
    hrel.1.lift_fst _ _ _
  have hst : hrel.1.lift a h hab.symm ≫ hrel.1.snd b = h := hrel.1.lift_snd _ _ _
  have hsEtale : Etale ((BigFppfOver.toScheme B S hS).map (hrel.1.lift a h hab.symm)) :=
    etale_of_etale_charts B S hS a (hrel.1.fst b) ha hx (hrel.1.lift a h hab.symm) hsx
  have key : P ((BigFppfOver.toScheme B S hS).map (hrel.1.lift a h hab.symm) ≫
      (BigFppfOver.toScheme B S hS).map (hrel.1.snd b)) :=
    hP.precomp _ hsEtale _ (hrel.2 b _ _ (hrel.1.isPullback b))
  rwa [← Functor.map_comp, hst] at key

end Chart

/-! ### From the absolute diagonal to the comparison of fibre products -/

section MapDesc

variable {X Y Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- A relative morphism property of the absolute diagonal of `Z` is inherited by the comparison
of fibre products, which is a base change of it through the relative diagonal of `h`. -/
theorem presheaf_mapDesc_of_presheaf_diag (P : MorphismProperty Scheme.{u})
    (hd : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (diag Z)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.mapDesc f g h) :=
  presheaf_inverseImage_of_isPullback B S hS P (pullback_map_diagonal_isPullback f g h)
    (presheaf_inverseImage_of_isPullback B S hS P (isPullback_pullbackDiagonal_diag B S hS h) hd)

end MapDesc

end Space

end AlgebraicGeometry

end
