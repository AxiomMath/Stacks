module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.PullbackSquare

/-!
# Transitivity of base change of descent data

Let `f : X ⟶ S` be a morphism of schemes, `g : T ⟶ S` and `g' : T' ⟶ T`. A descent datum
relative to `X / S` can be base changed to `T'` in two ways: directly along `g' ≫ g`, giving a
datum relative to `X ×_S T' ⟶ T'`, or in two steps, giving a datum relative to
`(X ×_S T) ×_T T' ⟶ T'`. The two underlying morphisms are canonically isomorphic over `T'`, and
the two base changes have the same étale effectivity.

## Main results

* `AlgebraicGeometry.DescentDatum.changeCompDatumIso`: the iterated base change of a datum is
  the direct base change, after the comparison of the two base morphisms.
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_changeDatum_comp_iff`: **the iterated base
  change of a descent datum is étale effective exactly when the direct one is.**
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_changeDatum_iso_iff`: base change along an
  isomorphism of the base has the same étale effectivity as no base change at all.
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_baseDatum_of_le_iff`: for opens `U ≤ W` of
  the base, restricting a datum to `U` directly or through `W` has the same étale effectivity.

## References

* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentDatum

variable {S X T T' : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ T)

/-- **The iterated base change `(X ×_S T) ×_T T'` compared with the direct base change
`X ×_S T'`.** -/
abbrev changeCompIso : pullback (pullback.snd f g) g' ≅ pullback f (g' ≫ g) :=
  pullbackLeftPullbackSndIso f g g'

/-- The comparison isomorphism `changeCompIso` commutes with the projections to `T'`. -/
lemma changeCompIso_hom_comp_snd :
    (changeCompIso f g g').hom ≫ pullback.snd f (g' ≫ g) =
      pullback.snd (pullback.snd f g) g' ≫ 𝟙 T' := by
  simp

/-- The inverse of the comparison isomorphism `changeCompIso` commutes with the projections to
`T'`. -/
lemma changeCompIso_inv_comp_snd :
    (changeCompIso f g g').inv ≫ pullback.snd (pullback.snd f g) g' =
      pullback.snd f (g' ≫ g) ≫ 𝟙 T' := by
  rw [Category.comp_id, Iso.inv_comp_eq, changeCompIso_hom_comp_snd, Category.comp_id]

/-- The pullback functor taking a datum relative to the direct base change to a datum relative
to the iterated one. -/
abbrev changeCompFunctor :
    DescentData.PullbackFunctor (pullback.snd f (g' ≫ g))
      (pullback.snd (pullback.snd f g) g') (𝟙 T') (changeCompIso f g g').hom
      (changeCompIso_hom_comp_snd f g g') :=
  DescentData.pullbackFunctor _ _ _ _ _

/-- The square from the iterated base change to `X` and `T'`, through the comparison isomorphism
and the direct base change, commutes over `S`. -/
lemma changeComp_commDirect :
    ((changeCompIso f g g').hom ≫ pullback.fst f (g' ≫ g)) ≫ f =
      pullback.snd (pullback.snd f g) g' ≫ g' ≫ g := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, changeCompIso_hom_comp_snd,
    Category.comp_id]

/-- The square from the iterated base change to `X` and `T'`, through the two first projections,
commutes over `S`. -/
lemma changeComp_commIter :
    (pullback.fst (pullback.snd f g) g' ≫ pullback.fst f g) ≫ f =
      pullback.snd (pullback.snd f g) g' ≫ g' ≫ g := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]

/-- The direct base change to `T'` of a datum relative to `X / S`, read as a datum relative to
the *iterated* base change, via the comparison isomorphism of the two. -/
abbrev changeCompDirectFunctor :
    DescentData.PullbackFunctor f (pullback.snd (pullback.snd f g) g') (g' ≫ g)
      ((changeCompIso f g g').hom ≫ pullback.fst f (g' ≫ g))
      (changeComp_commDirect f g g') :=
  DescentData.pullbackFunctor _ _ _ _ _

/-- The iterated base change to `T'` of a datum relative to `X / S`, read in one step. -/
abbrev changeCompIterFunctor :
    DescentData.PullbackFunctor f (pullback.snd (pullback.snd f g) g') (g' ≫ g)
      (pullback.fst (pullback.snd f g) g' ≫ pullback.fst f g)
      (changeComp_commIter f g g') :=
  DescentData.pullbackFunctor _ _ _ _ _

variable {f} in
/-- **The iterated base change of a descent datum is its direct base change**, after the two
base morphisms have been compared over `T'`. -/
def changeCompDatumIso (D : DescentDatum f) :
    pullbackSquareDatum (changeCompFunctor f g g') (D.changeDatum (g' ≫ g)) ≅
      (D.changeDatum g).changeDatum g' :=
  ((DescentData.pullbackFactorizationIso (changeCompDirectFunctor f g g')
      (changePullbackFunctor f (g' ≫ g)) (changeCompFunctor f g g')).app D).symm ≪≫
    (DescentData.pullbackFunctorIsoOfSpec (changeCompDirectFunctor f g g')
      (changeCompIterFunctor f g g')).iso.app D ≪≫
    (DescentData.pullbackFactorizationIso (changeCompIterFunctor f g g')
      (changePullbackFunctor f g) (changePullbackFunctor (pullback.snd f g) g')).app D

variable {f g g'} in
/-- **The iterated base change of a descent datum is étale effective exactly when the direct
base change is.** -/
theorem isEtaleEffective_changeDatum_comp_iff (D : DescentDatum f) [Etale D.over.hom] :
    ((D.changeDatum g).changeDatum g').IsEtaleEffective ↔
      (D.changeDatum (g' ≫ g)).IsEtaleEffective := by
  have hEt : Etale (pullbackSquareDatum (changeCompFunctor f g g')
      (D.changeDatum (g' ≫ g))).over.hom :=
    property_pullbackSquare_over_hom (changeCompFunctor f g g') @Etale _ inferInstance
  refine ⟨fun h ↦ isEtaleEffective_of_isEtaleEffective_pullbackSquare
      (pullback.snd (pullback.snd f g) g') (pullback.snd f (g' ≫ g))
      (changeCompIso f g g').inv (changeCompIso f g g').hom
      (changeCompIso_inv_comp_snd f g g') (changeCompIso_hom_comp_snd f g g') _
      (Functor.essImage.ofIso (ObjectProperty.isoMk _ (changeCompDatumIso g g' D).symm) h),
    fun h ↦ Functor.essImage.ofIso (ObjectProperty.isoMk _ (changeCompDatumIso g g' D))
      (isEtaleEffective_pullbackSquare (changeCompFunctor f g g') h)⟩

variable {f g g'} in
/-- Base change along two equal morphisms of the base has the same étale effectivity. -/
theorem isEtaleEffective_changeDatum_of_eq (D : DescentDatum f) [Etale D.over.hom]
    {g₁ g₂ : T ⟶ S} (h : g₁ = g₂) :
    (D.changeDatum g₁).IsEtaleEffective ↔ (D.changeDatum g₂).IsEtaleEffective := by
  subst h
  rfl

variable {f g g'} in
/-- **Base change along the identity has the same étale effectivity as no base change at
all.** -/
theorem isEtaleEffective_changeDatum_id_iff (D : DescentDatum f) [Etale D.over.hom] :
    (D.changeDatum (𝟙 S)).IsEtaleEffective ↔ D.IsEtaleEffective :=
  ⟨fun h ↦ isEtaleEffective_of_isEtaleEffective_pullbackSquare (pullback.snd f (𝟙 S)) f
      (pullback.lift (𝟙 X) f (by simp)) (pullback.fst f (𝟙 S))
      (by simp only [pullback.lift_snd, Category.comp_id]) pullback.condition _ h,
    isEtaleEffective_pullbackSquare (changePullbackFunctor f (𝟙 S))⟩

variable {f g g'} in
/-- **Base change along an isomorphism of the base has the same étale effectivity as no base
change at all.** -/
theorem isEtaleEffective_changeDatum_iso_iff (D : DescentDatum f) [Etale D.over.hom]
    (e : T ≅ S) : (D.changeDatum e.hom).IsEtaleEffective ↔ D.IsEtaleEffective := by
  refine ⟨fun h ↦ ?_, isEtaleEffective_pullbackSquare (changePullbackFunctor f e.hom)⟩
  have h₁ : ((D.changeDatum e.hom).changeDatum e.inv).IsEtaleEffective :=
    isEtaleEffective_pullbackSquare (changePullbackFunctor (pullback.snd f e.hom) e.inv) h
  exact (isEtaleEffective_changeDatum_id_iff D).mp
    ((isEtaleEffective_changeDatum_of_eq D e.inv_hom_id).mp
      ((isEtaleEffective_changeDatum_comp_iff D).mp h₁))

variable {f g g'} in
/-- **Base change along a morphism of the base precomposed with an isomorphism has the same
étale effectivity as base change along the morphism itself.** -/
theorem isEtaleEffective_changeDatum_iso_comp_iff (D : DescentDatum f) [Etale D.over.hom]
    (g : T ⟶ S) (e : T' ≅ T) :
    (D.changeDatum (e.hom ≫ g)).IsEtaleEffective ↔ (D.changeDatum g).IsEtaleEffective :=
  (isEtaleEffective_changeDatum_comp_iff D).symm.trans
    (isEtaleEffective_changeDatum_iso_iff (D.changeDatum g) e)

variable {f} in
/-- **Étale effectivity over an open of the base does not depend on whether the open is
reached directly or through a larger open.** For `U ≤ W` opens of `S`, the datum restricted to
`U` is étale effective exactly when the datum restricted to `W` is étale effective over the
preimage of `U` in `W`. -/
theorem isEtaleEffective_baseDatum_of_le_iff (D : DescentDatum f) [Etale D.over.hom]
    {U W : S.Opens} (hUW : U ≤ W) :
    ((D.baseDatum W).baseDatum (W.ι ⁻¹ᵁ U)).IsEtaleEffective ↔
      (D.baseDatum U).IsEtaleEffective :=
  (isEtaleEffective_changeDatum_comp_iff D).trans
    ((isEtaleEffective_changeDatum_of_eq D (Scheme.Opens.isoOfLE_hom_ι hUW).symm).trans
      (isEtaleEffective_changeDatum_iso_comp_iff D U.ι (Scheme.Opens.isoOfLE hUW)))

end DescentDatum

end AlgebraicGeometry

end
