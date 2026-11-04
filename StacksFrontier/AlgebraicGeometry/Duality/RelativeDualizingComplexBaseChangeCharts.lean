module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexReindex

/-!
# The base change of diagonal opens, restricted to charts

Let `X' = X ×_S S'`, with `g' : X' ⟶ X` and `f' : X' ⟶ S'`, let `W`, `W'` be diagonal opens of
`f`, `f'` and `w : W' ⟶ W` the restriction of `g' × g'`. For open immersions `jU : U ⟶ X`,
`jU' : U' ⟶ X'` and `gU : U' ⟶ U` with `gU ≫ jU = jU' ≫ g'`, the restricted diagonal opens
`W_U ⊆ U ×_S U` and `W'_{U'} ⊆ U' ×_{S'} U'` are related by the restriction `w_U` of `w`, which
is again the restriction of `gU × gU`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.restrictBaseChangeHom`: `w_U : W'_{U'} ⟶ W_U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  (hpb : IsPullback g' f' f g) (D : DiagonalOpen f) (D' : DiagonalOpen f')
  (w : D'.W ⟶ D.W) (hw : w ≫ D.ι = D'.ι ≫ pullbackMapOfIsPullback hpb)
  {U U' : Scheme.{u}} (jU : U ⟶ X) [IsOpenImmersion jU] (jU' : U' ⟶ X') [IsOpenImmersion jU']
  (gU : U' ⟶ U) (hgU : gU ≫ jU = jU' ≫ g')

omit [IsOpenImmersion jU] [IsOpenImmersion jU'] in
include hpb hgU in
/-- The square `U' ⟶ U ⟶ S` and `U' ⟶ S' ⟶ S` commutes: `gU ≫ jU ≫ f = (jU' ≫ f') ≫ g`. -/
theorem restrictBaseChange_comm : gU ≫ jU ≫ f = (jU' ≫ f') ≫ g := by
  rw [← Category.assoc, hgU, Category.assoc, Category.assoc, hpb.w]

/-- `gU × gU : U' ×_{S'} U' ⟶ U ×_S U`. -/
abbrev restrictPullbackMap : pullback (jU' ≫ f') (jU' ≫ f') ⟶ pullback (jU ≫ f) (jU ≫ f) :=
  pullback.map _ _ _ _ gU gU g (restrictBaseChange_comm hpb jU jU' gU hgU).symm
    (restrictBaseChange_comm hpb jU jU' gU hgU).symm

omit [IsOpenImmersion jU] [IsOpenImmersion jU'] in
include hgU in
/-- The map `gU × gU` is compatible with `g' × g'` under the open immersions
`U' ×_{S'} U' ⟶ X' ×_{S'} X'` and `U ×_S U ⟶ X ×_S X` induced by `jU'` and `jU`. -/
theorem restrictPullbackMap_comp :
    restrictPullbackMap hpb jU jU' gU hgU ≫ pullbackOpensMap jU =
      pullbackOpensMap jU' ≫ pullbackMapOfIsPullback hpb := by
  apply pullback.hom_ext <;>
  · simp only [Category.assoc, pullbackOpensMap_fst, pullbackOpensMap_snd,
      pullbackMapOfIsPullback_fst, pullbackMapOfIsPullback_snd, restrictPullbackMap,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, pullback.map]
    rw [hgU]

/-- The restriction `w_U : W'_{U'} ⟶ W_U` of `w`. -/
def restrictBaseChangeHom : (D'.restrict jU').W ⟶ (D.restrict jU).W :=
  pullback.lift (D'.restrictInclusion jU' ≫ w)
    ((D'.restrict jU').ι ≫ restrictPullbackMap hpb jU jU' gU hgU) (by
      rw [Category.assoc, hw, Category.assoc, restrictPullbackMap_comp, ← Category.assoc,
        ← Category.assoc]
      congr 1
      exact pullback.condition)

/-- The map `w_U` is compatible with `w` under the inclusions `W_U ⟶ W` and `W'_{U'} ⟶ W'`. -/
@[reassoc]
theorem restrictBaseChangeHom_restrictInclusion :
    restrictBaseChangeHom hpb D D' w hw jU jU' gU hgU ≫ D.restrictInclusion jU =
      D'.restrictInclusion jU' ≫ w :=
  pullback.lift_fst _ _ _

/-- The map `w_U` is the restriction of `gU × gU : U' ×_{S'} U' ⟶ U ×_S U`. -/
@[reassoc]
theorem restrictBaseChangeHom_ι :
    restrictBaseChangeHom hpb D D' w hw jU jU' gU hgU ≫ (D.restrict jU).ι =
      (D'.restrict jU').ι ≫ restrictPullbackMap hpb jU jU' gU hgU :=
  pullback.lift_snd _ _ _

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
