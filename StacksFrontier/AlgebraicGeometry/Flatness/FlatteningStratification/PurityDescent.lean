module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.ImpurityAscent
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback

/-!
# Purity along a fibre descends through a flat pointed base change

Let `f : X ⟶ S` be a finite type morphism carrying a finite type quasi-coherent module `ℱ`, let
`s` be a point of `S`, and let `g : S' ⟶ S` carry a point `s'` to `s` and be flat at `s'`. Then
purity of `ℱ` along the fibre over `s` follows from purity of the pulled-back module along the
fibre of `X ×_S S' ⟶ S'` over `s'`, and the same holds for universal purity.

## Main definitions

* `AlgebraicGeometry.FlatPointedBaseChangeSituation.baseChangedSituation` is the pre-pure
  situation obtained by base changing the morphism and the module along the given base change.

## Main results

* `AlgebraicGeometry.isPureAlong_of_flatPointedBaseChange`: purity along the new fibre implies
  purity along the old one.
* `AlgebraicGeometry.universallyPureAlong_of_flatPointedBaseChange`: the same for universal
  purity.

## Implementation notes

An impurity over the old distinguished point is turned into one over the new one by
`AlgebraicGeometry.exists_impurity_after_flatPointedBaseChange`, which produces the base-changed
data as an arbitrary pre-pure situation together with identifications of its base, source,
morphism, module and distinguished point with the chosen fibre products. Purity along the new
fibre is therefore hypothesized in that same form, with the identifications as hypotheses;
universal purity, where no étale neighbourhood has to be transported, is hypothesized for the
canonical choice `FlatPointedBaseChangeSituation.baseChangedSituation`, which the
identifications pin down because a pre-pure situation is determined by those five fields.

Transporting purity needs the ascended impurity diagram to be defined over an *elementary* étale
neighbourhood of the old distinguished point. Its base change along `g` is an elementary étale
neighbourhood of the new one: étale morphisms are stable under base change, and the residue field
extension stays trivial because the residue field at a point of a fibre product is the residue
field of the corresponding prime of the tensor product of residue fields.

## References

* [Stacks Project, Tag 05J9](https://stacks.math.columbia.edu/tag/05J9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Points of equal schemes which correspond under transport along the equality of schemes are
heterogeneously equal. -/
private theorem point_heq {X Y : Scheme.{u}} (e : X = Y) (x : X) (y : Y) (h : e ▸ x = y) :
    HEq x y := by
  cases e
  exact heq_of_eq h

/-- Being elementary transports along an identification of two étale neighbourhoods given by
equalities of their bases, their base points and their schemes compatible with their structure
morphisms and their distinguished points. -/
private lemma etaleNeighborhood_isElementary_of_eq {S S' : Scheme.{u}} {s : S} {s' : S'}
    (U : EtaleNeighborhood S s) (V : EtaleNeighborhood S' s') (eS : S = S')
    (eT : U.scheme = V.scheme) (hf : U.toBase ≫ eqToHom eS = eqToHom eT ≫ V.toBase)
    (ht : eT ▸ U.point = V.point) (hs : eS ▸ s = s') (hV : V.IsElementary) : U.IsElementary := by
  cases U
  cases V
  cases eS
  cases eT
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  cases hf
  cases ht
  cases hs
  simpa [EtaleNeighborhood.IsElementary, EtaleNeighborhood.residueFieldMap] using hV

/-- A pre-pure situation is determined by its base, its source, its morphism, its module and its
distinguished point. -/
private theorem prePureSituation_eq_of_cast {P Q : PrePureSituation.{u}} (hS : P.S = Q.S)
    (hX : P.X = Q.X) (hf : eqToHom hX.symm ≫ P.f ≫ eqToHom hS = Q.f) (hF : HEq P.F Q.F)
    (hs : HEq P.s Q.s) : P = Q := by
  cases P
  cases Q
  cases hS
  cases hX
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  cases hf
  cases hF
  cases hs
  rfl

/-- **Stacks Project, Tag 05J9.** Purity along the original fibre follows from purity along the
fibre of a pointed base change which is flat at its distinguished point. -/
@[stacks 05J9 "flat_descend_pure"]
public theorem isPureAlong_of_flatPointedBaseChange (H : FlatPointedBaseChangeSituation.{u})
    (P' : PrePureSituation.{u}) (eS : P'.S = H.S') (eX : P'.X = pullback H.f H.g)
    (hf : eqToHom eX.symm ≫ P'.f ≫ eqToHom eS = pullback.snd H.f H.g)
    (hF : HEq P'.F ((Scheme.Modules.pullback (pullback.fst H.f H.g)).obj H.F))
    (hs : eS ▸ P'.s = H.s') (hpure : IsPureAlong P') :
    IsPureAlong ({ S := H.S, X := H.X, f := H.f, F := H.F, s := H.s } :
      PrePureSituation.{u}) := by
  intro D hEtale hElem hImp
  obtain ⟨P₁, D₁, eS₁, eX₁, eT, hf₁, hF₁, hs₁, hg₁, hImp₁, _, ht₁, hts₁, _⟩ :=
    exists_impurity_after_flatPointedBaseChange H D hImp
  have hRes : IsIso (D.g.residueFieldMap D.t) := by
    rwa [EtaleNeighborhood.isElementary_iff] at hElem
  have : Etale D.g := hEtale
  have : Etale (pullback.snd D.g H.g) := inferInstance
  let z₁ : (pullback D.g H.g : Scheme).carrier := eT ▸ D₁.t
  let Ucan : EtaleNeighborhood H.S' H.s' :=
    { scheme := pullback D.g H.g
      point := z₁
      toBase := pullback.snd D.g H.g
      map_point := hts₁ }
  have hElemCan : Ucan.IsElementary := (EtaleNeighborhood.isElementary_iff _).mpr
    (pullback_snd_residueFieldMap_isIso D.g H.g z₁ (by rwa [ht₁]))
  have : LocallyOfFiniteType (eqToHom eS₁) := inferInstance
  have : FormallyUnramified (eqToHom eS₁) := inferInstance
  have : Etale D₁.g := by
    have : Etale (D₁.g ≫ eqToHom eS₁) := by
      rw [hg₁]
      infer_instance
    exact Etale.of_comp D₁.g (eqToHom eS₁)
  let U₁ : EtaleNeighborhood P₁.S P₁.s :=
    { scheme := D₁.T
      point := D₁.t
      toBase := D₁.g
      map_point := D₁.mapsToChosenPoint }
  have hElem₁ : U₁.IsElementary :=
    etaleNeighborhood_isElementary_of_eq U₁ Ucan eS₁ eT hg₁ rfl hs₁ hElemCan
  have hS₁₂ : P₁.S = P'.S := eS₁.trans eS.symm
  have hX₁₂ : P₁.X = P'.X := eX₁.trans eX.symm
  have eP : P₁ = P' := by
    refine prePureSituation_eq_of_cast hS₁₂ hX₁₂ ?_ (HEq.trans hF₁ hF.symm)
      (HEq.trans (point_heq eS₁ P₁.s H.s' hs₁) (point_heq eS P'.s H.s' hs).symm)
    calc
      eqToHom hX₁₂.symm ≫ P₁.f ≫ eqToHom hS₁₂ =
          eqToHom eX ≫ (eqToHom eX₁.symm ≫ P₁.f ≫ eqToHom eS₁) ≫ eqToHom eS.symm := by
        simp
      _ = P'.f := by
        rw [hf₁, ← hf]
        simp
  subst eP
  exact hpure D₁ inferInstance hElem₁ hImp₁

/-- The pre-pure situation obtained from a flat pointed base change by base changing the finite
type morphism and the module along the base-change morphism. -/
public abbrev FlatPointedBaseChangeSituation.baseChangedSituation
    (H : FlatPointedBaseChangeSituation.{u}) : PrePureSituation.{u} where
  S := H.S'
  X := pullback H.f H.g
  f := pullback.snd H.f H.g
  F := (Scheme.Modules.pullback (pullback.fst H.f H.g)).obj H.F
  isFiniteType :=
    SheafOfModules.pullback_isFiniteType (pullback.fst H.f H.g).toLRSHom.toShHom H.F
  isQuasicoherent := @SheafOfModules.modulePullback_isQuasicoherent
    (pullback H.f H.g).toRingedSpace H.X.toRingedSpace
    (pullback.fst H.f H.g).toLRSHom.toShHom H.F H.FIsQuasicoherent
  s := H.s'

/-- A pre-pure situation identified field by field with the canonical base change of a flat
pointed base change situation is that base change. -/
private theorem situation_eq_of_fields (H : FlatPointedBaseChangeSituation.{u})
    (P' : PrePureSituation.{u}) (eS : P'.S = H.S') (eX : P'.X = pullback H.f H.g)
    (hf : eqToHom eX.symm ≫ P'.f ≫ eqToHom eS = pullback.snd H.f H.g)
    (hF : HEq P'.F ((Scheme.Modules.pullback (pullback.fst H.f H.g)).obj H.F))
    (hs : eS ▸ P'.s = H.s') : P' = H.baseChangedSituation :=
  prePureSituation_eq_of_cast eS eX hf hF (point_heq eS P'.s H.s' hs)

/-- **Stacks Project, Tag 05J9.** Universal purity along a fibre descends through a pointed base
change which is flat at the new distinguished point. -/
@[stacks 05J9 "flat_descend_universally_pure"]
public theorem universallyPureAlong_of_flatPointedBaseChange
    (H : FlatPointedBaseChangeSituation.{u})
    (h : IsUniversallyPureAlong H.baseChangedSituation) :
    IsUniversallyPureAlong ({ S := H.S, X := H.X, f := H.f, F := H.F, s := H.s } :
      PrePureSituation.{u}) := by
  intro D hD
  obtain ⟨P', D₁, eS, eX, _, hf, hF, hs, _, hImp, _, _, _, _⟩ :=
    exists_impurity_after_flatPointedBaseChange H D hD
  have eP := situation_eq_of_fields H P' eS eX hf hF hs
  subst P'
  exact h D₁ hImp

end AlgebraicGeometry
