module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.BaseChange

/-!
# The inverse-line base-change comparison is normalized by its evaluation pairing

`StacksFrontier/AlgebraicGeometry/InvertibleQuotient/BaseChange.lean` builds Tag 0B3V's
inverse-line comparison `g^*(L^{⊗ -1}) ≅ (g^*L)^{⊗ -1}` as
`Stacks.Divisors.inverseQuotientBaseChange`, for an invertible quotient `Q` of `E` on `X`, an
invertible quotient `Q'` of `E'` on `X'` and an identification `hL : Q'.L ≅ g^* Q.L`. That tag
also asks for the comparison to be *pinned down*, and the normalization it uses is the
evaluation pairing: tensoring the comparison with `hL` must carry the canonical trivialization
of `(g^*L)^{⊗ -1} ⊗ g^*L` to the pullback of the canonical trivialization of
`L^{⊗ -1} ⊗ L`. This file proves that, so the inverse-line clause of Tag 0B3V's base change is
complete — comparison and normalization both — with no hypothesis beyond `hL`.

## Main results

* `Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne_evaluation`: the site-level statement,
  and the whole of the mathematics. If `M ⊗ B ≅ 𝒪` and `hL : L ≅ B` for an invertible `L`, then
  the identification `M ≅ L^{⊗ -1}` determined by the transported pairing is the one that
  carries the canonical trivialization of `L^{⊗ -1} ⊗ L` back to the given pairing.
* `Stacks.RingedSpace.comparison_comp_tensorIsoUnitPullback_hom`: the pulled-back pairing of
  `Stacks.RingedSpace.tensorIsoUnitPullback`, precomposed with the Tag 01CD comparison, is the
  pullback of the original pairing followed by `SheafOfModules.pullbackObjUnitToUnit`. This is
  the only thing used about how that pairing was built.
* `Stacks.Divisors.inverseQuotientBaseChange_evaluation`: the two combined, at the spelling
  Tag 0B3V states.

Two general facts about the sheaf tensor product are recorded on the way, both immediate from
`Stacks.SheafOfModules.Invertible.tensorProductBifunctor` being a functor:
`Stacks.SheafOfModules.Invertible.tensorProductIso_trans` and
`Stacks.SheafOfModules.Invertible.tensorProductIso_refl`.

## Implementation notes

`tensorPowerReindex O hO L (h : -1 + 1 = 0)` is `Iso.refl` and `tensorPower O hO L 0` is
`SheafOfModules.unit _`, both by `rfl`, so the three-step passage
`L^{⊗ -1} ⊗ L ≅ L^{⊗ (-1 + 1)} ≅ L^{⊗ 0} = 𝒪` is definitionally its first step. That is why
`isoTensorPowerNegOne_evaluation_self` is `isoTensorPowerNegOne_hom_tensor` outright, and why
the pullback of the three-step passage reduces to the pullback of `tensorPowerSuccIso` after two
applications of `Functor.map_comp_assoc`.

The two coincidences are *definitional only*, and that is load-bearing for how the proofs are
written: the composite `L^{⊗ -1} ⊗ L ⟶ 𝒪` and the composite `L^{⊗ -1} ⊗ L ⟶ L^{⊗ (-1 + 1)}`
have types that agree by unfolding `tensorPower`, so a term mentioning both is not type-correct
at `implicit` transparency and `rw` will not fire inside it. Every step that would need such a
rewrite is therefore done by `Eq.trans`/`congrArg` in term mode, and every rewriting step is
done in `isoTensorPowerNegOne_evaluation`, whose statement is over an abstract site and so
mentions no scheme projection at all.

The trivializing pairings are stated over
`((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, _⟩).obj M).obj B`, whose ring of scalars is
`Stacks.SheafOfModules.Tensor.ringSheaf ⟨O, _⟩`, while the modules themselves are stated over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO`. The two rings are the same
sheaf, but both names are plain `def`s, so without help the agreement is invisible at `implicit`
transparency: a goal mentioning a pairing is then not type-correct there and `rw` reports that
it cannot find a pattern that is plainly present. Both names are therefore made
`implicit_reducible` locally — the device
`StacksFrontier/CategoryTheory/Sites/Modules/InvertibleRankOne.lean` uses for the same pair. With
them reducible the `Iso.refl` cancellations of `hsplit` have to be named rather than left to
`simp`, which no longer closes the resulting reflexivity.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The sheaf tensor product of two isomorphisms is functorial in both arguments at once. -/
theorem tensorProductIso_trans
    {M M' M'' N N' N'' : SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (e : M ≅ M') (e' : M' ≅ M'') (f : N ≅ N') (f' : N' ≅ N'') :
    tensorProductIso O hO (e ≪≫ e') (f ≪≫ f') =
      tensorProductIso O hO e f ≪≫ tensorProductIso O hO e' f' := by
  have hp : (e ≪≫ e').prod (f ≪≫ f') = e.prod f ≪≫ e'.prod f' := by ext <;> simp
  change (tensorProductBifunctor O hO).mapIso ((e ≪≫ e').prod (f ≪≫ f')) = _
  exact (congrArg (tensorProductBifunctor O hO).mapIso hp).trans
    (Functor.mapIso_trans (tensorProductBifunctor O hO) _ _)

/-- The sheaf tensor product of two identities is the identity. -/
theorem tensorProductIso_refl
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} :
    tensorProductIso O hO (Iso.refl M) (Iso.refl N) = Iso.refl _ := by
  have hp : (Iso.refl M).prod (Iso.refl N) = Iso.refl (M, N) := by ext <;> simp
  change (tensorProductBifunctor O hO).mapIso ((Iso.refl M).prod (Iso.refl N)) = _
  rw [hp]
  exact Iso.ext ((tensorProductBifunctor O hO).map_id _)

/-- **The identification `M ≅ L^{⊗ -1}` supplied by a trivializing pairing `M ⊗ L ≅ 𝒪` carries
the canonical trivialization of `L^{⊗ -1} ⊗ L` back to that pairing.** This is
`Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne_hom_tensor` read along the three-step
passage `L^{⊗ -1} ⊗ L ≅ L^{⊗ (-1 + 1)} ≅ L^{⊗ 0} = 𝒪`, which is definitionally its first
step. -/
theorem isoTensorPowerNegOne_evaluation_self
    (L M : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]
    (h : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj (L)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorProductIso O hO (isoTensorPowerNegOne O hO L M h) (Iso.refl L)).hom ≫
      (tensorPowerSuccIso O hO L (-1)).hom ≫
      (tensorPowerReindex O hO L (show (-1 : ℤ) + 1 = 0 by omega)).hom ≫
      eqToHom (tensorPower_zero O hO L) = h.hom :=
  isoTensorPowerNegOne_hom_tensor O hO L M h

/-- **The evaluation normalization of the negative first tensor power, for a quotient line
identified with another sheaf of modules.** Let `L` be invertible, let `hL : L ≅ B`, and let
`h : M ⊗ B ≅ 𝒪` be a trivializing pairing of `M` against `B`. Transporting `h` along `hL`
presents `M` as `L^{⊗ -1}`, and this says that identification is the one whose tensor product
with `hL.symm` carries the canonical trivialization of `L^{⊗ -1} ⊗ L` back to `h`.

With `B = g^* Q.L`, `M = g^*(Q.L^{⊗ -1})` and `h` the pulled-back pairing, this is the
normalization clause of Tag 0B3V's inverse-line base change. -/
theorem isoTensorPowerNegOne_evaluation
    (L M B : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]
    (hL : L ≅ B)
    (h : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj (M)).obj (B)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (tensorProductIso O hO
        (isoTensorPowerNegOne O hO L M (tensorProductIso O hO (Iso.refl M) hL ≪≫ h))
        hL.symm).hom ≫
      (tensorPowerSuccIso O hO L (-1)).hom ≫
      (tensorPowerReindex O hO L (show (-1 : ℤ) + 1 = 0 by omega)).hom ≫
      eqToHom (tensorPower_zero O hO L) = h.hom := by
  have hsplit : tensorProductIso O hO
      (isoTensorPowerNegOne O hO L M (tensorProductIso O hO (Iso.refl M) hL ≪≫ h))
      hL.symm =
    tensorProductIso O hO (Iso.refl M) hL.symm ≪≫
      tensorProductIso O hO
        (isoTensorPowerNegOne O hO L M (tensorProductIso O hO (Iso.refl M) hL ≪≫ h))
        (Iso.refl L) := by
    rw [← tensorProductIso_trans, Iso.refl_trans, Iso.trans_refl]
  rw [hsplit, Iso.trans_hom, Category.assoc,
    isoTensorPowerNegOne_evaluation_self O hO L M (tensorProductIso O hO (Iso.refl M) hL ≪≫ h),
    Iso.trans_hom, ← Category.assoc, ← Iso.trans_hom, ← tensorProductIso_trans]
  simp [tensorProductIso_refl]

end Stacks.SheafOfModules.Invertible

namespace Stacks.RingedSpace

open Stacks.SheafOfModules.Invertible

/-- **The pulled-back trivializing pairing, read through the Tag 01CD comparison, is the
pullback of the original pairing.** `Stacks.RingedSpace.tensorIsoUnitPullback` inverts that
comparison, so this is the only fact about it a consumer of the pairing needs. -/
theorem comparison_comp_tensorIsoUnitPullback_hom {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (A B : SheafOfModules.{u} (structureSheafRing Y))
    (hAB : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Y.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ (Y.sheaf.obj) (forget₂ CommRingCat RingCat) ((structureSheafRing Y).property)⟩).obj (A)).obj (B)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf Y.sheaf.obj
        (structureSheafRing Y).property))
    (hcomp : IsIso (comparison f A B)) :
    letI : (_root_.SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
      modulePushforward_isRightAdjoint f
    comparison f A B ≫ (tensorIsoUnitPullback f A B hAB hcomp).hom =
      (modulePullback f).map hAB.hom ≫
        _root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f) := by
  let _ : (_root_.SheafOfModules.pushforward (structureSheafHom f)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint f
  have h : (tensorIsoUnitPullback f A B hAB hcomp).hom =
      inv (comparison f A B) ≫ (modulePullback f).map hAB.hom ≫
        _root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom f) := rfl
  change comparison f A B ≫ (tensorIsoUnitPullback f A B hAB hcomp).hom = _
  rw [h]
  exact IsIso.hom_inv_id_assoc _ _

end Stacks.RingedSpace

namespace Stacks.Divisors

open Stacks.SheafOfModules.Invertible

/-- **Tag 0B3V's inverse-line base-change comparison is normalized by evaluation.** Tensoring
`Stacks.Divisors.inverseQuotientBaseChange` with the given identification `hL` of the quotient
lines carries the canonical trivialization of `Q'.L^{⊗ -1} ⊗ Q'.L` back to the pullback, along
the Tag 01CD comparison, of the canonical trivialization of `Q.L^{⊗ -1} ⊗ Q.L`. So the
comparison is not merely some isomorphism of the two sheaves: it is the one the tag specifies.

The proof is `Stacks.SheafOfModules.Invertible.isoTensorPowerNegOne_evaluation` at the pulled
back pairing, composed with
`Stacks.RingedSpace.comparison_comp_tensorIsoUnitPullback_hom`, which says how that pairing was
built. -/
theorem inverseQuotientBaseChange_evaluation
    {X X' : Scheme.{u}} (g : X' ⟶ X)
    (E : X.Modules) (E' : X'.Modules)
    (Q : InvertibleQuotient X E) (Q' : InvertibleQuotient X' E')
    (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L) :
    letI : (_root_.SheafOfModules.pushforward
      (structureSheafHom g.toLRSHom.toShHom)).IsRightAdjoint :=
        modulePushforward_isRightAdjoint g.toLRSHom.toShHom
    letI := Q.invertible
    letI := Q'.invertible
    let N := tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)
    (Scheme.Modules.pullback g).map
        (tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 Q.L (-1)).hom ≫
      (Scheme.Modules.pullback g).map
        (tensorPowerReindex X.presheaf X.ringCatSheaf.2 Q.L
          (show (-1 : ℤ) + 1 = 0 by omega)).hom ≫
      (Scheme.Modules.pullback g).map
        (eqToHom (tensorPower_zero X.presheaf X.ringCatSheaf.2 Q.L)) ≫
      _root_.SheafOfModules.pullbackObjUnitToUnit (structureSheafHom g.toLRSHom.toShHom) =
    (Stacks.RingedSpace.comparisonBifunctorIso g.toLRSHom.toShHom).hom.app (N, Q.L) ≫
      (tensorProductIso X'.presheaf X'.ringCatSheaf.2
        (inverseQuotientBaseChange g E E' Q Q' hL) hL.symm).hom ≫
      (tensorPowerSuccIso X'.presheaf X'.ringCatSheaf.2 Q'.L (-1)).hom ≫
      (tensorPowerReindex X'.presheaf X'.ringCatSheaf.2 Q'.L
        (show (-1 : ℤ) + 1 = 0 by omega)).hom ≫
      eqToHom (tensorPower_zero X'.presheaf X'.ringCatSheaf.2 Q'.L) := by
  let _ := Q.invertible
  let _ := Q'.invertible
  let _ : (_root_.SheafOfModules.pushforward
      (structureSheafHom g.toLRSHom.toShHom)).IsRightAdjoint :=
    modulePushforward_isRightAdjoint g.toLRSHom.toShHom
  -- `g^*` of the three-step passage to `𝒪_X` is `g^*` of its first step, definitionally.
  intro N
  erw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  refine Eq.trans
    (Stacks.RingedSpace.comparison_comp_tensorIsoUnitPullback_hom g.toLRSHom.toShHom
      (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) Q.L
      (tensorPowerSuccIso X.presheaf X.ringCatSheaf.2 Q.L (-1))
      (Stacks.RingedSpace.isIso_comparison _ _ _)).symm ?_
  exact congrArg
    (fun k => Stacks.RingedSpace.comparison g.toLRSHom.toShHom
      (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) Q.L ≫ k)
    (isoTensorPowerNegOne_evaluation X'.presheaf X'.ringCatSheaf.2 Q'.L
      ((Scheme.Modules.pullback g).obj (tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)))
      ((Scheme.Modules.pullback g).obj Q.L) hL
      (inverseQuotientBaseChangePairing g Q.L)).symm

end Stacks.Divisors

end
