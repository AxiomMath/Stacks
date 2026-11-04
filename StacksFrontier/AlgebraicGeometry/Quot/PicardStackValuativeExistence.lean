module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToBase
public import StacksFrontier.AlgebraicGeometry.Quot.PicardValuativeExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionLifted

/-!
# The Picard stack satisfies the existence part of the valuative criterion (Stacks 0DNG)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` which is proper, of finite
presentation and smooth. Stacks 0DNG says that the structure morphism
`Picardstack_{X/B} ⟶ B` satisfies the existence part of the valuative criterion of Stacks 0CLK.

## Main results

* `AlgebraicGeometry.Space.liftedValuativeCriterionExistence_picardToBase`: **Stacks 0DNG**.

## The argument

After base change to a valuation ring `R` with fraction field `K`, an invertible module `L_K` on
the generic fibre `X_K` of `X_R = X ×_B Spec R` must be extended to an invertible module on
`X_R`. That is
`AlgebraicGeometry.Space.exists_isInvertibleModule_modulePullback_iso_of_valuationRing`, which
writes `L_K ≅ 𝒪_{X_K}(D_K - D'_K)` (Stacks 0DMM, `X_K` being Noetherian, separated and regular by
Stacks 04ZL and 06M1), extends both divisors (Stacks 0DMC) and pulls back.

Given a valuative square, no extension of the valuation ring is needed: the trivial dominating
extension (`AlgebraicGeometry.Stack.LiftedValuativeSquare.trivialExtension`) is taken. The
generic point is an object `(Spec K, b_K, L_K)` of `Picardstack_{X/B}`, the special point is a
test scheme `(Spec R, b_R)` over `B`, and the 2-morphism of the square identifies `b_K` with the
composite of `b_R` and `Spec K ⟶ Spec R`, which gives the morphism
`g : (Spec K, b_K) ⟶ (Spec R, b_R)` of test schemes over `B`. The extension `L` of `L_K` gives
the object `(Spec R, b_R, L)` and the morphism `(g, L|_{X_K} ≅ L_K)` of `Picardstack_{X/B}`, and
since `𝒮_B` is fibred in sets these are all a dotted arrow needs
(`AlgebraicGeometry.Stack.nonempty_dottedArrow_liftedRepresentable_of_faithful`).

## Implementation notes

The Picard stack has its morphisms in the universe `u + 1`, one above the schemes of the site,
so the criterion is stated with
`AlgebraicGeometry.Stack.LiftedValuativeCriterion.Existence`, Stacks 0CLK at that morphism
universe, rather than with `AlgebraicGeometry.Stack.ValuativeCriterion.Existence`, which is for
1-morphisms of `AlgebraicGeometry.Stack.AlgebraicStacks` and so needs morphisms in the universe
`u`.

Of the standing assumptions of Section 0DM9 — `f` flat, proper and of finite presentation — only
properness and finite presentation are binders: flatness follows from the smoothness of the tag.

## References

* [Stacks Project, Tag 0DNG](https://stacks.math.columbia.edu/tag/0DNG)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Section 0DM9](https://stacks.math.columbia.edu/tag/0DM9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` which is proper, of finite
presentation and smooth. Then the structure morphism `Picardstack_{X/B} ⟶ B` satisfies the
existence part of the valuative criterion (Stacks 0CLK). -/
@[stacks 0DNG]
theorem liftedValuativeCriterionExistence_picardToBase (s : PicardSituation B S hS)
    (hfp : IsFinitePresentation B S hS s.f.hom) (hproper : IsProper B S hS s.f.hom)
    (hsmooth : IsSmooth B S hS s.f.hom) :
    Stack.LiftedValuativeCriterion.Existence.{u, u + 1} B S hS
      (picardToBase (modulePushforwardCoherence B S hS) s) := by
  intro q
  refine ⟨q.trivialExtension B S hS, ?_⟩
  let : Category.{u + 1} (PicardObject s) :=
    (picardCategoryData (modulePushforwardCoherence B S hS) s).category
  let U' : BigFppfOver B S hS := siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫
      Spec.map (CommRingCat.ofHom q.trivialRingMap) ≫ q.base)
  let V' : BigFppfOver B S hS := siteObject B S hS q.ring_mem
    (Spec.map (CommRingCat.ofHom q.trivialRingMap) ≫ q.base)
  let r : U' ⟶ V' := q.trivialGenericMap B S hS
  let e := q.trivialExtension B S hS
  let x' := e.k ≫ q.x
  let y' := e.a ≫ q.y
  let oneK := ULiftHom.objUp.{u + 1, u + 1} (Over.mk (𝟙 U'))
  let oneR := ULiftHom.objUp.{u + 1, u + 1} (Over.mk (𝟙 V'))
  let A : PicardObject s := x'.hom.obj oneK
  let Yv := y'.hom.obj oneR
  let TR : s.SchemesOver := ULiftHom.objDown Yv
  have hTK : A.T.left = U' := Functor.congr_obj x'.hom.w oneK
  have hTR : TR.left = V' := Functor.congr_obj y'.hom.w oneR
  let c1 := e.inducedGamma.hom.app oneK
  have hc1 : (baseCFG s.base).val.p.IsHomLift (𝟙 U') c1 := e.inducedGamma.hom.isHomLift' oneK
  have hc1iso : IsIso c1 :=
    Functor.isIso_of_fiber_isGroupoid
      ((baseCFG s.base).isFiberedInGroupoids.fiber_isGroupoid U') c1 hc1
  have hc1inv : (baseCFG s.base).val.p.IsHomLift (𝟙 U') (inv c1) :=
    have := hc1
    IsHomLift.lift_id_inv_isIso (baseCFG s.base).val.p U' c1
  let H : BasedCategory.slice V' ⥤ᵇ BasedCategory.ofFunctor (baseCFG s.base).val.p :=
    BasedFunctor.comp (Stack.liftedRepresentableUp.{u, u + 1} B S hS V') y'.hom
  let c2 := H.map (Over.mkIdTerminal.from (Functor.TwoYoneda.unitOver r))
  have hc2 : (baseCFG s.base).val.p.IsHomLift r c2 :=
    Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal_unitOver (baseCFG s.base).val.p r
  let φ : (picardToBase (modulePushforwardCoherence B S hS) s).hom.obj A ⟶ Yv :=
    @inv _ _ _ _ c1 hc1iso ≫ c2
  have hφ : (baseCFG s.base).val.p.IsHomLift r φ :=
    @IsHomLift.comp_lift_id_left _ _ _ _ (baseCFG s.base).val.p _ _ _ _ _ r c2 hc2
      (@inv _ _ _ _ c1 hc1iso) hc1inv
  let g : A.T ⟶ TR := φ.down
  have hgl : g.left = eqToHom hTK ≫ r ≫ eqToHom hTR.symm :=
    IsHomLift.fac' (baseCFG s.base).val.p r φ
  have hTK' : (BigFppfOver.toScheme B S hS).obj A.T.left = Spec (.of q.K) :=
    congrArg (BigFppfOver.toScheme B S hS).obj hTK
  have hTR' : (BigFppfOver.toScheme B S hS).obj TR.left = Spec (.of q.R) :=
    congrArg (BigFppfOver.toScheme B S hS).obj hTR
  have hr : (BigFppfOver.toScheme B S hS).map r =
      Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) :=
    q.trivialGenericMap_left B S hS
  have hgs : (BigFppfOver.toScheme B S hS).map g.left =
      eqToHom hTK' ≫ Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ eqToHom hTR'.symm := by
    rw [hgl, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, hr]
  obtain ⟨M, hM, ⟨eM⟩⟩ := exists_isInvertibleModule_modulePullback_iso_of_valuationRing s hfp
    hproper hsmooth g hTK' hTR' hgs A.lineBundle A.invertible
  let Z : PicardObject s := ⟨TR, M, hM⟩
  let m : A ⟶ Z := (⟨g, eM.hom, inferInstance⟩ : PicardHom A Z)
  have hm : (picardCFG (modulePushforwardCoherence B S hS) s).val.p.IsHomLift r m :=
    IsHomLift.of_fac' _ r m hTK hTR hgl
  exact Stack.nonempty_dottedArrow_liftedRepresentable_of_faithful B S hS r rfl Z hTR m hm
    (𝟙 Yv) (IsHomLift.id hTR)

end AlgebraicGeometry.Space

end
