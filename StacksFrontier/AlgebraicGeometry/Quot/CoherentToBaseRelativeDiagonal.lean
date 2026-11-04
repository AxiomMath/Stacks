module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFiberedUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackToBaseFactorization
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomRepresentableFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentStackIsomEqualizer
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordIsomCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedFibered
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf

/-!
# The relative diagonal of `Coh_{X/Y} ⟶ 𝒮_Y` is affine

Let `f : X ⟶ Y` be a morphism of algebraic spaces of finite presentation (Situation 08KB) and let
`π : Coh_{X/Y} ⟶ 𝒮_Y` be the projection of Stacks 08LP. Stacks 0DLY says that the relative
diagonal `Δ_π : Coh_{X/Y} ⟶ Coh_{X/Y} ×_{𝒮_Y} Coh_{X/Y}` is affine (and of finite presentation),
and the first half of the proof of Stacks 0DLZ deduces that `π` is quasi-separated. The base
change of `Δ_π` along a point `(x, x', α)` over a scheme `U` is the relative Isom functor
`Isom(F, F')` of the two modules over `U`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isAffineAlgebraicSpaceOver_pairIsom`: over a common
  test scheme, the relative Isom functor of the pullbacks of two objects of `Coh_{X/Y}` is affine
  over the base (Stacks 08K9).
* `AlgebraicGeometry.Space.CoherentSituation.exists_relVertHomPresheaf_iso`: the base change of
  `Δ_π` along a scheme-valued point is an algebraic space whose structure morphism over the scheme
  is affine.
* `CoherentSituation.isAffineHom_smallerBasePresheafEquivalence_functor_obj`:
  a presheaf corresponding under Stacks 04SG to a space affine over `U` has affine structure
  morphism.
* `CoherentSituation.isRepresentableByAlgebraicSpaces_relativeDiagonal_coherentToBaseCFG` and
  `CoherentSituation.isAffineHom_relativeDiagonal_coherentToBaseCFG`: `Δ_π` is representable by
  algebraic spaces and affine (the affine half of Stacks 0DLY).
* `AlgebraicGeometry.Space.CoherentSituation.relativeDiagonal_coherentToBaseCFG`: `Δ_π` is
  representable by algebraic spaces, quasi-compact and quasi-separated (the quasi-separation half
  of the proof of Stacks 0DLZ).

## References

* [Stacks Project, Tag 0DLY](https://stacks.math.columbia.edu/tag/0DLY)
* [Stacks Project, Tag 0DLZ](https://stacks.math.columbia.edu/tag/0DLZ)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 0DMB](https://stacks.math.columbia.edu/tag/0DMB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TwoFibreProductOver.RelativeDiagonalFibre

namespace AlgebraicGeometry.Space.CoherentSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] cohCategory cohIsFibered

variable {D : CoherentSituation B S hS}

/-- **Stacks 08K9 for two objects of `Coh_{X/Y}` over a common test scheme, affine half.** Over a
test scheme `T` mapping to the test schemes of `A` and `A'`, the relative Isom functor of the
pullbacks of the two modules is an algebraic space affine over `T`. -/
theorem isAffineAlgebraicSpaceOver_pairIsom
    {T : SchemesOver D.Y} {A A' : CoherentObject D} (tA : T ⟶ A.T) (tA' : T ⟶ A'.T) :
    IsAffineAlgebraicSpaceOver (pairHomSituation tA tA').base
      (pairHomSituation tA tA').isomFunctor := by
  let hst := modulePullbackStabilityOfFinitePresentation B S hS
  let P := pullbackObject' hst A tA
  let P' := pullbackObject' hst A' tA'
  obtain ⟨_, hU, hP⟩ := P.properSupport
  obtain ⟨_, hU', hP'⟩ := P'.properSupport
  let s := pairHomSituation tA tA'
  exact (s.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation
    (D.isFinitePresentation_projection T) P.finitePresentation P'.finitePresentation P.flat P'.flat
    ⟨hU, hP⟩ ⟨hU', hP'⟩
    fun s' hfp' hF' hG' hflat' hsupp' =>
      s'.isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation hfp' hF' hG' hflat'
        hsupp').isAffineAlgebraicSpaceOver

/-- **A presheaf on the schemes over `U` corresponding, under Stacks 04SG, to a space affine over
`U` has affine structure morphism.** If `F` is isomorphic to the presheaf that the presheaf-level
equivalence of Stacks 04SG attaches to an affine `X ⟶ U`, then the image of `F` over `S` has
affine structure morphism. -/
theorem isAffineHom_smallerBasePresheafEquivalence_functor_obj {U : BigFppfOver B S hS}
    (X : Over (yoneda.obj (Over.mk U.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hX : Space.IsAffineHom B S hS X.hom)
    {F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
    (e : F ≅ (smallerBasePresheafEquivalence B U.left.1 S U.left.2 hS U.hom).inverse.obj X) :
    Space.IsAffineHom B S hS
      ((smallerBasePresheafEquivalence B U.left.1 S U.left.2 hS U.hom).functor.obj F).hom := by
  let E := smallerBasePresheafEquivalence B U.left.1 S U.left.2 hS U.hom
  let k : E.functor.obj F ≅ X := E.functor.mapIso e ≪≫ E.counitIso.app X
  let k' := (Over.forget _).mapIso k
  have sq : IsPullback k'.hom (E.functor.obj F).hom X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w k.hom).trans (Category.comp_id _).symm⟩
  exact IsAffineHom.of_isPullback sq hX

variable (D) in
/-- **The base change of the relative diagonal of `Coh_{X/Y} ⟶ 𝒮_Y` along a scheme-valued point
is an algebraic space affine over the scheme.** For a point `y = (x, x', α)` of
`Coh_{X/Y} ×_{𝒮_Y} Coh_{X/Y}` over `U`, the presheaf of vertical morphisms `x ⟶ x'` over `α` is,
after lifting universes, the presheaf that Stacks 04SG attaches to an algebraic space `H` with an
affine morphism to `U`. -/
theorem exists_relVertHomPresheaf_iso (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (Stack.twoFibreProduct B S hS (baseCFG D.Y) (coherentCFG D) (coherentCFG D)
        (coherentToBaseCFG D).hom (coherentToBaseCFG D).hom).val.obj)
    (hy : y ⋙ (Stack.twoFibreProduct B S hS (baseCFG D.Y) (coherentCFG D) (coherentCFG D)
        (coherentToBaseCFG D).hom (coherentToBaseCFG D).hom).val.p = Over.map U.hom) :
    ∃ X : Over (yoneda.obj (Over.mk U.hom) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B S hS X.left ∧ Space.IsAffineHom B S hS X.hom ∧
        Nonempty (relVertHomPresheaf (baseCFG D.Y).isFiberedInGroupoids
            (coherentCFG D).isFiberedInGroupoids hy (coherentToBaseCFG D).hom.w ⋙
              uliftFunctor.{u, u + 1} ≅
          (smallerBasePresheafEquivalence B U.left.1 S U.left.2 hS U.hom).inverse.obj X ⋙
            uliftFunctor.{u + 1, u}) := by
  let hp := (coherentCFG D).isFiberedInGroupoids
  have : (coherentCFG D).val.p.IsFibered := hp.isFibered
  let x : (coherentSiteProjection D.categoryData).Fiber U :=
    Functor.sliceValue (coherentCFG D).val.p U (Y₁' y) (h1' hy)
  let x' : (coherentSiteProjection D.categoryData).Fiber U :=
    Functor.sliceValue (coherentCFG D).val.p U (Y₂' y) (h2' hy)
  let o : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let tA' : x.1.T ⟶ x'.1.T := (y.obj o).iso.hom.down
  have htA' : tA'.left = eqToHom x.2 ≫ eqToHom (show x'.1.T.left = U from x'.2).symm := by
    have := (y.obj o).vertical
    have h := IsHomLift.fac' (baseCFG D.Y).val.p (𝟙 (y.obj o).base) (y.obj o).iso.hom
    rw [Category.id_comp, eqToHom_trans] at h
    exact h.trans (eqToHom_trans _ _).symm
  let ιi : x.1.T.left ≅ U := eqToIso x.2
  obtain ⟨H, pH, hpH, ⟨θ⟩⟩ := isAffineAlgebraicSpaceOver_pairIsom (𝟙 x.1.T) tA'
  let q : H.1 ⟶ yoneda.obj (Over.mk U.hom) := pH.hom ≫ (yoneda.mapIso ιi).hom
  refine ⟨Over.mk q, H.2, ?_, ⟨?_⟩⟩
  · exact isAffineHom_comp_iso (yoneda.mapIso ιi).hom hpH
  · have hfac : ∀ (g : Over U), (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D x =
        (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D x' →
          ∃ κ' : g.left ⟶ x.1.T.left, κ' ≫ ιi.hom = g.hom :=
      fun g _ => ⟨g.hom ≫ ιi.inv, by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
    have := isIso_relVertHomInclusion_of_faithful (baseCFG D.Y).isFiberedInGroupoids hp hy
      (coherentToBaseCFG D).hom.w
    exact Functor.isoWhiskerRight (asIso (relVertHomInclusion (baseCFG D.Y).isFiberedInGroupoids
        hp hy (coherentToBaseCFG D).hom.w) ≪≫
        Functor.vertHomPresheafIsoIsomPresheafOfFunctors (coherentCFG D).val.p hp U (Y₁' y)
          (Y₂' y) (h1' hy) (h2' hy)) uliftFunctor.{u, u + 1} ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op
        (Functor.isoWhiskerRight (Stack.isomPresheafIsoMorPresheaf
            (coherentSiteProjection D.categoryData) hp x x' ≪≫
          Functor.morPresheafIsoHomOver (coherentSiteProjection D.categoryData) x x')
          uliftFunctor.{u, u + 1} ≪≫
        (pointPresheafIso x x' ιi.hom (𝟙 x.1.T)
          ((eqToHom_trans (show x.1.T.left = U from x.2) x.2.symm).trans (eqToHom_refl _ _)).symm
          tA' pH θ htA' hfac).symm) ≪≫
      (Functor.associator _ _ _).symm

variable (D) in
/-- **The relative diagonal of `Coh_{X/Y} ⟶ 𝒮_Y` is representable by algebraic spaces.** -/
theorem isRepresentableByAlgebraicSpaces_relativeDiagonal_coherentToBaseCFG :
    Stack.IsRepresentableByAlgebraicSpaces B S hS
      (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ (coherentToBaseCFG D)).hom := by
  intro U _ _ y hy
  obtain ⟨X, hX, -, ⟨e⟩⟩ := exists_relVertHomPresheaf_iso D U y hy
  exact ⟨_, isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B U.left.1 S U.left.2 hS
      U.hom X hX,
    (nonempty_equivalenceOver_fst_iff (baseCFG D.Y).isFiberedInGroupoids
      (coherentCFG D).isFiberedInGroupoids hy (coherentToBaseCFG D).hom.w _).2 ⟨e⟩⟩

variable (D) in
/-- **The affine half of Stacks 0DLY for `Coh_{X/Y} ⟶ 𝒮_Y`**: its relative diagonal is affine in
the sense of Stacks 04XB. -/
theorem isAffineHom_relativeDiagonal_coherentToBaseCFG :
    Stack.IsAffineHom B S hS
      (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ (coherentToBaseCFG D)) := by
  intro U y hy F hF hE
  obtain ⟨X, -, haff, ⟨e⟩⟩ := exists_relVertHomPresheaf_iso D U y hy
  obtain ⟨e'⟩ := (nonempty_equivalenceOver_fst_iff (baseCFG D.Y).isFiberedInGroupoids
    (coherentCFG D).isFiberedInGroupoids hy (coherentToBaseCFG D).hom.w F).1 hE
  exact isAffineHom_smallerBasePresheafEquivalence_functor_obj X haff
    (((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1, u}).preimageIso (e'.symm ≪≫ e))

variable (D) in
/-- **The quasi-separation half of the proof of Stacks 0DLZ.** The relative diagonal of the
projection `Coh_{X/Y} ⟶ 𝒮_Y` of Stacks 08LP is representable by algebraic spaces, quasi-compact
and quasi-separated. -/
theorem relativeDiagonal_coherentToBaseCFG :
    ∃ _ : Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ (coherentToBaseCFG D)).hom,
      Stack.IsQuasiCompact B S hS
          (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ (coherentToBaseCFG D)) ∧
        Stack.IsQuasiSeparated B S hS
          (Stack.relativeDiagonal.{u, u + 1, u + 1} B S hS _ _ (coherentToBaseCFG D)) :=
  ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_coherentToBaseCFG D,
    Stack.isQuasiCompact_of_isAffineHom B S hS
      (isAffineHom_relativeDiagonal_coherentToBaseCFG D),
    Stack.isQuasiSeparated_of_isAffineHom B S hS
      (isAffineHom_relativeDiagonal_coherentToBaseCFG D)⟩

end AlgebraicGeometry.Space.CoherentSituation

end
