module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFinitePresentationStability
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitFlatProperSupport
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomRepresentableFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.SpacePointsOverScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentStackIsomEqualizer

/-!
# Isomorphism sheaves of `Coh_{X/B}` over one point of `B` are affine and of finite presentation

Let `f : X ⟶ B` be of finite presentation, and let `x`, `x'` be objects of `Coh_{X/B}` over a
scheme `U` lying over one and the same point `U ⟶ B`. Then the isomorphism sheaf `Isom(x, x')` on
`(Sch/U)_fppf` is an algebraic space over `U`, affine and of finite presentation over `U`.

## Main definitions

* `AlgebraicGeometry.Space.overSchemePointsCompIsoPointPresheaf`: the points of `H` over `U` along
  a composite `H ⟶ E ⟶ U`, as a presheaf on `(Sch/U)_fppf`.

## Main results

* `CoherentSituation.isAffineFinitePresentationAlgebraicSpaceOver_coherentEqualizerIsomFunctor`:
  over the equalizer of the base maps of two objects of `Coh_{X/B}`, the relative Isom functor is
  an algebraic space affine and of finite presentation.
* `AlgebraicGeometry.Space.CoherentSituation.isIso_coherentEqualizerMap_of_isHomLift`: over one
  point of `B` the equalizer of the two base maps is all of `U`.
* `AlgebraicGeometry.Space.CoherentSituation.coherentIsomPresheaf_affineFinitePresentation`:
  the isomorphism sheaves of `Coh_{X/B}` over one point of `B` are algebraic spaces affine and
  of finite presentation over the test scheme.

## References

* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 08W6](https://stacks.math.columbia.edu/tag/08W6)
* [Stacks Project, Tag 0DLY](https://stacks.math.columbia.edu/tag/0DLY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The points of `H` over `U` along a composite `H ⟶ E ⟶ U`.** For `p : H ⟶ E` and
`ι : E ⟶ U`, the points of `H` over `U` along `p ≫ ι`, read on `(Sch/U)_fppf`, are the sections
of `H` whose image under `p ≫ ι` is the given morphism to `U`: the presheaf
`AlgebraicGeometry.Space.CoherentSituation.pointPresheaf` read on `(Sch/U)_fppf`. -/
def overSchemePointsCompIsoPointPresheaf {U : BigFppfOver B S hS}
    {E : BigFppfOver B S hS} (ι : E ⟶ U) {H : AlgebraicSpaces B S hS}
    (p : H ⟶ (schemeSpaceFunctor B S hS).obj E) :
    overSchemePoints (p ≫ (schemeSpaceFunctor B S hS).map ι) ≅
      (Over.iteratedSliceBackward U).op ⋙
        OverShriek.fiber (𝟙 (yoneda.obj U)) (p.hom ≫ yoneda.map ι) :=
  NatIso.ofComponents
    (fun a => Equiv.toIso (Equiv.subtypeEquivRight fun s =>
      Iff.of_eq (congrArg (fun t => (p.hom ≫ yoneda.map ι).app _ s = t)
        (yonedaEquiv_yoneda_map ((Over.iteratedSliceBackward U).obj a.unop).hom))))
    (fun _ => rfl)

namespace CoherentSituation

attribute [local instance] cohCategory cohIsFibered

variable (D : CoherentSituation B S hS) {U : BigFppfOver B S hS}

/-- **The relative Isom functor over the equalizer of two objects of `Coh_{X/B}`.** For two
objects `x`, `y` of `Coh_{X/B}` over a scheme `U`, the relative Isom functor of the two pulled-back
modules over the equalizer of their two base maps is an algebraic space affine and of finite
presentation over the equalizer. -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_coherentEqualizerIsomFunctor
    (x y : (coherentSiteProjection D.categoryData).Fiber U) :
    IsAffineFinitePresentationAlgebraicSpaceOver
      ((schemeSpaceFunctor B S hS).obj (coherentEqualizer D x.1 y.1 x.2 y.2))
      (coherentEqualizerHomSituation D x.1 y.1 x.2 y.2
        (modulePullbackStabilityOfFinitePresentation B S hS)).isomFunctor := by
  let hst := modulePullbackStabilityOfFinitePresentation B S hS
  let A := coherentEqualizerObjectFst D x.1 y.1 x.2 y.2 hst
  let A' := coherentEqualizerObjectSnd D x.1 y.1 x.2 y.2 hst
  obtain ⟨_, hU, hP⟩ := A.properSupport
  obtain ⟨_, hU', hP'⟩ := A'.properSupport
  exact (coherentEqualizerHomSituation D x.1 y.1 x.2 y.2
    hst).isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation
      (D.isFinitePresentation_projection _) A.finitePresentation A'.finitePresentation A.flat
      A'.flat ⟨hU, hP⟩ ⟨hU', hP'⟩
        HomSituation.isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation

/-- Two test schemes over `B` with the same underlying scheme `U`, related by a morphism over the
identity of `U`, carry the same morphism `U ⟶ B`. -/
theorem coherentObjectPoint_eq_of_hom (A A' : CoherentObject D) (hA : A.T.left = U)
    (hA' : A'.T.left = U) (φ : A.T ⟶ A'.T) (hφ : φ.left = eqToHom hA ≫ eqToHom hA'.symm) :
    coherentObjectPoint A hA = coherentObjectPoint A' hA' := by
  unfold coherentObjectPoint
  rw [← CostructuredArrow.w φ, hφ]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc]

/-- **Over one point of `B` the equalizer is everything.** If two objects `x`, `y` of
`Coh_{X/B}` over `U` lie over the same morphism `U ⟶ B` — a morphism of their test schemes over
the identity of `U` — then the morphism from the equalizer of their base maps to `U` is an
isomorphism. -/
theorem isIso_coherentEqualizerMap_of_isHomLift
    (x y : (coherentSiteProjection D.categoryData).Fiber U)
    (φ : (coherentToBase D.categoryData).obj x.1 ⟶ (coherentToBase D.categoryData).obj y.1)
    (hφ : (baseBasedCategory D.Y).p.IsHomLift (𝟙 U) φ) :
    IsIso (coherentEqualizerMap D x.1 y.1 x.2 y.2) := by
  have hfac := IsHomLift.fac' (baseBasedCategory D.Y).p (𝟙 U) φ
  rw [Category.id_comp] at hfac
  have hpt := coherentObjectPoint_eq_of_hom D x.1 y.1 x.2 y.2 φ.down hfac
  obtain ⟨b, hb⟩ := exists_factor_pointEqualizer D.Y (coherentObjectPoint x.1 x.2).hom
    (coherentObjectPoint y.1 y.2).hom (𝟙 U) (by rw [hpt])
  have := mono_coherentEqualizerMap D x.1 y.1 x.2 y.2
  exact ⟨⟨b, (cancel_mono (coherentEqualizerMap D x.1 y.1 x.2 y.2)).1
    ((Category.assoc _ _ _).trans ((congrArg (coherentEqualizerMap D x.1 y.1 x.2 y.2 ≫ ·) hb).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))), hb⟩⟩

/-- **The isomorphism sheaves of `Coh_{X/B}` over one point of `B` are affine and of finite
presentation.** Let `f : X ⟶ B` be of finite presentation (the data `D`) and let `x`, `x'` be
objects of `Coh_{X/B}` over a scheme `U` lying over the same point `U ⟶ B`. Then the isomorphism
sheaf `Isom(x, x')` on `(Sch/U)_fppf` is an algebraic space over `U`, affine and of finite
presentation over `U`. -/
theorem coherentIsomPresheaf_affineFinitePresentation :
    letI : (coherentCFG D).val.p.IsFibered := (coherentCFG D).isFiberedInGroupoids.isFibered
    ∀ (U : BigFppfOver B S hS) (x x' : (coherentCFG D).val.p.Fiber U),
      (∃ φ : (coherentToBase D.categoryData).obj x.1 ⟶
          (coherentToBase D.categoryData).obj x'.1,
        (baseBasedCategory D.Y).p.IsHomLift (𝟙 U) φ) →
      ∃ (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
        Nonempty (G ⋙ uliftFunctor.{u + 1, u} ≅
          ((Over.iteratedSliceBackward U).op ⋙ (coherentCFG D).val.p.isomPresheaf x x') ⋙
            uliftFunctor.{u, u + 1}) ∧
        affineFinitePresentation B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)) := by
  intro U x y ⟨φ, hφ⟩
  let hst := modulePullbackStabilityOfFinitePresentation B S hS
  obtain ⟨H, p, hpa, hpf, ⟨θ⟩⟩ :=
    isAffineFinitePresentationAlgebraicSpaceOver_coherentEqualizerIsomFunctor D x y
  let ι := coherentEqualizerMap D x.1 y.1 x.2 y.2
  have : Mono (show (coherentEqualizerTestScheme D x.1 y.1 x.2 y.2).left ⟶ U from ι) :=
    mono_coherentEqualizerMap D x.1 y.1 x.2 y.2
  have : IsIso ι := isIso_coherentEqualizerMap_of_isHomLift D x y φ hφ
  let tA := coherentEqualizerToFst D x.1 y.1 x.2 y.2
  let tA' := coherentEqualizerToSnd D x.1 y.1 x.2 y.2
  have hfac : ∀ (g : Over U), (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D x =
      (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D y →
        ∃ κ' : g.left ⟶ (coherentEqualizerTestScheme D x.1 y.1 x.2 y.2).left, κ' ≫ ι = g.hom :=
    fun g hg => exists_factor_pointEqualizer D.Y (coherentObjectPoint x.1 x.2).hom
      (coherentObjectPoint y.1 y.2).hom g.hom (congrArg InducedCategory.Hom.hom hg)
  let p' : H ⟶ (schemeSpaceFunctor B S hS).obj U := p ≫ (schemeSpaceFunctor B S hS).map ι
  refine ⟨overSchemePoints p', isAlgebraicSpace_overSchemePoints p', ⟨?_⟩, ?_⟩
  · exact Functor.isoWhiskerRight (overSchemePointsCompIsoPointPresheaf ι p)
        uliftFunctor.{u + 1, u} ≪≫
      Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op
        (pointPresheafIso (T := coherentEqualizerTestScheme D x.1 y.1 x.2 y.2) x y ι tA rfl tA'
          p θ rfl hfac ≪≫
        Functor.isoWhiskerRight
          ((Functor.morPresheafIsoHomOver (coherentSiteProjection D.categoryData) x y).symm ≪≫
            (@Stack.isomPresheafIsoMorPresheaf _ _ _ _ (coherentSiteProjection D.categoryData)
              (cohIsFibered D) D.isFiberedInGroupoids_siteProjection _ x y).symm)
          uliftFunctor.{u, u + 1})
  · exact prop_algebraicSpaceMap_overSchemePoints p' (affineFinitePresentation B S hS)
      (((affineFinitePresentation B S hS).cancel_right_of_respectsIso p
        ((schemeSpaceFunctor B S hS).map ι)).2 ⟨hpa, hpf⟩)

end CoherentSituation

end AlgebraicGeometry.Space

end
