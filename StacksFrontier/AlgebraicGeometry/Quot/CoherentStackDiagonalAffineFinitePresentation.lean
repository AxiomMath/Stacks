module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackValuativeExistence
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomRepresentableFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseCohomology
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentStackIsomEqualizer
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedFibered
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
/-!
# The diagonal of `Coh_{X/B}` over `B` is affine and of finite presentation

Let `f : X ⟶ B` be a morphism of algebraic spaces over `S` of finite presentation, the standing
data of Stacks 08KB, and let `𝒳 = Coh_{X/B}`. The diagonal `𝒳 ⟶ 𝒳 ×_B 𝒳` of `𝒳` over `B` is
representable by algebraic spaces, affine and of finite presentation (Stacks 0DLY). Its base
change along a scheme-valued point `(x, x')` of `𝒳 ×_B 𝒳` over `U` is the isomorphism sheaf
`Isom_𝒳(x, x')` of two objects over one point `g : U ⟶ B`; over the equalizer `E` of the two base
maps, which here is `U` itself, it is the relative isomorphism functor `Isom(ℱ, ℱ')` of the two
modules on `X_U` (Stacks 08W6), an algebraic space affine and of finite presentation over `U` by
Proposition 08K9, itself from Stacks 08K6 for the four relative Hom functors.

Consequently the projection `Coh_{X/B} ⟶ B` is quasi-separated: an affine morphism of algebraic
spaces is quasi-compact and quasi-separated.

## Main results

All in the namespace `AlgebraicGeometry.Space.CoherentSituation`.

* `isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_coherentEqualizer`: Proposition 08K9
  for the two modules over the equalizer of two objects of `Coh_{X/B}`.
* `exists_isAlgebraicSpace_isomPresheaf_affineFinitePresentation`: the isomorphism sheaf of two
  objects of `Coh_{X/B}` over one point of `B` is an algebraic space affine and of finite
  presentation over the base scheme.
* `coherentRelativeDiagonal_affine_finitePresentation`: the diagonal of `Coh_{X/B}` over `B` is
  representable by algebraic spaces, affine and of finite presentation (Stacks 0DLY).
* `isFiberedQuasiSeparated_toBaseCFG`: the projection `Coh_{X/B} ⟶ B` is quasi-separated.
* `isAlgebraicSpaceIsomPresheaf_coherentCFG`: the isomorphism presheaves of `Coh_{X/B}` are
  algebraic spaces (Stacks 08W6).

## References

* [Stacks Project, Tag 0DLY](https://stacks.math.columbia.edu/tag/0DLY)
* [Stacks Project, Tag 08W6](https://stacks.math.columbia.edu/tag/08W6)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

attribute [local instance] cohCategory cohIsFibered

/-- **Proposition 08K9 over the equalizer of two objects of `Coh_{X/B}`.** For two objects `x`,
`x'` of `Coh_{X/B}` over a scheme `U`, the relative isomorphism functor of the two modules over
the equalizer of their base maps is an algebraic space affine and of finite presentation over the
equalizer: the base change of `f` is of finite presentation and the two modules are of finite
presentation, flat, with proper support, so Proposition 08K9 applies, with the four relative Hom
functors it uses supplied by Stacks 08K6. -/
theorem isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_coherentEqualizer
    {U : BigFppfOver B S hS} (x x' : (coherentSiteProjection D.categoryData).Fiber U) :
    IsAffineFinitePresentationAlgebraicSpaceOver
      ((schemeSpaceFunctor B S hS).obj (coherentEqualizer D x.1 x'.1 x.2 x'.2))
      (coherentEqualizerHomSituation D x.1 x'.1 x.2 x'.2
        (modulePullbackStabilityOfFinitePresentation B S hS)).isomFunctor := by
  let hst := modulePullbackStabilityOfFinitePresentation B S hS
  let A := coherentEqualizerObjectFst D x.1 x'.1 x.2 x'.2 hst
  let A' := coherentEqualizerObjectSnd D x.1 x'.1 x.2 x'.2 hst
  obtain ⟨_, hU, hP⟩ := A.properSupport
  obtain ⟨_, hU', hP'⟩ := A'.properSupport
  exact (coherentEqualizerHomSituation D x.1 x'.1 x.2 x'.2 hst)
    |>.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation
      (D.isFinitePresentation_projection _) A.finitePresentation A'.finitePresentation A.flat
      A'.flat ⟨hU, hP⟩ ⟨hU', hP'⟩ fun s' hfp' hF' hG' hflat' hsupp' =>
        s'.isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation hfp' hF' hG'
          hflat' hsupp'

/-- **The isomorphism sheaf of two objects of `Coh_{X/B}` over one point of `B`.** Let `x`, `x'`
be objects of `Coh_{X/B}` over a scheme `U` with the same morphism `U ⟶ B`. The isomorphism sheaf
`Isom(x, x')`, read on the schemes over `U`, is an algebraic space over `U`, affine and of finite
presentation over `U`.

The equalizer `E ⟶ U` of the two base maps is a monomorphism through which the identity of `U`
factors, hence an isomorphism. Over `E` the isomorphism sheaf is the relative isomorphism functor
of the two modules, represented by an algebraic space `H` affine and of finite presentation over
`E` (Proposition 08K9); read over `U` it is the algebraic space of Stacks 04SG attached to
`H ⟶ E ≅ U`, whose structure morphism is `H ⟶ E ≅ U`. -/
theorem exists_isAlgebraicSpace_isomPresheaf_affineFinitePresentation
    {U : BigFppfOver B S hS} (x x' : (coherentSiteProjection D.categoryData).Fiber U)
    (hpt : coherentFiberPoint D x = coherentFiberPoint D x') :
    ∃ (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
      Nonempty (G ⋙ uliftFunctor.{u + 1, u} ≅
        ((Over.iteratedSliceBackward U).op ⋙
          (coherentSiteProjection D.categoryData).isomPresheaf x x') ⋙ uliftFunctor.{u, u + 1}) ∧
      affineFinitePresentation B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)) := by
  obtain ⟨H, p, hpA, hpF, ⟨θ⟩⟩ :=
    D.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_coherentEqualizer x x'
  let ι := coherentEqualizerMap D x.1 x'.1 x.2 x'.2
  have : Mono (show (coherentEqualizerTestScheme D x.1 x'.1 x.2 x'.2).left ⟶ U from ι) :=
    mono_coherentEqualizerMap D x.1 x'.1 x.2 x'.2
  let tA := coherentEqualizerToFst D x.1 x'.1 x.2 x'.2
  let tA' := coherentEqualizerToSnd D x.1 x'.1 x.2 x'.2
  have hfac : ∀ (g : Over U), (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D x =
      (schemeSpaceFunctor B S hS).map g.hom ≫ coherentFiberPoint D x' →
        ∃ κ' : g.left ⟶ (coherentEqualizerTestScheme D x.1 x'.1 x.2 x'.2).left, κ' ≫ ι = g.hom :=
    fun g hg => exists_factor_pointEqualizer D.Y (coherentObjectPoint x.1 x.2).hom
      (coherentObjectPoint x'.1 x'.2).hom g.hom (congrArg InducedCategory.Hom.hom hg)
  obtain ⟨κ, hκ⟩ := hfac (Over.mk (𝟙 U)) (by rw [hpt])
  have : Mono ι := mono_coherentEqualizerMap D x.1 x'.1 x.2 x'.2
  have : IsSplitEpi ι := IsSplitEpi.mk' ⟨κ, hκ⟩
  have : IsIso ι := isIso_of_mono_of_isSplitEpi ι
  have : IsIso ((schemeSpaceFunctor B S hS).map ι) := Functor.map_isIso _ ι
  let G := (Over.iteratedSliceBackward U).op ⋙
    pointPresheaf (T := coherentEqualizerTestScheme D x.1 x'.1 x.2 x'.2) ι p
  let q : H ⟶ schemeSpace U := p ≫ (schemeSpaceFunctor B S hS).map ι
  have hq : affineFinitePresentation B S hS q :=
    MorphismProperty.RespectsIso.postcomp (affineFinitePresentation B S hS)
      ((schemeSpaceFunctor B S hS).map ι) p ⟨hpA, hpF⟩
  refine ⟨G,
    isAlgebraicSpace_pointPresheaf (T := coherentEqualizerTestScheme D x.1 x'.1 x.2 x'.2) ι p,
    ⟨?_⟩, ?_⟩
  · exact Functor.isoWhiskerLeft (Over.iteratedSliceBackward U).op
      (pointPresheafIso (T := coherentEqualizerTestScheme D x.1 x'.1 x.2 x'.2) x x' ι tA rfl
        tA' p θ rfl hfac ≪≫
        Functor.isoWhiskerRight ((Functor.morPresheafIsoHomOver
          (coherentSiteProjection D.categoryData) x x').symm ≪≫
          (@Stack.isomPresheafIsoMorPresheaf _ _ _ _ (coherentSiteProjection D.categoryData)
            (cohIsFibered D) D.isFiberedInGroupoids_siteProjection _ x x').symm)
          uliftFunctor.{u, u + 1})
  · rw [Stack.prop_algebraicSpaceMap_iff B S hS (affineFinitePresentation B S hS)]
    let e : (OverShriek.relocalizePresheafFunctor U.hom).obj G ≅ H.1 :=
      relocalizeSpaceOverSmallerBaseIso B U.left.1 S U.left.2 hS U.hom H q.hom
    have he : e.hom ≫ q.hom = OverShriek.relocalizeToYoneda U.hom G :=
      relocalizeSpaceOverSmallerBaseIso_hom_comp B U.left.1 S U.left.2 hS U.hom H q.hom
    refine ((affineFinitePresentation B S hS).arrow_mk_iso_iff ?_).2 hq
    refine Arrow.isoMk (ObjectProperty.isoMk _ e) (Iso.refl _) ?_
    exact ObjectProperty.hom_ext _ (he.trans (Category.comp_id _).symm)

/-- Two objects of `Coh_{X/B}` over `U` whose images in `𝒮_B` are related by a morphism over the
identity of `U` have the same morphism `U ⟶ B`. -/
theorem coherentFiberPoint_eq_of_isHomLift {U : BigFppfOver B S hS}
    (x x' : (coherentSiteProjection D.categoryData).Fiber U)
    (φ : (coherentToBase D.categoryData).obj x.1 ⟶ (coherentToBase D.categoryData).obj x'.1)
    (hφ : (baseBasedCategory D.Y).p.IsHomLift (𝟙 U) φ) :
    coherentFiberPoint D x = coherentFiberPoint D x' := by
  have hfac := IsHomLift.fac' (baseBasedCategory D.Y).p (𝟙 U) φ
  have hw : (schemeSpaceFunctor B S hS).map φ.down.left ≫ x'.1.T.hom = x.1.T.hom :=
    CostructuredArrow.w φ.down
  change φ.down.left = _ at hfac
  change (schemeSpaceFunctor B S hS).map (eqToHom x.2.symm) ≫ x.1.T.hom =
    (schemeSpaceFunctor B S hS).map (eqToHom x'.2.symm) ≫ x'.1.T.hom
  rw [← hw, hfac]
  simp only [Category.id_comp, eqToHom_trans]
  exact ((schemeSpaceFunctor B S hS).map_comp_assoc _ _ _).symm.trans
    (congrArg (fun k => (schemeSpaceFunctor B S hS).map k ≫ _) (eqToHom_trans _ _))


/-- **The diagonal of `Coh_{X/B}` over `B` is affine and of finite presentation** (Stacks 0DLY).
The relative diagonal of the projection `Coh_{X/B} ⟶ 𝒮_B` is representable by algebraic spaces,
and every algebraic space representing one of its base changes along a scheme-valued point over
`U` is affine and of finite presentation over `U`: that base change is the isomorphism sheaf of
two objects over one point of `B`
(`exists_isAlgebraicSpace_isomPresheaf_affineFinitePresentation`). -/
@[stacks 0DLY]
theorem coherentRelativeDiagonal_affine_finitePresentation :
    ∃ _hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS
        (Stack.relativeDiagonalBasedFunctor B S hS (coherentCFG D) (baseCFG D.Y)
          (coherentToBase D.categoryData)),
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (Stack.twoFibreProduct B S hS (baseCFG D.Y) (coherentCFG D) (coherentCFG D)
            (coherentToBase D.categoryData) (coherentToBase D.categoryData)).val.obj)
        (_hy : y ⋙ (Stack.twoFibreProduct B S hS (baseCFG D.Y) (coherentCFG D) (coherentCFG D)
            (coherentToBase D.categoryData) (coherentToBase D.categoryData)).val.p =
          Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) (coherentCFG D).val.p
            (Stack.twoFibreProduct B S hS (baseCFG D.Y) (coherentCFG D) (coherentCFG D)
              (coherentToBase D.categoryData) (coherentToBase D.categoryData)).val.p y
            (Stack.relativeDiagonalBasedFunctor B S hS (coherentCFG D) (baseCFG D.Y)
              (coherentToBase D.categoryData)).toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        IsAffineHom B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom ∧
          IsFinitePresentation B S hS (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
  coherentRelativeDiagonal_affine_finitePresentation_of_isom D (baseCFG D.Y).isFiberedInGroupoids
    fun _ x x' ⟨φ, hφ⟩ =>
      D.exists_isAlgebraicSpace_isomPresheaf_affineFinitePresentation x x'
        (D.coherentFiberPoint_eq_of_isHomLift x x' φ hφ)

/-- **The projection `Coh_{X/B} ⟶ B` is quasi-separated**: its relative diagonal is representable
by algebraic spaces and affine (Stacks 0DLY), and an affine morphism of algebraic spaces is
quasi-compact and quasi-separated. -/
theorem isFiberedQuasiSeparated_toBaseCFG :
    Stack.IsFiberedQuasiSeparated.{u, u + 1, u + 1} B S hS D.toBaseCFG := by
  obtain ⟨hrep, haff⟩ := D.coherentRelativeDiagonal_affine_finitePresentation
  exact Stack.IsFiberedQuasiSeparated.of_isAffineHom_relativeDiagonal hrep
    fun U y hy F hF hE => (haff U y hy F hF hE).1

/-- **The isomorphism presheaves of `Coh_{X/B}` are algebraic spaces** (Stacks 08W6, in the form
of condition (2) of Stacks 045G): over the equalizer of the two base maps of two objects over a
scheme, the isomorphism presheaf is the relative isomorphism functor of the two modules, an
algebraic space by Proposition 08K9. -/
theorem isAlgebraicSpaceIsomPresheaf_coherentCFG :
    Stack.IsAlgebraicSpaceIsomPresheaf B S hS (coherentCFG D) :=
  D.coherentCFG_isAlgebraicSpaceIsomPresheaf fun _ x y => by
    obtain ⟨H, p, -, -, hθ⟩ :=
      D.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_coherentEqualizer x y
    exact ⟨H, p, hθ⟩

end AlgebraicGeometry.Space.CoherentSituation

end
