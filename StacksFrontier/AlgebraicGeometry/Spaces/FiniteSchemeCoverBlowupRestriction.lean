module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverEtaleOverDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.BlowupRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.RepresentableOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCondition2
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusDescentFlattening

/-!
# Restricting the blowup of a finite scheme cover to an open over which it is unchanged

Let `X` be an algebraic space over a scheme `S` and let `f : Y ⟶ X` be a surjective finite
morphism of finite presentation from a scheme `T = Y`, finite étale over an open subspace
`U ⊆ X`, as in clause (1) of Stacks 0GUN. Let `b : T' ⟶ T` be a `V`-admissible blowup of `T` in
a sheaf of ideals `I`, and let `U' ⊆ U` be an open subspace with `f⁻¹(|U'|) ⊆ V`.

Over `U'` the blowup changes nothing: `b` is an isomorphism over `V`, every morphism to `T`
which factors through `T ×_X U'` lands in `V`, and therefore `T' ×_X U' ⟶ T ×_X U'` is an
isomorphism. The base change `T ×_X U' ⟶ U'` of the finite étale `T ×_X U ⟶ U` is finite, flat
and locally of finite presentation, hence finite locally free, and so is `T' ×_X U' ⟶ U'`. On
points, every point of `|U'|` comes from `T` by surjectivity of `f`, from a point lying in `V`,
over which `b` is bijective; so `|U'|` lies in the image of `T' ⟶ X`. These are the two facts
about the cover `T' ⟶ X` used in the proof of Stacks 0GV5.

## Main results

* `Stacks.Blowup.IsAdmissibleBlowup.isIso_morphismRestrict`: a `U`-admissible blowup is an
  isomorphism over `U`.
* `AlgebraicGeometry.Space.isIso_pullback_snd_yoneda_map_openSubHom`: a morphism of the site
  which is an isomorphism over an open `O` has an isomorphism as base change, on represented
  presheaves, along the inclusion of `O`.
* `AlgebraicGeometry.Space.IsFiniteSchemeCoverFiniteEtaleOverDenseOpen.isFiniteLocallyFree_blowUp`:
  `T' ×_X U' ⟶ U'` is finite locally free.
* `AlgebraicGeometry.Space.IsFiniteSchemeCoverFiniteEtaleOverDenseOpen.subset_range_blowUp`:
  `|U'|` lies in the image of `|T'| ⟶ |X|`.

## References

* [Stacks Project, Tag 0GUN](https://stacks.math.columbia.edu/tag/0GUN)
* [Stacks Project, Tag 0GV5](https://stacks.math.columbia.edu/tag/0GV5)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

open AlgebraicGeometry in
/-- **A `U`-admissible blowup is an isomorphism over `U`.** The centre is disjoint from `U`, and
the blowup is an isomorphism off its centre (Stacks 02OS). -/
theorem Stacks.Blowup.IsAdmissibleBlowup.isIso_morphismRestrict {X X' : Scheme.{u}}
    {U : X.Opens} {f : X' ⟶ X} (h : Stacks.Blowup.IsAdmissibleBlowup U f) :
    IsIso (f ∣_ U) := by
  obtain ⟨I, -, hdisj, e, he⟩ := (Stacks.Blowup.isAdmissibleBlowup_iff U f).1 h
  have h₁ := isIso_blowUpToBase_morphismRestrict I hdisj
  rw [← he, morphismRestrict_comp]
  exact IsIso.comp_isIso'
    (inferInstanceAs (IsIso (e.hom ∣_ AlgebraicGeometry.blowUpToBase I ⁻¹ᵁ U))) h₁

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- If the second projection of a pullback square is an isomorphism, so is that of the
chosen pullback. -/
private theorem isIso_pullback_snd_of_isPullback {C : Type*} [Category C] {P X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullback f g]
    (h : IsPullback fst snd f g) [IsIso snd] : IsIso (pullback.snd f g) := by
  rw [← h.isoPullback_inv_snd]
  infer_instance

/-- **Base change of a morphism which is an isomorphism over an open.** Let `q : P ⟶ Q` be a
morphism of the site whose underlying morphism of schemes is an isomorphism over an open `O` of
`Q`. Then the base change of `h_q : h_P ⟶ h_Q` along the inclusion `h_O ⟶ h_Q` is an
isomorphism. -/
theorem isIso_pullback_snd_yoneda_map_openSubHom {P Q : BigFppfOver B S hS} (q : P ⟶ Q)
    (O : ((BigFppfOver.toScheme B S hS).obj Q).Opens)
    (hq : IsIso ((BigFppfOver.toScheme B S hS).map q ∣_ O)) :
    IsIso (pullback.snd (yoneda.map q) (yoneda.map (openSubHom Q O))) := by
  have hsq := (isPullback_stage B S hS q (openSubHom Q O)).map yoneda
  have : IsIso ((BigFppfOver.toScheme B S hS).map (stageSnd B S hS q (openSubHom Q O))) := by
    have h₁ : IsPullback ((BigFppfOver.toScheme B S hS).map q ⁻¹ᵁ O).ι
        ((BigFppfOver.toScheme B S hS).map q ∣_ O) ((BigFppfOver.toScheme B S hS).map q)
        ((BigFppfOver.toScheme B S hS).map (openSubHom Q O)) := by
      rw [toScheme_map_openSubHom B S hS]
      exact (isPullback_morphismRestrict _ O).flip
    have := hq
    have h₂ := isIso_pullback_snd_of_isPullback h₁
    exact h₂
  have : IsIso (stageSnd B S hS q (openSubHom Q O)) :=
    isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  exact isIso_pullback_snd_of_isPullback hsq

/-- **Over an open subspace `U' ≤ U` whose points in `T` lie in `V`, the blowup of a finite
scheme cover is finite locally free.** Let `f : h_T ⟶ X` be finite étale over the open subspace
`U`, as in clause (1) of Stacks 0GUN, let `T' ⟶ T` be a `V`-admissible blowup of `T` in `I`, and
let `U' ≤ U` be an open subspace such that every point of `T` over `|U'|` lies in `V`. Then the
base change `T' ×_X U' ⟶ U'` of the composite `T' ⟶ T ⟶ X` is finite locally free.

Indeed `T' ×_X U' ⟶ T ×_X U'` is an isomorphism, because `T ×_X U' ⟶ T` factors through `V`,
over which the blowup is an isomorphism; and `T ×_X U' ⟶ U'` is a base change of the finite étale
`T ×_X U ⟶ U`, so it is finite, flat and locally of finite presentation. -/
theorem IsFiniteSchemeCoverFiniteEtaleOverDenseOpen.isFiniteLocallyFree_blowUp
    {X : AlgebraicSpaces B S hS} {Y : BigFppfOver B S hS} {f : yoneda.obj Y ⟶ X.1}
    {U : Subfunctor X.1} (hf : IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS Y f U)
    {I : ((BigFppfOver.toScheme B S hS).obj Y).IdealSheafData}
    {V : ((BigFppfOver.toScheme B S hS).obj Y).Opens}
    (hI : Stacks.Blowup.IsAdmissibleBlowup V (_root_.AlgebraicGeometry.blowUpToBase I))
    {U' : Subfunctor X.1} (hU'open : IsOpenSubspace B S hS U') (hU'U : U' ≤ U)
    (hU'V : ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
      pointsMap B S hS _ f ((schemePointsHomeomorph B S hS Y).symm y) ∈
        subspacePointSet B S hS X.1 U' → y ∈ V) :
    IsFiniteLocallyFree B S hS
      (ObjectProperty.homMk (pullback.snd
          (schemeSpaceMap (blowUpObjHom Y I) ≫ ObjectProperty.homMk f :
            schemeSpace (blowUpObj Y I) ⟶ X).hom U'.ι) :
        AlgebraicSpaces.fiberProduct B S hS
            (schemeSpaceMap (blowUpObjHom Y I) ≫ ObjectProperty.homMk f :
              schemeSpace (blowUpObj Y I) ⟶ X)
            (ObjectProperty.homMk U'.ι : (⟨U'.toFunctor, hU'open.1⟩ : AlgebraicSpaces B S hS) ⟶ X) ⟶
          ⟨U'.toFunctor, hU'open.1⟩) := by
  obtain ⟨-, -, -, hU, -, -, hUfin, hUet⟩ := hf
  set β := yoneda.map (blowUpObjHom Y I)
  set jV := openSubHom Y V
  -- The base change of the blowup along `V ⊆ T` is an isomorphism.
  have hbc : IsIso (pullback.snd β (yoneda.map jV)) :=
    isIso_pullback_snd_yoneda_map_openSubHom B S hS _ V hI.isIso_morphismRestrict
  -- `T ×_X U' ⟶ T` factors through `V`.
  have hmono : Mono (yoneda.map jV) := by
    have : Mono jV := (BigFppfOver.toScheme B S hS).mono_of_mono_map (by
      rw [toScheme_map_openSubHom B S hS]
      exact inferInstanceAs (Mono V.ι))
    exact Functor.map_mono yoneda _
  have hpts : ∀ w : points B S hS (pullback f U'.ι),
      pointsToScheme B S hS Y (pointsMap B S hS _ (pullback.fst f U'.ι) w) ∈ V := by
    intro w
    refine hU'V _ ?_
    rw [← schemePointsHomeomorph_apply, Homeomorph.symm_apply_apply, ← pointsMap_comp_apply,
      pullback.condition, pointsMap_comp_apply]
    exact ⟨_, rfl⟩
  have hle : Subfunctor.range (pullback.fst f U'.ι) ≤ Subfunctor.range (yoneda.map jV) := by
    rw [← openSubspaceOfPoints_preimage_pointsToScheme Y V]
    rintro Z _ ⟨x, rfl⟩
    rintro _ ⟨p, rfl⟩
    have hy : (yonedaEquiv.symm ((pullback.fst f U'.ι).app Z x) : yoneda.obj Z.unop ⟶ _) =
        yonedaEquiv.symm x ≫ pullback.fst f U'.ι := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    show pointsToScheme B S hS Y (pointsMap B S hS _
      (yonedaEquiv.symm ((pullback.fst f U'.ι).app Z x)) p) ∈ V
    rw [hy, pointsMap_comp_apply]
    exact hpts _
  set g : pullback f U'.ι ⟶ yoneda.obj (openSub Y V) :=
    Subfunctor.lift (pullback.fst f U'.ι) hle ≫ inv (Subfunctor.toRange (yoneda.map jV))
  have hg : g ≫ yoneda.map jV = pullback.fst f U'.ι := by
    have h : inv (Subfunctor.toRange (yoneda.map jV)) ≫ yoneda.map jV =
        (Subfunctor.range (yoneda.map jV)).ι := by
      rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
    simp only [g, Category.assoc]
    rw [h, Subfunctor.lift_ι]
  -- Hence `T' ×_X U' ⟶ T ×_X U'` is an isomorphism.
  set φ : pullback (β ≫ f) U'.ι ⟶ pullback f U'.ι :=
    pullback.lift (pullback.fst _ _ ≫ β) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition])
  have hφ₁ : IsPullback φ (pullback.fst (β ≫ f) U'.ι) (pullback.fst f U'.ι) β :=
    IsPullback.of_right (h₁₂ := pullback.snd f U'.ι) (h₂₂ := f) (v₁₃ := U'.ι)
      (by rw [pullback.lift_snd]; exact (IsPullback.of_hasPullback _ _).flip)
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f U'.ι).flip
  set k : pullback (β ≫ f) U'.ι ⟶ pullback β (yoneda.map jV) :=
    pullback.lift (pullback.fst _ _) (φ ≫ g)
      (by rw [Category.assoc, hg, ← hφ₁.w])
  have hφ₂ : IsPullback k φ (pullback.snd β (yoneda.map jV)) g :=
    IsPullback.of_right (h₁₂ := pullback.fst β (yoneda.map jV)) (h₂₂ := yoneda.map jV)
      (v₁₃ := β) (by rw [pullback.lift_fst, hg]; exact hφ₁.flip) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
  have hφ : IsIso φ :=
    (MorphismProperty.isomorphisms _).of_isPullback hφ₂ hbc
  -- `T ×_X U' ⟶ U'` is the base change of the finite étale `T ×_X U ⟶ U`.
  have hYalg := AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Y
  have hPU := isAlgebraicSpace_pullback B S hS U.ι f hU.1 hYalg X.2
  have hflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst U.ι f) :=
    (isFiniteLocallyFree_presheaf_iff B S hS hPU hU.1 _).2
      ⟨hUfin, isFlat_of_isEtale B S hS hUet, isLocallyOfFinitePresentation_of_isEtale B S hS hUet⟩
  set m : pullback f U'.ι ⟶ pullback U.ι f :=
    pullback.lift (pullback.snd _ _ ≫ Subfunctor.homOfLe hU'U) (pullback.fst _ _)
      (by rw [Category.assoc, Subfunctor.homOfLe_ι, pullback.condition])
  have hm : IsPullback m (pullback.snd f U'.ι) (pullback.fst U.ι f)
      (Subfunctor.homOfLe hU'U) :=
    IsPullback.of_right (h₁₂ := pullback.snd U.ι f) (h₂₂ := U.ι) (v₁₃ := f)
      (by rw [pullback.lift_snd, Subfunctor.homOfLe_ι]; exact IsPullback.of_hasPullback _ _)
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback U.ι f).flip
  have hflf' := (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hm hflf
  have hcomp : pullback.snd (β ≫ f) U'.ι = φ ≫ pullback.snd f U'.ι :=
    (pullback.lift_snd _ _ _).symm
  refine (isFiniteLocallyFree_presheaf_iff_isFiniteLocallyFree B S hS _).1 ?_
  show (MorphismProperty.inverseImage _ _).presheaf (pullback.snd (β ≫ f) U'.ι)
  rw [hcomp]
  exact MorphismProperty.RespectsIso.precomp _ φ _ hflf'

/-- **Over an open subspace `U'` whose points in `T` lie in `V`, every point is in the image of
the blowup of a finite scheme cover.** Let `f : h_T ⟶ X` be surjective, as in clause (1) of
Stacks 0GUN, let `T' ⟶ T` be a `V`-admissible blowup of `T` in `I`, and let `U'` be a subspace
such that every point of `T` over `|U'|` lies in `V`. Then `|U'|` lies in the image of
`|T'| ⟶ |X|`: a point of `|U'|` comes from a point of `T`, which lies in `V`, over which the
blowup is an isomorphism. -/
theorem IsFiniteSchemeCoverFiniteEtaleOverDenseOpen.subset_range_blowUp
    {X : AlgebraicSpaces B S hS} {Y : BigFppfOver B S hS} {f : yoneda.obj Y ⟶ X.1}
    {U : Subfunctor X.1} (hf : IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS Y f U)
    {I : ((BigFppfOver.toScheme B S hS).obj Y).IdealSheafData}
    {V : ((BigFppfOver.toScheme B S hS).obj Y).Opens}
    (hI : Stacks.Blowup.IsAdmissibleBlowup V (_root_.AlgebraicGeometry.blowUpToBase I))
    {U' : Subfunctor X.1}
    (hU'V : ∀ y : (BigFppfOver.toScheme B S hS).obj Y,
      pointsMap B S hS _ f ((schemePointsHomeomorph B S hS Y).symm y) ∈
        subspacePointSet B S hS X.1 U' → y ∈ V) :
    subspacePointSet B S hS X.1 U' ⊆
      Set.range (pointsMap B S hS _
        (schemeSpaceMap (blowUpObjHom Y I) ≫ ObjectProperty.homMk f :
          schemeSpace (blowUpObj Y I) ⟶ X).hom) := by
  intro x hx
  obtain ⟨p, rfl⟩ := hf.1 x
  set e := schemePointsHomeomorph B S hS Y
  have hpV : e p ∈ V := hU'V (e p) (by rwa [e.symm_apply_apply])
  have := hI.isIso_morphismRestrict
  obtain ⟨z, hz⟩ := (_root_.AlgebraicGeometry.blowUpToBase I ∣_ V).surjective ⟨e p, hpV⟩
  have hbz : _root_.AlgebraicGeometry.blowUpToBase I
      ((_root_.AlgebraicGeometry.blowUpToBase I ⁻¹ᵁ V).ι z) = e p := by
    rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply, hz]
    rfl
  let w : (BigFppfOver.toScheme B S hS).obj (blowUpObj Y I) :=
    (_root_.AlgebraicGeometry.blowUpToBase I ⁻¹ᵁ V).ι z
  have hw : (BigFppfOver.toScheme B S hS).map (blowUpObjHom Y I) w = e p := hbz
  refine ⟨(schemePointsHomeomorph B S hS (blowUpObj Y I)).symm w, ?_⟩
  show pointsMap B S hS _ (yoneda.map (blowUpObjHom Y I) ≫ f) _ = _
  rw [pointsMap_comp_apply, schemePointsHomeomorph_symm_naturality, hw, e.symm_apply_apply]

end AlgebraicGeometry.Space

end
