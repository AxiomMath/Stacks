module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceOfAlgebraicSpace
import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAffineMcQuillan
import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationOutputQuasiCompact
import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactZariskiLocalTarget

/-!
# Quasi-compactness of a modification and of its completion

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a locally Noetherian algebraic
space over `S`, let `T ⊆ |X|` be a closed subset and let `U ⊂ X` be the open subspace with
`|U| = |X| ∖ T`. **Stacks 0ARU** says that a morphism `f : X' ⟶ X` of algebraic spaces which is
locally of finite type and an isomorphism over `U` is quasi-compact exactly when the
corresponding morphism `g : W ⟶ X_{/T}` of formal algebraic spaces is quasi-compact, where
under the completion functor of Stacks 0AR5 the morphism `g` corresponding to `f` is
`f_{/T} : X'_{/T'} ⟶ X_{/T}` up to isomorphism over `X_{/T}`.

## Main results

* `AlgebraicGeometry.FormalSpace.isQuasiCompact_completionSheafMap_of_isQuasiCompact`: if `f` is
  quasi-compact then `f_{/T}` is quasi-compact in the sense of Stacks 0AJC, for an arbitrary
  morphism of algebraic spaces and an arbitrary set of points.
* `AlgebraicGeometry.FormalSpace.isQuasiCompact_of_isQuasiCompact_completionSheafMap`: the
  converse, for a morphism which is an isomorphism over `U` and a locally Noetherian `X`.
* `AlgebraicGeometry.FormalSpace.isQuasiCompact_iff_isQuasiCompact_of_overIso`:
  **Stacks 0ARU**.

## Implementation notes

*Quasi-compactness of `g`* is the notion of Stacks 0AJC,
`AlgebraicGeometry.FormalSpace.IsQuasiCompact`: every fibre product of `g` with an affine
scheme of the site is a quasi-compact formal algebraic space. By the completion square of
Stacks 0APV such a fibre product of `f_{/T}` is the universe lift of the fibre product
`T₀ ×_X X'` of algebraic spaces, so the two notions of a quasi-compact space are compared on an
algebraic space through
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceOfAlgebraicSpace`. The forward
direction is then Stacks 0GDE read in the form of Stacks 0AJC.

*The converse* follows the source. Quasi-compactness of `f` is étale local on the target
(Stacks 03KG), and Zariski local on a scheme chart of the target, so it suffices to treat the
base change of `f` to an affine scheme `Spec A` étale over `X`, where `A` is Noetherian. There
the inverse image of `T` is `V(I)` for an ideal `I`, the base change `X'_A` is an isomorphism
over the complement of `V(I)`, which is covered by finitely many basic opens `D(s)` since `I`
is finitely generated, and over `Spec (A ⧸ I)` it is the fibre product of `f_{/T}` with the
affine scheme `Spec (A ⧸ I)` mapping to `X_{/T}`, which is quasi-compact by hypothesis. So
`X'_A` is covered by finitely many quasi-compact pieces. The source passes instead through
Stacks 0GDQ, the compatibility of the completion functor with base change, and the reduction
`W_{red}` of the completion; neither is needed here, the closed subscheme `Spec (A ⧸ I)`
playing the role of `W_{red}`.

*The correspondence.* Stacks 0ARB, that the completion functor of Stacks 0AR5 is an
equivalence, is not available in this library, so "`g` corresponds to `f`" is read through the
functor itself: `g` is isomorphic over `X_{/T}` to the completion `f_{/T}`, which is the value
of `AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor` at `f`
(`AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor_comp_ι`). Every object
isomorphic to the image of `f` under the functor is of this form.

## References

* [Stacks Project, Tag 0ARU](https://stacks.math.columbia.edu/tag/0ARU)
* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0AR5](https://stacks.math.columbia.edu/tag/0AR5)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0GDE](https://stacks.math.columbia.edu/tag/0GDE)
* [Stacks Project, Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search for them times out
under Lean v4.35.0). -/
local instance (priority := high) hasPullbacks_presheaf_CompletionQuasiCompactIff :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  CategoryTheory.Limits.functorCategoryHasLimitsOfShape

/-- The pullback of two morphisms of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_CompletionQuasiCompactIff
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Fibre products of a completion morphism with schemes -/

/-- A fibre product of the completion `f_{/T} : X'_{/T'} ⟶ X_{/T}` with a scheme `T₀` of the
site mapping to `X_{/T}` is the universe lift of the fibre product `T₀ ×_X X'` of algebraic
spaces, where `ζ : h_{T₀} ⟶ X` is the composite of the given morphism with `X_{/T} ⟶ X`. This
is the completion square of Stacks 0APV pasted with the given cartesian square. -/
theorem nonempty_iso_pullback_of_isPullback_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X)) {T₀ : BigFppfOver B S hS}
    (g : yonedaSheaf B S hS T₀ ⟶ Space.completionSheaf B S hS X T) (ζ : yoneda.obj T₀ ⟶ X)
    (hζ : (g ≫ Space.completionSheafInclusion B S hS X T).hom ≫
        (Space.sheafifiedULiftIso B S hS X hX.isSheaf).inv =
      Functor.whiskerRight ζ uliftFunctor.{u + 1})
    {W : FppfSheaf B S hS} {p : W ⟶ yonedaSheaf B S hS T₀}
    {q : W ⟶ Space.completionSheaf B S hS X' (Space.pointsMap B S hS X' f ⁻¹' T)}
    (sq : IsPullback p q g (Space.completionSheafMap B S hS f T)) :
    Nonempty (W.obj ≅ pullback ζ f ⋙ uliftFunctor.{u + 1}) := by
  let H := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}
  let eX := Space.sheafifiedULiftIso B S hS X hX.isSheaf
  let eX' := Space.sheafifiedULiftIso B S hS X' hX'.isSheaf
  have hbig := (sq.flip.paste_horiz (Space.isPullback_completionSheafMap B S hS f T)).map
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have hcomm : (Space.sheafifiedULiftMap B S hS f).hom ≫ eX.inv = eX'.inv ≫ H.map f := by
    rw [← cancel_epi eX'.hom, Iso.hom_inv_id_assoc, ← Category.assoc,
      ← Space.whiskerRight_comp_sheafifiedULiftIso_hom B S hS hX'.isSheaf hX.isSheaf f,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have hp : IsPullback
      ((q ≫ Space.completionSheafInclusion B S hS X' _).hom ≫ eX'.inv) p.hom (H.map f)
      ((g ≫ Space.completionSheafInclusion B S hS X T).hom ≫ eX.inv) :=
    IsPullback.of_iso hbig (Iso.refl _) eX'.symm (Iso.refl _) eX.symm
      (by simp) (by simp) hcomm (by simp)
  have hpbζ := (IsPullback.of_hasPullback ζ f).map H
  have hHζ : H.map ζ = (g ≫ Space.completionSheafInclusion B S hS X T).hom ≫ eX.inv := hζ.symm
  rw [hHζ] at hpbζ
  exact ⟨hp.flip.isoIsPullback _ _ hpbζ⟩

/-- A section of the completion subfunctor of `X` along `T` over an object `T₀` of the site
gives a morphism from the sheaf represented by `T₀` to `X_{/T}`, whose composite with
`X_{/T} ⟶ X` is the universe lift of the section read as a morphism `h_{T₀} ⟶ X`. -/
theorem exists_hom_completionSheaf_of_mem {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (T : Set (Space.points B S hS X))
    {T₀ : BigFppfOver B S hS}
    (z : (Space.completionSubfunctor B S hS X T).toFunctor.obj (Opposite.op T₀)) :
    ∃ g : yonedaSheaf B S hS T₀ ⟶ Space.completionSheaf B S hS X T,
      (g ≫ Space.completionSheafInclusion B S hS X T).hom ≫
          (Space.sheafifiedULiftIso B S hS X hX.isSheaf).inv =
        Functor.whiskerRight (yonedaEquiv.symm z.1.down) uliftFunctor.{u + 1} := by
  let J := BigFppfOver.topology B S hS
  let C := Space.completionSubfunctor B S hS X T
  refine ⟨ObjectProperty.homMk (uliftYonedaEquiv.symm z ≫ J.toSheafify C.toFunctor), ?_⟩
  have h₁ : (ObjectProperty.homMk (uliftYonedaEquiv.symm z ≫ J.toSheafify C.toFunctor) ≫
        Space.completionSheafInclusion B S hS X T :
          yonedaSheaf B S hS T₀ ⟶ Space.sheafifiedULift B S hS X).hom =
      uliftYonedaEquiv.symm z ≫ C.ι ≫ J.toSheafify (X ⋙ uliftFunctor.{u + 1}) := by
    change uliftYonedaEquiv.symm z ≫ J.toSheafify C.toFunctor ≫ J.sheafifyMap C.ι = _
    rw [J.toSheafify_naturality]
  have hiso : J.toSheafify (X ⋙ uliftFunctor.{u + 1}) ≫
      (Space.sheafifiedULiftIso B S hS X hX.isSheaf).inv = 𝟙 _ :=
    (Space.sheafifiedULiftIso B S hS X hX.isSheaf).hom_inv_id
  rw [h₁]
  ext V x
  exact congrArg (fun φ => φ.app V (C.ι.app V ((uliftYonedaEquiv.symm z).app V x))) hiso

/-! ### The forward direction -/

/-- **Stacks 0GDE in the form of Stacks 0AJC.** Let `f : X' ⟶ X` be a quasi-compact morphism of
algebraic spaces over `S` and let `T` be a set of points of `X`. Then the completion
`f_{/T} : X'_{/T'} ⟶ X_{/T}` is quasi-compact in the sense of Stacks 0AJC: every fibre product
of it with an affine scheme of the site is a quasi-compact formal algebraic space. Such a fibre
product is the universe lift of the fibre product `T₀ ×_X X'`, which is a quasi-compact algebraic
space because `f` is quasi-compact. -/
theorem isQuasiCompact_completionSheafMap_of_isQuasiCompact
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X)) (hf : Space.IsQuasiCompact B S hS f) :
    IsQuasiCompact B S hS (Space.completionSheafMap B S hS f T) := by
  intro T₀ hT₀ g W p q sq
  let H := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}
  let hFF : H.FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u + 1}).whiskeringRight _
  let k : H.obj (yoneda.obj T₀) ⟶ H.obj X :=
    (g ≫ Space.completionSheafInclusion B S hS X T).hom ≫
      (Space.sheafifiedULiftIso B S hS X hX.isSheaf).inv
  let ζ : yoneda.obj T₀ ⟶ X := hFF.preimage k
  obtain ⟨eW⟩ := nonempty_iso_pullback_of_isPullback_completionSheafMap B S hS hX' hX f T g ζ
    (hFF.map_preimage k).symm sq
  exact isQuasiCompactSpace_of_iso_uliftFunctor B S hS
    (isAlgebraicSpace_pullback B S hS ζ f (isAlgebraicSpace_yoneda B S hS T₀) hX' hX)
    (hf _ (isAlgebraicSpace_yoneda B S hS T₀)
      (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS T₀ hT₀) ζ) eW

/-! ### The converse -/

/-- The finitely many basic opens `D(s)`, for generators `s` of an ideal `I`, together with
`V(I)` cover `Spec A`. -/
private theorem mem_zeroLocus_or_exists_mem_basicOpen {A : Type*} [CommRing A] {I : Ideal A}
    {t : Set A} (ht : Ideal.span t = I) (p : PrimeSpectrum A) :
    p ∈ PrimeSpectrum.zeroLocus (I : Set A) ∨ ∃ s ∈ t, p ∈ PrimeSpectrum.basicOpen s := by
  by_cases h : t ⊆ p.asIdeal
  · left
    rw [← ht]
    exact Ideal.span_le.mpr h
  · obtain ⟨s, hst, hsp⟩ := Set.not_subset.mp h
    exact Or.inr ⟨s, hst, (PrimeSpectrum.mem_basicOpen _ _).mpr hsp⟩

/-- Let `f : X' ⟶ X` be a morphism of algebraic spaces and `ψ : h_W ⟶ X` a morphism from a
scheme of the site. If finitely many morphisms `j_o : V_o ⟶ W` of the site jointly cover `W` and
each fibre product of `f` with `V_o ⟶ W ⟶ X` is quasi-compact, then so is `X' ×_X W`. -/
private theorem isQuasiCompactSpace_pullback_of_finite_cover
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X) (f : X' ⟶ X)
    {W : BigFppfOver B S hS} (ψ : yoneda.obj W ⟶ X) {J : Type*} [Finite J]
    {V : J → BigFppfOver B S hS} (j : ∀ o, V o ⟶ W)
    (hqc : ∀ o, Space.IsQuasiCompactSpace B S hS (pullback f (yoneda.map (j o) ≫ ψ)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj W,
      ∃ o, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (j o))) :
    Space.IsQuasiCompactSpace B S hS (pullback f ψ) := by
  have hsq : ∀ o, ∃ c : pullback f (yoneda.map (j o) ≫ ψ) ⟶ pullback f ψ,
      IsPullback c (pullback.snd f (yoneda.map (j o) ≫ ψ)) (pullback.snd f ψ)
        (yoneda.map (j o)) := fun o ↦
    ⟨_, IsPullback.of_right' (IsPullback.of_hasPullback f (yoneda.map (j o) ≫ ψ))
      (IsPullback.of_hasPullback f ψ)⟩
  choose c hc using hsq
  refine Space.isQuasiCompactSpace_of_finite_jointly_surjective' B S hS
    (isAlgebraicSpace_pullback B S hS f ψ hX' (isAlgebraicSpace_yoneda B S hS W) hX)
    (fun _ ↦ isAlgebraicSpace_pullback B S hS f _ hX' (isAlgebraicSpace_yoneda B S hS _) hX)
    c hqc fun w ↦ ?_
  obtain ⟨o, ho⟩ :=
    hcov (Space.pointsToScheme B S hS W (Space.pointsMap B S hS _ (pullback.snd f ψ) w))
  obtain ⟨d, hd⟩ := Space.mem_range_pointsMap_yoneda_map B S hS (j o) _ ho
  obtain ⟨v, hv, -⟩ := Space.exists_points_of_isPullback B S hS (hc o) w d hd.symm
  exact ⟨o, v, hv⟩

/-- **The closed piece of the converse of Stacks 0ARU.** Let `f : X' ⟶ X` be a morphism of
algebraic spaces whose completion `f_{/T}` is quasi-compact, and let `ψ : Spec A ⟶ X` pull `T`
back to `V(I)`. Then the fibre product of `f` with `Spec (A ⧸ I) ⟶ Spec A ⟶ X`, which is a
fibre product of `f_{/T}` with an affine scheme, is quasi-compact. -/
private theorem isQuasiCompactSpace_pullback_supportStageToAffine
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (f : X' ⟶ X)
    (hf : IsQuasiCompact B S hS (Space.completionSheafMap B S hS f T))
    {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A)))
    (str : Spec (.of A) ⟶ S) (ψ : yoneda.obj (affineOver B S hS hA str) ⟶ X) (I : Ideal A)
    (hPre : Space.pointsMap B S hS _ ψ ⁻¹' T = zeroLocusPoints B S hS hA str I) :
    Space.IsQuasiCompactSpace B S hS
      (pullback f (yoneda.map (supportStageToAffine B S hS hA str I ⟨I, rfl⟩) ≫ ψ)) := by
  let Z : BigFppfOver B S hS :=
    (BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA str I ⟨I, rfl⟩)
  let ι : Z ⟶ affineOver B S hS hA str := supportStageToAffine B S hS hA str I ⟨I, rfl⟩
  have hιZ : Space.HasImageIn B S hS (yoneda.obj (affineOver B S hS hA str))
      (Space.pointsMap B S hS _ ψ ⁻¹' T) Z ι := by
    rw [hPre]
    exact supportStage_hasImageIn B S hS hA str I ⟨I, rfl⟩
  let z : (Space.completionSubfunctor B S hS X T).toFunctor.obj (Opposite.op Z) :=
    (Space.completionMap B S hS ψ T).app (Opposite.op Z) ⟨ULift.up ι, hιZ⟩
  obtain ⟨gZ, hgZ⟩ := exists_hom_completionSheaf_of_mem B S hS hX T z
  let ζ : yoneda.obj Z ⟶ X := yonedaEquiv.symm z.1.down
  have hζ : ζ = yoneda.map ι ≫ ψ := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    rfl
  have hZaff : IsAffine ((BigFppfOver.toScheme B S hS).obj Z) :=
    (supportStage B S hS hA str I ⟨I, rfl⟩).2
  have hpb := IsPullback.of_hasPullback gZ (Space.completionSheafMap B S hS f T)
  obtain ⟨eWZ⟩ := nonempty_iso_pullback_of_isPullback_completionSheafMap B S hS hX' hX f T gZ ζ
    hgZ hpb
  exact Space.isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry ζ f ≪≫ pullback.congrHom rfl hζ)
    (isQuasiCompactSpace_of_isQuasiCompactSpace_of_iso B S hS
      (isAlgebraicSpace_pullback B S hS ζ f (isAlgebraicSpace_yoneda B S hS Z) hX' hX) eWZ
      (hf Z hZaff gZ _ _ _ hpb))

/-- **An open piece of the converse of Stacks 0ARU.** Let `f : X' ⟶ X` be an isomorphism over
the open subspace with point set `Tᶜ`, and let `ψ : Spec A ⟶ X` pull `T` back to the points
supported on `T''`. If `s ∈ A` lies in every prime of `T''`, then `D(s)` maps into that open
subspace, so the fibre product of `f` with `D(s) ⟶ Spec A ⟶ X` is the affine scheme `D(s)`,
hence quasi-compact. -/
private theorem isQuasiCompactSpace_pullback_basicOpen_of_isIso
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Set (Space.points B S hS X)) (f : X' ⟶ X)
    (hU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    {A : Type u} [CommRing A] (hA : B.Contains (Spec (.of A)))
    (str : Spec (.of A) ⟶ S) (ψ : yoneda.obj (affineOver B S hS hA str) ⟶ X)
    {T'' : Set ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hA str))}
    (hTpts : Space.pointsMap B S hS _ ψ ⁻¹' T =
      supportedPoints B S hS (affineOver B S hS hA str) T'')
    (s : A) (hs : ∀ p ∈ T'', s ∈ (show PrimeSpectrum A from p).asIdeal)
    (hAs : B.Contains (Spec (.of (Localization.Away s)))) :
    Space.IsQuasiCompactSpace B S hS (pullback f (yoneda.map
      (Over.homMk (ObjectProperty.homMk
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))))) rfl :
        affineOver B S hS hAs
          (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ str) ⟶
          affineOver B S hS hA str) ≫ ψ)) := by
  let Ws := affineOver B S hS hAs
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))) ≫ str)
  let js : Ws ⟶ affineOver B S hS hA str := Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s))))) rfl
  have hjsRange : (show Set (PrimeSpectrum A) from
      Set.range ((BigFppfOver.toScheme B S hS).map js)) =
      (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away s) s
  have hsU : Set.range (Space.pointsMap B S hS _ (yoneda.map js ≫ ψ)) ⊆ Tᶜ := by
    rintro _ ⟨x, rfl⟩ hx
    rw [Space.pointsMap_comp, Function.comp_apply] at hx
    have hmem : Space.pointsMap B S hS _ (yoneda.map js) x ∈
        supportedPoints B S hS (affineOver B S hS hA str) T'' := by
      rwa [← hTpts]
    change Space.pointsToScheme B S hS _ (Space.pointsMap B S hS _ (yoneda.map js) x) ∈
      T'' at hmem
    rw [Space.pointsToScheme_pointsMap] at hmem
    have hbo : (BigFppfOver.toScheme B S hS).map js (Space.pointsToScheme B S hS Ws x) ∈
        (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum A)) :=
      (Set.ext_iff.mp hjsRange _).mp ⟨_, rfl⟩
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hbo (hs _ hmem)
  let Uo := Space.openSubspaceOfPoints B S hS X Tᶜ
  have hsle : Subfunctor.range (yoneda.map js ≫ ψ) ≤ Uo :=
    (Space.range_le_openSubspaceOfPoints_range_pointsMap _).trans
      (Space.openSubspaceOfPoints_mono B S hS hsU)
  have hisoU : ∀ {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {k : V ⟶ X} (m : V ⟶ Uo.toFunctor),
      k = m ≫ Uo.ι → IsIso (pullback.snd f k) := by
    rintro V k m rfl
    have h : (pullbackLeftPullbackSndIso f Uo.ι m).inv ≫
        pullback.snd (pullback.snd f Uo.ι) m = pullback.snd f (m ≫ Uo.ι) := by
      rw [Iso.inv_comp_eq, pullbackLeftPullbackSndIso_hom_snd]
    rw [← h]
    infer_instance
  have : IsIso (pullback.snd f (yoneda.map js ≫ ψ)) :=
    hisoU (Subfunctor.lift (yoneda.map js ≫ ψ) hsle) (Subfunctor.lift_ι _ _).symm
  exact Space.isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd f (yoneda.map js ≫ ψ))).symm
    (Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS Ws
      (inferInstanceAs (IsAffine (Spec (.of (Localization.Away s))))))

/-- **The affine case of the converse of Stacks 0ARU.** Let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S` which is an isomorphism over the open subspace `U` with point set
`Tᶜ`, for a closed set `T` of points of `X`, and whose completion `f_{/T}` is quasi-compact. Let
`ψ : Spec A ⟶ X` be a morphism from the spectrum of a Noetherian ring in the site. Then the
fibre product `X' ×_X Spec A` is a quasi-compact algebraic space.

The inverse image of `T` in `Spec A` is `V(I)` for an ideal `I`. Over `Spec (A ⧸ I)`, which
maps into `X_{/T}`, the fibre product is a fibre product of `f_{/T}` with an affine scheme,
hence quasi-compact. Over each of the finitely many basic opens `D(s)`, for generators `s` of
`I`, it is `D(s)` itself, `f` being an isomorphism over `U`. These pieces cover. -/
theorem isQuasiCompactSpace_pullback_of_isQuasiCompact_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (f : X' ⟶ X)
    (hU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hf : IsQuasiCompact B S hS (Space.completionSheafMap B S hS f T))
    {A : Type u} [CommRing A] [IsNoetherianRing A] (hA : B.Contains (Spec (.of A)))
    (str : Spec (.of A) ⟶ S) (ψ : yoneda.obj (affineOver B S hS hA str) ⟶ X) :
    Space.IsQuasiCompactSpace B S hS (pullback f ψ) := by
  obtain ⟨T'', hT'', hTpts⟩ := exists_isClosed_preimage_eq_supportedPoints hT ψ
  let I : Ideal A := PrimeSpectrum.vanishingIdeal T''
  have hZT : PrimeSpectrum.zeroLocus (I : Set A) = T'' :=
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure T'').trans hT''.closure_eq
  have hPre : Space.pointsMap B S hS _ ψ ⁻¹' T = zeroLocusPoints B S hS hA str I := by
    rw [hTpts, ← supportedPoints_zeroLocus, hZT]
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian I : I.FG)
  have hAs : ∀ s : t, B.Contains (Spec (.of (Localization.Away (s : A)))) := fun s ↦
    Scheme.size_lt_of_isOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (s : A))))) hA
  have hsI : ∀ s : t, (s : A) ∈ I := fun s ↦ ht ▸ Ideal.subset_span s.2
  have hs : ∀ s : t, ∀ p ∈ T'', (s : A) ∈ (show PrimeSpectrum A from p).asIdeal :=
    fun s p hp ↦ by rw [← hZT] at hp; exact hp (hsI s)
  refine isQuasiCompactSpace_pullback_of_finite_cover B S hS hX' hX f ψ (J := Option t)
    (V := fun o ↦ o.elim
      ((BigAffineFppf.inclusion B S hS).obj (supportStage B S hS hA str I ⟨I, rfl⟩))
      fun s ↦ affineOver B S hS (hAs s)
        (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (s : A)))) ≫ str))
    (fun
      | none => supportStageToAffine B S hS hA str I ⟨I, rfl⟩
      | some s => Over.homMk (ObjectProperty.homMk
          (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away (s : A)))))) rfl)
    (fun
      | none => isQuasiCompactSpace_pullback_supportStageToAffine B S hS hX' hX T f hf hA str ψ
          I hPre
      | some s => isQuasiCompactSpace_pullback_basicOpen_of_isIso B S hS T f hU hA str ψ hTpts
          s (hs s) (hAs s)) fun x ↦ ?_
  rcases mem_zeroLocus_or_exists_mem_basicOpen ht x with hx | ⟨s, hst, hsx⟩
  · refine ⟨none, ?_⟩
    change _ ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I))
    rwa [_root_.range_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  · exact ⟨some ⟨s, hst⟩, (Set.ext_iff.mp (PrimeSpectrum.localization_away_comap_range
      (Localization.Away s) s) _).mpr hsx⟩

/-- **The converse of Stacks 0ARU.** Let `X` be a locally Noetherian algebraic space over `S`,
let `T` be a closed set of points of `X` and let `f : X' ⟶ X` be a morphism of algebraic spaces
which is an isomorphism over the open subspace `U` with point set `Tᶜ`. If the completion
`f_{/T} : X'_{/T'} ⟶ X_{/T}` is quasi-compact in the sense of Stacks 0AJC, then `f` is
quasi-compact.

Quasi-compactness of `f` is tested on a surjective étale scheme chart of `X` (Stacks 03KG), and
on the base change to that chart Zariski locally, over its affine opens; each of these is the
spectrum of a Noetherian ring étale over `X`, where
`AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_pullback_of_isQuasiCompact_completionSheafMap`
applies. -/
theorem isQuasiCompact_of_isQuasiCompact_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hXN : Space.IsLocallyNoetherian B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (f : X' ⟶ X)
    (hU : IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hf : IsQuasiCompact B S hS (Space.completionSheafMap B S hS f T)) :
    Space.IsQuasiCompact B S hS f := by
  obtain ⟨V, φ, hφS, hφE⟩ := hX.exists_atlas
  refine Space.isQuasiCompact_of_surjectiveEtale_atlas B S hS f hX' hX V φ
    ((Space.presheafSurjective_iff_isSurjective_yoneda B S hS X hX V φ).mp hφS)
    (Space.isEtale_of_presheaf_etale B S hS hφE) ?_
  let Y := (BigFppfOver.toScheme B S hS).obj V
  let K := Y.affineOpens
  let A : K → Type u := fun W ↦ Γ(Y, W.1)
  have hopen : ∀ W : K, IsOpenImmersion (W.2.fromSpec : Spec (.of (A W)) ⟶ Y) := fun W ↦
    IsAffineOpen.isOpenImmersion_fromSpec W.2
  have hA : ∀ W : K, B.Contains (Spec (.of (A W))) := fun W ↦
    Scheme.size_lt_of_isOpenImmersion (W.2.fromSpec : Spec (.of (A W)) ⟶ Y) V.left.property
  let str : ∀ W : K, Spec (.of (A W)) ⟶ S := fun W ↦ W.2.fromSpec ≫ B.inclusion.map V.hom
  let ι : ∀ W : K, affineOver B S hS (hA W) (str W) ⟶ V := fun W ↦
    Over.homMk (ObjectProperty.homMk W.2.fromSpec) rfl
  have hιet : ∀ W : K, Space.IsEtale B S hS (yoneda.map (ι W) ≫ φ) := fun W ↦
    Space.isEtale_comp B S hS
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS _).2
        ((Space.presheaf_yoneda_map_etale_iff B S hS (ι W)).2 (by
          have := hopen W
          exact (inferInstance : Etale (W.2.fromSpec : Spec (.of (A W)) ⟶ Y)))))
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφE)
  refine Space.isQuasiCompact_pullback_snd_of_openCover B S hS f hX' hX V φ
    (fun W ↦ affineOver B S hS (hA W) (str W)) ι (fun W ↦ hopen W) (fun v ↦ ?_) (fun W ↦ ?_)
  · obtain ⟨W, hW, hvW, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := v) (U := ⊤)
      trivial
    exact ⟨⟨W, hW⟩, (Set.ext_iff.mp hW.range_fromSpec v).mpr hvW⟩
  · have hNoeth : IsNoetherianRing (A W) := by
      have hloc : _root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of (A W))) :=
        hXN (affineOver B S hS (hA W) (str W)) _ (hιet W)
      have : _root_.AlgebraicGeometry.IsNoetherian (Spec (.of (A W))) := ⟨⟩
      exact isNoetherian_Spec.mp this
    exact Space.isQuasiCompact_of_isQuasiCompactSpace_of_isAffine
      (isAlgebraicSpace_pullback B S hS f _ hX' (isAlgebraicSpace_yoneda B S hS _) hX)
      (isQuasiCompactSpace_pullback_of_isQuasiCompact_completionSheafMap B S hS hX' hX T hT f
        hU hf (hA W) (str W) (yoneda.map (ι W) ≫ φ))
      (affineOver B S hS (hA W) (str W)) (inferInstanceAs (IsAffine (Spec (.of (A W))))) _

/-! ### Stacks 0ARU -/

/-- **Stacks 0ARU.** Let `X` be a locally Noetherian algebraic space over `S`, let `T ⊆ |X|` be
a closed subset and let `U ⊂ X` be the open subspace with `|U| = |X| ∖ T`. Let `f : X' ⟶ X` be
a morphism of algebraic spaces which is locally of finite type and such that `f⁻¹U ⟶ U` is an
isomorphism, and let `g : W ⟶ X_{/T}` correspond to `f` under the completion functor of
Stacks 0AR5, that is, be isomorphic over `X_{/T}` to `f_{/T} : X'_{/T'} ⟶ X_{/T}`. Then `f` is
quasi-compact if and only if `g` is quasi-compact. -/
@[stacks 0ARU]
theorem isQuasiCompact_iff_isQuasiCompact_of_overIso
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXN : Space.IsLocallyNoetherian B S hS X)
    (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    (M : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ))
    {W : FppfSheaf B S hS} (g : W ⟶ Space.completionSheaf B S hS X T)
    (e : Over.mk g ≅ Over.mk (Space.completionSheafMap B S hS M.obj.hom T)) :
    Space.IsQuasiCompact B S hS M.obj.hom ↔ IsQuasiCompact B S hS g := by
  have hw : e.hom.left ≫ Space.completionSheafMap B S hS M.obj.hom T = g := Over.w e.hom
  have hw' : e.inv.left ≫ g = Space.completionSheafMap B S hS M.obj.hom T := Over.w e.inv
  have : IsIso e.hom.left := (inferInstance : IsIso ((Over.forget _).mapIso e).hom)
  have : IsIso e.inv.left := (inferInstance : IsIso ((Over.forget _).mapIso e).inv)
  refine ⟨fun hf ↦ ?_, fun hg ↦ ?_⟩
  · exact IsQuasiCompact.of_isPullback B S hS
      (IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, hw]⟩)
      (isQuasiCompact_completionSheafMap_of_isQuasiCompact B S hS
        M.property.source_isAlgebraicSpace hX M.obj.hom T hf)
  · exact isQuasiCompact_of_isQuasiCompact_completionSheafMap B S hS
      M.property.source_isAlgebraicSpace hX hXN T hT M.obj.hom M.property.isIso_pullback_snd
      (IsQuasiCompact.of_isPullback B S hS
        (IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, hw']⟩) hg)

end AlgebraicGeometry.FormalSpace

end
