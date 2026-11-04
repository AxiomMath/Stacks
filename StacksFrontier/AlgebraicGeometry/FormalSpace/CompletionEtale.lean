module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Completion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms

/-!
# Étaleness for a morphism of completions

Let `S` be a scheme contained in a big fppf site `B`, let `f : X' ⟶ X` be a morphism of
algebraic spaces over `S` and let `T` be a set of points of `X`. If `f` is étale then so is the
induced morphism of completions `f_{/T} : X'_{/|f|⁻¹ T} ⟶ X_{/T}`.

Conversely, for a morphism `f : X' ⟶ X` of schemes of the site which is locally of finite type
with `X` locally Noetherian, if `f` is étale away from `T` and `f_{/T}` is étale, then `f` is
étale everywhere.

Étaleness of a morphism of formal algebraic spaces is the Bootstrap condition of Stacks 03XZ
evaluated at étaleness of morphisms of large-valued algebraic spaces:
`AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpacesULift` together with
`AlgebraicGeometry.Space.HasPropertyULift` of `AlgebraicGeometry.Space.IsEtaleULift`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_hasPropertyULift_sheafifiedULiftMap_of_isEtale`: an
  étale morphism of algebraic spaces over `S` is étale in the bootstrap sense of Stacks 03XZ
  after its sheafified universe lift.
* `AlgebraicGeometry.FormalSpace.isEtale_completionSheafMap`: the morphism of completions
  induced by an étale morphism of algebraic spaces is étale.
* `AlgebraicGeometry.FormalSpace.etale_pullback_nthOrderToBase_of_isEtale_completionSheafMap`:
  étaleness of a morphism of completions descends to the infinitesimal neighbourhoods of the
  closed subscheme cut out by `T`.
* `AlgebraicGeometry.FormalSpace.isEtale_of_isEtale_completionSheafMap`: a morphism locally of
  finite type over a locally Noetherian scheme which is étale away from `T` and whose completion
  along `T` is étale is étale.

## References

* [Stacks Project, Tag 0GI0](https://stacks.math.columbia.edu/tag/0GI0)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 0A43](https://stacks.math.columbia.edu/tag/0A43)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
* [Stacks Project, Tag 0AR4](https://stacks.math.columbia.edu/tag/0AR4)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If `f_{/T} : X'_{/|f|⁻¹ T} ⟶ X_{/T}` is étale, then the base change of `f` to the `n`th-order
infinitesimal neighbourhood of a closed subscheme `Z ⊂ X` is étale for every `n`. -/
abbrev EtaleCompletionDescendsToInfinitesimalNeighbourhoods
    {X' X : BigFppfOver B S hS} (f : X' ⟶ X)
    (T : Set (Space.points B S hS (yoneda.obj X)))
    {Z : Scheme.{u}} (i : Z ⟶ (BigFppfOver.toScheme B S hS).obj X)
    [IsClosedImmersion i] : Prop :=
  (∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (Space.completionSheafMap B S hS (yoneda.map f) T).hom,
    Space.HasPropertyULift.{u + 1} B S hS
      (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (g : A ⟶ C) ↦
        Space.IsEtaleULift.{u + 1} B S hS g.hom)
      (Space.completionSheafMap B S hS (yoneda.map f) T).hom hrep) →
    ∀ n : ℕ, AlgebraicGeometry.Etale (pullback.snd ((BigFppfOver.toScheme B S hS).map f)
      (Stacks.Thickenings.nthOrderToBase i n))

/-- Étaleness of a morphism of large-valued presheaves is unchanged by precomposing with an
isomorphism. -/
private theorem isEtaleULift_precomp
    {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : F ⟶ G) [IsIso e] (f : G ⟶ K)
    (hf : Space.IsEtaleULift.{u + 1} B S hS f) :
    Space.IsEtaleULift.{u + 1} B S hS (e ≫ f) := by
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let _ : (P.relative (uliftYoneda.{u + 1})).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (F := uliftYoneda.{u + 1}) P).respectsIso
  intro U φ hφ
  simpa [Category.assoc] using hf U (φ ≫ e) (MorphismProperty.RespectsIso.postcomp
    (P.relative (uliftYoneda.{u + 1})) e φ hφ)

/-- Étaleness of a morphism of large-valued presheaves is unchanged by postcomposing with an
isomorphism. -/
private theorem isEtaleULift_postcomp
    {F G K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (e : G ⟶ K) [IsIso e] (f : F ⟶ G)
    (hf : Space.IsEtaleULift.{u + 1} B S hS f) :
    Space.IsEtaleULift.{u + 1} B S hS (f ≫ e) := by
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let _ : (P.relative (uliftYoneda.{u + 1})).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (F := uliftYoneda.{u + 1}) P).respectsIso
  intro U φ hφ
  simpa [Category.assoc] using MorphismProperty.RespectsIso.postcomp
    (P.relative (uliftYoneda.{u + 1})) e (φ ≫ f) (hf U φ hφ)

/-- Étaleness, as a property of morphisms of large-valued algebraic spaces over `S`, is
invariant under isomorphism. -/
private instance etalePropertyULift_respectsIso :
    MorphismProperty.RespectsIso
      (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (g : A ⟶ C) ↦
        Space.IsEtaleULift.{u + 1} B S hS g.hom) := by
  refine MorphismProperty.RespectsIso.mk _ (fun e f hf => ?_) (fun e f hf => ?_)
  · have : IsIso e.hom.hom :=
      ⟨e.inv.hom, congrArg (fun k => k.hom) e.hom_inv_id,
        congrArg (fun k => k.hom) e.inv_hom_id⟩
    exact isEtaleULift_precomp B S hS e.hom.hom f.hom hf
  · have : IsIso e.hom.hom :=
      ⟨e.inv.hom, congrArg (fun k => k.hom) e.hom_inv_id,
        congrArg (fun k => k.hom) e.inv_hom_id⟩
    exact isEtaleULift_postcomp B S hS e.hom.hom f.hom hf

/-- The universe lift of an étale morphism of algebraic spaces over `S` is étale in the
bootstrap sense of Stacks 03XZ. -/
public theorem hasPropertyULift_whiskerRight_of_isEtale
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (hf : Space.IsEtale B S hS f)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (Functor.whiskerRight f uliftFunctor.{u + 1})) :
    Space.HasPropertyULift.{u + 1} B S hS
      (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (g : A ⟶ C) ↦
        Space.IsEtaleULift.{u + 1} B S hS g.hom)
      (Functor.whiskerRight f uliftFunctor.{u + 1}) hrep := by
  let C := BigFppfOver B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  intro U ξ
  show Space.IsEtaleULift.{u + 1} B S hS
    (pullback.fst ξ (Functor.whiskerRight f uliftFunctor.{u + 1}))
  obtain ⟨ξ₀, hξ₀⟩ := H.map_surjective (ξ : H.obj (yoneda.obj U) ⟶ H.obj X)
  let A : AlgebraicSpaces B S hS := ⟨X', hX'⟩
  let Z : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Uₐ : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let fA : A ⟶ Z := ObjectProperty.homMk f
  let ξA : Uₐ ⟶ Z := ObjectProperty.homMk ξ₀
  let q : AlgebraicSpaces.fiberProduct B S hS ξA fA ⟶ Uₐ :=
    ObjectProperty.homMk (pullback.fst ξA.hom fA.hom)
  let r : AlgebraicSpaces.fiberProduct B S hS ξA fA ⟶ A :=
    ObjectProperty.homMk (pullback.snd ξA.hom fA.hom)
  have hq : Space.IsEtale B S hS q.hom :=
    Space.isEtale_of_isPullback B S hS r q fA ξA
      (AlgebraicSpaces.isPullback_fiberProduct B S hS ξA fA).flip hf
  have hqlift : Space.IsEtaleULift.{u + 1} B S hS
      (Functor.whiskerRight (pullback.fst ξ₀ f) uliftFunctor.{u + 1}) :=
    (Space.isEtaleULift_whiskerRight_iff B S hS (pullback.fst ξ₀ f)).mpr hq
  have hsq : IsPullback (H.map (pullback.fst ξ₀ f)) (H.map (pullback.snd ξ₀ f)) ξ
      (Functor.whiskerRight f uliftFunctor.{u + 1}) := by
    rw [← hξ₀]
    exact (IsPullback.of_hasPullback ξ₀ f).map H
  have h := isEtaleULift_precomp B S hS hsq.isoPullback.inv
    (Functor.whiskerRight (pullback.fst ξ₀ f) uliftFunctor.{u + 1}) hqlift
  have heq := (Iso.inv_comp_eq hsq.isoPullback).mpr hsq.isoPullback_hom_fst.symm
  exact heq ▸ h

/-- The sheafified universe lift of an étale morphism of algebraic spaces over `S` is
representable by algebraic spaces and étale in the bootstrap sense of Stacks 03XZ. -/
public theorem exists_hasPropertyULift_sheafifiedULiftMap_of_isEtale
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (hf : Space.IsEtale B S hS f) :
    ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS f).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (q : A ⟶ C) ↦
          Space.IsEtaleULift.{u + 1} B S hS q.hom)
        (Space.sheafifiedULiftMap B S hS f).hom hrep := by
  have hlarge : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (Functor.whiskerRight f uliftFunctor.{u + 1}) :=
    (Space.isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS f).mpr fun U ξ =>
      isAlgebraicSpace_pullback B S hS ξ f (isAlgebraicSpace_yoneda B S hS U) hX' hX
  exact Space.exists_hasPropertyULift_sheafifiedULiftMap B S hS hX'.isSheaf hX.isSheaf f hlarge
    (hasPropertyULift_whiskerRight_of_isEtale B S hS hX' hX f hf hlarge)

/-- Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S` and let `T` be a set of points
of `X`. If `f` is étale, then the induced morphism of completions `X'_{/|f|⁻¹ T} ⟶ X_{/T}` is
étale: it is representable by algebraic spaces and each of its base changes along a
scheme-valued point of its target is étale. -/
@[stacks 0GI0]
theorem isEtale_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (Space.points B S hS X))
    (hf : Space.IsEtale B S hS f) :
    ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafMap B S hS f T).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (g : A ⟶ C) ↦
          Space.IsEtaleULift.{u + 1} B S hS g.hom)
        (Space.completionSheafMap B S hS f T).hom hrep := by
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  have hlarge : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (H.map f) :=
    (Space.isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS f).mpr fun U ξ =>
      isAlgebraicSpace_pullback B S hS ξ f (isAlgebraicSpace_yoneda B S hS U) hX' hX
  have hprop := hasPropertyULift_whiskerRight_of_isEtale B S hS hX' hX f hf hlarge
  have hX'large : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (H.obj X') :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X').mpr hX'
  have hXlarge : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (H.obj X) :=
    (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X).mpr hX
  let eX' : H.obj X' ≅ (Space.sheafifiedULift B S hS X').obj := J.isoSheafify hX'large.isSheaf
  let eX : H.obj X ≅ (Space.sheafifiedULift B S hS X).obj := J.isoSheafify hXlarge.isSheaf
  have hpb := (Space.isPullback_completionSheafMap B S hS f T).map
    (sheafToPresheaf J (Type (u + 1)))
  have hcomm : (Space.sheafifiedULiftMap B S hS f).hom ≫ eX.inv = eX'.inv ≫ H.map f := by
    have hn' : H.map f ≫ eX.hom = eX'.hom ≫ (Space.sheafifiedULiftMap B S hS f).hom := by
      show (Functor.whiskerRight f uliftFunctor.{u + 1}) ≫
          J.toSheafify (X ⋙ uliftFunctor.{u + 1}) =
        J.toSheafify (X' ⋙ uliftFunctor.{u + 1}) ≫
          J.sheafifyMap (Functor.whiskerRight f uliftFunctor.{u + 1})
      exact J.toSheafify_naturality _
    calc
      (Space.sheafifiedULiftMap B S hS f).hom ≫ eX.inv =
          eX'.inv ≫ (eX'.hom ≫ (Space.sheafifiedULiftMap B S hS f).hom) ≫ eX.inv := by
            simp [Category.assoc]
      _ = eX'.inv ≫ (H.map f ≫ eX.hom) ≫ eX.inv := by rw [hn']
      _ = eX'.inv ≫ H.map f := by simp [Category.assoc]
  have hp : IsPullback
      ((Space.completionSheafInclusion B S hS X'
        (Space.pointsMap B S hS X' f ⁻¹' T)).hom ≫ eX'.inv)
      (Space.completionSheafMap B S hS f T).hom
      (H.map f)
      ((Space.completionSheafInclusion B S hS X T).hom ≫ eX.inv) :=
    IsPullback.of_iso hpb (Iso.refl _) eX'.symm (Iso.refl _) eX.symm
      (by simp) (by simp) hcomm (by simp)
  exact ⟨Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ hp hlarge,
    Space.hasPropertyULift_of_isPullback B S hS hp hlarge hprop⟩

/-! ### Étaleness from étaleness of the completion -/

/-- The universe-lifted Yoneda image of a morphism of the big fppf site of `S` is the universe
lift of its Yoneda image. -/
private theorem uliftYoneda_map_eq_whiskerRight {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).map h =
      Functor.whiskerRight (yoneda.map h) uliftFunctor.{u + 1} := rfl

/-- Sheafifying a morphism into a sheaf and then undoing the sheafification isomorphism of the
target gives the morphism which the sheafification of the source lifts it to. -/
private theorem sheafifyMap_comp_isoSheafify_inv
    {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q) (η : P ⟶ Q) :
    (BigFppfOver.topology B S hS).sheafifyMap η ≫
        ((BigFppfOver.topology B S hS).isoSheafify hQ).inv =
      (BigFppfOver.topology B S hS).sheafifyLift η hQ := by
  rw [(BigFppfOver.topology B S hS).isoSheafify_inv,
    (BigFppfOver.topology B S hS).sheafifyMap_sheafifyLift, Category.comp_id]

/-- For a morphism `f : X' ⟶ X` of presheaves whose universe lifts are fppf sheaves, the
completions of `X'` along `|f|⁻¹ T` and of `X` along `T` form a cartesian square over the
universe lift of `f`. -/
private theorem isPullback_completionSheafInclusion
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (Space.points B S hS X))
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X' ⋙ uliftFunctor.{u + 1}))
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X ⋙ uliftFunctor.{u + 1})) :
    IsPullback
      ((Space.completionSheafInclusion B S hS X' (Space.pointsMap B S hS X' f ⁻¹' T)).hom ≫
        ((BigFppfOver.topology B S hS).isoSheafify hX').inv)
      (Space.completionSheafMap B S hS f T).hom
      (Functor.whiskerRight f uliftFunctor.{u + 1})
      ((Space.completionSheafInclusion B S hS X T).hom ≫
        ((BigFppfOver.topology B S hS).isoSheafify hX).inv) := by
  let J := BigFppfOver.topology B S hS
  let eX' : X' ⋙ uliftFunctor.{u + 1} ≅ (Space.sheafifiedULift B S hS X').obj :=
    J.isoSheafify hX'
  let eX : X ⋙ uliftFunctor.{u + 1} ≅ (Space.sheafifiedULift B S hS X).obj := J.isoSheafify hX
  have hpb := (Space.isPullback_completionSheafMap B S hS f T).map
    (sheafToPresheaf J (Type (u + 1)))
  have hcomm : (Space.sheafifiedULiftMap B S hS f).hom ≫ eX.inv =
      eX'.inv ≫ Functor.whiskerRight f uliftFunctor.{u + 1} := by
    have hn' : Functor.whiskerRight f uliftFunctor.{u + 1} ≫ eX.hom =
        eX'.hom ≫ (Space.sheafifiedULiftMap B S hS f).hom := by
      show (Functor.whiskerRight f uliftFunctor.{u + 1}) ≫
          J.toSheafify (X ⋙ uliftFunctor.{u + 1}) =
        J.toSheafify (X' ⋙ uliftFunctor.{u + 1}) ≫
          J.sheafifyMap (Functor.whiskerRight f uliftFunctor.{u + 1})
      exact J.toSheafify_naturality _
    calc
      (Space.sheafifiedULiftMap B S hS f).hom ≫ eX.inv =
          eX'.inv ≫ (eX'.hom ≫ (Space.sheafifiedULiftMap B S hS f).hom) ≫ eX.inv := by
            simp [Category.assoc]
      _ = eX'.inv ≫ (Functor.whiskerRight f uliftFunctor.{u + 1} ≫ eX.hom) ≫ eX.inv := by
            rw [hn']
      _ = eX'.inv ≫ Functor.whiskerRight f uliftFunctor.{u + 1} := by simp [Category.assoc]
  exact IsPullback.of_iso hpb (Iso.refl _) eX'.symm (Iso.refl _) eX.symm
    (by rw [Iso.refl_hom, Category.id_comp]; rfl) (by simp)
    hcomm (by rw [Iso.refl_hom, Category.id_comp]; rfl)

/-- A closed subscheme and its `n`th-order infinitesimal neighbourhood have the same point-set
image in the ambient scheme. -/
@[ega "III 5.3.5" "partial"]
private theorem range_nthOrderToBase {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]
    (n : ℕ) :
    Set.range (Stacks.Thickenings.nthOrderToBase i n) = Set.range i := by
  have hsurj : Function.Surjective (Stacks.Thickenings.nthOrderInclusion i n) :=
    (Stacks.Thickenings.IsNthOrderThickening.isThickening
      (Stacks.Thickenings.nthOrderInclusion_isNthOrderThickening i n)).2
  have hfac : ∀ z : Z, Stacks.Thickenings.nthOrderToBase i n
      (Stacks.Thickenings.nthOrderInclusion i n z) = i z := fun z =>
    congrArg (fun g : Z ⟶ W => g z) (Stacks.Thickenings.nthOrderInclusion_toBase i n)
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨t, rfl⟩
    obtain ⟨z, rfl⟩ := hsurj t
    exact ⟨z, (hfac z).symm⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨Stacks.Thickenings.nthOrderInclusion i n z, hfac z⟩

/-- The `n`th-order infinitesimal neighbourhood of a closed subscheme of the scheme underlying
an object of the big fppf site of `S` is again a scheme of that site. -/
private theorem contains_nthOrderInfinitesimalNeighbourhood
    {X : BigFppfOver B S hS} {Z : Scheme.{u}}
    (i : Z ⟶ (BigFppfOver.toScheme B S hS).obj X) [IsClosedImmersion i] (n : ℕ) :
    B.Contains (Stacks.Thickenings.nthOrderInfinitesimalNeighbourhood i n) :=
  Scheme.size_lt_of_isClosedImmersion (i.liftCoborder.ker ^ (n + 1)).subschemeι
    (Scheme.size_lt_of_isOpenImmersion i.coborderRange.ι X.left.property)

/-- The `n`th-order infinitesimal neighbourhood of a closed subscheme `Z` of an object `X` of
the big fppf site of `S`, as an object of that site, with the structure morphism to `S`
inherited from `X`. -/
private def nthOrderOver {X : BigFppfOver B S hS} {Z : Scheme.{u}}
    (i : Z ⟶ (BigFppfOver.toScheme B S hS).obj X) [IsClosedImmersion i] (n : ℕ) :
    BigFppfOver B S hS :=
  Over.mk (Y := B.obj (contains_nthOrderInfinitesimalNeighbourhood B S hS i n))
    (ObjectProperty.homMk (Stacks.Thickenings.nthOrderToBase i n ≫ X.hom.hom))

/-- The structure morphism of the `n`th-order infinitesimal neighbourhood of `Z ⊆ X`, as a
morphism of the big fppf site of `S`. -/
private def nthOrderOverToBase {X : BigFppfOver B S hS} {Z : Scheme.{u}}
    (i : Z ⟶ (BigFppfOver.toScheme B S hS).obj X) [IsClosedImmersion i] (n : ℕ) :
    nthOrderOver B S hS i n ⟶ X :=
  Over.homMk (ObjectProperty.homMk (Stacks.Thickenings.nthOrderToBase i n)) rfl

/-- The morphism of schemes underlying the structure morphism of the `n`th-order infinitesimal
neighbourhood is the structure morphism itself. -/
private theorem toScheme_map_nthOrderOverToBase {X : BigFppfOver B S hS} {Z : Scheme.{u}}
    (i : Z ⟶ (BigFppfOver.toScheme B S hS).obj X) [IsClosedImmersion i] (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map (nthOrderOverToBase B S hS i n) =
      Stacks.Thickenings.nthOrderToBase i n := rfl

/-- A section of `X` in the image of a morphism whose point-set image lies in `T` has point-set
image in `T`. -/
public theorem hasImageIn_of_range_pointsMap_subset
    {X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (i : W ⟶ X)
    (hrange : Set.range (Space.pointsMap B S hS W i) ⊆ T)
    (U : BigFppfOver B S hS) (x : W.obj (Opposite.op U)) :
    Space.HasImageIn B S hS X T U (i.app (Opposite.op U) x) := by
  intro p
  refine hrange ⟨(⟨p.carrier, p.contained, p.toBase, W.map p.value.op x⟩ :
    Space.FieldValuedPoint B S hS W).class B S hS W, ?_⟩
  rw [Space.pointsMap_class]
  exact congrArg (fun q : Space.FieldValuedPoint B S hS X => q.class B S hS X)
    (congrArg (fun v : X.obj (Opposite.op
          (Space.FieldValuedPoint.siteObject B S hS (yoneda.obj U) p)) =>
        (⟨p.carrier, p.contained, p.toBase, v⟩ : Space.FieldValuedPoint B S hS X))
      (NatTrans.naturality_apply i p.value.op x))

/-- The structure morphism of the `n`th-order infinitesimal neighbourhood of a closed subscheme
with set of points `T` is a section of `X` with point-set image in `T`. -/
private theorem hasImageIn_nthOrderOverToBase {X : BigFppfOver B S hS}
    {T : Set (Space.points B S hS (yoneda.obj X))} {Z : Scheme.{u}}
    (i : Z ⟶ (BigFppfOver.toScheme B S hS).obj X) [IsClosedImmersion i]
    (hiT : Set.range i = Space.pointsToScheme B S hS X '' T) (n : ℕ) :
    Space.HasImageIn B S hS (yoneda.obj X) T (nthOrderOver B S hS i n)
      (nthOrderOverToBase B S hS i n) := by
  have hrange : Set.range (Space.pointsMap B S hS (yoneda.obj (nthOrderOver B S hS i n))
      (yoneda.map (nthOrderOverToBase B S hS i n))) ⊆ T := by
    rintro _ ⟨p, rfl⟩
    have h1 := Space.pointsToScheme_pointsMap B S hS (nthOrderOverToBase B S hS i n) p
    have h3 : Stacks.Thickenings.nthOrderToBase i n
        (Space.pointsToScheme B S hS (nthOrderOver B S hS i n) p) ∈ Set.range i :=
      (range_nthOrderToBase i n).le (Set.mem_range_self _)
    have h2 : Space.pointsToScheme B S hS X
        (Space.pointsMap B S hS (yoneda.obj (nthOrderOver B S hS i n))
          (yoneda.map (nthOrderOverToBase B S hS i n)) p) ∈ Set.range i := by
      rwa [h1, toScheme_map_nthOrderOverToBase B S hS i n]
    rw [hiT] at h2
    obtain ⟨t, htT, hteq⟩ := h2
    exact Space.injective_pointsToScheme B S hS X hteq ▸ htT
  simpa using hasImageIn_of_range_pointsMap_subset B S hS T
    (yoneda.map (nthOrderOverToBase B S hS i n)) hrange (nthOrderOver B S hS i n)
    (𝟙 (nthOrderOver B S hS i n))

/-- The `n`th-order infinitesimal neighbourhood of a closed subscheme with set of points `T`
is a scheme-valued point of the completion `X_{/T}` lying over the structure morphism of that
neighbourhood: its composite with the morphism `X_{/T} ⟶ X` is the universe lift of that
structure morphism. -/
private theorem exists_completionSheafPoint_nthOrder {X : BigFppfOver B S hS}
    (T : Set (Space.points B S hS (yoneda.obj X))) {Z : Scheme.{u}}
    (i : Z ⟶ (BigFppfOver.toScheme B S hS).obj X) [IsClosedImmersion i]
    (hiT : Set.range i = Space.pointsToScheme B S hS X '' T) (n : ℕ)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (yoneda.obj X ⋙ uliftFunctor.{u + 1})) :
    ∃ ξ : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).obj (nthOrderOver B S hS i n) ⟶
        (Space.completionSheaf B S hS (yoneda.obj X) T).obj,
      ξ ≫ (Space.completionSheafInclusion B S hS (yoneda.obj X) T).hom ≫
          ((BigFppfOver.topology B S hS).isoSheafify hX).inv =
        Functor.whiskerRight (yoneda.map (nthOrderOverToBase B S hS i n))
          uliftFunctor.{u + 1} := by
  let sec : (Space.completionSubfunctor B S hS (yoneda.obj X) T).toFunctor.obj
      (Opposite.op (nthOrderOver B S hS i n)) :=
    ⟨ULift.up (nthOrderOverToBase B S hS i n), hasImageIn_nthOrderOverToBase B S hS i hiT n⟩
  have key : (BigFppfOver.topology B S hS).toSheafify
        (Space.completionSubfunctor B S hS (yoneda.obj X) T).toFunctor ≫
      ((BigFppfOver.topology B S hS).sheafifyMap
          (Space.completionSubfunctor B S hS (yoneda.obj X) T).ι ≫
        ((BigFppfOver.topology B S hS).isoSheafify hX).inv) =
      (Space.completionSubfunctor B S hS (yoneda.obj X) T).ι := by
    rw [sheafifyMap_comp_isoSheafify_inv B S hS hX,
      (BigFppfOver.topology B S hS).toSheafify_sheafifyLift]
  have hval := congrArg
    (fun α : (Space.completionSubfunctor B S hS (yoneda.obj X) T).toFunctor ⟶
        yoneda.obj X ⋙ uliftFunctor.{u + 1} =>
      α.app (Opposite.op (nthOrderOver B S hS i n)) sec) key
  refine ⟨uliftYonedaEquiv.{u + 1}.symm
    (((BigFppfOver.topology B S hS).toSheafify
        (Space.completionSubfunctor B S hS (yoneda.obj X) T).toFunctor).app
      (Opposite.op (nthOrderOver B S hS i n)) sec), ?_⟩
  refine (uliftYonedaEquiv_symm_comp _ _).trans
    (uliftYonedaEquiv.{u + 1}.symm_apply_eq.mpr ?_)
  exact hval.trans
    (uliftYonedaEquiv_uliftYoneda_map (nthOrderOverToBase B S hS i n)).symm

/-- Let `f : X' ⟶ X` be a morphism of the big fppf site over `S`, let `T` be a set of points of
`X` and let `i : Z ⟶ X` be a closed subscheme whose set of points is `T`. If the morphism of
completions `f_{/T}` is étale, then the base change of `f` to the `n`th-order infinitesimal
neighbourhood of `Z` is étale for every `n`. -/
theorem etale_pullback_nthOrderToBase_of_isEtale_completionSheafMap
    {X' X : BigFppfOver B S hS} (f : X' ⟶ X)
    (T : Set (Space.points B S hS (yoneda.obj X)))
    {Z : Scheme.{u}} (i : Z ⟶ (BigFppfOver.toScheme B S hS).obj X)
    [IsClosedImmersion i]
    (hiT : Set.range i = Space.pointsToScheme B S hS X '' T)
    (hetale : ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafMap B S hS (yoneda.map f) T).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (g : A ⟶ C) ↦
          Space.IsEtaleULift.{u + 1} B S hS g.hom)
        (Space.completionSheafMap B S hS (yoneda.map f) T).hom hrep)
    (n : ℕ) :
    AlgebraicGeometry.Etale (pullback.snd ((BigFppfOver.toScheme B S hS).map f)
      (Stacks.Thickenings.nthOrderToBase i n)) := by
  obtain ⟨hrep, hprop⟩ := hetale
  have : HasPullbacks (AlgebraicGeometry.SchemeBelow B.cutoff) := inferInstance
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have hsheafX : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (yoneda.obj X ⋙ uliftFunctor.{u + 1}) :=
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS (yoneda.obj X)).mpr
      (isAlgebraicSpace_yoneda B S hS X)).isSheaf
  have hsheafX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (yoneda.obj X' ⋙ uliftFunctor.{u + 1}) :=
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS (yoneda.obj X')).mpr
      (isAlgebraicSpace_yoneda B S hS X')).isSheaf
  obtain ⟨ξ, hξ⟩ := exists_completionSheafPoint_nthOrder B S hS T i hiT n hsheafX
  have hpaste := (IsPullback.of_hasPullback ξ
      (Space.completionSheafMap B S hS (yoneda.map f) T).hom).paste_vert
    (isPullback_completionSheafInclusion B S hS (yoneda.map f) T hsheafX' hsheafX).flip
  rw [hξ] at hpaste
  have hsq : IsPullback
      (Functor.whiskerRight (yoneda.map (pullback.fst (nthOrderOverToBase B S hS i n) f))
        uliftFunctor.{u + 1})
      (Functor.whiskerRight (yoneda.map (pullback.snd (nthOrderOverToBase B S hS i n) f))
        uliftFunctor.{u + 1})
      (Functor.whiskerRight (yoneda.map (nthOrderOverToBase B S hS i n)) uliftFunctor.{u + 1})
      (Functor.whiskerRight (yoneda.map f) uliftFunctor.{u + 1}) :=
    ((IsPullback.of_hasPullback (nthOrderOverToBase B S hS i n) f).map
        (yoneda (C := BigFppfOver B S hS))).map
      ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
        uliftFunctor.{u + 1})
  have hfst : Space.IsEtaleULift.{u + 1} B S hS
      (Functor.whiskerRight (yoneda.map (pullback.fst (nthOrderOverToBase B S hS i n) f))
        uliftFunctor.{u + 1}) := by
    have heq := hsq.isoIsPullback_hom_fst _ _ hpaste
    rw [← heq]
    exact isEtaleULift_precomp B S hS (hsq.isoIsPullback _ _ hpaste).hom _
      (hprop (nthOrderOver B S hS i n) ξ)
  have hEt : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      (pullback.fst (nthOrderOverToBase B S hS i n) f)) :=
    (Space.presheaf_yoneda_map_etale_iff B S hS
        (pullback.fst (nthOrderOverToBase B S hS i n) f)).1
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS
          (yoneda.map (pullback.fst (nthOrderOverToBase B S hS i n) f))).1
        ((Space.isEtaleULift_whiskerRight_iff B S hS
          (yoneda.map (pullback.fst (nthOrderOverToBase B S hS i n) f))).1 hfst))
  have hps : IsPullback ((BigFppfOver.toScheme B S hS).map
        (pullback.fst (nthOrderOverToBase B S hS i n) f))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd (nthOrderOverToBase B S hS i n) f))
      (Stacks.Thickenings.nthOrderToBase i n) ((BigFppfOver.toScheme B S hS).map f) := by
    have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
      Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
    rw [← toScheme_map_nthOrderOverToBase B S hS i n]
    exact (IsPullback.of_hasPullback (nthOrderOverToBase B S hS i n) f).map
      (BigFppfOver.toScheme B S hS)
  have hps2 : IsPullback
      (pullback.snd ((BigFppfOver.toScheme B S hS).map f) (Stacks.Thickenings.nthOrderToBase i n))
      (pullback.fst ((BigFppfOver.toScheme B S hS).map f) (Stacks.Thickenings.nthOrderToBase i n))
      (Stacks.Thickenings.nthOrderToBase i n) ((BigFppfOver.toScheme B S hS).map f) :=
    (IsPullback.of_hasPullback ((BigFppfOver.toScheme B S hS).map f)
      (Stacks.Thickenings.nthOrderToBase i n)).flip
  have : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange.respectsIso
  rw [← hps2.isoIsPullback_hom_fst _ _ hps]
  exact MorphismProperty.RespectsIso.precomp
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) _ _ hEt

/-- Let `f : X' ⟶ X` be a morphism of the big fppf site over `S` which is locally of finite
type, let `X` be locally Noetherian, let `T` be a set of points of `X` and let `i : Z ⟶ X` be a
closed subscheme whose set of points is `T`. If `f` is étale at every point of `X'` outside
`|f|⁻¹ T` and the morphism of completions `f_{/T}` is étale, then `f` is étale. -/
@[stacks 0AR4 "the étale clause: a morphism locally of finite type which is étale away from \
`T` and whose completion `f_{/T}` is étale is étale everywhere, by Tag 0A43 \
(`AlgebraicGeometry.etaleAt_of_etale_infinitesimalNeighbourhoods`) above the closed subscheme \
cut out by `T`. Stated for `f` locally of finite type over a locally Noetherian `X`, where \
the source has `f` of finite type over an affine Noetherian `X`. The existence clause of the \
tag is not stated"]
theorem isEtale_of_isEtale_completionSheafMap
    {X' X : BigFppfOver B S hS} (f : X' ⟶ X)
    (T : Set (Space.points B S hS (yoneda.obj X)))
    {Z : Scheme.{u}} (i : Z ⟶ (BigFppfOver.toScheme B S hS).obj X)
    [IsClosedImmersion i]
    [_root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj X)]
    (hiT : Set.range i = Space.pointsToScheme B S hS X '' T)
    (hf : Space.IsLocallyOfFiniteType B S hS (yoneda.map f))
    (haway : ∀ p : Space.points B S hS (yoneda.obj X'),
      Space.pointsMap B S hS (yoneda.obj X') (yoneda.map f) p ∉ T →
        AlgebraicGeometry.EtaleAt ((BigFppfOver.toScheme B S hS).map f)
          (Space.pointsToScheme B S hS X' p))
    (hetale : ∃ hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.completionSheafMap B S hS (yoneda.map f) T).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun ⦃A C : Space.AlgebraicSpacesULift.{u + 1} B S hS⦄ (g : A ⟶ C) ↦
          Space.IsEtaleULift.{u + 1} B S hS g.hom)
        (Space.completionSheafMap B S hS (yoneda.map f) T).hom hrep) :
    Space.IsEtale B S hS (yoneda.map f) := by
  have hid : ∀ U : BigFppfOver B S hS,
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj U)) := fun U ↦ by
    simpa using (Space.presheaf_yoneda_map_etale_iff B S hS (𝟙 U)).2 inferInstance
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map f) :=
    hf X' X (𝟙 _) (𝟙 _) f (hid X') (hid X) (by simp)
  rw [Space.isEtale_iff_presheaf_of_yoneda, Space.presheaf_yoneda_map_etale_iff,
    AlgebraicGeometry.etale_iff_forall_etaleAt]
  intro x
  obtain ⟨p, rfl⟩ := Space.surjective_pointsToScheme B S hS X' x
  by_cases hmem : (BigFppfOver.toScheme B S hS).map f
      (Space.pointsToScheme B S hS X' p) ∈ Set.range i
  · exact AlgebraicGeometry.etaleAt_of_etale_infinitesimalNeighbourhoods _ i
      (etale_pullback_nthOrderToBase_of_isEtale_completionSheafMap B S hS f T i hiT hetale)
      _ hmem
  · refine haway p fun hT ↦ hmem ?_
    rw [hiT]
    exact ⟨_, hT, Space.pointsToScheme_pointsMap B S hS f p⟩

end AlgebraicGeometry.FormalSpace

end
