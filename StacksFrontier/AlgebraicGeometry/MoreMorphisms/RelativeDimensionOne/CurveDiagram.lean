module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeDimensionOne.StageDiagram
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeDimensionOne.GenericFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeDimensionOne.FibreDensity
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Improving morphisms of relative dimension one

Let `f : X ⟶ S` be separated and of finite presentation, and let `η` be a generic point of an
irreducible component of `S` with `dim(X_η) ≤ 1`. Then, after shrinking `S` to an open
neighbourhood `U` of `η` and base changing along a finite, surjective, universally injective
`V ⟶ U`, the base change `X_V` is covered, by a finite surjective `ν`, by smooth families of curves
`Yᵢ ⟶ Tᵢ` over finite étale `V`-schemes `Tᵢ`, each an open in a smooth proper family `Ȳᵢ ⟶ Tᵢ`
with geometrically connected fibres of dimension at most one, and `ν` is a thickening over an
open `W ⊆ X_V` dense in all fibres. This is [Stacks, Tag 0GK7].

## Main results

* `AlgebraicGeometry.exists_curveDiagram_near_genericPoint`: [Stacks, Tag 0GK7].

## Implementation notes

The source's proof is followed. The base is first made reduced, then affine around `η` with
`κ(η) = 𝒪_{S, η}`; [Stacks, Tag 0GK5] is applied to the generic fibre; the purely inseparable
extension it requires is realised by a finite locally free, surjective, universally injective
cover of a principal open neighbourhood of `η`, exactly as in [Stacks, Tag 0H43]; and the whole
diagram over the residue field of the point over `η` is descended to a principal open
neighbourhood by `AlgebraicGeometry.exists_stage_curveDiagram`, the fibrewise density conditions
being read off at the end by `AlgebraicGeometry.dense_preimage_fiberι_of_smooth` and
`AlgebraicGeometry.dense_preimage_fiberι_of_surjective`.

The base change `X_V = V ×_S X` is any pullback square over `V ⟶ U ⟶ S`, and `X_U` is the
restriction of `X` to `U`, through which the projection `X_V ⟶ X` factors. The disjoint unions
`∐ Yᵢ`, `∐ Tᵢ`, `∐ Ȳᵢ` are indexed by `Fin n`; the proof produces `n = 1`, all the summands of
the source being collected in one.

## References

* [Stacks Project, Tag 0GK7](https://stacks.math.columbia.edu/tag/0GK7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Finite morphisms are stable under isomorphism. -/
private instance respectsIso_isFinite : MorphismProperty.RespectsIso (@IsFinite.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- Closed immersions are stable under composition. -/
private instance isStableUnderComposition_isClosedImmersion :
    MorphismProperty.IsStableUnderComposition @IsClosedImmersion.{u} :=
  ⟨fun a c ha hc => by have := ha; have := hc; infer_instance⟩

/-- **The conclusion of [Stacks, Tag 0GK7] from one smooth family of curves.** A single finite
étale `T ⟶ V`, smooth proper `q̄ : Ȳ ⟶ T` with geometrically connected fibres of dimension at most
one, open immersion `j : Y ⟶ Ȳ`, and finite surjective `ν : Y ⟶ X_V` closed immersion over an
open `W` whose preimage meets every fibre of `j ≫ q̄`, give the diagram of the tag with `n = 1`. -/
theorem exists_fin_curveDiagram_of_single {V XV : Scheme.{u}} (pV : XV ⟶ V)
    {T Ybar Y : Scheme.{u}} (t : T ⟶ V) (qbar : Ybar ⟶ T) (jY : Y ⟶ Ybar) (ν : Y ⟶ XV)
    (hcomm : ν ≫ pV = jY ≫ qbar ≫ t) (W : XV.Opens)
    (htf : IsFinite t) (hte : Etale t) (hqs : Smooth qbar) (hqp : IsProper qbar)
    (hqc : GeometricallyConnected qbar) (hqd : ∀ s, topologicalKrullDim (qbar.fiber s) ≤ 1)
    (hj : IsOpenImmersion jY) (hνf : IsFinite ν) (hνs : Surjective ν)
    (hW : IsClosedImmersion (ν ∣_ W)) (hWs : ∀ s : T, ∃ y : Y, ν y ∈ W ∧ qbar (jY y) = s) :
    ∃ (n : ℕ) (T' Y' Ybar' : Fin n → Scheme.{u}) (t' : ∀ i, T' i ⟶ V) (q' : ∀ i, Y' i ⟶ T' i)
      (qbar' : ∀ i, Ybar' i ⟶ T' i) (j' : ∀ i, Y' i ⟶ Ybar' i) (ν' : (∐ Y') ⟶ XV),
      (∀ i, j' i ≫ qbar' i = q' i) ∧ (∀ i, Sigma.ι Y' i ≫ ν' ≫ pV = q' i ≫ t' i) ∧
      IsFinite ν' ∧ Surjective ν' ∧
      (∀ s : V, Dense ((pV.fiberι s) ⁻¹' (W : Set XV))) ∧
      (∀ i (s : T' i), Dense (((q' i).fiberι s) ⁻¹' ((Sigma.ι Y' i ≫ ν') ⁻¹' (W : Set XV)))) ∧
      Stacks.Thickenings.IsThickening (ν' ∣_ W) ∧
      (∀ i, IsOpenImmersion (j' i)) ∧ (∀ i, IsFinite (t' i) ∧ Etale (t' i)) ∧
      (∀ i, Surjective (q' i) ∧ Smooth (q' i)) ∧
      (∀ i, IsProper (qbar' i) ∧ Smooth (qbar' i) ∧
        (∀ s : T' i, GeometricallyConnected ((qbar' i).fiberToSpecResidueField s)) ∧
        ∀ s : T' i, topologicalKrullDim ((qbar' i).fiber s) ≤ 1) := by
  classical
  let Yc : Fin 1 → Scheme.{u} := fun _ => Y
  let e := coproductUniqueIso Yc
  have he : ∀ i : Fin 1, Sigma.ι Yc i ≫ e.hom = 𝟙 Y := fun i => by
    obtain rfl : i = default := Subsingleton.elim _ _
    rw [← coproductUniqueIso_inv, Iso.inv_hom_id]
  let ν' : (∐ Yc) ⟶ XV := e.hom ≫ ν
  have hνi : ∀ i : Fin 1, Sigma.ι Yc i ≫ ν' = ν := fun i => by
    rw [← Category.assoc, he, Category.id_comp]
  have hO : IsOpen (ν ⁻¹' (W : Set XV)) := W.isOpen.preimage ν.continuous
  have hdense₁ : ∀ s : T, Dense (((jY ≫ qbar).fiberι s) ⁻¹' (ν ⁻¹' (W : Set XV))) :=
    dense_preimage_fiberι_of_smooth qbar jY hO hWs
  have hν'f : IsFinite ν' := (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr hνf
  have hν's : Surjective ν' := (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr hνs
  refine ⟨1, fun _ => T, Yc, fun _ => Ybar, fun _ => t, fun _ => jY ≫ qbar, fun _ => qbar,
    fun _ => jY, ν', fun _ => rfl, fun i => by rw [← Category.assoc, hνi, hcomm]; simp, hν'f,
    hν's,
    dense_preimage_fiberι_of_surjective pV t (jY ≫ qbar) ν hcomm _ hdense₁,
    fun i s => by rw [hνi]; exact hdense₁ s, ⟨?_, ?_⟩, fun _ => hj, fun _ => ⟨htf, hte⟩,
    fun _ => ⟨?_, inferInstance⟩,
    fun _ => ⟨hqp, hqs, (GeometricallyConnected.iff_geometricallyConnected_fiber _).mp hqc, hqd⟩⟩
  · have hiso : IsIso (e.hom ∣_ ν ⁻¹ᵁ W) :=
      IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms _)
        (inferInstanceAs (IsIso e.hom)) _
    have : IsClosedImmersion (e.hom ∣_ ν ⁻¹ᵁ W) := inferInstance
    change IsClosedImmersion ((e.hom ≫ ν) ∣_ W)
    rw [morphismRestrict_comp]
    exact MorphismProperty.comp_mem _ _ _ this hW
  · rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := hν's.1 x
    exact ⟨⟨y, hx⟩, Subtype.ext (morphismRestrict_base_coe ν' W ⟨y, hx⟩)⟩
  · exact ⟨fun s => (hWs s).imp fun _ h => h.2⟩

/-- **The input of the descent step, from the diagram over a field.** The diagram of
`AlgebraicGeometry.exists_curveDiagram_over_field` over `Spec k'`, transported along an
isomorphism `Spec k' ≅ L` and an identification of the base change of `X` with an object `X_L`
over `L`, gives objects and morphisms over `L` in the shape consumed by
`AlgebraicGeometry.exists_stage_curveDiagram`. -/
theorem exists_limitCurveData {L Xk T Ybar Y : Scheme.{u}} (k' : Type u) [Field k']
    (eK : Spec (.of k') ≅ L) (pr : Xk ⟶ Spec (.of k')) [LocallyOfFiniteType pr]
    [QuasiCompact pr] (XL : Over L) (eX : Xk ≅ XL.left) (heX : eX.hom ≫ XL.hom = pr ≫ eK.hom)
    (t : T ⟶ Spec (.of k')) (qbar : Ybar ⟶ T) (jY : Y ⟶ Ybar) (ν : Y ⟶ Xk) (W : Xk.Opens)
    (hcomm : ν ≫ pr = jY ≫ qbar ≫ t)
    (htf : IsFinite t) (hte : Etale t) (hqs : Smooth qbar) (hqp : IsProper qbar)
    (hqc : GeometricallyConnected qbar) (hqd : ∀ s, topologicalKrullDim (qbar.fiber s) ≤ 1)
    (hj : IsOpenImmersion jY) (hνf : IsFinite ν) (hνs : Surjective ν)
    (hW : IsClosedImmersion (ν ∣_ W)) (hWs : ∀ s : T, ∃ y : Y, ν y ∈ W ∧ qbar (jY y) = s) :
    ∃ (OT OYb OY OW : Over L) (mq : OYb ⟶ OT) (mj : OY ⟶ OYb) (mν : OY ⟶ XL) (mw : OW ⟶ XL),
      FinitePresentation OT.hom ∧ FinitePresentation OYb.hom ∧ FinitePresentation OY.hom ∧
      FinitePresentation OW.hom ∧ IsFinite OT.hom ∧ Etale OT.hom ∧ Smooth mq.left ∧
      IsProper mq.left ∧ GeometricallyConnected mq.left ∧
      (∀ s, topologicalKrullDim (mq.left.fiber s) ≤ 1) ∧ IsOpenImmersion mj.left ∧
      IsFinite mν.left ∧ Surjective mν.left ∧ IsOpenImmersion mw.left ∧
      IsClosedImmersion (pullback.snd mν.left mw.left) ∧
      Surjective (pullback.fst mν.left mw.left ≫ mj.left ≫ mq.left) := by
  have : IsLocallyNoetherian L := isLocallyNoetherian_of_isOpenImmersion eK.inv
  have : IsNoetherian Xk := isNoetherian_of_locallyOfFiniteType_of_quasiCompact k' pr
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have : IsNoetherian W.toScheme := ⟨⟩
  let OT := Over.mk (t ≫ eK.hom)
  let OYb := Over.mk (qbar ≫ t ≫ eK.hom)
  let OY := Over.mk (jY ≫ qbar ≫ t ≫ eK.hom)
  let OW := Over.mk (W.ι ≫ pr ≫ eK.hom)
  have hYfac : jY ≫ qbar ≫ t ≫ eK.hom = ν ≫ pr ≫ eK.hom := by rw [reassoc_of% hcomm]
  let mν : OY ⟶ XL := Over.homMk (ν ≫ eX.hom) (by
    change (ν ≫ eX.hom) ≫ XL.hom = jY ≫ qbar ≫ t ≫ eK.hom
    rw [Category.assoc, heX, hYfac])
  let mw : OW ⟶ XL := Over.homMk (W.ι ≫ eX.hom) (by
    change (W.ι ≫ eX.hom) ≫ XL.hom = W.ι ≫ pr ≫ eK.hom
    rw [Category.assoc, heX])
  have hsq := isPullback_pullback_comp_iso ν W.ι eX
  have hφs := hsq.isoIsPullback_inv_snd _ _ (IsPullback.of_hasPullback (ν ≫ eX.hom) (W.ι ≫ eX.hom))
  have hφf := hsq.isoIsPullback_inv_fst _ _ (IsPullback.of_hasPullback (ν ≫ eX.hom) (W.ι ≫ eX.hom))
  refine ⟨OT, OYb, OY, OW, Over.homMk qbar rfl, Over.homMk jY rfl, mν, mw,
    show FinitePresentation (t ≫ eK.hom) from finitePresentation_of_finiteType _,
    show FinitePresentation (qbar ≫ t ≫ eK.hom) from finitePresentation_of_finiteType _, ?_,
    show FinitePresentation (W.ι ≫ pr ≫ eK.hom) from finitePresentation_of_finiteType _,
    inferInstanceAs (IsFinite (t ≫ eK.hom)),
    inferInstanceAs (Etale (t ≫ eK.hom)), hqs, hqp, hqc, hqd, hj,
    inferInstanceAs (IsFinite (ν ≫ eX.hom)), inferInstanceAs (Surjective (ν ≫ eX.hom)),
    inferInstanceAs (IsOpenImmersion (W.ι ≫ eX.hom)), ?_, ?_⟩
  · change FinitePresentation (jY ≫ qbar ≫ t ≫ eK.hom)
    rw [hYfac]
    exact finitePresentation_of_finiteType (ν ≫ pr ≫ eK.hom)
  · change IsClosedImmersion (pullback.snd (ν ≫ eX.hom) (W.ι ≫ eX.hom))
    rw [← hφs]
    have : IsClosedImmersion (pullback.snd ν W.ι) := by
      rw [prop_snd_iff_morphismRestrict @IsClosedImmersion (IsPullback.of_hasPullback ν W.ι),
        Scheme.Opens.opensRange_ι]
      exact hW
    infer_instance
  · change Surjective (pullback.fst (ν ≫ eX.hom) (W.ι ≫ eX.hom) ≫ jY ≫ qbar)
    rw [← hφf, Category.assoc]
    have : Surjective (pullback.fst ν W.ι ≫ jY ≫ qbar) := by
      refine ⟨fun s => ?_⟩
      obtain ⟨y, hy, hys⟩ := hWs s
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := ν) (g := W.ι) y
        ⟨ν y, hy⟩ rfl
      exact ⟨z, by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hz, hys]⟩
    infer_instance

/-- **[Stacks, Tag 0GK7] over a reduced base, with one smooth family.** -/
theorem exists_curveDiagram_of_isReduced {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (hf : FinitePresentation f) [IsReduced S] (η : S) (hη : η ∈ genericPoints S)
    (hdim : topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (v : V ⟶ U.toScheme),
      IsFinite v ∧ Surjective v ∧ UniversallyInjective v ∧
      ∃ (XV : Scheme.{u}) (a : XV ⟶ X) (pV : XV ⟶ V), IsPullback a pV f (v ≫ U.ι) ∧
      ∃ (T Ybar Y : Scheme.{u}) (t : T ⟶ V) (qbar : Ybar ⟶ T) (jY : Y ⟶ Ybar) (ν : Y ⟶ XV)
        (W : XV.Opens), ν ≫ pV = jY ≫ qbar ≫ t ∧ IsFinite t ∧ Etale t ∧ Smooth qbar ∧
        IsProper qbar ∧ GeometricallyConnected qbar ∧
        (∀ s, topologicalKrullDim (qbar.fiber s) ≤ 1) ∧ IsOpenImmersion jY ∧ IsFinite ν ∧
        Surjective ν ∧ IsClosedImmersion (ν ∣_ W) ∧
        ∀ s : T, ∃ y : Y, ν y ∈ W ∧ qbar (jY y) = s := by
  classical
  obtain ⟨R, α, hα, 𝔭, hpη, hp⟩ :=
    Stacks.SmoothStrata.exists_affine_genericPoint_isField η
      ⟨closure {η}, hη, rfl⟩
  have : IsOpenImmersion α := hα
  let := hp.toField
  let K := Localization.AtPrime 𝔭.asIdeal
  let ξ : Spec (.of K) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ α
  let fη : pullback f ξ ⟶ Spec (.of K) := pullback.snd f ξ
  have hfiber := Stacks.GenericFlatness.finitePresentation_pullback ξ (Over.mk f) hf
  have : LocallyOfFinitePresentation fη := hfiber.1
  have : QuasiCompact fη := hfiber.2.1
  have : IsSeparated fη := MorphismProperty.of_isPullback (IsPullback.of_hasPullback f ξ) ‹_›
  have : LocallyOfFiniteType fη := inferInstance
  have : LocallyOfFiniteType f := by have := hf.1; infer_instance
  have hξη : ∀ o : Spec (.of K), ξ o = η := fun o => by
    have ho : o = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [ho, ← hpη]
    change α (Spec.map (CommRingCat.ofHom (algebraMap R K)) (IsLocalRing.closedPoint K)) = α 𝔭
    congr 1
    exact PrimeSpectrum.ext (IsLocalization.AtPrime.under_maximalIdeal K 𝔭.asIdeal)
  have hdimK : topologicalKrullDim (pullback f ξ : Scheme.{u}) ≤ 1 := by
    let o : Spec (.of K) := IsLocalRing.closedPoint K
    have hpre : ⇑fη ⁻¹' {o} = Set.univ :=
      Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
    have h₁ : topologicalKrullDim (pullback f ξ : Scheme.{u}) =
        topologicalKrullDim (⇑fη ⁻¹' {o}) := by
      rw [hpre]
      exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).symm
    have h₂ := congrFun (Scheme.Hom.fiberDimension_eq_of_isPullback
      (IsPullback.of_hasPullback f ξ)) o
    rw [h₁, ← IsHomeomorph.topologicalKrullDim_eq _ (fη.fiberHomeo o).isHomeomorph]
    change fη.fiberDimension o ≤ 1
    rw [h₂, Function.comp_apply, hξη]
    exact hdim
  obtain ⟨k', hfield, halg, hfin, hpi, T, Ybar, Y, t, qbar, jY, ν, W, hcomm, htf, hte, hqs, hqp,
    hqc, hqd, hj, hνf, hνs, hW, hWs⟩ := exists_curveDiagram_over_field K fη hdimK
  let := hfield
  let := halg
  have : Module.Finite K k' := hfin
  obtain ⟨i, Vo, hVfp, hVfree, hVsurj, hVinj, ⟨eV⟩⟩ :=
    Stacks.SmoothStrata.PrincipalLocalization.exists_purelyInseparable_cover 𝔭.asIdeal hp k' hpi
  let I := ULiftHom.{u} (Stacks.SmoothStrata.PrincipalLocalization.Index 𝔭.asIdeal)ᵒᵖ
  let F₀ : I ⥤ (Stacks.SmoothStrata.PrincipalLocalization.Index 𝔭.asIdeal)ᵒᵖ :=
    { obj A := A
      map h := h.down }
  have : IsCofiltered I := IsCofiltered.of_equivalence ULiftHom.equiv
  have : F₀.Initial := Functor.initial_of_adjunction ULiftHom.equiv.symm.toAdjunction
  let D₀ := F₀ ⋙ Stacks.SmoothStrata.PrincipalLocalization.diagram 𝔭.asIdeal
  let c₀ := (Stacks.SmoothStrata.PrincipalLocalization.cone 𝔭.asIdeal).whisker F₀
  have hc₀ : IsLimit c₀ :=
    (Functor.Initial.isLimitWhiskerEquiv F₀
      (Stacks.SmoothStrata.PrincipalLocalization.cone 𝔭.asIdeal)).symm
      (Stacks.SmoothStrata.PrincipalLocalization.cone_isLimit 𝔭.asIdeal)
  let i₀ : I := i
  have : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have : ∀ {i j : I} (h : i ⟶ j), IsAffineHom (D₀.map h) :=
    fun h => Stacks.SmoothStrata.PrincipalLocalization.diagram_map_isAffine 𝔭.asIdeal (F₀.map h)
  have hD₀aff : ∀ i : I, IsAffine (D₀.obj i) := fun i => by
    change IsAffine (Spec (.of (Localization.Away (i.unop : R))))
    infer_instance
  have hVfin : IsFinite Vo.hom :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      Vo.hom).mp hVfree).1
  have : IsAffine Vo.left := by
    have : IsAffine (D₀.obj i₀) := hD₀aff i₀
    exact isAffine_of_isAffineHom (Y := D₀.obj i₀) Vo.hom
  let F : Over i₀ ⥤ Over Vo.left := Over.post D₀ ⋙ Over.pullback Vo.hom
  let cF : Cone F := (Over.pullback Vo.hom).mapCone ((Over.conePost D₀ i₀).obj c₀)
  have hcF : IsLimit cF := isLimitOfPreserves _ (Over.isLimitConePost i₀ hc₀)
  let E := F ⋙ Over.forget Vo.left
  let cE := (Over.forget Vo.left).mapCone cF
  have hcE : IsLimit cE := isLimitOfPreserves _ hcF
  have : ∀ {a b : Over i₀} (h : a ⟶ b), IsAffineHom (E.map h) :=
    fun h => MorphismProperty.overPullbackMap Vo.hom ((Over.post D₀).map h)
      (inferInstanceAs (IsAffineHom (D₀.map h.left)))
  have : ∀ a : Over i₀, IsAffine (E.obj a) := fun a => by
    have := hD₀aff a.left
    change IsAffine (pullback (D₀.map a.hom) Vo.hom)
    infer_instance
  let β := Stacks.SmoothStrata.PrincipalLocalization.baseMap 𝔭.asIdeal i ≫ α
  let v := Vo.hom ≫ β
  let fV := pullback.snd f v
  have hfV : FinitePresentation fV :=
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback f v) hf
  let gK := Spec.map (CommRingCat.ofHom (algebraMap K k'))
  let eK : Spec (.of k') ≅ cF.pt.left :=
    (Over.forget _).mapIso eV ≪≫ pullbackSymmetry Vo.hom (c₀.π.app i₀)
  have heK : eK.hom ≫ cF.pt.hom ≫ v = gK ≫ ξ := by
    change ((Over.forget _).mapIso eV ≪≫
      pullbackSymmetry Vo.hom (c₀.π.app i₀)).hom ≫
      pullback.snd (c₀.π.app i₀) Vo.hom ≫ Vo.hom ≫ β = _
    simp only [Iso.trans_hom, Functor.mapIso_hom, Over.forget_map, Category.assoc,
      pullbackSymmetry_hom_comp_snd_assoc]
    change eV.hom.left ≫ pullback.fst Vo.hom (c₀.π.app i₀) ≫ Vo.hom ≫ β = _
    rw [pullback.condition_assoc, ← Category.assoc,
      show eV.hom.left ≫ pullback.snd Vo.hom (c₀.π.app i₀) = gK from Over.w eV.hom]
    change gK ≫ (Stacks.SmoothStrata.PrincipalLocalization.cone 𝔭.asIdeal).π.app i ≫
      Stacks.SmoothStrata.PrincipalLocalization.baseMap 𝔭.asIdeal i ≫ α = gK ≫ ξ
    rw [← Category.assoc ((Stacks.SmoothStrata.PrincipalLocalization.cone 𝔭.asIdeal).π.app i),
      Stacks.SmoothStrata.PrincipalLocalization.cone_comp_baseMap]
  let a₀ : Over i₀ := Over.mk (𝟙 i₀)
  let X₀ : Over (E.obj a₀) := Over.mk (pullback.fst (F.obj a₀).hom fV)
  have hX₀ : FinitePresentation X₀.hom :=
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback (F.obj a₀).hom fV).flip hfV
  have hsq₂ : IsPullback (pullback.snd (F.obj a₀).hom fV ≫ pullback.fst f v) X₀.hom f
      ((F.obj a₀).hom ≫ v) :=
    (IsPullback.of_hasPullback (F.obj a₀).hom fV).flip.paste_horiz (IsPullback.of_hasPullback f v)
  have hsq₁ : IsPullback (pullback.snd gK fη ≫ pullback.fst f ξ) (pullback.fst gK fη ≫ eK.hom) f
      (cF.pt.hom ≫ v) :=
    IsPullback.of_iso ((IsPullback.of_hasPullback gK fη).flip.paste_horiz
        (IsPullback.of_hasPullback f ξ)) (Iso.refl _) (Iso.refl _) eK (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp [heK])
  have hw₀ : (cF.π.app a₀).left ≫ (F.obj a₀).hom = cF.pt.hom := Over.w (cF.π.app a₀)
  let ψ : pullback gK fη ⟶ pullback f v :=
    pullback.lift (pullback.snd gK fη ≫ pullback.fst f ξ) ((pullback.fst gK fη ≫ eK.hom) ≫
      cF.pt.hom) (by rw [Category.assoc, Category.assoc, ← hsq₁.w, Category.assoc])
  let φ : pullback gK fη ⟶ X₀.left :=
    pullback.lift ((pullback.fst gK fη ≫ eK.hom) ≫ (cF.π.app a₀).left) ψ (by
      rw [Category.assoc, hw₀, pullback.lift_snd])
  have hsq₃ : IsPullback φ (pullback.fst gK fη ≫ eK.hom) X₀.hom (cE.π.app a₀) := by
    have e₁ : φ ≫ pullback.snd (F.obj a₀).hom fV ≫ pullback.fst f v =
        pullback.snd gK fη ≫ pullback.fst f ξ := by
      simp only [φ, ψ, pullback.lift_snd_assoc, pullback.lift_fst]
    have e₂ : cE.π.app a₀ ≫ (F.obj a₀).hom ≫ v = cF.pt.hom ≫ v := by
      change (cF.π.app a₀).left ≫ (F.obj a₀).hom ≫ v = _
      rw [← Category.assoc, hw₀]
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) hsq₂
    rw [e₁, e₂]
    exact hsq₁
  let eXL := hsq₃.isoPullback
  have heXL : eXL.hom ≫ ((Over.pullback (cE.π.app a₀)).obj X₀).hom =
      pullback.fst gK fη ≫ eK.hom := hsq₃.isoPullback_hom_snd
  obtain ⟨OT, OYb, OY, OW, mq, mj, mν, mw, hOT, hOYb, hOY, hOW, hTf, hTe, hqs₀, hqp₀, hqc₀, hqd₀,
      hj₀, hνf₀, hνs₀, hw₀', hW₀, hWs₀⟩ :=
    exists_limitCurveData (L := cE.pt) k' eK (pullback.fst gK fη)
      ((Over.pullback (cE.π.app a₀)).obj X₀) eXL heXL t qbar jY ν W hcomm htf hte hqs hqp hqc
      hqd hj hνf hνs hW hWs
  obtain ⟨a, g, T', Ybar', Y', WL', qbar', jY', ν', w', hTf', hTe', hqs', hqp', hqc', hqd', hj',
      hνf', hνs', hw', hcl', hsu'⟩ :=
    exists_stage_curveDiagram E cE hcE a₀ X₀ hX₀ OT OYb OY OW hOT hOYb hOY hOW mq mj mν mw
      hTf hTe hqs₀ hqp₀ hqc₀ hqd₀ hj₀ hνf₀ hνs₀ hw₀' hW₀ hWs₀
  let β' := Stacks.SmoothStrata.PrincipalLocalization.baseMap 𝔭.asIdeal (F₀.obj a.left) ≫ α
  have : IsOpenImmersion
      (Stacks.SmoothStrata.PrincipalLocalization.baseMap 𝔭.asIdeal (F₀.obj a.left)) :=
    Stacks.SmoothStrata.PrincipalLocalization.baseMap_isOpenImmersion 𝔭.asIdeal _
  have : IsOpenImmersion β' := inferInstance
  have hηU : η ∈ β'.opensRange := by
    obtain ⟨z, hz⟩ :=
      Stacks.SmoothStrata.PrincipalLocalization.baseMap_mem_range 𝔭 (F₀.obj a.left)
    rw [← hpη]
    exact ⟨z, by
      change α (Stacks.SmoothStrata.PrincipalLocalization.baseMap 𝔭.asIdeal (F₀.obj a.left) z) =
        α 𝔭
      rw [hz]⟩
  let v' : (F.obj a).left ⟶ D₀.obj a.left := pullback.fst (D₀.map a.hom) Vo.hom
  have hvsurj : Surjective v' :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D₀.map a.hom) Vo.hom).flip hVsurj
  have hvinj : UniversallyInjective v' :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D₀.map a.hom) Vo.hom).flip hVinj
  have hvfin : IsFinite v' :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (D₀.map a.hom) Vo.hom).flip hVfin
  let vU : (F.obj a).left ⟶ β'.opensRange.toScheme := v' ≫ β'.isoOpensRange.hom
  have huiRI : MorphismProperty.RespectsIso (@UniversallyInjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hsurj : Surjective vU :=
    (MorphismProperty.cancel_right_of_respectsIso (@Surjective) _ _).mpr hvsurj
  have hinj : UniversallyInjective vU :=
    (MorphismProperty.cancel_right_of_respectsIso (@UniversallyInjective) _ _).mpr hvinj
  have hfin : IsFinite vU :=
    (MorphismProperty.cancel_right_of_respectsIso (@IsFinite) _ _).mpr hvfin
  have htotal : vU ≫ β'.opensRange.ι = (F.obj a).hom ≫ v := by
    dsimp [vU]
    rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]
    have hn : D₀.map a.hom ≫ β = β' := by
      change (Stacks.SmoothStrata.PrincipalLocalization.diagram 𝔭.asIdeal).map (F₀.map a.hom) ≫
        Stacks.SmoothStrata.PrincipalLocalization.baseMap 𝔭.asIdeal i ≫ α = _
      rw [← Category.assoc, Stacks.SmoothStrata.PrincipalLocalization.baseMap_naturality]
    rw [← hn, ← Category.assoc]
    change (pullback.fst (D₀.map a.hom) Vo.hom ≫ D₀.map a.hom) ≫ β =
      pullback.snd (D₀.map a.hom) Vo.hom ≫ Vo.hom ≫ β
    rw [pullback.condition, Category.assoc]
  let XV := (Over.pullback (E.map g)).obj X₀
  have hXVsq : IsPullback (pullback.fst X₀.hom (E.map g) ≫ pullback.snd (F.obj a₀).hom fV ≫
      pullback.fst f v) XV.hom f (vU ≫ β'.opensRange.ι) := by
    have h := (IsPullback.of_hasPullback X₀.hom (E.map g)).paste_horiz hsq₂
    have e : E.map g ≫ (F.obj a₀).hom ≫ v = vU ≫ β'.opensRange.ι := by
      rw [htotal, ← Category.assoc]
      exact congrArg (· ≫ v) (Over.w (F.map g))
    rw [← e]
    exact h
  have : IsOpenImmersion w'.left := hw'
  refine ⟨β'.opensRange, hηU, (F.obj a).left, vU, hfin, hsurj, hinj, XV.left, _, XV.hom, hXVsq,
    T'.left, Ybar'.left, Y'.left, T'.hom, qbar'.left, jY'.left, ν'.left, w'.left.opensRange,
    ?_, hTf', hTe', hqs', hqp', hqc', hqd', hj', hνf', hνs',
    (prop_snd_iff_morphismRestrict @IsClosedImmersion
      (IsPullback.of_hasPullback ν'.left w'.left)).mp hcl', ?_⟩
  · rw [Over.w ν', Over.w qbar', Over.w jY']
  · intro s
    obtain ⟨z, hz⟩ := hsu'.1 s
    refine ⟨pullback.fst ν'.left w'.left z, ⟨pullback.snd ν'.left w'.left z, ?_⟩, ?_⟩
    · rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    · simpa only [Scheme.Hom.comp_apply] using hz

/-- **[Stacks, Tag 0GK7] with one smooth family.** -/
theorem exists_curveDiagram_single {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (hf : FinitePresentation f) (η : S) (hη : η ∈ genericPoints S)
    (hdim : topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (v : V ⟶ U.toScheme),
      IsFinite v ∧ Surjective v ∧ UniversallyInjective v ∧
      ∃ (XV : Scheme.{u}) (a : XV ⟶ X) (pV : XV ⟶ V), IsPullback a pV f (v ≫ U.ι) ∧
      ∃ (T Ybar Y : Scheme.{u}) (t : T ⟶ V) (qbar : Ybar ⟶ T) (jY : Y ⟶ Ybar) (ν : Y ⟶ XV)
        (W : XV.Opens), ν ≫ pV = jY ≫ qbar ≫ t ∧ IsFinite t ∧ Etale t ∧ Smooth qbar ∧
        IsProper qbar ∧ GeometricallyConnected qbar ∧
        (∀ s, topologicalKrullDim (qbar.fiber s) ≤ 1) ∧ IsOpenImmersion jY ∧ IsFinite ν ∧
        Surjective ν ∧ IsClosedImmersion (ν ∣_ W) ∧
        ∀ s : T, ∃ y : Y, ν y ∈ W ∧ qbar (jY y) = s := by
  classical
  let r := S.nilradical.subschemeι
  have : IsReduced S.nilradical.subscheme := isReduced_nilradical_subscheme S
  have hsurj : Function.Surjective r := fun x =>
    Set.mem_range.mp (by rw [S.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)
  let h := r.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective hsurj
  obtain ⟨η', rfl⟩ := hsurj η
  have hη' : η' ∈ genericPoints S.nilradical.subscheme := (h.mem_genericPoints_iff η').mp hη
  let fr := pullback.snd f r
  have : IsSeparated fr := MorphismProperty.of_isPullback (IsPullback.of_hasPullback f r) ‹_›
  have hfr : FinitePresentation fr :=
    FinitePresentation.of_isPullback (IsPullback.of_hasPullback f r) hf
  have : LocallyOfFiniteType f := by have := hf.1; infer_instance
  have hdimr : topologicalKrullDim (fr.fiber η') ≤ 1 := by
    change fr.fiberDimension η' ≤ 1
    rw [Scheme.Hom.fiberDimension_eq_of_isPullback (IsPullback.of_hasPullback f r)]
    exact hdim
  obtain ⟨U', hηU', V, v, hvf, hvs, hvi, XV, a, pV, hsq, T, Ybar, Y, t, qbar, jY, ν, W, hrest⟩ :=
    exists_curveDiagram_of_isReduced fr hfr η' hη' hdimr
  let U : S.Opens := ⟨r '' U', h.isOpenMap _ U'.isOpen⟩
  have hU' : r ⁻¹ᵁ U = U' := by
    ext x
    change r x ∈ r '' (U' : Set S.nilradical.subscheme) ↔ x ∈ U'
    exact r.isClosedEmbedding.injective.mem_set_image
  let ρ : U'.toScheme ⟶ U.toScheme := (S.nilradical.subscheme.isoOfEq hU'.symm).hom ≫ r ∣_ U
  have hρ : ρ ≫ U.ι = U'.ι ≫ r := by
    simp only [ρ, Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
  have hρci : IsClosedImmersion ρ :=
    MorphismProperty.comp_mem _ _ _ inferInstance
      (IsZariskiLocalAtTarget.restrict (P := @IsClosedImmersion) inferInstance U)
  have hρs : Surjective ρ := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x', hx'U, hx'⟩ := y.2
    refine ⟨⟨x', hx'U⟩, U.ι.isOpenEmbedding.injective ?_⟩
    change (ρ ≫ U.ι) ⟨x', hx'U⟩ = U.ι y
    rw [hρ]
    exact hx'
  have hcompS : MorphismProperty.IsStableUnderComposition @Surjective.{u} :=
    ⟨fun a c ha hc => by have := ha; have := hc; infer_instance⟩
  have hρui : UniversallyInjective ρ := inferInstance
  have hρf : IsFinite ρ := inferInstance
  refine ⟨U, ⟨η', hηU', rfl⟩, V, v ≫ ρ, MorphismProperty.comp_mem _ _ _ hvf hρf,
    MorphismProperty.comp_mem _ _ _ hvs hρs, MorphismProperty.comp_mem _ _ _ hvi hρui, XV,
    a ≫ pullback.fst f r, pV, ?_, T, Ybar, Y, t, qbar, jY, ν, W, hrest⟩
  have e : (v ≫ U'.ι) ≫ r = (v ≫ ρ) ≫ U.ι := by
    rw [Category.assoc, Category.assoc, hρ]
  rw [← e]
  exact hsq.paste_horiz (IsPullback.of_hasPullback f r)

/-- **Stacks Project, Tag 0GK7.** Let `f : X ⟶ S` be separated and of finite presentation, and
let `η` be a generic point of an irreducible component of `S` such that `dim(X_η) ≤ 1`. Then
there are

1. an open neighbourhood `U` of `η`,
2. a finite, surjective, universally injective morphism `V ⟶ U`,
3. the base change `X_V = V ×_S X`, a pullback square over `V ⟶ U ⟶ S`,
4. a finite surjective morphism `ν : ∐ Yᵢ ⟶ X_V` and an open `W ⊆ X_V` such that `W` is dense
   in all fibres of `X_V ⟶ V`, `ν⁻¹(W) ∩ Yᵢ` is dense in all fibres of `Yᵢ ⟶ Tᵢ`, and
   `ν⁻¹(W) ⟶ W` is a thickening,
5. open immersions `jᵢ : Yᵢ ⟶ Ȳᵢ`,
6. finite étale morphisms `Tᵢ ⟶ V`,
7. surjective smooth morphisms `Yᵢ ⟶ Tᵢ`, and
8. smooth proper morphisms `Ȳᵢ ⟶ Tᵢ` with geometrically connected fibres of dimension at most
   one,

such that the diagram commutes: `jᵢ ≫ (Ȳᵢ ⟶ Tᵢ) = (Yᵢ ⟶ Tᵢ)` and the map `Yᵢ ⟶ X_V ⟶ V` is
`Yᵢ ⟶ Tᵢ ⟶ V`. -/
@[stacks 0GK7]
theorem exists_curveDiagram_near_genericPoint {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (hf : FinitePresentation f) (η : S) (hη : η ∈ genericPoints S)
    (hdim : topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (v : V ⟶ U.toScheme),
      IsFinite v ∧ Surjective v ∧ UniversallyInjective v ∧
      ∃ (XV : Scheme.{u}) (a : XV ⟶ X) (pV : XV ⟶ V), IsPullback a pV f (v ≫ U.ι) ∧
      ∃ (n : ℕ) (T Y Ybar : Fin n → Scheme.{u}) (t : ∀ i, T i ⟶ V) (q : ∀ i, Y i ⟶ T i)
        (qbar : ∀ i, Ybar i ⟶ T i) (j : ∀ i, Y i ⟶ Ybar i) (ν : (∐ Y) ⟶ XV) (W : XV.Opens),
        (∀ i, j i ≫ qbar i = q i) ∧ (∀ i, Sigma.ι Y i ≫ ν ≫ pV = q i ≫ t i) ∧
        IsFinite ν ∧ Surjective ν ∧
        (∀ s : V, Dense ((pV.fiberι s) ⁻¹' (W : Set XV))) ∧
        (∀ i (s : T i), Dense (((q i).fiberι s) ⁻¹' ((Sigma.ι Y i ≫ ν) ⁻¹' (W : Set XV)))) ∧
        Stacks.Thickenings.IsThickening (ν ∣_ W) ∧
        (∀ i, IsOpenImmersion (j i)) ∧ (∀ i, IsFinite (t i) ∧ Etale (t i)) ∧
        (∀ i, Surjective (q i) ∧ Smooth (q i)) ∧
        (∀ i, IsProper (qbar i) ∧ Smooth (qbar i) ∧
          (∀ s : T i, GeometricallyConnected ((qbar i).fiberToSpecResidueField s)) ∧
          ∀ s : T i, topologicalKrullDim ((qbar i).fiber s) ≤ 1) := by
  obtain ⟨U, hηU, V, v, hvf, hvs, hvi, XV, a, pV, hsq, T, Ybar, Y, t, qbar, jY, ν, W, hcomm, htf,
    hte, hqs, hqp, hqc, hqd, hj, hνf, hνs, hW, hWs⟩ := exists_curveDiagram_single f hf η hη hdim
  obtain ⟨n, T', Y', Ybar', t', q', qbar', j', ν', h⟩ := exists_fin_curveDiagram_of_single pV t
    qbar jY ν hcomm W htf hte hqs hqp hqc hqd hj hνf hνs hW hWs
  exact ⟨U, hηU, V, v, hvf, hvs, hvi, XV, a, pV, hsq, n, T', Y', Ybar', t', q', qbar', j', ν', W, h⟩

end AlgebraicGeometry

end
