module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineRigEtaleAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLiftGluing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleRigEtale
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.CategoryTheory.Sites.Density
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Stacks 0GDR: the affine case of fullness, and the statement

This file proves `AlgebraicGeometry.Space.AffineCompletionLiftProperty`, the local existence
statement over a Noetherian affine base to which
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLiftGluing` reduces the fullness half of
Stacks 0GDR. The argument is the source's: for a point `q` of `Y₁` over `T`, choose an affine `V`
étale over `X'` through the image of `q` under `α`; the fibre product
`W = Y_{1,/T} ×_{X'_{/T}} V_{/T}` is representable étale over `Y_{1,/T}`, hence covered by
Noetherian affine formal algebraic spaces rig-étale over `Y_{1,/T}`; Stacks 0AR4 algebraizes the
piece through `q` as `Y' ⟶ Y₁` étale, and Stacks 0AR3, applied to the induced morphism
`Y'_{/T} ⟶ V_{/T}`, produces the étale neighbourhood `Y'' ⟶ Y'` and the morphism `Y'' ⟶ V`.
Together with the faithfulness half and the reductions of
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionLiftGluing` this gives Stacks 0GDR.

## Main results

* `AlgebraicGeometry.Space.exists_isCompletionLift_of_completionSheafMap_eq`: the Stacks 0AR3
  step: a morphism `Y'_{/T} ⟶ V_{/T}` compatible with `α` yields the étale neighbourhood
  `Y'' ⟶ Y'` and a lift of `α` along it, and every section of `Y₁` over `T` coming from
  `Y'_{/T}` factors through `Y''`.
* `AlgebraicGeometry.Space.exists_isCompletionLift_affineOver` and
  `AlgebraicGeometry.Space.affineCompletionLiftProperty`: the affine case of Stacks 0GDR.
* `AlgebraicGeometry.Space.completionOverFunctor_map_bijective`: **Stacks 0GDR**, completion
  along `T` is a bijection `Mor_X(Y, X') ⟶ Mor_{X_{/T}}(Y_{/T}, X'_{/T})`.
* `AlgebraicGeometry.FormalSpace.finiteTypeModificationCompletionFullyFaithful`: its
  consequence, the functor of Stacks 0AR5 is fully faithful.

## Implementation notes

Sections of the completions are compared through
`AlgebraicGeometry.Space.completionSheafIsoSubfunctor` only in morphism form
(`AlgebraicGeometry.Space.exists_app_eq_of_completionOverMap_app_eq`), and the morphism
`V ⟶ X₁` enters Stacks 0AR3 only through an equation `yoneda.map fV = v ≫ f₁`, the completions
of `V` along the two descriptions of its points over `T₁` being identified by `eqToHom`.

## References

* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
* [Stacks Project, Tag 0AR3](https://stacks.math.columbia.edu/tag/0AR3)
* [Stacks Project, Tag 0AR4](https://stacks.math.columbia.edu/tag/0AR4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-! ### Preliminaries -/

/-- An affine Noetherian object of the site is isomorphic to `Spec` of its ring of global
sections, as an object `FormalSpace.affineOver` of the site. -/
theorem exists_isIso_affineOver (Y : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsNoetherianRing R) (hR : B.Contains (Spec (.of R)))
      (s : Spec (.of R) ⟶ S) (ι : FormalSpace.affineOver B S hS hR s ⟶ Y),
      IsIso ((BigFppfOver.toScheme B S hS).map ι) := by
  have hR := FormalSpace.contains_spec_globalSections B S hS Y
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  refine ⟨Γ((BigFppfOver.toScheme B S hS).obj Y, ⊤), inferInstance, inferInstance, hR,
    ((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv ≫ Y.hom.hom,
    FormalSpace.siteHom B S hS ((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv rfl, ?_⟩
  show IsIso ((BigFppfOver.toScheme B S hS).obj Y).isoSpec.inv
  infer_instance

/-- **Completion of an étale morphism of algebraic spaces is representable étale** (Stacks 0GI0),
in the form of the completion of a morphism over `X`. -/
theorem isRepresentableEtale_completionOverMap {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (points B S hS X)) {M N : Over X} (a : M ⟶ N)
    (hM : IsAlgebraicSpace B S hS M.left) (hN : IsAlgebraicSpace B S hS N.left)
    (ha : IsEtale B S hS a.left) :
    FormalSpace.IsRepresentableEtale B S hS (completionOverMap B S hS T a) := by
  obtain ⟨hrep, hprop⟩ := FormalSpace.isEtale_completionSheafMap B S hS hM hN a.left
    (pointsMap B S hS N.left N.hom ⁻¹' T) ha
  exact (FormalSpace.isRepresentableEtale_of_isIso B S hS _).comp B S hS ⟨hrep, hprop⟩

/-- A covering sieve of an object of the site contains, through every point of that object, an
arrow whose source has a point. -/
theorem exists_mem_point_of_mem_topology {Z : BigFppfOver B S hS} {R : Sieve Z}
    (hR : R ∈ BigFppfOver.topology B S hS Z) (z : (BigFppfOver.toScheme B S hS).obj Z) :
    ∃ (Z' : BigFppfOver B S hS) (k : Z' ⟶ Z), R k ∧ Nonempty (points B S hS (yoneda.obj Z')) := by
  obtain ⟨c, k, hk, -, -, ⟨x, -⟩⟩ := BigFppfOver.exists_mem_of_mem_topology B S hS hR z
  obtain ⟨r, -⟩ := surjective_pointsToScheme B S hS c x
  exact ⟨c, k, hk, ⟨r⟩⟩

/-- **An affine étale chart through a point.** For a morphism `x : h_{K₀} ⟶ X'` into a locally
Noetherian algebraic space and a point `k` of `K₀` there are a Noetherian affine object `V` with an
étale morphism `v : h_V ⟶ X'` and an object `Z` with a morphism `p : Z ⟶ K₀` through `k` and a
morphism `Z ⟶ V` over `X'`. -/
theorem exists_affine_etale_chart_through {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : HasEtaleLocalProperty B S hS X'
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    {K₀ : BigFppfOver B S hS} (x : yoneda.obj K₀ ⟶ X')
    (k : (BigFppfOver.toScheme B S hS).obj K₀) :
    ∃ (V : BigFppfOver B S hS) (_ : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
      (_ : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj V))
      (v : yoneda.obj V ⟶ X'), (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf v ∧
      ∃ (Z : BigFppfOver B S hS) (p : Z ⟶ K₀) (z₂ : Z ⟶ V),
        yoneda.map z₂ ≫ v = yoneda.map p ≫ x ∧
        k ∈ Set.range ((BigFppfOver.toScheme B S hS).map p) := by
  obtain ⟨U, a, has, hae, hU⟩ := hX'
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) := hU
  let Pe := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
    MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  have _ : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have _ : Pe.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  let hrep := hae.rep
  let P := hrep.pullback x
  let fst : P ⟶ U := hrep.fst' x
  let snd : P ⟶ K₀ := hrep.snd x
  have hsq : yoneda.map fst ≫ a = yoneda.map snd ≫ x := by
    rw [Functor.relativelyRepresentable.map_fst']
    exact hrep.w x
  have hsnds : Surjective ((BigFppfOver.toScheme B S hS).map snd) := has.property_snd x
  obtain ⟨z, hz⟩ := hsnds.surj k
  obtain ⟨O, hO, hzO, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := (BigFppfOver.toScheme B S hS).obj U) (x := (BigFppfOver.toScheme B S hS).map fst z)
    (U := ⊤) (show _ ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens) from trivial)
  let O' : ((BigFppfOver.toScheme B S hS).obj P).Opens :=
    (BigFppfOver.toScheme B S hS).map fst ⁻¹ᵁ O
  let jU := openIncl B S hS U O
  let jP := openIncl B S hS P O'
  have : IsAffine (Scheme.Opens.toScheme O) := hO
  have hVa : IsAffine ((BigFppfOver.toScheme B S hS).obj (openObj B S hS U O)) := hO
  have hVn : _root_.AlgebraicGeometry.IsNoetherian
      ((BigFppfOver.toScheme B S hS).obj (openObj B S hS U O)) :=
    { toIsLocallyNoetherian := inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian
          (Scheme.Opens.toScheme O))
      toCompactSpace := inferInstanceAs (CompactSpace (Scheme.Opens.toScheme O)) }
  have hjUo : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map jU) := by
    rw [toScheme_map_openIncl]
    exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion O.ι)
  have hjUe : Etale ((BigFppfOver.toScheme B S hS).map jU) := by
    rw [toScheme_map_openIncl]
    exact inferInstanceAs (Etale O.ι)
  obtain ⟨z₂, hz₂⟩ := exists_factorization_of_isOpenImmersion jU hjUo (jP ≫ fst) (by
    rintro _ ⟨w, rfl⟩
    have hw : (BigFppfOver.toScheme B S hS).map fst w.1 ∈ O := w.2
    refine ⟨⟨_, hw⟩, ?_⟩
    rw [Functor.map_comp]
    show O.ι ⟨_, hw⟩ = (BigFppfOver.toScheme B S hS).map fst (O'.ι w)
    rfl)
  refine ⟨openObj B S hS U O, hVa, hVn, yoneda.map jU ≫ a,
    MorphismProperty.comp_mem Pe.presheaf _ _ (MorphismProperty.relative_map hjUe) hae,
    openObj B S hS P O', jP ≫ snd, z₂, ?_, ⟨⟨z, hzO⟩, ?_⟩⟩
  · rw [← Category.assoc, ← Functor.map_comp, hz₂, Functor.map_comp, Functor.map_comp,
      Category.assoc, Category.assoc, hsq]
  · rw [Functor.map_comp]
    show (BigFppfOver.toScheme B S hS).map snd (O'.ι ⟨z, hzO⟩) = k
    exact hz

/-- The open subobject of `X₁` on the complement of the image of a set `T₁` of points lands in
the open subspace with points `T₁ᶜ`. -/
theorem range_yoneda_map_openIncl_le_openSubspaceOfPoints {X₁ : BigFppfOver B S hS}
    {T₁ : Set (points B S hS (yoneda.obj X₁))} (hZ : IsClosed (pointsToScheme B S hS X₁ '' T₁)) :
    Subfunctor.range (yoneda.map (openIncl B S hS X₁ ⟨_, hZ.isOpen_compl⟩)) ≤
      openSubspaceOfPoints B S hS _ T₁ᶜ := by
  rintro W _ ⟨k, rfl⟩
  rw [mem_openSubspaceOfPoints_iff]
  rintro _ ⟨w, rfl⟩ hw
  have hmem : pointsToScheme B S hS X₁ (pointsMap B S hS _ (yonedaEquiv.symm
      ((yoneda.map (openIncl B S hS X₁ ⟨_, hZ.isOpen_compl⟩)).app W k)) w) ∈
        (⟨_, hZ.isOpen_compl⟩ : ((BigFppfOver.toScheme B S hS).obj X₁).Opens) := by
    rw [yonedaEquiv_symm_app_eq_comp,
      yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map k).symm, ← Functor.map_comp,
      pointsToScheme_pointsMap_yoneda, Functor.map_comp, Scheme.Hom.comp_apply]
    exact ((BigFppfOver.toScheme B S hS).map k (pointsToScheme B S hS _ w)).2
  exact hmem ⟨_, hw, rfl⟩

/-- **Étaleness off `T`.** Let `f₁ : X'₁ ⟶ h_{X₁}` be an isomorphism over the open complement of a
closed `T₁ ⊆ |X₁|` and let `ψ : h_V ⟶ X'₁` be étale. The induced morphism `V ⟶ X₁` of the site
is étale at every point lying over the complement of `T₁`: over the open subscheme `X₁°` with
points `T₁ᶜ`, the fibre product `X'₁ ×_{X₁} X₁°` is `X₁°` itself, and `V ×_{X₁} X₁°` is its base
change along `ψ`. -/
theorem etaleAt_of_isIso_pullback_snd {X₁ V : BigFppfOver B S hS}
    {X'₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f₁ : X'₁ ⟶ yoneda.obj X₁)
    {T₁ : Set (points B S hS (yoneda.obj X₁))} (hT₁ : IsClosed T₁)
    (hfU₁ : IsIso (pullback.snd f₁ (openSubspaceOfPoints B S hS _ T₁ᶜ).ι))
    (ψ : yoneda.obj V ⟶ X'₁) (hψ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ψ)
    (vX : V ⟶ X₁) (hvX : yoneda.map vX = ψ ≫ f₁) (p : points B S hS (yoneda.obj V))
    (hp : pointsMap B S hS _ (yoneda.map vX) p ∉ T₁) :
    EtaleAt ((BigFppfOver.toScheme B S hS).map vX) (pointsToScheme B S hS V p) := by
  let Pe := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
    MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  have hZ : IsClosed (pointsToScheme B S hS X₁ '' T₁) :=
    isClosed_image_pointsToScheme B S hS X₁ hT₁
  let O : ((BigFppfOver.toScheme B S hS).obj X₁).Opens := ⟨_, hZ.isOpen_compl⟩
  let j := openIncl B S hS X₁ O
  have hjmap : (BigFppfOver.toScheme B S hS).map j = O.ι := toScheme_map_openIncl B S hS X₁ O
  -- `j` lands in the open subspace with points `T₁ᶜ`
  have hle : Subfunctor.range (yoneda.map j) ≤ openSubspaceOfPoints B S hS _ T₁ᶜ :=
    range_yoneda_map_openIncl_le_openSubspaceOfPoints hZ
  let j' := Subfunctor.lift (yoneda.map j) hle
  let ι := (openSubspaceOfPoints B S hS (yoneda.obj X₁) T₁ᶜ).ι
  -- `X'₁ ×_{X₁} X₁° ⟶ X₁°` is an isomorphism
  have hsnd : IsIso (pullback.snd f₁ (j' ≫ ι)) := by
    have h1 : IsIso ((pullbackLeftPullbackSndIso f₁ ι j').hom ≫ pullback.snd f₁ (j' ≫ ι)) := by
      rw [pullbackLeftPullbackSndIso_hom_snd]
      infer_instance
    exact IsIso.of_isIso_comp_left (pullbackLeftPullbackSndIso f₁ ι j').hom _
  -- the fibre product `V° = V ×_{X₁} X₁°` of the site
  let Vo := pullback vX j
  have hsqY : IsPullback (yoneda.map (pullback.fst vX j)) (yoneda.map (pullback.snd vX j))
      (yoneda.map vX) (yoneda.map j) := (IsPullback.of_hasPullback vX j).map yoneda
  let l : yoneda.obj Vo ⟶ pullback f₁ (j' ≫ ι) :=
    pullback.lift (yoneda.map (pullback.fst vX j) ≫ ψ) (yoneda.map (pullback.snd vX j)) (by
      rw [Category.assoc, ← hvX]
      exact hsqY.w)
  have htop : IsPullback (yoneda.map (pullback.fst vX j)) l ψ (pullback.fst f₁ (j' ≫ ι)) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd f₁ (j' ≫ ι)) (v₂₂ := f₁) ?_
      (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f₁ (j' ≫ ι))
    rw [pullback.lift_snd, ← hvX]
    exact hsqY
  have hl : Pe.presheaf l :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) Pe).of_isPullback htop hψ
  have hsnde : Etale ((BigFppfOver.toScheme B S hS).map (pullback.snd vX j)) := by
    have h := MorphismProperty.RespectsIso.postcomp Pe.presheaf (pullback.snd f₁ (j' ≫ ι)) l hl
    rw [pullback.lift_snd] at h
    exact MorphismProperty.of_relative_map (P := Pe) h
  have hfstO : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (pullback.fst vX j)) := by
    have hjo : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) := by
      rw [hjmap]
      exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion O.ι)
    exact (presheaf_yoneda_map_of_inverseImage B S hS
      (P := @_root_.AlgebraicGeometry.IsOpenImmersion) inferInstance j hjo).property
      (yoneda.map vX) (yoneda.map (pullback.snd vX j)) (pullback.fst vX j)
      hsqY.flip
  have hcompE : Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst vX j ≫ vX)) := by
    rw [pullback.condition, Functor.map_comp, hjmap]
    exact MorphismProperty.comp_mem _ _ _ hsnde (inferInstanceAs (Etale O.ι))
  -- the point lies in the range of `V° ⟶ V`
  have hxO : (BigFppfOver.toScheme B S hS).map vX (pointsToScheme B S hS V p) ∈ O := by
    rintro ⟨t, ht, hteq⟩
    rw [← pointsToScheme_pointsMap_yoneda] at hteq
    exact hp ((bijective_pointsToScheme B S hS X₁).1 hteq ▸ ht)
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hsqS := (IsPullback.of_hasPullback vX j).map (BigFppfOver.toScheme B S hS)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (BigFppfOver.toScheme B S hS).map vX) (g := (BigFppfOver.toScheme B S hS).map j)
    (pointsToScheme B S hS V p) (⟨_, hxO⟩ : O) rfl
  have hfz : (BigFppfOver.toScheme B S hS).map (pullback.fst vX j)
      (hsqS.isoPullback.inv z) = pointsToScheme B S hS V p := by
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
    exact hz
  refine (etaleAt_iff_exists_open _ _).mpr
    ⟨((BigFppfOver.toScheme B S hS).map (pullback.fst vX j)).opensRange, ⟨_, hfz⟩, ?_⟩
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, ← Functor.map_comp]
  exact MorphismProperty.comp_mem _ _ _ (inferInstance : Etale _) hcompE

/-! ### The affine case -/

section Core

variable {X₁ : BigFppfOver B S hS} {T₁ : Set (points B S hS (yoneda.obj X₁))}
  {X'₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f₁ : X'₁ ⟶ yoneda.obj X₁}

/-- Every point of the field spectrum of a field-valued point `p` maps to the class of `p`. -/
private theorem pointsMap_yoneda_value_eq_class {Y₁ : BigFppfOver B S hS}
    (p : FieldValuedPoint B S hS (yoneda.obj Y₁))
    (r : points B S hS (yoneda.obj p.siteObject)) :
    pointsMap B S hS _ (yoneda.map p.value) r = p.class B S hS _ := by
  have hsub := subsingleton_points_yoneda_fieldSpec B S hS p.carrier p.contained p.toBase
  let p₀ : FieldValuedPoint B S hS (yoneda.obj p.siteObject) :=
    ⟨p.carrier, p.contained, p.toBase, 𝟙 _⟩
  rw [@Subsingleton.elim _ hsub r (p₀.class B S hS _)]
  show (FieldValuedPoint.map B S hS _ (yoneda.map p.value) p₀).class B S hS _ = _
  have h2 : FieldValuedPoint.map B S hS _ (yoneda.map p.value) p₀ = p := by
    show (⟨p.carrier, p.contained, p.toBase, 𝟙 _ ≫ p.value⟩ : FieldValuedPoint B S hS _) = p
    rw [Category.id_comp]
  rw [h2]

/-- The value of a morphism of completion subfunctors at a field-valued point of `Y₁` over `T`:
the field spectrum has a single point, which lies over `T`. -/
theorem hasImageIn_fieldValuedPoint {Y₁ : BigFppfOver B S hS}
    {T : Set (points B S hS (yoneda.obj Y₁))} (p : FieldValuedPoint B S hS (yoneda.obj Y₁))
    (hp : p.class B S hS _ ∈ T) :
    HasImageIn B S hS (yoneda.obj Y₁) T p.siteObject p.value := by
  intro r
  show pointsMap B S hS _ (yoneda.map p.value) (r.class B S hS _) ∈ T
  rwa [pointsMap_yoneda_value_eq_class]

/-! ### Lifts from equations of completions -/

/-- **Lifts from an equation of completions, for any presentation of the source over `X`.**
This is `AlgebraicGeometry.Space.isCompletionLift_of_completionOverFunctor_map_eq` with the
structure morphism `m : Z ⟶ X` of the source given by any morphism equal to `v ≫ g`. -/
theorem isCompletionLift_of_completionOverFunctor_map_eq_of_eq
    {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X' ⟶ X} {g : Y ⟶ X}
    {T : Set (points B S hS X)} (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (hX' : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X')
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (v : Z ⟶ Y) (c : Z ⟶ X') {m : Z ⟶ X}
    (hm : v ≫ g = m) (hc : c ≫ f = m)
    (α : (completionOverFunctor B S hS T).obj (Over.mk g) ⟶
      (completionOverFunctor B S hS T).obj (Over.mk f))
    (h : (completionOverFunctor B S hS T).map (Over.homMk c hc : Over.mk m ⟶ Over.mk f) =
      (completionOverFunctor B S hS T).map (Over.homMk v hm : Over.mk m ⟶ Over.mk g) ≫ α) :
    IsCompletionLift (completionSubfunctorHom hY hX' α.left) v c := by
  subst hm
  exact isCompletionLift_of_completionOverFunctor_map_eq hY hX' v c hc α h

/-- **Sections of a completion in the image of a completed morphism.** If the completion along
`T` of a morphism `a : M ⟶ N` over `X` carries a section `s` of `M_{/T}` to the section of
`N_{/T}` given by a section `ξ` of `N` over `T`, then `ξ` is the image under `a` of a section
of `M`. -/
theorem exists_app_eq_of_completionOverMap_app_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (points B S hS X)) {M N : Over X} (a : M ⟶ N)
    (hM : Presheaf.IsSheaf (BigFppfOver.topology B S hS) M.left)
    (hN : Presheaf.IsSheaf (BigFppfOver.topology B S hS) N.left) {W : (BigFppfOver B S hS)ᵒᵖ}
    (s : (completionSheaf B S hS M.left (pointsMap B S hS M.left M.hom ⁻¹' T)).obj.obj W)
    (ξ : (completionSubfunctor B S hS N.left
      (pointsMap B S hS N.left N.hom ⁻¹' T)).toFunctor.obj W)
    (hs : (completionOverMap B S hS T a).hom.app W s =
      (completionSheafIsoSubfunctor B S hS hN _).inv.app W ξ) :
    ∃ y : M.left.obj W, a.left.app W y = ξ.1.down := by
  let iM := completionSheafIsoSubfunctor B S hS hM (pointsMap B S hS M.left M.hom ⁻¹' T)
  let iN := completionSheafIsoSubfunctor B S hS hN (pointsMap B S hS N.left N.hom ⁻¹' T)
  let φ := completionSubfunctorMap B S hS a.left (pointsMap B S hS M.left M.hom ⁻¹' T)
    (pointsMap B S hS N.left N.hom ⁻¹' T)
    (image_preimage_subset_preimage_of_comp_eq B S hS (Over.w a) T)
  have key : (completionOverMap B S hS T a).hom ≫ iN.hom = iM.hom ≫ φ := by
    rw [← cancel_epi iM.inv, Iso.inv_hom_id_assoc]
    show (BigFppfOver.topology B S hS).toSheafify _ ≫ (completionOverMap B S hS T a).hom ≫
      iN.hom = φ
    have hts := toSheafify_comp_completionOverMap (T := T) a
    calc (BigFppfOver.topology B S hS).toSheafify _ ≫ (completionOverMap B S hS T a).hom ≫ iN.hom
        = ((BigFppfOver.topology B S hS).toSheafify _ ≫ (completionOverMap B S hS T a).hom) ≫
            iN.hom := (Category.assoc _ _ _).symm
      _ = (φ ≫ iN.inv) ≫ iN.hom := congrArg (· ≫ iN.hom) hts
      _ = φ := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h1 : iN.hom.app W ((completionOverMap B S hS T a).hom.app W s) =
      φ.app W (iM.hom.app W s) :=
    congrFun (congrArg (fun ψ => (ψ.app W : _ → _)) key) s
  have hid : iN.hom.app W (iN.inv.app W ξ) = ξ :=
    congrFun (congrArg (fun ψ => (ψ.app W : _ → _)) iN.inv_hom_id) ξ
  rw [hs, hid] at h1
  exact ⟨(iM.hom.app W s).1.down, (congrArg (fun x => x.1.down) h1).symm⟩

/-- Transporting the source of a completed morphism along an equality of morphisms. -/
theorem eqToHom_comp_completionSheafMap {M N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {φ ψ : M ⟶ N}
    (hφ : φ = ψ) (T : Set (points B S hS N)) :
    eqToHom (congrArg (fun χ : M ⟶ N => completionSheaf B S hS M (pointsMap B S hS M χ ⁻¹' T))
        hφ.symm) ≫ completionSheafMap B S hS φ T = completionSheafMap B S hS ψ T := by
  subst hφ
  simp

/-- Transporting the target of a completed morphism along an equality of sets of points. -/
theorem completionSheafMap_comp_eqToHom {M N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : M ⟶ N)
    {T T' : Set (points B S hS N)} (hT : T = T') :
    completionSheafMap B S hS a T ≫ eqToHom (congrArg (completionSheaf B S hS N) hT) =
      eqToHom (congrArg (fun T'' => completionSheaf B S hS M (pointsMap B S hS M a ⁻¹' T''))
        hT) ≫ completionSheafMap B S hS a T' := by
  subst hT
  simp

/-- Transporting the target of the completion of a morphism over `X` along an equality of
structure morphisms. -/
theorem completionOverMap_homMk_comp_eqToHom {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (points B S hS X)) {Z N : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : Z ⟶ X}
    {φ ψ : N ⟶ X} (hφψ : φ = ψ) (a : Z ⟶ N) (ha : a ≫ φ = m) (ha' : a ≫ ψ = m) :
    completionOverMap B S hS T (Over.homMk a ha : Over.mk m ⟶ Over.mk φ) ≫
        eqToHom (congrArg (fun χ : N ⟶ X => completionSheaf B S hS N (pointsMap B S hS N χ ⁻¹' T))
          hφψ) =
      completionOverMap B S hS T (Over.homMk a ha' : Over.mk m ⟶ Over.mk ψ) := by
  subst hφψ
  simp

/-- **The Stacks 0AR3 step of the affine case of Stacks 0GDR.** Let `X₁`, `V`, `Y'` be
Noetherian affine objects of the site, `T₁ ⊆ |X₁|` closed, `f₁ : X'₁ ⟶ X₁` a morphism of fppf
sheaves, `α : Y_{1,/T₁} ⟶ X'_{1,/T₁}` a morphism over `X_{1,/T₁}`, `v : V ⟶ X'₁` such that
`fV : V ⟶ X₁` is locally of finite type and étale over `X₁ ∖ T₁`, and `f' : Y' ⟶ Y₁`. A morphism
`ρ : Y'_{/T} ⟶ V_{/T₁}` with `α ∘ f'_{/T} = v_{/T₁} ∘ ρ` gives, by Stacks 0AR3 applied to `ρ`, an
étale `b : Y'' ⟶ Y'` with `b_{/T}` an isomorphism and `a : Y'' ⟶ V` such that `a ≫ v` lifts `α`
along `b ≫ f'`. Moreover a section `ξ` of `Y₁` over `T` which is the image of a section of
`Y'_{/T}` factors through `b ≫ f'`. -/
theorem exists_isCompletionLift_of_completionSheafMap_eq {X₁ Y₁ V Y' : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X₁)]
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj X₁)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y')]
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y')]
    {T₁ : Set (points B S hS (yoneda.obj X₁))} (hT₁ : IsClosed T₁)
    {X'₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX'₁ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X'₁) {f₁ : X'₁ ⟶ yoneda.obj X₁}
    (h : Y₁ ⟶ X₁) (hY₁ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj Y₁))
    (α : (completionOverFunctor B S hS T₁).obj (Over.mk (yoneda.map h)) ⟶
      (completionOverFunctor B S hS T₁).obj (Over.mk f₁))
    (v : yoneda.obj V ⟶ X'₁) (fV : V ⟶ X₁) (hfV : yoneda.map fV = v ≫ f₁)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map fV)]
    (hfVet : ∀ p : points B S hS (yoneda.obj V), pointsMap B S hS _ (yoneda.map fV) p ∉ T₁ →
      EtaleAt ((BigFppfOver.toScheme B S hS).map fV) (pointsToScheme B S hS V p))
    (f' : Y' ⟶ Y₁)
    (ρ : completionSheaf B S hS (yoneda.obj Y') (pointsMap B S hS _ (yoneda.map f') ⁻¹'
        (pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁)) ⟶
      completionSheaf B S hS (yoneda.obj V) (pointsMap B S hS _ (v ≫ f₁) ⁻¹' T₁))
    (hρ : completionSheafMap B S hS (yoneda.map f') (pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁) ≫
        (α.left : completionSheaf B S hS (yoneda.obj Y₁)
          (pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁) ⟶
          completionSheaf B S hS X'₁ (pointsMap B S hS X'₁ f₁ ⁻¹' T₁)) =
      ρ ≫ (((completionOverFunctor B S hS T₁).map
        (Over.homMk v rfl : Over.mk (v ≫ f₁) ⟶ Over.mk f₁)).left :
          completionSheaf B S hS (yoneda.obj V) (pointsMap B S hS _ (v ≫ f₁) ⁻¹' T₁) ⟶
          completionSheaf B S hS X'₁ (pointsMap B S hS X'₁ f₁ ⁻¹' T₁))) :
    ∃ (Y'' : BigFppfOver B S hS) (b : Y'' ⟶ Y') (_ : Etale ((BigFppfOver.toScheme B S hS).map b))
      (a : Y'' ⟶ V),
      IsCompletionLift (completionSubfunctorHom hY₁ hX'₁ α.left) (yoneda.map (b ≫ f'))
        (yoneda.map a ≫ v) ∧
      ∀ (Z : BigFppfOver B S hS)
        (t : (completionSheaf B S hS (yoneda.obj Y') (pointsMap B S hS _ (yoneda.map f') ⁻¹'
          (pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁))).obj.obj (op Z))
        (ξ : (completionSubfunctor B S hS (yoneda.obj Y₁)
          (pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁)).toFunctor.obj (op Z)),
        (completionSheafMap B S hS (yoneda.map f') _).hom.app (op Z) t =
            (completionSheafIsoSubfunctor B S hS hY₁ _).inv.app (op Z) ξ →
          ∃ y : Z ⟶ Y'', y ≫ b ≫ f' = ξ.1.down := by
  classical
  let T := pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁
  let vO : Over.mk (v ≫ f₁) ⟶ Over.mk f₁ := Over.homMk v rfl
  let f'O : Over.mk (yoneda.map (f' ≫ h)) ⟶ Over.mk (yoneda.map h) :=
    Over.homMk (yoneda.map f') (Functor.map_comp _ _ _).symm
  -- the morphisms, with their sources and targets written out
  let F' : completionSheaf B S hS (yoneda.obj Y')
      (pointsMap B S hS _ (yoneda.map (f' ≫ h)) ⁻¹' T₁) ⟶
      completionSheaf B S hS (yoneda.obj Y₁) T :=
    ((completionOverFunctor B S hS T₁).map f'O).left
  have hP0 : completionSheaf B S hS (yoneda.obj Y')
      (pointsMap B S hS _ (yoneda.map (f' ≫ h)) ⁻¹' T₁) =
      completionSheaf B S hS (yoneda.obj Y') (pointsMap B S hS _ (yoneda.map f') ⁻¹' T) :=
    congrArg (completionSheaf B S hS (yoneda.obj Y')) (preimage_pointsMap_over B S hS T₁ f'O)
  have hE0 : F' = eqToHom hP0 ≫ completionSheafMap B S hS (yoneda.map f') T := rfl
  have hP1 : completionSheaf B S hS (yoneda.obj V) (pointsMap B S hS _ (v ≫ f₁) ⁻¹' T₁) =
      completionSheaf B S hS (yoneda.obj V) (pointsMap B S hS _ (yoneda.map fV) ⁻¹' T₁) := by
    rw [hfV]
  let αL : completionSheaf B S hS (yoneda.obj Y₁) T ⟶
      completionSheaf B S hS X'₁ (pointsMap B S hS X'₁ f₁ ⁻¹' T₁) := α.left
  let cvL : completionSheaf B S hS (yoneda.obj V) (pointsMap B S hS _ (v ≫ f₁) ⁻¹' T₁) ⟶
      completionSheaf B S hS X'₁ (pointsMap B S hS X'₁ f₁ ⁻¹' T₁) :=
    ((completionOverFunctor B S hS T₁).map vO).left
  have hρ' : completionSheafMap B S hS (yoneda.map f') T ≫ αL = ρ ≫ cvL := hρ
  have h1 : eqToHom hP1 ≫ completionSheafMap B S hS (yoneda.map fV) T₁ =
      completionSheafMap B S hS (v ≫ f₁) T₁ := eqToHom_comp_completionSheafMap hfV T₁
  have h2 : cvL ≫ completionSheafMap B S hS f₁ T₁ = completionSheafMap B S hS (v ≫ f₁) T₁ :=
    completionOverMap_comp_completionSheafMap B S hS T₁ vO
  have h3 : αL ≫ completionSheafMap B S hS f₁ T₁ =
      completionSheafMap B S hS (yoneda.map h) T₁ := Over.w α
  have h4 : F' ≫ completionSheafMap B S hS (yoneda.map h) T₁ =
      completionSheafMap B S hS (yoneda.map (f' ≫ h)) T₁ :=
    completionOverMap_comp_completionSheafMap B S hS T₁ f'O
  -- the morphism `Y'_{/T} ⟶ V_{/T}` over `X_{1,/T₁}` fed into Stacks 0AR3
  have hβ : (eqToHom hP0 ≫ ρ ≫ eqToHom hP1) ≫ completionSheafMap B S hS (yoneda.map fV) T₁ =
      completionSheafMap B S hS (yoneda.map (f' ≫ h)) T₁ := by
    rw [Category.assoc, Category.assoc, h1, ← h2, ← Category.assoc ρ, ← hρ', Category.assoc, h3,
      ← Category.assoc, ← hE0, h4]
  let α3 : (completionOverFunctor B S hS T₁).obj (Over.mk (yoneda.map (f' ≫ h))) ⟶
      (completionOverFunctor B S hS T₁).obj (Over.mk (yoneda.map fV)) :=
    Over.homMk (eqToHom hP0 ≫ ρ ≫ eqToHom hP1) hβ
  obtain ⟨Y'', -, b, hb, a, comm_ab, hiso, hα3⟩ :=
    FormalSpace.exists_etale_completion_factorization B S hS T₁ hT₁ fV hfVet (f' ≫ h) α3
  let bO : Over.mk (yoneda.map b ≫ yoneda.map (f' ≫ h)) ⟶ Over.mk (yoneda.map (f' ≫ h)) :=
    Over.homMk (yoneda.map b)
  let aO : Over.mk (yoneda.map b ≫ yoneda.map (f' ≫ h)) ⟶ Over.mk (yoneda.map fV) :=
    Over.homMk (yoneda.map a) (by simp only [Over.mk_hom, ← Functor.map_comp, comm_ab])
  have hα3' : (completionOverFunctor B S hS T₁).map bO ≫ α3 =
      (completionOverFunctor B S hS T₁).map aO := by
    rw [hα3]
    exact IsIso.hom_inv_id_assoc _ _
  let CY'' := completionSheaf B S hS (yoneda.obj Y'')
    (pointsMap B S hS _ (yoneda.map b ≫ yoneda.map (f' ≫ h)) ⁻¹' T₁)
  let BL : CY'' ⟶ completionSheaf B S hS (yoneda.obj Y')
      (pointsMap B S hS _ (yoneda.map (f' ≫ h)) ⁻¹' T₁) :=
    ((completionOverFunctor B S hS T₁).map bO).left
  let AL : CY'' ⟶ completionSheaf B S hS (yoneda.obj V)
      (pointsMap B S hS _ (yoneda.map fV) ⁻¹' T₁) :=
    ((completionOverFunctor B S hS T₁).map aO).left
  have hBA : BL ≫ eqToHom hP0 ≫ ρ ≫ eqToHom hP1 = AL :=
    congrArg (fun φ => φ.left) hα3'
  have hcomm : (yoneda.map a ≫ v) ≫ f₁ = yoneda.map b ≫ yoneda.map (f' ≫ h) := by
    rw [Category.assoc, ← hfV, ← Functor.map_comp, comm_ab, Functor.map_comp]
  let aO' : Over.mk (yoneda.map b ≫ yoneda.map (f' ≫ h)) ⟶ Over.mk (v ≫ f₁) :=
    Over.homMk (yoneda.map a) ((Category.assoc _ _ _).symm.trans hcomm)
  let AL' : CY'' ⟶ completionSheaf B S hS (yoneda.obj V)
      (pointsMap B S hS _ (v ≫ f₁) ⁻¹' T₁) :=
    ((completionOverFunctor B S hS T₁).map aO').left
  have haO' : AL' = AL ≫ eqToHom hP1.symm :=
    (completionOverMap_homMk_comp_eqToHom T₁ hfV (yoneda.map a) _ _).symm
  have hlift := isCompletionLift_of_completionOverFunctor_map_eq_of_eq hY₁ hX'₁
    (yoneda.map (b ≫ f')) (yoneda.map a ≫ v)
    (by simp only [Functor.map_comp, Category.assoc]) hcomm α (by
      have e1 : (Over.homMk (yoneda.map a ≫ v) hcomm :
          Over.mk (yoneda.map b ≫ yoneda.map (f' ≫ h)) ⟶ Over.mk f₁) = aO' ≫ vO := by
        ext1
        rfl
      have e2 : (Over.homMk (yoneda.map (b ≫ f'))
          (by simp only [Over.mk_hom, Functor.map_comp, Category.assoc]) :
          Over.mk (yoneda.map b ≫ yoneda.map (f' ≫ h)) ⟶ Over.mk (yoneda.map h)) =
          bO ≫ f'O := by
        ext1
        exact yoneda.map_comp b f'
      rw [e1, e2, (completionOverFunctor B S hS T₁).map_comp,
        (completionOverFunctor B S hS T₁).map_comp]
      apply Over.OverMorphism.ext
      show AL' ≫ cvL = (BL ≫ F') ≫ αL
      rw [Category.assoc, haO', ← hBA, hE0]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← hρ'])
  refine ⟨Y'', b, hb, a, hlift, fun Z t ξ ht => ?_⟩
  -- the point part
  have : IsIso BL := Functor.map_isIso (Over.forget _) ((completionOverFunctor B S hS T₁).map bO)
  let t₀ := (eqToHom hP0.symm).hom.app (op Z) t
  have ht₀ : (eqToHom hP0).hom.app (op Z) t₀ = t := by
    have hc : eqToHom hP0.symm ≫ eqToHom hP0 = 𝟙 _ := by rw [eqToHom_trans, eqToHom_refl]
    exact congrFun (congrArg (fun φ => (φ.hom.app (op Z) : _ → _)) hc) t
  let s'' := (inv BL).hom.app (op Z) t₀
  have hs'' : BL.hom.app (op Z) s'' = t₀ :=
    congrFun (congrArg (fun φ => (φ.hom.app (op Z) : _ → _)) (IsIso.inv_hom_id BL)) t₀
  have hs : (completionOverMap B S hS T₁ (bO ≫ f'O)).hom.app (op Z) s'' =
      (completionSheafMap B S hS (yoneda.map f') T).hom.app (op Z) t := by
    rw [completionOverMap_comp]
    show F'.hom.app (op Z) (BL.hom.app (op Z) s'') = _
    rw [hs'', hE0]
    show (completionSheafMap B S hS (yoneda.map f') T).hom.app (op Z)
      ((eqToHom hP0).hom.app (op Z) t₀) = _
    rw [ht₀]
  obtain ⟨y, hy⟩ := exists_app_eq_of_completionOverMap_app_eq T₁ (bO ≫ f'O)
    (isAlgebraicSpace_yoneda B S hS Y'').isSheaf hY₁ s'' ξ (hs.trans ht)
  exact ⟨y, (Category.assoc y b f').symm.trans hy⟩

/-- **The affine case of Stacks 0GDR, for `Y₁ = Spec R`.** See
`AlgebraicGeometry.Space.affineCompletionLiftProperty`. -/
theorem exists_isCompletionLift_affineOver
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X₁)]
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj X₁)]
    (hT₁ : IsClosed T₁) (hX'₁ : IsAlgebraicSpace B S hS X'₁)
    (hf₁ : IsLocallyOfFiniteType B S hS f₁)
    (hfU₁ : IsIso (pullback.snd f₁ (openSubspaceOfPoints B S hS _ T₁ᶜ).ι))
    {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of R) ⟶ S) (h : FormalSpace.affineOver B S hS hR s ⟶ X₁)
    (α₁ : (completionSubfunctor B S hS (yoneda.obj (FormalSpace.affineOver B S hS hR s))
        (pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁)).toFunctor ⟶
      (completionSubfunctor B S hS X'₁ (pointsMap B S hS X'₁ f₁ ⁻¹' T₁)).toFunctor)
    (hα₁ : ∀ (W : (BigFppfOver B S hS)ᵒᵖ)
      (y : (yoneda.obj (FormalSpace.affineOver B S hS hR s)).obj W)
      (hy : HasImageIn B S hS (yoneda.obj (FormalSpace.affineOver B S hS hR s))
        (pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁) W.unop y),
      f₁.app W (α₁.app W ⟨ULift.up y, hy⟩).1.down = (yoneda.map h).app W y)
    (q : points B S hS (yoneda.obj (FormalSpace.affineOver B S hS hR s)))
    (hq : pointsMap B S hS _ (yoneda.map h) q ∈ T₁) :
    ∃ (V : BigFppfOver B S hS) (π : V ⟶ FormalSpace.affineOver B S hS hR s),
      Etale ((BigFppfOver.toScheme B S hS).map π) ∧
      q ∈ Set.range (pointsMap B S hS _ (yoneda.map π)) ∧
      ∃ c, IsCompletionLift α₁ (yoneda.map π) c := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FormalSpace.FppfSheaf B S hS) :=
    Sheaf.instHasColimitsOfSize
  let Y₁ := FormalSpace.affineOver B S hS hR s
  let J := BigFppfOver.topology B S hS
  have hX₁sh := (isAlgebraicSpace_yoneda B S hS X₁).isSheaf
  have hY₁sh := (isAlgebraicSpace_yoneda B S hS Y₁).isSheaf
  let T : Set (points B S hS (yoneda.obj Y₁)) := pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁
  have hT : IsClosed T := hT₁.preimage (continuous_pointsMap B S hS _)
  let αs := completionOverHomOfSubfunctor hX₁sh hY₁sh hX'₁.isSheaf α₁ hα₁
  have hX'noeth := isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hX'₁
    (isAlgebraicSpace_yoneda B S hS X₁) f₁ hf₁
    (hasEtaleLocalProperty_isLocallyNoetherian_yoneda inferInstance)
  -- the field-valued point `p` representing `q`, and its value `α₁(p)`
  obtain ⟨p, rfl⟩ := Quot.exists_rep q
  let K₀ := p.siteObject
  let s₀ : K₀ ⟶ Y₁ := p.value
  have hs₀T : HasImageIn B S hS (yoneda.obj Y₁) T K₀ s₀ := hasImageIn_fieldValuedPoint p hq
  let x : yoneda.obj K₀ ⟶ X'₁ :=
    yonedaEquiv.symm ((α₁.app (op K₀) ⟨ULift.up s₀, hs₀T⟩).1.down)
  have hK₀pts : ∀ r : points B S hS (yoneda.obj K₀),
      pointsMap B S hS _ (yoneda.map s₀) r = Quot.mk _ p :=
    pointsMap_yoneda_value_eq_class p
  obtain ⟨k₀, -⟩ := surjective_pointsToScheme B S hS K₀ (pointsToScheme B S hS K₀ (Quot.mk _
    (⟨p.carrier, p.contained, p.toBase, 𝟙 _⟩ : FieldValuedPoint B S hS (yoneda.obj K₀))))
  -- an affine étale chart `V ⟶ X'₁` through the image of `p`
  obtain ⟨V, hVa, hVn, v, hv, Z, p', z₂, hz₂, ⟨zpt, -⟩⟩ := exists_affine_etale_chart_through
    hX'noeth x (pointsToScheme B S hS K₀ k₀)
  let z₁ : Z ⟶ Y₁ := p' ≫ s₀
  have hz₁q : ∀ r : points B S hS (yoneda.obj Z), pointsMap B S hS _ (yoneda.map z₁) r =
      Quot.mk _ p := fun r => by
    rw [Functor.map_comp, pointsMap_comp_apply, hK₀pts]
  have hz₁T : HasImageIn B S hS (yoneda.obj Y₁) T Z z₁ := by
    rw [hasImageIn_iff_range_subset, yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map z₁).symm]
    rintro _ ⟨r, rfl⟩
    rwa [hz₁q]
  have hxf : x ≫ f₁ = yoneda.map (s₀ ≫ h) := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
    exact hα₁ (op K₀) s₀ hs₀T
  have hzz : yoneda.map z₁ ≫ yoneda.map h = yoneda.map z₂ ≫ v ≫ f₁ := by
    rw [← Category.assoc, hz₂, Category.assoc, hxf, ← Functor.map_comp, ← Functor.map_comp]
    simp only [z₁, Category.assoc]
  have hz₂T : HasImageIn B S hS (yoneda.obj V) (pointsMap B S hS _ (v ≫ f₁) ⁻¹' T₁) Z z₂ := by
    rw [hasImageIn_iff_range_subset, yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map z₂).symm]
    rintro _ ⟨r, rfl⟩
    rwa [Set.mem_preimage, ← pointsMap_comp_apply, ← hzz, pointsMap_comp_apply, hz₁q]
  -- the fibre product `W = Y_{1,/T} ×_{X'_{/T}} V_{/T}`
  let fV : V ⟶ X₁ := yoneda.preimage (v ≫ f₁)
  have hfV : yoneda.map fV = v ≫ f₁ := Functor.map_preimage _ _
  let vO : Over.mk (v ≫ f₁) ⟶ Over.mk f₁ := Over.homMk v rfl
  let cv := (completionOverFunctor B S hS T₁).map vO
  have hcv : FormalSpace.IsRepresentableEtale B S hS cv.left :=
    isRepresentableEtale_completionOverMap T₁ vO (isAlgebraicSpace_yoneda B S hS V) hX'₁
      (isEtale_of_presheaf_etale B S hS hv)
  have hfst := FormalSpace.isRepresentableEtale_pullback_fst B S hS αs.left cv.left hcv
  -- `Y_{1,/T}` is the formal spectrum of a Noetherian adic ring
  obtain ⟨A, _, _, _, _, hCA, D, ⟨eD⟩⟩ :=
    FormalSpace.exists_formalSpectrum_iso_completionSheaf B S hS hR s T hT
  have hYnoeth : FormalSpace.IsNoetherian B S hS (completionSheaf B S hS (yoneda.obj Y₁) T) :=
    FormalSpace.isNoetherian_completionSheaf B S hS hR s T hT
  -- the covering of `W`
  obtain ⟨K, C, _, fK, hfK, Q, gK, hgK, w, hw, hwrep, hwaff, hwnoeth, hsurj⟩ :=
    FormalSpace.exists_noetherian_completion_cover_of_isRepresentableEtale B S hS hCA D
      (pullback.fst αs.left cv.left ≫ eD.inv)
      (hfst.comp B S hS (FormalSpace.isRepresentableEtale_of_isIso B S hS eD.inv))
  -- the section of `W` over `Z` given by `z₁` and `z₂`
  let isoY := completionSheafIsoSubfunctor B S hS hY₁sh T
  let isoV := completionSheafIsoSubfunctor B S hS (isAlgebraicSpace_yoneda B S hS V).isSheaf
    (pointsMap B S hS _ (v ≫ f₁) ⁻¹' T₁)
  let isoX' := completionSheafIsoSubfunctor B S hS hX'₁.isSheaf (pointsMap B S hS _ f₁ ⁻¹' T₁)
  let ξ₁ : (completionSubfunctor B S hS (yoneda.obj Y₁) T).toFunctor.obj (op Z) :=
    ⟨ULift.up z₁, hz₁T⟩
  let ξ₂ : (completionSubfunctor B S hS (yoneda.obj V)
      (pointsMap B S hS _ (v ≫ f₁) ⁻¹' T₁)).toFunctor.obj (op Z) := ⟨ULift.up z₂, hz₂T⟩
  let ζ₁ : (Sheaf.sheafifiedYoneda J).obj Z ⟶
      ((completionOverFunctor B S hS T₁).obj (Over.mk (yoneda.map h))).left :=
    (Sheaf.sectionEquiv J (X := Z)
      (F := ((completionOverFunctor B S hS T₁).obj (Over.mk (yoneda.map h))).left)).symm
      (isoY.inv.app (op Z) ξ₁)
  let ζ₂ : (Sheaf.sheafifiedYoneda J).obj Z ⟶
      ((completionOverFunctor B S hS T₁).obj (Over.mk (v ≫ f₁))).left :=
    (Sheaf.sectionEquiv J (X := Z)
      (F := ((completionOverFunctor B S hS T₁).obj (Over.mk (v ≫ f₁))).left)).symm
      (isoV.inv.app (op Z) ξ₂)
  have e1 : αs.left.hom.app (op Z) (isoY.inv.app (op Z) ξ₁) =
      isoX'.inv.app (op Z) (α₁.app (op Z) ξ₁) := by
    have hid : isoY.hom.app (op Z) (isoY.inv.app (op Z) ξ₁) = ξ₁ :=
      congrFun (congrArg (fun φ => (φ.app (op Z) : _ → _)) isoY.inv_hom_id) ξ₁
    show isoX'.inv.app (op Z) (α₁.app (op Z) (isoY.hom.app (op Z) (isoY.inv.app (op Z) ξ₁))) = _
    rw [hid]
  have e2 : cv.left.hom.app (op Z) (isoV.inv.app (op Z) ξ₂) =
      isoX'.inv.app (op Z) ((completionSubfunctorMap B S hS v
        (pointsMap B S hS _ (v ≫ f₁) ⁻¹' T₁) (pointsMap B S hS _ f₁ ⁻¹' T₁)
        (image_preimage_subset_preimage_of_comp_eq B S hS (rfl : v ≫ f₁ = v ≫ f₁) T₁)).app
          (op Z) ξ₂) :=
    congrFun (congrArg (fun φ => (φ.app (op Z) : _ → _))
      (toSheafify_comp_completionOverMap (T := T₁) vO)) ξ₂
  have e3 : α₁.app (op Z) ξ₁ = (completionSubfunctorMap B S hS v
        (pointsMap B S hS _ (v ≫ f₁) ⁻¹' T₁) (pointsMap B S hS _ f₁ ⁻¹' T₁)
        (image_preimage_subset_preimage_of_comp_eq B S hS (rfl : v ≫ f₁ = v ≫ f₁) T₁)).app
          (op Z) ξ₂ := by
    apply Subtype.ext
    apply ULift.ext
    calc (α₁.app (op Z) ξ₁).1.down
        = X'₁.map p'.op (α₁.app (op K₀) ⟨ULift.up s₀, hs₀T⟩).1.down :=
          completionHom_app_map (α := α₁) p'.op s₀ hs₀T hz₁T
      _ = (yoneda.map p' ≫ x).app (op Z) (𝟙 Z) := by
          show _ = x.app (op Z) (𝟙 Z ≫ p')
          rw [Category.id_comp]
          rfl
      _ = (yoneda.map z₂ ≫ v).app (op Z) (𝟙 Z) := by rw [hz₂]
      _ = v.app (op Z) z₂ := by
          show v.app _ (𝟙 Z ≫ z₂) = _
          rw [Category.id_comp]
  have hζ : ζ₁ ≫ αs.left = ζ₂ ≫ cv.left := by
    apply (Sheaf.sectionEquiv J).injective
    rw [Sheaf.sectionEquiv_comp J ζ₁ αs.left, Sheaf.sectionEquiv_comp J ζ₂ cv.left]
    have h1 : Sheaf.sectionEquiv J ζ₁ = isoY.inv.app (op Z) ξ₁ := Equiv.apply_symm_apply _ _
    have h2 : Sheaf.sectionEquiv J ζ₂ = isoV.inv.app (op Z) ξ₂ := Equiv.apply_symm_apply _ _
    rw [h1, h2]
    exact e1.trans ((congrArg _ e3).trans e2.symm)
  let σ := Sheaf.sectionEquiv J (pullback.lift ζ₁ ζ₂ hζ)
  obtain ⟨Rs, hRs, hlift⟩ := (Sheaf.isLocallySurjective_sigmaDesc_iff w).mp hsurj σ
  obtain ⟨Z', g', hg', ⟨r'⟩⟩ := exists_mem_point_of_mem_topology hRs zpt
  obtain ⟨k, t, ht⟩ := hlift g' hg'
  -- Stacks 0AR4 algebraizes the piece `Spf (Q k)` through `σ`
  have hgk : FormalSpace.IsRepresentableEtale B S hS (w k ≫ pullback.fst αs.left cv.left) :=
    (hwrep k).comp B S hS hfst
  have hWk : FormalSpace.IsNoetherian B S hS (FormalSpace.formalSpectrum (Q k)) :=
    FormalSpace.isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale B S hS
      (FormalSpace.isLocallyNoetherian_of_isNoetherian B S hS hYnoeth) _ (hwaff k) hgk
  obtain ⟨Y', hY'a, f', e, hf'lft, -, -, he, hf'et⟩ :=
    FormalSpace.exists_affine_algebraization_of_isRigEtale B S hS hR s T hT (hwaff k) hWk _
      (FormalSpace.isRigEtale_of_isRepresentableEtale B S hS _ hWk hYnoeth hgk)
  have hf'e := hf'et hgk
  have : _root_.AlgebraicGeometry.IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Y₁) :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsLocallyNoetherian (Spec (.of R)))
  have : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y') :=
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map f') }
  -- the morphism `V ⟶ X₁` is locally of finite type and étale off `T₁`
  have hvE : IsEtale B S hS v := isEtale_of_presheaf_etale B S hS hv
  have hfVlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map fV) := by
    rw [← isLocallyOfFiniteType_yoneda_map_iff, hfV]
    exact isLocallyOfFiniteType_comp B S hS (isAlgebraicSpace_yoneda B S hS V) hX'₁
      (isAlgebraicSpace_yoneda B S hS X₁) v f₁
      (isLocallyOfFiniteType_of_isEtale B S hS hX'₁ hvE) hf₁
  -- Stacks 0AR3
  obtain ⟨Y'', b, hb, a, hlift', hpt⟩ := exists_isCompletionLift_of_completionSheafMap_eq hT₁
    hX'₁.isSheaf h hY₁sh αs v fV hfV
    (fun p hp => etaleAt_of_isIso_pullback_snd f₁ hT₁ hfU₁ v hv fV hfV p hp) f'
    (e.hom ≫ w k ≫ pullback.snd αs.left cv.left) (by
      have k1 : (e.hom ≫ w k ≫ pullback.fst αs.left cv.left) ≫ αs.left =
          (e.hom ≫ w k ≫ pullback.snd αs.left cv.left) ≫ cv.left := by
        simp only [Category.assoc, pullback.condition]
      exact (congrArg (· ≫ αs.left) he).symm.trans k1)
  have hα : completionSubfunctorHom hY₁sh hX'₁.isSheaf αs.left = α₁ :=
    completionSubfunctorHom_completionSheafHomOfSubfunctor hY₁sh hX'₁.isSheaf α₁
  rw [hα] at hlift'
  -- the point `q` is in the image of `Y'' ⟶ Y₁`
  have hσ : (pullback.fst αs.left cv.left).hom.app (op Z) σ = isoY.inv.app (op Z) ξ₁ := by
    show (pullback.fst αs.left cv.left).hom.app (op Z)
      (Sheaf.sectionEquiv J (pullback.lift ζ₁ ζ₂ hζ)) = _
    rw [← Sheaf.sectionEquiv_comp J, pullback.lift_fst]
    exact Equiv.apply_symm_apply _ _
  have ht' : (completionSheafMap B S hS (yoneda.map f') T).hom.app (op Z')
      (e.inv.hom.app (op Z') t) =
      isoY.inv.app (op Z') ((completionSubfunctor B S hS (yoneda.obj Y₁) T).toFunctor.map
        g'.op ξ₁) := by
    rw [← he]
    have hinv : e.hom.hom.app (op Z') (e.inv.hom.app (op Z') t) = t :=
      congrFun (congrArg (fun φ => (φ.hom.app (op Z') : _ → _)) e.inv_hom_id) t
    show (pullback.fst αs.left cv.left).hom.app (op Z') ((w k).hom.app (op Z')
      (e.hom.hom.app (op Z') (e.inv.hom.app (op Z') t))) = _
    rw [hinv, ht, NatTrans.naturality_apply (pullback.fst αs.left cv.left).hom g'.op σ, hσ]
    exact (NatTrans.naturality_apply isoY.inv g'.op ξ₁).symm
  obtain ⟨y, hy⟩ := hpt Z' (e.inv.hom.app (op Z') t) _ ht'
  have hy' : y ≫ b ≫ f' = g' ≫ z₁ := hy
  refine ⟨Y'', b ≫ f', ?_, ⟨pointsMap B S hS _ (yoneda.map y) r', ?_⟩, _, hlift'⟩
  · rw [Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ hb hf'e
  · rw [← pointsMap_comp_apply, ← Functor.map_comp, hy', Functor.map_comp, pointsMap_comp_apply,
      hz₁q]

/-- **The affine case of Stacks 0GDR.** `AlgebraicGeometry.Space.AffineCompletionLiftProperty`
holds: over a Noetherian affine `X₁`, for `X'₁ ⟶ X₁` locally of finite type and an
isomorphism over the complement of a closed `T₁`, and for a Noetherian affine `Y₁ ⟶ X₁`, every
morphism of completion subfunctors `α₁ : Y_{1,/T₁} ⟶ X'_{1,/T₁}` over `X₁` lifts étale locally
around each point of `Y₁` over `T₁`. This is
`AlgebraicGeometry.Space.exists_isCompletionLift_affineOver` transported along an isomorphism
`Spec Γ(Y₁) ≅ Y₁`. -/
theorem affineCompletionLiftProperty : AffineCompletionLiftProperty B S hS := by
  unfold AffineCompletionLiftProperty
  intro X₁ _ _ T₁ hT₁ X'₁ hX'₁ f₁ hf₁ hfU₁ Y₁ _ _ h α₁ hα₁ q hq
  obtain ⟨R, _, _, hR, s, ι, hι⟩ := exists_isIso_affineOver Y₁
  have hag : yoneda.map ι ≫ yoneda.map h = yoneda.map (ι ≫ h) := (yoneda.map_comp ι h).symm
  let α₁' := completionSubfunctorMap B S hS (yoneda.map ι)
    (pointsMap B S hS _ (yoneda.map (ι ≫ h)) ⁻¹' T₁) (pointsMap B S hS _ (yoneda.map h) ⁻¹' T₁)
    (image_preimage_subset_preimage_of_comp_eq B S hS hag T₁) ≫ α₁
  have hα₁' : ∀ (W : (BigFppfOver B S hS)ᵒᵖ)
      (y : (yoneda.obj (FormalSpace.affineOver B S hS hR s)).obj W)
      (hy : HasImageIn B S hS (yoneda.obj (FormalSpace.affineOver B S hS hR s))
        (pointsMap B S hS _ (yoneda.map (ι ≫ h)) ⁻¹' T₁) W.unop y),
      f₁.app W (α₁'.app W ⟨ULift.up y, hy⟩).1.down = (yoneda.map (ι ≫ h)).app W y := by
    intro W y hy
    refine (hα₁ W ((yoneda.map ι).app W y) _).trans ?_
    show (y ≫ ι) ≫ h = y ≫ ι ≫ h
    exact Category.assoc _ _ _
  -- `q` comes from a point of `Spec Γ(Y₁)`
  obtain ⟨x', hx'⟩ := (inferInstance : Surjective ((BigFppfOver.toScheme B S hS).map ι)).surj
    (pointsToScheme B S hS Y₁ q)
  obtain ⟨q', hq'⟩ := surjective_pointsToScheme B S hS _ x'
  have hqq : pointsMap B S hS _ (yoneda.map ι) q' = q := by
    apply (bijective_pointsToScheme B S hS Y₁).1
    rw [pointsToScheme_pointsMap_yoneda, hq', hx']
  obtain ⟨V, π, hπ, ⟨r, hr⟩, c, hc⟩ := exists_isCompletionLift_affineOver hT₁ hX'₁ hf₁ hfU₁ hR s
    (ι ≫ h) α₁' hα₁' q' (by rw [← hag, pointsMap_comp_apply, hqq]; exact hq)
  refine ⟨V, π ≫ ι, ?_, ⟨r, ?_⟩, c, ?_, fun W z hz => ?_⟩
  · rw [Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ hπ inferInstance
  · rw [Functor.map_comp, pointsMap_comp_apply, hr, hqq]
  · rw [hc.1, ← hag, Functor.map_comp, Category.assoc]
  · have hz' := hasImageIn_of_comp_eq (T := T₁) (g := yoneda.map h)
      (g' := yoneda.map (ι ≫ h)) (a := yoneda.map (π ≫ ι)) (b := yoneda.map π)
      (by rw [← hag, Functor.map_comp, Category.assoc]) W z hz
    rw [← hc.2 W z hz']
    exact completionHom_app_congr (α := α₁) W hz _ (Category.assoc z π ι).symm

/-- **Stacks 0GDR.** Let `X` be a locally Noetherian algebraic space over `S`, `T ⊆ |X|`
closed and `U ⊂ X` the open subspace with `|U| = |X| ∖ T`. Let `f : X' ⟶ X` be a morphism of
algebraic spaces which is locally of finite type and an isomorphism over `U`, and let
`g : Y ⟶ X` be a morphism with `Y` a locally Noetherian algebraic space. Then completion along
`T` (`AlgebraicGeometry.Space.completionOverFunctor`, the completion of Section 0GDB used in
Stacks 0AR5) is a bijection from the morphisms `Y ⟶ X'` over `X` to the morphisms
`Y_{/T} ⟶ X'_{/T}` over `X_{/T}`.

Injectivity is `AlgebraicGeometry.Space.completionOverFunctor_map_injective`; surjectivity is
`AlgebraicGeometry.Space.exists_completionOverFunctor_map_eq_of_affineCompletionLiftProperty`
applied to its affine case `AlgebraicGeometry.Space.affineCompletionLiftProperty`. The
consequence that the functor of Stacks 0AR5 is fully faithful is
`AlgebraicGeometry.FormalSpace.finiteTypeModificationCompletionFullyFaithful`. -/
@[stacks 0GDR]
theorem completionOverFunctor_map_bijective {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hXnoeth : HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    {T : Set (points B S hS X)} (hT : IsClosed T) {f : X' ⟶ X}
    (hX' : IsAlgebraicSpace B S hS X') (hf : IsLocallyOfFiniteType B S hS f)
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι)) (g : Y ⟶ X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hYnoeth : HasEtaleLocalProperty B S hS Y
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V)) :
    Function.Bijective
      (fun a : Over.mk g ⟶ Over.mk f => (completionOverFunctor B S hS T).map a) :=
  ⟨completionOverFunctor_map_injective hY hX' hYnoeth
      (isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hX' hX f hf hXnoeth) hT hfU,
    exists_completionOverFunctor_map_eq_of_affineCompletionLiftProperty
      affineCompletionLiftProperty hX hXnoeth hY hYnoeth hX' hf hT hfU⟩

end Core

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- **Stacks 0GDR, the consequence: the functor of Stacks 0AR5 is fully faithful.** For a
locally Noetherian algebraic space `X` and a closed `T ⊆ |X|`, completion along `T` is fully
faithful on the morphisms `X' ⟶ X` locally of finite type which are an isomorphism over the
open subspace with points `|X| ∖ T`. The functor of Stacks 0AR5,
`AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor`, is this functor with
its values regarded in the full subcategory of rig-étale morphisms with locally Noetherian
formal source (`AlgebraicGeometry.FormalSpace.completionFiniteTypeModificationFunctor_comp_ι`).
Fullness and faithfulness are the two halves of the bijection
`AlgebraicGeometry.Space.completionOverFunctor_map_bijective`, applied to a finite-type
modification `M` as the locally Noetherian source: `M` is locally Noetherian because it is
locally of finite type over `X`. -/
@[stacks 0GDR "in particular: the functor of Stacks 0AR5 is fully faithful"]
noncomputable def finiteTypeModificationCompletionFullyFaithful
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXnoeth : Space.HasEtaleLocalProperty B S hS X
      (fun V : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian V))
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) :
    (finiteTypeModificationCompletion (B := B) (S := S) (hS := hS) T).FullyFaithful :=
  have hbij : ∀ M N : Space.FiniteTypeModification B S hS (Space.openSubspaceOfPoints B S hS X Tᶜ),
      Function.Bijective
        (fun a : M.obj ⟶ N.obj => (Space.completionOverFunctor B S hS T).map a) :=
    fun M N => Space.completionOverFunctor_map_bijective hX hXnoeth hT N.property.1.1
      N.property.2 N.property.1.2 M.obj.hom M.property.1.1
      (Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS M.property.1.1 hX M.obj.hom
        M.property.2 hXnoeth)
  haveI : (finiteTypeModificationCompletion (B := B) (S := S) (hS := hS) T).Full :=
    ⟨fun {M N} α => by
      obtain ⟨a, ha⟩ := (hbij M N).2 α
      exact ⟨ObjectProperty.homMk a, ha⟩⟩
  haveI : (finiteTypeModificationCompletion (B := B) (S := S) (hS := hS) T).Faithful :=
    ⟨fun {M N} a b h => ObjectProperty.hom_ext _ ((hbij M N).1 h)⟩
  Functor.FullyFaithful.ofFullyFaithful _

end AlgebraicGeometry.FormalSpace

end
