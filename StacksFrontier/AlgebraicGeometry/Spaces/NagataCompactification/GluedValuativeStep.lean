module

public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.FlatCoverNearClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.SeparatedPushoutAlongChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.ClosedPointGeneric

/-!
# The valuative step of the proof of Stacks 0F4B

Let `U ⟶ Y` be separated, `(U₂ ⊆ U, f : U₁ ⟶ U)` an elementary distinguished square, and let
`W₁ = U ⊔_{U₁} N` and `W₂ = U ⊔_{U₂} N₂` be the two separated spaces of the repaired proof of
Stacks 0F4B, glued from open subspaces `N ⊆ X₁` and `N₂ ⊆ X₂` of compactifications of `U₁` and
`U₂`. The eighth paragraph of the source's proof shows: every morphism `γ : Spec K ⟶ U` from the
fraction field of a valuation ring `A`, compatible with `Spec A ⟶ Y`, extends after an extension
of valuation rings to `Spec A ⟶ W₁` or to `Spec A ⟶ W₂`.

* If `γ` lies over `Z = U ∖ U₂`, it lifts to `f⁻¹ Z ⊆ U₁`, and the extension to `X₁` has closed
  point in the closure of `f⁻¹ Z`, which lies in `N`.
* Otherwise `γ` lies in `U₂`, and extends to `g₂ : Spec A ⟶ X₂`. If the closed point lands in
  `N₂` or in `V₂` we are done (in the second case through `ψ₂ : V₂ ⟶ U`). Else it lies in the
  closure of `ψ₂⁻¹ Z`, and a flat `E ⟶ X₂` through the strict transform of `X₁₂` (Stacks 0F48)
  lifts `g₂` after an extension (Stacks 089F) to `E`, whose image in `X₁` lies in `N`; its
  generic point lies over `V₂`, so comes from `V₁`, hence from `N ∩ V₁ = U₁`.

## Main results

* `AlgebraicGeometry.Space.ValuativeSquare.exists_lift_of_range_subset_closedSet`: the first
  case.
* `AlgebraicGeometry.Space.ValuativeSquare.exists_lift_of_isFlat`: the flat case.
* `AlgebraicGeometry.Space.ValuativeSquare.exists_lift_of_range_subset_openSubspace`: the second
  case.
* `AlgebraicGeometry.Space.ValuativeSquare.exists_lift_of_isElementaryDistinguishedSquare`: the
  valuative step.

## Implementation notes

The valuative data are a valuative square `q` for an arbitrary morphism, of which only the
valuation ring, its fraction field and the structure morphism are used, together with
`γ : Spec K ⟶ U` and `σ : Spec A ⟶ Y`. This lets the statement be applied to the valuative
squares of the final glued space, whose generic points factor through `U`.

## References

* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

namespace ValuativeSquare

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

variable {Y U X₁ V₁ U₁ W₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : U ⟶ Y}

/-- **The points of the generic point of a valuative square form a subsingleton.** -/
theorem subsingleton_points_generic (q : ValuativeSquare p) :
    Subsingleton (points B S hS (yoneda.obj (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))) := by
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))) :=
    (inferInstance : Subsingleton (PrimeSpectrum q.K))
  exact (schemePointsHomeomorph B S hS _).injective.subsingleton

/-- A morphism from a representable into `X` whose points lie in an open set `N` factors through
the open subspace of `X` on `N`. -/
private theorem exists_comp_ι_eq_openSubspaceOfPoints {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {Nset : Set (points B S hS X)} (hNo : IsOpen Nset)
    {T : BigFppfOver B S hS} (φ : yoneda.obj T ⟶ X) (hφ : Set.range (pointsMap B S hS _ φ) ⊆ Nset) :
    ∃ φN : yoneda.obj T ⟶ (openSubspaceOfPoints B S hS X Nset).toFunctor,
      φN ≫ (openSubspaceOfPoints B S hS X Nset).ι = φ :=
  (factorsThrough_openSubspace_iff_points B S hS hX (isAlgebraicSpace_yoneda B S hS _) _
    (isOpenSubspace_openSubspaceOfPoints B S hS hX Nset hNo) φ).2
    (by rwa [range_pointsMap_ι_openSubspaceOfPoints])

/-- **The first case of the valuative step: the generic point over `Z`.** Let `π₁ : X₁ ⟶ Y`
satisfy the existence part of the valuative criterion, `ι₁ : V₁ ⟶ X₁` and `ψ₁ : V₁ ⟶ U` with
`ψ₁ ≫ p = ι₁ ≫ π₁`, and `j : U₁ ⟶ V₁` such that `f = j ≫ ψ₁` is an isomorphism over the reduced
closed subspace on a closed set `Z ⊆ |U|`. Let `N` be the open subspace of `X₁` on an open set
containing the closure of `f⁻¹ Z`, with `j_N : U₁ ⟶ N` over `j ≫ ι₁`, and let `h_N : N ⟶ W₁`,
`a : U ⟶ W₁` and `g : W₁ ⟶ Y` satisfy `j_N ≫ h_N = f ≫ a` and `h_N ≫ g = N ⟶ X₁ ⟶ Y`. Then a
morphism `γ : Spec K ⟶ U` over `Z`, compatible with `σ : Spec A ⟶ Y`, extends after a dominating
extension to `Spec A ⟶ W₁` over `σ`. -/
theorem exists_lift_of_range_subset_closedSet (hU : IsAlgebraicSpace B S hS U)
    {π₁ : X₁ ⟶ Y} (hπ₁ : ValuativeCriterion.Existence π₁) {ι₁ : V₁ ⟶ X₁} {ψ₁ : V₁ ⟶ U}
    (h₁ : ψ₁ ≫ p = ι₁ ≫ π₁) {j : U₁ ⟶ V₁} (Zs : Set (points B S hS U)) (hZs : IsClosed Zs)
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU Zs hZs).fromPreimage (j ≫ ψ₁)))
    (Nset : Set (points B S hS X₁)) (hNo : IsOpen Nset) (hX₁ : IsAlgebraicSpace B S hS X₁)
    (hN : closure (pointsMap B S hS U₁ (j ≫ ι₁) '' (pointsMap B S hS U₁ (j ≫ ψ₁) ⁻¹' Zs)) ⊆ Nset)
    {jN : U₁ ⟶ (openSubspaceOfPoints B S hS X₁ Nset).toFunctor}
    (hjN : jN ≫ (openSubspaceOfPoints B S hS X₁ Nset).ι = j ≫ ι₁)
    {hN' : (openSubspaceOfPoints B S hS X₁ Nset).toFunctor ⟶ W₁} {a : U ⟶ W₁} {g : W₁ ⟶ Y}
    (hsq : jN ≫ hN' = (j ≫ ψ₁) ≫ a) (hg : hN' ≫ g = (openSubspaceOfPoints B S hS X₁ Nset).ι ≫ π₁)
    {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f₀ : X₀ ⟶ Y₀} (q : ValuativeSquare f₀)
    (γ : yoneda.obj (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U)
    (σ : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ Y)
    (hγσ : γ ≫ p = yoneda.map q.fracHom ≫ σ)
    (hγ : Set.range (pointsMap B S hS _ γ) ⊆ Zs) :
    ∃ (e : q.DominatingExtension)
      (h : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ W₁),
      yoneda.map e.square.fracHom ≫ h = yoneda.map e.genericOver ≫ γ ≫ a ∧
        h ≫ g = yoneda.map e.specialOver ≫ σ := by
  set Zc := reducedClosedSubspace B S hS U hU Zs hZs with hZc
  have hred : HasEtaleLocalProperty B S hS (yoneda.obj (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
      (fun Y : Scheme.{u} => IsReduced Y) := by
    refine hasEtaleLocalProperty_of_representable B S hS _ _ _ (Iso.refl _) ?_
    change IsReduced (Spec (.of q.K))
    infer_instance
  obtain ⟨γ', hγ'⟩ := (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS U hU
    Zs hZs (isAlgebraicSpace_yoneda B S hS _) hred γ).2 hγ
  -- the lift of the generic point to `U₁`
  set γ₁ := γ' ≫ inv (Zc.fromPreimage (j ≫ ψ₁)) ≫ (Zc.preimage (j ≫ ψ₁)).ι with hγ₁
  have hγ₁f : γ₁ ≫ j ≫ ψ₁ = γ := by
    rw [hγ₁, Category.assoc, Category.assoc, ← Subfunctor.fromPreimage_ι, IsIso.inv_hom_id_assoc,
      hγ']
  have hγ₁Z : Set.range (pointsMap B S hS _ γ₁) ⊆ pointsMap B S hS U₁ (j ≫ ψ₁) ⁻¹' Zs := by
    rintro _ ⟨x, rfl⟩
    rw [Set.mem_preimage, ← pointsMap_comp_apply, hγ₁f]
    exact hγ ⟨x, rfl⟩
  -- the extension to `X₁`
  obtain ⟨e, φ, hφgen, hφsp⟩ := exists_dominatingExtension_lift_of_existence q π₁ hπ₁
    (γ₁ ≫ j ≫ ι₁) σ (by
      have : (γ₁ ≫ j ≫ ι₁) ≫ π₁ = (γ₁ ≫ j ≫ ψ₁) ≫ p := by simp only [Category.assoc, h₁]
      rw [this, hγ₁f]
      exact hγσ)
  -- it lands in `N`
  have hφN : Set.range (pointsMap B S hS _ φ) ⊆ Nset := by
    refine (e.square.range_subset_closure_range_fracHom_comp φ).trans
      ((closure_mono ?_).trans hN)
    rw [hφgen]
    rintro _ ⟨x, rfl⟩
    refine ⟨pointsMap B S hS _ γ₁ (pointsMap B S hS _ (yoneda.map e.genericOver) x),
      hγ₁Z ⟨_, rfl⟩, ?_⟩
    simp only [← pointsMap_comp_apply, Category.assoc]
  obtain ⟨φN, hφN'⟩ := exists_comp_ι_eq_openSubspaceOfPoints hX₁ hNo φ hφN
  refine ⟨e, φN ≫ hN', ?_, ?_⟩
  · have hgen : yoneda.map e.square.fracHom ≫ φN = yoneda.map e.genericOver ≫ γ₁ ≫ jN := by
      refine (cancel_mono (openSubspaceOfPoints B S hS X₁ Nset).ι).1 ?_
      simp only [Category.assoc]
      rw [hφN', hφgen, hjN]
    rw [reassoc_of% hgen, hsq, ← reassoc_of% hγ₁f]
    simp only [Category.assoc]
  · rw [Category.assoc, hg, reassoc_of% hφN', hφsp]

/-- **The flat case of the valuative step.** Let `t : E ⟶ X₂` be flat and `r : E ⟶ X₁` with
`r ≫ π₁ = t ≫ π₂`, landing in an open set `N ⊆ |X₁|` with `N ∩ V₁ ⊆ U₁`, such that every scheme
point of `E` over `V₂` comes, through `r`, from a point of `V₁` with the same image in `U`. Let
`φ : Spec A ⟶ X₂` send the closed point into the image of `t`, with generic point
`γ' ≫ e₂ ≫ ι₂` for some `γ' : Spec K ⟶ U₂`. Then after a dominating extension there is a morphism
`Spec A ⟶ W₁` extending `γ' ≫ U₂ ⟶ U ⟶ W₁` over `φ ≫ π₂`. -/
theorem exists_lift_of_isFlat {U₂ X₂ V₂ E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f' : X₀ ⟶ Y₀} (q : ValuativeSquare f')
    (hX₁ : IsAlgebraicSpace B S hS X₁) (hX₂ : IsAlgebraicSpace B S hS X₂)
    (hV₁ : IsAlgebraicSpace B S hS V₁) (hU₁ : IsAlgebraicSpace B S hS U₁)
    (hE : IsAlgebraicSpace B S hS E) {π₁ : X₁ ⟶ Y} {π₂ : X₂ ⟶ Y} {ι₁ : V₁ ⟶ X₁}
    (hι₁ : IsOpenImmersion B S hS ι₁) {ψ₁ : V₁ ⟶ U} {j : U₁ ⟶ V₁}
    (hj : IsOpenImmersion B S hS j) {ι₂ : V₂ ⟶ X₂} {ψ₂ : V₂ ⟶ U} {e₂ : U₂ ⟶ V₂} {i₂ : U₂ ⟶ U}
    (he₂ : e₂ ≫ ψ₂ = i₂)
    (Nset : Set (points B S hS X₁)) (hNo : IsOpen Nset)
    (hN₂ : Nset ∩ Set.range (pointsMap B S hS V₁ ι₁) ⊆ Set.range (pointsMap B S hS U₁ (j ≫ ι₁)))
    {jN : U₁ ⟶ (openSubspaceOfPoints B S hS X₁ Nset).toFunctor}
    (hjN : jN ≫ (openSubspaceOfPoints B S hS X₁ Nset).ι = j ≫ ι₁)
    {hN' : (openSubspaceOfPoints B S hS X₁ Nset).toFunctor ⟶ W₁} {a : U ⟶ W₁} {g : W₁ ⟶ Y}
    (hsq : jN ≫ hN' = (j ≫ ψ₁) ≫ a) (hg : hN' ≫ g = (openSubspaceOfPoints B S hS X₁ Nset).ι ≫ π₁)
    {t : E ⟶ X₂} (ht : IsFlat B S hS t) {r : E ⟶ X₁} (hr : r ≫ π₁ = t ≫ π₂)
    (hrN : Set.range (pointsMap B S hS E r) ⊆ Nset)
    (hfac : ∀ (T' : BigFppfOver B S hS) (s : yoneda.obj T' ⟶ E) (v : yoneda.obj T' ⟶ V₂),
      s ≫ t = v ≫ ι₂ → ∃ v₁ : yoneda.obj T' ⟶ V₁, v₁ ≫ ι₁ = s ≫ r ∧ v₁ ≫ ψ₁ = v ≫ ψ₂)
    (φ : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ X₂)
    (γ' : yoneda.obj (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U₂)
    (hφgen : yoneda.map q.fracHom ≫ φ = γ' ≫ e₂ ≫ ι₂)
    (himage : pointsMap B S hS _ φ q.closedPoint ∈ Set.range (pointsMap B S hS E t)) :
    ∃ (e : q.DominatingExtension)
      (h : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ W₁),
      yoneda.map e.square.fracHom ≫ h = yoneda.map e.genericOver ≫ γ' ≫ i₂ ≫ a ∧
        h ≫ g = yoneda.map e.specialOver ≫ φ ≫ π₂ := by
  have : Mono ι₁ := mono_of_presheaf_isOpenImmersion hι₁
  obtain ⟨e, ψ', hψ'⟩ := q.exists_dominatingExtension_lift_of_isFlat hE hX₂ t ht φ himage
  -- the image in `X₁` lies in `N`
  obtain ⟨κN, hκN⟩ := exists_comp_ι_eq_openSubspaceOfPoints hX₁ hNo (ψ' ≫ r) (by
      rw [pointsMap_comp, Set.range_comp]
      exact (Set.image_subset_range _ _).trans hrN)
  -- the generic point comes from `V₁`
  have hst : (yoneda.map e.square.fracHom ≫ ψ') ≫ t =
      (yoneda.map e.genericOver ≫ γ' ≫ e₂) ≫ ι₂ := by
    rw [Category.assoc, hψ', ← Category.assoc, ← e.yonedaMap_genericOver_comp_fracHom,
      Category.assoc, hφgen]
    simp only [Category.assoc]
  obtain ⟨v₁, hv₁ι, hv₁ψ⟩ := hfac _ _ _ hst
  -- and from `U₁`, since `N ∩ V₁ ⊆ U₁`
  obtain ⟨u, hu⟩ := exists_comp_eq_of_isOpenImmersion_of_range_pointsMap_subset hU₁
    (isAlgebraicSpace_yoneda B S hS _) hV₁ hj v₁ (by
      rintro _ ⟨τ, rfl⟩
      have h1 : pointsMap B S hS _ ι₁ (pointsMap B S hS _ v₁ τ) ∈ Nset := by
        rw [← pointsMap_comp_apply, hv₁ι, pointsMap_comp_apply]
        exact hrN ⟨_, rfl⟩
      obtain ⟨w, hw⟩ := hN₂ ⟨h1, _, rfl⟩
      refine ⟨w, pointsMap_injective_of_mono B S hS ι₁ ?_⟩
      rw [← hw, pointsMap_comp_apply])
  refine ⟨e, κN ≫ hN', ?_, ?_⟩
  · have hgen : yoneda.map e.square.fracHom ≫ κN = u ≫ jN := by
      refine (cancel_mono (openSubspaceOfPoints B S hS X₁ Nset).ι).1 ?_
      rw [Category.assoc, hκN, Category.assoc, hjN, ← Category.assoc u, hu, hv₁ι,
        Category.assoc]
    rw [reassoc_of% hgen, hsq, ← he₂]
    have : u ≫ (j ≫ ψ₁) ≫ a = v₁ ≫ ψ₁ ≫ a := by
      rw [← hu]
      simp only [Category.assoc]
    rw [this, reassoc_of% hv₁ψ]
    simp only [Category.assoc]
  · rw [Category.assoc, hg, reassoc_of% hκN, hr, reassoc_of% hψ']

/-- **The second case of the valuative step: the generic point in `U₂`.** In the situation of
`AlgebraicGeometry.Space.ValuativeSquare.exists_lift_of_isFlat`, let moreover `π₂ : X₂ ⟶ Y`
satisfy the existence part of the valuative criterion, `ψ₂ ≫ p = ι₂ ≫ π₂`, `e₂ : U₂ ⟶ V₂` over the
inclusion `U₂ ⊆ U`, every point of `V₂` off `U₂` lying over `Z`, and the closure of `ψ₂⁻¹ Z` in
`X₂` contained in the image of `t`. Let `N₂` be the open subspace of `X₂` off the closure of
`V₂ ∖ U₂`, glued to `U` along `U₂` into `W₂`. Then a morphism `γ : Spec K ⟶ U` into `U₂`,
compatible with `σ : Spec A ⟶ Y`, extends after a dominating extension to `Spec A ⟶ W₁` or to
`Spec A ⟶ W₂` over `σ`. -/
theorem exists_lift_of_range_subset_openSubspace {U₂ : Subfunctor U}
    {X₂ V₂ E W₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hU₂ : IsOpenSubspace B S hS U₂)
    (hX₁ : IsAlgebraicSpace B S hS X₁) (hX₂ : IsAlgebraicSpace B S hS X₂)
    (hV₁ : IsAlgebraicSpace B S hS V₁) (hV₂ : IsAlgebraicSpace B S hS V₂)
    (hU₁ : IsAlgebraicSpace B S hS U₁) (hE : IsAlgebraicSpace B S hS E)
    {π₁ : X₁ ⟶ Y} {π₂ : X₂ ⟶ Y} (hπ₂ : ValuativeCriterion.Existence π₂) {ι₁ : V₁ ⟶ X₁}
    (hι₁ : IsOpenImmersion B S hS ι₁) {ψ₁ : V₁ ⟶ U} {j : U₁ ⟶ V₁}
    (hj : IsOpenImmersion B S hS j) {ι₂ : V₂ ⟶ X₂} (hι₂ : IsOpenImmersion B S hS ι₂)
    {ψ₂ : V₂ ⟶ U} (h₂ : ψ₂ ≫ p = ι₂ ≫ π₂) {e₂ : U₂.toFunctor ⟶ V₂} (he₂ : e₂ ≫ ψ₂ = U₂.ι)
    (Zs : Set (points B S hS U))
    (hV₂Z : (Set.range (pointsMap B S hS _ e₂))ᶜ ⊆ pointsMap B S hS V₂ ψ₂ ⁻¹' Zs)
    (Nset : Set (points B S hS X₁)) (hNo : IsOpen Nset)
    (hN₂ : Nset ∩ Set.range (pointsMap B S hS V₁ ι₁) ⊆ Set.range (pointsMap B S hS U₁ (j ≫ ι₁)))
    {jN : U₁ ⟶ (openSubspaceOfPoints B S hS X₁ Nset).toFunctor}
    (hjN : jN ≫ (openSubspaceOfPoints B S hS X₁ Nset).ι = j ≫ ι₁)
    {hN' : (openSubspaceOfPoints B S hS X₁ Nset).toFunctor ⟶ W₁} {a₁ : U ⟶ W₁} {g₁ : W₁ ⟶ Y}
    (hsq₁ : jN ≫ hN' = (j ≫ ψ₁) ≫ a₁)
    (hg₁ : hN' ≫ g₁ = (openSubspaceOfPoints B S hS X₁ Nset).ι ≫ π₁)
    {jN₂ : U₂.toFunctor ⟶ (openSubspaceOfPoints B S hS X₂
      (closure (pointsMap B S hS V₂ ι₂ '' (Set.range (pointsMap B S hS _ e₂))ᶜ))ᶜ).toFunctor}
    (hjN₂ : jN₂ ≫ (openSubspaceOfPoints B S hS X₂
      (closure (pointsMap B S hS V₂ ι₂ '' (Set.range (pointsMap B S hS _ e₂))ᶜ))ᶜ).ι = e₂ ≫ ι₂)
    {hN₂' : (openSubspaceOfPoints B S hS X₂
      (closure (pointsMap B S hS V₂ ι₂ '' (Set.range (pointsMap B S hS _ e₂))ᶜ))ᶜ).toFunctor ⟶ W₂}
    {a₂ : U ⟶ W₂} {g₂ : W₂ ⟶ Y} (hsq₂ : jN₂ ≫ hN₂' = (e₂ ≫ ψ₂) ≫ a₂)
    (hg₂ : hN₂' ≫ g₂ = (openSubspaceOfPoints B S hS X₂
      (closure (pointsMap B S hS V₂ ι₂ '' (Set.range (pointsMap B S hS _ e₂))ᶜ))ᶜ).ι ≫ π₂)
    (ha₂ : a₂ ≫ g₂ = p)
    {t : E ⟶ X₂} (ht : IsFlat B S hS t) {r : E ⟶ X₁} (hr : r ≫ π₁ = t ≫ π₂)
    (hrN : Set.range (pointsMap B S hS E r) ⊆ Nset)
    (hcl : closure (pointsMap B S hS V₂ ι₂ '' (pointsMap B S hS V₂ ψ₂ ⁻¹' Zs)) ⊆
      Set.range (pointsMap B S hS E t))
    (hfac : ∀ (T' : BigFppfOver B S hS) (s : yoneda.obj T' ⟶ E) (v : yoneda.obj T' ⟶ V₂),
      s ≫ t = v ≫ ι₂ → ∃ v₁ : yoneda.obj T' ⟶ V₁, v₁ ≫ ι₁ = s ≫ r ∧ v₁ ≫ ψ₁ = v ≫ ψ₂)
    {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f₀ : X₀ ⟶ Y₀} (q : ValuativeSquare f₀)
    (γ : yoneda.obj (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U)
    (σ : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ Y)
    (hγσ : γ ≫ p = yoneda.map q.fracHom ≫ σ)
    (hγ : Set.range (pointsMap B S hS _ γ) ⊆ Set.range (pointsMap B S hS _ U₂.ι)) :
    ∃ e : q.DominatingExtension,
      (∃ h : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ W₁,
        yoneda.map e.square.fracHom ≫ h = yoneda.map e.genericOver ≫ γ ≫ a₁ ∧
          h ≫ g₁ = yoneda.map e.specialOver ≫ σ) ∨
      (∃ h : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ W₂,
        yoneda.map e.square.fracHom ≫ h = yoneda.map e.genericOver ≫ γ ≫ a₂ ∧
          h ≫ g₂ = yoneda.map e.specialOver ≫ σ) := by
  have : Mono ι₂ := mono_of_presheaf_isOpenImmersion hι₂
  obtain ⟨γ₂, hγ₂⟩ := (factorsThrough_openSubspace_iff_points B S hS hU
    (isAlgebraicSpace_yoneda B S hS _) U₂ hU₂ γ).2 hγ
  -- the extension to `X₂`
  obtain ⟨e, φ, hφgen, hφsp⟩ := exists_dominatingExtension_lift_of_existence q π₂ hπ₂
    (γ₂ ≫ e₂ ≫ ι₂) σ (by
      have : (γ₂ ≫ e₂ ≫ ι₂) ≫ π₂ = (γ₂ ≫ e₂ ≫ ψ₂) ≫ p := by simp only [Category.assoc, h₂]
      rw [this, he₂, hγ₂]
      exact hγσ)
  by_cases hN : pointsMap B S hS _ φ e.square.closedPoint ∈
      (closure (pointsMap B S hS V₂ ι₂ '' (Set.range (pointsMap B S hS _ e₂))ᶜ))ᶜ
  · -- the closed point lies in `N₂`
    obtain ⟨φN, hφN⟩ := exists_comp_ι_eq_openSubspaceOfPoints hX₂ isClosed_closure.isOpen_compl φ
      (e.square.range_subset_of_closedPoint_mem φ isClosed_closure.isOpen_compl hN)
    refine ⟨e, Or.inr ⟨φN ≫ hN₂', ?_, ?_⟩⟩
    · have hgen : yoneda.map e.square.fracHom ≫ φN = yoneda.map e.genericOver ≫ γ₂ ≫ jN₂ := by
        refine (cancel_mono (openSubspaceOfPoints B S hS X₂
          (closure (pointsMap B S hS V₂ ι₂ '' (Set.range (pointsMap B S hS _ e₂))ᶜ))ᶜ).ι).1 ?_
        rw [Category.assoc, hφN, hφgen, Category.assoc, Category.assoc, hjN₂]
      rw [reassoc_of% hgen, hsq₂, he₂, ← hγ₂]
      simp only [Category.assoc]
    · rw [Category.assoc, hg₂, reassoc_of% hφN, hφsp]
  by_cases hV : pointsMap B S hS _ φ e.square.closedPoint ∈ Set.range (pointsMap B S hS V₂ ι₂)
  · -- the closed point lies in `V₂`
    have hVo : IsOpen (Set.range (pointsMap B S hS V₂ ι₂)) := by
      rw [← Set.image_univ]
      exact isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hι₂ _ isOpen_univ
    obtain ⟨φV, hφV⟩ := exists_comp_eq_of_isOpenImmersion_of_range_pointsMap_subset hV₂
      (isAlgebraicSpace_yoneda B S hS _) hX₂ hι₂ φ
      (e.square.range_subset_of_closedPoint_mem φ hVo hV)
    refine ⟨e, Or.inr ⟨φV ≫ ψ₂ ≫ a₂, ?_, ?_⟩⟩
    · have hgen : yoneda.map e.square.fracHom ≫ φV = yoneda.map e.genericOver ≫ γ₂ ≫ e₂ := by
        refine (cancel_mono ι₂).1 ?_
        rw [Category.assoc, hφV, hφgen]
        simp only [Category.assoc]
      rw [reassoc_of% hgen, ← hγ₂, ← he₂]
      simp only [Category.assoc]
    · rw [Category.assoc, Category.assoc, ha₂, h₂, reassoc_of% hφV, hφsp]
  · -- otherwise it lies in the closure of `ψ₂⁻¹ Z`, hence in the image of `t`
    have hcl' : pointsMap B S hS _ φ e.square.closedPoint ∈ Set.range (pointsMap B S hS E t) := by
      refine hcl (closure_mono (Set.image_mono hV₂Z) ?_)
      simpa using hN
    obtain ⟨e', h, hgen, hsp⟩ := exists_lift_of_isFlat e.square hX₁ hX₂ hV₁ hU₁ hE hι₁ hj he₂
      Nset hNo hN₂ hjN hsq₁ hg₁ ht hr hrN hfac φ (yoneda.map e.genericOver ≫ γ₂)
      (by rw [hφgen]; simp only [Category.assoc]) hcl'
    refine ⟨e.trans e', Or.inl ⟨h, ?_, ?_⟩⟩
    · change yoneda.map e'.square.fracHom ≫ h =
        yoneda.map (e'.genericOver ≫ e.genericOver) ≫ γ ≫ a₁
      rw [hgen, Functor.map_comp, ← hγ₂]
      simp only [Category.assoc]
    · change h ≫ g₁ = yoneda.map (e'.specialOver ≫ e.specialOver) ≫ σ
      rw [hsp, Functor.map_comp, Category.assoc, hφsp]

/-- **The valuative step of the proof of Stacks 0F4B** (its eighth paragraph, with the chart `N`
of the repair in place of `X₁ ∖ (Z̄₁₂ ∪ T̄)`). Let `(U₂ ⊆ U, f = j ≫ ψ₁ : U₁ ⟶ U)` be an
elementary distinguished square, with `Z = U ∖ U₂`; let `W₁ = U ⊔_{U₁} N` and
`W₂ = U ⊔_{U₂} N₂` be glued from open subspaces `N ⊆ X₁` and `N₂ ⊆ X₂` as in
`AlgebraicGeometry.Space.ValuativeSquare.exists_lift_of_range_subset_closedSet` and
`AlgebraicGeometry.Space.ValuativeSquare.exists_lift_of_range_subset_openSubspace`, and let
`t : E ⟶ X₂` be the flat cover of the closure of `ψ₂⁻¹ Z`. Then every `γ : Spec K ⟶ U`
compatible with `σ : Spec A ⟶ Y` extends, after a dominating extension of valuation rings, to
`Spec A ⟶ W₁` or to `Spec A ⟶ W₂`, over `σ`. -/
theorem exists_lift_of_isElementaryDistinguishedSquare {U₂ : Subfunctor U}
    {X₂ V₂ E W₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hU₂ : IsOpenSubspace B S hS U₂)
    (hX₁ : IsAlgebraicSpace B S hS X₁) (hX₂ : IsAlgebraicSpace B S hS X₂)
    (hV₁ : IsAlgebraicSpace B S hS V₁) (hV₂ : IsAlgebraicSpace B S hS V₂)
    (hU₁ : IsAlgebraicSpace B S hS U₁) (hE : IsAlgebraicSpace B S hS E)
    {π₁ : X₁ ⟶ Y} {π₂ : X₂ ⟶ Y} (hπ₁ : ValuativeCriterion.Existence π₁)
    (hπ₂ : ValuativeCriterion.Existence π₂) {ι₁ : V₁ ⟶ X₁}
    (hι₁ : IsOpenImmersion B S hS ι₁) {ψ₁ : V₁ ⟶ U} (h₁ : ψ₁ ≫ p = ι₁ ≫ π₁) {j : U₁ ⟶ V₁}
    (hj : IsOpenImmersion B S hS j) {ι₂ : V₂ ⟶ X₂} (hι₂ : IsOpenImmersion B S hS ι₂)
    {ψ₂ : V₂ ⟶ U} (h₂ : ψ₂ ≫ p = ι₂ ≫ π₂) {e₂ : U₂.toFunctor ⟶ V₂} (he₂ : e₂ ≫ ψ₂ = U₂.ι)
    (hZs : IsClosed (Set.range (pointsMap B S hS _ U₂.ι))ᶜ)
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU _ hZs).fromPreimage (j ≫ ψ₁)))
    (hV₂Z : (Set.range (pointsMap B S hS _ e₂))ᶜ ⊆
      pointsMap B S hS V₂ ψ₂ ⁻¹' (Set.range (pointsMap B S hS _ U₂.ι))ᶜ)
    (Nset : Set (points B S hS X₁)) (hNo : IsOpen Nset)
    (hN₂ : Nset ∩ Set.range (pointsMap B S hS V₁ ι₁) ⊆ Set.range (pointsMap B S hS U₁ (j ≫ ι₁)))
    (hN₃ : closure (pointsMap B S hS U₁ (j ≫ ι₁) ''
      (pointsMap B S hS U₁ (j ≫ ψ₁) ⁻¹' (Set.range (pointsMap B S hS _ U₂.ι))ᶜ)) ⊆ Nset)
    {jN : U₁ ⟶ (openSubspaceOfPoints B S hS X₁ Nset).toFunctor}
    (hjN : jN ≫ (openSubspaceOfPoints B S hS X₁ Nset).ι = j ≫ ι₁)
    {hN' : (openSubspaceOfPoints B S hS X₁ Nset).toFunctor ⟶ W₁} {a₁ : U ⟶ W₁} {g₁ : W₁ ⟶ Y}
    (hsq₁ : jN ≫ hN' = (j ≫ ψ₁) ≫ a₁)
    (hg₁ : hN' ≫ g₁ = (openSubspaceOfPoints B S hS X₁ Nset).ι ≫ π₁)
    {jN₂ : U₂.toFunctor ⟶ (openSubspaceOfPoints B S hS X₂
      (closure (pointsMap B S hS V₂ ι₂ '' (Set.range (pointsMap B S hS _ e₂))ᶜ))ᶜ).toFunctor}
    (hjN₂ : jN₂ ≫ (openSubspaceOfPoints B S hS X₂
      (closure (pointsMap B S hS V₂ ι₂ '' (Set.range (pointsMap B S hS _ e₂))ᶜ))ᶜ).ι = e₂ ≫ ι₂)
    {hN₂' : (openSubspaceOfPoints B S hS X₂
      (closure (pointsMap B S hS V₂ ι₂ '' (Set.range (pointsMap B S hS _ e₂))ᶜ))ᶜ).toFunctor ⟶ W₂}
    {a₂ : U ⟶ W₂} {g₂ : W₂ ⟶ Y} (hsq₂ : jN₂ ≫ hN₂' = (e₂ ≫ ψ₂) ≫ a₂)
    (hg₂ : hN₂' ≫ g₂ = (openSubspaceOfPoints B S hS X₂
      (closure (pointsMap B S hS V₂ ι₂ '' (Set.range (pointsMap B S hS _ e₂))ᶜ))ᶜ).ι ≫ π₂)
    (ha₂ : a₂ ≫ g₂ = p)
    {t : E ⟶ X₂} (ht : IsFlat B S hS t) {r : E ⟶ X₁} (hr : r ≫ π₁ = t ≫ π₂)
    (hrN : Set.range (pointsMap B S hS E r) ⊆ Nset)
    (hcl : closure (pointsMap B S hS V₂ ι₂ ''
      (pointsMap B S hS V₂ ψ₂ ⁻¹' (Set.range (pointsMap B S hS _ U₂.ι))ᶜ)) ⊆
      Set.range (pointsMap B S hS E t))
    (hfac : ∀ (T' : BigFppfOver B S hS) (s : yoneda.obj T' ⟶ E) (v : yoneda.obj T' ⟶ V₂),
      s ≫ t = v ≫ ι₂ → ∃ v₁ : yoneda.obj T' ⟶ V₁, v₁ ≫ ι₁ = s ≫ r ∧ v₁ ≫ ψ₁ = v ≫ ψ₂)
    {X₀ Y₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f₀ : X₀ ⟶ Y₀} (q : ValuativeSquare f₀)
    (γ : yoneda.obj (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U)
    (σ : yoneda.obj (siteObject B S hS q.ring_mem q.base) ⟶ Y)
    (hγσ : γ ≫ p = yoneda.map q.fracHom ≫ σ) :
    ∃ e : q.DominatingExtension,
      (∃ h : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ W₁,
        yoneda.map e.square.fracHom ≫ h = yoneda.map e.genericOver ≫ γ ≫ a₁ ∧
          h ≫ g₁ = yoneda.map e.specialOver ≫ σ) ∨
      (∃ h : yoneda.obj (siteObject B S hS e.square.ring_mem e.square.base) ⟶ W₂,
        yoneda.map e.square.fracHom ≫ h = yoneda.map e.genericOver ≫ γ ≫ a₂ ∧
          h ≫ g₂ = yoneda.map e.specialOver ≫ σ) := by
  by_cases hγ : Set.range (pointsMap B S hS _ γ) ⊆ Set.range (pointsMap B S hS _ U₂.ι)
  · exact exists_lift_of_range_subset_openSubspace hU hU₂ hX₁ hX₂ hV₁ hV₂ hU₁ hE hπ₂ hι₁ hj hι₂
      h₂ he₂ _ hV₂Z Nset hNo hN₂ hjN hsq₁ hg₁ hjN₂ hsq₂ hg₂ ha₂ ht hr hrN hcl hfac q γ σ hγσ hγ
  · obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Set.not_subset.1 hγ
    have hsub := q.subsingleton_points_generic
    obtain ⟨e, h, hh₁, hh₂⟩ := exists_lift_of_range_subset_closedSet hU hπ₁ h₁ _ hZs hiso Nset
      hNo hX₁ hN₃ hjN hsq₁ hg₁ q γ σ hγσ (by
        rintro _ ⟨y, rfl⟩
        rw [Subsingleton.elim y x]
        exact hx)
    exact ⟨e, Or.inl ⟨h, hh₁, hh₂⟩⟩

end ValuativeSquare

end AlgebraicGeometry.Space

end
