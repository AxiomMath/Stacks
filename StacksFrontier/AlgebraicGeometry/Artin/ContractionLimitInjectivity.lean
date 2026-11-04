module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitInjective
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitReduction
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStage

/-!
# Injectivity in the limit preservation of Artin's contraction functor

The injectivity half of the proof of Stacks 0GI5, for an arbitrary `X'`, separated or not.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.exists_mapTriple_eq_of_isLimit`: two elements of
  `F(V_i)` which agree in `F(lim V_j)` agree in some `F(V_j)`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-- The formal component of a transported triple, in terms of the morphism of completions of
Stacks 0AMC. -/
theorem mapTriple_xhat_eq (c : ContractionSituation B S hS) {V₂ V₁ : BigFppfOver B S hS}
    (φ : V₂ ⟶ V₁) (t : Triple c V₁) :
    (mapTriple c φ t).xhat = Space.completionSheafMap B S hS (yoneda.map φ) t.Z ≫ t.xhat :=
  congrArg (· ≫ t.xhat) (Space.completionSheafRestrict_self B S hS (yoneda.map φ) t.Z _)

/-- Two transported triples with the same first component have the same formal component as soon
as the two compositions with the morphism of completions agree. -/
theorem heq_mapTriple_xhat_of_eq (c : ContractionSituation B S hS) {V₂ V₁ : BigFppfOver B S hS}
    (φ : V₂ ⟶ V₁) {Z : Set (Space.points B S hS (yoneda.obj V₁))} {hcZ₁ hcZ₂ : IsClosed Z}
    {u₁ u₂ : (Space.openSubspaceOfPoints B S hS (yoneda.obj V₁) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {x₁ x₂ : Space.completionSheaf B S hS (yoneda.obj V₁) Z ⟶ c.W} {a₁ a₂ w₁ w₂}
    (h : Space.completionSheafMap B S hS (yoneda.map φ) Z ≫ x₁ =
      Space.completionSheafMap B S hS (yoneda.map φ) Z ≫ x₂) :
    HEq (mapTriple c φ ⟨Z, hcZ₁, u₁, x₁, a₁, w₁⟩).xhat
      (mapTriple c φ ⟨Z, hcZ₂, u₂, x₂, a₂, w₂⟩).xhat := by
  rw [mapTriple_xhat_eq, mapTriple_xhat_eq]
  exact heq_of_eq h

/-- Conversely, equal transported formal components give equal compositions. -/
theorem completionSheafMap_comp_eq_of_heq (c : ContractionSituation B S hS)
    {V₂ V₁ : BigFppfOver B S hS}
    (φ : V₂ ⟶ V₁) {Z : Set (Space.points B S hS (yoneda.obj V₁))} {hcZ₁ hcZ₂ : IsClosed Z}
    {u₁ u₂ : (Space.openSubspaceOfPoints B S hS (yoneda.obj V₁) Zᶜ).toFunctor ⟶ c.U'.toFunctor}
    {x₁ x₂ : Space.completionSheaf B S hS (yoneda.obj V₁) Z ⟶ c.W} {a₁ a₂ w₁ w₂}
    (h : HEq (mapTriple c φ ⟨Z, hcZ₁, u₁, x₁, a₁, w₁⟩).xhat
      (mapTriple c φ ⟨Z, hcZ₂, u₂, x₂, a₂, w₂⟩).xhat) :
    Space.completionSheafMap B S hS (yoneda.map φ) Z ≫ x₁ =
      Space.completionSheafMap B S hS (yoneda.map φ) Z ≫ x₂ := by
  rw [mapTriple_xhat_eq, mapTriple_xhat_eq] at h
  exact eq_of_heq h

/-- **Two morphisms out of a completion agreeing after one morphism of completions agree after any
factorization of it**: if `g ≫ f = k` and `x₁, x₂` agree after `V₃_{/Z₃} ⟶ V₁_{/Z}`, they agree
after `V₃_{/Z₃} ⟶ V₂_{/Z₂} ⟶ V₁_{/Z}`. -/
theorem completionSheafMap_comp_comp_eq_of_eq {V₃ V₂ V₁ : BigFppfOver B S hS} (g : V₃ ⟶ V₂)
    (f : V₂ ⟶ V₁) (k : V₃ ⟶ V₁) (hk : g ≫ f = k) {Z : Set (Space.points B S hS (yoneda.obj V₁))}
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {x₁ x₂ : Space.completionSheaf B S hS (yoneda.obj V₁) Z ⟶ G}
    (hx : Space.completionSheafMap B S hS (yoneda.map k) Z ≫ x₁ =
      Space.completionSheafMap B S hS (yoneda.map k) Z ≫ x₂) :
    Space.completionSheafMap B S hS (yoneda.map g)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f) ⁻¹' Z) ≫
        Space.completionSheafMap B S hS (yoneda.map f) Z ≫ x₁ =
      Space.completionSheafMap B S hS (yoneda.map g)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f) ⁻¹' Z) ≫
        Space.completionSheafMap B S hS (yoneda.map f) Z ≫ x₂ := by
  subst hk
  have hT : Space.pointsMap B S hS (yoneda.obj V₃) (yoneda.map g) ⁻¹'
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f) ⁻¹' Z) =
      Space.pointsMap B S hS (yoneda.obj V₃) (yoneda.map (g ≫ f)) ⁻¹' Z := by
    rw [yoneda.map_comp, Space.pointsMap_comp, Set.preimage_comp]
  have e : Space.completionSheafMap B S hS (yoneda.map g)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map f) ⁻¹' Z) ≫
        Space.completionSheafMap B S hS (yoneda.map f) Z =
      Space.completionSheafRestrict B S hS (yoneda.map (g ≫ f)) _ Z hT.le := by
    rw [← Space.completionSheafRestrict_self B S hS (yoneda.map g) _ (fun _ hz => hz),
      ← Space.completionSheafRestrict_self B S hS (yoneda.map f) Z (fun _ hz => hz)]
    exact (Space.completionSheafRestrict_comp B S hS (yoneda.map g) (yoneda.map f) _ _ Z _ _
      (hT.trans (by rw [yoneda.map_comp])).le).symm.trans
      (Space.completionSheafRestrict_congr B S hS (yoneda.map_comp g f).symm _ _ _ _)
  rw [← Category.assoc, ← Category.assoc, e,
    Space.completionSheafRestrict_eq_eqToHom_comp B S hS _ _ _ _ hT, Category.assoc,
    Category.assoc, hx]

/-- Transporting two triples with the same first component preserves this equality. -/
private theorem mapTriple_Z_eq_of_Z_eq (c : ContractionSituation B S hS)
    {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) {t₁ t₂ : Triple c V₁} (hZ : t₁.Z = t₂.Z) :
    (mapTriple c φ t₁).Z = (mapTriple c φ t₂).Z :=
  congrArg (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' ·) hZ

/-- If two triples become equal over the limit, so do their transports to any stage. -/
private theorem mapTriple_π_mapTriple_eq (c : ContractionSituation B S hS) {I : Type u}
    [Category.{u} I] {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D} {i j : I}
    (f : j ⟶ i) {t₁ t₂ : Triple c (D.obj i).obj}
    (h : mapTriple c (κ.π.app i).hom t₁ = mapTriple c (κ.π.app i).hom t₂) :
    mapTriple c (κ.π.app j).hom (mapTriple c (D.map f).hom t₁) =
      mapTriple c (κ.π.app j).hom (mapTriple c (D.map f).hom t₂) := by
  rwa [mapTriple_π_mapTriple, mapTriple_π_mapTriple]

section Injective

variable (c : ContractionSituation B S hS)
  {I : Type u} [Category.{u} I] [IsCofiltered I] {D : I ⥤ LocallyNoetherianOver B S hS}
  {κ : Cone D} (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
  (hD : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
  (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt))

include hκ hD hpt in
/-- The second half of `exists_stage_xhat_heq`, once the reductions agree at a stage `jB`. -/
theorem exists_stage_xhat_heq_of_reduction (i : I)
    {Z : Set (Space.points B S hS (yoneda.obj (D.obj i).obj))} (hcZ hcZ₂ : IsClosed Z)
    {u₁ u₂ : (Space.openSubspaceOfPoints B S hS (yoneda.obj (D.obj i).obj) Zᶜ).toFunctor ⟶
      c.U'.toFunctor}
    {x₁ x₂ : Space.completionSheaf B S hS (yoneda.obj (D.obj i).obj) Z ⟶ c.W}
    (a₁ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS x₁.hom)
    (a₂ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS x₂.hom)
    (w₁ : Nonempty (CompatibilityWitness c (D.obj i).obj Z u₁ x₁))
    (w₂ : Nonempty (CompatibilityWitness c (D.obj i).obj Z u₂ x₂))
    (hxA : Space.completionSheafMap B S hS (yoneda.map (κ.π.app i).hom) Z ≫ x₁ =
      Space.completionSheafMap B S hS (yoneda.map (κ.π.app i).hom) Z ≫ x₂)
    (W₁ : CompatibilityWitness c (D.obj i).obj Z u₁ x₁)
    (W₂ : CompatibilityWitness c (D.obj i).obj Z u₂ x₂) (ψ : W₁.V' ⟶ W₂.V')
    (hψp : ψ ≫ W₂.p = W₁.p) (hψx : ψ ≫ W₂.x' = W₁.x') {jB : I} (fB : jB ⟶ i)
    (hred : FormalSpace.reducedClosedSubsetToCompletionSheaf B S hS
          (isAlgebraicSpace_yoneda B S hS (D.obj jB).obj)
          (Space.pointsMap B S hS _ (yoneda.map (D.map fB).hom) ⁻¹' Z)
          (hcZ.preimage (Space.continuous_pointsMap B S hS _)) ≫
        Space.completionSheafMap B S hS (yoneda.map (D.map fB).hom) Z ≫ x₁ =
      FormalSpace.reducedClosedSubsetToCompletionSheaf B S hS
          (isAlgebraicSpace_yoneda B S hS (D.obj jB).obj)
          (Space.pointsMap B S hS _ (yoneda.map (D.map fB).hom) ⁻¹' Z)
          (hcZ.preimage (Space.continuous_pointsMap B S hS _)) ≫
        Space.completionSheafMap B S hS (yoneda.map (D.map fB).hom) Z ≫ x₂) :
    ∃ (k : I) (f : k ⟶ jB),
      Space.completionSheafMap B S hS (yoneda.map (D.map f).hom)
          (Space.pointsMap B S hS _ (yoneda.map (D.map fB).hom) ⁻¹' Z) ≫
        Space.completionSheafMap B S hS (yoneda.map (D.map fB).hom) Z ≫ x₁ =
      Space.completionSheafMap B S hS (yoneda.map (D.map f).hom)
          (Space.pointsMap B S hS _ (yoneda.map (D.map fB).hom) ⁻¹' Z) ≫
        Space.completionSheafMap B S hS (yoneda.map (D.map fB).hom) Z ≫ x₂ := by
  obtain ⟨ψB, hψBp, hψBx⟩ := exists_hom_pullback_of_hom c (D.map fB).hom
    (s₁ := ⟨Z, hcZ, u₁, x₁, a₁, w₁⟩) (s₂ := ⟨Z, hcZ₂, u₂, x₂, a₂, w₂⟩) W₁ W₂ ψ hψp hψx
  have hE := isClosedImmersion_equalizer_of_reduction_eq c (D.obj jB).property
    (hcZ.preimage (Space.continuous_pointsMap B S hS _)) _ _ hred
  let WB := W₁.pullback (D.map fB).hom ⟨Z, hcZ, u₁, x₁, a₁, w₁⟩
  have hYx := completionSheafRestrict_comp_xhat_eq_of_hom c WB
    (W₂.pullback (D.map fB).hom ⟨Z, hcZ₂, u₂, x₂, a₂, w₂⟩) ψB hψBp hψBx
  rw [Space.completionSheafRestrict_self B S hS WB.p
    (mapTriple c (D.map fB).hom ⟨Z, hcZ, u₁, x₁, a₁, w₁⟩).Z (fun _ hz => hz)] at hYx
  have hYx' : Space.completionSheafMap B S hS WB.p
        (Space.pointsMap B S hS _ (yoneda.map (D.map fB).hom) ⁻¹' Z) ≫
        Space.completionSheafMap B S hS (yoneda.map (D.map fB).hom) Z ≫ x₁ =
      Space.completionSheafMap B S hS WB.p
        (Space.pointsMap B S hS _ (yoneda.map (D.map fB).hom) ⁻¹' Z) ≫
        Space.completionSheafMap B S hS (yoneda.map (D.map fB).hom) Z ≫ x₂ := by
    rwa [← mapTriple_xhat_eq c (D.map fB).hom ⟨Z, hcZ, u₁, x₁, a₁, w₁⟩,
      ← mapTriple_xhat_eq c (D.map fB).hom ⟨Z, hcZ₂, u₂, x₂, a₂, w₂⟩]
  have hlimB := completionSheafMap_comp_comp_eq_of_eq (κ.π.app jB).hom (D.map fB).hom
    (κ.π.app i).hom (congrArg (fun k => k.hom) (κ.w fB)) hxA
  exact exists_stage_completionSheafMap_comp_eq c hκ hD hpt jB
    (hcZ.preimage (Space.continuous_pointsMap B S hS _)) _ _ hlimB hE
    WB.isAlgebraicSpace_V' WB.p WB.isProper_p WB.j
    (WB.isPullback_j.w.symm.trans (Category.id_comp _)) hYx'

include hκ hD hpt in
/-- **The formal components agree at a stage**: if two triples over `V_i` have the same first
component, become equal over the limit, and admit witnesses related by a morphism `ψ` compatible
with the projections and the maps to `X'`, then their formal components agree over some `V_k`. -/
theorem exists_stage_xhat_heq (i : I) (t₁ t₂ : Triple c (D.obj i).obj) (hZ : t₁.Z = t₂.Z)
    (h : mapTriple c (κ.π.app i).hom t₁ = mapTriple c (κ.π.app i).hom t₂)
    (W₁ : CompatibilityWitness c (D.obj i).obj t₁.Z t₁.u t₁.xhat)
    (W₂ : CompatibilityWitness c (D.obj i).obj t₂.Z t₂.u t₂.xhat) (ψ : W₁.V' ⟶ W₂.V')
    (hψp : ψ ≫ W₂.p = W₁.p) (hψx : ψ ≫ W₂.x' = W₁.x') :
    ∃ (k : I) (f : k ⟶ i), HEq (mapTriple c (D.map f).hom t₁).xhat
      (mapTriple c (D.map f).hom t₂).xhat := by
  obtain ⟨Z, hcZ, u₁, x₁, a₁, w₁⟩ := t₁
  obtain ⟨Z₂, hcZ₂, u₂, x₂, a₂, w₂⟩ := t₂
  obtain rfl : Z = Z₂ := hZ
  have hxA := completionSheafMap_comp_eq_of_heq c (κ.π.app i).hom (congr_arg_heq Triple.xhat h)
  obtain ⟨jB, fB, hred⟩ := exists_reduction_comp_eq_of_isLimit c hκ hD hpt i hcZ x₁ x₂ hxA
  obtain ⟨k, f₃, h₃⟩ := exists_stage_xhat_heq_of_reduction c hκ hD hpt i hcZ hcZ₂ a₁ a₂ w₁ w₂
    hxA W₁ W₂ ψ hψp hψx fB hred
  refine ⟨k, f₃ ≫ fB, ?_⟩
  rw [mapTriple_map_comp, mapTriple_map_comp,
    mapTriple_xhat_eq c (D.map f₃).hom (mapTriple c (D.map fB).hom ⟨Z, hcZ, u₁, x₁, a₁, w₁⟩),
    mapTriple_xhat_eq c (D.map f₃).hom (mapTriple c (D.map fB).hom ⟨Z, hcZ₂, u₂, x₂, a₂, w₂⟩),
    mapTriple_xhat_eq c (D.map fB).hom ⟨Z, hcZ, u₁, x₁, a₁, w₁⟩,
    mapTriple_xhat_eq c (D.map fB).hom ⟨Z, hcZ₂, u₂, x₂, a₂, w₂⟩]
  exact heq_of_eq h₃

include hκ hD hpt in
/-- Two triples over `V_i` with the same first component which become equal over the limit become
equal over some `V_j`. -/
theorem exists_mapTriple_eq_of_isLimit_of_Z_eq (i : I) (t₁ t₂ : Triple c (D.obj i).obj)
    (hZ : t₁.Z = t₂.Z) (h : mapTriple c (κ.π.app i).hom t₁ = mapTriple c (κ.π.app i).hom t₂) :
    ∃ (j : I) (f : j ⟶ i), mapTriple c (D.map f).hom t₁ = mapTriple c (D.map f).hom t₂ := by
  obtain ⟨k, f, W₁, W₂, ψ, hψp, hψx⟩ := exists_stage_witness_hom c hκ hD hpt i t₁ t₂ h
  have hA := mapTriple_π_mapTriple_eq c f h
  have hZA := mapTriple_Z_eq_of_Z_eq c (D.map f).hom hZ
  obtain ⟨ν, g, hx⟩ := exists_stage_xhat_heq c hκ hD hpt k _ _ hZA hA W₁ W₂ ψ hψp hψx
  obtain ⟨k', g', hfin⟩ := exists_mapTriple_eq_of_xhat_heq c hκ hD hpt ν _ _
    (mapTriple_Z_eq_of_Z_eq c (D.map g).hom hZA) hx (mapTriple_π_mapTriple_eq c g hA)
  refine ⟨k', g' ≫ g ≫ f, ?_⟩
  simpa only [mapTriple_map_comp] using hfin

include hκ hD hpt in
/-- **Injectivity in the limit preservation of Artin's contraction functor** (the injectivity half
of the proof of Stacks 0GI5), for every `X'`, separated or not: two elements of `F(V_i)` which
agree in `F(V)` agree in some `F(V_j)`. The source's argument quotes Lemma 0GHE for the equalizer
`E'` of two witnesses, which needs `E' ⟶ V_i` proper, and that fails for non-separated `X'`; here
the comparison morphism of the witnesses over the limit is descended to a stage instead, and the
properness of one witness gives the finite torsion description of the equalizer of the formal
components (`AlgebraicGeometry.Space.exists_finset_torsion_iff_of_isProper`). -/
theorem exists_mapTriple_eq_of_isLimit (i : I) (t₁ t₂ : Triple c (D.obj i).obj)
    (h : mapTriple c (κ.π.app i).hom t₁ = mapTriple c (κ.π.app i).hom t₂) :
    ∃ (j : I) (f : j ⟶ i), mapTriple c (D.map f).hom t₁ = mapTriple c (D.map f).hom t₂ := by
  have hZlim : Space.pointsMap B S hS _ (yoneda.map (κ.π.app i).hom) ⁻¹' t₁.Z =
      Space.pointsMap B S hS _ (yoneda.map (κ.π.app i).hom) ⁻¹' t₂.Z := congrArg Triple.Z h
  obtain ⟨j, f, hf⟩ := exists_preimage_eq_of_isClosed hκ hD i t₁.isClosed_Z t₂.isClosed_Z hZlim
  obtain ⟨k, g, hg⟩ := exists_mapTriple_eq_of_isLimit_of_Z_eq c hκ hD hpt j
    (mapTriple c (D.map f).hom t₁) (mapTriple c (D.map f).hom t₂) hf
    (mapTriple_π_mapTriple_eq c f h)
  refine ⟨k, g ≫ f, ?_⟩
  simpa only [mapTriple_map_comp] using hg

end Injective

end AlgebraicGeometry.Artin.ContractionSituation

end
