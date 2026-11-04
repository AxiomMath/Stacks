module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentSpacesEtale
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedCocyclePairUnit
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedTransitionCompTwoIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictPseudonatural
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoAugmentedTransitionCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoPastingOfToposHom

/-!
# Stacks 0GMF on the strict components, realized: the pseudonaturality of the realizations

The structure `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictPairRealization` asserts
that a pair `(K₀, α)` on the spaces-étale sites satisfying the cocycle condition comes from a pair
of Stacks 0GMF on the strict components. Its content is the pseudonaturality of the realizations
`R_n` against the compositors of derived pullbacks (Stacks 0D6D) on both sides, proved here:

* `SimplicialSpacesEtaleSite.strictComponentDerivedTransitionIso_comp_hypercoverPullTriangle` and
  `SimplicialSpacesEtaleSite.strictComponentDerivedTransitionIso_compOfEq`: the compositor
  `Lf_φ^* Lf_ψ^* ≅ Lf_θ^*` of the strict components realizes, through the squares
  `strictComponentDerivedTransitionIso`, to the comparison `LX(θ)^* ⟶ LX(φ)^* LX(ψ)^*`. It is the
  pasting of squares of derived pullbacks (`derivedPullbackTwoIsoSquare_pasting`) at the pasting
  identity of the 2-isomorphisms of the strict components
  (`strictComponentTransitionTwoIso_pasting`), with the compositor of the derived transitions read
  through the 2-isomorphism of the transitions (`derivedTransitionCompComparison_eq_twoIso`).
* `CategoryTheory.hypercoverCocycle_of_realize`, over arbitrary categories: the cocycle condition
  of `α` transported along a faithful realization gives that of the pair, and
  `CategoryTheory.hypercoverPair_realize_delta_zero`,
  `CategoryTheory.hypercoverPair_realize_delta_one` for the realizations of the transitions in
  degree one.

## References

* [Stacks Project, Tag 0GMF](https://stacks.math.columbia.edu/tag/0GMF)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

section CocycleTransport

variable {𝒞₀ : Type u₁} [Category.{v₁} 𝒞₀] {𝒞₁ : Type u₂} [Category.{v₂} 𝒞₁]
  {𝒞₂ : Type u₃} [Category.{v₃} 𝒞₂] {𝒜₀ : Type u₄} [Category.{v₄} 𝒜₀]
  {𝒜₁ : Type u₅} [Category.{v₅} 𝒜₁] {𝒜₂ : Type u₆} [Category.{v₆} 𝒜₂]

/-- The cocycle condition of Stacks 0GMF in the realizations, over a single category: the
realized transitions and identifications of the three faces, written through the comparisons
`c` and the pullback triangles `T` of the vertices, satisfy the cocycle condition as soon as the
triangles do. -/
theorem hypercoverCocycle_core {Y₁s Y₁t Y₂s Y₂t Y₀s Y₀t Z₁s Z₁t Z₂s Z₂t Z₀s Z₀t U₀ U₁ U₂ : 𝒜₂}
    (c₁s : Y₁s ≅ Z₁s) (c₁t : Y₁t ≅ Z₁t) (c₂s : Y₂s ≅ Z₂s) (c₂t : Y₂t ≅ Z₂t)
    (c₀s : Y₀s ≅ Z₀s) (c₀t : Y₀t ≅ Z₀t) (a₁ : Z₁s ⟶ Z₁t) (a₂ : Z₂s ⟶ Z₂t) (a₀ : Z₀s ⟶ Z₀t)
    (T₀₂ : U₀ ≅ Z₂s) (T₀₁ : U₀ ≅ Z₁s) (T₁₂ : U₁ ≅ Z₂t) (T₁₀ : U₁ ≅ Z₀s) (T₂₀ : U₂ ≅ Z₀t)
    (T₂₁ : U₂ ≅ Z₁t)
    (hc : (T₀₂.hom ≫ a₂ ≫ T₁₂.inv) ≫ (T₁₀.hom ≫ a₀ ≫ T₂₀.inv) = T₀₁.hom ≫ a₁ ≫ T₂₁.inv) :
    c₁s.hom ≫ a₁ ≫ c₁t.inv =
      (c₁s.hom ≫ T₀₁.inv ≫ T₀₂.hom ≫ c₂s.inv) ≫ (c₂s.hom ≫ a₂ ≫ c₂t.inv) ≫
        (c₂t.hom ≫ T₁₂.inv ≫ T₁₀.hom ≫ c₀s.inv) ≫ (c₀s.hom ≫ a₀ ≫ c₀t.inv) ≫
        (c₀t.hom ≫ T₂₀.inv ≫ T₂₁.hom ≫ c₁t.inv) := by
  have hc' : a₁ = T₀₁.inv ≫ T₀₂.hom ≫ a₂ ≫ T₁₂.inv ≫ T₁₀.hom ≫ a₀ ≫ T₂₀.inv ≫ T₂₁.hom := by
    rw [← cancel_epi T₀₁.hom, ← cancel_mono T₂₁.inv]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
      hc.symm
  rw [hc']
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- A paste realizes to the comparison followed by the inverse triangle, through `ε`. -/
theorem hypercoverCocycle_realize_paste (R₀ : 𝒞₀ ⥤ 𝒜₀) (R₁ : 𝒞₁ ⥤ 𝒜₁) (R₂ : 𝒞₂ ⥤ 𝒜₂)
    (Lx : 𝒞₀ ⥤ 𝒞₁) (Lb : 𝒞₁ ⥤ 𝒞₂) (W : 𝒞₀ ⥤ 𝒞₂) (Qx : 𝒜₀ ⥤ 𝒜₁) (Qb : 𝒜₁ ⥤ 𝒜₂)
    (V : 𝒜₀ ⥤ 𝒜₂) (σx : Lx ⋙ R₁ ≅ R₀ ⋙ Qx) (σb : Lb ⋙ R₂ ≅ R₁ ⋙ Qb) (σv : W ⋙ R₂ ≅ R₀ ⋙ V)
    (T : V ≅ Qx ⋙ Qb) {K : 𝒞₀} {K₀ : 𝒜₀} (ε : R₀.obj K ≅ K₀)
    (P : Lb.obj (Lx.obj K) ⟶ W.obj K)
    (h : R₂.map P ≫ σv.hom.app K =
      σb.hom.app (Lx.obj K) ≫ Qb.map (σx.hom.app K) ≫ T.inv.app (R₀.obj K)) :
    R₂.map P ≫ σv.hom.app K ≫ V.map ε.hom =
      (σb.hom.app (Lx.obj K) ≫ Qb.map (σx.hom.app K) ≫ Qb.map (Qx.map ε.hom)) ≫ T.inv.app K₀ := by
  rw [reassoc_of% h]
  simp only [Category.assoc]
  exact congrArg (fun t ↦ σb.hom.app (Lx.obj K) ≫ Qb.map (σx.hom.app K) ≫ t)
    (T.inv.naturality ε.hom).symm

/-- Two pastes into the same vertex realize to the comparisons and the two triangles. -/
theorem hypercoverCocycle_realize_glue (R₀ : 𝒞₀ ⥤ 𝒜₀) (R₁ : 𝒞₁ ⥤ 𝒜₁) (R₂ : 𝒞₂ ⥤ 𝒜₂)
    (Lx Lx' : 𝒞₀ ⥤ 𝒞₁) (Lb Lb' : 𝒞₁ ⥤ 𝒞₂) (W : 𝒞₀ ⥤ 𝒞₂) (Qx Qx' : 𝒜₀ ⥤ 𝒜₁)
    (Qb Qb' : 𝒜₁ ⥤ 𝒜₂) (V : 𝒜₀ ⥤ 𝒜₂) (σx : Lx ⋙ R₁ ≅ R₀ ⋙ Qx) (σx' : Lx' ⋙ R₁ ≅ R₀ ⋙ Qx')
    (σb : Lb ⋙ R₂ ≅ R₁ ⋙ Qb) (σb' : Lb' ⋙ R₂ ≅ R₁ ⋙ Qb') (σv : W ⋙ R₂ ≅ R₀ ⋙ V)
    (T : V ≅ Qx ⋙ Qb) (T' : V ≅ Qx' ⋙ Qb') {K : 𝒞₀} {K₀ : 𝒜₀} (ε : R₀.obj K ≅ K₀)
    (P : Lb.obj (Lx.obj K) ≅ W.obj K) (P' : Lb'.obj (Lx'.obj K) ≅ W.obj K)
    (h : R₂.map P.hom ≫ σv.hom.app K =
      σb.hom.app (Lx.obj K) ≫ Qb.map (σx.hom.app K) ≫ T.inv.app (R₀.obj K))
    (h' : R₂.map P'.hom ≫ σv.hom.app K =
      σb'.hom.app (Lx'.obj K) ≫ Qb'.map (σx'.hom.app K) ≫ T'.inv.app (R₀.obj K)) :
    R₂.map (P'.hom ≫ P.inv) =
      (σb'.app (Lx'.obj K) ≪≫ Qb'.mapIso (σx'.app K) ≪≫ Qb'.mapIso (Qx'.mapIso ε)).hom ≫
        T'.inv.app K₀ ≫ T.hom.app K₀ ≫
        (σb.app (Lx.obj K) ≪≫ Qb.mapIso (σx.app K) ≪≫ Qb.mapIso (Qx.mapIso ε)).inv := by
  have e := hypercoverCocycle_realize_paste R₀ R₁ R₂ Lx Lb W Qx Qb V σx σb σv T ε P.hom h
  have e' := hypercoverCocycle_realize_paste R₀ R₁ R₂ Lx' Lb' W Qx' Qb' V σx' σb' σv T' ε P'.hom h'
  have eF : R₂.map P.hom = (σb.app (Lx.obj K) ≪≫ Qb.mapIso (σx.app K) ≪≫
      Qb.mapIso (Qx.mapIso ε)).hom ≫ T.inv.app K₀ ≫ (σv.app K ≪≫ V.mapIso ε).inv :=
    ((Iso.eq_comp_inv (σv.app K ≪≫ V.mapIso ε)).mpr e).trans (Category.assoc _ _ _)
  have eF' : R₂.map P'.hom = (σb'.app (Lx'.obj K) ≪≫ Qb'.mapIso (σx'.app K) ≪≫
      Qb'.mapIso (Qx'.mapIso ε)).hom ≫ T'.inv.app K₀ ≫ (σv.app K ≪≫ V.mapIso ε).inv :=
    ((Iso.eq_comp_inv (σv.app K ≪≫ V.mapIso ε)).mpr e').trans (Category.assoc _ _ _)
  have eI : R₂.map P.inv = (σv.app K ≪≫ V.mapIso ε).hom ≫ T.hom.app K₀ ≫
      (σb.app (Lx.obj K) ≪≫ Qb.mapIso (σx.app K) ≪≫ Qb.mapIso (Qx.mapIso ε)).inv := by
    rw [← cancel_epi (R₂.map P.hom), ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, eF]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Iso.inv_hom_id_app_assoc]
  rw [Functor.map_comp, eF', eI]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- A transition of a pair realizes to the gluing map, through the comparisons. -/
theorem hypercoverCocycle_realize_transition (R₀ : 𝒞₀ ⥤ 𝒜₀) (R₁ : 𝒞₁ ⥤ 𝒜₁) (R₂ : 𝒞₂ ⥤ 𝒜₂)
    (Ls Lt : 𝒞₀ ⥤ 𝒞₁) (Lb : 𝒞₁ ⥤ 𝒞₂) (Qs Qt : 𝒜₀ ⥤ 𝒜₁) (Qb : 𝒜₁ ⥤ 𝒜₂)
    (σs : Ls ⋙ R₁ ≅ R₀ ⋙ Qs) (σt : Lt ⋙ R₁ ≅ R₀ ⋙ Qt) (σb : Lb ⋙ R₂ ≅ R₁ ⋙ Qb)
    {K : 𝒞₀} {K₀ : 𝒜₀} (ε : R₀.obj K ≅ K₀) (α : Qs.obj K₀ ≅ Qt.obj K₀)
    (ι : Ls.obj K ≅ Lt.obj K)
    (hι : R₁.map ι.hom = σs.hom.app K ≫ Qs.map ε.hom ≫ α.hom ≫ Qt.map ε.inv ≫ σt.inv.app K) :
    R₂.map (Lb.map ι.hom) =
      (σb.app (Ls.obj K) ≪≫ Qb.mapIso (σs.app K) ≪≫ Qb.mapIso (Qs.mapIso ε)).hom ≫
        Qb.map α.hom ≫
          (σb.app (Lt.obj K) ≪≫ Qb.mapIso (σt.app K) ≪≫ Qb.mapIso (Qt.mapIso ε)).inv := by
  have n := σb.hom.naturality ι.hom
  simp only [Functor.comp_map] at n
  rw [← cancel_mono (σb.hom.app (Lt.obj K)), n, hι]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom,
    Iso.app_inv, Category.assoc, Functor.map_comp, Iso.inv_hom_id_app, Category.comp_id]

/-- **The cocycle condition of Stacks 0GMF transported along realizations.** If a realization
`R₂` is faithful, the transitions of a pair realize to `α` and the pastes of the three faces
realize to the pullback triangles of the vertices (the hypotheses of the shape of
`strictComponentDerivedTransitionIso_compOfEq`), then the cocycle condition of `α` gives that of
the pair. -/
theorem hypercoverCocycle_of_realize (R₀ : 𝒞₀ ⥤ 𝒜₀) (R₁ : 𝒞₁ ⥤ 𝒜₁) (R₂ : 𝒞₂ ⥤ 𝒜₂)
    [R₂.Faithful] (Ls Lt : 𝒞₀ ⥤ 𝒞₁) (L₀ L₁ L₂ : 𝒞₁ ⥤ 𝒞₂) (W₀ W₁ W₂ : 𝒞₀ ⥤ 𝒞₂)
    (Qs Qt : 𝒜₀ ⥤ 𝒜₁) (Q₀ Q₁ Q₂ : 𝒜₁ ⥤ 𝒜₂) (V₀ V₁ V₂ : 𝒜₀ ⥤ 𝒜₂)
    (σs : Ls ⋙ R₁ ≅ R₀ ⋙ Qs) (σt : Lt ⋙ R₁ ≅ R₀ ⋙ Qt) (σ₀ : L₀ ⋙ R₂ ≅ R₁ ⋙ Q₀)
    (σ₁ : L₁ ⋙ R₂ ≅ R₁ ⋙ Q₁) (σ₂ : L₂ ⋙ R₂ ≅ R₁ ⋙ Q₂) (σv₀ : W₀ ⋙ R₂ ≅ R₀ ⋙ V₀)
    (σv₁ : W₁ ⋙ R₂ ≅ R₀ ⋙ V₁) (σv₂ : W₂ ⋙ R₂ ≅ R₀ ⋙ V₂)
    (T₀₂ : V₀ ≅ Qs ⋙ Q₂) (T₀₁ : V₀ ≅ Qs ⋙ Q₁) (T₁₂ : V₁ ≅ Qt ⋙ Q₂) (T₁₀ : V₁ ≅ Qs ⋙ Q₀)
    (T₂₀ : V₂ ≅ Qt ⋙ Q₀) (T₂₁ : V₂ ≅ Qt ⋙ Q₁)
    {K : 𝒞₀} {K₀ : 𝒜₀} (ε : R₀.obj K ≅ K₀) (α : Qs.obj K₀ ≅ Qt.obj K₀) (ι : Ls.obj K ≅ Lt.obj K)
    (hι : R₁.map ι.hom = σs.hom.app K ≫ Qs.map ε.hom ≫ α.hom ≫ Qt.map ε.inv ≫ σt.inv.app K)
    (PA : L₂.obj (Ls.obj K) ≅ W₀.obj K) (PB : L₁.obj (Ls.obj K) ≅ W₀.obj K)
    (PC : L₂.obj (Lt.obj K) ≅ W₁.obj K) (PD : L₀.obj (Ls.obj K) ≅ W₁.obj K)
    (PE : L₀.obj (Lt.obj K) ≅ W₂.obj K) (PF : L₁.obj (Lt.obj K) ≅ W₂.obj K)
    (hA : R₂.map PA.hom ≫ σv₀.hom.app K =
      σ₂.hom.app (Ls.obj K) ≫ Q₂.map (σs.hom.app K) ≫ T₀₂.inv.app (R₀.obj K))
    (hB : R₂.map PB.hom ≫ σv₀.hom.app K =
      σ₁.hom.app (Ls.obj K) ≫ Q₁.map (σs.hom.app K) ≫ T₀₁.inv.app (R₀.obj K))
    (hC : R₂.map PC.hom ≫ σv₁.hom.app K =
      σ₂.hom.app (Lt.obj K) ≫ Q₂.map (σt.hom.app K) ≫ T₁₂.inv.app (R₀.obj K))
    (hD : R₂.map PD.hom ≫ σv₁.hom.app K =
      σ₀.hom.app (Ls.obj K) ≫ Q₀.map (σs.hom.app K) ≫ T₁₀.inv.app (R₀.obj K))
    (hE : R₂.map PE.hom ≫ σv₂.hom.app K =
      σ₀.hom.app (Lt.obj K) ≫ Q₀.map (σt.hom.app K) ≫ T₂₀.inv.app (R₀.obj K))
    (hF : R₂.map PF.hom ≫ σv₂.hom.app K =
      σ₁.hom.app (Lt.obj K) ≫ Q₁.map (σt.hom.app K) ≫ T₂₁.inv.app (R₀.obj K))
    (hc : (T₀₂.hom.app K₀ ≫ Q₂.map α.hom ≫ T₁₂.inv.app K₀) ≫
        (T₁₀.hom.app K₀ ≫ Q₀.map α.hom ≫ T₂₀.inv.app K₀) =
      T₀₁.hom.app K₀ ≫ Q₁.map α.hom ≫ T₂₁.inv.app K₀) :
    L₁.map ι.hom = (PA ≪≫ PB.symm).inv ≫ L₂.map ι.hom ≫ (PC ≪≫ PD.symm).hom ≫ L₀.map ι.hom ≫
      (PE ≪≫ PF.symm).hom := by
  apply R₂.map_injective
  have gL := hypercoverCocycle_realize_glue R₀ R₁ R₂ Ls Ls L₂ L₁ W₀ Qs Qs Q₂ Q₁ V₀ σs σs σ₂ σ₁ σv₀
    T₀₂ T₀₁ ε PA PB hA hB
  have gM := hypercoverCocycle_realize_glue R₀ R₁ R₂ Ls Lt L₀ L₂ W₁ Qs Qt Q₀ Q₂ V₁ σs σt σ₀ σ₂ σv₁
    T₁₀ T₁₂ ε PD PC hD hC
  have gR := hypercoverCocycle_realize_glue R₀ R₁ R₂ Lt Lt L₁ L₀ W₂ Qt Qt Q₁ Q₀ V₂ σt σt σ₁ σ₀ σv₂
    T₂₁ T₂₀ ε PF PE hF hE
  have t₀ := hypercoverCocycle_realize_transition R₀ R₁ R₂ Ls Lt L₀ Qs Qt Q₀ σs σt σ₀ ε α ι hι
  have t₁ := hypercoverCocycle_realize_transition R₀ R₁ R₂ Ls Lt L₁ Qs Qt Q₁ σs σt σ₁ ε α ι hι
  have t₂ := hypercoverCocycle_realize_transition R₀ R₁ R₂ Ls Lt L₂ Qs Qt Q₂ σs σt σ₂ ε α ι hι
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  refine t₁.trans ((hypercoverCocycle_core
    (σ₁.app (Ls.obj K) ≪≫ Q₁.mapIso (σs.app K) ≪≫ Q₁.mapIso (Qs.mapIso ε))
    (σ₁.app (Lt.obj K) ≪≫ Q₁.mapIso (σt.app K) ≪≫ Q₁.mapIso (Qt.mapIso ε))
    (σ₂.app (Ls.obj K) ≪≫ Q₂.mapIso (σs.app K) ≪≫ Q₂.mapIso (Qs.mapIso ε))
    (σ₂.app (Lt.obj K) ≪≫ Q₂.mapIso (σt.app K) ≪≫ Q₂.mapIso (Qt.mapIso ε))
    (σ₀.app (Ls.obj K) ≪≫ Q₀.mapIso (σs.app K) ≪≫ Q₀.mapIso (Qs.mapIso ε))
    (σ₀.app (Lt.obj K) ≪≫ Q₀.mapIso (σt.app K) ≪≫ Q₀.mapIso (Qt.mapIso ε))
    _ _ _ (T₀₂.app K₀) (T₀₁.app K₀) (T₁₂.app K₀) (T₁₀.app K₀) (T₂₀.app K₀) (T₂₁.app K₀)
    hc).trans ?_)
  exact congrArg₂ (· ≫ ·) gL.symm (congrArg₂ (· ≫ ·) t₂.symm (congrArg₂ (· ≫ ·) gM.symm
    (congrArg₂ (· ≫ ·) t₀.symm gR.symm)))

/-- The transition along `δ¹₀` of a pair realizes to the identity through the comparisons `ε₀`
and `ε₁`, with `ε₁` defined from the transition. -/
theorem hypercoverPair_realize_delta_zero (R₀ : 𝒞₀ ⥤ 𝒜₀) (R₁ : 𝒞₁ ⥤ 𝒜₁) (Lt : 𝒞₀ ⥤ 𝒞₁)
    (Qt : 𝒜₀ ⥤ 𝒜₁) (σt : Lt ⋙ R₁ ≅ R₀ ⋙ Qt) {O : 𝒞₀} {O₁ : 𝒞₁} {K₀ : 𝒜₀}
    (ε₀ : R₀.obj O ≅ K₀) (T : Lt.obj O ≅ O₁) :
    R₁.map T.hom = σt.hom.app O ≫ Qt.map ε₀.hom ≫
      (R₁.mapIso T.symm ≪≫ σt.app O ≪≫ Qt.mapIso ε₀).inv := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.app_inv, Category.assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app_assoc]

/-- The transition along `δ¹₁` of a pair realizes to `α` through the comparisons `ε₀` and `ε₁`. -/
theorem hypercoverPair_realize_delta_one (R₀ : 𝒞₀ ⥤ 𝒜₀) (R₁ : 𝒞₁ ⥤ 𝒜₁) (Ls Lt : 𝒞₀ ⥤ 𝒞₁)
    (Qs Qt : 𝒜₀ ⥤ 𝒜₁) (σs : Ls ⋙ R₁ ≅ R₀ ⋙ Qs) (σt : Lt ⋙ R₁ ≅ R₀ ⋙ Qt) {O K : 𝒞₀}
    {O₁ : 𝒞₁} {K₀ : 𝒜₀} (u : O ≅ K) (ε : R₀.obj K ≅ K₀) (α : Qs.obj K₀ ≅ Qt.obj K₀)
    (ι : Ls.obj K ≅ Lt.obj K)
    (hι : R₁.map ι.hom = σs.hom.app K ≫ Qs.map ε.hom ≫ α.hom ≫ Qt.map ε.inv ≫ σt.inv.app K)
    (T : Lt.obj O ≅ O₁) (Ts : Ls.obj O ⟶ O₁)
    (hT : Ts = Ls.map u.hom ≫ ι.hom ≫ Lt.map u.inv ≫ T.hom) :
    R₁.map Ts = σs.hom.app O ≫ Qs.map (R₀.mapIso u ≪≫ ε).hom ≫ α.hom ≫
      (R₁.mapIso T.symm ≪≫ σt.app O ≪≫ Qt.mapIso (R₀.mapIso u ≪≫ ε)).inv := by
  subst hT
  have n₁ := σs.hom.naturality u.hom
  have n₂ := σt.inv.naturality u.inv
  simp only [Functor.comp_map] at n₁ n₂
  simp only [Functor.map_comp, hι, Category.assoc]
  rw [reassoc_of% n₁, ← reassoc_of% n₂]
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_inv,
    Iso.app_inv, Functor.map_comp, Category.assoc]

end CocycleTransport

/-- The pullback triangle of the 0DLA interface at the tautological factorization is the
composition comparison. -/
theorem hypercoverPullTriangle_rfl_inv_app {𝒜 : Type*} [Category 𝒜] {D : 𝒜 → Type*}
    [∀ a, Category (D a)] (pull : ∀ {a b : 𝒜}, (a ⟶ b) → (D b ⥤ D a))
    (comp : ∀ {a b c : 𝒜} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {a b c : 𝒜} (f : a ⟶ b) (g : b ⟶ c) (M : D c) :
    (hypercoverPullTriangle pull comp (rfl : f ≫ g = f ≫ g)).inv.app M = (comp f g).inv.app M := by
  simp [hypercoverPullTriangle]

end CategoryTheory

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.CategoryTheory.Hypercovering
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedBaseChangeOfToposHom

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

/-- The square of derived pullbacks of the strict components is the square of derived pullbacks
of the 2-isomorphism `strictComponentTransitionTwoIso`. -/
theorem strictComponentDerivedTransitionIso_hom_app {m n : SimplexCategory} (φ : m ⟶ n)
    (Y : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) m).Modules) :
    (strictComponentDerivedTransitionIso X φ).hom.app Y =
      (derivedPullbackTwoIsoSquareIso (strictComponentRingedToposHom X n)
        (strictComponentRingedToposHom X m)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (spacesEtaleRingedToposHom (X.map φ.op)) (strictComponentTransitionTwoIso X φ)).hom.app Y :=
  (congrArg (· ≫ _) ((derivedPullback (strictComponentRingedToposHom X n)).map_id
    (((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) φ).obj Y))).trans
    (Category.id_comp _)

/-- The 2-isomorphism `k_{étale} ≅ g_{étale} ∘ f_{étale}` of Stacks 0DE7 read through an equality
`f ≫ g = k` of morphisms of algebraic spaces. -/
abbrev spacesEtaleCompTwoIsoOfEq {Y Y' Z : AlgebraicSpaces B S hS} (f : Y ⟶ Y') (g : Y' ⟶ Z)
    {k : Y ⟶ Z} (hk : f ≫ g = k) :
    RingedToposHom.TwoIso (A := spacesEtaleRingedTopos B S hS Y)
      (B := spacesEtaleRingedTopos B S hS Z) (spacesEtaleRingedToposHom k)
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS Y)
        (Y := spacesEtaleRingedTopos B S hS Y') (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f)) :=
  hk ▸ spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp f g

/-- `spacesEtaleCompTwoIsoOfEq` is the 2-isomorphism of the equality followed by that of Stacks
0DE7. -/
theorem spacesEtaleCompTwoIsoOfEq_eq {Y Y' Z : AlgebraicSpaces B S hS} (f : Y ⟶ Y') (g : Y' ⟶ Z)
    {k : Y ⟶ Z} (hk : f ≫ g = k) :
    spacesEtaleCompTwoIsoOfEq f g hk =
      (RingedToposHom.TwoIso.ofEq (congrArg spacesEtaleRingedToposHom hk.symm)).trans
        (spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp f g) := by
  subst hk
  apply RingedToposHom.TwoIso.ext
  exact (Iso.refl_trans _).symm

/-- Stacks 0D6D on the spaces-étale sites, `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*`, is the composition
isomorphism of derived pullbacks followed by the inverse of the derived pullback isomorphism of the
2-isomorphism `(f ≫ g)_{étale} ≅ g_{étale} ∘ f_{étale}`. -/
theorem spacesEtaleDerivedPullbackCompIso_hom_eq {Y Y' Z : AlgebraicSpaces B S hS} (f : Y ⟶ Y')
    (g : Y' ⟶ Z) :
    (spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp f g).hom =
      (derivedPullbackCompIso (spacesEtaleRingedToposHom f) (spacesEtaleRingedToposHom g)).hom ≫
        (derivedPullbackIsoOfTwoIso
          (spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp f g)).inv := by
  have := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS Y)
      (Y := spacesEtaleRingedTopos B S hS Y') (Z := spacesEtaleRingedTopos B S hS Z)
      (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f))
  exact congrArg (_ ≫ ·) ((congrArg (fun e ↦ (derivedPullbackIsoOfPullbackModulesIso
      (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS Y)
        (Y := spacesEtaleRingedTopos B S hS Y') (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f))
      (ψ := spacesEtaleRingedToposHom (f ≫ g)) e).hom)
    (RingedToposHom.TwoIso.pullbackModulesIso_symm_of_hasWeakSheafify
      (spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp f g)).symm).trans
    (congrArg Iso.hom (derivedPullbackIsoOfTwoIso_symm
      (spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp f g))))

/-- **The comparison `Lk^* ⟶ Lf^* Lg^*` of the 0DLA interface on the spaces-étale sites**, for
`f ≫ g = k`: the composition isomorphism of derived pullbacks followed by the derived pullback
isomorphism of `spacesEtaleCompTwoIsoOfEq`. -/
theorem hypercoverPullTriangle_inv_app_spacesEtale {Y Y' Z : AlgebraicSpaces B S hS} (f : Y ⟶ Y')
    (g : Y' ⟶ Z) {k : Y ⟶ Z} (hk : f ≫ g = k) (M : spacesEtaleDerivedModules B S hS Z) :
    (@hypercoverPullTriangle _ _ (spacesEtaleDerivedModules B S hS) (fun _ => inferInstance)
        (fun f => spacesEtaleDerivedPull B S hS f)
        (fun f g => spacesEtaleDerivedPullComp B S hS f g) _ _ _ _ _ _ hk).inv.app M =
      (derivedPullbackCompIso (spacesEtaleRingedToposHom f)
          (spacesEtaleRingedToposHom g)).hom.app M ≫
        (derivedPullbackIsoOfTwoIso (spacesEtaleCompTwoIsoOfEq f g hk)).inv.app M := by
  subst hk
  refine (hypercoverPullTriangle_rfl_inv_app _ _ f g M).trans
    ((congrArg (fun t ↦ t.app M) (spacesEtaleDerivedPullbackCompIso_hom_eq f g)).trans ?_)
  rfl

/-- The compositor of the derived transitions, realized: by
`derivedTransitionCompComparison_eq_twoIso` it is the composition isomorphism of derived pullbacks
followed by the 2-isomorphism of the transitions. -/
theorem strictComponentDerivedRealize_map_derivedModulePasteIso_hom {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (Y : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Modules) :
    (strictComponentDerivedRealize X n).map
      ((strictSituation X).derivedModulePasteIso (strictStructureSheaf X) ψ φ Y).hom =
      (derivedPullback (strictComponentRingedToposHom X n)).map
        ((derivedPullbackCompIso
            ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
            ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) ψ)).hom.app Y ≫
          (derivedPullbackIsoOfTwoIso ((strictSituation X).transitionRingedToposHomCompTwoIso
            (strictStructureSheaf X) ψ φ)).hom.app Y) :=
  congrArg (fun t ↦ (strictComponentDerivedRealize X n).map (t.app Y))
    (SimplicialSiteSituation.derivedTransitionCompComparison_eq_twoIso (strictSituation X)
      (strictStructureSheaf X) ψ φ)

/-- `derivedPullbackTwoIsoSquare_pasting` for the squares of the strict components. -/
theorem strictComponent_derivedPullbackTwoIsoSquare_pasting {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (hk : X.map φ.op ≫ X.map ψ.op = X.map (ψ ≫ φ).op)
    (Y : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Modules) :
    (derivedPullback (strictComponentRingedToposHom X n)).map
        ((derivedPullbackCompIso
            ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
            ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) ψ)).hom.app Y ≫
          (derivedPullbackIsoOfTwoIso ((strictSituation X).transitionRingedToposHomCompTwoIso
            (strictStructureSheaf X) ψ φ)).hom.app Y) ≫
      (derivedPullbackTwoIsoSquareIso (strictComponentRingedToposHom X n)
        (strictComponentRingedToposHom X l)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) (ψ ≫ φ))
        (spacesEtaleRingedToposHom (X.map (ψ ≫ φ).op))
        (strictComponentTransitionTwoIso X (ψ ≫ φ))).hom.app Y =
    (derivedPullbackTwoIsoSquareIso (strictComponentRingedToposHom X n)
        (strictComponentRingedToposHom X m)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (spacesEtaleRingedToposHom (X.map φ.op)) (strictComponentTransitionTwoIso X φ)).hom.app
        ((derivedPullback
          ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) ψ)).obj Y) ≫
      (derivedPullback (spacesEtaleRingedToposHom (X.map φ.op))).map
        ((derivedPullbackTwoIsoSquareIso (strictComponentRingedToposHom X m)
          (strictComponentRingedToposHom X l)
          ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) ψ)
          (spacesEtaleRingedToposHom (X.map ψ.op))
          (strictComponentTransitionTwoIso X ψ)).hom.app Y) ≫
      (derivedPullbackCompIso (spacesEtaleRingedToposHom (X.map φ.op))
          (spacesEtaleRingedToposHom (X.map ψ.op))).hom.app
        ((derivedPullback (strictComponentRingedToposHom X l)).obj Y) ≫
      (derivedPullbackIsoOfTwoIso (spacesEtaleCompTwoIsoOfEq (X.map φ.op) (X.map ψ.op) hk)).inv.app
        ((derivedPullback (strictComponentRingedToposHom X l)).obj Y) :=
  derivedPullbackTwoIsoSquare_pasting (strictComponentRingedToposHom X n)
    (strictComponentRingedToposHom X m) (strictComponentRingedToposHom X l)
    ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
    ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) ψ)
    ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) (ψ ≫ φ))
    (spacesEtaleRingedToposHom (X.map φ.op)) (spacesEtaleRingedToposHom (X.map ψ.op))
    (spacesEtaleRingedToposHom (X.map (ψ ≫ φ).op)) (strictComponentTransitionTwoIso X φ)
    (strictComponentTransitionTwoIso X ψ) (strictComponentTransitionTwoIso X (ψ ≫ φ))
    ((strictSituation X).transitionRingedToposHomCompTwoIso (strictStructureSheaf X) ψ φ)
    (spacesEtaleCompTwoIsoOfEq (X.map φ.op) (X.map ψ.op) hk)
    ((spacesEtaleCompTwoIsoOfEq_eq (X.map φ.op) (X.map ψ.op) hk).symm ▸
      strictComponentTransitionTwoIso_pasting X ψ φ hk) Y

/-- `strictComponentDerivedTransitionIso_hom_app` at a derived transition pullback, read with the
derived pullback along the transition morphism of ringed topoi. -/
theorem strictComponentDerivedTransitionIso_hom_app_derivedTransitionPullback
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (Y : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Modules) :
    (strictComponentDerivedTransitionIso X φ).hom.app
          (((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) ψ).obj Y) =
    (derivedPullbackTwoIsoSquareIso (strictComponentRingedToposHom X n)
        (strictComponentRingedToposHom X m)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
        (spacesEtaleRingedToposHom (X.map φ.op)) (strictComponentTransitionTwoIso X φ)).hom.app
        ((derivedPullback
          ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) ψ)).obj Y) :=
  strictComponentDerivedTransitionIso_hom_app X φ _

/-- **The realizations of the strict components are pseudonatural** (the input (C1) of Stacks
0GMF realized). -/
theorem strictComponentDerivedTransitionIso_comp_hypercoverPullTriangle {l m n : SimplexCategory}
    (ψ : l ⟶ m)
    (φ : m ⟶ n) (hk : X.map φ.op ≫ X.map ψ.op = X.map (ψ ≫ φ).op)
    (Y : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Modules) :
    (strictComponentDerivedRealize X n).map
        ((strictSituation X).derivedModulePasteIso (strictStructureSheaf X) ψ φ Y).hom ≫
        (strictComponentDerivedTransitionIso X (ψ ≫ φ)).hom.app Y =
      (strictComponentDerivedTransitionIso X φ).hom.app
          (((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) ψ).obj Y) ≫
        (spacesEtaleDerivedPull B S hS (X.map φ.op)).map
          ((strictComponentDerivedTransitionIso X ψ).hom.app Y) ≫
        (@hypercoverPullTriangle _ _ (spacesEtaleDerivedModules B S hS) (fun _ => inferInstance)
          (fun f => spacesEtaleDerivedPull B S hS f)
          (fun f g => spacesEtaleDerivedPullComp B S hS f g) _ _ _ _ _ _ hk).inv.app
          ((strictComponentDerivedRealize X l).obj Y) :=
  (congrArg₂ (· ≫ ·) (strictComponentDerivedRealize_map_derivedModulePasteIso_hom X ψ φ Y)
    (strictComponentDerivedTransitionIso_hom_app X (ψ ≫ φ) Y)).trans
    ((strictComponent_derivedPullbackTwoIsoSquare_pasting X ψ φ hk Y).trans
      (congrArg₂ (· ≫ ·)
        (strictComponentDerivedTransitionIso_hom_app_derivedTransitionPullback X ψ φ Y)
        (congrArg₂ (· ≫ ·) (congrArg (spacesEtaleDerivedPull B S hS (X.map φ.op)).map
          (strictComponentDerivedTransitionIso_hom_app X ψ Y))
          (hypercoverPullTriangle_inv_app_spacesEtale (X.map φ.op) (X.map ψ.op) hk
            ((strictComponentDerivedRealize X l).obj Y)))).symm)

/-- **The realizations of the strict components are pseudonatural, at a chosen factorization**:
the compositor `Lf_φ^* Lf_ψ^* ≅ Lf_θ^*` at `ψ ≫ φ = θ` realizes, through the squares
`strictComponentDerivedTransitionIso`, to the comparison `LX(θ)^* ⟶ LX(φ)^* LX(ψ)^*` of the 0DLA
interface at `X(φ) ≫ X(ψ) = X(θ)`. -/
theorem strictComponentDerivedTransitionIso_compOfEq {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (θ : l ⟶ n) (h : ψ ≫ φ = θ) (hk : X.map φ.op ≫ X.map ψ.op = X.map θ.op)
    (Y : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Modules) :
    (strictComponentDerivedRealize X n).map
        ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X) ψ φ θ h Y).hom ≫
        (strictComponentDerivedTransitionIso X θ).hom.app Y =
      (strictComponentDerivedTransitionIso X φ).hom.app
          (((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) ψ).obj Y) ≫
        (spacesEtaleDerivedPull B S hS (X.map φ.op)).map
          ((strictComponentDerivedTransitionIso X ψ).hom.app Y) ≫
        (@hypercoverPullTriangle _ _ (spacesEtaleDerivedModules B S hS) (fun _ => inferInstance)
          (fun f => spacesEtaleDerivedPull B S hS f)
          (fun f g => spacesEtaleDerivedPullComp B S hS f g) _ _ _ _ _ _ hk).inv.app
          ((strictComponentDerivedRealize X l).obj Y) := by
  subst h
  rw [SimplicialSiteSituation.derivedModulePasteIsoOfEq_rfl]
  exact
  (congrArg₂ (· ≫ ·) (strictComponentDerivedRealize_map_derivedModulePasteIso_hom X ψ φ Y)
    (strictComponentDerivedTransitionIso_hom_app X (ψ ≫ φ) Y)).trans
    ((strictComponent_derivedPullbackTwoIsoSquare_pasting X ψ φ hk Y).trans
      (congrArg₂ (· ≫ ·)
        (strictComponentDerivedTransitionIso_hom_app_derivedTransitionPullback X ψ φ Y)
        (congrArg₂ (· ≫ ·) (congrArg (spacesEtaleDerivedPull B S hS (X.map φ.op)).map
          (strictComponentDerivedTransitionIso_hom_app X ψ Y))
          (hypercoverPullTriangle_inv_app_spacesEtale (X.map φ.op) (X.map ψ.op) hk
            ((strictComponentDerivedRealize X l).obj Y)))).symm)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
