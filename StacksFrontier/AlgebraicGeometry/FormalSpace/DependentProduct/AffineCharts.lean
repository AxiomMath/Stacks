module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AlgebraicSpaceDiagonalCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.ChartBound

/-!
# Affine étale charts of an algebraic space, and of a relative product over a sheaf with
representable diagonal

Let `S` be a scheme contained in a big fppf site `B`.

* The relative product `h_a ×_Z h_b` of two points of an fppf sheaf `Z` whose diagonal is
  representable by algebraic spaces is an algebraic space (Stacks 03XY applied to the diagonal).
* An algebraic space `G` admits a family of affine étale charts `h_{W_i} ⟶ G`, each representable
  by objects of the site and étale, which cover `G` pointwise: after base change along any point
  `h_T ⟶ G`, the representing objects of the charts are jointly surjective onto `T`. They are the
  affine opens of an étale atlas (Stacks 03FX).

## Main results

* `isAlgebraicSpaceULift_pullback_of_representableDiagonal`: the relative product of two points
  of a sheaf with representable diagonal is an algebraic space.
* `exists_affine_etale_charts`: an algebraic space has a pointwise covering family of affine
  étale charts.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03XY](https://stacks.math.columbia.edu/tag/03XY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The relative product of two points of a sheaf whose diagonal is representable by
algebraic spaces is an algebraic space.** It is a base change of the diagonal along a morphism
out of the representable presheaf of a product of the site (Stacks 03XY). -/
theorem isAlgebraicSpaceULift_pullback_of_representableDiagonal {Z : FppfSheaf B S hS}
    (hZ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (diag Z.obj))
    {a b : BigFppfOver B S hS}
    (g : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj a ⟶ Z)
    (h : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj b ⟶ Z) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback g h).obj := by
  let : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  let J := BigFppfOver.topology B S hS
  let K := sheafToPresheaf J (Type (u + 1))
  let ξa : uliftYoneda.{u + 1}.obj a ⟶ Z.obj := g.hom
  let ξb : uliftYoneda.{u + 1}.obj b ⟶ Z.obj := h.hom
  have hprod : Space.IsAlgebraicSpaceULift.{u + 1} B S hS
      (uliftYoneda.{u + 1}.obj a ⨯ uliftYoneda.{u + 1}.obj b) :=
    Space.isAlgebraicSpaceULift_of_iso B S hS
      (PreservesLimitPair.iso uliftYoneda.{u + 1} a b)
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS (a ⨯ b))
  have hdsq : IsPullback (pullback.fst ξa ξb ≫ ξa)
      (prod.lift (pullback.fst ξa ξb) (pullback.snd ξa ξb)) (diag Z.obj)
      (prod.map ξa ξb) :=
    Stacks.Spaces.isPullback_diag_prodMap (IsPullback.of_hasPullback ξa ξb)
  have halg1 : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξa ξb) :=
    Space.isAlgebraicSpaceULift_of_iso B S hS hdsq.flip.isoPullback.symm
      (Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS
        (diag Z.obj) (prod.map ξa ξb) hZ hprod)
  have hKsq : IsPullback (K.map (pullback.fst g h)) (K.map (pullback.snd g h)) ξa ξb :=
    (IsPullback.of_hasPullback g h).map K
  exact Space.isAlgebraicSpaceULift_of_iso B S hS hKsq.isoPullback.symm halg1

/-- **An algebraic space has a family of affine étale charts covering it pointwise.** -/
theorem exists_affine_etale_charts {G : FppfSheaf B S hS}
    (hG : Space.IsAlgebraicSpaceULift.{u + 1} B S hS G.obj) :
    ∃ (ι : Type u) (W : ι → BigFppfOver B S hS)
      (c : ∀ i, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (W i) ⟶ G),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (W i))) ∧
      (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1} (c i).hom) ∧
      ∀ (T : BigFppfOver B S hS)
        (x : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T ⟶ G)
        (t : (BigFppfOver.toScheme B S hS).obj T),
        ∃ (i : ι) (L₀ : BigFppfOver B S hS) (q₀ : L₀ ⟶ T)
          (r₀ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj L₀ ⟶
            (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj (W i)),
          IsPullback ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map q₀) r₀ x (c i) ∧
          t ∈ Set.range ((BigFppfOver.toScheme B S hS).map q₀) := by
  classical
  set F := BigFppfOver.toScheme B S hS with hF
  set J := BigFppfOver.topology B S hS with hJ
  obtain ⟨U, f, hfS, hfE⟩ := hG.exists_atlas
  set Uc : Scheme.{u} := F.obj U with hUc
  let hU (i : Uc.affineOpens) : B.Contains (i.1 : Scheme.{u}) :=
    Scheme.size_lt_of_isOpenImmersion i.1.ι U.left.property
  let fO (i : Uc.affineOpens) : B.obj (hU i) ⟶ U.left :=
    B.inclusion.preimage
      (show B.inclusion.obj (B.obj (hU i)) ⟶ B.inclusion.obj U.left from i.1.ι)
  let W (i : Uc.affineOpens) : BigFppfOver B S hS := Over.mk (fO i ≫ U.hom)
  let gW (i : Uc.affineOpens) : W i ⟶ U := Over.homMk (fO i) rfl
  have hgW (i : Uc.affineOpens) : F.map (gW i) = i.1.ι := B.inclusion.map_preimage _
  have hgWopen (i : Uc.affineOpens) : IsOpenImmersion (F.map (gW i)) := by
    rw [hgW i]; infer_instance
  let c (i : Uc.affineOpens) : J.uliftYoneda.{u + 1}.obj (W i) ⟶ G :=
    ⟨uliftYoneda.{u + 1}.map (gW i) ≫ f⟩
  have := Space.inverseImage_isStableUnderBaseChange B S hS
    (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@Etale.{u} : MorphismProperty Scheme.{u}))
  have hEc (i : Uc.affineOpens) : (MorphismProperty.inverseImage (@Etale.{u} :
      MorphismProperty Scheme.{u}) F).relative uliftYoneda.{u + 1} (c i).hom := by
    have h1 := Space.relative_uliftYoneda_map B S hS (@Etale.{u}) (gW i)
      (by have := hgWopen i; infer_instance)
    have : ((MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        F).relative (uliftYoneda.{u + 1} (C := BigFppfOver B S hS))).IsStableUnderComposition :=
      MorphismProperty.relative_isStableUnderComposition _
    exact MorphismProperty.comp_mem _ _ _ h1 hfE
  refine ⟨Uc.affineOpens, W, c, fun i ↦ i.2, hEc, ?_⟩
  intro T x t
  have := hasPullbacks_bigFppfOver B S hS
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  -- the base change of the atlas along `x`
  set P := hfE.1.pullback x.hom
  set p₁ : P ⟶ T := hfE.1.snd x.hom
  set p₂ := hfE.1.fst x.hom
  have hP : IsPullback p₂ (uliftYoneda.{u + 1}.map p₁) f x.hom := hfE.1.isPullback x.hom
  set fst' : P ⟶ U := (uliftYoneda.{u + 1}).preimage p₂
  have hfst' : uliftYoneda.{u + 1}.map fst' = p₂ := (uliftYoneda.{u + 1}).map_preimage p₂
  have hsurj : Surjective (F.map p₁) := hfS.2 x.hom p₂ p₁ hP
  obtain ⟨w, hw⟩ := hsurj.surj t
  -- the affine open of the atlas containing the image of `w`
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_affineOpens_eq_top Uc).ge (Set.mem_univ (F.map fst' w)))
  set L₀ := pullback fst' (gW i)
  refine ⟨i, L₀, pullback.fst fst' (gW i) ≫ p₁,
    J.uliftYoneda.{u + 1}.map (pullback.snd fst' (gW i)), ?_, ?_⟩
  · have hA : IsPullback (J.uliftYoneda.{u + 1}.map (pullback.snd fst' (gW i)))
        (J.uliftYoneda.{u + 1}.map (pullback.fst fst' (gW i)))
        (J.uliftYoneda.{u + 1}.map (gW i)) (J.uliftYoneda.{u + 1}.map fst') :=
      ((IsPullback.of_hasPullback fst' (gW i)).map J.uliftYoneda.{u + 1}).flip
    have hBpre : IsPullback (uliftYoneda.{u + 1}.map fst') (uliftYoneda.{u + 1}.map p₁)
        f x.hom := by rw [hfst']; exact hP
    have hB : IsPullback (J.uliftYoneda.{u + 1}.map fst') (J.uliftYoneda.{u + 1}.map p₁)
        (⟨f⟩ : J.uliftYoneda.{u + 1}.obj U ⟶ G) x :=
      IsPullback.of_map_of_faithful (sheafToPresheaf J (Type (u + 1))) hBpre
    have hpaste := (hA.paste_vert hB).flip
    rw [← Functor.map_comp] at hpaste
    exact hpaste
  · -- a point of the fibre product over `w` and over a point of the affine open
    obtain ⟨y', hy'⟩ : F.map fst' w ∈ Set.range (F.map (gW i)) := by
      rw [hgW i]; exact ⟨⟨_, hi⟩, rfl⟩
    obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback w y' hy'.symm
    set e := PreservesPullback.iso F fst' (gW i)
    refine ⟨e.inv z, ?_⟩
    have h1 : e.inv ≫ F.map (pullback.fst fst' (gW i)) = pullback.fst (F.map fst') (F.map (gW i)) :=
      PreservesPullback.iso_inv_fst F fst' (gW i)
    have h2 : F.map (pullback.fst fst' (gW i)) (e.inv z) = w := by
      rw [← Scheme.Hom.comp_apply, h1, hz₁]
    rw [F.map_comp, Scheme.Hom.comp_apply, h2, hw]

end AlgebraicGeometry.FormalSpace.DependentProduct

end
