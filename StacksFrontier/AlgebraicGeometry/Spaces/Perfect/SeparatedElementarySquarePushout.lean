module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquareGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SeparatedFromElementarySquare
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal

/-!
# Separatedness across a cartesian elementary distinguished square

Let `(U_w ⊆ W, f : N ⟶ W)` be an elementary distinguished square of algebraic spaces such that
the square `U₁ = U_w ×_W N` is cartesian, with `f' : U₁ ⟶ U ≅ U_w` étale; this is the shape of
the pushout `W = U ⊔_{U₁} N` of Stacks 0DVJ. A morphism `g : W ⟶ Y` which is separated on `U`
and on `N` is separated as soon as the graph `U₁ ⟶ U ×_Y N` is closed and the image in
`N ×_Y N` of `U₁ ×_U U₁` off its diagonal is closed.

This is the form of the corrected Stacks 0F45 used in the repaired proof of Stacks 0F4B: there
the second condition is the condition `(H)` on the off-diagonal part of `U₁ ×_U U₁`, which
fails for the space `X₁ ∖ (Z̄₁₂ ∪ T̄)` of the source and holds after the blowups of the repair.

## Main results

* `AlgebraicGeometry.Space.mem_range_diagonal_or_mem_range_pullbackMap`: the points of
  `N ×_W N` lie on the diagonal or come from `U₁ ×_U U₁`.
* `AlgebraicGeometry.Space.isSeparated_of_isPullback_of_isClosedMap_offDiagonal`: the
  separatedness criterion.

## References

* [Stacks Project, Tag 0F45](https://stacks.math.columbia.edu/tag/0F45)
* [Stacks Project, Tag 0DVJ](https://stacks.math.columbia.edu/tag/0DVJ)
* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
instance hasPullbacks_presheaf_SeparatedElementarySquarePushout :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

instance (priority := high) hasPullback_presheaf_SeparatedElementarySquarePushout
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section Points

variable {W N U U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
  {Uw : Subfunctor W} {fW : N ⟶ W} (hsq : IsElementaryDistinguishedSquare B S hS hW Uw fW)
  {j : U₁ ⟶ N} {f' : U₁ ⟶ U} {e : U ⟶ Uw.toFunctor} [IsIso e] (hpb : IsPullback j f' fW (e ≫ Uw.ι))

include hsq hpb in
/-- **The points of `N ×_W N` for a cartesian elementary distinguished square.** Let
`(U_w ⊆ W, f : N ⟶ W)` be an elementary distinguished square whose restriction over `U_w` is
`U₁ ⟶ U ≅ U_w`. Then every point of `N ×_W N` lies on the diagonal or comes from `U₁ ×_U U₁`:
over the complement of `U_w` the morphism `f` is an isomorphism, so two sections of `N` with the
same image there agree. -/
theorem mem_range_diagonal_or_mem_range_pullbackMap (k : points B S hS (pullback fW fW)) :
    k ∈ Set.range (pointsMap B S hS N (pullback.diagonal fW)) ∨
      k ∈ Set.range (pointsMap B S hS (pullback f' f')
        (pullback.map f' f' fW fW j j (e ≫ Uw.ι) hpb.w.symm hpb.w.symm)) := by
  classical
  obtain ⟨p, rfl⟩ := Quot.exists_rep k
  obtain ⟨c, cont, tb, v⟩ := p
  let T : BigFppfOver B S hS := Over.mk (⟨tb⟩ : B.obj cont ⟶ B.obj hS)
  set m : yoneda.obj T ⟶ pullback fW fW := yonedaEquiv.symm v with hm
  set a := m ≫ pullback.fst fW fW
  set b := m ≫ pullback.snd fW fW
  have hab : a ≫ fW = b ≫ fW := by simp only [a, b, Category.assoc, pullback.condition]
  have hcl : ∀ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (φ : F ⟶ pullback fW fW)
      (μ : yoneda.obj T ⟶ F), μ ≫ φ = m →
      pointsMap B S hS F φ
        ((⟨c, cont, tb, yonedaEquiv μ⟩ : FieldValuedPoint B S hS F).class B S hS F) =
        Quot.mk _ (⟨c, cont, tb, v⟩ : FieldValuedPoint B S hS (pullback fW fW)) := by
    intro F φ μ hμ
    rw [pointsMap_class]
    congr 1
    change (⟨c, cont, tb, φ.app _ (yonedaEquiv μ)⟩ : FieldValuedPoint B S hS _) = _
    rw [← yonedaEquiv_comp, hμ, hm, Equiv.apply_symm_apply]
  by_cases h : yonedaEquiv (a ≫ fW) ∈ Uw.obj (op T)
  · right
    let x' : yoneda.obj T ⟶ Uw.toFunctor := yonedaEquiv.symm ⟨yonedaEquiv (a ≫ fW), h⟩
    have hx' : x' ≫ Uw.ι = a ≫ fW := by
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp]
      have e1 := (yonedaEquiv (X := T) (F := Uw.toFunctor)).apply_symm_apply
        ⟨yonedaEquiv (a ≫ fW), h⟩
      change (yonedaEquiv x').1 = _
      rw [e1]
    have hx'' : (x' ≫ inv e) ≫ (e ≫ Uw.ι) = a ≫ fW := by
      rw [Category.assoc, IsIso.inv_hom_id_assoc, hx']
    let a₁ := hpb.lift a (x' ≫ inv e) hx''.symm
    let b₁ := hpb.lift b (x' ≫ inv e) (hab ▸ hx''.symm)
    have hab₁ : a₁ ≫ f' = b₁ ≫ f' := by rw [hpb.lift_snd, hpb.lift_snd]
    refine ⟨_, hcl _ (pullback.lift a₁ b₁ hab₁) ?_⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, a₁, hpb.lift_fst, a]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, b₁, hpb.lift_fst, b]
  · left
    have hnot : (⟨c, cont, tb, yonedaEquiv (a ≫ fW)⟩ : FieldValuedPoint B S hS W).class B S hS W ∉
        Set.range (pointsMap B S hS Uw.toFunctor Uw.ι) := fun hm' =>
      h ((FieldValuedPoint.mem_obj_iff_class_mem_range B S hS hW Uw hsq.isOpenSubspace _).2 hm')
    have hmem := (FieldValuedPoint.mem_obj_reducedClosedSubspace_iff_class_mem B S hS hW
      (Set.range (pointsMap B S hS Uw.toFunctor Uw.ι))ᶜ hsq.isClosedComplement
      ⟨c, cont, tb, yonedaEquiv (a ≫ fW)⟩).2 hnot
    have := hsq.isIsoOverComplement
    have hbij : Function.Bijective ((Subfunctor.fromPreimage (reducedClosedSubspace B S hS W hW
        (Set.range (pointsMap B S hS Uw.toFunctor Uw.ι))ᶜ hsq.isClosedComplement) fW).app
          (op T)) :=
      (isIso_iff_bijective _).1 inferInstance
    have ha : fW.app (op T) (yonedaEquiv a) = yonedaEquiv (a ≫ fW) := (yonedaEquiv_comp a fW).symm
    have hb : fW.app (op T) (yonedaEquiv b) = yonedaEquiv (a ≫ fW) := by
      rw [hab]; exact (yonedaEquiv_comp b fW).symm
    have hyab : yonedaEquiv a = yonedaEquiv b := by
      have := @hbij.1 ⟨yonedaEquiv a, show fW.app (op T) (yonedaEquiv a) ∈ _ from ha ▸ hmem⟩
        ⟨yonedaEquiv b, show fW.app (op T) (yonedaEquiv b) ∈ _ from hb ▸ hmem⟩
        (Subtype.ext (ha.trans hb.symm))
      exact congrArg Subtype.val this
    have hab' : a = b := yonedaEquiv.injective hyab
    refine ⟨_, hcl _ a ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hab']

end Points

section Separated

attribute [local instance] pointTopology

/-- A closed map on points composed with a homeomorphism-inducing isomorphism on either side is
closed. -/
private theorem isClosedMap_pointsMap_iso_comp_comp {F F' G G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ F') [IsIso a] (φ : F' ⟶ G') (b : G' ⟶ G) [IsIso b]
    (hφ : IsClosedMap (pointsMap B S hS F' φ)) :
    IsClosedMap (pointsMap B S hS F (a ≫ φ ≫ b)) := by
  rw [pointsMap_comp, pointsMap_comp]
  exact (isClosedMap_pointsMap_of_isIso B S hS b).comp
    (hφ.comp (isClosedMap_pointsMap_of_isIso B S hS a))

/-- **Separatedness across a cartesian elementary distinguished square.** Let
`(U_w ⊆ W, f : N ⟶ W)` be an elementary distinguished square of algebraic spaces whose
restriction over `U_w` is an étale morphism `f' : U₁ ⟶ U`, through an isomorphism `U ≅ U_w`, by
a cartesian square. Let `g : W ⟶ Y` restrict to separated morphisms `q_U` on `U` and `q_N` on
`N`. Suppose that the graph `U₁ ⟶ U ×_Y N` is a closed map on points, and that
`U₁ ×_U U₁ ⟶ N ×_Y N` carries the closed sets of points off the diagonal of `U₁ ×_U U₁` to
closed sets. Then `g` is separated.

This is the corrected Stacks 0F45 once `N ×_W N` is identified: by
`AlgebraicGeometry.Space.mem_range_diagonal_or_mem_range_pullbackMap` its points are those of
the diagonal of `N` and those coming from `U₁ ×_U U₁`, so the image of a closed set of
`N ×_W N` in `N ×_Y N` is the union of its part on the diagonal, closed because `q_N` is
separated, and its part off the diagonal of `U₁ ×_U U₁`, closed by hypothesis. -/
theorem isSeparated_of_isPullback_of_isClosedMap_offDiagonal
    {Y W N U U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hW : IsAlgebraicSpace B S hS W) (hN : IsAlgebraicSpace B S hS N)
    (hU₁ : IsAlgebraicSpace B S hS U₁) (hU : IsAlgebraicSpace B S hS U)
    {Uw : Subfunctor W} {fW : N ⟶ W} (hsq : IsElementaryDistinguishedSquare B S hS hW Uw fW)
    {j : U₁ ⟶ N} {f' : U₁ ⟶ U} {e : U ⟶ Uw.toFunctor} [IsIso e]
    (hpb : IsPullback j f' fW (e ≫ Uw.ι)) (hf' : IsEtale B S hS f')
    (g : W ⟶ Y) {qU : U ⟶ Y} {qN : N ⟶ Y} (hgU : e ≫ Uw.ι ≫ g = qU) (hgN : fW ≫ g = qN)
    (hqU : IsSeparated B S hS qU) (hqN : IsSeparated B S hS qN) (hcomm : f' ≫ qU = j ≫ qN)
    (hUV : IsClosedMorphism B S hS (pullback.lift f' j hcomm : U₁ ⟶ pullback qU qN))
    (hO : ∀ K : Set (points B S hS (pullback f' f')), IsClosed K →
      Disjoint K (Set.range (pointsMap B S hS U₁ (pullback.diagonal f'))) →
      IsClosed (pointsMap B S hS _ (pullback.map f' f' qN qN j j qU hcomm hcomm) '' K)) :
    IsSeparated B S hS g := by
  subst hgU hgN
  refine isSeparated_of_elementaryDistinguishedSquare B S hS hW hY g Uw fW hsq ?_ hqN ?_ ?_
  · rw [show Uw.ι ≫ g = inv e ≫ (e ≫ Uw.ι ≫ g) by simp]
    exact isSeparated_comp B S hS _ _ (isSeparated_of_isIso B S hS _) hqU
  · -- `U_w ×_W N` is `U₁`
    have hpb' : IsPullback (f' ≫ e) j Uw.ι fW :=
      hpb.flip.of_iso (Iso.refl _) (asIso e) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
        (by simp) (by simp)
    let π := pullback.map (e ≫ Uw.ι ≫ g) (fW ≫ g) (Uw.ι ≫ g) (fW ≫ g) e (𝟙 N) (𝟙 Y)
      (by simp) (by simp)
    have : IsIso π := by
      refine ⟨⟨pullback.map (Uw.ι ≫ g) (fW ≫ g) (e ≫ Uw.ι ≫ g) (fW ≫ g) (inv e) (𝟙 N) (𝟙 Y)
        (by simp) (by simp), ?_, ?_⟩⟩ <;> apply pullback.hom_ext <;> simp [π]
    have heq : pullback.mapDesc Uw.ι fW g =
        hpb'.isoPullback.inv ≫ pullback.lift f' j hcomm ≫ π := by
      rw [Iso.eq_inv_comp]
      apply pullback.hom_ext
      · simp only [π, pullback.mapDesc, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
          IsPullback.isoPullback_hom_fst, Category.comp_id]
      · simp only [π, pullback.mapDesc, Category.assoc, pullback.lift_snd,
          IsPullback.isoPullback_hom_snd, Category.comp_id]
    rw [IsClosedMorphism, heq]
    exact isClosedMap_pointsMap_iso_comp_comp _ _ _ hUV
  · intro K hK
    have hY₂ : IsAlgebraicSpace B S hS (pullback (fW ≫ g) (fW ≫ g)) :=
      isAlgebraicSpace_pullback B S hS _ _ hN hN hY
    let ρ := pullback.map f' f' fW fW j j (e ≫ Uw.ι) hpb.w.symm hpb.w.symm
    let ι := pullback.map f' f' (fW ≫ g) (fW ≫ g) j j (e ≫ Uw.ι ≫ g) hcomm hcomm
    have h1 : pullback.diagonal fW ≫ pullback.mapDesc fW fW g = pullback.diagonal (fW ≫ g) := by
      apply pullback.hom_ext <;> simp [pullback.mapDesc]
    have h2 : ρ ≫ pullback.mapDesc fW fW g = ι := by
      apply pullback.hom_ext <;> simp [ρ, ι, pullback.mapDesc]
    have h3 : pullback.diagonal f' ≫ ρ = j ≫ pullback.diagonal fW := by
      apply pullback.hom_ext <;> simp [ρ]
    have hopen : IsOpen (Set.range (pointsMap B S hS U₁ (pullback.diagonal f'))) := by
      simpa using isOpenMap_pointsMap_of_isOpenImmersion B S hS _
        (isOpenImmersion_diagonal_of_isUnramified B S hS hU₁ hU f'
          (isUnramified_of_isEtale B S hS hf')) _ isOpen_univ
    let A := pointsMap B S hS N (pullback.diagonal fW) ⁻¹' K
    let Bs := pointsMap B S hS _ ρ ⁻¹' K ∩
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal f')))ᶜ
    have himage : pointsMap B S hS _ (pullback.mapDesc fW fW g) '' K =
        pointsMap B S hS N (pullback.diagonal (fW ≫ g)) '' A ∪ pointsMap B S hS _ ι '' Bs := by
      ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        rcases mem_range_diagonal_or_mem_range_pullbackMap hW hsq hpb k with ⟨n, rfl⟩ | ⟨r, rfl⟩
        · exact Or.inl ⟨n, hk, by rw [← h1, pointsMap_comp_apply]⟩
        · by_cases hr : r ∈ Set.range (pointsMap B S hS U₁ (pullback.diagonal f'))
          · obtain ⟨u, rfl⟩ := hr
            have hk' : pointsMap B S hS _ ρ (pointsMap B S hS _ (pullback.diagonal f') u) =
                pointsMap B S hS _ (pullback.diagonal fW) (pointsMap B S hS _ j u) := by
              rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, h3]
            refine Or.inl ⟨pointsMap B S hS U₁ j u, ?_, ?_⟩
            · change pointsMap B S hS _ (pullback.diagonal fW) (pointsMap B S hS _ j u) ∈ K
              rwa [← hk']
            · rw [hk', ← h1, pointsMap_comp_apply]
          · exact Or.inr ⟨r, ⟨hk, hr⟩, by rw [← h2, pointsMap_comp_apply]⟩
      · rintro (⟨n, hn, rfl⟩ | ⟨r, ⟨hr, -⟩, rfl⟩)
        · exact ⟨_, hn, by rw [← h1, pointsMap_comp_apply]⟩
        · exact ⟨_, hr, by rw [← h2, pointsMap_comp_apply]⟩
    rw [himage]
    exact (isClosedMorphism_of_isClosedImmersion B S hS hN hY₂ _ hqN _
        (hK.preimage (continuous_pointsMap B S hS _))).union
      (hO Bs ((hK.preimage (continuous_pointsMap B S hS _)).inter hopen.isClosed_compl)
        (Set.disjoint_left.2 fun _ h h' => h.2 h'))

end Separated

end AlgebraicGeometry.Space

end
