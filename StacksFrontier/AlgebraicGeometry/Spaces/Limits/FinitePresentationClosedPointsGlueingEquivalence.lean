module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedPointsGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationGlueingAlongMono
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationLocalSchemeGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation

/-!
# Glueing algebraic spaces of finite presentation at finitely many closed points (Stacks 0E92)

Let `S` be a scheme of a big fppf site and let `s₁, …, sₙ` be pairwise distinct closed points of
`S` whose open complement `U = S ∖ {s₁, …, sₙ}` has quasi-compact inclusion. With
`Sᵢ = Spec 𝒪_{S,sᵢ}` and `Uᵢ = Sᵢ ∖ {sᵢ}`, the comparison functor
`FP_S ⥤ FP_U ×_{FP_{U₁} × ⋯ × FP_{Uₙ}} (FP_{S₁} × ⋯ × FP_{Sₙ})`
is an equivalence of categories, where `FP_T` is the category of algebraic spaces of finite
presentation over `T`.

The comparison functor is
`AlgebraicGeometry.FinitePresentationSpacesOver.ClosedPointsGlueingData.comparisonFunctor` of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedPointsGlueing`, applied to
the glueing data `AlgebraicGeometry.FinitePresentationSpacesOver.closedPointsGlueingData` built
from `S`, the points, `U`, the local schemes `Spec 𝒪_{S,sᵢ}` and their punctures.

The proof is the induction of Stacks 0E92. The last point `sₙ` is split off over the intermediate
base `S ∖ {s₁, …, s_{n-1}}` by the case of one point, Stacks 0E90, which is available over that
non-terminal base by
`AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_of_mono`: the base is
a quasi-compact open of `S`, and Stacks 0E90 at `sₙ` over `S` itself extends to it. The remaining
points are handled by the induction hypothesis, with the intermediate base as the open part.
Essential surjectivity is
`AlgebraicGeometry.FinitePresentationSpacesOver.ClosedPointsGlueingData.essSurj_comparisonFunctor`;
faithfulness and fullness are proved here by the same splitting.

## Main results

* `FinitePresentationSpacesOver.ClosedPointsGlueingData.faithful_comparisonFunctor_peel`
  and `FinitePresentationSpacesOver.ClosedPointsGlueingData.full_comparisonFunctor_peel`:
  faithfulness and fullness pass along a splitting.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_comparisonFunctor_closedPoints`:
  **Stacks 0E92.**

## References

* [Stacks Project, Tag 0E92](https://stacks.math.columbia.edu/tag/0E92)
* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FinitePresentationSpacesOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace ClosedPointsGlueingData

variable {B S hS}

/-- If `F.map h` is the conjugate by an isomorphism `e : G ≅ F` of `a`, then `G.map h = a`. -/
private theorem map_eq_of_map_eq_inv_comp_comp {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : G ≅ F) {Y Y' : C} (h : Y ⟶ Y') (a : G.obj Y ⟶ G.obj Y')
    (H : F.map h = e.inv.app Y ≫ a ≫ e.hom.app Y') : G.map h = a := by
  rw [← cancel_mono (e.hom.app Y'), e.hom.naturality h, H, Iso.hom_inv_id_app_assoc]

/-- **Faithfulness passes along a splitting.** If the comparison functor of Stacks 0E90 at the
split-off point and the comparison functor of the remaining points are faithful, so is the
comparison functor of all the points. -/
theorem faithful_comparisonFunctor_peel {n : ℕ} {D : ClosedPointsGlueingData B S hS (n + 1)}
    (p : D.Peel) (hlast : p.lastFunctor.Faithful) (htail : p.tail.comparisonFunctor.Faithful) :
    D.comparisonFunctor.Faithful where
  map_injective {Y Y'} {f g} h := by
    have hU : (baseChange B S hS D.openToBase).map f = (baseChange B S hS D.openToBase).map g :=
      congrArg (fun t => t.hom.left) h
    have hL : ∀ i, (baseChange B S hS (D.localToBase i)).map f =
        (baseChange B S hS (D.localToBase i)).map g :=
      fun i => congrArg (fun t => t.hom.right i) h
    have hmid : (baseChange B S hS p.midToBase).map f = (baseChange B S hS p.midToBase).map g := by
      refine hlast.map_injective (ObjectProperty.hom_ext _ (Comma.hom_ext _ _ ?_ ?_))
      · exact map_eq_of_natIso (baseChangeFactorIso B S hS p.openToMid_comp) hU
      · exact map_eq_of_natIso (baseChangeFactorIso B S hS p.lastToMid_comp) (hL _)
    exact htail.map_injective
      (ObjectProperty.hom_ext _ (Comma.hom_ext _ _ hmid (funext fun i => hL i.castSucc)))

/-- **Fullness passes along a splitting.** If the comparison functor of Stacks 0E90 at the
split-off point and the comparison functor of the remaining points are full, so is the comparison
functor of all the points: a morphism of glueing data gives a morphism of glueing data at the
split-off point over the intermediate base, which comes from a morphism over the intermediate
base; together with the components at the remaining points this is a morphism of glueing data
for the remaining points, which comes from a morphism over the base. -/
theorem full_comparisonFunctor_peel {n : ℕ} {D : ClosedPointsGlueingData B S hS (n + 1)}
    (p : D.Peel) (hlast : p.lastFunctor.Full) (htail : p.tail.comparisonFunctor.Full) :
    D.comparisonFunctor.Full where
  map_surjective {Y Y'} g := by
    let a : (baseChange B S hS D.openToBase).obj Y ⟶ (baseChange B S hS D.openToBase).obj Y' :=
      g.hom.left
    let b : ∀ i, (baseChange B S hS (D.localToBase i)).obj Y ⟶
        (baseChange B S hS (D.localToBase i)).obj Y' := g.hom.right
    have hw : ∀ i, (baseChange B S hS (D.overlapToOpen i)).map a ≫
        (baseChangeSquareIso B S hS (D.w i)).hom.app Y' =
          (baseChangeSquareIso B S hS (D.w i)).hom.app Y ≫
            (baseChange B S hS (D.overlapToLocal i)).map (b i) :=
      fun i => comparisonFunctor_hom_w D g i
    let Fo := baseChangeFactorIso B S hS p.openToMid_comp
    let Fl := baseChangeFactorIso B S hS p.lastToMid_comp
    -- the glueing datum at the split-off point, over the intermediate base
    let a' : (baseChange B S hS p.openToMid).obj ((baseChange B S hS p.midToBase).obj Y) ⟶
        (baseChange B S hS p.openToMid).obj ((baseChange B S hS p.midToBase).obj Y') :=
      Fo.inv.app Y ≫ a ≫ Fo.hom.app Y'
    let b' : (baseChange B S hS p.lastToMid).obj ((baseChange B S hS p.midToBase).obj Y) ⟶
        (baseChange B S hS p.lastToMid).obj ((baseChange B S hS p.midToBase).obj Y') :=
      Fl.inv.app Y ≫ b (Fin.last n) ≫ Fl.hom.app Y'
    have CB : ∀ Z, (baseChange B S hS (D.overlapToOpen (Fin.last n))).map (Fo.hom.app Z) ≫
        (baseChangeSquareIso B S hS p.last_w).hom.app ((baseChange B S hS p.midToBase).obj Z) =
          (baseChangeSquareIso B S hS (D.w (Fin.last n))).hom.app Z ≫
            (baseChange B S hS (D.overlapToLocal (Fin.last n))).map (Fl.hom.app Z) :=
      fun Z => baseChangeSquareIso_comp_base B S hS p.openToMid_comp p.lastToMid_comp p.last_w
        (D.w (Fin.last n)) Z
    have hw' : (baseChange B S hS (D.overlapToOpen (Fin.last n))).map a' ≫
        (baseChangeSquareIso B S hS p.last_w).hom.app ((baseChange B S hS p.midToBase).obj Y') =
          (baseChangeSquareIso B S hS p.last_w).hom.app ((baseChange B S hS p.midToBase).obj Y) ≫
            (baseChange B S hS (D.overlapToLocal (Fin.last n))).map b' := by
      simp only [a', b', Functor.map_comp, Category.assoc]
      rw [CB Y', reassoc_of% (hw (Fin.last n))]
      have : Epi ((baseChange B S hS (D.overlapToOpen (Fin.last n))).map (Fo.hom.app Y)) :=
        @IsIso.epi_of_iso _ _ _ _ _
          (Functor.map_isIso (baseChange B S hS (D.overlapToOpen (Fin.last n))) (Fo.app Y).hom)
      rw [← cancel_epi ((baseChange B S hS (D.overlapToOpen (Fin.last n))).map (Fo.hom.app Y)),
        reassoc_of% (CB Y)]
      exact (Iso.hom_inv_id_map_assoc (Fo.app Y) _ _).trans
        (congrArg (_ ≫ ·) (Iso.hom_inv_id_map_assoc (Fl.app Y) _ _).symm)
    let c₁ : p.lastFunctor.obj ((baseChange B S hS p.midToBase).obj Y) ⟶
        p.lastFunctor.obj ((baseChange B S hS p.midToBase).obj Y') :=
      ObjectProperty.homMk { left := a', right := b', w := hw' }
    obtain ⟨c, hc⟩ := hlast.map_surjective c₁
    have hca : (baseChange B S hS p.openToMid).map c = a' := congrArg (fun t => t.hom.left) hc
    have hcb : (baseChange B S hS p.lastToMid).map c = b' := congrArg (fun t => t.hom.right) hc
    -- the glueing datum for the remaining points
    have hwt : ∀ i : Fin n, (baseChange B S hS (p.tail.overlapToOpen i)).map c ≫
        (baseChangeSquareIso B S hS (p.tail.w i)).hom.app Y' =
          (baseChangeSquareIso B S hS (p.tail.w i)).hom.app Y ≫
            (baseChange B S hS (p.tail.overlapToLocal i)).map (b i.castSucc) := by
      intro i
      let ovo := D.overlapToOpen i.castSucc
      let ovl := D.overlapToLocal i.castSucc
      let loc := D.localToBase i.castSucc
      have wt : (ovo ≫ p.openToMid) ≫ p.midToBase = ovl ≫ loc := p.tail.w i
      have hz₂ : (ovo ≫ p.openToMid) ≫ p.midToBase = ovo ≫ D.openToBase := by
        rw [Category.assoc, p.openToMid_comp]
      have hz₁ : ovo ≫ D.openToBase = ovo ≫ D.openToBase := rfl
      have hnm : ovo ≫ p.openToMid = ovo ≫ p.openToMid := rfl
      let Fnm := baseChangeFactorIso B S hS hnm
      let fz₁ := baseChangeFactorIso B S hS hz₁
      let fz₂ := baseChangeFactorIso B S hS hz₂
      have CF := fun Z => baseChangeSquareIso_comp_factor B S hS (D.w i.castSucc) wt hz₁ hz₂ Z
      have AS := fun Z => baseChangeFactorIso_assoc B S hS hnm p.openToMid_comp hz₁ hz₂ Z
      have NAT' : (baseChange B S hS (ovo ≫ p.openToMid)).map c =
          Fnm.hom.app ((baseChange B S hS p.midToBase).obj Y) ≫ (baseChange B S hS ovo).map a' ≫
            Fnm.inv.app ((baseChange B S hS p.midToBase).obj Y') := by
        have hnat := Fnm.hom.naturality c
        simp only [Functor.comp_map, hca] at hnat
        rw [← reassoc_of% hnat, Iso.hom_inv_id_app, Category.comp_id]
      have key : (baseChange B S hS ovo).map (Fo.hom.app Y') ≫
          Fnm.inv.app ((baseChange B S hS p.midToBase).obj Y') ≫
            (baseChangeSquareIso B S hS wt).hom.app Y' =
          (baseChangeSquareIso B S hS (D.w i.castSucc)).hom.app Y' := by
        rw [← cancel_epi (fz₁.hom.app Y'), reassoc_of% (AS Y'), Iso.hom_inv_id_app_assoc, CF Y']
      change (baseChange B S hS (ovo ≫ p.openToMid)).map c ≫
          (baseChangeSquareIso B S hS wt).hom.app Y' =
        (baseChangeSquareIso B S hS wt).hom.app Y ≫ (baseChange B S hS ovl).map (b i.castSucc)
      rw [← cancel_epi (fz₂.hom.app Y), reassoc_of% (CF Y), ← hw i.castSucc, NAT']
      simp only [Category.assoc]
      rw [← reassoc_of% (AS Y)]
      simp only [a', Functor.map_comp, Category.assoc]
      have e : (baseChange B S hS ovo).map (Fo.hom.app Y) ≫
          (baseChange B S hS ovo).map (Fo.inv.app Y) = 𝟙 _ :=
        Iso.hom_inv_id_map (Fo.app Y) _
      rw [reassoc_of% e, key]
    let c₂ : p.tail.comparisonFunctor.obj Y ⟶ p.tail.comparisonFunctor.obj Y' :=
      ObjectProperty.homMk { left := c, right := fun i => b i.castSucc, w := funext hwt }
    obtain ⟨h₀, hh⟩ := htail.map_surjective c₂
    let h : Y ⟶ Y' := h₀
    have h₁ : (baseChange B S hS p.midToBase).map h = c := congrArg (fun t => t.hom.left) hh
    refine ⟨h, ObjectProperty.hom_ext _ (Comma.hom_ext _ _ ?_ ?_)⟩
    · exact map_eq_of_map_eq_inv_comp_comp Fo h a (by simp only [Functor.comp_map, h₁, hca, a'])
    · funext i
      induction i using Fin.lastCases with
      | last =>
        exact map_eq_of_map_eq_inv_comp_comp Fl h (b (Fin.last n))
          (by simp only [Functor.comp_map, h₁, hcb, b'])
      | cast i => exact congrArg (fun t => t.hom.right i) hh

end ClosedPointsGlueingData

/-! ### Quasi-compactness of the intermediate bases -/

/-- If `U` is the complement of a finite set, then `W ∖ U` is finite for every `W`. -/
private theorem finite_diff_of_compl_eq {F : Set S} (hF : F.Finite) {U : S.Opens}
    (hU : (U : Set S) = Fᶜ) (W : S.Opens) : ((W : Set S) \ U).Finite :=
  hF.subset fun x hx => by simpa [hU] using hx.2

/-- An open containing a quasi-compact open `V` with finitely many points outside `V` is
quasi-compact over `S`. -/
theorem quasiCompact_ι_of_finite_diff {V W : S.Opens} (hV : QuasiCompact V.ι) (hVW : V ≤ W)
    (hfin : ((W : Set S) \ V).Finite) : QuasiCompact W.ι := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro A hA
  rw [W.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
  change IsCompact (W.ι '' (W.ι ⁻¹' (A : Set S)))
  rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  have h₁ : IsCompact ((A : Set S) ∩ V) := by
    have := (hV.isCompact_preimage _ A.2 hA.isCompact).image V.ι.continuous
    rwa [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι] at this
  rw [← Set.union_sdiff_cancel (show (V : Set S) ⊆ W from hVW), Set.inter_union_distrib_left]
  exact h₁.union (hfin.subset Set.inter_subset_right).isCompact

/-- The inclusion of a quasi-compact open into an open is of finite presentation. -/
theorem finitePresentation_homOfLE {V W : S.Opens} (hV : QuasiCompact V.ι) (h : V ≤ W) :
    FinitePresentation (S.homOfLE h) := by
  have : QuasiCompact (S.homOfLE h ≫ W.ι) := by rwa [Scheme.homOfLE_ι]
  exact ⟨inferInstance, QuasiCompact.of_comp _ W.ι, inferInstance⟩

/-- A quasi-compact open of `S` is of finite presentation over `S`. -/
theorem finitePresentation_ι {V : S.Opens} (hV : QuasiCompact V.ι) : FinitePresentation V.ι :=
  ⟨inferInstance, hV, inferInstance⟩

/-! ### Stacks 0E90 over the intermediate bases -/

/-- The local scheme at `s` lies over every open containing `s`, as an object of the site. -/
noncomputable def localToOpens (s : S) (Z : S.Opens) (hs : s ∈ Z) :
    localObj B S hS s ⟶ opensObj B S hS Z :=
  toOpensObj B S hS Z (range_localObj_subset B hS Z hs)

/-- Two opens of `S` whose intersection is a third are its fibre product over `S`, in the
site. -/
theorem isPullback_opensObj_of_eq {P V V' : S.Opens} (h₁ : P ≤ V) (h₂ : P ≤ V')
    (hP : P = V ⊓ V') :
    IsPullback (opensHomOfLE B S hS h₁) (opensHomOfLE B S hS h₂)
      (toBase B S hS (opensObj B S hS V)) (toBase B S hS (opensObj B S hS V')) := by
  subst hP
  exact isPullback_opensObj_inf B S hS V V'

/-- **Stacks 0E90 over an open of `S`.** Let `F` be a finite set of closed points of `S`
containing `s`, with complement `U` of quasi-compact inclusion, and let `Z = S ∖ (F ∖ {s})`.
Then the comparison functor `FP_Z ⥤ FP_U ×_{FP_V} FP_{Spec 𝒪_{S,s}}` of the square over `Z` is
an equivalence. It is obtained from Stacks 0E90 at `s` over `S` itself by glueing along the
inclusion of `Z`, which is quasi-compact because only finitely many points of `Z` lie outside
`U`. -/
theorem isEquivalence_glueingFunctor_closedPoint_of_open {s : S} (hs : IsClosed ({s} : Set S))
    {F : Set S} (hF : ∀ x ∈ F, IsClosed {x}) (hsF : s ∈ F) (hFfin : F.Finite) (U : S.Opens)
    (hU : (U : Set S) = Fᶜ) (hqc : QuasiCompact U.ι) (Z : S.Opens)
    (hZ : (Z : Set S) = (F \ {s})ᶜ) (hUZ : U ≤ Z) (hsZ : s ∈ Z) :
    (glueingFunctor B S hS (isSubterminal_opensObj B S hS Z
      (puncturedToOpens B S hS hF hsF U hU ≫ opensHomOfLE B S hS hUZ)
      (puncturedToLocal B S hS s ≫ localToOpens B S hS s Z hsZ))).IsEquivalence := by
  -- the complement of `s`, over which Stacks 0E90 applies
  let U' : S.Opens := ⟨{s}ᶜ, hs.isOpen_compl⟩
  have hU' : (U' : Set S) = {s}ᶜ := rfl
  have hUU' : U ≤ U' := by
    intro x hx
    change x ∈ (U : Set S) at hx
    rw [hU] at hx
    exact fun h => hx ((Set.mem_singleton_iff.1 h) ▸ hsF)
  have hqc' : QuasiCompact U'.ι :=
    quasiCompact_ι_of_finite_diff S hqc hUU' (finite_diff_of_compl_eq S hFfin hU U')
  have hZqc : QuasiCompact Z.ι :=
    quasiCompact_ι_of_finite_diff S hqc hUZ (finite_diff_of_compl_eq S hFfin hU Z)
  have hT := isEquivalence_glueingFunctor_closedPoint B S hS hs U' hU' hqc'
  have : Mono (toBase B S hS (opensObj B S hS Z)) :=
    mono_of_isSubterminal (isSubterminal_opensObj B S hS Z) _
  refine isEquivalence_glueingFunctor_of_mono B S hS (u' := toBase B S hS (opensObj B S hS U'))
    (m := toBase B S hS (localObj B S hS s))
    (nU' := puncturedToOpens B S hS (F := {s}) (fun x hx => (Set.mem_singleton_iff.1 hx) ▸ hs)
      (Set.mem_singleton s) U' hU')
    (Space.isFinitePresentation_yoneda_map B S hS _ ?_)
    (Space.isFinitePresentation_yoneda_map B S hS (opensHomOfLE B S hS hUU') ?_)
    (isPullback_opensObj_of_eq B S hS hUU' hUZ ?_)
    (isSubterminal_base B S hS _ _) (isSubterminal_opensObj B S hS _ _ _) _ _ hT
  · rw [toScheme_map_eq_inclusion_map_hom, inclusion_map_opensObj_hom]
    exact finitePresentation_ι S hZqc
  · exact finitePresentation_homOfLE S hqc hUU'
  · apply SetLike.ext'
    change (U : Set S) = (U' : Set S) ∩ Z
    rw [hU, hU', hZ]
    ext x
    by_cases hx : x = s
    · subst hx
      simp [hsF]
    · simp [hx]

/-! ### The glueing data of Stacks 0E92 -/

/-- The points of a family of closed points are closed. -/
theorem isClosed_of_mem_range {n : ℕ} {s : Fin n → S} (hs : ∀ i, IsClosed ({s i} : Set S)) :
    ∀ x ∈ Set.range s, IsClosed ({x} : Set S) :=
  Set.forall_mem_range.2 hs

/-- **The glueing data of Stacks 0E92**, attached to a family `s₁, …, sₙ` of closed points of `S`
and the open `U = S ∖ {s₁, …, sₙ}`: the base is `S`, the open part is `U`, the `i`th local part
is `Spec 𝒪_{S,sᵢ}` with its canonical morphism to `S`, and the `i`th overlap is the punctured
local scheme `Spec 𝒪_{S,sᵢ} ∖ {sᵢ}`, which lies over `U`. -/
noncomputable def closedPointsGlueingData {n : ℕ} (s : Fin n → S)
    (hs : ∀ i, IsClosed ({s i} : Set S)) (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) :
    ClosedPointsGlueingData B S hS n where
  base := Over.mk (𝟙 (B.obj hS))
  openPart := opensObj B S hS U
  localPart i := localObj B S hS (s i)
  overlapPart i := puncturedObj B S hS (s i)
  openToBase := toBase B S hS _
  localToBase _ := toBase B S hS _
  overlapToOpen i :=
    puncturedToOpens B S hS (isClosed_of_mem_range S hs) (Set.mem_range_self i) U hU
  overlapToLocal i := puncturedToLocal B S hS (s i)
  w _ := isSubterminal_base B S hS _ _

/-- Base change along an isomorphism of the site is an equivalence. -/
theorem isEquivalence_baseChange_of_isIso {X Y : BigFppfOver B S hS} (j : X ⟶ Y) [IsIso j] :
    (baseChange B S hS j).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (baseChange B S hS j) (baseChange B S hS (inv j))
    ((baseChangeId B S hS Y).symm ≪≫
      eqToIso (congrArg (baseChange B S hS) (IsIso.inv_hom_id j)).symm ≪≫
        baseChangeComp B S hS (inv j) j)
    ((baseChangeComp B S hS j (inv j)).symm ≪≫
      eqToIso (congrArg (baseChange B S hS) (IsIso.hom_inv_id j)) ≪≫
        baseChangeId B S hS X)).isEquivalence_functor

/-- **Stacks 0E92 for no points.** The open part is `S` itself, and the comparison functor is
base change along an isomorphism. -/
theorem isEquivalence_comparisonFunctor_closedPointsGlueingData_zero (s : Fin 0 → S)
    (hs : ∀ i, IsClosed ({s i} : Set S)) (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) :
    IsIso (closedPointsGlueingData B S hS s hs U hU).openToBase ∧
      (closedPointsGlueingData B S hS s hs U hU).comparisonFunctor.Faithful ∧
        (closedPointsGlueingData B S hS s hs U hU).comparisonFunctor.Full := by
  have hUtop : U = ⊤ := by
    apply SetLike.ext'
    rw [hU, Set.range_eq_empty, Set.compl_empty]
    rfl
  have hiso : IsIso (closedPointsGlueingData B S hS s hs U hU).openToBase := by
    have : IsIso ((BigFppfOver.toScheme B S hS).map
        (closedPointsGlueingData B S hS s hs U hU).openToBase) := by
      change IsIso ((BigFppfOver.toScheme B S hS).map (toBase B S hS (opensObj B S hS U)))
      rw [toScheme_map_eq_inclusion_map_hom, inclusion_map_opensObj_hom]
      subst hUtop
      exact (S.topIso).isIso_hom
    exact isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  have := isEquivalence_baseChange_of_isIso B S hS
    (closedPointsGlueingData B S hS s hs U hU).openToBase
  refine ⟨hiso, ⟨fun {Y Y'} {f g} h => ?_⟩, ⟨fun {Y Y'} g => ?_⟩⟩
  · exact (baseChange B S hS _).map_injective (congrArg (fun t => t.hom.left) h)
  · obtain ⟨f, hf⟩ := (baseChange B S hS _).map_surjective g.hom.left
    exact ⟨f, ObjectProperty.hom_ext _ (Comma.hom_ext _ _ hf (funext fun i => i.elim0))⟩

/-! ### Splitting off the last point -/

/-- The intermediate base of the splitting at the last point: the complement of all the points
but the last. -/
def midOpens {n : ℕ} (s : Fin (n + 1) → S) (hs : ∀ i, IsClosed ({s i} : Set S)) : S.Opens :=
  ⟨(Set.range (s ∘ Fin.castSucc))ᶜ, by
    rw [← Set.iUnion_singleton_eq_range]
    exact (isClosed_iUnion_of_finite fun i => hs _).isOpen_compl⟩

/-- The underlying set of `midOpens S s hs` is the complement of `{s₁, …, s_{n-1}}`. -/
theorem coe_midOpens {n : ℕ} (s : Fin (n + 1) → S) (hs : ∀ i, IsClosed ({s i} : Set S)) :
    (midOpens S s hs : Set S) = (Set.range (s ∘ Fin.castSucc))ᶜ :=
  rfl

/-- The complement of all the points is contained in `midOpens S s hs`. -/
theorem le_midOpens {n : ℕ} (s : Fin (n + 1) → S) (hs : ∀ i, IsClosed ({s i} : Set S))
    (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) : U ≤ midOpens S s hs := by
  intro x hx
  change x ∈ (U : Set S) at hx
  rw [hU] at hx
  rintro ⟨i, rfl⟩
  exact hx ⟨_, rfl⟩

/-- If the points are pairwise distinct, the last point lies in `midOpens S s hs`. -/
theorem last_mem_midOpens {n : ℕ} (s : Fin (n + 1) → S) (hinj : Function.Injective s)
    (hs : ∀ i, IsClosed ({s i} : Set S)) : s (Fin.last n) ∈ midOpens S s hs := by
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i (hinj hi)

/-- If the points are pairwise distinct, the set of all points but the last is the set of all
points with the last one removed. -/
theorem range_castSucc_eq {n : ℕ} (s : Fin (n + 1) → S) (hinj : Function.Injective s) :
    Set.range (s ∘ Fin.castSucc) = Set.range s \ {s (Fin.last n)} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨⟨_, rfl⟩, fun h => Fin.castSucc_ne_last i (hinj h)⟩
  · rintro ⟨⟨j, rfl⟩, hj⟩
    induction j using Fin.lastCases with
    | last => exact absurd rfl hj
    | cast i => exact ⟨i, rfl⟩

/-- **The splitting of the glueing data of Stacks 0E92 at its last point**, through the
intermediate base `S ∖ {s₁, …, s_{n-1}}`. -/
noncomputable def closedPointsPeel {n : ℕ} (s : Fin (n + 1) → S) (hinj : Function.Injective s)
    (hs : ∀ i, IsClosed ({s i} : Set S)) (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) :
    (closedPointsGlueingData B S hS s hs U hU).Peel where
  mid := opensObj B S hS (midOpens S s hs)
  midToBase := toBase B S hS _
  openToMid := opensHomOfLE B S hS (le_midOpens S s hs U hU)
  openToMid_comp := isSubterminal_base B S hS _ _
  lastToMid :=
    localToOpens B S hS (s (Fin.last n)) (midOpens S s hs) (last_mem_midOpens S s hinj hs)
  lastToMid_comp := isSubterminal_base B S hS _ _
  last_w := isSubterminal_opensObj B S hS _ _ _

/-- The glueing data of the remaining points is the glueing data of Stacks 0E92 for them, with
the intermediate base as the open part. -/
theorem closedPointsPeel_tail {n : ℕ} (s : Fin (n + 1) → S) (hinj : Function.Injective s)
    (hs : ∀ i, IsClosed ({s i} : Set S)) (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ) :
    (closedPointsPeel B S hS s hinj hs U hU).tail =
      closedPointsGlueingData B S hS (s ∘ Fin.castSucc) (fun i => hs i.castSucc)
        (midOpens S s hs) rfl := by
  simp only [ClosedPointsGlueingData.Peel.tail, closedPointsPeel, closedPointsGlueingData]
  congr 1
  funext i
  exact isSubterminal_opensObj B S hS _ _ _

/-! ### Stacks 0E92 -/

/-- **The induction of Stacks 0E92.** The glueing data at finitely many closed points admits a
tower of splittings whose comparison functors of Stacks 0E90 are essentially surjective, and its
comparison functor is faithful and full. -/
theorem solvable_and_faithful_and_full_closedPointsGlueingData :
    ∀ (n : ℕ) (s : Fin n → S), Function.Injective s → ∀ (hs : ∀ i, IsClosed ({s i} : Set S))
      (U : S.Opens) (hU : (U : Set S) = (Set.range s)ᶜ), QuasiCompact U.ι →
      ClosedPointsGlueingData.Solvable n (closedPointsGlueingData B S hS s hs U hU) ∧
        (closedPointsGlueingData B S hS s hs U hU).comparisonFunctor.Faithful ∧
          (closedPointsGlueingData B S hS s hs U hU).comparisonFunctor.Full
  | 0, s, _, hs, U, hU, _ =>
    isEquivalence_comparisonFunctor_closedPointsGlueingData_zero B S hS s hs U hU
  | n + 1, s, hinj, hs, U, hU, hqc => by
    let p := closedPointsPeel B S hS s hinj hs U hU
    have hmid : QuasiCompact (midOpens S s hs).ι :=
      quasiCompact_ι_of_finite_diff S hqc (le_midOpens S s hs U hU)
        (finite_diff_of_compl_eq S (Set.finite_range s) hU _)
    have IH := solvable_and_faithful_and_full_closedPointsGlueingData n (s ∘ Fin.castSucc)
      (hinj.comp (Fin.castSucc_injective n)) (fun i => hs _) (midOpens S s hs) rfl hmid
    rw [← closedPointsPeel_tail B S hS s hinj hs U hU] at IH
    have hlast : p.lastFunctor.IsEquivalence :=
      isEquivalence_glueingFunctor_closedPoint_of_open B S hS (hs (Fin.last n))
        (isClosed_of_mem_range S hs) (Set.mem_range_self _) (Set.finite_range s) U hU hqc
        (midOpens S s hs) (by rw [coe_midOpens, range_castSucc_eq S s hinj])
        (le_midOpens S s hs U hU) (last_mem_midOpens S s hinj hs)
    exact ⟨⟨p, inferInstance, IH.1⟩,
      ClosedPointsGlueingData.faithful_comparisonFunctor_peel p inferInstance IH.2.1,
      ClosedPointsGlueingData.full_comparisonFunctor_peel p inferInstance IH.2.2⟩

/-- **Stacks 0E92.** Let `S` be a scheme of a big fppf site and let `s₁, …, sₙ` be pairwise
distinct closed points of `S` such that `U = S ∖ {s₁, …, sₙ} ⟶ S` is quasi-compact. With
`Sᵢ = Spec 𝒪_{S,sᵢ}` and `Uᵢ = Sᵢ ∖ {sᵢ}`, the comparison functor
`FP_S ⥤ FP_U ×_{(FP_{U₁} × ⋯ × FP_{Uₙ})} (FP_{S₁} × ⋯ × FP_{Sₙ})`,
taking an algebraic space of finite presentation over `S` to its base change to `U`, the family
of its base changes to the `Sᵢ` and the family of the canonical identifications of their base
changes to the `Uᵢ`, is an equivalence of categories. Here `FP_T` is the category of algebraic
spaces of finite presentation over `T`, and the `2`-fibre product is the iso-comma category of
the two functors into `∀ i, FP_{Uᵢ}` assembled from the base changes. -/
@[stacks 0E92]
theorem isEquivalence_comparisonFunctor_closedPoints {n : ℕ} (s : Fin n → S)
    (hinj : Function.Injective s) (hs : ∀ i, IsClosed ({s i} : Set S)) (U : S.Opens)
    (hU : (U : Set S) = (Set.range s)ᶜ) (hqc : QuasiCompact U.ι) :
    (closedPointsGlueingData B S hS s hs U hU).comparisonFunctor.IsEquivalence := by
  obtain ⟨hsol, hfaith, hfull⟩ :=
    solvable_and_faithful_and_full_closedPointsGlueingData B S hS n s hinj hs U hU hqc
  exact ⟨hfaith, hfull, ClosedPointsGlueingData.essSurj_comparisonFunctor n _ hsol⟩

end AlgebraicGeometry.FinitePresentationSpacesOver

end
