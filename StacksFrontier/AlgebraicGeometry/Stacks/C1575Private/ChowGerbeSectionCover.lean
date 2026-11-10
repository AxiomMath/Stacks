module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeMergeStep
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackCoproductDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackOneMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.Zariski

/-!
# Sections over the preimage of the image, and finite unions (proof of Stacks 0CQ7)

Let `f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to an algebraic space all of whose values
lie in an open subspace `W ⊆ Y`. A section cover of a set `A` of points of `Y` is a proper
morphism `p : Y' ⟶ Y` of algebraic spaces together with a 1-morphism `x : p⁻¹(W) ⟶ 𝒳` with
`f ∘ x ≅ p|_{p⁻¹(W)}` such that `A` lies in the image of `p⁻¹(W)`. A section cover of `|V|` solves
the problem of [Stacks, Tag 0CQ7] for `V`, and section covers are stable under finite unions.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeSectionCover.SectionCover`: a proper
  modification of `Y` with a section of `f` over the preimage of `W`, reaching a set of points.

## Main results

* `SectionCover.hasProperCompactifiableCover`: a section cover of `|V|` solves Stacks 0CQ7 for `V`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeSectionCover.sectionCover_of_mergeData`:
  merge data produce a section cover.
* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeSectionCover.SectionCover.iUnion`: finite
  unions.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeSectionCover

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
  (W : Subfunctor Y)

/-- **A section of `f` over the preimage of `W` in a proper modification, reaching `A`.** There
are a proper morphism `p : Y' ⟶ Y` of algebraic spaces and a 1-morphism `x : p⁻¹(W) ⟶ 𝒳` with
`f ∘ x` 2-isomorphic to `p|_{p⁻¹(W)}`, and every point of `A` is in the image of `p⁻¹(W)`. -/
def SectionCover (A : Set (Space.points B S hS Y)) : Prop :=
  ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y') (p : Y' ⟶ Y)
    (_ : Space.IsProper B S hS p) (hT : IsAlgebraicSpace B S hS (W.preimage p).toFunctor)
    (x : algebraicSpaceStack.{u, w} B S hS (W.preimage p).toFunctor hT ⟶ 𝒳),
    Nonempty (x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hT hY ((W.preimage p).ι ≫ p)) ∧
      A ⊆ Set.range (Space.pointsMap B S hS (W.preimage p).toFunctor ((W.preimage p).ι ≫ p))

variable {hY f W}

/-- A section cover of `A` is a section cover of every subset of `A`. -/
theorem SectionCover.mono {A A' : Set (Space.points B S hS Y)} (h : A' ⊆ A)
    (hA : SectionCover hY f W A) : SectionCover hY f W A' := by
  obtain ⟨Y', hY', p, hp, hT, x, hx, hA⟩ := hA
  exact ⟨Y', hY', p, hp, hT, x, hx, h.trans hA⟩

/-- **A section cover solves Stacks 0CQ7.** If `f` is separated with all values in the open
subspace `W` and `SectionCover f W |V|`, then the conclusion of [Stacks, Tag 0CQ7] holds for
`(f, V)`. -/
theorem SectionCover.hasProperCompactifiableCover (hf : IsSeparated B S hS f)
    (hW : Space.IsOpenSubspace B S hS W)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)))
    (V : Subfunctor Y)
    (h : SectionCover hY f W (Set.range (Space.pointsMap B S hS V.toFunctor V.ι))) :
    HasProperCompactifiableCover.{u, w} B S hS hY f V := by
  obtain ⟨Y', hY', p, hp, hT, x, hx, hA⟩ := h
  exact HasProperCompactifiableCover.of_section_preimage hY hY' f hf W hW hfW p hp x hx V hA

open ChowGerbeMerge in
/-- **Merge data with a single open produce a section cover.** -/
theorem sectionCover_of_mergeData_zero {V : Subfunctor Y} (D : MergeData hY f W V 0)
    (hW : Space.IsOpenSubspace B S hS W) :
    SectionCover hY f W (Set.range (Space.pointsMap B S hS V.toFunctor V.ι)) := by
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ _).1 D.Y'.2.isSheaf
  have hsheaf₀ := (isSheaf_iff_isSheaf_of_type _ _).1 (D.Wi 0).2.1.isSheaf
  have hle : W.preimage D.p ≤ (D.Wi 0).1 := by
    have e : (⨆ k : Fin (0 + 1), (D.Wi k).1) = (D.Wi 0).1 :=
      le_antisymm (iSup_le fun k => by
          rcases k with ⟨_ | k, hk⟩
          · exact le_rfl
          · omega)
        (le_iSup_of_le (⟨0, by omega⟩ : Fin (0 + 1)) le_rfl)
    have h := D.hcov
    rwa [e, ← Subfunctor.eq_sheafify _ hsheaf hsheaf₀] at h
  have hW' := Space.isOpenSubspace_preimage B S hS D.p W hY D.Y'.2 hW
  obtain ⟨k⟩ := nonempty_comp_iso_of_iso hW'.1 (D.Wi 0).2.1 hY f (Subfunctor.homOfLe hle)
    (D.x 0) _ (D.hx 0)
  refine ⟨D.Y'.1, D.Y'.2, D.p, D.hp, hW'.1,
    algebraicSpaceStackMap.{u, w} B S hS hW'.1 (D.Wi 0).2.1 (Subfunctor.homOfLe hle) ≫ D.x 0,
    ⟨k ≪≫ eqToIso (by rw [Subfunctor.homOfLe_ι_assoc])⟩, ?_⟩
  intro v hv
  obtain ⟨w', rfl⟩ := D.hV hv
  refine ⟨Space.pointsMap B S hS _ (Subfunctor.homOfLe D.hV'W) w', ?_⟩
  rw [← Space.pointsMap_comp_apply, Subfunctor.homOfLe_ι_assoc]

open ChowGerbeMerge in
/-- **Merge data produce a section cover.** -/
theorem sectionCover_of_mergeData (hf : IsSeparated B S hS f)
    (hW : Space.IsOpenSubspace B S hS W) {V : Subfunctor Y} :
    ∀ {n : ℕ} (_ : MergeData hY f W V n),
      SectionCover hY f W (Set.range (Space.pointsMap B S hS V.toFunctor V.ι))
  | 0, D => sectionCover_of_mergeData_zero D hW
  | _ + 1, D => (D.nonempty_merge hf).elim fun D' => sectionCover_of_mergeData hf hW D'

/-! ### Finite unions -/

section Union

/-- **A 1-morphism of space stacks out of a coproduct is read on the summands.** Let `Z` be the
coproduct, among fppf sheaves, of algebraic spaces `T k` with legs `e k`, and let
`a : Z ⟶ Y` be a 1-morphism of space stacks whose restriction to every `T k` is 2-isomorphic to
the 1-morphism of `e k ≫ g`. Then `a` is 2-isomorphic to the 1-morphism of `g`. -/
theorem nonempty_iso_algebraicSpaceStackMap_of_isColimit {Z Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z) (hY : IsAlgebraicSpace B S hS Y) {K : Type u}
    (T : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : ∀ k, IsAlgebraicSpace B S hS (T k))
    (e : ∀ k, T k ⟶ Z)
    (he : IsColimit (Cofan.mk (⟨Z, hZ.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u))
      fun k => (⟨e k⟩ : (⟨T k, (hT k).isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
        ⟨Z, hZ.isSheaf⟩)))
    (a : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (g : Z ⟶ Y)
    (ha : ∀ k, Nonempty (algebraicSpaceStackMap.{u, w} B S hS (hT k) hZ (e k) ≫ a ≅
      algebraicSpaceStackMap.{u, w} B S hS (hT k) hY (e k ≫ g))) :
    Nonempty (a ≅ algebraicSpaceStackMap.{u, w} B S hS hZ hY g) := by
  refine nonempty_iso_algebraicSpaceStackMap_of_representingMap_eq B S hS hZ hY a g ?_
  let r := representingMap B S hS (fibredCategory B S hS Z) (fibredCategory B S hS Y) Z Y
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) a.hom
  let Zsh : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨Z, hZ.isSheaf⟩
  let Ysh : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨Y, hY.isSheaf⟩
  let rS : Zsh ⟶ Ysh := ⟨r⟩
  let gS : Zsh ⟶ Ysh := ⟨g⟩
  have key : rS = gS := by
    refine Cofan.IsColimit.hom_ext he _ _ (fun k => ?_)
    obtain ⟨ek⟩ := ha k
    have h1 := representingMap_comp B S hS _ _ _ (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (associatedMap B S hS (e k)).1 a.hom
    rw [representingMap_associatedMap] at h1
    have h2 : e k ≫ r = e k ≫ g := by
      rw [← h1]
      refine (representingMap_congr_twoIso B S hS _ _ _ _
        { hom := ek.hom.hom, inv := ek.inv.hom
          hom_inv_id := congrArg Bicategory.InducedBicategory.Hom₂.hom ek.hom_inv_id
          inv_hom_id := congrArg Bicategory.InducedBicategory.Hom₂.hom ek.inv_hom_id }).trans ?_
      exact representingMap_associatedMap B S hS _ _ _
    exact Sheaf.hom_ext h2
  exact Sheaf.hom_ext_iff.mp key

/-- **Finite unions of section covers.** If `SectionCover f W (A k)` for finitely many `k`, then
`SectionCover f W (⋃ k, A k)`. -/
theorem SectionCover.iUnion (hW : Space.IsOpenSubspace B S hS W) {K : Type u} [Finite K]
    (A : K → Set (Space.points B S hS Y)) (h : ∀ k, SectionCover hY f W (A k)) :
    SectionCover hY f W (⋃ k, A k) := by
  classical
  choose Y' hY' p hp hT x hx hA using h
  have _ : EssentiallySmall.{u} (BigFppfOver B S hS) := essentiallySmall_bigFppfOver B S hS
  let := BigFppfOver.hasSheafify_type B S hS
  have _ : HasColimitsOfShape (Discrete K) (Sheaf (BigFppfOver.topology B S hS) (Type u)) :=
    CategoryTheory.Limits.hasColimitsOfShape_discrete _ K
  let F : K → Sheaf (BigFppfOver.topology B S hS) (Type u) := fun k => ⟨Y' k, (hY' k).isSheaf⟩
  let P := ∐ F
  let ι : ∀ k, F k ⟶ P := Sigma.ι F
  have hP : IsColimit (Cofan.mk P ι) := coproductIsCoproduct F
  have hPalg : IsAlgebraicSpace B S hS P.obj :=
    Space.isAlgebraicSpace_finiteCoproduct B S hS Y' hY' P ι hP
  let Ysh : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨Y, hY.isSheaf⟩
  let pk : ∀ k, F k ⟶ Ysh := fun k => ⟨p k⟩
  let pS : P ⟶ Ysh := Sigma.desc pk
  let pp : P.obj ⟶ Y := pS.hom
  have hιp : ∀ k, (ι k).hom ≫ pp = p k := fun k =>
    Sheaf.hom_ext_iff.mp (Sigma.ι_comp_desc pk k)
  have hpp : Space.IsProper B S hS pp :=
    Space.isProper_of_isColimit_cofan B S hS ι hP (fun k => hY' k) hPalg hY pp
      (fun k => by rw [hιp k]; exact hp k)
  have hTW := Space.isOpenSubspace_preimage B S hS pp W hY hPalg hW
  have hEq : ∀ k, (W.preimage pp).preimage (ι k).hom = W.preimage (p k) := fun k => by
    rw [← Subfunctor.preimage_comp, hιp k]
  have hT'alg : ∀ k, IsAlgebraicSpace B S hS ((W.preimage pp).preimage (ι k).hom).toFunctor :=
    fun k => (Space.isOpenSubspace_preimage B S hS (ι k).hom (W.preimage pp) hPalg (hY' k) hTW).1
  let T' : K → AlgebraicSpaces B S hS := fun k =>
    ⟨((W.preimage pp).preimage (ι k).hom).toFunctor, hT'alg k⟩
  let Tsp : AlgebraicSpaces B S hS := ⟨(W.preimage pp).toFunctor, hTW.1⟩
  let e : ∀ k, T' k ⟶ Tsp := fun k =>
    ObjectProperty.homMk ((W.preimage pp).fromPreimage (ι k).hom)
  let xk : ∀ k, (algebraicSpaceStackFunctor.{u, w} B S hS).obj (T' k) ⟶ 𝒳 := fun k =>
    algebraicSpaceStackMap.{u, w} B S hS (hT'alg k) (hT k) (Subfunctor.homOfLe (hEq k).le) ≫ x k
  have hcomm : ∀ k, (e k).hom ≫ (W.preimage pp).ι ≫ pp =
      ((W.preimage pp).preimage (ι k).hom).ι ≫ p k := fun k => by
    rw [← hιp k]
    exact Subfunctor.fromPreimage_ι_assoc _ _ _
  have hinj : ∀ (k : K) (V : BigFppfOver B S hS) (a a' : (T' k).obj.obj (op V)),
      (e k).hom.app _ a = (e k).hom.app _ a' → a = a' := by
    intro k V a a' hh
    have h' : (ι k).hom.app (op V) a.1 = (ι k).hom.app (op V) a'.1 := congrArg Subtype.val hh
    have hm := (NatTrans.mono_iff_mono_app _).1 (Sheaf.mono_hom_cofan_inj ι hP k) (op V)
    exact Subtype.ext ((mono_iff_injective _).1 hm h')
  have hdisj : ∀ (k l : K), k ≠ l → ∀ (V : BigFppfOver B S hS) (a : (T' k).obj.obj (op V))
      (b : (T' l).obj.obj (op V)), (e k).hom.app _ a = (e l).hom.app _ b →
        IsEmpty ((BigFppfOver.toScheme B S hS).obj V) := fun k l hkl V a b hh =>
    Sheaf.isEmpty_toScheme_of_eq_of_ne ι hP hkl a.1 b.1 (congrArg Subtype.val hh)
  have hOI : ∀ k, Space.IsOpenImmersion B S hS (e k).hom := fun k =>
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback
      (Subfunctor.isPullback_fromPreimage (W.preimage pp) (ι k).hom).flip
      (coproductIncl_isOpenImmersion B S hS F P ι hP k)
  have hSurj : ∀ t : Space.points B S hS (W.preimage pp).toFunctor, ∃ k,
      ∃ r : Space.points B S hS (T' k).obj, Space.pointsMap B S hS (T' k).obj (e k).hom r = t := by
    intro t
    have hZar := Space.isZariskiCover_range_cofan_inj ι hP hY'
    have hcovP := Space.iUnion_range_pointsMap_of_isLocallySurjective_sigmaDesc_ι B S hS hPalg K
      (fun k => Subfunctor.range (ι k).hom) hZar.1 hZar.2
    have hq : Space.pointsMap B S hS (W.preimage pp).toFunctor (W.preimage pp).ι t ∈
        ⋃ k, Set.range (Space.pointsMap B S hS (Subfunctor.range (ι k).hom).toFunctor
          (Subfunctor.range (ι k).hom).ι) := by
      rw [hcovP]
      trivial
    obtain ⟨k, r, hr⟩ := Set.mem_iUnion.1 hq
    obtain ⟨y, rfl⟩ := Space.surjective_pointsMap_of_isLocallySurjective B S hS
      (Subfunctor.toRange (ι k).hom) inferInstance r
    rw [← Space.pointsMap_comp_apply, Subfunctor.toRange_ι] at hr
    obtain ⟨w', hw', -⟩ := Space.exists_point_of_isPullback_presheaf B S hS
      (Subfunctor.isPullback_fromPreimage (W.preimage pp) (ι k).hom) t y hr.symm
    exact ⟨k, w', hw'⟩
  have he : Space.IsEtaleCovering B S hS (fun k => (T' k).obj) (fun k => (e k).hom) :=
    Space.isEtaleCovering_of_isZariskiCovering B S hS hTW.1 hT'alg ⟨hOI, hSurj⟩
  obtain ⟨G, ψ, -⟩ := exists_hom_of_isEtaleCovering he (disjointGluing e hinj hdisj xk)
  have hcolim : IsColimit (Cofan.mk
      (⟨(W.preimage pp).toFunctor, hTW.1.isSheaf⟩ : Sheaf (BigFppfOver.topology B S hS) (Type u))
      fun k => (⟨(e k).hom⟩ : (⟨(T' k).obj, (hT'alg k).isSheaf⟩ :
        Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶
          ⟨(W.preimage pp).toFunctor, hTW.1.isSheaf⟩)) :=
    (Space.nonempty_isColimit_cofanMk_of_isPullback B S hS ι hP
      (⟨(W.preimage pp).ι⟩ : (⟨(W.preimage pp).toFunctor, hTW.1.isSheaf⟩ :
        Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ P) _
      (fun k => (⟨((W.preimage pp).preimage (ι k).hom).ι⟩ : (⟨(T' k).obj, (hT'alg k).isSheaf⟩ :
        Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ F k))
      (fun k => IsPullback.of_map (sheafToPresheaf _ _)
        (Sheaf.hom_ext (Subfunctor.fromPreimage_ι _ _))
        (Subfunctor.isPullback_fromPreimage (W.preimage pp) (ι k).hom))).some
  refine ⟨P.obj, hPalg, pp, hpp, hTW.1, G, ?_, ?_⟩
  · refine nonempty_iso_algebraicSpaceStackMap_of_isColimit hTW.1 hY (fun k => (T' k).obj)
      hT'alg (fun k => (e k).hom) hcolim (G ≫ f) _ (fun k => ?_)
    obtain ⟨ek⟩ := ChowGerbeMerge.nonempty_comp_iso_of_iso (hT'alg k) (hT k) hY f
      (Subfunctor.homOfLe (hEq k).le) (x k) _ (hx k)
    have heq : Subfunctor.homOfLe (hEq k).le ≫ (W.preimage (p k)).ι ≫ p k =
        (e k).hom ≫ (W.preimage pp).ι ≫ pp := by
      rw [Subfunctor.homOfLe_ι_assoc, hcomm k]
    exact ⟨(Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso (asIso (ψ k)) f ≪≫
      ek ≪≫ eqToIso (by rw [heq])⟩
  · intro v hv
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hv
    obtain ⟨z, rfl⟩ := hA k hk
    refine ⟨Space.pointsMap B S hS _ (Subfunctor.homOfLe (hEq k).ge ≫ (e k).hom) z, ?_⟩
    rw [← Space.pointsMap_comp_apply]
    congr 1
    rw [Category.assoc, hcomm k, Subfunctor.homOfLe_ι_assoc]

end Union

end AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeSectionCover

end
