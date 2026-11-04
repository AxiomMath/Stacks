module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceQuasiCompactOperations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowCompactifiableCoverFamily
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowSectionIsomExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoOpenGluing

/-!
# Sections over a proper modification and the gluing step of Stacks 0CQ7

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism from an algebraic stack to an algebraic space all of
whose values lie in an open subspace `W ⊆ Y`, and let `p : Y' ⟶ Y` be a proper morphism from a
quasi-compact quasi-separated algebraic space. Suppose that `p⁻¹(W)` is covered by quasi-compact
opens `U₀, …, Uₙ` carrying 1-morphisms `xᵢ : Uᵢ ⟶ 𝒳` over `Y`, and that the `xᵢ` are
2-isomorphic to `x₀` over a quasi-compact open `V ⊆ U₀ ∩ … ∩ Uₙ`. Then the conclusion of
[Stacks, Tag 0CQ7] holds for the image of `|V|` in `|Y|`. This is the last paragraph of the
proof of [Stacks, Tag 0CQ7], with the gluing of the `xᵢ` done one open at a time: two sections
which are isomorphic over `V` become isomorphic over the intersection of their domains after a
`V`-admissible blowup ([Stacks, Tag 0CPI]), and then glue, the cocycle condition being empty for
two members.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompactSpace_inf`: the intersection of two quasi-compact open
  subspaces of a quasi-separated algebraic space is quasi-compact.
* `AlgebraicGeometry.Space.range_pointsMap_subset_image_of_isAdmissibleBlowup`: a `V`-admissible
  blowup is surjective over `V`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.CompactifiableCover.ofSection`: a section over the
  inverse image of `W` is a proper compactifiable cover.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The intersection of two quasi-compact open subspaces of a quasi-separated algebraic space
is quasi-compact.** Its point set is the image, under the inclusion of `U₀`, of the point set of
the inverse image of `U₁` in `U₀`, which is quasi-compact because the inclusion of `U₀` is
quasi-compact (Stacks 073B). -/
theorem isQuasiCompactSpace_inf {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X) {U₀ U₁ : Subfunctor X}
    (hU₀ : IsOpenSubspace B S hS U₀) (hU₁ : IsOpenSubspace B S hS U₁)
    (hU₀qc : IsQuasiCompactSpace B S hS U₀.toFunctor)
    (hU₁qc : IsQuasiCompactSpace B S hS U₁.toFunctor) :
    IsQuasiCompactSpace B S hS (U₀ ⊓ U₁).toFunctor := by
  let := pointTopology B S hS X
  let := pointTopology B S hS U₀.toFunctor
  have hpre : IsQuasiCompactSpace B S hS (U₁.preimage U₀.ι).toFunctor :=
    isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS hX hU₀.1 U₀.ι
      (isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal hX hXqs hU₀qc U₀.ι)
      hU₁ hU₁qc
  have hpreo : IsOpenSubspace B S hS (U₁.preimage U₀.ι) :=
    isOpenSubspace_preimage B S hS U₀.ι U₁ hX hU₀.1 hU₁
  refine isQuasiCompactSpace_of_isCompact_range B S hS hX
    (isOpenSubspace_inf B S hS hX U₀ U₁ hU₀ hU₁) ?_
  have hcpt := (isCompact_range_of_isQuasiCompactSpace B S hS hpreo hpre).image
    (continuous_pointsMap B S hS U₀.ι)
  convert hcpt using 1
  rw [← Set.range_comp, ← pointsMap_comp]
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    let k : (U₀ ⊓ U₁).toFunctor ⟶ (U₁.preimage U₀.ι).toFunctor :=
      Subfunctor.lift (Subfunctor.homOfLe inf_le_left) (by
        rintro T _ ⟨y, rfl⟩
        exact y.2.2)
    refine ⟨pointsMap B S hS _ k z, ?_⟩
    rw [← pointsMap_comp_apply]
    rfl
  · rintro _ ⟨z, rfl⟩
    let k : (U₁.preimage U₀.ι).toFunctor ⟶ (U₀ ⊓ U₁).toFunctor :=
      Subfunctor.lift ((U₁.preimage U₀.ι).ι ≫ U₀.ι) (by
        rintro T _ ⟨y, rfl⟩
        exact ⟨y.1.2, y.2⟩)
    refine ⟨pointsMap B S hS _ k z, ?_⟩
    rw [← pointsMap_comp_apply]
    rfl

/-- The inclusion of a smaller subfunctor into the inverse image of itself along the inclusion
of a larger one is an isomorphism. -/
theorem isIso_fromPreimage_ι_of_le {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U Z : Subfunctor X}
    (hUZ : U ≤ Z) : IsIso (U.fromPreimage Z.ι) :=
  Subfunctor.isIso_fromPreimage_of_le_range U Z.ι fun _ x hx => ⟨⟨x, hUZ _ hx⟩, rfl⟩

/-- **A `V`-admissible blowup is surjective over `V`**: every point of `V` is the image of a
point of `b⁻¹(V)`. The centre misses `V`, so `V` lies in the complement of the centre, over which
the blowup is an isomorphism (Stacks 085T). -/
theorem range_pointsMap_subset_image_of_isAdmissibleBlowup {X X' : AlgebraicSpaces B S hS}
    (V : OpenSubspaces B S hS X.1) {b : X' ⟶ X} (hb : IsAdmissibleBlowup B S hS V b) :
    Set.range (pointsMap B S hS V.1.toFunctor V.1.ι) ⊆
      pointsMap B S hS X'.1 b.hom '' Set.range
        (pointsMap B S hS (V.1.preimage b.hom).toFunctor (V.1.preimage b.hom).ι) := by
  obtain ⟨Z, -, hdisj, hbl⟩ := hb
  let C := openComplementOfClosedSubspace B S hS X Z
  have hVC : Set.range (pointsMap B S hS V.1.toFunctor V.1.ι) ⊆
      Set.range (pointsMap B S hS C.1.toFunctor C.1.ι) := by
    intro y hy
    show y ∈ subspacePointSet B S hS X.1 C.1
    rw [subspacePointSet_openComplement B S hS X Z]
    exact fun hz => Set.disjoint_left.1 hdisj hy hz
  have := isIso_fromPreimage_openComplement hbl
  intro y hy
  obtain ⟨c, hc⟩ := hVC hy
  let c' := pointsMap B S hS _ (inv (C.1.fromPreimage b.hom)) c
  have hc' : pointsMap B S hS _ (C.1.fromPreimage b.hom) c' = c := by
    rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id]
    rfl
  let y' := pointsMap B S hS _ (C.1.preimage b.hom).ι c'
  have hy' : pointsMap B S hS X'.1 b.hom y' = y := by
    rw [← pointsMap_comp_apply, ← Subfunctor.fromPreimage_ι, pointsMap_comp_apply, hc', hc]
  refine ⟨y', ?_, hy'⟩
  rwa [range_pointsMap_preimage_ι, Set.mem_preimage, hy']

end AlgebraicGeometry.Space


namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A section over the inverse image of an open containing the values of `f` is a proper
compactifiable cover.** Let `f : 𝒳 ⟶ Y` be separated with all its values in an open `W ⊆ Y`, let
`p : Y' ⟶ Y` be proper and let `x : p⁻¹(W) ⟶ 𝒳` be a 1-morphism over `Y`. Then `Z̄ = Y'`,
`Z = p⁻¹(W)`, `h = x` is a proper compactifiable cover of `f`; this is the last step of the proof
of [Stacks, Tag 0CQ7], `HasProperCompactifiableCover.of_section_preimage`, read as a cover. -/
def CompactifiableCover.ofSection {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hY' : IsAlgebraicSpace B S hS Y')
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : IsSeparated B S hS f) (W : Subfunctor Y) (hW : Space.IsOpenSubspace B S hS W)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)))
    (p : Y' ⟶ Y) (hp : Space.IsProper B S hS p)
    (x : algebraicSpaceStack.{u, w} B S hS (W.preimage p).toFunctor
      (Space.isOpenSubspace_preimage B S hS p W hY hY' hW).1 ⟶ 𝒳)
    (hx : Nonempty (x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS
      (Space.isOpenSubspace_preimage B S hS p W hY hY' hW).1 hY ((W.preimage p).ι ≫ p))) :
    CompactifiableCover hY f where
  Zbar := Y'
  Z := (W.preimage p).toFunctor
  isAlgebraicSpace_Zbar := hY'
  isAlgebraicSpace_Z := (Space.isOpenSubspace_preimage B S hS p W hY hY' hW).1
  j := (W.preimage p).ι
  gbar := p
  h := x
  isOpenImmersion_j := (Space.isOpenSubspace_preimage B S hS p W hY hY' hW).2
  isProper_gbar := hp
  isProper_h := by
    have hW' := Space.isOpenSubspace_preimage B S hS p W hY hY' hW
    obtain ⟨e⟩ := hx
    let fW := corestrictAlgebraicSpaceStack f W hW.1 hfW
    have hιsep : IsSeparated B S hS (algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι) :=
      (isSeparated_algebraicSpaceStackMap_iff.{u, w} B S hS hW.1 hY W.ι).2
        (Space.isSeparated_of_mono W.ι inferInstance)
    have hfWsep : IsSeparated B S hS fW :=
      isSeparated_of_comp_of_isSeparated_diagonal B S hS fW _
        (by rwa [corestrictAlgebraicSpaceStack_comp])
        (Stack.isSeparated_of_isProper B S hS _ hιsep)
    have hcomp : x ≫ fW = algebraicSpaceStackMap.{u, w} B S hS hW'.1 hW.1 (W.fromPreimage p) := by
      refine eq_of_comp_algebraicSpaceStackMap_ι hY hW.1 ?_
      have h1 : (x ≫ fW) ≫ algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι = x ≫ f := by
        rw [Category.assoc, corestrictAlgebraicSpaceStack_comp]
      have h2 : algebraicSpaceStackMap.{u, w} B S hS hW'.1 hW.1 (W.fromPreimage p) ≫
          algebraicSpaceStackMap.{u, w} B S hS hW.1 hY W.ι =
            algebraicSpaceStackMap.{u, w} B S hS hW'.1 hY ((W.preimage p).ι ≫ p) := by
        rw [← Subfunctor.fromPreimage_ι]
        simp only [algebraicSpaceStackMap, associatedMap_comp]
        rfl
      rw [h1, h2]
      exact Bicategory.InducedBicategory.hom_ext (hom_eq_of_hom₂ B S hS e.hom.hom)
    have hpW : Space.IsProper B S hS (W.fromPreimage p) :=
      Space.isProper_of_isPullback B S hS hW'.1 hY' hW.1 hY
        (Subfunctor.isPullback_fromPreimage W p).flip hp
    exact isProper_of_comp_of_isSeparated B S hS x fW
      (by rw [hcomp]; exact (isProper_algebraicSpaceStackMap_iff.{u, w} B S hS _ _ _).2 hpW)
      hfWsep
  iso := hx

section Gluing

variable {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT : IsAlgebraicSpace B S hS T)

/-- The stack map of a composite. -/
theorem algebraicSpaceStackMap_comp_eq {X₁ X₂ X₃ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h₁ : IsAlgebraicSpace B S hS X₁) (h₂ : IsAlgebraicSpace B S hS X₂)
    (h₃ : IsAlgebraicSpace B S hS X₃) (g : X₁ ⟶ X₂) (g' : X₂ ⟶ X₃) :
    algebraicSpaceStackMap.{u, w} B S hS h₁ h₃ (g ≫ g') =
      algebraicSpaceStackMap.{u, w} B S hS h₁ h₂ g ≫
        algebraicSpaceStackMap.{u, w} B S hS h₂ h₃ g' :=
  (Stack.algebraicSpaceStackMap_comp B S hS h₁ h₂ h₃ g g').symm

/-- The stack map of an identity is the identity. -/
theorem algebraicSpaceStackMap_id_eq {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) :
    algebraicSpaceStackMap.{u, w} B S hS hX hX (𝟙 X) = 𝟙 _ :=
  (algebraicSpaceStackFunctor.{u, w} B S hS).map_id ⟨X, hX⟩

/-- If `G` restricts to `x` along `U.preimage Z.ι ≅ U`, it also does so along `U ⟶ Z`. -/
private theorem nonempty_iso_homOfLe_comp {Z U : Subfunctor T}
    (hZ : IsAlgebraicSpace B S hS Z.toFunctor) (hU : IsAlgebraicSpace B S hS U.toFunctor)
    (hV : IsAlgebraicSpace B S hS (U.preimage Z.ι).toFunctor) (h : U ≤ Z)
    {𝒴 : AlgebraicStacks.{u, w} B S hS} (x : algebraicSpaceStack.{u, w} B S hS U.toFunctor hU ⟶ 𝒴)
    (G : algebraicSpaceStack.{u, w} B S hS Z.toFunctor hZ ⟶ 𝒴)
    (i : algebraicSpaceStackMap.{u, w} B S hS hV hZ (U.preimage Z.ι).ι ≫ G ≅
      algebraicSpaceStackMap.{u, w} B S hS hV hU (U.fromPreimage Z.ι) ≫ x) :
    Nonempty (algebraicSpaceStackMap.{u, w} B S hS hU hZ (Subfunctor.homOfLe h) ≫ G ≅ x) := by
  have : IsIso (U.fromPreimage Z.ι) := Space.isIso_fromPreimage_ι_of_le h
  have hk : Subfunctor.homOfLe h = inv (U.fromPreimage Z.ι) ≫ (U.preimage Z.ι).ι := by
    rw [IsIso.eq_inv_comp]
    rfl
  exact ⟨eqToIso (congrArg (· ≫ G) ((congrArg _ hk).trans
      (algebraicSpaceStackMap_comp_eq hU hV hZ _ _))) ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ i ≪≫ (α_ _ _ _).symm ≪≫
      eqToIso (congrArg (· ≫ x) ((algebraicSpaceStackMap_comp_eq hU hV hU _ _).symm.trans
        ((congrArg _ (IsIso.inv_hom_id (U.fromPreimage Z.ι))).trans
          (algebraicSpaceStackMap_id_eq hU)))) ≪≫ λ_ _⟩

/-- **Gluing two 1-morphisms out of open subspaces `U₀, U₁ ⊆ Z` covering an open subspace `Z` of
an algebraic space**, all three subspaces of one ambient space `T`. The two opens are read inside
`Z` through their inverse images along `Z ⟶ T`, which are isomorphic to them, and glued there by
`AlgebraicGeometry.Stack.exists_hom_of_two_opens`. -/
theorem exists_hom_of_two_le {Z U₀ U₁ : Subfunctor T} (hZ : Space.IsOpenSubspace B S hS Z)
    (hU₀ : Space.IsOpenSubspace B S hS U₀) (hU₁ : Space.IsOpenSubspace B S hS U₁)
    (h₀ : U₀ ≤ Z) (h₁ : U₁ ≤ Z)
    (hcov : Set.range (Space.pointsMap B S hS Z.toFunctor Z.ι) ⊆
      Set.range (Space.pointsMap B S hS U₀.toFunctor U₀.ι) ∪
        Set.range (Space.pointsMap B S hS U₁.toFunctor U₁.ι))
    {𝒴 : AlgebraicStacks.{u, w} B S hS}
    (x₀ : algebraicSpaceStack.{u, w} B S hS U₀.toFunctor hU₀.1 ⟶ 𝒴)
    (x₁ : algebraicSpaceStack.{u, w} B S hS U₁.toFunctor hU₁.1 ⟶ 𝒴)
    (ψ : algebraicSpaceStackMap.{u, w} B S hS
        (Space.isOpenSubspace_inf B S hS hT U₀ U₁ hU₀ hU₁).1 hU₀.1
        (Subfunctor.homOfLe inf_le_left) ≫ x₀ ≅
      algebraicSpaceStackMap.{u, w} B S hS
        (Space.isOpenSubspace_inf B S hS hT U₀ U₁ hU₀ hU₁).1 hU₁.1
        (Subfunctor.homOfLe inf_le_right) ≫ x₁) :
    ∃ G : algebraicSpaceStack.{u, w} B S hS Z.toFunctor hZ.1 ⟶ 𝒴,
      Nonempty (algebraicSpaceStackMap.{u, w} B S hS hU₀.1 hZ.1 (Subfunctor.homOfLe h₀) ≫ G ≅
        x₀) ∧
      Nonempty (algebraicSpaceStackMap.{u, w} B S hS hU₁.1 hZ.1 (Subfunctor.homOfLe h₁) ≫ G ≅
        x₁) := by
  let T' : AlgebraicSpaces B S hS := ⟨Z.toFunctor, hZ.1⟩
  have hV₀ : Space.IsOpenSubspace B S hS (U₀.preimage Z.ι) :=
    Space.isOpenSubspace_preimage B S hS Z.ι U₀ hT hZ.1 hU₀
  have hV₁ : Space.IsOpenSubspace B S hS (U₁.preimage Z.ι) :=
    Space.isOpenSubspace_preimage B S hS Z.ι U₁ hT hZ.1 hU₁
  have hInt := (Space.isOpenSubspace_inf B S hS hT U₀ U₁ hU₀ hU₁).1
  have hInt' := (Space.isOpenSubspace_inf B S hS hZ.1 (U₀.preimage Z.ι) (U₁.preimage Z.ι)
    hV₀ hV₁).1
  let e₀ : (U₀.preimage Z.ι).toFunctor ⟶ U₀.toFunctor := U₀.fromPreimage Z.ι
  let e₁ : (U₁.preimage Z.ι).toFunctor ⟶ U₁.toFunctor := U₁.fromPreimage Z.ι
  let F₀ := algebraicSpaceStackMap.{u, w} B S hS hV₀.1 hU₀.1 e₀ ≫ x₀
  let F₁ := algebraicSpaceStackMap.{u, w} B S hS hV₁.1 hU₁.1 e₁ ≫ x₁
  let c : ((U₀.preimage Z.ι) ⊓ (U₁.preimage Z.ι)).toFunctor ⟶ (U₀ ⊓ U₁).toFunctor :=
    Subfunctor.lift (((U₀.preimage Z.ι) ⊓ (U₁.preimage Z.ι)).ι ≫ Z.ι) (by
      rintro V _ ⟨y, rfl⟩
      exact y.2)
  have hc₀ : Subfunctor.homOfLe inf_le_left ≫ e₀ = c ≫ Subfunctor.homOfLe inf_le_left := rfl
  have hc₁ : Subfunctor.homOfLe inf_le_right ≫ e₁ = c ≫ Subfunctor.homOfLe inf_le_right := rfl
  let ψ' : (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (twoOpenInterFst (T := T') (U₀.preimage Z.ι) (U₁.preimage Z.ι) hV₀ hV₁) ≫ F₀ ≅
      (algebraicSpaceStackFunctor.{u, w} B S hS).map
        (twoOpenInterSnd (T := T') (U₀.preimage Z.ι) (U₁.preimage Z.ι) hV₀ hV₁) ≫ F₁ :=
    (α_ _ _ _).symm ≪≫
      eqToIso (congrArg (· ≫ x₀) ((algebraicSpaceStackMap_comp_eq hInt' hV₀.1 hU₀.1 _ e₀).symm.trans
        ((congrArg (algebraicSpaceStackMap.{u, w} B S hS hInt' hU₀.1) hc₀).trans
          (algebraicSpaceStackMap_comp_eq hInt' hInt hU₀.1 c _)))) ≪≫
      α_ _ _ _ ≪≫ whiskerLeftIso _ ψ ≪≫ (α_ _ _ _).symm ≪≫
      eqToIso (congrArg (· ≫ x₁) ((algebraicSpaceStackMap_comp_eq hInt' hInt hU₁.1 c _).symm.trans
        ((congrArg (algebraicSpaceStackMap.{u, w} B S hS hInt' hU₁.1) hc₁).symm.trans
          (algebraicSpaceStackMap_comp_eq hInt' hV₁.1 hU₁.1 _ e₁)))) ≪≫ α_ _ _ _
  have hcov' : Set.range (Space.pointsMap B S hS (U₀.preimage Z.ι).toFunctor
        (U₀.preimage Z.ι).ι) ∪
      Set.range (Space.pointsMap B S hS (U₁.preimage Z.ι).toFunctor (U₁.preimage Z.ι).ι) =
        Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    rw [Space.range_pointsMap_preimage_ι, Space.range_pointsMap_preimage_ι]
    exact hcov ⟨z, rfl⟩
  obtain ⟨G, ⟨i₀⟩, ⟨i₁⟩⟩ := exists_hom_of_two_opens (T := T') (U₀.preimage Z.ι)
    (U₁.preimage Z.ι) hV₀ hV₁ F₀ F₁ ψ' hcov'
  exact ⟨G, nonempty_iso_homOfLe_comp hZ.1 hU₀.1 hV₀.1 h₀ x₀ G i₀,
    nonempty_iso_homOfLe_comp hZ.1 hU₁.1 hV₁.1 h₁ x₁ G i₁⟩

end Gluing

end AlgebraicGeometry.Stack.AlgebraicStacks

end
