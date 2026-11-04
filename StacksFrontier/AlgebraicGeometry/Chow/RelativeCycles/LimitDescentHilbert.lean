module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.LimitDescent
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorLimitPreserving

/-!
# Descending members of `Hilb` to a finite stage of a limit

Let `S = lim_i S_i` be the limit of a cofiltered system of schemes with affine transition
morphisms, let `T ⟶ S_i` be a scheme over a stage and let `Y ⟶ T` be of finite presentation.
Write `T_j = S_j ×_{S_i} T` and `Y_j = S_j ×_{S_i} Y` for the later stages `j ⟶ i`, and
`T_∞ = S ×_{S_i} T`, `Y_∞ = S ×_{S_i} Y`. Every member of `Hilb(Y_∞/T_∞, r)` — a closed subscheme
flat, of finite presentation and of relative dimension at most `r` over `T_∞` — is the inverse
image of a member of `Hilb(Y_j/T_j, r)` for some stage `j`, and consequently so is every element
of the free abelian group on `Hilb(Y_∞/T_∞, r)`.

The closed subscheme descends as an ideal sheaf of finite presentation
(`Stacks.Hilbert.exists_closed_model`, Limits, Lemmas 01ZM and 01ZP); flatness descends by
Limits, Lemma 04AI and the bound on the relative dimension by Tag 0H3V, both read on the
morphism from the closed subscheme to `T_j`.

## Main results

* `AlgebraicGeometry.relativeDimensionLE_iff_of_isPullback` — the bound on the relative dimension
  of a base change does not depend on the choice of the fibre product.
* `AlgebraicGeometry.exists_relativeDimensionLE_pullback_snd_of_isLimit` — Tag 0H3V for a scheme
  over a stage, in the form of the second projection of a fibre product.
* `Stacks.Chow.exists_hilbertCycleDatum_ofIsPullback_eq` — a member of `Hilb(Y_∞/T_∞, r)` is the
  inverse image of a member of `Hilb(Y_j/T_j, r)`.
* `Stacks.Chow.exists_map_ofIsPullback_eq` — the same for the free abelian group on `Hilb`.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
* [Stacks Project, Tag 0H3V](https://stacks.math.columbia.edu/tag/0H3V)
* [Stacks Project, Tag 0H5D](https://stacks.math.columbia.edu/tag/0H5D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The bound on the relative dimension of a base change of `p` does not depend on the fibre
product chosen to compute it, nor on an isomorphism of the base of the base change. -/
theorem relativeDimensionLE_of_isPullback_of_isIso {Z S T₁ T₂ A B : Scheme.{u}} {p : Z ⟶ S}
    {b₁ : T₁ ⟶ S} {b₂ : T₂ ⟶ S} {a₁ : A ⟶ Z} {f₁ : A ⟶ T₁} {a₂ : B ⟶ Z} {f₂ : B ⟶ T₂}
    [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂] (sq₁ : IsPullback a₁ f₁ p b₁)
    (sq₂ : IsPullback a₂ f₂ p b₂) (e : T₁ ⟶ T₂) (he : e ≫ b₂ = b₁) (d : ℕ)
    (h : RelativeDimensionLE f₂ d) : RelativeDimensionLE f₁ d := by
  have hsq : IsPullback (sq₂.lift a₁ (f₁ ≫ e) (by rw [Category.assoc, he, sq₁.w])) f₁ f₂ e := by
    refine IsPullback.of_right ?_ (sq₂.lift_snd _ _ _) sq₂
    rw [sq₂.lift_fst, he]
    exact sq₁
  exact RelativeDimensionLE.of_isPullback hsq h

/-- **Tag 0H3V for a scheme over a stage.** Let `D` be a cofiltered system of schemes with affine
transition morphisms and limit cone `c`, and let `p : W ⟶ D.obj i₀` be quasi-compact and locally
of finite type, with `D.obj i₀` quasi-compact. If the base change of `p` to the limit has relative
dimension at most `d`, then so has its base change to some later stage. -/
theorem exists_relativeDimensionLE_pullback_snd_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (c : Cone D) (hc : IsLimit c) (i₀ : I)
    {W : Scheme.{u}} (p : W ⟶ D.obj i₀) [CompactSpace (D.obj i₀)] [LocallyOfFiniteType p]
    [QuasiCompact p] (d : ℕ) (h : RelativeDimensionLE (pullback.snd p (c.π.app i₀)) d) :
    ∃ (i : I) (g : i ⟶ i₀), RelativeDimensionLE (pullback.snd p (D.map g)) d := by
  let X₀ : Over (D.obj i₀) := Over.mk p
  let Y₀ : Over (D.obj i₀) := Over.mk (𝟙 _)
  let f₀ : X₀ ⟶ Y₀ := Over.homMk p (Category.comp_id p)
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i₀))
  have : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType p)
  have : QuasiCompact f₀.left := inferInstanceAs (QuasiCompact p)
  have key {T : Scheme.{u}} (b : T ⟶ D.obj i₀) :
      IsPullback (pullback.snd b X₀.hom) (baseChangeMap b X₀ Y₀ f₀) p
        (pullback.snd b Y₀.hom) :=
    (baseChangeMap_isPullback b X₀ Y₀ f₀).flip
  have hiso {T : Scheme.{u}} (b : T ⟶ D.obj i₀) : IsIso (pullback.fst b Y₀.hom) := by
    change IsIso (pullback.fst b (𝟙 _))
    infer_instance
  have hinv' {T : Scheme.{u}} (b : T ⟶ D.obj i₀) :
      pullback.fst b Y₀.hom ≫ b = pullback.snd b Y₀.hom := by
    rw [pullback.condition]
    exact Category.comp_id (pullback.snd b Y₀.hom)
  have hlim : RelativeDimensionLE (baseChangeMap (c.π.app i₀) X₀ Y₀ f₀) d :=
    relativeDimensionLE_of_isPullback_of_isIso (key _) (IsPullback.of_hasPullback p _)
      (pullback.fst _ _) (hinv' _) d h
  obtain ⟨i, g, hg⟩ :=
    exists_relativeDimensionLE_baseChangeMap_of_isLimit D c hc i₀ X₀ Y₀ f₀ d hlim
  exact ⟨i, g, relativeDimensionLE_of_isPullback_of_isIso (IsPullback.of_hasPullback p _)
    (key _) (inv (pullback.fst _ _))
    ((IsIso.inv_comp_eq _).2 (hinv' _).symm) d hg⟩

end AlgebraicGeometry

open AlgebraicGeometry

namespace Stacks.Chow

/-- Two members of `Hilb(X/S, r)` with the same ideal sheaf are equal. -/
theorem HilbertCycleDatum.ext_ideal {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    {Z Z' : HilbertCycleDatum f r} (h : Z.ideal = Z'.ideal) : Z = Z' := by
  cases Z
  cases Z'
  cases h
  rfl

/-- A morphism `ρ : Y ⟶ T` of schemes over `S`, as a morphism of the slice over `S`. -/
abbrev overHom {S Y T : Scheme.{u}} (q : Y ⟶ S) (gT : T ⟶ S) (ρ : Y ⟶ T) (hρ : ρ ≫ gT = q) :
    Over.mk q ⟶ Over.mk gT :=
  Over.homMk ρ hρ

/-- The base change along `b : S' ⟶ S` of a morphism `ρ : Y ⟶ T` over `S` that is locally of
finite presentation is locally of finite presentation. -/
instance locallyOfFinitePresentation_baseChangeMap_overHom {S S' Y T : Scheme.{u}} (q : Y ⟶ S)
    (gT : T ⟶ S) (ρ : Y ⟶ T) (hρ : ρ ≫ gT = q) [LocallyOfFinitePresentation ρ] (b : S' ⟶ S) :
    LocallyOfFinitePresentation
      (AlgebraicGeometry.baseChangeMap b (Over.mk q) (Over.mk gT) (overHom q gT ρ hρ)) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
    (baseChangeMap_isPullback b _ _ (overHom q gT ρ hρ)).flip
      (inferInstanceAs (LocallyOfFinitePresentation ρ))

/-- The base change along `b : S' ⟶ S` of a quasi-compact morphism `ρ : Y ⟶ T` over `S` is
quasi-compact. -/
instance quasiCompact_baseChangeMap_overHom {S S' Y T : Scheme.{u}} (q : Y ⟶ S) (gT : T ⟶ S)
    (ρ : Y ⟶ T) (hρ : ρ ≫ gT = q) [QuasiCompact ρ] (b : S' ⟶ S) :
    QuasiCompact (AlgebraicGeometry.baseChangeMap b (Over.mk q) (Over.mk gT) (overHom q gT ρ hρ)) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact)
    (baseChangeMap_isPullback b _ _ (overHom q gT ρ hρ)).flip (inferInstanceAs (QuasiCompact ρ))

section Descent

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D) (hc : IsLimit c) {i : I} {Y T : Scheme.{u}}
  (q : Y ⟶ D.obj i) (gT : T ⟶ D.obj i) (ρ : Y ⟶ T) (hρ : ρ ≫ gT = q)
  [LocallyOfFinitePresentation ρ] [QuasiCompact ρ] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace T] [QuasiSeparatedSpace T] (r : ℕ)


omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **A member of `Hilb` over the limit comes from a finite stage.** Let `ρ : Y ⟶ T` be a
morphism of finite presentation of quasi-compact, quasi-separated schemes over the stage
`D.obj i`. Every member of `Hilb(S ×_{S_i} Y / S ×_{S_i} T, r)` is the inverse image, through the
cartesian square relating the base changes of `ρ` to the limit and to a later stage `a`, of a
member of `Hilb(S_a ×_{S_i} Y / S_a ×_{S_i} T, r)`. -/
theorem exists_hilbertCycleDatum_ofIsPullback_eq
    (Z : HilbertCycleDatum (AlgebraicGeometry.baseChangeMap (c.π.app i) (Over.mk q) (Over.mk gT)
      (overHom q gT ρ hρ)) r) :
    ∃ (a : Over i) (Z' : HilbertCycleDatum
        (AlgebraicGeometry.baseChangeMap (D.map a.hom) (Over.mk q) (Over.mk gT)
          (overHom q gT ρ hρ)) r),
      Z'.ofIsPullback (baseChangeCone_π_isPullback D i (overHom q gT ρ hρ) c a) = Z := by
  classical
  -- Notation: the two systems of base changes, their cones and the maps between them.
  let F := overHom q gT ρ hρ
  have : CompactSpace (Over.mk q).left := inferInstanceAs (CompactSpace Y)
  have : QuasiSeparatedSpace (Over.mk q).left := inferInstanceAs (QuasiSeparatedSpace Y)
  have : CompactSpace (Over.mk gT).left := inferInstanceAs (CompactSpace T)
  have : QuasiSeparatedSpace (Over.mk gT).left := inferInstanceAs (QuasiSeparatedSpace T)
  have : ∀ (X : Over (D.obj i)) {a b : Over i} (g : a ⟶ b),
      IsAffineHom ((baseChangeDiagram D i X).map g) :=
    fun X _ _ g => isAffineHom_baseChangeDiagram_map D i X g
  have : ∀ (X : Over (D.obj i)) [CompactSpace X.left] (a : Over i),
      CompactSpace ((baseChangeDiagram D i X).obj a) :=
    fun X _ a => compactSpace_baseChangeDiagram_obj D i X a
  have : ∀ (X : Over (D.obj i)) [QuasiSeparatedSpace X.left] (a : Over i),
      QuasiSeparatedSpace ((baseChangeDiagram D i X).obj a) :=
    fun X _ a => quasiSeparatedSpace_baseChangeDiagram_obj D i X a
  have hcY : IsLimit (baseChangeCone D c i (Over.mk q)) := baseChangeConeIsLimit D hc i _
  have hcT : IsLimit (baseChangeCone D c i (Over.mk gT)) := baseChangeConeIsLimit D hc i _
  have hρL : LocallyOfFinitePresentation (AlgebraicGeometry.baseChangeMap (c.π.app i) (Over.mk q)
      (Over.mk gT) F) := locallyOfFinitePresentation_baseChangeMap_overHom q gT ρ hρ _
  have hρA (a : Over i) : LocallyOfFinitePresentation
      ((baseChangeDiagramMap D i F).app a) :=
    locallyOfFinitePresentation_baseChangeMap_overHom q gT ρ hρ _
  have hρA' (a : Over i) : QuasiCompact ((baseChangeDiagramMap D i F).app a) :=
    quasiCompact_baseChangeMap_overHom q gT ρ hρ _
  -- The closed subscheme descends as an ideal sheaf of finite presentation.
  have hZlfp := Z.locallyFinitePresentation
  have : LocallyOfFinitePresentation Z.ideal.subschemeι :=
    locallyOfFinitePresentation_of_comp Z.ideal.subschemeι
      (AlgebraicGeometry.baseChangeMap (c.π.app i) (Over.mk q) (Over.mk gT) F)
  have hK : FinitePresentation Z.ideal.subschemeι :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨a, J, hJ, hJK⟩ := Stacks.Hilbert.exists_closed_model (baseChangeDiagram D i (Over.mk q))
    (baseChangeCone D c i (Over.mk q)) hcY Z.ideal hK
  have : MorphismProperty.RespectsIso @Flat := MorphismProperty.IsStableUnderBaseChange.respectsIso
  let πY : Limits.pullback (c.π.app i) (Over.mk q).hom ⟶
      (baseChangeDiagram D i (Over.mk q)).obj a :=
    (baseChangeCone D c i (Over.mk q)).π.app a
  let πT : Limits.pullback (c.π.app i) (Over.mk gT).hom ⟶
      (baseChangeDiagram D i (Over.mk gT)).obj a :=
    (baseChangeCone D c i (Over.mk gT)).π.app a
  have hJK' : J.comap πY = Z.ideal := hJK
  let W : J.subscheme ⟶ (baseChangeDiagram D i (Over.mk gT)).obj a :=
    J.subschemeι ≫ (baseChangeDiagramMap D i F).app a
  have : CompactSpace J.subscheme := QuasiCompact.compactSpace_of_compactSpace J.subschemeι
  have : QuasiSeparatedSpace J.subscheme :=
    quasiSeparatedSpace_of_quasiSeparated J.subschemeι
  have hWlfp : LocallyOfFinitePresentation W :=
    MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ hJ.1 (hρA a)
  have hWqc : QuasiCompact W := MorphismProperty.comp_mem @QuasiCompact _ _ hJ.2.1 (hρA' a)
  -- The square comparing the limit with the stage `a`.
  have sqB : IsPullback _ ((J.comap πY).subschemeι ≫
      AlgebraicGeometry.baseChangeMap (c.π.app i) (Over.mk q) (Over.mk gT) F) W
      πT :=
    (isPullback_comap_subschemeι J πY).paste_vert
      (baseChangeCone_π_isPullback D i F c a)
  have hflatL : Flat ((J.comap πY).subschemeι ≫
      AlgebraicGeometry.baseChangeMap (c.π.app i) (Over.mk q) (Over.mk gT) F) := by
    rw [hJK']
    exact Z.flat
  have hlftL : LocallyOfFiniteType ((J.comap πY).subschemeι ≫
      AlgebraicGeometry.baseChangeMap (c.π.app i) (Over.mk q) (Over.mk gT) F) := by
    rw [hJK']
    infer_instance
  have hdimL : RelativeDimensionLE ((J.comap πY).subschemeι ≫
      AlgebraicGeometry.baseChangeMap (c.π.app i) (Over.mk q) (Over.mk gT) F) r := by
    have := Z.relativeDimensionLE
    revert hlftL
    rw [hJK']
    intro
    exact this
  -- Flatness at a later stage (Tag 04AI).
  let G : Over.mk W ⟶ Over.mk (𝟙 ((baseChangeDiagram D i (Over.mk gT)).obj a)) :=
    Over.homMk W (Category.comp_id W)
  have hflatG : Flat ((Over.pullback ((baseChangeCone D c i (Over.mk gT)).π.app a)).map G).left :=
    (overPullback_map_homMk_left_iff @Flat W _).mpr
      ((prop_iff_of_isPullback (P := @Flat) (IsPullback.of_hasPullback W _) sqB).mpr hflatL)
  have : CompactSpace (Over.mk W).left := inferInstanceAs (CompactSpace J.subscheme)
  have : QuasiSeparatedSpace (Over.mk W).left := inferInstanceAs (QuasiSeparatedSpace J.subscheme)
  have : CompactSpace (Over.mk (𝟙 ((baseChangeDiagram D i (Over.mk gT)).obj a))).left :=
    inferInstanceAs (CompactSpace ((baseChangeDiagram D i (Over.mk gT)).obj a))
  have : QuasiSeparatedSpace (Over.mk (𝟙 ((baseChangeDiagram D i (Over.mk gT)).obj a))).left :=
    inferInstanceAs (QuasiSeparatedSpace ((baseChangeDiagram D i (Over.mk gT)).obj a))
  have : LocallyOfFinitePresentation G.left := hWlfp
  obtain ⟨b₁, g₁, hg₁⟩ := exists_flat_baseChange_of_limitBaseChange
    (baseChangeDiagram D i (Over.mk gT)) (baseChangeCone D c i (Over.mk gT)) a (Over.mk W)
    (Over.mk (𝟙 _)) G hcT
  have hg₁' : Flat (pullback.snd W ((baseChangeDiagram D i (Over.mk gT)).map g₁)) :=
    (overPullback_map_homMk_left_iff @Flat W _).mp hg₁
  -- The bound on the relative dimension at a later stage (Tag 0H3V).
  obtain ⟨b₂, g₂, hg₂⟩ := exists_relativeDimensionLE_pullback_snd_of_isLimit
    (baseChangeDiagram D i (Over.mk gT)) (baseChangeCone D c i (Over.mk gT)) hcT a W r
    (relativeDimensionLE_of_isPullback_of_isIso (IsPullback.of_hasPullback W _) sqB (𝟙 _)
      (Category.id_comp _) r hdimL)
  -- A common later stage.
  obtain ⟨b, m₁, m₂, hm⟩ := IsCofiltered.cospan g₁ g₂
  let g : b ⟶ a := m₁ ≫ g₁
  have hpb {x : Over i} (u : x ⟶ a) (m : b ⟶ x) (hu : m ≫ u = g) :
      IsPullback (pullback.fst (pullback.snd W ((baseChangeDiagram D i (Over.mk gT)).map u))
        ((baseChangeDiagram D i (Over.mk gT)).map m) ≫
          pullback.fst W ((baseChangeDiagram D i (Over.mk gT)).map u))
        (pullback.snd (pullback.snd W ((baseChangeDiagram D i (Over.mk gT)).map u))
          ((baseChangeDiagram D i (Over.mk gT)).map m)) W
        ((baseChangeDiagram D i (Over.mk gT)).map g) := by
    have hpb := isPullback_pullback_snd_comp W ((baseChangeDiagram D i (Over.mk gT)).map u)
      ((baseChangeDiagram D i (Over.mk gT)).map m)
    rwa [← (baseChangeDiagram D i (Over.mk gT)).map_comp, hu] at hpb
  have hflatb : Flat (pullback.snd W ((baseChangeDiagram D i (Over.mk gT)).map g)) :=
    (prop_iff_of_isPullback (P := @Flat) (IsPullback.of_hasPullback W _) (hpb g₁ m₁ rfl)).mpr
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hg₁')
  have hdimb :
      RelativeDimensionLE (pullback.snd W ((baseChangeDiagram D i (Over.mk gT)).map g)) r :=
    relativeDimensionLE_of_isPullback_of_isIso (IsPullback.of_hasPullback W _)
      (hpb g₂ m₂ hm.symm) (𝟙 _) (Category.id_comp _) r
      (RelativeDimensionLE.of_isPullback (IsPullback.of_hasPullback _ _) hg₂)
  -- The member of `Hilb` at the stage `b`.
  let Jb := J.comap ((baseChangeDiagram D i (Over.mk q)).map g)
  have sqC : IsPullback _ (Jb.subschemeι ≫ (baseChangeDiagramMap D i F).app b) W
      ((baseChangeDiagram D i (Over.mk gT)).map g) :=
    (isPullback_comap_subschemeι J ((baseChangeDiagram D i (Over.mk q)).map g)).paste_vert
      (baseChangeDiagramMap_isPullback D i F g)
  have hlftb : LocallyOfFiniteType (Jb.subschemeι ≫ (baseChangeDiagramMap D i F).app b) :=
    MorphismProperty.comp_mem @LocallyOfFiniteType _ _ inferInstance inferInstance
  let Z' : HilbertCycleDatum ((baseChangeDiagramMap D i F).app b) r :=
    { ideal := Jb
      flat := (prop_iff_of_isPullback (P := @Flat) (IsPullback.of_hasPullback W _) sqC).mp hflatb
      locallyFinitePresentation := MorphismProperty.of_isPullback sqC hWlfp
      quasiCompact := MorphismProperty.of_isPullback sqC hWqc
      relativeDimensionLE := relativeDimensionLE_of_isPullback_of_isIso sqC
        (IsPullback.of_hasPullback W _) (𝟙 _) (Category.id_comp _) r hdimb }
  refine ⟨b, Z', HilbertCycleDatum.ext_ideal ?_⟩
  refine (HilbertCycleDatum.ofIsPullback_ideal Z' _).trans ?_
  rw [← hJK]
  change (J.comap ((baseChangeDiagram D i (Over.mk q)).map g)).comap
    ((baseChangeCone D c i (Over.mk q)).π.app b) =
      J.comap ((baseChangeCone D c i (Over.mk q)).π.app a)
  rw [← Scheme.IdealSheafData.comap_comp, (baseChangeCone D c i (Over.mk q)).w g]

omit [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] [IsCofiltered I] [LocallyOfFinitePresentation ρ]
  [QuasiCompact ρ] [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace T]
  [QuasiSeparatedSpace T] in
/-- The inverse image of a member of `Hilb` at a stage `a`, first to a later stage `b` and then
to the limit, is its inverse image to the limit. -/
theorem ofIsPullback_baseChangeDiagramMap_ofIsPullback {a b : Over i} (g : b ⟶ a)
    (Z : HilbertCycleDatum (AlgebraicGeometry.baseChangeMap (D.map a.hom) _ _
      (overHom q gT ρ hρ)) r) :
    (Z.ofIsPullback (baseChangeDiagramMap_isPullback D i (overHom q gT ρ hρ) g)).ofIsPullback
        (baseChangeCone_π_isPullback D i (overHom q gT ρ hρ) c b) =
      Z.ofIsPullback (baseChangeCone_π_isPullback D i (overHom q gT ρ hρ) c a) := by
  refine HilbertCycleDatum.ext_ideal ?_
  refine (HilbertCycleDatum.ofIsPullback_ideal _ _).trans ?_
  refine (congrArg (fun I => Scheme.IdealSheafData.comap I _)
    (HilbertCycleDatum.ofIsPullback_ideal _ _)).trans ?_
  refine Eq.trans ?_ (HilbertCycleDatum.ofIsPullback_ideal _ _).symm
  exact (Scheme.IdealSheafData.comap_comp Z.ideal ((baseChangeCone D c i (Over.mk q)).π.app b)
    ((baseChangeDiagram D i (Over.mk q)).map g)).symm.trans
      (congrArg Z.ideal.comap ((baseChangeCone D c i (Over.mk q)).w g))

omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **An element of the free abelian group on `Hilb` over the limit comes from a finite
stage.** In the situation of `Stacks.Chow.exists_hilbertCycleDatum_ofIsPullback_eq`, every
element of the free abelian group on `Hilb(S ×_{S_i} Y / S ×_{S_i} T, r)` is the image, under
inverse image through the cartesian square of a later stage `a`, of an element of the free
abelian group on `Hilb(S_a ×_{S_i} Y / S_a ×_{S_i} T, r)`. -/
theorem exists_map_ofIsPullback_eq
    (C : FreeAbelianGroup (HilbertCycleDatum
      (AlgebraicGeometry.baseChangeMap (c.π.app i) _ _ (overHom q gT ρ hρ)) r)) :
    ∃ (a : Over i) (C' : FreeAbelianGroup (HilbertCycleDatum
        (AlgebraicGeometry.baseChangeMap (D.map a.hom) _ _ (overHom q gT ρ hρ)) r)),
      FreeAbelianGroup.map
        (fun Z ↦ Z.ofIsPullback (baseChangeCone_π_isPullback D i (overHom q gT ρ hρ) c a)) C' =
        C := by
  induction C using FreeAbelianGroup.induction_on with
  | zero => exact ⟨Over.mk (𝟙 i), 0, map_zero _⟩
  | of Z =>
    obtain ⟨a, Z', hZ'⟩ := exists_hilbertCycleDatum_ofIsPullback_eq D c hc q gT ρ hρ r Z
    exact ⟨a, FreeAbelianGroup.of Z', (FreeAbelianGroup.map_of_apply _).trans (congrArg _ hZ')⟩
  | neg Z h =>
    obtain ⟨a, C', hC'⟩ := h
    exact ⟨a, -C', (map_neg _ _).trans (congrArg _ hC')⟩
  | add C₁ C₂ h₁ h₂ =>
    obtain ⟨a₁, C₁', hC₁'⟩ := h₁
    obtain ⟨a₂, C₂', hC₂'⟩ := h₂
    let b := IsCofiltered.min a₁ a₂
    let m₁ := IsCofiltered.minToLeft a₁ a₂
    let m₂ := IsCofiltered.minToRight a₁ a₂
    refine ⟨b, FreeAbelianGroup.map
        (fun Z ↦ Z.ofIsPullback (baseChangeDiagramMap_isPullback D i (overHom q gT ρ hρ) m₁)) C₁' +
      FreeAbelianGroup.map
        (fun Z ↦ Z.ofIsPullback (baseChangeDiagramMap_isPullback D i (overHom q gT ρ hρ) m₂)) C₂',
      ?_⟩
    refine (map_add _ _ _).trans ?_
    refine congrArg₂ (· + ·) ((FreeAbelianGroup.map_comp_apply _).symm.trans ?_)
      ((FreeAbelianGroup.map_comp_apply _).symm.trans ?_)
    · refine Eq.trans ?_ hC₁'
      congr 2
      funext Z
      exact ofIsPullback_baseChangeDiagramMap_ofIsPullback D c q gT ρ hρ r m₁ Z
    · refine Eq.trans ?_ hC₂'
      congr 2
      funext Z
      exact ofIsPullback_baseChangeDiagramMap_ofIsPullback D c q gT ρ hρ r m₂ Z

end Descent

end Stacks.Chow

end
