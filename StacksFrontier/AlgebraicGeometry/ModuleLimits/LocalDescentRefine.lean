module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentAffine
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentStage
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ColimitReindex
public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Descent of morphisms of finitely presented modules along a cofiltered limit of schemes

Let `D : I ⥤ Scheme` be a cofiltered diagram with affine transition morphisms and limit cone `c`,
and let `F`, `G` be sheaves of modules of finite presentation on a quasi-compact quasi-separated
stage `D.obj i`. A morphism between the pullbacks of `F` and `G` to the limit is, at some later
stage, the base change of a morphism there. It follows that, given that filtered colimits of
quasi-coherent modules of finite presentation behave as in
`Stacks.AlgebraicGeometry.ModuleLimits.QcohFilteredColimitFinitePresentation`, every module of
finite presentation on the limit comes from a stage.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_finite_affineOpen_cover`: a quasi-compact scheme
  has a finite cover by affine opens, indexed by a type in the scheme's own universe.
* `Stacks.AlgebraicGeometry.ModuleLimits.valSections_stageTransport_agree`: agreement of two data
  on the overlap of their opens survives a transport to a later stage.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_common_stage_localDescent` and
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_common_stage_localDescent_cover`: one stage
  carrying a local descent datum over the preimage of every member of a finite affine cover.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_localDescent_agree_on` and
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_localDescent_cover_agree`: one stage whose
  data agree on every overlap.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_canonical_eq_of_isLimit`: a morphism between the
  pullbacks to the limit is, at a later stage, the base change of a morphism, through
  `Stacks.AlgebraicGeometry.ModuleLimits.canHom`.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_upToIso_of_isLimit` and
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_upToIso_of_isLimit'`: the same
  up to some identifications of the pullbacks.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_filteredColim`
  and its primed form: given `QcohFilteredColimitFinitePresentation`, every module of finite
  presentation on the limit is the pullback of a module of finite presentation on some stage.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 01PJ](https://stacks.math.columbia.edu/tag/01PJ)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- A quasi-compact scheme is covered by finitely many affine opens, indexed by a type in the
scheme's own universe. -/
theorem exists_finite_affineOpen_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.Opens),
      (∀ a, IsAffineOpen (V a)) ∧ ∀ x : X, ∃ a, x ∈ V a := by
  obtain ⟨s, hs, hu⟩ :=
    AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
      (X := X) (U := (Set.univ : Set X)) |>.mp ⟨isCompact_univ, isOpen_univ⟩
  refine ⟨{U : X.affineOpens // U ∈ s}, hs.to_subtype, fun a ↦ a.1.1, fun a ↦ a.1.2,
    fun x ↦ ?_⟩
  obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.mp (hu ▸ Set.mem_univ x)
  exact ⟨⟨U, hU⟩, hxU⟩

section Agree

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})

/-- Two data over the preimages of two opens `Va`, `Vb` of the stage `i` whose sectionwise
families agree over every open contained in both continue to agree after
`Stacks.AlgebraicGeometry.ModuleLimits.stageTransport` along a morphism of stages. -/
theorem valSections_stageTransport_agree {i : I} {k k' : Over i} (p : k' ⟶ k)
    {F G : (D.obj i).Modules} {Va Vb : (D.obj i).Opens}
    (Θa : Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
          (D.map k.hom ⁻¹ᵁ Va : (D.obj k.left).Opens).ι ⟶
        Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
          (D.map k.hom ⁻¹ᵁ Va : (D.obj k.left).Opens).ι)
    (Θb : Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
          (D.map k.hom ⁻¹ᵁ Vb : (D.obj k.left).Opens).ι ⟶
        Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
          (D.map k.hom ⁻¹ᵁ Vb : (D.obj k.left).Opens).ι)
    (h : ∀ (W : (D.obj k.left).Opens)
      (hwa : W ≤ (D.map k.hom ⁻¹ᵁ Va : (D.obj k.left).Opens))
      (hwb : W ≤ (D.map k.hom ⁻¹ᵁ Vb : (D.obj k.left).Opens))
      (m : ((Scheme.Modules.pullback (D.map k.hom)).obj F).val.obj (op W)),
      valSections Θa W hwa m = valSections Θb W hwb m)
    (W : (D.obj k'.left).Opens)
    (hwa : W ≤ (D.map k'.hom ⁻¹ᵁ Va : (D.obj k'.left).Opens))
    (hwb : W ≤ (D.map k'.hom ⁻¹ᵁ Vb : (D.obj k'.left).Opens))
    (m : ((Scheme.Modules.pullback (D.map k'.hom)).obj F).val.obj (op W)) :
    valSections (stageTransport D p Θa) W hwa m
      = valSections (stageTransport D p Θb) W hwb m := by
  have hRa := Scheme.Hom.preimage_mono (D.map k.hom) (inf_le_left : Va ⊓ Vb ≤ Va)
  have hRb := Scheme.Hom.preimage_mono (D.map k.hom) (inf_le_right : Va ⊓ Vb ≤ Vb)
  have hWa := (preimage_map_left D p Va).le
  have hWb := (preimage_map_left D p Vb).le
  have hWR := (preimage_map_left D p (Va ⊓ Vb)).le
  have hR'a := Scheme.Hom.preimage_mono (D.map k'.hom) (inf_le_left : Va ⊓ Vb ≤ Va)
  have hR'b := Scheme.Hom.preimage_mono (D.map k'.hom) (inf_le_right : Va ⊓ Vb ≤ Vb)
  have hWR' : W ≤ (D.map k'.hom ⁻¹ᵁ (Va ⊓ Vb) : (D.obj k'.left).Opens) := le_inf hwa hwb
  have hΘ : restrictTo hRa Θa = restrictTo hRb Θb := by
    refine restrictSections_ext fun U hU y ↦ ?_
    rw [restrictSections_eq_valSections (restrictTo hRa Θa) U hU y,
      restrictSections_eq_valSections (restrictTo hRb Θb) U hU y,
      valSections_restrictTo hRa Θa U hU y, valSections_restrictTo hRb Θb U hU y]
    exact h U (hU.trans hRa) (hU.trans hRb) y
  have hbr : pullbackRestrictHom (D.map p.left) hWR (restrictTo hRa Θa)
      = pullbackRestrictHom (D.map p.left) hWR (restrictTo hRb Θb) :=
    congrArg (pullbackRestrictHom (D.map p.left) hWR) hΘ
  have hta := restrictTo_pullbackRestrictHom (D.map p.left) hRa hWa hWR hR'a Θa
  have htb := restrictTo_pullbackRestrictHom (D.map p.left) hRb hWb hWR hR'b Θb
  have hsec : valSections (pullbackRestrictHom (D.map p.left) hWa Θa) W hwa
        ((inv (canHom (D.map p.left) (D.map k.hom) (D.map k'.hom) (map_left_comp D p)
          F)).val.app (op W) m)
      = valSections (pullbackRestrictHom (D.map p.left) hWb Θb) W hwb
        ((inv (canHom (D.map p.left) (D.map k.hom) (D.map k'.hom) (map_left_comp D p)
          F)).val.app (op W) m) := by
    rw [← valSections_restrictTo hR'a (pullbackRestrictHom (D.map p.left) hWa Θa) W hWR',
      ← valSections_restrictTo hR'b (pullbackRestrictHom (D.map p.left) hWb Θb) W hWR',
      hta, htb, hbr]
  unfold stageTransport transportRestrictHom
  simp only [valSections_comp, valSections_restrictFunctor_map, hsec]

end Agree

section Refine

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- Given finitely many affine opens `V a` of the stage `i`, some later stage carries a local
descent datum of `φ` over the preimage of each `V a`. -/
theorem exists_common_stage_localDescent (hc : IsLimit c) (i : I)
    {ι : Type u} [Finite ι] (V : ι → (D.obj i).Opens) (hV : ∀ a, IsAffineOpen (V a))
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (k : Over i)
      (Θ : ∀ a : ι, Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
            (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens).ι ⟶
          Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
            (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens).ι),
      ∀ a : ι, LocalDescent (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) φ
        (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens) (Θ a) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  choose kk ΘΘ hΘΘ using fun a : ι ↦
    exists_localDescent_of_isAffineOpen D c hc i (hV a) F G φ
  obtain ⟨S, hS⟩ :=
    CategoryTheory.IsCofiltered.inf_objs_exists (Finset.image kk (Finset.univ : Finset ι))
  have p : ∀ a : ι, S ⟶ kk a := fun a ↦
    (hS (Finset.mem_image_of_mem kk (Finset.mem_univ a))).some
  exact ⟨S, fun a ↦ stageTransport D (p a) (ΘΘ a),
    fun a ↦ localDescent_stageTransport D c (p a) (ΘΘ a) (hΘΘ a)⟩

/-- For a quasi-compact stage `i`, there are a finite family of affine opens `V a` of `D.obj i`
and a later stage carrying a local descent datum of `φ` over the preimage of each `V a`, these
preimages covering the later stage. -/
theorem exists_common_stage_localDescent_cover (hc : IsLimit c) (i : I)
    [CompactSpace (D.obj i)]
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → (D.obj i).Opens) (k : Over i)
      (Θ : ∀ a : ι, Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
            (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens).ι ⟶
          Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
            (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens).ι),
      (∀ a, IsAffineOpen (V a)) ∧
        (∀ x : D.obj k.left, ∃ a, x ∈ (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens)) ∧
          ∀ a : ι, LocalDescent (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) φ
            (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens) (Θ a) := by
  obtain ⟨ι, hι, V, hVaff, hVcov⟩ := exists_finite_affineOpen_cover (D.obj i)
  obtain ⟨k, Θ, hΘ⟩ := exists_common_stage_localDescent D c hc i V hVaff F G φ
  exact ⟨ι, hι, V, k, Θ, hVaff, fun x ↦ hVcov ((D.map k.hom).base x), hΘ⟩

/-- Given local descent data over the preimages of a family of affine opens of a quasi-separated
stage `i`, all at one stage, a later stage carries local descent data that agree on the overlaps
of every pair in a given finite set of pairs. -/
theorem exists_stage_localDescent_agree_on (hc : IsLimit c) (i : I)
    [QuasiSeparatedSpace (D.obj i)]
    {ι : Type u} (V : ι → (D.obj i).Opens) (hV : ∀ a, IsAffineOpen (V a))
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G)
    (s : Finset (ι × ι)) (k : Over i)
    (Θ : ∀ a : ι, Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
          (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens).ι ⟶
        Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
          (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens).ι)
    (hΘ : ∀ a : ι, LocalDescent (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) φ
      (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens) (Θ a)) :
    ∃ (k' : Over i)
      (Θ' : ∀ a : ι, Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k'.hom)).obj F)
            (D.map k'.hom ⁻¹ᵁ V a : (D.obj k'.left).Opens).ι ⟶
          Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k'.hom)).obj G)
            (D.map k'.hom ⁻¹ᵁ V a : (D.obj k'.left).Opens).ι),
      (∀ a : ι, LocalDescent (c.π.app k'.left) (D.map k'.hom) (c.π.app i) (c.w k'.hom) φ
          (D.map k'.hom ⁻¹ᵁ V a : (D.obj k'.left).Opens) (Θ' a)) ∧
        ∀ ab ∈ s, ∀ (W : (D.obj k'.left).Opens)
          (hwa : W ≤ (D.map k'.hom ⁻¹ᵁ V ab.1 : (D.obj k'.left).Opens))
          (hwb : W ≤ (D.map k'.hom ⁻¹ᵁ V ab.2 : (D.obj k'.left).Opens))
          (m : ((Scheme.Modules.pullback (D.map k'.hom)).obj F).val.obj (op W)),
          valSections (Θ' ab.1) W hwa m = valSections (Θ' ab.2) W hwb m := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => exact ⟨k, Θ, hΘ, by simp⟩
  | @insert ab s _ ih =>
    obtain ⟨k₁, Θ₁, hΘ₁, hag₁⟩ := ih k Θ hΘ
    have hqc : IsCompact ((V ab.1 ⊓ V ab.2 : (D.obj i).Opens) : Set (D.obj i)) := by
      rw [TopologicalSpace.Opens.coe_inf]
      exact QuasiSeparatedSpace.inter_isCompact _ _ (V ab.1).isOpen (hV ab.1).isCompact
        (V ab.2).isOpen (hV ab.2).isCompact
    obtain ⟨k₂, p, hnew⟩ := exists_stage_valSections_eq D c hc i hqc F G φ k₁
      (Θ₁ ab.1) (Θ₁ ab.2) (hΘ₁ ab.1) (hΘ₁ ab.2)
    refine ⟨k₂, fun a ↦ stageTransport D p (Θ₁ a),
      fun a ↦ localDescent_stageTransport D c p (Θ₁ a) (hΘ₁ a), fun cd hcd W hwa hwb m ↦ ?_⟩
    rcases Finset.mem_insert.mp hcd with rfl | hcd
    · exact hnew W hwa hwb m
    · exact valSections_stageTransport_agree D p (Θ₁ cd.1) (Θ₁ cd.2) (hag₁ cd hcd) W hwa hwb m

/-- For a quasi-compact quasi-separated stage `i`, some later stage carries local descent data
of `φ` over the preimages of a finite affine cover of `D.obj i`, which cover the later stage and
agree on every overlap. -/
theorem exists_stage_localDescent_cover_agree (hc : IsLimit c) (i : I)
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (F G : (D.obj i).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (ι : Type u) (V : ι → (D.obj i).Opens) (k : Over i)
      (Θ : ∀ a : ι, Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj F)
            (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens).ι ⟶
          Scheme.Modules.restrict ((Scheme.Modules.pullback (D.map k.hom)).obj G)
            (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens).ι),
      (∀ x : D.obj k.left, ∃ a, x ∈ (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens)) ∧
        (∀ a : ι, LocalDescent (c.π.app k.left) (D.map k.hom) (c.π.app i) (c.w k.hom) φ
            (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens) (Θ a)) ∧
          ∀ (a b : ι) (W : (D.obj k.left).Opens)
            (hwa : W ≤ (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens))
            (hwb : W ≤ (D.map k.hom ⁻¹ᵁ V b : (D.obj k.left).Opens))
            (m : ((Scheme.Modules.pullback (D.map k.hom)).obj F).val.obj (op W)),
            valSections (Θ a) W hwa m = valSections (Θ b) W hwb m := by
  classical
  obtain ⟨ι, hι, V, hVaff, hVcov⟩ := exists_finite_affineOpen_cover (D.obj i)
  obtain ⟨k₁, Θ₁, hΘ₁⟩ := exists_common_stage_localDescent D c hc i V hVaff F G φ
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨k, Θ, hΘ, hag⟩ := exists_stage_localDescent_agree_on D c hc i V hVaff F G φ
    (Finset.univ : Finset (ι × ι)) k₁ Θ₁ hΘ₁
  exact ⟨ι, V, k, Θ, fun x ↦ hVcov ((D.map k.hom).base x), hΘ,
    fun a b ↦ hag (a, b) (Finset.mem_univ _)⟩

/-- A morphism between the pullbacks to the limit of two sheaves of modules of finite
presentation on a quasi-compact quasi-separated stage is, at some later stage, the base change of
a morphism there, through the canonical identification
`Stacks.AlgebraicGeometry.ModuleLimits.canHom`. -/
theorem exists_canonical_eq_of_isLimit (hc : IsLimit c) (i : I)
    [CompactSpace (D.obj i)] [QuasiSeparatedSpace (D.obj i)]
    (F G : (D.obj i).Modules)
    (hF : F.IsFinitePresentation) (hG : G.IsFinitePresentation)
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i) (Φ : (Scheme.Modules.pullback (D.map e)).obj F ⟶
        (Scheme.Modules.pullback (D.map e)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map Φ ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) G
        = canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) F ≫ φ := by
  have := hF
  have := hG
  obtain ⟨ι, V, k, Θ, hcov, hΘ, hag⟩ :=
    exists_stage_localDescent_cover_agree D c hc i F G φ
  obtain ⟨Φ, hΦ⟩ := exists_canonical_eq_of_cover (c.π.app k.left) (D.map k.hom)
    (c.π.app i) (c.w k.hom) φ (fun a ↦ (D.map k.hom ⁻¹ᵁ V a : (D.obj k.left).Opens))
    hcov Θ hΘ hag
  exact ⟨k.left, k.hom, Φ, hΦ⟩

/-- For a cofiltered system of quasi-compact quasi-separated schemes with affine transition
morphisms, a morphism between the pullbacks to the limit of two sheaves of modules of finite
presentation on a stage is, at some later stage, the base change of a morphism there, up to
isomorphisms of the pullbacks. -/
theorem exists_map_of_pullback_upToIso_of_isLimit (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (F G : (D.obj i).Modules)
    (hF : F.IsFinitePresentation) (hG : G.IsFinitePresentation)
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i) (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
      (Scheme.Modules.pullback (D.map e)).obj G)
      (iF : (Scheme.Modules.pullback (c.π.app j)).obj
            ((Scheme.Modules.pullback (D.map e)).obj F) ≅
          (Scheme.Modules.pullback (c.π.app i)).obj F)
      (iG : (Scheme.Modules.pullback (c.π.app j)).obj
            ((Scheme.Modules.pullback (D.map e)).obj G) ≅
          (Scheme.Modules.pullback (c.π.app i)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map φj ≫ iG.hom = iF.hom ≫ φ := by
  obtain ⟨j, e, Φ, hΦ⟩ := exists_canonical_eq_of_isLimit D c hc i F G hF hG φ
  exact ⟨j, e, Φ,
    asIso (canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) F),
    asIso (canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) G), hΦ⟩

/-- For a cofiltered system of quasi-compact quasi-separated schemes with affine transition
morphisms, given `QcohFilteredColimitFinitePresentation`, every sheaf of modules of finite
presentation on the limit is the pullback of a sheaf of modules of finite presentation on some
stage. -/
theorem exists_isFinitePresentation_pullback_iso_of_filteredColim (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (hfilt : QcohFilteredColimitFinitePresentation.{u})
    (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) :=
  exists_isFinitePresentation_pullback_iso_of_filteredColim_and_upToIso_map D c hc hfilt
    (exists_map_of_pullback_upToIso_of_isLimit D c hc) F

end Refine

section IndexUniverse

open CategoryTheory.Functor CategoryTheory.Functor.FullImage

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)


/-- `exists_map_of_pullback_upToIso_of_isLimit` for an index category whose morphisms live in an
arbitrary universe. -/
theorem exists_map_of_pullback_upToIso_of_isLimit' (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (F G : (D.obj i).Modules)
    (hF : F.IsFinitePresentation) (hG : G.IsFinitePresentation)
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj F ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj G) :
    ∃ (j : I) (e : j ⟶ i) (φj : (Scheme.Modules.pullback (D.map e)).obj F ⟶
      (Scheme.Modules.pullback (D.map e)).obj G)
      (iF : (Scheme.Modules.pullback (c.π.app j)).obj
            ((Scheme.Modules.pullback (D.map e)).obj F) ≅
          (Scheme.Modules.pullback (c.π.app i)).obj F)
      (iG : (Scheme.Modules.pullback (c.π.app j)).obj
            ((Scheme.Modules.pullback (D.map e)).obj G) ≅
          (Scheme.Modules.pullback (c.π.app i)).obj G),
      (Scheme.Modules.pullback (c.π.app j)).map φj ≫ iG.hom = iF.hom ≫ φ := by
  obtain ⟨j, e, φj, iF, iG, hφ⟩ := exists_map_of_pullback_upToIso_of_isLimit
    (ι D) (cone D c) (isLimitCone D hc) ⟨i⟩ F G hF hG φ
  refine ⟨j.as, hom D e, ?_⟩
  rw [map_hom D e]
  exact ⟨φj, iF, iG, hφ⟩

/-- `exists_isFinitePresentation_pullback_iso_of_filteredColim` for an index category whose
morphisms live in an arbitrary universe. -/
theorem exists_isFinitePresentation_pullback_iso_of_filteredColim' (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (hfilt : QcohFilteredColimitFinitePresentation.{u})
    (F : c.pt.Modules) [F.IsFinitePresentation] :
    ∃ (i : I) (Fᵢ : (D.obj i).Modules),
      Fᵢ.IsFinitePresentation ∧
        Nonempty (F ≅ (Scheme.Modules.pullback (c.π.app i)).obj Fᵢ) :=
  exists_isFinitePresentation_pullback_iso_of_filteredColim_and_upToIso_map D c hc hfilt
    (exists_map_of_pullback_upToIso_of_isLimit' D c hc) F

end IndexUniverse

end Stacks.AlgebraicGeometry.ModuleLimits

end
