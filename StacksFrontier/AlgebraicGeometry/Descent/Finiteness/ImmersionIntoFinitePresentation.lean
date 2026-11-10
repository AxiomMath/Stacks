module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.Extension.Generators
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Induction
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian

/-!
# Immersing a finite type scheme into one of finite presentation

Let `f : X ⟶ S` be a morphism locally of finite type with `X` quasi-compact and
quasi-separated.  This file produces a scheme `X'` of finite presentation over `S` together
with an immersion `X ⟶ X'` over `S`.

The construction is the one of the source.  Noetherian approximation writes `X` as the
inverse limit of a directed system of schemes `D j` of finite type over `Spec ℤ` with affine
transition morphisms.  A finite affine open cover `V` of `X`, each member mapping into an
affine open of `S`, comes from one stage `i` of that system, and the finitely many algebra
generators of each chart `Γ(V j)` over `Γ(S, U j)` are global sections of affine opens of the
limit, so they all descend to one common stage `k`.  The candidate is then
`X' = D k ×_{Spec ℤ} S`: it is of finite presentation over `S` because `D k ⟶ Spec ℤ` is of
finite type over a Noetherian base and finite presentation is stable under base change, and
the canonical morphism `X ⟶ X'` is a closed immersion over each chart because the descended
generators generate.  Being an immersion is Zariski local on the target, so these local closed
immersions assemble.

## Main results

* `AlgebraicGeometry.exists_finitePresentation_isImmersion`: the immersion of `X` into a
  scheme of finite presentation over `S`.

## Implementation notes

The terminal scheme is replaced by `Spec (ULift ℤ)` throughout, via
`AlgebraicGeometry.specULiftZIsTerminal`, because the base change defining `X'` must be taken
over an honestly Noetherian affine scheme.  Finite presentation of a morphism is
`AlgebraicGeometry.FinitePresentation`, the conjunction of
`AlgebraicGeometry.LocallyOfFinitePresentation`, `AlgebraicGeometry.QuasiCompact` and
`AlgebraicGeometry.QuasiSeparated`.

## References

* [Stacks Project, Tag 01ZE](https://stacks.math.columbia.edu/tag/01ZE)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- The integers, viewed as the affine base over which Noetherian approximation takes place. -/
private abbrev integersBase : Scheme.{u} := Spec (CommRingCat.of (ULift.{u} ℤ))

private instance : IsNoetherianRing (ULift.{u} ℤ) :=
  isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm

/-- **Noetherian approximation of a quasi-compact, quasi-separated scheme.**  This is
[Stacks, Tag 07RN] applied to the empty open subscheme, which is the inverse limit of the
constant one-object system on itself, so that the conclusion constrains nothing and the
approximation is of `X` alone. -/
private def finiteTypeApproximationBot (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] :
    Scheme.FiniteTypeApproximation
      ((Functor.const PUnit.{u + 1}ᵒᵈ).obj ((⊥ : X.Opens) : Scheme.{u}))
      X (⊥ : X.Opens) (𝟙 _) := by
  let D : PUnit.{u + 1}ᵒᵈ ⥤ Scheme.{u} :=
    (Functor.const PUnit.{u + 1}ᵒᵈ).obj ((⊥ : X.Opens) : Scheme.{u})
  let c : Cone D := Cone.mk ((⊥ : X.Opens) : Scheme.{u}) (𝟙 _)
  have : IsEmpty ((⊥ : X.Opens) : Scheme.{u}) := ⟨fun x => x.2⟩
  have : ∀ i : PUnit.{u + 1}ᵒᵈ, LocallyOfFiniteType (terminal.from (D.obj i)) := fun _ =>
    inferInstanceAs (LocallyOfFiniteType (terminal.from ((⊥ : X.Opens) : Scheme.{u})))
  have : ∀ i : PUnit.{u + 1}ᵒᵈ, QuasiCompact (terminal.from (D.obj i)) := by
    intro i
    cases i
    refine ⟨fun V _ _ => ?_⟩
    have : IsEmpty (D.obj PUnit.unit) :=
      inferInstanceAs (IsEmpty ((⊥ : X.Opens) : Scheme.{u}))
    exact Set.eq_empty_of_isEmpty (terminal.from (D.obj PUnit.unit) ⁻¹' V) ▸ isCompact_empty
  have hc : IsLimit c :=
    { lift := fun s => s.π.app PUnit.unit
      fac := fun _ _ => Category.comp_id _
      uniq := by
        intro s m _
        have : IsEmpty (D.obj PUnit.unit) :=
          inferInstanceAs (IsEmpty ((⊥ : X.Opens) : Scheme.{u}))
        have : IsEmpty s.pt := ⟨fun x => isEmptyElim ((s.π.app PUnit.unit).base x)⟩
        exact (isInitialOfIsEmpty : IsInitial s.pt).hom_ext m (s.π.app PUnit.unit) }
  exact finiteTypeApproximationOfIsLimit D X (⊥ : X.Opens) (𝟙 _) hc

/-- A scheme quasi-compact and locally of finite type over the integers is quasi-compact and
quasi-separated: it is locally Noetherian, hence quasi-separated, and quasi-compactness of its
structural morphism is compactness of its space. -/
@[ega "IV 1.2.8" "special case"]
private theorem compactSpace_and_quasiSeparatedSpace_of_locallyOfFiniteType {Y : Scheme.{u}}
    (g : Y ⟶ integersBase.{u}) [LocallyOfFiniteType g] [QuasiCompact (terminal.from Y)] :
    CompactSpace Y ∧ QuasiSeparatedSpace Y :=
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  ⟨(quasiCompact_iff_compactSpace (terminal.from Y)).mp inferInstance, inferInstance⟩

/-- The base change to `S` of a quasi-compact morphism locally of finite type to the integers is
of finite presentation: over a Noetherian base finite type implies finite presentation, which is
stable under base change. -/
private theorem finitePresentation_pullback_snd {Y S : Scheme.{u}} (g : Y ⟶ integersBase.{u})
    [LocallyOfFiniteType g] [QuasiCompact g] (h : S ⟶ integersBase.{u}) :
    FinitePresentation (pullback.snd g h) := by
  obtain ⟨hlfp, hqc, hqs⟩ := finitePresentation_of_finiteType g
  have : LocallyOfFinitePresentation g := hlfp
  have : QuasiSeparated g := hqs
  exact FinitePresentation.mk inferInstance inferInstance inferInstance

/-- **Being an immersion is Zariski local on the target.**  A morphism which restricts to a
closed immersion over each member of a family of opens covering the image is an immersion. -/
private theorem isImmersion_of_isClosedImmersion_resLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    {ι : Type*} (U : ι → Y.Opens) (hcover : ∀ x : X, ∃ i, f x ∈ U i)
    (hclosed : ∀ i, IsClosedImmersion (f.resLE (U i) (f ⁻¹ᵁ U i) le_rfl)) : IsImmersion f := by
  have : MorphismProperty.RespectsRight (@IsImmersion) (@IsOpenImmersion) :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  have : MorphismProperty.HasOfPostcompProperty (@IsImmersion) (@IsOpenImmersion) :=
    ⟨fun p i _ hpi => MorphismProperty.HasOfPostcompProperty.of_postcomp
      (W := @IsImmersion) (W' := (⊤ : MorphismProperty Scheme)) p i trivial hpi⟩
  apply IsZariskiLocalAtTarget.of_forall_source_exists_preimage (P := @IsImmersion) f
  intro x
  obtain ⟨i, hx⟩ := hcover x
  refine ⟨U i, hx, ?_⟩
  have : IsClosedImmersion (f.resLE (U i) (f ⁻¹ᵁ U i) le_rfl) := hclosed i
  have hcomp : IsImmersion (f.resLE (U i) (f ⁻¹ᵁ U i) le_rfl ≫ (U i).ι) := inferInstance
  simpa only [Scheme.Hom.resLE_comp_ι] using hcomp

/-- An algebra whose structure map is of finite type admits a finite family of generators. -/
private theorem exists_generators_of_finiteType_algebraMap {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] (h : RingHom.FiniteType (algebraMap R A)) :
    ∃ n, Nonempty (Algebra.Generators R A (Fin n)) :=
  have : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp h
  Algebra.FiniteType.iff_exists_generators.mp inferInstance

/-- An algebra map hitting a generating family is surjective. -/
private theorem surjective_of_generators_in_range {R C A : Type*} [CommRing R] [CommRing C]
    [CommRing A] [Algebra R C] [Algebra R A] (ψ : C →ₐ[R] A) {n : ℕ}
    (P : Algebra.Generators R A (Fin n)) (hgen : ∀ i, ∃ c : C, ψ c = P.val i) :
    Function.Surjective ψ := by
  have hp : Algebra.adjoin R (Set.range P.val) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact (AlgHom.range_eq_top _).2 P.aeval_val_surjective
  have hmem : Set.range P.val ⊆ ψ.range := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := hgen i
    exact ⟨c, hc⟩
  refine (AlgHom.range_eq_top ψ).mp (top_unique ?_)
  rw [← hp]
  exact Algebra.adjoin_le_iff.mpr hmem

/-- A quasi-compact scheme over `S` has a finite affine open cover each of whose members maps
into an affine open of `S`. -/
private theorem exists_finite_affine_open_cover_subordinate {X S : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ S) :
    ∃ (s : Finset X) (U : s → S.Opens) (V : s → X.Opens),
      (∀ j, IsAffineOpen (U j) ∧ IsAffineOpen (V j) ∧ V j ≤ f ⁻¹ᵁ U j) ∧
        TopologicalSpace.IsOpenCover V := by
  classical
  have htarget (x : X) : ∃ U : S.Opens, IsAffineOpen U ∧ f x ∈ U := by
    obtain ⟨_, ⟨U, hU : IsAffineOpen U, rfl⟩, hfx, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    exact ⟨U, hU, hfx⟩
  choose U hU hfx using htarget
  have hsource (x : X) : ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ f ⁻¹ᵁ U x := by
    obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (hfx x) (f ⁻¹ᵁ U x).2
    exact ⟨V, hV, hx, hle⟩
  choose V hV hx hle using hsource
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X))
    (fun x => (V x).2) fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩
  refine ⟨s, fun j => U j.1, fun j => V j.1, fun j => ⟨hU j.1, hV j.1, hle j.1⟩, ?_⟩
  refine TopologicalSpace.IsOpenCover.mk (SetLike.ext fun x => ?_)
  simp only [TopologicalSpace.Opens.mem_iSup, TopologicalSpace.Opens.mem_top, iff_true]
  obtain ⟨y, hyS, hy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact ⟨⟨y, hyS⟩, hy⟩

/-- **A finite family of sections on affine opens of a limit descends to one common stage.**
Each section lives on the preimage of an affine open of a fixed stage, which is the limit of
the affine opens of the later stages, so each descends individually; the index category is
cofiltered, so a single later stage dominates all the finitely many stages obtained. -/
private theorem exists_common_stage_sections {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I) {J : Type u} [Finite J] (W : J → (D.obj i).Opens)
    (hW : ∀ j, IsAffineOpen (W j))
    (s : ∀ j, Γ((c.π.app i ⁻¹ᵁ W j : c.pt.Opens), ⊤)) :
    ∃ (k : Over i) (t : ∀ j, Γ((opensDiagram D i (W j)).obj k, ⊤)),
      ∀ j, s j = ((opensCone D c i (W j)).π.app k).appTop (t j) := by
  classical
  have hAff (j : J) (k : Over i) : IsAffine ((opensDiagram D i (W j)).obj k) :=
    (hW j).preimage (D.map k.hom)
  have (j : J) : ∀ k : Over i, CompactSpace ((opensDiagram D i (W j)).obj k) := fun k =>
    have : IsAffine ((opensDiagram D i (W j)).obj k) := hAff j k
    inferInstance
  have (j : J) : ∀ k : Over i, QuasiSeparatedSpace ((opensDiagram D i (W j)).obj k) := fun k =>
    have : IsAffine ((opensDiagram D i (W j)).obj k) := hAff j k
    inferInstance
  choose a t ht using fun j => exists_appTop_π_eq_of_isLimit (opensDiagram D i (W j))
    (opensCone D c i (W j)) (isLimitOpensCone D c hc i (W j)) (s j)
  have : Fintype J := Fintype.ofFinite J
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image a)
  let m (j : J) : k ⟶ a j := (hk (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)).some
  refine ⟨k, fun j => ((opensDiagram D i (W j)).map (m j)).appTop (t j), fun j => ?_⟩
  rw [ht j, ← (opensCone D c i (W j)).w (m j)]
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rfl

/-- **Stacks Project, Tag 01ZE.**  A quasi-compact, quasi-separated scheme locally of finite
type over `S` immerses over `S` into a scheme of finite presentation over `S`. -/
@[stacks 01ZE]
theorem exists_finitePresentation_isImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (X' : Scheme.{u}) (f' : X' ⟶ S) (i : X ⟶ X'),
      FinitePresentation f' ∧ IsImmersion i ∧ i ≫ f' = f := by
  classical
  let A := finiteTypeApproximationBot X
  let _ : Preorder A.indexType := A.indexPreorder
  have _ : Nonempty A.indexType := A.indexNonempty
  have _ : IsDirected A.indexType (· ≤ ·) := A.indexDirected
  let D := A.ambient
  let c : Cone D := Cone.mk X A.ambientCone
  have hc : IsLimit c := A.ambientCone_isLimit
  let e : (⊤_ Scheme.{u}) ≅ integersBase.{u} :=
    (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).symm
  have _ : ∀ {j j' : A.indexTypeᵒᵈ} (g : j ⟶ j'), IsAffineHom (D.map g) := A.transition_affine
  have hstage : ∀ j : A.indexTypeᵒᵈ, CompactSpace (D.obj j) ∧ QuasiSeparatedSpace (D.obj j) := by
    intro j
    have : LocallyOfFiniteType (terminal.from (D.obj j)) := A.locallyOfFiniteType j
    have : QuasiCompact (terminal.from (D.obj j)) := A.quasiCompact j
    exact compactSpace_and_quasiSeparatedSpace_of_locallyOfFiniteType
      (terminal.from (D.obj j) ≫ e.hom)
  have _ : ∀ j : A.indexTypeᵒᵈ, CompactSpace (D.obj j) := fun j => (hstage j).1
  have _ : ∀ j : A.indexTypeᵒᵈ, QuasiSeparatedSpace (D.obj j) := fun j => (hstage j).2
  obtain ⟨s, U, V, hcharts, hcover⟩ := exists_finite_affine_open_cover_subordinate f
  obtain ⟨i, t, W, hWcover, hW⟩ :=
    Scheme.exists_isOpenCover_and_isAffine D c hc V hcover fun j => (hcharts j).2.1
  let hS : S ⟶ integersBase.{u} := terminal.from S ≫ e.hom
  let Vlim (j : t) : X.Opens := c.π.app i ⁻¹ᵁ W j
  have hVeq (j : t) : Vlim j = V j.1 := ((hW j).2).symm
  have hVlim (j : t) : IsAffineOpen (Vlim j) := hVeq j ▸ (hcharts j.1).2.1
  have hle (j : t) : Vlim j ≤ f ⁻¹ᵁ U j.1 := hVeq j ▸ (hcharts j.1).2.2
  let fchart (j : t) : (Vlim j : Scheme) ⟶ (U j.1 : Scheme) := f.resLE (U j.1) (Vlim j) (hle j)
  have _ (j : t) : IsAffine (U j.1 : Scheme) := (hcharts j.1).1
  have _ (j : t) : IsAffine (Vlim j : Scheme) := hVlim j
  have _ (j : t) : LocallyOfFiniteType (fchart j) := inferInstanceAs
    (LocallyOfFiniteType (f.resLE (U j.1) (Vlim j) (hle j)))
  let R (j : t) := Γ((U j.1 : Scheme), ⊤)
  let B (j : t) := Γ((Vlim j : Scheme), ⊤)
  let φ (j : t) : R j →+* B j := (fchart j).appTop.hom
  let _ (j : t) : Algebra (R j) (B j) := (φ j).toAlgebra
  have hgens (j : t) : ∃ n, Nonempty (Algebra.Generators (R j) (B j) (Fin n)) :=
    exists_generators_of_finiteType_algebraMap
      (show RingHom.FiniteType (algebraMap (R j) (B j)) from
        HasRingHomProperty.appTop (@LocallyOfFiniteType) (fchart j) inferInstance)
  let n (j : t) : ℕ := Classical.choose (hgens j)
  let P (j : t) : Algebra.Generators (R j) (B j) (Fin (n j)) :=
    Classical.choice (Classical.choose_spec (hgens j))
  let J := Σ j : t, Fin (n j)
  obtain ⟨k, tgen, htgen⟩ := exists_common_stage_sections D c hc i (fun a : J => W a.1)
    (fun a => (hW a.1).1) fun a : J => (P a.1).val a.2
  let g : D.obj k.left ⟶ integersBase.{u} := terminal.from (D.obj k.left) ≫ e.hom
  have _ : LocallyOfFiniteType (terminal.from (D.obj k.left)) := A.locallyOfFiniteType k.left
  have _ : QuasiCompact (terminal.from (D.obj k.left)) := A.quasiCompact k.left
  have _ : LocallyOfFiniteType g := inferInstanceAs
    (LocallyOfFiniteType (terminal.from (D.obj k.left) ≫ e.hom))
  have _ : QuasiCompact g := inferInstanceAs
    (QuasiCompact (terminal.from (D.obj k.left) ≫ e.hom))
  let X' := pullback g hS
  let f' : X' ⟶ S := pullback.snd g hS
  have hbase : c.π.app k.left ≫ g = f ≫ hS := specULiftZIsTerminal.hom_ext _ _
  let q : X ⟶ X' := pullback.lift (c.π.app k.left) f hbase
  have hqfst : q ≫ pullback.fst g hS = c.π.app k.left := pullback.lift_fst _ _ _
  have hqf : q ≫ f' = f := pullback.lift_snd _ _ _
  let Wk (j : t) : (D.obj k.left).Opens := D.map k.hom ⁻¹ᵁ W j
  let Uopen (j : t) : X'.Opens := pullback.fst g hS ⁻¹ᵁ Wk j ⊓ f' ⁻¹ᵁ U j.1
  have hWlim (j : t) : c.π.app k.left ⁻¹ᵁ Wk j = Vlim j := by
    rw [show Wk j = D.map k.hom ⁻¹ᵁ W j from rfl, ← Scheme.Hom.comp_preimage, c.w]
  have hpreV (j : t) : q ⁻¹ᵁ Uopen j = Vlim j := by
    have h₁ : q ⁻¹ᵁ (pullback.fst g hS ⁻¹ᵁ Wk j) = Vlim j := by
      rw [← Scheme.Hom.comp_preimage, hqfst, hWlim]
    have h₂ : q ⁻¹ᵁ (f' ⁻¹ᵁ U j.1) = f ⁻¹ᵁ U j.1 := by
      rw [← Scheme.Hom.comp_preimage, hqf]
    rw [show Uopen j = pullback.fst g hS ⁻¹ᵁ Wk j ⊓ f' ⁻¹ᵁ U j.1 from rfl,
      Scheme.Hom.preimage_inf, h₁, h₂]
    exact inf_eq_left.mpr (hle j)
  let wι (j : t) : (Wk j : Scheme) ⟶ D.obj k.left := (opensDiagramι D i (W j)).app k
  let uι (j : t) : (U j.1 : Scheme) ⟶ S := (U j.1).ι
  let wToZ (j : t) : (Wk j : Scheme) ⟶ integersBase.{u} := wι j ≫ g
  let uToZ (j : t) : (U j.1 : Scheme) ⟶ integersBase.{u} := uι j ≫ hS
  let Tj (j : t) := pullback (wToZ j) (uToZ j)
  have _ (j : t) : IsOpenImmersion (wι j) :=
    inferInstanceAs (IsOpenImmersion ((opensDiagramι D i (W j)).app k))
  have _ (j : t) : IsOpenImmersion (uι j) := inferInstanceAs (IsOpenImmersion (U j.1).ι)
  let tmap (j : t) : Tj j ⟶ X' :=
    pullback.map (wToZ j) (uToZ j) g hS (wι j) (uι j) (𝟙 _) (by simp [wToZ]) (by simp [uToZ])
  have htmapRange (j : t) : (tmap j).opensRange = Uopen j := by
    have hWrange : Set.range (wι j) = (Wk j : Set (D.obj k.left)) := Scheme.Opens.range_ι _
    have hUrange : Set.range (uι j) = (U j.1 : Set S) := Scheme.Opens.range_ι _
    refine TopologicalSpace.Opens.ext ?_
    change Set.range (tmap j).base = _
    rw [show tmap j = pullback.map (wToZ j) (uToZ j) g hS (wι j) (uι j) (𝟙 _)
        (by simp [wToZ]) (by simp [uToZ]) from rfl, Scheme.Pullback.range_map, hWrange, hUrange]
    rfl
  have hcover' (x : X) : ∃ j : t, q x ∈ Uopen j := by
    have hx : (c.π.app i).base x ∈ (⨆ j, W j : (D.obj i).Opens) := by
      rw [hWcover.iSup_eq_top]
      trivial
    obtain ⟨j, hxj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hpoint : (D.map k.hom).base ((c.π.app k.left).base x) = (c.π.app i).base x := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun z : X ⟶ D.obj i => z x) (c.w k.hom)
    refine ⟨j, ⟨?_, ?_⟩⟩
    · change (pullback.fst g hS).base (q x) ∈ Wk j
      rw [← Scheme.Hom.comp_apply, hqfst]
      change (D.map k.hom).base ((c.π.app k.left).base x) ∈ W j
      exact hpoint ▸ hxj
    · change f'.base (q x) ∈ U j.1
      rw [← Scheme.Hom.comp_apply, hqf]
      exact hle j (show x ∈ Vlim j from hxj)
  have hclosed (j : t) : IsClosedImmersion (q.resLE (Uopen j) (q ⁻¹ᵁ Uopen j) le_rfl) := by
    have _ : IsOpenImmersion (tmap j) := inferInstanceAs
      (IsOpenImmersion (pullback.map (wToZ j) (uToZ j) g hS (wι j) (uι j) (𝟙 _)
        (by simp [wToZ]) (by simp [uToZ])))
    let a : (Vlim j : Scheme) ⟶ (Wk j : Scheme) :=
      (c.π.app k.left).resLE (Wk j) (Vlim j) (hWlim j).ge
    let b : (Vlim j : Scheme) ⟶ (U j.1 : Scheme) := fchart j
    have ha : a ≫ wι j = (Vlim j).ι ≫ c.π.app k.left := Scheme.Hom.resLE_comp_ι _ _
    have hb : b ≫ uι j = (Vlim j).ι ≫ f := Scheme.Hom.resLE_comp_ι _ _
    have hab : a ≫ wToZ j = b ≫ uToZ j := by
      change a ≫ wι j ≫ g = b ≫ uι j ≫ hS
      rw [reassoc_of% ha, reassoc_of% hb, hbase]
    let ℓ : (Vlim j : Scheme) ⟶ Tj j := pullback.lift a b hab
    have _ : IsAffine (Wk j : Scheme) := (hW j).1.preimage (D.map k.hom)
    have _ : IsAffine (Tj j) := isAffine_of_isAffineHom (pullback.snd (wToZ j) (uToZ j))
    let _ : Algebra (R j) Γ(Tj j, ⊤) :=
      (pullback.snd (wToZ j) (uToZ j)).appTop.hom.toAlgebra
    let ψ : Γ(Tj j, ⊤) →ₐ[R j] Γ((Vlim j : Scheme), ⊤) :=
      { toRingHom := ℓ.appTop.hom
        commutes' := fun r => by
          change (ℓ ≫ pullback.snd (wToZ j) (uToZ j)).appTop.hom r = φ j r
          rw [pullback.lift_snd] }
    have hgen (a' : Fin (n j)) : ∃ z : Γ(Tj j, ⊤), ψ z = (P j).val a' := by
      refine ⟨(pullback.fst (wToZ j) (uToZ j)).appTop.hom (tgen ⟨j, a'⟩), ?_⟩
      change (ℓ ≫ pullback.fst (wToZ j) (uToZ j)).appTop.hom (tgen ⟨j, a'⟩) = _
      rw [pullback.lift_fst]
      exact (htgen ⟨j, a'⟩).symm
    have hℓ : IsClosedImmersion ℓ :=
      IsClosedImmersion.of_surjective_of_isAffine ℓ (surjective_of_generators_in_range ψ (P j) hgen)
    let hIso := (tmap j).isoOpensRange ≪≫ X'.isoOfEq (htmapRange j)
    have htmapfst : tmap j ≫ pullback.fst g hS = pullback.fst (wToZ j) (uToZ j) ≫ wι j :=
      pullback.lift_fst _ _ _
    have htmapsnd : tmap j ≫ pullback.snd g hS = pullback.snd (wToZ j) (uToZ j) ≫ uι j :=
      pullback.lift_snd _ _ _
    have hfactor : q.resLE (Uopen j) (Vlim j) (hpreV j).symm.le = ℓ ≫ hIso.hom := by
      refine (cancel_mono (Uopen j).ι).1 ?_
      have hℓfst : ℓ ≫ pullback.fst (wToZ j) (uToZ j) = a := pullback.lift_fst _ _ _
      have hℓsnd : ℓ ≫ pullback.snd (wToZ j) (uToZ j) = b := pullback.lift_snd _ _ _
      calc q.resLE (Uopen j) (Vlim j) (hpreV j).symm.le ≫ (Uopen j).ι =
            (Vlim j).ι ≫ q := Scheme.Hom.resLE_comp_ι _ _
        _ = ℓ ≫ tmap j := by
          refine pullback.hom_ext ?_ ?_
          · rw [Category.assoc, hqfst, Category.assoc, htmapfst, ← Category.assoc, hℓfst, ha]
          · rw [Category.assoc, hqf, Category.assoc, htmapsnd, ← Category.assoc, hℓsnd, hb]
        _ = ℓ ≫ hIso.hom ≫ (Uopen j).ι := by simp [hIso]
        _ = (ℓ ≫ hIso.hom) ≫ (Uopen j).ι := (Category.assoc _ _ _).symm
    refine (q.resLE_congr le_rfl rfl (hpreV j) (P := @IsClosedImmersion)).mpr ?_
    rw [hfactor]
    exact MorphismProperty.RespectsIso.postcomp (@IsClosedImmersion) hIso.hom ℓ hℓ
  exact ⟨X', f', q, finitePresentation_pullback_snd g hS,
    isImmersion_of_isClosedImmersion_resLE q Uopen hcover' hclosed, hqf⟩

end AlgebraicGeometry

end
