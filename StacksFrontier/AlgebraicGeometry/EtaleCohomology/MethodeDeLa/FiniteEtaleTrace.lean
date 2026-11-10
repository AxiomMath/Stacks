module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSectionsLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SplitOver
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.TraceInjectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.StalksTestMaps
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sweep.PrimePowerTorsionMultiplication
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.TraceDegree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricFibreDegree
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace of a finite étale morphism and the méthode de la trace

Let `g : Y ⟶ S` be an étale morphism and let `G` be an abelian sheaf on the small étale site of
`S`. Restriction `g⁻¹` along `g` is left adjoint to the direct image `g_*`, and the sections of
`g_* g⁻¹ G` over an object `U` of the small étale site of `S` are the sections of `G` over the
base change `U ×_S Y`, viewed over `S`.

When `g` has sheet data over `U` (`Stacks.Etale.IsSplitOver`: finitely many pairwise disjoint
sections `σ_i : U ⟶ Y` over `S` through which every `U`-point of `Y` locally factors, that is
`U ×_S Y = ∐ U`), each sheet gives a section `U ⟶ U ×_S Y` of the projection, and the sum of the
restrictions along them is a map

`G(U ×_S Y) ⟶ G(U)`, `s ↦ ∑ᵢ σᵢ^* s`.

This is the trace map of [Stacks, Section 03SH] over an object over which `g` is split. This file
proves that it does not depend on the choice of the sheet data, and that it is compatible with
restriction. Composed with the restriction `G(U) ⟶ G(U ×_S Y)` it is multiplication by the
number of sheets, which is the degree `d` of `g` when `g` is finite étale of constant degree `d`.

For a finite étale `g` the objects over which `g` is split are cover dense ([Stacks, Tag 04HN]),
so these maps glue to a morphism of sheaves `g_* g⁻¹ G ⟶ G`, the trace, and the unit
`G ⟶ g_* g⁻¹ G` followed by the trace is multiplication by `d`. With
`Stacks.EtaleCohomology.injective_etaleCohomologyPullback_of_isIso` this gives the méthode de la
trace: if multiplication by `d` is invertible on `G`, then `Hⁿ(S, G) ⟶ Hⁿ(Y, g⁻¹ G)` is
injective.

## Main definitions

* `Stacks.EtaleCohomology.sheetSection`: the section `U ⟶ U ×_S Y` attached to a sheet.
* `Stacks.EtaleCohomology.splitTrace`: the sum over the sheets.
* `Stacks.EtaleCohomology.finiteEtaleTrace`: the trace `g_* g⁻¹ G ⟶ G`.

## Main results

* `Stacks.EtaleCohomology.splitTrace_eq`: the sum does not depend on the sheet data.
* `Stacks.EtaleCohomology.map_splitTrace`: compatibility with restriction.
* `Stacks.EtaleCohomology.splitTrace_unit`: restriction followed by the trace is multiplication
  by the number of sheets.
* `Stacks.EtaleCohomology.unit_comp_finiteEtaleTrace`: the unit followed by the trace is
  multiplication by the degree.
* `Stacks.EtaleCohomology.injective_etaleCohomologyPullback_of_isPrimePowerTorsion`: the méthode
  de la trace for `ℓ`-power torsion sheaves and a degree prime to `ℓ`.

## Implementation notes

The trace is built for restriction `g⁻¹` along the étale `g`, the left adjoint of `g_*` whose
sections are literally those of `G`; it is transported to Mathlib's inverse image by uniqueness
of left adjoints. The trace is not characterised here by its behaviour on stalks or by its
naturality in `G`; only the identity `unit ≫ trace = d` is used.

## References

* [Stacks Project, Section 03SH](https://stacks.math.columbia.edu/tag/03SH)
* [Stacks Project, Tag 03SE](https://stacks.math.columbia.edu/tag/03SE)
* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u


namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Etale.IsSplitOver.finite_I

variable {S Y : Scheme.{u}} (g : Y ⟶ S) [Etale g]

/-- The base change `U ×_S Y` of an object `U` of the small étale site of `S`, viewed over `S`
through `Y`: the object whose sections are those of `g_* g⁻¹ G` over `U`. -/
abbrev baseChangeCompose (U : S.Etale) : S.Etale :=
  (Scheme.Etale.smallEtaleCompose g).obj ((smallEtaleBaseChange g).obj U)

/-- The projection `U ×_S Y ⟶ U`, the counit of composition with `g` against base change. -/
abbrev baseChangeComposeπ (U : S.Etale) : baseChangeCompose g U ⟶ U :=
  (Scheme.Etale.smallEtaleComposeBaseChangeAdj g).counit.app U

/-- On underlying schemes, the projection `U ×_S Y ⟶ U` is the first projection of the pullback. -/
lemma baseChangeComposeπ_left (U : S.Etale) :
    (baseChangeComposeπ g U).left = pullback.fst U.hom g := rfl

/-- **The section `U ⟶ U ×_S Y` attached to a sheet** `σ : U ⟶ Y` of sheet data of `g` over
`q = U.hom`. -/
def sheetSection (U : S.Etale) {q : U.left ⟶ S} (h : Stacks.Etale.IsSplitOver g q)
    (hq : U.hom = q) (i : h.I) : U ⟶ baseChangeCompose g U :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 U.left) (h.sheet i) (by rw [Category.id_comp, h.sheet_comp, hq]))
    (by
      change pullback.lift _ _ _ ≫ pullback.snd U.hom g ≫ g = U.hom
      rw [pullback.lift_snd_assoc, h.sheet_comp, hq])

/-- A sheet section followed by the first projection `U ×_S Y ⟶ U` is the identity. -/
lemma sheetSection_left_fst (U : S.Etale) {q : U.left ⟶ S} (h : Stacks.Etale.IsSplitOver g q)
    (hq : U.hom = q) (i : h.I) : (sheetSection g U h hq i).left ≫ pullback.fst U.hom g = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- A sheet section followed by the second projection `U ×_S Y ⟶ Y` is the sheet. -/
lemma sheetSection_left_snd (U : S.Etale) {q : U.left ⟶ S} (h : Stacks.Etale.IsSplitOver g q)
    (hq : U.hom = q) (i : h.I) :
    (sheetSection g U h hq i).left ≫ pullback.snd U.hom g = h.sheet i :=
  pullback.lift_snd _ _ _

/-- A sheet section is a section of the projection. -/
@[reassoc (attr := simp)]
lemma sheetSection_π (U : S.Etale) {q : U.left ⟶ S} (h : Stacks.Etale.IsSplitOver g q)
    (hq : U.hom = q) (i : h.I) : sheetSection g U h hq i ≫ baseChangeComposeπ g U = 𝟙 U :=
  MorphismProperty.Over.Hom.ext (sheetSection_left_fst g U h hq i)

/-- After restriction along `k : W ⟶ U`, a sheet section only depends on the restricted sheet. -/
lemma comp_sheetSection_eq {U W : S.Etale} (k : W ⟶ U) {q q' : U.left ⟶ S}
    (h : Stacks.Etale.IsSplitOver g q) (hq : U.hom = q) (h' : Stacks.Etale.IsSplitOver g q')
    (hq' : U.hom = q') (i : h.I) (j : h'.I) (hij : k.left ≫ h.sheet i = k.left ≫ h'.sheet j) :
    k ≫ sheetSection g U h hq i = k ≫ sheetSection g U h' hq' j := by
  refine MorphismProperty.Over.Hom.ext (show k.left ≫ pullback.lift (𝟙 U.left) (h.sheet i) _ =
    k.left ≫ pullback.lift (𝟙 U.left) (h'.sheet j) _ from pullback.hom_ext ?_ ?_)
  · simp only [Category.assoc, pullback.lift_fst]
  · simp only [Category.assoc, pullback.lift_snd, hij]

omit [Etale g] in
/-- The scheme-level identity behind `Stacks.EtaleCohomology.comp_sheetSection`. -/
private lemma comp_lift_id {W' U' : Scheme.{u}} (k : W' ⟶ U') (a : U' ⟶ S) (b : W' ⟶ S)
    (hab : k ≫ a = b) (σ : U' ⟶ Y) (hσ : σ ≫ g = a) :
    k ≫ pullback.lift (𝟙 U') σ (by rw [Category.id_comp, hσ]) =
      pullback.lift (𝟙 W') (k ≫ σ) (by rw [Category.id_comp, Category.assoc, hσ, hab]) ≫
        pullback.lift (pullback.fst b g ≫ k) (pullback.snd b g)
          (by rw [Category.assoc, hab, pullback.condition]) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc,
      pullback.lift_fst, Category.id_comp, Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd]

/-- **Sheet sections and restriction.** Restricting the sheet section of `σ` along `k : W ⟶ U`
is the sheet section of `k ≫ σ`, followed by the base change of `k`. -/
lemma comp_sheetSection {U W : S.Etale} (k : W ⟶ U) {q : U.left ⟶ S}
    (h : Stacks.Etale.IsSplitOver g q) (hq : U.hom = q) (hq' : W.hom = k.left ≫ q) (i : h.I) :
    k ≫ sheetSection g U h hq i = sheetSection g W (h.comp k.left) hq' i ≫
      (Scheme.Etale.smallEtaleCompose g).map ((smallEtaleBaseChange g).map k) :=
  MorphismProperty.Over.Hom.ext (comp_lift_id g k.left U.hom W.hom (MorphismProperty.Over.w k)
    (h.sheet i) ((h.sheet_comp i).trans hq.symm))

variable (G : Sheaf (smallEtaleTopology S) Ab.{u + 1})

/-- **The trace over an object over which `g` is split**: the sum of the restrictions along the
sheet sections, `G(U ×_S Y) ⟶ G(U)`. -/
def splitTrace (U : S.Etale) {q : U.left ⟶ S} (h : Stacks.Etale.IsSplitOver g q)
    (hq : U.hom = q) : G.obj.obj (op (baseChangeCompose g U)) ⟶ G.obj.obj (op U) :=
  letI : Fintype h.I := Fintype.ofFinite _
  AddCommGrpCat.ofHom (∑ i, (G.obj.map (sheetSection g U h hq i).op).hom)

/-- The trace of a section `s` is the sum over the sheets of the restrictions of `s` along the
sheet sections. -/
lemma splitTrace_apply (U : S.Etale) {q : U.left ⟶ S} (h : Stacks.Etale.IsSplitOver g q)
    (hq : U.hom = q) (s : ToType (G.obj.obj (op (baseChangeCompose g U)))) :
    letI : Fintype h.I := Fintype.ofFinite _
    splitTrace g G U h hq s = ∑ i, G.obj.map (sheetSection g U h hq i).op s := by
  simp [splitTrace]

/-- Restricting the trace along `k : W ⟶ U` is the sum over the sheets of the restrictions along
the restricted sheet sections. -/
lemma map_splitTrace_apply {U W : S.Etale} (k : W ⟶ U) {q : U.left ⟶ S}
    (h : Stacks.Etale.IsSplitOver g q) (hq : U.hom = q)
    (s : ToType (G.obj.obj (op (baseChangeCompose g U)))) :
    letI : Fintype h.I := Fintype.ofFinite _
    G.obj.map k.op (splitTrace g G U h hq s) =
      ∑ i, G.obj.map (k ≫ sheetSection g U h hq i).op s := by
  simp [splitTrace_apply]

/-- Two sections over an object with empty underlying scheme are equal. -/
lemma smallEtale_section_eq_of_isEmpty {V : S.Etale} (hV : IsEmpty V.left)
    (a b : ToType (G.obj.obj (op V))) : a = b :=
  smallEtale_section_ext G ⊥ ((mem_smallEtaleTopology_iff ⊥).mpr fun w ↦ isEmptyElim w) a b
    fun _ _ hg ↦ hg.elim

omit [Etale g] in
/-- **Two sheet data agree locally up to relabelling**: every point of `U` has an open
neighbourhood on which the sheets of `h` are the sheets of `h'`, matched by a bijection. -/
lemma exists_open_sheet_equiv (U : S.Etale) {q q' : U.left ⟶ S}
    (h : Stacks.Etale.IsSplitOver g q) (h' : Stacks.Etale.IsSplitOver g q') (hqq : q = q')
    (w : U.left) : ∃ (O : U.left.Opens) (e : h.I ≃ h'.I), w ∈ O ∧
      ∀ i, O.ι ≫ h.sheet i = O.ι ≫ h'.sheet (e i) := by
  have H : ∀ {q₁ q₂ : U.left ⟶ S} (h₁ : Stacks.Etale.IsSplitOver g q₁)
      (h₂ : Stacks.Etale.IsSplitOver g q₂), q₁ = q₂ → ∀ i : h₁.I, ∃ (Z : Scheme.{u})
      (p : Z ⟶ U.left) (_ : IsOpenImmersion p) (j : h₂.I),
      w ∈ Set.range p ∧ p ≫ h₁.sheet i = p ≫ h₂.sheet j := by
    intro q₁ q₂ h₁ h₂ hq i
    obtain ⟨κ, Z, p, hp, ι, hcov, hfac⟩ := h₂.exists_openCover (𝟙 U.left) (h₁.sheet i)
      (by rw [h₁.sheet_comp, Category.id_comp, hq])
    obtain ⟨k, hk⟩ := hcov w
    exact ⟨Z k, p k, hp k, ι k, hk, by simpa only [Category.id_comp] using hfac k⟩
  choose Z₁ p₁ hp₁ e₁ hw₁ hf₁ using H h h' hqq
  choose Z₂ p₂ hp₂ e₂ hw₂ hf₂ using H h' h hqq.symm
  let O : U.left.Opens := ⟨(⋂ i, Set.range (p₁ i)) ∩ ⋂ j, Set.range (p₂ j),
    (isOpen_iInter_of_finite fun i ↦ (p₁ i).isOpenEmbedding.isOpen_range).inter
      (isOpen_iInter_of_finite fun j ↦ (p₂ j).isOpenEmbedding.isOpen_range)⟩
  have hwO : w ∈ O := ⟨Set.mem_iInter.mpr hw₁, Set.mem_iInter.mpr hw₂⟩
  have hO₁ : ∀ i, O.ι ≫ h.sheet i = O.ι ≫ h'.sheet (e₁ i) := by
    intro i
    have hsub : Set.range O.ι ⊆ Set.range (p₁ i) := by
      rw [Scheme.Opens.range_ι]
      exact fun x hx ↦ Set.mem_iInter.mp hx.1 i
    rw [← IsOpenImmersion.lift_fac (p₁ i) O.ι hsub, Category.assoc, Category.assoc, hf₁]
  have hO₂ : ∀ j, O.ι ≫ h'.sheet j = O.ι ≫ h.sheet (e₂ j) := by
    intro j
    have hsub : Set.range O.ι ⊆ Set.range (p₂ j) := by
      rw [Scheme.Opens.range_ι]
      exact fun x hx ↦ Set.mem_iInter.mp hx.2 j
    rw [← IsOpenImmersion.lift_fac (p₂ j) O.ι hsub, Category.assoc, Category.assoc, hf₂]
  have hne : Nonempty O := ⟨⟨w, hwO⟩⟩
  refine ⟨O, ⟨e₁, e₂, fun i ↦ ?_, fun j ↦ ?_⟩, hwO, hO₁⟩
  · by_contra hi
    exact (h.isEmpty_of_sheet_eq O.ι hi ((hO₂ (e₁ i)).symm.trans (hO₁ i).symm)).false
      (Classical.choice hne)
  · by_contra hj
    exact (h'.isEmpty_of_sheet_eq O.ι hj ((hO₁ (e₂ j)).symm.trans (hO₂ j).symm)).false
      (Classical.choice hne)

/-- **The trace over a split object does not depend on the sheet data.** -/
theorem splitTrace_eq (U : S.Etale) {q q' : U.left ⟶ S} (h : Stacks.Etale.IsSplitOver g q)
    (hq : U.hom = q) (h' : Stacks.Etale.IsSplitOver g q') (hq' : U.hom = q') :
    splitTrace g G U h hq = splitTrace g G U h' hq' := by
  let : Fintype h.I := Fintype.ofFinite _
  let : Fintype h'.I := Fintype.ofFinite _
  let M : Sieve U :=
    { arrows := fun W k ↦ ∃ e : h.I ≃ h'.I, ∀ i, k.left ≫ h.sheet i = k.left ≫ h'.sheet (e i)
      downward_closed := by
        rintro W W' k ⟨e, he⟩ l
        refine ⟨e, fun i ↦ ?_⟩
        change l.left ≫ k.left ≫ h.sheet i = l.left ≫ k.left ≫ h'.sheet (e i)
        rw [he i] }
  have hM : M ∈ smallEtaleTopology S U := by
    rw [mem_smallEtaleTopology_iff]
    intro w
    obtain ⟨O, e, hwO, he⟩ := exists_open_sheet_equiv g U h h' (hq.symm.trans hq') w
    let V : S.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ U.hom) (by infer_instance)
    refine ⟨V, MorphismProperty.Over.homMk O.ι rfl, ⟨e, he⟩, ?_⟩
    change w ∈ Set.range O.ι
    rw [Scheme.Opens.range_ι]
    exact hwO
  ext s
  refine smallEtale_section_ext G M hM _ _ fun W k ⟨e, he⟩ ↦ ?_
  rw [map_splitTrace_apply, map_splitTrace_apply]
  exact Fintype.sum_equiv e _ _ fun i ↦ by
    rw [comp_sheetSection_eq g k h hq h' hq' i (e i) (he i)]

/-- **The trace is compatible with restriction**: restricting along `k : W ⟶ U` and taking the
trace over `W` (for any sheet data over `W`) is taking the trace over `U` and restricting. -/
theorem map_splitTrace {U W : S.Etale} (k : W ⟶ U) {q : U.left ⟶ S}
    (h : Stacks.Etale.IsSplitOver g q) (hq : U.hom = q) {q' : W.left ⟶ S}
    (h' : Stacks.Etale.IsSplitOver g q') (hq' : W.hom = q') :
    G.obj.map ((Scheme.Etale.smallEtaleCompose g).map ((smallEtaleBaseChange g).map k)).op ≫
        splitTrace g G W h' hq' = splitTrace g G U h hq ≫ G.obj.map k.op := by
  have hW : W.hom = k.left ≫ q := by rw [← hq, MorphismProperty.Over.w k]
  rw [← splitTrace_eq g G W (h.comp k.left) hW h' hq']
  let : Fintype h.I := Fintype.ofFinite _
  ext s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, map_splitTrace_apply,
    splitTrace_apply]
  simp [comp_sheetSection g k h hq hW]
  rfl

/-- **Restriction followed by the trace is multiplication by the number of sheets.** -/
theorem splitTrace_unit (U : S.Etale) {q : U.left ⟶ S} (h : Stacks.Etale.IsSplitOver g q)
    (hq : U.hom = q) (t : ToType (G.obj.obj (op U))) :
    splitTrace g G U h hq (G.obj.map (baseChangeComposeπ g U).op t) = Nat.card h.I • t := by
  let : Fintype h.I := Fintype.ofFinite _
  rw [splitTrace_apply, Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, sheetSection_π,
    op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-! ### The trace as a morphism of sheaves -/

/-- The objects of the small étale site of `S` over which `g` has sheet data. -/
def IsSplitObject : ObjectProperty S.Etale := fun U ↦ Nonempty (Stacks.Etale.IsSplitOver g U.hom)

variable [IsFinite g]

/-- The objects over which `g` is split are cover dense, by [Stacks, Tag 04HN]. -/
instance isCoverDense_isSplitObject :
    (ObjectProperty.ι (IsSplitObject g)).IsCoverDense (smallEtaleTopology S) := by
  refine ⟨fun U ↦ (mem_smallEtaleTopology_iff _).mpr fun y ↦ ?_⟩
  obtain ⟨W, e, he, w, hw, ⟨hs⟩⟩ := Stacks.Etale.exists_isSplitOver g U.hom y
  let V : S.Etale := MorphismProperty.Over.mk ⊤ (e ≫ U.hom) (by infer_instance)
  exact ⟨V, MorphismProperty.Over.homMk e rfl,
    ⟨⟨V, ⟨hs⟩⟩, 𝟙 V, MorphismProperty.Over.homMk e rfl, Category.id_comp _⟩, w, hw⟩

/-- The trace on the split objects, as a natural transformation. -/
def splitTraceNatTrans :
    (ObjectProperty.ι (IsSplitObject g)).op ⋙
        ((etaleAbelianDirectImage.{u, 0} g).obj ((etaleRestriction.{u, 0} g).obj G)).obj ⟶
      (ObjectProperty.ι (IsSplitObject g)).op ⋙ G.obj where
  app X := splitTrace g G X.unop.obj X.unop.property.some rfl
  naturality X X' f :=
    map_splitTrace g G ((ObjectProperty.ι (IsSplitObject g)).map f.unop) X.unop.property.some rfl
      X'.unop.property.some rfl

/-- **The trace of a finite étale morphism** `g_* g⁻¹ G ⟶ G`, the sum over the sheets of `g`
étale locally on `S`. -/
def finiteEtaleTrace :
    (etaleAbelianDirectImage.{u, 0} g).obj ((etaleRestriction.{u, 0} g).obj G) ⟶ G :=
  ⟨Functor.IsCoverDense.sheafHom (splitTraceNatTrans g G)⟩

/-- Over a split object the trace is the sum over the sheets. -/
lemma finiteEtaleTrace_app (U : S.Etale) (h : Stacks.Etale.IsSplitOver g U.hom) :
    (finiteEtaleTrace g G).hom.app (op U) = splitTrace g G U h rfl :=
  (congrArg (fun α ↦ α.app (op (⟨U, ⟨h⟩⟩ : (IsSplitObject g).FullSubcategory)))
    (Functor.IsCoverDense.sheafHom_restrict_eq (splitTraceNatTrans g G))).trans
    (splitTrace_eq g G U _ rfl h rfl)

/-- **The unit followed by the trace is multiplication by the number of sheets**, when that
number is the same `d` over every nonempty split object. -/
theorem unit_comp_finiteEtaleTrace_of_natCard {d : ℕ}
    (hd : ∀ (U : S.Etale) (h : Stacks.Etale.IsSplitOver g U.hom), Nonempty U.left →
      Nat.card h.I = d) :
    (etaleRestrictionAbelianDirectImageAdj.{u, 0} g).unit.app G ≫ finiteEtaleTrace g G =
      d • 𝟙 G := by
  have hnsmul : ∀ (U : S.Etale) (t : ToType (G.obj.obj (op U))),
      (d • 𝟙 G).hom.app (op U) t = d • t := by
    intro U t
    have h1 : ((sheafToPresheaf _ Ab.{u + 1}).map (d • 𝟙 G)).app (op U) = d • 𝟙 _ := by
      rw [Functor.map_nsmul, NatTrans.app_nsmul, CategoryTheory.Functor.map_id, NatTrans.id_app]
    exact (ConcreteCategory.congr_hom h1 t).trans (by simp)
  refine (sheafToPresheaf _ _).map_injective ?_
  rw [← Functor.IsCoverDense.sheafHom_eq (ObjectProperty.ι (IsSplitObject g))
      ((sheafToPresheaf _ _).map _),
    ← Functor.IsCoverDense.sheafHom_eq (ObjectProperty.ι (IsSplitObject g))
      ((sheafToPresheaf _ _).map (d • 𝟙 G))]
  congr 1
  ext X t
  obtain ⟨⟨U, ⟨h⟩⟩⟩ := X
  change (finiteEtaleTrace g G).hom.app (op U)
    (G.obj.map (baseChangeComposeπ g U).op t) = (d • 𝟙 G).hom.app (op U) t
  rw [finiteEtaleTrace_app g G U h]
  refine (splitTrace_unit g G U h rfl t).trans ?_
  rw [hnsmul]
  by_cases hU : Nonempty U.left
  · rw [hd U h hU]
  · exact smallEtale_section_eq_of_isEmpty G (not_nonempty_iff.mp hU) _ _

/-- **Unit followed by trace.** For a finite étale `g` of constant degree `d`, the unit
`G ⟶ g_* g⁻¹ G` followed by the trace is multiplication by `d`. -/
@[sga "5 IIIB 3.2" "partial"]
theorem unit_comp_finiteEtaleTrace {d : ℕ} [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d] :
    (etaleRestrictionAbelianDirectImageAdj.{u, 0} g).unit.app G ≫ finiteEtaleTrace g G =
      d • 𝟙 G :=
  unit_comp_finiteEtaleTrace_of_natCard g G fun _ h hV ↦
    @Stacks.Etale.IsSplitOver.natCard_I _ _ _ _ _ h _ _ _ _ hV

/-- **The méthode de la trace** ([Stacks, Section 03SH]). Let `g : Y ⟶ S` be finite étale of
constant degree `d` and let `G` be an abelian sheaf on `S_étale` on which multiplication by `d`
is invertible. Then pulling back `Hⁿ(S, G) ⟶ Hⁿ(Y, g⁻¹ G)` is injective. -/
theorem injective_etaleCohomologyPullback_of_isFiniteLocallyFreeOfRank {d : ℕ}
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d] (hG : IsIso (d • 𝟙 G)) (p : ℕ) :
    Function.Injective (etaleCohomologyPullback g (𝟙 ((smallEtalePullbackAb g).obj G)) p) := by
  let A := smallEtaleAdjunctionAb g
  let B := etaleRestrictionAbelianDirectImageAdj.{u, 0} g
  refine injective_etaleCohomologyPullback_of_isIso g G
    ((smallEtalePushforwardAb g).map ((A.leftAdjointUniq B).hom.app G) ≫ finiteEtaleTrace g G)
    ?_ p
  have key : A.unit.app G ≫ (smallEtalePushforwardAb g).map ((A.leftAdjointUniq B).hom.app G) ≫
      finiteEtaleTrace g G = d • 𝟙 G :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ finiteEtaleTrace g G)
      (Adjunction.unit_leftAdjointUniq_hom_app A B G)).trans (unit_comp_finiteEtaleTrace g G))
  exact key.symm ▸ hG

/-- **The méthode de la trace for `ℓ`-power torsion sheaves.** Let `g : Y ⟶ S` be finite étale
of constant degree `d` prime to `ℓ` and let `G` be an `ℓ`-power torsion abelian sheaf on
`S_étale`. Then `Hⁿ(S, G) ⟶ Hⁿ(Y, g⁻¹ G)` is injective. -/
theorem injective_etaleCohomologyPullback_of_isPrimePowerTorsion {ℓ d : ℕ}
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d] (hd : d.Coprime ℓ)
    (hG : Stacks.Torsion.IsPrimePowerTorsion (smallEtaleTopology S) ℓ G) (p : ℕ) :
    Function.Injective (etaleCohomologyPullback g (𝟙 ((smallEtalePullbackAb g).obj G)) p) :=
  injective_etaleCohomologyPullback_of_isFiniteLocallyFreeOfRank g G
    (Stacks.Torsion.isIso_nsmul_id_of_isPrimePowerTorsion _ hd hG) p

end Stacks.EtaleCohomology

end
