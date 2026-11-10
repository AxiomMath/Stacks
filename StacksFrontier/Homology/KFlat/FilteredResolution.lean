module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Basis.Prod
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.HomologyColimit
public import StacksFrontier.Homology.Injectives.FilteredComplex.MappingCone
public import StacksFrontier.Homology.KFlat.Basic
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Iso
public import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Free K-flat resolutions of filtered complexes

Every filtered complex of modules, a `FilteredObject` of cochain complexes indexed by `ℤᵒᵖ`,
admits a filtered quasi-isomorphic replacement whose terms, filtration steps, and associated
graded pieces are free modules and K-flat complexes.

## Main results

* `CochainComplex.KFlat.exists_free_kFlat_filtered_resolution`: a free K-flat filtered resolution
  inducing quasi-isomorphisms on the underlying complex, every filtration step, and every
  associated graded piece.

## References

* [The Stacks Project, Tag 0H7X](https://stacks.math.columbia.edu/tag/0H7X)
-/


open CategoryTheory Opposite

open Stacks.HomologyColimit

open Stacks.Injectives (filteredMappingCone filteredMappingConeInr)

namespace CochainComplex.KFlat

universe u

-- The cell-attachment arguments compare `Finsupp`-valued maps with their `ModuleCat` packaging;
-- the default transparency setting rejects the defeq.
set_option backward.isDefEq.respectTransparency false

private theorem supported_free (R : Type*) [Ring R] (B : Type*) (s : Set B) :
    Module.Free R (Finsupp.supported R R s) :=
  Module.Free.of_equiv (Finsupp.supportedEquivFinsupp (M := R) (R := R) s).symm

private theorem supported_compl_free (R : Type*) [Ring R] (B : Type*) (s : Set B) :
    Module.Free R ((B →₀ R) ⧸ Finsupp.supported R R s) := by
  classical
  have hc : IsCompl (Finsupp.supported R R s) (Finsupp.supported R R sᶜ) :=
    ⟨Finsupp.disjoint_supported_supported disjoint_compl_right,
      Finsupp.codisjoint_supported_supported (codisjoint_iff.mpr (by simp))⟩
  have := supported_free R B sᶜ
  exact Module.Free.of_equiv (Submodule.quotientEquivOfIsCompl _ _ hc).symm

private theorem cokernel_lmapDomain_free (R : Type u) [Ring R]
    {A B : Type u} (f : A → B) :
    Module.Free R ↥(Limits.cokernel (C := ModuleCat.{u} R)
      (ModuleCat.ofHom (Finsupp.lmapDomain R R f))) := by
  have hr : LinearMap.range (Finsupp.lmapDomain R R f) =
      Finsupp.supported R R (Set.range f) := by
    simpa using Finsupp.lmapDomain_supported R R f Set.univ
  have hfree : Module.Free R ((B →₀ R) ⧸ LinearMap.range (Finsupp.lmapDomain R R f)) :=
    hr ▸ supported_compl_free R B _
  exact Module.Free.of_equiv
    (ModuleCat.cokernelIsoRangeQuotient
      (ModuleCat.ofHom (Finsupp.lmapDomain R R f))).toLinearEquiv.symm

private def stepSet {B : Type u} (w : B → Option ℤ) (i : ℤ) : Set B :=
  {b | ∃ j : ℤ, w b = some j ∧ i ≤ j}

private lemma stepSet_mono {B : Type u} (w : B → Option ℤ) {i j : ℤ} (h : i ≤ j) :
    stepSet w j ⊆ stepSet w i := by
  rintro b ⟨k, hk, hj⟩
  exact ⟨k, hk, h.trans hj⟩

private noncomputable def freeZeroComplex (R : Type u) [Ring R] (B : ℤ → Type u) :
    CochainComplex (ModuleCat.{u} R) ℤ where
  X n := ModuleCat.of R (B n →₀ R)
  d _ _ := 0

private noncomputable def freeZeroComplexMap {R : Type u} [Ring R] {B C : ℤ → Type u}
    (f : ∀ n, B n → C n) : freeZeroComplex R B ⟶ freeZeroComplex R C where
  f n := ModuleCat.ofHom (Finsupp.lmapDomain R R (f n))
  comm' _ _ _ := by simp [freeZeroComplex]

private lemma freeZeroComplexMap_id (R : Type u) [Ring R] (B : ℤ → Type u) :
    freeZeroComplexMap (R := R) (fun n => @id (B n)) = 𝟙 (freeZeroComplex R B) :=
  HomologicalComplex.Hom.ext <| funext fun _ => ModuleCat.hom_ext <| Finsupp.lmapDomain_id R R

private lemma freeZeroComplexMap_comp {R : Type u} [Ring R] {B C D : ℤ → Type u}
    (f : ∀ n, B n → C n) (g : ∀ n, C n → D n) :
    freeZeroComplexMap (R := R) (fun n => g n ∘ f n) =
      freeZeroComplexMap f ≫ freeZeroComplexMap g :=
  HomologicalComplex.Hom.ext <| funext fun n =>
    ModuleCat.hom_ext <| Finsupp.lmapDomain_comp R R (f n) (g n)

private lemma freeZeroComplexMap_mono {R : Type u} [Ring R] {B C : ℤ → Type u}
    (f : ∀ n, B n → C n) (hf : ∀ n, Function.Injective (f n)) :
    Mono (freeZeroComplexMap (R := R) f) :=
  HomologicalComplex.mono_of_mono_f _ fun n =>
    (ModuleCat.mono_iff_injective _).2 (Finsupp.mapDomain_injective (hf n))

private noncomputable def weightedFreeDiagram (R : Type u) [Ring R] {B : ℤ → Type u}
    (w : ∀ n, B n → Option ℤ) : ℤᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj i := freeZeroComplex R (fun n => stepSet (w n) i.unop)
  map {i j} a := freeZeroComplexMap (fun n b =>
    ⟨b.val, stepSet_mono (w n) (leOfHom a.unop) b.property⟩)
  map_id i := freeZeroComplexMap_id R _
  map_comp a b := by
    rw [← freeZeroComplexMap_comp]
    rfl

private noncomputable def weightedFreeInclusion (R : Type u) [Ring R] {B : ℤ → Type u}
    (w : ∀ n, B n → Option ℤ) :
    weightedFreeDiagram R w ⟶ (Functor.const ℤᵒᵖ).obj (freeZeroComplex R B) where
  app i := freeZeroComplexMap (R := R)
    (fun n => (Subtype.val : stepSet (w n) i.unop → B n))
  naturality _ _ _ := by
    change freeZeroComplexMap _ ≫ freeZeroComplexMap _ = freeZeroComplexMap _ ≫ 𝟙 _
    rw [Category.comp_id, ← freeZeroComplexMap_comp]
    rfl

private noncomputable def weightedFreeComplex (R : Type u) [Ring R] {B : ℤ → Type u}
    (w : ∀ n, B n → Option ℤ) :
    FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ := by
  letI : ∀ i, Mono ((weightedFreeInclusion R w).app i) := fun i =>
    freeZeroComplexMap_mono (R := R)
      (fun n => (Subtype.val : stepSet (w n) i.unop → B n))
      (fun _ => Subtype.val_injective)
  exact ⟨freeZeroComplex R B, Filtration.ofDiagram _ (weightedFreeInclusion R w)⟩

private theorem weightedFreeComplex_free (R : Type u) [Ring R] {B : ℤ → Type u}
    (w : ∀ n, B n → Option ℤ) (n : ℤ) :
    Module.Free R ((weightedFreeComplex R w).X.X n) := by
  change Module.Free R (B n →₀ R)
  infer_instance

private theorem weightedFreeComplex_filtration_free (R : Type u) [Ring R]
    {B : ℤ → Type u} (w : ∀ n, B n → Option ℤ) (i n : ℤ) :
    Module.Free R (((weightedFreeComplex R w).filtration.obj (op i)).X n) := by
  change Module.Free R (stepSet (w n) i →₀ R)
  infer_instance

/-- The inclusion of filtration steps `i + 1 → i`, whose cokernel is the `i`-th graded piece. -/
private abbrev gradedStep (i : ℤ) : op (i + 1) ⟶ op i :=
  (homOfLE (Int.le_add_one le_rfl) : i ⟶ i + 1).op

private theorem weightedFreeComplex_gradedPiece_free (R : Type u) [Ring R]
    {B : ℤ → Type u} (w : ∀ n, B n → Option ℤ) (i n : ℤ) :
    Module.Free R (((FilteredObject.gr i).obj (weightedFreeComplex R w)).X n) := by
  let a := gradedStep i
  let e := Limits.PreservesCokernel.iso
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n)
    ((weightedFreeComplex R w).filtration.diagram.map a)
  have hf : Module.Free R ↥(Limits.cokernel (C := ModuleCat.{u} R)
      (((weightedFreeComplex R w).filtration.diagram.map a).f n)) :=
    cokernel_lmapDomain_free R _
  exact Module.Free.of_equiv' hf e.toLinearEquiv.symm

private noncomputable def freeZeroComplexDesc {R : Type u} [Ring R] {B : ℤ → Type u}
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (v : ∀ n, B n → K.cycles n) :
    freeZeroComplex R B ⟶ K where
  f n := ModuleCat.ofHom (Finsupp.linearCombination R (v n)) ≫ K.iCycles n
  comm' n m _ := by simp [freeZeroComplex]

private theorem freeZeroComplexDesc_epi_homologyMap {R : Type u} [Ring R]
    {B : ℤ → Type u} (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (v : ∀ n, B n → K.cycles n) (n : ℤ) (hv : Function.Surjective (v n)) :
    Epi (HomologicalComplex.homologyMap (freeZeroComplexDesc K v) n) := by
  let P := freeZeroComplex R B
  let e : P.cycles n ≅ P.X n := P.iCyclesIso n (n + 1) (by simp) rfl
  have he : e.inv ≫ HomologicalComplex.cyclesMap (freeZeroComplexDesc K v) n =
      ModuleCat.ofHom (Finsupp.linearCombination R (v n)) := by
    rw [← cancel_mono (K.iCycles n), Category.assoc,
      HomologicalComplex.cyclesMap_i]
    change e.inv ≫ e.hom ≫ _ = _
    simp [e, freeZeroComplexDesc]
  have hc : Epi (ModuleCat.ofHom (Finsupp.linearCombination R (v n))) := by
    rw [ModuleCat.epi_iff_surjective]
    intro x
    obtain ⟨b, rfl⟩ := hv x
    exact ⟨Finsupp.single b 1, by simp⟩
  exact ShortComplex.epi_homologyMap_of_epi_cyclesMap' _ (epi_of_epi_fac he)

private abbrev CycleGenerator {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (n : ℤ) :=
  K.X.cycles n ⊕ Σ i : ℤ, (K.filtration.obj (op i)).cycles n

private def cycleWeight {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (n : ℤ) :
    CycleGenerator K n → Option ℤ
  | Sum.inl _ => none
  | Sum.inr ⟨i, _⟩ => some i

private noncomputable def cycleValue {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (n : ℤ) :
    CycleGenerator K n → K.X.cycles n
  | Sum.inl x => x
  | Sum.inr ⟨i, x⟩ => HomologicalComplex.cyclesMap (K.filtration.ι.app (op i)) n x

private noncomputable def filteredCycleValue {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (i n : ℤ) :
    stepSet (cycleWeight K n) i → (K.filtration.obj (op i)).cycles n := by
  rintro ⟨b, hb⟩
  rcases b with x | ⟨j, x⟩
  · exfalso
    rcases hb with ⟨j, hj, _⟩
    cases hj
  · have hij : i ≤ j := by simpa [stepSet, cycleWeight] using hb
    exact HomologicalComplex.cyclesMap
      (K.filtration.diagram.map (homOfLE hij).op) n x

private theorem filteredCycleValue_naturality {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (i n : ℤ)
    (b : stepSet (cycleWeight K n) i) :
    HomologicalComplex.cyclesMap (K.filtration.ι.app (op i)) n
        (filteredCycleValue K i n b) = cycleValue K n b.val := by
  rcases b with ⟨b, hb⟩
  rcases b with x | ⟨j, x⟩
  · rcases hb with ⟨j, hj, _⟩
    cases hj
  · change (HomologicalComplex.cyclesMap (K.filtration.diagram.map _) n ≫
      HomologicalComplex.cyclesMap (K.filtration.ι.app (op i)) n) x = _
    rw [← HomologicalComplex.cyclesMap_comp]
    have hnat := K.filtration.ι.naturality
      ((homOfLE (show i ≤ j by simpa [stepSet, cycleWeight] using hb)).op)
    dsimp at hnat
    rw [Category.comp_id] at hnat
    change K.filtration.diagram.map _ ≫ K.filtration.ι.app (op i) =
      K.filtration.ι.app (op j) at hnat
    rw [hnat]
    rfl

private theorem filteredCycleValue_surjective {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (i n : ℤ) :
    Function.Surjective (filteredCycleValue K i n) := by
  intro x
  refine ⟨⟨Sum.inr ⟨i, x⟩, ⟨i, rfl, le_rfl⟩⟩, ?_⟩
  change HomologicalComplex.cyclesMap (K.filtration.diagram.map (𝟙 (op i))) n x = x
  simp

private noncomputable def weightedFreeDesc {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ)
    {B : ℤ → Type u} (w : ∀ n, B n → Option ℤ)
    (v : ∀ n, B n → K.X.cycles n)
    (vi : ∀ i n, stepSet (w n) i → (K.filtration.obj (op i)).cycles n)
    (hv : ∀ i n (b : stepSet (w n) i),
      HomologicalComplex.cyclesMap (K.filtration.ι.app (op i)) n (vi i n b) = v n b.val) :
    weightedFreeComplex R w ⟶ K :=
  FilteredObject.homMk (freeZeroComplexDesc K.X v)
    (fun i => freeZeroComplexDesc (K.filtration.obj i) (vi i.unop))
    (by
      intro i
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext'
      intro b
      apply LinearMap.ext_ring
      change ((K.filtration.ι.app i).f n)
          ((K.filtration.obj i).iCycles n
            (Finsupp.linearCombination R (vi i.unop n)
              (Finsupp.single b 1))) =
        K.X.iCycles n (Finsupp.linearCombination R (v n)
          (Finsupp.mapDomain Subtype.val (Finsupp.single b 1)))
      simp only [Finsupp.linearCombination_single, Finsupp.mapDomain_single, one_smul]
      have h := hv i.unop n b
      apply_fun (K.X.iCycles n) at h
      change (HomologicalComplex.cyclesMap (K.filtration.ι.app i) n ≫ K.X.iCycles n)
        (vi i.unop n b) = _ at h
      exact (congrArg
        (fun g : (K.filtration.obj i).cycles n ⟶ K.X.X n =>
          g (vi i.unop n b))
        (HomologicalComplex.cyclesMap_i (K.filtration.ι.app i) n)).symm.trans h)

private noncomputable def cycleAugmentation {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) :
    weightedFreeComplex R (cycleWeight K) ⟶ K :=
  weightedFreeDesc K (cycleWeight K) (cycleValue K) (filteredCycleValue K)
    (filteredCycleValue_naturality K)

private theorem cycleAugmentation_epi_homologyMap {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (n : ℤ) :
    Epi (HomologicalComplex.homologyMap (cycleAugmentation K).hom n) :=
  freeZeroComplexDesc_epi_homologyMap K.X (cycleValue K) n
    (fun x => ⟨Sum.inl x, rfl⟩)

private theorem cycleAugmentation_filtration_epi_homologyMap {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (i n : ℤ) :
    Epi (HomologicalComplex.homologyMap ((cycleAugmentation K).natTrans.app (op i)) n) :=
  freeZeroComplexDesc_epi_homologyMap (K.filtration.obj (op i))
    (filteredCycleValue K i) n (filteredCycleValue_surjective K i n)

private theorem mappingCone_free {R : Type u} [Ring R]
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (g : A ⟶ B) (n : ℤ)
    (hA : Module.Free R (A.X (n + 1))) (hB : Module.Free R (B.X n)) :
    Module.Free R ((CochainComplex.mappingCone g).X n) := by
  let e := HomologicalComplex.homotopyCofiber.XIsoBiprod g n (n + 1) rfl
  let e' := ModuleCat.biprodIsoProd (A.X (n + 1)) (B.X n)
  exact Module.Free.of_equiv (e ≪≫ e').toLinearEquiv.symm

private theorem filteredMappingCone_free {R : Type u} [Ring R]
    {A B : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (g : A ⟶ B) (hA : ∀ n, Module.Free R (A.X.X n))
    (hB : ∀ n, Module.Free R (B.X.X n)) (n : ℤ) :
    Module.Free R ((filteredMappingCone g).X.X n) :=
  mappingCone_free g.hom n (hA _) (hB _)

private theorem filteredMappingCone_filtration_free {R : Type u} [Ring R]
    {A B : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (g : A ⟶ B) (hA : ∀ i n, Module.Free R ((A.filtration.obj (op i)).X n))
    (hB : ∀ i n, Module.Free R ((B.filtration.obj (op i)).X n)) (i n : ℤ) :
    Module.Free R (((filteredMappingCone g).filtration.obj (op i)).X n) :=
  mappingCone_free (g.natTrans.app (op i)) n (hA _ _) (hB _ _)

private noncomputable def cokernelBiprodMapIso {C : Type*} [Category C] [Abelian C]
    {A B A' B' : C} (a : A ⟶ A') (b : B ⟶ B') :
    Limits.cokernel (Limits.biprod.map a b) ≅
      Limits.biprod (Limits.cokernel a) (Limits.cokernel b) := by
  let f := Limits.biprod.map a b
  let q := Limits.biprod.map (Limits.cokernel.π a) (Limits.cokernel.π b)
  have hq : f ≫ q = 0 := by
    ext <;> simp [f, q]
  let x := Limits.cokernel.desc a
    (Limits.biprod.inl ≫ Limits.cokernel.π f) (by
      rw [← Limits.biprod.inl_map_assoc a b]
      change Limits.biprod.inl ≫ f ≫ Limits.cokernel.π f = 0
      rw [Limits.cokernel.condition, Limits.comp_zero])
  let y := Limits.cokernel.desc b
    (Limits.biprod.inr ≫ Limits.cokernel.π f) (by
      rw [← Limits.biprod.inr_map_assoc a b]
      change Limits.biprod.inr ≫ f ≫ Limits.cokernel.π f = 0
      rw [Limits.cokernel.condition, Limits.comp_zero])
  refine ⟨Limits.cokernel.desc f q hq, Limits.biprod.desc x y, ?_, ?_⟩
  · apply (cancel_epi (Limits.cokernel.π f)).mp
    simp only [Limits.cokernel.π_desc_assoc]
    apply Limits.biprod.hom_ext'
    · simp [q, x, f]
    · simp [q, y, f]
  · apply Limits.biprod.hom_ext'
    · apply (cancel_epi (Limits.cokernel.π a)).mp
      simp [q, x]
    · apply (cancel_epi (Limits.cokernel.π b)).mp
      simp [q, y]

private noncomputable def cokernelMappingConeMapIso {C : Type*} [Category C] [Abelian C]
    {A B A' B' : CochainComplex C ℤ} (g : A ⟶ B) (g' : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : g ≫ b = a ≫ g') (n : ℤ) :
    Limits.cokernel ((CochainComplex.mappingCone.map g g' a b h).f n) ≅
      Limits.biprod (Limits.cokernel (a.f (n + 1))) (Limits.cokernel (b.f n)) := by
  let e : (CochainComplex.mappingCone g).X n ≅ Limits.biprod (A.X (n + 1)) (B.X n) :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod g n (n + 1) rfl
  let e' : (CochainComplex.mappingCone g').X n ≅ Limits.biprod (A'.X (n + 1)) (B'.X n) :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod g' n (n + 1) rfl
  refine Limits.cokernel.mapIso _ (Limits.biprod.map (a.f (n + 1)) (b.f n)) e e' ?_ ≪≫
    cokernelBiprodMapIso _ _
  apply CochainComplex.mappingCone.ext_from g (n + 1) n rfl
  · simp only [CochainComplex.mappingCone.map, Category.assoc,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v]
    simp [CochainComplex.mappingCone.inl, e, e', ← Category.assoc]
  · simp only [CochainComplex.mappingCone.map, Category.assoc,
      CochainComplex.mappingCone.inr_f_desc_f_assoc, HomologicalComplex.comp_f]
    simp [CochainComplex.mappingCone.inr, e, e', ← Category.assoc]

private theorem filteredMappingCone_gradedPiece_free {R : Type u} [Ring R]
    {A B : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (g : A ⟶ B)
    (hA : ∀ i n, Module.Free R (((FilteredObject.gr i).obj A).X n))
    (hB : ∀ i n, Module.Free R (((FilteredObject.gr i).obj B).X n)) (i n : ℤ) :
    Module.Free R (((FilteredObject.gr i).obj (filteredMappingCone g)).X n) := by
  let a := gradedStep i
  let E := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n
  let E' := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) (n + 1)
  let eA := Limits.PreservesCokernel.iso E' (A.filtration.diagram.map a)
  let eB := Limits.PreservesCokernel.iso E (B.filtration.diagram.map a)
  have hfA : Module.Free R ↥(Limits.cokernel (C := ModuleCat.{u} R)
      ((A.filtration.diagram.map a).f (n + 1))) :=
    Module.Free.of_equiv' (hA i (n + 1)) eA.toLinearEquiv
  have hfB : Module.Free R ↥(Limits.cokernel (C := ModuleCat.{u} R)
      ((B.filtration.diagram.map a).f n)) :=
    Module.Free.of_equiv' (hB i n) eB.toLinearEquiv
  let e := Limits.PreservesCokernel.iso E ((filteredMappingCone g).filtration.diagram.map a)
  let e' := cokernelMappingConeMapIso (g.natTrans.app (op (i + 1))) (g.natTrans.app (op i))
    (A.filtration.diagram.map a) (B.filtration.diagram.map a) (g.natTrans.naturality a).symm n
  let e'' := ModuleCat.biprodIsoProd (Limits.cokernel ((A.filtration.diagram.map a).f (n + 1)))
    (Limits.cokernel ((B.filtration.diagram.map a).f n))
  exact Module.Free.of_equiv (e ≪≫ e' ≪≫ e'').toLinearEquiv.symm

private abbrev BoundaryGenerator {R : Type u} [Ring R]
    {P K : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ K) (n : ℤ) :=
  {zy : P.cycles n × K.X (n - 1) //
    K.d (n - 1) n zy.2 = f.f n (P.iCycles n zy.1)}

private theorem map_boundary {R : Type u} [Ring R]
    {P K P' K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ K) (f' : P' ⟶ K') (a : P ⟶ P') (b : K ⟶ K')
    (h : f ≫ b = a ≫ f') (n : ℤ) (z : P.cycles n) (y : K.X (n - 1))
    (hy : K.d (n - 1) n y = f.f n (P.iCycles n z)) :
    K'.d (n - 1) n (b.f (n - 1) y) =
      f'.f n (P'.iCycles n (HomologicalComplex.cyclesMap a n z)) := by
  calc
    _ = b.f n (K.d (n - 1) n y) :=
      congrArg (fun k : K.X (n - 1) ⟶ K'.X n => k y) (b.comm (n - 1) n)
    _ = b.f n (f.f n (P.iCycles n z)) := congrArg (b.f n) hy
    _ = f'.f n (a.f n (P.iCycles n z)) :=
      congrArg (fun k : P.X n ⟶ K'.X n => k (P.iCycles n z))
        (HomologicalComplex.congr_hom h n)
    _ = _ := congrArg (f'.f n)
      (congrArg (fun k : P.cycles n ⟶ P'.X n => k z)
        (HomologicalComplex.cyclesMap_i a n)).symm

private noncomputable def boundaryGeneratorMap {R : Type u} [Ring R]
    {P K P' K' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ K) (f' : P' ⟶ K') (a : P ⟶ P') (b : K ⟶ K')
    (h : f ≫ b = a ≫ f') (n : ℤ) : BoundaryGenerator f n → BoundaryGenerator f' n :=
  fun z => ⟨⟨HomologicalComplex.cyclesMap a n z.val.1, b.f (n - 1) z.val.2⟩,
    map_boundary f f' a b h n _ _ z.property⟩

private theorem boundaryGeneratorMap_comp {R : Type u} [Ring R]
    {P K P' K' P'' K'' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ K) (f' : P' ⟶ K') (f'' : P'' ⟶ K'')
    (a : P ⟶ P') (b : K ⟶ K') (a' : P' ⟶ P'') (b' : K' ⟶ K'')
    (h : f ≫ b = a ≫ f') (h' : f' ≫ b' = a' ≫ f'')
    (h'' : f ≫ (b ≫ b') = (a ≫ a') ≫ f'') (n : ℤ) (z : BoundaryGenerator f n) :
    boundaryGeneratorMap f' f'' a' b' h' n (boundaryGeneratorMap f f' a b h n z) =
      boundaryGeneratorMap f f'' (a ≫ a') (b ≫ b') h'' n z :=
  Subtype.ext <| Prod.ext (congrArg (fun k : P.cycles n ⟶ P''.cycles n => k z.val.1)
    (HomologicalComplex.cyclesMap_comp a a' n)).symm rfl

private abbrev BoundaryIndex {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (f : P ⟶ K) (n : ℤ) :=
  BoundaryGenerator f.hom n ⊕ Σ i : ℤ, BoundaryGenerator (f.natTrans.app (op i)) n

private def boundaryWeight {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (f : P ⟶ K) (n : ℤ) : BoundaryIndex f n → Option ℤ
  | Sum.inl _ => none
  | Sum.inr ⟨i, _⟩ => some i

private noncomputable def boundaryValue {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (f : P ⟶ K) (n : ℤ) : BoundaryIndex f n → BoundaryGenerator f.hom n
  | Sum.inl z => z
  | Sum.inr ⟨i, z⟩ => boundaryGeneratorMap _ _
      (P.filtration.ι.app (op i)) (K.filtration.ι.app (op i)) (f.comm (op i)) n z

private noncomputable def filteredBoundaryValue {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (f : P ⟶ K) (i n : ℤ) :
    stepSet (boundaryWeight f n) i → BoundaryGenerator (f.natTrans.app (op i)) n := by
  rintro ⟨b, hb⟩
  rcases b with z | ⟨j, z⟩
  · exfalso
    rcases hb with ⟨j, hj, _⟩
    cases hj
  · have hij : i ≤ j := by simpa [stepSet, boundaryWeight] using hb
    exact boundaryGeneratorMap _ _ (P.filtration.diagram.map (homOfLE hij).op)
      (K.filtration.diagram.map (homOfLE hij).op)
      (f.natTrans.naturality (homOfLE hij).op).symm n z

private theorem filteredBoundaryValue_naturality {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (f : P ⟶ K) (i n : ℤ) (b : stepSet (boundaryWeight f n) i) :
    boundaryGeneratorMap _ _ (P.filtration.ι.app (op i)) (K.filtration.ι.app (op i))
        (f.comm (op i)) n (filteredBoundaryValue f i n b) = boundaryValue f n b.val := by
  rcases b with ⟨b, hb⟩
  rcases b with z | ⟨j, z⟩
  · rcases hb with ⟨j, hj, _⟩
    cases hj
  · let a := (homOfLE (show i ≤ j by simpa [stepSet, boundaryWeight] using hb)).op
    have hP : P.filtration.diagram.map a ≫ P.filtration.ι.app (op i) =
        P.filtration.ι.app (op j) := (P.filtration.ι.naturality a).trans (Category.comp_id _)
    have hK : K.filtration.diagram.map a ≫ K.filtration.ι.app (op i) =
        K.filtration.ι.app (op j) := (K.filtration.ι.naturality a).trans (Category.comp_id _)
    apply Subtype.ext
    apply Prod.ext
    · change (HomologicalComplex.cyclesMap (P.filtration.diagram.map a) n ≫
        HomologicalComplex.cyclesMap (P.filtration.ι.app (op i)) n) z.val.1 = _
      rw [← HomologicalComplex.cyclesMap_comp, hP]
      rfl
    · exact congrArg
        (fun k : K.filtration.obj (op j) ⟶ K.X => k.f (n - 1) z.val.2) hK

private noncomputable def boundaryAugmentation {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ} (f : P ⟶ K) :
    weightedFreeComplex R (boundaryWeight f) ⟶ P :=
  weightedFreeDesc P (boundaryWeight f) (fun n b => (boundaryValue f n b).val.1)
    (fun i n b => (filteredBoundaryValue f i n b).val.1)
    (fun i n b => congrArg (fun z => z.val.1) (filteredBoundaryValue_naturality f i n b))

private noncomputable def freeZeroComplexHomotopy {R : Type u} [Ring R]
    {B : ℤ → Type u} {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : freeZeroComplex R B ⟶ K) (y : ∀ n, B n → K.X (n - 1))
    (hy : ∀ n b, K.d (n - 1) n (y n b) = f.f n (Finsupp.single b 1)) :
    Homotopy f 0 := by
  classical
  let H : ∀ n m, (freeZeroComplex R B).X n ⟶ K.X m := fun n m =>
    if h : n - 1 = m then
      ModuleCat.ofHom (Finsupp.linearCombination R (y n)) ≫ (K.XIsoOfEq h).hom
    else 0
  refine ⟨H, ?_, ?_⟩
  · intro n m h
    dsimp [H]
    rw [dite_eq_right]
    intro h'
    apply h
    change m + 1 = n
    omega
  · intro n
    rw [dNext_eq H (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
      prevD_eq H (show (ComplexShape.up ℤ).Rel (n - 1) n by change (n - 1) + 1 = n; omega)]
    change f.f n = 0 ≫ H (n + 1) n + H n (n - 1) ≫ K.d (n - 1) n + 0
    simp only [Limits.zero_comp, zero_add, add_zero, H, dite_eq_left rfl,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id]
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro b
    apply LinearMap.ext_ring
    change f.f n (Finsupp.single b 1) =
      K.d (n - 1) n (Finsupp.linearCombination R (y n) (Finsupp.single b 1))
    simpa only [Finsupp.linearCombination_single, one_smul] using (hy n b).symm

private noncomputable def boundaryAugmentationHomotopy {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ} (f : P ⟶ K) :
    Homotopy ((boundaryAugmentation f).hom ≫ f.hom) 0 :=
  freeZeroComplexHomotopy _ (fun n b => (boundaryValue f n b).val.2) (by
    intro n b
    change K.X.d (n - 1) n (boundaryValue f n b).val.2 =
      f.hom.f n (P.X.iCycles n
        (Finsupp.linearCombination R (fun b => (boundaryValue f n b).val.1)
          (Finsupp.single b 1)))
    simpa only [Finsupp.linearCombination_single, one_smul] using (boundaryValue f n b).property)

private noncomputable def boundaryAugmentationFiltrationHomotopy {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ} (f : P ⟶ K) (i : ℤ) :
    Homotopy ((boundaryAugmentation f).natTrans.app (op i) ≫ f.natTrans.app (op i)) 0 :=
  freeZeroComplexHomotopy _ (fun n b => (filteredBoundaryValue f i n b).val.2) (by
    intro n b
    change (K.filtration.obj (op i)).d (n - 1) n (filteredBoundaryValue f i n b).val.2 =
      (f.natTrans.app (op i)).f n ((P.filtration.obj (op i)).iCycles n
        (Finsupp.linearCombination R (fun b => (filteredBoundaryValue f i n b).val.1)
          (Finsupp.single b 1)))
    simpa only [Finsupp.linearCombination_single, one_smul] using
      (filteredBoundaryValue f i n b).property)

private theorem freeZeroComplexHomotopy_hom {R : Type u} [Ring R]
    {B : ℤ → Type u} {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : freeZeroComplex R B ⟶ K) (y : ∀ n, B n → K.X (n - 1))
    (hy : ∀ n b, K.d (n - 1) n (y n b) = f.f n (Finsupp.single b 1)) (n : ℤ) :
    (freeZeroComplexHomotopy f y hy).hom n (n - 1) =
      ModuleCat.ofHom (Finsupp.linearCombination R (y n)) := by
  simp [freeZeroComplexHomotopy]

private theorem boundaryAugmentationHomotopy_naturality {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (f : P ⟶ K) (i n m : ℤ) :
    (((weightedFreeComplex R (boundaryWeight f)).filtration.ι.app (op i)).f n) ≫
        (boundaryAugmentationHomotopy f).hom n m =
      (boundaryAugmentationFiltrationHomotopy f i).hom n m ≫
        (K.filtration.ι.app (op i)).f m := by
  by_cases h : n - 1 = m
  · subst m
    dsimp only [boundaryAugmentationHomotopy, boundaryAugmentationFiltrationHomotopy]
    rw [freeZeroComplexHomotopy_hom, freeZeroComplexHomotopy_hom]
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro b
    apply LinearMap.ext_ring
    change Finsupp.linearCombination R (fun b => (boundaryValue f n b).val.2)
        (Finsupp.mapDomain Subtype.val (Finsupp.single b 1)) =
      (K.filtration.ι.app (op i)).f (n - 1)
        (Finsupp.linearCombination R (fun b => (filteredBoundaryValue f i n b).val.2)
          (Finsupp.single b 1))
    simp only [Finsupp.mapDomain_single, Finsupp.linearCombination_single, one_smul]
    exact (congrArg (fun z => z.val.2) (filteredBoundaryValue_naturality f i n b)).symm
  · have h' : ¬ (ComplexShape.up ℤ).Rel m n := by change ¬ m + 1 = n; omega
    rw [(boundaryAugmentationHomotopy f).zero n m h',
      (boundaryAugmentationFiltrationHomotopy f i).zero n m h']
    simp

private theorem mappingCone_inl_desc_homotopy {C : Type*} [Category C] [Abelian C]
    {A B K : CochainComplex C ℤ} (g : A ⟶ B) (f : B ⟶ K)
    (H : Homotopy (g ≫ f) 0) (n : ℤ) :
    (CochainComplex.mappingCone.inl g).v (n + 1) n (by omega) ≫
        (HomologicalComplex.homotopyCofiber.desc g f H).f n = H.hom (n + 1) n :=
  HomologicalComplex.homotopyCofiber.inlX_desc_f g f H (n + 1) n rfl

private noncomputable def filteredMappingConeDesc {C : Type*} [Category C] [Abelian C]
    {A B K : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ}
    (g : A ⟶ B) (f : B ⟶ K) (H : Homotopy (g.hom ≫ f.hom) 0)
    (Hi : ∀ i : ℤ, Homotopy (g.natTrans.app (op i) ≫ f.natTrans.app (op i)) 0)
    (hH : ∀ i n m, (A.filtration.ι.app (op i)).f n ≫ H.hom n m =
      (Hi i).hom n m ≫ (K.filtration.ι.app (op i)).f m) :
    filteredMappingCone g ⟶ K :=
  FilteredObject.homMk (HomologicalComplex.homotopyCofiber.desc g.hom f.hom H)
    (fun i => HomologicalComplex.homotopyCofiber.desc
      (g.natTrans.app i) (f.natTrans.app i) (Hi i.unop))
    (by
      intro i
      apply HomologicalComplex.Hom.ext
      funext n
      apply CochainComplex.mappingCone.ext_from (g.natTrans.app i) (n + 1) n rfl
      · simp only [HomologicalComplex.comp_f]
        change _ = (CochainComplex.mappingCone.inl (g.natTrans.app i)).v (n + 1) n _ ≫
          (CochainComplex.mappingCone.map (g.natTrans.app i) g.hom
            (A.filtration.ι.app i) (B.filtration.ι.app i) (g.comm i)).f n ≫ _
        simp only [CochainComplex.mappingCone.map, ← Category.assoc,
          CochainComplex.mappingCone.inl_v_desc_f,
          CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
          CochainComplex.HomComplex.Cochain.ofHom_v, mappingCone_inl_desc_homotopy]
        rw [Category.assoc, mappingCone_inl_desc_homotopy]
        exact (hH i.unop (n + 1) n).symm
      · simp only [HomologicalComplex.comp_f]
        change _ = (CochainComplex.mappingCone.inr (g.natTrans.app i)).f n ≫
          (CochainComplex.mappingCone.map (g.natTrans.app i) g.hom
            (A.filtration.ι.app i) (B.filtration.ι.app i) (g.comm i)).f n ≫ _
        simp only [CochainComplex.mappingCone.map, ← Category.assoc,
          CochainComplex.mappingCone.inr_f_desc_f, HomologicalComplex.comp_f]
        simp only [CochainComplex.mappingCone.inr, HomologicalComplex.homotopyCofiber.inr_f,
          Category.assoc, HomologicalComplex.homotopyCofiber.inrX_desc_f]
        exact HomologicalComplex.congr_hom (f.comm i) n)

private noncomputable def cellExtensionMap {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ} (f : P ⟶ K) :
    filteredMappingCone (boundaryAugmentation f) ⟶ K :=
  filteredMappingConeDesc (boundaryAugmentation f) f (boundaryAugmentationHomotopy f)
    (boundaryAugmentationFiltrationHomotopy f) (boundaryAugmentationHomotopy_naturality f)

private theorem cellExtensionMap_extends {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ} (f : P ⟶ K) :
    filteredMappingConeInr (boundaryAugmentation f) ≫ cellExtensionMap f = f :=
  FilteredObject.hom_ext (HomologicalComplex.homotopyCofiber.inr_desc _ _ _)

private theorem mappingCone_boundary_of_freeZero {R : Type u} [Ring R]
    {B : ℤ → Type u} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : freeZeroComplex R B ⟶ P) (n : ℤ) (b : B n) (c : P.X n)
    (hc : g.f n (Finsupp.single b 1) = c) :
    ∃ w : (CochainComplex.mappingCone g).X (n - 1),
      (CochainComplex.mappingCone g).d (n - 1) n w = (CochainComplex.mappingCone.inr g).f n c := by
  subst hc
  refine ⟨(CochainComplex.mappingCone.inl g).v n (n - 1) (by omega)
    (Finsupp.single b 1), ?_⟩
  have hd := CochainComplex.mappingCone.inl_v_d g n (n - 1) (n + 1) (by omega) (by omega)
  change _ = _ - (0 : (freeZeroComplex R B).X n ⟶ _ ) ≫ _ at hd
  simp only [Limits.zero_comp, sub_zero] at hd
  exact congrArg (fun k : (freeZeroComplex R B).X n ⟶ _ => k (Finsupp.single b 1)) hd

/-- A map `g` kills the homology classes killed by `f` once it kills the boundary cycles of `f`. -/
private theorem homologyMap_eq_zero_of_kills_boundaryCycles {R : Type u} [Ring R]
    {P K Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ K) (g : P ⟶ Q) (n : ℤ)
    (h : ∀ z : BoundaryGenerator f n,
      ∃ w : Q.X (n - 1), Q.d (n - 1) n w = g.f n (P.iCycles n z.val.1))
    (x : P.homology n) (hx : HomologicalComplex.homologyMap f n x = 0) :
    HomologicalComplex.homologyMap g n x = 0 := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (P.homologyπ n)).mp inferInstance x
  obtain ⟨y, hy⟩ := (homologyMap_eq_zero_iff f n x z hz).mp hx
  exact (homologyMap_eq_zero_iff g n x z hz).mpr (h ⟨⟨z, y⟩, hy⟩)

private theorem cellExtension_kills_boundaryCycle {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (f : P ⟶ K) (n : ℤ) (z : BoundaryGenerator f.hom n) :
    ∃ w : (filteredMappingCone (boundaryAugmentation f)).X.X (n - 1),
      (filteredMappingCone (boundaryAugmentation f)).X.d (n - 1) n w =
        (filteredMappingConeInr (boundaryAugmentation f)).hom.f n (P.X.iCycles n z.val.1) := by
  refine mappingCone_boundary_of_freeZero (boundaryAugmentation f).hom n (Sum.inl z) _ ?_
  change P.X.iCycles n (Finsupp.linearCombination R
    (fun b => (boundaryValue f n b).val.1) (Finsupp.single (Sum.inl z) 1)) = _
  simp [boundaryValue]

private theorem cellExtension_filtration_kills_boundaryCycle {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (f : P ⟶ K) (i n : ℤ) (z : BoundaryGenerator (f.natTrans.app (op i)) n) :
    ∃ w : ((filteredMappingCone (boundaryAugmentation f)).filtration.obj (op i)).X (n - 1),
      ((filteredMappingCone (boundaryAugmentation f)).filtration.obj (op i)).d (n - 1) n w =
        ((filteredMappingConeInr (boundaryAugmentation f)).natTrans.app (op i)).f n
          ((P.filtration.obj (op i)).iCycles n z.val.1) := by
  let b : stepSet (boundaryWeight f n) i := ⟨Sum.inr ⟨i, z⟩, ⟨i, rfl, le_rfl⟩⟩
  have hz : (filteredBoundaryValue f i n b).val.1 = z.val.1 := by
    change HomologicalComplex.cyclesMap (P.filtration.diagram.map (𝟙 (op i))) n z.val.1 = z.val.1
    simp
  refine mappingCone_boundary_of_freeZero ((boundaryAugmentation f).natTrans.app (op i)) n b _ ?_
  change (P.filtration.obj (op i)).iCycles n (Finsupp.linearCombination R
    (fun b => (filteredBoundaryValue f i n b).val.1) (Finsupp.single b 1)) = _
  simp only [Finsupp.linearCombination_single, one_smul, hz]

private theorem cellExtension_kills_homologyKernel {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (f : P ⟶ K) (n : ℤ) (x : P.X.homology n)
    (hx : HomologicalComplex.homologyMap f.hom n x = 0) :
    HomologicalComplex.homologyMap
      (filteredMappingConeInr (boundaryAugmentation f)).hom n x = 0 := by
  exact homologyMap_eq_zero_of_kills_boundaryCycles _ _ n (cellExtension_kills_boundaryCycle f n)
    x hx

private theorem cellExtension_filtration_kills_homologyKernel {R : Type u} [Ring R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (f : P ⟶ K) (i n : ℤ) (x : (P.filtration.obj (op i)).homology n)
    (hx : HomologicalComplex.homologyMap (f.natTrans.app (op i)) n x = 0) :
    HomologicalComplex.homologyMap
      ((filteredMappingConeInr (boundaryAugmentation f)).natTrans.app (op i)) n x = 0 := by
  exact homologyMap_eq_zero_of_kills_boundaryCycles _ _ n
    (cellExtension_filtration_kills_boundaryCycle f i n) x hx

private noncomputable def resolutionStage {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) : ℕ → Over K
  | 0 => Over.mk (cycleAugmentation K)
  | m + 1 => Over.mk (cellExtensionMap (resolutionStage K m).hom)

private noncomputable def resolutionStageInclusion {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (m : ℕ) :
    resolutionStage K m ⟶ resolutionStage K (m + 1) :=
  Over.homMk (filteredMappingConeInr (boundaryAugmentation (resolutionStage K m).hom))
    (cellExtensionMap_extends _)

private noncomputable def resolutionDiagram {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) :
    ℕ ⥤ FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ :=
  Functor.ofSequence (resolutionStageInclusion K) ⋙ Over.forget K

private noncomputable def resolutionCocone {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) :
    Limits.Cocone (resolutionDiagram K) where
  pt := K
  ι := NatTrans.ofSequence (fun m => (resolutionStage K m).hom) (by
    intro m
    simpa [resolutionDiagram, resolutionStageInclusion, resolutionStage] using
      cellExtensionMap_extends (resolutionStage K m).hom)

section FilteredColimit

open Limits

variable {C : Type*} [Category C] [Abelian C]
    {I : Type*} [Category I]
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]

private def filtrationFunctor : FilteredObject C I ⥤ (I ⥤ C) where
  obj P := P.filtration.diagram
  map f := f.natTrans

private abbrev underlyingDiagram (D : ℕ ⥤ FilteredObject C I) : ℕ ⥤ C :=
  D ⋙ FilteredObject.forget (C := C) (I := I)

private abbrev filtrationDiagrams (D : ℕ ⥤ FilteredObject C I) : I ⥤ (ℕ ⥤ C) :=
  (D ⋙ filtrationFunctor).flip

private def filtrationDiagramInclusion (D : ℕ ⥤ FilteredObject C I) (i : I) :
    (filtrationDiagrams D).obj i ⟶ underlyingDiagram D where
  app m := (D.obj m).filtration.ι.app i
  naturality _m _n f := (D.map f).comm i

private noncomputable def colimitFiltrationInclusion (D : ℕ ⥤ FilteredObject C I) :
    filtrationDiagrams D ⋙ colim ⟶ (Functor.const I).obj (colimit (underlyingDiagram D)) where
  app i := colim.map (filtrationDiagramInclusion D i)
  naturality i j f := by
    change colim.map ((filtrationDiagrams D).map f) ≫
        colim.map (filtrationDiagramInclusion D j) =
      colim.map (filtrationDiagramInclusion D i) ≫ 𝟙 _
    rw [Category.comp_id, ← colim.map_comp]
    congr 1
    ext m
    exact ((D.obj m).filtration.ι.naturality f).trans (Category.comp_id _)

private noncomputable def filteredColimit (D : ℕ ⥤ FilteredObject C I) :
    FilteredObject C I := by
  have (i : I) (m : ℕ) : Mono ((filtrationDiagramInclusion D i).app m) :=
    inferInstanceAs (Mono ((D.obj m).filtration.ι.app i))
  have (i : I) : Mono (filtrationDiagramInclusion D i) :=
    NatTrans.mono_of_mono_app _
  have (i : I) : Mono ((colimitFiltrationInclusion D).app i) :=
    inferInstanceAs (Mono (colim.map (filtrationDiagramInclusion D i)))
  exact ⟨colimit (underlyingDiagram D), Filtration.ofDiagram _ (colimitFiltrationInclusion D)⟩

private noncomputable def filteredColimitι (D : ℕ ⥤ FilteredObject C I) (m : ℕ) :
    D.obj m ⟶ filteredColimit D :=
  FilteredObject.homMk (colimit.ι (underlyingDiagram D) m)
    (fun i => colimit.ι ((filtrationDiagrams D).obj i) m)
    (fun i => ι_colimMap (filtrationDiagramInclusion D i) m)

private theorem filteredColimitι_naturality (D : ℕ ⥤ FilteredObject C I)
    {m n : ℕ} (f : m ⟶ n) : D.map f ≫ filteredColimitι D n = filteredColimitι D m :=
  FilteredObject.hom_ext (colimit.w (underlyingDiagram D) f)

private noncomputable def filteredColimitDesc {D : ℕ ⥤ FilteredObject C I}
    (c : Cocone D) : filteredColimit D ⟶ c.pt :=
  FilteredObject.homMk
    (colimit.desc (underlyingDiagram D) ((FilteredObject.forget (C := C) (I := I)).mapCocone c))
    (fun i => colimit.desc ((filtrationDiagrams D).obj i)
      (((filtrationFunctor : FilteredObject C I ⥤ (I ⥤ C)) ⋙
        (evaluation I C).obj i).mapCocone c))
    (by
      intro i
      apply colimit.hom_ext
      intro m
      change colimit.ι ((filtrationDiagrams D).obj i) m ≫
        colimit.desc ((filtrationDiagrams D).obj i)
          (((filtrationFunctor : FilteredObject C I ⥤ (I ⥤ C)) ⋙
            (evaluation I C).obj i).mapCocone c) ≫ c.pt.filtration.ι.app i =
        colimit.ι ((filtrationDiagrams D).obj i) m ≫
          colim.map (filtrationDiagramInclusion D i) ≫
            colimit.desc _ ((FilteredObject.forget (C := C) (I := I)).mapCocone c)
      simp only [colim_map, ι_colimMap_assoc, colimit.ι_desc_assoc, colimit.ι_desc]
      exact (c.ι.app m).comm i)


private theorem filteredColimitι_desc {D : ℕ ⥤ FilteredObject C I}
    (c : Cocone D) (m : ℕ) :
    filteredColimitι D m ≫ filteredColimitDesc c = c.ι.app m :=
  FilteredObject.hom_ext (colimit.ι_desc ((FilteredObject.forget (C := C) (I := I)).mapCocone c) m)

end FilteredColimit

private theorem resolutionStage_free {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (m : ℕ) :
    (∀ n, Module.Free R ((resolutionStage K m).left.X.X n)) ∧
    (∀ i n, Module.Free R (((resolutionStage K m).left.filtration.obj (op i)).X n)) ∧
    (∀ i n, Module.Free R
      (((FilteredObject.gr i).obj (resolutionStage K m).left).X n)) := by
  induction m with
  | zero =>
      exact ⟨weightedFreeComplex_free R _, weightedFreeComplex_filtration_free R _,
        weightedFreeComplex_gradedPiece_free R _⟩
  | succ m hm =>
      exact ⟨filteredMappingCone_free _ (weightedFreeComplex_free R _) hm.1,
        filteredMappingCone_filtration_free _ (weightedFreeComplex_filtration_free R _) hm.2.1,
        filteredMappingCone_gradedPiece_free _ (weightedFreeComplex_gradedPiece_free R _) hm.2.2⟩

section HomologyColimit

open Limits

variable {A : Type*} [Category A] [Abelian A]

end HomologyColimit

private theorem moduleCat_exactColimits_nat (R : Type u) [Ring R] :
    HasExactColimitsOfShape ℕ (ModuleCat.{u} R) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  infer_instance

attribute [local instance] moduleCat_exactColimits_nat

private theorem moduleCat_forget_preservesColimits_nat (R : Type u) [Ring R] :
    Limits.PreservesColimitsOfShape ℕ (forget (ModuleCat.{u} R)) := by
  have : Limits.PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} R)) :=
    Limits.preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, 0} _
  infer_instance

attribute [local instance] moduleCat_forget_preservesColimits_nat

private theorem quasiIso_of_colimit_kills_kernels {R : Type u} [Ring R]
    (D : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (c : Limits.Cocone D)
    (hepi : ∀ n : ℤ, Epi (HomologicalComplex.homologyMap (c.ι.app 0) n))
    (hkill : ∀ (m : ℕ) (n : ℤ) (x : (D.obj m).homology n),
      HomologicalComplex.homologyMap (c.ι.app m) n x = 0 →
        HomologicalComplex.homologyMap (D.map (homOfLE (Nat.le_succ m))) n x = 0) :
    QuasiIso (Limits.colimit.desc D c) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n
  have := preservesColimitsOfShape_homologyFunctor (A := ModuleCat.{u} R) (J := ℕ)
    (ComplexShape.up ℤ) n
  have hc : Limits.IsColimit (H.mapCocone (Limits.colimit.cocone D)) :=
    Limits.isColimitOfPreserves H (Limits.colimit.isColimit D)
  have hfac (m : ℕ) : H.map (Limits.colimit.ι D m) ≫ H.map (Limits.colimit.desc D c) =
      H.map (c.ι.app m) := by rw [← H.map_comp, Limits.colimit.ι_desc]
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨m, y, hy⟩ := Limits.Concrete.isColimit_exists_rep (D ⋙ H) hc x
    have hy' : H.map (Limits.colimit.ι D m) y = x := hy
    have hz : H.map (c.ι.app m) y = 0 := by
      rw [← hfac]
      change H.map (Limits.colimit.desc D c) (H.map (Limits.colimit.ι D m) y) = 0
      rwa [hy']
    have hk := hkill m n y hz
    change H.map (D.map (homOfLE (Nat.le_succ m))) y = 0 at hk
    have hw := congrArg H.map (Limits.colimit.w D (homOfLE (Nat.le_succ m)))
    rw [H.map_comp] at hw
    rw [← hy', ← hw]
    change H.map (Limits.colimit.ι D (m + 1))
      (H.map (D.map (homOfLE (Nat.le_succ m))) y) = 0
    rw [hk, map_zero]
  · intro x
    obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
      (HomologicalComplex.homologyMap (c.ι.app 0) n)).mp (hepi n) x
    exact ⟨H.map (Limits.colimit.ι D 0) y,
      (congrArg (fun f : H.obj (D.obj 0) ⟶ H.obj c.pt => f y) (hfac 0)).trans hy⟩

section FreeColimit

open Limits

variable {R : Type u} [Ring R] (D : ℕ ⥤ ModuleCat.{u} R)
    (Q : ℕ → ModuleCat.{u} R) [Module.Free R (D.obj 0)] [∀ m, Module.Free R (Q m)]
    (e : ∀ m, (Q m × D.obj m) ≃ₗ[R] D.obj (m + 1))

private noncomputable def sequenceBasis : ∀ m, Σ B : Type u, Module.Basis B R (D.obj m)
  | 0 => ⟨Module.Free.ChooseBasisIndex R (D.obj 0), Module.Free.chooseBasis R (D.obj 0)⟩
  | m + 1 => ⟨Module.Free.ChooseBasisIndex R (Q m) ⊕ (sequenceBasis m).1,
      ((Module.Free.chooseBasis R (Q m)).prod (sequenceBasis m).2).map (e m)⟩

private theorem free_colimit_of_split_extensions
    (he : ∀ m (x : D.obj m), e m (0, x) = D.map (homOfLE (Nat.le_succ m)) x) :
    Module.Free R ↥(colimit D) := by
  classical
  let B (m : ℕ) := (sequenceBasis D Q e m).1
  let b (m : ℕ) : Module.Basis (B m) R (D.obj m) := (sequenceBasis D Q e m).2
  let E : ℕ ⥤ Type u := Functor.ofSequence (X := B)
    (fun m => (↾(Sum.inr : B m → B (m + 1))))
  let φ : E ⋙ ModuleCat.free R ⟶ D := NatTrans.ofSequence
    (fun m => (b m).repr.symm.toModuleIso.hom) (by
      intro m
      apply ModuleCat.free_hom_ext
      intro x
      change (b (m + 1)).repr.symm
        ((ModuleCat.free R).map (E.map (homOfLE (Nat.le_succ m))) (ModuleCat.freeMk x)) =
        D.map (homOfLE (Nat.le_succ m)) ((b m).repr.symm (ModuleCat.freeMk x))
      simp only [E, Functor.ofSequence_map_homOfLE_succ, ModuleCat.free_map_apply]
      simp only [ModuleCat.freeMk, Module.Basis.repr_symm_single, one_smul]
      change (sequenceBasis D Q e (m + 1)).2 (Sum.inr x) = _
      simpa only [sequenceBasis, Module.Basis.map_apply, Module.Basis.prod_apply,
        Sum.elim_inr, Function.comp_apply, LinearMap.inr_apply] using he m (b m x))
  have (m : ℕ) : IsIso (φ.app m) := inferInstanceAs (IsIso (b m).repr.symm.toModuleIso.hom)
  have : IsIso φ := NatIso.isIso_of_isIso_app φ
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.free R) :=
    (ModuleCat.adj R).leftAdjoint_preservesColimits
  have : Module.Free R ((ModuleCat.free R).obj (colimit E)) :=
    inferInstanceAs (Module.Free R (colimit E →₀ R))
  let iso : (ModuleCat.free R).obj (colimit E) ≅ colimit D :=
    preservesColimitIso (ModuleCat.free R) E ≪≫ colim.mapIso (asIso φ)
  exact Module.Free.of_equiv iso.toLinearEquiv

end FreeColimit

private theorem cokernelSequence_shortExact {C : Type*} [Category C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.cokernelSequence f).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f)
    (show Mono f from inferInstance) inferInstance

private theorem quasiIso_gradedPiece_of_quasiIso_filtration
    {C : Type*} [Category C] [Abelian C]
    {P K : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ} (f : P ⟶ K) (i : ℤ)
    (hi : QuasiIso (f.natTrans.app (op i)))
    (hi' : QuasiIso (f.natTrans.app (op (i + 1)))) :
    QuasiIso ((FilteredObject.gr i).map f) := by
  let a := gradedStep i
  let φ : ShortComplex.cokernelSequence (P.filtration.diagram.map a) ⟶
      ShortComplex.cokernelSequence (K.filtration.diagram.map a) :=
    { τ₁ := f.natTrans.app (op (i + 1))
      τ₂ := f.natTrans.app (op i)
      τ₃ := (FilteredObject.gr i).map f
      comm₁₂ := (f.natTrans.naturality a).symm
      comm₂₃ := (Limits.cokernel.π_desc _ _ _).symm }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ
    (cokernelSequence_shortExact _) (cokernelSequence_shortExact _) hi' hi

private theorem kFlat_gradedPiece_of_kFlat_filtration
    {R : Type u} [CommRing R]
    (P : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (i : ℤ)
    (hflat : ∀ n : ℤ, Module.Flat R (((FilteredObject.gr i).obj P).X n))
    (hi : (P.filtration.obj (op i)).KFlat)
    (hi' : (P.filtration.obj (op (i + 1))).KFlat) :
    ((FilteredObject.gr i).obj P).KFlat := by
  let a := gradedStep i
  exact (KFlatTwoOutOfThree.kFlat_two_out_of_three
    (ShortComplex.cokernelSequence (P.filtration.diagram.map a))
    (cokernelSequence_shortExact _) hflat (Or.inl ⟨hi', hi⟩)).2.2

private theorem cokernelBiprodMapIso_π {C : Type*} [Category C] [Abelian C]
    {A B A' B' : C} (a : A ⟶ A') (b : B ⟶ B') :
    Limits.cokernel.π (Limits.biprod.map a b) ≫ (cokernelBiprodMapIso a b).hom =
      Limits.biprod.map (Limits.cokernel.π a) (Limits.cokernel.π b) :=
  Limits.cokernel.π_desc _ _ _

private theorem cokernelMappingConeMapIso_π {C : Type*} [Category C] [Abelian C]
    {A B A' B' : CochainComplex C ℤ} (g : A ⟶ B) (g' : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : g ≫ b = a ≫ g') (n : ℤ) :
    Limits.cokernel.π ((CochainComplex.mappingCone.map g g' a b h).f n) ≫
        (cokernelMappingConeMapIso g g' a b h n).hom =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod g' n (n + 1) rfl).hom ≫
        Limits.biprod.map (Limits.cokernel.π (a.f (n + 1))) (Limits.cokernel.π (b.f n)) := by
  simp only [cokernelMappingConeMapIso, Iso.trans_hom, Category.assoc,
    Limits.cokernel.mapIso_hom, Limits.cokernel.map, Limits.cokernel.π_desc_assoc,
    cokernelBiprodMapIso_π]

private noncomputable def filteredMappingConeGradedIso {C : Type*} [Category C] [Abelian C]
    {A B : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ} (g : A ⟶ B) (i n : ℤ) :
    ((FilteredObject.gr i).obj (filteredMappingCone g)).X n ≅
      Limits.biprod (((FilteredObject.gr i).obj A).X (n + 1))
        (((FilteredObject.gr i).obj B).X n) := by
  let a := gradedStep i
  let E := HomologicalComplex.eval C (ComplexShape.up ℤ) n
  let E' := HomologicalComplex.eval C (ComplexShape.up ℤ) (n + 1)
  exact Limits.PreservesCokernel.iso E ((filteredMappingCone g).filtration.diagram.map a) ≪≫
    cokernelMappingConeMapIso (g.natTrans.app (op (i + 1))) (g.natTrans.app (op i))
      (A.filtration.diagram.map a) (B.filtration.diagram.map a) (g.natTrans.naturality a).symm n ≪≫
    Limits.biprod.mapIso (Limits.PreservesCokernel.iso E' (A.filtration.diagram.map a)).symm
      (Limits.PreservesCokernel.iso E (B.filtration.diagram.map a)).symm

private theorem filteredMappingConeGradedIso_inr {C : Type*} [Category C] [Abelian C]
    {A B : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ} (g : A ⟶ B) (i n : ℤ) :
    ((FilteredObject.gr i).map (filteredMappingConeInr g)).f n ≫
        (filteredMappingConeGradedIso g i n).hom = Limits.biprod.inr := by
  let a := gradedStep i
  let E := HomologicalComplex.eval C (ComplexShape.up ℤ) n
  apply (cancel_epi (E.map (Limits.cokernel.π (B.filtration.diagram.map a)))).mp
  have hp₀ : Limits.cokernel.π (B.filtration.diagram.map a) ≫
      (FilteredObject.gr i).map (filteredMappingConeInr g) =
        (filteredMappingConeInr g).natTrans.app (op i) ≫
          Limits.cokernel.π ((filteredMappingCone g).filtration.diagram.map a) :=
    Limits.cokernel.π_desc _ _ _
  have hp := congrArg E.map hp₀
  simp only [Functor.map_comp] at hp
  change E.map (Limits.cokernel.π (B.filtration.diagram.map a)) ≫
    E.map ((FilteredObject.gr i).map (filteredMappingConeInr g)) ≫ _ = _
  rw [← Category.assoc, hp, Category.assoc]
  dsimp only [filteredMappingConeGradedIso, Iso.trans_hom]
  rw [Limits.PreservesCokernel.π_iso_hom_assoc]
  change (CochainComplex.mappingCone.inr (g.natTrans.app (op i))).f n ≫
    Limits.cokernel.π ((CochainComplex.mappingCone.map
      (g.natTrans.app (op (i + 1))) (g.natTrans.app (op i))
      (A.filtration.diagram.map a) (B.filtration.diagram.map a)
      (g.natTrans.naturality a).symm).f n) ≫
    (cokernelMappingConeMapIso (g.natTrans.app (op (i + 1)))
      (g.natTrans.app (op i)) (A.filtration.diagram.map a)
      (B.filtration.diagram.map a) (g.natTrans.naturality a).symm n).hom ≫
    (Limits.biprod.mapIso
      (Limits.PreservesCokernel.iso
        (HomologicalComplex.eval C (ComplexShape.up ℤ) (n + 1)) (A.filtration.diagram.map a)).symm
      (Limits.PreservesCokernel.iso E (B.filtration.diagram.map a)).symm).hom =
    E.map (Limits.cokernel.π (B.filtration.diagram.map a)) ≫ Limits.biprod.inr
  have hh := cokernelMappingConeMapIso_π
    (g.natTrans.app (op (i + 1))) (g.natTrans.app (op i))
    (A.filtration.diagram.map a) (B.filtration.diagram.map a)
    (g.natTrans.naturality a).symm n
  have hh' := congrArg (fun k =>
    (CochainComplex.mappingCone.inr (g.natTrans.app (op i))).f n ≫ k ≫
      (Limits.biprod.mapIso
        (Limits.PreservesCokernel.iso
          (HomologicalComplex.eval C (ComplexShape.up ℤ) (n + 1))
            (A.filtration.diagram.map a)).symm
        (Limits.PreservesCokernel.iso E (B.filtration.diagram.map a)).symm).hom) hh
  simp only [Category.assoc] at hh'
  refine hh'.trans ?_
  change (CochainComplex.mappingCone.inr (g.natTrans.app (op i))).f n ≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod _ n (n + 1) rfl).hom ≫ _ = _
  change HomologicalComplex.homotopyCofiber.inrX (g.natTrans.app (op i)) n ≫ _ ≫ _ = _
  rw [HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc]
  simp only [Limits.biprod.mapIso_hom, Iso.symm_hom, Limits.biprod.inr_map_assoc]
  simp only [Limits.PreservesCokernel.iso_inv, Limits.biprod.inr_map]
  change Limits.cokernel.π (E.map (B.filtration.diagram.map a)) ≫
    Limits.cokernelComparison (B.filtration.diagram.map a) E ≫ Limits.biprod.inr = _
  rw [Limits.π_comp_cokernelComparison_assoc]

private noncomputable def gradedPieceColimitIso {C : Type*} [Category C] [Abelian C]
    [Limits.HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    (D : ℕ ⥤ FilteredObject C ℤᵒᵖ) (i : ℤ) :
    (FilteredObject.gr (C := C) i).obj (filteredColimit D) ≅
      Limits.colimit (D ⋙ FilteredObject.gr (C := C) i) := by
  let a := gradedStep i
  let α := (filtrationDiagrams D).map a
  let e : Limits.cokernel α ≅ D ⋙ FilteredObject.gr (C := C) i :=
    NatIso.ofComponents
      (fun m => Limits.PreservesCokernel.iso ((evaluation ℕ C).obj m) α)
      (by
        intro m n f
        apply (cancel_epi ((Limits.cokernel.π α).app m)).mp
        rw [← (Limits.cokernel.π α).naturality_assoc f]
        change ((filtrationDiagrams D).obj (op i)).map f ≫
            (Limits.cokernel.π α).app n ≫
              (Limits.PreservesCokernel.iso ((evaluation ℕ C).obj n) α).hom =
          (Limits.cokernel.π α).app m ≫
            (Limits.PreservesCokernel.iso ((evaluation ℕ C).obj m) α).hom ≫ _
        have hm := Limits.PreservesCokernel.π_iso_hom ((evaluation ℕ C).obj m) α
        have hn := Limits.PreservesCokernel.π_iso_hom ((evaluation ℕ C).obj n) α
        change (Limits.cokernel.π α).app m ≫
          (Limits.PreservesCokernel.iso ((evaluation ℕ C).obj m) α).hom =
            Limits.cokernel.π (α.app m) at hm
        change (Limits.cokernel.π α).app n ≫
          (Limits.PreservesCokernel.iso ((evaluation ℕ C).obj n) α).hom =
            Limits.cokernel.π (α.app n) at hn
        rw [reassoc_of% hm, hn]
        exact (Limits.cokernel.π_desc _ _ _).symm)
  exact (Limits.PreservesCokernel.iso Limits.colim α).symm ≪≫ Limits.colim.mapIso e

private noncomputable def resolution {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) :
    FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ :=
  filteredColimit (resolutionDiagram K)

private noncomputable def resolutionMap {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) : resolution K ⟶ K :=
  filteredColimitDesc (resolutionCocone K)

private theorem resolutionDiagram_map_succ {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (m : ℕ) :
    (resolutionDiagram K).map (homOfLE (Nat.le_succ m)) =
      filteredMappingConeInr (boundaryAugmentation (resolutionStage K m).hom) := by
  simp [resolutionDiagram, resolutionStageInclusion]

private theorem resolutionMap_quasiIso {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) :
    QuasiIso (resolutionMap K).hom := by
  refine quasiIso_of_colimit_kills_kernels (underlyingDiagram (resolutionDiagram K))
    ((FilteredObject.forget).mapCocone (resolutionCocone K))
    (cycleAugmentation_epi_homologyMap K) fun m n x hx => ?_
  change HomologicalComplex.homologyMap
    ((resolutionDiagram K).map (homOfLE (Nat.le_succ m))).hom n x = 0
  rw [resolutionDiagram_map_succ]
  exact cellExtension_kills_homologyKernel (resolutionStage K m).hom n x hx

private theorem resolutionMap_filtration_quasiIso {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (i : ℤ) :
    QuasiIso ((resolutionMap K).natTrans.app (op i)) := by
  refine quasiIso_of_colimit_kills_kernels ((filtrationDiagrams (resolutionDiagram K)).obj (op i))
    (((filtrationFunctor : _ ⥤ (ℤᵒᵖ ⥤ _)) ⋙
      (evaluation ℤᵒᵖ _).obj (op i)).mapCocone (resolutionCocone K))
    (cycleAugmentation_filtration_epi_homologyMap K i) fun m n x hx => ?_
  change HomologicalComplex.homologyMap
    (((resolutionDiagram K).map (homOfLE (Nat.le_succ m))).natTrans.app (op i)) n x = 0
  rw [resolutionDiagram_map_succ]
  exact cellExtension_filtration_kills_homologyKernel (resolutionStage K m).hom i n x hx

private theorem resolutionMap_gradedPiece_quasiIso {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (i : ℤ) :
    QuasiIso ((FilteredObject.gr i).map (resolutionMap K)) :=
  quasiIso_gradedPiece_of_quasiIso_filtration _ _
    (resolutionMap_filtration_quasiIso K i) (resolutionMap_filtration_quasiIso K (i + 1))

private noncomputable def mappingConeProductEquiv {R : Type u} [Ring R]
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (g : A ⟶ B) (n : ℤ) :
    (A.X (n + 1) × B.X n) ≃ₗ[R] (CochainComplex.mappingCone g).X n :=
  ((HomologicalComplex.homotopyCofiber.XIsoBiprod g n (n + 1) rfl) ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv.symm

private theorem biprod_inr_isoProd {R : Type u} [Ring R] (M N : ModuleCat.{u} R) :
    (Limits.biprod.inr : N ⟶ Limits.biprod M N) ≫ (ModuleCat.biprodIsoProd M N).hom =
      ModuleCat.ofHom (LinearMap.inr R M N) := by
  apply (cancel_mono (ModuleCat.biprodIsoProd M N).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply Limits.biprod.hom_ext
  · simp only [Category.assoc, Limits.biprod.inr_fst,
      ModuleCat.biprodIsoProd_inv_comp_fst]
    rfl
  · simp only [Category.assoc, Limits.biprod.inr_snd,
      ModuleCat.biprodIsoProd_inv_comp_snd]
    rfl

private theorem mappingConeProductEquiv_inr {R : Type u} [Ring R]
    {A B : CochainComplex (ModuleCat.{u} R) ℤ} (g : A ⟶ B) (n : ℤ) (x : B.X n) :
    mappingConeProductEquiv g n (0, x) = (CochainComplex.mappingCone.inr g).f n x := by
  apply (mappingConeProductEquiv g n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change (0, x) = ((CochainComplex.mappingCone.inr g).f n ≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod g n (n + 1) rfl).hom ≫
      (ModuleCat.biprodIsoProd _ _).hom) x
  change ((0 : A.X (n + 1)), x) = (HomologicalComplex.homotopyCofiber.inrX g n ≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod g n (n + 1) rfl).hom ≫
      (ModuleCat.biprodIsoProd _ _).hom) x
  rw [HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc, biprod_inr_isoProd]
  rfl

/-- The degree `n` term of a sequential colimit of complexes is free if the first term is and
each step splits off a free summand. -/
private theorem free_colimit_term_of_split_extensions {R : Type u} [Ring R]
    (D : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) (Q : ℕ → ModuleCat.{u} R)
    [Module.Free R ((D.obj 0).X n)] [∀ m, Module.Free R (Q m)]
    (e : ∀ m, (Q m × (D.obj m).X n) ≃ₗ[R] (D.obj (m + 1)).X n)
    (he : ∀ m x, e m (0, x) = ((D.map (homOfLE (Nat.le_succ m))).f n) x) :
    Module.Free R ((Limits.colimit D).X n) :=
  let E := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n
  have : Module.Free R ((D ⋙ E).obj 0) := ‹Module.Free R ((D.obj 0).X n)›
  Module.Free.of_equiv' (free_colimit_of_split_extensions (D ⋙ E) Q e he)
    (preservesColimitIso E D).toLinearEquiv.symm

private theorem resolution_free {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (n : ℤ) :
    Module.Free R ((resolution K).X.X n) := by
  let Q (m : ℕ) : ModuleCat.{u} R :=
    (weightedFreeComplex R (boundaryWeight (resolutionStage K m).hom)).X.X (n + 1)
  have : Module.Free R (((underlyingDiagram (resolutionDiagram K)).obj 0).X n) :=
    weightedFreeComplex_free R (cycleWeight K) n
  have (m : ℕ) : Module.Free R (Q m) :=
    weightedFreeComplex_free R (boundaryWeight (resolutionStage K m).hom) _
  exact free_colimit_term_of_split_extensions (underlyingDiagram (resolutionDiagram K)) n Q
    (fun m => mappingConeProductEquiv (boundaryAugmentation (resolutionStage K m).hom).hom n)
    (by
      intro m x
      change _ = (((resolutionDiagram K).map (homOfLE (Nat.le_succ m))).hom.f n) x
      rw [resolutionDiagram_map_succ]
      exact mappingConeProductEquiv_inr _ n x)

private theorem resolution_filtration_free {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (i n : ℤ) :
    Module.Free R (((resolution K).filtration.obj (op i)).X n) := by
  let Q (m : ℕ) : ModuleCat.{u} R :=
    ((weightedFreeComplex R (boundaryWeight (resolutionStage K m).hom)).filtration.obj
      (op i)).X (n + 1)
  have : Module.Free R ((((filtrationDiagrams (resolutionDiagram K)).obj (op i)).obj 0).X n) :=
    weightedFreeComplex_filtration_free R (cycleWeight K) i n
  have (m : ℕ) : Module.Free R (Q m) :=
    weightedFreeComplex_filtration_free R (boundaryWeight (resolutionStage K m).hom) i _
  exact free_colimit_term_of_split_extensions
    ((filtrationDiagrams (resolutionDiagram K)).obj (op i)) n Q
    (fun m => mappingConeProductEquiv
      ((boundaryAugmentation (resolutionStage K m).hom).natTrans.app (op i)) n)
    (by
      intro m x
      change _ = ((((resolutionDiagram K).map (homOfLE (Nat.le_succ m))).natTrans.app (op i)).f n) x
      rw [resolutionDiagram_map_succ]
      exact mappingConeProductEquiv_inr _ n x)

private noncomputable def filteredMappingConeGradedProductEquiv {R : Type u} [Ring R]
    {A B : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (g : A ⟶ B) (i n : ℤ) :
    (((FilteredObject.gr i).obj A).X (n + 1) ×
      ((FilteredObject.gr i).obj B).X n) ≃ₗ[R]
        ((FilteredObject.gr i).obj (filteredMappingCone g)).X n :=
  (filteredMappingConeGradedIso g i n ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv.symm

private theorem filteredMappingConeGradedProductEquiv_inr {R : Type u} [Ring R]
    {A B : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ}
    (g : A ⟶ B) (i n : ℤ) (x : ((FilteredObject.gr i).obj B).X n) :
    filteredMappingConeGradedProductEquiv g i n (0, x) =
      ((FilteredObject.gr i).map (filteredMappingConeInr g)).f n x := by
  apply (filteredMappingConeGradedProductEquiv g i n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change ((0 : ((FilteredObject.gr i).obj A).X (n + 1)), x) =
    (((FilteredObject.gr i).map (filteredMappingConeInr g)).f n ≫
      (filteredMappingConeGradedIso g i n).hom ≫ (ModuleCat.biprodIsoProd _ _).hom) x
  rw [← Category.assoc, filteredMappingConeGradedIso_inr, biprod_inr_isoProd]
  rfl

private theorem resolution_gradedPiece_free {R : Type u} [Ring R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (i n : ℤ) :
    Module.Free R (((FilteredObject.gr i).obj (resolution K)).X n) := by
  let E := HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) n
  let D := resolutionDiagram K ⋙ FilteredObject.gr i ⋙ E
  let Q (m : ℕ) : ModuleCat.{u} R :=
    ((FilteredObject.gr i).obj
      (weightedFreeComplex R (boundaryWeight (resolutionStage K m).hom))).X (n + 1)
  have : Module.Free R (D.obj 0) :=
    weightedFreeComplex_gradedPiece_free R (cycleWeight K) i n
  have (m : ℕ) : Module.Free R (Q m) :=
    weightedFreeComplex_gradedPiece_free R (boundaryWeight (resolutionStage K m).hom) i _
  have hf : Module.Free R ↥(Limits.colimit D) := free_colimit_of_split_extensions D Q
    (fun m => filteredMappingConeGradedProductEquiv
      (boundaryAugmentation (resolutionStage K m).hom) i n)
    (by
      intro m x
      change _ = ((FilteredObject.gr i).map
        ((resolutionDiagram K).map (homOfLE (Nat.le_succ m)))).f n x
      rw [resolutionDiagram_map_succ]
      exact filteredMappingConeGradedProductEquiv_inr _ i n x)
  exact Module.Free.of_equiv' hf
    (E.mapIso (gradedPieceColimitIso (resolutionDiagram K) i) ≪≫
      preservesColimitIso E
        (resolutionDiagram K ⋙ FilteredObject.gr i)).toLinearEquiv.symm

private noncomputable def freeZeroTruncDiagram (R : Type u) [Ring R] (B : ℤ → Type u) :
    ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj m := freeZeroComplex R (fun n => {b : B n // n ≤ (m : ℤ)})
  map {m k} f := freeZeroComplexMap (fun n b =>
    ⟨b.val, b.property.trans (Int.ofNat_le.mpr (leOfHom f))⟩)
  map_id m := freeZeroComplexMap_id R _
  map_comp f g := by rw [← freeZeroComplexMap_comp]; rfl

private noncomputable def freeZeroTruncCocone (R : Type u) [Ring R] (B : ℤ → Type u) :
    Limits.Cocone (freeZeroTruncDiagram R B) where
  pt := freeZeroComplex R B
  ι.app m := freeZeroComplexMap (fun _ => Subtype.val)
  ι.naturality m k f := by
    change freeZeroComplexMap _ ≫ freeZeroComplexMap _ = freeZeroComplexMap _ ≫ 𝟙 _
    rw [Category.comp_id, ← freeZeroComplexMap_comp]
    rfl

private noncomputable def isColimit_of_eventually_isIso {C : Type*} [Category C]
    {D : ℕ ⥤ C} (c : Limits.Cocone D) (N : ℕ)
    (h : ∀ m, N ≤ m → IsIso (c.ι.app m)) : Limits.IsColimit c := by
  have : IsIso (c.ι.app N) := h N le_rfl
  have hD : D.IsEventuallyConstantFrom N := by
    intro m f
    have : IsIso (c.ι.app m) := h m (leOfHom f)
    exact IsIso.of_isIso_fac_right (c.w f)
  exact hD.isColimitOfIsIso c

private noncomputable def freeZeroTruncIsColimit (R : Type u) [Ring R] (B : ℤ → Type u) :
    Limits.IsColimit (freeZeroTruncCocone R B) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  apply isColimit_of_eventually_isIso _ n.toNat
  intro m hm
  have hn : n ≤ (m : ℤ) := by omega
  let f : {b : B n // n ≤ (m : ℤ)} ⟶ B n := ↾Subtype.val
  have : IsIso f := (CategoryTheory.isIso_iff_bijective f).mpr
    ⟨Subtype.val_injective, fun b => ⟨⟨b, hn⟩, rfl⟩⟩
  exact inferInstanceAs (IsIso ((ModuleCat.free R).map f))

private theorem freeZeroTrunc_strictlyLE (R : Type u) [Ring R] (B : ℤ → Type u) (m : ℕ) :
    ((freeZeroTruncDiagram R B).obj m).IsStrictlyLE (m : ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have : IsEmpty {b : B n // n ≤ (m : ℤ)} := ⟨fun b => (not_le_of_gt hn) b.property⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (inferInstanceAs (Subsingleton ({b : B n // n ≤ (m : ℤ)} →₀ R)))

private theorem freeZeroComplex_kFlat (R : Type u) [CommRing R] (B : ℤ → Type u) :
    (freeZeroComplex R B).KFlat := by
  have h (m : ℕ) : ((freeZeroTruncDiagram R B).obj m).KFlat := by
    have := freeZeroTrunc_strictlyLE R B m
    have (n : ℤ) : Module.Flat R (((freeZeroTruncDiagram R B).obj m).X n) :=
      inferInstanceAs (Module.Flat R ({b : B n // n ≤ (m : ℤ)} →₀ R))
    exact kFlat_of_flat _ (m : ℤ)
  exact of_iso
    ((Limits.colimit.isColimit (freeZeroTruncDiagram R B)).coconePointUniqueUpToIso
      (freeZeroTruncIsColimit R B)) (kFlat_colimit.{u, 0, 0, u} _ h)

private noncomputable def freeZeroComplexShiftIso (R : Type u) [Ring R]
    (B : ℤ → Type u) (s : ℤ) :
    (freeZeroComplex R B)⟦s⟧ ≅ freeZeroComplex R (fun n => B (n + s)) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro n m h
    simp [CochainComplex.shiftFunctor_obj_d', freeZeroComplex])

private theorem mappingCone_freeZero_kFlat {R : Type u} [CommRing R]
    {B : ℤ → Type u} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (g : freeZeroComplex R B ⟶ P) (hP : P.KFlat) :
    (CochainComplex.mappingCone g).KFlat := by
  let S := CochainComplex.mappingCone.triangleRotateShortComplex g
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact S
    (fun n => (CochainComplex.mappingCone.triangleRotateShortComplexSplitting g n).shortExact)
  have hflat (n : ℤ) : Module.Flat R (S.X₃.X n) :=
    inferInstanceAs (Module.Flat R (B (n + 1) →₀ R))
  have hQ : S.X₃.KFlat := of_iso (freeZeroComplexShiftIso R B 1).symm
    (freeZeroComplex_kFlat R (fun n => B (n + 1)))
  exact (KFlatTwoOutOfThree.kFlat_two_out_of_three S hS hflat
    (Or.inr (Or.inl ⟨hP, hQ⟩))).2.1

private theorem resolutionStage_kFlat {R : Type u} [CommRing R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (m : ℕ) :
    (resolutionStage K m).left.X.KFlat ∧
      ∀ i : ℤ, ((resolutionStage K m).left.filtration.obj (op i)).KFlat := by
  induction m with
  | zero => exact ⟨freeZeroComplex_kFlat R _, fun i => freeZeroComplex_kFlat R _⟩
  | succ m hm =>
      exact ⟨mappingCone_freeZero_kFlat (boundaryAugmentation (resolutionStage K m).hom).hom hm.1,
        fun i => mappingCone_freeZero_kFlat
          ((boundaryAugmentation (resolutionStage K m).hom).natTrans.app (op i)) (hm.2 i)⟩

private theorem resolution_kFlat {R : Type u} [CommRing R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) :
    (resolution K).X.KFlat ∧ ∀ i : ℤ, ((resolution K).filtration.obj (op i)).KFlat :=
  ⟨kFlat_colimit.{u, 0, 0, u} (underlyingDiagram (resolutionDiagram K))
      (fun m => (resolutionStage_kFlat K m).1),
    fun i => kFlat_colimit.{u, 0, 0, u}
      ((filtrationDiagrams (resolutionDiagram K)).obj (op i))
      (fun m => (resolutionStage_kFlat K m).2 i)⟩

/-- A filtered complex of modules admits a filtered morphism from a complex whose underlying
terms, filtration steps, and associated graded pieces are free and K-flat, and this morphism is
a quasi-isomorphism on the underlying complex, on every filtration step, and on every associated
graded piece. -/
@[stacks 0H7X]
public theorem exists_free_kFlat_filtered_resolution
    (R : Type u) [CommRing R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) :
    ∃ (P : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) (f : P ⟶ K),
      (∀ n : ℤ, Module.Free R (P.X.X n)) ∧
      (∀ i n : ℤ, Module.Free R ((P.filtration.obj (op i)).X n)) ∧
      (∀ i n : ℤ,
        Module.Free R (((FilteredObject.gr i).obj P).X n)) ∧
      P.X.KFlat ∧
      (∀ i : ℤ, (P.filtration.obj (op i)).KFlat) ∧
      (∀ i : ℤ, ((FilteredObject.gr i).obj P).KFlat) ∧
      QuasiIso f.hom ∧
      (∀ i : ℤ, QuasiIso (f.natTrans.app (op i))) ∧
      (∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map f)) := by
  refine ⟨resolution K, resolutionMap K, resolution_free K, resolution_filtration_free K,
    resolution_gradedPiece_free K, (resolution_kFlat K).1, (resolution_kFlat K).2, ?_,
    resolutionMap_quasiIso K, resolutionMap_filtration_quasiIso K,
    resolutionMap_gradedPiece_quasiIso K⟩
  exact fun i => kFlat_gradedPiece_of_kFlat_filtration _ i
    (fun n => have := resolution_gradedPiece_free K i n; inferInstance)
    ((resolution_kFlat K).2 i) ((resolution_kFlat K).2 (i + 1))

end CochainComplex.KFlat

end
