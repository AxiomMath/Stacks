module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Canonical
public import StacksCore.CategoryTheory.Abelian.CommSq
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The first page of the spectral sequence of a filtered complex, and its differential

Let `(K^•, F)` be a filtered complex of an abelian category `𝒜`. The first page of its spectral
sequence ([Stacks, Tag 012M]) is the cohomology of the graded pieces,

`E_1^{p, q} = H^{p + q}(gr^p K^•)`,

and the differential `d_1^{p, q} : E_1^{p, q} ⟶ E_1^{p + 1, q}` is the connecting morphism of the
short exact sequence of complexes

`0 ⟶ gr^{p + 1}K^• ⟶ F^pK^•/F^{p + 2}K^• ⟶ gr^pK^• ⟶ 0`.

## Main definitions

* `CochainComplex.Filtered.grShortComplex`: the short complex
  `gr^{p + 1}K^• ⟶ F^pK^•/F^{p + 2}K^• ⟶ gr^pK^•`.
* `CochainComplex.Filtered.firstPageIso`: the isomorphism
  `E_1^{p, q} ≅ H^n(gr^pK^•)`, `n = p + q`, sending the class of a cycle `x ∈ Z_1^{p, q}` to the
  class of its image in `gr^pK^n` (`π_firstPageIso_hom`).
* `CochainComplex.Filtered.firstPageClass`: that class, as a morphism out of `Z_1^{p, q}`.

## Main results

* `CochainComplex.Filtered.grShortComplex_shortExact`: `grShortComplex` is short exact.
* `CochainComplex.Filtered.firstPage_d`: **`d_1` is the connecting morphism** of
  `grShortComplex_shortExact`, read through `firstPageIso`, with no sign.
* `CochainComplex.Filtered.firstPageClass_comp_δ`: the connecting morphism on first-page classes,
  `[x] ↦ [dx]`.

## Implementation notes

`firstPageIso` is the page-turning isomorphism `E_1 ≅ H(E_0)` of
`FilteredComplexSpectralSequence.pageHomologyIso` followed by the identification of the zeroth
page with `gr^pK^•`, which is chosen from
`FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage`. The choice is harmless: the
formula `π_firstPageIso_hom` determines `firstPageIso` completely, the class map out of
`Z_1^{p, q}` being an epimorphism onto `E_1^{p, q}`.

## References

* [Stacks Project, Tag 012M](https://stacks.math.columbia.edu/tag/012M)
* [Stacks Project, Tag 012K](https://stacks.math.columbia.edu/tag/012K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite FilteredComplexSpectralSequence

universe v u

namespace CochainComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C] (M : Filtered C)

/-! ### The short exact sequence `gr^{p + 1} ⟶ F^p/F^{p + 2} ⟶ gr^p` -/

/-- The inclusion `F^{p + 1}K^• ⟶ F^pK^•` of consecutive filtration steps. -/
abbrev succStep (p : ℤ) : M.filtration.obj (op (p + 1)) ⟶ M.filtration.obj (op p) :=
  M.filtration.step (FilteredObject.succHom p)

/-- **The short complex `gr^{p + 1}K^• ⟶ F^pK^•/F^{p + 2}K^• ⟶ gr^pK^•`** of a filtered complex,
whose middle term is the cokernel of `F^{p + 2}K^• ⟶ F^pK^•`. -/
abbrev grShortComplex (p : ℤ) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk
    (cokernel.map (M.succStep (p + 1)) (M.succStep (p + 1) ≫ M.succStep p) (𝟙 _)
      (M.succStep p) (by simp))
    (cokernel.map (M.succStep (p + 1) ≫ M.succStep p) (M.succStep p) (M.succStep (p + 1))
      (𝟙 _) (by simp))
    (Abelian.cokernel_map_comp_cokernel_map _ _)

/-- The first term of `grShortComplex` is the graded piece `gr^{p + 1}K^•`. -/
lemma grShortComplex_X₁ (p : ℤ) :
    (M.grShortComplex p).X₁ = (FilteredObject.gr (p + 1)).obj M := rfl

/-- The last term of `grShortComplex` is the graded piece `gr^pK^•`. -/
lemma grShortComplex_X₃ (p : ℤ) :
    (M.grShortComplex p).X₃ = (FilteredObject.gr p).obj M := rfl

/-- **`0 ⟶ gr^{p + 1}K^• ⟶ F^pK^•/F^{p + 2}K^• ⟶ gr^pK^• ⟶ 0` is short exact.** -/
lemma grShortComplex_shortExact (p : ℤ) : (M.grShortComplex p).ShortExact :=
  { exact := ShortComplex.exact_of_f_is_kernel _
      (Abelian.isLimitKernelForkCokernelMap (M.succStep (p + 1)) (M.succStep p))
    mono_f := Abelian.mono_cokernel_map_comp (M.succStep (p + 1)) (M.succStep p)
    epi_g := epi_of_isColimit_cofork
      (Abelian.isColimitCokernelCoforkCokernelMap (M.succStep (p + 1)) (M.succStep p)) }

/-! ### Cycles of the spectral sequence, lifted to the filtration -/

/-- The degreewise filtration `F^pK^n ⊆ K^n` of a filtered complex. -/
local notation "𝔽" => filtrationSubobject M

/-- The inclusion `Z_r^{p, n} ⊆ F^pK^n`, read as a morphism into the term of the complex
`F^pK^•`. -/
def cyclesToStep (r p n : ℤ) :
    (cycles M.X (filtrationSubobject M) r p n : C) ⟶ (M.filtration.obj (op p)).X n :=
  Subobject.ofLE _ _ (by rw [FilteredComplexSpectralSequence.cycles]; exact inf_le_left) ≫
    (Subobject.underlyingIso ((M.filtration.ι.app (op p)).f n)).hom

/-- `cyclesToStep` followed by the inclusion `F^pK^n ⟶ K^n` is the inclusion `Z_r^{p, n} ⊆ K^n`. -/
@[reassoc (attr := simp)]
lemma cyclesToStep_ι (r p n : ℤ) :
    M.cyclesToStep r p n ≫ (M.filtration.ι.app (op p)).f n =
      (cycles M.X (filtrationSubobject M) r p n).arrow := by
  rw [cyclesToStep, Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]

/-- The differential of a cycle of `Z_r^{p, n}`, which lies in `F^{p + r}K^{n + 1}`, read as a
morphism into the term of the complex `F^{p + r}K^•`. -/
def cyclesDiffToStep (r p n : ℤ) :
    (cycles M.X (filtrationSubobject M) r p n : C) ⟶ (M.filtration.obj (op (p + r))).X (n + 1) :=
  Subobject.factorThru _ ((cycles M.X (filtrationSubobject M) r p n).arrow ≫ M.X.d n (n + 1))
      ((Subobject.le_pullback_iff _ _ _).1 inf_le_right) ≫
    (Subobject.underlyingIso ((M.filtration.ι.app (op (p + r))).f (n + 1))).hom

/-- `cyclesDiffToStep` followed by the inclusion `F^{p + r}K^{n + 1} ⟶ K^{n + 1}` is the
differential of `K^•` restricted to `Z_r^{p, n}`. -/
@[reassoc (attr := simp)]
lemma cyclesDiffToStep_ι (r p n : ℤ) :
    M.cyclesDiffToStep r p n ≫ (M.filtration.ι.app (op (p + r))).f (n + 1) =
      (cycles M.X (filtrationSubobject M) r p n).arrow ≫ M.X.d n (n + 1) := by
  rw [cyclesDiffToStep, Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk,
    Subobject.factorThru_arrow]

/-- For a first-page cycle `x ∈ Z_1^{p, n}`, the differential `dx ∈ F^{p + 1}K^{n + 1}` is the
differential of `x` computed in the complex `F^pK^•`. -/
@[reassoc]
lemma cyclesDiffToStep_succStep (p n : ℤ) :
    M.cyclesDiffToStep 1 p n ≫ (M.succStep p).f (n + 1) =
      M.cyclesToStep 1 p n ≫ (M.filtration.obj (op p)).d n (n + 1) := by
  rw [← cancel_mono ((M.filtration.ι.app (op p)).f (n + 1)), Category.assoc, Category.assoc,
    ← HomologicalComplex.comp_f, Filtration.step_comp_ι_app, cyclesDiffToStep_ι,
    ← (M.filtration.ι.app (op p)).comm, cyclesToStep_ι_assoc]
  rfl

/-- The projection `F^pK^• ⟶ gr^pK^•`. -/
abbrev grπ (p : ℤ) : M.filtration.obj (op p) ⟶ (FilteredObject.gr p).obj M :=
  FilteredObject.grMapπ (FilteredObject.succHom p) M

/-- The composite `F^{p + 1}K^n ⟶ F^pK^n ⟶ gr^pK^n` vanishes. -/
@[reassoc (attr := simp)]
lemma succStep_f_grπ_f (p n : ℤ) : (M.succStep p).f n ≫ (M.grπ p).f n = 0 := by
  rw [← HomologicalComplex.comp_f, FilteredObject.step_grMapπ, HomologicalComplex.zero_f]

/-- The image in `gr^pK^n` of a first-page cycle is a cycle of `gr^pK^•`. -/
lemma cyclesToStep_grπ_d (p n : ℤ) :
    M.cyclesToStep 1 p n ≫ (M.grπ p).f n ≫ ((FilteredObject.gr p).obj M).d n (n + 1) = 0 := by
  rw [(M.grπ p).comm, ← Category.assoc, ← cyclesDiffToStep_succStep, Category.assoc,
    succStep_f_grπ_f, comp_zero]

/-- **The class in `H^n(gr^pK^•)` of a first-page cycle** `x ∈ Z_1^{p, n}`: the class of its image
in `gr^pK^n`. -/
def firstPageClass (p n : ℤ) :
    (cycles M.X (filtrationSubobject M) 1 p n : C) ⟶ ((FilteredObject.gr p).obj M).homology n :=
  ((FilteredObject.gr p).obj M).liftCycles (M.cyclesToStep 1 p n ≫ (M.grπ p).f n) (n + 1)
      (by simp) ((Category.assoc _ _ _).trans (M.cyclesToStep_grπ_d p n)) ≫
    ((FilteredObject.gr p).obj M).homologyπ n

/-! ### The first page as the cohomology of the graded pieces -/

/-- The identification `E_0^{p, q} ≅ gr^pK^n` of the zeroth page, chosen from
`FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage`. -/
def zeroPageIso (p q n : ℤ) (hn : n = p + q) :
    ((filteredSpectralSequence M).page 0 le_rfl).X (p, q) ≅
      ((FilteredObject.gr p).obj M).X n :=
  (exists_iso_gradedPiece_zeroPage M (filtrationSubobject M) (fun _ _ ↦ rfl)
    (filtrationSubobject_antitone M)).choose p q n hn

/-- For any lift `u : Z_0^{p, n} ⟶ F^pK^n` of the inclusion `Z_0^{p, n} ⊆ K^n`, the class map
`Z_0^{p, n} ⟶ E_0^{p, q}` followed by `zeroPageIso` is `u` followed by the projection to
`gr^pK^n`. -/
lemma π_zeroPageIso_hom (p q n : ℤ) (hn : n = p + q)
    (u : (cycles M.X (filtrationSubobject M) 0 p n : C) ⟶ (M.filtration.obj (op p)).X n)
    (hu : u ≫ (M.filtration.ι.app (op p)).f n = (cycles M.X (filtrationSubobject M) 0 p n).arrow) :
    cokernel.π (den M.X (filtrationSubobject M) 0 p n) ≫
        (eIso M.X (filtrationSubobject M) (filtrationSubobject_antitone M) 0 p q n le_rfl hn).inv ≫
          (M.zeroPageIso p q n hn).hom = u ≫ (M.grπ p).f n :=
  (exists_iso_gradedPiece_zeroPage M (filtrationSubobject M) (fun _ _ ↦ rfl)
    (filtrationSubobject_antitone M)).choose_spec.1 p q n hn u hu

/-- The zeroth differential is `gr^p(d)`, with the indices given up to arithmetic. -/
lemma zeroPage_d_comp_zeroPageIso (p q n q' n' : ℤ) (hn : n = p + q) (hn' : n' = p + q')
    (hq : q' = q + 1) (hnn : n' = n + 1) :
    ((filteredSpectralSequence M).page 0 le_rfl).d (p, q) (p, q') ≫
        (M.zeroPageIso p q' n' hn').hom =
      (M.zeroPageIso p q n hn).hom ≫ ((FilteredObject.gr p).obj M).d n n' := by
  subst hq hnn
  exact (exists_iso_gradedPiece_zeroPage M (filtrationSubobject M) (fun _ _ ↦ rfl)
    (filtrationSubobject_antitone M)).choose_spec.2.1 p q n hn

/-- The zeroth page around `(p, q)`, as a short complex, is `gr^pK^•` around `n = p + q`. -/
def zeroPageScIso (p q n : ℤ) (hn : n = p + q) :
    ((filteredSpectralSequence M).page 0 le_rfl).sc' (p, q - 1) (p, q) (p, q + 1) ≅
      ((FilteredObject.gr p).obj M).sc' (n - 1) n (n + 1) :=
  ShortComplex.isoMk (M.zeroPageIso p (q - 1) (n - 1) (by omega)) (M.zeroPageIso p q n hn)
    (M.zeroPageIso p (q + 1) (n + 1) (by omega))
    (M.zeroPage_d_comp_zeroPageIso p (q - 1) (n - 1) q n (by omega) hn (by omega) (by omega)).symm
    (M.zeroPage_d_comp_zeroPageIso p q n (q + 1) (n + 1) hn (by omega) rfl rfl).symm

/-- **The first page of the spectral sequence of a filtered complex is the cohomology of the
graded pieces**: `E_1^{p, q} ≅ H^n(gr^pK^•)` for `n = p + q`. It is the page-turning isomorphism
`E_1 ≅ H(E_0)` followed by the identification of the zeroth page with `gr^pK^•`; on classes it
sends the class of `x ∈ Z_1^{p, q}` to the class of its image in `gr^pK^n`
(`π_firstPageIso_hom`). -/
@[ega "0 11.2.2" "partial"]
def firstPageIso (p q n : ℤ) (hn : n = p + q) :
    ((filteredSpectralSequence M).page 1 (by omega)).X (p, q) ≅
      ((FilteredObject.gr p).obj M).homology n :=
  ((filteredSpectralSequence M).iso 0 1 (p, q)).symm ≪≫
    ((filteredSpectralSequence M).page 0 le_rfl).homologyIsoSc' (p, q - 1) (p, q) (p, q + 1)
      (ComplexShape.prev_eq' _ (by simp [ComplexShape.up'_Rel]))
      (ComplexShape.next_eq' _ (by simp [ComplexShape.up'_Rel])) ≪≫
    ShortComplex.homologyMapIso (M.zeroPageScIso p q n hn) ≪≫
    (((FilteredObject.gr p).obj M).homologyIsoSc' (n - 1) n (n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)).symm

/-- `Z_1^{p, n} ⊆ Z_0^{p, n}`. -/
lemma cycles_one_le_cycles_zero (p n : ℤ) :
    cycles M.X (filtrationSubobject M) 1 p n ≤ cycles M.X (filtrationSubobject M) 0 p n := by
  refine FilteredComplexSpectralSequence.le_cycles _ _
    (by rw [FilteredComplexSpectralSequence.cycles]; exact inf_le_left) ?_
  rw [FilteredComplexSpectralSequence.cycles]
  exact inf_le_right.trans ((Subobject.pullback _).monotone
    (filtrationSubobject_antitone M _ _ _ (by omega)))

/-- The inclusion `Z_1^{p, n} ⊆ Z_0^{p, n}` followed by `cyclesToStep 0` is `cyclesToStep 1`. -/
@[reassoc (attr := simp)]
lemma ofLE_cyclesToStep (p n : ℤ) :
    Subobject.ofLE _ _ (M.cycles_one_le_cycles_zero p n) ≫ M.cyclesToStep 0 p n =
      M.cyclesToStep 1 p n := by
  rw [← cancel_mono ((M.filtration.ι.app (op p)).f n), Category.assoc, cyclesToStep_ι,
    cyclesToStep_ι, Subobject.ofLE_arrow]

/-- The page-turning isomorphism `H(E_0)^{p, q} ≅ E_1^{p, q}` of the spectral sequence of a
filtered complex is the one of `FilteredComplexSpectralSequence.pageHomologyIso`. -/
lemma iso_zero_one_eq (p q : ℤ) :
    ((filteredSpectralSequence M).iso 0 1 (p, q)).hom =
      (pageHomologyIso M.X (filtrationSubobject M) (filtrationSubobject_antitone M) 0 (p, q)).hom :=
  rfl

/-- `π_firstPageIso_hom` at `n = p + q`. -/
private lemma π_firstPageIso_hom_self (p q : ℤ) :
    cokernel.π (den M.X (filtrationSubobject M) 1 p (p + q)) ≫
        (eIso M.X (filtrationSubobject M) (filtrationSubobject_antitone M) 1 p q (p + q)
          (by omega) rfl).inv ≫
        (M.firstPageIso p q (p + q) rfl).hom = M.firstPageClass p (p + q) := by
  let x' := Subobject.ofLE _ _ (M.cycles_one_le_cycles_zero p (p + q))
  have hnext : (ComplexShape.up' ((0 : ℤ), (1 - 0 : ℤ))).next (p, q) = (p, q + 1) :=
    ComplexShape.next_eq' _ (by simp [ComplexShape.up'_Rel])
  let e0 := (eIso M.X (filtrationSubobject M) (filtrationSubobject_antitone M) 0 p q (p + q)
    le_rfl rfl).inv
  have hu : (x' ≫ cokernel.π (den M.X (filtrationSubobject M) 0 p (p + q)) ≫ e0) ≫
      (M.zeroPageIso p q (p + q) rfl).hom =
      M.cyclesToStep 1 p (p + q) ≫ (M.grπ p).f (p + q) := by
    rw [Category.assoc, Category.assoc,
      M.π_zeroPageIso_hom p q (p + q) rfl _ (M.cyclesToStep_ι 0 p (p + q)),
      ofLE_cyclesToStep_assoc]
  have hy0 : (x' ≫ cokernel.π (den M.X (filtrationSubobject M) 0 p (p + q)) ≫ e0) ≫
      ((filteredSpectralSequence M).page 0 le_rfl).d (p, q) (p, q + 1) = 0 := by
    rw [← cancel_mono (M.zeroPageIso p (q + 1) (p + q + 1) (by omega)).hom, zero_comp,
      Category.assoc, M.zeroPage_d_comp_zeroPageIso p q (p + q) (q + 1) (p + q + 1) rfl
        (by omega) rfl rfl, ← Category.assoc, hu, Category.assoc,
      M.cyclesToStep_grπ_d p (p + q)]
  let y := ((filteredSpectralSequence M).page 0 le_rfl).liftCycles _ (p, q + 1) hnext hy0
  have hyi : y ≫ ((filteredSpectralSequence M).page 0 le_rfl).iCycles (p, q) =
      x' ≫ cokernel.π (den M.X (filtrationSubobject M) 0 p (p + q)) ≫ e0 :=
    HomologicalComplex.liftCycles_i _ _ _ _ _
  have hkey := homologyπ_comp_pageHomologyIso_hom M.X (filtrationSubobject M)
    (filtrationSubobject_antitone M) 0 (p, q) y (𝟙 _) x' (by simp [x'])
    (hyi.trans (by simp [e0]))
  have h1 : cokernel.π (den M.X (filtrationSubobject M) 1 p (p + q)) ≫
      (eIso M.X (filtrationSubobject M) (filtrationSubobject_antitone M) 1 p q (p + q)
          (by omega) rfl).inv ≫
      ((filteredSpectralSequence M).iso 0 1 (p, q)).inv =
        y ≫ ((filteredSpectralSequence M).page 0 le_rfl).homologyπ (p, q) := by
    rw [← Category.assoc, Iso.comp_inv_eq, iso_zero_one_eq, Category.assoc]
    exact (hkey.trans (by simp)).symm
  simp only [firstPageIso, Iso.trans_hom, Iso.symm_hom, ShortComplex.homologyMapIso_hom]
  rw [reassoc_of% h1, HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    ShortComplex.homologyπ_naturality_assoc, HomologicalComplex.π_homologyIsoSc'_inv,
    firstPageClass]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (((FilteredObject.gr p).obj M).iCycles (p + q))]
  simp only [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    HomologicalComplex.liftCycles_i]
  refine Eq.trans ?_ hu
  rw [← hyi, Category.assoc]
  refine congrArg (y ≫ ·) ?_
  have h2 := ShortComplex.cyclesMap_i (M.zeroPageScIso p q (p + q) rfl).hom
  have h3 := HomologicalComplex.cyclesIsoSc'_hom_iCycles
    ((filteredSpectralSequence M).page 0 le_rfl) (p, q - 1) (p, q) (p, q + 1)
    (ComplexShape.prev_eq' _ (by simp [ComplexShape.up'_Rel]))
    (ComplexShape.next_eq' _ (by simp [ComplexShape.up'_Rel]))
  exact (congrArg (_ ≫ ·) h2).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h3))

/-- **The first-page identification on classes.** The class of a cycle `x ∈ Z_1^{p, q}` in
`E_1^{p, q}` is sent by `firstPageIso` to the class in `H^n(gr^pK^•)` of the image of `x` in
`gr^pK^n`. -/
lemma π_firstPageIso_hom (p q n : ℤ) (hn : n = p + q) :
    cokernel.π (den M.X (filtrationSubobject M) 1 p n) ≫
        (eIso M.X (filtrationSubobject M) (filtrationSubobject_antitone M) 1 p q n
          (by omega) hn).inv ≫
        (M.firstPageIso p q n hn).hom = M.firstPageClass p n := by
  subst hn
  exact M.π_firstPageIso_hom_self p q

/-- The image in `gr^pK^n` of a first-page cycle is a cycle of `gr^pK^•`, against the
differential into an arbitrary degree. -/
lemma cyclesToStep_grπ_d' (p n j : ℤ) :
    M.cyclesToStep 1 p n ≫ (M.grπ p).f n ≫ ((FilteredObject.gr p).obj M).d n j = 0 := by
  by_cases h : n + 1 = j
  · subst h
    exact M.cyclesToStep_grπ_d p n
  · rw [((FilteredObject.gr p).obj M).shape n j (by simpa using h), comp_zero, comp_zero]

/-- **The connecting morphism on first-page classes.** The connecting morphism of
`0 ⟶ gr^{p + 1}K^• ⟶ F^pK^•/F^{p + 2}K^• ⟶ gr^pK^• ⟶ 0` sends the class of a first-page cycle
`x ∈ Z_1^{p, n}` to the class of `dx ∈ Z_1^{p + 1, n + 1}`: lift `x` to `F^pK^n/F^{p + 2}K^n`,
apply the differential, and read the result in `gr^{p + 1}K^{n + 1}`. -/
lemma firstPageClass_comp_δ (p n n' : ℤ) (hn' : n' = n + 1) :
    M.firstPageClass p n ≫ (M.grShortComplex_shortExact p).δ n n' (by simp [hn']) =
      deltaCycles' M.X (filtrationSubobject M) 1 p n (p + 1) n' rfl hn' ≫
        M.firstPageClass (p + 1) n' := by
  subst hn'
  let S := M.grShortComplex p
  let π₂ := cokernel.π (M.succStep (p + 1) ≫ M.succStep p)
  let δ' := deltaCycles' M.X (filtrationSubobject M) 1 p n (p + 1) (n + 1) rfl rfl
  have hg : π₂ ≫ S.g = M.grπ p := by
    simp [S, π₂, grShortComplex, grπ, FilteredObject.grMapπ]
  have hf : M.grπ (p + 1) ≫ S.f = M.succStep p ≫ π₂ := by
    simp [S, π₂, grShortComplex, grπ, FilteredObject.grMapπ]
  have hd : δ' ≫ M.cyclesToStep 1 (p + 1) (n + 1) ≫ (M.succStep p).f (n + 1) =
      M.cyclesToStep 1 p n ≫ (M.filtration.obj (op p)).d n (n + 1) := by
    rw [← cyclesDiffToStep_succStep, ← Category.assoc]
    congr 1
    rw [← cancel_mono ((M.filtration.ι.app (op (p + 1))).f (n + 1)), Category.assoc,
      cyclesToStep_ι, cyclesDiffToStep_ι, deltaCycles'_arrow]
  have key := (M.grShortComplex_shortExact p).δ_eq n (n + 1) (by simp)
    (M.cyclesToStep 1 p n ≫ (M.grπ p).f n)
    ((Category.assoc _ _ _).trans (M.cyclesToStep_grπ_d' p n (n + 1)))
    (M.cyclesToStep 1 p n ≫ π₂.f n)
    (by rw [Category.assoc, ← HomologicalComplex.comp_f, hg])
    (δ' ≫ M.cyclesToStep 1 (p + 1) (n + 1) ≫ (M.grπ (p + 1)).f (n + 1))
    (by
      rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f, hf,
        HomologicalComplex.comp_f, ← Category.assoc, ← Category.assoc, Category.assoc δ', hd,
        Category.assoc, Category.assoc]
      exact congrArg (M.cyclesToStep 1 p n ≫ ·) (π₂.comm n (n + 1)).symm)
    (n + 1 + 1) (by simp)
  have h₃ : M.firstPageClass p n = (M.grShortComplex p).X₃.liftCycles
      (M.cyclesToStep 1 p n ≫ (M.grπ p).f n) (n + 1) (by simp)
      ((Category.assoc _ _ _).trans (M.cyclesToStep_grπ_d' p n (n + 1))) ≫
      (M.grShortComplex p).X₃.homologyπ n := rfl
  rw [h₃, Category.assoc, key, firstPageClass, HomologicalComplex.comp_liftCycles_assoc]
  rfl

/-- **`d_1` is the connecting morphism.** Under the identification `firstPageIso` of the first
page with the cohomology of the graded pieces, the differential
`d_1^{p, q} : E_1^{p, q} ⟶ E_1^{p + 1, q}` of the spectral sequence of a filtered complex is the
connecting morphism `H^n(gr^pK^•) ⟶ H^{n + 1}(gr^{p + 1}K^•)` of the short exact sequence
`0 ⟶ gr^{p + 1}K^• ⟶ F^pK^•/F^{p + 2}K^• ⟶ gr^pK^• ⟶ 0`, with no sign. -/
theorem firstPage_d (p q n n' : ℤ) (hn : n = p + q) (hn' : n' = n + 1) :
    ((spectralSequenceFunctor.obj M).page 1 (by omega)).d (p, q) (p + 1, q) =
      (M.firstPageIso p q n hn).hom ≫
        (M.grShortComplex_shortExact p).δ n n' (by simp [hn']) ≫
          (M.firstPageIso (p + 1) q n' (by omega)).inv := by
  change ((filteredSpectralSequence M).page 1 (by omega)).d (p, q) (p + 1, q) = _
  subst hn
  obtain rfl : n' = p + 1 + q := by omega
  rw [← cancel_epi (eIso M.X (filtrationSubobject M) (filtrationSubobject_antitone M) 1 p q
      (p + q) (by omega) rfl).inv, ← cancel_epi (cokernel.π (den M.X (filtrationSubobject M) 1 p
      (p + q))), reassoc_of% M.π_firstPageIso_hom p q (p + q) rfl,
    reassoc_of% M.firstPageClass_comp_δ p (p + q) (p + 1 + q) hn',
    ← M.π_firstPageIso_hom (p + 1) q (p + 1 + q) rfl]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, eIso_inv_rfl, Category.id_comp]
  have hd := pageComplex_d M.X (filtrationSubobject M) 1 (pq := (p, q)) (pq' := (p + 1, q))
    (Prod.ext rfl (by simp))
  refine (congrArg (cokernel.π (den M.X (filtrationSubobject M) 1 p (p + q)) ≫ ·) hd).trans ?_
  exact π_comp_pageMap' M.X (filtrationSubobject M) 1 p (p + q) (p + 1) (p + 1 + q) rfl _

end CochainComplex.Filtered
