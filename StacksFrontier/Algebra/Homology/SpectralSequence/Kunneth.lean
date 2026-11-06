module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.LocalRing.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality
public import StacksFrontier.CategoryTheory.Subobject.Butterfly
public import StacksFrontier.Homology.KFlat.FilteredResolution
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.TensorComplex.Monoidal

/-!
# The Kunneth spectral sequence of two filtered complexes

Let `R` be a commutative ring and let `K` and `L` be decreasingly filtered cochain complexes of
`R`-modules. The *convolution filtration* on the total tensor product `K ⊗ L` is the filtration
whose `p`-th step is the smallest subcomplex containing the image of `F^i K ⊗ F^j L` for every
`i + j = p`. When the terms, the filtration steps and the graded pieces of both factors are flat
and K-flat, the graded pieces of the convolution filtration are the direct sums
`⨁_{i + j = p} gr^i K ⊗ gr^j L`, so the first page of the associated spectral sequence is
`E_1^{p, q} = ⨁_{i + j = p} H^{p + q}(gr^i K ⊗ gr^j L)` — the Kunneth first page.

This spectral sequence is bounded and converges to `H^*(K ⊗ L)` in two situations: when both
filtrations are finite, and when the filtration steps of both factors are eventually acyclic in
one direction and eventually quasi-isomorphic to the whole complex in the other. For arbitrary
filtered complexes of modules, a filtered K-flat resolution reduces the general case to the
flat one, which gives the Kunneth spectral sequence of a pair of filtered complexes.

## Main results

* `CochainComplex.Kunneth.exists_kunneth_convolution_spectral_sequence`: for filtered complexes
  whose terms, steps and graded pieces are flat and K-flat, the convolution filtration on the
  tensor product carries a spectral sequence with the Kunneth first page, bounded and convergent
  under either of the two hypotheses above.
* `CochainComplex.Kunneth.exists_kunneth_filtered_complex`: for arbitrary filtered complexes of
  modules, a filtered K-flat resolution of each factor produces a filtered representative of
  their derived tensor product whose spectral sequence has the Kunneth first page and converges
  under eventual acyclicity and eventual quasi-isomorphism of the original filtration steps.

## References

* [The Stacks Project, Tag 0H7W](https://stacks.math.columbia.edu/tag/0H7W)
* [The Stacks Project, Tag 0H7Y](https://stacks.math.columbia.edu/tag/0H7Y)
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

open scoped TensorProduct

namespace CochainComplex.Kunneth

universe u v

/-- Zero terms persist from one page of a spectral sequence to the next. -/
private lemma isZero_page_succ (R : Type u) [CommRing R]
    (E : CohomologicalSpectralSequence (ModuleCat.{u} R) 0)
    (r : ℤ) (hr : 0 ≤ r) (p q : ℤ)
    (h : IsZero ((E.page r hr).X (p, q))) :
    IsZero ((E.page (r + 1) (by omega)).X (p, q)) := by
  have hh : IsZero ((E.page r hr).homology (p, q)) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ h
  exact IsZero.of_iso hh (E.iso r (r + 1) (p, q)).symm

/-- A finite filtration on a complex is finite in every cohomological degree. -/
private lemma degreewiseFinite_of_finite (R : Type u) [CommRing R]
    (T : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ)
    (hT : T.filtration.IsFinite) : T.filtration.IsDegreewiseFinite := by
  obtain ⟨a, ha⟩ := hT.exists_isIso_ι
  obtain ⟨b, hb⟩ := hT.exists_isZero_obj
  intro n
  exact ⟨a, b, inferInstanceAs (IsIso ((T.filtration.ι.app (op a)).f n)),
    (HomologicalComplex.eval _ _ n).map_isZero hb⟩

/-- Boundedness on page zero implies boundedness on page one. -/
private lemma finite_page_one_of_finite_page_zero (R : Type u) [CommRing R]
    (E : CohomologicalSpectralSequence (ModuleCat.{u} R) 0)
    (h : ∀ n : ℤ,
      {p : ℤ | ¬ IsZero ((E.page 0).X (p, n - p))}.Finite) :
    ∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite := by
  intro n
  apply (h n).subset
  intro p hp
  by_contra hz
  have hz0 : IsZero ((E.page 0).X (p, n - p)) := by simpa using hz
  exact hp (isZero_page_succ R E 0 (by omega) p (n - p) hz0)

/-- For a finite filtration, the first page is bounded, the induced filtration on cohomology is
finite, the differentials eventually vanish, and the stable cycles and boundaries are the limits
of the cycles and boundaries. -/
private lemma finite_filtration_consequences (R : Type u) [CommRing R]
    (T : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ)
    (hT : T.filtration.IsFinite)
    (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
    (FH : ∀ (n _p : ℤ), Subobject (T.X.homology n))
    (hFH : ∀ n p : ℤ, FH n p =
      imageSubobject (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))
    (E : CohomologicalSpectralSequence (ModuleCat.{u} R) 0)
    (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))) :
    (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite) ∧
    (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
    (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
    (∀ p n : ℤ,
      IsGLB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n)
        (kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.«exists» (T.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔
            F (p + 1) n)
        (imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)) := by
  obtain ⟨h0, hFHfinite, hreg, hstable, _⟩ :=
    CochainComplex.isBounded_and_converges_of_isDegreewiseFinite T
      (degreewiseFinite_of_finite R T hT) F hF Z hZ D hD FH hFH E hE
  exact ⟨finite_page_one_of_finite_page_zero R E h0, hFHfinite, hreg, hstable⟩

/-- Once stable cycles and boundaries agree with the ordinary cycles and boundaries, the
canonical map from the latter to the associated graded piece is an isomorphism. -/
private lemma stable_page_comparison (R : Type u) [CommRing R]
    (T : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n))
    (p n : ℤ)
    (hstable :
      IsGLB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n)
        (kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.«exists» (T.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔
            F (p + 1) n)
        (imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)) :
    let A := (Subobject.pullback (T.X.iCycles n)).obj (F p n)
    let N := kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
    let B := imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
    ∃ (a : (A : ModuleCat.{u} R) ⟶ (N : ModuleCat.{u} R))
      (b : (A : ModuleCat.{u} R) ⟶
        image (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))
      (e : cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) ≅
        cokernel (image.preComp
          (HomologicalComplex.homologyMap (T.filtration.diagram.map
            (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
          (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))),
      A.arrow ≫ T.X.iCycles n = a ≫ N.arrow ∧
      A.arrow ≫ T.X.homologyπ n =
        b ≫ image.ι (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n) ∧
      a ≫ cokernel.π (Subobject.ofLE (B ⊓ N) N inf_le_right) ≫ e.hom =
        b ≫ cokernel.π (image.preComp
          (HomologicalComplex.homologyMap (T.filtration.diagram.map
            (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
          (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n)) := by
  dsimp
  let A := (Subobject.pullback (T.X.iCycles n)).obj (F p n)
  let N := kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
  let B := imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
  obtain ⟨_, a, b, _, _, _, ha, hb, _, _, _, _⟩ :=
    CochainComplex.exists_epi_gradedPiece_homology_of_isGLB_isLUB
      T p n F hF A rfl N B hstable.1 hstable.2
  have hcmp := (CochainComplex.exists_iso_stablePage_iff_and_isGLB_isLUB_inducedFiltration_iff
    T p n F hF A rfl N B rfl rfl
      (fun p' => imageSubobject (HomologicalComplex.homologyMap
        (T.filtration.ι.app (op p')) n)) (fun _ => rfl)).1
  obtain ⟨e, he⟩ := (hcmp N B hstable.1 hstable.2 a ha.symm b hb.symm).2 ⟨rfl, rfl⟩
  exact ⟨a, b, e, ha, hb, he⟩

/-- Containment in a subobject is detected by its cokernel. -/
private lemma mk_le_iff_comp_cokernel_eq_zero {C : Type*} [Category C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) [Mono f] (Q : Subobject Y) :
    Subobject.mk f ≤ Q ↔ f ≫ cokernel.π Q.arrow = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Subobject.ofMkLE_arrow h, Category.assoc, cokernel.condition, comp_zero]
  · let hc := Abelian.monoIsKernelOfCokernel (C := C) (f := Q.arrow) _
      (cokernelIsCokernel Q.arrow)
    exact Subobject.mk_le_of_comm (hc.lift (KernelFork.ofι f h))
      (hc.fac (KernelFork.ofι f h) WalkingParallelPair.zero)

/-- An image is contained in a subobject exactly when its quotient annihilates the map. -/
private lemma imageSubobject_le_iff_comp_cokernel_eq_zero {C : Type*} [Category C]
    [Abelian C] {X Y : C} (f : X ⟶ Y) (Q : Subobject Y) :
    imageSubobject f ≤ Q ↔ f ≫ cokernel.π Q.arrow = 0 := by
  show Subobject.mk (image.ι f) ≤ Q ↔ _
  rw [mk_le_iff_comp_cokernel_eq_zero]
  refine ⟨fun h => ?_, fun h => zero_of_epi_comp (factorThruImage f) (by simpa using h)⟩
  rw [← image.fac f, Category.assoc, h, comp_zero]

/-- A functor preserving images and coproducts preserves the universal property of a sum. -/
private lemma map_image_ι_sigma_desc_le_iff
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (G : C ⥤ D) [G.PreservesMonomorphisms] [G.PreservesEpimorphisms]
    [G.PreservesZeroMorphisms] {I : Type*} (A : I → C) [HasCoproduct A]
    [HasCoproduct (fun i => G.obj (A i))]
    [PreservesColimit (Discrete.functor A) G]
    {X : C} (f : ∀ i, A i ⟶ X) (Q : Subobject (G.obj X)) :
    Subobject.mk (G.map (image.ι (Sigma.desc f))) ≤ Q ↔
      ∀ i, imageSubobject (G.map (f i)) ≤ Q := by
  simp only [imageSubobject_le_iff_comp_cokernel_eq_zero]
  rw [mk_le_iff_comp_cokernel_eq_zero]
  have hfac : G.map (factorThruImage (Sigma.desc f)) ≫
      G.map (image.ι (Sigma.desc f)) = G.map (Sigma.desc f) := by
    rw [← G.map_comp, image.fac]
  constructor
  · intro h i
    have hf : G.map (Sigma.desc f) ≫ cokernel.π Q.arrow = 0 := by
      rw [← hfac, Category.assoc, h, comp_zero]
    have hi := congrArg (fun k => G.map (Sigma.ι A i) ≫ k) hf
    simpa only [← G.map_comp_assoc, Sigma.ι_desc, comp_zero] using hi
  · intro h
    apply zero_of_epi_comp (G.map (factorThruImage (Sigma.desc f)))
    rw [← Category.assoc, hfac]
    apply zero_of_epi_comp (sigmaComparison G A)
    apply Sigma.hom_ext
    intro i
    simpa only [Category.assoc, ι_comp_sigmaComparison_assoc, ← G.map_comp_assoc,
      Sigma.ι_desc, comp_zero] using h i

variable {R : Type u} [CommRing R]
    (K L : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ)

/-- The direct sum of tensor products of filtration steps of total filtration degree `p`. -/
private noncomputable abbrev tensorFiltrationSum (p : ℤ) :=
  ∐ fun i : ℤ => K.filtration.obj (op i) ⊗ L.filtration.obj (op (p - i))

/-- The sum of the canonical maps from tensor products of filtration steps. -/
private noncomputable abbrev tensorFiltrationSumι (p : ℤ) :
    tensorFiltrationSum K L p ⟶ K.X ⊗ L.X :=
  Sigma.desc fun i : ℤ =>
    K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i))

/-- Images of the tensor sums decrease with total filtration degree. -/
private lemma tensorFiltrationSumι_antitone :
    Antitone (fun p => imageSubobject (tensorFiltrationSumι K L p)) := by
  intro p q hpq
  let t : tensorFiltrationSum K L q ⟶ tensorFiltrationSum K L p :=
    Sigma.desc fun i : ℤ =>
      (𝟙 (K.filtration.obj (op i)) ⊗ₘ
        L.filtration.diagram.map (homOfLE (sub_le_sub_right hpq i)).op) ≫
      Sigma.ι (fun j : ℤ => K.filtration.obj (op j) ⊗
        L.filtration.obj (op (p - j))) i
  have h : t ≫ tensorFiltrationSumι K L p = tensorFiltrationSumι K L q := by
    apply Sigma.hom_ext
    intro i
    dsimp [t, tensorFiltrationSumι]
    simp only [Sigma.ι_desc_assoc, Sigma.ι_desc, Category.assoc, tensorHom_comp_tensorHom,
      Category.id_comp]
    congr 1
    simp
  exact imageSubobject_le (tensorFiltrationSumι K L q)
    (t ≫ factorThruImageSubobject (tensorFiltrationSumι K L p)) (by simp [h])

/-- The tensor product equipped with the convolution filtration. -/
private noncomputable def tensorConvolution :
    FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ where
  X := K.X ⊗ L.X
  filtration.toMonoOver :=
    ({ obj p := imageSubobject (tensorFiltrationSumι K L p.unop)
       map {p q} f := homOfLE (tensorFiltrationSumι_antitone K L (leOfHom f.unop)) } :
      ℤᵒᵖ ⥤ Subobject (K.X ⊗ L.X)) ⋙ Subobject.representative

/-- The convolution filtration is the least subcomplex containing every tensor summand. -/
private lemma tensorConvolution_le_iff (p n : ℤ)
    (Q : Subobject ((K.X ⊗ L.X).X n)) :
    Subobject.mk (((tensorConvolution K L).filtration.ι.app (op p)).f n) ≤ Q ↔
      ∀ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = p},
        imageSubobject (((K.filtration.ι.app (op ij.1.1)) ⊗ₘ
          (L.filtration.ι.app (op ij.1.2))).f n) ≤ Q := by
  show Subobject.mk ((HomologicalComplex.eval _ _ n).map
    (imageSubobject (tensorFiltrationSumι K L p)).arrow) ≤ Q ↔ _
  have heq : Subobject.mk ((HomologicalComplex.eval _ _ n).map
      (imageSubobject (tensorFiltrationSumι K L p)).arrow) =
      Subobject.mk ((HomologicalComplex.eval _ _ n).map
        (image.ι (tensorFiltrationSumι K L p))) :=
    Subobject.mk_eq_mk_of_comm _ _
      ((HomologicalComplex.eval _ _ n).mapIso (imageSubobjectIso (tensorFiltrationSumι K L p)))
      (by simp only [Functor.mapIso_hom, ← Functor.map_comp, imageSubobject_arrow])
  rw [heq]
  rw [map_image_ι_sigma_desc_le_iff (HomologicalComplex.eval _ _ n)
    (fun i : ℤ => K.filtration.obj (op i) ⊗ L.filtration.obj (op (p - i)))
    (fun i => K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i))) Q]
  constructor
  · rintro h ⟨⟨i, j⟩, hij⟩
    dsimp at hij ⊢
    have hj : j = p - i := by omega
    subst j
    exact h i
  · intro h i
    exact h ⟨(i, p - i), by omega⟩

/-- A decreasing filtration remains zero above a zero step. -/
private lemma filtration_isZero_of_le {C : Type*} [Category C] [HasZeroMorphisms C]
    {X : C} (F : Filtration X ℤᵒᵖ) {a b : ℤ} (hab : a ≤ b)
    (ha : IsZero (F.obj (op a))) : IsZero (F.obj (op b)) :=
  IsZero.of_mono (F.diagram.map (homOfLE hab).op) ha

/-- Tensoring a zero cochain map on the left gives zero. -/
private lemma cochain_zero_tensor
    {P Q S T : CochainComplex (ModuleCat.{u} R) ℤ} (g : S ⟶ T) :
    (0 : P ⟶ Q) ⊗ₘ g = 0 := by
  show HomologicalComplex.mapBifunctorMap (0 : P ⟶ Q) g
    (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) = 0
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp

/-- Tensoring a zero cochain map on the right gives zero. -/
private lemma cochain_tensor_zero
    {P Q S T : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) :
    f ⊗ₘ (0 : S ⟶ T) = 0 := by
  show HomologicalComplex.mapBifunctorMap f (0 : S ⟶ T)
    (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) = 0
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp

/-- The convolution of two finite filtrations is finite. -/
private lemma tensorConvolution_isFinite
    (hK : K.filtration.IsFinite) (hL : L.filtration.IsFinite) :
    (tensorConvolution K L).filtration.IsFinite := by
  obtain ⟨a, ha⟩ := hK.exists_isIso_ι
  obtain ⟨b, hb⟩ := hL.exists_isIso_ι
  obtain ⟨c, hc⟩ := hK.exists_isZero_obj
  obtain ⟨d, hd⟩ := hL.exists_isZero_obj
  refine Filtration.IsFinite.of_exists ?_ ?_
  · refine ⟨a + b, ?_⟩
    have : IsIso (L.filtration.ι.app (op (a + b - a))) := by
      rw [add_sub_cancel_left]
      infer_instance
    have hcomp : IsIso (Sigma.ι (fun i : ℤ => K.filtration.obj (op i) ⊗
        L.filtration.obj (op (a + b - i))) a ≫ tensorFiltrationSumι K L (a + b)) := by
      dsimp only [tensorFiltrationSumι]
      rw [Sigma.ι_desc]
      infer_instance
    have : Epi (tensorFiltrationSumι K L (a + b)) := epi_of_epi
      (Sigma.ι (fun i : ℤ => K.filtration.obj (op i) ⊗
        L.filtration.obj (op (a + b - i))) a) _
    show IsIso (imageSubobject (tensorFiltrationSumι K L (a + b))).arrow
    have : Epi (imageSubobject (tensorFiltrationSumι K L (a + b))).arrow :=
      epi_of_epi_fac (imageSubobject_arrow_comp _)
    exact isIso_of_mono_of_epi _
  · refine ⟨c + d, ?_⟩
    have hzero : tensorFiltrationSumι K L (c + d) = 0 := by
      apply Sigma.hom_ext
      intro i
      dsimp only [tensorFiltrationSumι]
      rw [Sigma.ι_desc, comp_zero]
      by_cases hi : c ≤ i
      · rw [(filtration_isZero_of_le K.filtration hi hc).eq_of_src
          (K.filtration.ι.app (op i)) 0, cochain_zero_tensor]
      · rw [(filtration_isZero_of_le L.filtration (show d ≤ c + d - i by omega) hd).eq_of_src
          (L.filtration.ι.app (op (c + d - i))) 0, cochain_tensor_zero]
    show IsZero (imageSubobject (tensorFiltrationSumι K L (c + d)) :
      CochainComplex (ModuleCat R) ℤ)
    rw [hzero, imageSubobject_zero]
    exact (isZero_zero _).of_iso Subobject.botCoeIsoZero

/-- The spectral sequence of a filtered complex has the standard cycle-boundary pages, and its
first page is the cohomology of the associated graded pieces. -/
private lemma exists_filteredComplex_spectralSequence
    {C : Type u} [Category.{v} C] [Abelian C]
    (T : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ) :
    ∃ (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
      (Z D : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
      (FH : ∀ (n _p : ℤ), Subobject (T.X.homology n))
      (E : CohomologicalSpectralSequence C 0)
      (_hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
        cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))),
      (∀ p n : ℤ, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n)) ∧
      (∀ r p n : ℤ, Z r p n =
        F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1))) ∧
      (∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
        (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1))) ∧
      (∀ n p : ℤ, FH n p =
        imageSubobject (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n)) ∧
      (∀ p q : ℤ, Nonempty ((E.page 1 (by omega)).X (p, q) ≅
        ((FilteredObject.gr p).obj T).homology (p + q))) := by
  have hF : ∀ p n : ℤ, CochainComplex.filtrationSubobject T p n =
      Subobject.mk ((T.filtration.ι.app (op p)).f n) := fun _ _ => rfl
  obtain ⟨e, -, -, -, -, hone⟩ :=
    CochainComplex.exists_iso_spectralSequence_page T (CochainComplex.filtrationSubobject T) hF
      (FilteredComplexSpectralSequence.cycles T.X (CochainComplex.filtrationSubobject T))
      (fun _ _ _ => rfl)
      (FilteredComplexSpectralSequence.boundaries T.X (CochainComplex.filtrationSubobject T))
      (fun _ _ _ => rfl)
  exact ⟨CochainComplex.filtrationSubobject T,
    FilteredComplexSpectralSequence.cycles T.X (CochainComplex.filtrationSubobject T),
    FilteredComplexSpectralSequence.boundaries T.X (CochainComplex.filtrationSubobject T),
    fun n p => imageSubobject (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n),
    CochainComplex.spectralSequenceOf T (CochainComplex.filtrationSubobject T) hF, e, hF,
    fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun p q => hone p q (p + q) rfl⟩

/-- Reindexing a morphism of graded objects by coproducts is the coproduct of its components. -/
private lemma graded_mapMap_eq_sigma_map {I J C : Type*} [Category C] [Abelian C]
    {X Y : GradedObject I C} (f : X ⟶ Y) (p : I → J) [X.HasMap p] [Y.HasMap p] (j : J) :
    GradedObject.mapMap f p j = Limits.Sigma.map (fun i : p ⁻¹' {j} => f i.1) := by
  apply Sigma.hom_ext
  rintro ⟨i, hi⟩
  set_option backward.isDefEq.respectTransparency false in
  simpa only [GradedObject.ιMapObj, GradedObject.mapObjFun, Sigma.ι_map] using
    (GradedObject.ι_mapMap f p i j hi)

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing a graded family by coproducts preserves componentwise monomorphisms. -/
private lemma graded_mapMap_mono {I J C : Type*} [Category C] [Abelian C]
    {X Y : GradedObject I C} (f : X ⟶ Y) (p : I → J)
    [X.HasMap p] [Y.HasMap p]
    (j : J) [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [∀ i, Mono (f i)] : Mono (GradedObject.mapMap f p j) := by
  have := HasExactColimitsOfShape.preservesFiniteLimits
    (J := Discrete (p ⁻¹' {j})) (C := C)
  rw [graded_mapMap_eq_sigma_map]
  let t : Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j) :=
    Discrete.natTrans (fun i => f i.as.1)
  have : ∀ i, Mono (t.app i) := fun i => by dsimp [t]; infer_instance
  have : Mono t := NatTrans.mono_of_mono_app t
  show Mono (colim.map t)
  infer_instance

/-- The tensor product of two monomorphisms of modules is monic if the target of the first
and the source of the second are flat. -/
private lemma moduleCat_mono_tensorHom {A B C D : ModuleCat.{u} R} (f : A ⟶ B) (g : C ⟶ D)
    [Mono f] [Mono g] [Module.Flat R B] [Module.Flat R C] : Mono (f ⊗ₘ g) :=
  (ModuleCat.mono_iff_injective _).mpr <| TensorProduct.map_injective_of_flat_flat _ _
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- The total tensor product of two monomorphisms is monic if the first target and
second source are degreewise flat. -/
private lemma cochain_tensorHom_mono
    {P Q S T : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (g : S ⟶ T) [Mono f] [Mono g]
    (hQ : ∀ n, Module.Flat R (Q.X n)) (hS : ∀ n, Module.Flat R (S.X n)) :
    Mono (f ⊗ₘ g) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  show Mono (GradedObject.mapMap
    (fun ij : ℤ × ℤ => (f.f ij.1 ▷ S.X ij.2) ≫ (Q.X ij.1 ◁ g.f ij.2))
      (fun ij => ij.1 + ij.2) n)
  have (ij : ℤ × ℤ) : Mono ((f.f ij.1 ▷ S.X ij.2) ≫ (Q.X ij.1 ◁ g.f ij.2)) := by
    rw [← MonoidalCategory.tensorHom_def]
    have := hQ ij.1
    have := hS ij.2
    exact moduleCat_mono_tensorHom _ _
  exact graded_mapMap_mono _ _ _

/-- A tensor product is acyclic if its right factor is acyclic and its left factor is K-flat. -/
private lemma acyclic_tensor_of_kFlat_left
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (hQ : Q.Acyclic) :
    (P ⊗ Q).Acyclic := by
  obtain ⟨s, _⟩ := TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R
  let := s
  exact (hP Q hQ).of_iso (β_ Q P)

/-- Tensoring on the right by a K-flat complex preserves quasi-isomorphisms. -/
private lemma quasiIso_tensor_id_of_kFlat
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) [QuasiIso f]
    (S : CochainComplex (ModuleCat.{u} R) ℤ) (hS : S.KFlat) :
    QuasiIso (f ⊗ₘ 𝟙 S) := by
  have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).mpr ‹QuasiIso f›
  have h := CochainComplex.KFlat.kFlat_tright_preserves_quasiIso S hS
    ((HomotopyCategory.quotient _ _).map f) hf
  change HomotopyCategory.quasiIso (ModuleCat R) (ComplexShape.up ℤ)
    ((HomotopyCategory.quotient _ _ ⋙ Tright S).map f) at h
  unfold Tright at h
  rw [descendF_comp_quotient] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp h

/-- Tensoring on the left by a K-flat complex preserves quasi-isomorphisms. -/
private lemma quasiIso_id_tensor_of_kFlat
    (S : CochainComplex (ModuleCat.{u} R) ℤ) (hS : S.KFlat)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso (𝟙 S ⊗ₘ f) := by
  obtain ⟨s, _⟩ := TotalTensorComplex.cochainComplex_symmetricMonoidalCategory R
  let := s
  have : QuasiIso (f ⊗ₘ 𝟙 S) := quasiIso_tensor_id_of_kFlat f S hS
  have heq : (𝟙 S ⊗ₘ f) ≫ (β_ S Q).hom = (β_ S P).hom ≫ (f ⊗ₘ 𝟙 S) :=
    (BraidedCategory.braiding_naturality (𝟙 S) f)
  have : QuasiIso ((𝟙 S ⊗ₘ f) ≫ (β_ S Q).hom) := by
    rw [heq]
    infer_instance
  exact quasiIso_of_comp_right _ (β_ S Q).hom

/-- Tensor images intersect in the tensor image of the two sources when the first
cokernel is flat. -/
private lemma range_rTensor_inf_range_lTensor
    {A B C D E : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E]
    [Module R A] [Module R B] [Module R C] [Module R D] [Module R E]
    (f : A →ₗ[R] B) (q : B →ₗ[R] E) (g : C →ₗ[R] D)
    (h : Function.Exact f q) (hq : Function.Surjective q)
    (hg : Function.Injective g) [Module.Flat R E] :
    (f.rTensor D).range ⊓ (g.lTensor B).range = (TensorProduct.map f g).range := by
  have hcomm : (g.lTensor E).comp (q.rTensor C) = (q.rTensor D).comp (g.lTensor B) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have hcomp := LinearMap.lTensor_comp_rTensor A f g
  have hcomp' := LinearMap.rTensor_comp_lTensor A f g
  apply le_antisymm
  · rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have hb0 : q.rTensor C b = 0 := by
      apply Module.Flat.lTensor_preserves_injective_linearMap g hg
      rw [map_zero, ← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, hb, ← ha]
      exact (rTensor_exact D h hq).apply_apply_eq_zero a
    obtain ⟨c, hc⟩ := (rTensor_exact C h hq b).mp hb0
    exact ⟨c, by rw [← hcomp, LinearMap.comp_apply, hc, hb]⟩
  · rintro x ⟨c, rfl⟩
    exact ⟨⟨g.lTensor A c, by rw [← LinearMap.comp_apply, hcomp']⟩,
      ⟨f.rTensor C c, by rw [← LinearMap.comp_apply, hcomp]⟩⟩

/-- Tensor products of two quasi-isomorphisms are quasi-isomorphisms when the intervening
complexes are K-flat. -/
private lemma quasiIso_tensorHom_of_kFlat
    {P Q S T : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (g : S ⟶ T) [QuasiIso f] [QuasiIso g]
    (hS : S.KFlat) (hQ : Q.KFlat) : QuasiIso (f ⊗ₘ g) := by
  have := quasiIso_tensor_id_of_kFlat f S hS
  have := quasiIso_id_tensor_of_kFlat Q hQ g
  have heq : f ⊗ₘ g = (f ⊗ₘ 𝟙 S) ≫ (𝟙 Q ⊗ₘ g) := by
    rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
  rw [heq]
  infer_instance

/-- A tensor product of filtration steps above the sum of the acyclicity bounds is acyclic. -/
private lemma tensor_steps_acyclic_of_add_lt
    (hkK : ∀ i : ℤ, (K.filtration.obj (op i)).KFlat)
    (hkL : ∀ j : ℤ, (L.filtration.obj (op j)).KFlat)
    (b c : ℤ)
    (hK : ∀ i : ℤ, b < i → (K.filtration.obj (op i)).Acyclic)
    (hL : ∀ j : ℤ, c < j → (L.filtration.obj (op j)).Acyclic)
    (i j : ℤ) (hij : b + c < i + j) :
    (K.filtration.obj (op i) ⊗ L.filtration.obj (op j)).Acyclic := by
  by_cases hi : b < i
  · exact hkL j _ (hK i hi)
  · exact acyclic_tensor_of_kFlat_left _ _ (hkK i) (hL j (by omega))

/-- The image of a monic map of complexes is acyclic when its source is acyclic. -/
private lemma imageSubobject_acyclic_of_mono
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) [Mono f] (hP : P.Acyclic) :
    (imageSubobject f : CochainComplex (ModuleCat R) ℤ).Acyclic :=
  hP.of_iso ((imageMonoIsoSource f).symm ≪≫ (imageSubobjectIso f).symm)

/-- The one-term intervals in the convolution construction are acyclic above the sum bound. -/
private lemma tensor_steps_image_acyclic_of_add_lt
    (hflatK : ∀ n : ℤ, Module.Flat R (K.X.X n))
    (hflatL : ∀ j n : ℤ, Module.Flat R ((L.filtration.obj (op j)).X n))
    (hkK : ∀ i : ℤ, (K.filtration.obj (op i)).KFlat)
    (hkL : ∀ j : ℤ, (L.filtration.obj (op j)).KFlat)
    (b c : ℤ)
    (hK : ∀ i : ℤ, b < i → (K.filtration.obj (op i)).Acyclic)
    (hL : ∀ j : ℤ, c < j → (L.filtration.obj (op j)).Acyclic)
    (i j : ℤ) (hij : b + c < i + j) :
    (imageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j)) :
      CochainComplex (ModuleCat R) ℤ).Acyclic := by
  have := cochain_tensorHom_mono (K.filtration.ι.app (op i))
    (L.filtration.ι.app (op j)) hflatK (hflatL j)
  exact imageSubobject_acyclic_of_mono _
    (tensor_steps_acyclic_of_add_lt K L hkK hkL b c hK hL i j hij)

/-- A transition between steps that both map quasi-isomorphically to the ambient complex
is itself a quasi-isomorphism. -/
private lemma quasiIso_filtration_map_of_quasiIso_ι
    {C : Type*} [Category C] [Abelian C]
    {X : CochainComplex C ℤ} (F : Filtration X ℤᵒᵖ)
    {i j : ℤ} (hij : i ≤ j)
    [QuasiIso (F.ι.app (op i))] [QuasiIso (F.ι.app (op j))] :
    QuasiIso (F.diagram.map (homOfLE hij).op) := by
  have : QuasiIso (F.diagram.map (homOfLE hij).op ≫ F.ι.app (op i)) := by
    rw [Filtration.diagram_map_comp_ι_app]
    infer_instance
  exact quasiIso_of_comp_right _ (F.ι.app (op i))

/-- The central one-term interval computes the total tensor product below the sum bound. -/
private lemma tensor_steps_quasiIso_of_lt
    (hkK : K.X.KFlat)
    (hkL : ∀ j : ℤ, (L.filtration.obj (op j)).KFlat)
    (a c : ℤ)
    (hK : ∀ i : ℤ, i < a → QuasiIso (K.filtration.ι.app (op i)))
    (hL : ∀ j : ℤ, j < c → QuasiIso (L.filtration.ι.app (op j)))
    (i j : ℤ) (hi : i < a) (hj : j < c) :
    QuasiIso (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j)) := by
  have := hK i hi
  have := hL j hj
  exact quasiIso_tensorHom_of_kFlat _ _ (hkL j) hkK

/-- Exact colimits of acyclic complexes are acyclic. -/
private lemma acyclic_of_isColimit
    {C I J : Type*} [Category C] [Abelian C] [Category J]
    {c : ComplexShape I} [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (D : J ⥤ HomologicalComplex C c) (s : Cocone D) (hs : IsColimit s)
    (hD : ∀ j, (D.obj j).Acyclic) : s.pt.Acyclic := by
  intro i
  let E := D ⋙ HomologicalComplex.shortComplexFunctor C c i
  let S := (ShortComplex.functorEquivalence J C).inverse.obj E
  have href : JointlyReflectIsomorphisms (fun j : J ↦ (evaluation J C).obj j) :=
    ⟨fun f h ↦ by
      have : ∀ j, IsIso (f.app j) := h
      exact NatIso.isIso_of_isIso_app f⟩
  have hS : S.Exact := by
    refine (href.exact_iff S).mpr fun j ↦ ?_
    exact ShortComplex.exact_of_iso
      (((ShortComplex.functorEquivalence J C).counitIso.app E).app j).symm (hD j i)
  exact colim.exact_mapShortComplex hS
    (isColimitOfPreserves (HomologicalComplex.eval C c (c.prev i)) hs)
    (isColimitOfPreserves (HomologicalComplex.eval C c i) hs)
    (isColimitOfPreserves (HomologicalComplex.eval C c (c.next i)) hs)
    (s.pt.d _ _) (s.pt.d _ _)
    (fun j ↦ (s.ι.app j).comm _ _) (fun j ↦ (s.ι.app j).comm _ _)

/-- The transition maps of a filtration are monomorphisms. -/
private lemma mono_filtration_diagram_map {C : Type*} [Category C] [Abelian C]
    {X : CochainComplex C ℤ} (F : Filtration X ℤᵒᵖ) {i j : ℤ} (hij : i ≤ j) :
    Mono (F.diagram.map (homOfLE hij).op) :=
  mono_of_mono_fac (Filtration.diagram_map_comp_ι_app F _)

/-- Degreewise, a monomorphism of complexes of modules and its cokernel map are exact. -/
private lemma exact_cokernel_f {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) [Mono f]
    (n : ℤ) : Function.Exact (f.f n).hom ((cokernel.π f).f n).hom ∧
      Function.Surjective ((cokernel.π f).f n).hom ∧ Function.Injective (f.f n).hom := by
  let S := (ShortComplex.cokernelSequence f).map (HomologicalComplex.eval _ _ n)
  have : Epi S.g := by dsimp [S]; infer_instance
  have : Mono S.f := by change Mono (f.f n); infer_instance
  exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp
    ((ShortComplex.cokernelSequence_exact f).map _),
    (ModuleCat.epi_iff_surjective _).mp inferInstance,
    (ModuleCat.mono_iff_injective _).mp inferInstance⟩

/-- The inclusion of one filtration step into its predecessor stays monic after tensoring
with any module when the corresponding graded piece is flat. -/
private lemma lTensor_filtration_step_injective
    (hflat : ∀ i n : ℤ, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    (i n : ℤ) (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective ((((K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : i ⟶ i + 1).op).f n).hom).lTensor M) := by
  let f := K.filtration.diagram.map
    (homOfLE (Int.le_add_one le_rfl) : i ⟶ i + 1).op
  have : Mono f := mono_filtration_diagram_map K.filtration _
  obtain ⟨hex, hsurj, hinj⟩ := exact_cokernel_f f n
  have : Module.Flat R ((cokernel f).X n) := hflat i n
  exact LinearMap.lTensor_injective_of_exact_of_flat _ hsurj _ hinj hex M

set_option backward.isDefEq.respectTransparency false in
/-- Every finite composite of the step inclusions stays monic after tensoring. -/
private lemma lTensor_filtration_map_injective
    (hflat : ∀ i n : ℤ, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    (n : ℤ) (M : Type*) [AddCommGroup M] [Module R M]
    {i j : ℤ} (hij : i ≤ j) :
    Function.Injective ((((K.filtration.diagram.map (homOfLE hij).op).f n).hom).lTensor M) := by
  induction j, hij using Int.leInduction with
  | base =>
      simpa using (Function.injective_id : Function.Injective
        (id : M ⊗[R] ((K.filtration.obj (op i)).X n) → _))
  | succ j hij ih =>
      have heq : K.filtration.diagram.map
          (homOfLE (show i ≤ j + 1 by omega)).op =
          K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : j ⟶ j + 1).op ≫
            K.filtration.diagram.map (homOfLE hij).op := by
        rw [← Functor.map_comp]
        rfl
      rw [heq]
      simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.lTensor_comp,
        LinearMap.coe_comp] using
        ih.comp (lTensor_filtration_step_injective K hflat j n M)

/-- A cokernel with flat middle term is flat if its kernel map stays monic after tensoring. -/
private lemma flat_of_exact_of_rTensor_injective
    {A B P : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup P]
    [Module R A] [Module R B] [Module R P] [Module.Flat R B]
    (f : A →ₗ[R] B) (q : B →ₗ[R] P)
    (h : Function.Exact f q) (hq : Function.Surjective q)
    (hf : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Function.Injective (f.rTensor N)) : Module.Flat R P := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro M N _ _ _ _ g hg
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective h hq
    (LinearMap.exact_map_mkQ_range g) (Submodule.mkQ_surjective _)
    (hf (N ⧸ LinearMap.range g)) (Module.Flat.lTensor_preserves_injective_linearMap g hg)

/-- Quotients of two filtration steps have flat terms when all steps and graded pieces do. -/
private lemma flat_cokernel_filtration_map
    (hflat : ∀ i n : ℤ, Module.Flat R ((K.filtration.obj (op i)).X n))
    (hgr : ∀ i n : ℤ, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    {i j : ℤ} (hij : i ≤ j) (n : ℤ) :
    Module.Flat R ((cokernel (K.filtration.diagram.map (homOfLE hij).op)).X n) := by
  let f := K.filtration.diagram.map (homOfLE hij).op
  have : Mono f := mono_filtration_diagram_map K.filtration _
  obtain ⟨hex, hsurj, hinj⟩ := exact_cokernel_f f n
  have : Module.Flat R ((K.filtration.obj (op i)).X n) := hflat i n
  exact flat_of_exact_of_rTensor_injective _ _ hex hsurj fun N _ _ ↦
    (LinearMap.lTensor_inj_iff_rTensor_inj N _).mp (lTensor_filtration_map_injective K hgr n N hij)

/-- The image of a coproduct map is the least upper bound of its summand images. -/
private lemma imageSubobject_sigma_desc_isLUB
    {C I : Type*} [Category C] [Abelian C]
    (A : I → C) [HasCoproduct A] {X : C} (f : ∀ i, A i ⟶ X) :
    IsLUB (Set.range (fun i => imageSubobject (f i))) (imageSubobject (Sigma.desc f)) := by
  have : HasCoproduct (fun i => (𝟭 C).obj (A i)) := by
    show HasCoproduct A
    infer_instance
  have h (Q : Subobject X) : imageSubobject (Sigma.desc f) ≤ Q ↔
      ∀ i, imageSubobject (f i) ≤ Q :=
    map_image_ι_sigma_desc_le_iff (𝟭 C) A f Q
  refine ⟨?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact (h _).mp le_rfl i
  · intro Q hQ
    exact (h Q).mpr (fun i => hQ ⟨i, rfl⟩)

/-- The subcomplex generated by a finite interval of tensor filtration steps. -/
private noncomputable abbrev tensorFiltrationInterval (p s t : ℤ) :
    Subobject (K.X ⊗ L.X) :=
  (Finset.Icc s t).sup fun i =>
    imageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i)))

/-- A singleton interval is the image of the corresponding tensor product. -/
private lemma tensorFiltrationInterval_self (p i : ℤ) :
    tensorFiltrationInterval K L p i i =
      imageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i))) := by
  simp [tensorFiltrationInterval]

/-- Enlarging the index interval enlarges its tensor-generated subcomplex. -/
private lemma tensorFiltrationInterval_mono (p : ℤ) {s t s' t' : ℤ}
    (hs : s' ≤ s) (ht : t ≤ t') :
    tensorFiltrationInterval K L p s t ≤ tensorFiltrationInterval K L p s' t' :=
  Finset.sup_mono (Finset.Icc_subset_Icc hs ht)

set_option backward.isDefEq.respectTransparency false in
/-- The convolution step is the supremum of the finite, symmetric tensor intervals. -/
private lemma tensorFiltrationSumι_image_eq_iSup (p : ℤ) :
    imageSubobject (tensorFiltrationSumι K L p) =
      ⨆ m : ℕ, tensorFiltrationInterval K L p (-m) m := by
  have heq := (imageSubobject_sigma_desc_isLUB
    (fun i : ℤ => K.filtration.obj (op i) ⊗ L.filtration.obj (op (p - i)))
    (fun i => K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i)) )).iSup_eq.symm
  rw [tensorFiltrationSumι, heq]
  apply le_antisymm
  · refine iSup_le fun i ↦ le_iSup_of_le i.natAbs ?_
    dsimp only [tensorFiltrationInterval]
    exact Finset.le_sup (f := fun i => imageSubobject
      (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i))))
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · exact iSup_le fun m ↦ Finset.sup_le fun i _ ↦ le_iSup (fun j : ℤ => imageSubobject
      (K.filtration.ι.app (op j) ⊗ₘ L.filtration.ι.app (op (p - j)))) i

/-- The cocone in `Over X` of a diagram of subobjects of `X` with vertex a larger subobject. -/
private noncomputable def subobjectOverCocone {X : CochainComplex (ModuleCat.{u} R) ℤ}
    {J : Type u} [SmallCategory J] (P : J ⥤ Subobject X) (Q : Subobject X)
    (hle : ∀ j, P.obj j ≤ Q) : Cocone ((P ⋙ Subobject.representative) ⋙ MonoOver.forget X) where
  pt := Over.mk Q.arrow
  ι :=
    { app j := Over.homMk (Subobject.ofLE (P.obj j) Q (hle j))
      naturality {i j} f := by
        apply Over.OverMorphism.ext
        apply (cancel_mono Q.arrow).mp
        exact (Over.w _).trans (Over.w _).symm }

/-- A filtered supremum of subobjects is the colimit of the subobjects. -/
private lemma nonempty_isColimit_subobjectOverCocone {X : CochainComplex (ModuleCat.{u} R) ℤ}
    {J : Type u} [SmallCategory J] [IsFiltered J] (P : J ⥤ Subobject X) (Q : Subobject X)
    (hle : ∀ j, P.obj j ≤ Q) (hQ : Q = ⨆ j, P.obj j) :
    Nonempty (IsColimit ((Over.forget X).mapCocone (subobjectOverCocone P Q hle))) := by
  have : Mono (subobjectOverCocone P Q hle).pt.hom := by change Mono Q.arrow; infer_instance
  refine ⟨IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup
    (P ⋙ Subobject.representative) _ ?_⟩
  change Subobject.mk Q.arrow = ⨆ j, Subobject.mk (P.obj j).arrow
  simpa only [Subobject.mk_arrow] using hQ

/-- Filtered unions of acyclic subcomplexes of a complex of modules are acyclic. -/
private lemma acyclic_iSup_of_filtered
    (X : CochainComplex (ModuleCat.{u} R) ℤ)
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (P : J ⥤ Subobject X)
    (hP : ∀ j, (P.obj j : CochainComplex (ModuleCat R) ℤ).Acyclic) :
    ((⨆ j, P.obj j : Subobject X) : CochainComplex (ModuleCat R) ℤ).Acyclic := by
  obtain ⟨hc⟩ := nonempty_isColimit_subobjectOverCocone P _ (le_iSup _) rfl
  exact acyclic_of_isColimit _ _ hc hP

/-- Eventual acyclicity and quasi-isomorphism of filtration steps imply canonical convergence. -/
private lemma isBounded_and_converges_of_step_bounds
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))
    (FH : ∀ (n _p : ℤ), Subobject (K.X.homology n))
    (hFH : ∀ n p : ℤ, FH n p =
      imageSubobject (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))
    (E : CohomologicalSpectralSequence A 0)
    (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
      cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))
    (a b : ℤ)
    (hzero : ∀ p : ℤ, b < p → (K.filtration.obj (op p)).Acyclic)
    (hiso : ∀ p : ℤ, p < a → QuasiIso (K.filtration.ι.app (op p))) :
    (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite) ∧
    (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
    (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
    (∀ p n : ℤ,
      IsGLB (Set.range fun r : ℕ ↦
          F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔
            F (p + 1) n)
        (kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ ↦
          F p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔
            F (p + 1) n)
        (imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)) ∧
    (∀ p n : ℤ,
      let C := (Subobject.pullback (K.X.iCycles n)).obj (F p n)
      let N := kernelSubobject (K.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
      let B := imageSubobject (K.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
      ∃ (a : (C : A) ⟶ (N : A))
        (b : (C : A) ⟶ image (HomologicalComplex.homologyMap
          (K.filtration.ι.app (op p)) n))
        (e : cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) ≅
          cokernel (image.preComp
            (HomologicalComplex.homologyMap (K.filtration.diagram.map
              (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
            (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n))),
        C.arrow ≫ K.X.iCycles n = a ≫ N.arrow ∧
        C.arrow ≫ K.X.homologyπ n =
          b ≫ image.ι (HomologicalComplex.homologyMap
            (K.filtration.ι.app (op p)) n) ∧
        a ≫ cokernel.π (Subobject.ofLE (B ⊓ N) N inf_le_right) ≫ e.hom =
          b ≫ cokernel.π (image.preComp
            (HomologicalComplex.homologyMap (K.filtration.diagram.map
              (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
            (HomologicalComplex.homologyMap
              (K.filtration.ι.app (op p)) n))) := by
  apply CochainComplex.isBounded_and_converges_of_eventually_isZero_of_eventually_isIso
    K F hF Z hZ D hD FH hFH E hE
  · intro n
    exact ⟨b + 1, fun p hp => (hzero p (by omega) n).isZero_homology⟩
  · intro n
    refine ⟨a - 1, fun p hp => ?_⟩
    have := hiso p (by omega)
    infer_instance

/-- Adding the top index to an interval extends the supremum over it. -/
private lemma sup_Icc_succ {C : Type*} [Category C] [Abelian C] {X : C}
    (P : ℤ → Subobject X) (s t : ℤ) (hst : s ≤ t + 1) :
    (Finset.Icc s (t + 1)).sup P = (Finset.Icc s t).sup P ⊔ P (t + 1) := by
  rw [show Finset.Icc s (t + 1) = insert (t + 1) (Finset.Icc s t) by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sup_insert, sup_comm]


private lemma tensorFiltrationInterval_succ (p s t : ℤ) (hst : s ≤ t + 1) :
    tensorFiltrationInterval K L p s (t + 1) =
      tensorFiltrationInterval K L p s t ⊔
        imageSubobject (K.filtration.ι.app (op (t + 1)) ⊗ₘ
          L.filtration.ι.app (op (p - (t + 1)))) := by
  exact sup_Icc_succ _ s t hst

/-- If every finite interval of tensor filtration summands is acyclic, then their
convolution step is acyclic. -/
private lemma tensorConvolution_acyclic_of_intervals (p : ℤ)
    (h : ∀ s t : ℤ, s ≤ t →
      (tensorFiltrationInterval K L p s t : CochainComplex (ModuleCat R) ℤ).Acyclic) :
    ((tensorConvolution K L).filtration.obj (op p)).Acyclic := by
  let P : ULift.{u} ℕ ⥤ Subobject (K.X ⊗ L.X) :=
    { obj m := tensorFiltrationInterval K L p (-m.down) m.down
      map {m n} f := homOfLE (tensorFiltrationInterval_mono K L p
        (by have := leOfHom f; change m.down ≤ n.down at this; omega)
        (by have := leOfHom f; change m.down ≤ n.down at this; omega)) }
  have hP : ∀ m, (P.obj m : CochainComplex (ModuleCat R) ℤ).Acyclic :=
    fun m => h _ _ (by omega)
  have hz := acyclic_iSup_of_filtered (K.X ⊗ L.X) P hP
  have heq : (⨆ m, P.obj m) = imageSubobject (tensorFiltrationSumι K L p) := by
    rw [tensorFiltrationSumι_image_eq_iSup]
    simp only [P, iSup_ulift]
  rw [heq] at hz
  exact hz

section

variable {A : Type*} [Category A] [Abelian A]

/-- Passing to three consecutive terms preserves colimits. -/
public lemma preservesColimitsOfShape_shortComplexFunctor {J : Type*} [Category J]
    [HasColimitsOfShape J A] (i : ℤ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i) :=
  ⟨fun {_} => ⟨fun hs => ⟨ShortComplex.isColimitOfIsColimitπ _
    (isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) _) hs)
    (isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) _) hs)
    (isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) _) hs)⟩⟩⟩

end

/-- Cohomology of a coproduct of module complexes is the coproduct of their cohomologies. -/
private noncomputable abbrev homologyCoproductIso {I : Type*} [Small.{u} I]
    (X : I → CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (∐ X).homology n ≅ ∐ (fun i => (X i).homology n) := by
  have : HasColimitsOfShape (Discrete (Shrink.{u} I)) (ModuleCat.{u} R) := inferInstance
  have : HasColimitsOfShape (Discrete I) (ModuleCat.{u} R) :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{u} I).symm)
  have := HasExactColimitsOfShape.of_domain_equivalence (C := ModuleCat R)
    (Discrete.equivalence (equivShrink.{u} I).symm)
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := ModuleCat R) (J := Discrete I) (ComplexShape.up ℤ) n
  exact (asIso (sigmaComparison (HomologicalComplex.homologyFunctor _ _ n) X)).symm

section MayerVietoris

variable {A : Type*} [Category A] [Abelian A]

/-- For subobjects `P` and `Q`, the sequence `P ⊓ Q → P ⊞ Q → P ⊔ Q` is short exact. -/
private lemma shortExact_inf_biprod_sup {X : A} (P Q : Subobject X) :
    (ShortComplex.mk
      (biprod.lift (Subobject.ofLE (P ⊓ Q) P inf_le_left)
        (-Subobject.ofLE (P ⊓ Q) Q inf_le_right))
      (biprod.desc (Subobject.ofLE P (P ⊔ Q) le_sup_left)
        (Subobject.ofLE Q (P ⊔ Q) le_sup_right))
      (by ext; simp)).ShortExact := by
  have hmono : Mono (biprod.lift (Subobject.ofLE (P ⊓ Q) P inf_le_left)
      (-Subobject.ofLE (P ⊓ Q) Q inf_le_right)) :=
    mono_of_mono_fac (biprod.lift_fst _ _)
  refine ShortComplex.ShortExact.mk' ?_ hmono ?_
  · rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro T x hx
    dsimp at x hx
    have hw : (x ≫ biprod.fst) ≫ P.arrow = (-(x ≫ biprod.snd)) ≫ Q.arrow := by
      have := congrArg (· ≫ (P ⊔ Q).arrow) hx
      simp only [Category.assoc, biprod.desc_eq, Preadditive.comp_add, Preadditive.add_comp,
        Subobject.ofLE_arrow, zero_comp] at this
      simp only [Category.assoc, Preadditive.neg_comp]
      rw [← sub_eq_zero, sub_neg_eq_add]
      exact this
    refine ⟨T, 𝟙 T, inferInstance, (Subobject.inf_isPullback P Q).lift _ _ hw, ?_⟩
    dsimp
    apply biprod.hom_ext <;> simp
  · rw [epi_iff_surjective_up_to_refinements]
    intro T y
    obtain ⟨T', z, hz, β, γ, fac⟩ := Subobject.exists_refinement_of_factors_sup
      (y ≫ (P ⊔ Q).arrow) (Subobject.factors_comp_arrow y)
    refine ⟨T', z, hz, biprod.lift β γ, ?_⟩
    apply (cancel_mono (P ⊔ Q).arrow).mp
    simp [fac]

/-- The join of two acyclic subcomplexes with acyclic intersection is acyclic. -/
private lemma acyclic_sup_of_acyclic {ι : Type*} {c : ComplexShape ι}
    {X : HomologicalComplex A c} (P Q : Subobject X)
    (hP : (P : HomologicalComplex A c).Acyclic) (hQ : (Q : HomologicalComplex A c).Acyclic)
    (hPQ : ((P ⊓ Q : Subobject X) : HomologicalComplex A c).Acyclic) :
    ((P ⊔ Q : Subobject X) : HomologicalComplex A c).Acyclic := by
  have hS := shortExact_inf_biprod_sup P Q
  have hB : ((P : HomologicalComplex A c) ⊞ (Q : HomologicalComplex A c)).Acyclic :=
    (ShortComplex.Splitting.ofHasBinaryBiproduct _ _).shortExact.acyclic_X₂ hP hQ
  have : QuasiIso (biprod.lift (Subobject.ofLE (P ⊓ Q) P inf_le_left)
      (-Subobject.ofLE (P ⊓ Q) Q inf_le_right)) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ⟨⟨0, (hPQ i).isZero_homology.eq_of_src _ _, (hB i).isZero_homology.eq_of_src _ _⟩⟩
  exact hS.acyclic_X₃ this

end MayerVietoris

/-- A monic square of modules is a pullback when its images have the expected intersection. -/
private lemma moduleCat_isPullback_of_range
    {P X Y Z : ModuleCat.{u} R} (t : P ⟶ X) (l : P ⟶ Y)
    (r : X ⟶ Z) (b : Y ⟶ Z) [Mono r] [Mono b] [Mono t]
    (w : t ≫ r = l ≫ b)
    (h : r.hom.range ⊓ b.hom.range = (t ≫ r).hom.range) :
    IsPullback t l r b := by
  apply IsPullback.of_map (forget (ModuleCat R)) w
  rw [Types.isPullback_iff]
  refine ⟨by ext x; exact congrArg (fun f : P ⟶ Z => f x) w,
    fun x y hxy => (ModuleCat.mono_iff_injective t).mp inferInstance hxy.1, ?_⟩
  intro x y hxy
  have hz : r x ∈ r.hom.range ⊓ b.hom.range := ⟨⟨x, rfl⟩, ⟨y, hxy.symm⟩⟩
  rw [h] at hz
  obtain ⟨z, hz⟩ := hz
  refine ⟨z, (ModuleCat.mono_iff_injective r).mp inferInstance hz, ?_⟩
  apply (ModuleCat.mono_iff_injective b).mp inferInstance
  exact (ModuleCat.hom_ext_iff.mp w ▸ hz).trans hxy

/-- A square of cochain complexes is a pullback if it is a pullback in every degree. -/
private lemma cochain_isPullback_of_f
    {P X Y Z : CochainComplex (ModuleCat.{u} R) ℤ}
    (t : P ⟶ X) (l : P ⟶ Y) (r : X ⟶ Z) (b : Y ⟶ Z)
    (w : t ≫ r = l ≫ b)
    (h : ∀ n, IsPullback (t.f n) (l.f n) (r.f n) (b.f n)) :
    IsPullback t l r b := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk t l w)
  apply HomologicalComplex.isLimitOfEval
  intro n
  exact (isLimitMapConePullbackConeEquiv _ _).symm (h n).isLimit

set_option backward.isDefEq.respectTransparency false in
/-- Exact coproducts preserve componentwise pullback squares of graded objects. -/
private lemma graded_mapMap_isPullback {I J C : Type*} [Category C] [Abelian C]
    {P X Y Z : GradedObject I C} (t : P ⟶ X) (l : P ⟶ Y)
    (r : X ⟶ Z) (b : Y ⟶ Z) (p : I → J)
    [P.HasMap p] [X.HasMap p] [Y.HasMap p] [Z.HasMap p]
    (j : J) [HasColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    [HasExactColimitsOfShape (Discrete (p ⁻¹' {j})) C]
    (h : ∀ i, IsPullback (t i) (l i) (r i) (b i)) :
    IsPullback (GradedObject.mapMap t p j) (GradedObject.mapMap l p j)
      (GradedObject.mapMap r p j) (GradedObject.mapMap b p j) := by
  have := HasExactColimitsOfShape.preservesFiniteLimits
    (J := Discrete (p ⁻¹' {j})) (C := C)
  simp only [graded_mapMap_eq_sigma_map]
  let t' : Discrete.functor (P.mapObjFun p j) ⟶ Discrete.functor (X.mapObjFun p j) :=
    Discrete.natTrans (fun i => t i.as.1)
  let l' : Discrete.functor (P.mapObjFun p j) ⟶ Discrete.functor (Y.mapObjFun p j) :=
    Discrete.natTrans (fun i => l i.as.1)
  let r' : Discrete.functor (X.mapObjFun p j) ⟶ Discrete.functor (Z.mapObjFun p j) :=
    Discrete.natTrans (fun i => r i.as.1)
  let b' : Discrete.functor (Y.mapObjFun p j) ⟶ Discrete.functor (Z.mapObjFun p j) :=
    Discrete.natTrans (fun i => b i.as.1)
  exact IsPullback.map (colim : (Discrete (p ⁻¹' {j}) ⥤ C) ⥤ C)
    (IsPullback.of_forall_isPullback_app (f₁ := t') (f₂ := l') (f₃ := r') (f₄ := b')
      (fun i => h i.as.1))

/-- The tensor square of monomorphisms is a pullback when its first cokernel is flat. -/
private lemma moduleCat_tensor_isPullback
    {A B C D E : ModuleCat.{u} R} (f : A ⟶ B) (q : B ⟶ E) (g : C ⟶ D)
    [Mono f] [Mono g] [Epi q]
    [Module.Flat R B] [Module.Flat R C] [Module.Flat R D] [Module.Flat R E]
    (h : Function.Exact f.hom q.hom) :
    IsPullback (f ⊗ₘ 𝟙 C) (𝟙 A ⊗ₘ g) (𝟙 B ⊗ₘ g) (f ⊗ₘ 𝟙 D) := by
  have := moduleCat_mono_tensorHom f (𝟙 C)
  have := moduleCat_mono_tensorHom f (𝟙 D)
  have := moduleCat_mono_tensorHom (𝟙 B) g
  apply moduleCat_isPullback_of_range _ _ _ _
    (by simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id])
  show (g.hom.lTensor B).range ⊓ (f.hom.rTensor D).range =
    ((g.hom.lTensor B).comp (f.hom.rTensor C)).range
  rw [inf_comm, LinearMap.lTensor_comp_rTensor]
  exact range_rTensor_inf_range_lTensor _ _ _ h
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    ((ModuleCat.mono_iff_injective _).mp inferInstance)

/-- The intersection represented by a pullback square of monomorphisms. -/
private lemma mk_inf_eq_of_isPullback {C : Type*} [Category C] [HasPullbacks C]
    {P X Y Z : C} {t : P ⟶ X} {l : P ⟶ Y} {r : X ⟶ Z} {b : Y ⟶ Z}
    [Mono r] [Mono b] [Mono t] (h : IsPullback t l r b) :
    Subobject.mk r ⊓ Subobject.mk b = Subobject.mk (t ≫ r) := by
  have := h.mono_fst_of_mono
  apply le_antisymm
  · let Q := Subobject.mk r ⊓ Subobject.mk b
    let x := Subobject.ofLEMk Q r inf_le_left
    let y := Subobject.ofLEMk Q b inf_le_right
    have w : x ≫ r = y ≫ b := by simp [x, y]
    apply Subobject.le_mk_of_comm (h.lift x y w)
    simp [x]
  · exact le_inf (Subobject.mk_le_mk_of_comm t rfl)
      (Subobject.mk_le_mk_of_comm l h.w.symm)

/-- A tensor square of complexes is a pullback under degreewise flatness conditions. -/
private lemma cochain_tensor_isPullback
    {P Q S T : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (g : S ⟶ T) [Mono f] [Mono g]
    (hQ : ∀ n, Module.Flat R (Q.X n))
    (hS : ∀ n, Module.Flat R (S.X n))
    (hT : ∀ n, Module.Flat R (T.X n))
    (hC : ∀ n, Module.Flat R ((cokernel f).X n)) :
    IsPullback (f ⊗ₘ 𝟙 S) (𝟙 P ⊗ₘ g) (𝟙 Q ⊗ₘ g) (f ⊗ₘ 𝟙 T) := by
  apply cochain_isPullback_of_f _ _ _ _
    (by simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id])
  intro n
  show IsPullback
    (GradedObject.mapMap (fun ij : ℤ × ℤ => (f.f ij.1 ▷ S.X ij.2) ≫ (Q.X ij.1 ◁ 𝟙 (S.X ij.2)))
      (fun ij => ij.1 + ij.2) n)
    (GradedObject.mapMap (fun ij : ℤ × ℤ => (𝟙 (P.X ij.1) ▷ S.X ij.2) ≫ (P.X ij.1 ◁ g.f ij.2))
      (fun ij => ij.1 + ij.2) n)
    (GradedObject.mapMap (fun ij : ℤ × ℤ => (𝟙 (Q.X ij.1) ▷ S.X ij.2) ≫ (Q.X ij.1 ◁ g.f ij.2))
      (fun ij => ij.1 + ij.2) n)
    (GradedObject.mapMap (fun ij : ℤ × ℤ => (f.f ij.1 ▷ T.X ij.2) ≫ (Q.X ij.1 ◁ 𝟙 (T.X ij.2)))
      (fun ij => ij.1 + ij.2) n)
  simp only [← MonoidalCategory.tensorHom_def]
  apply graded_mapMap_isPullback
  intro ij
  have := hQ ij.1
  have := hS ij.2
  have := hT ij.2
  have := hC ij.1
  exact moduleCat_tensor_isPullback (f.f ij.1) ((cokernel.π f).f ij.1) (g.f ij.2)
    (exact_cokernel_f f ij.1).1

/-- Nested tensor images intersect in the image of the two smaller filtration steps. -/
private lemma tensorStepImage_inf
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFK : ∀ i n, Module.Flat R ((K.filtration.obj (op i)).X n))
    (hgrK : ∀ i n, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n))
    (i j k l : ℤ) (hki : k ≤ i) (hlj : l ≤ j) :
    imageSubobject (K.filtration.ι.app (op k) ⊗ₘ L.filtration.ι.app (op j)) ⊓
      imageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op l)) =
      imageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j)) := by
  let f := K.filtration.diagram.map (homOfLE hki).op
  let g := L.filtration.diagram.map (homOfLE hlj).op
  let m := K.filtration.ι.app (op k) ⊗ₘ L.filtration.ι.app (op l)
  have : Mono f := mono_filtration_diagram_map K.filtration _
  have : Mono g := mono_filtration_diagram_map L.filtration _
  have : Mono m := cochain_tensorHom_mono _ _ hK (hFL l)
  have : Mono (𝟙 (K.filtration.obj (op k)) ⊗ₘ g) :=
    cochain_tensorHom_mono _ _ (hFK k) (hFL j)
  have : Mono (f ⊗ₘ 𝟙 (L.filtration.obj (op l))) :=
    cochain_tensorHom_mono _ _ (hFK k) (hFL l)
  have h := cochain_tensor_isPullback f g (hFK k) (hFL j) (hFL l)
    (fun n => flat_cokernel_filtration_map K hFK hgrK hki n)
  have := h.mono_fst_of_mono
  have heq := congrArg (Subobject.map m).obj (mk_inf_eq_of_isPullback h)
  rw [Subobject.inf_map] at heq
  simp only [Subobject.map_mk, f, g, m, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id, Filtration.diagram_map_comp_ι_app] at heq
  have (a b : ℤ) : Mono (K.filtration.ι.app (op a) ⊗ₘ L.filtration.ι.app (op b)) :=
    cochain_tensorHom_mono _ _ hK (hFL b)
  simpa only [imageSubobject_mono] using heq

/-- Tensor images decrease in each filtration index. -/
private lemma tensorStepImage_antitone {i j k l : ℤ} (hki : k ≤ i) (hlj : l ≤ j) :
    imageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j)) ≤
      imageSubobject (K.filtration.ι.app (op k) ⊗ₘ L.filtration.ι.app (op l)) := by
  have heq :
      (K.filtration.diagram.map (homOfLE hki).op ⊗ₘ
        L.filtration.diagram.map (homOfLE hlj).op) ≫
        (K.filtration.ι.app (op k) ⊗ₘ L.filtration.ι.app (op l)) =
      K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j) := by
    simp only [tensorHom_comp_tensorHom, Filtration.diagram_map_comp_ι_app]
  rw [← heq]
  exact imageSubobject_comp_le _ _

/-- A finite tensor interval lies in the rectangle bounded by its two endpoints. -/
private lemma tensorFiltrationInterval_le_rectangle (p s t : ℤ) :
    tensorFiltrationInterval K L p s t ≤
      imageSubobject (K.filtration.ι.app (op s) ⊗ₘ L.filtration.ι.app (op (p - t))) := by
  apply Finset.sup_le
  intro i hi
  obtain ⟨hsi, hit⟩ := Finset.mem_Icc.mp hi
  exact tensorStepImage_antitone K L hsi (by omega)

/-- The intersection of a nonempty tensor interval with its next summand. -/
private lemma tensorFiltrationInterval_inf_next
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFK : ∀ i n, Module.Flat R ((K.filtration.obj (op i)).X n))
    (hgrK : ∀ i n, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n))
    (p s t : ℤ) (hst : s ≤ t) :
    tensorFiltrationInterval K L p s t ⊓
      imageSubobject (K.filtration.ι.app (op (t + 1)) ⊗ₘ
        L.filtration.ι.app (op (p - t - 1))) =
      imageSubobject (K.filtration.ι.app (op (t + 1)) ⊗ₘ
        L.filtration.ι.app (op (p - t))) := by
  apply le_antisymm
  · calc
      _ ≤ imageSubobject (K.filtration.ι.app (op s) ⊗ₘ
          L.filtration.ι.app (op (p - t))) ⊓
          imageSubobject (K.filtration.ι.app (op (t + 1)) ⊗ₘ
          L.filtration.ι.app (op (p - t - 1))) :=
        inf_le_inf_right _ (tensorFiltrationInterval_le_rectangle K L p s t)
      _ = _ := tensorStepImage_inf K L hK hFK hgrK hFL _ _ _ _ (by omega) (by omega)
  · apply le_inf
    · exact (tensorStepImage_antitone K L (show t ≤ t + 1 by omega) le_rfl).trans
        (Finset.le_sup (f := fun i => imageSubobject
          (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i)) ))
          (Finset.mem_Icc.mpr ⟨hst, le_rfl⟩))
    · exact tensorStepImage_antitone K L le_rfl (by omega)

/-- Finite intervals of tensor steps are acyclic above the sum of the two bounds. -/
private lemma tensorFiltrationInterval_acyclic_of_add_lt
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFK : ∀ i n, Module.Flat R ((K.filtration.obj (op i)).X n))
    (hgrK : ∀ i n, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n))
    (hkK : ∀ i : ℤ, (K.filtration.obj (op i)).KFlat)
    (hkL : ∀ j : ℤ, (L.filtration.obj (op j)).KFlat)
    (b c : ℤ)
    (haK : ∀ i : ℤ, b < i → (K.filtration.obj (op i)).Acyclic)
    (haL : ∀ j : ℤ, c < j → (L.filtration.obj (op j)).Acyclic)
    (p s t : ℤ) (hp : b + c < p) (hst : s ≤ t) :
    (tensorFiltrationInterval K L p s t : CochainComplex (ModuleCat R) ℤ).Acyclic := by
  induction t, hst using Int.leInduction with
  | base =>
      rw [tensorFiltrationInterval_self]
      exact tensor_steps_image_acyclic_of_add_lt K L hK hFL hkK hkL b c haK haL
        s (p - s) (by omega)
  | succ t hst ih =>
      rw [tensorFiltrationInterval_succ K L p s t (by omega)]
      apply acyclic_sup_of_acyclic _ _ ih
      · exact tensor_steps_image_acyclic_of_add_lt K L hK hFL hkK hkL b c haK haL
          (t + 1) (p - (t + 1)) (by omega)
      · rw [show p - (t + 1) = p - t - 1 by omega,
          tensorFiltrationInterval_inf_next K L hK hFK hgrK hFL p s t hst]
        exact tensor_steps_image_acyclic_of_add_lt K L hK hFL hkK hkL b c haK haL
          (t + 1) (p - t) (by omega)

/-- The convolution filtration is acyclic above the sum of the two acyclicity bounds. -/
private lemma tensorConvolution_acyclic_of_add_lt
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFK : ∀ i n, Module.Flat R ((K.filtration.obj (op i)).X n))
    (hgrK : ∀ i n, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n))
    (hkK : ∀ i : ℤ, (K.filtration.obj (op i)).KFlat)
    (hkL : ∀ j : ℤ, (L.filtration.obj (op j)).KFlat)
    (b c : ℤ)
    (haK : ∀ i : ℤ, b < i → (K.filtration.obj (op i)).Acyclic)
    (haL : ∀ j : ℤ, c < j → (L.filtration.obj (op j)).Acyclic)
    (p : ℤ) (hp : b + c < p) :
    ((tensorConvolution K L).filtration.obj (op p)).Acyclic :=
  tensorConvolution_acyclic_of_intervals K L p
    (fun s t hst => tensorFiltrationInterval_acyclic_of_add_lt K L
      hK hFK hgrK hFL hkK hkL b c haK haL p s t hp hst)

section
variable {C : Type*} [Category C] [Abelian C]
set_option backward.isDefEq.respectTransparency false in
private lemma quasiIso_biprod_map {A B A' B' : CochainComplex C ℤ}
    (f : A ⟶ A') (g : B ⟶ B') [QuasiIso f] [QuasiIso g] :
    QuasiIso (biprod.map f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n
  have hf : IsIso (H.map f) := (quasiIsoAt_iff_isIso_homologyMap f n).mp inferInstance
  have hg : IsIso (H.map g) := (quasiIsoAt_iff_isIso_homologyMap g n).mp inferInstance
  have : H.Additive := by dsimp [H]; infer_instance
  have := preservesBinaryBiproducts_of_preservesBiproducts H
  have : IsIso (biprod.map (H.map f) (H.map g)) :=
    inferInstanceAs (IsIso (biprod.mapIso (asIso (H.map f)) (asIso (H.map g))).hom)
  show IsIso (H.map (biprod.map f g))
  have he : H.map (biprod.map f g) =
      (H.mapBiprod A B).hom ≫ biprod.map (H.map f) (H.map g) ≫
        (H.mapBiprod A' B').inv := by
    apply (cancel_epi (H.mapBiprod A B).inv).mp
    apply (cancel_mono (H.mapBiprod A' B').hom).mp
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;>
      simp only [Functor.mapBiprod_hom, Functor.mapBiprod_inv, Category.assoc,
        biprod.lift_fst, biprod.lift_snd, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        ← H.map_comp, biprod.inl_fst_assoc, biprod.inr_snd_assoc, biprod.inr_fst_assoc,
        biprod.inl_snd_assoc, biprod.map_fst, biprod.map_snd, zero_comp, H.map_zero]
  rw [he]
  infer_instance

private lemma quasiIso_sup_of_quasiIso_inf {X : CochainComplex C ℤ}
    (P Q : Subobject X)
    [QuasiIso (Subobject.ofLE (P ⊓ Q) Q inf_le_right)] :
    QuasiIso (Subobject.ofLE P (P ⊔ Q) le_sup_left) := by
  let i := Subobject.ofLE (P ⊓ Q) P inf_le_left
  let j := Subobject.ofLE (P ⊓ Q) Q inf_le_right
  let S := ShortComplex.mk (biprod.lift i (-𝟙 _)) (biprod.desc (𝟙 _) i) (by simp)
  let sp : S.Splitting :=
    { r := -biprod.snd
      s := biprod.inl
      f_r := by simp [S]
      s_g := by simp [S]
      id := by ext <;> simp [S] }
  let U := ShortComplex.mk (biprod.lift i (-j))
    (biprod.desc (Subobject.ofLE P (P ⊔ Q) le_sup_left)
      (Subobject.ofLE Q (P ⊔ Q) le_sup_right)) (by ext ; simp [i, j])
  let φ : S ⟶ U :=
    { τ₁ := 𝟙 _
      τ₂ := biprod.map (𝟙 _) j
      τ₃ := Subobject.ofLE P (P ⊔ Q) le_sup_left
      comm₁₂ := by
        dsimp only [S, U]
        apply biprod.hom_ext <;> simp
      comm₂₃ := by
        dsimp only [S, U]
        apply biprod.hom_ext' <;> simp [i, j] }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ sp.shortExact
    (shortExact_inf_biprod_sup P Q) inferInstance (quasiIso_biprod_map _ _)
end
section
variable {C : Type*} [Category C] [Abelian C]
private lemma isIso_factorThruImageSubobject {A X : C} (f : A ⟶ X) [Mono f] :
    IsIso (factorThruImageSubobject f) := by
  have : Mono (factorThruImageSubobject f) := mono_of_mono_fac (imageSubobject_arrow_comp f)
  exact isIso_of_mono_of_epi _

private lemma quasiIso_imageSubobject_arrow {A X : CochainComplex C ℤ}
    (f : A ⟶ X) [Mono f] [QuasiIso f] : QuasiIso (imageSubobject f).arrow := by
  have := isIso_factorThruImageSubobject f
  have : QuasiIso (factorThruImageSubobject f ≫ (imageSubobject f).arrow) := by
    rw [imageSubobject_arrow_comp]; infer_instance
  exact quasiIso_of_comp_left (factorThruImageSubobject f) _

private lemma quasiIso_ofLE_imageSubobject {A B X : CochainComplex C ℤ}
    (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g]
    (t : A ⟶ B) [QuasiIso t] (w : t ≫ g = f)
    (h : imageSubobject f ≤ imageSubobject g) :
    QuasiIso (Subobject.ofLE (imageSubobject f) (imageSubobject g) h) := by
  have := isIso_factorThruImageSubobject f
  have := isIso_factorThruImageSubobject g
  have he : factorThruImageSubobject f ≫ Subobject.ofLE _ _ h =
      t ≫ factorThruImageSubobject g := by
    apply (cancel_mono (imageSubobject g).arrow).mp
    simp [w]
  have : QuasiIso (factorThruImageSubobject f ≫ Subobject.ofLE _ _ h) := by
    rw [he]; infer_instance
  exact quasiIso_of_comp_left (factorThruImageSubobject f) _
end

private lemma tensorFiltrationInterval_pred (p s t : ℤ) (hst : s - 1 ≤ t) :
    tensorFiltrationInterval K L p (s - 1) t =
      tensorFiltrationInterval K L p s t ⊔
      imageSubobject (K.filtration.ι.app (op (s - 1)) ⊗ₘ
        L.filtration.ι.app (op (p - s + 1))) := by
  unfold tensorFiltrationInterval
  rw [show Finset.Icc (s - 1) t = insert (s - 1) (Finset.Icc s t) by
    ext i; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
    Finset.sup_insert, sup_comm]
  apply congrArg (fun Q : Subobject (K.X ⊗ L.X) =>
    tensorFiltrationInterval K L p s t ⊔ Q)
  exact congrArg (fun j : ℤ => imageSubobject
    (K.filtration.ι.app (op (s - 1)) ⊗ₘ L.filtration.ι.app (op j))) (by omega)

private lemma tensorFiltrationInterval_inf_prev
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFK : ∀ i n, Module.Flat R ((K.filtration.obj (op i)).X n))
    (hgrK : ∀ i n, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n))
    (p s t : ℤ) (hst : s ≤ t) :
    tensorFiltrationInterval K L p s t ⊓
      imageSubobject (K.filtration.ι.app (op (s - 1)) ⊗ₘ
        L.filtration.ι.app (op (p - s + 1))) =
      imageSubobject (K.filtration.ι.app (op s) ⊗ₘ
        L.filtration.ι.app (op (p - s + 1))) := by
  apply le_antisymm
  · calc
      _ ≤ imageSubobject (K.filtration.ι.app (op s) ⊗ₘ
          L.filtration.ι.app (op (p - t))) ⊓
          imageSubobject (K.filtration.ι.app (op (s - 1)) ⊗ₘ
          L.filtration.ι.app (op (p - s + 1))) :=
        inf_le_inf_right _ (tensorFiltrationInterval_le_rectangle K L p s t)
      _ = _ := by
        rw [inf_comm]
        exact tensorStepImage_inf K L hK hFK hgrK hFL _ _ _ _ (by omega) (by omega)
  · apply le_inf
    · exact (tensorStepImage_antitone K L le_rfl (show p - s ≤ p - s + 1 by omega)).trans
        (Finset.le_sup (f := fun i => imageSubobject
          (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i))))
          (Finset.mem_Icc.mpr ⟨le_rfl, hst⟩))
    · exact tensorStepImage_antitone K L (by omega) le_rfl

private lemma tensorStepImage_quasiIso_left
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n))
    (i k j : ℤ) (hki : k ≤ i)
    (hkL : (L.filtration.obj (op j)).KFlat)
    [QuasiIso (K.filtration.diagram.map (homOfLE hki).op)] :
    QuasiIso (Subobject.ofLE
      (imageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j)))
      (imageSubobject (K.filtration.ι.app (op k) ⊗ₘ L.filtration.ι.app (op j)))
      (tensorStepImage_antitone K L hki le_rfl)) := by
  have := cochain_tensorHom_mono (K.filtration.ι.app (op i))
    (L.filtration.ι.app (op j)) hK (hFL j)
  have := cochain_tensorHom_mono (K.filtration.ι.app (op k))
    (L.filtration.ι.app (op j)) hK (hFL j)
  have := quasiIso_tensor_id_of_kFlat (K.filtration.diagram.map (homOfLE hki).op)
    (L.filtration.obj (op j)) hkL
  apply quasiIso_ofLE_imageSubobject _ _
    (K.filtration.diagram.map (homOfLE hki).op ⊗ₘ 𝟙 _)
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Filtration.diagram_map_comp_ι_app]

private lemma tensorStepImage_quasiIso_right
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n))
    (i j l : ℤ) (hlj : l ≤ j)
    (hkK : (K.filtration.obj (op i)).KFlat)
    [QuasiIso (L.filtration.diagram.map (homOfLE hlj).op)] :
    QuasiIso (Subobject.ofLE
      (imageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j)))
      (imageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op l)))
      (tensorStepImage_antitone K L le_rfl hlj)) := by
  have := cochain_tensorHom_mono (K.filtration.ι.app (op i))
    (L.filtration.ι.app (op j)) hK (hFL j)
  have := cochain_tensorHom_mono (K.filtration.ι.app (op i))
    (L.filtration.ι.app (op l)) hK (hFL l)
  have := quasiIso_id_tensor_of_kFlat (K.filtration.obj (op i)) hkK
    (L.filtration.diagram.map (homOfLE hlj).op)
  apply quasiIso_ofLE_imageSubobject _ _
    (𝟙 _ ⊗ₘ L.filtration.diagram.map (homOfLE hlj).op)
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Filtration.diagram_map_comp_ι_app]

private lemma quasiIso_sup_arrow {C : Type*} [Category C] [Abelian C]
    {X : CochainComplex C ℤ} (P Q : Subobject X)
    [QuasiIso P.arrow] [QuasiIso (Subobject.ofLE (P ⊓ Q) Q inf_le_right)] :
    QuasiIso (P ⊔ Q).arrow := by
  have := quasiIso_sup_of_quasiIso_inf P Q
  have : QuasiIso (Subobject.ofLE P (P ⊔ Q) le_sup_left ≫ (P ⊔ Q).arrow) := by
    rw [Subobject.ofLE_arrow]; infer_instance
  exact quasiIso_of_comp_left (Subobject.ofLE P (P ⊔ Q) le_sup_left) _

private lemma quasiIso_ofLE_of_eq {C : Type*} [Category C] [Abelian C]
    {X : CochainComplex C ℤ} {P P' Q Q' : Subobject X}
    (h : P ≤ Q) (h' : P' ≤ Q') (eP : P = P') (eQ : Q = Q')
    (hq : QuasiIso (Subobject.ofLE P' Q' h')) : QuasiIso (Subobject.ofLE P Q h) := by
  subst P'; subst Q'; exact hq

private lemma tensorFiltrationInterval_quasiIso_of_lt
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFK : ∀ i n, Module.Flat R ((K.filtration.obj (op i)).X n))
    (hgrK : ∀ i n, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n))
    (hkK : K.X.KFlat) (hkFK : ∀ i, (K.filtration.obj (op i)).KFlat)
    (hkFL : ∀ j, (L.filtration.obj (op j)).KFlat)
    (a c : ℤ)
    (hqK : ∀ i, i < a → QuasiIso (K.filtration.ι.app (op i)))
    (hqL : ∀ j, j < c → QuasiIso (L.filtration.ι.app (op j)))
    (p s t : ℤ) (hp : p < a + c - 1) (hs : s ≤ a - 1) (ht : a - 1 ≤ t) :
    QuasiIso (tensorFiltrationInterval K L p s t).arrow := by
  have hright : QuasiIso (tensorFiltrationInterval K L p (a - 1) t).arrow := by
    induction t, ht using Int.leInduction with
    | base =>
        rw [tensorFiltrationInterval_self]
        have := cochain_tensorHom_mono (K.filtration.ι.app (op (a - 1)))
          (L.filtration.ι.app (op (p - (a - 1)))) hK (hFL _)
        have := tensor_steps_quasiIso_of_lt K L hkK hkFL a c hqK hqL
          (a - 1) (p - (a - 1)) (by omega) (by omega)
        exact quasiIso_imageSubobject_arrow _
    | succ t ht ih =>
        rw [tensorFiltrationInterval_succ K L p (a - 1) t (by omega),
          show p - (t + 1) = p - t - 1 by omega]
        have := hqL (p - t) (by omega)
        have := hqL (p - t - 1) (by omega)
        have := quasiIso_filtration_map_of_quasiIso_ι L.filtration
          (show p - t - 1 ≤ p - t by omega)
        have : QuasiIso (Subobject.ofLE
            (tensorFiltrationInterval K L p (a - 1) t ⊓
              imageSubobject (K.filtration.ι.app (op (t + 1)) ⊗ₘ
                L.filtration.ι.app (op (p - t - 1))))
            (imageSubobject (K.filtration.ι.app (op (t + 1)) ⊗ₘ
                L.filtration.ι.app (op (p - t - 1)))) inf_le_right) :=
          quasiIso_ofLE_of_eq _ _
            (tensorFiltrationInterval_inf_next K L hK hFK hgrK hFL p (a - 1) t ht) rfl
            (tensorStepImage_quasiIso_right K L hK hFL _ _ _ (sub_le_self _ zero_le_one) (hkFK _))
        exact quasiIso_sup_arrow _ _
  suffices ∀ m : ℕ, QuasiIso (tensorFiltrationInterval K L p (a - 1 - m) t).arrow by
    exact Eq.mp (congrArg (fun z : ℤ =>
      QuasiIso (tensorFiltrationInterval K L p z t).arrow)
      (show a - 1 - ((a - 1 - s).toNat : ℤ) = s by omega))
      (this (a - 1 - s).toNat)
  intro m
  induction m with
  | zero =>
      exact Eq.mp (congrArg (fun z : ℤ =>
        QuasiIso (tensorFiltrationInterval K L p z t).arrow)
        (show a - 1 = a - 1 - ((0 : ℕ) : ℤ) by omega)) hright
  | succ m ih =>
      rw [show a - 1 - ((m + 1 : ℕ) : ℤ) = (a - 1 - m) - 1 by omega,
        tensorFiltrationInterval_pred K L p (a - 1 - m) t (by omega)]
      have := hqK (a - 1 - m) (by omega)
      have := hqK (a - 1 - m - 1) (by omega)
      have := quasiIso_filtration_map_of_quasiIso_ι K.filtration
        (show a - 1 - m - 1 ≤ a - 1 - m by omega)
      have : QuasiIso (Subobject.ofLE
          (tensorFiltrationInterval K L p (a - 1 - m) t ⊓
            imageSubobject (K.filtration.ι.app (op (a - 1 - m - 1)) ⊗ₘ
              L.filtration.ι.app (op (p - (a - 1 - m) + 1))))
          (imageSubobject (K.filtration.ι.app (op (a - 1 - m - 1)) ⊗ₘ
            L.filtration.ι.app (op (p - (a - 1 - m) + 1)))) inf_le_right) :=
        quasiIso_ofLE_of_eq _ _
          (tensorFiltrationInterval_inf_prev K L hK hFK hgrK hFL p (a - 1 - m) t (by omega)) rfl
          (tensorStepImage_quasiIso_left K L hK hFL _ _ _ (sub_le_self _ zero_le_one) (hkFL _))
      exact quasiIso_sup_arrow _ _

set_option backward.isDefEq.respectTransparency false in
private lemma quasiIso_iSup_of_filtered
    (X : CochainComplex (ModuleCat.{u} R) ℤ)
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (P : J ⥤ Subobject X)
    (hP : ∀ j, QuasiIso (P.obj j).arrow) :
    QuasiIso (⨆ j, P.obj j : Subobject X).arrow := by
  let Q : Subobject X := ⨆ j, P.obj j
  obtain ⟨hc⟩ := nonempty_isColimit_subobjectOverCocone P Q (le_iSup _) rfl
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) n
  have := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := ModuleCat R) (J := J) (ComplexShape.up ℤ) n
  have hcH := isColimitOfPreserves H hc
  have hi (j : J) : IsIso (H.map (P.obj j).arrow) := by
    have := hP j
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance
  have hfac (j : J) : H.map (Subobject.ofLE (P.obj j) Q (le_iSup _ j)) ≫
      H.map Q.arrow = H.map (P.obj j).arrow := by
    rw [← H.map_comp, Subobject.ofLE_arrow]
  show IsIso (H.map Q.arrow)
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep _ hcH x
    change H.map (Subobject.ofLE (P.obj j) Q (le_iSup _ j)) y = x at hy
    have hy0 : H.map (P.obj j).arrow y = 0 := by
      rw [← hfac]
      show H.map Q.arrow (H.map (Subobject.ofLE (P.obj j) Q (le_iSup _ j)) y) = 0
      rwa [hy]
    have : y = 0 := (ModuleCat.mono_iff_injective _).mp inferInstance (hy0.trans (map_zero _).symm)
    simpa [this] using hy.symm
  · intro x
    let j : J := Classical.choice (IsFiltered.nonempty (C := J))
    obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (H.map (P.obj j).arrow)) x
    refine ⟨H.map (Subobject.ofLE (P.obj j) Q (le_iSup _ j)) y, ?_⟩
    show (H.map (Subobject.ofLE (P.obj j) Q (le_iSup _ j)) ≫ H.map Q.arrow) y = x
    rwa [hfac]

set_option backward.isDefEq.respectTransparency false in
private lemma tensorConvolution_quasiIso_of_lt
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFK : ∀ i n, Module.Flat R ((K.filtration.obj (op i)).X n))
    (hgrK : ∀ i n, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n))
    (hkK : K.X.KFlat) (hkFK : ∀ i, (K.filtration.obj (op i)).KFlat)
    (hkFL : ∀ j, (L.filtration.obj (op j)).KFlat)
    (a c : ℤ)
    (hqK : ∀ i, i < a → QuasiIso (K.filtration.ι.app (op i)))
    (hqL : ∀ j, j < c → QuasiIso (L.filtration.ι.app (op j)))
    (p : ℤ) (hp : p < a + c - 1) :
    QuasiIso ((tensorConvolution K L).filtration.ι.app (op p)) := by
  let P : ULift.{u} ℕ ⥤ Subobject (K.X ⊗ L.X) :=
    { obj m := tensorFiltrationInterval K L p
        (min (a - 1) (-m.down)) (max (a - 1) m.down)
      map {m n} f := homOfLE (tensorFiltrationInterval_mono K L p
        (min_le_min_left _ (by have := leOfHom f; change m.down ≤ n.down at this; omega))
        (max_le_max_left _ (by have := leOfHom f; change m.down ≤ n.down at this; omega))) }
  have hP : (⨆ m, P.obj m) = imageSubobject (tensorFiltrationSumι K L p) := by
    rw [tensorFiltrationSumι_image_eq_iSup]
    simp only [P, iSup_ulift]
    apply le_antisymm
    · refine iSup_le fun m ↦ le_iSup_of_le (max m (a - 1).natAbs) ?_
      apply tensorFiltrationInterval_mono K L p <;>
        simp only [min_def, max_def] <;> split_ifs <;> omega
    · exact iSup_le fun m ↦ le_iSup_of_le m
        (tensorFiltrationInterval_mono K L p (min_le_right _ _) (le_max_right _ _))
  have hq := quasiIso_iSup_of_filtered _ P (fun m =>
    tensorFiltrationInterval_quasiIso_of_lt K L hK hFK hgrK hFL hkK hkFK hkFL
      a c hqK hqL p _ _ hp (min_le_left _ _) (le_max_left _ _))
  rw [hP] at hq
  exact hq

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring a cochain complex of modules on the right preserves colimits of shape `J`. -/
private lemma preservesColimitsOfShape_cochain_tensorRight
    {J : Type*} [Category J] [HasColimitsOfShape J (ModuleCat.{u} R)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesColimitsOfShape J (tensorRight P) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  let D : CochainComplex (ModuleCat.{u} R) ℤ ⥤
      (Discrete {ij : ℤ × ℤ // ij.1 + ij.2 = n} ⥤ ModuleCat.{u} R) :=
    { obj X := Discrete.functor
        (GradedObject.mapObjFun
          (fun ij : ℤ × ℤ => (X.X ij.1 ⊗ P.X ij.2 : ModuleCat.{u} R))
          (fun ij => ij.1 + ij.2) n)
      map f := Discrete.natTrans (fun ij => f.f ij.as.1.1 ▷ P.X ij.as.1.2)
      map_id X := by ext ij; simp
      map_comp f g := by ext ij; simp }
  have hD : PreservesColimitsOfShape J D := by
    apply preservesColimitsOfShape_of_evaluation
    intro ij
    have : PreservesColimitsOfShape J (tensorRight (P.X ij.as.1.2)) := ⟨inferInstance⟩
    have : PreservesColimitsOfShape J
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) ij.as.1.1) :=
      ⟨inferInstance⟩
    exact inferInstanceAs (PreservesColimitsOfShape J
      (HomologicalComplex.eval _ _ ij.as.1.1 ⋙ tensorRight (P.X ij.as.1.2)))
  let e : tensorRight P ⋙ HomologicalComplex.eval _ _ n ≅ D ⋙ colim :=
    NatIso.ofComponents (fun X => Iso.refl _) (by
      intro X Y f
      dsimp
      simp only [Category.id_comp, Category.comp_id]
      show GradedObject.mapMap
        (fun ij : ℤ × ℤ => (f.f ij.1 ▷ P.X ij.2) ≫ (Y.X ij.1 ◁ 𝟙 (P.X ij.2)))
        (fun ij => ij.1 + ij.2) n = _
      simp only [whiskerLeft_id, Category.comp_id]
      show GradedObject.mapMap (fun ij : ℤ × ℤ => f.f ij.1 ▷ P.X ij.2)
        (fun ij => ij.1 + ij.2) n =
          Limits.Sigma.map
            (g := GradedObject.mapObjFun
              (fun ij : ℤ × ℤ => (X.X ij.1 ⊗ P.X ij.2 : ModuleCat.{u} R))
              (fun ij => ij.1 + ij.2) n)
            (f := GradedObject.mapObjFun
              (fun ij : ℤ × ℤ => (Y.X ij.1 ⊗ P.X ij.2 : ModuleCat.{u} R))
              (fun ij => ij.1 + ij.2) n)
            (fun ij => f.f ij.1.1 ▷ P.X ij.1.2)
      exact graded_mapMap_eq_sigma_map _ _ _)
  exact preservesColimitsOfShape_of_natIso e.symm

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring a cochain complex of modules on the left preserves colimits of shape `J`. -/
private lemma preservesColimitsOfShape_cochain_tensorLeft
    {J : Type*} [Category J] [HasColimitsOfShape J (ModuleCat.{u} R)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    PreservesColimitsOfShape J (tensorLeft P) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  let D : CochainComplex (ModuleCat.{u} R) ℤ ⥤
      (Discrete {ij : ℤ × ℤ // ij.1 + ij.2 = n} ⥤ ModuleCat.{u} R) :=
    { obj X := Discrete.functor
        (GradedObject.mapObjFun
          (fun ij : ℤ × ℤ => (P.X ij.1 ⊗ X.X ij.2 : ModuleCat.{u} R))
          (fun ij => ij.1 + ij.2) n)
      map f := Discrete.natTrans (fun ij => P.X ij.as.1.1 ◁ f.f ij.as.1.2)
      map_id X := by ext ij; simp
      map_comp f g := by ext ij; simp }
  have hD : PreservesColimitsOfShape J D := by
    apply preservesColimitsOfShape_of_evaluation
    intro ij
    have : PreservesColimitsOfShape J (tensorLeft (P.X ij.as.1.1)) := ⟨inferInstance⟩
    have : PreservesColimitsOfShape J
        (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) ij.as.1.2) :=
      ⟨inferInstance⟩
    exact inferInstanceAs (PreservesColimitsOfShape J
      (HomologicalComplex.eval _ _ ij.as.1.2 ⋙ tensorLeft (P.X ij.as.1.1)))
  let e : tensorLeft P ⋙ HomologicalComplex.eval _ _ n ≅ D ⋙ colim :=
    NatIso.ofComponents (fun X => Iso.refl _) (by
      intro X Y f
      dsimp
      simp only [Category.id_comp, Category.comp_id]
      show GradedObject.mapMap
        (fun ij : ℤ × ℤ => (𝟙 (P.X ij.1) ▷ X.X ij.2) ≫ (P.X ij.1 ◁ f.f ij.2))
        (fun ij => ij.1 + ij.2) n = _
      simp only [id_whiskerRight, Category.id_comp]
      show GradedObject.mapMap (fun ij : ℤ × ℤ => P.X ij.1 ◁ f.f ij.2)
        (fun ij => ij.1 + ij.2) n =
          Limits.Sigma.map
            (g := GradedObject.mapObjFun
              (fun ij : ℤ × ℤ => (P.X ij.1 ⊗ X.X ij.2 : ModuleCat.{u} R))
              (fun ij => ij.1 + ij.2) n)
            (f := GradedObject.mapObjFun
              (fun ij : ℤ × ℤ => (P.X ij.1 ⊗ Y.X ij.2 : ModuleCat.{u} R))
              (fun ij => ij.1 + ij.2) n)
            (fun ij => P.X ij.1.1 ◁ f.f ij.1.2)
      exact graded_mapMap_eq_sigma_map _ _ _)
  exact preservesColimitsOfShape_of_natIso e.symm

private lemma cochain_monoidalPreadditive :
    MonoidalPreadditive (CochainComplex (ModuleCat.{u} R) ℤ) := by
  have hl (P : CochainComplex (ModuleCat.{u} R) ℤ) :
      (tensorLeft P).PreservesZeroMorphisms := ⟨fun _ _ => cochain_tensor_zero (𝟙 P)⟩
  have hr (P : CochainComplex (ModuleCat.{u} R) ℤ) :
      (tensorRight P).PreservesZeroMorphisms := ⟨fun _ _ => cochain_zero_tensor (𝟙 P)⟩
  have hal (P : CochainComplex (ModuleCat.{u} R) ℤ) : (tensorLeft P).Additive := by
    have := preservesColimitsOfShape_cochain_tensorLeft (J := Discrete WalkingPair) P
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft P)
    exact Functor.additive_of_preservesBinaryBiproducts (tensorLeft P)
  have har (P : CochainComplex (ModuleCat.{u} R) ℤ) : (tensorRight P).Additive := by
    have := preservesColimitsOfShape_cochain_tensorRight (J := Discrete WalkingPair) P
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight P)
    exact Functor.additive_of_preservesBinaryBiproducts (tensorRight P)
  exact
    { whiskerLeft_zero := fun {P _ _} => (tensorLeft P).map_zero _ _
      zero_whiskerRight := fun {P _ _} => (tensorRight P).map_zero _ _
      whiskerLeft_add := fun {P _ _} f g => (tensorLeft P).map_add
      add_whiskerRight := fun {P _ _} f g => (tensorRight P).map_add }

section
variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : C}
private lemma exists_desc_sup (P Q : Subobject X) (f : (P : C) ⟶ Y) (g : (Q : C) ⟶ Y)
    (h : Subobject.ofLE (P ⊓ Q) P inf_le_left ≫ f =
      Subobject.ofLE (P ⊓ Q) Q inf_le_right ≫ g) :
    ∃ t : ((P ⊔ Q : Subobject X) : C) ⟶ Y,
      Subobject.ofLE P (P ⊔ Q) le_sup_left ≫ t = f ∧
      Subobject.ofLE Q (P ⊔ Q) le_sup_right ≫ t = g := by
  have hs := shortExact_inf_biprod_sup P Q
  have := hs.epi_g
  have hz : (biprod.lift (Subobject.ofLE (P ⊓ Q) P inf_le_left)
      (-Subobject.ofLE (P ⊓ Q) Q inf_le_right)) ≫ biprod.desc f g = 0 := by
    simp [h]
  refine ⟨hs.exact.desc (biprod.desc f g) hz, ?_, ?_⟩
  · have hh := congrArg (biprod.inl ≫ ·) (hs.exact.g_desc (biprod.desc f g) hz)
    simpa using hh
  · have hh := congrArg (biprod.inr ≫ ·) (hs.exact.g_desc (biprod.desc f g) hz)
    simpa using hh

private lemma sup_hom_ext (P Q : Subobject X) {f g : ((P ⊔ Q : Subobject X) : C) ⟶ Y}
    (hP : Subobject.ofLE P (P ⊔ Q) le_sup_left ≫ f =
      Subobject.ofLE P (P ⊔ Q) le_sup_left ≫ g)
    (hQ : Subobject.ofLE Q (P ⊔ Q) le_sup_right ≫ f =
      Subobject.ofLE Q (P ⊔ Q) le_sup_right ≫ g) : f = g := by
  have hs := shortExact_inf_biprod_sup P Q
  have := hs.epi_g
  apply (cancel_epi (biprod.desc
    (Subobject.ofLE P (P ⊔ Q) le_sup_left) (Subobject.ofLE Q (P ⊔ Q) le_sup_right))).mp
  apply biprod.hom_ext'
  · simpa using hP
  · simpa using hQ

private lemma finsetSup_hom_ext {I : Type*} (P : I → Subobject X)
    (s : Finset I) (Q : Subobject X) (hQ : s.sup P = Q)
    {f g : (Q : C) ⟶ Y}
    (h : ∀ i (hi : i ∈ s), Subobject.ofLE (P i) Q (hQ ▸ Finset.le_sup hi) ≫ f =
      Subobject.ofLE (P i) Q (hQ ▸ Finset.le_sup hi) ≫ g) : f = g := by
  classical
  induction s using Finset.induction_on generalizing Q with
  | empty =>
      subst Q
      exact (isZero_zero C).of_iso Subobject.botCoeIsoZero |>.eq_of_src f g
  | @insert i s hi ih =>
      rw [Finset.sup_insert] at hQ
      let e := Subobject.isoOfEq (P i ⊔ s.sup P) Q hQ
      apply (cancel_epi e.hom).mp
      apply sup_hom_ext (P i) (s.sup P)
      · simpa [e] using h i (Finset.mem_insert_self _ _)
      · apply ih (s.sup P) rfl
        intro j hj
        simpa [e] using h j (Finset.mem_insert_of_mem hj)
private lemma exists_desc_Icc
    (P B : ℤ → Subobject X) (hB : ∀ i, B i ≤ P i) (hB' : ∀ i, B i ≤ P (i + 1))
    (hcap : ∀ s t, s ≤ t → (Finset.Icc s t).sup P ⊓ P (t + 1) = B t)
    (f : ∀ i, (P i : C) ⟶ Y)
    (hf : ∀ i, Subobject.ofLE (B i) (P i) (hB i) ≫ f i =
      Subobject.ofLE (B i) (P (i + 1)) (hB' i) ≫ f (i + 1))
    (s t : ℤ) (hst : s ≤ t) :
    ∃ g : (((Finset.Icc s t).sup P : Subobject X) : C) ⟶ Y,
      ∀ i (hi : i ∈ Finset.Icc s t), Subobject.ofLE (P i) _ (Finset.le_sup hi) ≫ g = f i := by
  induction t, hst using Int.leInduction with
  | base =>
      have he : (Finset.Icc s s).sup P = P s := by simp
      refine ⟨(Subobject.isoOfEq _ _ he).hom ≫ f s, ?_⟩
      intro i hi
      have : i = s := by simpa using hi
      subst i
      simp
  | succ t hst ih =>
      obtain ⟨g, hg⟩ := ih
      let Q := (Finset.Icc s t).sup P
      have ht : P t ≤ Q := Finset.le_sup (Finset.mem_Icc.mpr ⟨hst, le_rfl⟩)
      have hcompat : Subobject.ofLE (Q ⊓ P (t + 1)) Q inf_le_left ≫ g =
          Subobject.ofLE (Q ⊓ P (t + 1)) (P (t + 1)) inf_le_right ≫ f (t + 1) := by
        let e := Subobject.isoOfEq (B t) (Q ⊓ P (t + 1)) (hcap s t hst).symm
        apply (cancel_epi e.hom).mp
        dsimp [e]
        simp only [Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE_assoc]
        calc
          _ = Subobject.ofLE (B t) (P t) (hB t) ≫
              (Subobject.ofLE (P t) Q ht ≫ g) := by simp
          _ = _ := by rw [hg t (Finset.mem_Icc.mpr ⟨hst, le_rfl⟩)]; exact hf t
      obtain ⟨u, hu, hu'⟩ := exists_desc_sup Q (P (t + 1)) g (f (t + 1)) hcompat
      let e := Subobject.isoOfEq ((Finset.Icc s (t + 1)).sup P) (Q ⊔ P (t + 1))
        (sup_Icc_succ P s t (by omega))
      refine ⟨e.hom ≫ u, ?_⟩
      intro i hi
      obtain ⟨hsi, hit⟩ := Finset.mem_Icc.mp hi
      by_cases he : i = t + 1
      · subst i
        simpa [e] using hu'
      · have hi' : i ∈ Finset.Icc s t := Finset.mem_Icc.mpr ⟨hsi, by omega⟩
        calc
          _ = Subobject.ofLE (P i) Q (Finset.le_sup hi') ≫
              (Subobject.ofLE Q (Q ⊔ P (t + 1)) le_sup_left ≫ u) := by simp [e]
          _ = f i := by rw [hu]; exact hg i hi'

end

set_option backward.isDefEq.respectTransparency false in
private lemma existsUnique_desc_iSup_of_interval_intersections
    {R : Type u} [CommRing R]
    {X Y : CochainComplex (ModuleCat.{u} R) ℤ}
    (P B : ℤ → Subobject X) (hB : ∀ i, B i ≤ P i) (hB' : ∀ i, B i ≤ P (i + 1))
    (hcap : ∀ s t, s ≤ t → (Finset.Icc s t).sup P ⊓ P (t + 1) = B t)
    (f : ∀ i, (P i : CochainComplex (ModuleCat R) ℤ) ⟶ Y)
    (hf : ∀ i, Subobject.ofLE (B i) (P i) (hB i) ≫ f i =
      Subobject.ofLE (B i) (P (i + 1)) (hB' i) ≫ f (i + 1)) :
    ∃! g : ((⨆ i, P i : Subobject X) : CochainComplex (ModuleCat R) ℤ) ⟶ Y,
      ∀ i, Subobject.ofLE (P i) _ (le_iSup _ i) ≫ g = f i := by
  classical
  let U : ULift.{u} ℕ ⥤ Subobject X :=
    { obj m := (Finset.Icc (-(m.down : ℤ)) m.down).sup P
      map {m n} f := homOfLE (Finset.sup_mono (fun i hi => by
        obtain ⟨hil, hir⟩ := Finset.mem_Icc.mp hi
        have hmn := leOfHom f
        change m.down ≤ n.down at hmn
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩)) }
  let Q : Subobject X := ⨆ i, P i
  have hle (m : ULift.{u} ℕ) : U.obj m ≤ Q := by
    dsimp only [U, Q]
    exact Finset.sup_le fun i _ => le_iSup P i
  have hQ : Q = ⨆ m, U.obj m := by
    apply le_antisymm
    · apply iSup_le
      intro i
      apply le_iSup_of_le (ULift.up i.natAbs)
      exact Finset.le_sup (Finset.mem_Icc.mpr ⟨by dsimp; omega, by dsimp; omega⟩)
    · exact iSup_le hle
  choose g hg using fun m : ULift.{u} ℕ =>
    exists_desc_Icc P B hB hB' hcap f hf (-m.down) m.down (by omega)
  obtain ⟨hc⟩ := nonempty_isColimit_subobjectOverCocone U Q hle hQ
  let d : Cocone ((U ⋙ Subobject.representative) ⋙ MonoOver.forget X ⋙ Over.forget X) :=
    { pt := Y
      ι :=
        { app m := g m
          naturality {m n} e := by
            show Subobject.ofLE (U.obj m) (U.obj n) _ ≫ g n = g m
            apply finsetSup_hom_ext P (Finset.Icc (-m.down) m.down) (U.obj m) rfl
            intro i hi
            have hin : i ∈ Finset.Icc (-(n.down : ℤ)) n.down := by
              have hmn := leOfHom e
              change m.down ≤ n.down at hmn
              obtain ⟨hil, hir⟩ := Finset.mem_Icc.mp hi
              exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            simpa only [Subobject.ofLE_comp_ofLE_assoc] using
              (hg n i hin).trans (hg m i hi).symm } }
  let u := hc.desc d
  have hu (m : ULift.{u} ℕ) : Subobject.ofLE (U.obj m) Q (hle m) ≫ u = g m := hc.fac d m
  have huf (i : ℤ) : Subobject.ofLE (P i) Q (le_iSup _ i) ≫ u = f i := by
    let m : ULift.{u} ℕ := ⟨i.natAbs⟩
    have hi : i ∈ Finset.Icc (-(m.down : ℤ)) m.down :=
      Finset.mem_Icc.mpr ⟨by dsimp [m]; omega, by dsimp [m]; omega⟩
    calc
      _ = Subobject.ofLE (P i) (U.obj m) (Finset.le_sup hi) ≫
          (Subobject.ofLE (U.obj m) Q (hle m) ≫ u) := by simp
      _ = _ := by rw [hu]; exact hg m i hi
  refine ⟨u, huf, ?_⟩
  intro v hv
  apply hc.hom_ext
  intro m
  show Subobject.ofLE (U.obj m) Q (hle m) ≫ v =
    Subobject.ofLE (U.obj m) Q (hle m) ≫ u
  apply finsetSup_hom_ext P (Finset.Icc (-m.down) m.down) (U.obj m) rfl
  intro i hi
  simpa only [Subobject.ofLE_comp_ofLE_assoc] using (hv i).trans (huf i).symm

private noncomputable abbrev tensorStepQuotient (i j : ℤ) :
    K.filtration.obj (op i) ⊗ L.filtration.obj (op j) ⟶
      (FilteredObject.gr i).obj K ⊗ (FilteredObject.gr j).obj L :=
  cokernel.π (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : i ⟶ i + 1).op) ⊗ₘ
    cokernel.π (L.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : j ⟶ j + 1).op)

set_option backward.isDefEq.respectTransparency false in
private lemma tensorStepQuotient_left (i j : ℤ) :
    (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : i ⟶ i + 1).op ▷
      L.filtration.obj (op j)) ≫ tensorStepQuotient K L i j = 0 := by
  show (_ ⊗ₘ 𝟙 _) ≫ (_ ⊗ₘ _) = 0
  rw [tensorHom_comp_tensorHom, cokernel.condition, cochain_zero_tensor]

set_option backward.isDefEq.respectTransparency false in
private lemma tensorStepQuotient_right (i j : ℤ) :
    (K.filtration.obj (op i) ◁
      L.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : j ⟶ j + 1).op) ≫
        tensorStepQuotient K L i j = 0 := by
  show (𝟙 _ ⊗ₘ _) ≫ (_ ⊗ₘ _) = 0
  rw [tensorHom_comp_tensorHom, cokernel.condition, cochain_tensor_zero]

set_option backward.isDefEq.respectTransparency false in
private lemma tensorStepQuotient_universal (i j : ℤ)
    {Y : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K.filtration.obj (op i) ⊗ L.filtration.obj (op j) ⟶ Y)
    (hfK : (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : i ⟶ i + 1).op ▷
      L.filtration.obj (op j)) ≫ f = 0)
    (hfL : (K.filtration.obj (op i) ◁
      L.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : j ⟶ j + 1).op) ≫ f = 0) :
    ∃! g, tensorStepQuotient K L i j ≫ g = f := by
  have := cochain_monoidalPreadditive (R := R)
  let fK := K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : i ⟶ i + 1).op
  let fL := L.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : j ⟶ j + 1).op
  let cK := CokernelCofork.ofπ (cokernel.π fK) (cokernel.condition fK)
  let cL := CokernelCofork.ofπ (cokernel.π fL) (cokernel.condition fL)
  have hcK : IsColimit cK := cokernelIsCokernel fK
  have hcL : IsColimit cL := cokernelIsCokernel fL
  have := preservesColimitsOfShape_cochain_tensorLeft (J := WalkingParallelPair) cK.pt
  have := preservesColimitsOfShape_cochain_tensorRight (J := WalkingParallelPair)
    (L.filtration.obj (op j))
  have := preservesColimitsOfShape_cochain_tensorRight (J := WalkingParallelPair)
    (L.filtration.obj (op (j + 1)))
  let h := CokernelCofork.isColimitTensor hcK hcL
  have hf : coprod.desc
      (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : i ⟶ i + 1).op ▷
        L.filtration.obj (op j))
      (K.filtration.obj (op i) ◁ L.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : j ⟶ j + 1).op) ≫ f = 0 := by
    apply coprod.hom_ext
    · simpa only [coprod.inl_desc_assoc, comp_zero] using hfK
    · simpa only [coprod.inr_desc_assoc, comp_zero] using hfL
  obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' h f hf
  have : Epi (tensorStepQuotient K L i j) := epi_of_isColimit_cofork h
  exact ⟨g, hg, fun g' hg' => (cancel_epi (tensorStepQuotient K L i j)).mp (hg'.trans hg.symm)⟩

private noncomputable abbrev tensorStepImage (i j : ℤ) : Subobject (K.X ⊗ L.X) :=
  imageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j))

private noncomputable def tensorStepImageQuotient
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n)) (i j : ℤ) :
    (tensorStepImage K L i j : CochainComplex (ModuleCat R) ℤ) ⟶
      (FilteredObject.gr i).obj K ⊗ (FilteredObject.gr j).obj L := by
  have := cochain_tensorHom_mono (K.filtration.ι.app (op i)) (L.filtration.ι.app (op j)) hK (hFL j)
  have := isIso_factorThruImageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j))
  exact inv (factorThruImageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j))) ≫
    tensorStepQuotient K L i j

private lemma factor_tensorStepImageQuotient
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n)) (i j : ℤ) :
    factorThruImageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j)) ≫
      tensorStepImageQuotient K L hK hFL i j = tensorStepQuotient K L i j := by
  unfold tensorStepImageQuotient
  simp

private lemma tensorStepImageQuotient_left
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n)) (i j : ℤ) :
    Subobject.ofLE (tensorStepImage K L (i + 1) j) (tensorStepImage K L i j)
      (tensorStepImage_antitone K L (by omega) le_rfl) ≫
      tensorStepImageQuotient K L hK hFL i j = 0 := by
  apply (cancel_epi (factorThruImageSubobject
    (K.filtration.ι.app (op (i + 1)) ⊗ₘ L.filtration.ι.app (op j)))).mp
  have he : factorThruImageSubobject
      (K.filtration.ι.app (op (i + 1)) ⊗ₘ L.filtration.ι.app (op j)) ≫
        Subobject.ofLE (tensorStepImage K L (i + 1) j) (tensorStepImage K L i j)
          (tensorStepImage_antitone K L (by omega) le_rfl) =
      (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : i ⟶ i + 1).op ▷
        L.filtration.obj (op j)) ≫ factorThruImageSubobject
          (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j)) := by
    apply (cancel_mono (tensorStepImage K L i j).arrow).mp
    simp only [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
    show _ = (_ ⊗ₘ 𝟙 _) ≫ (_ ⊗ₘ _)
    rw [tensorHom_comp_tensorHom, Filtration.diagram_map_comp_ι_app, Category.id_comp]
  rw [← Category.assoc, he, Category.assoc, factor_tensorStepImageQuotient,
    tensorStepQuotient_left, comp_zero]

private lemma tensorStepImageQuotient_right
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n)) (i j : ℤ) :
    Subobject.ofLE (tensorStepImage K L i (j + 1)) (tensorStepImage K L i j)
      (tensorStepImage_antitone K L le_rfl (by omega)) ≫
      tensorStepImageQuotient K L hK hFL i j = 0 := by
  apply (cancel_epi (factorThruImageSubobject
    (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (j + 1))))).mp
  have he : factorThruImageSubobject
      (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (j + 1))) ≫
        Subobject.ofLE (tensorStepImage K L i (j + 1)) (tensorStepImage K L i j)
          (tensorStepImage_antitone K L le_rfl (by omega)) =
      (K.filtration.obj (op i) ◁ L.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : j ⟶ j + 1).op) ≫ factorThruImageSubobject
          (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j)) := by
    apply (cancel_mono (tensorStepImage K L i j).arrow).mp
    simp only [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
    show _ = (𝟙 _ ⊗ₘ _) ≫ (_ ⊗ₘ _)
    rw [tensorHom_comp_tensorHom, Filtration.diagram_map_comp_ι_app, Category.id_comp]
  rw [← Category.assoc, he, Category.assoc, factor_tensorStepImageQuotient,
    tensorStepQuotient_right, comp_zero]
private lemma tensorStepImage_iSup (p : ℤ) :
    imageSubobject (tensorFiltrationSumι K L p) = ⨆ i, tensorStepImage K L i (p - i) :=
  (imageSubobject_sigma_desc_isLUB
    (fun i : ℤ => K.filtration.obj (op i) ⊗ L.filtration.obj (op (p - i)))
    (fun i => K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i)))).iSup_eq.symm

private lemma tensorStepImage_le_convolution (p i j : ℤ) (h : p ≤ i + j) :
    tensorStepImage K L i j ≤ imageSubobject (tensorFiltrationSumι K L p) := by
  rw [tensorStepImage_iSup]
  exact (tensorStepImage_antitone K L le_rfl (show p - i ≤ j by omega)).trans
    (le_iSup (fun k => tensorStepImage K L k (p - k)) i)

private lemma tensorConvolution_image_hom_ext (p : ℤ)
    {Y : CochainComplex (ModuleCat.{u} R) ℤ}
    {f g : (imageSubobject (tensorFiltrationSumι K L p) : CochainComplex (ModuleCat R) ℤ) ⟶ Y}
    (h : ∀ i, Subobject.ofLE (tensorStepImage K L i (p - i)) _
      (tensorStepImage_le_convolution K L p i (p - i) (by omega)) ≫ f =
      Subobject.ofLE (tensorStepImage K L i (p - i)) _
      (tensorStepImage_le_convolution K L p i (p - i) (by omega)) ≫ g) : f = g := by
  apply (cancel_epi (factorThruImageSubobject (tensorFiltrationSumι K L p))).mp
  apply Sigma.hom_ext
  intro i
  have he : Sigma.ι (fun i : ℤ => K.filtration.obj (op i) ⊗
      L.filtration.obj (op (p - i))) i ≫ factorThruImageSubobject (tensorFiltrationSumι K L p) =
      factorThruImageSubobject (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i))) ≫
        Subobject.ofLE (tensorStepImage K L i (p - i)) _
          (tensorStepImage_le_convolution K L p i (p - i) (by omega)) := by
    apply (cancel_mono (imageSubobject (tensorFiltrationSumι K L p)).arrow).mp
    simp [tensorFiltrationSumι]
  simp only [← Category.assoc]
  rw [he]
  simpa only [Category.assoc] using
    congrArg (factorThruImageSubobject
      (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i))) ≫ ·) (h i)

private lemma comp_ofLE_eq_zero_of_eq {C : Type*} [Category C] [Abelian C]
    {X Y : C} {P P' Q : Subobject X} (h : P ≤ Q) (h' : P' ≤ Q) (e : P = P')
    (f : (Q : C) ⟶ Y) (hf : Subobject.ofLE P' Q h' ≫ f = 0) :
    Subobject.ofLE P Q h ≫ f = 0 := by subst P'; exact hf

private lemma comp_cokernel_of_image_le {C : Type*} [Category C] [Abelian C]
    {X A : C} (S T : Subobject X) (hTS : T ≤ S) (f : A ⟶ (S : C))
    (hf : imageSubobject (f ≫ S.arrow) ≤ T) :
    f ≫ cokernel.π (Subobject.ofLE T S hTS) = 0 := by
  let t := factorThruImageSubobject (f ≫ S.arrow) ≫ Subobject.ofLE _ T hf
  have he : t ≫ Subobject.ofLE T S hTS = f := by
    apply (cancel_mono S.arrow).mp
    simp [t]
  rw [← he, Category.assoc, cokernel.condition, comp_zero]

private lemma tensorStepQuotient_epi (i j : ℤ) : Epi (tensorStepQuotient K L i j) := by
  constructor
  intro Y f g h
  obtain ⟨t, ht, hu⟩ := tensorStepQuotient_universal K L i j (tensorStepQuotient K L i j ≫ f)
    (by rw [← Category.assoc, tensorStepQuotient_left, zero_comp])
    (by rw [← Category.assoc, tensorStepQuotient_right, zero_comp])
  exact (hu f rfl).trans (hu g h.symm).symm

private lemma tensorStepImageQuotient_epi
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n)) (i j : ℤ) :
    Epi (tensorStepImageQuotient K L hK hFL i j) := by
  have := tensorStepQuotient_epi K L i j
  exact epi_of_epi_fac (factor_tensorStepImageQuotient K L hK hFL i j)

set_option maxHeartbeats 800000 in
-- Both universal-property constructions elaborate diagrams of tensor-image subobjects.
set_option backward.isDefEq.respectTransparency false in
private lemma tensorConvolution_gradedPieceIso
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFK : ∀ i n, Module.Flat R ((K.filtration.obj (op i)).X n))
    (hgrK : ∀ i n, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n)) (p : ℤ) :
    Nonempty (((FilteredObject.gr p).obj (tensorConvolution K L)) ≅
      ∐ fun i : ℤ => (FilteredObject.gr i).obj K ⊗
        (FilteredObject.gr (p - i)).obj L) := by
  let P (i : ℤ) := tensorStepImage K L i (p - i)
  let B (i : ℤ) := tensorStepImage K L (i + 1) (p - i)
  let G (i : ℤ) := (FilteredObject.gr i).obj K ⊗
    (FilteredObject.gr (p - i)).obj L
  have hB (i : ℤ) : B i ≤ P i := tensorStepImage_antitone K L (by omega) le_rfl
  have hB' (i : ℤ) : B i ≤ P (i + 1) := tensorStepImage_antitone K L le_rfl (by omega)
  have hcap (s t : ℤ) (hst : s ≤ t) : (Finset.Icc s t).sup P ⊓ P (t + 1) = B t := by
    show tensorFiltrationInterval K L p s t ⊓ tensorStepImage K L (t + 1) (p - (t + 1)) = _
    rw [congrArg (tensorStepImage K L (t + 1)) (show p - (t + 1) = p - t - 1 by omega)]
    exact tensorFiltrationInterval_inf_next K L hK hFK hgrK hFL p s t hst
  let q (i : ℤ) := tensorStepImageQuotient K L hK hFL i (p - i)
  have hq (i : ℤ) : Epi (q i) := tensorStepImageQuotient_epi K L hK hFL i (p - i)
  have hcompat (i : ℤ) : Subobject.ofLE (B i) (P i) (hB i) ≫ (q i ≫ Sigma.ι G i) =
      Subobject.ofLE (B i) (P (i + 1)) (hB' i) ≫ (q (i + 1) ≫ Sigma.ι G (i + 1)) := by
    have hl : Subobject.ofLE (B i) (P i) (hB i) ≫ q i = 0 :=
      tensorStepImageQuotient_left K L hK hFL i (p - i)
    have hr : Subobject.ofLE (B i) (P (i + 1)) (hB' i) ≫ q (i + 1) = 0 :=
      comp_ofLE_eq_zero_of_eq _ _
        (congrArg (tensorStepImage K L (i + 1)) (show p - i = p - (i + 1) + 1 by omega)) _
        (tensorStepImageQuotient_right K L hK hFL (i + 1) (p - (i + 1)))
    rw [← Category.assoc, hl, zero_comp, ← Category.assoc, hr, zero_comp]
  obtain ⟨g, hg, _⟩ := existsUnique_desc_iSup_of_interval_intersections P B hB hB' hcap
    (fun i => q i ≫ Sigma.ι G i) hcompat
  let S := imageSubobject (tensorFiltrationSumι K L p)
  let T := imageSubobject (tensorFiltrationSumι K L (p + 1))
  have hTS : T ≤ S := tensorFiltrationSumι_antitone K L (by omega)
  let e := Subobject.isoOfEq S (⨆ i, P i) (tensorStepImage_iSup K L p)
  let gS := e.hom ≫ g
  have hle (i : ℤ) : P i ≤ S := tensorStepImage_le_convolution K L p i (p - i) (by omega)
  have hgS (i : ℤ) : Subobject.ofLE (P i) S (hle i) ≫ gS = q i ≫ Sigma.ι G i := by
    simpa [gS, e] using hg i
  have hzero : Subobject.ofLE T S hTS ≫ gS = 0 := by
    apply tensorConvolution_image_hom_ext K L (p + 1)
    intro i
    have hrel : tensorStepImage K L i (p + 1 - i) ≤ P i :=
      tensorStepImage_antitone K L le_rfl (by omega)
    have hz : Subobject.ofLE (tensorStepImage K L i (p + 1 - i)) (P i) hrel ≫ q i = 0 :=
      comp_ofLE_eq_zero_of_eq _ _
        (congrArg (tensorStepImage K L i) (show p + 1 - i = p - i + 1 by omega)) _
        (tensorStepImageQuotient_right K L hK hFL i (p - i))
    simp only [comp_zero]
    calc
      _ = Subobject.ofLE (tensorStepImage K L i (p + 1 - i)) (P i) hrel ≫
          (Subobject.ofLE (P i) S (hle i) ≫ gS) := by simp [T]
      _ = 0 := by rw [hgS, ← Category.assoc, hz, zero_comp]
  let π := cokernel.π (Subobject.ofLE T S hTS)
  have hψ (i : ℤ) : ∃ ψ : G i ⟶ cokernel (Subobject.ofLE T S hTS),
      q i ≫ ψ = Subobject.ofLE (P i) S (hle i) ≫ π := by
    let f := factorThruImageSubobject
      (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i))) ≫
      Subobject.ofLE (P i) S (hle i)
    have hf : f ≫ S.arrow = K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i)) := by
      simp [f, S, P, tensorStepImage]
    have hleft : (K.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : i ⟶ i + 1).op ▷ L.filtration.obj (op (p - i))) ≫
        (f ≫ π) = 0 := by
      rw [← Category.assoc]
      apply comp_cokernel_of_image_le S T hTS
      rw [Category.assoc, hf]
      show imageSubobject ((_ ⊗ₘ 𝟙 _) ≫ (_ ⊗ₘ _)) ≤ T
      simp only [tensorHom_comp_tensorHom, Filtration.diagram_map_comp_ι_app, Category.id_comp]
      exact tensorStepImage_le_convolution K L (p + 1) (i + 1) (p - i) (by omega)
    have hright : (K.filtration.obj (op i) ◁ L.filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : p - i ⟶ p - i + 1).op) ≫ (f ≫ π) = 0 := by
      rw [← Category.assoc]
      apply comp_cokernel_of_image_le S T hTS
      rw [Category.assoc, hf]
      show imageSubobject ((𝟙 _ ⊗ₘ _) ≫ (_ ⊗ₘ _)) ≤ T
      simp only [tensorHom_comp_tensorHom, Filtration.diagram_map_comp_ι_app, Category.id_comp]
      exact tensorStepImage_le_convolution K L (p + 1) i (p - i + 1) (by omega)
    obtain ⟨ψ, hψ, _⟩ := tensorStepQuotient_universal K L i (p - i) (f ≫ π) hleft hright
    refine ⟨ψ, ?_⟩
    apply (cancel_epi (factorThruImageSubobject
      (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op (p - i))))).mp
    simpa only [q, f, ← Category.assoc, factor_tensorStepImageQuotient] using hψ
  choose ψ hψ using hψ
  let Φ := cokernel.desc (Subobject.ofLE T S hTS) gS hzero
  let Ψ := Sigma.desc ψ
  have hΦ : π ≫ Φ = gS := cokernel.π_desc _ _ _
  have hΦΨ : Φ ≫ Ψ = 𝟙 _ := by
    apply (cancel_epi (cokernel.π (Subobject.ofLE T S hTS))).mp
    rw [← Category.assoc, hΦ, Category.comp_id]
    apply tensorConvolution_image_hom_ext K L p
    intro i
    rw [← Category.assoc, hgS, Category.assoc]
    show q i ≫ Sigma.ι G i ≫ Sigma.desc ψ = _
    rw [Sigma.ι_desc, hψ]
  have hΨΦ : Ψ ≫ Φ = 𝟙 _ := by
    apply Sigma.hom_ext
    intro i
    apply (cancel_epi (q i)).mp
    simp only [Category.comp_id]
    show q i ≫ Sigma.ι G i ≫ Sigma.desc ψ ≫ Φ = _
    rw [Sigma.ι_desc_assoc, ← Category.assoc, hψ, Category.assoc, hΦ, hgS]
  exact ⟨{ hom := Φ, inv := Ψ, hom_inv_id := hΦΨ, inv_hom_id := hΨΦ }⟩

private lemma tensorConvolution_graded_homologyIso
    (hK : ∀ n, Module.Flat R (K.X.X n))
    (hFK : ∀ i n, Module.Flat R ((K.filtration.obj (op i)).X n))
    (hgrK : ∀ i n, Module.Flat R (((FilteredObject.gr i).obj K).X n))
    (hFL : ∀ j n, Module.Flat R ((L.filtration.obj (op j)).X n)) (p q : ℤ) :
    Nonempty ((((FilteredObject.gr p).obj (tensorConvolution K L)).homology (p + q)) ≅
      ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = p} =>
        (((FilteredObject.gr ij.1.1).obj K) ⊗
          ((FilteredObject.gr ij.1.2).obj L)).homology (p + q)) := by
  obtain ⟨e⟩ := tensorConvolution_gradedPieceIso K L hK hFK hgrK hFL p
  let ei : ℤ ≃ {ij : ℤ × ℤ // ij.1 + ij.2 = p} :=
    { toFun i := ⟨(i, p - i), by omega⟩
      invFun ij := ij.1.1
      left_inv _ := rfl
      right_inv ij := by ext <;> dsimp ; have := ij.2 ; omega }
  exact ⟨(HomologicalComplex.homologyFunctor _ _ (p + q)).mapIso e ≪≫
    homologyCoproductIso (fun i : ℤ => (FilteredObject.gr i).obj K ⊗
      (FilteredObject.gr (p - i)).obj L) (p + q) ≪≫
    Limits.Sigma.reindex ei (fun ij =>
      (((FilteredObject.gr ij.1.1).obj K) ⊗
        ((FilteredObject.gr ij.1.2).obj L)).homology (p + q))⟩

/-- For decreasingly filtered complexes `K` and `L` satisfying the flatness and K-flatness
assumptions of the Künneth construction, there is a convolution-filtered tensor product `T` and an
associated spectral sequence with the expected first page. If both filtrations are finite, or their
steps are eventually acyclic and eventually quasi-isomorphic to the underlying complexes, then the
first page has finite support in each total degree, the induced filtration on cohomology is finite,
and the sequence converges with the canonical stable-page comparison. -/
@[stacks 0H7W]
public theorem exists_kunneth_convolution_spectral_sequence
    (R : Type u) [CommRing R]
    (K L : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ)
    (hflatK :
      (∀ n : ℤ, Module.Flat R (K.X.X n)) ∧
      (∀ i n : ℤ, Module.Flat R ((K.filtration.obj (op i)).X n)) ∧
      (∀ i n : ℤ, Module.Flat R (((FilteredObject.gr i).obj K).X n)))
    (hflatL :
      (∀ n : ℤ, Module.Flat R (L.X.X n)) ∧
      (∀ i n : ℤ, Module.Flat R ((L.filtration.obj (op i)).X n)) ∧
      (∀ i n : ℤ, Module.Flat R (((FilteredObject.gr i).obj L).X n)))
    (hkflatK : K.X.KFlat ∧ (∀ i : ℤ, (K.filtration.obj (op i)).KFlat) ∧
      (∀ i : ℤ, ((FilteredObject.gr i).obj K).KFlat))
    (hkflatL : L.X.KFlat ∧ (∀ i : ℤ, (L.filtration.obj (op i)).KFlat) ∧
      (∀ i : ℤ, ((FilteredObject.gr i).obj L).KFlat)) :
    ∃ (T : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ)
      (eT : K.X ⊗ L.X ≅ T.X),
      (∀ p n : ℤ, ∀ Q : Subobject (T.X.X n),
        Subobject.mk ((T.filtration.ι.app (op p)).f n) ≤ Q ↔
          ∀ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = p},
            imageSubobject ((((K.filtration.ι.app (op ij.1.1)) ⊗ₘ
              (L.filtration.ι.app (op ij.1.2))) ≫ eT.hom).f n) ≤ Q) ∧
      ∃ (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
        (Z : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
        (D : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
        (FH : ∀ (n _p : ℤ), Subobject (T.X.homology n))
        (E : CohomologicalSpectralSequence (ModuleCat.{u} R) 0)
        (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))),
      (∀ p n : ℤ, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n)) ∧
      (∀ r p n : ℤ, Z r p n =
        F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1))) ∧
      (∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
        (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1))) ∧
      (∀ n p : ℤ, FH n p =
        imageSubobject (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n)) ∧
      (∀ p q : ℤ, Nonempty ((E.page 1 (by omega)).X (p, q) ≅
        ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = p} ↦
          (((FilteredObject.gr ij.1.1).obj K) ⊗
            ((FilteredObject.gr ij.1.2).obj L)).homology (p + q))) ∧
      (((K.filtration.IsFinite ∧ L.filtration.IsFinite) ∨
          ∃ a b : ℤ, a < b ∧
            (∀ i : ℤ, b < i → (K.filtration.obj (op i)).Acyclic) ∧
            (∀ i : ℤ, i < a → QuasiIso (K.filtration.ι.app (op i))) ∧
            (∀ j : ℤ, b < j → (L.filtration.obj (op j)).Acyclic) ∧
            (∀ j : ℤ, j < a → QuasiIso (L.filtration.ι.app (op j)))) →
      (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite) ∧
      (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
      (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
      (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
    (∀ p n : ℤ,
      IsGLB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1)) ⊔ F (p + 1) n)
        (kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
      IsLUB (Set.range fun r : ℕ =>
          F p n ⊓ (Subobject.«exists» (T.X.d (n - 1) n)).obj (F (p - r) (n - 1)) ⊔
            F (p + 1) n)
        (imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)) ∧
    (∀ p n : ℤ,
      let A := (Subobject.pullback (T.X.iCycles n)).obj (F p n)
      let N := kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
      let B := imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
      ∃ (a : (A : ModuleCat.{u} R) ⟶ (N : ModuleCat.{u} R))
        (b : (A : ModuleCat.{u} R) ⟶
          image (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))
        (e : cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) ≅
          cokernel (image.preComp
            (HomologicalComplex.homologyMap (T.filtration.diagram.map
              (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
            (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))),
        A.arrow ≫ T.X.iCycles n = a ≫ N.arrow ∧
        A.arrow ≫ T.X.homologyπ n =
          b ≫ image.ι (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n) ∧
        a ≫ cokernel.π (Subobject.ofLE (B ⊓ N) N inf_le_right) ≫ e.hom =
          b ≫ cokernel.π (image.preComp
            (HomologicalComplex.homologyMap (T.filtration.diagram.map
              (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
            (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n)))) := by
  let T := tensorConvolution K L
  obtain ⟨F, Z, D, FH, E, hE, hF, hZ, hD, hFH, hOne⟩ := exists_filteredComplex_spectralSequence T
  refine ⟨T, Iso.refl _, ?_, F, Z, D, FH, E, hE, hF, hZ, hD, hFH, ?_, ?_⟩
  · intro p n Q
    have hcomp (i j : ℤ) : (((K.filtration.ι.app (op i) ⊗ₘ
        L.filtration.ι.app (op j)) ≫ 𝟙 (K.X ⊗ L.X)).f n) =
        ((K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j)).f n) :=
      congrArg (fun f => f.f n)
        (Category.comp_id (K.filtration.ι.app (op i) ⊗ₘ L.filtration.ι.app (op j)))
    constructor
    · intro h ij
      show imageSubobject (((K.filtration.ι.app (op ij.1.1) ⊗ₘ
        L.filtration.ι.app (op ij.1.2)) ≫ 𝟙 (K.X ⊗ L.X)).f n) ≤ Q
      rw [hcomp]
      exact (tensorConvolution_le_iff K L p n Q).mp h ij
    · intro h
      apply (tensorConvolution_le_iff K L p n Q).mpr
      intro ij
      have hij := h ij
      change imageSubobject (((K.filtration.ι.app (op ij.1.1) ⊗ₘ
        L.filtration.ι.app (op ij.1.2)) ≫ 𝟙 (K.X ⊗ L.X)).f n) ≤ Q at hij
      rwa [hcomp] at hij
  · intro p q
    obtain ⟨e⟩ := hOne p q
    obtain ⟨f⟩ := tensorConvolution_graded_homologyIso K L
      hflatK.1 hflatK.2.1 hflatK.2.2 hflatL.2.1 p q
    exact ⟨e ≪≫ f⟩
  · rintro (⟨hK, hL⟩ | ⟨a, b, hab, haK, hqK, haL, hqL⟩)
    · obtain ⟨hbounded, hfinite, hregular, hstable⟩ :=
        finite_filtration_consequences R T (tensorConvolution_isFinite K L hK hL)
          F hF Z hZ D hD FH hFH E hE
      exact ⟨hbounded, hfinite, hregular, hstable,
        fun p n => stable_page_comparison R T F hF p n (hstable p n)⟩
    · exact isBounded_and_converges_of_step_bounds T F hF Z hZ D hD FH hFH E hE
        (a + a - 1) (b + b)
        (fun p hp => tensorConvolution_acyclic_of_add_lt K L
          hflatK.1 hflatK.2.1 hflatK.2.2 hflatL.2.1 hkflatK.2.1 hkflatL.2.1
          b b haK haL p hp)
        (fun p hp => tensorConvolution_quasiIso_of_lt K L
          hflatK.1 hflatK.2.1 hflatK.2.2 hflatL.2.1 hkflatK.1 hkflatK.2.1 hkflatL.2.1
          a a hqK hqL p hp)

/-- A complex quasi-isomorphic to an acyclic complex is acyclic. -/
private lemma acyclic_of_quasiIso {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (hf : QuasiIso f) (hL : L.Acyclic) : K.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have : QuasiIso f := hf
  have : IsIso (HomologicalComplex.homologyMap f n) :=
    (quasiIsoAt_iff_isIso_homologyMap f n).1 inferInstance
  exact (hL n).isZero_homology.of_iso
    (asIso (HomologicalComplex.homologyMap f n))

/-- A filtered quasi-isomorphism to `K` lifts quasi-isomorphisms of the filtration steps. -/
private lemma quasiIso_filtration_ι_of_hom {R : Type u} [CommRing R]
    {P K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ} (f : P ⟶ K)
    (hf : QuasiIso f.hom) (i : ℤ) (hfi : QuasiIso (f.natTrans.app (op i)))
    (hK : QuasiIso (K.filtration.ι.app (op i))) : QuasiIso (P.filtration.ι.app (op i)) := by
  rw [← quasiIso_iff_comp_right (P.filtration.ι.app (op i)) f.hom, ← f.comm (op i)]
  infer_instance

/-- Two filtered complexes of modules have a filtered K-flat tensor representative whose
associated spectral sequence has the expected Künneth first page. If the filtration steps of both
complexes are eventually acyclic and eventually quasi-isomorphic to the underlying complexes,
then the first page is bounded in every total degree, the induced filtration on cohomology is
finite, and the spectral sequence converges canonically to the cohomology of the derived tensor
product. -/
@[stacks 0H7Y]
public theorem exists_kunneth_filtered_complex
    (R : Type u) [CommRing R]
    (K L : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ) :
    ∃ (P Q : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ)
      (f : P ⟶ K) (g : Q ⟶ L)
      (T : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ) ℤᵒᵖ)
      (eT : P.X ⊗ Q.X ≅ T.X),
      ((∀ n : ℤ, Module.Flat R (P.X.X n)) ∧
        (∀ i n : ℤ, Module.Flat R ((P.filtration.obj (op i)).X n)) ∧
        (∀ i n : ℤ, Module.Flat R (((FilteredObject.gr i).obj P).X n)) ∧
        P.X.KFlat ∧
        (∀ i : ℤ, (P.filtration.obj (op i)).KFlat) ∧
        (∀ i : ℤ, ((FilteredObject.gr i).obj P).KFlat) ∧
        QuasiIso f.hom ∧
        (∀ i : ℤ, QuasiIso (f.natTrans.app (op i))) ∧
        (∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map f))) ∧
      ((∀ n : ℤ, Module.Flat R (Q.X.X n)) ∧
        (∀ i n : ℤ, Module.Flat R ((Q.filtration.obj (op i)).X n)) ∧
        (∀ i n : ℤ, Module.Flat R (((FilteredObject.gr i).obj Q).X n)) ∧
        Q.X.KFlat ∧
        (∀ i : ℤ, (Q.filtration.obj (op i)).KFlat) ∧
        (∀ i : ℤ, ((FilteredObject.gr i).obj Q).KFlat) ∧
        QuasiIso g.hom ∧
        (∀ i : ℤ, QuasiIso (g.natTrans.app (op i))) ∧
        (∀ i : ℤ, QuasiIso ((FilteredObject.gr i).map g))) ∧
      (∀ p n : ℤ, ∀ U : Subobject (T.X.X n),
        Subobject.mk ((T.filtration.ι.app (op p)).f n) ≤ U ↔
          ∀ ij : {ij : ℤ × ℤ // ij.1 + ij.2 = p},
            imageSubobject ((((P.filtration.ι.app (op ij.1.1)) ⊗ₘ
              (Q.filtration.ι.app (op ij.1.2))) ≫ eT.hom).f n) ≤ U) ∧
      ∃ (F : ∀ (_p n : ℤ), Subobject (T.X.X n))
        (Z : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
        (D : ∀ (_r _p n : ℤ), Subobject (T.X.X n))
        (FH : ∀ (n _p : ℤ), Subobject (T.X.homology n))
        (E : CohomologicalSpectralSequence (ModuleCat.{u} R) 0)
        (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _
            (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n))),
        (∀ p n : ℤ, F p n = Subobject.mk ((T.filtration.ι.app (op p)).f n)) ∧
        (∀ r p n : ℤ, Z r p n =
          F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (F (p + r) (n + 1))) ∧
        (∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (T.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1))) ∧
        (∀ n p : ℤ, FH n p =
          imageSubobject (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n)) ∧
        (∀ p q : ℤ, Nonempty ((E.page 1 (by omega)).X (p, q) ≅
          ∐ fun ij : {ij : ℤ × ℤ // ij.1 + ij.2 = p} ↦
            (((FilteredObject.gr ij.1.1).obj P) ⊗
              ((FilteredObject.gr ij.1.2).obj Q)).homology (p + q))) ∧
        (((∃ b : ℤ, ∀ i : ℤ, b < i → (K.filtration.obj (op i)).Acyclic) ∧
          (∃ a : ℤ, ∀ i : ℤ, i < a → QuasiIso (K.filtration.ι.app (op i))) ∧
          (∃ b : ℤ, ∀ j : ℤ, b < j → (L.filtration.obj (op j)).Acyclic) ∧
          (∃ a : ℤ, ∀ j : ℤ, j < a → QuasiIso (L.filtration.ι.app (op j)))) →
          (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 1 (by omega)).X (p, n - p))}.Finite) ∧
          (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
          (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
            (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
          (∀ p n : ℤ,
            IsGLB (Set.range fun r : ℕ ↦
                F p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj
                  (F (p + r) (n + 1)) ⊔ F (p + 1) n)
              (kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n) ∧
            IsLUB (Set.range fun r : ℕ ↦
                F p n ⊓ (Subobject.«exists» (T.X.d (n - 1) n)).obj
                  (F (p - r) (n - 1)) ⊔ F (p + 1) n)
              (imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n)) ∧
          (∀ p n : ℤ,
            let A := (Subobject.pullback (T.X.iCycles n)).obj (F p n)
            let N := kernelSubobject (T.X.d n (n + 1)) ⊓ F p n ⊔ F (p + 1) n
            let B := imageSubobject (T.X.d (n - 1) n) ⊓ F p n ⊔ F (p + 1) n
            ∃ (a : (A : ModuleCat.{u} R) ⟶ (N : ModuleCat.{u} R))
              (b : (A : ModuleCat.{u} R) ⟶
                image (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))
              (e : cokernel (Subobject.ofLE (B ⊓ N) N inf_le_right) ≅
                cokernel (image.preComp
                  (HomologicalComplex.homologyMap (T.filtration.diagram.map
                    (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
                  (HomologicalComplex.homologyMap (T.filtration.ι.app (op p)) n))),
              A.arrow ≫ T.X.iCycles n = a ≫ N.arrow ∧
              A.arrow ≫ T.X.homologyπ n =
                b ≫ image.ι (HomologicalComplex.homologyMap
                  (T.filtration.ι.app (op p)) n) ∧
              a ≫ cokernel.π (Subobject.ofLE (B ⊓ N) N inf_le_right) ≫ e.hom =
                b ≫ cokernel.π (image.preComp
                  (HomologicalComplex.homologyMap (T.filtration.diagram.map
                    (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) n)
                  (HomologicalComplex.homologyMap
                    (T.filtration.ι.app (op p)) n)))) := by
  obtain ⟨P, f, hfreePX, hfreePF, hfreePgr, hkPX, hkPF, hkPgr, hf, hfF, hfgr⟩ :=
    CochainComplex.KFlat.exists_free_kFlat_filtered_resolution R K
  obtain ⟨Q, g, hfreeQX, hfreeQF, hfreeQgr, hkQX, hkQF, hkQgr, hg, hgF, hggr⟩ :=
    CochainComplex.KFlat.exists_free_kFlat_filtered_resolution R L
  have hflatP :
      (∀ n : ℤ, Module.Flat R (P.X.X n)) ∧
      (∀ i n : ℤ, Module.Flat R ((P.filtration.obj (op i)).X n)) ∧
      (∀ i n : ℤ, Module.Flat R (((FilteredObject.gr i).obj P).X n)) :=
    ⟨fun n ↦ Module.Flat.of_free,
    fun i n ↦ Module.Flat.of_free, fun i n ↦ Module.Flat.of_free⟩
  have hflatQ :
      (∀ n : ℤ, Module.Flat R (Q.X.X n)) ∧
      (∀ i n : ℤ, Module.Flat R ((Q.filtration.obj (op i)).X n)) ∧
      (∀ i n : ℤ, Module.Flat R (((FilteredObject.gr i).obj Q).X n)) :=
    ⟨fun n ↦ Module.Flat.of_free,
    fun i n ↦ Module.Flat.of_free, fun i n ↦ Module.Flat.of_free⟩
  obtain ⟨T, eT, hT, F, Z, D, FH, E, hE, hspec⟩ :=
    exists_kunneth_convolution_spectral_sequence R P Q hflatP hflatQ
      ⟨hkPX, hkPF, hkPgr⟩ ⟨hkQX, hkQF, hkQgr⟩
  refine ⟨P, Q, f, g, T, eT,
    ⟨hflatP.1, hflatP.2.1, hflatP.2.2, hkPX, hkPF, hkPgr, hf, hfF, hfgr⟩,
    ⟨hflatQ.1, hflatQ.2.1, hflatQ.2.2, hkQX, hkQF, hkQgr, hg, hgF, hggr⟩,
    hT, F, Z, D, FH, E, hE, ?_⟩
  rcases hspec with ⟨hF, hZ, hD, hFH, hpage, hconv⟩
  refine ⟨hF, hZ, hD, hFH, hpage, ?_⟩
  intro hbounds
  apply hconv
  right
  rcases hbounds with ⟨⟨bK, hbK⟩, ⟨aK, haK⟩, ⟨bL, hbL⟩, ⟨aL, haL⟩⟩
  let a := min aK aL
  let b := max (max bK bL) (a + 1)
  refine ⟨a, b, by dsimp [b]; omega, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact acyclic_of_quasiIso (f.natTrans.app (op i)) (hfF i) (hbK i (by dsimp [b] at hi; omega))
  · intro i hi
    exact quasiIso_filtration_ι_of_hom f hf i (hfF i) (haK i (by dsimp [a] at hi; omega))
  · intro j hj
    exact acyclic_of_quasiIso (g.natTrans.app (op j)) (hgF j) (hbL j (by dsimp [b] at hj; omega))
  · intro j hj
    exact quasiIso_filtration_ι_of_hom g hg j (hgF j) (haL j (by dsimp [a] at hj; omega))
end CochainComplex.Kunneth

end
