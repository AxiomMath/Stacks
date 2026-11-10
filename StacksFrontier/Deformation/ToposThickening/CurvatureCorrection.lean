module

public import StacksFrontier.Deformation.ToposThickening.FlatComplexObstruction
public import StacksFrontier.Deformation.ToposThickening.IdealKernelNaturality
public import StacksFrontier.Deformation.ToposThickening.SquareZeroLiftRealization

/-!
# Correcting a lifted differential by a homotopy

Let `f : O ⟶ O₀` be a locally surjective morphism of sheaves of commutative rings on a site
whose kernel is a square-zero ideal sheaf `I`, let `F` be a bounded above flat lift of a complex
`K₀` of `O₀`-modules with reduction `F₀` and lifted differential `d`, and let
`c : F₀ ⟶ (F₀ ⊗_{O₀} I)[2]` be its curvature, the square `d ∘ d` read in the ideal part. This
file carries out the construction in the proof of `(1) ⇒ (2)` of Stacks 0DIW.

Suppose `α : G₀ ⟶ F₀` is a map of complexes and `h^n : G₀^n ⟶ F₀^{n + 1} ⊗ I` are maps with
`α ∘ c = d ∘ h + h ∘ d`. The fibre products `H^n = F^n ×_{F₀^n} G₀^n` with the differential
`(x, g) ↦ (d x - h(g), d g)` then form an honest complex of `O`-modules
(`Deformation.ComplexLift.correctedComplex`), and it sits in a short exact sequence of complexes
of `O`-modules
`0 ⟶ (F₀ ⊗_{O₀} I)|_O ⟶ H ⟶ G₀|_O ⟶ 0`
(`Deformation.ComplexLift.shortExact_correctedSequence`). For a bounded above complex `P` of flat
`O`-modules the reduction sequence `0 ⟶ (P₀ ⊗_{O₀} I)|_O ⟶ P ⟶ P₀|_O ⟶ 0` is short exact as
well (`Deformation.ComplexLift.shortExact_flatComplexSequence`), and the descending induction of
the source, using Stacks 0DIV, shows that a map from the second sequence to the first whose
outer components are `(δ ≫ s) ⊗ I` and `δ`, with `s` a quasi-isomorphism and middle component a
quasi-isomorphism, has `δ` a quasi-isomorphism
(`Deformation.ComplexLift.quasiIso_of_shortExact_comparison`).

## Main definitions

* `Deformation.ComplexLift.correctedComplex`: the complex `H` with the corrected differential.
* `Deformation.ComplexLift.correctedSequence`: `0 ⟶ (F₀ ⊗ I)|_O ⟶ H ⟶ G₀|_O ⟶ 0`.
* `Deformation.ComplexLift.flatComplexSequence`: the reduction sequence of a bounded above
  complex of flat `O`-modules, built from the canonical kernel identification of Tag 0DIU.
* `Deformation.ComplexLift.flatComplexTranspose`: the transpose `P₀ ⟶ X` of a map of complexes
  `P ⟶ X|_O`.

## Main results

* `Deformation.ComplexLift.correctedD_comp_correctedD`: the corrected differential squares to
  zero.
* `Deformation.ComplexLift.shortExact_correctedSequence` and
  `Deformation.ComplexLift.shortExact_flatComplexSequence`: the two sequences are short exact.
* `Deformation.ComplexLift.emb_comp_of_unit`: the kernel identifications of two flat lifts are
  compatible with any degreewise map compatible with the reductions.
* `Deformation.ComplexLift.emb_comp_correctedIncl`: a map from a flat lift into the corrected
  complex respects the ideal parts.
* `Deformation.ComplexLift.quasiIso_of_shortExact_comparison`: the descending induction.

## References

* [Stacks Project, Tag 0DIW](https://stacks.math.columbia.edu/tag/0DIW)
* [Stacks Project, Tag 0DIV](https://stacks.math.columbia.edu/tag/0DIV)
* [Stacks Project, Tag 05QA](https://stacks.math.columbia.edu/tag/05QA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Sheaves.ChangeOfRings (ringSheafMap)
open Stacks.SheafOfModules.ComplexLifting (GradedDifferential BaseChangeTo
  IsExtensionOfScalars)

universe v u w d d₀

namespace Deformation.ComplexLift

attribute [-instance] CategoryTheory.catToReflQuiver

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  {O O₀ : Sheaf J CommRingCat.{max u v w}} {f : O ⟶ O₀}
  {I : SheafMod O₀} [((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).Additive]
  {S : SquareZeroIdeal f I}

variable (f) in
/-- Restriction of scalars along `f`, applied degreewise to complexes, at the spelling of the flat
lifts. -/
abbrev restrictC : CochainComplex (SheafMod O₀) ℤ ⥤ CochainComplex (SheafMod O) ℤ :=
  (restrict f).mapHomologicalComplex (ComplexShape.up ℤ)

section Correction

variable {K₀ : CochainComplex (SheafMod O₀) ℤ} {L : FlatLift f K₀} (T : IdealKernel S L)
  {G₀ : CochainComplex (SheafMod O₀) ℤ} (α : G₀ ⟶ L.baseChange.complex)
  (k : ∀ n : ℤ, G₀.X n ⟶ (L.idealTensor (I := I)).X (n + 1))

/-- The reduction map of a flat lift is an epimorphism when `f` is locally surjective. -/
private theorem epi_baseChange_unit (hf : Sheaf.IsLocallySurjective f) (n : ℤ) :
    Epi (L.baseChange.unit n) :=
  IsExtensionOfScalars.epi_unit.{v, u, max u v w, max u v w} f hf (L.baseChange.isExtension n)

/-- The term `F^n ×_{F₀^n} G₀^n` of the corrected complex. -/
abbrev correctedTerm (n : ℤ) : SheafMod O :=
  pullback (L.baseChange.unit n) ((restrict f).map (α.f n))

/-- The corrected differential `(x, g) ↦ (d x - h(g), d g)` of `F ×_{F₀} G₀`. -/
def correctedD (n : ℤ) : correctedTerm α n ⟶ correctedTerm α (n + 1) :=
  pullback.lift
    (pullback.fst _ _ ≫ L.F.d n - pullback.snd _ _ ≫ (restrict f).map (k n) ≫ T.emb (n + 1))
    (pullback.snd _ _ ≫ (restrict f).map (G₀.d n (n + 1))) (by
      simp only [Preadditive.sub_comp, Category.assoc, L.baseChange.differential n,
        T.emb_comp_unit, comp_zero, sub_zero]
      rw [← CategoryTheory.Functor.map_comp, ← α.comm n (n + 1),
        CategoryTheory.Functor.map_comp, pullback.condition_assoc])

/-- The first component of the corrected differential is `(x, g) ↦ d x - h(g)`. -/
@[reassoc (attr := simp)]
theorem correctedD_fst (n : ℤ) :
    correctedD T α k n ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ L.F.d n - pullback.snd _ _ ≫ (restrict f).map (k n) ≫ T.emb (n + 1) :=
  pullback.lift_fst _ _ _

/-- The second component of the corrected differential is `(x, g) ↦ d g`. -/
@[reassoc (attr := simp)]
theorem correctedD_snd (n : ℤ) :
    correctedD T α k n ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ (restrict f).map (G₀.d n (n + 1)) :=
  pullback.lift_snd _ _ _

variable (hk : ∀ n : ℤ, α.f n ≫ curvature T n =
    k n ≫ (L.idealTensor (I := I)).d (n + 1) (n + 1 + 1) + G₀.d n (n + 1) ≫ k (n + 1))

include hk in
/-- **The corrected differential squares to zero**: the square of `d` is the curvature, which the
correction `h` cancels by `α ∘ c = d ∘ h + h ∘ d`. -/
theorem correctedD_comp_correctedD (n : ℤ) :
    correctedD T α k n ≫ correctedD T α k (n + 1) = 0 := by
  apply pullback.hom_ext
  · have h1 : pullback.fst (L.baseChange.unit n) ((restrict f).map (α.f n)) ≫ L.F.d n ≫
        L.F.d (n + 1) = pullback.snd _ _ ≫ (restrict f).map (α.f n ≫ curvature T n) ≫
          T.emb (n + 1 + 1) := by
      rw [← unit_comp_curvature T n, pullback.condition_assoc, CategoryTheory.Functor.map_comp,
        Category.assoc]
    have h2 := T.emb_d (n + 1)
    simp only [Category.assoc, correctedD_fst, correctedD_fst_assoc, correctedD_snd_assoc,
      Preadditive.sub_comp, Preadditive.comp_sub, zero_comp]
    rw [h1, h2, hk n]
    simp only [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_comp,
      Preadditive.add_comp, Preadditive.comp_add, Category.assoc]
    abel
  · simp only [Category.assoc, correctedD_snd, correctedD_snd_assoc, zero_comp,
      ← CategoryTheory.Functor.map_comp, HomologicalComplex.d_comp_d,
      CategoryTheory.Functor.map_zero, comp_zero]

/-- **The corrected complex** `H = F ×_{F₀} G₀` with the differential `(x, g) ↦ (d x - h(g), d g)`,
an honest complex of `O`-modules. -/
abbrev correctedComplex : CochainComplex (SheafMod O) ℤ :=
  CochainComplex.of (correctedTerm α) (correctedD T α k) (correctedD_comp_correctedD T α k hk)

/-- The differential of the corrected complex in degree `n` is `correctedD`. -/
theorem correctedComplex_d (n : ℤ) :
    (correctedComplex T α k hk).d n (n + 1) = correctedD T α k n :=
  CochainComplex.of_d (correctedTerm α) (correctedD T α k) n

/-- The inclusion `(F₀ ⊗ I)|_O ⟶ H`, `y ↦ (y, 0)`. -/
def correctedIncl :
    (restrictC f).obj (L.idealTensor (I := I)) ⟶ correctedComplex T α k hk where
  f n := pullback.lift (T.emb n) 0 (by rw [T.emb_comp_unit, zero_comp])
  comm' i j hij := by
    obtain rfl : j = i + 1 := by simpa using hij.symm
    rw [correctedComplex_d, Functor.mapHomologicalComplex_obj_d]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, correctedD_fst, pullback.lift_fst, Preadditive.comp_sub,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, zero_comp, sub_zero]
      exact T.emb_d i
    · rw [Category.assoc, Category.assoc, correctedD_snd, pullback.lift_snd,
        pullback.lift_snd_assoc, zero_comp, comp_zero]

/-- The projection `H ⟶ G₀|_O`. -/
def correctedProj : correctedComplex T α k hk ⟶ (restrictC f).obj G₀ where
  f n := pullback.snd _ _
  comm' i j hij := by
    obtain rfl : j = i + 1 := by simpa using hij.symm
    rw [correctedComplex_d, Functor.mapHomologicalComplex_obj_d, correctedD_snd]

/-- **The sequence** `0 ⟶ (F₀ ⊗_{O₀} I)|_O ⟶ H ⟶ G₀|_O ⟶ 0`. -/
def correctedSequence : ShortComplex (CochainComplex (SheafMod O) ℤ) :=
  ShortComplex.mk (correctedIncl T α k hk) (correctedProj T α k hk) (by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
    exact pullback.lift_snd _ _ _)

/-- The projection `H ⟶ F` of the corrected complex onto the lift, degreewise. -/
def correctedFst (n : ℤ) : (correctedComplex T α k hk).X n ⟶ L.F.X n :=
  pullback.fst (L.baseChange.unit n) ((restrict f).map (α.f n))

/-- The two projections of `F^n ×_{F₀^n} G₀^n` agree in `F₀^n|_O`: the reduction of the first
component is the image under `α` of the second. -/
theorem correctedFst_unit (n : ℤ) :
    correctedFst T α k hk n ≫ L.baseChange.unit n =
      (correctedProj T α k hk).f n ≫ (restrict f).map (α.f n) :=
  pullback.condition

/-- Two maps into a term of the corrected complex are equal if their composites with both
projections agree. -/
theorem corrected_hom_ext {Z : SheafMod O} (n : ℤ) {a b : Z ⟶ (correctedComplex T α k hk).X n}
    (h₁ : a ≫ correctedFst T α k hk n = b ≫ correctedFst T α k hk n)
    (h₂ : a ≫ (correctedProj T α k hk).f n = b ≫ (correctedProj T α k hk).f n) : a = b :=
  pullback.hom_ext h₁ h₂

/-- The first component of the inclusion `y ↦ (y, 0)` is the ideal-part inclusion of the lift. -/
@[reassoc (attr := simp)]
theorem correctedIncl_f_fst (n : ℤ) :
    (correctedIncl T α k hk).f n ≫ correctedFst T α k hk n = T.emb n :=
  pullback.lift_fst _ _ _

/-- The second component of the inclusion `y ↦ (y, 0)` is zero. -/
@[reassoc (attr := simp)]
theorem correctedIncl_f_proj (n : ℤ) :
    (correctedIncl T α k hk).f n ≫ (correctedProj T α k hk).f n = 0 :=
  pullback.lift_snd _ _ _

omit [((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).Additive] in
/-- The inclusion `y ↦ (y, 0)` of the ideal part is the kernel of the projection
`F^n ×_{F₀^n} G₀^n ⟶ G₀^n`. -/
def correctedTermIsLimit (n : ℤ) :
    IsLimit (KernelFork.ofι (f := pullback.snd (L.baseChange.unit n) ((restrict f).map (α.f n)))
      (pullback.lift (T.emb n) 0 (by rw [T.emb_comp_unit, zero_comp])) (pullback.lift_snd _ _ _)) :=
  KernelFork.IsLimit.ofι _ _
    (fun z hz => (T.isKernel n).lift (KernelFork.ofι (z ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hz, zero_comp])))
    (fun z hz => by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst]
        exact Fork.IsLimit.lift_ι (T.isKernel n)
      · rw [Category.assoc, pullback.lift_snd, comp_zero]
        exact hz.symm)
    (fun z hz m hm => by
      have : Mono (T.emb n) := mono_emb T n
      rw [← cancel_mono (T.emb n)]
      have h1 := Fork.IsLimit.lift_ι (T.isKernel n) (t := KernelFork.ofι (z ≫ pullback.fst _ _)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc, hz, zero_comp]))
      simp only [KernelFork.ι_ofι] at h1
      rw [h1, ← hm, Category.assoc, pullback.lift_fst])

/-- **The sequence `0 ⟶ (F₀ ⊗ I)|_O ⟶ H ⟶ G₀|_O ⟶ 0` is short exact**: in each degree the
inclusion is a kernel of the projection, and the projection is a pullback of the reduction,
which is an epimorphism. -/
theorem shortExact_correctedSequence (hf : Sheaf.IsLocallySurjective f) :
    (correctedSequence T α k hk).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  have := epi_baseChange_unit (L := L) hf n
  have : Mono (T.emb n) := mono_emb T n
  have : Mono ((correctedIncl T α k hk).f n) :=
    mono_of_mono_fac (pullback.lift_fst (T.emb n) 0 _)
  have : Epi ((correctedProj T α k hk).f n) := by
    change Epi (pullback.snd _ _)
    infer_instance
  refine .mk' ?_ ‹_› ‹_›
  exact ShortComplex.exact_of_f_is_kernel _ (correctedTermIsLimit T α n)

/-- The corrected complex vanishes above any common bound of the lift and of `G₀`. -/
theorem isStrictlyLE_correctedComplex (b : ℤ) (hF : ∀ n, b < n → IsZero (L.F.X n))
    [G₀.IsStrictlyLE b] : (correctedComplex T α k hk).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have h1 := hF n hn
  have h2 : IsZero ((restrict f).obj (G₀.X n)) :=
    (G₀.isZero_of_isStrictlyLE b n hn).of_iso (Iso.refl _) |>.of_iso (Iso.refl _) |> fun h =>
      Functor.map_isZero _ h
  change IsZero (pullback _ _)
  rw [IsZero.iff_id_eq_zero]
  apply pullback.hom_ext
  · exact h1.eq_of_tgt _ _
  · exact h2.eq_of_tgt _ _

end Correction

section FlatComplexSequence

variable (hf : Sheaf.IsLocallySurjective f) (S) {P : CochainComplex (SheafMod O) ℤ}
  (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (P.X n))
  (hbdd : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (P.X n))

/-- The canonical kernel identification of a bounded above complex of flat `O`-modules, read as
a flat lift of its reduction. -/
abbrev flatComplexKernel : IdealKernel S (FlatLift.ofFlatComplex f P hflat hbdd) :=
  idealKernel hf S (FlatLift.ofFlatComplex f P hflat hbdd)

/-- The inclusion `(P₀ ⊗_{O₀} I)|_O ⟶ P` of the ideal part of a bounded above complex of flat
`O`-modules, as a map of complexes. -/
def flatComplexEmb :
    (restrictC f).obj ((idealTensorFunctor O₀ I).obj
      ((extensionOfScalarsCochainComplex J f).obj P)) ⟶ P where
  f n := (flatComplexKernel S hf hflat hbdd).emb n
  comm' i j hij := by
    obtain rfl : j = i + 1 := by simpa using hij.symm
    exact (flatComplexKernel S hf hflat hbdd).emb_d i

/-- In degree `n`, `flatComplexEmb` is the canonical kernel inclusion. -/
theorem flatComplexEmb_f (n : ℤ) :
    (flatComplexEmb S hf hflat hbdd).f n = (flatComplexKernel S hf hflat hbdd).emb n := rfl

/-- The reduction `P ⟶ P₀|_O`, as a map of complexes. -/
def flatComplexUnitMap (P : CochainComplex (SheafMod O) ℤ) :
    P ⟶ (restrictC f).obj ((extensionOfScalarsCochainComplex J f).obj P) where
  f n := flatComplexUnit f P n
  comm' i j _ := (flatComplexUnit_naturality P i j).symm

/-- In degree `n`, `flatComplexUnitMap` is the reduction map `P^n ⟶ P₀^n|_O`. -/
theorem flatComplexUnitMap_f (P : CochainComplex (SheafMod O) ℤ) (n : ℤ) :
    (flatComplexUnitMap (f := f) P).f n = flatComplexUnit f P n := rfl

/-- The transpose `P₀ ⟶ X` of a map of complexes `x : P ⟶ X|_O`, degreewise the map out of the
extension of scalars given by its universal property. -/
def flatComplexTranspose {P : CochainComplex (SheafMod O) ℤ}
    {X : CochainComplex (SheafMod O₀) ℤ} (x : P ⟶ (restrictC f).obj X) :
    (extensionOfScalarsCochainComplex J f).obj P ⟶ X where
  f n := IsExtensionOfScalars.desc.{v, u, max u v w, max u v w} f
    (flatComplexUnit_isExtension P n) (x.f n)
  comm' i j _ := by
    apply (flatComplexUnit_isExtension P i _).injective
    change flatComplexUnit f P i ≫ (restrict f).map (_ ≫ _) =
      flatComplexUnit f P i ≫ (restrict f).map (_ ≫ _)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ← Category.assoc,
      IsExtensionOfScalars.desc_spec, ← Category.assoc, ← flatComplexUnit_naturality,
      Category.assoc, IsExtensionOfScalars.desc_spec]
    exact x.comm i j

/-- The composite of the reduction `P ⟶ P₀|_O` with the restriction of the transpose of
`x : P ⟶ X|_O` is `x`. -/
@[reassoc]
theorem flatComplexUnitMap_comp_transpose {P : CochainComplex (SheafMod O) ℤ}
    {X : CochainComplex (SheafMod O₀) ℤ} (x : P ⟶ (restrictC f).obj X) :
    flatComplexUnitMap P ≫ (restrictC f).map (flatComplexTranspose x) = x :=
  HomologicalComplex.hom_ext _ _ fun n =>
    IsExtensionOfScalars.desc_spec f (flatComplexUnit_isExtension P n) (x.f n)

/-- The transpose of `x : P ⟶ X|_O` is the map out of the reduction of the flat lift `P` whose
composite with the reduction is `x`. -/
theorem flatComplexTranspose_spec {X : CochainComplex (SheafMod O₀) ℤ}
    (x : P ⟶ (restrictC f).obj X) (n : ℤ) :
    (FlatLift.ofFlatComplex f P hflat hbdd).baseChange.unit n ≫
      (restrict f).map ((flatComplexTranspose x).f n) = x.f n :=
  IsExtensionOfScalars.desc_spec f (flatComplexUnit_isExtension P n) (x.f n)

/-- **The reduction sequence** `0 ⟶ (P₀ ⊗_{O₀} I)|_O ⟶ P ⟶ P₀|_O ⟶ 0` of a bounded above complex
of flat `O`-modules. -/
def flatComplexSequence : ShortComplex (CochainComplex (SheafMod O) ℤ) :=
  ShortComplex.mk (flatComplexEmb S hf hflat hbdd) (flatComplexUnitMap (f := f) P) (by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
    exact (flatComplexKernel S hf hflat hbdd).emb_comp_unit n)

/-- **The reduction sequence of a bounded above complex of flat `O`-modules is short exact**: the
ideal part is the kernel of the reduction (Tag 0DIU, through Tag 08M4), and the reduction is an
epimorphism. -/
theorem shortExact_flatComplexSequence : (flatComplexSequence S hf hflat hbdd).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  have : Epi (flatComplexUnit f P n) :=
    epi_baseChange_unit (L := FlatLift.ofFlatComplex f P hflat hbdd) hf n
  have : Mono ((flatComplexKernel S hf hflat hbdd).emb n) := mono_emb _ n
  refine .mk' ?_ ‹_› ‹_›
  exact ShortComplex.exact_of_f_is_kernel _ ((flatComplexKernel S hf hflat hbdd).isKernel n)

end FlatComplexSequence

section Comparison

variable {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ} {L : FlatLift f K₀} {M : FlatLift f L₀}

/-- **The kernel identifications are compatible with any degreewise map of flat lifts that is
compatible with the reductions.** If `g : L^n ⟶ M^n` and `r : L₀^n ⟶ M₀^n` satisfy
`g ≫ unit = unit ≫ r`, then `g` carries the ideal part of `L^n` to that of `M^n` through
`r ⊗ I`. Both sides send a local pure tensor `x̄ ⊗ a` to `a · g(x)`; no compatibility of `g` with
the lifted differentials is needed. -/
theorem emb_comp_of_unit (hf : Sheaf.IsLocallySurjective f) (TL : IdealKernel S L)
    (TM : IdealKernel S M) (n : ℤ) (g : L.F.X n ⟶ M.F.X n)
    (r : L.baseChange.complex.X n ⟶ M.baseChange.complex.X n)
    (hg : g ≫ M.baseChange.unit n = L.baseChange.unit n ≫ (restrict f).map r) :
    (restrict f).map (((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).map r) ≫
      TM.emb n = TL.emb n ≫ g := by
  have := epi_baseChange_unit (L := L) hf n
  refine Deformation.ToposThickening.tensorSheaf_restrict_hom_ext_of_locallySurjective_left
    O₀ (ringSheafMap f)
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).map
      (L.baseChange.unit n).val)
    (Deformation.ToposThickening.sheafModule_epi_locallySurjective
      (L.baseChange.unit n)) ?_
  intro U x a
  have hred : r.val.app U ((L.baseChange.unit n).val.app U x) =
      (M.baseChange.unit n).val.app U (g.val.app U x) :=
    (congrArg (fun q : L.F.X n ⟶ _ => q.val.app U x) hg).symm
  change (TM.emb n).val.app U
      (((restrict f).map (((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).map
        r)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X n).val I.val)).app U
          ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a))) =
    g.val.app U ((TL.emb n).val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X n).val I.val)).app U
        ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a)))
  have hmap : ((restrict f).map (((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).map
        r)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X n).val I.val)).app U
          ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a)) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (M.baseChange.complex.X n).val I.val)).app U
        ((M.baseChange.unit n).val.app U (g.val.app U x) ⊗ₜ[O₀.obj.obj U] a) := by
    rw [← hred]
    exact Deformation.ToposThickening.tensorSheaf_map_unit_tmul O₀ r U _ a
  rw [hmap, TM.emb_tmul n U (g.val.app U x) a, TL.emb_tmul n U x a]
  exact ((g.val.app U).hom.map_smul
    (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from S.incl U a) x).symm

end Comparison

section CorrectedComparison

variable {K₀ K₁ : CochainComplex (SheafMod O₀) ℤ} {L : FlatLift f K₀} (T : IdealKernel S L)
  {G₀ : CochainComplex (SheafMod O₀) ℤ} (α : G₀ ⟶ L.baseChange.complex)
  (k : ∀ n : ℤ, G₀.X n ⟶ (L.idealTensor (I := I)).X (n + 1))
  (hk : ∀ n : ℤ, α.f n ≫ curvature T n =
    k n ≫ (L.idealTensor (I := I)).d (n + 1) (n + 1 + 1) + G₀.d n (n + 1) ≫ k (n + 1))

/-- **A map from a flat lift into the corrected complex respects the ideal parts.** If
`g : M^n ⟶ H^n` lies over `r : M₀^n ⟶ G₀^n`, it carries the ideal part of `M^n` to the ideal part
`(F₀^n ⊗ I)|_O` of `H^n` through `(r ≫ α) ⊗ I`. -/
theorem emb_comp_correctedIncl (hf : Sheaf.IsLocallySurjective f) {M : FlatLift f K₁}
    (TM : IdealKernel S M) (n : ℤ) (g : M.F.X n ⟶ (correctedComplex T α k hk).X n)
    (r : M.baseChange.complex.X n ⟶ G₀.X n)
    (hg : g ≫ (correctedProj T α k hk).f n = M.baseChange.unit n ≫ (restrict f).map r) :
    (restrict f).map (((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).map
      (r ≫ α.f n)) ≫ (correctedIncl T α k hk).f n = TM.emb n ≫ g := by
  refine corrected_hom_ext T α k hk n ?_ ?_
  · rw [Category.assoc, correctedIncl_f_fst, Category.assoc]
    refine emb_comp_of_unit hf TM T n (g ≫ correctedFst T α k hk n) (r ≫ α.f n) ?_
    rw [Category.assoc, correctedFst_unit, ← Category.assoc, hg, Category.assoc,
      CategoryTheory.Functor.map_comp]
  · rw [Category.assoc, correctedIncl_f_proj, comp_zero, Category.assoc, hg, ← Category.assoc,
      TM.emb_comp_unit, zero_comp]

end CorrectedComparison

section Induction

variable [HasDerivedCategory.{d₀} (SheafMod O₀)]

variable {X Y G : CochainComplex (SheafMod O₀) ℤ} {P H : CochainComplex (SheafMod O) ℤ}
  (eA : (restrictC f).obj ((idealTensorFunctor O₀ I).obj X) ⟶ P)
  (uA : P ⟶ (restrictC f).obj X) (wA : eA ≫ uA = 0)
  (hA : (ShortComplex.mk eA uA wA).ShortExact)
  (eB : (restrictC f).obj ((idealTensorFunctor O₀ I).obj Y) ⟶ H)
  (pB : H ⟶ (restrictC f).obj G) (wB : eB ≫ pB = 0)
  (hB : (ShortComplex.mk eB pB wB).ShortExact)
  (γ : P ⟶ H) [QuasiIso γ] (δ : X ⟶ G) (s : G ⟶ Y) [QuasiIso s]
  (c₁ : ∀ n, (restrict f).map (((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I).map
    (δ.f n ≫ s.f n)) ≫ eB.f n = eA.f n ≫ γ.f n)
  (c₂ : γ ≫ pB = uA ≫ (restrictC f).map δ)
  (b : ℤ) [X.IsStrictlyLE b] [Y.IsStrictlyLE b]
  (hX : ∀ i, flatObjects O₀ (X.X i)) (hY : ∀ i, flatObjects O₀ (Y.X i))

/-- The map of short exact sequences `(0 ⟶ (X ⊗ I)|_O ⟶ P ⟶ X|_O ⟶ 0) ⟶
(0 ⟶ (Y ⊗ I)|_O ⟶ H ⟶ G|_O ⟶ 0)` given by `(δ ≫ s) ⊗ I`, `γ` and `δ`. -/
def shortExactComparison : ShortComplex.mk eA uA wA ⟶ ShortComplex.mk eB pB wB where
  τ₁ := (restrictC f).map ((idealTensorFunctor O₀ I).map (δ ≫ s))
  τ₂ := γ
  τ₃ := (restrictC f).map δ
  comm₁₂ := HomologicalComplex.hom_ext _ _ fun n => by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f]
    exact c₁ n
  comm₂₃ := c₂

include hA hB c₁ c₂ b hX hY in
/-- **The inductive step of the source**: if `δ ≫ s` is an isomorphism on cohomology in degrees
`≥ n`, it is one in degree `n - 1`. The same holds for `(δ ≫ s) ⊗ I` by Stacks 0DIV, and the
five lemma (Stacks 05QA) applied twice to the long exact cohomology sequences gives first
surjectivity and then injectivity of `Hⁿ⁻¹(δ)`. -/
theorem isIso_homologyMap_comparison_step (n : ℤ)
    (h : ∀ i, n ≤ i → IsIso (HomologicalComplex.homologyMap (δ ≫ s) i)) :
    IsIso (HomologicalComplex.homologyMap (δ ≫ s) (n - 1)) := by
  have : (restrict f).Faithful :=
    Stacks.SheafOfModules.ComplexLifting.restrictScalars_faithful.{v, u, max u v w, max u v w} f
  let φ := shortExactComparison eA uA wA eB pB wB γ δ s c₁ c₂
  have : QuasiIso φ.τ₂ := ‹QuasiIso γ›
  have T := homologyMap_tensorRight_of_isStrictlyLE.{d₀} O₀ I (δ ≫ s) b hX hY n
    (fun i hi ↦ h i hi.le) (fun i hi ↦ by have := h i hi; infer_instance)
  have h₁ : Epi (HomologicalComplex.homologyMap φ.τ₃ (n - 1)) := by
    refine HomologicalComplex.HomologySequence.epi_homologyMap_τ₃ φ hA hB (n - 1)
      inferInstance (fun j hj ↦ ?_) fun j hj ↦ inferInstance
    have hj' : j = n - 1 + 1 := hj.symm
    exact (epi_homologyMap_map_iff (restrict f) _ j).2 (T.2 j (by omega))
  have h₂ : Epi (HomologicalComplex.homologyMap δ (n - 1)) :=
    (epi_homologyMap_map_iff (restrict f) _ _).1 h₁
  have h₃ : Epi (HomologicalComplex.homologyMap (δ ≫ s) (n - 1)) := by
    rw [HomologicalComplex.homologyMap_comp]; exact epi_comp _ _
  have T' := homologyMap_tensorRight_of_isStrictlyLE.{d₀} O₀ I (δ ≫ s) b hX hY (n - 1)
    (fun i hi ↦ h i (by omega))
    (fun i hi ↦ by
      by_cases hin : i = n - 1
      · subst hin; exact h₃
      · have := h i (by omega); infer_instance)
  have h₄ : Mono (HomologicalComplex.homologyMap φ.τ₃ (n - 1)) :=
    HomologicalComplex.HomologySequence.mono_homologyMap_τ₃ φ hA hB (n - 1)
      ((epi_homologyMap_map_iff (restrict f) _ _).2 (T'.2 (n - 1) le_rfl))
      inferInstance
      (fun j hj ↦ (mono_homologyMap_map_iff (restrict f) _ j).2
        (by have := T'.1 j (by have hj' : n - 1 + 1 = j := hj; omega); infer_instance))
  have h₅ : Mono (HomologicalComplex.homologyMap δ (n - 1)) :=
    (mono_homologyMap_map_iff (restrict f) _ _).1 h₄
  have : IsIso (HomologicalComplex.homologyMap δ (n - 1)) := isIso_of_mono_of_epi _
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

include hA hB c₁ c₂ b hX hY in
/-- **The reduction `δ` is a quasi-isomorphism**, by descending induction on the degree starting
above the common bound `b`. -/
theorem quasiIso_of_shortExact_comparison : QuasiIso δ := by
  have key : ∀ k : ℕ, ∀ i, b + 1 - k ≤ i → IsIso (HomologicalComplex.homologyMap (δ ≫ s) i) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      exact ⟨⟨0, (isZero_homology_of_isStrictlyLE' X b i (by omega)).eq_of_src _ _,
        (isZero_homology_of_isStrictlyLE' Y b i (by omega)).eq_of_src _ _⟩⟩
    | succ k ih =>
      intro i hi
      by_cases hik : b + 1 - k ≤ i
      · exact ih i hik
      · have hi' : i = b + 1 - k - 1 := by omega
        subst hi'
        exact isIso_homologyMap_comparison_step eA uA wA hA eB pB wB hB γ δ s c₁ c₂ b hX hY
          (b + 1 - k) ih
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hu := key (b + 1 - i).toNat i (by omega)
  rw [HomologicalComplex.homologyMap_comp] at hu
  exact IsIso.of_isIso_comp_right _ (HomologicalComplex.homologyMap s i)

end Induction

end Deformation.ComplexLift

end
