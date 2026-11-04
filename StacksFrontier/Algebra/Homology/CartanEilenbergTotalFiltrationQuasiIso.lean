module

public import StacksFrontier.Algebra.Homology.CartanEilenbergTotalFiltration
public import StacksFrontier.Algebra.Homology.Embedding.StupidTruncHomology

/-!
# The filtered augmentation into a Cartan-Eilenberg resolution is a filtered quasi-isomorphism

Let `K^•` be a cochain complex of an abelian category and let `I^{•,•}` be a Cartan-Eilenberg
resolution of it ([Stacks, Tag 015H]).  The augmentation `K^• ⟶ Tot(I)` is a quasi-isomorphism
([Stacks, Tag 0133], `StacksDraft.CartanEilenbergResolutions.quasiIso_totalAugmentation`), and it
is filtered for the brutal truncation filtration of the source and the first total filtration of
the target (`StacksDraft.CartanEilenbergResolutions.filteredTotalAugmentation`).  This file proves
that *each step* of that filtered morphism, `σ_{≥ p}K^• ⟶ F^pTot(I)`, is again a
quasi-isomorphism.

The mechanism is that the `p`-th step of the first total filtration is the total complex of the
brutal truncation of the *bicomplex* `I` in its first coordinate: `F^pTot(I) ≅ Tot(σ_{≥ p}I)`,
where `σ_{≥ p}I` keeps only the columns `I^{i,•}` with `i ≥ p`.  Under that identification the
`p`-th step of the filtered augmentation becomes the total augmentation
`σ_{≥ p}K^• ⟶ Tot(σ_{≥ p}I)`, and `σ_{≥ p}I` resolves `σ_{≥ p}K^•` column by column: the columns
of `σ_{≥ p}I` are those of `I` in degrees `≥ p` and zero below, exactly as for `σ_{≥ p}K^•`.  So
the acyclic assembly lemma `StacksDraft.TotalComplexQuasiIso.quasiIso_total_map` applies, just as
it does for the unfiltered augmentation.

## Main results

* `HomologicalComplex₂.totalBrutalTruncStepIso`: `Tot(σ_{≥ p}L) ≅ F^pTot(L)` for an arbitrary
  bicomplex `L`, the structural isomorphism carrying the argument.
* `StacksDraft.CartanEilenbergResolutions.quasiIso_filteredTotalAugmentation_natTrans_app`: each
  step `σ_{≥ p}K^• ⟶ F^pTot(I)` of the filtered augmentation is a quasi-isomorphism.

## Implementation notes

The subcomplex `F^pTot(L)^n ⊆ Tot(L)^n` is the image of the idempotent
`HomologicalComplex₂.totalProjector` cutting out the summands of first coordinate `≥ p`, so the
isomorphism `Tot(σ_{≥ p}L) ≅ F^pTot(L)` is built by exhibiting `Tot(σ_{≥ p}L)^n ⟶ Tot(L)^n` as a
split monomorphism whose image subobject is that of the projector.  The splitting
`HomologicalComplex₂.totalBrutalTruncRetraction` is assembled out of the degreewise inverses of
the inclusion `σ_{≥ p}L ⟶ L`, which is an isomorphism in first degrees `≥ p` and has zero source
below `p`.

Every inclusion of a filtration step is spelled through `CochainComplex.filtrationStepι` (and its
specialisations `StacksDraft.CartanEilenbergResolutions.totalFiltration₁ι` and
`...stupidTruncationFiltrationι`), whose ascribed types cross the `Functor.const` seam in the
codomain of `CategoryTheory.FilteredObject.Filtration.ι` once and for all.  In particular the
components of `totalBrutalTruncStepIso` are built with that inclusion, not with the arrow of the
image subobject it is definitionally equal to: a goal mixing the two spellings is not type-correct
at reducible transparency, and then neither `rw` nor `simp` can touch it.  For the same reason the
comparison in `quasiIso_filteredTotalAugmentation_natTrans_app` is assembled from a morphism
produced with the filtration-step spelling of its source, obtained together with its
characterisation rather than by definition.

## References

* [Stacks Project, Tag 015H](https://stacks.math.columbia.edu/tag/015H)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open StacksDraft.TotalComplexQuasiIso

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (p : ℤ)

/-- In first degrees `≥ p` the inclusion `σ_{≥ p}L ⟶ L` of the brutal truncation of a bicomplex
is an isomorphism in every second degree, being an isomorphism of columns. -/
lemma isIso_ιStupidTrunc_f_f (i j : ℤ) (hi : p ≤ i) :
    IsIso (((L.ιStupidTrunc (ComplexShape.embeddingUpIntGE p)).f i).f j) := by
  have := L.isIso_ιStupidTrunc_embeddingUpIntGE_f p i hi
  infer_instance

/-- In first degrees `< p` every component of the brutal truncation `σ_{≥ p}L` is zero. -/
private lemma isZero_stupidTrunc_f_f (i j : ℤ) (hi : i < p) :
    IsZero (((L.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X i).X j) :=
  ((HomologicalComplex.eval C (ComplexShape.up ℤ) j).map_isZero
    (L.isZero_X_stupidTrunc_embeddingUpIntGE p i hi))

section

variable [L.HasTotal (ComplexShape.up ℤ)]

/-- The inclusion of the `p`-th step of the first total filtration of `Tot(L)` is a monomorphism
in every degree. -/
instance mono_filtrationStepι_totalFiltration₁_f (n : ℤ) :
    Mono ((CochainComplex.filtrationStepι L.totalFiltration₁ (op p)).f n) :=
  inferInstanceAs
    (Mono (imageSubobject (L.totalProjector (fun i _ => p ≤ i) n)).arrow)

/-- The `p`-th step of the filtration of `Tot(L)` by the first coordinate is, in degree `n`, the
image of the projector onto the summands of first coordinate `≥ p`. -/
lemma mk_filtrationStepι_totalFiltration₁_f (n : ℤ) :
    Subobject.mk ((CochainComplex.filtrationStepι L.totalFiltration₁ (op p)).f n) =
      imageSubobject (L.totalProjector (fun i _ => p ≤ i) n) :=
  Subobject.mk_arrow _

variable [HomologicalComplex₂.HasTotal (L.stupidTrunc (ComplexShape.embeddingUpIntGE p))
    (ComplexShape.up ℤ)]

/-- The retraction `Tot(L)^n ⟶ Tot(σ_{≥ p}L)^n` of the inclusion induced by `σ_{≥ p}L ⟶ L`: on the
summand `L^{i,j}` it is the inverse of `(σ_{≥ p}L)^{i,j} ≅ L^{i,j}` when `i ≥ p`, and zero
otherwise. -/
def totalBrutalTruncRetraction (n : ℤ) :
    (L.total (ComplexShape.up ℤ)).X n ⟶
      (HomologicalComplex₂.total (L.stupidTrunc (ComplexShape.embeddingUpIntGE p))
        (ComplexShape.up ℤ)).X n :=
  L.totalDesc fun i j h =>
    if hi : p ≤ i then
      haveI := L.isIso_ιStupidTrunc_f_f p i j hi
      inv (((L.ιStupidTrunc (ComplexShape.embeddingUpIntGE p)).f i).f j) ≫
        HomologicalComplex₂.ιTotal (L.stupidTrunc (ComplexShape.embeddingUpIntGE p))
          (ComplexShape.up ℤ) i j n h
    else 0

/-- The retraction followed by the inclusion is the projector cutting out the `p`-th step of the
first total filtration. -/
lemma totalBrutalTruncRetraction_comp (n : ℤ) :
    L.totalBrutalTruncRetraction p n ≫
        (HomologicalComplex₂.total.map (L.ιStupidTrunc (ComplexShape.embeddingUpIntGE p))
          (ComplexShape.up ℤ)).f n =
      L.totalProjector (fun i _ => p ≤ i) n := by
  apply HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ)
  intro i j hij
  rw [← Category.assoc]
  dsimp only [totalBrutalTruncRetraction]
  rw [HomologicalComplex₂.ι_totalDesc, HomologicalComplex₂.ι_totalProjector]
  by_cases hi : p ≤ i
  · have := L.isIso_ιStupidTrunc_f_f p i j hi
    rw [dif_pos hi, if_pos hi, Category.assoc, HomologicalComplex₂.ιTotal_map,
      ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · rw [dif_neg hi, if_neg hi, zero_comp]

/-- The inclusion `Tot(σ_{≥ p}L) ⟶ Tot(L)` followed by the retraction is the identity: the
inclusion is a split monomorphism in every degree. -/
lemma comp_totalBrutalTruncRetraction (n : ℤ) :
    (HomologicalComplex₂.total.map (L.ιStupidTrunc (ComplexShape.embeddingUpIntGE p))
          (ComplexShape.up ℤ)).f n ≫ L.totalBrutalTruncRetraction p n =
      𝟙 ((HomologicalComplex₂.total (L.stupidTrunc (ComplexShape.embeddingUpIntGE p))
        (ComplexShape.up ℤ)).X n) := by
  apply HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ)
  intro i j hij
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc, Category.comp_id]
  dsimp only [totalBrutalTruncRetraction]
  rw [HomologicalComplex₂.ι_totalDesc]
  by_cases hi : p ≤ i
  · have := L.isIso_ιStupidTrunc_f_f p i j hi
    rw [dif_pos hi, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  · exact (L.isZero_stupidTrunc_f_f p i j (by omega)).eq_of_src _ _

/-- The map `Tot(σ_{≥ p}L)^n ⟶ Tot(L)^n` induced by the inclusion `σ_{≥ p}L ⟶ L` is a
monomorphism. -/
instance mono_total_map_ιStupidTrunc_f (n : ℤ) :
    Mono ((HomologicalComplex₂.total.map (L.ιStupidTrunc (ComplexShape.embeddingUpIntGE p))
      (ComplexShape.up ℤ)).f n) :=
  mono_of_mono_fac (L.comp_totalBrutalTruncRetraction p n)

/-- The image of `Tot(σ_{≥ p}L)^n ⟶ Tot(L)^n` is the image of the projector onto the summands of
first coordinate `≥ p`. -/
lemma mk_total_map_ιStupidTrunc_f (n : ℤ) :
    Subobject.mk ((HomologicalComplex₂.total.map
        (L.ιStupidTrunc (ComplexShape.embeddingUpIntGE p)) (ComplexShape.up ℤ)).f n) =
      imageSubobject (L.totalProjector (fun i _ => p ≤ i) n) := by
  apply le_antisymm
  · rw [← Subobject.mk_arrow (imageSubobject (L.totalProjector (fun i _ => p ≤ i) n))]
    apply Subobject.mk_le_mk_of_comm
      ((HomologicalComplex₂.total.map (L.ιStupidTrunc (ComplexShape.embeddingUpIntGE p))
        (ComplexShape.up ℤ)).f n ≫ factorThruImageSubobject _)
    rw [Category.assoc, imageSubobject_arrow_comp, ← L.totalBrutalTruncRetraction_comp p n,
      ← Category.assoc, L.comp_totalBrutalTruncRetraction p n, Category.id_comp]
  · apply imageSubobject_le (L.totalProjector (fun i _ => p ≤ i) n)
      (L.totalBrutalTruncRetraction p n ≫ (Subobject.underlyingIso _).inv)
    simpa only [Category.assoc, Subobject.underlyingIso_arrow] using
      L.totalBrutalTruncRetraction_comp p n

/-- The degree-`n` component of `Tot(σ_{≥ p}L) ≅ F^pTot(L)`, with codomain spelled as the
filtration step rather than as the image of the projector. -/
def totalBrutalTruncStepXIso (n : ℤ) :
    (HomologicalComplex₂.total (L.stupidTrunc (ComplexShape.embeddingUpIntGE p))
        (ComplexShape.up ℤ)).X n ≅ (L.totalFiltration₁.filtration.obj (op p)).X n :=
  Subobject.isoOfMkEqMk
    ((HomologicalComplex₂.total.map (L.ιStupidTrunc (ComplexShape.embeddingUpIntGE p))
      (ComplexShape.up ℤ)).f n)
    ((CochainComplex.filtrationStepι L.totalFiltration₁ (op p)).f n)
    ((L.mk_total_map_ιStupidTrunc_f p n).trans
      (L.mk_filtrationStepι_totalFiltration₁_f p n).symm)

/-- `totalBrutalTruncStepXIso` followed by the inclusion of the filtration step is the map
`Tot(σ_{≥ p}L)^n ⟶ Tot(L)^n` induced by `σ_{≥ p}L ⟶ L`. -/
@[reassoc]
lemma totalBrutalTruncStepXIso_hom_filtrationStepι (n : ℤ) :
    (L.totalBrutalTruncStepXIso p n).hom ≫
        (CochainComplex.filtrationStepι L.totalFiltration₁ (op p)).f n =
      (HomologicalComplex₂.total.map (L.ιStupidTrunc (ComplexShape.embeddingUpIntGE p))
        (ComplexShape.up ℤ)).f n := by
  simp only [totalBrutalTruncStepXIso, Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp]

/-- The inclusion of the `p`-th step of the first total filtration commutes with the
differentials. -/
lemma totalFiltration₁_d_filtrationStepι (q : ℤᵒᵖ) (n m : ℤ) :
    (L.totalFiltration₁.filtration.obj q).d n m ≫
        (CochainComplex.filtrationStepι L.totalFiltration₁ q).f m =
      (CochainComplex.filtrationStepι L.totalFiltration₁ q).f n ≫
        (L.total (ComplexShape.up ℤ)).d n m :=
  CochainComplex.filtrationStepι_comm L.totalFiltration₁ q n m

/-- The morphism of complexes `Tot(σ_{≥ p}L) ⟶ F^pTot(L)` given in degree `n` by
`totalBrutalTruncStepXIso`. -/
def totalBrutalTruncStepHom :
    HomologicalComplex₂.total (L.stupidTrunc (ComplexShape.embeddingUpIntGE p))
        (ComplexShape.up ℤ) ⟶
      L.totalFiltration₁.filtration.obj (op p) where
  f n := (L.totalBrutalTruncStepXIso p n).hom
  comm' n m _ := by
    rw [← cancel_mono ((CochainComplex.filtrationStepι L.totalFiltration₁ (op p)).f m),
      Category.assoc, L.totalFiltration₁_d_filtrationStepι (op p)]
    conv_lhs => rw [← Category.assoc, L.totalBrutalTruncStepXIso_hom_filtrationStepι p]
    conv_rhs => rw [Category.assoc, L.totalBrutalTruncStepXIso_hom_filtrationStepι p]
    exact (HomologicalComplex₂.total.map (L.ιStupidTrunc (ComplexShape.embeddingUpIntGE p))
      (ComplexShape.up ℤ)).comm n m

/-- Each component of `totalBrutalTruncStepHom` is an isomorphism. -/
instance isIso_totalBrutalTruncStepHom_f (n : ℤ) :
    IsIso ((L.totalBrutalTruncStepHom p).f n) :=
  inferInstanceAs (IsIso (L.totalBrutalTruncStepXIso p n).hom)

/-- The comparison `Tot(σ_{≥ p}L) ⟶ F^pTot(L)` is an isomorphism of complexes. -/
instance isIso_totalBrutalTruncStepHom : IsIso (L.totalBrutalTruncStepHom p) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- **`Tot(σ_{≥ p}L) ≅ F^pTot(L)`**: the total complex of the brutal truncation of a bicomplex
`L` in its first coordinate is the `p`-th step of the filtration of `Tot(L)` by the first
coordinate. -/
def totalBrutalTruncStepIso :
    HomologicalComplex₂.total (L.stupidTrunc (ComplexShape.embeddingUpIntGE p))
        (ComplexShape.up ℤ) ≅
      L.totalFiltration₁.filtration.obj (op p) :=
  asIso (L.totalBrutalTruncStepHom p)

/-- `totalBrutalTruncStepIso` followed by the inclusion of the filtration step is the inclusion
`Tot(σ_{≥ p}L) ⟶ Tot(L)` induced by `σ_{≥ p}L ⟶ L`. -/
@[reassoc]
lemma totalBrutalTruncStepIso_hom_f_filtrationStepι (n : ℤ) :
    (L.totalBrutalTruncStepIso p).hom.f n ≫
        (CochainComplex.filtrationStepι L.totalFiltration₁ (op p)).f n =
      (HomologicalComplex₂.total.map (L.ιStupidTrunc (ComplexShape.embeddingUpIntGE p))
        (ComplexShape.up ℤ)).f n :=
  L.totalBrutalTruncStepXIso_hom_filtrationStepι p n

end

end HomologicalComplex₂

namespace StacksDraft.CartanEilenbergResolutions

variable {A : Type u} [Category.{v} A] [Abelian A] {K : CochainComplex A ℤ}
  (I : K.CartanEilenbergResolution) [I.bicomplex.HasTotal (ComplexShape.up ℤ)]

/-- The degree-`n` component of the `p`-th step of the filtered augmentation is
`filteredTotalAugmentationStepf`. -/
lemma filteredTotalAugmentationStep_f (p : ℤᵒᵖ) (n : ℤ) :
    (filteredTotalAugmentationStep I p).f n = filteredTotalAugmentationStepf I p n :=
  rfl

/-- Each step `σ_{≥ p}K^• ⟶ F^pTot(I)` of the filtered augmentation into a Cartan-Eilenberg
resolution is a quasi-isomorphism. -/
theorem quasiIso_filteredTotalAugmentation_natTrans_app (hK : CochainComplex.plus A K) (p : ℤ) :
    QuasiIso ((filteredTotalAugmentation I).natTrans.app (Opposite.op p)) := by
  classical
  obtain ⟨a, ha⟩ := hK
  have hAq : ∀ i j : ℤ, j < 0 →
      IsZero (((singleRowZero (K.stupidTrunc (ComplexShape.embeddingUpIntGE p))).X i).X j) :=
    fun i j hj => isZero_singleRowZero_X_X _ i j hj
  have hAp : ∀ i : ℤ, i < p →
      IsZero ((singleRowZero (K.stupidTrunc (ComplexShape.embeddingUpIntGE p))).X i) :=
    fun i hi => Functor.map_isZero (HomologicalComplex.single A (ComplexShape.up ℤ) 0)
      (K.isZero_X_stupidTrunc_embeddingUpIntGE p i hi)
  have hBp : ∀ i : ℤ, i < p →
      IsZero ((I.bicomplex.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X i) :=
    fun i hi => I.bicomplex.isZero_X_stupidTrunc_embeddingUpIntGE p i hi
  have hBq : ∀ i j : ℤ, j < 0 →
      IsZero (((I.bicomplex.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X i).X j) := by
    intro i j hj
    by_cases hi : p ≤ i
    · have := I.bicomplex.isIso_ιStupidTrunc_f_f p i j hi
      exact IsZero.of_iso (CochainComplex.isZero_of_isStrictlyGE (I.bicomplex.X i) 0 j hj)
        (asIso (((I.bicomplex.ιStupidTrunc (ComplexShape.embeddingUpIntGE p)).f i).f j))
    · exact I.bicomplex.isZero_stupidTrunc_f_f p i j (by omega)
  have : HomologicalComplex₂.HasTotal
      (singleRowZero (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)))
      (ComplexShape.up ℤ) := hasTotal_of_bounded _ p hAq hAp
  have : HomologicalComplex₂.HasTotal
      (I.bicomplex.stupidTrunc (ComplexShape.embeddingUpIntGE p)) (ComplexShape.up ℤ) :=
    hasTotal_of_bounded _ p hBq hBp
  have : HomologicalComplex₂.HasTotal (singleRowZero K) (ComplexShape.up ℤ) :=
    hasTotal_of_bounded _ a (fun i j hj => isZero_singleRowZero_X_X K i j hj)
      (fun i hi => isZero_singleRowZero_X K a i hi)
  obtain ⟨fp, hfp⟩ : ∃ fp : singleRowZero (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)) ⟶
      I.bicomplex.stupidTrunc (ComplexShape.embeddingUpIntGE p),
      fp ≫ I.bicomplex.ιStupidTrunc (ComplexShape.embeddingUpIntGE p) =
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE p)) ≫ I.ε :=
    ⟨StacksDraft.StupidTruncation.liftStupidTrunc _ _ _,
      StacksDraft.StupidTruncation.liftStupidTrunc_ι _ _ _⟩
  have hq : ∀ i : ℤ, QuasiIso (fp.f i) := by
    intro i
    by_cases hi : p ≤ i
    · have := I.bicomplex.isIso_ιStupidTrunc_embeddingUpIntGE_f p i hi
      have := K.isIso_ιStupidTrunc_embeddingUpIntGE_f p i hi
      have : QuasiIso (I.ε.f i) := I.quasiIso i
      have : QuasiIso ((((HomologicalComplex.single A (ComplexShape.up ℤ)
          0).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE p)) ≫ I.ε).f i) := by
        show QuasiIso ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).map
          ((K.ιStupidTrunc (ComplexShape.embeddingUpIntGE p)).f i) ≫ I.ε.f i)
        infer_instance
      have : QuasiIso (fp.f i ≫
          (I.bicomplex.ιStupidTrunc (ComplexShape.embeddingUpIntGE p)).f i) := by
        rw [← HomologicalComplex.comp_f, HomologicalComplex.congr_hom hfp i]
        infer_instance
      rw [show fp.f i = (fp.f i ≫
            (I.bicomplex.ιStupidTrunc (ComplexShape.embeddingUpIntGE p)).f i) ≫
          inv ((I.bicomplex.ιStupidTrunc (ComplexShape.embeddingUpIntGE p)).f i) by simp]
      infer_instance
    · have : IsIso (fp.f i) := isIso_of_isZero _ (hAp i (by omega)) (hBp i (by omega))
      infer_instance
  have : QuasiIso (HomologicalComplex₂.total.map fp (ComplexShape.up ℤ)) :=
    quasiIso_total_map fp p hAq hAp hBq hBp hq
  have key : totalSingleRowZeroUnit (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)) ≫
      HomologicalComplex₂.total.map fp (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          (I.bicomplex.ιStupidTrunc (ComplexShape.embeddingUpIntGE p))
          (ComplexShape.up ℤ) =
      K.ιStupidTrunc (ComplexShape.embeddingUpIntGE p) ≫ totalAugmentation I := by
    rw [← HomologicalComplex₂.total.map_comp, hfp, HomologicalComplex₂.total.map_comp,
      ← Category.assoc, totalSingleRowZeroUnit_naturality, Category.assoc,
      ← totalAugmentation_eq]
  have hcomp : ∀ n : ℤ,
      (totalSingleRowZeroUnit (K.stupidTrunc (ComplexShape.embeddingUpIntGE p))).f n ≫
        (HomologicalComplex₂.total.map fp (ComplexShape.up ℤ)).f n ≫
          (I.bicomplex.totalBrutalTruncStepIso p).hom.f n ≫
            (CochainComplex.filtrationStepι I.bicomplex.totalFiltration₁ (op p)).f n =
      (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE p)).f n ≫ totalAugmentationf I n := by
    intro n
    rw [HomologicalComplex₂.totalBrutalTruncStepIso_hom_f_filtrationStepι,
      ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, key,
      HomologicalComplex.comp_f, totalAugmentation_f]
  obtain ⟨u, hu, hu'⟩ : ∃ u : (CochainComplex.stupidTruncationFiltration K).filtration.obj (op p) ⟶
      HomologicalComplex₂.total
        (singleRowZero (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)))
        (ComplexShape.up ℤ),
      IsIso u ∧ ∀ n : ℤ, u.f n ≫ (HomologicalComplex₂.total.map fp (ComplexShape.up ℤ)).f n ≫
          (I.bicomplex.totalBrutalTruncStepIso p).hom.f n ≫ totalFiltration₁ι I (op p) n =
        stupidTruncationFiltrationι (K := K) (op p) n ≫ totalAugmentationf I n :=
    ⟨totalSingleRowZeroUnit (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)),
      isIso_totalSingleRowZeroUnit (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)), hcomp⟩
  have heq : filteredTotalAugmentationStep I (op p) =
      u ≫ HomologicalComplex₂.total.map fp (ComplexShape.up ℤ) ≫
        (I.bicomplex.totalBrutalTruncStepIso p).hom := by
    apply HomologicalComplex.Hom.ext
    funext n
    rw [← cancel_mono (totalFiltration₁ι I (op p) n), filteredTotalAugmentationStep_f,
      filteredTotalAugmentationStepf_ι]
    simpa only [HomologicalComplex.comp_f, Category.assoc] using (hu' n).symm
  rw [filteredTotalAugmentation_natTrans_app, heq]
  infer_instance

end StacksDraft.CartanEilenbergResolutions

end
