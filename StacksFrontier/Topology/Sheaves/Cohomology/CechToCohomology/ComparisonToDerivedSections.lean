module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.QuasiIsoToDerivedCechCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.AugmentationIsAKernel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Čech-to-derived-sections transformation for sheaves of modules

Let `(X, O)` be a ringed space, let `U` be an open subset and let `Ui` be a family of opens
with `U = ⨆ i, Ui i`.  For a sheaf of `O`-modules `F` the Čech complex `Č•(Ui, F)` of the
cover, taken in the slice over `U` so that all its terms are modules over `O(U)`, maps
canonically to the derived sections `RΓ(U, F)` in the bounded-below derived category, naturally
in `F`; applying cohomology gives the canonical maps from Čech cohomology to sheaf cohomology.

The transformation is built at an injective resolution `F ⟶ J•`.  The Čech bicomplex of `J•`
has `(q, p)` term the Čech `p`-cochains of `J^q`, and its total complex receives two
augmentations,

* `α : Γ(U, J•) ⟶ Tot(Č•(Ui, J•))`, the Čech augmentation in each resolution degree, landing
  in the `(q, 0)` corner;
* `β : Č•(Ui, F) ⟶ Tot(Č•(Ui, J•))`, the Čech complex of `F ⟶ J⁰`, landing in the `(0, p)`
  corner,

and the transformation is `Q(β) ≫ Q(α)⁻¹` followed by the identification of the sections of an
injective resolution with derived sections.

## Implementation notes

Only `α` is a quasi-isomorphism here, and only `α` has to be: the columns of the Čech bicomplex
are the Čech complexes of the injective sheaves `J^q`, whose augmented Čech complexes are exact
by [Stacks, Tag 01EP] -- the degree-zero half because a sheaf satisfies the sheaf condition for
the cover, the positive-degree half because `J^q` is injective -- so [Stacks, Tag 0133] applies
to the columns.  The *rows* are a different matter.  For presheaves of modules the Čech cochain
functors are exact, and that is what makes the companion augmentation `β` of the presheaf case,
[Stacks, Tag 01EN], a quasi-isomorphism; for sheaves of modules it
fails, because an injective resolution of sheaves is not exact on sections.  So `β` is here
only a morphism of complexes, constructed from the functoriality of the Čech complex and the
vanishing of `F ⟶ J⁰ ⟶ J¹`, and the transformation it produces is a natural transformation and
not an isomorphism.  That is all the source asserts in this generality.

Naturality in the sheaf and independence of the chosen resolution come from the same three
facts as in the presheaf case: both augmentations are natural in the resolution, the comparison
of the sections of a resolution with derived sections is natural in the resolution, and
`CategoryTheory.InjectiveResolution.desc_commutes` is an equality rather than a homotopy, so no
homotopy bookkeeping is needed.

The Čech complex is extended by zero from `ℕ` to `ℤ` and the resolution is bounded below, so
the Čech bicomplex is supported in a quadrant, its antidiagonals are finite, and the total
complex exists.

The degree-zero Čech augmentation is `Stacks.Cohomology.CechSheaf.cechAugmentation`, the
degree-zero half of [Stacks, Tag 01EP],
whose source is the module of sections at the terminal object of the slice over `U`;
`Stacks.Cohomology.CechSheaf.sectionsTerminalFunctorIso` identifies that with
`SheafOfModules.evaluation`, which is the presentation used throughout here.  The two carry the
same underlying abelian group but different `O(U)`-actions on the nose, so they are crossed
exactly once, inside `cechDegreeZeroRestriction`, and never mixed again.

## References

* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.CechSheaf
open Stacks.Cohomology.CechTotalComparison (resolutionAug resolutionAug_comp_d
  isIso_kernelLift_resolutionAug exactAt_cochainComplex resolutionMap resolutionAug_naturality
  comp_iso_inv_eq comp_inv_eq_inv_comp inducesIsoKernel_extendZeroInclusion
  isIso_kernelLift_of_mono_of_exact resolutionDerivedComparison_naturality)
open Stacks.Cohomology.HigherDirectImagePresheaf (resolutionDerivedComparison
  resolutionDerivedComparison_inv resolutionDerivedIso Q_map_resolutionSingleHom)

universe u

namespace Stacks.Cohomology.CechDerived

attribute [local instance] HasDerivedCategory.standard

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {I : Type u} (U : Opens X) (Ui : I → Opens X) (hU : U = ⨆ i, Ui i)

/-! ### The Čech complex functor in integer degrees -/

/-- The functor `sectionsPresheafFunctor U` preserves zero morphisms. -/
instance preservesZeroMorphisms_sectionsPresheafFunctor :
    (sectionsPresheafFunctor (R := O) U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The Čech complex functor `CategoryTheory.cechComplexFunctor W` preserves zero morphisms. -/
instance preservesZeroMorphisms_cechComplexFunctor {C' : Type*} [Category* C']
    [HasFiniteProducts C'] {κ : Type u} (W : κ → C') {A' : Type*} [Category* A']
    [Preadditive A'] [HasProducts.{u} A'] :
    (CategoryTheory.cechComplexFunctor W (A := A')).PreservesZeroMorphisms where
  map_zero P Q := HomologicalComplex.hom_ext _ _ fun n =>
    hom_ext W Q fun x => (cech_map_comp_π W (0 : P ⟶ Q) n x).trans (by simp)

/-- The Čech complex functor of the cover `Ui` of `U` preserves zero morphisms. -/
instance preservesZeroMorphisms_cechComplexFunctorOfCover :
    (cechComplexFunctorOfCover (R := O) U Ui hU).PreservesZeroMorphisms := by
  dsimp only [cechComplexFunctorOfCover]
  infer_instance

/-- **Evaluating a sheaf of modules on an open subset is additive.**
`SheafOfModules.evaluation` is a plain definition, so it has to be unfolded before instance
search can see the additive functors it is composed of. -/
instance additive_evaluation : (SheafOfModules.evaluation.{u} O (op U)).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- **The Čech complex functor of the cover**, at the spelling of [Stacks, Tag 01EP]. -/
def cechComplexNatFunctor :
    SheafOfModules.{u} O ⥤ CochainComplex (ModuleCat.{u} (SectionRing O U)) ℕ :=
  cechComplexFunctorOfCover.{u, u, u} (R := O) (ι := I) U Ui hU

/-- The Čech complex functor of the cover is the one of [Stacks, Tag 01EP] on the nose. -/
theorem cechComplexNatFunctor_eq :
    cechComplexNatFunctor O U Ui hU = cechComplexFunctorOfCover.{u, u, u} (R := O) U Ui hU :=
  rfl

/-- The Čech complex functor `cechComplexNatFunctor` preserves zero morphisms. -/
instance preservesZeroMorphisms_cechComplexNatFunctor :
    (cechComplexNatFunctor O U Ui hU).PreservesZeroMorphisms :=
  preservesZeroMorphisms_cechComplexFunctorOfCover O U Ui hU

/-- **The Čech complex of the cover, extended by zero from natural to integer degrees.** -/
def cechComplexIntFunctor :
    SheafOfModules.{u} O ⥤ CochainComplex (ModuleCat.{u} (SectionRing O U)) ℤ :=
  cechComplexNatFunctor O U Ui hU ⋙
    embeddingUpNat.extendFunctor (ModuleCat.{u} (SectionRing O U))

/-- The Čech complex functor in integer degrees, `cechComplexIntFunctor`, preserves zero
morphisms. -/
instance preservesZeroMorphisms_cechComplexIntFunctor :
    (cechComplexIntFunctor O U Ui hU).PreservesZeroMorphisms := by
  dsimp only [cechComplexIntFunctor]
  infer_instance

/-- **The Čech complex of the cover, as a functor to bounded-below cochain complexes.** -/
def cechComplexPlusFunctor :
    SheafOfModules.{u} O ⥤ CochainComplex.Plus (ModuleCat.{u} (SectionRing O U)) :=
  ObjectProperty.lift _ (cechComplexIntFunctor O U Ui hU) (fun F ↦ ⟨0, by
    change CochainComplex.IsStrictlyGE
      (((cechComplexNatFunctor O U Ui hU).obj F).extend embeddingUpNat) 0
    infer_instance⟩)

/-- **The restriction map from sections on the covered open to degree zero of the Čech
complex.**  It is the Čech augmentation of [Stacks, Tag 01EP], with its source read as
`SheafOfModules.evaluation`. -/
def cechDegreeZeroRestriction (F : SheafOfModules.{u} O) :
    (SheafOfModules.evaluation.{u} O (op U)).obj F ⟶
      ((cechComplexNatFunctor O U Ui hU).obj F).X 0 :=
  (sectionsTerminalFunctorIso (R := O) U).inv.app F ≫ cechAugmentation U Ui hU F

/-- **The components of the degree-zero restriction map** are the restrictions of the given
section to the opens selected by the tuples of length one. -/
theorem cechDegreeZeroRestriction_comp_π (F : SheafOfModules.{u} O) (x : Fin 1 → I) :
    cechDegreeZeroRestriction O U Ui hU F ≫ π (coverObject Ui hU) (sectionsPresheaf U F) 0 x =
      (sectionsTerminalFunctorIso (R := O) U).inv.app F ≫
        (sectionsPresheaf U F).map
          (Over.mkIdTerminal.from (inter (coverObject Ui hU) x)).op :=
  (Category.assoc _ _ _).trans
    (congrArg (fun m => (sectionsTerminalFunctorIso (R := O) U).inv.app F ≫ m)
      (cechAugmentation_comp_π U Ui hU F x))

/-- **The degree-zero restriction map, read in integer degrees.** -/
def cechAugmentationInt (F : SheafOfModules.{u} O) :
    (SheafOfModules.evaluation.{u} O (op U)).obj F ⟶
      ((cechComplexIntFunctor O U Ui hU).obj F).X 0 :=
  cechDegreeZeroRestriction O U Ui hU F ≫
    (HomologicalComplex.extendXIso _ embeddingUpNat (i := 0) rfl).inv

/-- **The double complex with `(q, p)` term the Čech `p`-cochains of `J^q`.** -/
def cechBicomplex (J : CochainComplex (SheafOfModules.{u} O) ℤ) :
    HomologicalComplex₂ (ModuleCat.{u} (SectionRing O U)) (up ℤ) (up ℤ) :=
  ((cechComplexIntFunctor O U Ui hU).mapHomologicalComplex (up ℤ)).obj J

/-! ### Vanishing and finiteness for the Čech bicomplex -/

/-- The Čech complex extended by zero to integer degrees vanishes in negative degrees. -/
lemma isZero_cechComplexIntFunctor_X (F : SheafOfModules.{u} O) (p : ℤ) (hp : p < 0) :
    IsZero (((cechComplexIntFunctor O U Ui hU).obj F).X p) := by
  dsimp only [cechComplexIntFunctor, Functor.comp_obj, Embedding.extendFunctor_obj]
  exact HomologicalComplex.isZero_extend_X _ embeddingUpNat p
    (fun i => by change ((i : ℕ) : ℤ) ≠ p; omega)

/-- A term of the Čech bicomplex vanishes if the resolved complex vanishes in that resolution
degree, or if the Čech degree is negative. -/
lemma isZero_cechBicomplex_X_X (J : CochainComplex (SheafOfModules.{u} O) ℤ) (q p : ℤ)
    (h : IsZero (J.X q) ∨ p < 0) :
    IsZero (((cechBicomplex O U Ui hU J).X q).X p) := by
  obtain h | h := h
  · exact (HomologicalComplex.eval _ _ p).map_isZero
      ((cechComplexIntFunctor O U Ui hU).map_isZero h)
  · exact isZero_cechComplexIntFunctor_X O U Ui hU (J.X q) p h

/-- **The antidiagonals of the Čech bicomplex are finite.**  Both indices are bounded below --
the Čech degree because the Čech complex is extended by zero from `ℕ`, the resolution degree
because the resolved complex is bounded below -- so only finitely many summands survive in each
total degree. -/
lemma diagonalFinite_cechBicomplex (J : CochainComplex (SheafOfModules.{u} O) ℤ) (a : ℤ)
    [J.IsStrictlyGE a] : DiagonalFinite (cechBicomplex O U Ui hU J) := by
  intro n
  refine (Set.finite_Icc a n).subset ?_
  intro q hq
  simp only [Set.mem_ofPred_eq] at hq
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hq (isZero_cechBicomplex_X_X O U Ui hU J q (n - q)
      (Or.inl (J.isZero_of_isStrictlyGE a q (by omega))))
  · by_contra h
    exact hq (isZero_cechBicomplex_X_X O U Ui hU J q (n - q) (Or.inr (by omega)))

/-- The Čech bicomplex of a complex bounded below in degree `0` has a total complex. -/
instance hasTotal_cechBicomplex (J : CochainComplex (SheafOfModules.{u} O) ℤ)
    [J.IsStrictlyGE 0] : (cechBicomplex O U Ui hU J).HasTotal (up ℤ) :=
  hasTotal_of_diagonalFinite _ (diagonalFinite_cechBicomplex O U Ui hU J 0)

/-! ### The Čech augmentation in integer degrees, as a natural transformation -/

/-- **Extension by zero is, in degree zero, the degree-zero term itself**, naturally in the
complex. -/
def extendEvalZeroIso :
    cechComplexIntFunctor O U Ui hU ⋙
        HomologicalComplex.eval (ModuleCat.{u} (SectionRing O U)) (up ℤ) (0 : ℤ) ≅
      cechComplexFunctorOfCover.{u, u, u} (R := O) (ι := I) U Ui hU ⋙
        HomologicalComplex.eval (ModuleCat.{u} (SectionRing O U)) (up ℕ) 0 :=
  Functor.isoWhiskerLeft _
    (embeddingUpNat.extendFunctorCompEvalIso (ModuleCat.{u} (SectionRing O U))
      (i := 0) (i' := (0 : ℤ)) rfl)

/-- **The degree-zero Čech augmentation in integer degrees, as a natural transformation** of
functors of the sheaf of modules. -/
def cechAugmentationIntNat :
    SheafOfModules.evaluation.{u} O (op U) ⟶
      cechComplexIntFunctor O U Ui hU ⋙
        HomologicalComplex.eval (ModuleCat.{u} (SectionRing O U)) (up ℤ) (0 : ℤ) :=
  (sectionsTerminalFunctorIso (R := O) U).inv ≫ cechAugmentationNatTrans U Ui hU ≫
    (extendEvalZeroIso O U Ui hU).inv

/-- The components of `cechAugmentationIntNat` are `cechAugmentationInt`. -/
theorem cechAugmentationIntNat_app (F : SheafOfModules.{u} O) :
    (cechAugmentationIntNat O U Ui hU).app F = cechAugmentationInt O U Ui hU F :=
  (Category.assoc _ _ _).symm

/-- **The degree-zero Čech augmentation in integer degrees is natural in the sheaf of
modules.** -/
theorem cechAugmentationInt_naturality {F G : SheafOfModules.{u} O} (f : F ⟶ G) :
    cechAugmentationInt O U Ui hU F ≫ ((cechComplexIntFunctor O U Ui hU).map f).f 0 =
      (SheafOfModules.evaluation.{u} O (op U)).map f ≫ cechAugmentationInt O U Ui hU G := by
  have h := (cechAugmentationIntNat O U Ui hU).naturality f
  rw [cechAugmentationIntNat_app, cechAugmentationIntNat_app] at h
  exact h.symm

/-! ### The hypotheses of Stacks 0133 for the column augmentation -/

/-- **The augmentation `α`**, as a morphism into the zeroth row of the Čech bicomplex: in
resolution degree `q` it is the Čech augmentation of `J^q`. -/
def cechAlphaRow (J : CochainComplex (SheafOfModules.{u} O) ℤ) :
    ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj J ⟶
      rowZero (cechBicomplex O U Ui hU J) where
  f q := cechAugmentationInt O U Ui hU (J.X q)
  comm' q q' _ := cechAugmentationInt_naturality O U Ui hU (J.d q q')

/-- The components of `cechAlphaRow`. -/
@[simp]
lemma cechAlphaRow_f (J : CochainComplex (SheafOfModules.{u} O) ℤ) (q : ℤ) :
    (cechAlphaRow O U Ui hU J).f q = cechAugmentationInt O U Ui hU (J.X q) := rfl

/-- **`cechAlphaRow` is natural in the resolved complex.** -/
lemma cechAlphaRow_naturality {J K : CochainComplex (SheafOfModules.{u} O) ℤ} (φ : J ⟶ K) :
    cechAlphaRow O U Ui hU J ≫
        rowZeroMap (((cechComplexIntFunctor O U Ui hU).mapHomologicalComplex (up ℤ)).map φ) =
      ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).map φ ≫
        cechAlphaRow O U Ui hU K :=
  HomologicalComplex.hom_ext _ _ fun q =>
    cechAugmentationInt_naturality O U Ui hU (φ.f q)

/-- **The kernel clause for an augmentation, transported to the extension by zero.**  The
extended complex has no term in degree `-1`, so nothing changes: the augmentation is still a
kernel of the first differential, up to the identifications of the two extended terms and an
isomorphism of the source. -/
lemma inducesIsoKernel_extendAugmentation {B : Type*} [Category* B] [Abelian B]
    (C : CochainComplex B ℕ) {T T' : B} (ξ : T ⟶ C.X 0) (hξ : ξ ≫ C.d 0 1 = 0) (hmono : Mono ξ)
    (hex : (ShortComplex.mk ξ (C.d 0 1) hξ).Exact) (eT : T' ≅ T)
    (h₀ : embeddingUpNat.f 0 = (0 : ℤ)) (h₁ : embeddingUpNat.f 1 = (1 : ℤ))
    (ζ : T' ⟶ (C.extend embeddingUpNat).X 0)
    (hζ : ζ = eT.hom ≫ ξ ≫ (C.extendXIso embeddingUpNat h₀).inv) :
    ∃ hα : ζ ≫ (C.extend embeddingUpNat).d 0 1 = 0,
      IsIso (kernel.lift ((C.extend embeddingUpNat).d 0 1) ζ hα) := by
  have hd : (C.extend embeddingUpNat).d 0 1 =
      (C.extendXIso embeddingUpNat h₀).hom ≫ C.d 0 1 ≫
        (C.extendXIso embeddingUpNat h₁).inv :=
    C.extend_d_eq embeddingUpNat h₀ h₁
  have hα : ζ ≫ (C.extend embeddingUpNat).d 0 1 = 0 := by
    rw [hζ, hd]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% hξ]
    simp
  refine ⟨hα, ?_⟩
  have := hmono
  have : Mono ζ := by rw [hζ]; infer_instance
  have e : ShortComplex.mk ξ (C.d 0 1) hξ ≅
      ShortComplex.mk ζ ((C.extend embeddingUpNat).d 0 1) hα :=
    ShortComplex.isoMk eT.symm (C.extendXIso embeddingUpNat h₀).symm
      (C.extendXIso embeddingUpNat h₁).symm (by simp [hζ]) (by simp [hd])
  exact isIso_kernelLift_of_mono_of_exact _ _ _ (ShortComplex.exact_of_iso e hex)

/-- **The kernel clause of Stacks 0133 for the Čech bicomplex**: in each resolution degree the
Čech augmentation is a kernel of the first Čech differential.  This is the degree-zero clause
of [Stacks, Tag 01EP]. -/
lemma inducesIsoKernel_cechAlphaRow (J : CochainComplex (SheafOfModules.{u} O) ℤ) (q : ℤ) :
    ∃ hα : (cechAlphaRow O U Ui hU J).f q ≫ ((cechBicomplex O U Ui hU J).X q).d 0 1 = 0,
      IsIso (kernel.lift (((cechBicomplex O U Ui hU J).X q).d 0 1)
        ((cechAlphaRow O U Ui hU J).f q) hα) :=
  inducesIsoKernel_extendAugmentation
    (C := (cechComplexFunctorOfCover.{u, u, u} (R := O) (ι := I) U Ui hU).obj (J.X q))
    (cechAugmentation U Ui hU (J.X q)) (cechAugmentation_comp_d U Ui hU (J.X q))
    (mono_cechAugmentation U Ui hU (J.X q)) (exact_augmentedShortComplex U Ui hU (J.X q))
    ((sectionsTerminalFunctorIso (R := O) U).app (J.X q)).symm rfl rfl
    (cechAugmentationInt O U Ui hU (J.X q)) (Category.assoc _ _ _)

/-- **The columns of the Čech bicomplex of a complex of injective sheaves are exact away from
Čech degree zero.**  In negative degree the column is supported away from it; in positive
degree this is the positive-degree clause of [Stacks, Tag 01EP], transported along the
extension by zero. -/
lemma exactAt_cechBicomplex_X (J : CochainComplex (SheafOfModules.{u} O) ℤ)
    (hinj : ∀ q, Injective (J.X q)) (q p : ℤ) (hp : p ≠ 0) :
    ((cechBicomplex O U Ui hU J).X q).ExactAt p := by
  rcases lt_trichotomy p 0 with h | h | h
  · exact HomologicalComplex.extend_exactAt _ embeddingUpNat p
      fun j => by change ((j : ℕ) : ℤ) ≠ p; omega
  · exact absurd h hp
  · have hk : embeddingUpNat.f p.toNat = p := by change ((p.toNat : ℕ) : ℤ) = p; omega
    refine (HomologicalComplex.extend_exactAt_iff _ embeddingUpNat hk).2 ?_
    have := hinj q
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_cechComplex_homology_of_injective U Ui hU (J.X q) p.toNat (by omega))

/-- **The hypotheses of Stacks 0133 for the Čech bicomplex of a bounded-below complex of
injective sheaves of modules**, with the Čech augmentation in each resolution degree. -/
theorem hypotheses_cechAlphaRow (J : CochainComplex (SheafOfModules.{u} O) ℤ)
    [J.IsStrictlyGE 0] (hinj : ∀ q, Injective (J.X q)) :
    Hypotheses
      (((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj J)
      (cechBicomplex O U Ui hU J) (cechAlphaRow O U Ui hU J) where
  diagonalFinite := diagonalFinite_cechBicomplex O U Ui hU J 0
  zero_of_neg q p hp := isZero_cechBicomplex_X_X O U Ui hU J q p (Or.inr hp)
  exactAt_of_ne_zero q p hp := exactAt_cechBicomplex_X O U Ui hU J hinj q p hp
  inducesIsoKernel q := inducesIsoKernel_cechAlphaRow O U Ui hU J q

/-! ### The two augmentations -/

/-- **The augmentation `α`**: the sections of a bounded-below complex of injective sheaves of
modules include into the total complex of its Čech bicomplex, in the `(q, 0)` corner. -/
def cechAlpha (J : CochainComplex (SheafOfModules.{u} O) ℤ) [J.IsStrictlyGE 0]
    (hinj : ∀ q, Injective (J.X q)) :
    ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj J ⟶
      (cechBicomplex O U Ui hU J).total (up ℤ) :=
  comparisonMapP _ _ _ (hypotheses_cechAlphaRow O U Ui hU J hinj)

/-- **The component formula for `α`.** -/
lemma cechAlpha_f (J : CochainComplex (SheafOfModules.{u} O) ℤ) [J.IsStrictlyGE 0]
    (hinj : ∀ q, Injective (J.X q)) (q : ℤ) :
    (cechAlpha O U Ui hU J hinj).f q = cechAugmentationInt O U Ui hU (J.X q) ≫
      (cechBicomplex O U Ui hU J).ιTotal (up ℤ) q 0 q (by simp) :=
  comparisonMapP_f _ _ _ _ q

/-- **`α` is a quasi-isomorphism**, by [Stacks, Tag 0133]: the columns of the Čech bicomplex
are the Čech complexes of the injective sheaves `J^q`, whose augmented Čech complexes are
exact. -/
instance quasiIso_cechAlpha (J : CochainComplex (SheafOfModules.{u} O) ℤ) [J.IsStrictlyGE 0]
    (hinj : ∀ q, Injective (J.X q)) : QuasiIso (cechAlpha O U Ui hU J hinj) :=
  quasiIso_comparisonMapP _ _ _ _

/-- **A morphism into the column `0` of a double complex which the first horizontal
differential kills is a morphism into the total complex.**  On the summand `(0, p)` the
differential of the total complex is `d₁ + (-1)^0 d₂` ([Stacks, Tag 012Z]); the `d₁` term dies
because the given morphism is killed by the first horizontal differential, and the `d₂` term is
the vertical differential of the column, with which the given morphism commutes. -/
def totalColumnZeroMap {A' : Type*} [Category* A'] [Preadditive A']
    (Z : HomologicalComplex₂ A' (up ℤ) (up ℤ)) [Z.HasTotal (up ℤ)]
    (W : CochainComplex A' ℤ) (g : W ⟶ Z.X 0) (hg : g ≫ Z.d 0 1 = 0) :
    W ⟶ Z.total (up ℤ) where
  f p := g.f p ≫ Z.ιTotal (up ℤ) 0 p p (by simp)
  comm' p p' hpp' := by
    obtain rfl : p + 1 = p' := hpp'
    have hg' : g.f p ≫ (Z.d 0 (0 + 1)).f p = 0 := by
      rw [show (0 : ℤ) + 1 = 1 from zero_add 1, ← HomologicalComplex.comp_f, hg,
        HomologicalComplex.zero_f]
    rw [Category.assoc, Z.ιTotal_d_up_ℤ 0 p p (by omega), Preadditive.comp_add,
      ← Category.assoc, hg', zero_comp, zero_add, Int.negOnePow_zero, one_smul,
      ← Category.assoc, g.comm p (p + 1), Category.assoc]

/-- The components of `totalColumnZeroMap`. -/
@[simp]
lemma totalColumnZeroMap_f {A' : Type*} [Category* A'] [Preadditive A']
    (Z : HomologicalComplex₂ A' (up ℤ) (up ℤ)) [Z.HasTotal (up ℤ)]
    (W : CochainComplex A' ℤ) (g : W ⟶ Z.X 0) (hg : g ≫ Z.d 0 1 = 0) (p : ℤ) :
    (totalColumnZeroMap Z W g hg).f p = g.f p ≫ Z.ιTotal (up ℤ) 0 p p (by simp) := rfl

/-- **The augmentation `β`**: the Čech complex of the resolved sheaf of modules includes into
the total complex of the Čech bicomplex of the resolution, in the `(0, p)` corner.

Unlike `α` this is only a morphism of complexes: the rows of the Čech bicomplex of an injective
resolution of sheaves of modules are not exact, since an injective resolution of sheaves need
not be exact on sections. -/
def cechBeta (J : CochainComplex (SheafOfModules.{u} O) ℤ) [J.IsStrictlyGE 0]
    {F : SheafOfModules.{u} O} (ξ : F ⟶ J.X 0) (hz : ξ ≫ J.d 0 1 = 0) :
    (cechComplexIntFunctor O U Ui hU).obj F ⟶ (cechBicomplex O U Ui hU J).total (up ℤ) :=
  totalColumnZeroMap (cechBicomplex O U Ui hU J) ((cechComplexIntFunctor O U Ui hU).obj F)
    ((cechComplexIntFunctor O U Ui hU).map ξ)
    (show (cechComplexIntFunctor O U Ui hU).map ξ ≫
        (cechComplexIntFunctor O U Ui hU).map (J.d 0 1) = 0 from
      ((cechComplexIntFunctor O U Ui hU).map_comp ξ (J.d 0 1)).symm.trans
        ((congrArg (cechComplexIntFunctor O U Ui hU).map hz).trans
          ((cechComplexIntFunctor O U Ui hU).map_zero _ _)))

/-- **The component formula for `β`.** -/
lemma cechBeta_f (J : CochainComplex (SheafOfModules.{u} O) ℤ) [J.IsStrictlyGE 0]
    {F : SheafOfModules.{u} O} (ξ : F ⟶ J.X 0) (hz : ξ ≫ J.d 0 1 = 0) (p : ℤ) :
    (cechBeta O U Ui hU J ξ hz).f p = ((cechComplexIntFunctor O U Ui hU).map ξ).f p ≫
      (cechBicomplex O U Ui hU J).ιTotal (up ℤ) 0 p p (by simp) := rfl


/-! ### Both augmentations are natural in the resolution -/

/-- The map of Čech bicomplexes induced by a morphism of complexes of sheaves of modules. -/
def cechBicomplexMap {J J' : CochainComplex (SheafOfModules.{u} O) ℤ} (φ : J ⟶ J') :
    cechBicomplex O U Ui hU J ⟶ cechBicomplex O U Ui hU J' :=
  ((cechComplexIntFunctor O U Ui hU).mapHomologicalComplex (up ℤ)).map φ

/-- The induced map of total complexes. -/
def cechTotalMap {J J' : CochainComplex (SheafOfModules.{u} O) ℤ} [J.IsStrictlyGE 0]
    [J'.IsStrictlyGE 0] (φ : J ⟶ J') :
    (cechBicomplex O U Ui hU J).total (up ℤ) ⟶ (cechBicomplex O U Ui hU J').total (up ℤ) :=
  HomologicalComplex₂.total.map (cechBicomplexMap O U Ui hU φ) (up ℤ)

/-- **The inclusion of a summand commutes with the induced map of total complexes.** -/
lemma ιTotal_comp_cechTotalMap {J J' : CochainComplex (SheafOfModules.{u} O) ℤ}
    [J.IsStrictlyGE 0] [J'.IsStrictlyGE 0] (φ : J ⟶ J') (q p n : ℤ) (h : q + p = n) :
    (cechBicomplex O U Ui hU J).ιTotal (up ℤ) q p n h ≫ (cechTotalMap O U Ui hU φ).f n =
      ((cechComplexIntFunctor O U Ui hU).map (φ.f q)).f p ≫
        (cechBicomplex O U Ui hU J').ιTotal (up ℤ) q p n h :=
  HomologicalComplex₂.ιTotal_map _ _ (cechBicomplexMap O U Ui hU φ) (up ℤ) q p n h

/-- **Naturality of a summand inclusion into the total complex**: a morphism into a summand
`(q, p)` which is natural for the induced map of Čech bicomplexes is natural for the induced map
of total complexes. -/
private lemma comp_ιTotal_comp_cechTotalMap {J J' : CochainComplex (SheafOfModules.{u} O) ℤ}
    [J.IsStrictlyGE 0] [J'.IsStrictlyGE 0] (φ : J ⟶ J') (q p n : ℤ) (h : q + p = n)
    {A B : ModuleCat.{u} (SectionRing O U)} (a : A ⟶ ((cechBicomplex O U Ui hU J).X q).X p)
    (b : B ⟶ ((cechBicomplex O U Ui hU J').X q).X p) (c : A ⟶ B)
    (hab : a ≫ ((cechComplexIntFunctor O U Ui hU).map (φ.f q)).f p = c ≫ b) :
    (a ≫ (cechBicomplex O U Ui hU J).ιTotal (up ℤ) q p n h) ≫ (cechTotalMap O U Ui hU φ).f n =
      c ≫ b ≫ (cechBicomplex O U Ui hU J').ιTotal (up ℤ) q p n h := by
  rw [Category.assoc, ιTotal_comp_cechTotalMap]
  exact (Category.assoc _ _ _).symm.trans (((congrArg (· ≫ _) hab)).trans (Category.assoc _ _ _))

/-- **`α` is natural in the resolved complex.**  Its components are the Čech augmentation,
which is natural, so the square is that naturality read inside the `(q, 0)` summand of the
total complex. -/
lemma cechAlpha_comp_cechTotalMap (J J' : CochainComplex (SheafOfModules.{u} O) ℤ)
    [J.IsStrictlyGE 0] [J'.IsStrictlyGE 0] (hinj : ∀ q, Injective (J.X q))
    (hinj' : ∀ q, Injective (J'.X q)) (φ : J ⟶ J') :
    cechAlpha O U Ui hU J hinj ≫ cechTotalMap O U Ui hU φ =
      ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).map φ ≫
        cechAlpha O U Ui hU J' hinj' :=
  HomologicalComplex.hom_ext _ _ fun q => by
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, cechAlpha_f, cechAlpha_f]
    exact comp_ιTotal_comp_cechTotalMap O U Ui hU φ q 0 q _ _ _ _
      (cechAugmentationInt_naturality O U Ui hU (φ.f q))

/-- **`β` is natural in the resolution**, over any morphism of sheaves of modules compatible
with the two augmentations.  Its components are the Čech cochains of the augmentation, so the
square is the image under the Čech complex functor of the compatibility `hξ`, read inside the
`(0, p)` summand of the total complex. -/
lemma cechBeta_comp_cechTotalMap (J J' : CochainComplex (SheafOfModules.{u} O) ℤ)
    [J.IsStrictlyGE 0] [J'.IsStrictlyGE 0] {F G : SheafOfModules.{u} O} (f : F ⟶ G)
    (ξ : F ⟶ J.X 0) (hz : ξ ≫ J.d 0 1 = 0) (ξ' : G ⟶ J'.X 0) (hz' : ξ' ≫ J'.d 0 1 = 0)
    (φ : J ⟶ J') (hξ : ξ ≫ φ.f 0 = f ≫ ξ') :
    cechBeta O U Ui hU J ξ hz ≫ cechTotalMap O U Ui hU φ =
      (cechComplexIntFunctor O U Ui hU).map f ≫ cechBeta O U Ui hU J' ξ' hz' :=
  HomologicalComplex.hom_ext _ _ fun p => by
    have hcomp : ((cechComplexIntFunctor O U Ui hU).map ξ).f p ≫
          ((cechComplexIntFunctor O U Ui hU).map (φ.f 0)).f p =
        ((cechComplexIntFunctor O U Ui hU).map f).f p ≫
          ((cechComplexIntFunctor O U Ui hU).map ξ').f p := by
      rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← Functor.map_comp,
        ← Functor.map_comp, hξ]
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, cechBeta_f, cechBeta_f]
    exact comp_ιTotal_comp_cechTotalMap O U Ui hU φ 0 p p _ _ _ _ hcomp


/-! ### Derived global sections -/

section Derived

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)]

/-- **The bounded-below derived global-sections functor `RΓ(U, -)`.** -/
def derivedGlobalSectionsFunctor :
    SheafOfModules.{u} O ⥤ DerivedCategory.Plus (ModuleCat.{u} (SectionRing O U)) :=
  DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} O) 0 ⋙
    (SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus

/-- **An injective resolution identifies a sheaf of modules in degree zero with its
resolution** in the bounded-below derived category. -/
def injectiveResolutionIso (F : SheafOfModules.{u} O) (J : InjectiveResolution F) :
    (DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} O) 0).obj F ≅
      DerivedCategory.Plus.Q.obj ⟨J.cochainComplex, 0, inferInstance⟩ :=
  ObjectProperty.isoMk _ (@asIso _ _ _ _ (DerivedCategory.Q.map J.ι')
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ J.ι').2 inferInstance))

/-- **The canonical identification of the sections of an injective resolution with derived
sections**, using the unit of the right derived functor and the resolution
quasi-isomorphism. -/
def injectiveResolutionToDerivedGlobalSections (F : SheafOfModules.{u} O)
    (J : InjectiveResolution F) :
    DerivedCategory.Q.obj
      (((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj
        J.cochainComplex) ⟶ ((derivedGlobalSectionsFunctor O U).obj F).obj :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
  ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlusUnith.app
    ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} O)).obj
      ⟨J.cochainComplex, 0, inferInstance⟩)).hom ≫
  ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus.map
    (ObjectProperty.homMk ((DerivedCategory.quotientCompQhIso _).hom.app
      J.cochainComplex))).hom ≫
  ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus.mapIso
    (injectiveResolutionIso O F J)).inv.hom

/-- **The injective-resolution specification of a Čech-to-derived-sections transformation.**
The two chain maps have the prescribed restriction and resolution components; the first becomes
invertible, and their quotient is the specified transformation. -/
structure CechResolutionComparison
    (τ : cechComplexPlusFunctor O U Ui hU ⋙ DerivedCategory.Plus.Q ⟶
      derivedGlobalSectionsFunctor O U) (F : SheafOfModules.{u} O)
    (J : InjectiveResolution F) where
  /-- The augmentation from sections of the resolution to its total Čech complex. -/
  α : ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj
      J.cochainComplex ⟶ (cechBicomplex O U Ui hU J.cochainComplex).total (up ℤ)
  /-- The map induced by the inclusion of the sheaf into its resolution. -/
  β : (cechComplexIntFunctor O U Ui hU).obj F ⟶
      (cechBicomplex O U Ui hU J.cochainComplex).total (up ℤ)
  /-- The first map is given by restriction of sections in each resolution degree. -/
  α_f (q : ℤ) : α.f q = cechAugmentationInt O U Ui hU (J.cochainComplex.X q) ≫
    (cechBicomplex O U Ui hU J.cochainComplex).ιTotal (up ℤ) q 0 q (by simp)
  /-- The second map is induced by `F ⟶ J⁰` in each Čech degree. -/
  β_f (p : ℤ) : β.f p =
    ((cechComplexIntFunctor O U Ui hU).map
      ((HomologicalComplex.singleObjXSelf (up ℤ) 0 F).inv ≫ J.ι'.f 0)).f p ≫
    (cechBicomplex O U Ui hU J.cochainComplex).ιTotal (up ℤ) 0 p p (by simp)
  /-- The augmentation becomes an isomorphism in the derived category. -/
  αIso : DerivedCategory.Q.obj
      (((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj
        J.cochainComplex) ≅
      DerivedCategory.Q.obj ((cechBicomplex O U Ui hU J.cochainComplex).total (up ℤ))
  /-- This is the isomorphism induced by `α`, not an arbitrary identification. -/
  αIso_hom : αIso.hom = DerivedCategory.Q.map α
  /-- The comparison is `β` followed by the inverse of `α` and the canonical identification
  with derived sections. -/
  comparison : (τ.app F).hom = DerivedCategory.Q.map β ≫ αIso.inv ≫
    injectiveResolutionToDerivedGlobalSections O U F J

/-! ### The two augmentations at an injective resolution -/

section Resolution

variable {F : SheafOfModules.{u} O} (J : InjectiveResolution F)

/-- **The augmentation `α` at an injective resolution.** -/
def cechAlphaRes :
    ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj
        J.cochainComplex ⟶
      (cechBicomplex O U Ui hU J.cochainComplex).total (up ℤ) :=
  cechAlpha O U Ui hU J.cochainComplex (fun _ => inferInstance)

/-- The augmentation `cechAlphaRes` at an injective resolution is a quasi-isomorphism. -/
instance quasiIso_cechAlphaRes : QuasiIso (cechAlphaRes O U Ui hU J) :=
  quasiIso_cechAlpha O U Ui hU J.cochainComplex (fun _ => inferInstance)

/-- **The augmentation `β` at an injective resolution.** -/
def cechBetaRes :
    (cechComplexIntFunctor O U Ui hU).obj F ⟶
      (cechBicomplex O U Ui hU J.cochainComplex).total (up ℤ) :=
  cechBeta O U Ui hU J.cochainComplex (resolutionAug J) (resolutionAug_comp_d J)

/-- The identification of `Qh ∘ quotient` with `Q` at an injective resolution, read in the
bounded-below derived category. -/
def resolutionQhQ :
    DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} O)).obj
          ⟨J.cochainComplex, 0, inferInstance⟩) ⟶
      DerivedCategory.Plus.Q.obj
        (⟨J.cochainComplex, 0, inferInstance⟩ : CochainComplex.Plus (SheafOfModules.{u} O)) :=
  ObjectProperty.homMk
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)).hom.app J.cochainComplex)

omit [EnoughInjectives (SheafOfModules.{u} O)] in
/-- **The two comparisons of `F` with its injective resolution agree.**  The one used here,
`injectiveResolutionIso`, is the image under `DerivedCategory.Q` of the augmentation; the one
used by the comparison with the right derived functor is built in the homotopy category and
lands in `Qh ∘ quotient`.  They differ exactly by `resolutionQhQ`. -/
lemma resolutionDerivedIso_hom_comp :
    (resolutionDerivedIso J).hom ≫ resolutionQhQ O J =
      (injectiveResolutionIso O F J).hom :=
  DerivedCategory.Plus.ι.map_injective
    ((DerivedCategory.Plus.ι.map_comp _ _).trans (Q_map_resolutionSingleHom J))

omit [EnoughInjectives (SheafOfModules.{u} O)] in
/-- The inverse form of `resolutionDerivedIso_hom_comp`. -/
lemma resolutionDerivedIso_inv_eq :
    (resolutionDerivedIso J).inv =
      resolutionQhQ O J ≫ (injectiveResolutionIso O F J).inv :=
  (Iso.eq_comp_inv (injectiveResolutionIso O F J)).2
    ((congrArg (fun φ => (resolutionDerivedIso J).inv ≫ φ)
        (resolutionDerivedIso_hom_comp O J).symm).trans
      (Iso.inv_hom_id_assoc (resolutionDerivedIso J) (resolutionQhQ O J)))

/-- **The identification of the sections of an injective resolution with derived sections is
the inverse of `resolutionDerivedComparison`.**  Both are the same composite; the only
difference is which of the two spellings of the comparison of `F` with its resolution is
used. -/
lemma injectiveResolutionToDerivedGlobalSections_eq :
    injectiveResolutionToDerivedGlobalSections O U F J =
      (resolutionDerivedComparison (SheafOfModules.evaluation.{u} O (op U)) J).inv := by
  have step : (SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus.map
        (resolutionQhQ O J) ≫
      ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus.mapIso
        (injectiveResolutionIso O F J)).inv =
      (SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus.map
        (resolutionDerivedIso J).inv := by
    rw [Functor.mapIso_inv, ← Functor.map_comp, ← resolutionDerivedIso_inv_eq O J]
    rfl
  have h2 := congrArg (fun φ => DerivedCategory.Plus.ι.map φ) step
  rw [resolutionDerivedComparison_inv]
  exact whisker_eq _ (whisker_eq _ h2)

/-- **The identification of the sections of an injective resolution with derived sections is an
isomorphism**, being the inverse of one. -/
instance isIso_injectiveResolutionToDerivedGlobalSections :
    IsIso (injectiveResolutionToDerivedGlobalSections O U F J) := by
  rw [injectiveResolutionToDerivedGlobalSections_eq O U J]
  exact ⟨(resolutionDerivedComparison (SheafOfModules.evaluation.{u} O (op U)) J).hom,
    Iso.inv_hom_id _, Iso.hom_inv_id _⟩

end Resolution

/-! ### The comparison, natural in the sheaf and independent of the resolution -/

section Comparison

variable {F G : SheafOfModules.{u} O} (f : F ⟶ G) (JF : InjectiveResolution F)
  (JG : InjectiveResolution G)

/-- The image of the augmentation `cechAlphaRes` in the derived category is an isomorphism. -/
instance isIso_Q_map_cechAlphaRes {F : SheafOfModules.{u} O} (J : InjectiveResolution F) :
    IsIso (DerivedCategory.Q.map (cechAlphaRes O U Ui hU J)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ (cechAlphaRes O U Ui hU J)).2 inferInstance

/-- **The identification of the sections of a resolution with derived sections is natural in
the resolution.** -/
lemma Q_map_comp_injectiveResolutionToDerivedGlobalSections :
    DerivedCategory.Q.map
        (((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).map
          (resolutionMap f JF JG)) ≫
      injectiveResolutionToDerivedGlobalSections O U G JG =
      injectiveResolutionToDerivedGlobalSections O U F JF ≫
        DerivedCategory.Plus.ι.map
          ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} O) 0).map f)) :=
  (congrArg (fun m => DerivedCategory.Q.map
      (((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).map
        (resolutionMap f JF JG)) ≫ m)
    (injectiveResolutionToDerivedGlobalSections_eq O U JG)).trans
    ((comp_iso_inv_eq _ _ _ _
        (resolutionDerivedComparison_naturality (SheafOfModules.evaluation.{u} O (op U)) f JF JG
          (InjectiveResolution.desc f JG JF)
          (InjectiveResolution.desc_commutes f JG JF).symm)).trans
      (congrArg (fun m => m ≫ DerivedCategory.Plus.ι.map
          ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} O) 0).map f)))
        (injectiveResolutionToDerivedGlobalSections_eq O U JF).symm))

/-- **The comparison at a chosen injective resolution**: `Q(β) ≫ Q(α)⁻¹` followed by the
identification of the sections of the resolution with derived sections. -/
def cechComparison {F : SheafOfModules.{u} O} (J : InjectiveResolution F) :
    DerivedCategory.Q.obj ((cechComplexIntFunctor O U Ui hU).obj F) ⟶
      ((derivedGlobalSectionsFunctor O U).obj F).obj :=
  DerivedCategory.Q.map (cechBetaRes O U Ui hU J) ≫
    inv (DerivedCategory.Q.map (cechAlphaRes O U Ui hU J)) ≫
    injectiveResolutionToDerivedGlobalSections O U F J

/-- **The comparison is natural in the sheaf of modules.**  Both augmentations are natural in
the resolution and the identification with derived sections is too, so the composite is. -/
lemma cechComparison_naturality :
    DerivedCategory.Q.map ((cechComplexIntFunctor O U Ui hU).map f) ≫
        cechComparison O U Ui hU JG =
      cechComparison O U Ui hU JF ≫ DerivedCategory.Plus.ι.map
        ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor (SheafOfModules.{u} O) 0).map f)) := by
  have hβ : cechBetaRes O U Ui hU JF ≫ cechTotalMap O U Ui hU (resolutionMap f JF JG) =
      (cechComplexIntFunctor O U Ui hU).map f ≫ cechBetaRes O U Ui hU JG :=
    cechBeta_comp_cechTotalMap O U Ui hU JF.cochainComplex JG.cochainComplex f
      (resolutionAug JF) (resolutionAug_comp_d JF) (resolutionAug JG) (resolutionAug_comp_d JG)
      (resolutionMap f JF JG) (resolutionAug_naturality f JF JG)
  have hα : cechAlphaRes O U Ui hU JF ≫ cechTotalMap O U Ui hU (resolutionMap f JF JG) =
      ((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).map
        (resolutionMap f JF JG) ≫ cechAlphaRes O U Ui hU JG :=
    cechAlpha_comp_cechTotalMap O U Ui hU JF.cochainComplex JG.cochainComplex
      (fun _ => inferInstance) (fun _ => inferInstance) (resolutionMap f JF JG)
  have hQα : DerivedCategory.Q.map (cechAlphaRes O U Ui hU JF) ≫
      DerivedCategory.Q.map (cechTotalMap O U Ui hU (resolutionMap f JF JG)) =
      DerivedCategory.Q.map
          (((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).map
            (resolutionMap f JF JG)) ≫
        DerivedCategory.Q.map (cechAlphaRes O U Ui hU JG) :=
    by rw [← Functor.map_comp, ← Functor.map_comp, hα]
  have hconj := comp_inv_eq_inv_comp
    (DerivedCategory.Q.map (cechAlphaRes O U Ui hU JF))
    (DerivedCategory.Q.map (cechTotalMap O U Ui hU (resolutionMap f JF JG)))
    (DerivedCategory.Q.map
      (((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).map
        (resolutionMap f JF JG)))
    (DerivedCategory.Q.map (cechAlphaRes O U Ui hU JG)) hQα
  dsimp only [cechComparison]
  rw [← Category.assoc (DerivedCategory.Q.map ((cechComplexIntFunctor O U Ui hU).map f)),
    ← Functor.map_comp, ← hβ, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hconj,
    Q_map_comp_injectiveResolutionToDerivedGlobalSections O U f JF JG]
  rfl

/-- **The comparison does not depend on the chosen resolution**, being natural over the
identity. -/
lemma cechComparison_eq {F : SheafOfModules.{u} O} (J J' : InjectiveResolution F) :
    cechComparison O U Ui hU J = cechComparison O U Ui hU J' := by
  have h := cechComparison_naturality O U Ui hU (𝟙 F) J J'
  simp only [CategoryTheory.Functor.map_id] at h
  simp only [Category.id_comp] at h
  exact (Category.comp_id _).symm.trans h.symm

end Comparison

/-! ### The three clauses -/

/-- **The canonical natural transformation from the Čech complex of an open cover to derived
global sections on the covered open.**

It is built at an injective resolution chosen for each sheaf of modules; it is natural because
the two augmentations and the identification of the sections of a resolution with derived
sections are each natural in the resolution. -/
@[stacks 01EQ "the derived transformation", ega "0 12.1.2" "A-linear Č^p → H^p maps"]
def cechToDerivedGlobalSections :
    cechComplexPlusFunctor O U Ui hU ⋙ DerivedCategory.Plus.Q ⟶
      derivedGlobalSectionsFunctor O U where
  app F := ObjectProperty.homMk (cechComparison O U Ui hU (InjectiveResolution.of F))
  naturality _ _ f := ObjectProperty.hom_ext _
    (cechComparison_naturality O U Ui hU f (InjectiveResolution.of _)
      (InjectiveResolution.of _))

/-- **The canonical maps from Čech cohomology to sheaf cohomology**, natural in the sheaf of
modules. -/
@[stacks 01EQ "the induced cohomology maps", ega "0 12.1.2" "A-linear Ȟ^p → H^p"]
def cechCohomologyToCohomology (p : ℤ) :
    (cechComplexPlusFunctor O U Ui hU ⋙ DerivedCategory.Plus.Q ⋙
        DerivedCategory.Plus.homologyFunctor _ p) ⟶
      (derivedGlobalSectionsFunctor O U ⋙
        DerivedCategory.Plus.homologyFunctor _ p) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (cechToDerivedGlobalSections O U Ui hU) _

/-- **For every injective resolution, the canonical comparison is the map prescribed by the
total Čech complex construction.**  In particular it is independent of the resolution. -/
@[stacks 01EQ "the injective-resolution specification"]
theorem nonempty_cechResolutionComparison (F : SheafOfModules.{u} O)
    (J : InjectiveResolution F) :
    Nonempty (CechResolutionComparison O U Ui hU
      (cechToDerivedGlobalSections O U Ui hU) F J) :=
  ⟨{ α := cechAlphaRes O U Ui hU J
     β := cechBetaRes O U Ui hU J
     α_f q := cechAlpha_f O U Ui hU J.cochainComplex (fun _ => inferInstance) q
     β_f p := cechBeta_f O U Ui hU J.cochainComplex (resolutionAug J)
       (resolutionAug_comp_d J) p
     αIso := asIso (DerivedCategory.Q.map (cechAlphaRes O U Ui hU J))
     αIso_hom := rfl
     comparison := cechComparison_eq O U Ui hU (InjectiveResolution.of F) J }⟩

end Derived

end Stacks.Cohomology.CechDerived

end
