module

public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveResolutionDerived
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalCoverModules

/-!
# The Čech complex of a family covering the final object computes derived global sections

Let `C` be a site, `R` a sheaf of rings, `A` a ring with a ring map `φ : A ⟶ Γ(C, R)`, and
`D : ι → C` a family of objects covering the final object all of whose finite nonempty products
`D_x` exist. For a sheaf of `R`-modules `N` this file constructs the comparison

`Č(D, N) ⟶ RΓ(C, N)`

in the bounded below derived category of `A`-modules, naturally in `N`
(`cechToDerivedGlobalSections`), and proves that it is an isomorphism as soon as the higher
cohomology of `N` vanishes on every `D_x` (`isIso_cechToDerivedGlobalSections_app`). This is the
form of [Stacks, Tag 03F7] for a covering of the final object, at module coefficients; the
covering-of-an-object form at abelian coefficients is
`Stacks.CechSite.Acyclic.isIso_cechToDerivedSections_app`.

## The construction

For an injective resolution `N ⟶ I^•`, form the Čech double complex `Č(D, I^•)` and its total
complex. There are two maps into it:

* `α : Γ(C, I^•) ⟶ Tot Č(D, I^•)`, restricting global sections into the degree zero Čech term. It
  is a quasi-isomorphism for every `N`, by [Stacks, Tag 0133]: the columns are the augmented Čech
  complexes of the injective sheaves `I^q`, exact by
  `Stacks.CechSite.FinalCover.isZero_homology_cechFunctor_of_injective` and the sheaf condition
  `Stacks.CechSite.FinalCover.isLimit_augmentationFork`.
* `β : Č(D, N) ⟶ Tot Č(D, I^•)`, the Čech complex of `N ⟶ I^0`. It is a quasi-isomorphism when
  `N` is acyclic on the `D_x`, again by [Stacks, Tag 0133], now for the rows:
  `Stacks.CechSite.FinalCover.exactAt_cechTerm_cochainComplex`.

The comparison is `Q(β) ≫ Q(α)⁻¹` followed by the identification of `Γ(C, I^•)` with `RΓ(C, N)`.
The map `α` is taken to be `StacksDraft.TotalComplexQuasiIso.comparisonMapP`, the data form of
[Stacks, Tag 0133], so that its naturality is a lemma rather than a choice.

## Main definitions

All of this lives in the namespace `Stacks.CechSite.FinalCover`.

* `cechIntFunctor`, `cechPlusFunctor`, `cechDerivedFunctor` — the Čech complex, extended by zero to
  integer degrees, as a bounded below complex, and in `D⁺(A)`.
* `derivedGlobalSectionsFunctor` — `N ↦ RΓ(C, N)` in `D⁺(A)`.
* `totalAugmentation`, `cechToTotal` — the maps `α` and `β`.
* `cechComparison` — the comparison computed through a chosen injective resolution.
* `cechToDerivedGlobalSections` — the natural transformation `Č(D, -) ⟶ RΓ(C, -)`.

## Main results

* `cechComparison_naturality`, `cechComparison_eq` — the comparison is natural and does not depend
  on the resolution.
* `isIso_cechToDerivedGlobalSections_app` — **the comparison is an isomorphism at a sheaf of
  modules acyclic on every `D_x`.**
* `cechDerivedIso` — the resulting isomorphism `Č(D, N) ≅ RΓ(C, N)`.

## References

* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ComplexShape
open Stacks.Cohomology.SiteModules StacksDraft.TotalComplexQuasiIso

universe w v u r uA

namespace Stacks.CechSite.FinalCover

attribute [local instance high] hasProducts_moduleCat

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})
  {A : Type uA} [Ring A] (φ : A →+* GlobalSectionRing R) {ι : Type w} (D : ι → C)
  [∀ (n : ℕ) (x : Fin (n + 1) → ι), HasProduct (fun a ↦ D (x a))]
  [HasSheafify J AddCommGrpCat.{max u v w}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-! ### The Čech complex in integer degrees -/

/-- The Čech complex, extended by zero to integer degrees. -/
abbrev cechIntFunctor :
    SheafOfModules.{max u v w} R ⥤ CochainComplex (ModuleCat.{max u v w} A) ℤ :=
  cechFunctor R φ D ⋙ ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{max u v w} A)

/-- The integer-graded Čech complex functor preserves zero morphisms. -/
instance cechIntFunctor_preservesZeroMorphisms :
    (cechIntFunctor R φ D).PreservesZeroMorphisms := by
  dsimp only [cechIntFunctor]
  infer_instance

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The integer-graded Čech complex vanishes in negative degrees. -/
lemma isZero_cechIntFunctor_X (N : SheafOfModules.{max u v w} R) (p : ℤ) (hp : p < 0) :
    IsZero (((cechIntFunctor R φ D).obj N).X p) :=
  HomologicalComplex.isZero_extend_X _ _ p (fun i hi ↦ by
    change (i : ℤ) = p at hi
    omega)

/-- The integer-graded Čech complex is strictly bounded below by `0`. -/
instance isStrictlyGE_cechIntFunctor_obj (N : SheafOfModules.{max u v w} R) :
    ((cechIntFunctor R φ D).obj N).IsStrictlyGE 0 := by
  change CochainComplex.IsStrictlyGE
    (((cechFunctor R φ D).obj N).extend ComplexShape.embeddingUpNat) 0
  infer_instance

/-- The Čech complex as a bounded below complex. -/
def cechPlusFunctor :
    SheafOfModules.{max u v w} R ⥤ CochainComplex.Plus (ModuleCat.{max u v w} A) :=
  ObjectProperty.lift _ (cechIntFunctor R φ D) (fun _ ↦ ⟨0, inferInstance⟩)

/-- The degree-`p` term of the integer-graded Čech complex, for `p` the image of `m : ℕ`. -/
def cechIntXIso (N : SheafOfModules.{max u v w} R) (m : ℕ) (p : ℤ)
    (h : ComplexShape.embeddingUpNat.f m = p) :
    ((cechIntFunctor R φ D).obj N).X p ≅ ((cechFunctor R φ D).obj N).X m :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat h

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The differential of the integer-graded Čech complex in nonnegative degrees. -/
lemma cechIntFunctor_d (N : SheafOfModules.{max u v w} R) (m : ℕ) (p q : ℤ)
    (hp : ComplexShape.embeddingUpNat.f m = p) (hq : ComplexShape.embeddingUpNat.f (m + 1) = q) :
    ((cechIntFunctor R φ D).obj N).d p q =
      (cechIntXIso R φ D N m p hp).hom ≫ ((cechFunctor R φ D).obj N).d m (m + 1) ≫
        (cechIntXIso R φ D N (m + 1) q hq).inv :=
  HomologicalComplex.extend_d_eq _ _ hp hq

omit [HasSheafify J AddCommGrpCat.{max u v w}] in
  omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
  /-- The integer-graded Čech map in nonnegative degrees, in terms of the Čech map. -/
  private lemma cechIntFunctor_map_f {N N' : SheafOfModules.{max u v w} R} (f : N ⟶ N') (m : ℕ)
    (p : ℤ) (hp : ComplexShape.embeddingUpNat.f m = p) :
    ((cechIntFunctor R φ D).map f).f p =
      (cechIntXIso R φ D N m p hp).hom ≫ ((cechFunctor R φ D).map f).f m ≫
        (cechIntXIso R φ D N' m p hp).inv :=
  HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat hp

/-- In a degree in the range of the embedding, the integer-graded Čech complex is the Čech term
functor of that degree. -/
def cechEvalIso (i : ℕ) :
    cechIntFunctor R φ D ⋙ HomologicalComplex.eval _ (up ℤ) (i : ℤ) ≅ cechTermFunctor R φ D i :=
  NatIso.ofComponents (fun N ↦ cechIntXIso R φ D N i (i : ℤ) (ComplexShape.embeddingUpNat_f i))
    (fun {_ _} f ↦ Stacks.CechSite.Acyclic.extendXIso_naturality
      ((cechFunctor R φ D).map f) (ComplexShape.embeddingUpNat_f i))

/-- The augmentation in the integer grading. -/
def augmentationInt (N : SheafOfModules.{max u v w} R) :
    (baseGlobalSections R φ).obj N ⟶ ((cechIntFunctor R φ D).obj N).X 0 :=
  (augmentation R φ D).app N ≫ (cechIntXIso R φ D N 0 0 rfl).inv

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The integer-graded augmentation is natural. -/
@[reassoc]
lemma augmentationInt_naturality {N N' : SheafOfModules.{max u v w} R} (f : N ⟶ N') :
    augmentationInt R φ D N ≫ ((cechIntFunctor R φ D).map f).f 0 =
      (baseGlobalSections R φ).map f ≫ augmentationInt R φ D N' := by
  dsimp only [augmentationInt]
  rw [cechIntFunctor_map_f R φ D f 0 0 rfl, Category.assoc, Iso.inv_hom_id_assoc,
    ← Category.assoc]
  exact (congrArg (· ≫ (cechIntXIso R φ D N' 0 0 rfl).inv)
    ((augmentation R φ D).naturality f).symm).trans (Category.assoc _ _ _)

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The integer-graded augmentation lands in the kernel of the first differential. -/
@[reassoc (attr := simp)]
lemma augmentationInt_comp_d (N : SheafOfModules.{max u v w} R) :
    augmentationInt R φ D N ≫ ((cechIntFunctor R φ D).obj N).d 0 1 = 0 := by
  rw [cechIntFunctor_d R φ D N 0 0 1 rfl rfl]
  dsimp only [augmentationInt]
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, augmentation_app_comp_d, zero_comp]

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- **The sheaf condition in Čech form, integer grading**: for a family covering the final
object, the augmentation is a kernel of the first differential. -/
lemma isIso_kernelLift_augmentationInt (hD : J.CoversTop D) (N : SheafOfModules.{max u v w} R) :
    IsIso (kernel.lift (((cechIntFunctor R φ D).obj N).d 0 1) (augmentationInt R φ D N)
      (augmentationInt_comp_d R φ D N)) := by
  obtain ⟨hl⟩ := isLimit_augmentationFork R φ D hD N
  let S₁ := ShortComplex.mk ((augmentation R φ D).app N) (((cechFunctor R φ D).obj N).d 0 1)
    (augmentation_app_comp_d R φ D N)
  let S₂ := ShortComplex.mk (augmentationInt R φ D N) (((cechIntFunctor R φ D).obj N).d 0 1)
    (augmentationInt_comp_d R φ D N)
  let e : S₁ ≅ S₂ := ShortComplex.isoMk (Iso.refl _) (cechIntXIso R φ D N 0 0 rfl).symm
    (cechIntXIso R φ D N 1 1 rfl).symm (by simp [S₁, S₂, augmentationInt])
    (by
      simp only [S₁, S₂, Iso.symm_hom]
      rw [cechIntFunctor_d R φ D N 0 0 1 rfl rfl, Iso.inv_hom_id_assoc])
  obtain ⟨hl'⟩ := (ShortComplex.exact_and_mono_f_iff_f_is_kernel S₂).1
    ((ShortComplex.exact_and_mono_f_iff_of_iso e).1
      ((ShortComplex.exact_and_mono_f_iff_f_is_kernel S₁).2 ⟨hl⟩))
  exact isIso_kernelLift_of_isLimit _ _ _ hl'

/-- The integer-graded Čech complex of an injective sheaf of modules is exact away from degree
zero. -/
lemma exactAt_cechIntFunctor_of_injective (I : SheafOfModules.{max u v w} R)
    [Injective I] (p : ℤ) (hp : p ≠ 0) : ((cechIntFunctor R φ D).obj I).ExactAt p := by
  rcases lt_trichotomy p 0 with h | h | h
  · exact HomologicalComplex.ExactAt.of_isZero (isZero_cechIntFunctor_X R φ D I p h)
  · exact absurd h hp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = p := ⟨p.toNat, by omega⟩
    refine (HomologicalComplex.extend_exactAt_iff ((cechFunctor R φ D).obj I)
      ComplexShape.embeddingUpNat (j := m) (j' := (m : ℤ)) rfl).2 ?_
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact isZero_homology_cechFunctor_of_injective R φ D I m (by omega)

/-! ### The Čech double complex -/

section Bicomplex

/-- **The Čech double complex `Č(D, L^•)`** of a complex of sheaves of modules, resolution degree
first and Čech degree second. -/
abbrev cechBicomplex (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ) :
    HomologicalComplex₂ (ModuleCat.{max u v w} A) (up ℤ) (up ℤ) :=
  ((cechIntFunctor R φ D).mapHomologicalComplex (up ℤ)).obj L

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- A term of the Čech double complex vanishes as soon as its resolution-degree term does, and
in every negative Čech degree. -/
lemma isZero_cechBicomplex_X_X (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ) (q p : ℤ)
    (h : IsZero (L.X q) ∨ p < 0) : IsZero (((cechBicomplex R φ D L).X q).X p) := by
  rcases h with h | h
  · exact (HomologicalComplex.eval _ (up ℤ) p).map_isZero ((cechIntFunctor R φ D).map_isZero h)
  · exact isZero_cechIntFunctor_X R φ D (L.X q) p h

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The antidiagonals of the Čech double complex of a bounded below complex are finite. -/
lemma diagonalFinite_cechBicomplex (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ)
    [L.IsStrictlyGE 0] : DiagonalFinite (cechBicomplex R φ D L) := by
  intro n
  refine (Set.finite_Icc (0 : ℤ) n).subset fun q hq ↦ ?_
  simp only [Set.mem_ofPred_eq] at hq
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hq (isZero_cechBicomplex_X_X R φ D L q (n - q)
      (Or.inl (L.isZero_of_isStrictlyGE 0 q (by omega))))
  · by_contra h
    exact hq (isZero_cechBicomplex_X_X R φ D L q (n - q) (Or.inr (by omega)))

omit [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The antidiagonals of the flipped Čech double complex of a bounded below complex are
finite. -/
lemma diagonalFinite_cechBicomplex_flip (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ)
    [L.IsStrictlyGE 0] : DiagonalFinite (cechBicomplex R φ D L).flip := by
  intro n
  refine (Set.finite_Icc (0 : ℤ) n).subset fun p hp ↦ ?_
  simp only [Set.mem_ofPred_eq] at hp
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hp (isZero_cechBicomplex_X_X R φ D L (n - p) p (Or.inr (by omega)))
  · by_contra h
    exact hp (isZero_cechBicomplex_X_X R φ D L (n - p) p
      (Or.inl (L.isZero_of_isStrictlyGE 0 (n - p) (by omega))))

/-- The Čech double complex of a bounded below complex has a total complex. -/
instance hasTotal_cechBicomplex (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ)
    [L.IsStrictlyGE 0] : (cechBicomplex R φ D L).HasTotal (up ℤ) :=
  hasTotal_of_diagonalFinite _ (diagonalFinite_cechBicomplex R φ D L)

/-- The flipped Čech double complex of a bounded below complex has a total complex. -/
instance hasTotal_cechBicomplex_flip (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ)
    [L.IsStrictlyGE 0] : (cechBicomplex R φ D L).flip.HasTotal (up ℤ) :=
  hasTotal_of_diagonalFinite _ (diagonalFinite_cechBicomplex_flip R φ D L)

/-- The total complex of the Čech double complex of a complex strictly bounded below by `0` is
strictly bounded below by `0`. -/
instance isStrictlyGE_total_cechBicomplex (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ)
    [L.IsStrictlyGE 0] :
    CochainComplex.IsStrictlyGE ((cechBicomplex R φ D L).total (up ℤ)) 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact isZero_total_X _ 0 (fun p q hq ↦ isZero_cechBicomplex_X_X R φ D L p q (Or.inr hq))
    (fun p hp ↦ (cechIntFunctor R φ D).map_isZero (L.isZero_of_isStrictlyGE 0 p hp)) n hn

/-- **The augmentation `α`, as a map into the zeroth row of the Čech double complex**: in
resolution degree `q` it is the restriction of global sections of `L^q` into the degree zero Čech
term. -/
def alphaRow (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ) :
    ((baseGlobalSections R φ).mapHomologicalComplex (up ℤ)).obj L ⟶
      rowZero (cechBicomplex R φ D L) where
  f q := augmentationInt R φ D (L.X q)
  comm' q q' _ := augmentationInt_naturality R φ D (L.d q q')

/-- **The hypotheses of [Stacks, Tag 0133] for the columns of the Čech double complex** of a
bounded below complex of injective sheaves of modules, for a family covering the final object. -/
theorem hypotheses_alphaRow (hD : J.CoversTop D)
    (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ) [L.IsStrictlyGE 0]
    [∀ q, Injective (L.X q)] :
    Hypotheses (((baseGlobalSections R φ).mapHomologicalComplex (up ℤ)).obj L)
      (cechBicomplex R φ D L) (alphaRow R φ D L) where
  diagonalFinite := diagonalFinite_cechBicomplex R φ D L
  zero_of_neg p q hq := isZero_cechIntFunctor_X R φ D (L.X p) q hq
  exactAt_of_ne_zero p q hq := exactAt_cechIntFunctor_of_injective R φ D (L.X p) q hq
  inducesIsoKernel p := ⟨augmentationInt_comp_d R φ D (L.X p),
    isIso_kernelLift_augmentationInt R φ D hD (L.X p)⟩

/-- **The map `α : Γ(C, L^•) ⟶ Tot Č(D, L^•)`**, the comparison map of [Stacks, Tag 0133] for the
columns. -/
def totalAugmentation (hD : J.CoversTop D)
    (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ) [L.IsStrictlyGE 0]
    [∀ q, Injective (L.X q)] :
    ((baseGlobalSections R φ).mapHomologicalComplex (up ℤ)).obj L ⟶
      (cechBicomplex R φ D L).total (up ℤ) :=
  comparisonMapP _ _ _ (hypotheses_alphaRow R φ D hD L)

/-- **`α` is a quasi-isomorphism**, for every bounded below complex of injective sheaves of
modules. -/
instance quasiIso_totalAugmentation (hD : J.CoversTop D)
    (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ) [L.IsStrictlyGE 0]
    [∀ q, Injective (L.X q)] : QuasiIso (totalAugmentation R φ D hD L) := by
  dsimp only [totalAugmentation]
  infer_instance

/-- The components of `α`. -/
lemma totalAugmentation_f (hD : J.CoversTop D)
    (L : CochainComplex (SheafOfModules.{max u v w} R) ℤ) [L.IsStrictlyGE 0]
    [∀ q, Injective (L.X q)] (q : ℤ) :
    (totalAugmentation R φ D hD L).f q =
      augmentationInt R φ D (L.X q) ≫ (cechBicomplex R φ D L).ιTotal (up ℤ) q 0 q (by simp) :=
  rfl

/-- **The map `β : Č(D, N) ⟶ Tot Č(D, I^•)`** for an injective resolution `N ⟶ I^•`: the Čech
complex of the inclusion `N ⟶ I^0`, landing in the column of resolution degree zero. -/
def cechToTotal {N : SheafOfModules.{max u v w} R} (I : InjectiveResolution N) :
    (cechIntFunctor R φ D).obj N ⟶ (cechBicomplex R φ D I.cochainComplex).total (up ℤ) where
  f p := ((cechIntFunctor R φ D).map I.inclusionZero).f p ≫
    (cechBicomplex R φ D I.cochainComplex).ιTotal (up ℤ) 0 p p (by simp)
  comm' p p' hpp' := by
    obtain rfl : p + 1 = p' := hpp'
    have h : (cechIntFunctor R φ D).map I.inclusionZero ≫
        (cechIntFunctor R φ D).map (I.cochainComplex.d 0 1) = 0 := by
      rw [← Functor.map_comp, InjectiveResolution.inclusionZero_comp_d, Functor.map_zero]
    have hz : ((cechIntFunctor R φ D).map I.inclusionZero).f p ≫
        ((cechBicomplex R φ D I.cochainComplex).d 0 (0 + 1)).f p = 0 := by
      rw [show (0 : ℤ) + 1 = 1 by norm_num]
      have hd : (cechBicomplex R φ D I.cochainComplex).d 0 1 =
          (cechIntFunctor R φ D).map (I.cochainComplex.d 0 1) :=
        Functor.mapHomologicalComplex_obj_d _ _ _ _ _
      rw [hd, ← HomologicalComplex.comp_f, h, HomologicalComplex.zero_f]
    rw [Category.assoc, HomologicalComplex₂.ιTotal_d_up_ℤ _ 0 p p (by simp),
      Preadditive.comp_add, ← Category.assoc, hz, zero_comp, zero_add,
      Int.negOnePow_zero, one_smul, ← Category.assoc, ← Category.assoc]
    congr 1
    exact ((cechIntFunctor R φ D).map I.inclusionZero).comm p (p + 1)

/-- **The map `β`, as a map into the zeroth row of the flipped Čech double complex**. -/
def betaRow {N : SheafOfModules.{max u v w} R} (I : InjectiveResolution N) :
    (cechIntFunctor R φ D).obj N ⟶ rowZero (cechBicomplex R φ D I.cochainComplex).flip where
  f p := ((cechIntFunctor R φ D).map I.inclusionZero).f p
  comm' p p' _ := ((cechIntFunctor R φ D).map I.inclusionZero).comm p p'

/-- The rows of the Čech double complex of an injective resolution are exact away from
resolution degree zero, for a sheaf of modules acyclic on every `D_x`. -/
lemma exactAt_cechBicomplex_flip_X [EnoughInjectives (SheafOfModules.{max u v w} R)]
    {N : SheafOfModules.{max u v w} R} (I : InjectiveResolution N)
    (hac : ∀ (n : ℕ) (x : Fin (n + 1) → ι) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation R (op (inter D x))).rightDerived m).obj N))
    (p q : ℤ) (hq : q ≠ 0) :
    ((cechBicomplex R φ D I.cochainComplex).flip.X p).ExactAt q := by
  rcases lt_or_ge p 0 with hp | hp
  · exact HomologicalComplex.ExactAt.of_isZero
      (isZero_cechBicomplex_X_X R φ D I.cochainComplex q p (Or.inr hp))
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ℤ) = p := ⟨p.toNat, by omega⟩
    have hiso : (cechBicomplex R φ D I.cochainComplex).flip.X (i : ℤ) ≅
        ((cechTermFunctor R φ D i).mapHomologicalComplex (up ℤ)).obj I.cochainComplex :=
      (NatIso.mapHomologicalComplex (cechEvalIso R φ D i) (up ℤ)).app I.cochainComplex
    exact (exactAt_cechTerm_cochainComplex R φ D I i (hac i) q hq).of_iso hiso.symm

/-- **The kernel clause of [Stacks, Tag 0133] for the rows of the Čech double complex**: the Čech
complex of `N` is, in each Čech degree, a kernel of the first differential of the row. -/
lemma inducesIsoKernel_betaRow [EnoughInjectives (SheafOfModules.{max u v w} R)]
    {N : SheafOfModules.{max u v w} R} (I : InjectiveResolution N) (p : ℤ) :
    ∃ hβ : (betaRow R φ D I).f p ≫
        ((cechBicomplex R φ D I.cochainComplex).flip.X p).d 0 1 = 0,
      IsIso (kernel.lift (((cechBicomplex R φ D I.cochainComplex).flip.X p).d 0 1)
        ((betaRow R φ D I).f p) hβ) := by
  have hz := InjectiveResolution.inclusionZero_comp_d I
  have hβ : (betaRow R φ D I).f p ≫
      ((cechBicomplex R φ D I.cochainComplex).flip.X p).d 0 1 = 0 := by
    change ((cechIntFunctor R φ D).map I.inclusionZero).f p ≫
      ((cechIntFunctor R φ D).map (I.cochainComplex.d 0 1)).f p = 0
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, hz, Functor.map_zero,
      HomologicalComplex.zero_f]
  refine ⟨hβ, ?_⟩
  let := HasDerivedCategory.standard (SheafOfModules.{max u v w} R)
  have hmonoξ : Mono I.inclusionZero := Stacks.CechSite.Acyclic.mono_inclusionZero I
  rcases lt_or_ge p 0 with hp | hp
  · refine isIso_of_isZero _ (isZero_cechIntFunctor_X R φ D N p hp) ?_
    exact IsZero.of_mono (kernel.ι _)
      (isZero_cechBicomplex_X_X R φ D I.cochainComplex 0 p (Or.inr hp))
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ℤ) = p := ⟨p.toNat, by omega⟩
    have hS : (ShortComplex.mk I.inclusionZero (I.cochainComplex.d 0 1) hz).Exact :=
      Stacks.CechSite.Acyclic.exact_inclusionZero I
    have hexT := hS.map_of_mono_of_preservesKernel (cechTermFunctor R φ D i) hmonoξ
      inferInstance
    have hmono : Mono ((betaRow R φ D I).f (i : ℤ)) := by
      have : Mono (((cechFunctor R φ D).map I.inclusionZero).f i) :=
        (inferInstance : Mono ((cechTermFunctor R φ D i).map I.inclusionZero))
      change Mono (((cechIntFunctor R φ D).map I.inclusionZero).f (i : ℤ))
      rw [cechIntFunctor_map_f R φ D I.inclusionZero i i rfl]
      infer_instance
    have eiso : (ShortComplex.mk I.inclusionZero (I.cochainComplex.d 0 1) hz).map
          (cechTermFunctor R φ D i) ≅
        ShortComplex.mk ((betaRow R φ D I).f (i : ℤ))
          (((cechBicomplex R φ D I.cochainComplex).flip.X (i : ℤ)).d 0 1) hβ :=
      ShortComplex.isoMk ((cechEvalIso R φ D i).app N).symm
        ((cechEvalIso R φ D i).app (I.cochainComplex.X 0)).symm
        ((cechEvalIso R φ D i).app (I.cochainComplex.X 1)).symm
        ((cechEvalIso R φ D i).inv.naturality I.inclusionZero).symm
        ((cechEvalIso R φ D i).inv.naturality (I.cochainComplex.d 0 1)).symm
    exact @Stacks.Cohomology.CechTotalComparison.isIso_kernelLift_of_mono_of_exact
      _ _ _ _ _ _ _ _ _ hmono (ShortComplex.exact_of_iso eiso hexT)

/-- **The hypotheses of [Stacks, Tag 0133] for the rows of the Čech double complex** of an
injective resolution of a sheaf of modules acyclic on every `D_x`. -/
theorem hypotheses_betaRow [EnoughInjectives (SheafOfModules.{max u v w} R)]
    {N : SheafOfModules.{max u v w} R} (I : InjectiveResolution N)
    (hac : ∀ (n : ℕ) (x : Fin (n + 1) → ι) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation R (op (inter D x))).rightDerived m).obj N)) :
    Hypotheses ((cechIntFunctor R φ D).obj N) (cechBicomplex R φ D I.cochainComplex).flip
      (betaRow R φ D I) where
  diagonalFinite := diagonalFinite_cechBicomplex_flip R φ D I.cochainComplex
  zero_of_neg p q hq := isZero_cechBicomplex_X_X R φ D I.cochainComplex q p
    (Or.inl (I.cochainComplex.isZero_of_isStrictlyGE 0 q (by omega)))
  exactAt_of_ne_zero p q hq := exactAt_cechBicomplex_flip_X R φ D I hac p q hq
  inducesIsoKernel p := inducesIsoKernel_betaRow R φ D I p

/-- **`β` is the comparison map of [Stacks, Tag 0133] for the rows**, read in the total complex
through the flip. -/
lemma cechToTotal_eq [EnoughInjectives (SheafOfModules.{max u v w} R)]
    {N : SheafOfModules.{max u v w} R} (I : InjectiveResolution N)
    (hac : ∀ (n : ℕ) (x : Fin (n + 1) → ι) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation R (op (inter D x))).rightDerived m).obj N)) :
    cechToTotal R φ D I =
      comparisonMapP _ _ _ (hypotheses_betaRow R φ D I hac) ≫
        ((cechBicomplex R φ D I.cochainComplex).totalFlipIso (up ℤ)).hom := by
  refine HomologicalComplex.hom_ext _ _ fun p ↦ ?_
  rw [HomologicalComplex.comp_f, comparisonMapP_f, Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  simp only [rowZero_X, σ_def, zero_mul, Int.negOnePow_zero, one_smul]
  rfl

/-- **`β` is a quasi-isomorphism** for a sheaf of modules acyclic on every `D_x`. -/
lemma quasiIso_cechToTotal [EnoughInjectives (SheafOfModules.{max u v w} R)]
    {N : SheafOfModules.{max u v w} R} (I : InjectiveResolution N)
    (hac : ∀ (n : ℕ) (x : Fin (n + 1) → ι) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation R (op (inter D x))).rightDerived m).obj N)) :
    QuasiIso (cechToTotal R φ D I) := by
  rw [cechToTotal_eq R φ D I hac]
  infer_instance

end Bicomplex

/-! ### Naturality of the two maps into the total complex -/

section Naturality

/-- The map of Čech double complexes induced by a morphism of complexes of sheaves of modules. -/
abbrev cechBicomplexMap {L L' : CochainComplex (SheafOfModules.{max u v w} R) ℤ} (ψ : L ⟶ L') :
    cechBicomplex R φ D L ⟶ cechBicomplex R φ D L' :=
  ((cechIntFunctor R φ D).mapHomologicalComplex (up ℤ)).map ψ

/-- `α` is natural in the bounded below complex of injectives. -/
lemma totalAugmentation_naturality (hD : J.CoversTop D)
    {L L' : CochainComplex (SheafOfModules.{max u v w} R) ℤ} [L.IsStrictlyGE 0]
    [L'.IsStrictlyGE 0] [∀ q, Injective (L.X q)] [∀ q, Injective (L'.X q)] (ψ : L ⟶ L') :
    totalAugmentation R φ D hD L ≫
        HomologicalComplex₂.total.map (cechBicomplexMap R φ D ψ) (up ℤ) =
      ((baseGlobalSections R φ).mapHomologicalComplex (up ℤ)).map ψ ≫
        totalAugmentation R φ D hD L' :=
  comparisonMapP_naturality _ _ _ _ _ _ _ <| HomologicalComplex.hom_ext _ _ fun q ↦
    augmentationInt_naturality R φ D (ψ.f q)

/-- `β` is natural in a morphism of injective resolutions. -/
lemma cechToTotal_naturality {N N' : SheafOfModules.{max u v w} R} {g : N ⟶ N'}
    {I : InjectiveResolution N} {I' : InjectiveResolution N'}
    (ψ : InjectiveResolution.Hom I I' g) :
    cechToTotal R φ D I ≫ HomologicalComplex₂.total.map (cechBicomplexMap R φ D ψ.hom') (up ℤ) =
      (cechIntFunctor R φ D).map g ≫ cechToTotal R φ D I' := by
  refine HomologicalComplex.hom_ext _ _ (fun p ↦ ?_)
  have key : ((cechIntFunctor R φ D).map I.inclusionZero).f p ≫
      ((cechIntFunctor R φ D).map (ψ.hom'.f 0)).f p =
      ((cechIntFunctor R φ D).map g).f p ≫
      ((cechIntFunctor R φ D).map I'.inclusionZero).f p := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← Functor.map_comp,
      ← Functor.map_comp, InjectiveResolution.inclusionZero_comp_hom'_f_zero]
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  dsimp only [cechToTotal]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  exact (congrArg (· ≫ _) key).trans (Category.assoc _ _ _)

end Naturality

/-! ### The comparison with derived global sections -/

section Comparison

variable [EnoughInjectives (SheafOfModules.{max u v w} R)]
  [HasDerivedCategory (SheafOfModules.{max u v w} R)] [HasDerivedCategory (ModuleCat.{max u v w} A)]

/-- **Derived global sections `RΓ(C, N)`** of a sheaf of modules, in `D⁺(A)`. -/
abbrev derivedGlobalSectionsFunctor :
    SheafOfModules.{max u v w} R ⥤ DerivedCategory.Plus (ModuleCat.{max u v w} A) :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙ (baseGlobalSections R φ).rightDerivedFunctorPlus

/-- **The Čech complex `Č(D, N)`, as an object of `D⁺(A)`.** -/
abbrev cechDerivedFunctor :
    SheafOfModules.{max u v w} R ⥤ DerivedCategory.Plus (ModuleCat.{max u v w} A) :=
  cechPlusFunctor R φ D ⋙ DerivedCategory.Plus.Q

omit [HasDerivedCategory (ModuleCat.{max u v w} A)] in
/-- A quasi-isomorphism of bounded below complexes becomes invertible in `D⁺`. -/
lemma isIso_Q_map_of_quasiIso {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] [HasDerivedCategory 𝒞]
    {L L' : CochainComplex.Plus 𝒞} (f : L ⟶ L') (hf : QuasiIso f.hom) :
    IsIso (DerivedCategory.Plus.Q.map f) :=
  (ObjectProperty.isIso_hom_iff _).1 ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hf)

/-- The global sections of an injective resolution, as a bounded below complex. -/
abbrev sectionsPlus {N : SheafOfModules.{max u v w} R} (I : InjectiveResolution N) :
    CochainComplex.Plus (ModuleCat.{max u v w} A) :=
  ⟨((baseGlobalSections R φ).mapHomologicalComplex (up ℤ)).obj I.cochainComplex, 0,
    inferInstance⟩

/-- The total complex of the Čech double complex of an injective resolution, as a bounded below
complex. -/
abbrev totalPlus {N : SheafOfModules.{max u v w} R} (I : InjectiveResolution N) :
    CochainComplex.Plus (ModuleCat.{max u v w} A) :=
  ⟨(cechBicomplex R φ D I.cochainComplex).total (up ℤ), 0, inferInstance⟩

/-- `α` as a morphism of bounded below complexes. -/
abbrev totalAugmentationPlus (hD : J.CoversTop D) {N : SheafOfModules.{max u v w} R}
    (I : InjectiveResolution N) : sectionsPlus R φ I ⟶ totalPlus R φ D I :=
  ObjectProperty.homMk (totalAugmentation R φ D hD I.cochainComplex)

/-- `β` as a morphism of bounded below complexes. -/
abbrev cechToTotalPlus {N : SheafOfModules.{max u v w} R} (I : InjectiveResolution N) :
    (cechPlusFunctor R φ D).obj N ⟶ totalPlus R φ D I :=
  ObjectProperty.homMk (cechToTotal R φ D I)

omit [EnoughInjectives (SheafOfModules.{max u v w} R)]
  [HasDerivedCategory (SheafOfModules.{max u v w} R)] in
/-- `α` becomes invertible in `D⁺(A)`. -/
theorem isIso_Q_map_totalAugmentationPlus (hD : J.CoversTop D) {N : SheafOfModules.{max u v w} R}
    (I : InjectiveResolution N) :
    IsIso (DerivedCategory.Plus.Q.map (totalAugmentationPlus R φ D hD I)) :=
  isIso_Q_map_of_quasiIso _ (quasiIso_totalAugmentation R φ D hD I.cochainComplex)

/-- **The comparison `Č(D, N) ⟶ RΓ(C, N)`**, computed through an injective resolution:
`Q(β) ≫ Q(α)⁻¹` followed by the identification of the global sections of the resolution with
derived global sections. -/
def cechComparison (hD : J.CoversTop D) (N : SheafOfModules.{max u v w} R)
    (I : InjectiveResolution N) :
    (cechDerivedFunctor R φ D).obj N ⟶ (derivedGlobalSectionsFunctor R φ).obj N :=
  haveI := isIso_Q_map_totalAugmentationPlus R φ D hD I
  DerivedCategory.Plus.Q.map (cechToTotalPlus R φ D I) ≫
    inv (DerivedCategory.Plus.Q.map (totalAugmentationPlus R φ D hD I)) ≫
    (DerivedCategory.Plus.qhQIso (sectionsPlus R φ I)).inv ≫
    I.toRightDerivedPlus (baseGlobalSections R φ)

omit [HasDerivedCategory (SheafOfModules.{max u v w} R)]
  [HasDerivedCategory (ModuleCat.{max u v w} A)] in
/-- The bookkeeping of `cechComparison_naturality`, in an arbitrary category. -/
lemma comparison_paste {𝒦 : Type*} [Category* 𝒦]
    {cN cN' tot tot' sec sec' secQh secQh' rN rN' : 𝒦}
    (β : cN ⟶ tot) (α : sec ⟶ tot) [IsIso α] (e : secQh ≅ sec) (t : secQh ⟶ rN)
    (Rg : rN ⟶ rN') (β' : cN' ⟶ tot') (α' : sec' ⟶ tot') [IsIso α'] (e' : secQh' ≅ sec')
    (t' : secQh' ⟶ rN') (Kg : cN ⟶ cN') (T : tot ⟶ tot') (Γψ : sec ⟶ sec')
    (Γψh : secQh ⟶ secQh') (h4 : β ≫ T = Kg ≫ β') (h3 : α ≫ T = Γψ ≫ α')
    (h2 : Γψh ≫ e'.hom = e.hom ≫ Γψ) (h1 : Γψh ≫ t' = t ≫ Rg) :
    (β ≫ inv α ≫ e.inv ≫ t) ≫ Rg = Kg ≫ β' ≫ inv α' ≫ e'.inv ≫ t' := by
  simp only [Category.assoc]
  have h2' : e.inv ≫ Γψh = Γψ ≫ e'.inv := by
    rw [Iso.inv_comp_eq, ← reassoc_of% h2, Iso.hom_inv_id, Category.comp_id]
  have h3' : inv α ≫ Γψ = T ≫ inv α' := by
    rw [IsIso.inv_comp_eq, reassoc_of% h3, IsIso.hom_inv_id, Category.comp_id]
  rw [← h1, reassoc_of% h2', reassoc_of% h3', reassoc_of% h4]

omit [EnoughInjectives (SheafOfModules.{max u v w} R)]
  [HasDerivedCategory (SheafOfModules.{max u v w} R)] in
/-- `Q(α)` is natural in a morphism of injective resolutions. -/
lemma Q_map_totalAugmentationPlus_naturality (hD : J.CoversTop D)
    {N N' : SheafOfModules.{max u v w} R} {g : N ⟶ N'}
    {I : InjectiveResolution N} {I' : InjectiveResolution N'}
    (ψ : InjectiveResolution.Hom I I' g) :
    DerivedCategory.Plus.Q.map (totalAugmentationPlus R φ D hD I) ≫
        DerivedCategory.Plus.Q.map (ObjectProperty.homMk
          (HomologicalComplex₂.total.map (cechBicomplexMap R φ D ψ.hom') (up ℤ)) :
            totalPlus R φ D I ⟶ totalPlus R φ D I') =
      DerivedCategory.Plus.Q.map (ObjectProperty.homMk
          (((baseGlobalSections R φ).mapHomologicalComplex (up ℤ)).map ψ.hom') :
            sectionsPlus R φ I ⟶ sectionsPlus R φ I') ≫
        DerivedCategory.Plus.Q.map (totalAugmentationPlus R φ D hD I') := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact ObjectProperty.hom_ext _ (totalAugmentation_naturality R φ D hD ψ.hom')

omit [EnoughInjectives (SheafOfModules.{max u v w} R)]
  [HasDerivedCategory (SheafOfModules.{max u v w} R)] in
/-- `Q(β)` is natural in a morphism of injective resolutions. -/
lemma Q_map_cechToTotalPlus_naturality {N N' : SheafOfModules.{max u v w} R} {g : N ⟶ N'}
    {I : InjectiveResolution N} {I' : InjectiveResolution N'}
    (ψ : InjectiveResolution.Hom I I' g) :
    DerivedCategory.Plus.Q.map (cechToTotalPlus R φ D I) ≫
        DerivedCategory.Plus.Q.map (ObjectProperty.homMk
          (HomologicalComplex₂.total.map (cechBicomplexMap R φ D ψ.hom') (up ℤ)) :
            totalPlus R φ D I ⟶ totalPlus R φ D I') =
      (cechDerivedFunctor R φ D).map g ≫ DerivedCategory.Plus.Q.map (cechToTotalPlus R φ D I') := by
  rw [Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact ObjectProperty.hom_ext _ (cechToTotal_naturality R φ D ψ)

/-- **The comparison is natural** in the sheaf of modules and compatible with a morphism of
injective resolutions. -/
lemma cechComparison_naturality (hD : J.CoversTop D)
    {N N' : SheafOfModules.{max u v w} R} {g : N ⟶ N'}
    {I : InjectiveResolution N} {I' : InjectiveResolution N'}
    (ψ : InjectiveResolution.Hom I I' g) :
    cechComparison R φ D hD N I ≫ (derivedGlobalSectionsFunctor R φ).map g =
      (cechDerivedFunctor R φ D).map g ≫ cechComparison R φ D hD N' I' := by
  have := isIso_Q_map_totalAugmentationPlus R φ D hD I
  have := isIso_Q_map_totalAugmentationPlus R φ D hD I'
  have h1 := InjectiveResolution.toRightDerivedPlus_naturality (baseGlobalSections R φ) ψ
  have h2 := DerivedCategory.Plus.qhQIso_naturality
    (ObjectProperty.homMk (((baseGlobalSections R φ).mapHomologicalComplex (up ℤ)).map ψ.hom') :
      sectionsPlus R φ I ⟶ sectionsPlus R φ I')
  have h3 := Q_map_totalAugmentationPlus_naturality R φ D hD ψ
  have h4 := Q_map_cechToTotalPlus_naturality R φ D ψ
  dsimp only [cechComparison]
  exact comparison_paste _ _ _ _ _ _ _ _ _ _ _ _ _ h4 h3 h2 h1

/-- **The comparison does not depend on the injective resolution.** -/
lemma cechComparison_eq (hD : J.CoversTop D) (N : SheafOfModules.{max u v w} R)
    (I : InjectiveResolution N) :
    cechComparison R φ D hD N (InjectiveResolution.of N) = cechComparison R φ D hD N I := by
  simpa using cechComparison_naturality R φ D hD
    (InjectiveResolution.homOfDesc (𝟙 N) (InjectiveResolution.of N) I)

/-- **The comparison `Č(D, -) ⟶ RΓ(C, -)`** of functors from sheaves of modules to `D⁺(A)`, for a
family `D` covering the final object: at `N` it is `Q(β) ≫ Q(α)⁻¹` followed by the identification
of the global sections of an injective resolution with `RΓ(C, N)`. -/
def cechToDerivedGlobalSections (hD : J.CoversTop D) :
    cechDerivedFunctor R φ D ⟶ derivedGlobalSectionsFunctor R φ where
  app N := cechComparison R φ D hD N (InjectiveResolution.of N)
  naturality N N' g := (cechComparison_naturality R φ D hD
    (InjectiveResolution.homOfDesc g (InjectiveResolution.of N)
      (InjectiveResolution.of N'))).symm

/-- The component of the comparison at `N` is computed by any injective resolution of `N`. -/
lemma cechToDerivedGlobalSections_app (hD : J.CoversTop D) (N : SheafOfModules.{max u v w} R)
    (I : InjectiveResolution N) :
    (cechToDerivedGlobalSections R φ D hD).app N = cechComparison R φ D hD N I :=
  cechComparison_eq R φ D hD N I

/-- **Stacks Project, Tag 03F7, for a covering of the final object, at module coefficients.** Let
`D : ι → C` be a family of objects of a site covering the final object, all of whose finite
nonempty products `D_x = D (x 0) × ⋯ × D (x n)` exist, and let `N` be a sheaf of `R`-modules whose
higher cohomology vanishes on every `D_x`. Then the comparison `Č(D, N) ⟶ RΓ(C, N)` in the bounded
below derived category of `A`-modules is an isomorphism: the Čech complex of `N` computes the
cohomology of `N`. -/
theorem isIso_cechToDerivedGlobalSections_app (hD : J.CoversTop D)
    (N : SheafOfModules.{max u v w} R)
    (hac : ∀ (n : ℕ) (x : Fin (n + 1) → ι) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation R (op (inter D x))).rightDerived m).obj N)) :
    IsIso ((cechToDerivedGlobalSections R φ D hD).app N) := by
  have := isIso_Q_map_totalAugmentationPlus R φ D hD (InjectiveResolution.of N)
  have := isIso_Q_map_of_quasiIso (cechToTotalPlus R φ D (InjectiveResolution.of N))
    (quasiIso_cechToTotal R φ D (InjectiveResolution.of N) hac)
  have hT := InjectiveResolution.isIso_toRightDerivedPlus (baseGlobalSections R φ)
    (InjectiveResolution.of N)
  dsimp only [cechToDerivedGlobalSections, cechComparison]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' inferInstance hT))

/-- **The Čech complex of a sheaf of modules acyclic on the `D_x` is its derived global
sections**: `Č(D, N) ≅ RΓ(C, N)` in `D⁺(A)`, the comparison of
`cechToDerivedGlobalSections`. -/
def cechDerivedIso (hD : J.CoversTop D) (N : SheafOfModules.{max u v w} R)
    (hac : ∀ (n : ℕ) (x : Fin (n + 1) → ι) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation R (op (inter D x))).rightDerived m).obj N)) :
    (cechDerivedFunctor R φ D).obj N ≅ (derivedGlobalSectionsFunctor R φ).obj N :=
  haveI := isIso_cechToDerivedGlobalSections_app R φ D hD N hac
  asIso ((cechToDerivedGlobalSections R φ D hD).app N)

/-- `cechDerivedIso` is the component of the natural comparison. -/
@[simp]
lemma cechDerivedIso_hom (hD : J.CoversTop D) (N : SheafOfModules.{max u v w} R)
    (hac : ∀ (n : ℕ) (x : Fin (n + 1) → ι) (m : ℕ), 0 < m →
      IsZero (((SheafOfModules.evaluation R (op (inter D x))).rightDerived m).obj N)) :
    (cechDerivedIso R φ D hD N hac).hom = (cechToDerivedGlobalSections R φ D hD).app N :=
  rfl

end Comparison

end Stacks.CechSite.FinalCover

end
