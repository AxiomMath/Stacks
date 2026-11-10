module

public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.AcyclicCoveringFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.FinalObjectCovering

/-!
# The Čech complex of an object covering the final object computes cohomology

Let `U` be an object covering the final object of a ringed site `(C, J, O)`, with all powers
`U^{m+1}`, and let `M` be a sheaf of `O`-modules with no higher cohomology on the `U^{m+1}`. Then
the Čech complex of `M` for `U` computes the cohomology of `M`: for an injective resolution
`M → I^•` the Čech bicomplex `Č^p(U, I^q)` receives quasi-isomorphisms from the Čech complex of
`M` (its rows resolve it) and from the global sections `Γ(I^•)` (its columns resolve them), by
[Stacks, Tag 0133]. Everything is read over a base ring `A` mapping to the global sections of `O`.

## Main definitions

* `Stacks.CechTop.cechFunctorZ`: the `ℤ`-graded Čech complex over `A`.
* `Stacks.CechTop.cechBicomplex`: the Čech bicomplex of a complex of modules.

## Main results

* `Stacks.CechTop.hypotheses_cechBicomplexAugmentation`,
  `Stacks.CechTop.hypotheses_cechRowAugmentation`: the hypotheses of [Stacks, Tag 0133] for the
  columns and the rows.
* `Stacks.CechTop.exists_quasiIso_cechFunctorZ`: the Čech complex of `M` and the global sections
  of an injective resolution of `M` are related by a zigzag of quasi-isomorphisms, hence
  isomorphic in `D(A)`.

## References

* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial ComplexShape
open Stacks.Cohomology.SiteModules

universe u u'

namespace Stacks.CechTop

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable {C : Type u'} [Category.{u} C] (U : C) [∀ n : ℕ, HasProduct (fun _ : Fin (n + 1) => U)]
  {J : GrothendieckTopology C} (O : Sheaf J RingCat.{u}) {A : Type u} [CommRing A]
  (ρ : A →+* GlobalSectionRing O)

/-- The Čech complex over the base ring, graded by `ℤ`. -/
abbrev cechFunctorZ : SheafOfModules.{u} O ⥤ CochainComplex (ModuleCat.{max u u'} A) ℤ :=
  cechFunctorOverBase U O ρ ⋙ embeddingUpNat.extendFunctor (ModuleCat.{max u u'} A)

/-- The `ℤ`-graded Čech complex functor is additive. -/
instance : (cechFunctorZ U O ρ).Additive := by
  dsimp only [cechFunctorZ]
  infer_instance

/-- The `ℤ`-graded Čech complex vanishes in negative degrees. -/
theorem isZero_cechFunctorZ_X (M : SheafOfModules.{u} O) (p : ℤ) (hp : p < 0) :
    IsZero (((cechFunctorZ U O ρ).obj M).X p) :=
  HomologicalComplex.isZero_extend_X _ _ _ fun i => by
    change (i : ℤ) ≠ p
    omega

/-- The degree-`m` term of the `ℤ`-graded Čech complex is the degree-`m` Čech cochains. -/
abbrev cechFunctorZXIso (M : SheafOfModules.{u} O) (m : ℕ) :
    ((cechFunctorZ U O ρ).obj M).X m ≅ ((cechFunctorOverBase U O ρ).obj M).X m :=
  HomologicalComplex.extendXIso _ embeddingUpNat rfl

/-! ### The Čech bicomplex of a complex of modules -/

/-- The Čech bicomplex of a complex of sheaves of modules: first degree the degree of the complex,
second degree the Čech degree. -/
abbrev cechBicomplex (I : CochainComplex (SheafOfModules.{u} O) ℤ) :
    HomologicalComplex₂ (ModuleCat.{max u u'} A) (up ℤ) (up ℤ) :=
  ((cechFunctorZ U O ρ).mapHomologicalComplex (up ℤ)).obj I

variable {U O ρ} in
/-- The term `Č^p(U, I^q)` of the Čech bicomplex is zero when `I^q` is zero or `p < 0`. -/
theorem isZero_cechBicomplex_X_X (I : CochainComplex (SheafOfModules.{u} O) ℤ) (q p : ℤ)
    (h : IsZero (I.X q) ∨ p < 0) : IsZero (((cechBicomplex U O ρ I).X q).X p) := by
  rcases h with h | h
  · exact (HomologicalComplex.eval _ (up ℤ) p).map_isZero ((cechFunctorZ U O ρ).map_isZero h)
  · exact isZero_cechFunctorZ_X U O ρ _ p h

/-- A bicomplex whose terms vanish in negative degrees in both variables is diagonal finite. -/
private theorem diagonalFinite_of_isZero_of_neg {V : Type*} [Category V] [Abelian V]
    {K : HomologicalComplex₂ V (up ℤ) (up ℤ)} (h₁ : ∀ p q, p < 0 → IsZero ((K.X p).X q))
    (h₂ : ∀ p q, q < 0 → IsZero ((K.X p).X q)) : DiagonalFinite K := by
  intro n
  refine (Set.finite_Icc (0 : ℤ) n).subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hp (h₁ _ _ (by omega))
  · by_contra h
    exact hp (h₂ _ _ (by omega))

/-- The Čech bicomplex of a complex concentrated in nonnegative degrees has finitely many nonzero
terms on each antidiagonal. -/
theorem diagonalFinite_cechBicomplex (I : CochainComplex (SheafOfModules.{u} O) ℤ)
    [I.IsStrictlyGE 0] : DiagonalFinite (cechBicomplex U O ρ I) :=
  diagonalFinite_of_isZero_of_neg
    (fun p q hp => isZero_cechBicomplex_X_X I p q (Or.inl (I.isZero_of_isStrictlyGE 0 p hp)))
    fun p q hq => isZero_cechBicomplex_X_X I p q (Or.inr hq)

/-! ### The columns: Čech complexes of injective modules -/

variable [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}]

/-- Lifting the universe of a complex of modules preserves exactness in each degree. -/
theorem exactAt_ulift_mapHomologicalComplex {K : CochainComplex (ModuleCat.{u} A) ℕ} {m : ℕ}
    (h : K.ExactAt m) :
    (((ModuleCat.uliftFunctor.{u'} A).mapHomologicalComplex _).obj K).ExactAt m := by
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  exact h.map (ModuleCat.uliftFunctor.{u'} A)

/-- **The `ℤ`-graded Čech complex of an injective sheaf of modules is exact away from degree
zero.** -/
theorem exactAt_cechFunctorZ_of_injective (M : SheafOfModules.{u} O) [Injective M] (q : ℤ)
    (hq : q ≠ 0) : ((cechFunctorZ U O ρ).obj M).ExactAt q := by
  rcases lt_or_gt_of_ne hq with h | h
  · exact HomologicalComplex.ExactAt.of_isZero (isZero_cechFunctorZ_X U O ρ M q h)
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = q := ⟨q.toNat, by omega⟩
    refine (HomologicalComplex.extend_exactAt_iff ((cechFunctorOverBase U O ρ).obj M)
      embeddingUpNat (ComplexShape.embeddingUpNat_f m)).2 ?_
    exact exactAt_ulift_mapHomologicalComplex
      (cechComplexOverBase_exactAt_of_injective U O ρ M m (by omega))

/-- The augmentation into degree zero of the `ℤ`-graded Čech complex. -/
abbrev cechAugmentationZ (M : SheafOfModules.{u} O) :
    (globalSectionsOverBase O ρ).obj M ⟶ ((cechFunctorZ U O ρ).obj M).X 0 :=
  cechAugmentation U O ρ M ≫ (cechFunctorZXIso U O ρ M 0).inv

omit [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}] in
/-- The differential `d⁰¹` of the `ℤ`-graded Čech complex is the first Čech differential, read
through `cechFunctorZXIso`. -/
theorem cechFunctorZ_d_zero_one (M : SheafOfModules.{u} O) :
    ((cechFunctorZ U O ρ).obj M).d 0 1 = (cechFunctorZXIso U O ρ M 0).hom ≫
      ((cechFunctorOverBase U O ρ).obj M).d 0 1 ≫ (cechFunctorZXIso U O ρ M 1).inv :=
  HomologicalComplex.extend_d_eq _ _ rfl rfl

omit [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}] in
/-- The augmentation composed with the first differential of the `ℤ`-graded Čech complex is zero.
-/
theorem cechAugmentationZ_comp_d (M : SheafOfModules.{u} O) :
    cechAugmentationZ U O ρ M ≫ ((cechFunctorZ U O ρ).obj M).d 0 1 = 0 := by
  rw [cechFunctorZ_d_zero_one, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
    cechAugmentation_comp_d, zero_comp]

private theorem isIso_kernelLift_of_mono_of_exact' {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {T B₁ B₂ : 𝒜} (f : T ⟶ B₁) (g : B₁ ⟶ B₂) (hf : f ≫ g = 0) [Mono f]
    (hex : (ShortComplex.mk f g hf).Exact) : IsIso (kernel.lift g f hf) :=
  have : Mono (kernel.lift g f hf) := mono_of_mono_fac (kernel.lift_ι g f hf)
  have : Epi (kernel.lift g f hf) := (ShortComplex.mk f g hf).exact_iff_epi_kernel_lift.1 hex
  isIso_of_mono_of_epi _

omit [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}] in
variable {U} in
/-- **Global sections are the kernel of the first Čech differential**, in the `ℤ`-graded complex.
-/
theorem isIso_kernelLift_cechAugmentationZ (hU : J.CoversTop fun _ : Unit => U)
    (M : SheafOfModules.{u} O) :
    IsIso (kernel.lift (((cechFunctorZ U O ρ).obj M).d 0 1) (cechAugmentationZ U O ρ M)
      (cechAugmentationZ_comp_d U O ρ M)) := by
  have := mono_cechAugmentation O ρ hU M
  have e : ShortComplex.mk (cechAugmentation U O ρ M) (((cechFunctorOverBase U O ρ).obj M).d 0 1)
      (cechAugmentation_comp_d U O ρ M) ≅
      ShortComplex.mk (cechAugmentationZ U O ρ M) (((cechFunctorZ U O ρ).obj M).d 0 1)
        (cechAugmentationZ_comp_d U O ρ M) :=
    ShortComplex.isoMk (Iso.refl _) (cechFunctorZXIso U O ρ M 0).symm
      (cechFunctorZXIso U O ρ M 1).symm (by simp [cechAugmentationZ])
      (by
        dsimp only [Iso.symm_hom]
        rw [cechFunctorZ_d_zero_one, Iso.inv_hom_id_assoc])
  exact isIso_kernelLift_of_mono_of_exact' _ _ _
    (ShortComplex.exact_of_iso e (exact_cechAugmentation O ρ hU M))

omit [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}] in
/-- In degree `m ≥ 0`, the map of `ℤ`-graded Čech complexes induced by `φ` is the map of Čech
cochains, read through `cechFunctorZXIso`. -/
theorem cechFunctorZ_map_f {M N : SheafOfModules.{u} O} (φ : M ⟶ N) (m : ℕ) :
    ((cechFunctorZ U O ρ).map φ).f m = (cechFunctorZXIso U O ρ M m).hom ≫
      ((cechFunctorOverBase U O ρ).map φ).f m ≫ (cechFunctorZXIso U O ρ N m).inv := by
  change (HomologicalComplex.extendMap ((cechFunctorOverBase U O ρ).map φ) embeddingUpNat).f m = _
  rw [HomologicalComplex.extendMap_f _ embeddingUpNat (i := m) (i' := m) rfl]
  rfl

omit [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}] in
/-- In degree zero, the map of `ℤ`-graded Čech complexes induced by `φ` is the map of Čech
cochains, read through `cechFunctorZXIso`. -/
theorem cechFunctorZ_map_f_zero {M N : SheafOfModules.{u} O} (φ : M ⟶ N) :
    ((cechFunctorZ U O ρ).map φ).f 0 = (cechFunctorZXIso U O ρ M 0).hom ≫
      ((cechFunctorOverBase U O ρ).map φ).f 0 ≫ (cechFunctorZXIso U O ρ N 0).inv :=
  cechFunctorZ_map_f U O ρ φ 0

omit [HasSheafify J Ab.{u}] [J.WEqualsLocallyBijective Ab.{u}] in
/-- The augmentation `cechAugmentationZ` is natural in the module. -/
theorem cechAugmentationZ_naturality {M N : SheafOfModules.{u} O} (φ : M ⟶ N) :
    (globalSectionsOverBase O ρ).map φ ≫ cechAugmentationZ U O ρ N =
      cechAugmentationZ U O ρ M ≫ ((cechFunctorZ U O ρ).map φ).f 0 := by
  rw [cechFunctorZ_map_f_zero, cechAugmentationZ, cechAugmentationZ, Category.assoc,
    Iso.inv_hom_id_assoc, ← Category.assoc, cechAugmentation_naturality, Category.assoc]

/-- The augmentation of the Čech bicomplex of a complex by its global sections. -/
def cechBicomplexAugmentation (I : CochainComplex (SheafOfModules.{u} O) ℤ) :
    ((globalSectionsOverBase O ρ).mapHomologicalComplex (up ℤ)).obj I ⟶
      rowZero (cechBicomplex U O ρ I) where
  f p := cechAugmentationZ U O ρ (I.X p)
  comm' p p' _ := by
    change cechAugmentationZ U O ρ (I.X p) ≫ ((cechFunctorZ U O ρ).map (I.d p p')).f 0 =
      (globalSectionsOverBase O ρ).map (I.d p p') ≫ cechAugmentationZ U O ρ (I.X p')
    rw [cechAugmentationZ_naturality]

variable {U} in
/-- **The hypotheses of [Stacks, Tag 0133] for the Čech bicomplex of an injective resolution**,
column by column: each column is the Čech complex of an injective module, exact away from degree
zero with the global sections as kernel. -/
theorem hypotheses_cechBicomplexAugmentation (hU : J.CoversTop fun _ : Unit => U)
    {F : SheafOfModules.{u} O} (R : InjectiveResolution F) :
    Hypotheses _ (cechBicomplex U O ρ R.cochainComplex)
      (cechBicomplexAugmentation U O ρ R.cochainComplex) where
  diagonalFinite := diagonalFinite_cechBicomplex U O ρ R.cochainComplex
  zero_of_neg p q hq := isZero_cechBicomplex_X_X _ p q (Or.inr hq)
  exactAt_of_ne_zero _ q hq := exactAt_cechFunctorZ_of_injective U O ρ _ q hq
  inducesIsoKernel _ :=
    ⟨cechAugmentationZ_comp_d U O ρ _, isIso_kernelLift_cechAugmentationZ O ρ hU _⟩

/-! ### The rows: sections of a resolution over the powers of `U` -/

/-- The term of the Čech complex in a fixed degree `m`, as a functor of the module: sections over
`U^{m+1}` read as `A`-modules. -/
abbrev cechTermFunctor (m : ℕ) : SheafOfModules.{u} O ⥤ ModuleCat.{max u u'} A :=
  SheafOfModules.evaluation O (op ((cechNerve U).obj (op ⦋m⦌))) ⋙
    ModuleCat.restrictScalars (baseToSections O ρ (op ((cechNerve U).obj (op ⦋m⦌)))) ⋙
      ModuleCat.uliftFunctor.{u'} A

/-- The degree-`m` term of the `ℤ`-graded Čech complex is `cechTermFunctor m`. -/
def cechFunctorZEvalIso (m : ℕ) :
    cechFunctorZ U O ρ ⋙ HomologicalComplex.eval _ (up ℤ) (m : ℤ) ≅ cechTermFunctor U O ρ m :=
  NatIso.ofComponents (fun M => (cechFunctorZXIso U O ρ M m :
      (cechFunctorZ U O ρ ⋙ HomologicalComplex.eval _ (up ℤ) (m : ℤ)).obj M ≅
        (cechTermFunctor U O ρ m).obj M))
    fun {M N} φ => by
    change ((cechFunctorZ U O ρ).map φ).f m ≫ (cechFunctorZXIso U O ρ N m).hom = _
    rw [cechFunctorZ_map_f, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl

/-- An additive functor preserving homology preserves exactness of a complex in each degree. -/
theorem exactAt_mapHomologicalComplex_of_preservesHomology {𝒜 ℬ : Type*} [Category 𝒜]
    [Category ℬ] [Abelian 𝒜] [Abelian ℬ] (E : 𝒜 ⥤ ℬ) [E.Additive] [E.PreservesHomology]
    {K : CochainComplex 𝒜 ℤ} {q : ℤ} (h : K.ExactAt q) :
    ((E.mapHomologicalComplex _).obj K).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  exact h.map E

/-- Evaluation of sheaves of modules at an object is additive. -/
instance (V : Cᵒᵖ) : (SheafOfModules.evaluation O V).Additive where
  map_add := rfl

/-- **The sections over `U^{m+1}` of an injective resolution of a module acyclic there are exact
away from degree zero.** -/
theorem exactAt_cechTermFunctor_mapHomologicalComplex (m : ℕ) {M : SheafOfModules.{u} O}
    (R : InjectiveResolution M)
    (q : ℤ)
    (h : (((SheafOfModules.evaluation O (op ((cechNerve U).obj (op ⦋m⦌)))).mapHomologicalComplex
      (up ℤ)).obj R.cochainComplex).ExactAt q) :
    (((cechTermFunctor U O ρ m).mapHomologicalComplex (up ℤ)).obj R.cochainComplex).ExactAt q := by
  have := Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars
    (baseToSections O ρ (op ((cechNerve U).obj (op ⦋m⦌))))
  exact exactAt_mapHomologicalComplex_of_preservesHomology (ModuleCat.uliftFunctor.{u'} A)
    (exactAt_mapHomologicalComplex_of_preservesHomology
      (ModuleCat.restrictScalars (baseToSections O ρ (op ((cechNerve U).obj (op ⦋m⦌))))) h)

variable {M : SheafOfModules.{u} O} (R : InjectiveResolution M)

/-- The augmentation of the rows of the Čech bicomplex of an injective resolution by the Čech
complex of the resolved module. -/
def cechRowAugmentation :
    (cechFunctorZ U O ρ).obj M ⟶ rowZero (cechBicomplex U O ρ R.cochainComplex).flip where
  f p := ((cechFunctorZ U O ρ).map R.inclusionZero).f p
  comm' p p' _ := ((cechFunctorZ U O ρ).map R.inclusionZero).comm p p'

/-- The flipped Čech bicomplex of an injective resolution has finitely many nonzero terms on each
antidiagonal. -/
theorem diagonalFinite_cechBicomplex_flip :
    DiagonalFinite (cechBicomplex U O ρ R.cochainComplex).flip :=
  diagonalFinite_of_isZero_of_neg
    (fun p q hp => isZero_cechBicomplex_X_X _ q p (Or.inr hp))
    fun p q hq => isZero_cechBicomplex_X_X _ q p
      (Or.inl (R.cochainComplex.isZero_of_isStrictlyGE 0 q hq))

/-- The row of the flipped Čech bicomplex in Čech degree `m` is the complex of sections over
`U^{m+1}` of the resolution. -/
def cechBicomplexFlipXIso (m : ℕ) :
    (cechBicomplex U O ρ R.cochainComplex).flip.X (m : ℤ) ≅
      ((cechTermFunctor U O ρ m).mapHomologicalComplex (up ℤ)).obj R.cochainComplex :=
  (NatIso.mapHomologicalComplex (cechFunctorZEvalIso U O ρ m) (up ℤ)).app R.cochainComplex

variable {U} in
/-- **The hypotheses of [Stacks, Tag 0133] for the rows of the Čech bicomplex of an injective
resolution of a module acyclic on every power of `U`.** -/
theorem hypotheses_cechRowAugmentation
    (hM : ∀ (m : ℕ) (q : ℤ), q ≠ 0 → (((SheafOfModules.evaluation O
      (op ((cechNerve U).obj (op ⦋m⦌)))).mapHomologicalComplex (up ℤ)).obj
        R.cochainComplex).ExactAt q) :
    Hypotheses _ (cechBicomplex U O ρ R.cochainComplex).flip (cechRowAugmentation U O ρ R) where
  diagonalFinite := diagonalFinite_cechBicomplex_flip U O ρ R
  zero_of_neg p q hq := isZero_cechBicomplex_X_X _ q p
    (Or.inl (R.cochainComplex.isZero_of_isStrictlyGE 0 q (by omega)))
  exactAt_of_ne_zero p q hq := by
    rcases lt_or_ge p 0 with hp | hp
    · exact HomologicalComplex.ExactAt.of_isZero (isZero_cechBicomplex_X_X _ q p (Or.inr hp))
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = p := ⟨p.toNat, by omega⟩
      exact (exactAt_cechTermFunctor_mapHomologicalComplex U O ρ m R q (hM m q hq)).of_iso
        (cechBicomplexFlipXIso U O ρ R m).symm
  inducesIsoKernel p := by
    have hz : ((cechFunctorZ U O ρ).map R.inclusionZero).f p ≫
        ((cechBicomplex U O ρ R.cochainComplex).flip.X p).d 0 1 = 0 := by
      change ((cechFunctorZ U O ρ).map R.inclusionZero).f p ≫
        ((cechFunctorZ U O ρ).map (R.cochainComplex.d 0 1)).f p = 0
      rw [← HomologicalComplex.comp_f, ← Functor.map_comp, R.inclusionZero_comp_d,
        Functor.map_zero, HomologicalComplex.zero_f]
    refine ⟨hz, ?_⟩
    rcases lt_or_ge p 0 with hp | hp
    · refine StacksDraft.TotalComplexQuasiIso.isIso_of_isZero _
        (isZero_cechFunctorZ_X U O ρ M p hp) ?_
      exact IsZero.of_mono (kernel.ι _) (isZero_cechBicomplex_X_X _ 0 p (Or.inr hp))
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = p := ⟨p.toNat, by omega⟩
      let G := cechTermFunctor U O ρ m
      let e := cechFunctorZEvalIso U O ρ m
      let := HasDerivedCategory.standard (SheafOfModules.{u} O)
      have hS := Stacks.CechSite.Acyclic.exact_inclusionZero R
      have hmono : Mono R.inclusionZero := Stacks.CechSite.Acyclic.mono_inclusionZero R
      have hSG := hS.map_of_mono_of_preservesKernel G hmono inferInstance
      have eS : (ShortComplex.mk R.inclusionZero (R.cochainComplex.d 0 1)
          R.inclusionZero_comp_d).map G ≅ ShortComplex.mk
            (((cechFunctorZ U O ρ).map R.inclusionZero).f (m : ℤ))
            (((cechBicomplex U O ρ R.cochainComplex).flip.X (m : ℤ)).d 0 1) hz :=
        ShortComplex.isoMk (e.app M).symm (e.app (R.cochainComplex.X 0)).symm
          (e.app (R.cochainComplex.X 1)).symm
          (e.inv.naturality R.inclusionZero).symm (e.inv.naturality (R.cochainComplex.d 0 1)).symm
      have hmonoG : Mono (G.map R.inclusionZero) := inferInstance
      have : Mono (((cechFunctorZ U O ρ).map R.inclusionZero).f (m : ℤ)) := by
        have h := e.inv.naturality R.inclusionZero
        have h2 : ((cechFunctorZ U O ρ).map R.inclusionZero).f (m : ℤ) =
            (e.app M).hom ≫ G.map R.inclusionZero ≫ (e.app (R.cochainComplex.X 0)).inv := by
          have h3 := e.hom.naturality R.inclusionZero
          change _ = (e.hom.app M ≫ G.map R.inclusionZero) ≫ e.inv.app _
          rw [← h3, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
          rfl
        rw [h2]
        infer_instance
      have : Mono ((cechRowAugmentation U O ρ R).f (m : ℤ)) := this
      exact isIso_kernelLift_of_mono_of_exact' _ _ _ (ShortComplex.exact_of_iso eS hSG)

/-! ### The comparison -/

variable {U} in
/-- **The Čech complex of an object covering the final object computes cohomology.** Let `U` be
an object covering the final object of a ringed site, all of whose powers `U^{m+1}` exist, and let
`M` be a module with no higher cohomology on any of them, in the sense that the sections over
each `U^{m+1}` of an injective resolution of `M` are exact away from degree zero. Then the Čech
complex of `M` for `U`, over a base ring `A` mapping to the global sections of the structure sheaf,
and the complex of global sections of the resolution both map quasi-isomorphically to the total
complex of the Čech bicomplex of the resolution. -/
theorem exists_quasiIso_cechFunctorZ (hU : J.CoversTop fun _ : Unit => U)
    (hM : ∀ (m : ℕ) (q : ℤ), q ≠ 0 → (((SheafOfModules.evaluation O
      (op ((cechNerve U).obj (op ⦋m⦌)))).mapHomologicalComplex (up ℤ)).obj
        R.cochainComplex).ExactAt q) :
    ∃ (T : CochainComplex (ModuleCat.{max u u'} A) ℤ)
      (φ : ((globalSectionsOverBase O ρ).mapHomologicalComplex (up ℤ)).obj R.cochainComplex ⟶ T)
      (ψ : (cechFunctorZ U O ρ).obj M ⟶ T), QuasiIso φ ∧ QuasiIso ψ := by
  have hα := hypotheses_cechBicomplexAugmentation O ρ hU R
  have hβ := hypotheses_cechRowAugmentation O ρ R hM
  have : (cechBicomplex U O ρ R.cochainComplex).HasTotal (up ℤ) :=
    hasTotal_of_diagonalFinite _ hα.diagonalFinite
  have : (cechBicomplex U O ρ R.cochainComplex).flip.HasTotal (up ℤ) :=
    hasTotal_of_diagonalFinite _ hβ.diagonalFinite
  refine ⟨_, comparisonMapP _ _ _ hα, comparisonMapP _ _ _ hβ ≫
    ((cechBicomplex U O ρ R.cochainComplex).totalFlipIso (up ℤ)).hom, inferInstance, ?_⟩
  infer_instance

end Stacks.CechTop

end
