module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsComparison
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-!
# Resolving a bounded below complex column by column

Let `C` be an abelian category with functorial injective embeddings. Then the objects of `C` have
a *functorial* injective resolution `X ↦ R(X)`, concentrated in nonnegative degrees
([Stacks, Tag 0141]). Applying it termwise to a cochain complex `K` which vanishes in negative
degrees gives a double complex `R(K)^{p,q} = R(K^p)^q` whose `p`-th column resolves `K^p`. Its
total complex is then a bounded below complex of injective objects receiving a
quasi-isomorphism from `K` ([Stacks, Tag 0133]); in particular it is K-injective.

Unlike a Cartan–Eilenberg resolution, this double complex is strictly functorial in `K`, and
its columns are the resolutions of the individual terms `K^p`. This is what makes it suitable
for comparing a right derived functor of a complex with the right derived functors of its terms.

## Main definitions

* `StacksDraft.ColumnResolution.FunctorialResolution`: a functorial injective resolution of the
  objects of `C`, concentrated in nonnegative degrees.
* `StacksDraft.ColumnResolution.FunctorialResolution.bicomplex`: the double complex `R(K)`.
* `StacksDraft.ColumnResolution.FunctorialResolution.augmentation`: the augmentation from `K`,
  placed in row zero, to `R(K)`.
* `StacksDraft.ColumnResolution.FunctorialResolution.totalComparison`: the quasi-isomorphism
  `K ⟶ Tot(R(K))`.

## Main results

* `StacksDraft.ColumnResolution.exists_functorialResolution`: functorial injective embeddings
  give a functorial resolution.
* `StacksDraft.ColumnResolution.FunctorialResolution.isKInjective_total`: `Tot(R(K))` is
  K-injective.
* `StacksDraft.ColumnResolution.FunctorialResolution.totalComparison_naturality`: the comparison
  is natural in `K`.

## References

* [Stacks Project, Tag 0141](https://stacks.math.columbia.edu/tag/0141)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory Limits ZeroObject HomologicalComplex StacksDraft.TotalComplexQuasiIso

namespace StacksDraft.ColumnResolution

universe v u

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- A **functorial injective resolution** of the objects of an abelian category, concentrated in
nonnegative degrees: a functor `R` to cochain complexes with a natural quasi-isomorphism
`ν_X : X[0] ⟶ R(X)`, such that each `R(X)` vanishes in negative degrees, has injective terms, and
is zero when `X` is. -/
structure FunctorialResolution where
  /-- The resolution functor. -/
  F : C ⥤ CochainComplex C ℤ
  /-- The augmentation `X[0] ⟶ R(X)`. -/
  ν : HomologicalComplex.single C (ComplexShape.up ℤ) 0 ⟶ F
  /-- Each component `X[0] ⟶ R(X)` of the augmentation is a quasi-isomorphism. -/
  quasiIso_ν : ∀ X, QuasiIso (ν.app X)
  /-- Each `R(X)` vanishes in negative degrees. -/
  isStrictlyGE : ∀ X, (F.obj X).IsStrictlyGE 0
  /-- Each term `R(X)^n` is injective. -/
  injective : ∀ X n, Injective ((F.obj X).X n)
  /-- `R(X)` is zero when `X` is zero. -/
  isZero : ∀ X, IsZero X → IsZero (F.obj X)

variable {C}

/-- Functorial injective embeddings give a functorial injective resolution of the objects,
concentrated in nonnegative degrees ([Stacks, Tag 0141]). -/
theorem exists_functorialResolution (h : HasFunctorialInjectiveEmbeddings C) :
    Nonempty (FunctorialResolution C) := by
  obtain ⟨J, η, hη⟩ := StacksDraft.DerivedSectionsComparison.exists_injectiveEmbeddingData C h
  obtain ⟨F, α, hqis, hge⟩ :=
    CochainComplex.Plus.exists_functorial_injective_resolution_isStrictlyGE C J η hη
  let S := StacksDraft.DerivedSectionsComparison.singlePlus C
  have hS : ∀ (X : C) (a : ℤ), IsZero X → (S.obj X).obj.IsStrictlyGE a := by
    intro X a hX
    refine ⟨fun n _ => ?_⟩
    dsimp [S, StacksDraft.DerivedSectionsComparison.singlePlus]
    rcases eq_or_ne n 0 with rfl | hn
    · exact (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).isZero_iff.2 hX
    · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
  exact ⟨{
    F := S ⋙ F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus ⋙ CochainComplex.Plus.ι C
    ν := Functor.whiskerLeft S (Functor.whiskerRight α (CochainComplex.Plus.ι C))
    quasiIso_ν := fun X => hqis (S.obj X)
    isStrictlyGE := fun X => hge (S.obj X) 0 (by
      change CochainComplex.IsStrictlyGE
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X) 0
      infer_instance)
    injective := fun X n => by
      change Injective ((InjectiveObject.ι C).obj ((F.obj (S.obj X)).obj.X n))
      infer_instance
    isZero := fun X hX => by
      rw [IsZero.iff_id_eq_zero]
      ext n
      refine IsZero.eq_of_src ?_ _ _
      have : CochainComplex.IsStrictlyGE
          ((S ⋙ F ⋙ (InjectiveObject.ι C).mapCochainComplexPlus ⋙ CochainComplex.Plus.ι C).obj X)
          (n + 1) := hge (S.obj X) (n + 1) (hS X (n + 1) hX)
      exact CochainComplex.isZero_of_isStrictlyGE _ (n + 1) n (by omega) }⟩

namespace FunctorialResolution

variable (R : FunctorialResolution C)

/-- The augmentation `X[0] ⟶ R(X)` is a quasi-isomorphism. -/
instance (X : C) : QuasiIso (R.ν.app X) := R.quasiIso_ν X

/-- `R(X)` vanishes in negative degrees. -/
instance (X : C) : (R.F.obj X).IsStrictlyGE 0 := R.isStrictlyGE X

/-- The terms of `R(X)` are injective. -/
instance (X : C) (n : ℤ) : Injective ((R.F.obj X).X n) := R.injective X n

/-- The resolution functor preserves zero morphisms. -/
instance : R.F.PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_map_zero_object
    ((R.isZero 0 (isZero_zero C)).iso (isZero_zero _))

/-- The degree-zero component of the augmentation, read out of `X` itself. -/
abbrev aug₀ (X : C) : X ⟶ (R.F.obj X).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ (R.ν.app X).f 0

/-- The comparison `X ≅ Z^0(R(X))` through which the augmentation factors. -/
def cyclesIso (X : C) : X ≅ (R.F.obj X).cycles 0 := by
  let A := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X
  let B := R.F.obj X
  have hA₁ : IsIso (A.iCycles 0) := A.isIso_iCycles 0 1 (by simp)
    (IsZero.eq_of_tgt (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)) _ _)
  have hπB : IsIso (B.homologyπ 0) := B.isIso_homologyπ (-1) 0 (by simp)
    (IsZero.eq_of_src (CochainComplex.isZero_of_isStrictlyGE B 0 (-1) (by omega)) _ _)
  have hπA : IsIso (A.homologyπ 0) := A.isIso_homologyπ (-1) 0 (by simp)
    (IsZero.eq_of_src (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)) _ _)
  have hH : IsIso (homologyMap (R.ν.app X) 0) :=
    (quasiIsoAt_iff_isIso_homologyMap (R.ν.app X) 0).1 inferInstance
  have hZ : IsIso (cyclesMap (R.ν.app X) 0) := by
    have : IsIso (cyclesMap (R.ν.app X) 0 ≫ B.homologyπ 0) := by
      rw [← homologyπ_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (B.homologyπ 0)
  exact (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).symm ≪≫
    (asIso (A.iCycles 0)).symm ≪≫ asIso (cyclesMap (R.ν.app X) 0)

/-- The isomorphism `X ≅ Z^0(R(X))` followed by the inclusion of cycles is `aug₀ X`. -/
lemma cyclesIso_hom_iCycles (X : C) :
    (R.cyclesIso X).hom ≫ (R.F.obj X).iCycles 0 = R.aug₀ X := by
  simp [cyclesIso, aug₀, cyclesMap_i]

/-- The map `aug₀ X : X ⟶ R(X)^0` is a monomorphism. -/
instance (X : C) : Mono (R.aug₀ X) := by
  rw [← R.cyclesIso_hom_iCycles]
  infer_instance

/-- The degree-zero component of the augmentation `X[0] ⟶ R(X)` is a monomorphism. -/
instance mono_ν_f_zero (X : C) : Mono ((R.ν.app X).f 0) := by
  rw [show (R.ν.app X).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).hom ≫ R.aug₀ X by simp [aug₀]]
  infer_instance

/-- The map `aug₀` is natural: `aug₀ X ≫ R(g)^0 = g ≫ aug₀ Y` for `g : X ⟶ Y`. -/
lemma aug₀_naturality {X Y : C} (g : X ⟶ Y) :
    R.aug₀ X ≫ (R.F.map g).f 0 = g ≫ R.aug₀ Y := by
  have h := congrArg (fun φ => HomologicalComplex.Hom.f φ 0) (R.ν.naturality g)
  dsimp at h
  simp only [aug₀, Category.assoc, ← h]
  rw [HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc, Category.assoc]

/-- The composite of `aug₀ X` with the differential `R(X)^0 ⟶ R(X)^1` is zero. -/
lemma aug₀_comp_d (X : C) : R.aug₀ X ≫ (R.F.obj X).d 0 1 = 0 := by
  rw [← R.cyclesIso_hom_iCycles, Category.assoc, HomologicalComplex.iCycles_d, comp_zero]

/-- The augmentation `X ⟶ R(X)^0` is a kernel of the first differential of `R(X)`. -/
def isLimitAug₀ (X : C) : IsLimit (KernelFork.ofι (R.aug₀ X) (R.aug₀_comp_d X)) :=
  IsKernel.isoKernel _ _ ((R.F.obj X).cyclesIsKernel 0 1 (by simp)) (R.cyclesIso X)
    (R.cyclesIso_hom_iCycles X)

/-- **The degree-zero cycles of `R(X)` are `X`.** The augmentation identifies `X` with the
kernel of the first differential of `R(X)`. -/
lemma isIso_kernelLift_aug₀ (X : C) :
    IsIso (kernel.lift ((R.F.obj X).d 0 1) (R.aug₀ X) (R.aug₀_comp_d X)) := by
  set B := R.F.obj X
  have hk : IsIso (kernel.lift (B.d 0 1) (B.iCycles 0) (B.iCycles_d 0 1)) := by
    refine ⟨⟨B.liftCycles (kernel.ι (B.d 0 1)) 1 (by simp) (kernel.condition _), ?_, ?_⟩⟩
    · rw [← cancel_mono (B.iCycles 0)]
      simp
    · rw [← cancel_mono (kernel.ι _)]
      simp
  have e : kernel.lift (B.d 0 1) (R.aug₀ X) (R.aug₀_comp_d X) =
      (R.cyclesIso X).hom ≫ kernel.lift (B.d 0 1) (B.iCycles 0) (B.iCycles_d 0 1) := by
    rw [← cancel_mono (kernel.ι _)]
    simp [B, cyclesIso_hom_iCycles]
  rw [e]
  infer_instance

/-- The double complex `R(K)^{p,q} = R(K^p)^q` of a cochain complex `K`. -/
abbrev bicomplex (K : CochainComplex C ℤ) :
    HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (R.F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The augmentation `K ⟶ R(K)^{•,0}` of the double complex. -/
def augmentation (K : CochainComplex C ℤ) : K ⟶ rowZero (R.bicomplex K) where
  f p := R.aug₀ (K.X p)
  comm' p p' _ := by
    change R.aug₀ (K.X p) ≫ (R.F.map (K.d p p')).f 0 = K.d p p' ≫ R.aug₀ (K.X p')
    exact R.aug₀_naturality _

/-- The `p`-th component of the augmentation `K ⟶ R(K)^{•,0}` is `aug₀ (K^p)`. -/
lemma augmentation_f (K : CochainComplex C ℤ) (p : ℤ) :
    (R.augmentation K).f p = R.aug₀ (K.X p) := rfl

variable (K : CochainComplex C ℤ) [K.IsStrictlyGE 0]

/-- The column `R(K^p)` is zero for `p < 0`. -/
lemma isZero_bicomplex_X (p : ℤ) (hp : p < 0) : IsZero ((R.bicomplex K).X p) :=
  R.isZero _ (K.isZero_of_isStrictlyGE 0 p hp)

omit [K.IsStrictlyGE 0] in
/-- The term `R(K)^{p,q}` is zero for `q < 0`. -/
lemma isZero_bicomplex_X_X (p q : ℤ) (hq : q < 0) : IsZero (((R.bicomplex K).X p).X q) :=
  (R.F.obj (K.X p)).isZero_of_isStrictlyGE 0 q hq

/-- **The columns of `R(K)` resolve the terms of `K`**: the hypotheses of [Stacks, Tag 0133]. -/
lemma hypotheses : Hypotheses K (R.bicomplex K) (R.augmentation K) where
  diagonalFinite n :=
    ((finite_not_isZero_of_bounded (R.bicomplex K) 0 (R.isZero_bicomplex_X_X K)
      (R.isZero_bicomplex_X K) n).image Prod.fst).subset
      fun p hp => ⟨(p, n - p), ⟨by simp, hp⟩, rfl⟩
  zero_of_neg := R.isZero_bicomplex_X_X K
  exactAt_of_ne_zero p q hq := by
    change (R.F.obj (K.X p)).ExactAt q
    rw [← quasiIsoAt_iff_exactAt (R.ν.app (K.X p)) q
      (HomologicalComplex.exactAt_single_obj _ _ _ _ hq)]
    infer_instance
  inducesIsoKernel p := ⟨R.aug₀_comp_d (K.X p), R.isIso_kernelLift_aug₀ (K.X p)⟩

/-- The double complex `R(K)` has a total complex. -/
instance hasTotal_bicomplex : (R.bicomplex K).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_bounded _ 0 (R.isZero_bicomplex_X_X K) (R.isZero_bicomplex_X K)

/-- The total complex `Tot(R(K))`. -/
abbrev total : CochainComplex C ℤ := (R.bicomplex K).total (ComplexShape.up ℤ)

/-- **The comparison `K ⟶ Tot(R(K))`**, a quasi-isomorphism by [Stacks, Tag 0133]. -/
def totalComparison : K ⟶ R.total K :=
  comparisonMapP K (R.bicomplex K) (R.augmentation K) (R.hypotheses K)

/-- The comparison `K ⟶ Tot(R(K))` is a quasi-isomorphism. -/
instance : QuasiIso (R.totalComparison K) := by
  dsimp only [totalComparison]
  infer_instance

/-- In degree `n`, the comparison `K ⟶ Tot(R(K))` is `aug₀ (K^n)` followed by the inclusion of
`R(K)^{n,0}` into `Tot(R(K))^n`. -/
lemma totalComparison_f (n : ℤ) :
    (R.totalComparison K).f n =
      R.aug₀ (K.X n) ≫ (R.bicomplex K).ιTotal (ComplexShape.up ℤ) n 0 n (by simp) := rfl

/-- The terms of `Tot(R(K))` are injective. -/
instance (n : ℤ) : Injective ((R.total K).X n) :=
  injective_total_X_of_bounded _ 0 (R.isZero_bicomplex_X_X K) (R.isZero_bicomplex_X K)
    (fun p q => R.injective (K.X p) q) n

/-- `Tot(R(K))` vanishes in negative degrees. -/
instance : (R.total K).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact HomologicalComplex₂.isZero_total_X_of_isZero _ _ n (fun p q hpq => by
    have h₁ : p + q = n := hpq
    have h₂ : n < 0 := hn
    by_cases hp : p < 0
    · exact Functor.map_isZero (HomologicalComplex.eval C (ComplexShape.up ℤ) q)
        (R.isZero_bicomplex_X K p hp)
    · exact R.isZero_bicomplex_X_X K p q (by omega))

/-- **`Tot(R(K))` is K-injective**: it is a bounded below complex of injective objects. -/
instance isKInjective_total : (R.total K).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

/-- Each component of the comparison `K ⟶ Tot(R(K))` is a monomorphism. -/
instance (n : ℤ) : Mono ((R.totalComparison K).f n) := by
  rw [totalComparison_f]
  have : Mono ((R.bicomplex K).ιTotal (ComplexShape.up ℤ) n 0 n (by simp)) := by
    refine ⟨fun {Z} g₁ g₂ h => ?_⟩
    have := congrArg (· ≫ (R.bicomplex K).totalDesc (fun p q _ =>
      if hpq : p = n ∧ q = 0 then eqToHom (by obtain ⟨rfl, rfl⟩ := hpq; rfl) else 0)) h
    simpa using this
  infer_instance

variable {K} in
/-- **The comparison is natural** in the resolved complex. -/
lemma totalComparison_naturality {M : CochainComplex C ℤ} [M.IsStrictlyGE 0] (ρ : K ⟶ M) :
    R.totalComparison K ≫ HomologicalComplex₂.total.map
        ((R.F.mapHomologicalComplex (ComplexShape.up ℤ)).map ρ) (ComplexShape.up ℤ) =
      ρ ≫ R.totalComparison M :=
  comparisonMapP_naturality K (R.bicomplex K) (R.augmentation K) (R.hypotheses K)
    (R.hypotheses M) ρ _ (by
      ext p
      exact R.aug₀_naturality (ρ.f p))

/-! ### Applying an additive functor to the double complex -/

section Map

variable {D : Type*} [Category D] [Abelian D] (B : C ⥤ D) [B.Additive]

/-- The double complex `B(R(K))`. -/
abbrev mapBicomplex : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  HomologicalComplex₂.TotalMap.mapBicomplex B (R.bicomplex K)

/-- The column `B(R(K^p))` is zero for `p < 0`. -/
lemma isZero_mapBicomplex_X (p : ℤ) (hp : p < 0) : IsZero ((R.mapBicomplex K B).X p) :=
  Functor.map_isZero (B.mapHomologicalComplex _) (R.isZero_bicomplex_X K p hp)

omit [K.IsStrictlyGE 0] in
/-- The term `B(R(K)^{p,q})` is zero for `q < 0`. -/
lemma isZero_mapBicomplex_X_X (p q : ℤ) (hq : q < 0) :
    IsZero (((R.mapBicomplex K B).X p).X q) :=
  B.map_isZero (R.isZero_bicomplex_X_X K p q hq)

/-- The double complex `B(R(K))` has a total complex. -/
instance hasTotal_mapBicomplex : (R.mapBicomplex K B).HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_bounded _ 0 (R.isZero_mapBicomplex_X_X K B) (R.isZero_mapBicomplex_X K B)

/-- **`Tot(B(R(K))) ≅ B(Tot(R(K)))`**, since only finitely many terms are nonzero in each total
degree. -/
def mapTotalIso :
    (R.mapBicomplex K B).total (ComplexShape.up ℤ) ≅
      (B.mapHomologicalComplex (ComplexShape.up ℤ)).obj (R.total K) :=
  HomologicalComplex₂.TotalMap.totalIsoOfFinite B (R.bicomplex K)
    (finite_not_isZero_of_bounded _ 0 (R.isZero_bicomplex_X_X K) (R.isZero_bicomplex_X K))

end Map

end FunctorialResolution

end StacksDraft.ColumnResolution

end
