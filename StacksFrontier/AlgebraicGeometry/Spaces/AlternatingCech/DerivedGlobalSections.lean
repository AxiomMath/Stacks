module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Opposite
public import StacksFrontier.Algebra.Homology.HomBicomplexCohomology
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.ExtSpectralSequence

/-!
# The canonical map from the alternating Čech complex to `RΓ(X, ℱ)`

Let `S` be a scheme, let `f : U ⟶ X` be a surjective étale morphism of algebraic spaces over `S`
and let `ℱ` be an abelian sheaf on the spaces-étale site of `X`.  Writing `K^p = ∧^{p+1} f_! ℤ`
for the terms of the Koszul complex and `Č^•_alt(f, ℱ) = Hom(K^•, ℱ)` for the alternating Čech
complex of [Stacks 0724], this file builds the canonical map

`Č^•_alt(f, ℱ) ⟶ RΓ(X, ℱ)`

in `D(Ab)`, which is the first assertion of [Stacks 0725]; the spectral sequence which is its
second assertion is
`AlgebraicGeometry.Space.SpacesEtale.exists_alternatingCechCohomologySpectralSequence` in
`StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.ExtSpectralSequence`.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.globalSectionsCochainComplex` is the complex
  `Γ(X, I^•) = Hom(ℤ, I^•)` of global sections of a complex of abelian sheaves.
* `AlgebraicGeometry.Space.SpacesEtale.derivedGlobalSections` is `RΓ(X, ℱ)`, the object of
  `D(Ab)` represented by `Γ(X, I^•)` for `I^•` the chosen injective resolution of `ℱ`.
* `AlgebraicGeometry.Space.SpacesEtale.alternatingCechComplexExtend` is the alternating Čech
  complex of [Stacks 0724] read as a cochain complex indexed by `ℤ`.
* `AlgebraicGeometry.Space.SpacesEtale.alternatingCechToDerivedGlobalSections` is
  **[Stacks 0725], the canonical map**.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.alternatingCechCochainComplexIsoExtend`: the complex
  `Hom(K^•, ℱ)` indexed by `ℤ` is the alternating Čech complex of [Stacks 0724], extended by
  zero to the negative degrees.
* `AlgebraicGeometry.Space.SpacesEtale.hypotheses_koszulHomBicomplex_flip`: the rows
  `Hom(K^•, I^q)` of the Hom bicomplex resolve the global sections `Γ(X, I^q)`, which is the
  input to [Stacks 0133].
* `AlgebraicGeometry.Space.SpacesEtale.globalSectionsHomologyAddEquivSheafH` and
  `AlgebraicGeometry.Space.SpacesEtale.derivedGlobalSectionsHomologyAddEquivSheafH`:
  `H^n(RΓ(X, ℱ)) = H^n(X, ℱ)`.

## Implementation notes

The construction is the one of [Stacks 0725]: for `I^•` an injective resolution of `ℱ`, the Hom
bicomplex `Hom(K^p, I^q)` has a total complex, the alternating Čech complex maps into it by
`AlgebraicGeometry.Space.SpacesEtale.alternatingCechToTotal` (postcomposition with `ℱ ⟶ I^0`
into the column `q = 0`), and the complex of global sections `Γ(X, I^•)` maps into it by
[Stacks 0133] — `comparisonMapP`, read through `HomologicalComplex₂.totalFlipIso` — as a
*quasi-isomorphism*.  The canonical map is the first composed with the inverse of the second in
`D(Ab)`.

The hypothesis of [Stacks 0133] that needs the resolution property of `K^•` is that each row
`Hom(K^•, I^q)` of the bicomplex is exact outside the Koszul degree `0`, with `Γ(X, I^q)` the
kernel of its first differential.  This holds because `I^q` is injective and the augmented
Koszul complex is exact: the functor `Hom(-, I^q)` preserves homology
(`CochainComplex.preservesHomology_preadditiveYoneda_obj`, from Mathlib's
`CategoryTheory.Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj`), so it
carries the quasi-isomorphism `K^• ⟶ ℤ[0]` of [Stacks 0723] — read in the opposite category
through `CochainComplex.opEquivalence`, where quasi-isomorphisms are detected by
`CochainComplex.quasiIso_opEquivalence_functor_map_iff` — to a quasi-isomorphism
`Hom(ℤ[0]^{-•}, I^q) ⟶ Hom(K^{-•}, I^q)` whose source is concentrated in degree `0`.
Translating that into the kernel statement is
`HomologicalComplex.isIso_kernelLift_of_quasiIsoAt`.

The row of the Hom bicomplex in `I`-degree `q`, the complex `Hom(K^{-•}, I^q)`, has three
spellings which are definitionally but not syntactically equal:
`(koszulHomBicomplex B S hS X U I).flip.X q`,
`CochainComplex.yonedaOp (I.X q) (koszulCochainComplex ...)` and
`alternatingCechCochainComplex B S hS X U (I.X q)`. Crossing between them is free at the level
of objects and morphisms of complexes, but *not* at the level of the `kernel` of a differential:
a kernel is a `limit`, whose `HasLimit` instance is found by instance search, and unifying two
of them unfolds the whole bicomplex. So `rowAugmentation` is stated in the bicomplex spelling.

`RΓ(X, ℱ)` is *defined* as the image in `D(Ab)` of `Γ(X, I^•)` for the resolution chosen by
`CochainComplex.injectiveResolutionSingle`. By `derivedGlobalSectionsHomologyAddEquivSheafH`,
its cohomology is Mathlib's sheaf cohomology
`CategoryTheory.Sheaf.H`, by [Stacks 06XR] in the form
`CochainComplex.HomBicomplex.coyonedaHomologyAddEquivZExt`, since `Γ = Hom(ℤ, -)` and sheaf
cohomology is `Ext` out of the constant sheaf `ℤ`.

## References

* [Stacks, Tag 0725](https://stacks.math.columbia.edu/tag/0725)
* [Stacks, Tag 0724](https://stacks.math.columbia.edu/tag/0724)
* [Stacks, Tag 0723](https://stacks.math.columbia.edu/tag/0723)
* [Stacks, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks, Tag 0136](https://stacks.math.columbia.edu/tag/0136)
* [Stacks, Tag 06XR](https://stacks.math.columbia.edu/tag/06XR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The degree `0` component of a morphism of cochain complexes is killed by the differential of
the target as soon as the source vanishes in degree `1`. -/
lemma comp_d_eq_zero_of_isZero_X {D K : CochainComplex A ℤ} (φ : D ⟶ K)
    (h : IsZero (D.X 1)) : φ.f 0 ≫ K.d 0 1 = 0 := by
  rw [φ.comm 0 1, h.eq_of_tgt (D.d 0 1) 0, zero_comp]

/-- **A quasi-isomorphism out of a complex concentrated in degree `0` identifies that degree
with a kernel.** For `φ : D ⟶ K` a quasi-isomorphism in degree `0`, with `D` vanishing in
degrees `1` and `-1` and `K` vanishing in degree `-1`, the map `D^0 ⟶ K^0` induces an
isomorphism onto the kernel of `K^0 ⟶ K^1`. -/
lemma isIso_kernelLift_of_quasiIsoAt {D K : CochainComplex A ℤ} (φ : D ⟶ K)
    (h1 : IsZero (D.X 1)) (hm1 : IsZero (D.X (-1))) (hkm1 : IsZero (K.X (-1)))
    [QuasiIsoAt φ 0] (hφ : φ.f 0 ≫ K.d 0 1 = 0) :
    IsIso (kernel.lift (K.d 0 1) (φ.f 0) hφ) := by
  have hiD : IsIso (D.iCycles 0) := D.isIso_iCycles 0 1 (by simp) (h1.eq_of_tgt _ _)
  have hπD : IsIso (D.homologyπ 0) := D.isIso_homologyπ (-1) 0 (by simp) (hm1.eq_of_src _ _)
  have hπK : IsIso (K.homologyπ 0) := K.isIso_homologyπ (-1) 0 (by simp) (hkm1.eq_of_src _ _)
  have hhom : IsIso (homologyMap φ 0) := (quasiIsoAt_iff_isIso_homologyMap φ 0).1 inferInstance
  have hcyc : IsIso (cyclesMap φ 0) := by
    have h : IsIso (cyclesMap φ 0 ≫ K.homologyπ 0) := by
      rw [← homologyπ_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (K.homologyπ 0)
  let hk := K.cyclesIsKernel 0 1 (by simp)
  let e : K.cycles 0 ≅ kernel (K.d 0 1) := IsLimit.conePointUniqueUpToIso hk (limit.isLimit _)
  have he : e.hom ≫ kernel.ι (K.d 0 1) = K.iCycles 0 :=
    IsLimit.conePointUniqueUpToIso_hom_comp hk (limit.isLimit _) WalkingParallelPair.zero
  have key : kernel.lift (K.d 0 1) (φ.f 0) hφ = inv (D.iCycles 0) ≫ cyclesMap φ 0 ≫ e.hom := by
    refine (cancel_mono (kernel.ι (K.d 0 1))).1 ?_
    rw [kernel.lift_ι, Category.assoc, Category.assoc, he, cyclesMap_i, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  rw [key]
  infer_instance

/-- `comp_d_eq_zero_of_isZero_X`, read through an isomorphism of the source. -/
lemma comp_d_eq_zero_of_eq {D K : CochainComplex A ℤ} (φ : D ⟶ K) (h1 : IsZero (D.X 1))
    {W : A} (e : W ≅ D.X 0) (g : W ⟶ K.X 0) (hg : g = e.hom ≫ φ.f 0) :
    g ≫ K.d 0 1 = 0 := by
  subst hg
  rw [Category.assoc, comp_d_eq_zero_of_isZero_X φ h1, comp_zero]

/-- `isIso_kernelLift_of_quasiIsoAt`, read through an isomorphism of the source. -/
lemma isIso_kernelLift_of_quasiIsoAt' {D K : CochainComplex A ℤ} (φ : D ⟶ K)
    (h1 : IsZero (D.X 1)) (hm1 : IsZero (D.X (-1))) (hkm1 : IsZero (K.X (-1)))
    [QuasiIsoAt φ 0] {W : A} (e : W ≅ D.X 0) (g : W ⟶ K.X 0) (hg : g = e.hom ≫ φ.f 0)
    (hg0 : g ≫ K.d 0 1 = 0) :
    IsIso (kernel.lift (K.d 0 1) g hg0) := by
  subst hg
  have hφ := comp_d_eq_zero_of_isZero_X φ h1
  have := isIso_kernelLift_of_quasiIsoAt φ h1 hm1 hkm1 hφ
  have heq : kernel.lift (K.d 0 1) (e.hom ≫ φ.f 0) hg0 =
      e.hom ≫ kernel.lift (K.d 0 1) (φ.f 0) hφ := by
    refine (cancel_mono (kernel.ι (K.d 0 1))).1 ?_
    rw [kernel.lift_ι, Category.assoc, kernel.lift_ι]
  rw [heq]
  infer_instance

end HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- `Hom(K⁻ᵖ, J)`: the complex obtained by applying `Hom_C(-, J)` to the opposite of a cochain
complex `K`. -/
abbrev yonedaOp (J : C) (K : CochainComplex C ℤ) : CochainComplex AddCommGrpCat.{v} ℤ :=
  ((preadditiveYoneda.obj J).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((opEquivalence C).functor.obj (op K))

/-- `Hom_C(-, J)` applied to a morphism of cochain complexes. -/
def yonedaOpMap (J : C) {K L : CochainComplex C ℤ} (a : K ⟶ L) : yonedaOp J L ⟶ yonedaOp J K :=
  ((preadditiveYoneda.obj J).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((opEquivalence C).functor.map a.op)

/-- **[Stacks 0136].** `Hom_C(-, J)` is exact for `J` injective, hence preserves homology. -/
lemma preservesHomology_preadditiveYoneda_obj (J : C) [Injective J] :
    (preadditiveYoneda.obj J).PreservesHomology := by
  have := (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj J).mp
    inferInstance
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- `Hom_C(-, J)` carries a quasi-isomorphism to a quasi-isomorphism, for `J` injective. -/
lemma quasiIso_yonedaOpMap (J : C) [Injective J] {K L : CochainComplex C ℤ} (a : K ⟶ L)
    [QuasiIso a] : QuasiIso (yonedaOpMap J a) := by
  have h : QuasiIso ((opEquivalence C).functor.map a.op) :=
    (quasiIso_opEquivalence_functor_map_iff a).2 inferInstance
  have := preservesHomology_preadditiveYoneda_obj J
  exact inferInstanceAs (QuasiIso
    (((preadditiveYoneda.obj J).mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((opEquivalence C).functor.map a.op)))

/-- `Hom(K⁻ᵖ, J)` vanishes where `K` does. -/
lemma isZero_yonedaOp_X (J : C) (K : CochainComplex C ℤ) (p : ℤ) (h : IsZero (K.X (-p))) :
    IsZero ((yonedaOp J K).X p) :=
  (preadditiveYoneda.obj J).map_isZero h.op

end CochainComplex

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### The complex of global sections -/

/-- The complex `ℤ[0]`: the constant sheaf of integers placed in degree `0`. -/
abbrev constantIntSheafSingle :
    CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ :=
  (HomologicalComplex.single (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (ComplexShape.up ℤ) 0).obj (constantIntSheaf B S hS X)

/-- The complex of global sections `Γ(X, I^•) = Hom(ℤ, I^•)` of a complex of abelian sheaves on
the spaces-étale site of `X`. -/
def globalSectionsCochainComplex
    (I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ) :
    CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  ((preadditiveCoyoneda.obj (op (constantIntSheaf B S hS X))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I

/-- The trace `K^0 ⟶ ℤ`, read out of the term of `K^•` in cochain degree `0`. -/
def koszulCochainTrace (U : SpacesEtale B S hS X) :
    (koszulCochainComplex B S hS X U).X 0 ⟶ constantIntSheaf B S hS X :=
  (koszulCochainAugmentation B S hS X U).f 0 ≫
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (constantIntSheaf B S hS X)).hom

/-- The restriction of a global section of `I^q` along the trace `K^0 ⟶ ℤ`: the augmentation
of the rows of the Hom bicomplex by the complex of global sections. -/
def globalSectionsToRowZero (U : SpacesEtale B S hS X)
    (I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ) :
    globalSectionsCochainComplex B S hS X I ⟶
      rowZero (koszulHomBicomplex B S hS X U I).flip :=
  (NatTrans.mapHomologicalComplex
    (preadditiveCoyoneda.map (koszulCochainTrace B S hS X U).op)
    (ComplexShape.up ℤ)).app I

/-! ### The rows of the Hom bicomplex resolve the global sections -/

/-- The augmentation `Hom(ℤ[0]⁻ᵖ, I^q) ⟶ Hom(K⁻ᵖ, I^q)`, read as a morphism into the row of the
Hom bicomplex in `I`-degree `q`. -/
def rowAugmentation (U : SpacesEtale B S hS X)
    (I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ) (q : ℤ) :
    CochainComplex.yonedaOp (I.X q) (constantIntSheafSingle B S hS X) ⟶
      (koszulHomBicomplex B S hS X U I).flip.X q :=
  CochainComplex.yonedaOpMap (I.X q) (koszulCochainAugmentation B S hS X U)

/-- For a surjective cover and an injective `I^q`, the row augmentation is a
quasi-isomorphism: this is [Stacks 0723] pushed through the exact functor `Hom(-, I^q)`. -/
lemma quasiIso_rowAugmentation (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom)
    (I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ) (q : ℤ)
    (hinj : Injective (I.X q)) : QuasiIso (rowAugmentation B S hS X U I q) := by
  have := quasiIso_koszulCochainAugmentation B S hS X U hsurj
  exact CochainComplex.quasiIso_yonedaOpMap (I.X q) (koszulCochainAugmentation B S hS X U)

/-- `Hom(ℤ, I^q) ≅ Hom(ℤ[0]⁰, I^q)`. -/
def globalSectionsXIsoSingle
    (I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ) (q : ℤ) :
    (globalSectionsCochainComplex B S hS X I).X q ≅
      (CochainComplex.yonedaOp (I.X q) (constantIntSheafSingle B S hS X)).X 0 :=
  (preadditiveYoneda.obj (I.X q)).mapIso
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (constantIntSheaf B S hS X)).op

/-- The augmentation of the rows is the row augmentation, read through
`globalSectionsXIsoSingle`. -/
lemma globalSectionsToRowZero_f (U : SpacesEtale B S hS X)
    (I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ) (q : ℤ) :
    (globalSectionsToRowZero B S hS X U I).f q =
      (globalSectionsXIsoSingle B S hS X I q).hom ≫ (rowAugmentation B S hS X U I q).f 0 :=
  AddCommGrpCat.ext fun g => Category.assoc ((koszulCochainAugmentation B S hS X U).f 0)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (constantIntSheaf B S hS X)).hom g

/-- `Hom(ℤ[0]⁻ᵖ, J)` vanishes in every degree other than `0`. -/
private lemma isZero_yonedaOp_constantIntSheafSingle_X (J : Sheaf (topology B S hS X)
    AddCommGrpCat.{u + 1}) {q : ℤ} (hq : q ≠ 0) :
    IsZero ((CochainComplex.yonedaOp J (constantIntSheafSingle B S hS X)).X q) :=
  CochainComplex.isZero_yonedaOp_X _ _ _
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
      (constantIntSheaf B S hS X) (-q) (by omega))

/-- **The input to [Stacks 0133].** For `U ⟶ X` surjective and `I^•` a bounded below complex of
injectives, the rows `Hom(K^•, I^q)` of the Hom bicomplex are exact outside the Koszul degree
`0`, where the complex of global sections `Γ(X, I^q)` is the kernel of the first
differential. -/
theorem hypotheses_koszulHomBicomplex_flip (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom)
    (I : CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ)
    (hI : CochainComplex.plus _ I) (hinj : ∀ q, Injective (I.X q)) :
    Hypotheses (globalSectionsCochainComplex B S hS X I)
      (koszulHomBicomplex B S hS X U I).flip
      (globalSectionsToRowZero B S hS X U I) where
  diagonalFinite n :=
    ((koszulHomBicomplex_diagonalFinite B S hS X U I hI n).image Prod.snd).subset
      fun p hp => ⟨(n - p, p), ⟨by simp, hp⟩, rfl⟩
  zero_of_neg p q hq := isZero_koszulHomBicomplex_X_X_of_neg B S hS X U I q p hq
  exactAt_of_ne_zero p q hq := by
    have hqi := quasiIso_rowAugmentation B S hS X U hsurj I p (hinj p)
    exact (quasiIsoAt_iff_exactAt (rowAugmentation B S hS X U I p) q
      (HomologicalComplex.ExactAt.of_isZero
        (isZero_yonedaOp_constantIntSheafSingle_X B S hS X _ hq))).1 (hqi.quasiIsoAt q)
  inducesIsoKernel p := by
    have hqi := quasiIso_rowAugmentation B S hS X U hsurj I p (hinj p)
    have h1 := isZero_yonedaOp_constantIntSheafSingle_X B S hS X (I.X p) (q := 1) (by simp)
    have hm1 := isZero_yonedaOp_constantIntSheafSingle_X B S hS X (I.X p) (q := -1) (by simp)
    have hkm1 : IsZero (((koszulHomBicomplex B S hS X U I).flip.X p).X (-1)) :=
      isZero_koszulHomBicomplex_X_X_of_neg B S hS X U I (-1) p (by omega)
    have hα : (globalSectionsToRowZero B S hS X U I).f p ≫
        ((koszulHomBicomplex B S hS X U I).flip.X p).d 0 1 = 0 :=
      HomologicalComplex.comp_d_eq_zero_of_eq (rowAugmentation B S hS X U I p) h1
        (globalSectionsXIsoSingle B S hS X I p) _
        (globalSectionsToRowZero_f B S hS X U I p)
    have hqa : QuasiIsoAt (rowAugmentation B S hS X U I p) 0 := hqi.quasiIsoAt 0
    exact ⟨hα, HomologicalComplex.isIso_kernelLift_of_quasiIsoAt'
      (rowAugmentation B S hS X U I p) h1 hm1 hkm1
      (globalSectionsXIsoSingle B S hS X I p) _
      (globalSectionsToRowZero_f B S hS X U I p) hα⟩

/-! ### `Hom(K^•, ℱ)` is the alternating Čech complex of [Stacks 0724] -/

/-- The differential of `K^•` read in cochain degrees, in terms of the differential of the
Koszul complex. -/
lemma koszulCochainComplex_d_eq (U : SpacesEtale B S hS X) (n : ℕ) :
    (koszulCochainComplex B S hS X U).d (-((n : ℤ) + 1)) (-(n : ℤ)) =
      (koszulCochainComplexXIso B S hS X U (n + 1)).hom ≫
        (koszulComplex B S hS X U).d (n + 1) n ≫
          (koszulCochainComplexXIso B S hS X U n).inv :=
  HomologicalComplex.extend_d_eq (koszulComplex B S hS X U)
    ComplexShape.embeddingDownNat (i := n + 1) (i' := -((n : ℤ) + 1)) (j := n)
    (j' := -(n : ℤ)) (by simp) (by simp)

/-- The square relating the differential of `Hom(K^•, ℱ)` in cochain degrees to the differential
of the alternating Čech complex of [Stacks 0724]. -/
lemma alternatingCechRestriction_comm (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (n : ℕ)
    (g : (koszulCochainComplex B S hS X U).X (-(n : ℤ)) ⟶ F) :
    (koszulComplex B S hS X U).d (n + 1) n ≫
        (koszulCochainComplexXIso B S hS X U n).inv ≫ g =
      (koszulCochainComplexXIso B S hS X U (n + 1)).inv ≫
        (koszulCochainComplex B S hS X U).d (-((n : ℤ) + 1)) (-(n : ℤ)) ≫ g := by
  rw [koszulCochainComplex_d_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- `Hom(K^•, ℱ)` vanishes in the negative degrees. -/
private lemma isZero_alternatingCechCochainComplex_X_of_neg (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) {p : ℤ} (hp : p < 0) :
    IsZero ((alternatingCechCochainComplex B S hS X U F).X p) :=
  CochainComplex.isZero_yonedaOp_X F (koszulCochainComplex B S hS X U) p
    (isZero_koszulCochainComplex_X B S hS X U (-p) (by omega))

/-- The restriction of `Hom(K^•, ℱ)` to the nonnegative degrees is the alternating Čech complex
`Č^•_alt(f, ℱ)` of [Stacks 0724]. -/
def alternatingCechRestrictionIso (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    (alternatingCechCochainComplex B S hS X U F).restriction
        ComplexShape.embeddingUpNat ≅
      alternatingCechComplex B S hS X U F :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => alternatingCechCochainComplexXIsoAlternatingCech B S hS X U F n)
    (fun n m hnm => by
      obtain rfl : m = n + 1 := hnm.symm
      refine AddCommGrpCat.ext fun g => ?_
      change ((alternatingCechComplex B S hS X U F).d n (n + 1)).hom
          ((koszulCochainComplexXIso B S hS X U n).inv ≫ g) =
        (koszulCochainComplexXIso B S hS X U (n + 1)).inv ≫
          (koszulCochainComplex B S hS X U).d (-((n : ℤ) + 1)) (-(n : ℤ)) ≫ g
      rw [alternatingCechComplex_d_apply]
      exact alternatingCechRestriction_comm B S hS X U F n g)

/-- **Stacks 0724** read as a cochain complex indexed by `ℤ`: the alternating Čech complex
`Č^•_alt(f, ℱ)`, extended by zero to the negative degrees. -/
abbrev alternatingCechComplexExtend (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  (alternatingCechComplex B S hS X U F).extend ComplexShape.embeddingUpNat

/-- The isomorphism `alternatingCechRestrictionIso` lifts along the embedding `ℕ ⟶ ℤ`: the
complex `Hom(K^•, ℱ)` vanishes in the degrees outside its image. -/
lemma hasLift_alternatingCechRestrictionIso (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    ComplexShape.embeddingUpNat.HasLift
      (alternatingCechRestrictionIso B S hS X U F).hom := by
  intro j hj i' hij'
  have hf : ∀ k : ℕ, ComplexShape.embeddingUpNat.f k = (k : ℤ) := fun _ => rfl
  have hne : ∀ i : ℕ, ComplexShape.embeddingUpNat.f i ≠ i' := hj.notMem hij'
  have hneg : i' < 0 := by
    by_contra hcon
    exact hne i'.toNat ((hf _).trans (Int.toNat_of_nonneg (by omega)))
  exact (isZero_alternatingCechCochainComplex_X_of_neg B S hS X U F hneg).eq_of_src _ _

/-- The comparison `Hom(K^•, ℱ) ⟶ Č^•_alt(f, ℱ)` of complexes indexed by `ℤ`. -/
def alternatingCechCochainToExtend (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    alternatingCechCochainComplex B S hS X U F ⟶
      alternatingCechComplexExtend B S hS X U F :=
  ComplexShape.embeddingUpNat.liftExtend (alternatingCechRestrictionIso B S hS X U F).hom
    (hasLift_alternatingCechRestrictionIso B S hS X U F)

/-- The comparison `Hom(K^•, ℱ) ⟶ Č^•_alt(f, ℱ)` of complexes indexed by `ℤ` is an
isomorphism. -/
lemma isIso_alternatingCechCochainToExtend (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    IsIso (alternatingCechCochainToExtend B S hS X U F) := by
  have h : ∀ p : ℤ, IsIso ((alternatingCechCochainToExtend B S hS X U F).f p) := by
    intro p
    by_cases hp : ∃ n : ℕ, (n : ℤ) = p
    · obtain ⟨n, rfl⟩ := hp
      refine (ComplexShape.embeddingUpNat.isIso_liftExtend_f_iff
        (alternatingCechRestrictionIso B S hS X U F).hom
        (hasLift_alternatingCechRestrictionIso B S hS X U F) (i := n) rfl).2 ?_
      exact inferInstanceAs (IsIso ((HomologicalComplex.eval
        AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) n).map
        (alternatingCechRestrictionIso B S hS X U F).hom))
    · have hneg : p < 0 := by
        by_contra hcon
        exact hp ⟨p.toNat, Int.toNat_of_nonneg (by omega)⟩
      refine StacksDraft.TotalComplexQuasiIso.isIso_of_isZero _ ?_ ?_
      · exact isZero_alternatingCechCochainComplex_X_of_neg B S hS X U F hneg
      · exact HomologicalComplex.isZero_extend_X _ _ p (fun i hi => hp ⟨i, hi⟩)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **`Hom(K^•, ℱ) ≅ Č^•_alt(f, ℱ)`.** The complex `Hom(K^•, ℱ)` indexed by `ℤ` is the
alternating Čech complex of [Stacks 0724], extended by zero to the negative degrees. -/
def alternatingCechCochainComplexIsoExtend (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    alternatingCechCochainComplex B S hS X U F ≅
      alternatingCechComplexExtend B S hS X U F :=
  @asIso _ _ _ _ (alternatingCechCochainToExtend B S hS X U F)
    (isIso_alternatingCechCochainToExtend B S hS X U F)

/-! ### The canonical map to `RΓ(X, ℱ)` -/

/-- The chosen injective resolution of `ℱ`, as a complex of abelian sheaves. -/
abbrev injectiveResolutionCocomplex (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    CochainComplex (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) ℤ :=
  (CochainComplex.injectiveResolutionSingle F).cocomplex

/-- The Hom bicomplex `Hom(K^p, I^q)` of the chosen injective resolution of `ℱ` has a total
complex. -/
instance hasTotalKoszulHomBicomplexRes (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    (koszulHomBicomplex B S hS X U
      (injectiveResolutionCocomplex B S hS X F)).HasTotal (ComplexShape.up ℤ) :=
  koszulHomBicomplex_hasTotal B S hS X U _
    (CochainComplex.injectiveResolutionSingle F).boundedBelow

/-- **[Stacks 0133] in the alternating Čech situation.** The comparison
`Γ(X, I^•) ⟶ Tot(Hom(K^•, I^•))`. -/
def globalSectionsToTotal (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    globalSectionsCochainComplex B S hS X (injectiveResolutionCocomplex B S hS X F) ⟶
      (koszulHomBicomplex B S hS X U
        (injectiveResolutionCocomplex B S hS X F)).total (ComplexShape.up ℤ) :=
  comparisonMapP (globalSectionsCochainComplex B S hS X
      (injectiveResolutionCocomplex B S hS X F))
    (koszulHomBicomplex B S hS X U (injectiveResolutionCocomplex B S hS X F)).flip
    (globalSectionsToRowZero B S hS X U (injectiveResolutionCocomplex B S hS X F))
    (hypotheses_koszulHomBicomplex_flip B S hS X U hsurj _
      (CochainComplex.injectiveResolutionSingle F).boundedBelow
      (CochainComplex.injectiveResolutionSingle F).injective) ≫
    ((koszulHomBicomplex B S hS X U
      (injectiveResolutionCocomplex B S hS X F)).totalFlipIso (ComplexShape.up ℤ)).hom

/-- The comparison `Γ(X, I^•) ⟶ Tot(Hom(K^•, I^•))` is a quasi-isomorphism. -/
lemma quasiIso_globalSectionsToTotal (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    QuasiIso (globalSectionsToTotal B S hS X U hsurj F) :=
  quasiIso_comp _ _

/-- The resolution map in degree `0`, `ℱ ⟶ I^0`. -/
def resolutionEpsilon (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    F ⟶ (injectiveResolutionCocomplex B S hS X F).X 0 :=
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫
    (CochainComplex.injectiveResolutionSingle F).ι.f 0

/-- The composite `ℱ ⟶ I^0 ⟶ I^1` of the resolution map with the first differential is zero. -/
lemma resolutionEpsilon_comp_d (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    resolutionEpsilon B S hS X F ≫ (injectiveResolutionCocomplex B S hS X F).d 0 1 = 0 := by
  have hd : ((CochainComplex.singleFunctor
      (Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) 0).obj F).d 0 1 = 0 :=
    HomologicalComplex.single_obj_d _ _ _ _ _
  rw [resolutionEpsilon, Category.assoc,
    (CochainComplex.injectiveResolutionSingle F).ι.comm 0 1, hd, zero_comp, comp_zero]

/-- The canonical map `Hom(K^•, ℱ) ⟶ Tot(Hom(K^•, I^•))`. -/
def alternatingCechToTotalRes (U : SpacesEtale B S hS X)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    alternatingCechCochainComplex B S hS X U F ⟶
      (koszulHomBicomplex B S hS X U
        (injectiveResolutionCocomplex B S hS X F)).total (ComplexShape.up ℤ) :=
  alternatingCechToTotal B S hS X U (resolutionEpsilon B S hS X F)
    (resolutionEpsilon_comp_d B S hS X F)

/-- `RΓ(X, ℱ)`: the object of `D(Ab)` represented by the complex of global sections of an
injective resolution of `ℱ`. -/
def derivedGlobalSections (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    DerivedCategory AddCommGrpCat.{u + 1} :=
  DerivedCategory.Q.obj
    (globalSectionsCochainComplex B S hS X (injectiveResolutionCocomplex B S hS X F))

/-- The comparison `Γ(X, I^•) ⟶ Tot(Hom(K^•, I^•))` becomes an isomorphism in `D(Ab)`. -/
lemma isIso_Q_map_globalSectionsToTotal (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    IsIso (DerivedCategory.Q.map (globalSectionsToTotal B S hS X U hsurj F)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
    (quasiIso_globalSectionsToTotal B S hS X U hsurj F)

/-- The comparison `Γ(X, I^•) ⟶ Tot(Hom(K^•, I^•))`, as an isomorphism of `D(Ab)`. -/
def globalSectionsToTotalIso (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    derivedGlobalSections B S hS X F ≅
      DerivedCategory.Q.obj ((koszulHomBicomplex B S hS X U
        (injectiveResolutionCocomplex B S hS X F)).total (ComplexShape.up ℤ)) :=
  @asIso _ _ _ _ (DerivedCategory.Q.map (globalSectionsToTotal B S hS X U hsurj F))
    (isIso_Q_map_globalSectionsToTotal B S hS X U hsurj F)

/-- The canonical map `Hom(K^•, ℱ) ⟶ RΓ(X, ℱ)` in `D(Ab)`. -/
def alternatingCechCochainToDerivedGlobalSections (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    DerivedCategory.Q.obj (alternatingCechCochainComplex B S hS X U F) ⟶
      derivedGlobalSections B S hS X F :=
  DerivedCategory.Q.map (alternatingCechToTotalRes B S hS X U F) ≫
    (globalSectionsToTotalIso B S hS X U hsurj F).inv

/-- Let `S` be a scheme, let `f : U ⟶ X` be a surjective étale morphism of algebraic spaces over
`S` and let `ℱ` be an abelian sheaf on the spaces-étale site of `X`. There is a canonical map

`Č^•_alt(f, ℱ) ⟶ RΓ(X, ℱ)`

in `D(Ab)`, where `Č^•_alt(f, ℱ)` is the alternating Čech complex of [Stacks 0724] and
`RΓ(X, ℱ)` is represented by the global sections of an injective resolution of `ℱ`, so that
`H^n(RΓ(X, ℱ)) = H^n(X, ℱ)` by `derivedGlobalSectionsHomologyAddEquivSheafH`.

It is the composite of the map into the total complex of the Hom bicomplex `Hom(K^p, I^q)` with
the inverse of the quasi-isomorphism `Γ(X, I^•) ⟶ Tot(Hom(K^•, I^•))` of [Stacks 0133].

The other assertion of [Stacks 0725], the spectral sequence with `E₁^{p,q} = Ext^q(K^p, ℱ)`
converging to `H^{p+q}(X, ℱ)`, is
`AlgebraicGeometry.Space.SpacesEtale.exists_alternatingCechCohomologySpectralSequence`. -/
@[stacks 0725 "the canonical map Č^•_alt(f, ℱ) ⟶ RΓ(X, ℱ) in D(Ab)"]
def alternatingCechToDerivedGlobalSections (U : SpacesEtale B S hS X)
    (hsurj : IsSurjective B S hS U.obj.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    DerivedCategory.Q.obj (alternatingCechComplexExtend B S hS X U F) ⟶
      derivedGlobalSections B S hS X F :=
  DerivedCategory.Q.map (alternatingCechCochainComplexIsoExtend B S hS X U F).inv ≫
    alternatingCechCochainToDerivedGlobalSections B S hS X U hsurj F

/-! ### The cohomology of `RΓ(X, ℱ)` -/

/-- The cohomology of the complex of global sections of an injective resolution of `ℱ` is the
`Ext` group out of the constant sheaf `ℤ`. -/
def globalSectionsHomologyAddEquivZExt
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (n : ℤ) :
    (globalSectionsCochainComplex B S hS X
        (injectiveResolutionCocomplex B S hS X F)).homology n ≃+
      Abelian.zExt (constantIntSheaf B S hS X) F n :=
  CochainComplex.HomBicomplex.coyonedaHomologyAddEquivZExt (constantIntSheaf B S hS X) F
    (injectiveResolutionCocomplex B S hS X F)
    (CochainComplex.HomBicomplex.isInjectiveResolution_injectiveResolutionSingle F) n

/-- The cohomology of the complex of global sections of an injective resolution of `ℱ` is the
sheaf cohomology of `ℱ`. -/
def globalSectionsHomologyAddEquivSheafH
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (globalSectionsCochainComplex B S hS X
        (injectiveResolutionCocomplex B S hS X F)).homology (n : ℤ) ≃+ Sheaf.H F n :=
  (globalSectionsHomologyAddEquivZExt B S hS X F (n : ℤ)).trans
    (sheafHIsoZExt B S hS X F n).addCommGroupIsoToAddEquiv.symm

/-- **`H^n(RΓ(X, ℱ)) = H^n(X, ℱ)`.** The cohomology of `RΓ(X, ℱ)`, computed in `D(Ab)`, is the
sheaf cohomology of `ℱ` on the spaces-étale site of `X`. -/
def derivedGlobalSectionsHomologyAddEquivSheafH
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).obj
        (derivedGlobalSections B S hS X F) ≃+ Sheaf.H F n :=
  ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} (n : ℤ)).app
      (globalSectionsCochainComplex B S hS X
        (injectiveResolutionCocomplex B S hS X F))).addCommGroupIsoToAddEquiv.trans
    (globalSectionsHomologyAddEquivSheafH B S hS X F n)

end AlgebraicGeometry.Space.SpacesEtale

end
