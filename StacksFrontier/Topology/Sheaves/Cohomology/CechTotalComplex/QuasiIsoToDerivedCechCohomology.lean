module

public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.Assembled
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.FunctorialQuasiIsomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functorial quasi-isomorphism of Stacks 01EN

Let `(X, O)` be a ringed space and `𝒰` an open covering of an open `U ⊆ X`.  For a presheaf of
`O`-modules `F` and an injective resolution `F ⟶ J•`, the Čech bicomplex of `J•` has `(q, p)`
term the Čech `p`-cochains of `J^q`, and its total complex receives two augmentations:

* `α : Ȟ⁰(𝒰, J•) ⟶ Tot(Č•(𝒰, J•))`, the inclusion of degree-zero Čech cohomology into the
  degree-zero Čech cochains of each `J^q`, landing in the `(q, 0)` corner;
* `β : Č•(𝒰, F) ⟶ Tot(Č•(𝒰, J•))`, the Čech complex of the augmentation `F ⟶ J^0`, landing in
  the `(0, p)` corner.

Both are quasi-isomorphisms, each by [Stacks, Tag 0133] applied in one of the two directions of
the bicomplex.  For `α` the columns are the Čech complexes of the injective presheaves `J^q`,
whose higher Čech cohomology vanishes; for `β` the rows are the Čech cochains of the resolution
in a fixed degree, and the Čech cochain functors are exact, so each row resolves the
corresponding Čech cochains of `F`.

Consequently `Q(β) ≫ Q(α)⁻¹` is an isomorphism in the derived category, which composed with
`injectiveResolutionToRightDerived` lands in the total right derived functor `RȞ⁰(𝒰, F)`.
Both augmentations and that last comparison are natural in the resolution, so the composite is
natural in `F` and independent of the resolution chosen for each `F`; that is the functorial
quasi-isomorphism the source asserts.

## Main definitions

* `cechAlpha`, `cechBeta`: the two augmentations, with `cechAlpha_f` and `cechBeta_f` their
  prescribed component formulas and `quasiIso_cechAlpha`, `quasiIso_cechBeta` their
  quasi-isomorphy.
* `cechAlphaRes`, `cechBetaRes`: the same at an injective resolution.
* `cechBicomplexMap`, `cechTotalMap`: the maps of Čech bicomplexes and of their total complexes
  induced by a morphism of complexes of presheaves.
* `resolutionQhQ`: the identification of `Qh ∘ quotient` with `Q` at an injective resolution.
* `cechResolutionComparisonOfComparison`: a `CechResolutionComparison` built from a natural
  isomorphism and the single equation characterizing it at the given resolution.
* `cechComparison`, `cechComparisonPlusIso`: the comparison at a chosen injective resolution,
  in the derived category and in its bounded-below part.
* `resolutionMap`: the comparison of two injective resolutions descending a morphism.

## Main results

* `isZero_cechCohomology_injective`: the higher Čech cohomology of an injective presheaf of
  modules vanishes.  This is read off the Čech-to-derived comparison of Stacks 01EN together
  with the vanishing of higher right derived functors on injective objects.
* `hypotheses_cechAlphaRow`, `hypotheses_cechBetaRow`: the four hypotheses of
  [Stacks, Tag 0133] for the Čech bicomplex of a bounded-below complex of injective presheaves,
  and for its flip at a resolution.
* `isIso_kernelLift_of_quasiIso_single`: a quasi-isomorphism out of a complex concentrated in
  degree `0` identifies its object with the kernel of the first differential.
* `injectiveResolutionToRightDerived_eq` and `isIso_injectiveResolutionToRightDerived`: the
  comparison of the Čech `Ȟ⁰` of an injective resolution with the total right derived functor
  is the inverse of
  `Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedComparison`, hence an
  isomorphism.
* `cechAlpha_comp_cechTotalMap` and `cechBeta_comp_cechTotalMap`: both augmentations are
  natural in the resolution.
* `resolutionDerivedIso_naturality`, `derivedPlusResolutionIso_naturality` and
  `resolutionDerivedComparison_naturality`: the comparison of an object with its injective
  resolution, and the resulting comparison of the total right derived functor with the
  `Φ`-image of the resolution, are natural in the resolution. Stated for an arbitrary additive
  functor between abelian categories with enough injectives in the source.
* `cechComparison_naturality` and `cechComparison_eq`: the comparison is natural in the
  presheaf and independent of the chosen resolution.
* `cechComplexIsoRightDerived`: **the *moreover* clause of Stacks 01EN.**

## Implementation notes

The Čech complex is extended by zero from `ℕ` to `ℤ`, and the resolution is bounded below, so
the Čech bicomplex is supported in a quadrant and its antidiagonals are finite; this is what
makes the total complex exist (`hasTotal_cechBicomplex`) and what discharges two of the four
hypotheses of [Stacks, Tag 0133] outright.

For `β` the bicomplex has to be read in the other order, which is `HomologicalComplex₂.flip`
followed by `HomologicalComplex₂.totalFlipIso`.  The sign that flipping a total complex
introduces is `(-1)^{0 · p}` on the summand `β` lands in, hence trivial, so the prescribed
component formula holds with no sign (`cechBeta_f`).

Exactness of the rows and the kernel clause for `β` are transported between the extended and
the unextended Čech indexing along `cechEvalIso`, the identification of the Čech complex in a
degree in the range of the embedding with the Čech cochain functor of Stacks 01EJ.

`injectiveResolutionToRightDerived` and
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedComparison` are the same
composite written with two different spellings of the comparison of `F` with its resolution:
the first uses `DerivedCategory.Q` of the augmentation, the second builds the comparison in the
homotopy category.  `resolutionDerivedIso_hom_comp` identifies them, which is how iso-ness of
the first is obtained — the alternative, invoking the invertibility of the unit of the total
right derived functor directly, meets a spelling mismatch, Mathlib's instance being stated for
complexes presented through `CategoryTheory.InjectiveObject.ι`.

The naturality of `resolutionDerivedIso` is the mathematical content of the last square: its
three factors are two components of natural isomorphisms and the localization of the
augmentation, so it reduces to two naturality statements and
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionSingleHom_naturality`. Nothing here
needs the homotopy between two descents of a morphism to chosen resolutions:
`CategoryTheory.InjectiveResolution.desc_commutes` is an equality of morphisms of complexes.

The two augmentation naturality squares are proved componentwise and in term mode.  Their component
equations mix the two spellings `((cechBicomplex O 𝒰 K).X q).X p` and
`((cechComplexIntFunctor O 𝒰).obj (K.X q)).X p` — the prescribed component formulas of Stacks
01EN are stated across exactly that boundary — so `rw` and `simp only [Category.assoc]` cannot
reassociate inside them, and each step is an explicit `congrArg`, `Category.assoc` or
`Eq.trans`, which check up to full definitional equality.

## References

* [Stacks Project, Tag 01EN](https://stacks.math.columbia.edu/tag/01EN)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 01EJ](https://stacks.math.columbia.edu/tag/01EJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechExactFunctor (presheafCechComplexFunctor)
open Stacks.Cohomology.CechComparison
open Stacks.Cohomology.HigherDirectImagePresheaf

universe u

namespace Stacks.Cohomology.CechTotalComparison

attribute [local instance] HasDerivedCategory.standard

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (𝒰 : CechExactFunctor.CechOpenCover.{u, u} (TopCat.of X))

/-! ### Vanishing and finiteness for the Čech bicomplex -/

/-- The Čech complex extended by zero to integer degrees vanishes in negative degrees. -/
lemma isZero_cechComplexIntFunctor_X (M : Modules.{u} O) (p : ℤ) (hp : p < 0) :
    IsZero (((cechComplexIntFunctor.{u} O 𝒰).obj M).X p) := by
  dsimp only [cechComplexIntFunctor, Functor.comp_obj, Embedding.extendFunctor_obj]
  exact HomologicalComplex.isZero_extend_X _ embeddingUpNat p
    (fun i => by change ((i : ℕ) : ℤ) ≠ p; omega)

/-- A term of the Čech bicomplex of a complex vanishes if the complex vanishes in that
resolution degree, or if the Čech degree is negative. -/
lemma isZero_cechBicomplex_X_X (K : CochainComplex (Modules.{u} O) ℤ) (q p : ℤ)
    (h : IsZero (K.X q) ∨ p < 0) :
    IsZero (((cechBicomplex.{u} O 𝒰 K).X q).X p) := by
  obtain h | h := h
  · exact (HomologicalComplex.eval _ _ p).map_isZero
      ((cechComplexIntFunctor.{u} O 𝒰).map_isZero h)
  · exact isZero_cechComplexIntFunctor_X O 𝒰 (K.X q) p h

/-- **The antidiagonals of the Čech bicomplex are finite.** Both indices are bounded below —
the Čech degree because the Čech complex is extended by zero from `ℕ`, the resolution degree
because the resolved complex is bounded below — so only finitely many summands survive in each
total degree. -/
lemma diagonalFinite_cechBicomplex (K : CochainComplex (Modules.{u} O) ℤ) (a : ℤ)
    [K.IsStrictlyGE a] : DiagonalFinite (cechBicomplex.{u} O 𝒰 K) := by
  intro n
  refine (Set.finite_Icc a n).subset ?_
  intro q hq
  simp only [Set.mem_ofPred_eq] at hq
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hq (isZero_cechBicomplex_X_X O 𝒰 K q (n - q)
      (Or.inl (K.isZero_of_isStrictlyGE a q (by omega))))
  · by_contra h
    exact hq (isZero_cechBicomplex_X_X O 𝒰 K q (n - q) (Or.inr (by omega)))

/-- The Čech bicomplex of a complex bounded below in degree `0` has a total complex. -/
instance hasTotal_cechBicomplex (K : CochainComplex (Modules.{u} O) ℤ) [K.IsStrictlyGE 0] :
    (cechBicomplex.{u} O 𝒰 K).HasTotal (up ℤ) :=
  hasTotal_of_diagonalFinite _ (diagonalFinite_cechBicomplex O 𝒰 K 0)

/-! ### The augmentation by degree-zero Čech cohomology -/

/-- Degree-zero Čech cohomology acts on morphisms as the degree-zero cohomology of the Čech
complex of Stacks 01EJ. -/
lemma cechCohomologyZeroFunctor_map {M N : Modules.{u} O} (f : M ⟶ N) :
    (cechCohomologyZeroFunctor.{u} O 𝒰).map f =
      HomologicalComplex.homologyMap
        ((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).map f) 0 :=
  rfl

/-- The integer-indexed Čech complex acts on morphisms by extending the Čech complex of
Stacks 01EJ by zero. -/
lemma cechComplexIntFunctor_map_f {M N : Modules.{u} O} (f : M ⟶ N) (p : ℤ) :
    ((cechComplexIntFunctor.{u} O 𝒰).map f).f p =
      (HomologicalComplex.extendMap
        ((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).map f)
        embeddingUpNat).f p :=
  rfl

/-- **Degree-zero cohomology of an `ℕ`-indexed cochain complex includes naturally into the
degree-zero term of its extension by zero.** For an `ℕ`-indexed cochain complex there is no
incoming differential in degree `0`, so cohomology there is the cycles, which are a subobject
of the degree-zero term; the inclusion commutes with every morphism of complexes. -/
lemma extendZeroInclusion_naturality {B : Type*} [Category* B] [Abelian B]
    {K L : CochainComplex B ℕ} (φ : K ⟶ L) (h : embeddingUpNat.f 0 = (0 : ℤ)) :
    (K.isoHomologyπ₀.inv ≫ K.iCycles 0 ≫ (K.extendXIso embeddingUpNat h).inv) ≫
        (HomologicalComplex.extendMap φ embeddingUpNat).f 0 =
      HomologicalComplex.homologyMap φ 0 ≫
        (L.isoHomologyπ₀.inv ≫ L.iCycles 0 ≫ (L.extendXIso embeddingUpNat h).inv) := by
  have h₁ : HomologicalComplex.homologyMap φ 0 ≫ L.isoHomologyπ₀.inv =
      K.isoHomologyπ₀.inv ≫ HomologicalComplex.cyclesMap φ 0 :=
    CochainComplex.isoHomologyπ₀_inv_naturality φ
  have h₂ : HomologicalComplex.cyclesMap φ 0 ≫ L.iCycles 0 = K.iCycles 0 ≫ φ.f 0 :=
    HomologicalComplex.cyclesMap_i φ 0
  rw [HomologicalComplex.extendMap_f φ embeddingUpNat h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂]

/-- **The inclusion of degree-zero Čech cohomology into degree-zero Čech cochains is
natural.** -/
lemma cechZeroInclusion_naturality {M N : Modules.{u} O} (f : M ⟶ N) :
    cechZeroInclusion.{u} O 𝒰 M ≫ ((cechComplexIntFunctor.{u} O 𝒰).map f).f 0 =
      (cechCohomologyZeroFunctor.{u} O 𝒰).map f ≫ cechZeroInclusion.{u} O 𝒰 N :=
  extendZeroInclusion_naturality
    ((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).map f) rfl

/-- **The augmentation `α`**, as a morphism into the zeroth row of the Čech bicomplex: in
resolution degree `q` it is the inclusion of the degree-zero Čech cohomology of `K^q` into its
degree-zero Čech cochains. -/
def cechAlphaRow (K : CochainComplex (Modules.{u} O) ℤ) :
    ((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj K ⟶
      rowZero (cechBicomplex.{u} O 𝒰 K) where
  f q := cechZeroInclusion.{u} O 𝒰 (K.X q)
  comm' q q' _ := cechZeroInclusion_naturality O 𝒰 (K.d q q')

/-- The components of `cechAlphaRow`. -/
@[simp]
lemma cechAlphaRow_f (K : CochainComplex (Modules.{u} O) ℤ) (q : ℤ) :
    (cechAlphaRow.{u} O 𝒰 K).f q = cechZeroInclusion.{u} O 𝒰 (K.X q) := rfl

/-- **`cechAlphaRow` is natural in the resolved complex.** -/
lemma cechAlphaRow_naturality {K L : CochainComplex (Modules.{u} O) ℤ} (φ : K ⟶ L) :
    cechAlphaRow.{u} O 𝒰 K ≫
        rowZeroMap (((cechComplexIntFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).map φ) =
      ((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).map φ ≫
        cechAlphaRow.{u} O 𝒰 L :=
  HomologicalComplex.hom_ext _ _ fun q => cechZeroInclusion_naturality O 𝒰 (φ.f q)

/-! ### The higher Čech cohomology of an injective presheaf vanishes -/

/-- **The degreewise form of the Čech-to-derived comparison of Stacks 01EN**:
`Ȟⁿ(𝒰, -) ≅ Rⁿ Ȟ⁰(𝒰, -)`. It is the degree-`n` component of the δ-functor isomorphism, read
through the identifications of the components of the two δ-functors. -/
def cechCohomologyIsoRightDerived (n : ℕ) :
    cechCohomologyFunctor.{u} O 𝒰 n ≅ (cechCohomologyZeroFunctor.{u} O 𝒰).rightDerived n :=
  let c : CechComparison.CechDerivedComparison.{u} O 𝒰 :=
    CechComparisonU.cechDerivedComparisonEquiv O 𝒰
      (CechComparisonU.cechDerivedComparison.{u, u, u, u} O 𝒰)
  let ev : DeltaFunctor (Modules.{u} O) (SectionModules.{u} O 𝒰) ⥤
      (Modules.{u} O ⥤ SectionModules.{u} O 𝒰) :=
    { obj := fun G => G.functor n
      map := fun f => f.app n }
  eqToIso (cechDeltaFunctor_functor.{u} O 𝒰 n).symm ≪≫ ev.mapIso c.deltaIso ≪≫
    eqToIso (c.derivedFunctor_eq n)

/-- **The higher Čech cohomology of an injective presheaf of modules vanishes.** By Stacks
01EN the Čech cohomology functors are the right derived functors of their degree-zero part,
and higher right derived functors vanish on injective objects. -/
lemma isZero_cechCohomology_injective (k : ℕ) (I : Modules.{u} O) [Injective I] :
    IsZero ((cechCohomologyFunctor.{u} O 𝒰 (k + 1)).obj I) :=
  IsZero.of_iso
    (Functor.isZero_rightDerived_obj_injective_succ (cechCohomologyZeroFunctor.{u} O 𝒰) k I)
    ((cechCohomologyIsoRightDerived.{u} O 𝒰 (k + 1)).app I)

/-! ### The hypotheses of Stacks 0133 for the column augmentation -/

/-- **A monomorphism whose short complex is exact is a kernel of the next map.** The comparison
with the kernel is a monomorphism because the given map is, and an epimorphism because the
short complex is exact; an abelian category is balanced. -/
theorem isIso_kernelLift_of_mono_of_exact {B : Type*} [Category* B] [Abelian B]
    {T A A' : B} (f : T ⟶ A) (g : A ⟶ A') (hf : f ≫ g = 0) [Mono f]
    (hex : (ShortComplex.mk f g hf).Exact) :
    IsIso (kernel.lift g f hf) :=
  have : Mono (kernel.lift g f hf) := mono_of_mono_fac (kernel.lift_ι g f hf)
  have : Epi (kernel.lift g f hf) :=
    (ShortComplex.mk f g hf).exact_iff_epi_kernel_lift.1 hex
  isIso_of_mono_of_epi _

/-- **Degree-zero cohomology of an `ℕ`-indexed cochain complex is the kernel of the first
differential of its extension by zero.** The extension has no term in degree `-1`, so nothing
changes: degree-zero cohomology of the original complex is its degree-zero cycles, and those
are the kernel of `d⁰` transported along the two identifications of the extended terms. -/
lemma inducesIsoKernel_extendZeroInclusion {B : Type*} [Category* B] [Abelian B]
    (C : CochainComplex B ℕ) (h₀ : embeddingUpNat.f 0 = (0 : ℤ))
    (h₁ : embeddingUpNat.f 1 = (1 : ℤ)) :
    ∃ hα : (C.isoHomologyπ₀.inv ≫ C.iCycles 0 ≫ (C.extendXIso embeddingUpNat h₀).inv) ≫
        (C.extend embeddingUpNat).d 0 1 = 0,
      IsIso (kernel.lift ((C.extend embeddingUpNat).d 0 1)
        (C.isoHomologyπ₀.inv ≫ C.iCycles 0 ≫ (C.extendXIso embeddingUpNat h₀).inv) hα) := by
  have hd : (C.extend embeddingUpNat).d 0 1 =
      (C.extendXIso embeddingUpNat h₀).hom ≫ C.d 0 1 ≫
        (C.extendXIso embeddingUpNat h₁).inv :=
    C.extend_d_eq embeddingUpNat h₀ h₁
  have hα : (C.isoHomologyπ₀.inv ≫ C.iCycles 0 ≫ (C.extendXIso embeddingUpNat h₀).inv) ≫
      (C.extend embeddingUpNat).d 0 1 = 0 := by
    rw [hd]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (C.iCycles_d 0 1)]
    simp
  refine ⟨hα, ?_⟩
  have hS : (ShortComplex.mk (C.iCycles 0) (C.d 0 1) (C.iCycles_d 0 1)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (C.cyclesIsKernel 0 1 (by simp))
  have e : ShortComplex.mk (C.iCycles 0) (C.d 0 1) (C.iCycles_d 0 1) ≅
      ShortComplex.mk
        (C.isoHomologyπ₀.inv ≫ C.iCycles 0 ≫ (C.extendXIso embeddingUpNat h₀).inv)
        ((C.extend embeddingUpNat).d 0 1) hα :=
    ShortComplex.isoMk C.isoHomologyπ₀ (C.extendXIso embeddingUpNat h₀).symm
      (C.extendXIso embeddingUpNat h₁).symm (by simp) (by simp [hd])
  exact isIso_kernelLift_of_mono_of_exact _ _ _ (ShortComplex.exact_of_iso e hS)

/-- **The kernel clause of Stacks 0133 for the Čech bicomplex**: in each resolution degree the
augmentation by degree-zero Čech cohomology is a kernel of the first Čech differential. -/
lemma inducesIsoKernel_cechAlphaRow (K : CochainComplex (Modules.{u} O) ℤ) (q : ℤ) :
    ∃ hα : (cechAlphaRow.{u} O 𝒰 K).f q ≫ ((cechBicomplex.{u} O 𝒰 K).X q).d 0 1 = 0,
      IsIso (kernel.lift (((cechBicomplex.{u} O 𝒰 K).X q).d 0 1)
        ((cechAlphaRow.{u} O 𝒰 K).f q) hα) :=
  inducesIsoKernel_extendZeroInclusion
    ((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).obj (K.X q)) rfl rfl

/-- **The columns of the Čech bicomplex of a complex of injective presheaves are exact away
from Čech degree zero.** In negative degree the column is supported away from it; in positive
degree this is the vanishing of the higher Čech cohomology of an injective presheaf,
transported along the extension by zero. -/
lemma exactAt_cechBicomplex_X (K : CochainComplex (Modules.{u} O) ℤ)
    (hinj : ∀ q, Injective (K.X q)) (q p : ℤ) (hp : p ≠ 0) :
    ((cechBicomplex.{u} O 𝒰 K).X q).ExactAt p := by
  rcases lt_trichotomy p 0 with h | h | h
  · exact HomologicalComplex.extend_exactAt _ embeddingUpNat p
      fun j => by change ((j : ℕ) : ℤ) ≠ p; omega
  · exact absurd h hp
  · have hk : embeddingUpNat.f p.toNat = p := by change ((p.toNat : ℕ) : ℤ) = p; omega
    refine (HomologicalComplex.extend_exactAt_iff _ embeddingUpNat hk).2 ?_
    obtain ⟨k, hk'⟩ : ∃ k : ℕ, p.toNat = k + 1 := ⟨p.toNat - 1, by omega⟩
    rw [hk']
    have := hinj q
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_cechCohomology_injective.{u} O 𝒰 k (K.X q))

/-- **The hypotheses of Stacks 0133 for the Čech bicomplex of a bounded-below complex of
injective presheaves**, with the augmentation by degree-zero Čech cohomology. -/
theorem hypotheses_cechAlphaRow (K : CochainComplex (Modules.{u} O) ℤ) [K.IsStrictlyGE 0]
    (hinj : ∀ q, Injective (K.X q)) :
    Hypotheses (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj K)
      (cechBicomplex.{u} O 𝒰 K) (cechAlphaRow.{u} O 𝒰 K) where
  diagonalFinite := diagonalFinite_cechBicomplex O 𝒰 K 0
  zero_of_neg q p hp := isZero_cechBicomplex_X_X O 𝒰 K q p (Or.inr hp)
  exactAt_of_ne_zero q p hp := exactAt_cechBicomplex_X O 𝒰 K hinj q p hp
  inducesIsoKernel q := inducesIsoKernel_cechAlphaRow O 𝒰 K q

/-! ### Generic homological-algebra inputs -/

/-- The forward map of an isomorphism is a monomorphism. -/
lemma mono_iso_hom {B : Type*} [Category* B] {Y Z : B} (e : Y ≅ Z) : Mono e.hom :=
  mono_of_mono_fac e.hom_inv_id

/-- An additive functor preserving homology sends `ExactAt` to `ExactAt`. -/
lemma exactAt_mapHomologicalComplex {B D : Type*} [Category* B] [Category* D] [Abelian B]
    [Abelian D] {ι : Type*} (c : ComplexShape ι) (Φ : B ⥤ D) [Φ.Additive] [Φ.PreservesHomology]
    (K : HomologicalComplex B c) (i : ι) (h : K.ExactAt i) :
    ((Φ.mapHomologicalComplex c).obj K).ExactAt i := by
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  have heq : ((Φ.mapHomologicalComplex c).obj K).sc i = (K.sc i).map Φ := rfl
  rw [heq]
  exact h.map Φ

/-- **A quasi-isomorphism out of a complex concentrated in degree `0` identifies its object
with the kernel of the first differential.** If `ψ : F[0] ⟶ K` is a quasi-isomorphism and `K`
vanishes in degree `-1`, then degree-zero cohomology of `K` is both `F` and the kernel of
`d⁰`, and the two identifications agree. -/
lemma isIso_kernelLift_of_quasiIso_single {B : Type*} [Category* B] [Abelian B] {F : B}
    {K : CochainComplex B ℤ} (hK : IsZero (K.X (-1)))
    (ψ : (HomologicalComplex.single B (up ℤ) 0).obj F ⟶ K) [QuasiIso ψ] (ξ : F ⟶ K.X 0)
    (hξ : (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom ≫ ξ = ψ.f 0)
    (hz : ξ ≫ K.d 0 1 = 0) :
    IsIso (kernel.lift (K.d 0 1) ξ hz) := by
  have hS : IsIso (((HomologicalComplex.single B (up ℤ) 0).obj F).iCycles 0) :=
    ((HomologicalComplex.single B (up ℤ) 0).obj F).isIso_iCycles 0 1 (by simp)
      (HomologicalComplex.single_obj_d _ _ _ _ _)
  have hSπ : IsIso (((HomologicalComplex.single B (up ℤ) 0).obj F).homologyπ 0) :=
    ((HomologicalComplex.single B (up ℤ) 0).obj F).isIso_homologyπ (-1) 0 (by simp)
      (HomologicalComplex.single_obj_d _ _ _ _ _)
  have hKπ : IsIso (K.homologyπ 0) :=
    K.isIso_homologyπ (-1) 0 (by simp) (hK.eq_of_src _ _)
  have hψ : IsIso (HomologicalComplex.homologyMap ψ 0) :=
    (quasiIsoAt_iff_isIso_homologyMap ψ 0).1 inferInstance
  have hcyc : IsIso (HomologicalComplex.cyclesMap ψ 0) := by
    have hnat := HomologicalComplex.homologyπ_naturality ψ 0
    have : IsIso (HomologicalComplex.cyclesMap ψ 0 ≫ K.homologyπ 0) := by
      rw [← hnat]; infer_instance
    exact IsIso.of_isIso_comp_right _ (K.homologyπ 0)
  let hker := K.cyclesIsKernel 0 1 (by simp)
  let e : K.cycles 0 ≅ kernel (K.d 0 1) :=
    IsLimit.conePointUniqueUpToIso hker (limit.isLimit _)
  have he : e.hom ≫ kernel.ι (K.d 0 1) = K.iCycles 0 :=
    IsLimit.conePointUniqueUpToIso_hom_comp hker (limit.isLimit _) WalkingParallelPair.zero
  have heq : HomologicalComplex.cyclesMap ψ 0 ≫ e.hom =
      ((HomologicalComplex.single B (up ℤ) 0).obj F).iCycles 0 ≫
        (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom ≫
          kernel.lift (K.d 0 1) ξ hz := by
    apply (cancel_mono (kernel.ι (K.d 0 1))).mp
    simp only [Category.assoc, he, kernel.lift_ι, HomologicalComplex.cyclesMap_i]
    rw [hξ]
  have h₁ : IsIso (((HomologicalComplex.single B (up ℤ) 0).obj F).iCycles 0 ≫
      (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom ≫
        kernel.lift (K.d 0 1) ξ hz) := by
    rw [← heq]; infer_instance
  have h₂ : IsIso ((HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom ≫
      kernel.lift (K.d 0 1) ξ hz) :=
    IsIso.of_isIso_comp_left (((HomologicalComplex.single B (up ℤ) 0).obj F).iCycles 0) _
  exact IsIso.of_isIso_comp_left (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).hom _

/-! ### The augmentation by the Čech complex of the resolved presheaf -/

/-- The presheaf Čech complex functor of the covering preserves finite limits. -/
instance preservesFiniteLimits_presheafCechComplexFunctor :
    PreservesFiniteLimits (presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le) :=
  (CechExactFunctor.presheafCechComplexFunctor_exact.{u, u, u, u}
    O.obj 𝒰.U 𝒰.obj 𝒰.le).1

/-- The presheaf Čech complex functor of the covering preserves finite colimits. -/
instance preservesFiniteColimits_presheafCechComplexFunctor :
    PreservesFiniteColimits (presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le) :=
  (CechExactFunctor.presheafCechComplexFunctor_exact.{u, u, u, u}
    O.obj 𝒰.U 𝒰.obj 𝒰.le).2

/-- The Čech cochains of the covering in a fixed degree. -/
abbrev cechTermFunctor (i : ℕ) : Modules.{u} O ⥤ SectionModules.{u} O 𝒰 :=
  presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le ⋙
    HomologicalComplex.eval _ (up ℕ) i

/-- **The Čech cochain functor in a fixed degree preserves homology**, being exact. -/
instance preservesHomology_cechTermFunctor (i : ℕ) :
    (cechTermFunctor.{u} O 𝒰 i).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The embedding of `ℕ` into `ℤ` as complex shapes is the cast. -/
lemma embeddingUpNat_f (i : ℕ) : embeddingUpNat.f i = (i : ℤ) := by simp

/-- **Extension by zero is, in a degree in the range of the embedding, the original term**,
naturally in the complex. -/
lemma extendXIso_naturality {B : Type*} [Category* B] [Abelian B] {K L : CochainComplex B ℕ}
    (φ : K ⟶ L) {i : ℕ} {i' : ℤ} (h : embeddingUpNat.f i = i') :
    (HomologicalComplex.extendMap φ embeddingUpNat).f i' ≫
        (L.extendXIso embeddingUpNat h).hom =
      (K.extendXIso embeddingUpNat h).hom ≫ φ.f i := by
  rw [HomologicalComplex.extendMap_f φ embeddingUpNat h]
  simp

/-- In a Čech degree in the range of the embedding, the integer-indexed Čech complex is the
Čech cochain functor of Stacks 01EJ. -/
def cechEvalIso (i : ℕ) :
    cechComplexIntFunctor.{u} O 𝒰 ⋙ HomologicalComplex.eval _ (up ℤ) (i : ℤ) ≅
      cechTermFunctor.{u} O 𝒰 i :=
  NatIso.ofComponents
    (fun M => HomologicalComplex.extendXIso
      ((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).obj M) embeddingUpNat
      (embeddingUpNat_f i))
    (fun {_M _N} f => extendXIso_naturality
      ((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).map f)
      (embeddingUpNat_f i))

/-- **The rows of the Čech bicomplex of a resolution are exact away from resolution degree
zero.** Off the range of the embedding the row vanishes; on it the row is the Čech cochains of
the resolution in a fixed degree, and the Čech cochain functor is exact, so it carries the
exactness of the resolution across. -/
lemma exactAt_cechBicomplexFlip_X (K : CochainComplex (Modules.{u} O) ℤ)
    (hK : ∀ q : ℤ, q ≠ 0 → K.ExactAt q) (p q : ℤ) (hq : q ≠ 0) :
    (((cechBicomplex.{u} O 𝒰 K).flip).X p).ExactAt q := by
  rcases lt_or_ge p 0 with hp | hp
  · exact HomologicalComplex.ExactAt.of_isZero
      (isZero_cechBicomplex_X_X O 𝒰 K q p (Or.inr hp))
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ℤ) = p := ⟨p.toNat, by omega⟩
    have hiso : ((cechBicomplex.{u} O 𝒰 K).flip).X (i : ℤ) ≅
        ((cechTermFunctor.{u} O 𝒰 i).mapHomologicalComplex (up ℤ)).obj K :=
      (NatIso.mapHomologicalComplex (cechEvalIso.{u} O 𝒰 i) (up ℤ)).app K
    refine (HomologicalComplex.exactAt_iff_isZero_homology _ q).2 ?_
    refine (Iso.isZero_iff ((HomologicalComplex.homologyFunctor
      (SectionModules.{u} O 𝒰) (up ℤ) q).mapIso hiso)).2 ?_
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ q).1
      (exactAt_mapHomologicalComplex (up ℤ) (cechTermFunctor.{u} O 𝒰 i) K q (hK q hq))

/-- **The kernel clause of Stacks 0133 for the rows of the Čech bicomplex**: the Čech complex
of the resolved presheaf is, in each Čech degree, a kernel of the first differential of the
row. Off the range of the embedding both terms vanish; on it the clause is the image under the
exact Čech cochain functor of the corresponding clause for the resolution itself. -/
lemma inducesIsoKernel_cechBetaRow (K : CochainComplex (Modules.{u} O) ℤ) {F : Modules.{u} O}
    (ξ : F ⟶ K.X 0) (hz : ξ ≫ K.d 0 1 = 0) (hker : IsIso (kernel.lift (K.d 0 1) ξ hz))
    (p : ℤ) :
    ∃ hβ : ((cechComplexIntFunctor.{u} O 𝒰).map ξ).f p ≫
        (((cechBicomplex.{u} O 𝒰 K).flip).X p).d 0 1 = 0,
      IsIso (kernel.lift ((((cechBicomplex.{u} O 𝒰 K).flip).X p).d 0 1)
        (((cechComplexIntFunctor.{u} O 𝒰).map ξ).f p) hβ) := by
  have hβ : ((cechComplexIntFunctor.{u} O 𝒰).map ξ).f p ≫
      (((cechBicomplex.{u} O 𝒰 K).flip).X p).d 0 1 = 0 := by
    show ((cechComplexIntFunctor.{u} O 𝒰).map ξ).f p ≫
      ((cechComplexIntFunctor.{u} O 𝒰).map (K.d 0 1)).f p = 0
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, hz, Functor.map_zero,
      HomologicalComplex.zero_f]
  refine ⟨hβ, ?_⟩
  have hmonoξ : Mono ξ := by
    rw [← kernel.lift_ι (K.d 0 1) ξ hz]
    infer_instance
  rcases lt_or_ge p 0 with hp | hp
  · refine StacksDraft.TotalComplexQuasiIso.isIso_of_isZero _
      (isZero_cechComplexIntFunctor_X O 𝒰 F p hp) ?_
    exact IsZero.of_mono (kernel.ι ((((cechBicomplex.{u} O 𝒰 K).flip).X p).d 0 1))
      (isZero_cechBicomplex_X_X O 𝒰 K 0 p (Or.inr hp))
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, (i : ℤ) = p := ⟨p.toNat, by omega⟩
    have heq : ((cechComplexIntFunctor.{u} O 𝒰).map ξ).f (i : ℤ) =
        (HomologicalComplex.extendXIso
            ((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).obj F)
            embeddingUpNat (embeddingUpNat_f i)).hom ≫
          ((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).map ξ).f i ≫
          (HomologicalComplex.extendXIso
            ((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).obj (K.X 0))
            embeddingUpNat (embeddingUpNat_f i)).inv :=
      HomologicalComplex.extendMap_f _ embeddingUpNat (embeddingUpNat_f i)
    have hmono : Mono (((cechComplexIntFunctor.{u} O 𝒰).map ξ).f (i : ℤ)) := by
      have hm : Mono ((cechTermFunctor.{u} O 𝒰 i).map ξ) := inferInstance
      have hm' : Mono
          (((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).map ξ).f i) := hm
      rw [heq]
      have h1 : Mono
          (((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).map ξ).f i ≫
            (HomologicalComplex.extendXIso
              ((presheafCechComplexFunctor.{u, u, u, u} O.obj 𝒰.U 𝒰.obj 𝒰.le).obj (K.X 0))
              embeddingUpNat (embeddingUpNat_f i)).inv) := mono_comp _ _
      exact @mono_comp _ _ _ _ _ _ (mono_iso_hom _) _ h1
    have hexS : (ShortComplex.mk ξ (K.d 0 1) hz).Exact := by
      have := hker
      exact (ShortComplex.exact_iff_epi_kernel_lift _).2 inferInstance
    have hexT : ((ShortComplex.mk ξ (K.d 0 1) hz).map (cechTermFunctor.{u} O 𝒰 i)).Exact :=
      hexS.map _
    have eiso : (ShortComplex.mk ξ (K.d 0 1) hz).map (cechTermFunctor.{u} O 𝒰 i) ≅
        ShortComplex.mk (((cechComplexIntFunctor.{u} O 𝒰).map ξ).f (i : ℤ))
          ((((cechBicomplex.{u} O 𝒰 K).flip).X (i : ℤ)).d 0 1) hβ :=
      ShortComplex.isoMk ((cechEvalIso.{u} O 𝒰 i).app F).symm
        ((cechEvalIso.{u} O 𝒰 i).app (K.X 0)).symm
        ((cechEvalIso.{u} O 𝒰 i).app (K.X 1)).symm
        ((cechEvalIso.{u} O 𝒰 i).inv.naturality ξ).symm
        ((cechEvalIso.{u} O 𝒰 i).inv.naturality (K.d 0 1)).symm
    exact @isIso_kernelLift_of_mono_of_exact _ _ _ _ _ _ _ _ _ hmono
      (ShortComplex.exact_of_iso eiso hexT)

/-! ### The two augmentations into the total Čech complex -/

/-- **The augmentation `β`**, as a morphism into the zeroth row of the flipped Čech bicomplex:
in Čech degree `p` it is the Čech `p`-cochains of the augmentation `F ⟶ K⁰`. -/
def cechBetaRow (K : CochainComplex (Modules.{u} O) ℤ) {F : Modules.{u} O} (ξ : F ⟶ K.X 0) :
    (cechComplexIntFunctor.{u} O 𝒰).obj F ⟶ rowZero ((cechBicomplex.{u} O 𝒰 K).flip) where
  f p := ((cechComplexIntFunctor.{u} O 𝒰).map ξ).f p
  comm' p p' _ := ((cechComplexIntFunctor.{u} O 𝒰).map ξ).comm p p'

/-- The components of `cechBetaRow`. -/
@[simp]
lemma cechBetaRow_f (K : CochainComplex (Modules.{u} O) ℤ) {F : Modules.{u} O} (ξ : F ⟶ K.X 0)
    (p : ℤ) :
    (cechBetaRow.{u} O 𝒰 K ξ).f p = ((cechComplexIntFunctor.{u} O 𝒰).map ξ).f p := rfl

/-- **The antidiagonals of the flipped Čech bicomplex are finite.** -/
lemma diagonalFinite_cechBicomplexFlip (K : CochainComplex (Modules.{u} O) ℤ)
    [K.IsStrictlyGE 0] : DiagonalFinite ((cechBicomplex.{u} O 𝒰 K).flip) := by
  intro n
  refine (Set.finite_Icc (0 : ℤ) n).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hp (isZero_cechBicomplex_X_X O 𝒰 K (n - p) p (Or.inr (by omega)))
  · by_contra h
    exact hp (isZero_cechBicomplex_X_X O 𝒰 K (n - p) p
      (Or.inl (K.isZero_of_isStrictlyGE 0 (n - p) (by omega))))

/-- The flipped Čech bicomplex of a complex bounded below in degree `0` has a total complex. -/
instance hasTotal_cechBicomplexFlip (K : CochainComplex (Modules.{u} O) ℤ)
    [K.IsStrictlyGE 0] : ((cechBicomplex.{u} O 𝒰 K).flip).HasTotal (up ℤ) :=
  hasTotal_of_diagonalFinite _ (diagonalFinite_cechBicomplexFlip O 𝒰 K)

/-- **The hypotheses of Stacks 0133 for the flipped Čech bicomplex of a resolution**, with the
augmentation by the Čech complex of the resolved presheaf. -/
theorem hypotheses_cechBetaRow (K : CochainComplex (Modules.{u} O) ℤ) [K.IsStrictlyGE 0]
    {F : Modules.{u} O} (ξ : F ⟶ K.X 0) (hz : ξ ≫ K.d 0 1 = 0)
    (hker : IsIso (kernel.lift (K.d 0 1) ξ hz)) (hK : ∀ q : ℤ, q ≠ 0 → K.ExactAt q) :
    Hypotheses ((cechComplexIntFunctor.{u} O 𝒰).obj F) ((cechBicomplex.{u} O 𝒰 K).flip)
      (cechBetaRow.{u} O 𝒰 K ξ) where
  diagonalFinite := diagonalFinite_cechBicomplexFlip O 𝒰 K
  zero_of_neg p q hq := isZero_cechBicomplex_X_X O 𝒰 K q p
    (Or.inl (K.isZero_of_isStrictlyGE 0 q (by omega)))
  exactAt_of_ne_zero p q hq := exactAt_cechBicomplexFlip_X O 𝒰 K hK p q hq
  inducesIsoKernel p := inducesIsoKernel_cechBetaRow O 𝒰 K ξ hz hker p

/-- **The augmentation `α` of Stacks 01EN**: the degree-zero Čech cohomology of a bounded-below
complex of injective presheaves includes into the total complex of its Čech bicomplex, in the
`(q, 0)` corner. -/
def cechAlpha (K : CochainComplex (Modules.{u} O) ℤ) [K.IsStrictlyGE 0]
    (hinj : ∀ q, Injective (K.X q)) :
    ((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj K ⟶
      (cechBicomplex.{u} O 𝒰 K).total (up ℤ) :=
  comparisonMapP _ _ _ (hypotheses_cechAlphaRow.{u} O 𝒰 K hinj)

/-- **The component formula for `α`**, exactly as Stacks 01EN prescribes it. -/
lemma cechAlpha_f (K : CochainComplex (Modules.{u} O) ℤ) [K.IsStrictlyGE 0]
    (hinj : ∀ q, Injective (K.X q)) (q : ℤ) :
    (cechAlpha.{u} O 𝒰 K hinj).f q = cechZeroInclusion.{u} O 𝒰 (K.X q) ≫
      (cechBicomplex.{u} O 𝒰 K).ιTotal (up ℤ) q 0 q (by simp) :=
  comparisonMapP_f _ _ _ _ q

/-- **`α` is a quasi-isomorphism**, by Stacks 0133: the columns of the Čech bicomplex of a
complex of injective presheaves are the Čech complexes of injective presheaves, which have no
higher Čech cohomology. -/
instance quasiIso_cechAlpha (K : CochainComplex (Modules.{u} O) ℤ) [K.IsStrictlyGE 0]
    (hinj : ∀ q, Injective (K.X q)) : QuasiIso (cechAlpha.{u} O 𝒰 K hinj) :=
  quasiIso_comparisonMapP _ _ _ _

/-- **The augmentation `β` of Stacks 01EN**: the Čech complex of the resolved presheaf includes
into the total complex of the Čech bicomplex of the resolution, in the `(0, p)` corner. -/
def cechBeta (K : CochainComplex (Modules.{u} O) ℤ) [K.IsStrictlyGE 0] {F : Modules.{u} O}
    (ξ : F ⟶ K.X 0) (hz : ξ ≫ K.d 0 1 = 0) (hker : IsIso (kernel.lift (K.d 0 1) ξ hz))
    (hK : ∀ q : ℤ, q ≠ 0 → K.ExactAt q) :
    (cechComplexIntFunctor.{u} O 𝒰).obj F ⟶ (cechBicomplex.{u} O 𝒰 K).total (up ℤ) :=
  comparisonMapP _ _ _ (hypotheses_cechBetaRow.{u} O 𝒰 K ξ hz hker hK) ≫
    ((cechBicomplex.{u} O 𝒰 K).totalFlipIso (up ℤ)).hom

/-- **The component formula for `β`**, exactly as Stacks 01EN prescribes it. The sign that
flipping a total complex introduces is `(-1)^{0 · p}`, hence trivial. -/
lemma cechBeta_f (K : CochainComplex (Modules.{u} O) ℤ) [K.IsStrictlyGE 0] {F : Modules.{u} O}
    (ξ : F ⟶ K.X 0) (hz : ξ ≫ K.d 0 1 = 0) (hker : IsIso (kernel.lift (K.d 0 1) ξ hz))
    (hK : ∀ q : ℤ, q ≠ 0 → K.ExactAt q) (p : ℤ) :
    (cechBeta.{u} O 𝒰 K ξ hz hker hK).f p = ((cechComplexIntFunctor.{u} O 𝒰).map ξ).f p ≫
      (cechBicomplex.{u} O 𝒰 K).ιTotal (up ℤ) 0 p p (by simp) := by
  dsimp only [cechBeta]
  rw [HomologicalComplex.comp_f, comparisonMapP_f, Category.assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom]
  simp
  rfl

/-- **`β` is a quasi-isomorphism**, by Stacks 0133: the rows of the Čech bicomplex of a
resolution are the Čech cochains of that resolution in a fixed degree, and the Čech cochain
functor is exact. -/
instance quasiIso_cechBeta (K : CochainComplex (Modules.{u} O) ℤ) [K.IsStrictlyGE 0]
    {F : Modules.{u} O} (ξ : F ⟶ K.X 0) (hz : ξ ≫ K.d 0 1 = 0)
    (hker : IsIso (kernel.lift (K.d 0 1) ξ hz)) (hK : ∀ q : ℤ, q ≠ 0 → K.ExactAt q) :
    QuasiIso (cechBeta.{u} O 𝒰 K ξ hz hker hK) := by
  dsimp only [cechBeta]
  have := quasiIso_comparisonMapP ((cechComplexIntFunctor.{u} O 𝒰).obj F)
    ((cechBicomplex.{u} O 𝒰 K).flip) (cechBetaRow.{u} O 𝒰 K ξ)
    (hypotheses_cechBetaRow.{u} O 𝒰 K ξ hz hker hK)
  infer_instance

/-! #### Both augmentations are natural in the resolution -/

/-- The map of Čech bicomplexes induced by a morphism of complexes of presheaves. -/
noncomputable def cechBicomplexMap {K K' : CochainComplex (Modules.{u} O) ℤ} (φ : K ⟶ K') :
    cechBicomplex.{u} O 𝒰 K ⟶ cechBicomplex.{u} O 𝒰 K' :=
  ((cechComplexIntFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).map φ

/-- The induced map of total complexes. -/
noncomputable def cechTotalMap {K K' : CochainComplex (Modules.{u} O) ℤ} [K.IsStrictlyGE 0]
    [K'.IsStrictlyGE 0] (φ : K ⟶ K') :
    (cechBicomplex.{u} O 𝒰 K).total (up ℤ) ⟶ (cechBicomplex.{u} O 𝒰 K').total (up ℤ) :=
  HomologicalComplex₂.total.map (cechBicomplexMap.{u} O 𝒰 φ) (up ℤ)

/-- **The inclusion of a summand commutes with the induced map of total complexes.** -/
lemma ιTotal_comp_cechTotalMap {K K' : CochainComplex (Modules.{u} O) ℤ} [K.IsStrictlyGE 0]
    [K'.IsStrictlyGE 0] (φ : K ⟶ K') (q p n : ℤ) (h : q + p = n) :
    (cechBicomplex.{u} O 𝒰 K).ιTotal (up ℤ) q p n h ≫ (cechTotalMap.{u} O 𝒰 φ).f n =
      ((cechComplexIntFunctor.{u} O 𝒰).map (φ.f q)).f p ≫
        (cechBicomplex.{u} O 𝒰 K').ιTotal (up ℤ) q p n h :=
  HomologicalComplex₂.ιTotal_map _ _ (cechBicomplexMap.{u} O 𝒰 φ) (up ℤ) q p n h

/-- **`α` is natural in the resolved complex.** Its components are the inclusion of degree-zero
Čech cohomology into degree-zero Čech cochains, which is natural, so the square is that
naturality read inside the `(q, 0)` summand of the total complex. -/
lemma cechAlpha_comp_cechTotalMap (K K' : CochainComplex (Modules.{u} O) ℤ) [K.IsStrictlyGE 0]
    [K'.IsStrictlyGE 0] (hinj : ∀ q, Injective (K.X q)) (hinj' : ∀ q, Injective (K'.X q))
    (φ : K ⟶ K') :
    cechAlpha.{u} O 𝒰 K hinj ≫ cechTotalMap.{u} O 𝒰 φ =
      ((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).map φ ≫
        cechAlpha.{u} O 𝒰 K' hinj' :=
  HomologicalComplex.hom_ext _ _ fun q =>
    (congrArg (fun m => m ≫ (cechTotalMap.{u} O 𝒰 φ).f q)
        (cechAlpha_f.{u} O 𝒰 K hinj q)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => cechZeroInclusion.{u} O 𝒰 (K.X q) ≫ m)
            (ιTotal_comp_cechTotalMap.{u} O 𝒰 φ q 0 q (by simp))).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg
                (fun m => m ≫ (cechBicomplex.{u} O 𝒰 K').ιTotal (up ℤ) q 0 q (by simp))
                (cechZeroInclusion_naturality.{u} O 𝒰 (φ.f q))).trans
              ((Category.assoc _ _ _).trans
                (congrArg
                  (fun m => (cechCohomologyZeroFunctor.{u} O 𝒰).map (φ.f q) ≫ m)
                  (cechAlpha_f.{u} O 𝒰 K' hinj' q).symm))))))

/-- **`β` is natural in the resolution, over any morphism of presheaves compatible with the two
augmentations.** Its components are the Čech cochains of the augmentation, so the square is the
image under the Čech cochain functors of the compatibility `hξ`, read inside the `(0, p)`
summand of the total complex. -/
lemma cechBeta_comp_cechTotalMap (K K' : CochainComplex (Modules.{u} O) ℤ) [K.IsStrictlyGE 0]
    [K'.IsStrictlyGE 0] {F G : Modules.{u} O} (f : F ⟶ G)
    (ξ : F ⟶ K.X 0) (hz : ξ ≫ K.d 0 1 = 0) (hker : IsIso (kernel.lift (K.d 0 1) ξ hz))
    (hK : ∀ q : ℤ, q ≠ 0 → K.ExactAt q)
    (ξ' : G ⟶ K'.X 0) (hz' : ξ' ≫ K'.d 0 1 = 0) (hker' : IsIso (kernel.lift (K'.d 0 1) ξ' hz'))
    (hK' : ∀ q : ℤ, q ≠ 0 → K'.ExactAt q)
    (φ : K ⟶ K') (hξ : ξ ≫ φ.f 0 = f ≫ ξ') :
    cechBeta.{u} O 𝒰 K ξ hz hker hK ≫ cechTotalMap.{u} O 𝒰 φ =
      (cechComplexIntFunctor.{u} O 𝒰).map f ≫ cechBeta.{u} O 𝒰 K' ξ' hz' hker' hK' :=
  HomologicalComplex.hom_ext _ _ fun p =>
    have hcomp : ((cechComplexIntFunctor.{u} O 𝒰).map ξ).f p ≫
          ((cechComplexIntFunctor.{u} O 𝒰).map (φ.f 0)).f p =
        ((cechComplexIntFunctor.{u} O 𝒰).map f).f p ≫
          ((cechComplexIntFunctor.{u} O 𝒰).map ξ').f p := by
      rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← Functor.map_comp,
        ← Functor.map_comp, hξ]
    (congrArg (fun m => m ≫ (cechTotalMap.{u} O 𝒰 φ).f p)
        (cechBeta_f.{u} O 𝒰 K ξ hz hker hK p)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun m => ((cechComplexIntFunctor.{u} O 𝒰).map ξ).f p ≫ m)
            (ιTotal_comp_cechTotalMap.{u} O 𝒰 φ 0 p p (by simp))).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg
                (fun m => m ≫ (cechBicomplex.{u} O 𝒰 K').ιTotal (up ℤ) 0 p p (by simp))
                hcomp).trans
              ((Category.assoc _ _ _).trans
                (congrArg
                  (fun m => ((cechComplexIntFunctor.{u} O 𝒰).map f).f p ≫ m)
                  (cechBeta_f.{u} O 𝒰 K' ξ' hz' hker' hK' p).symm))))))

/-! ### The two augmentations at an injective resolution -/

/-- The augmentation `F ⟶ J⁰` of an injective resolution, read in integer degrees. This is the
morphism whose Čech cochains make up `β`. -/
def resolutionAug {B : Type*} [Category* B] [Abelian B] {F : B} (J : InjectiveResolution F) :
    F ⟶ J.cochainComplex.X 0 :=
  (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).inv ≫ J.ι'.f 0

/-- The augmentation of a resolution is killed by the first differential. -/
lemma resolutionAug_comp_d {B : Type*} [Category* B] [Abelian B] {F : B}
    (J : InjectiveResolution F) : resolutionAug J ≫ J.cochainComplex.d 0 1 = 0 := by
  have hd : ((CochainComplex.singleFunctor B 0).obj F).d 0 1 = 0 :=
    HomologicalComplex.single_obj_d (up ℤ) 0 F 0 1
  dsimp only [resolutionAug]
  rw [Category.assoc, J.ι'.comm 0 1, hd, zero_comp, comp_zero]

/-- **The augmentation of an injective resolution is a kernel of the first differential.** -/
lemma isIso_kernelLift_resolutionAug {B : Type*} [Category* B] [Abelian B] {F : B}
    (J : InjectiveResolution F) :
    IsIso (kernel.lift (J.cochainComplex.d 0 1) (resolutionAug J) (resolutionAug_comp_d J)) :=
  isIso_kernelLift_of_quasiIso_single
    (CochainComplex.isZero_of_isStrictlyGE J.cochainComplex 0 (-1) (by omega)) J.ι'
    (resolutionAug J) (by simp [resolutionAug]) (resolutionAug_comp_d J)

/-- **An injective resolution is exact away from degree zero.** -/
lemma exactAt_cochainComplex {B : Type*} [Category* B] [Abelian B] {F : B}
    (J : InjectiveResolution F) (q : ℤ) (hq : q ≠ 0) : J.cochainComplex.ExactAt q :=
  (quasiIsoAt_iff_exactAt J.ι' q (HomologicalComplex.ExactAt.of_isZero
    (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 F q hq))).1 inferInstance

section Resolution

variable {F : Modules.{u} O} (J : InjectiveResolution F)

/-- **The augmentation `α` at an injective resolution.** -/
def cechAlphaRes :
    ((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).obj
        J.cochainComplex ⟶
      (cechBicomplex.{u} O 𝒰 J.cochainComplex).total (up ℤ) :=
  cechAlpha.{u} O 𝒰 J.cochainComplex (fun _ => inferInstance)

/-- The augmentation `cechAlphaRes` at an injective resolution is a quasi-isomorphism. -/
instance quasiIso_cechAlphaRes : QuasiIso (cechAlphaRes.{u} O 𝒰 J) :=
  quasiIso_cechAlpha.{u} O 𝒰 J.cochainComplex (fun _ => inferInstance)

/-- **The augmentation `β` at an injective resolution.** -/
def cechBetaRes :
    (cechComplexIntFunctor.{u} O 𝒰).obj F ⟶
      (cechBicomplex.{u} O 𝒰 J.cochainComplex).total (up ℤ) :=
  cechBeta.{u} O 𝒰 J.cochainComplex (resolutionAug J) (resolutionAug_comp_d J)
    (isIso_kernelLift_resolutionAug J) (exactAt_cochainComplex J)

/-- The augmentation `cechBetaRes` at an injective resolution is a quasi-isomorphism. -/
instance quasiIso_cechBetaRes : QuasiIso (cechBetaRes.{u} O 𝒰 J) :=
  quasiIso_cechBeta.{u} O 𝒰 J.cochainComplex (resolutionAug J) (resolutionAug_comp_d J)
    (isIso_kernelLift_resolutionAug J) (exactAt_cochainComplex J)

/-! #### The comparison with the total right derived functor is an isomorphism -/

/-- The identification of `Qh ∘ quotient` with `Q` at an injective resolution, read in the
bounded-below derived category. -/
noncomputable def resolutionQhQ :
    DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient (Modules.{u} O)).obj
          ⟨J.cochainComplex, 0, inferInstance⟩) ⟶
      DerivedCategory.Plus.Q.obj
        (⟨J.cochainComplex, 0, inferInstance⟩ : CochainComplex.Plus (Modules.{u} O)) :=
  ObjectProperty.homMk
    ((DerivedCategory.quotientCompQhIso (Modules.{u} O)).hom.app J.cochainComplex)

/-- **The two comparisons of `F` with its injective resolution agree.** The one used here,
`injectiveResolutionIso`, is the image under `DerivedCategory.Q` of the augmentation; the one
used by the connecting-morphism comparison,
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedIso`, is built in the homotopy
category and lands in `Qh ∘ quotient`. They differ exactly by `resolutionQhQ`, which is what
`Stacks.Cohomology.HigherDirectImagePresheaf.Q_map_resolutionSingleHom` says, the inclusion of
the bounded-below derived category into the derived category being faithful. -/
lemma resolutionDerivedIso_hom_comp :
    (resolutionDerivedIso J).hom ≫ resolutionQhQ.{u} O J =
      (injectiveResolutionIso.{u} O F J).hom :=
  DerivedCategory.Plus.ι.map_injective
    ((DerivedCategory.Plus.ι.map_comp _ _).trans (Q_map_resolutionSingleHom J))

/-- The inverse form of `resolutionDerivedIso_hom_comp`. -/
lemma resolutionDerivedIso_inv_eq :
    (resolutionDerivedIso J).inv =
      resolutionQhQ.{u} O J ≫ (injectiveResolutionIso.{u} O F J).inv :=
  (Iso.eq_comp_inv (injectiveResolutionIso.{u} O F J)).2
    ((congrArg (fun φ => (resolutionDerivedIso J).inv ≫ φ)
        (resolutionDerivedIso_hom_comp O J).symm).trans
      (Iso.inv_hom_id_assoc (resolutionDerivedIso J) (resolutionQhQ.{u} O J)))

/-- **The comparison of the Čech `Ȟ⁰` of an injective resolution with the total right derived
functor is the inverse of
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedComparison`.** Both are the same
composite: the identification of `Q` with `Qh ∘ quotient`, the unit of the total right derived
functor at the resolution, and the comparison of `F` with that resolution. The only difference
is which of the two spellings of the last factor is used, and `resolutionDerivedIso_inv_eq`
identifies those. -/
lemma injectiveResolutionToRightDerived_eq :
    injectiveResolutionToRightDerived.{u} O 𝒰 F J =
      (resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J).inv := by
  have step : (rightDerivedCechFunctor.{u} O 𝒰).map (resolutionQhQ.{u} O J) ≫
      ((rightDerivedCechFunctor.{u} O 𝒰).mapIso (injectiveResolutionIso.{u} O F J)).inv =
      (rightDerivedCechFunctor.{u} O 𝒰).map (resolutionDerivedIso J).inv := by
    rw [Functor.mapIso_inv, ← Functor.map_comp, ← resolutionDerivedIso_inv_eq O J]
    rfl
  have h2 := congrArg (fun φ => DerivedCategory.Plus.ι.map φ) step
  rw [resolutionDerivedComparison_inv]
  exact whisker_eq _ (whisker_eq _ h2)

/-- **The comparison of the Čech `Ȟ⁰` of an injective resolution with the total right derived
functor is an isomorphism**, being the inverse of one. -/
instance isIso_injectiveResolutionToRightDerived :
    IsIso (injectiveResolutionToRightDerived.{u} O 𝒰 F J) := by
  rw [injectiveResolutionToRightDerived_eq O 𝒰 J]
  exact ⟨(resolutionDerivedComparison (cechCohomologyZeroFunctor.{u} O 𝒰) J).hom,
    Iso.inv_hom_id _, Iso.hom_inv_id _⟩

/-- **The whole of a `CechResolutionComparison` except the comparison equation.** Both
augmentations, both component formulas and both quasi-isomorphy statements of Stacks 01EN's
*moreover* clause are supplied here; what is left for a caller is exactly the equation
identifying the given natural isomorphism with `Q(β) ≫ Q(α)⁻¹` followed by the identification
of the Čech `Ȟ⁰` of the resolution with the total right derived functor. -/
def cechResolutionComparisonOfComparison
    (e : cechComplexPlusFunctor.{u} O 𝒰 ⋙ DerivedCategory.Plus.Q ≅
      DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0 ⋙ rightDerivedCechFunctor.{u} O 𝒰)
    (hcomp : (e.hom.app F).hom = DerivedCategory.Q.map (cechBetaRes.{u} O 𝒰 J) ≫
      inv (DerivedCategory.Q.map (cechAlphaRes.{u} O 𝒰 J)) ≫
      injectiveResolutionToRightDerived.{u} O 𝒰 F J) :
    CechResolutionComparison.{u} O 𝒰 e F J where
  α := cechAlphaRes.{u} O 𝒰 J
  β := cechBetaRes.{u} O 𝒰 J
  α_f q := cechAlpha_f.{u} O 𝒰 J.cochainComplex (fun _ => inferInstance) q
  β_f p := cechBeta_f.{u} O 𝒰 J.cochainComplex (resolutionAug J) (resolutionAug_comp_d J)
    (isIso_kernelLift_resolutionAug J) (exactAt_cochainComplex J) p
  comparison := hcomp

end Resolution

/-! ### Naturality of the comparison with the total right derived functor

The remaining input for the *moreover* clause of Stacks 01EN is that the comparison of the
Čech `Ȟ⁰` of an injective resolution with the total right derived functor is compatible with a
morphism of resolutions.  Via `injectiveResolutionToRightDerived_eq` that is naturality of
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedComparison`, which is proved
here for an arbitrary additive functor.
-/

/-- Applying a functor to an equation `a ≫ b = c ≫ d` gives an equation of the same shape. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {W Y Z T : C} {a : W ⟶ Y} {b : Y ⟶ T} {c : W ⟶ Z} {d : Z ⟶ T} (h : a ≫ b = c ≫ d) :
    G.map a ≫ G.map b = G.map c ≫ G.map d := by
  rw [← G.map_comp, ← G.map_comp, h]

/-- An isomorphism-conjugated square: from `a ≫ b = c ≫ d` with `a` and `d` invertible. -/
lemma comp_iso_inv_eq {C : Type*} [Category* C] {W Y Z T : C} (a : W ≅ Y) (b : Y ⟶ T)
    (c : W ⟶ Z) (d : Z ≅ T) (h : a.hom ≫ b = c ≫ d.hom) : b ≫ d.inv = a.inv ≫ c := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, h]

/-- The same with invertibility given by instances rather than by isomorphisms. -/
lemma comp_inv_eq_inv_comp {C : Type*} [Category* C] {W Y Z T : C} (a : W ⟶ Y) (b : Y ⟶ T)
    (c : W ⟶ Z) (d : Z ⟶ T) [IsIso a] [IsIso d] (h : a ≫ b = c ≫ d) :
    b ≫ inv d = inv a ≫ c := by
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, h]

/-- **The comparison of an object with its injective resolution in `D⁺` is natural.** Its three
factors are two components of natural isomorphisms and the localization of the augmentation, so
the square is two naturality statements together with the naturality of the augmentation
(`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionSingleHom_naturality`). -/
lemma resolutionDerivedIso_naturality {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {M N : A} (f : M ⟶ N) (I : InjectiveResolution M)
    (J : InjectiveResolution N) (ψ : I.cocomplex ⟶ J.cocomplex)
    (hψ : (CochainComplex.single₀ A).map f ≫ J.ι = I.ι ≫ ψ) :
    (resolutionDerivedIso I).hom ≫ DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient A).map
          (⟨HomologicalComplex.extendMap ψ embeddingUpNat⟩ :
            resolutionCochainPlus I ⟶ resolutionCochainPlus J)) =
      (DerivedCategory.Plus.singleFunctor A 0).map f ≫ (resolutionDerivedIso J).hom := by
  have hnat : resolutionSinglePlusHom I ≫
      (⟨HomologicalComplex.extendMap ψ embeddingUpNat⟩ :
        resolutionCochainPlus I ⟶ resolutionCochainPlus J) =
      (singleCochainPlusFunctor (A := A)).map f ≫ resolutionSinglePlusHom J :=
    ObjectProperty.hom_ext _ (resolutionSingleHom_naturality I J f ψ hψ).symm
  have hC : DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient A).map (resolutionSinglePlusHom I)) ≫
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient A).map
        (⟨HomologicalComplex.extendMap ψ embeddingUpNat⟩ :
          resolutionCochainPlus I ⟶ resolutionCochainPlus J)) =
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient A).map
          ((singleCochainPlusFunctor (A := A)).map f)) ≫
        DerivedCategory.Plus.Qh.map
          ((HomotopyCategory.Plus.quotient A).map (resolutionSinglePlusHom J)) :=
    map_comp_eq_map_comp (HomotopyCategory.Plus.quotient A ⋙ DerivedCategory.Plus.Qh) hnat
  have hB : DerivedCategory.Plus.Qh.map
        ((singlePlusToCochainQuotientIso (A := A)).hom.app M) ≫
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient A).map
        ((singleCochainPlusFunctor (A := A)).map f)) =
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor A 0).map f) ≫
        DerivedCategory.Plus.Qh.map
          ((singlePlusToCochainQuotientIso (A := A)).hom.app N) :=
    map_comp_eq_map_comp DerivedCategory.Plus.Qh
      ((singlePlusToCochainQuotientIso (A := A)).hom.naturality f).symm
  have hA : (Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app M ≫
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor A 0).map f) =
      (DerivedCategory.Plus.singleFunctor A 0).map f ≫
        (Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app N :=
    ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.naturality f).symm
  rw [resolutionDerivedIso_hom_eq', resolutionDerivedIso_hom_eq']
  simp only [Category.assoc]
  rw [hC, reassoc_of% hB, reassoc_of% hA]

/-- **The inverse of the unit of the total right derived functor is natural** wherever the unit
is invertible. -/
lemma inv_unit_naturality {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] (Φ : A ⥤ B) [Φ.Additive] [EnoughInjectives A]
    {Y Z : HomotopyCategory.Plus A} (g : Y ⟶ Z)
    [IsIso (Φ.rightDerivedFunctorPlusUnith.app Y)]
    [IsIso (Φ.rightDerivedFunctorPlusUnith.app Z)] :
    inv (Φ.rightDerivedFunctorPlusUnith.app Y) ≫
        (Φ.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map g =
      Φ.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map g) ≫
        inv (Φ.rightDerivedFunctorPlusUnith.app Z) := by
  rw [← cancel_mono (Φ.rightDerivedFunctorPlusUnith.app Z), Category.assoc, Category.assoc,
    IsIso.inv_hom_id, Category.comp_id, Φ.rightDerivedFunctorPlusUnith.naturality g,
    IsIso.inv_hom_id_assoc]
  rfl

/-- **The derived-category comparison of `RΦ` at a resolution is natural**, in `D⁺`. -/
lemma derivedPlusResolutionIso_naturality {A B : Type*} [Category* A] [Category* B] [Abelian A]
    [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] (Φ : A ⥤ B) [Φ.Additive]
    [EnoughInjectives A] {M N : A} (f : M ⟶ N) (I : InjectiveResolution M)
    (J : InjectiveResolution N) (ψ : I.cocomplex ⟶ J.cocomplex)
    (hψ : (CochainComplex.single₀ A).map f ≫ J.ι = I.ι ≫ ψ) :
    (derivedPlusResolutionIso Φ I).hom ≫
        (Φ.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map
          ((HomotopyCategory.Plus.quotient A).map
            (⟨HomologicalComplex.extendMap ψ embeddingUpNat⟩ :
              resolutionCochainPlus I ⟶ resolutionCochainPlus J)) =
      Φ.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map f) ≫
        (derivedPlusResolutionIso Φ J).hom := by
  have hdI : (derivedPlusResolutionIso Φ I).hom =
      Φ.rightDerivedFunctorPlus.map (resolutionDerivedIso I).hom ≫
        inv (Φ.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I))) := rfl
  have hdJ : (derivedPlusResolutionIso Φ J).hom =
      Φ.rightDerivedFunctorPlus.map (resolutionDerivedIso J).hom ≫
        inv (Φ.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus J))) := rfl
  rw [hdI, hdJ, Category.assoc, inv_unit_naturality, ← Category.assoc, ← Functor.map_comp,
    resolutionDerivedIso_naturality f I J ψ hψ, Functor.map_comp, Category.assoc]

/-- **`resolutionDerivedComparison` is natural in the resolution**, read in the full derived
category. -/
lemma resolutionDerivedComparison_naturality {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] (Φ : A ⥤ B)
    [Φ.Additive] [EnoughInjectives A] {M N : A} (f : M ⟶ N) (I : InjectiveResolution M)
    (J : InjectiveResolution N) (ψ : I.cocomplex ⟶ J.cocomplex)
    (hψ : (CochainComplex.single₀ A).map f ≫ J.ι = I.ι ≫ ψ) :
    (resolutionDerivedComparison Φ I).hom ≫ DerivedCategory.Q.map
        ((Φ.mapHomologicalComplex (up ℤ)).map
          (HomologicalComplex.extendMap ψ embeddingUpNat)) =
      DerivedCategory.Plus.ι.map
          (Φ.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map f)) ≫
        (resolutionDerivedComparison Φ J).hom := by
  have hq : ((DerivedCategory.quotientCompQhIso B).app
          ((Φ.mapHomologicalComplex (up ℤ)).obj
            (HomologicalComplex.extend I.cocomplex embeddingUpNat))).hom ≫
        DerivedCategory.Q.map ((Φ.mapHomologicalComplex (up ℤ)).map
          (HomologicalComplex.extendMap ψ embeddingUpNat)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (up ℤ)).map
          ((Φ.mapHomologicalComplex (up ℤ)).map
            (HomologicalComplex.extendMap ψ embeddingUpNat))) ≫
        ((DerivedCategory.quotientCompQhIso B).app
          ((Φ.mapHomologicalComplex (up ℤ)).obj
            (HomologicalComplex.extend J.cocomplex embeddingUpNat))).hom :=
    ((DerivedCategory.quotientCompQhIso B).hom.naturality
      ((Φ.mapHomologicalComplex (up ℤ)).map
        (HomologicalComplex.extendMap ψ embeddingUpNat))).symm
  have hbridge : DerivedCategory.Qh.map ((HomotopyCategory.quotient B (up ℤ)).map
        ((Φ.mapHomologicalComplex (up ℤ)).map
          (HomologicalComplex.extendMap ψ embeddingUpNat))) =
      DerivedCategory.Plus.ι.map
        ((Φ.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map
          ((HomotopyCategory.Plus.quotient A).map
            (⟨HomologicalComplex.extendMap ψ embeddingUpNat⟩ :
              resolutionCochainPlus I ⟶ resolutionCochainPlus J))) := rfl
  have key : DerivedCategory.Plus.ι.map (derivedPlusResolutionIso Φ I).hom ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (up ℤ)).map
        ((Φ.mapHomologicalComplex (up ℤ)).map
          (HomologicalComplex.extendMap ψ embeddingUpNat))) =
      DerivedCategory.Plus.ι.map
          (Φ.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map f)) ≫
        DerivedCategory.Plus.ι.map (derivedPlusResolutionIso Φ J).hom :=
    (congrArg
        (fun m => DerivedCategory.Plus.ι.map (derivedPlusResolutionIso Φ I).hom ≫ m)
        hbridge).trans
      (map_comp_eq_map_comp DerivedCategory.Plus.ι
        (derivedPlusResolutionIso_naturality Φ f I J ψ hψ))
  rw [resolutionDerivedComparison_hom, resolutionDerivedComparison_hom]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg
    (fun m => DerivedCategory.Plus.ι.map (derivedPlusResolutionIso Φ I).hom ≫ m) hq).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun m => m ≫ ((DerivedCategory.quotientCompQhIso B).app
    ((Φ.mapHomologicalComplex (up ℤ)).obj
      (HomologicalComplex.extend J.cocomplex embeddingUpNat))).hom) key).trans ?_
  exact Category.assoc _ _ _

/-- The comparison of two injective resolutions induced by a morphism of objects. -/
noncomputable def resolutionMap {A : Type*} [Category* A] [Abelian A] {M N : A} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    I.cochainComplex ⟶ J.cochainComplex :=
  HomologicalComplex.extendMap (InjectiveResolution.desc f J I) embeddingUpNat

/-- **The augmentations of two injective resolutions are compatible with `resolutionMap`.** The
descent of a morphism commutes with the augmentations on the nose, not merely up to homotopy. -/
@[sga "2 VIII 1.4" "special case"]
lemma ι'_comp_resolutionMap {A : Type*} [Category* A] [Abelian A] {M N : A} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    (HomologicalComplex.single A (up ℤ) 0).map f ≫ J.ι' = I.ι' ≫ resolutionMap f I J :=
  resolutionSingleHom_naturality I J f (InjectiveResolution.desc f J I)
    (InjectiveResolution.desc_commutes f J I).symm

/-- **`resolutionAug` is natural**: in degree zero the square of `ι'_comp_resolutionMap`
descends to the augmentations themselves. -/
lemma resolutionAug_naturality {A : Type*} [Category* A] [Abelian A] {M N : A} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
    resolutionAug I ≫ (resolutionMap f I J).f 0 = f ≫ resolutionAug J := by
  have h := HomologicalComplex.congr_hom (ι'_comp_resolutionMap f I J) 0
  simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
    Category.assoc] at h
  dsimp only [resolutionAug]
  rw [← cancel_epi (HomologicalComplex.singleObjXSelf (up ℤ) 0 M).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact h.symm

/-! ### The functorial quasi-isomorphism -/

section Comparison

variable {F G : Modules.{u} O} (f : F ⟶ G) (JF : InjectiveResolution F)
  (JG : InjectiveResolution G)

/-- The image of `cechAlphaRes` in the derived category is an isomorphism. -/
instance isIso_Q_map_cechAlphaRes {F : Modules.{u} O} (J : InjectiveResolution F) :
    IsIso (DerivedCategory.Q.map (cechAlphaRes.{u} O 𝒰 J)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ (cechAlphaRes.{u} O 𝒰 J)).2 inferInstance

/-- The image of `cechBetaRes` in the derived category is an isomorphism. -/
instance isIso_Q_map_cechBetaRes {F : Modules.{u} O} (J : InjectiveResolution F) :
    IsIso (DerivedCategory.Q.map (cechBetaRes.{u} O 𝒰 J)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ (cechBetaRes.{u} O 𝒰 J)).2 inferInstance

/-- **The comparison with the total right derived functor is natural in the resolution.** -/
lemma Q_map_comp_injectiveResolutionToRightDerived :
    DerivedCategory.Q.map
        (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).map
          (resolutionMap f JF JG)) ≫
      injectiveResolutionToRightDerived.{u} O 𝒰 G JG =
      injectiveResolutionToRightDerived.{u} O 𝒰 F JF ≫
        DerivedCategory.Plus.ι.map ((rightDerivedCechFunctor.{u} O 𝒰).map
          ((DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).map f)) :=
  (congrArg (fun m => DerivedCategory.Q.map
      (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).map
        (resolutionMap f JF JG)) ≫ m)
    (injectiveResolutionToRightDerived_eq.{u} O 𝒰 JG)).trans
    ((comp_iso_inv_eq _ _ _ _
        (resolutionDerivedComparison_naturality (cechCohomologyZeroFunctor.{u} O 𝒰) f JF JG
          (InjectiveResolution.desc f JG JF)
          (InjectiveResolution.desc_commutes f JG JF).symm)).trans
      (congrArg (fun m => m ≫ DerivedCategory.Plus.ι.map
          ((rightDerivedCechFunctor.{u} O 𝒰).map
            ((DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).map f)))
        (injectiveResolutionToRightDerived_eq.{u} O 𝒰 JF).symm))

/-- **The comparison of Stacks 01EN at a chosen injective resolution**: `Q(β) ≫ Q(α)⁻¹`
followed by the identification of the Čech `Ȟ⁰` of the resolution with the total right derived
functor. -/
noncomputable def cechComparison {F : Modules.{u} O} (J : InjectiveResolution F) :
    DerivedCategory.Q.obj ((cechComplexIntFunctor.{u} O 𝒰).obj F) ⟶
      ((rightDerivedCechFunctor.{u} O 𝒰).obj
        ((DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).obj F)).obj :=
  DerivedCategory.Q.map (cechBetaRes.{u} O 𝒰 J) ≫
    inv (DerivedCategory.Q.map (cechAlphaRes.{u} O 𝒰 J)) ≫
    injectiveResolutionToRightDerived.{u} O 𝒰 F J

/-- The comparison `cechComparison` at an injective resolution is an isomorphism. -/
instance isIso_cechComparison {F : Modules.{u} O} (J : InjectiveResolution F) :
    IsIso (cechComparison.{u} O 𝒰 J) := by
  dsimp only [cechComparison]
  infer_instance

/-- **The comparison is natural.** The two augmentations are natural in the resolution and the
comparison with the total right derived functor is too, so the composite is. -/
lemma cechComparison_naturality :
    DerivedCategory.Q.map ((cechComplexIntFunctor.{u} O 𝒰).map f) ≫
        cechComparison.{u} O 𝒰 JG =
      cechComparison.{u} O 𝒰 JF ≫ DerivedCategory.Plus.ι.map
        ((rightDerivedCechFunctor.{u} O 𝒰).map
          ((DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0).map f)) := by
  have hβ : cechBetaRes.{u} O 𝒰 JF ≫ cechTotalMap.{u} O 𝒰 (resolutionMap f JF JG) =
      (cechComplexIntFunctor.{u} O 𝒰).map f ≫ cechBetaRes.{u} O 𝒰 JG :=
    cechBeta_comp_cechTotalMap.{u} O 𝒰 JF.cochainComplex JG.cochainComplex f
      (resolutionAug JF) (resolutionAug_comp_d JF) (isIso_kernelLift_resolutionAug JF)
      (exactAt_cochainComplex JF) (resolutionAug JG) (resolutionAug_comp_d JG)
      (isIso_kernelLift_resolutionAug JG) (exactAt_cochainComplex JG)
      (resolutionMap f JF JG) (resolutionAug_naturality f JF JG)
  have hα : cechAlphaRes.{u} O 𝒰 JF ≫ cechTotalMap.{u} O 𝒰 (resolutionMap f JF JG) =
      ((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).map
        (resolutionMap f JF JG) ≫ cechAlphaRes.{u} O 𝒰 JG :=
    cechAlpha_comp_cechTotalMap.{u} O 𝒰 JF.cochainComplex JG.cochainComplex
      (fun _ => inferInstance) (fun _ => inferInstance) (resolutionMap f JF JG)
  have hQα : DerivedCategory.Q.map (cechAlphaRes.{u} O 𝒰 JF) ≫
      DerivedCategory.Q.map (cechTotalMap.{u} O 𝒰 (resolutionMap f JF JG)) =
      DerivedCategory.Q.map
          (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).map
            (resolutionMap f JF JG)) ≫
        DerivedCategory.Q.map (cechAlphaRes.{u} O 𝒰 JG) :=
    map_comp_eq_map_comp DerivedCategory.Q hα
  have hconj := comp_inv_eq_inv_comp
    (DerivedCategory.Q.map (cechAlphaRes.{u} O 𝒰 JF))
    (DerivedCategory.Q.map (cechTotalMap.{u} O 𝒰 (resolutionMap f JF JG)))
    (DerivedCategory.Q.map
      (((cechCohomologyZeroFunctor.{u} O 𝒰).mapHomologicalComplex (up ℤ)).map
        (resolutionMap f JF JG)))
    (DerivedCategory.Q.map (cechAlphaRes.{u} O 𝒰 JG)) hQα
  dsimp only [cechComparison]
  rw [← Category.assoc (DerivedCategory.Q.map ((cechComplexIntFunctor.{u} O 𝒰).map f)),
    ← Functor.map_comp, ← hβ, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hconj,
    Q_map_comp_injectiveResolutionToRightDerived.{u} O 𝒰 f JF JG]

/-- **The comparison does not depend on the chosen resolution**, being natural over the
identity. -/
lemma cechComparison_eq {F : Modules.{u} O} (J J' : InjectiveResolution F) :
    cechComparison.{u} O 𝒰 J = cechComparison.{u} O 𝒰 J' := by
  have h := cechComparison_naturality.{u} O 𝒰 (𝟙 F) J J'
  simp only [CategoryTheory.Functor.map_id] at h
  simp only [Category.id_comp] at h
  exact (Category.comp_id _).symm.trans h.symm

/-- The comparison of Stacks 01EN, read as an isomorphism in the bounded-below derived
category. -/
noncomputable def cechComparisonPlusIso (F : Modules.{u} O) (J : InjectiveResolution F) :
    (cechComplexPlusFunctor.{u} O 𝒰 ⋙ DerivedCategory.Plus.Q).obj F ≅
      (DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0 ⋙
        rightDerivedCechFunctor.{u} O 𝒰).obj F :=
  ObjectProperty.isoMk _
    (@asIso _ _ _ _ (cechComparison.{u} O 𝒰 J) (isIso_cechComparison.{u} O 𝒰 J))

/-- `cechComparisonPlusIso` is natural; the inclusion of the bounded-below derived category
into the derived category is faithful, so this is `cechComparison_naturality`. -/
lemma cechComparisonPlusIso_naturality :
    (cechComplexPlusFunctor.{u} O 𝒰 ⋙ DerivedCategory.Plus.Q).map f ≫
        (cechComparisonPlusIso.{u} O 𝒰 G JG).hom =
      (cechComparisonPlusIso.{u} O 𝒰 F JF).hom ≫
        (DerivedCategory.Plus.singleFunctor (Modules.{u} O) 0 ⋙
          rightDerivedCechFunctor.{u} O 𝒰).map f :=
  ObjectProperty.hom_ext _ (cechComparison_naturality.{u} O 𝒰 f JF JG)

end Comparison

/-- **Stacks Project, Tag 01EN, moreover assertion.** The functorial quasi-isomorphism from the
Čech complex functor to the total right-derived functor of degree-zero Čech cohomology,
together with, for every injective resolution, the two augmentations into the total Čech
complex that prescribe it.

The isomorphism is built at a resolution chosen for each presheaf; it is natural because the
two augmentations and the comparison with the total right derived functor are each natural in
the resolution, and independent of that choice because naturality over the identity says so. -/
@[stacks 01EN "the functorial quasi-isomorphism"]
noncomputable def cechComplexIsoRightDerived : CechComplexIsoRightDerived.{u} O 𝒰 :=
  ⟨NatIso.ofComponents
      (fun F => cechComparisonPlusIso.{u} O 𝒰 F (InjectiveResolution.of F))
      (fun f => cechComparisonPlusIso_naturality.{u} O 𝒰 f _ _),
    fun F J => ⟨cechResolutionComparisonOfComparison.{u} O 𝒰 J _
      (cechComparison_eq.{u} O 𝒰 (InjectiveResolution.of F) J)⟩⟩


end Stacks.Cohomology.CechTotalComparison

end
