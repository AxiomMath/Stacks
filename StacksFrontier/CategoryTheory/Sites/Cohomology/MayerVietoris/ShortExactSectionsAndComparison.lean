module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksFrontier.Algebra.Homology.MappingCoconeFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfASquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.DerivedCanonicalMapAndTriangle
import StacksCore.Tactic.StacksAttribute

/-!
# Short exact sections and the Mayer–Vietoris comparison map

Let `E ⟶ Y`, `Z ⟶ X` be a commutative square in a site carrying a sheaf of rings `R`.
Stacks 0F16 attaches to it
the canonical map `c : I(X) ⟶ C(β)[-1]` of a K-injective complex `I` of module sheaves, and
Stacks 0EVY asserts that `c` is an isomorphism as soon as the sheafified representables form
a pushout square with injective upper-left map. The source proves this by exhibiting, for an
injective module sheaf `M`, the short exact sequence of sections

`0 ⟶ M(X) ⟶ M(Z) ⊞ M(Y) ⟶ M(E) ⟶ 0`

and deducing that `c` is a quasi-isomorphism. This file formalizes the *second* half of that
argument, in two steps which are independent of the site.

## Main results

* `Stacks.Cohomology.MayerVietoris.quasiIso_shortComplexLift`: for a short exact sequence
  `S` of cochain complexes in an abelian category, the canonical map
  `S.X₁ ⟶ mappingCocone S.g` built from `S.f` and the zero null-homotopy is a
  quasi-isomorphism. This is the general homological statement behind Stacks 0EVY.
* `Stacks.Cohomology.MayerVietoris.isIso_derivedCSquare_of_sectionsShortExact`: if the
  sections short complex `sectionsShortComplex` is short exact for every injective module
  sheaf, then the canonical natural transformation of Stacks 0F16 — the `comparison` field of
  `Stacks.MayerVietoris.CanonicalMapOfComplexes.derivedCSquareData` — is an isomorphism.

## Implementation notes

`quasiIso_shortComplexLift` is proved by exhibiting the degreewise short exact sequence
`0 ⟶ S.X₁ ⟶ mappingCocone S.g ⟶ mappingCocone (𝟙 S.X₃) ⟶ 0`, whose third term is acyclic
because the mapping cocone of an isomorphism is. Degreewise this is a biproduct of the given
short exact sequence with the identity of `S.X₃` one degree down; `shortExact_of_bicones`
isolates that computation, taking the two biproduct decompositions as plain data rather than
as biproducts, because the mapping cocone is not literally a biproduct in each degree.

The reduction of Stacks 0EVY to short exactness of the sections is itself stated, in the
`General` namespace, for an arbitrary contravariant system `S : ιᵒᵖ ⥤ (A ⥤ B)` of additive
section functors and a square of objects of `ι`, matching the engine of
`StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfComplexes`; the
existence of K-injective resolutions with injective terms enters as a hypothesis, which at
the site is `exists_kInjectiveResolution_injective`. The site-theoretic statements are that
general reduction instantiated at `sectionsSystem`.

The Stacks 0F16 construction itself is not repeated here: the chain-level maps `firstMap`,
`secondMap`, `cSquare` and the derived data `DerivedCSquareData` are taken from
`StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfComplexes` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.DerivedCanonicalMapAndTriangle`,
which state them for an arbitrary site and an arbitrary sheaf of rings. Only the generic
K-injective and biproduct wrappers are taken from
`StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfASquare`.

`HomologicalComplex.eval` does not send a biproduct of complexes to the biproduct of its
values on the nose, so `evalIsoSectionsShortComplex` compares the degreewise value of the
short complex of Stacks 0F16 with `sectionsShortComplex` along `Functor.biprodComparison`.
The two spellings of the same object force two distinct instance terms for
`HasBinaryBiproduct`, which is why the two rewrites that cross them are performed at default
transparency.

The hypothesis that `sectionsShortComplex` is short exact for every injective module sheaf
is exactly the sheaf-theoretic content of Stacks 0EVY, and is *not* proved here: deriving it
from the pushout and monomorphism assumptions of that tag needs the free module sheaf on a
sheafified representable, which is what corepresents the sections functor, at independent
site, ring and module universes. That implication is
`StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.TriangleOfAPushoutSquare`.

## References

* [Stacks Project, Tag 0EVY](https://stacks.math.columbia.edu/tag/0EVY)
* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite CategoryTheory.Pretriangulated
open Stacks.MayerVietoris

namespace Stacks.Cohomology.MayerVietoris

universe u v w r v₁ u₁ w₁

section Abstract

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

/-- A short complex whose middle and right terms carry a splitting off a common object `N`,
compatibly with a given short exact sequence, is short exact. The two splittings are given as
retraction–section data rather than as binary biproducts, so that the lemma applies to the
degreewise decomposition of a mapping cocone, which is not literally a biproduct. -/
lemma shortExact_of_bicones {N P Q : A} {T : ShortComplex A} (hT : T.ShortExact)
    (π₁ : P ⟶ T.X₂) (π₂ : P ⟶ N) (j₁ : T.X₂ ⟶ P) (j₂ : N ⟶ P)
    (hj₁π₁ : j₁ ≫ π₁ = 𝟙 T.X₂) (hj₁π₂ : j₁ ≫ π₂ = 0)
    (hj₂π₁ : j₂ ≫ π₁ = 0) (hj₂π₂ : j₂ ≫ π₂ = 𝟙 N)
    (htotP : π₁ ≫ j₁ + π₂ ≫ j₂ = 𝟙 P)
    (π₁' : Q ⟶ T.X₃) (π₂' : Q ⟶ N) (j₁' : T.X₃ ⟶ Q) (j₂' : N ⟶ Q)
    (htotQ : π₁' ≫ j₁' + π₂' ≫ j₂' = 𝟙 Q)
    (c : T.X₁ ⟶ P) (hc₁ : c ≫ π₁ = T.f) (hc₂ : c ≫ π₂ = 0)
    (ψ : P ⟶ Q) (hψ₁ : ψ ≫ π₁' = π₁ ≫ T.g) (hψ₂ : ψ ≫ π₂' = π₂)
    (hcψ : c ≫ ψ = 0) :
    (ShortComplex.mk c ψ hcψ).ShortExact := by
  have hmono : Mono c := by
    have := hT.mono_f
    exact mono_of_mono_fac hc₁
  have hepig := hT.epi_g
  have hj₁ψ : j₁ ≫ ψ = T.g ≫ j₁' := by
    conv_lhs => rw [← Category.comp_id ψ, ← htotQ]
    simp only [Preadditive.comp_add, reassoc_of% hψ₁, reassoc_of% hψ₂,
      reassoc_of% hj₁π₁, reassoc_of% hj₁π₂, zero_comp, add_zero]
  have hj₂ψ : j₂ ≫ ψ = j₂' := by
    conv_lhs => rw [← Category.comp_id ψ, ← htotQ]
    simp only [Preadditive.comp_add, reassoc_of% hψ₁, reassoc_of% hψ₂,
      reassoc_of% hj₂π₁, reassoc_of% hj₂π₂, zero_comp, zero_add]
  have hepi : Epi ψ := by
    rw [Preadditive.epi_iff_cancel_zero]
    intro T' g hg
    have h1 : T.g ≫ j₁' ≫ g = 0 := by rw [← reassoc_of% hj₁ψ, hg, comp_zero]
    have h2 : j₂' ≫ g = 0 := by rw [← hj₂ψ, Category.assoc, hg, comp_zero]
    have h1' : j₁' ≫ g = 0 := by rwa [← cancel_epi T.g, comp_zero]
    conv_lhs => rw [← Category.id_comp g, ← htotQ]
    simp only [Preadditive.add_comp, Category.assoc, h1', h2, comp_zero, add_zero]
  have hcok : IsColimit (CokernelCofork.ofπ ψ hcψ) := by
    refine CokernelCofork.IsColimit.ofπ' _ _ (fun {A'} h hh => ?_)
    have hα : T.f ≫ (j₁ ≫ h) = 0 := by
      have hid : c ≫ h = c ≫ (π₁ ≫ j₁ + π₂ ≫ j₂) ≫ h := by rw [htotP, Category.id_comp]
      rw [hh] at hid
      simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
        reassoc_of% hc₁, reassoc_of% hc₂, zero_comp, add_zero] at hid
      exact hid.symm
    obtain ⟨t, ht⟩ := CokernelCofork.IsColimit.desc' hT.gIsCokernel (j₁ ≫ h) hα
    simp only [CokernelCofork.π_ofπ] at ht
    refine ⟨π₁' ≫ t + π₂' ≫ (j₂ ≫ h), ?_⟩
    simp only [Preadditive.comp_add, reassoc_of% hψ₁, reassoc_of% hψ₂]
    rw [ht]
    conv_rhs => rw [← Category.id_comp h, ← htotP]
    simp only [Preadditive.add_comp, Category.assoc]
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.mk c ψ hcψ).exact_of_g_is_cokernel hcok) hmono hepi

end Abstract

section Chain

open CochainComplex HomComplex

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  (T : ShortComplex (CochainComplex A ℤ))

/-- Every degree of a cochain complex indexed by `ℤ` has a predecessor; this is the
hypothesis under which a morphism of arrows induces a morphism of mapping cocones. -/
theorem upRelExists : ∀ j : ℤ, ∃ i, (ComplexShape.up ℤ).Rel i j := fun j => ⟨j - 1, by simp⟩

/-- The morphism of arrows from `S.g` to the identity of `S.X₃`, with components `S.g` and
the identity. -/
def toIdentityArrow : Arrow.mk T.g ⟶ Arrow.mk (𝟙 T.X₃) := Arrow.homMk' T.g (𝟙 _) (by simp)

/-- The left component of `toIdentityArrow` is `S.g`. -/
@[simp]
lemma toIdentityArrow_left : (toIdentityArrow T).left = T.g := rfl

/-- The right component of `toIdentityArrow` is the identity. -/
@[simp]
lemma toIdentityArrow_right : (toIdentityArrow T).right = 𝟙 T.X₃ := rfl

/-- The canonical map `S.X₁ ⟶ C(S.g)[-1]`, built from `S.f` and the zero null-homotopy. For
the sections of a square on a ringed site this is the map `c` of Stacks 0F16. -/
def shortComplexLift : T.X₁ ⟶ mappingCocone T.g :=
  mappingCocone.lift T.g T.f 0 (by simp [T.zero])

/-- The map `C(S.g)[-1] ⟶ C(𝟙)[-1]` induced by `toIdentityArrow`. Degreewise it is `S.g` on
the first summand and the identity on the second, so its kernel is that of `S.g`. -/
def shortComplexQuotient : mappingCocone T.g ⟶ mappingCocone (𝟙 T.X₃) :=
  mappingCocone.mapArrow T.g (𝟙 T.X₃) upRelExists (toIdentityArrow T)

/-- Degreewise, `shortComplexQuotient` acts as `S.g` on the first summand of the mapping
cocone. -/
lemma shortComplexQuotient_fst (p : ℤ) :
    (shortComplexQuotient T).f p ≫ (mappingCocone.fst (𝟙 T.X₃)).f p =
      (mappingCocone.fst T.g).f p ≫ T.g.f p := by
  simpa [shortComplexQuotient] using congrArg (fun z : mappingCocone T.g ⟶ T.X₃ => z.f p)
    (mappingCocone.mapArrow_fst T.g (𝟙 T.X₃) upRelExists (toIdentityArrow T))

/-- Degreewise, `shortComplexQuotient` acts as the identity on the second summand of the
mapping cocone. -/
lemma shortComplexQuotient_snd (p : ℤ) :
    (shortComplexQuotient T).f p ≫ (mappingCocone.snd (𝟙 T.X₃)).v p (p + -1) (by lia) =
      (mappingCocone.snd T.g).v p (p + -1) (by lia) := by
  simpa [shortComplexQuotient] using
    mappingCocone.mapArrow_snd_v T.g (𝟙 T.X₃) upRelExists (toIdentityArrow T) p

/-- The first component of `shortComplexLift` is `S.f`. -/
@[simp]
lemma shortComplexLift_fst (p : ℤ) :
    (shortComplexLift T).f p ≫ (mappingCocone.fst T.g).f p = T.f.f p :=
  mappingCocone.lift_f_fst_f _ _ _ _ p

/-- The second component of `shortComplexLift` vanishes: the chosen null-homotopy is zero. -/
@[simp]
lemma shortComplexLift_snd (p : ℤ) :
    (shortComplexLift T).f p ≫ (mappingCocone.snd T.g).v p (p + -1) (by lia) = 0 := by
  rw [shortComplexLift, mappingCocone.lift_f_snd_v]
  simp

/-- The canonical map into the mapping cocone is killed by the projection to the mapping
cocone of the identity. -/
lemma shortComplexLift_comp_shortComplexQuotient :
    shortComplexLift T ≫ shortComplexQuotient T = 0 := by
  ext p
  have hid := mappingCocone.id_X (𝟙 T.X₃) p (p + -1) (by lia)
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    ← Category.comp_id ((shortComplexLift T).f p ≫ (shortComplexQuotient T).f p), ← hid]
  simp only [Preadditive.comp_add, Category.assoc,
    reassoc_of% (shortComplexQuotient_fst T p), reassoc_of% (shortComplexQuotient_snd T p),
    reassoc_of% (shortComplexLift_fst T p), reassoc_of% (shortComplexLift_snd T p),
    zero_comp, add_zero]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, T.zero]
  simp

/-- For a short exact sequence `S` of cochain complexes, `S.X₁` is the kernel and
`C(𝟙)[-1]` the cokernel of `C(S.g)[-1]`. -/
lemma shortExact_shortComplexLift (hT : T.ShortExact) :
    (ShortComplex.mk (shortComplexLift T) (shortComplexQuotient T)
      (shortComplexLift_comp_shortComplexQuotient T)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p =>
    shortExact_of_bicones ((HomologicalComplex.shortExact_iff_degreewise_shortExact T).1 hT p)
      ((mappingCocone.fst T.g).f p) ((mappingCocone.snd T.g).v p (p + -1) (by lia))
      ((mappingCocone.inl T.g).v p p (add_zero p))
      ((mappingCocone.inr T.g).1.v (p + -1) p (by lia))
      (mappingCocone.inl_v_fst_f T.g p) (mappingCocone.inl_v_snd_v T.g p (p + -1) (by lia))
      (mappingCocone.inr_v_fst_f T.g (p + -1) p (by lia))
      (mappingCocone.inr_v_snd_v T.g (p + -1) p (by lia))
      (mappingCocone.id_X T.g p (p + -1) (by lia))
      ((mappingCocone.fst (𝟙 T.X₃)).f p) ((mappingCocone.snd (𝟙 T.X₃)).v p (p + -1) (by lia))
      ((mappingCocone.inl (𝟙 T.X₃)).v p p (add_zero p))
      ((mappingCocone.inr (𝟙 T.X₃)).1.v (p + -1) p (by lia))
      (mappingCocone.id_X (𝟙 T.X₃) p (p + -1) (by lia))
      ((shortComplexLift T).f p) (shortComplexLift_fst T p) (shortComplexLift_snd T p)
      ((shortComplexQuotient T).f p) (shortComplexQuotient_fst T p)
      (shortComplexQuotient_snd T p) _

variable [HasDerivedCategory.{w₁} A]

/-- The mapping cocone of an identity is zero in the derived category. -/
lemma isZero_Q_mappingCocone_id (X : CochainComplex A ℤ) :
    IsZero (DerivedCategory.Q.obj (mappingCocone (𝟙 X))) := by
  refine Triangle.isZero₁_of_isIso₂ _
    (DerivedCategory.mappingCocone_triangle_distinguished (𝟙 X)) ?_
  change IsIso (DerivedCategory.Q.map (𝟙 X))
  rw [CategoryTheory.Functor.map_id]
  infer_instance

/-- **The homological heart of Stacks 0EVY.** For a short exact sequence `S` of cochain
complexes, the canonical map `S.X₁ ⟶ C(S.g)[-1]` is a quasi-isomorphism. -/
theorem quasiIso_shortComplexLift (hT : T.ShortExact) : QuasiIso (shortComplexLift T) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (Triangle.isZero₃_iff_isIso₁ _
    (DerivedCategory.triangleOfSES_distinguished (shortExact_shortComplexLift T hT))).1
    (isZero_Q_mappingCocone_id T.X₃)

end Chain

namespace General

open Stacks.MayerVietoris.CanonicalMapOfComplexes

section Chain

variable {ι : Type*} [Category* ι]
  {A : Type*} [Category* A] [Preadditive A]
  {B : Type*} [Category* B] [Abelian B]
  (S : ιᵒᵖ ⥤ (A ⥤ B)) [∀ X : ιᵒᵖ, (S.obj X).Additive] (sq : Square ι)

/-- The sections short complex of a square at an object `M`: `M(X) ⟶ M(Z) ⊞ M(Y) ⟶ M(E)`,
with the minus sign on the restriction from `Y` to `E`, as in Stacks 0F16. -/
def sectionsShortComplex (M : A) : ShortComplex B :=
  ShortComplex.mk
    (biprod.lift ((S.map sq.f₃₄.op).app M) ((S.map sq.f₂₄.op).app M))
    (biprod.desc ((S.map sq.f₁₃.op).app M) (-((S.map sq.f₁₂.op).app M))) (by
      have h : S.map sq.f₃₄.op ≫ S.map sq.f₁₃.op = S.map sq.f₂₄.op ≫ S.map sq.f₁₂.op := by
        rw [← S.map_comp, ← S.map_comp]
        exact congrArg (fun g => S.map g.op) sq.fac.symm
      rw [biprod.lift_desc, Preadditive.comp_neg, add_neg_eq_zero]
      exact congrArg (fun α : S.obj (op sq.X₄) ⟶ S.obj (op sq.X₁) => α.app M) h)

/-- The first component of `firstMap`, in degree `p`. -/
lemma firstMap_f_evalFst (I : CochainComplex A ℤ) (p : ℤ) :
    (General.firstMap S sq I).f p ≫
        (HomologicalComplex.eval B (ComplexShape.up ℤ) p).map
          (biprod.fst : (General.complexFunctor S sq.X₃).obj I ⊞
            (General.complexFunctor S sq.X₂).obj I ⟶ _) =
      (S.map sq.f₃₄.op).app (I.X p) :=
  congrArg (fun z : (General.complexFunctor S sq.X₄).obj I ⟶
      (General.complexFunctor S sq.X₃).obj I => z.f p) (biprod.lift_fst _ _)

/-- The second component of `firstMap`, in degree `p`. -/
lemma firstMap_f_evalSnd (I : CochainComplex A ℤ) (p : ℤ) :
    (General.firstMap S sq I).f p ≫
        (HomologicalComplex.eval B (ComplexShape.up ℤ) p).map
          (biprod.snd : (General.complexFunctor S sq.X₃).obj I ⊞
            (General.complexFunctor S sq.X₂).obj I ⟶ _) =
      (S.map sq.f₂₄.op).app (I.X p) :=
  congrArg (fun z : (General.complexFunctor S sq.X₄).obj I ⟶
      (General.complexFunctor S sq.X₂).obj I => z.f p) (biprod.lift_snd _ _)

/-- The first component of `secondMap`, in degree `p`. -/
lemma evalInl_secondMap_f (I : CochainComplex A ℤ) (p : ℤ) :
    (HomologicalComplex.eval B (ComplexShape.up ℤ) p).map
        (biprod.inl : (General.complexFunctor S sq.X₃).obj I ⟶
          (General.complexFunctor S sq.X₃).obj I ⊞
            (General.complexFunctor S sq.X₂).obj I) ≫
        (General.secondMap S sq I).f p =
      (S.map sq.f₁₃.op).app (I.X p) :=
  congrArg (fun z : (General.complexFunctor S sq.X₃).obj I ⟶
      (General.complexFunctor S sq.X₁).obj I => z.f p) (biprod.inl_desc _ _)

/-- The second component of `secondMap`, in degree `p`; it carries the sign. -/
lemma evalInr_secondMap_f (I : CochainComplex A ℤ) (p : ℤ) :
    (HomologicalComplex.eval B (ComplexShape.up ℤ) p).map
        (biprod.inr : (General.complexFunctor S sq.X₂).obj I ⟶
          (General.complexFunctor S sq.X₃).obj I ⊞
            (General.complexFunctor S sq.X₂).obj I) ≫
        (General.secondMap S sq I).f p =
      -((S.map sq.f₁₂.op).app (I.X p)) :=
  congrArg (fun z : (General.complexFunctor S sq.X₂).obj I ⟶
      (General.complexFunctor S sq.X₁).obj I => z.f p) (biprod.inr_desc _ _)

/-- In each degree, the short complex of Stacks 0F16 at a complex `I` is the sections short
complex at the term `I.X p`. The comparison is the identity on the outer terms and
`Functor.biprodComparison` in the middle, because evaluation in degree `p` does not send a
biproduct of complexes to the biproduct of its values on the nose. -/
def evalIsoSectionsShortComplex (I : CochainComplex A ℤ) (p : ℤ) :
    (ShortComplex.mk (General.firstMap S sq I) (General.secondMap S sq I)
        (General.firstMap_comp_secondMap S sq I)).map
      (HomologicalComplex.eval B (ComplexShape.up ℤ) p) ≅
      sectionsShortComplex S sq (I.X p) := by
  have hb := isIso_biprodComparison
    (HomologicalComplex.eval B (ComplexShape.up ℤ) p)
    ((General.complexFunctor S sq.X₃).obj I) ((General.complexFunctor S sq.X₂).obj I)
  have h2 := Functor.biprodComparison'_comp_biprodComparison
    (HomologicalComplex.eval B (ComplexShape.up ℤ) p)
    ((General.complexFunctor S sq.X₃).obj I) ((General.complexFunctor S sq.X₂).obj I)
  have hbi : (HomologicalComplex.eval B (ComplexShape.up ℤ) p).biprodComparison
        ((General.complexFunctor S sq.X₃).obj I)
        ((General.complexFunctor S sq.X₂).obj I) ≫
      Functor.biprodComparison' _ _ _ = 𝟙 _ := by
    rw [← cancel_mono ((HomologicalComplex.eval B (ComplexShape.up ℤ)
      p).biprodComparison ((General.complexFunctor S sq.X₃).obj I)
      ((General.complexFunctor S sq.X₂).obj I)),
      Category.assoc, h2, Category.comp_id, Category.id_comp]
  refine ShortComplex.isoMk (Iso.refl _) (@asIso _ _ _ _ _ hb) (Iso.refl _) ?_ ?_
  · dsimp [sectionsShortComplex]
    rw [Category.id_comp]
    apply biprod.hom_ext
    · rw [biprod.lift_fst, Category.assoc, Functor.biprodComparison]
      rw (transparency := .default) [biprod.lift_fst]
      exact (firstMap_f_evalFst S sq I p).symm
    · rw [biprod.lift_snd, Category.assoc, Functor.biprodComparison]
      rw (transparency := .default) [biprod.lift_snd]
      exact (firstMap_f_evalSnd S sq I p).symm
  · dsimp [sectionsShortComplex]
    rw [Category.comp_id]
    have hbi' : IsIso (Functor.biprodComparison'
        (HomologicalComplex.eval B (ComplexShape.up ℤ) p)
        ((General.complexFunctor S sq.X₃).obj I)
        ((General.complexFunctor S sq.X₂).obj I)) := ⟨_, h2, hbi⟩
    rw [← cancel_epi (Functor.biprodComparison'
      (HomologicalComplex.eval B (ComplexShape.up ℤ) p)
      ((General.complexFunctor S sq.X₃).obj I)
      ((General.complexFunctor S sq.X₂).obj I)),
      ← Category.assoc, h2, Category.id_comp]
    apply biprod.hom_ext'
    · rw (transparency := .default) [biprod.inl_desc]
      rw [← Category.assoc, Functor.biprodComparison', biprod.inl_desc]
      exact (evalInl_secondMap_f S sq I p).symm
    · rw (transparency := .default) [biprod.inr_desc]
      rw [← Category.assoc, Functor.biprodComparison', biprod.inr_desc]
      exact (evalInr_secondMap_f S sq I p).symm

/-- If the sections short complex is short exact at every term of `I`, then the chain-level
short complex of Stacks 0F16 is short exact. -/
lemma shortExact_firstMap_secondMap (I : CochainComplex A ℤ)
    (h : ∀ p : ℤ, (sectionsShortComplex S sq (I.X p)).ShortExact) :
    (ShortComplex.mk (General.firstMap S sq I) (General.secondMap S sq I)
      (General.firstMap_comp_secondMap S sq I)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun p =>
    ShortComplex.shortExact_of_iso (evalIsoSectionsShortComplex S sq I p).symm (h p)

variable [HasDerivedCategory B]

/-- The canonical chain-level map of Stacks 0F16 is a quasi-isomorphism as soon as the
sections short complex is short exact at every term of `I`. -/
theorem quasiIso_cSquare_of_sectionsShortExact (I : CochainComplex A ℤ)
    (h : ∀ p : ℤ, (sectionsShortComplex S sq (I.X p)).ShortExact) :
    QuasiIso (General.cSquare S sq I) :=
  quasiIso_shortComplexLift (ShortComplex.mk (General.firstMap S sq I)
    (General.secondMap S sq I) (General.firstMap_comp_secondMap S sq I))
    (shortExact_firstMap_secondMap S sq I h)

end Chain

section Derived

variable {ι : Type*} [Category* ι]
  {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (S : ιᵒᵖ ⥤ (A ⥤ B)) [∀ X : ιᵒᵖ, (S.obj X).Additive] (sq : Square ι)

/-- **The reduction of Stacks 0EVY to its sheaf-theoretic input.** If the sections short
complex is short exact at every injective object, and every complex admits a K-injective
resolution with injective terms, then the canonical natural transformation of the derived
data is an isomorphism. -/
theorem isIso_derivedCSquare_of_sectionsShortExact
    (D : General.DerivedCSquareData S sq)
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f ∧ ∀ p : ℤ, Injective (I.X p))
    (h : ∀ M : A, Injective M → (sectionsShortComplex S sq M).ShortExact) :
    IsIso D.derivedCSquare := by
  have hall : ∀ K : DerivedCategory A, IsIso (D.derivedCSquare.app K) := by
    intro K
    obtain ⟨I, f, hI, hf, hinj⟩ := hres (DerivedCategory.Q.objPreimage K)
    have hq : IsIso (DerivedCategory.Q.map f) := by
      rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact (D.isCSquareIso_iff_quasiIso K I
        ((@asIso _ _ _ _ _ hq).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K)).2
      (quasiIso_cSquare_of_sectionsShortExact S sq I (fun p => h (I.X p) (hinj p)))
  exact NatIso.isIso_of_isIso_app _

end Derived

end General

section Site

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{r}}

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of sections composes contravariantly, at a fixed sheaf of modules. -/
lemma sectionsRestriction_comp_app {U V W : C} (f : U ⟶ V) (g : V ⟶ W)
    (M : SheafOfModules.{v} R) :
    (CanonicalMapOfComplexes.sectionsRestriction R g).app M ≫
        (CanonicalMapOfComplexes.sectionsRestriction R f).app M =
      (CanonicalMapOfComplexes.sectionsRestriction R (f ≫ g)).app M :=
  (congrArg
    (fun α : CanonicalMapOfComplexes.sections.{u, v} R W ⟶
      CanonicalMapOfComplexes.sections.{u, v} R U => α.app M)
    (CanonicalMapOfComplexes.sectionsRestriction_comp R f g)).symm

/-- The sections short complex of a square at a sheaf of modules `M`:
`M(X) ⟶ M(Z) ⊞ M(Y) ⟶ M(E)`, with the minus sign on the restriction from `Y` to `E`, as in
Stacks 0F16. Stacks 0EVY asserts that it is short exact when `M` is injective and the
sheafified representables of the square form a pushout with monic upper-left map. -/
def sectionsShortComplex (sq : Square C) (M : SheafOfModules.{v} R) :
    ShortComplex AddCommGrpCat.{v} :=
  General.sectionsShortComplex (CanonicalMapOfComplexes.sectionsSystem R) sq M

/-- The first component of `firstMap`, in degree `p`. -/
lemma firstMap_f_evalFst (sq : Square C)
    (I : CochainComplex (SheafOfModules.{v} R) ℤ) (p : ℤ) :
    (CanonicalMapOfComplexes.firstMap sq I).f p ≫
        (HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℤ) p).map
          (biprod.fst : (CanonicalMapOfComplexes.sectionsComplex R sq.X₃).obj I ⊞
            (CanonicalMapOfComplexes.sectionsComplex R sq.X₂).obj I ⟶ _) =
      (CanonicalMapOfComplexes.sectionsRestriction R sq.f₃₄).app (I.X p) :=
  General.firstMap_f_evalFst (CanonicalMapOfComplexes.sectionsSystem R) sq I p

/-- The second component of `firstMap`, in degree `p`. -/
lemma firstMap_f_evalSnd (sq : Square C)
    (I : CochainComplex (SheafOfModules.{v} R) ℤ) (p : ℤ) :
    (CanonicalMapOfComplexes.firstMap sq I).f p ≫
        (HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℤ) p).map
          (biprod.snd : (CanonicalMapOfComplexes.sectionsComplex R sq.X₃).obj I ⊞
            (CanonicalMapOfComplexes.sectionsComplex R sq.X₂).obj I ⟶ _) =
      (CanonicalMapOfComplexes.sectionsRestriction R sq.f₂₄).app (I.X p) :=
  General.firstMap_f_evalSnd (CanonicalMapOfComplexes.sectionsSystem R) sq I p

/-- The first component of `secondMap`, in degree `p`. -/
lemma evalInl_secondMap_f (sq : Square C)
    (I : CochainComplex (SheafOfModules.{v} R) ℤ) (p : ℤ) :
    (HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℤ) p).map
        (biprod.inl : (CanonicalMapOfComplexes.sectionsComplex R sq.X₃).obj I ⟶
          (CanonicalMapOfComplexes.sectionsComplex R sq.X₃).obj I ⊞
            (CanonicalMapOfComplexes.sectionsComplex R sq.X₂).obj I) ≫
        (CanonicalMapOfComplexes.secondMap sq I).f p =
      (CanonicalMapOfComplexes.sectionsRestriction R sq.f₁₃).app (I.X p) :=
  General.evalInl_secondMap_f (CanonicalMapOfComplexes.sectionsSystem R) sq I p

/-- The second component of `secondMap`, in degree `p`; it carries the sign. -/
lemma evalInr_secondMap_f (sq : Square C)
    (I : CochainComplex (SheafOfModules.{v} R) ℤ) (p : ℤ) :
    (HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℤ) p).map
        (biprod.inr : (CanonicalMapOfComplexes.sectionsComplex R sq.X₂).obj I ⟶
          (CanonicalMapOfComplexes.sectionsComplex R sq.X₃).obj I ⊞
            (CanonicalMapOfComplexes.sectionsComplex R sq.X₂).obj I) ≫
        (CanonicalMapOfComplexes.secondMap sq I).f p =
      -((CanonicalMapOfComplexes.sectionsRestriction R sq.f₁₂).app (I.X p)) :=
  General.evalInr_secondMap_f (CanonicalMapOfComplexes.sectionsSystem R) sq I p

/-- In each degree, the short complex of Stacks 0F16 at a complex `I` is the sections short
complex at the term `I.X p`. The comparison is the identity on the outer terms and
`Functor.biprodComparison` in the middle, because evaluation in degree `p` does not send a
biproduct of complexes to the biproduct of its values on the nose. -/
def evalIsoSectionsShortComplex (sq : Square C)
    (I : CochainComplex (SheafOfModules.{v} R) ℤ) (p : ℤ) :
    (ShortComplex.mk (CanonicalMapOfComplexes.firstMap sq I)
        (CanonicalMapOfComplexes.secondMap sq I)
        (CanonicalMapOfComplexes.firstMap_comp_secondMap sq I)).map
      (HomologicalComplex.eval AddCommGrpCat.{v} (ComplexShape.up ℤ) p) ≅
      sectionsShortComplex sq (I.X p) :=
  General.evalIsoSectionsShortComplex (CanonicalMapOfComplexes.sectionsSystem R) sq I p

section Reduction

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]

/-- Every complex of sheaves of modules on a site carrying a sheaf of rings admits a
K-injective resolution whose terms are injective objects: this is the resolution of
Stacks 079P. -/
theorem exists_kInjectiveResolution_injective
    (K : CochainComplex (SheafOfModules.{v} R) ℤ) :
    ∃ (I : CochainComplex (SheafOfModules.{v} R) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f ∧ ∀ p : ℤ, Injective (I.X p) :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{v} R)).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{v} R)).app K,
    inferInstance, inferInstance, fun _ => inferInstance⟩

omit [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}] in
/-- If the sections short complex is short exact at every term of `I`, then the chain-level
short complex of Stacks 0F16 is short exact. -/
lemma shortExact_firstMap_secondMap (sq : Square C)
    (I : CochainComplex (SheafOfModules.{v} R) ℤ)
    (h : ∀ p : ℤ, (sectionsShortComplex sq (I.X p)).ShortExact) :
    (ShortComplex.mk (CanonicalMapOfComplexes.firstMap sq I)
      (CanonicalMapOfComplexes.secondMap sq I)
      (CanonicalMapOfComplexes.firstMap_comp_secondMap sq I)).ShortExact :=
  General.shortExact_firstMap_secondMap (CanonicalMapOfComplexes.sectionsSystem R) sq I h

omit [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}] in
/-- The canonical chain-level map of Stacks 0F16 is a quasi-isomorphism as soon as the
sections short complex is short exact at every term of `I`. -/
theorem quasiIso_cSquare_of_sectionsShortExact (sq : Square C)
    (I : CochainComplex (SheafOfModules.{v} R) ℤ)
    (h : ∀ p : ℤ, (sectionsShortComplex sq (I.X p)).ShortExact) :
    QuasiIso (CanonicalMapOfComplexes.cSquare sq I) :=
  General.quasiIso_cSquare_of_sectionsShortExact
    (CanonicalMapOfComplexes.sectionsSystem R) sq I h

/-- **The reduction of Stacks 0EVY to its sheaf-theoretic input.** If the sections short
complex `M(X) ⟶ M(Z) ⊞ M(Y) ⟶ M(E)` is short exact for every injective sheaf of modules `M`,
then the canonical natural transformation of Stacks 0F16 is an isomorphism, so that the
Mayer-Vietoris triangle `cSquareTriangle` is distinguished for every object of the derived
category.

Under the hypotheses of Stacks 0EVY - the sheafified representables of the square form a
pushout square and `h_E^# ⟶ h_Y^#` is a monomorphism - the hypothesis below is what the
source establishes; that implication is not proved here. -/
theorem isIso_derivedCSquare_of_sectionsShortExact (sq : Square C)
    (h : ∀ M : SheafOfModules.{v} R, Injective M →
      (sectionsShortComplex sq M).ShortExact) :
    IsIso (CanonicalMapOfComplexes.derivedCSquareData.{u, v} (R := R) sq).derivedCSquare :=
  General.isIso_derivedCSquare_of_sectionsShortExact
    (CanonicalMapOfComplexes.sectionsSystem R) sq
    (CanonicalMapOfComplexes.derivedCSquareData.{u, v} (R := R) sq)
    (fun K => exists_kInjectiveResolution_injective.{u, v, w, r} (R := R) K) h

end Reduction

end Site

end Stacks.Cohomology.MayerVietoris
