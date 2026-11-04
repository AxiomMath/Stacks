module

public import Mathlib.Algebra.Homology.Refinements
public import StacksFrontier.CategoryTheory.Sites.CechComplexExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.AcyclicCoveringFamily
import StacksCore.Tactic.StacksAttribute

/-!
# The degree-one Čech-to-cohomology comparison of a covering family is injective

Let `(C, K)` be a site, let `𝒰 = {U_i → U}` be a covering family of an object `U` and let `G`
be an abelian sheaf on `C`. This file proves that the degree-one comparison
`Stacks.CechSite.cechCohomologyToCohomology` of Stacks 03AX, from the first Čech cohomology of
the family to the first cohomology of `G` over `U`, is a monomorphism.

The proof is the classical one. Fix an injective resolution `G ⟶ J^•`. Stacks 03AX computes
the comparison through the Čech bicomplex of the resolution, as the map `β` induced by
`G ⟶ J^0` followed by the inverse of the quasi-isomorphic augmentation `α`
(`Stacks.CechSite.CechResolutionComparison`). Since `α` becomes invertible, the comparison is a
monomorphism as soon as `H¹(β)` is one, and that is forced by the beginning `G ⟶ J^0 ⟶ J^1` of
the resolution: evaluating the Čech complex in a fixed degree is a left exact functor of the
sheaf, so it carries the kernel presentation of `G` to a kernel presentation again, and a map
into a first-quadrant total complex which factors through the zeroth column that way is
injective on first homology.

## Main results

* `Stacks.CechSite.preservesFiniteLimits_cechIntEval`: evaluating the integer-graded Čech
  complex of a covering family in a fixed degree is left exact in the abelian sheaf.
* `Stacks.CechSite.mono_homologyMap_total_of_kernel`: the abstract form of the argument — first
  homology of a map into a first-quadrant total complex is injective as soon as the map factors
  through the zeroth column and that column begins with a kernel.
* `Stacks.CechSite.injective_cechCohomologyToCohomology_one` and
  `Stacks.CechSite.mono_cechCohomologyToCohomology_one`: **Stacks 0A6G**, the degree-one
  comparison of Stacks 03AX is a monomorphism. This is the injectivity assertion of the source;
  it is joined to the source's other assertion, the identification of `Ȟ¹(𝒰, G)` with the
  locally trivial torsor classes, in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.CechClassCohomologyComparison`, where the
  Čech cohomology group used here is identified with the explicit quotient of Čech `1`-cocycles
  by Čech `1`-coboundaries that the identification lands in.

## Implementation notes

The total complex is read off through `Stacks.CechSite.totalProjection`, the retraction of the
inclusion of one bidegree which kills every other summand of the same total degree; in total
degree zero a first-quadrant double complex has only one summand, so there the projection is
inverse to the inclusion, which is what identifies a cycle of the total complex in degree zero
with an element of the zeroth column.

A composite of monomorphisms of abelian groups is formed through injectivity rather than by the
generic instance, because the groups met here are homology groups with two spellings — as a
value of the homology functor and as the homology of a complex — which are definitionally but
not reducibly equal.

The total-complex lemmas of the first two sections also exist, privately, inside
`StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.DegreeOneIsomorphism`, which runs the
same argument for an open covering of a topological space. They are stated here at the
generality they are proved at, so that file's copies can be retired onto these; that has not
been done, because the names it exports from them are used by two further files of its own
chain.

## References

* [Stacks Project, Tag 0A6G](https://stacks.math.columbia.edu/tag/0A6G)
* [Stacks Project, Tag 03AX](https://stacks.math.columbia.edu/tag/03AX)
* [Stacks Project, Tag 09V1](https://stacks.math.columbia.edu/tag/09V1), the same argument for
  an open covering of a topological space.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe a s t w v u

namespace Stacks.CechSite

/-! ### Reading off a column of a total complex -/

section Total

variable {A : Type s} [Category.{t} A] [Preadditive A]
  (L : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [L.HasTotal (ComplexShape.up ℤ)]

/-- The projection of the total complex of a double complex onto one of its constituent
objects, zero on every other summand of the given total degree. -/
def totalProjection (p q n : ℤ) : (L.total (ComplexShape.up ℤ)).X n ⟶ (L.X p).X q :=
  L.totalDesc (fun i j _ ↦ if hi : i = p then if hj : j = q then
    eqToHom (by subst i j; rfl) else 0 else 0)

/-- The projection is a retraction of the inclusion of the summand it names. -/
lemma ι_totalProjection (p q n : ℤ) (h : p + q = n) :
    L.ιTotal (ComplexShape.up ℤ) p q n h ≫ totalProjection L p q n = 𝟙 _ := by
  simp [totalProjection]

/-- The projection kills every summand other than the one it names. -/
lemma ι_totalProjection_of_ne (p q i j n : ℤ) (h : i + j = n) (hne : i ≠ p ∨ j ≠ q) :
    L.ιTotal (ComplexShape.up ℤ) i j n h ≫ totalProjection L p q n = 0 := by
  rcases hne with hne | hne <;> simp [totalProjection, hne]

/-- In total degree zero a first-quadrant double complex has a single summand, so the
projection onto it is inverse to its inclusion. -/
lemma total_zero_decomposition (hz : ∀ i j, i < 0 ∨ j < 0 → IsZero ((L.X i).X j)) :
    totalProjection L 0 0 0 ≫ L.ιTotal (ComplexShape.up ℤ) 0 0 0 (by simp) = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  change i + j = 0 at hij
  by_cases hi : i = 0
  · subst i
    obtain rfl : j = 0 := by omega
    simp [← Category.assoc, ι_totalProjection]
  · exact (hz i j (by omega)).eq_of_src _ _

/-- The differential of a total complex, read on the summand in bidegree `(0, q)`. -/
lemma total_zero_row_d (q : ℤ) :
    L.ιTotal (ComplexShape.up ℤ) 0 q q (by simp) ≫ (L.total (ComplexShape.up ℤ)).d q (q + 1) =
      (L.d 0 1).f q ≫ L.ιTotal (ComplexShape.up ℤ) 1 q (q + 1) (by simp; omega) +
      (L.X 0).d q (q + 1) ≫ L.ιTotal (ComplexShape.up ℤ) 0 (q + 1) (q + 1) (by simp) := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
    L.d₁_eq (ComplexShape.up ℤ) (by simp : (ComplexShape.up ℤ).Rel 0 1) q (q + 1)
      (by simp; omega),
    L.d₂_eq (ComplexShape.up ℤ) 0 (by simp : (ComplexShape.up ℤ).Rel q (q + 1)) (q + 1)
      (by simp)]
  simp [ComplexShape.ε₁, ComplexShape.ε₂]

/-- The differential of a total complex out of total degree zero. -/
lemma total_zero_d :
    L.ιTotal (ComplexShape.up ℤ) 0 0 0 (by simp) ≫ (L.total (ComplexShape.up ℤ)).d 0 1 =
      (L.d 0 1).f 0 ≫ L.ιTotal (ComplexShape.up ℤ) 1 0 1 (by simp) +
      (L.X 0).d 0 1 ≫ L.ιTotal (ComplexShape.up ℤ) 0 1 1 (by simp) := by
  simpa using total_zero_row_d L 0

end Total

section TotalAbelian

variable {A : Type s} [Category.{t} A] [Abelian A]
  (L : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [L.HasTotal (ComplexShape.up ℤ)]

/-- **First homology of a map into a total complex is a monomorphism** as soon as the map
factors through the zeroth column and that column begins with a kernel. This is the abstract
form of the injectivity assertion of Stacks 0A6G. -/
lemma mono_homologyMap_total_of_kernel
    (hz : ∀ i j, i < 0 ∨ j < 0 → IsZero ((L.X i).X j))
    {B : CochainComplex A ℤ} (f : B ⟶ L.X 0) (hf : f ≫ L.d 0 1 = 0)
    (hker : IsLimit (KernelFork.ofι (f.f 0)
      (show f.f 0 ≫ (L.d 0 1).f 0 = 0 from congrArg (fun g ↦ g.f 0) hf)))
    [Mono (f.f 1)] (β : B ⟶ L.total (ComplexShape.up ℤ))
    (hβ : ∀ p, β.f p = f.f p ≫ L.ιTotal (ComplexShape.up ℤ) 0 p p (by simp)) :
    Mono (HomologicalComplex.homologyMap β 1) := by
  rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements β 0 1 2 (by simp) (by simp)]
  intro T x hx y hxy
  let b := y ≫ totalProjection L 0 0 0
  have hy : y = b ≫ L.ιTotal (ComplexShape.up ℤ) 0 0 0 (by simp) := by
    dsimp only [b]
    rw [Category.assoc, total_zero_decomposition L hz, Category.comp_id]
  rw [hβ 1, hy, Category.assoc, total_zero_d, Preadditive.comp_add,
    ← Category.assoc, ← Category.assoc] at hxy
  have h1 := congrArg (· ≫ totalProjection L 1 0 1) hxy
  have h0 := congrArg (· ≫ totalProjection L 0 1 1) hxy
  simp only [Category.assoc, Preadditive.add_comp, ι_totalProjection, Category.comp_id,
    ι_totalProjection_of_ne L 1 0 0 1 1 (by simp) (Or.inl (by decide)), comp_zero, add_zero,
    ι_totalProjection_of_ne L 0 1 1 0 1 (by simp) (Or.inl (by decide)), zero_add] at h1 h0
  let a := hker.lift (KernelFork.ofι b h1.symm)
  have ha : a ≫ f.f 0 = b := hker.fac _ WalkingParallelPair.zero
  refine ⟨T, 𝟙 T, inferInstance, a, ?_⟩
  rw [Category.id_comp, ← cancel_mono (f.f 1), Category.assoc, ← f.comm 0 1,
    ← Category.assoc, ha]
  exact h0

end TotalAbelian

/-! ### The inclusion into the degree-zero term of an injective resolution is a kernel -/

section Resolution

variable {A : Type s} [Category.{t} A] [Abelian A] [HasDerivedCategory A] {Y : A}

/-- **The inclusion of an object into the degree-zero term of an injective resolution exhibits
the object as the kernel of the first differential of the resolution.** This is
`Stacks.CechSite.Acyclic.exact_inclusionZero` together with
`Stacks.CechSite.Acyclic.mono_inclusionZero`. -/
def isLimit_kernelFork_inclusionZero (J : InjectiveResolution Y) :
    IsLimit (KernelFork.ofι J.inclusionZero
      (CategoryTheory.InjectiveResolution.inclusionZero_comp_d J)) :=
  haveI := Acyclic.mono_inclusionZero J
  (Acyclic.exact_inclusionZero J).fIsKernel

end Resolution

/-! ### Exactness of the Čech complex functor in a fixed degree -/

section Exactness

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]

/-- **Evaluating the integer-graded Čech complex of a covering family in a fixed degree is a
left exact functor of the abelian sheaf.** This is what makes the first Čech cohomology of the
family inject into cohomology over the covered object: the Čech complex functor carries the
beginning of an injective resolution to an exact sequence. -/
lemma preservesFiniteLimits_cechIntEval (p : ℤ) :
    PreservesFiniteLimits (cechComplexIntFunctor.{a} K E ⋙
      HomologicalComplex.eval Ab.{max a u v w} (ComplexShape.up ℤ) p) := by
  have hext : PreservesFiniteLimits
      (ComplexShape.embeddingUpNat.extendFunctor Ab.{max a u v w}) :=
    ⟨fun _ _ _ ↦ HomologicalComplex.preservesLimitsOfShape_of_eval _ fun i' ↦ by
      by_cases h : ∃ i, ComplexShape.embeddingUpNat.f i = i'
      · obtain ⟨i, hi⟩ := h
        exact preservesLimitsOfShape_of_natIso
          (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso _ hi).symm
      · refine Functor.preservesLimitsOfShape_of_isZero _ ?_ _
        rw [Functor.isZero_iff]
        exact fun L ↦ L.isZero_extend_X _ i' (by tauto)⟩
  have hcech : PreservesFiniteLimits
      (cechComplexFunctor E (A := Ab.{max a u v w})) := by
    unfold cechComplexFunctor FormalCoproduct.cochainComplexFunctor
      FormalCoproduct.cosimplicialObjectFunctor
    infer_instance
  dsimp only [cechComplexIntFunctor, cechComplexIntFunctorPre]
  infer_instance

end Exactness

/-! ### The comparison for a single covering family is a monomorphism -/

section Mono

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{w} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun j ↦ Over.mk (E.f (i j)))]
  [HasSheafify K Ab.{max a u v w}]

/-- A composite of monomorphisms of abelian groups is a monomorphism. Proved through
injectivity rather than taken from the generic instance because the objects met here are
homology groups with two spellings — as a value of the homology functor and as the homology of
a complex — that are definitionally but not reducibly equal, which the generic instance cannot
bridge. -/
private lemma mono_comp_of_mono {X Y Z : Ab.{s}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) := by
  rw [AddCommGrpCat.mono_iff_injective] at hf hg ⊢
  exact fun p q hpq ↦ hf (hg (by simpa only [ConcreteCategory.comp_apply] using hpq))

/-- The Čech bicomplex of a bounded-below resolution vanishes outside the first quadrant. -/
private lemma cechBicomplex_isZero_of_neg {G : Sheaf K Ab.{max a u v w}}
    (J : InjectiveResolution G) (i j : ℤ) (h : i < 0 ∨ j < 0) :
    IsZero (((cechBicomplex.{a} K E J.cochainComplex).X i).X j) := by
  rcases h with hi | hj
  · exact (cechComplexIntFunctor.{a} K E ⋙
      HomologicalComplex.eval Ab.{max a u v w} (ComplexShape.up ℤ) j).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE J.cochainComplex 0 i hi)
  · exact isZero_cechComplexIntFunctorPre_X.{a} E (J.cochainComplex.X i).obj j hj

variable [K.WEqualsLocallyBijective Ab.{max a u v w}]
  [EnoughInjectives (Sheaf K Ab.{max a u v w})]

omit [K.WEqualsLocallyBijective Ab.{max a u v w}] in
/-- First homology of the map induced by the inclusion of a sheaf into the degree-zero term of
an injective resolution is a monomorphism: evaluating the Čech complex is left exact, so that
inclusion stays a kernel in every Čech degree. -/
private lemma mono_homologyMap_cechResolutionComparison_beta
    (hE : Sieve.generate E.presieve₀ ∈ K U) {G : Sheaf K Ab.{max a u v w}}
    (J : InjectiveResolution G)
    (r : CechResolutionComparison.{a} K E hE G J) :
    Mono (HomologicalComplex.homologyMap r.β 1) := by
  set F := cechComplexIntFunctor.{a} K E with hFdef
  have hC0 := preservesFiniteLimits_cechIntEval.{a} K E 0
  have hC1 := preservesFiniteLimits_cechIntEval.{a} K E 1
  have hmono := Acyclic.mono_inclusionZero J
  have hzero : F.map J.inclusionZero ≫
      (cechBicomplex.{a} K E J.cochainComplex).d 0 1 = 0 := by
    change F.map J.inclusionZero ≫ F.map (J.cochainComplex.d 0 1) = 0
    rw [← F.map_comp, CategoryTheory.InjectiveResolution.inclusionZero_comp_d,
      Functor.map_zero]
  have hf1 : Mono ((F.map J.inclusionZero).f 1) :=
    (F ⋙ HomologicalComplex.eval Ab.{max a u v w} (ComplexShape.up ℤ) 1).map_mono _
  refine mono_homologyMap_total_of_kernel _ (cechBicomplex_isZero_of_neg.{a} K E J)
    (F.map J.inclusionZero) hzero ?_ r.β r.β_f
  exact KernelFork.mapIsLimit _ (isLimit_kernelFork_inclusionZero J)
    (F ⋙ HomologicalComplex.eval Ab.{max a u v w} (ComplexShape.up ℤ) 0)

omit [K.WEqualsLocallyBijective Ab.{max a u v w}] in
/-- For a covering family of an object of a site, the degree-one comparison of Stacks 03AX
from Čech cohomology to the cohomology of the sheaf over that object is a monomorphism. -/
theorem mono_cechCohomologyToCohomology_one (hE : Sieve.generate E.presieve₀ ∈ K U)
    (G : Sheaf K Ab.{max a u v w}) :
    Mono ((cechCohomologyToCohomology.{a} K E hE 1).app G) := by
  obtain ⟨r⟩ := nonempty_cechResolutionComparison.{a} K E hE G (InjectiveResolution.of G)
  have hβ : Mono (HomologicalComplex.homologyMap r.β 1) :=
    mono_homologyMap_cechResolutionComparison_beta.{a} K E hE _ r
  have hiso : IsIso ((DerivedCategory.homologyFunctorFactors Ab.{max a u v w} 1).hom.app
      ((cechComplexIntFunctor.{a} K E).obj G)) :=
    Iso.isIso_hom ((DerivedCategory.homologyFunctorFactors Ab.{max a u v w} 1).app
      ((cechComplexIntFunctor.{a} K E).obj G))
  have hQ : Mono ((DerivedCategory.homologyFunctor Ab.{max a u v w} 1).map
      (DerivedCategory.Q.map r.β)) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro p p' hpp'
    have hn := DerivedCategory.homologyFunctorFactors_hom_naturality r.β 1
    have h1 := ConcreteCategory.congr_hom hn p
    have h2 := ConcreteCategory.congr_hom hn p'
    simp only [ConcreteCategory.comp_apply] at h1 h2
    rw [hpp', h2] at h1
    have h3 := (AddCommGrpCat.mono_iff_injective _).mp hβ h1
    exact ((AddCommGrpCat.mono_iff_injective _).mp inferInstance h3).symm
  have hρ : IsIso ((InjectiveResolution.of G).toRightDerived
      ((sheafSections K Ab.{max a u v w}).obj (op U))) := inferInstance
  have hcc : ((cechCohomologyToCohomology.{a} K E hE 1).app G) =
      (DerivedCategory.homologyFunctor Ab.{max a u v w} 1).map
          (DerivedCategory.Q.map r.β) ≫
        (DerivedCategory.homologyFunctor Ab.{max a u v w} 1).map
          (r.αIso.inv ≫ (InjectiveResolution.of G).toRightDerived
            ((sheafSections K Ab.{max a u v w}).obj (op U))) :=
    (congrArg (DerivedCategory.homologyFunctor Ab.{max a u v w} 1).map
        r.comparison).trans
      ((DerivedCategory.homologyFunctor Ab.{max a u v w} 1).map_comp _ _)
  have hm2 : Mono ((DerivedCategory.homologyFunctor Ab.{max a u v w} 1).map
      (r.αIso.inv ≫ (InjectiveResolution.of G).toRightDerived
        ((sheafSections K Ab.{max a u v w}).obj (op U)))) := inferInstance
  rw [hcc]
  exact mono_comp_of_mono _ _ hQ hm2

omit [K.WEqualsLocallyBijective Ab.{max a u v w}] in
/-- **Stacks Project, Tag 0A6G.** For a covering family `𝒰 = {U_i → U}` of an object of a site
and an abelian sheaf `G`, the map `Ȟ¹(𝒰, G) → H¹(U, G)` of Stacks 03AX is injective. -/
@[stacks 0A6G "variant: injectivity of the derived-category comparison; \
the tag is Stacks.CechSite.cechH1ToSliceH_injective_and_range_eq"]
theorem injective_cechCohomologyToCohomology_one (hE : Sieve.generate E.presieve₀ ∈ K U)
    (G : Sheaf K Ab.{max a u v w}) :
    Function.Injective ((cechCohomologyToCohomology.{a} K E hE 1).app G) :=
  (AddCommGrpCat.mono_iff_injective _).1
    (mono_cechCohomologyToCohomology_one.{a} K E hE G)

end Mono

end Stacks.CechSite

end
