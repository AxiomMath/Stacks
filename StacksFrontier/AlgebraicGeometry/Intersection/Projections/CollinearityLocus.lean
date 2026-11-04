module

public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.ProjTwistSection.NonvanishingEq
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RationalPointHyperplane
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The collinearity locus in a triple product of projective spaces

Let `V` be a vector space over a field `k` and `𝐏(V) = Proj (Sym_k V)`. Three points of `𝐏(V)`
are collinear when the three linear functionals cutting them out are linearly dependent, that is
when every `3 × 3` determinant `det (fᵢ (wⱼ))` formed from three vectors `w₀, w₁, w₂` of `V`
vanishes. Those determinants are the global sections of the invertible module
`𝒪(1,1,1) = pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1) ⊗ pr₃^* 𝒪(1)` on `𝐏(V) × 𝐏(V) × 𝐏(V)` obtained by
antisymmetrising the tensors `pr₁^*(w) ⊗ pr₂^*(w) ⊗ pr₃^*(w)` of the tautological sections, so
their common zero locus is a closed subset of the triple product and carries a closed subscheme:
the collinearity locus. Base changing its projection to the first two factors along a morphism
`S ⟶ 𝐏(V) × 𝐏(V)` gives the incidence variety of lines over `S`, whose fibre over a pair of
distinct closed points is the line joining them.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.tautologicalModule` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tautologicalSection`: `𝒪(1)` on `𝐏(V)` and its
  global section `ι v / 1` attached to a vector `v` of `V`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.prodTwo` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.prodThree`: the products `𝐏(V) ×_k 𝐏(V)` and
  `𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)`, with their projections
  `AlgebraicGeometry.ProjectiveSpaceOfModule.prFst`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pr₁`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pr₂` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pr₃`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.tripleTwistModule`: `𝒪(1,1,1)` on the triple
  product, with `AlgebraicGeometry.ProjectiveSpaceOfModule.tripleSection` the tensor of three
  tautological sections and `AlgebraicGeometry.ProjectiveSpaceOfModule.detSection` the
  antisymmetrisation of the latter in the three vectors, the determinant section.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.collinearLocus`: the common zero locus of the
  determinant sections, the set of collinear triples.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.collinearSubscheme`: that locus as a closed
  subscheme of the triple product, with
  `AlgebraicGeometry.ProjectiveSpaceOfModule.collinearSubschemeι` its closed immersion,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.collinearProj` its projection to the first two
  factors and `AlgebraicGeometry.ProjectiveSpaceOfModule.collinearProj₃` its projection to the
  third.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.incidenceVariety`: the base change of that
  projection along a morphism `S ⟶ 𝐏(V) ×_k 𝐏(V)`, with
  `AlgebraicGeometry.ProjectiveSpaceOfModule.incidenceVarietyOfClosed` the case of a product of
  two closed subschemes of `𝐏(V)`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_tautologicalSection_iff`: the
  section `ι v / 1` of `𝒪(1)` is nonvanishing at a point exactly on the standard open
  `D₊(ι v)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_tripleSection_iff`: the
  tensor `pr₁^*(ι a) ⊗ pr₂^*(ι b) ⊗ pr₃^*(ι c)` is nonvanishing exactly on
  `pr₁⁻¹D₊(ι a) ∩ pr₂⁻¹D₊(ι b) ∩ pr₃⁻¹D₊(ι c)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isClosed_collinearLocus` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.range_collinearSubschemeι`: the collinearity locus
  is closed and is the image of the collinearity subscheme.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_prodTwo` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_prodThree`: the dimension of a
  product of projective spaces is the sum of the dimensions.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isPullback_incidenceVariety`: the incidence variety
  is the fibre product of the collinearity subscheme with the base.

## Implementation notes

The triple product is formed as `(𝐏(V) ×_k 𝐏(V)) ×_k 𝐏(V)`, the fibre product over `Spec k`, so
that the projection to the first two factors is a single `pullback.fst`.

The determinant sections are handled through `Stacks.SheafOfModules.nonvanishingLocus`, which,
unlike `Stacks.SheafOfModules.nonvanishingOpen`, takes no invertibility instance. A determinant
section is built directly as a compatible family of sections, as a sum over the permutations of
`Fin 3` of signed tensors, since the global sections of a presheaf of modules form a bare type
with no additive structure.

The subscheme structure on the collinearity locus is the reduced induced one, that of
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` of the locus, rather than the subscheme
cut out by the ideal sheaf generated by the determinant sections. The two have the same
underlying closed subset.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The tautological invertible module on `𝐏(V)` -/

/-- The grading of the symmetric algebra `Sym_k V` by its symmetric powers, the graded ring
whose `Proj` is `𝐏(V)`. -/
@[ega "II 1.7.1" "special case"]
public abbrev symmetricGrading : ℕ → Submodule k (SymmetricAlgebra k V) :=
  fun n => SymPow.symmetricPower n k V

/-- **The tautological invertible module `𝒪(1)` on `𝐏(V)`**, the degree-one twisting sheaf of
the symmetric grading. -/
public abbrev tautologicalModule : (projectiveSpaceOfModule k V).Modules :=
  Stacks.ProjTwistSection.twistingModule (symmetricGrading k V) 1

/-- **`𝒪(1)` on `𝐏(V)` is invertible**: the symmetric algebra is generated in degree one over
its degree-zero part. -/
public theorem isInvertible_tautologicalModule :
    Stacks.SheafOfModules.IsInvertible (projectiveSpaceOfModule k V).presheaf
      (structureSheafRing
        (projectiveSpaceOfModule k V).toRingedSpace).property (tautologicalModule k V) :=
  Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf (symmetricGrading k V)
    (SymmetricAlgebra.adjoin_symmetricPower_one_eq_top k V) 1

/-- The global section `ι v / 1` of `𝒪(1)` on `𝐏(V)` attached to a vector `v` of `V`, the
linear form `v` read as a section of the twisting sheaf. -/
public def tautologicalSection (v : V) : (tautologicalModule k V).sections :=
  Stacks.ProjTwistSection.homogeneousSection (symmetricGrading k V) (SymmetricAlgebra.ι k V v)
    (ι_mem_symmetricPower_one k V v)

/-- **The section attached to `v` is nonvanishing exactly on the standard open `D₊(ι v)`**: a
point lies in its nonvanishing locus exactly when `ι v` is outside the homogeneous prime of that
point. -/
public theorem mem_nonvanishingLocus_tautologicalSection_iff (v : V)
    (y : projectiveSpaceOfModule k V) :
    y ∈ Stacks.SheafOfModules.nonvanishingLocus
        (X := (projectiveSpaceOfModule k V).toRingedSpace)
        (tautologicalModule k V) (tautologicalSection k V v) ↔
      SymmetricAlgebra.ι k V v ∉ y.asHomogeneousIdeal := by
  have hinv := isInvertible_tautologicalModule k V
  have hcov : ∀ x : ProjectiveSpectrum.top (symmetricGrading k V),
      ∃ g : SymmetricAlgebra k V, g ∈ symmetricGrading k V 1 ∧
        x ∈ ProjectiveSpectrum.basicOpen (symmetricGrading k V) g := by
    intro x
    obtain ⟨w, hw⟩ := exists_ι_notMem k V x
    exact ⟨SymmetricAlgebra.ι k V w, ι_mem_symmetricPower_one k V w, hw⟩
  have hdict := Stacks.ProjTwistSection.nonvanishingOpen_homogeneousSection_eq_basicOpen
    (symmetricGrading k V) (SymmetricAlgebra.ι k V v) (ι_mem_symmetricPower_one k V v) hcov
  have hset := congrArg (fun U : Opens (ProjectiveSpectrum.top (symmetricGrading k V)) =>
    (U : Set (ProjectiveSpectrum.top (symmetricGrading k V)))) hdict
  exact Set.ext_iff.mp hset y

/-! ### Products of projective spaces -/

private instance locallyOfFiniteType_toSpec [FiniteDimensional k V] [Nontrivial V] :
    LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  infer_instance

/-- The product `𝐏(V) ×_k 𝐏(V)`. -/
public abbrev prodTwo : Scheme.{u} :=
  pullback (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V)

/-- The structure morphism of `𝐏(V) ×_k 𝐏(V)` over `Spec k`. -/
public def prodTwoToSpec : prodTwo k V ⟶ Spec (.of k) :=
  pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) ≫
    projectiveSpaceOfModuleToSpec k V

/-- The product `𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)`, formed as `(𝐏(V) ×_k 𝐏(V)) ×_k 𝐏(V)`. -/
public abbrev prodThree : Scheme.{u} :=
  pullback (prodTwoToSpec k V) (projectiveSpaceOfModuleToSpec k V)

/-- The projection of the triple product to the product of the first two factors. -/
public def prFst : prodThree k V ⟶ prodTwo k V := pullback.fst _ _

/-- The projection of the triple product to the first factor. -/
public def pr₁ : prodThree k V ⟶ projectiveSpaceOfModule k V :=
  prFst k V ≫ pullback.fst _ _

/-- The projection of the triple product to the second factor. -/
public def pr₂ : prodThree k V ⟶ projectiveSpaceOfModule k V :=
  prFst k V ≫ pullback.snd _ _

/-- The projection of the triple product to the third factor. -/
public def pr₃ : prodThree k V ⟶ projectiveSpaceOfModule k V := pullback.snd _ _

/-- The structure morphism of the triple product over `Spec k`. -/
public def prodThreeToSpec : prodThree k V ⟶ Spec (.of k) :=
  pr₃ k V ≫ projectiveSpaceOfModuleToSpec k V

/-- `𝐏(V) ×_k 𝐏(V)` is locally of finite type over `k`. -/
public instance locallyOfFiniteType_prodTwoToSpec [FiniteDimensional k V] [Nontrivial V] :
    LocallyOfFiniteType (prodTwoToSpec k V) := by
  rw [prodTwoToSpec]
  infer_instance

/-- The triple product is locally of finite type over `k`. -/
public instance locallyOfFiniteType_prodThreeToSpec [FiniteDimensional k V] [Nontrivial V] :
    LocallyOfFiniteType (prodThreeToSpec k V) := by
  rw [prodThreeToSpec, pr₃]
  infer_instance

/-- **The dimension of `𝐏(V) ×_k 𝐏(V)` is twice the dimension of `𝐏(V)`.** -/
public theorem topologicalKrullDim_prodTwo [FiniteDimensional k V] [Nontrivial V] :
    topologicalKrullDim (prodTwo k V) =
      topologicalKrullDim (projectiveSpaceOfModule k V) +
        topologicalKrullDim (projectiveSpaceOfModule k V) :=
  topologicalKrullDim_pullback k _ _

/-- **The dimension of the triple product is the dimension of `𝐏(V) ×_k 𝐏(V)` plus that of
`𝐏(V)`.** -/
public theorem topologicalKrullDim_prodThree [FiniteDimensional k V] [Nontrivial V] :
    topologicalKrullDim (prodThree k V) =
      topologicalKrullDim (prodTwo k V) + topologicalKrullDim (projectiveSpaceOfModule k V) :=
  topologicalKrullDim_pullback k (prodTwoToSpec k V) (projectiveSpaceOfModuleToSpec k V)

/-! ### The invertible module `𝒪(1,1,1)` and its determinant sections -/

/-- The pullback `pr₁^* 𝒪(1)` of the tautological module along the first projection. -/
public abbrev taut₁ : (prodThree k V).Modules :=
  (Scheme.Modules.pullback (pr₁ k V)).obj (tautologicalModule k V)

/-- The pullback `pr₂^* 𝒪(1)` of the tautological module along the second projection. -/
public abbrev taut₂ : (prodThree k V).Modules :=
  (Scheme.Modules.pullback (pr₂ k V)).obj (tautologicalModule k V)

/-- The pullback `pr₃^* 𝒪(1)` of the tautological module along the third projection. -/
public abbrev taut₃ : (prodThree k V).Modules :=
  (Scheme.Modules.pullback (pr₃ k V)).obj (tautologicalModule k V)

/-- **The invertible module `𝒪(1,1,1) = pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1) ⊗ pr₃^* 𝒪(1)`** on the triple
product of projective spaces. -/
public def tripleTwistModule : (prodThree k V).Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(prodThree k V).toRingedSpace.presheaf, (prodThree k V).toRingedSpace.IsSheaf⟩).obj
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(prodThree k V).toRingedSpace.presheaf, (prodThree k V).toRingedSpace.IsSheaf⟩).obj
        (taut₁ k V)).obj (taut₂ k V))).obj (taut₃ k V)

/-- **`𝒪(1,1,1)` is invertible**: a pullback of an invertible module is invertible, and so is a
tensor product of invertible modules. -/
public theorem isInvertible_tripleTwistModule :
    Stacks.SheafOfModules.IsInvertible (prodThree k V).presheaf
      (structureSheafRing
        (prodThree k V).toRingedSpace).property (tripleTwistModule k V) :=
  have : Stacks.SheafOfModules.IsInvertible (projectiveSpaceOfModule k V).presheaf
      (structureSheafRing
        (projectiveSpaceOfModule k V).toRingedSpace).property (tautologicalModule k V) :=
    isInvertible_tautologicalModule k V
  have h12 := @Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ (prodThree k V).presheaf
    (structureSheafRing
      (prodThree k V).toRingedSpace).property _ _ (taut₁ k V) (taut₂ k V)
    (Stacks.Modules.isInvertible_pullback _ _) (Stacks.Modules.isInvertible_pullback _ _)
  @Stacks.SheafOfModules.tensorProduct_isInvertible _ _ _ (prodThree k V).presheaf
    (structureSheafRing
      (prodThree k V).toRingedSpace).property _ _
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(prodThree k V).toRingedSpace.presheaf, (prodThree k V).toRingedSpace.IsSheaf⟩).obj
        (taut₁ k V)).obj (taut₂ k V))
    (taut₃ k V) h12 (Stacks.Modules.isInvertible_pullback _ _)

/-- The pullback along a projection of the section of `𝒪(1)` attached to a vector. -/
public def tautologicalPullbackSection (f : prodThree k V ⟶ projectiveSpaceOfModule k V)
    (v : V) :
    ((Scheme.Modules.pullback f).obj (tautologicalModule k V)).sections :=
  Stacks.SheafOfModules.modulePullbackSection f.toLRSHom (tautologicalModule k V)
    (tautologicalSection k V v)

/-- The nonvanishing locus of a pulled-back tautological section is the preimage of the
nonvanishing locus. -/
public theorem nonvanishingLocus_tautologicalPullbackSection
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (v : V) :
    Stacks.SheafOfModules.nonvanishingLocus (X := (prodThree k V).toRingedSpace)
        ((Scheme.Modules.pullback f).obj (tautologicalModule k V))
        (tautologicalPullbackSection k V f v) =
      f.base ⁻¹' Stacks.SheafOfModules.nonvanishingLocus
        (X := (projectiveSpaceOfModule k V).toRingedSpace)
        (tautologicalModule k V) (tautologicalSection k V v) := by
  have hinv := isInvertible_tautologicalModule k V
  exact (congrArg (fun U : (prodThree k V).Opens => (U : Set (prodThree k V)))
    (Stacks.SheafOfModules.preimage_nonvanishingOpen f (tautologicalModule k V)
      (tautologicalSection k V v))).symm

/-- The global section `pr₁^*(ι a) ⊗ pr₂^*(ι b) ⊗ pr₃^*(ι c)` of `𝒪(1,1,1)`. -/
public def tripleSection (a b c : V) : (tripleTwistModule k V).sections :=
  Stacks.SheafOfModules.tensorSections _ _
    (Stacks.SheafOfModules.tensorSections _ _
      (tautologicalPullbackSection k V (pr₁ k V) a)
      (tautologicalPullbackSection k V (pr₂ k V) b))
    (tautologicalPullbackSection k V (pr₃ k V) c)

/-- **The nonvanishing locus of `pr₁^*(ι a) ⊗ pr₂^*(ι b) ⊗ pr₃^*(ι c)` is the intersection of
the three preimages** of the nonvanishing loci of the three factors. -/
public theorem nonvanishingLocus_tripleSection (a b c : V) :
    Stacks.SheafOfModules.nonvanishingLocus (X := (prodThree k V).toRingedSpace)
        (tripleTwistModule k V) (tripleSection k V a b c) =
      ((pr₁ k V).base ⁻¹' Stacks.SheafOfModules.nonvanishingLocus
          (X := (projectiveSpaceOfModule k V).toRingedSpace)
          (tautologicalModule k V) (tautologicalSection k V a) ∩
        (pr₂ k V).base ⁻¹' Stacks.SheafOfModules.nonvanishingLocus
          (X := (projectiveSpaceOfModule k V).toRingedSpace)
          (tautologicalModule k V) (tautologicalSection k V b)) ∩
      (pr₃ k V).base ⁻¹' Stacks.SheafOfModules.nonvanishingLocus
        (X := (projectiveSpaceOfModule k V).toRingedSpace)
        (tautologicalModule k V) (tautologicalSection k V c) :=
  (Stacks.SheafOfModules.nonvanishingLocus_tensorSections _ _ _ _).trans
    (congrArg₂ (· ∩ ·)
      ((Stacks.SheafOfModules.nonvanishingLocus_tensorSections _ _ _ _).trans
        (congrArg₂ (· ∩ ·) (nonvanishingLocus_tautologicalPullbackSection k V (pr₁ k V) a)
          (nonvanishingLocus_tautologicalPullbackSection k V (pr₂ k V) b)))
      (nonvanishingLocus_tautologicalPullbackSection k V (pr₃ k V) c))

/-- **The tensor of three tautological sections is nonvanishing at a point of the triple product
exactly when each of the three linear forms avoids the homogeneous prime of the corresponding
projection** of that point. -/
public theorem mem_nonvanishingLocus_tripleSection_iff (a b c : V) (t : prodThree k V) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := (prodThree k V).toRingedSpace)
        (tripleTwistModule k V) (tripleSection k V a b c) ↔
      SymmetricAlgebra.ι k V a ∉ ((pr₁ k V).base t).asHomogeneousIdeal ∧
        SymmetricAlgebra.ι k V b ∉ ((pr₂ k V).base t).asHomogeneousIdeal ∧
        SymmetricAlgebra.ι k V c ∉ ((pr₃ k V).base t).asHomogeneousIdeal := by
  have h := Set.ext_iff.mp (nonvanishingLocus_tripleSection k V a b c) t
  rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage,
    Set.mem_preimage, mem_nonvanishingLocus_tautologicalSection_iff,
    mem_nonvanishingLocus_tautologicalSection_iff,
    mem_nonvanishingLocus_tautologicalSection_iff] at h
  exact h.trans and_assoc

/-- The section `pr₁^*(ι w₀) ⊗ pr₂^*(ι w₁) ⊗ pr₃^*(ι w₂)` attached to a triple of vectors. -/
public def tripleSectionOf (w : Fin 3 → V) : (tripleTwistModule k V).sections :=
  tripleSection k V (w 0) (w 1) (w 2)

/-- **The determinant section attached to three vectors of `V`**: the antisymmetrisation
`∑ σ, sign σ • pr₁^*(ι w_{σ 0}) ⊗ pr₂^*(ι w_{σ 1}) ⊗ pr₃^*(ι w_{σ 2})` of the tensors of the
three tautological sections. At a triple of points cut out by functionals `f₁, f₂, f₃` it is,
in any local trivialisation of `𝒪(1,1,1)`, the determinant of the matrix `fᵢ (wⱼ)`. -/
public def detSection (w : Fin 3 → V) : (tripleTwistModule k V).sections :=
  (tripleTwistModule k V).val.sectionsMk
    (fun U => ∑ σ : Equiv.Perm (Fin 3),
      (Equiv.Perm.sign σ : ℤ) • (tripleSectionOf k V (w ∘ σ)).eval U)
    (by
      intro U W f
      rw [map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [map_zsmul, PresheafOfModules.sections_property]
      rfl)

/-- The determinant section evaluates over an open to the signed sum of the evaluations of the
tensors of tautological sections. -/
public theorem detSection_eval (w : Fin 3 → V) (U : (Opens ↥(prodThree k V))ᵒᵖ) :
    (detSection k V w).eval U =
      ∑ σ : Equiv.Perm (Fin 3),
        (Equiv.Perm.sign σ : ℤ) • (tripleSectionOf k V (w ∘ σ)).eval U :=
  rfl

/-! ### The collinearity locus and the incidence variety -/

/-- **The collinearity locus**: the set of points of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)` at which every
determinant section vanishes, that is at which the three points span a subspace of dimension at
most two. -/
public def collinearLocus : Set (prodThree k V) :=
  ⋂ w : Fin 3 → V, (Stacks.SheafOfModules.nonvanishingLocus
    (X := (prodThree k V).toRingedSpace) (tripleTwistModule k V) (detSection k V w))ᶜ

/-- A point of the triple product is collinear exactly when no determinant section is
nonvanishing at it. -/
public theorem mem_collinearLocus_iff (t : prodThree k V) :
    t ∈ collinearLocus k V ↔ ∀ w : Fin 3 → V,
      t ∉ Stacks.SheafOfModules.nonvanishingLocus (X := (prodThree k V).toRingedSpace)
        (tripleTwistModule k V) (detSection k V w) :=
  Set.mem_iInter

/-- **The collinearity locus is closed**: the nonvanishing locus of a global section of an
invertible module is open, and the collinearity locus is the intersection of the complements. -/
public theorem isClosed_collinearLocus : IsClosed (collinearLocus k V) := by
  have hinv := isInvertible_tripleTwistModule k V
  exact isClosed_iInter fun w =>
    (Stacks.SheafOfModules.isOpen_nonvanishingLocus (tripleTwistModule k V)
      (detSection k V w)).isClosed_compl

/-- The ideal sheaf of the collinearity locus, the vanishing ideal of that closed subset. -/
public def collinearIdeal : (prodThree k V).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨collinearLocus k V, isClosed_collinearLocus k V⟩

/-- **The collinearity locus as a closed subscheme** of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)`, with its
reduced induced structure. -/
public def collinearSubscheme : Scheme.{u} := (collinearIdeal k V).subscheme

/-- The inclusion of the collinearity subscheme into the triple product. -/
public def collinearSubschemeι : collinearSubscheme k V ⟶ prodThree k V :=
  (collinearIdeal k V).subschemeι

/-- The collinearity subscheme is a closed subscheme of the triple product. -/
public theorem isClosedImmersion_collinearSubschemeι :
    IsClosedImmersion (collinearSubschemeι k V) :=
  inferInstanceAs (IsClosedImmersion (collinearIdeal k V).subschemeι)

/-- **The points of the collinearity subscheme are exactly the collinear triples.** -/
public theorem range_collinearSubschemeι :
    Set.range (collinearSubschemeι k V).base = collinearLocus k V :=
  ((collinearIdeal k V).range_subschemeι).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- **The projection of the collinearity subscheme to the first two factors**, the morphism
whose fibre over a pair of distinct closed points is the line joining them. -/
public def collinearProj : collinearSubscheme k V ⟶ prodTwo k V :=
  collinearSubschemeι k V ≫ prFst k V

/-- The projection of the collinearity subscheme to the third factor. -/
public def collinearProj₃ : collinearSubscheme k V ⟶ projectiveSpaceOfModule k V :=
  collinearSubschemeι k V ≫ pr₃ k V

/-- The structure morphism of the collinearity subscheme over `Spec k`. -/
public def collinearToSpec : collinearSubscheme k V ⟶ Spec (.of k) :=
  collinearSubschemeι k V ≫ prodThreeToSpec k V

/-- The collinearity subscheme is locally of finite type over `k`. -/
public instance locallyOfFiniteType_collinearToSpec [FiniteDimensional k V] [Nontrivial V] :
    LocallyOfFiniteType (collinearToSpec k V) := by
  have := isClosedImmersion_collinearSubschemeι k V
  rw [collinearToSpec]
  infer_instance

/-- **The incidence variety of lines over a base `S` mapping to `𝐏(V) ×_k 𝐏(V)`**: the base
change along that morphism of the projection of the collinearity subscheme to the first two
factors. Over `S = Y × Z` its points are the triples `(y, z, p)` with `p` on the line joining
`y` to `z`. -/
public def incidenceVariety {S : Scheme.{u}} (f : S ⟶ prodTwo k V) : Scheme.{u} :=
  pullback (collinearProj k V) f

/-- The projection of the incidence variety to its base. -/
public def incidenceVarietyToBase {S : Scheme.{u}} (f : S ⟶ prodTwo k V) :
    incidenceVariety k V f ⟶ S := pullback.snd _ _

/-- The projection of the incidence variety to the collinearity subscheme. -/
public def incidenceVarietyToCollinear {S : Scheme.{u}} (f : S ⟶ prodTwo k V) :
    incidenceVariety k V f ⟶ collinearSubscheme k V := pullback.fst _ _

/-- The morphism from the incidence variety to `𝐏(V)` sending a triple to the point on the
line. -/
public def incidenceVarietyToProj {S : Scheme.{u}} (f : S ⟶ prodTwo k V) :
    incidenceVariety k V f ⟶ projectiveSpaceOfModule k V :=
  incidenceVarietyToCollinear k V f ≫ collinearProj₃ k V

/-- **The incidence variety is the fibre product** of the collinearity subscheme with the base
over `𝐏(V) ×_k 𝐏(V)`. -/
public theorem isPullback_incidenceVariety {S : Scheme.{u}} (f : S ⟶ prodTwo k V) :
    IsPullback (incidenceVarietyToCollinear k V f) (incidenceVarietyToBase k V f)
      (collinearProj k V) f :=
  IsPullback.of_hasPullback _ _

/-! ### Products of closed subschemes as bases -/

/-- A closed subset of `𝐏(V)` as a closed subscheme, with its reduced induced structure. -/
public def closedSubschemeOf (Y : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y) :
    Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨Y, hY⟩).subscheme

/-- The inclusion of a closed subscheme of `𝐏(V)`. -/
public def closedSubschemeOfι (Y : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y) :
    closedSubschemeOf k V Y hY ⟶ projectiveSpaceOfModule k V :=
  (Scheme.IdealSheafData.vanishingIdeal ⟨Y, hY⟩).subschemeι

/-- The structure morphism of a closed subscheme of `𝐏(V)` over `Spec k`. -/
public def closedSubschemeOfToSpec (Y : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y) :
    closedSubschemeOf k V Y hY ⟶ Spec (.of k) :=
  closedSubschemeOfι k V Y hY ≫ projectiveSpaceOfModuleToSpec k V

/-- The product over `Spec k` of two closed subschemes of `𝐏(V)`. -/
public def prodOfClosed (Y Z : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y)
    (hZ : IsClosed Z) : Scheme.{u} :=
  pullback (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ)

/-- The closed immersion of the product of two closed subschemes of `𝐏(V)` into
`𝐏(V) ×_k 𝐏(V)`. -/
public def prodOfClosedToProdTwo (Y Z : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y)
    (hZ : IsClosed Z) : prodOfClosed k V Y Z hY hZ ⟶ prodTwo k V :=
  pullback.map _ _ _ _ (closedSubschemeOfι k V Y hY) (closedSubschemeOfι k V Z hZ) (𝟙 _)
    (by rw [Category.comp_id, closedSubschemeOfToSpec])
    (by rw [Category.comp_id, closedSubschemeOfToSpec])

/-- **The incidence variety of lines over a product of two closed subschemes of `𝐏(V)`**: the
triples `(y, z, p)` with `y` in `Y`, `z` in `Z` and `p` on the line joining them. -/
public def incidenceVarietyOfClosed (Y Z : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y)
    (hZ : IsClosed Z) : Scheme.{u} :=
  incidenceVariety k V (prodOfClosedToProdTwo k V Y Z hY hZ)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
