module

public import StacksFrontier.AlgebraicGeometry.Perfect.KGroups.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectKGroupRing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional

/-!
# The product on `K₀(D_{Z,perf}(𝒪_X))`

Let `X` be a scheme and `Z ⊆ X` a closed subscheme. The derived tensor product `E ⊗^L F` of two
perfect complexes `E, F` whose cohomology sheaves are set-theoretically supported on `Z` is again
such a complex: it is perfect (Stacks 09J5), and its derived stalk at a point `x ∉ Z` is the
derived tensor product of the derived stalks over `𝒪_{X,x}`, the first of which vanishes. So the
derived tensor product restricts to a bifunctor of `D_{Z,perf}(𝒪_X)`, exact in each variable, and
as in Remark 0FDK it induces a biadditive multiplication

  `K₀(D_{Z,perf}(𝒪_X)) × K₀(D_{Z,perf}(𝒪_X)) ⟶ K₀(D_{Z,perf}(𝒪_X))`,   `[E] · [F] = [E ⊗^L F]`,

which is associative and commutative (Remark 0FDN). It has no unit in general: `𝒪_X` is not
supported on `Z` unless `Z` is all of `X` set-theoretically.

## Main definitions

* `AlgebraicGeometry.supportedPerfectTensor` — the derived tensor product as a bifunctor of
  `D_{Z,perf}(𝒪_X)`.
* `AlgebraicGeometry.supportedPerfectMul` — the multiplication of `K₀(D_{Z,perf}(𝒪_X))`.
* `AlgebraicGeometry.supportedPerfectNonUnitalCommRing` — the resulting commutative ring
  without unit.

## Main results

* `AlgebraicGeometry.cohomologySupportedOn_iff_supp_subset` — cohomological support in a set, as
  inclusion of the supports of the cohomology sheaves.
* `AlgebraicGeometry.supportedPerfect_derivedTensor` — `E ⊗^L F ∈ D_{Z,perf}(𝒪_X)` for
  `E, F ∈ D_{Z,perf}(𝒪_X)`.
* `AlgebraicGeometry.supportedPerfectMul_cls` — `[E] · [F] = [E ⊗^L F]`.
* `AlgebraicGeometry.supportedPerfectMul_assoc`, `AlgebraicGeometry.supportedPerfectMul_comm`.

## Implementation notes

The derived tensor product is the canonical one of Stacks 06YU
(`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`). The associativity and
commutativity isomorphisms of objects are those of the tensor structure of `D(𝒪_X)`
(`AlgebraicGeometry.RingedSpace.derivedTensorStructure`); since a class in `K₀` only depends on
its object up to isomorphism, no naturality or coherence of them is used.

## References

* [Stacks Project, Tag 0FDN](https://stacks.math.columbia.edu/tag/0FDN)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 09J5](https://stacks.math.columbia.edu/tag/09J5)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated StrictlyPerfect
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **Cohomological support, as supports of the cohomology sheaves.** An object of `D(𝒪_X)` has
its cohomology supported on `T` exactly when every cohomology sheaf has support contained in
`T`. -/
theorem cohomologySupportedOn_iff_supp_subset (T : Set X) (E : DerivedCategory X.Modules) :
    CohomologySupportedOn (structureSheafRing X.toRingedSpace) T E ↔
      ∀ n : ℤ, SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules n).obj E) ⊆ T := by
  refine ⟨fun hE n x hx ↦ ?_, fun hE n x hx ↦ ?_⟩
  · by_contra hxT
    obtain ⟨a, ha⟩ := hx
    exact ha ((AddCommGrpCat.isZero_iff_subsingleton.1 (hE n x hxT)).elim a 0)
  · have hx' : x ∉ SheafOfModules.supp
        ((DerivedCategory.homologyFunctor X.Modules n).obj E) := fun h ↦ hx (hE n h)
    simp only [SheafOfModules.supp, Set.mem_ofPred_eq, not_exists, not_not] at hx'
    refine (AddCommGrpCat.isZero_iff_subsingleton).2 ⟨fun a b ↦ ?_⟩
    rw [hx' a, hx' b]

variable {i} in
omit [IsClosedImmersion i] in
/-- **The derived tensor product of two perfect complexes supported on `Z` is a perfect complex
supported on `Z`**: it is perfect by Stacks 09J5, and its cohomology is supported on `Z` since
that of the first factor is
(`Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left`). -/
theorem supportedPerfect_derivedTensor {E F : DerivedCategory X.Modules}
    (hE : RingedSpace.IsPerfect E ∧ ∀ n : ℤ,
      SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules n).obj E) ⊆
        Set.range i.base)
    (hF : RingedSpace.IsPerfect F ∧ ∀ n : ℤ,
      SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules n).obj F) ⊆
        Set.range i.base) :
    RingedSpace.IsPerfect (((derivedTensorProductFunctor X.sheaf).obj E).obj F) ∧ ∀ n : ℤ,
      SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules n).obj
        (((derivedTensorProductFunctor X.sheaf).obj E).obj F)) ⊆ Set.range i.base :=
  ⟨RingedSpace.isPerfect_canonicalDerivedTensorProduct X.toRingedSpace E F hE.1 hF.1,
    (cohomologySupportedOn_iff_supp_subset _ _).1
      (Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_left
        X.sheaf _ E F ((cohomologySupportedOn_iff_supp_subset _ _).2 hE.2))⟩

/-! ### The derived tensor product on `D_{Z,perf}(𝒪_X)` -/

/-- **The derived tensor product of `D_{Z,perf}(𝒪_X)`**: the derived tensor product of Stacks
06YU restricted to the perfect complexes supported on `Z`, which it preserves
(`AlgebraicGeometry.supportedPerfect_derivedTensor`). -/
def supportedPerfectTensor :
    supportedPerfectDerivedCategory i ⥤ supportedPerfectDerivedCategory i ⥤
      supportedPerfectDerivedCategory i :=
  K0.liftBifunctor _ (derivedTensorProductFunctor X.sheaf) fun _ _ hE hF ↦
    supportedPerfect_derivedTensor hE hF

/-- The underlying object of the derived tensor product in `D_{Z,perf}(𝒪_X)` is `E ⊗^L F`. -/
@[simp]
theorem supportedPerfectTensor_obj_obj (E F : supportedPerfectDerivedCategory i) :
    (((supportedPerfectTensor i).obj E).obj F).obj =
      ((derivedTensorProductFunctor X.sheaf).obj E.obj).obj F.obj :=
  rfl

/-- Tensoring with a fixed object of `D_{Z,perf}(𝒪_X)` on the left commutes with the shift. -/
@[instance_reducible]
def supportedPerfectTensorCommShiftRight (E : supportedPerfectDerivedCategory i) :
    ((supportedPerfectTensor i).obj E).CommShift ℤ :=
  @K0.liftBifunctorCommShiftRight _ _ _ _ _ _ _ _ (isTriangulated_supportedPerfect i)
    (derivedTensorProductFunctor X.sheaf) _
    (canonicalDerivedTensorProduct X.sheaf).commShift_right E

/-- Tensoring with a fixed object of `D_{Z,perf}(𝒪_X)` on the right commutes with the shift. -/
@[instance_reducible]
def supportedPerfectTensorCommShiftLeft (F : supportedPerfectDerivedCategory i) :
    ((supportedPerfectTensor i).flip.obj F).CommShift ℤ :=
  @K0.liftBifunctorCommShiftLeft _ _ _ _ _ _ _ _ (isTriangulated_supportedPerfect i)
    (derivedTensorProductFunctor X.sheaf) _
    (canonicalDerivedTensorProduct X.sheaf).commShift_left F

/-- Tensoring with a fixed object of `D_{Z,perf}(𝒪_X)` on the left is exact. -/
theorem supportedPerfectTensor_isTriangulatedRight (E : supportedPerfectDerivedCategory i) :
    letI := supportedPerfectTensorCommShiftRight i E
    ((supportedPerfectTensor i).obj E).IsTriangulated :=
  @K0.liftBifunctor_isTriangulatedRight _ _ _ _ _ _ _ _ (isTriangulated_supportedPerfect i)
    (derivedTensorProductFunctor X.sheaf) _
    (canonicalDerivedTensorProduct X.sheaf).commShift_right
    (canonicalDerivedTensorProduct X.sheaf).exact_right E

/-- Tensoring with a fixed object of `D_{Z,perf}(𝒪_X)` on the right is exact. -/
theorem supportedPerfectTensor_isTriangulatedLeft (F : supportedPerfectDerivedCategory i) :
    letI := supportedPerfectTensorCommShiftLeft i F
    ((supportedPerfectTensor i).flip.obj F).IsTriangulated :=
  @K0.liftBifunctor_isTriangulatedLeft _ _ _ _ _ _ _ _ (isTriangulated_supportedPerfect i)
    (derivedTensorProductFunctor X.sheaf) _
    (canonicalDerivedTensorProduct X.sheaf).commShift_left
    (canonicalDerivedTensorProduct X.sheaf).exact_left F

/-- The biadditive map of Stacks 0FCT for the derived tensor product of `D_{Z,perf}(𝒪_X)`. -/
theorem exists_supportedPerfectMul :
    ∃ b : K0 (supportedPerfectDerivedCategory i) →+ K0 (supportedPerfectDerivedCategory i) →+
        K0 (supportedPerfectDerivedCategory i),
      ∀ E F, b (K0.cls E) (K0.cls F) = K0.cls (((supportedPerfectTensor i).obj E).obj F) :=
  K0.exists_bilinear_of_bifunctor (supportedPerfectDerivedCategory i)
    (supportedPerfectDerivedCategory i) (supportedPerfectDerivedCategory i)
    (supportedPerfectTensor i) (supportedPerfectTensorCommShiftRight i)
    (supportedPerfectTensor_isTriangulatedRight i) (supportedPerfectTensorCommShiftLeft i)
    (supportedPerfectTensor_isTriangulatedLeft i)

/-- **The multiplication of `K₀(D_{Z,perf}(𝒪_X))`** of Remark 0FDN: the biadditive map induced
by the derived tensor product, exact in each variable, through Stacks 0FCT. -/
def supportedPerfectMul :
    K0 (supportedPerfectDerivedCategory i) →+ K0 (supportedPerfectDerivedCategory i) →+
      K0 (supportedPerfectDerivedCategory i) :=
  (exists_supportedPerfectMul i).choose

/-- The product of two classes is the class of the derived tensor product:
`[E] · [F] = [E ⊗^L F]`. -/
@[simp]
theorem supportedPerfectMul_cls (E F : supportedPerfectDerivedCategory i) :
    supportedPerfectMul i (K0.cls E) (K0.cls F) =
      K0.cls (((supportedPerfectTensor i).obj E).obj F) :=
  (exists_supportedPerfectMul i).choose_spec E F

/-- The derived tensor product of `D_{Z,perf}(𝒪_X)` is commutative on objects, by the braiding of
the tensor structure of `D(𝒪_X)`. -/
def supportedPerfectTensorBraiding (E F : supportedPerfectDerivedCategory i) :
    ((supportedPerfectTensor i).obj E).obj F ≅ ((supportedPerfectTensor i).obj F).obj E :=
  ObjectProperty.isoMk _
    ((RingedSpace.derivedTensorStructure X.toRingedSpace
      (canonicalDerivedTensorProduct X.sheaf)).braiding E.obj F.obj)

/-- The derived tensor product of `D_{Z,perf}(𝒪_X)` is associative on objects, by the associator
of the tensor structure of `D(𝒪_X)`. -/
def supportedPerfectTensorAssociator (E F G : supportedPerfectDerivedCategory i) :
    ((supportedPerfectTensor i).obj (((supportedPerfectTensor i).obj E).obj F)).obj G ≅
      ((supportedPerfectTensor i).obj E).obj (((supportedPerfectTensor i).obj F).obj G) :=
  ObjectProperty.isoMk _
    ((RingedSpace.derivedTensorStructure X.toRingedSpace
      (canonicalDerivedTensorProduct X.sheaf)).associator E.obj F.obj G.obj)

/-- Isomorphic derived tensor products give equal products of the classes of the factors. -/
private theorem supportedPerfectMul_cls_eq_of_iso {E F E' F' : supportedPerfectDerivedCategory i}
    (e : ((supportedPerfectTensor i).obj E).obj F ≅ ((supportedPerfectTensor i).obj E').obj F') :
    supportedPerfectMul i (K0.cls E) (K0.cls F) = supportedPerfectMul i (K0.cls E') (K0.cls F') :=
  (supportedPerfectMul_cls i E F).trans
    ((K0.cls_eq_of_iso e).trans (supportedPerfectMul_cls i E' F').symm)

/-- **The multiplication of `K₀(D_{Z,perf}(𝒪_X))` is commutative.** -/
theorem supportedPerfectMul_comm (a b : K0 (supportedPerfectDerivedCategory i)) :
    supportedPerfectMul i a b = supportedPerfectMul i b a := by
  have key : ∀ E : supportedPerfectDerivedCategory i, supportedPerfectMul i (K0.cls E) =
      (K0.evalHom (K0.cls E)).comp (supportedPerfectMul i) := fun E ↦
    K0.hom_ext fun F ↦ supportedPerfectMul_cls_eq_of_iso i (supportedPerfectTensorBraiding i E F)
  have h : (K0.evalHom b).comp (supportedPerfectMul i) = supportedPerfectMul i b :=
    K0.hom_ext fun E ↦ DFunLike.congr_fun (key E) b
  exact DFunLike.congr_fun h a

/-- **The multiplication of `K₀(D_{Z,perf}(𝒪_X))` is associative.** -/
theorem supportedPerfectMul_assoc (a b c : K0 (supportedPerfectDerivedCategory i)) :
    supportedPerfectMul i (supportedPerfectMul i a b) c =
      supportedPerfectMul i a (supportedPerfectMul i b c) := by
  have inner : ∀ E F : supportedPerfectDerivedCategory i,
      supportedPerfectMul i (supportedPerfectMul i (K0.cls E) (K0.cls F)) =
        (supportedPerfectMul i (K0.cls E)).comp (supportedPerfectMul i (K0.cls F)) := fun E F ↦
    K0.hom_ext fun G ↦
      (congrArg (fun x ↦ supportedPerfectMul i x (K0.cls G)) (supportedPerfectMul_cls i E F)).trans
        ((supportedPerfectMul_cls_eq_of_iso i (supportedPerfectTensorAssociator i E F G)).trans
          (congrArg (supportedPerfectMul i (K0.cls E)) (supportedPerfectMul_cls i F G).symm))
  have step : ∀ E : supportedPerfectDerivedCategory i,
      ((K0.evalHom c).comp (supportedPerfectMul i)).comp (supportedPerfectMul i (K0.cls E)) =
        (supportedPerfectMul i (K0.cls E)).comp ((K0.evalHom c).comp (supportedPerfectMul i)) :=
    fun E ↦ K0.hom_ext fun F ↦ DFunLike.congr_fun (inner E F) c
  have outer : ((K0.evalHom c).comp (supportedPerfectMul i)).comp
      ((K0.evalHom b).comp (supportedPerfectMul i)) =
        (K0.evalHom (supportedPerfectMul i b c)).comp (supportedPerfectMul i) :=
    K0.hom_ext fun E ↦ DFunLike.congr_fun (step E) b
  exact DFunLike.congr_fun outer a

/-- **Remark 0FDN: `K₀(D_{Z,perf}(𝒪_X))` is a commutative ring without unit** under the
multiplication induced by the derived tensor product, `[E] · [F] = [E ⊗^L F]`
(`AlgebraicGeometry.supportedPerfect_cls_mul_cls`). Its additive group is that of `K₀`. -/
instance supportedPerfectNonUnitalCommRing :
    NonUnitalCommRing (K0 (supportedPerfectDerivedCategory i)) where
  __ := (inferInstance : AddCommGroup (K0 (supportedPerfectDerivedCategory i)))
  mul a b := supportedPerfectMul i a b
  left_distrib a b c := (supportedPerfectMul i a).map_add b c
  right_distrib a b c := DFunLike.congr_fun ((supportedPerfectMul i).map_add a b) c
  zero_mul a := DFunLike.congr_fun (supportedPerfectMul i).map_zero a
  mul_zero a := (supportedPerfectMul i a).map_zero
  mul_assoc := supportedPerfectMul_assoc i
  mul_comm := supportedPerfectMul_comm i

/-- The product of `K₀(D_{Z,perf}(𝒪_X))` is `AlgebraicGeometry.supportedPerfectMul`. -/
theorem supportedPerfect_mul_def (a b : K0 (supportedPerfectDerivedCategory i)) :
    a * b = supportedPerfectMul i a b :=
  rfl

/-- `[E] · [F] = [E ⊗^L F]` in `K₀(D_{Z,perf}(𝒪_X))`. -/
theorem supportedPerfect_cls_mul_cls (E F : supportedPerfectDerivedCategory i) :
    K0.cls E * K0.cls F = K0.cls (((supportedPerfectTensor i).obj E).obj F) :=
  supportedPerfectMul_cls i E F

end AlgebraicGeometry
