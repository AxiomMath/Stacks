module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement

/-!
# The integral closure of the structure sheaf in a quasi-coherent algebra is quasi-coherent

Let `F` be an algebraic space over a scheme `S` and let `A` be a quasi-coherent sheaf of
commutative `𝒪_F`-algebras on its small étale site.  This file proves the two assertions
Stacks 0820 makes about the subalgebra
`AlgebraicGeometry.Space.AlgebraSheaf.integralClosureSheaf` of locally integral sections of `A`:
over an affine étale chart its sections are the integral closure of the ring of functions on the
chart in the sections of `A` there, and it is again quasi-coherent.

Both rest on one computation: for a morphism `V ⟶ U` of affine étale charts the ring map
`𝒪_F(U) → 𝒪_F(V)` is smooth, so forming the integral closure commutes with the base change
`A(V) = 𝒪_F(V) ⊗_{𝒪_F(U)} A(U)` that quasi-coherence of `A` provides.  Integrality of a section
over an affine chart then descends from a finite affine étale covering, along which the product
of the restriction maps of chart rings is faithfully flat, and the integral closure is cartesian
on affine charts, hence quasi-coherent.

## Main results

* `Stacks.isIntegral_iff_mem_range_lTensor`: the elements of `S ⊗[R] M` integral over `S` are
  the base change of the elements of `M` integral over `R`, for `S` a smooth `R`-algebra.
* `Stacks.isIntegral_of_bijective_tensor`: integrality descends along a finite family of smooth
  base changes whose product is faithfully flat.
* `Stacks.bijective_of_isIntegral_range`: the base change of the integral closure of `R` in `M`
  along a smooth `R`-algebra `T` is the integral closure of `T` in `T ⊗[R] M`.
* `AlgebraicGeometry.Space.AlgebraSheaf.isIntegralLocalOnAffineCharts_of_isQuasicoherent`: over
  an affine étale chart a locally integral section of a quasi-coherent algebra sheaf is integral
  over the structure sheaf.
* `AlgebraicGeometry.Space.AlgebraSheaf.range_integralClosureInclusion_app_eq_integralClosure'`:
  **the sections of the integral closure over an affine étale chart are the integral closure of
  the ring of functions on the chart in the sections of the algebra.**
* `AlgebraicGeometry.Space.AlgebraSheaf.isCartesianOnAffineCharts_integralClosureSheaf` and
  `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_integralClosureSheaf`: **the integral
  closure of the structure sheaf in a quasi-coherent algebra sheaf is quasi-coherent.**

## Implementation notes

The module universe is the universe of the schemes.  It is where Descent, Proposition 03DX(2)
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`) is available,
and that proposition is used in both directions: forwards, to present the sections of `A` over
a smaller affine chart as a base change, and backwards, to turn the resulting cartesian property
of the integral closure into quasi-coherence.

The algebra structures a chart puts on the sections of an algebra sheaf are named
(`AlgebraicGeometry.Space.chartSectionsAlgebra` and its two companions) rather than introduced by
`letI` at each use: `IsScalarTower` is keyed on its `SMul` components, and the base change
comparison `AlgebraicGeometry.Space.sectionsBaseChange` is a linear map, so the algebra
comparison has to be built separately and identified with it
(`AlgebraicGeometry.Space.chartSectionsBaseChangeAlgHom_apply`).

## References

* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03GE](https://stacks.math.columbia.edu/tag/03GE)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u

namespace Stacks

/-! ### Base change of the integral closure along a smooth algebra -/

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing M] [Algebra R M]

/-- The comparison map `S ⊗[R] integralClosure R M ⟶ integralClosure S (S ⊗[R] M)` is, after
forgetting that it lands in the integral closure, the base change of the inclusion of the
integral closure of `R` in `M`. -/
theorem coe_toIntegralClosure (z : S ⊗[R] integralClosure R M) :
    ((TensorProduct.toIntegralClosure R S M z : integralClosure S (S ⊗[R] M)) : S ⊗[R] M) =
      LinearMap.lTensor S (integralClosure R M).val.toLinearMap z := by
  induction z with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, ← hx, ← hy]; rfl
  | tmul t a => rfl

/-- **The integral closure commutes with a smooth base change.**  If `S` is a smooth `R`-algebra
and the elements of `M` integral over `R` are exactly the image of an `R`-module `P`, then the
elements of `S ⊗[R] M` integral over `S` are exactly the image of `S ⊗[R] P`. -/
theorem isIntegral_iff_mem_range_lTensor [Algebra.Smooth R S]
    {P : Type*} [AddCommGroup P] [Module R P] (ι : P →ₗ[R] M)
    (hι : ∀ x : M, IsIntegral R x ↔ x ∈ LinearMap.range ι) (y : S ⊗[R] M) :
    IsIntegral S y ↔ y ∈ LinearMap.range (LinearMap.lTensor S ι) := by
  have hrange : LinearMap.range (LinearMap.lTensor S ι) =
      LinearMap.range (LinearMap.lTensor S (integralClosure R M).val.toLinearMap) := by
    let ι' : P →ₗ[R] integralClosure R M :=
      { toFun := fun p => ⟨ι p, (mem_integralClosure_iff R M).2 ((hι (ι p)).2 ⟨p, rfl⟩)⟩
        map_add' := fun p q => Subtype.ext (map_add ι p q)
        map_smul' := fun r p => Subtype.ext (map_smul ι r p) }
    have hι'surj : Function.Surjective ι' := fun z =>
      (((hι z.1).1 ((mem_integralClosure_iff R M).1 z.2)).imp fun _ h => Subtype.ext h)
    have hcomp : (integralClosure R M).val.toLinearMap ∘ₗ ι' = ι := rfl
    rw [← hcomp, LinearMap.lTensor_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.2 (LinearMap.lTensor_surjective S hι'surj), Submodule.map_top]
  rw [hrange]
  refine ⟨fun hy => ?_, ?_⟩
  · obtain ⟨z, hz⟩ :=
      (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := M)).2 ⟨y, hy⟩
    exact ⟨z, by rw [← coe_toIntegralClosure, hz]⟩
  · rintro ⟨z, rfl⟩
    rw [← coe_toIntegralClosure]
    exact (mem_integralClosure_iff S (S ⊗[R] M)).1 (TensorProduct.toIntegralClosure R S M z).2

/-- **Integrality descends along a finite faithfully flat family of smooth base changes.**  If
the product of the structure maps of a finite family of smooth `R`-algebras `T i` is faithfully
flat and an element of `M` becomes integral in every `T i ⊗[R] M`, then it is integral
over `R`. -/
theorem isIntegral_of_isIntegral_tensor {ι : Type*} [Finite ι]
    (T : ι → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)] [∀ i, Algebra.Smooth R (T i)]
    (hff : (RingHom.pi fun i => algebraMap R (T i)).FaithfullyFlat)
    {x : M} (hx : ∀ i, IsIntegral (T i) ((1 : T i) ⊗ₜ[R] x)) : IsIntegral R x := by
  classical
  have _ := Fintype.ofFinite ι
  have _ : Module.FaithfullyFlat R (∀ i, T i) := RingHom.faithfullyFlat_algebraMap_iff.1 hff
  set P : Submodule R M := Subalgebra.toSubmodule (integralClosure R M) with hPdef
  have hval : ∀ x : M, IsIntegral R x ↔ x ∈ LinearMap.range P.subtype := fun x => by
    rw [Submodule.range_subtype, hPdef]
    exact (mem_integralClosure_iff R M).symm
  have hcomp : P.mkQ ∘ₗ P.subtype = 0 :=
    LinearMap.ext fun a => by simp
  have hzero : ∀ i, (Pi.single i (1 : T i)) ⊗ₜ[R] (P.mkQ x) = (0 : (∀ i, T i) ⊗[R] (M ⧸ P)) := by
    intro i
    obtain ⟨z, hz⟩ :=
      (isIntegral_iff_mem_range_lTensor P.subtype hval ((1 : T i) ⊗ₜ[R] x)).1 (hx i)
    have h1 : LinearMap.lTensor (T i) P.mkQ ((1 : T i) ⊗ₜ[R] x) = 0 := by
      rw [← hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomp]
      simp
    simpa using congrArg (LinearMap.rTensor (M ⧸ P) (LinearMap.single R T i)) h1
  have hsum : (1 : ∀ i, T i) ⊗ₜ[R] (P.mkQ x) = 0 := by
    have hone : (1 : ∀ i, T i) = ∑ i, Pi.single i (1 : T i) :=
      (Finset.univ_sum_single (M := T) fun _ => 1).symm
    rw [hone, TensorProduct.sum_tmul, Finset.sum_eq_zero fun i _ => hzero i]
  have hq := (Module.FaithfullyFlat.one_tmul_eq_zero_iff R (M ⧸ P) (A := ∀ i, T i) _).1 hsum
  rw [Submodule.mkQ_apply] at hq
  exact (hval x).2 (by rw [Submodule.range_subtype]; exact (Submodule.Quotient.mk_eq_zero P).1 hq)

/-- **Integrality descends along a finite faithfully flat family of smooth base changes**, in
the form in which the base changes are presented by algebra isomorphisms `T i ⊗[R] M ≅ D i`.
The element `y i` of `D i` the base change carries `x` to is given separately. -/
theorem isIntegral_of_bijective_tensor {ι : Type*} [Finite ι]
    (T : ι → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)] [∀ i, Algebra.Smooth R (T i)]
    (D : ι → Type*) [∀ i, CommRing (D i)] [∀ i, Algebra (T i) (D i)]
    (g : ∀ i, (T i) ⊗[R] M →ₐ[T i] D i) (hg : ∀ i, Function.Bijective (g i))
    (hff : (RingHom.pi fun i => algebraMap R (T i)).FaithfullyFlat)
    {x : M} {y : ∀ i, D i} (hy : ∀ i, g i ((1 : T i) ⊗ₜ[R] x) = y i)
    (hx : ∀ i, IsIntegral (T i) (y i)) : IsIntegral R x :=
  isIntegral_of_isIntegral_tensor T hff fun i =>
    (isIntegral_algHom_iff (g i) (hg i).1).1 ((hy i).symm ▸ hx i)

/-- **The base change of the integral closure is the integral closure of the base change.**  Let
`T` be a smooth `R`-algebra, let `M` be an `R`-algebra and `D` a `T`-algebra presented as
`T ⊗[R] M` by an algebra isomorphism `g`, and let `P` and `Q` present the elements integral over
`R` and over `T`.  Then the base change `T ⊗[R] P ⟶ Q` of the inclusion is bijective. -/
theorem bijective_of_isIntegral_range {T D P Q : Type*}
    [CommRing T] [Algebra R T] [Algebra.Smooth R T] [CommRing D] [Algebra T D]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module T Q]
    (ιP : P →ₗ[R] M) (hιP : Function.Injective ιP)
    (ιQ : Q →ₗ[T] D) (hιQ : Function.Injective ιQ)
    (hP : ∀ x : M, IsIntegral R x ↔ x ∈ LinearMap.range ιP)
    (hQ : ∀ y : D, IsIntegral T y ↔ y ∈ LinearMap.range ιQ)
    (g : T ⊗[R] M →ₐ[T] D) (hg : Function.Bijective g)
    (l : T ⊗[R] P →ₗ[T] Q)
    (hl : ∀ (t : T) (p : P), ιQ (l (t ⊗ₜ[R] p)) = g (t ⊗ₜ[R] ιP p)) :
    Function.Bijective l := by
  have hl : ∀ z, ιQ (l z) = g (LinearMap.lTensor T ιP z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul t p => simpa using hl t p
  refine ⟨fun z z' h => ?_, fun q => ?_⟩
  · refine Module.Flat.lTensor_preserves_injective_linearMap ιP hιP (hg.1 ?_)
    rw [← hl, ← hl, h]
  · obtain ⟨w, hw⟩ := hg.2 (ιQ q)
    obtain ⟨z, hz⟩ := (isIntegral_iff_mem_range_lTensor ιP hP w).1
      ((isIntegral_algHom_iff g hg.1).1 (hw ▸ (hQ (ιQ q)).2 ⟨q, rfl⟩))
    exact ⟨z, hιQ (by rw [hl, hz, hw])⟩

end Stacks

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-! ### The algebras of sections of an algebra sheaf over a chart -/

/-- The algebra structure the structure-algebra map of an algebra sheaf puts on its sections over
a chart.  Not an instance: it depends on the algebra sheaf. -/
@[instance_reducible]
noncomputable def chartSectionsAlgebra (A : AlgebraSheaf.{u, u} B S hS F hF)
    (U : SmallEtale B S hS F) :
    Algebra (chartRing B S hS F hF U) (A.right.obj.obj (op U)) :=
  (A.algebraMap (op U)).toAlgebra

/-- The algebra structure that the structure-algebra map of an algebra sheaf, composed with
restriction along `f : V ⟶ U`, puts on the sections over `V` as an algebra over the chart ring
of `U`.  Not an instance: it depends on `f`. -/
@[instance_reducible]
noncomputable def chartSectionsAlgebraOfHom (A : AlgebraSheaf.{u, u} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    Algebra (chartRing B S hS F hF U) (A.right.obj.obj (op V)) :=
  ((A.algebraMap (op V)).comp (chartRestrict f)).toAlgebra

/-- Restriction of the sections of an algebra sheaf along a morphism `f : V ⟶ U` of charts, as a
morphism of algebras over the chart ring of `U`. -/
noncomputable def chartRestrictAlgHom (A : AlgebraSheaf.{u, u} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    letI := chartSectionsAlgebra A U
    letI := chartSectionsAlgebraOfHom A f
    A.right.obj.obj (op U) →ₐ[chartRing B S hS F hF U] A.right.obj.obj (op V) :=
  letI := chartSectionsAlgebra A U
  letI := chartSectionsAlgebraOfHom A f
  { __ := (A.right.obj.map f.op).hom
    commutes' := fun r => A.algebraMap_natural f.op r }

/-- The base change comparison of the sections of an algebra sheaf along a morphism of charts, as
a morphism of algebras.  It is the comparison
`AlgebraicGeometry.Space.sectionsBaseChange` of the underlying module, remembering the
multiplication; see `AlgebraicGeometry.Space.chartSectionsBaseChangeAlgHom_apply`. -/
noncomputable def chartSectionsBaseChangeAlgHom (A : AlgebraSheaf.{u, u} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    letI := chartAlgebra (hF := hF) f
    letI := chartSectionsAlgebra A U
    letI := chartSectionsAlgebra A V
    TensorProduct (chartRing B S hS F hF U) (chartRing B S hS F hF V)
        (A.right.obj.obj (op U)) →ₐ[chartRing B S hS F hF V] A.right.obj.obj (op V) :=
  letI := chartAlgebra (hF := hF) f
  letI := chartSectionsAlgebra A U
  letI := chartSectionsAlgebra A V
  letI := chartSectionsAlgebraOfHom A f
  haveI : IsScalarTower (chartRing B S hS F hF U) (chartRing B S hS F hF V)
      (A.right.obj.obj (op V)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (chartRestrictAlgHom A f)
    fun _ _ => Commute.all _ _

/-- The algebra base change comparison of an algebra sheaf is the base change comparison of its
underlying module. -/
theorem chartSectionsBaseChangeAlgHom_apply (A : AlgebraSheaf.{u, u} B S hS F hF)
    {U V : SmallEtale B S hS F} (f : V ⟶ U) :
    letI := chartAlgebra (hF := hF) f
    ∀ z, chartSectionsBaseChangeAlgHom A f z = sectionsBaseChange A.underlyingModule f z := by
  let _ := chartAlgebra (hF := hF) f
  let _ := chartSectionsAlgebra A U
  let _ := chartSectionsAlgebra A V
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy =>
      exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
  | tmul b x => exact (chartBaseChange_tmul A.underlyingModule f b x).symm

/-! ### Smoothness of the chart rings of affine charts -/

/-- Restriction of regular functions along a morphism of affine étale charts is a smooth ring
map: the underlying morphism of affine schemes is étale, hence smooth. -/
theorem smooth_chartRestrict {U V : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (f : V ⟶ U) : (chartRestrict (hF := hF) f).Smooth := by
  have _ := hU
  have _ := hV
  have _ : Etale ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map f) :=
    etale_toScheme_toOver_map B S hS F f
  exact HasRingHomProperty.appTop (P := @Smooth)
    ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map f) inferInstance

/-- The chart ring of a smaller affine chart is a smooth algebra over the chart ring of the
larger one. -/
theorem smooth_chartAlgebra {U V : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V))
    (f : V ⟶ U) :
    letI := chartAlgebra (hF := hF) f
    Algebra.Smooth (chartRing B S hS F hF U) (chartRing B S hS F hF V) :=
  (smooth_chartRestrict hU hV f).toAlgebra

namespace AlgebraSheaf

/-! ### The sections of the integral closure over an affine chart -/

/-- The inclusion of the locally integral sections of an algebra sheaf over a chart into its
sections, as a morphism of modules over the chart ring. -/
noncomputable def locallyIntegralSectionsInclusion (A : AlgebraSheaf.{u, u} B S hS F hF)
    (U : SmallEtale B S hS F) :
    letI := chartSectionsAlgebra A U
    (integralClosureSheaf A).underlyingModule.val.obj (op U) →ₗ[chartRing B S hS F hF U]
      A.right.obj.obj (op U) :=
  letI := chartSectionsAlgebra A U
  { toFun := Subtype.val
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The image of the inclusion of the locally integral sections is the subring of locally
integral sections. -/
theorem range_locallyIntegralSectionsInclusion (A : AlgebraSheaf.{u, u} B S hS F hF)
    (U : SmallEtale B S hS F) {x : A.right.obj.obj (op U)} :
    letI := chartSectionsAlgebra A U
    x ∈ LinearMap.range (locallyIntegralSectionsInclusion A U) ↔
      x ∈ A.locallyIntegralSections (op U) :=
  ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- **Over an affine étale chart a locally integral section of a quasi-coherent algebra sheaf is
integral over the structure sheaf.** -/
theorem isIntegralLocalOnAffineCharts_of_isQuasicoherent (A : AlgebraSheaf.{u, u} B S hS F hF)
    (hA : A.IsQuasicoherent) : A.IsIntegralLocalOnAffineCharts := by
  intro U hU x hx
  obtain ⟨n, z, φ, haff, hmem, -, hpre⟩ :=
    SmallEtale.exists_finite_affine_etale_ofArrows_le B S hS F hU
      (mem_locallyIntegralSections.1 hx)
  obtain ⟨hcover, hetale⟩ := (Scheme.ofArrows_mem_precoverage_iff (P := @Etale.{u})).1 hpre
  let _ := chartSectionsAlgebra A U
  let _ : ∀ i, Algebra (chartRing B S hS F hF U) (chartRing B S hS F hF (z i)) :=
    fun i => chartAlgebra (hF := hF) (φ i)
  have _ : ∀ i, Algebra.Smooth (chartRing B S hS F hF U) (chartRing B S hS F hF (z i)) :=
    fun i => smooth_chartAlgebra (hF := hF) hU (haff i) (φ i)
  let _ : ∀ i, Algebra (chartRing B S hS F hF (z i)) (A.right.obj.obj (op (z i))) :=
    fun i => chartSectionsAlgebra A (z i)
  have _ := hU
  have _ : ∀ i, IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (z i)) :=
    haff
  have _ : ∀ i, Flat ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map (φ i)) :=
    fun i => (Etale.iff_flat_and_formallyUnramified.mp (hetale i)).1
  have hff : (RingHom.pi fun i =>
      Algebra.algebraMap (chartRing B S hS F hF U)
        (chartRing B S hS F hF (z i))).FaithfullyFlat :=
    AlgebraicGeometry.Scheme.faithfullyFlat_pi_appTop
      (fun i => (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (z i))
      (fun i => (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map (φ i)) hcover
  refine mem_integralSections.2 (Stacks.isIntegral_of_bijective_tensor
    (fun i => chartRing B S hS F hF (z i)) (fun i => A.right.obj.obj (op (z i)))
    (fun i => chartSectionsBaseChangeAlgHom A (φ i)) (fun i => ?_) hff
    (y := fun i => (A.right.obj.map (φ i).op).hom x) (fun i => ?_) fun i => ?_)
  · rw [funext (chartSectionsBaseChangeAlgHom_apply A (φ i))]
    exact isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF
      A.underlyingModule hA U (z i) hU (haff i) (φ i)
  · exact (chartSectionsBaseChangeAlgHom_apply A (φ i) _).trans
      (chartBaseChange_one_tmul A.underlyingModule (φ i) x)
  · exact mem_integralSections.1
      ((sieveOfSection_integralSubfunctor_apply A x (φ i)).1 (hmem i))

/-- The sections of the integral closure of the structure sheaf in a quasi-coherent algebra
sheaf over an affine étale chart are the integral closure of the ring of functions on the chart
in the sections of the algebra over it. -/
@[stacks 0820 "the sections of the integral closure over an affine chart"]
theorem range_integralClosureInclusion_app_eq_integralClosure'
    (A : AlgebraSheaf.{u, u} B S hS F hF) (hA : A.IsQuasicoherent) (U : SmallEtale B S hS F)
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    letI : Algebra ((structureSheaf B S hS F hF).obj.obj (op U))
        (A.right.obj.obj (op U)) := (A.algebraMap (op U)).toAlgebra
    Set.range (((integralClosureInclusion A).right.hom.app (op U)).hom) =
      (integralClosure ((structureSheaf B S hS F hF).obj.obj (op U))
        (A.right.obj.obj (op U)) : Set _) :=
  range_integralClosureInclusion_app_eq_integralClosure A
    (isIntegralLocalOnAffineCharts_of_isQuasicoherent A hA) U hU

/-! ### Quasi-coherence of the integral closure -/

/-- The locally integral sections of a quasi-coherent algebra sheaf over an affine chart are
exactly the sections integral over the structure sheaf. -/
theorem isIntegral_iff_mem_locallyIntegralSections (A : AlgebraSheaf.{u, u} B S hS F hF)
    (hA : A.IsQuasicoherent) {U : SmallEtale B S hS F}
    (hU : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U))
    (x : A.right.obj.obj (op U)) :
    letI := chartSectionsAlgebra A U
    _root_.IsIntegral (chartRing B S hS F hF U) x ↔
      x ∈ LinearMap.range (locallyIntegralSectionsInclusion A U) := by
  let _ := chartSectionsAlgebra A U
  rw [range_locallyIntegralSectionsInclusion]
  exact ⟨fun h => A.integralSections_le_locallyIntegralSections (op U) (mem_integralSections.2 h),
    fun h => mem_integralSections.1
      (isIntegralLocalOnAffineCharts_of_isQuasicoherent A hA U hU x h)⟩

/-- **The integral closure of the structure sheaf in a quasi-coherent algebra sheaf is cartesian
on affine charts.** -/
theorem isCartesianOnAffineCharts_integralClosureSheaf (A : AlgebraSheaf.{u, u} B S hS F hF)
    (hA : A.IsQuasicoherent) :
    IsCartesianOnAffineCharts (integralClosureSheaf A).underlyingModule := by
  intro U V hU hV f
  let _ := chartAlgebra (hF := hF) f
  let _ := chartSectionsAlgebra A U
  let _ := chartSectionsAlgebra A V
  have _ := smooth_chartAlgebra (hF := hF) hU hV f
  refine Stacks.bijective_of_isIntegral_range
    (locallyIntegralSectionsInclusion A U) Subtype.val_injective
    (locallyIntegralSectionsInclusion A V) Subtype.val_injective
    (isIntegral_iff_mem_locallyIntegralSections A hA hU)
    (isIntegral_iff_mem_locallyIntegralSections A hA hV)
    (chartSectionsBaseChangeAlgHom A f) ?_ (sectionsBaseChange _ f) fun b a => ?_
  · rw [funext (chartSectionsBaseChangeAlgHom_apply A f)]
    exact isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF
      A.underlyingModule hA U V hU hV f
  · rw [chartSectionsBaseChangeAlgHom_apply A f]
    rfl

/-- **Quasi-coherence of the integral closure.**  The integral closure of the structure sheaf in a
quasi-coherent sheaf of `𝒪_F`-algebras is again a quasi-coherent sheaf of `𝒪_F`-algebras. -/
@[stacks 0820 "quasi-coherence of the integral closure"]
theorem isQuasicoherent_integralClosureSheaf (A : AlgebraSheaf.{u, u} B S hS F hF)
    (hA : A.IsQuasicoherent) : (integralClosureSheaf A).IsQuasicoherent :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (isCartesianOnAffineCharts_integralClosureSheaf A hA)

end AlgebraSheaf

end AlgebraicGeometry.Space

end
