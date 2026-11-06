module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusHomFibres
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Quot.MatrixKernelRepresentable

/-!
# The kernel scheme of a matrix over an affine test scheme

Let `V` be an affine scheme of the big fppf site of `S` with `A = Γ(V, 𝒪_V)`, and let `b` be an
`n × m` matrix over `A`.  The closed subscheme `H = Spec A[x_1, …, x_m]/(∑_j b_{ij} x_j)` of
`𝐀^m_V` is affine and of finite presentation over `V`, and its points over `V` with values in a
test scheme `T ⟶ V` are the tuples `x ∈ Γ(T, 𝒪_T)^m` with `∑_j b_{ij} x_j = 0` for every `i`,
naturally in `T`.  This is the scheme through which the proof of Stacks 0DLC, part (3), represents
the functor `T ↦ Hom(L_T, 𝒪_T)` for a complex `L` presented by `𝒪^n ⟶ 𝒪^m` in degree zero.
Nothing is registered.

## Main results

* `AlgebraicGeometry.Space.exists_kernelScheme`: the scheme `H`, as an algebraic space affine and
  of finite presentation over `V`, with its points over `V`.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 064U](https://stacks.math.columbia.edu/tag/064U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory


namespace AlgebraicGeometry

section KernelScheme

open MvPolynomial

/-- The coordinate ring of the kernel of a matrix `b` with entries in `A`: the polynomial ring
over `A` in the `m` coordinates modulo the `n` linear forms `∑ j, b i j * X j`. -/
abbrev kernelCoordRing {A : Type u} [CommRing A] {m n : ℕ} (b : Fin n → Fin m → A) : Type u :=
  MvPolynomial (Fin m) A ⧸ Ideal.span (Set.range fun i => ∑ j, C (b i j) * X j)

/-- The global sections of `Y.toSpecΓ ≫ Spec.map σ` are `σ`, up to the identification of the
global sections of `Spec R` with `R`. -/
theorem appTop_toSpecΓ_comp_Spec_map (Y : Scheme.{u}) {R : CommRingCat.{u}} (σ : R ⟶ Γ(Y, ⊤)) :
    (Y.toSpecΓ ≫ Spec.map σ).appTop = (Scheme.ΓSpecIso R).hom ≫ σ := by
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]

variable {Z : Scheme.{u}} [IsAffine Z] {m n : ℕ} (b : Fin n → Fin m → Γ(Z, ⊤))

/-- The kernel scheme of a matrix `b` over the global sections of an affine scheme `Z`: the
spectrum of `kernelCoordRing b`, over `X`. -/
def kernelSchemeHom : Spec (.of (kernelCoordRing b)) ⟶ Z :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, ⊤) (kernelCoordRing b))) ≫ Z.isoSpec.inv

/-- The `j`-th coordinate function on the kernel scheme of a matrix. -/
def kernelSchemeCoord (j : Fin m) : Γ(Spec (.of (kernelCoordRing b)), ⊤) :=
  (Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ (X j))

/-- On global sections, the structure morphism of the kernel scheme is the algebra map of
`kernelCoordRing b`. -/
theorem kernelSchemeHom_appTop :
    (kernelSchemeHom b).appTop =
      CommRingCat.ofHom (algebraMap Γ(Z, ⊤) (kernelCoordRing b)) ≫ (Scheme.ΓSpecIso _).inv := by
  have h : Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(Z, ⊤)).hom, Iso.hom_inv_id, ← Scheme.toSpecΓ_appTop,
      ← Scheme.Hom.comp_appTop, Scheme.isoSpec_inv_toSpecΓ]
    rfl
  rw [kernelSchemeHom, Scheme.Hom.comp_appTop, h]
  exact (Scheme.ΓSpecIso_inv_naturality _).symm

variable {b} {Y : Scheme.{u}}

/-- A morphism into the kernel scheme lies over a morphism `t` to `Z` exactly when, on global
sections, it restricts to `t` along the algebra map of `kernelCoordRing b`. -/
theorem comp_kernelSchemeHom_eq_iff (f : Y ⟶ Spec (.of (kernelCoordRing b))) (t : Y ⟶ Z) :
    f ≫ kernelSchemeHom b = t ↔
      CommRingCat.ofHom (algebraMap Γ(Z, ⊤) (kernelCoordRing b)) ≫
        (Scheme.ΓSpecIso _).inv ≫ f.appTop = t.appTop := by
  refine ⟨fun h => h ▸ ?_, fun h => ext_of_isAffine ?_⟩
  all_goals rw [Scheme.Hom.comp_appTop, kernelSchemeHom_appTop, Category.assoc]
  exact h

omit [IsAffine Z] in
/-- The relations `∑ j, b i j * X j = 0` hold in `kernelCoordRing b`. -/
theorem sum_algebraMap_mul_mk_X_eq_zero (i : Fin n) :
    ∑ j, algebraMap Γ(Z, ⊤) (kernelCoordRing b) (b i j) * Ideal.Quotient.mk _ (X j) = 0 := by
  show ∑ j, Ideal.Quotient.mk _ (C (b i j)) * Ideal.Quotient.mk _ (X j) = 0
  simp only [← map_mul, ← map_sum]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

set_option synthInstance.maxHeartbeats 100000 in
/-- The coordinates of a point of the kernel scheme lying over `t` satisfy the equations of the
kernel of `b`, read through `t`. -/
theorem sum_appTop_mul_appTop_kernelSchemeCoord {f : Y ⟶ Spec (.of (kernelCoordRing b))}
    {t : Y ⟶ Z} (h : f ≫ kernelSchemeHom b = t) (i : Fin n) :
    ∑ j, t.appTop (b i j) * f.appTop (kernelSchemeCoord b j) = 0 := by
  rw [comp_kernelSchemeHom_eq_iff] at h
  have key : ∀ a, t.appTop a =
      f.appTop ((Scheme.ΓSpecIso _).inv (algebraMap _ (kernelCoordRing b) a)) := fun a => by
    rw [← h]
    rfl
  simp only [key, kernelSchemeCoord, ← map_mul, ← map_sum, sum_algebraMap_mul_mk_X_eq_zero,
    map_zero]

variable (b) in
/-- The coordinates of a point of the kernel scheme of `b` lying over `t : Y ⟶ Z`: a solution
in `Γ(Y, ⊤)` of the linear equations given by `b`, read through `t`. -/
def kernelSchemePoint (t : Y ⟶ Z)
    (f : {f : Y ⟶ Spec (.of (kernelCoordRing b)) // f ≫ kernelSchemeHom b = t}) :
    {x : Fin m → Γ(Y, ⊤) // ∀ i, ∑ j, t.appTop (b i j) * x j = 0} :=
  ⟨fun j => f.1.appTop (kernelSchemeCoord b j), sum_appTop_mul_appTop_kernelSchemeCoord f.2⟩

/-- A point of the kernel scheme lying over `t` is determined by its coordinates. -/
theorem injective_kernelSchemePoint (t : Y ⟶ Z) : Function.Injective (kernelSchemePoint b t) := by
  rintro ⟨f, hf⟩ ⟨f', hf'⟩ hxy
  rw [comp_kernelSchemeHom_eq_iff] at hf hf'
  apply Subtype.ext
  apply ext_of_isAffine
  have : (Scheme.ΓSpecIso _).inv ≫ f.appTop = (Scheme.ΓSpecIso _).inv ≫ f'.appTop := by
    ext1
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      exact congrArg (fun g : Γ(Z, ⊤) ⟶ Γ(Y, ⊤) => g a) (hf.trans hf'.symm)
    · intro j
      exact congrFun (congrArg Subtype.val hxy) j
  exact (cancel_epi _).1 this

/-- Every solution of the linear equations given by `b`, read through `t`, is the tuple of
coordinates of a point of the kernel scheme lying over `t`. -/
theorem surjective_kernelSchemePoint (t : Y ⟶ Z) :
    Function.Surjective (kernelSchemePoint b t) := by
  rintro ⟨x, hx⟩
  let τ : Γ(Z, ⊤) →+* Γ(Y, ⊤) := t.appTop.hom
  have hle : Ideal.span (Set.range fun i => ∑ j, C (b i j) * X j) ≤
      RingHom.ker (eval₂Hom τ x) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simpa [τ] using hx i
  let σ : kernelCoordRing b →+* Γ(Y, ⊤) := Ideal.Quotient.lift _ (eval₂Hom τ x) fun p hp => hle hp
  refine ⟨⟨Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom σ), ?_⟩, ?_⟩
  · rw [comp_kernelSchemeHom_eq_iff, appTop_toSpecΓ_comp_Spec_map, Iso.inv_hom_id_assoc]
    ext a
    show σ (Ideal.Quotient.mk _ (C a)) = τ a
    exact (Ideal.Quotient.lift_mk _ _ _).trans (eval₂Hom_C _ _ _)
  · apply Subtype.ext
    funext j
    show (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom σ)).appTop
      ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ (X j))) = x j
    rw [appTop_toSpecΓ_comp_Spec_map]
    show σ ((Scheme.ΓSpecIso (.of (kernelCoordRing b))).hom
      ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ (X j)))) = x j
    rw [Iso.inv_hom_id_apply]
    exact (Ideal.Quotient.lift_mk _ _ _).trans (eval₂Hom_X' _ _ _)

/-- **The points of the kernel scheme.** The morphisms `Y ⟶ Spec (kernelCoordRing b)` over a
morphism `t : Y ⟶ Z` correspond, through their coordinates, to the solutions in `Γ(Y, ⊤)` of the
linear equations given by `b`, read through `t`. -/
theorem bijective_kernelSchemePoint (t : Y ⟶ Z) : Function.Bijective (kernelSchemePoint b t) :=
  ⟨injective_kernelSchemePoint t, surjective_kernelSchemePoint t⟩

variable (b) in
/-- The kernel scheme of a matrix is of finite presentation over its base: its coordinate ring
is a polynomial ring in finitely many variables modulo finitely many relations. -/
theorem finitePresentation_kernelSchemeHom : FinitePresentation (kernelSchemeHom b) := by
  have hfp : Algebra.FinitePresentation Γ(Z, ⊤) (kernelCoordRing b) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  have : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(Z, ⊤) (kernelCoordRing b)))) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finitePresentation_algebraMap.2 hfp)
  have : LocallyOfFinitePresentation (kernelSchemeHom b) := by
    unfold kernelSchemeHom
    infer_instance
  exact ⟨this, inferInstance, inferInstance⟩

end KernelScheme

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A point over `V` of the algebraic space of `H`, read as a morphism of the site, lies over
the structure morphism of the test scheme. -/
theorem comp_eq_testMap_of_spacePointsOverObj {H V : BigFppfOver B S hS} (p₀ : H ⟶ V)
    {T : SchemesOver ((schemeSpaceFunctor B S hS).obj V)}
    (x : spacePointsOverObj ((schemeSpaceFunctor B S hS).map p₀) T) :
    (x.1 : T.left ⟶ H) ≫ p₀ = testMap T :=
  x.2.trans (testPoint_eq_testMap T)

/-- **Points over `V` of a morphism of the site are morphisms of schemes over `V`.** For a
morphism `p₀ : H ⟶ V` of the big fppf category over `S`, the points over the algebraic space of
`V` of the algebraic space of `H`, at a test scheme `T`, are the morphisms of underlying schemes
from `T` to `H` lying over the structure morphism of `T`. -/
def spacePointsOverObjEquiv {H V : BigFppfOver B S hS} (p₀ : H ⟶ V)
    (T : SchemesOver ((schemeSpaceFunctor B S hS).obj V)) :
    spacePointsOverObj ((schemeSpaceFunctor B S hS).map p₀) T ≃
      {f : (BigFppfOver.toScheme B S hS).obj T.left ⟶ (BigFppfOver.toScheme B S hS).obj H //
        f ≫ (BigFppfOver.toScheme B S hS).map p₀ =
          (BigFppfOver.toScheme B S hS).map (testMap T)} where
  toFun x := ⟨(BigFppfOver.toScheme B S hS).map (x.1 : T.left ⟶ H),
    ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map (comp_eq_testMap_of_spacePointsOverObj p₀ x))⟩
  invFun f := ⟨BigFppfOver.homOfCompEq B S hS f.1
      (comp_inclusion_map_hom_of_comp_eq p₀ (testMap T) _ f.2), by
    change _ ≫ p₀ = testPoint T
    rw [testPoint_eq_testMap]
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq]
    exact f.2⟩
  left_inv x := Subtype.ext ((BigFppfOver.toScheme B S hS).map_injective
    (BigFppfOver.toScheme_map_homOfCompEq B S hS _
      (comp_inclusion_map_hom_of_comp_eq p₀ (testMap T) _
        (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans (congrArg
          (BigFppfOver.toScheme B S hS).map (comp_eq_testMap_of_spacePointsOverObj p₀ x))))))
  right_inv f := Subtype.ext (BigFppfOver.toScheme_map_homOfCompEq B S hS _
    (comp_inclusion_map_hom_of_comp_eq p₀ (testMap T) _ f.2))

/-- **The kernel scheme of a matrix over an affine test scheme.**  For an affine scheme `V` of
the site and an `n × m` matrix `b` over `Γ(V, 𝒪_V)` there is an algebraic space `H` affine and of
finite presentation over `V` whose points over `V` at a test scheme `T` are the tuples
`x ∈ Γ(T, 𝒪_T)^m` solving `∑_j b_{ij} x_j = 0`, naturally in `T`. -/
theorem exists_kernelScheme (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) {m n : ℕ}
    (b : Fin n → Fin m → Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    ∃ (H : AlgebraicSpaces B S hS) (p : H ⟶ (schemeSpaceFunctor B S hS).obj V),
      IsAffineHom B S hS p.hom ∧ IsFinitePresentation B S hS p.hom ∧
      ∃ φ : ∀ T : SchemesOver ((schemeSpaceFunctor B S hS).obj V),
          spacePointsOverObj p T ≃
            {x : Fin m → Γ((BigFppfOver.toScheme B S hS).obj T.left, ⊤) //
              ∀ i, ∑ j, ((BigFppfOver.toScheme B S hS).map (testMap T)).appTop (b i j) * x j = 0},
        ∀ {T T' : SchemesOver ((schemeSpaceFunctor B S hS).obj V)} (g : T' ⟶ T)
          (x : spacePointsOverObj p T),
          (φ T' ((spacePointsOver p).map g.op x)).1 =
            fun j => ((BigFppfOver.toScheme B S hS).map g.left).appTop ((φ T x).1 j) := by
  have := hV
  have hfp := finitePresentation_kernelSchemeHom b
  have : LocallyOfFinitePresentation (kernelSchemeHom b) := hfp.1
  have hH : B.Contains (Spec (.of (kernelCoordRing b))) :=
    (Scheme.size_le_of_locallyOfFiniteType (kernelSchemeHom b)).trans_lt V.left.2
  let Hobj : BigFppfOver B S hS :=
    BigFppfOver.mk B S hS hH (kernelSchemeHom b ≫ B.inclusion.map V.hom)
  let p₀ : Hobj ⟶ V := BigFppfOver.homOfCompEq B S hS (kernelSchemeHom b) rfl
  have hp₀ : (BigFppfOver.toScheme B S hS).map p₀ = kernelSchemeHom b :=
    BigFppfOver.toScheme_map_homOfCompEq B S hS _ _
  refine ⟨(schemeSpaceFunctor B S hS).obj Hobj, (schemeSpaceFunctor B S hS).map p₀, ?_, ?_,
    fun T => ((spacePointsOverObjEquiv p₀ T).trans (Equiv.subtypeEquivRight fun f => by
      rw [hp₀]; exact Iff.rfl)).trans (Equiv.ofBijective _ (bijective_kernelSchemePoint _)), ?_⟩
  · rw [schemeSpaceFunctor_map_hom]
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj Hobj) :=
      inferInstanceAs (IsAffine (Spec (.of (kernelCoordRing b))))
    exact isAffineHom_yoneda_map B S hS p₀
  · rw [schemeSpaceFunctor_map_hom]
    exact isFinitePresentation_yoneda_map B S hS p₀ (by rwa [hp₀])
  · intro T T' g x
    funext j
    have e := congrArg (fun h => h.appTop (kernelSchemeCoord b j))
      ((BigFppfOver.toScheme B S hS).map_comp g.left (show T.left ⟶ Hobj from x.1))
    refine e.trans ?_
    simp only [Scheme.Hom.comp_appTop]
    rfl

end AlgebraicGeometry.Space

end
