module

public import StacksFrontier.AlgebraicGeometry.Spaces.RetractionReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRightExact
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CoherentAdicLimitFactorization
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.GlobalSmulFunctoriality
public import StacksFrontier.Deformation.ModuleDeformation.CopowerExtension

/-!
# The extension attached to a module over a split square-zero thickening

Let `r : X' ⟶ X₀` be a representable morphism of algebraic spaces with a section `i`, and let
`M` be a finite-dimensional `k`-vector space together with a `k`-linear family `ι` of global
functions on `X'` with vanishing pairwise products, killed by `i`, and generating on every
affine chart the ideal of functions vanishing along `i`. This is the shape of
`X' = Spec k[M] ×_{Spec k} X₀` over `X₀`, with `ι` the pullback of the inclusion `M ⊂ k[M]`.

For a quasi-coherent `𝒪_{X'}`-module `ℱ` with an identification `ψ : i^*ℱ ≅ 𝒢`, multiplication
by `ι v` on `r_*ℱ` factors through the reduction `p : r_*ℱ ⟶ 𝒢` as `p ≫ μ v`, and when `ℱ` is
flat in the sense that a relation `∑ ι(b_j) n_j = 0` on an affine chart has every `n_j` in the
ideal of `i` times the sections, the sequence

`0 ⟶ 𝒢 ⊗ M ⟶ r_*ℱ ⟶ 𝒢 ⟶ 0`

is short exact: a `Deformation.ModuleDeformation.CopowerExtension`. This is the extension whose
class classifies the deformation `ℱ` in Stacks 08W8.

## Main definitions

* `AlgebraicGeometry.Space.retractionMultiplication`: multiplication by `ι v` on `r_*ℱ`.
* `AlgebraicGeometry.Space.retractionCopowerExtension`: the extension.

## Main results

* `AlgebraicGeometry.Space.exact_of_isAffine`: exactness of a short complex of modules on an
  algebraic space may be tested on the sections over affine charts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Exactness on affine charts -/

section Exactness

variable {X : AlgebraicSpaces B S hS}

/-- **Exactness in the middle of a short complex of `𝒪_F`-modules may be tested on affine
charts**: if over every affine chart every section killed by `g` comes from a section by `f`,
the short complex is exact. -/
theorem exact_of_isAffine (T : ShortComplex (Modules.{u, u} B S hS X.1 X.2))
    (h : ∀ V : SmallEtale B S hS X.1, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj V)) →
      ∀ x : T.X₂.val.obj (op V), T.g.val.app (op V) x = 0 →
        ∃ y : T.X₁.val.obj (op V), T.f.val.app (op V) y = x) : T.Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  refine epi_of_surjective_val_app_of_isAffine B S hS _ fun V hV z => ?_
  have hz : T.g.val.app (op V) ((kernel.ι T.g).val.app (op V) z) = 0 :=
    congrArg (fun φ => φ.val.app (op V) z) (kernel.condition T.g)
  obtain ⟨y, hy⟩ := h V hV _ hz
  refine ⟨y, Stacks.SheafOfModules.injective_val_app_of_mono (kernel.ι T.g) (op V) ?_⟩
  have := congrArg (fun φ => φ.val.app (op V) y) (kernel.lift_ι T.g T.f T.zero)
  exact this.trans hy

end Exactness

/-! ### Sections of finite biproducts -/

section Biproduct

variable {X : AlgebraicSpaces B S hS}

/-- A finite sum of morphisms of modules is computed sectionwise. -/
theorem sum_val_app {ι : Type*} (s : Finset ι) {M N : Modules.{u, u} B S hS X.1 X.2}
    (φ : ι → (M ⟶ N)) (V : (SmallEtale B S hS X.1)ᵒᵖ) (x : M.val.obj V) :
    (∑ j ∈ s, φ j).val.app V x = ∑ j ∈ s, (φ j).val.app V x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- The sections of a finite biproduct are the sums of their components. -/
theorem biproduct_section_eq_sum {J : Type} [Fintype J] (f : J → Modules.{u, u} B S hS X.1 X.2)
    (V : (SmallEtale B S hS X.1)ᵒᵖ) (z : (⨁ f).val.obj V) :
    z = ∑ j, (biproduct.ι f j).val.app V ((biproduct.π f j).val.app V z) := by
  have h := congrArg (fun φ => φ.val.app V z) (biproduct.total (f := f))
  simp only at h
  rw [sum_val_app] at h
  exact h.symm

/-- The value of `biproduct.desc` on a section. -/
theorem biproduct_desc_val_app {J : Type} [Fintype J] (f : J → Modules.{u, u} B S hS X.1 X.2)
    {N : Modules.{u, u} B S hS X.1 X.2} (g : ∀ j, f j ⟶ N) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : (⨁ f).val.obj V) :
    (biproduct.desc g).val.app V z = ∑ j, (g j).val.app V ((biproduct.π f j).val.app V z) := by
  conv_lhs => rw [biproduct_section_eq_sum B S hS f V z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := congrArg (fun φ => φ.val.app V ((biproduct.π f j).val.app V z))
    (biproduct.ι_desc g j)
  exact this

end Biproduct

/-! ### An algebra lemma -/

/-- An element killing every generator of an ideal kills that ideal times any module. -/
theorem smul_eq_zero_of_mem_span_smul_top {R N : Type*} [CommRing R] [AddCommGroup N]
    [Module R N] {T : Set R} {c : R} (hc : ∀ a ∈ T, c * a = 0) {x : N}
    (hx : x ∈ Ideal.span T • (⊤ : Submodule R N)) : c • x = 0 := by
  refine Submodule.smul_induction_on hx (fun a ha n _ => ?_) (fun a b ha hb => ?_)
  · rw [smul_smul]
    have : c * a = 0 := by
      refine Submodule.span_induction (p := fun a _ => c * a = 0) ?_ ?_ ?_ ?_ ha
      · exact hc
      · exact mul_zero _
      · intro a b _ _ ha hb
        rw [mul_add, ha, hb, add_zero]
      · intro d a _ ha
        rw [smul_eq_mul, mul_left_comm, ha, mul_zero]
    rw [this, zero_smul]
  · rw [smul_add, ha, hb, add_zero]

/-- An element of `span (range g) • N`, for a finite family `g`, is a combination `∑ g j • n j`. -/
theorem exists_sum_of_mem_span_range_smul_top {R N : Type*} [CommRing R] [AddCommGroup N]
    [Module R N] {J : Type*} [Fintype J] (g : J → R) {x : N}
    (hx : x ∈ Ideal.span (Set.range g) • (⊤ : Submodule R N)) :
    ∃ n : J → N, x = ∑ j, g j • n j := by
  classical
  refine Submodule.smul_induction_on hx (fun a ha n _ => ?_) (fun a b ha hb => ?_)
  · obtain ⟨c, hc⟩ := (Ideal.mem_span_range_iff_exists_fun).1 ha
    refine ⟨fun j => c j • n, ?_⟩
    rw [← hc, Finset.sum_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, mul_comm]
  · obtain ⟨n, rfl⟩ := ha
    obtain ⟨n', rfl⟩ := hb
    exact ⟨n + n', by simp [smul_add, Finset.sum_add_distrib]⟩

/-! ### The extension -/

section Extension

variable {X₀ X' : AlgebraicSpaces B S hS} (r : X' ⟶ X₀)
  (hrep : yoneda.relativelyRepresentable r.hom) (i : X₀ ⟶ X') (hi : i ≫ r = 𝟙 X₀)
  {k : Type u} [Field k] (M : FGModuleCat.{u} k)
  (ψ₀ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₀.1 X₀.2).O))
  (ψ' : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O))
  (ι : ↥M →+ Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O))

/-- **The hypotheses on a split square-zero thickening** `X'` of `X₀` by `M`: the base changes
of affine charts are affine, the pullback of functions along `i` on such charts is surjective
with kernel generated by the functions `ι v`, the products `ι v * ι w` vanish, `ι` is `k`-linear
for the scalars `ψ'`, and the scalars of `X'` are those of `X₀` pulled back along `r`. -/
structure IsSplitThickeningBy : Prop where
  isAffine : ∀ U : SmallEtale B S hS X₀.1,
    IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((SmallEtale.toOver B S hS X'.1 ⋙ BigFppfOver.toScheme B S hS).obj
        ((smallBaseChange B S hS r hrep).obj U))
  surjective : ∀ U : SmallEtale B S hS X₀.1,
    IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
      Function.Surjective
        (chartDiagramRestrict B S hS i (retractionChartDiagram B S hS r hrep i hi U))
  ker_eq : ∀ U : SmallEtale B S hS X₀.1,
    IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
      RingHom.ker (chartDiagramRestrict B S hS i (retractionChartDiagram B S hS r hrep i hi U)) =
        Ideal.span (Set.range fun v : ↥M =>
          (ι v).1 (op (retractionChartDiagram B S hS r hrep i hi U).V))
  mul_eq_zero : ∀ v w : ↥M, ι v * ι w = 0
  map_smul : ∀ (c : k) (v : ↥M), ι (c • v) = ψ' c * ι v
  scalars : ∀ (c : k) (U : SmallEtale B S hS X₀.1),
    (ψ' c).1 (op ((smallBaseChange B S hS r hrep).obj U)) =
      (smallBaseChangeSharp B S hS r hrep).hom.app (op U) ((ψ₀ c).1 (op U))

variable (F : Modules.{u, u} B S hS X'.1 X'.2) (G : Modules.{u, u} B S hS X₀.1 X₀.2)
  (ψ : (modulePullback B S hS i).obj F ≅ G)

/-- Multiplication by `ι v` on the direct image `r_*ℱ`. -/
def retractionMultiplication (v : ↥M) :
    (retractionPushforward B S hS r hrep).obj F ⟶ (retractionPushforward B S hS r hrep).obj F :=
  (retractionPushforward B S hS r hrep).map (Stacks.Cohomology.SiteModules.globalSmul _ (ι v) F)

/-- On the sections over `U`, multiplication by `ι v` on `r_*ℱ` is multiplication by the function
`ι v` on the base change of `U`. -/
theorem retractionMultiplication_app (v : ↥M) (U : SmallEtale B S hS X₀.1)
    (x : F.val.obj (op ((smallBaseChange B S hS r hrep).obj U))) :
    (retractionMultiplication B S hS r hrep M ι F v).val.app (op U) x =
      (ι v).1 (op ((smallBaseChange B S hS r hrep).obj U)) • x := rfl

/-- The direct image `r_*` is an additive functor. -/
instance : (retractionPushforward B S hS r hrep).Additive where
  map_add {F₁ F₂ f g} := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rfl

/-- The projection `r_*ℱ ⟶ 𝒢`: the reduction followed by the identification `ψ`. -/
def retractionProjection :
    (retractionPushforward B S hS r hrep).obj F ⟶ G :=
  reductionMap B S hS r hrep i hi F ≫ ψ.hom

variable {r hrep i hi M ψ₀ ψ' ι}
variable (hF : F.IsQuasicoherentOnSite) (h : IsSplitThickeningBy B S hS r hrep i hi M ψ₀ ψ' ι)

include hF h in
/-- The projection `r_*ℱ ⟶ 𝒢` is surjective on the sections over every affine chart. -/
theorem surjective_retractionProjection_app (U : SmallEtale B S hS X₀.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Function.Surjective ((retractionProjection B S hS r hrep i hi F G ψ).val.app (op U)) := by
  have h1 := surjective_reductionMap_app B S hS r hrep i hi F hF U hU (h.isAffine U hU)
    (h.surjective U hU)
  have h2 : Function.Surjective (ψ.hom.val.app (op U)) := fun y =>
    ⟨ψ.inv.val.app (op U) y, congrArg (fun φ => φ.val.app (op U) y) ψ.inv_hom_id⟩
  exact h2.comp h1

include hF h in
/-- **The projection `r_*ℱ ⟶ 𝒢` is an epimorphism.** -/
theorem epi_retractionProjection : Epi (retractionProjection B S hS r hrep i hi F G ψ) :=
  epi_of_surjective_val_app_of_isAffine B S hS _ fun W hW =>
    surjective_retractionProjection_app B S hS F G ψ hF h W hW

include hF h in
/-- The kernel of the projection on the sections over an affine chart: the ideal of `i` times
the sections. -/
theorem retractionProjection_app_eq_zero_iff (U : SmallEtale B S hS X₀.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (x : F.val.obj (op (retractionChartDiagram B S hS r hrep i hi U).V)) :
    (retractionProjection B S hS r hrep i hi F G ψ).val.app (op U) x = 0 ↔
      x ∈ (RingHom.ker (chartDiagramRestrict B S hS i
        (retractionChartDiagram B S hS r hrep i hi U))) •
          (⊤ : Submodule (chartRing B S hS X'.1 X'.2
              (retractionChartDiagram B S hS r hrep i hi U).V)
            (F.val.obj (op (retractionChartDiagram B S hS r hrep i hi U).V))) := by
  refine Iff.trans ?_ (reductionMap_app_eq_zero_iff B S hS r hrep i hi F hF U hU (h.isAffine U hU)
    (h.surjective U hU) x)
  have hinj : Function.Injective (ψ.hom.val.app (op U)) :=
    haveI : Mono ψ.hom := ⟨fun g g' e => by
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using congrArg (· ≫ ψ.inv) e⟩
    Stacks.SheafOfModules.injective_val_app_of_mono ψ.hom (op U)
  change ψ.hom.val.app (op U) ((reductionMap B S hS r hrep i hi F).val.app (op U) x) = 0 ↔ _
  exact ⟨fun h0 => hinj (h0.trans (map_zero _).symm), fun h0 => by rw [h0, map_zero]⟩

include hF h in
/-- **Multiplication by `ι v` kills the kernel of the projection.** -/
theorem kernel_ι_comp_retractionMultiplication (v : ↥M) :
    kernel.ι (retractionProjection B S hS r hrep i hi F G ψ) ≫
      retractionMultiplication B S hS r hrep M ι F v = 0 := by
  refine C1573.modules_hom_ext_of_isAffine B S hS X₀.1 X₀.2 fun V hV z => ?_
  let x : F.val.obj (op (retractionChartDiagram B S hS r hrep i hi V).V) :=
    (kernel.ι (retractionProjection B S hS r hrep i hi F G ψ)).val.app (op V) z
  have hx : (retractionProjection B S hS r hrep i hi F G ψ).val.app (op V) x = 0 :=
    congrArg (fun φ => φ.val.app (op V) z)
      (kernel.condition (retractionProjection B S hS r hrep i hi F G ψ))
  have hx' := (retractionProjection_app_eq_zero_iff B S hS F G ψ hF h V hV x).1 hx
  rw [h.ker_eq V hV] at hx'
  have key := smul_eq_zero_of_mem_span_smul_top
    (N := F.val.obj (op (retractionChartDiagram B S hS r hrep i hi V).V))
    (c := (ι v).1 (op (retractionChartDiagram B S hS r hrep i hi V).V)) (by
      rintro _ ⟨w, rfl⟩
      exact congrArg (fun t => t.1 (op (retractionChartDiagram B S hS r hrep i hi V).V))
        (h.mul_eq_zero v w)) hx'
  exact (retractionMultiplication_app B S hS r hrep M ι F v V x).trans key

/-- Multiplication by `ι v` on `r_*ℱ`, factored through the projection: `p ≫ μ v = ι v`. -/
def retractionMultiplicationFactor (v : ↥M) :
    G ⟶ (retractionPushforward B S hS r hrep).obj F :=
  haveI := epi_retractionProjection B S hS F G ψ hF h
  Abelian.epiDesc (retractionProjection B S hS r hrep i hi F G ψ)
    (retractionMultiplication B S hS r hrep M ι F v)
    (kernel_ι_comp_retractionMultiplication B S hS F G ψ hF h v)

/-- The factored multiplication satisfies `p ≫ μ v = ι v`. -/
theorem retractionProjection_comp_factor (v : ↥M) :
    retractionProjection B S hS r hrep i hi F G ψ ≫
      retractionMultiplicationFactor B S hS F G ψ hF h v =
        retractionMultiplication B S hS r hrep M ι F v := by
  have := epi_retractionProjection B S hS F G ψ hF h
  exact Abelian.comp_epiDesc _ _ _

/-- The `k`-linear structure on `𝒪_{X₀}`-modules given by the scalars `ψ₀`. -/
abbrev retractionLinear (ψ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X₀.1 X₀.2).O)) :
    Linear k (Modules.{u, u} B S hS X₀.1 X₀.2) :=
  Stacks.SheafOfModules.linearOver _ ψ

include h in
/-- The scalars of `X'` act on `r_*ℱ` as the scalars of `X₀`. -/
theorem retractionPushforward_map_globalSmul_scalar (c : k) :
    (retractionPushforward B S hS r hrep).map
        (Stacks.Cohomology.SiteModules.globalSmul _ (ψ' c) F) =
      Stacks.Cohomology.SiteModules.globalSmul _ (ψ₀ c)
        ((retractionPushforward B S hS r hrep).obj F) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let x' : F.val.obj (op ((smallBaseChange B S hS r hrep).obj U.unop)) := x
  exact congrArg (fun a => a • x') (h.scalars c U.unop)

/-- **The factored multiplications as a `k`-linear family.** -/
def retractionMultiplicationFamily :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    ↥M →ₗ[k] (G ⟶ (retractionPushforward B S hS r hrep).obj F) :=
  letI := retractionLinear B S hS (X₀ := X₀) ψ₀
  haveI := epi_retractionProjection B S hS F G ψ hF h
  { toFun := retractionMultiplicationFactor B S hS F G ψ hF h
    map_add' := fun v w => by
      apply (cancel_epi (retractionProjection B S hS r hrep i hi F G ψ)).1
      rw [Preadditive.comp_add, retractionProjection_comp_factor,
        retractionProjection_comp_factor, retractionProjection_comp_factor]
      change (retractionPushforward B S hS r hrep).map
          (Stacks.Cohomology.SiteModules.globalSmul _ (ι (v + w)) F) = _
      rw [map_add, Stacks.Cohomology.SiteModules.globalSmul_add, Functor.map_add]
      rfl
    map_smul' := fun c v => by
      apply (cancel_epi (retractionProjection B S hS r hrep i hi F G ψ)).1
      rw [retractionProjection_comp_factor, RingHom.id_apply, Linear.comp_smul]
      change (retractionPushforward B S hS r hrep).map
          (Stacks.Cohomology.SiteModules.globalSmul _ (ι (c • v)) F) =
        Stacks.Cohomology.SiteModules.globalSmul _ (ψ₀ c) _ ≫
          (retractionProjection B S hS r hrep i hi F G ψ ≫
            retractionMultiplicationFactor B S hS F G ψ hF h v)
      rw [retractionProjection_comp_factor, h.map_smul,
        Stacks.Cohomology.SiteModules.globalSmul_mul, Functor.map_comp,
        retractionPushforward_map_globalSmul_scalar B S hS F h]
      rfl }

/-- The `k`-linear family of factored multiplications takes `v` to `μ v`. -/
theorem retractionMultiplicationFamily_apply (v : ↥M) :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    retractionMultiplicationFamily B S hS F G ψ hF h v =
      retractionMultiplicationFactor B S hS F G ψ hF h v := rfl

include hF h in
/-- Multiplication by `ι v` followed by the projection vanishes. -/
theorem retractionMultiplication_comp_projection (v : ↥M) :
    retractionMultiplication B S hS r hrep M ι F v ≫
      retractionProjection B S hS r hrep i hi F G ψ = 0 := by
  refine C1573.modules_hom_ext_of_isAffine B S hS X₀.1 X₀.2 fun V hV x => ?_
  let x' : F.val.obj (op (retractionChartDiagram B S hS r hrep i hi V).V) := x
  have hmem : (ι v).1 (op (retractionChartDiagram B S hS r hrep i hi V).V) • x' ∈
      (RingHom.ker (chartDiagramRestrict B S hS i
        (retractionChartDiagram B S hS r hrep i hi V))) •
          (⊤ : Submodule (chartRing B S hS X'.1 X'.2
              (retractionChartDiagram B S hS r hrep i hi V).V)
            (F.val.obj (op (retractionChartDiagram B S hS r hrep i hi V).V))) := by
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [h.ker_eq V hV]
    exact Ideal.subset_span ⟨v, rfl⟩
  exact (retractionProjection_app_eq_zero_iff B S hS F G ψ hF h V hV _).2 hmem

include hF h in
/-- The factored multiplications are killed by the projection: `μ v ≫ p = 0`. -/
theorem retractionMultiplicationFactor_comp_projection (v : ↥M) :
    retractionMultiplicationFactor B S hS F G ψ hF h v ≫
      retractionProjection B S hS r hrep i hi F G ψ = 0 := by
  have := epi_retractionProjection B S hS F G ψ hF h
  apply (cancel_epi (retractionProjection B S hS r hrep i hi F G ψ)).1
  rw [← Category.assoc, retractionProjection_comp_factor, comp_zero,
    retractionMultiplication_comp_projection B S hS F G ψ hF h v]

include hF h in
/-- The factored multiplication on sections over a chart, at a section in the image of the
projection. -/
theorem retractionMultiplicationFactor_app_projection (v : ↥M) (U : SmallEtale B S hS X₀.1)
    (x : ((retractionPushforward B S hS r hrep).obj F).val.obj (op U)) :
    (retractionMultiplicationFactor B S hS F G ψ hF h v).val.app (op U)
        ((retractionProjection B S hS r hrep i hi F G ψ).val.app (op U) x) =
      (retractionMultiplication B S hS r hrep M ι F v).val.app (op U) x :=
  congrArg (fun φ => φ.val.app (op U) x) (retractionProjection_comp_factor B S hS F G ψ hF h v)

include h in
/-- The ideal of `i` on an affine chart is generated by the `ι` of a basis of `M`. -/
theorem ker_eq_span_basis (U : SmallEtale B S hS X₀.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    RingHom.ker (chartDiagramRestrict B S hS i (retractionChartDiagram B S hS r hrep i hi U)) =
      Ideal.span (Set.range fun j : Fin (Module.finrank k M) =>
        (ι (Deformation.ModuleDeformation.stdBasis M j)).1
          (op (retractionChartDiagram B S hS r hrep i hi U).V)) := by
  rw [h.ker_eq U hU]
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono ?_)
  · rintro _ ⟨v, rfl⟩
    change (ι v).1 _ ∈ _
    rw [← (Deformation.ModuleDeformation.stdBasis M).sum_repr v, map_sum]
    have hsum : ∀ (s : Finset (Fin (Module.finrank k M))),
        (∑ j ∈ s, ι ((Deformation.ModuleDeformation.stdBasis M).repr v j •
          Deformation.ModuleDeformation.stdBasis M j)).1
            (op (retractionChartDiagram B S hS r hrep i hi U).V) ∈
          Ideal.span (Set.range fun j : Fin (Module.finrank k M) =>
            (ι (Deformation.ModuleDeformation.stdBasis M j)).1
              (op (retractionChartDiagram B S hS r hrep i hi U).V)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact Submodule.zero_mem _
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        refine Submodule.add_mem _ ?_ ih
        rw [h.map_smul]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)
    exact hsum _
  · rintro _ ⟨j, rfl⟩
    exact ⟨_, rfl⟩

variable (hflat : ∀ U : SmallEtale B S hS X₀.1,
    IsAffine ((SmallEtale.toOver B S hS X₀.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
    ∀ n : Fin (Module.finrank k M) → F.val.obj (op (retractionChartDiagram B S hS r hrep i hi U).V),
      ∑ j, (ι (Deformation.ModuleDeformation.stdBasis M j)).1
          (op (retractionChartDiagram B S hS r hrep i hi U).V) • n j = 0 →
        ∀ j, n j ∈ (RingHom.ker (chartDiagramRestrict B S hS i
          (retractionChartDiagram B S hS r hrep i hi U))) •
            (⊤ : Submodule (chartRing B S hS X'.1 X'.2
                (retractionChartDiagram B S hS r hrep i hi U).V)
              (F.val.obj (op (retractionChartDiagram B S hS r hrep i hi U).V))))

open Deformation.ModuleDeformation in
include hF h in
/-- The map out of the copower on a section which is a sum of basis components in the image of
the projection. -/
theorem copowerDesc_app_sum (V : SmallEtale B S hS X₀.1)
    (n : Fin (Module.finrank k M) → ((retractionPushforward B S hS r hrep).obj F).val.obj (op V)) :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    (copowerDesc G (retractionMultiplicationFamily B S hS F G ψ hF h)).val.app (op V)
        (∑ j, (biproduct.ι (fun _ : Fin (Module.finrank k M) => G) j).val.app (op V)
          ((retractionProjection B S hS r hrep i hi F G ψ).val.app (op V) (n j))) =
      ∑ j, (retractionMultiplication B S hS r hrep M ι F (stdBasis M j)).val.app (op V) (n j) := by
  let := retractionLinear B S hS (X₀ := X₀) ψ₀
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e := congrArg (fun φ => φ.val.app (op V)
      ((retractionProjection B S hS r hrep i hi F G ψ).val.app (op V) (n j)))
    (ι_copowerDesc G (retractionMultiplicationFamily B S hS F G ψ hF h) j)
  exact e.trans (retractionMultiplicationFactor_app_projection B S hS F G ψ hF h _ V (n j))

open Deformation.ModuleDeformation in
include hF h hflat in
/-- **The map out of the copower is a monomorphism.** -/
theorem mono_copowerDesc_retractionMultiplicationFamily :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    Mono (copowerDesc G (retractionMultiplicationFamily B S hS F G ψ hF h)) := by
  let := retractionLinear B S hS (X₀ := X₀) ψ₀
  refine Abelian.mono_of_kernel_ι_eq_zero _ (C1573.modules_hom_ext_of_isAffine B S hS X₀.1 X₀.2
    fun V hV z => ?_)
  let y := (kernel.ι (copowerDesc G (retractionMultiplicationFamily B S hS F G ψ hF h))).val.app
    (op V) z
  have hy : (copowerDesc G (retractionMultiplicationFamily B S hS F G ψ hF h)).val.app (op V) y =
      0 :=
    congrArg (fun φ => φ.val.app (op V) z)
      (kernel.condition (copowerDesc G (retractionMultiplicationFamily B S hS F G ψ hF h)))
  have hsurj := surjective_retractionProjection_app B S hS F G ψ hF h V hV
  choose n hn using fun j : Fin (Module.finrank k M) =>
    hsurj ((biproduct.π (fun _ : Fin (Module.finrank k M) => G) j).val.app (op V) y)
  have hyeq : y = ∑ j, (biproduct.ι (fun _ : Fin (Module.finrank k M) => G) j).val.app (op V)
      ((retractionProjection B S hS r hrep i hi F G ψ).val.app (op V) (n j)) := by
    conv_lhs =>
      rw [biproduct_section_eq_sum B S hS (fun _ : Fin (Module.finrank k M) => G) (op V) y]
    exact Finset.sum_congr rfl fun j _ => congrArg _ (hn j).symm
  rw [hyeq, copowerDesc_app_sum B S hS F G ψ hF h V n] at hy
  have hrel := hflat V hV n hy
  have hzero : ∀ j, (retractionProjection B S hS r hrep i hi F G ψ).val.app (op V) (n j) = 0 :=
    fun j => (retractionProjection_app_eq_zero_iff B S hS F G ψ hF h V hV (n j)).2 (hrel j)
  change y = 0
  rw [hyeq]
  exact Finset.sum_eq_zero fun j _ => by rw [hzero j, map_zero]

open Deformation.ModuleDeformation in
include hF h in
/-- **Exactness in the middle**: the short complex `𝒢 ⊗ M ⟶ r_*ℱ ⟶ 𝒢` is exact. -/
theorem exact_copowerDesc_retractionProjection :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    (ShortComplex.mk (copowerDesc G (retractionMultiplicationFamily B S hS F G ψ hF h))
      (retractionProjection B S hS r hrep i hi F G ψ) (by
        refine biproduct.hom_ext' _ _ fun j => ?_
        rw [← Category.assoc, ι_copowerDesc, comp_zero]
        exact retractionMultiplicationFactor_comp_projection B S hS F G ψ hF h _)).Exact := by
  let := retractionLinear B S hS (X₀ := X₀) ψ₀
  apply exact_of_isAffine
  intro V hV x hx
  let x' : F.val.obj (op (retractionChartDiagram B S hS r hrep i hi V).V) := x
  have hx' := (retractionProjection_app_eq_zero_iff B S hS F G ψ hF h V hV x').1 hx
  rw [ker_eq_span_basis B S hS h V hV] at hx'
  obtain ⟨n, hn⟩ := exists_sum_of_mem_span_range_smul_top _ hx'
  refine ⟨∑ j, (biproduct.ι (fun _ : Fin (Module.finrank k M) => G) j).val.app (op V)
      ((retractionProjection B S hS r hrep i hi F G ψ).val.app (op V) (n j)), ?_⟩
  change (copowerDesc G (retractionMultiplicationFamily B S hS F G ψ hF h)).val.app (op V) _ = x
  rw [copowerDesc_app_sum B S hS F G ψ hF h V n]
  exact hn.symm

open Deformation.ModuleDeformation in
/-- **The extension `0 ⟶ 𝒢 ⊗ M ⟶ r_*ℱ ⟶ 𝒢 ⟶ 0` attached to a flat module over a split square-zero
thickening.** -/
def retractionCopowerExtension :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    CopowerExtension G M :=
  letI := retractionLinear B S hS (X₀ := X₀) ψ₀
  haveI := epi_retractionProjection B S hS F G ψ hF h
  haveI := mono_copowerDesc_retractionMultiplicationFamily B S hS F G ψ hF h hflat
  { E := (retractionPushforward B S hS r hrep).obj F
    p := retractionProjection B S hS r hrep i hi F G ψ
    μ := retractionMultiplicationFamily B S hS F G ψ hF h
    μ_p := retractionMultiplicationFactor_comp_projection B S hS F G ψ hF h
    shortExact := ShortComplex.ShortExact.mk'
      (exact_copowerDesc_retractionProjection B S hS F G ψ hF h)
      inferInstance inferInstance }

/-- The middle term of `retractionCopowerExtension` is `r_*ℱ`. -/
@[simp] theorem retractionCopowerExtension_E :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    (retractionCopowerExtension B S hS F G ψ hF h hflat).E =
      (retractionPushforward B S hS r hrep).obj F := rfl

/-- The projection of `retractionCopowerExtension` is `retractionProjection`. -/
@[simp] theorem retractionCopowerExtension_p :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    (retractionCopowerExtension B S hS F G ψ hF h hflat).p =
      retractionProjection B S hS r hrep i hi F G ψ := rfl

/-- The multiplication family of `retractionCopowerExtension` takes `v` to `μ v`. -/
theorem retractionCopowerExtension_μ (v : ↥M) :
    letI := retractionLinear B S hS (X₀ := X₀) ψ₀
    (retractionCopowerExtension B S hS F G ψ hF h hflat).μ v =
      retractionMultiplicationFactor B S hS F G ψ hF h v := rfl

end Extension

end AlgebraicGeometry.Space

end
