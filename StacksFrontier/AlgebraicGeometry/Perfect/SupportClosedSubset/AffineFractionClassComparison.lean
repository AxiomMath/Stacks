module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AffineFractionClass
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionMap

/-!
# The affine description of the fraction class map

Let `A` be a commutative ring, let `f₁, …, f_c ∈ A` be a finite nonempty family and let `M` be an
`A`-module.  Tag 0G7R asserts that the map `c_{f₁,…,f_c}` of Tag 0G7Q, for `X = Spec A` and
`ℱ = M~`, **can be described as** the map

`M/(f₁,…,f_c)M ⟶ Coker(⨁ᵢ M_{f₁⋯f̂ᵢ⋯f_c} ⟶ M_{f₁⋯f_c})`

of `Cech.supportedFraction`.  Tag 0G7Q's map, in the cokernel-to-cokernel presentation the
example uses, is `Stacks.Perfect.SupportedFraction.supportedFractionClass`, a morphism

`Coker((f₁,…,f_c) : ℱ^{⊕c} ⟶ ℱ) ⟶ Coker(lastDif f ℱ)`

of `𝒪_X`-modules.  Identifying the two therefore needs two `A`-linear isomorphisms between the
global sections of those cokernels and the two algebraic modules.  This file builds the
**source** isomorphism and shows that, given **any** target comparison normalised on fractions,
the global sections of Tag 0G7Q's map are `Cech.supportedFraction`.

## Main definitions

* `Stacks.Perfect.AffineFractionClass.specFun`: the family of global functions on `Spec R`
  belonging to a family of elements of `R`.
* `Stacks.Perfect.AffineFractionClass.affineSourceSection`: the canonical `R`-linear map sending a
  section `s` of `M` to the class of `s` in `Γ(Spec R, Coker((f₁,…,f_c) : (M~)^{⊕c} ⟶ M~))`.
* `Stacks.Perfect.AffineFractionClass.affineSourceComparison`: **the source comparison**, the map
  `M/(f₁,…,f_c)M ⟶ Γ(Spec R, Coker((f₁,…,f_c) : (M~)^{⊕c} ⟶ M~))` it induces, and
  `Stacks.Perfect.AffineFractionClass.affineSourceEquiv`, the same map as an isomorphism.
* `Stacks.Perfect.AffineFractionClass.equationsMul`, `sigmaTildeComparison`,
  `sourceCokernelIso`: the algebraic multiplication map `M^{⊕c} ⟶ M`, the coproduct comparison,
  and the resulting identification `Coker((f₁,…,f_c) : (M~)^{⊕c} ⟶ M~) ≅ (M/(f₁,…,f_c)M)~`.

## Main results

* `Stacks.Perfect.AffineFractionClass.globalSmul_app_top`: on global sections, multiplication by a
  global function is multiplication by that function.
* `Stacks.Perfect.AffineFractionClass.globalSmul_comp_cokernelπ`: multiplication by one equation is
  killed by the cokernel of multiplication by the whole family.
* `Stacks.Perfect.AffineFractionClass.tilde_hom_ext` and
  `Stacks.Perfect.AffineFractionClass.tilde_map_app_top`: morphisms of associated sheaves are
  determined by their effect on the global sections coming from the module.
* `Stacks.Perfect.AffineFractionClass.globalSmul_eq_tilde_map`: multiplication by the global
  function belonging to `a : R` on `M~` is the associated sheaf of multiplication by `a`.
* `Stacks.Perfect.AffineFractionClass.equationsMultiplication_eq`: consequently Tag 0G7Q's source
  map `(f₁,…,f_c) : (M~)^{⊕c} ⟶ M~` is the associated sheaf of the algebraic multiplication map,
  precomposed with the coproduct comparison, which
  `Stacks.Perfect.AffineFractionClass.isIso_sigmaTildeComparison` shows is an isomorphism.
* `Stacks.Perfect.AffineFractionClass.bijective_affineSourceComparison`: **the source comparison
  is bijective** — right exactness of `Γ(Spec R, -)` here, obtained from the exactness of
  `M ↦ M~` rather than from any vanishing theorem.
* `Stacks.Perfect.AffineFractionClass.supportedFraction_eq_of_targetComparison`: **the reduction.**
  For any `R`-linear `τ` from the algebraic cokernel to the global sections of
  `Coker(lastDif)` which carries the class of the fraction `s/(f₁⋯f_c)` to the class of the
  sheaf-theoretic fraction, the global sections of `supportedFractionClass`, read through the
  source comparison and through `τ`, are `Cech.supportedFraction`.
* `Stacks.Perfect.AffineFractionClass.supportedFraction_ne_zero` and
  `supportedFraction_int_two_ne_zero`: **non-degeneracy.**  For a single equation which is a
  nonzero non-unit of a domain, for instance `A = ℤ`, `f = ![2]`, `M = ℤ`,
  `Cech.supportedFraction` is not the zero map.

## Implementation notes

The target comparison, the hypothesis `τ` of
`Stacks.Perfect.AffineFractionClass.supportedFraction_eq_of_targetComparison`, is
`Stacks.Perfect.AffineFractionClass.targetComparison`; it is bijective by
`Stacks.Perfect.AffineFractionClass.bijective_targetComparison`, and clause 3 of Tag 0G7R is
`Stacks.Perfect.AffineFractionClass.supportedFraction_eq_conj`.

`tilde X` / `tilde.map φ` and `(tilde.functor R).obj X` / `.map φ` are definitionally equal, but
`cokernelIsoOfEq`, `cokernelEpiComp` and `PreservesCokernel.iso` are stated in the functor
spelling while `equationsMultiplication` is applied at `tilde M`, and `rw` does not cross the
two; `π_comp_tildeCokernelIso_hom` states the crossing once.

## References

* [Stacks Project, Tag 0G7R](https://stacks.math.columbia.edu/tag/0G7R)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Perfect.SupportedFraction
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AffineFractionClass

variable {R : CommRingCat.{u}} {d : ℕ}

/-- The family of global functions on `Spec R` determined by a family of elements of `R`. -/
public def specFun (f : Fin (d + 1) → R) : Fin (d + 1) → Γ(Spec R, ⊤) :=
  fun i => (Scheme.ΓSpecIso R).inv (f i)

/-! ### Multiplication by a global function on global sections -/

/-- On global sections, multiplication by a global function of the structure sheaf is
multiplication by that function. -/
public theorem globalSmul_app_top {X : Scheme.{u}} (r : Γ(X, ⊤)) (F : X.Modules)
    (z : Γ(F, ⊤)) :
    (globalSmul r F).app ⊤ z = r • z := by
  rw [globalSmul_app]
  congr 1
  have h : (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)) = 𝟙 (⊤ : X.Opens) :=
    Subsingleton.elim _ _
  rw [h]
  simp

/-- Multiplication by one of the equations is killed by the projection to the cokernel of
multiplication by the whole family. -/
public theorem globalSmul_comp_cokernelπ {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (F : X.Modules) (i : Fin c) :
    globalSmul (f i) F ≫ cokernel.π (equationsMultiplication f F) = 0 := by
  have hι : Sigma.ι (fun _ : Fin c => F) i ≫ equationsMultiplication f F = globalSmul (f i) F :=
    Sigma.ι_desc _ _
  rw [← hι, Category.assoc, cokernel.condition, comp_zero]

/-! ### Morphisms between associated sheaves -/

/-- A morphism of modules and the morphism of associated sheaves it induces agree on global
sections, under `tilde.isoTop`.  This is the naturality of the unit of the tilde–`Γ`
adjunction, read on elements. -/
public theorem tilde_map_app_top {M N : ModuleCat.{u} R} (φ : M ⟶ N) (s : M) :
    (tilde.map φ).app ⊤ ((tilde.isoTop M).hom s) = (tilde.isoTop N).hom (φ s) :=
  congrFun (congrArg (fun ψ : M ⟶ moduleSpecΓFunctor.obj (tilde N) =>
    (ConcreteCategory.hom ψ : M → _)) (tilde.toOpen_map_app φ ⊤)) s

/-- Two morphisms of associated sheaves are equal as soon as they agree on the global sections
coming from the module. -/
public theorem tilde_hom_ext {M N : ModuleCat.{u} R} {φ ψ : tilde M ⟶ tilde N}
    (h : ∀ s : M, φ.app ⊤ ((tilde.isoTop M).hom s) = ψ.app ⊤ ((tilde.isoTop M).hom s)) :
    φ = ψ := by
  obtain ⟨φ', rfl⟩ := (tilde.functor R).map_surjective φ
  obtain ⟨ψ', rfl⟩ := (tilde.functor R).map_surjective ψ
  refine congrArg (tilde.functor R).map ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  refine (ConcreteCategory.mono_iff_injective_of_preservesPullback (tilde.isoTop N).hom).mp
    inferInstance ?_
  exact ((tilde_map_app_top φ' s).symm.trans (h s)).trans (tilde_map_app_top ψ' s)

/-- Multiplication by the global function belonging to `a : R` sends the global section of `M~`
determined by `s` to the one determined by `a • s`. -/
private theorem globalSmul_app_top_isoTop (a : R) (M : ModuleCat.{u} R) (s : M) :
    (globalSmul ((Scheme.ΓSpecIso R).inv a) (tilde M)).app ⊤ ((tilde.isoTop M).hom s) =
      (tilde.isoTop M).hom (a • s) :=
  (globalSmul_app_top _ _ _).trans (map_smul (tilde.isoTop M).hom.hom a s).symm

/-- **Multiplication by an equation is the associated sheaf of multiplication.**  On `M~` over
`Spec R`, multiplication by the global function belonging to `a : R` is `tilde.map` of
multiplication by `a` on `M`. -/
public theorem globalSmul_eq_tilde_map (a : R) (M : ModuleCat.{u} R) :
    globalSmul ((Scheme.ΓSpecIso R).inv a) (tilde M) =
      tilde.map (ModuleCat.ofHom (a • LinearMap.id : M →ₗ[R] M)) := by
  refine tilde_hom_ext fun s => ?_
  exact (globalSmul_app_top_isoTop a M s).trans
    (tilde_map_app_top (ModuleCat.ofHom (a • LinearMap.id : M →ₗ[R] M)) s).symm

/-- The algebraic multiplication map `(f₁,…,f_c) : M^{⊕c} ⟶ M` whose cokernel is
`M/(f₁,…,f_c)M`. -/
public def equationsMul (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    (∐ fun _ : Fin (d + 1) => M) ⟶ M :=
  Sigma.desc fun i => ModuleCat.ofHom (f i • LinearMap.id : M →ₗ[R] M)

private theorem ι_comp_equationsMul (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (i : Fin (d + 1)) :
    Sigma.ι (fun _ : Fin (d + 1) => M) i ≫ equationsMul f M =
      ModuleCat.ofHom (f i • LinearMap.id : M →ₗ[R] M) :=
  Sigma.ι_desc _ _

/-- The comparison between a coproduct of associated sheaves and the associated sheaf of the
coproduct. -/
public def sigmaTildeComparison (M : ModuleCat.{u} R) :
    (∐ fun _ : Fin (d + 1) => tilde M) ⟶ tilde (∐ fun _ : Fin (d + 1) => M) :=
  Sigma.desc fun i => tilde.map (Sigma.ι (fun _ : Fin (d + 1) => M) i)

/-- **Tag 0G7Q's source map is the associated sheaf of the algebraic one.**  Multiplication by
the family of equations on `M~` is `tilde.map` of multiplication by the family on `M`,
precomposed with the coproduct comparison. -/
public theorem equationsMultiplication_eq (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    equationsMultiplication (specFun f) (tilde M) =
      sigmaTildeComparison M ≫ tilde.map (equationsMul f M) := by
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [equationsMultiplication, Sigma.ι_desc, ← Category.assoc, sigmaTildeComparison, Sigma.ι_desc]
  refine (globalSmul_eq_tilde_map (f i) M).trans ?_
  refine Eq.trans (congrArg (tilde.functor R).map (ι_comp_equationsMul f M i).symm) ?_
  exact (tilde.functor R).map_comp (Sigma.ι (fun _ : Fin (d + 1) => M) i) (equationsMul f M)

/-- The coproduct comparison is an isomorphism: `tilde.functor` is a left adjoint, hence
preserves colimits. -/
public instance isIso_sigmaTildeComparison (M : ModuleCat.{u} R) :
    IsIso (sigmaTildeComparison (d := d) M) := by
  have hc : IsColimit (Cofan.mk (tilde (∐ fun _ : Fin (d + 1) => M))
      (fun i => tilde.map (Sigma.ι (fun _ : Fin (d + 1) => M) i))) :=
    isColimitMapCoconeCofanMkEquiv (tilde.functor R) _ _
      (isColimitOfPreserves (tilde.functor R) (coproductIsCoproduct _))
  have heq : sigmaTildeComparison (d := d) M =
      (IsColimit.coconePointUniqueUpToIso
        (coproductIsCoproduct (fun _ : Fin (d + 1) => tilde M)) hc).hom := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [sigmaTildeComparison, Sigma.ι_desc]
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (coproductIsCoproduct (fun _ : Fin (d + 1) => tilde M)) hc ⟨i⟩).symm
  rw [heq]
  infer_instance

/-! ### The source comparison -/

/-- The canonical `R`-linear map carrying `s ∈ M` to the class, in the global sections of
`Coker((f₁,…,f_c) : (M~)^{⊕c} ⟶ M~)` over `Spec R`, of the section of `M~` it determines. -/
public def affineSourceSection (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    M ⟶ moduleSpecΓFunctor.obj (cokernel (equationsMultiplication (specFun f) (tilde M))) :=
  (tilde.isoTop M).hom ≫ moduleSpecΓFunctor.map (cokernel.π _)

/-- `affineSourceSection f M s` is the class in the cokernel of the global section of `M~`
determined by `s`. -/
public theorem affineSourceSection_apply (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (s : M) :
    affineSourceSection f M s =
      (cokernel.π (equationsMultiplication (specFun f) (tilde M))).app ⊤
        ((tilde.isoTop M).hom s) := rfl

/-- A multiple of a section by one of the equations has zero class in the cokernel. -/
public theorem affineSourceSection_smul (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (s : M)
    (i : Fin (d + 1)) : affineSourceSection f M (f i • s) = 0 := by
  refine Eq.trans (congrArg (fun y => (cokernel.π (equationsMultiplication (specFun f)
    (tilde M))).app ⊤ y) (globalSmul_app_top_isoTop (f i) M s).symm) ?_
  exact congrArg (fun φ : tilde M ⟶ cokernel (equationsMultiplication (specFun f) (tilde M)) =>
    φ.app ⊤ ((tilde.isoTop M).hom s)) (globalSmul_comp_cokernelπ (specFun f) (tilde M) i)

/-- The class of a section in the global sections of the cokernel of multiplication by the
equations only depends on the section modulo the submodule the equations generate. -/
public theorem span_smul_le_ker_affineSourceSection (f : Fin (d + 1) → R)
    (M : ModuleCat.{u} R) :
    Ideal.span (Set.range f) • (⊤ : Submodule R M) ≤
      LinearMap.ker (affineSourceSection f M).hom := by
  have key : ∀ r ∈ Ideal.span (Set.range f), ∀ s : M, affineSourceSection f M (r • s) = 0 := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact fun s => affineSourceSection_smul f M s i
    | zero =>
      intro s
      rw [zero_smul]
      exact map_zero _
    | add x y _ _ hx hy =>
      intro s
      rw [add_smul, map_add, hx, hy, add_zero]
    | smul a x _ hx =>
      intro s
      rw [smul_eq_mul, mul_smul, map_smul, hx, smul_zero]
  exact Submodule.smul_le.2 fun r hr s _ => key r hr s

/-- **The source comparison.**  The canonical `R`-linear map from `M/(f₁,…,f_c)M` to the global
sections over `Spec R` of `Coker((f₁,…,f_c) : (M~)^{⊕c} ⟶ M~)`, the module Tag 0G7Q presents
as `i_* i^*(M~)`. -/
public def affineSourceComparison (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    (M ⧸ Ideal.span (Set.range f) • (⊤ : Submodule R M)) →ₗ[R]
      moduleSpecΓFunctor.obj (cokernel (equationsMultiplication (specFun f) (tilde M))) :=
  Submodule.liftQ _ (affineSourceSection f M).hom (span_smul_le_ker_affineSourceSection f M)

/-- The source comparison sends the class of a section to the class of that section. -/
public theorem affineSourceComparison_mk (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (s : M) :
    affineSourceComparison f M (Submodule.Quotient.mk s) =
      (cokernel.π (equationsMultiplication (specFun f) (tilde M))).app ⊤
        ((tilde.isoTop M).hom s) := rfl

/-! ### The source comparison is an isomorphism -/

/-- The cokernel of `tilde.map φ` is the associated sheaf of the cokernel of `φ`. -/
public def tildeCokernelIso {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    cokernel (tilde.map φ) ≅ tilde (cokernel φ) :=
  (PreservesCokernel.iso (tilde.functor R) φ).symm

/-- The projection to the cokernel of `tilde.map φ`, followed by `tildeCokernelIso φ`, is
`tilde.map` of the projection to the cokernel of `φ`. -/
public theorem π_comp_tildeCokernelIso_hom {M N : ModuleCat.{u} R} (φ : M ⟶ N) :
    cokernel.π (tilde.map φ) ≫ (tildeCokernelIso φ).hom = tilde.map (cokernel.π φ) :=
  ((Iso.eq_comp_inv (PreservesCokernel.iso (tilde.functor R) φ)).mpr
    (PreservesCokernel.π_iso_hom (tilde.functor R) φ)).symm

/-- The cokernel of the sheaf-level multiplication map is the associated sheaf of the cokernel of
the algebraic one. -/
public def sourceCokernelIso (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    cokernel (equationsMultiplication (specFun f) (tilde M)) ≅
      tilde (cokernel (equationsMul f M)) :=
  cokernelIsoOfEq (equationsMultiplication_eq f M) ≪≫
    cokernelEpiComp (sigmaTildeComparison M) (tilde.map (equationsMul f M)) ≪≫
    tildeCokernelIso (equationsMul f M)

/-- The projection to the cokernel of `(f₁,…,f_c) : (M~)^{⊕c} ⟶ M~`, followed by
`sourceCokernelIso f M`, is `tilde.map` of the projection to the cokernel of `equationsMul f M`. -/
public theorem π_comp_sourceCokernelIso_hom (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    cokernel.π (equationsMultiplication (specFun f) (tilde M)) ≫ (sourceCokernelIso f M).hom =
      tilde.map (cokernel.π (equationsMul f M)) := by
  have h0 : cokernel.π (equationsMultiplication (specFun f) (tilde M)) ≫
      (cokernelIsoOfEq (equationsMultiplication_eq f M)).hom =
      cokernel.π (sigmaTildeComparison M ≫ tilde.map (equationsMul f M)) :=
    π_comp_cokernelIsoOfEq_hom _
  have h1 : cokernel.π (sigmaTildeComparison M ≫ tilde.map (equationsMul f M)) ≫
      (cokernelEpiComp (sigmaTildeComparison M) (tilde.map (equationsMul f M))).hom =
      cokernel.π (tilde.map (equationsMul f M)) := cokernel.π_desc _ _ _
  rw [sourceCokernelIso, Iso.trans_hom, Iso.trans_hom, ← Category.assoc, ← Category.assoc, h0, h1,
    π_comp_tildeCokernelIso_hom]

/-- The range of the algebraic multiplication map is the submodule the equations generate. -/
public theorem range_equationsMul (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    LinearMap.range (equationsMul f M).hom =
      Ideal.span (Set.range f) • (⊤ : Submodule R M) := by
  refine le_antisymm ?_ ?_
  · have hzero : equationsMul f M ≫
        ModuleCat.ofHom (Ideal.span (Set.range f) • (⊤ : Submodule R M)).mkQ = 0 := by
      refine Sigma.hom_ext _ _ fun i => ?_
      rw [← Category.assoc, ι_comp_equationsMul, comp_zero]
      refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
      exact (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) Submodule.mem_top)
    rintro _ ⟨x, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).1 (congrArg (fun ψ : (∐ fun _ : Fin (d + 1) => M) ⟶
      ModuleCat.of R (M ⧸ Ideal.span (Set.range f) • (⊤ : Submodule R M)) => ψ.hom x) hzero)
  · refine Submodule.smul_le.2 fun r hr m _ => ?_
    induction hr using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        refine ⟨(Sigma.ι (fun _ : Fin (d + 1) => M) i).hom m, ?_⟩
        exact congrArg (fun ψ : M ⟶ M => ψ.hom m) (ι_comp_equationsMul f M i)
    | zero => simp
    | add x y _ _ hx hy =>
        rw [add_smul]
        exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        rw [smul_eq_mul, mul_smul]
        exact Submodule.smul_mem _ a hx

/-- The source comparison, read through the two canonical isomorphisms, is the algebraic
projection to the cokernel. -/
public theorem sourceCokernelIso_affineSourceSection (f : Fin (d + 1) → R) (M : ModuleCat.{u} R)
    (s : M) :
    (moduleSpecΓFunctor.map (sourceCokernelIso f M).hom).hom (affineSourceSection f M s) =
      (tilde.isoTop (cokernel (equationsMul f M))).hom ((cokernel.π (equationsMul f M)).hom s) :=
  (congrArg (fun ψ : tilde M ⟶ tilde (cokernel (equationsMul f M)) =>
      ψ.app ⊤ ((tilde.isoTop M).hom s)) (π_comp_sourceCokernelIso_hom f M)).trans
    (tilde_map_app_top (cokernel.π (equationsMul f M)) s)

/-- A section of `M` whose image in the cokernel of `equationsMul f M` vanishes lies in
`(f₁,…,f_c)M`. -/
public theorem ker_cokernelπ (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (s : M)
    (h : (cokernel.π (equationsMul f M)).hom s = 0) :
    s ∈ Ideal.span (Set.range f) • (⊤ : Submodule R M) := by
  have happ : ((ModuleCat.cokernelIsoRangeQuotient (equationsMul f M)).hom).hom
      ((cokernel.π (equationsMul f M)).hom s) =
      (LinearMap.range (equationsMul f M).hom).mkQ s :=
    congrArg (fun ψ : M ⟶ ModuleCat.of R
      (M ⧸ LinearMap.range (equationsMul f M).hom) => ψ.hom s)
      (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom (equationsMul f M))
  rw [h, map_zero] at happ
  rw [← range_equationsMul]
  exact (Submodule.Quotient.mk_eq_zero _).1 happ.symm

/-- **The source comparison is bijective.**  This is right exactness of `Γ(Spec R, -)` on the
modules in question, obtained from the exactness of `M ↦ M~`. -/
public theorem bijective_affineSourceComparison (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    Function.Bijective (affineSourceComparison f M) := by
  have he₁ : Function.Bijective
      (moduleSpecΓFunctor.map (sourceCokernelIso f M).hom).hom :=
    ConcreteCategory.bijective_of_isIso (moduleSpecΓFunctor.map (sourceCokernelIso f M).hom)
  have he₂ : Function.Bijective
      ((tilde.isoTop (cokernel (equationsMul f M))).hom).hom :=
    ConcreteCategory.bijective_of_isIso (tilde.isoTop (cokernel (equationsMul f M))).hom
  have hπ : Function.Surjective (cokernel.π (equationsMul f M)).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  refine ⟨(injective_iff_map_eq_zero _).2 fun z hz => ?_, fun y => ?_⟩
  · obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hz' : affineSourceSection f M s = 0 := hz
    have h0 : (tilde.isoTop (cokernel (equationsMul f M))).hom
        ((cokernel.π (equationsMul f M)).hom s) = 0 :=
      (sourceCokernelIso_affineSourceSection f M s).symm.trans
        ((congrArg (moduleSpecΓFunctor.map (sourceCokernelIso f M).hom).hom hz').trans
          (map_zero _))
    exact (Submodule.Quotient.mk_eq_zero _).2
      (ker_cokernelπ f M s (he₂.injective (h0.trans (map_zero
        ((tilde.isoTop (cokernel (equationsMul f M))).hom).hom).symm)))
  · obtain ⟨v, hv⟩ := he₂.surjective
      ((moduleSpecΓFunctor.map (sourceCokernelIso f M).hom).hom y)
    obtain ⟨s, rfl⟩ := hπ v
    exact ⟨Submodule.Quotient.mk s,
      he₁.injective ((sourceCokernelIso_affineSourceSection f M s).trans hv)⟩

/-- **The source comparison, as an isomorphism.** -/
public def affineSourceEquiv (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) :
    (M ⧸ Ideal.span (Set.range f) • (⊤ : Submodule R M)) ≃ₗ[R]
      moduleSpecΓFunctor.obj (cokernel (equationsMultiplication (specFun f) (tilde M))) :=
  LinearEquiv.ofBijective (affineSourceComparison f M) (bijective_affineSourceComparison f M)

/-- `affineSourceEquiv f M` sends the class of `s` to the class in the cokernel of the global
section of `M~` determined by `s`. -/
public theorem affineSourceEquiv_mk (f : Fin (d + 1) → R) (M : ModuleCat.{u} R) (s : M) :
    affineSourceEquiv f M (Submodule.Quotient.mk s) =
      (cokernel.π (equationsMultiplication (specFun f) (tilde M))).app ⊤
        ((tilde.isoTop M).hom s) := rfl

/-! ### The reduction of clause 3 of Tag 0G7R to the target comparison -/

/-- **The affine description of `c_{f₁,…,f_c}`, given the target comparison.**  Let `τ` be any
`R`-linear map from the cokernel of the last algebraic Čech differential to the global sections
of `Coker(lastDif)` carrying the class of the fraction `s/(f₁⋯f_c)` to the class of the
sheaf-theoretic fraction.  Then the global sections of Tag 0G7Q's map `supportedFractionClass`,
read through the source comparison on the left and through `τ` on the right, are the map
`Cech.supportedFraction` of Tag 0G7R. -/
public theorem supportedFraction_eq_of_targetComparison (f : Fin (d + 1) → R)
    (M : ModuleCat.{u} R)
    (τ : (Cech.cechTerm f (M : Type u) (d + 1) ⧸
            LinearMap.range (Cech.cechD f (M : Type u) d)) →ₗ[R]
           moduleSpecΓFunctor.obj (cokernel (lastDif (specFun f) (tilde M))))
    (hτ : ∀ s : M, τ (Submodule.Quotient.mk (Cech.topFraction f (M : Type u) s)) =
            (cokernel.π (lastDif (specFun f) (tilde M))).app ⊤
              ((fractionHom (specFun f) (tilde M) d).app ⊤ ((tilde.isoTop M).hom s))) :
    (moduleSpecΓFunctor.map (supportedFractionClass (specFun f) (tilde M))).hom ∘ₗ
        affineSourceComparison f M =
      τ ∘ₗ Cech.supportedFraction f (M : Type u) := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  show (supportedFractionClass (specFun f) (tilde M)).app ⊤
      (affineSourceComparison f M (Submodule.Quotient.mk s)) =
    τ (Cech.supportedFraction f (M : Type u) (Submodule.Quotient.mk s))
  refine Eq.trans (congrArg (fun x => (supportedFractionClass (specFun f) (tilde M)).app ⊤ x)
    (affineSourceComparison_mk f M s)) ?_
  exact (supportedFractionClass_mk (specFun f) (tilde M) ⊤ _).trans (hτ s).symm

/-! ### Non-degeneracy of the affine description -/

section NonDegeneracy

/-- The unique index of the degree-`0` term of the Čech complex of a single equation. -/
private def idx0 : {s : Finset (Fin 1) // s.card = 0} := ⟨∅, Finset.card_empty⟩

/-- The unique index of the degree-`1` term of the Čech complex of a single equation. -/
private def idx1 : {s : Finset (Fin 1) // s.card = 1} := ⟨Finset.univ, Finset.card_fin 1⟩

private theorem eq_idx0 (s : {s : Finset (Fin 1) // s.card = 0}) : s = idx0 :=
  Subtype.ext (Finset.card_eq_zero.mp s.2)

private theorem idx0_subset (t : {s : Finset (Fin 1) // s.card = 1}) : idx0.1 ⊆ t.1 := by
  simp [idx0]

variable {A : Type u} [CommRing A] (f : Fin 1 → A)

/-- The image, in the degree-`1` Čech term of a single equation, of the degree-`0` one. -/
private def topImage : Submodule A (Cech.cechTerm f A 1) :=
  Submodule.map (DirectSum.lof A {s : Finset (Fin 1) // s.card = 1}
      (fun s => Cech.cechMod f A s.1) idx1)
    (LinearMap.range (Cech.cechι f A (idx0_subset idx1)))

/-- Every degree-`1` summand is the top one, so every transition map out of the degree-`0`
summand lands in `topImage`. -/
private theorem lof_cechι_mem (t : {s : Finset (Fin 1) // s.card = 1}) (h : idx0.1 ⊆ t.1)
    (x : Cech.cechMod f A idx0.1) :
    DirectSum.lof A {s : Finset (Fin 1) // s.card = 1} (fun s => Cech.cechMod f A s.1)
      t (Cech.cechι f A h x) ∈ topImage f := by
  obtain rfl : t = idx1 := Cech.eq_topIndex t
  exact ⟨_, ⟨x, rfl⟩, rfl⟩

/-- The boundaries in degree `1` are the fractions with denominator `1`. -/
private theorem range_cechD_le : LinearMap.range (Cech.cechD f A 0) ≤ topImage f := by
  rintro _ ⟨y, rfl⟩
  have hy : y = DirectSum.lof A {s : Finset (Fin 1) // s.card = 0}
      (fun s => Cech.cechMod f A s.1) idx0 (DirectSum.component A _ _ idx0 y) := by
    refine DirectSum.ext_component A fun i => ?_
    obtain rfl : i = idx0 := eq_idx0 i
    simp
  rw [hy, Cech.cechD_lof]
  refine Submodule.sum_mem _ fun i _ => zsmul_mem ?_ _
  exact lof_cechι_mem f _ (Finset.subset_insert i.1 idx0.1) _

/-- The empty product is `1`, so the degree-`0` denominators are trivial. -/
private theorem cechSub_idx0_eq_one (u : Cech.cechSub f idx0.1) : (u : A) = 1 := by
  obtain ⟨k, hk⟩ := u.2
  rw [← hk]
  simp [idx0]

/-- Everything in `topImage` is the class of a numerator over the denominator `1`. -/
private theorem exists_eq_mk_of_mem_topImage (z : Cech.cechMod f A idx1.1)
    (hz : DirectSum.lof A {s : Finset (Fin 1) // s.card = 1}
        (fun s => Cech.cechMod f A s.1) idx1 z ∈ topImage f) :
    ∃ m : A, z = LocalizedModule.mkLinearMap (Cech.cechSub f idx1.1) A m := by
  obtain ⟨w, ⟨y, rfl⟩, hw⟩ := hz
  have hz' : Cech.cechι f A (idx0_subset idx1) y = z := by
    simpa using congrArg (DirectSum.component A {s : Finset (Fin 1) // s.card = 1}
      (fun s => Cech.cechMod f A s.1) idx1) hw
  induction y using LocalizedModule.induction_on with
  | _ m den =>
      refine ⟨m, ?_⟩
      rw [← hz']
      have hden : den = (1 : Cech.cechSub f idx0.1) := Subtype.ext (cechSub_idx0_eq_one f den)
      rw [hden]
      exact Cech.cechι_mk f A (idx0_subset idx1) m

/-- **The affine description of Tag 0G7R is not degenerate.**  For a single equation `a` which is
a nonzero non-unit of a domain, `Cech.supportedFraction` is not the zero map: the class of the
fraction `1/a` in `Coker(M ⟶ M_a)` is not a boundary, because every boundary has denominator
`1`. -/
public theorem supportedFraction_ne_zero [IsDomain A] (h0 : f 0 ≠ 0) (hu : ¬ IsUnit (f 0)) :
    Cech.supportedFraction f A ≠ 0 := by
  intro hzero
  have hval : Cech.supportedFraction f A (Submodule.Quotient.mk (1 : A)) = 0 := by
    rw [hzero]
    rfl
  rw [Cech.supportedFraction_mk, Submodule.Quotient.mk_eq_zero] at hval
  obtain ⟨m, hm⟩ := exists_eq_mk_of_mem_topImage f _ (range_cechD_le f hval)
  obtain ⟨u, hu'⟩ := LocalizedModule.mk_eq.mp hm
  obtain ⟨k, hk⟩ := u.2
  have hu2 : (u : A) * ((1 : A) * (1 : A)) = (u : A) * ((∏ i, f i) * m) := hu'
  rw [mul_one, mul_one] at hu2
  have hune : (u : A) ≠ 0 := by
    rw [← hk]
    simpa using pow_ne_zero k h0
  have h1 : (1 : A) = (∏ i, f i) * m := mul_left_cancel₀ hune (by rwa [mul_one])
  rw [show (∏ i, f i) = f 0 by simp] at h1
  exact hu ⟨⟨f 0, m, h1.symm, (mul_comm m (f 0)).trans h1.symm⟩, rfl⟩

/-- For `A = ℤ`, `f = ![2]` and `M = ℤ`, `Cech.supportedFraction` is not the zero map; its source
is `ℤ/2` and its target `ℤ[1/2]/ℤ`. -/
public theorem supportedFraction_int_two_ne_zero :
    Cech.supportedFraction ![(2 : ℤ)] ℤ ≠ 0 :=
  supportedFraction_ne_zero ![(2 : ℤ)] (by norm_num) (by simp [Int.isUnit_iff])

end NonDegeneracy

end Stacks.Perfect.AffineFractionClass

end
