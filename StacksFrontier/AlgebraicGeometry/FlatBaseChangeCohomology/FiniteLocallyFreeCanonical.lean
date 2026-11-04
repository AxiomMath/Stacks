module

public import StacksFrontier.AlgebraicGeometry.SectionsIso.QuasicoherentArbitraryOpen
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.CechComparison
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionInFirstCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic

/-!
# Finite locally free base change of cohomology

Let

```
Y --p--> X
|        |
k        iX
v        v
T --q--> S
```

be a cartesian square of schemes with `S = Spec A` and `T = Spec B` affine and `q` finite locally
free, and let `F` be a quasi-coherent `𝒪_X`-module. This file proves [Stacks, Tag 0CKW]: for every
`n` the canonical map

  `B ⊗_A Hⁿ(X, F) ⟶ Hⁿ(Y, p^* F)`,  `b ⊗ x ↦ b • p^* x`,

is an isomorphism of `B`-modules, with no hypothesis on `X`.

## The argument

The morphism `p` is affine, so `Hⁿ(Y, p^* F) = Hⁿ(X, p_* p^* F)` ([Stacks, Tag 089W]); this
identification is natural in the module, and the pullback map is the unit `F ⟶ p_* p^* F` on
cohomology followed by it. Over every open `U` of `X` the sections of `p_* p^* F` are
`B ⊗_A Γ(U, F)` (`Stacks.Tag0CKW.bijective_sectionsBaseChangeMap_of_isFiniteLocallyFree`). The
module `B` is finite projective over `A`, so it has a finite dual basis `(eⱼ, fⱼ)`, and two kinds
of morphisms of `𝒪_X`-modules can be written down:

* for `b ∈ B` the twisted unit `u_b : F ⟶ p_* p^* F`, `x ↦ b • p^* x`;
* for an `A`-linear `f : B ⟶ A` the trace `tr_f : p_* p^* F ⟶ F`, `b ⊗ x ↦ f(b) x`.

They satisfy `u_b ≫ tr_f = f(b) • 𝟙` and `∑ⱼ tr_{fⱼ} ≫ u_{eⱼ} = 𝟙`. Applying the additive,
`Γ(X, 𝒪_X)`-linear functor `Hⁿ(X, -)` and using that multiplication by a function on `Y` acts on
`Hⁿ(Y, -)` as the cohomology of that multiplication, `y ↦ ∑ⱼ eⱼ ⊗ tr_{fⱼ}(y)` is a two-sided
inverse of the base change map.

## Main definitions

* `Stacks.Tag0CKW.cohomologyPullback`: the pullback map `Hⁿ(X, F) ⟶ Hⁿ(Y, p^* F)`.
* `Stacks.Tag0CKW.cohomologyBaseChangeMap`: its `B`-linear extension
  `B ⊗_A Hⁿ(X, F) ⟶ Hⁿ(Y, p^* F)`.
* `Stacks.Tag0CKW.twistedUnit` and `Stacks.Tag0CKW.trace`: the two morphisms above.

## Main results

* `Stacks.Tag0CKW.isIso_cohomologyBaseChangeMap`: **[Stacks, Tag 0CKW]**, over affine bases `S`
  and `T` with `T ⟶ S` finite locally free.
* `Stacks.Tag0CKW.isIso_cohomologyBaseChangeMap_of_isFiniteLocallyFree_module`: the same for
  `Spec B ⟶ Spec A` with `B` a finite locally free `A`-module.
* `Stacks.Tag0CKW.cohomologyIsoPushforward_hom_naturality`: [Stacks, Tag 089W] is natural in
  the module.

## References

* [Stacks Project, Tag 0CKW](https://stacks.math.columbia.edu/tag/0CKW)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 059K](https://stacks.math.columbia.edu/tag/059K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct ChangeOfRings

universe u

namespace Stacks.Tag0CKW

/-! ### A finite dual basis of a flat, finitely presented module -/

/-- A flat, finitely presented module `B` over `A` has a finite dual basis: elements `eⱼ` of `B`
and linear forms `fⱼ : B → A` with `∑ⱼ fⱼ(b) • eⱼ = b` for every `b`. -/
theorem exists_dualBasis_of_flat_of_finitePresentation (A B : Type u) [CommRing A]
    [AddCommGroup B] [Module A B] [Module.Flat A B] [Module.FinitePresentation A B] :
    ∃ (m : ℕ) (e : Fin m → B) (f : Fin m → (B →ₗ[A] A)),
      ∀ b : B, ∑ j, f j b • e j = b := by
  obtain ⟨m, h₂, h₃, h⟩ := Module.Flat.exists_factorization_of_finitePresentation
    (LinearMap.id : B →ₗ[A] B)
  refine ⟨m, fun j => h₃ (Finsupp.single j 1), fun j => Finsupp.lapply j ∘ₗ h₂, fun b => ?_⟩
  conv_rhs => rw [show b = h₃ (h₂ b) from congrArg (fun g : B →ₗ[A] B => g b) h]
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lapply_apply, ← map_smul,
    Finsupp.smul_single, smul_eq_mul, mul_one, ← map_sum, Finsupp.univ_sum_single]

/-! ### Sections-level constructions of morphisms of modules -/

section HomOfSections

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism of `𝒪_X`-modules from a family of `Γ(X, U)`-linear maps on sections compatible
with restriction. -/
def homOfSections (σ : ∀ U : X.Opens, Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U))
    (hσ : ∀ {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)),
      σ V (M.presheaf.map i.op x) = N.presheaf.map i.op (σ U x)) : M ⟶ N :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (σ U.unop).toAddMonoidHom
      naturality := fun U V i => by
        ext x
        exact hσ i.unop x }
    (fun U r m => (σ U.unop).map_smul r m)⟩

/-- The sections of `homOfSections σ hσ` over `U` are given by `σ U`. -/
@[simp]
theorem homOfSections_app (σ : ∀ U : X.Opens, Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U))
    (hσ : ∀ {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)),
      σ V (M.presheaf.map i.op x) = N.presheaf.map i.op (σ U x)) (U : X.Opens)
    (x : Γ(M, U)) : (homOfSections σ hσ).app U x = σ U x := rfl

/-- A finite sum of morphisms of `𝒪_X`-modules acts on sections as the sum of the actions. -/
theorem sum_app_apply {ι : Type*} (s : Finset ι) (φ : ι → (M ⟶ N)) (U : X.Opens)
    (x : Γ(M, U)) : (∑ j ∈ s, φ j).app U x = ∑ j ∈ s, (φ j).app U x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app, ← ih]
    rfl

end HomOfSections

/-! ### The unit, twisted by a function on the base -/

section Twist

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}

/-- Restricting `f.appLE ⊤ ⊤` to `U` gives `f.appLE ⊤ U`. -/
private theorem appLE_top_apply_eq_map {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens)
    (b : Γ(Y, ⊤)) : (f.appLE ⊤ U (le_preimage_top f U)).hom b =
      X.presheaf.map (isTerminalTop.from U).op ((f.appLE ⊤ ⊤ (le_preimage_top f ⊤)).hom b) :=
  congrArg (fun m : Γ(Y, ⊤) ⟶ Γ(X, U) => m.hom b)
    (Scheme.Hom.appLE_map f (le_preimage_top f ⊤) (isTerminalTop.from U).op).symm

/-- The unit `F ⟶ p_* p^* F` followed by multiplication by the pullback along `k` of a function
`b` on `T`. -/
def twistedUnit (k : Y ⟶ T) (p : Y ⟶ X) (F : X.Modules) (b : Γ(T, ⊤)) :
    F ⟶ (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F) :=
  (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F ≫
    (Scheme.Modules.pushforward p).map
      ((Scheme.smulEnd Y ((k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom b)).app _)

/-- On sections over `U`, the twisted unit sends `x` to `b • p^* x`. -/
theorem twistedUnit_app (k : Y ⟶ T) (p : Y ⟶ X) (F : X.Modules) (b : Γ(T, ⊤)) (U : X.Opens)
    (x : Γ(F, U)) :
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    (twistedUnit k p F b).app U x = b • pullbackUnitSections p F U x := by
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  show Y.presheaf.map (isTerminalTop.from (p ⁻¹ᵁ U)).op
      ((k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom b) • pullbackUnitSections p F U x =
    (k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom b • pullbackUnitSections p F U x
  rw [← appLE_top_apply_eq_map]

end Twist

/-! ### The trace of a functional on the base, as a map `p_* p^* F ⟶ F` -/

section Trace

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}
  (H : IsPullback p k iX q) [IsAffine S] [IsAffine T] [Stacks.Morphisms.IsFiniteLocallyFree q]
  (F : X.Modules) [F.IsQuasicoherent]

/-- The canonical comparison `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ≅ Γ(p^* F, p⁻¹U)`, over an arbitrary
open of `X`. -/
def sectionsBaseChangeEquiv (U : X.Opens) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(F, U) ≃ₗ[Γ(T, ⊤)] Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) :=
  letI := baseAlgebra q
  letI := baseModule iX F U
  letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  LinearEquiv.ofBijective (sectionsBaseChangeMap H F U)
    (bijective_sectionsBaseChangeMap_of_isFiniteLocallyFree H F U)

/-- The comparison `sectionsBaseChangeEquiv` sends `b ⊗ x` to `b • p^* x`. -/
theorem sectionsBaseChangeEquiv_tmul (U : X.Opens) (b : Γ(T, ⊤)) (x : Γ(F, U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    sectionsBaseChangeEquiv H F U (b ⊗ₜ[Γ(S, ⊤)] x) = b • pullbackUnitSections p F U x :=
  sectionsBaseChangeMap_tmul H F U b x

/-- Multiplication by a function on `U`, as a `Γ(S, ⊤)`-linear endomorphism of `Γ(F, U)`. -/
def sectionsSmul (U : X.Opens) (r : Γ(X, U)) :
    letI := baseModule iX F U
    Γ(F, U) →ₗ[Γ(S, ⊤)] Γ(F, U) :=
  letI := baseModule iX F U
  { toFun := fun x => r • x
    map_add' := smul_add r
    map_smul' := fun a x => by
      change r • ((iX.appLE ⊤ U (le_preimage_top iX U)).hom a • x) =
        (iX.appLE ⊤ U (le_preimage_top iX U)).hom a • (r • x)
      rw [← mul_smul, ← mul_smul, mul_comm] }

/-- The inverse of `sectionsBaseChangeEquiv` turns multiplication by the pullback of a function
`r` on `U` into `id ⊗ (r • -)`. -/
theorem sectionsBaseChangeEquiv_symm_smul (U : X.Opens) (r : Γ(X, U))
    (y : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    (sectionsBaseChangeEquiv H F U).symm ((p.app U).hom r • y) =
      LinearMap.lTensor Γ(T, ⊤) (sectionsSmul F U r) ((sectionsBaseChangeEquiv H F U).symm y) := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  rw [LinearEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (sectionsBaseChangeEquiv H F U).surjective y
  rw [LinearEquiv.symm_apply_apply]
  induction z with
  | zero => rw [map_zero, map_zero, map_zero, smul_zero]
  | tmul b x =>
    rw [LinearMap.lTensor_tmul, sectionsBaseChangeEquiv_tmul, sectionsBaseChangeEquiv_tmul]
    show (p.app U).hom r • (b • _) = b • pullbackUnitSections p F U (r • x)
    rw [pullbackUnitSections_smul p F U r x]
    show (p.app U).hom r • ((k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom b •
        pullbackUnitSections p F U x) =
      (k.appLE ⊤ (p ⁻¹ᵁ U) (le_preimage_top k _)).hom b •
        ((p.app U).hom r • pullbackUnitSections p F U x)
    rw [← mul_smul, ← mul_smul, mul_comm]
  | add z w hz hw => rw [map_add, smul_add, hz, hw, map_add, map_add]

/-- The inverse of `sectionsBaseChangeEquiv` commutes with restriction from `U` to `V`. -/
theorem sectionsBaseChangeEquiv_symm_res {U V : X.Opens} (h : V ≤ U)
    (y : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule iX F V
    (sectionsBaseChangeEquiv H F V).symm
        (((Scheme.Modules.pullback p).obj F).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono p h)).op y) =
      LinearMap.lTensor Γ(T, ⊤) (baseResHom iX F h) ((sectionsBaseChangeEquiv H F U).symm y) := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule iX F V
  rw [LinearEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (sectionsBaseChangeEquiv H F U).surjective y
  rw [LinearEquiv.symm_apply_apply]
  exact (sectionsBaseChangeMap_comm_res H F h z).symm

/-- A section of `p_* G` over `U` is a section of `G` over `p⁻¹U`. -/
abbrev pushforwardSection {G : Y.Modules} {U : X.Opens}
    (y : Γ((Scheme.Modules.pushforward p).obj G, U)) : Γ(G, p ⁻¹ᵁ U) := y

/-- The trace of a `Γ(S, ⊤)`-linear functional `f` on `Γ(T, ⊤)`, on the sections of
`p_* p^* F` over one open: `b ⊗ x ↦ f(b) x` read through the comparison. -/
def traceSections (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤)) (U : X.Opens) :
    Γ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F), U) →ₗ[Γ(X, U)]
      Γ(F, U) :=
  letI := baseAlgebra q
  letI := baseModule iX F U
  { toFun := fun y => TensorProduct.lid Γ(S, ⊤) Γ(F, U)
      (LinearMap.rTensor Γ(F, U) f ((sectionsBaseChangeEquiv H F U).symm (pushforwardSection y)))
    map_add' := fun y y' => by
      change TensorProduct.lid Γ(S, ⊤) Γ(F, U) (LinearMap.rTensor Γ(F, U) f
          ((sectionsBaseChangeEquiv H F U).symm (pushforwardSection y + pushforwardSection y'))) = _
      simp only [map_add]
    map_smul' := fun r y => by
      change TensorProduct.lid Γ(S, ⊤) Γ(F, U) (LinearMap.rTensor Γ(F, U) f
          ((sectionsBaseChangeEquiv H F U).symm ((p.app U).hom r • pushforwardSection y))) = r • _
      rw [sectionsBaseChangeEquiv_symm_smul]
      induction (sectionsBaseChangeEquiv H F U).symm (pushforwardSection y) with
      | zero => simp only [map_zero, smul_zero]
      | tmul b x =>
        simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
        change (iX.appLE ⊤ U (le_preimage_top iX U)).hom (f b) • (r • x) =
          r • ((iX.appLE ⊤ U (le_preimage_top iX U)).hom (f b) • x)
        rw [← mul_smul, ← mul_smul, mul_comm]
      | add z w hz hw => simp only [map_add, smul_add, hz, hw] }

/-- The trace of `f` on sections sends `b • p^* x` to `f(b) • x`. -/
theorem traceSections_apply_tmul (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (U : X.Opens) (b : Γ(T, ⊤)) (x : Γ(F, U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    traceSections H F f U (b • pullbackUnitSections p F U x) = f b • x := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  show TensorProduct.lid Γ(S, ⊤) Γ(F, U) (LinearMap.rTensor Γ(F, U) f
    ((sectionsBaseChangeEquiv H F U).symm (b • pullbackUnitSections p F U x))) = _
  rw [← sectionsBaseChangeEquiv_tmul H F U b x, LinearEquiv.symm_apply_apply,
    LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

/-- The trace of a functional on `Γ(T, ⊤)`, as a morphism of `𝒪_X`-modules `p_* p^* F ⟶ F`. -/
def trace (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤)) :
    (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F) ⟶ F :=
  homOfSections (traceSections H F f) fun {U V} i y => by
    let := baseAlgebra q
    let := baseModule iX F U
    let := baseModule iX F V
    change TensorProduct.lid Γ(S, ⊤) Γ(F, V) (LinearMap.rTensor Γ(F, V) f
      ((sectionsBaseChangeEquiv H F V).symm (((Scheme.Modules.pullback p).obj F).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono p (leOfHom i))).op (pushforwardSection y)))) =
      F.presheaf.map i.op (TensorProduct.lid Γ(S, ⊤) Γ(F, U)
        (LinearMap.rTensor Γ(F, U) f
          ((sectionsBaseChangeEquiv H F U).symm (pushforwardSection y))))
    rw [sectionsBaseChangeEquiv_symm_res]
    induction (sectionsBaseChangeEquiv H F U).symm (pushforwardSection y) with
    | zero => simp only [map_zero]
    | tmul b x =>
      simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      exact ((baseResHom iX F (leOfHom i)).map_smul (f b) x).symm
    | add z w hz hw => simp only [map_add, hz, hw]

/-- On sections over `U`, the twisted unit for `b` followed by the trace of `f` sends `x` to
`f(b) • x`. -/
theorem trace_app_twistedUnit_app (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (b : Γ(T, ⊤)) (U : X.Opens) (x : Γ(F, U)) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    (trace H F f).app U ((twistedUnit k p F b).app U x) = f b • x := by
  let := baseAlgebra q
  let := baseModule iX F U
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  rw [twistedUnit_app]
  exact traceSections_apply_tmul H F f U b x

/-- **The trace undoes the twisted unit up to the functional.** `x ↦ b • p^* x` followed by
the trace of `f` is multiplication by `f(b)`. -/
theorem twistedUnit_comp_trace (f : letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤))
    (b : Γ(T, ⊤)) :
    twistedUnit k p F b ≫ trace H F f =
      (Scheme.smulEnd X ((iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom (f b))).app F := by
  let := baseAlgebra q
  ext U x
  let := baseModule iX F U
  refine (trace_app_twistedUnit_app H F f b U x).trans ?_
  show (iX.appLE ⊤ U (le_preimage_top iX U)).hom (f b) • x =
    X.presheaf.map (isTerminalTop.from U).op ((iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom (f b)) • x
  rw [appLE_top_apply_eq_map]

/-- For a dual basis `(e, f)` of `Γ(T, ⊤)` over `Γ(S, ⊤)`, the sum `∑ⱼ tr_{fⱼ} ≫ u_{eⱼ}` of
traces followed by twisted units is the identity of `p_* p^* F`. -/
theorem sum_trace_comp_twistedUnit {m : ℕ} (e : Fin m → Γ(T, ⊤))
    (f : Fin m → (letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤)))
    (he : letI := baseAlgebra q; ∀ b : Γ(T, ⊤), ∑ j, f j b • e j = b) :
    ∑ j, trace H F (f j) ≫ twistedUnit k p F (e j) = 𝟙 _ := by
  let := baseAlgebra q
  ext U y
  let := baseModule iX F U
  let := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  let := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  let := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
  rw [sum_app_apply]
  obtain ⟨z, hz⟩ := (sectionsBaseChangeEquiv H F U).surjective (pushforwardSection y)
  show ∑ j, (twistedUnit k p F (e j)).app U ((trace H F (f j)).app U (pushforwardSection y)) =
    pushforwardSection y
  rw [← hz]
  clear hz
  induction z with
  | zero =>
    rw [map_zero]
    show ∑ j, (twistedUnit k p F (e j)).app U ((trace H F (f j)).app U
      (0 : Γ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F), U))) = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_zero, map_zero]
  | tmul b x =>
    rw [sectionsBaseChangeEquiv_tmul]
    have h1 : ∀ j, (twistedUnit k p F (e j)).app U ((trace H F (f j)).app U
        (b • pullbackUnitSections p F U x)) = (f j b • e j) • pullbackUnitSections p F U x := by
      intro j
      rw [twistedUnit_app]
      show e j • pullbackUnitSections p F U (traceSections H F (f j) U
        (b • pullbackUnitSections p F U x)) = _
      rw [traceSections_apply_tmul]
      show e j • sectionsBaseChangeHom iX p F U (f j b • x) = _
      rw [map_smul, smul_comm, smul_assoc]
      rfl
    have h2 : ∑ j, (f j b • e j) • pullbackUnitSections p F U x =
        b • pullbackUnitSections p F U x := by
      rw [← Finset.sum_smul, he]
    rw [Finset.sum_congr rfl fun j _ => h1 j]
    exact h2
  | add z w hz' hw' =>
    rw [map_add]
    let y₁ : Γ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F), U) :=
      sectionsBaseChangeEquiv H F U z
    let y₂ : Γ((Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj F), U) :=
      sectionsBaseChangeEquiv H F U w
    show ∑ j, (twistedUnit k p F (e j)).app U ((trace H F (f j)).app U (y₁ + y₂)) = y₁ + y₂
    simp only [map_add, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) hz' hw'

end Trace

/-! ### Naturality of the collapse of a composite at acyclic objects -/

section CollapseNaturality

open Stacks.Cohomology.AffineComparison

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

omit [EnoughInjectives B] in
/-- The forward map of `rightDerivedFunctorPlusObjSingleIso F X hX`, written out as a
composite. -/
theorem rightDerivedFunctorPlusObjSingleIso_hom (X : A) (hX : F.rightAcyclic X)
    [IsIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X))] :
    (rightDerivedFunctorPlusObjSingleIso F X hX).hom =
      F.rightDerivedFunctorPlus.map ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app X) ≫
        inv (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) ≫
        F.mapSingleFunctorCompQhIso.hom.app X := rfl

omit [EnoughInjectives B] in
/-- The isomorphism `rightDerivedFunctorPlusObjSingleIso` is natural in the `F`-acyclic
object. -/
theorem rightDerivedFunctorPlusObjSingleIso_hom_naturality {X X' : A} (φ : X ⟶ X')
    (hX : F.rightAcyclic X) (hX' : F.rightAcyclic X') :
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map φ) ≫
        (rightDerivedFunctorPlusObjSingleIso F X' hX').hom =
      (rightDerivedFunctorPlusObjSingleIso F X hX).hom ≫
        (DerivedCategory.Plus.singleFunctor B 0).map (F.map φ) := by
  have : IsIso (F.rightDerivedFunctorPlusUnit.app
    ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) := hX
  have : IsIso (F.rightDerivedFunctorPlusUnit.app
    ((HomotopyCategory.Plus.singleFunctor A 0).obj X')) := hX'
  have hα := (Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.naturality φ
  have hu := F.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.singleFunctor A 0).map φ)
  have hβ := (F.mapSingleFunctorCompQhIso).hom.naturality φ
  have hu' : F.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor A 0).map φ)) ≫
      inv (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X')) =
      inv (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) ≫
        DerivedCategory.Plus.Qh.map (F.mapHomotopyCategoryPlus.map
          ((HomotopyCategory.Plus.singleFunctor A 0).map φ)) := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hu.symm
  rw [rightDerivedFunctorPlusObjSingleIso_hom F X hX,
    rightDerivedFunctorPlusObjSingleIso_hom F X' hX',
    ← Functor.map_comp_assoc, hα, Functor.map_comp_assoc]
  simp only [Functor.comp_map, Category.assoc] at hβ ⊢
  rw [reassoc_of% hu', hβ]

/-- The isomorphism `rightDerivedPlusCollapseIso`, `R⁺(F ⋙ G) X ≅ R⁺G (F X)` for an `F`-acyclic
`X`, is natural in `X`. -/
theorem rightDerivedPlusCollapseIso_hom_naturality
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) {X X' : A} (φ : X ⟶ X')
    (hX : F.rightAcyclic X) (hX' : F.rightAcyclic X') (n : ℤ) :
    ((F ⋙ G).rightDerivedPlus n).map φ ≫ (rightDerivedPlusCollapseIso F G hFG X' hX' n).hom =
      (rightDerivedPlusCollapseIso F G hFG X hX n).hom ≫ (G.rightDerivedPlus n).map (F.map φ) := by
  simp only [Functor.rightDerivedPlus, Functor.comp_map, rightDerivedPlusCollapseIso,
    Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom, ← Functor.map_comp]
  congr 1
  have hc := (Stacks.Cohomology.DerivedPushforwardSections.compIso F G hFG).hom.naturality
    ((DerivedCategory.Plus.singleFunctor A 0).map φ)
  simp only [Functor.comp_map] at hc
  rw [reassoc_of% hc, ← Functor.map_comp,
    rightDerivedFunctorPlusObjSingleIso_hom_naturality F φ hX hX', Functor.map_comp,
    Category.assoc]

/-- The isomorphism `rightDerivedCollapseIso`, `Rⁿ(F ⋙ G) X ≅ RⁿG (F X)` for an `F`-acyclic `X`,
is natural in `X`. -/
theorem rightDerivedCollapseIso_hom_naturality
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) {X X' : A} (φ : X ⟶ X')
    (hX : F.rightAcyclic X) (hX' : F.rightAcyclic X') (n : ℕ) :
    ((F ⋙ G).rightDerived n).map φ ≫ (rightDerivedCollapseIso F G hFG X' hX' n).hom =
      (rightDerivedCollapseIso F G hFG X hX n).hom ≫ (G.rightDerived n).map (F.map φ) := by
  simp only [rightDerivedCollapseIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc]
  rw [NatTrans.naturality_assoc,
    reassoc_of% (rightDerivedPlusCollapseIso_hom_naturality F G hFG φ hX hX' (n : ℤ)),
    NatTrans.naturality]

end CollapseNaturality

/-! ### Naturality of the comparison of cohomology along an affine morphism -/

section AffineNaturality

open Stacks.Cohomology.AffineComparison Stacks.Cohomology.AffineBase

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The identification `Hⁿ(X, F) ≅ Hⁿ(S, f_* F)` along an affine morphism `f : X ⟶ S`
([Stacks, Tag 089W]) is natural in the quasi-coherent module `F`. -/
theorem cohomologyIsoPushforward_hom_naturality {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent] (φ : F ⟶ F') (n : ℕ) :
    (ModuleCat.restrictScalars f.appTop.hom).map (((moduleGlobalSections X).rightDerived n).map φ) ≫
        (cohomologyIsoPushforward f F' n).hom =
      (cohomologyIsoPushforward f F n).hom ≫
        ((moduleGlobalSections S).rightDerived n).map ((Scheme.Modules.pushforward f).map φ) := by
  simp only [cohomologyIsoPushforward, restrictScalarsRightDerivedIso, Iso.trans_hom,
    Iso.app_hom, Category.assoc]
  rw [← Functor.comp_map, NatTrans.naturality_assoc,
    rightDerivedCollapseIso_hom_naturality]

end AffineNaturality

/-! ### The canonical base change map on cohomology -/

section BaseChange

open Stacks.Cohomology.AffineComparison Stacks.Cohomology.AffineBase

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}
  (H : IsPullback p k iX q) [IsAffine S] [IsAffine T]

include H in
/-- The base change `p` of `iX : X ⟶ S` along a morphism `q` of affine schemes is affine. -/
theorem isAffineHom_of_isPullback : IsAffineHom p :=
  MorphismProperty.of_isPullback H.flip inferInstance

include H in
omit [IsAffine S] [IsAffine T] in
/-- The two ways round the square of global sections agree. -/
theorem appTop_appLE_comm (a : Γ(S, ⊤)) :
    p.appTop.hom ((iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom a) =
      (k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom ((q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom a) := by
  have e1 : iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤) ≫ p.appLE ⊤ ⊤ (le_preimage_top p ⊤) =
      (p ≫ iX).appLE ⊤ ⊤ (le_preimage_top (p ≫ iX) ⊤) :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  rw [← sectionsSquare_comm H ⊤ a, ← e1, CommRingCat.hom_comp, RingHom.comp_apply,
    appLE_top_eq_appTop, appLE_top_eq_appTop]

/-- **The pullback map on cohomology** `Hⁿ(X, F) ⟶ Hⁿ(Y, p^* F)`: the unit `F ⟶ p_* p^* F`
on cohomology, followed by the identification `Hⁿ(X, p_* G) = Hⁿ(Y, G)` along the affine
morphism `p` ([Stacks, Tag 089W]). -/
def cohomologyPullback (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    ((moduleGlobalSections X).rightDerived n).obj F ⟶
      (ModuleCat.restrictScalars p.appTop.hom).obj
        (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)) :=
  haveI := isAffineHom_of_isPullback H
  ((moduleGlobalSections X).rightDerived n).map
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F) ≫
    (cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj F) n).inv

/-- The pullback map on cohomology, evaluated at a class. -/
theorem cohomologyPullback_apply (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (x : ((moduleGlobalSections X).rightDerived n).obj F) :
    haveI := isAffineHom_of_isPullback H
    (cohomologyPullback H F n).hom x =
      (cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj F) n).inv.hom
        ((((moduleGlobalSections X).rightDerived n).map
          ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F)).hom x) := rfl

/-- The pullback map, as a `Γ(S, ⊤)`-linear map between the underlying modules. -/
def cohomologyPullbackBase (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    letI := Module.compHom ((baseRestrictScalars k).obj
      (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)))
      (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom
    (baseRestrictScalars iX).obj (((moduleGlobalSections X).rightDerived n).obj F) →ₗ[Γ(S, ⊤)]
      (baseRestrictScalars k).obj
        (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)) :=
  letI := Module.compHom ((baseRestrictScalars k).obj (((moduleGlobalSections Y).rightDerived n).obj
      ((Scheme.Modules.pullback p).obj F))) (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom
  { toFun := fun x => (cohomologyPullback H F n).hom x
    map_add' := fun x y => (cohomologyPullback H F n).hom.map_add x y
    map_smul' := fun a x => by
      let x' : ((moduleGlobalSections X).rightDerived n).obj F := x
      refine ((cohomologyPullback H F n).hom.map_smul
        ((iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom a) x').trans ?_
      change p.appTop.hom ((iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom a) •
          (cohomologyPullback H F n).hom x' =
        (k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom ((q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom a) •
          (cohomologyPullback H F n).hom x'
      rw [appTop_appLE_comm H a] }

/-- The canonical base change map on cohomology, as a `Γ(T, ⊤)`-linear map between the
underlying modules: the `Γ(T, ⊤)`-linear extension of the pullback map. -/
def cohomologyBaseChangeLinearMap (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    letI := baseAlgebra q
    Γ(T, ⊤) ⊗[Γ(S, ⊤)]
        (baseRestrictScalars iX).obj (((moduleGlobalSections X).rightDerived n).obj F) →ₗ[Γ(T, ⊤)]
      (baseRestrictScalars k).obj
        (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)) :=
  letI := baseAlgebra q
  letI := Module.compHom ((baseRestrictScalars k).obj (((moduleGlobalSections Y).rightDerived n).obj
      ((Scheme.Modules.pullback p).obj F))) (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom
  haveI : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) ((baseRestrictScalars k).obj
      (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  (cohomologyPullbackBase H F n).liftBaseChange Γ(T, ⊤)

/-- The base change map sends `b ⊗ x` to `b • p^* x`. -/
theorem cohomologyBaseChangeLinearMap_tmul (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (b : Γ(T, ⊤))
    (x : (baseRestrictScalars iX).obj (((moduleGlobalSections X).rightDerived n).obj F)) :
    letI := baseAlgebra q
    cohomologyBaseChangeLinearMap H F n (b ⊗ₜ[Γ(S, ⊤)] x) =
      ((k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom b • (cohomologyPullback H F n).hom x :
        ((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)) := by
  let := baseAlgebra q
  let := Module.compHom ((baseRestrictScalars k).obj (((moduleGlobalSections Y).rightDerived n).obj
      ((Scheme.Modules.pullback p).obj F))) (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom
  have : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) ((baseRestrictScalars k).obj
      (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact LinearMap.liftBaseChange_tmul _ _ _ _

/-- **The canonical base change map on cohomology**
`Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Hⁿ(X, F) ⟶ Hⁿ(Y, p^* F)`, `b ⊗ x ↦ b • p^* x`: the `Γ(T, ⊤)`-linear
extension of the pullback map `cohomologyPullback`. -/
def cohomologyBaseChangeMap (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (baseRestrictScalars iX ⋙ baseExtendScalars q).obj
        (((moduleGlobalSections X).rightDerived n).obj F) ⟶
      (baseRestrictScalars k).obj
        (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)) :=
  letI := baseAlgebra q
  (ModuleCat.ofHom (cohomologyBaseChangeLinearMap H F n) :
    ModuleCat.of Γ(T, ⊤) (Γ(T, ⊤) ⊗[Γ(S, ⊤)]
        (baseRestrictScalars iX).obj (((moduleGlobalSections X).rightDerived n).obj F)) ⟶
      ModuleCat.of Γ(T, ⊤) ((baseRestrictScalars k).obj
        (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F))))

/-- Multiplication by a function on `Y` on `Hⁿ(Y, G)` is, through [Stacks, Tag 089W], the
cohomology of the direct image of that multiplication. -/
theorem smul_cohomologyIsoPushforward_inv [IsAffineHom p] (G : Y.Modules) [G.IsQuasicoherent]
    (n : ℕ) (r : Γ(Y, ⊤))
    (w : ((moduleGlobalSections X).rightDerived n).obj ((Scheme.Modules.pushforward p).obj G)) :
    (r • (cohomologyIsoPushforward p G n).inv.hom w :
        ((moduleGlobalSections Y).rightDerived n).obj G) =
      (cohomologyIsoPushforward p G n).inv.hom
        ((((moduleGlobalSections X).rightDerived n).map
          ((Scheme.Modules.pushforward p).map ((Scheme.smulEnd Y r).app G))).hom w) := by
  have hnat := cohomologyIsoPushforward_hom_naturality p (F := G) (F' := G)
    ((Scheme.smulEnd Y r).app G) n
  have hinv : (cohomologyIsoPushforward p G n).inv ≫
      (ModuleCat.restrictScalars p.appTop.hom).map
        (((moduleGlobalSections Y).rightDerived n).map ((Scheme.smulEnd Y r).app G)) =
      ((moduleGlobalSections X).rightDerived n).map
          ((Scheme.Modules.pushforward p).map ((Scheme.smulEnd Y r).app G)) ≫
        (cohomologyIsoPushforward p G n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  refine Eq.trans ?_ (congrArg (fun h => h.hom w) hinv)
  exact (Scheme.rightDerived_sectionsFunctor_map_smulEnd_apply Y r n G _).symm

/-- The pullback of a class, multiplied by a function `b` on `T`, is the cohomology of the
twisted unit applied to the class. -/
theorem smul_cohomologyPullback (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) (b : Γ(T, ⊤))
    (x : ((moduleGlobalSections X).rightDerived n).obj F) :
    haveI := isAffineHom_of_isPullback H
    ((k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom b • (cohomologyPullback H F n).hom x :
        ((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)) =
      (cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj F) n).inv.hom
        ((((moduleGlobalSections X).rightDerived n).map (twistedUnit k p F b)).hom x) := by
  have := isAffineHom_of_isPullback H
  rw [cohomologyPullback_apply, smul_cohomologyIsoPushforward_inv, twistedUnit, Functor.map_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply]

section Inverse

/-- An element of a module, as an element of the module with its scalars restricted. -/
def restrictScalarsMk {R R' : Type u} [Ring R] [Ring R'] (φ : R →+* R') {M : ModuleCat.{u} R'}
    (x : M) : (ModuleCat.restrictScalars φ).obj M := x

/-- An element of a module with its scalars restricted, as an element of the module. -/
def restrictScalarsOut {R R' : Type u} [Ring R] [Ring R'] (φ : R →+* R') {M : ModuleCat.{u} R'}
    (x : (ModuleCat.restrictScalars φ).obj M) : M := x

/-- For an isomorphism `ε` out of a module with restricted scalars, `ε.hom (ε.inv v) = v`. -/
theorem hom_restrictScalarsMk_inv {R R' : Type u} [Ring R] [Ring R'] (φ : R →+* R')
    {M : ModuleCat.{u} R'} {N : ModuleCat.{u} R} (ε : (ModuleCat.restrictScalars φ).obj M ≅ N)
    (v : N) : ε.hom.hom (restrictScalarsMk φ (ε.inv.hom v)) = v :=
  congrArg (fun h => ModuleCat.Hom.hom h v) ε.inv_hom_id

variable [Stacks.Morphisms.IsFiniteLocallyFree q] (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
  {m : ℕ} (e : Fin m → Γ(T, ⊤))
  (f : Fin m → (letI := baseAlgebra q; Γ(T, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤)))

/-- The inverse of the base change map, built from a dual basis `(e, f)` of `Γ(T, ⊤)` over
`Γ(S, ⊤)`: `y ↦ ∑ⱼ eⱼ ⊗ tr_{fⱼ}(y)`. -/
def cohomologyBaseChangeInv :
    letI := baseAlgebra q
    (baseRestrictScalars k).obj
        (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)) →+
      Γ(T, ⊤) ⊗[Γ(S, ⊤)]
        (baseRestrictScalars iX).obj (((moduleGlobalSections X).rightDerived n).obj F) :=
  letI := baseAlgebra q
  haveI := isAffineHom_of_isPullback H
  let ν₁ : (baseRestrictScalars k).obj
        (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)) →+
      (ModuleCat.restrictScalars p.appTop.hom).obj
        (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F)) :=
    { toFun := fun y => y, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let ν₂ : ((moduleGlobalSections X).rightDerived n).obj F →+
      (baseRestrictScalars iX).obj (((moduleGlobalSections X).rightDerived n).obj F) :=
    { toFun := fun x => x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  ∑ j, (TensorProduct.mk Γ(S, ⊤) Γ(T, ⊤)
      ((baseRestrictScalars iX).obj (((moduleGlobalSections X).rightDerived n).obj F))
      (e j)).toAddMonoidHom.comp (ν₂.comp
    ((((moduleGlobalSections X).rightDerived n).map (trace H F (f j))).hom.toAddMonoidHom.comp
      ((cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj F)
        n).hom.hom.toAddMonoidHom.comp ν₁)))

/-- The inverse `cohomologyBaseChangeInv` sends `y` to `∑ⱼ eⱼ ⊗ tr_{fⱼ}(y)`. -/
theorem cohomologyBaseChangeInv_apply
    (y : (baseRestrictScalars k).obj
      (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F))) :
    letI := baseAlgebra q
    haveI := isAffineHom_of_isPullback H
    cohomologyBaseChangeInv H F n e f y = ∑ j, e j ⊗ₜ[Γ(S, ⊤)]
      restrictScalarsMk (iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom
        ((((moduleGlobalSections X).rightDerived n).map (trace H F (f j))).hom
          ((cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj F) n).hom.hom
            (restrictScalarsMk p.appTop.hom
              (restrictScalarsOut (k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom y)))) := by
  let := baseAlgebra q
  simp only [cohomologyBaseChangeInv, AddMonoidHom.finsetSum_apply]
  rfl

omit [Stacks.Morphisms.IsFiniteLocallyFree q] in
/-- Through [Stacks, Tag 089W], `b • p^* x` is the cohomology of the twisted unit for `b`
applied to `x`. -/
theorem cohomologyIsoPushforward_hom_smul_cohomologyPullback (b : Γ(T, ⊤))
    (x : ((moduleGlobalSections X).rightDerived n).obj F) :
    haveI := isAffineHom_of_isPullback H
    (cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj F) n).hom.hom
        (restrictScalarsMk p.appTop.hom
          ((k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom b • (cohomologyPullback H F n).hom x :
            ((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F))) =
      (((moduleGlobalSections X).rightDerived n).map (twistedUnit k p F b)).hom x := by
  have := isAffineHom_of_isPullback H
  rw [smul_cohomologyPullback]
  exact hom_restrictScalarsMk_inv _ _ _

/-- `cohomologyBaseChangeInv` is a right inverse of the base change map. -/
theorem cohomologyBaseChangeLinearMap_cohomologyBaseChangeInv
    (he : letI := baseAlgebra q; ∀ b : Γ(T, ⊤), ∑ j, f j b • e j = b)
    (y : (baseRestrictScalars k).obj
      (((moduleGlobalSections Y).rightDerived n).obj ((Scheme.Modules.pullback p).obj F))) :
    cohomologyBaseChangeLinearMap H F n (cohomologyBaseChangeInv H F n e f y) = y := by
  let := baseAlgebra q
  have := isAffineHom_of_isPullback H
  set ω := cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj F) n
  set w := ω.hom.hom (restrictScalarsMk p.appTop.hom
    (restrictScalarsOut (k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom y))
  rw [cohomologyBaseChangeInv_apply, map_sum]
  have h1 : ∀ j, cohomologyBaseChangeLinearMap H F n (e j ⊗ₜ[Γ(S, ⊤)]
      restrictScalarsMk (iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom
        ((((moduleGlobalSections X).rightDerived n).map (trace H F (f j))).hom w)) =
      ω.inv.hom ((((moduleGlobalSections X).rightDerived n).map (twistedUnit k p F (e j))).hom
        ((((moduleGlobalSections X).rightDerived n).map (trace H F (f j))).hom w)) :=
    fun j => (cohomologyBaseChangeLinearMap_tmul H F n (e j) _).trans
      (smul_cohomologyPullback H F n (e j) _)
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  refine Eq.trans (map_sum ω.inv.hom _ _).symm ?_
  have h2 : ∑ j, (((moduleGlobalSections X).rightDerived n).map (twistedUnit k p F (e j))).hom
        ((((moduleGlobalSections X).rightDerived n).map (trace H F (f j))).hom w) =
      (((moduleGlobalSections X).rightDerived n).map
        (∑ j, trace H F (f j) ≫ twistedUnit k p F (e j))).hom w := by
    rw [CategoryTheory.Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [h2, sum_trace_comp_twistedUnit H F e f he, CategoryTheory.Functor.map_id, ModuleCat.hom_id,
    LinearMap.id_apply]
  exact congrArg (fun h => ModuleCat.Hom.hom h _) ω.hom_inv_id

/-- `cohomologyBaseChangeInv` is a left inverse of the base change map on pure tensors. -/
theorem cohomologyBaseChangeInv_cohomologyBaseChangeLinearMap_tmul
    (he : letI := baseAlgebra q; ∀ b : Γ(T, ⊤), ∑ j, f j b • e j = b) (b : Γ(T, ⊤))
    (x : (baseRestrictScalars iX).obj (((moduleGlobalSections X).rightDerived n).obj F)) :
    letI := baseAlgebra q
    cohomologyBaseChangeInv H F n e f (cohomologyBaseChangeLinearMap H F n (b ⊗ₜ[Γ(S, ⊤)] x)) =
      b ⊗ₜ[Γ(S, ⊤)] x := by
  let := baseAlgebra q
  have := isAffineHom_of_isPullback H
  have h0 : (cohomologyIsoPushforward p ((Scheme.Modules.pullback p).obj F) n).hom.hom
      (restrictScalarsMk p.appTop.hom (restrictScalarsOut (k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom
        (cohomologyBaseChangeLinearMap H F n (b ⊗ₜ[Γ(S, ⊤)] x)))) =
      (((moduleGlobalSections X).rightDerived n).map (twistedUnit k p F b)).hom
        (restrictScalarsOut (iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom x) := by
    rw [cohomologyBaseChangeLinearMap_tmul]
    exact cohomologyIsoPushforward_hom_smul_cohomologyPullback H F n b _
  have h1 : ∀ j, restrictScalarsMk (iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom
      ((((moduleGlobalSections X).rightDerived n).map (trace H F (f j))).hom
        ((((moduleGlobalSections X).rightDerived n).map (twistedUnit k p F b)).hom
          (restrictScalarsOut (iX.appLE ⊤ ⊤ (le_preimage_top iX ⊤)).hom x))) =
      f j b • x := by
    intro j
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp,
      twistedUnit_comp_trace]
    exact Scheme.rightDerived_sectionsFunctor_map_smulEnd_apply X _ n F _
  rw [cohomologyBaseChangeInv_apply, h0, Finset.sum_congr rfl fun j _ => by rw [h1 j],
    ← Finset.sum_congr rfl fun j _ => TensorProduct.smul_tmul (f j b) (e j) x,
    ← TensorProduct.sum_tmul, he]

end Inverse

/-- **The canonical base change map on cohomology is bijective** for a finite locally free `q`,
with no hypothesis on `X`. -/
theorem bijective_cohomologyBaseChangeLinearMap [Stacks.Morphisms.IsFiniteLocallyFree q]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Function.Bijective (cohomologyBaseChangeLinearMap H F n) := by
  let := baseAlgebra q
  obtain ⟨hflat, hfp⟩ := flat_and_finitePresentation_of_isFiniteLocallyFree q
    (appLE_top_eq_appTop q (le_preimage_top q ⊤))
  have : Module.Flat Γ(S, ⊤) Γ(T, ⊤) := hflat
  have : Module.FinitePresentation Γ(S, ⊤) Γ(T, ⊤) := hfp
  obtain ⟨m, e, f, he⟩ := exists_dualBasis_of_flat_of_finitePresentation Γ(S, ⊤) Γ(T, ⊤)
  refine Function.bijective_iff_has_inverse.2 ⟨cohomologyBaseChangeInv H F n e f, fun z => ?_,
    fun y => cohomologyBaseChangeLinearMap_cohomologyBaseChangeInv H F n e f he y⟩
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul b x => exact cohomologyBaseChangeInv_cohomologyBaseChangeLinearMap_tmul H F n e f he b x
  | add z w hz hw => rw [map_add, map_add, hz, hw]

/-- The underlying linear map of `cohomologyBaseChangeMap` is `cohomologyBaseChangeLinearMap`. -/
theorem cohomologyBaseChangeMap_hom (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    letI := baseAlgebra q
    (cohomologyBaseChangeMap H F n).hom = cohomologyBaseChangeLinearMap H F n := rfl

/-- **Finite locally free base change.** For a cartesian square of schemes

```
Y --p--> X
|        |
k        iX
v        v
T --q--> S
```

with `S = Spec A` and `T = Spec B` affine and `q` finite locally free, and for every
quasi-coherent `𝒪_X`-module `F` and every `n`, the canonical map
`Hⁿ(X, F) ⊗_A B ⟶ Hⁿ(Y, p^* F)`, `x ⊗ b ↦ b • p^* x`, is an isomorphism of `B`-modules, for
an arbitrary scheme `X`.

The map is `cohomologyBaseChangeMap`, the `B`-linear extension of the pullback map
`cohomologyPullback`. -/
@[stacks 0CKW]
theorem isIso_cohomologyBaseChangeMap [Stacks.Morphisms.IsFiniteLocallyFree q]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    IsIso (cohomologyBaseChangeMap H F n) := by
  let := baseAlgebra q
  exact (LinearEquiv.ofBijective _
    (bijective_cohomologyBaseChangeLinearMap H F n)).toModuleIso.isIso_hom

/-- **Finite locally free base change.** Let `φ : A ⟶ B` be a ring map making `B` a finite
locally free `A`-module, and consider a cartesian square of schemes

```
Y ------p-----> X
|               |
k               iX
v               v
Spec B --> Spec A
```

with bottom arrow `Spec φ`. For every quasi-coherent `𝒪_X`-module `F` and every `n`, the canonical
map `Hⁿ(X, F) ⊗_A B ⟶ Hⁿ(Y, p^* F)`, `x ⊗ b ↦ b • p^* x`, is an isomorphism of `B`-modules; here
`A` and `B` act through `Γ(Spec A, 𝒪)` and `Γ(Spec B, 𝒪)`, and `X` is an arbitrary scheme. -/
@[stacks 0CKW "as stated: B a finite locally free A-module"]
theorem isIso_cohomologyBaseChangeMap_of_isFiniteLocallyFree_module {A B : CommRingCat.{u}}
    (φ : A ⟶ B) {X Y : Scheme.{u}} {iX : X ⟶ Spec A} {p : Y ⟶ X} {k : Y ⟶ Spec B}
    (H : IsPullback p k iX (Spec.map φ))
    (hB : letI := φ.hom.toAlgebra; Module.IsFiniteLocallyFree A B)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    IsIso (cohomologyBaseChangeMap H F n) :=
  have : Stacks.Morphisms.IsFiniteLocallyFree (Spec.map φ) :=
    (Stacks.Morphisms.specMap_finiteLocallyFree_iff_module A B φ).2 hB
  isIso_cohomologyBaseChangeMap H F n


end BaseChange

end Stacks.Tag0CKW

end
