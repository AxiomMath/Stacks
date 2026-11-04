module

public import StacksFrontier.Cotangent.ConormalTorDifferential

/-!
# `H₂(L_{B/A}) = H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` as `B`-modules (Stacks 09D5)

Both sides of the formula of Remark 09D5 are `B`-modules: `H₂(L_{B/A})` is the homology of the
cotangent complex of `B`-modules, and `Tor₁^𝒪(𝒥, B̲)` is a sheaf of `B̲`-modules, because on
`U = (P → B)` the ideal `J = ker(P → B)` annihilates `Tor₁^P(J, B)`. This file proves the formula
as an isomorphism of `B`-modules,
`Stacks.Cotangent.cotangentComplexHomologyTwoLinearIsoTorOne`. The underlying argument is the one
of `StacksFrontier/Cotangent/ConormalTorDifferential.lean` (see its module docstring for the
identification of the differential with `d₂` of the spectral sequence of Remark 08R7); what is
added here is linearity over `B`.

## Main definitions

* `Stacks.Cotangent.TorOneTerm` and `Stacks.Cotangent.torOneSimplicialB`: `Tor₁^𝒪(𝒥, B̲)` on the
  standard resolution as a simplicial `B`-module, `n ↦ Tor₁^{Pₙ}(Jₙ, B) = ker(Jₙ ⊗_{Pₙ} Jₙ → Jₙ²)`
  with `B = Pₙ/Jₙ` acting (`Stacks.Cotangent.isTorsionBySet_torOne`).
* `Stacks.Cotangent.torOneMooreComplexB`: its Moore complex of `B`-modules, whose `H₀` is
  `H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` as a `B`-module.
* `Stacks.Cotangent.cotangentComplexHomologyTwoLinearIsoTorOne`: **Stacks 09D5**,
  `H₂(L_{B/A}) ≅ H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` as `B`-modules.

## Implementation notes

**Why linearity over `P₀`.** The connecting maps live on simplicial modules over the standard
resolution, which are not `B`-modules (`𝒥`, `𝒥²`, `𝒥 ⊗_𝒪 𝒥`). They are, however, modules over
the constant simplicial ring `P₀`, through the totally degenerate maps `P₀ → Pₙ`
(`Stacks.Cotangent.SimplicialModuleOver.toSimplicialZero`), and every map in the argument is
`P₀`-linear; on the two `B`-modules the action of `P₀` is through the augmentation `P₀ → B`
(`Stacks.Cotangent.standardResolutionAugmentationHom_degenerateMap`). So the whole argument runs
over `P₀`, and since `P₀ → B` is surjective, a `P₀`-linear isomorphism between two `B`-modules is
`B`-linear (`Stacks.Cotangent.isoOfRestrictScalarsIso`). The vanishing statements are
transported from the `A`-linear argument: vanishing of homology does not depend on the ring of
scalars (`Stacks.Cotangent.SimplicialModuleOver.isZero_homology_toSimplicialZero_iff`).

## References

* [Stacks Project, Tag 09D5](https://stacks.math.columbia.edu/tag/09D5)
* [Stacks Project, Tag 08R7](https://stacks.math.columbia.edu/tag/08R7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial AlgebraicTopology
open scoped TensorProduct

universe u v

namespace Stacks.Cotangent

open CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-! ### `Tor₁^𝒪(𝒥, B̲)` as a simplicial `B`-module -/

/-- The augmentation is compatible with every simplicial operator. -/
private theorem augmentation_map_aux {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (p : (standardResolution A B).left.obj n) :
    standardResolutionAugmentationHom.{u, v} A B m (((standardResolution A B).left.map f).hom p) =
      standardResolutionAugmentationHom.{u, v} A B n p := by
  have hnat := (standardResolution A B).hom.naturality f
  have h := ConcreteCategory.congr_hom hnat p
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h
  exact h

/-- The augmentation `Pₙ → B` sends the totally degenerate image of `r ∈ P₀` to the augmentation
of `r`. -/
theorem standardResolutionAugmentationHom_degenerateMap (n : SimplexCategoryᵒᵖ)
    (r : (standardResolution A B).left.obj (op ⦋0⦌)) :
    standardResolutionAugmentationHom.{u, v} A B n (degenerateMap _ n r) =
      standardResolutionAugmentationHom.{u, v} A B (op ⦋0⦌) r :=
  augmentation_map_aux A B (SimplexCategory.const n.unop ⦋0⦌ 0).op r

/-- The augmentation is compatible with every simplicial operator. -/
theorem standardResolutionAugmentationHom_map {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (p : (standardResolution A B).left.obj n) :
    standardResolutionAugmentationHom.{u, v} A B m (((standardResolution A B).left.map f).hom p) =
      standardResolutionAugmentationHom.{u, v} A B n p :=
  augmentation_map_aux A B f p

/-- `Jₙ` annihilates `Tor₁^{Pₙ}(Jₙ, B) = ker(Jₙ ⊗_{Pₙ} Jₙ → Jₙ²)`: for `j ∈ Jₙ`,
`j · (x ⊗ y) = j ⊗ xy`, which vanishes on the kernel of the multiplication. -/
theorem isTorsionBySet_torOne (n : SimplexCategoryᵒᵖ) :
    Module.IsTorsionBySet ((standardResolution A B).left.obj n)
      ↥(LinearMap.ker (Submodule.mulMap' (augmentationIdeal A B n) (augmentationIdeal A B n)))
      (augmentationIdeal A B n : Set ((standardResolution A B).left.obj n)) := by
  intro t j
  apply Subtype.ext
  let J := augmentationIdeal A B n
  let μ : J ⊗[(standardResolution A B).left.obj n] J →ₗ[(standardResolution A B).left.obj n] J :=
    (Submodule.inclusion Ideal.mul_le_left).comp (Submodule.mulMap' J J)
  have key : ∀ s : J ⊗[(standardResolution A B).left.obj n] J,
      (j : (standardResolution A B).left.obj n) • s = (⟨j.1, j.2⟩ : J) ⊗ₜ μ s := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [TensorProduct.smul_tmul']
      show (⟨j.1 * x.1, _⟩ : J) ⊗ₜ y = _
      have hx : (⟨j.1 * x.1, J.mul_mem_left _ x.2⟩ : J) = x.1 • (⟨j.1, j.2⟩ : J) := by
        apply Subtype.ext
        show j.1 * x.1 = x.1 * j.1
        ring
      rw [hx, TensorProduct.smul_tmul]
      congr 1
    | add s s' hs hs' => rw [smul_add, hs, hs', map_add, TensorProduct.tmul_add]
  have hμ : μ t.1 = 0 := by
    show Submodule.inclusion Ideal.mul_le_left (Submodule.mulMap' J J t.1) = 0
    rw [LinearMap.mem_ker.1 t.2, map_zero]
  show (j : (standardResolution A B).left.obj n) • t.1 = 0
  rw [key, hμ, TensorProduct.tmul_zero]

/-- A simplicial operator of `𝒥 ⊗_𝒪 𝒥` preserves the kernel of the multiplication. -/
theorem map_mem_ker_mulMap' {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : (idealTensorIdeal.{u, v} A B).obj n)
    (hx : x ∈ LinearMap.ker
      (Submodule.mulMap' (augmentationIdeal A B n) (augmentationIdeal A B n))) :
    (idealTensorIdeal.{u, v} A B).map f x ∈
      LinearMap.ker (Submodule.mulMap' (augmentationIdeal A B m) (augmentationIdeal A B m)) := by
  rw [LinearMap.mem_ker] at hx ⊢
  have h := (idealMulHom.{u, v} A B).naturality f x
  change Submodule.mulMap' _ _ _ = _ at h
  rw [h]
  show (augmentationIdealSqModule.{u, v} A B).map f (Submodule.mulMap' _ _ x) = 0
  rw [hx, map_zero]

/-- The term of `Tor₁^𝒪(𝒥, B̲)` in degree `n`, `ker(Jₙ ⊗_{Pₙ} Jₙ → Jₙ²)`, to be read as a
`B`-module: `Jₙ` annihilates it, so it is a module over `Pₙ/Jₙ = B`. -/
def TorOneTerm (n : SimplexCategoryᵒᵖ) : Type (max u v) :=
  ↥(LinearMap.ker (Submodule.mulMap' (augmentationIdeal A B n) (augmentationIdeal A B n)))

/-- The identification of `TorOneTerm` with the kernel. -/
def torOneTermEquiv (n : SimplexCategoryᵒᵖ) : TorOneTerm.{u, v} A B n ≃
    ↥(LinearMap.ker (Submodule.mulMap' (augmentationIdeal A B n) (augmentationIdeal A B n))) :=
  Equiv.refl _

/-- `Tor₁^{Pₙ}(Jₙ, B)` is an abelian group. -/
instance (n : SimplexCategoryᵒᵖ) : AddCommGroup (TorOneTerm.{u, v} A B n) :=
  inferInstanceAs (AddCommGroup
    ↥(LinearMap.ker (Submodule.mulMap' (augmentationIdeal A B n) (augmentationIdeal A B n))))

/-- `Pₙ/Jₙ ≅ B`. -/
abbrev quotientAugmentationEquiv (n : SimplexCategoryᵒᵖ) :
    ((standardResolution A B).left.obj n ⧸ augmentationIdeal A B n) ≃+* (B : Type (max u v)) :=
  RingHom.quotientKerEquivOfSurjective (f := ((standardResolution A B).hom.app n).hom.toRingHom)
    (surjective_standardResolutionAugmentationHom.{u, v} A B n)

/-- `Tor₁^{Pₙ}(Jₙ, B)` is a `B`-module: `Jₙ` annihilates it, and `B = Pₙ/Jₙ`. -/
instance (n : SimplexCategoryᵒᵖ) : Module (B : Type (max u v)) (TorOneTerm.{u, v} A B n) :=
  letI := (isTorsionBySet_torOne.{u, v} A B n).module
  Module.compHom
    ↥(LinearMap.ker (Submodule.mulMap' (augmentationIdeal A B n) (augmentationIdeal A B n)))
    (quotientAugmentationEquiv.{u, v} A B n).symm.toRingHom

/-- `b ∈ B` acts on `Tor₁^{Pₙ}(Jₙ, B)` as any of its lifts `p ∈ Pₙ`. -/
theorem torOneTermEquiv_smul (n : SimplexCategoryᵒᵖ) (b : (B : Type (max u v)))
    (p : (standardResolution A B).left.obj n)
    (hp : standardResolutionAugmentationHom.{u, v} A B n p = b)
    (t : TorOneTerm.{u, v} A B n) :
    torOneTermEquiv.{u, v} A B n (b • t) = p • torOneTermEquiv.{u, v} A B n t := by
  let := (isTorsionBySet_torOne.{u, v} A B n).module
  have he : (quotientAugmentationEquiv.{u, v} A B n).symm b =
      Ideal.Quotient.mk (augmentationIdeal A B n) p := by
    rw [RingEquiv.symm_apply_eq]
    exact hp.symm
  have h : torOneTermEquiv.{u, v} A B n (b • t) =
      ((quotientAugmentationEquiv.{u, v} A B n).symm b) • torOneTermEquiv.{u, v} A B n t := rfl
  rw [h, he]
  rfl

/-- The simplicial operator of `Tor₁^𝒪(𝒥, B̲)` on the kernels. -/
def torOneMapFun {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (t : TorOneTerm.{u, v} A B n) :
    TorOneTerm.{u, v} A B m :=
  (torOneTermEquiv.{u, v} A B m).symm
    ⟨(idealTensorIdeal.{u, v} A B).map f (torOneTermEquiv.{u, v} A B n t).1,
      map_mem_ker_mulMap'.{u, v} A B f _ (torOneTermEquiv.{u, v} A B n t).2⟩

/-- The simplicial operator of `Tor₁^𝒪(𝒥, B̲)` is that of `𝒥 ⊗_𝒪 𝒥`. -/
theorem torOneMapFun_val {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (t : TorOneTerm.{u, v} A B n) :
    (torOneTermEquiv.{u, v} A B m (torOneMapFun.{u, v} A B f t)).1 =
      (idealTensorIdeal.{u, v} A B).map f (torOneTermEquiv.{u, v} A B n t).1 := rfl

/-- The simplicial operator of `Tor₁^𝒪(𝒥, B̲)`, `B`-linearly. -/
def torOneMapB {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    TorOneTerm.{u, v} A B n →ₗ[(B : Type (max u v))] TorOneTerm.{u, v} A B m where
  toFun := torOneMapFun.{u, v} A B f
  map_add' t t' := Subtype.ext (map_add ((idealTensorIdeal.{u, v} A B).map f)
    (torOneTermEquiv.{u, v} A B n t).1 (torOneTermEquiv.{u, v} A B n t').1)
  map_smul' b t := by
    obtain ⟨p, hp⟩ := surjective_standardResolutionAugmentationHom.{u, v} A B n b
    have h2 := torOneTermEquiv_smul.{u, v} A B m b (((standardResolution A B).left.map f).hom p)
      ((standardResolutionAugmentationHom_map.{u, v} A B f p).trans hp)
      (torOneMapFun.{u, v} A B f t)
    apply (torOneTermEquiv.{u, v} A B m).injective
    refine Eq.trans ?_ h2.symm
    apply Subtype.ext
    rw [torOneMapFun_val, torOneTermEquiv_smul.{u, v} A B n b p hp t]
    exact (idealTensorIdeal.{u, v} A B).map_smul f p _

/-- **`Tor₁^𝒪(𝒥, B̲)` on the standard resolution, as a simplicial `B`-module.** -/
def torOneSimplicialB : SimplicialObject (ModuleCat.{max u v} B) where
  obj n := ModuleCat.of B (TorOneTerm.{u, v} A B n)
  map f := ModuleCat.ofHom (torOneMapB.{u, v} A B f)
  map_id n := by
    ext t
    exact Subtype.ext ((idealTensorIdeal.{u, v} A B).map_id n (torOneTermEquiv.{u, v} A B n t).1)
  map_comp f g := by
    ext t
    exact Subtype.ext ((idealTensorIdeal.{u, v} A B).map_comp f g
      (torOneTermEquiv.{u, v} A B _ t).1)

/-- The Moore complex of `Tor₁^𝒪(𝒥, B̲)` as a complex of `B`-modules; its homology is
`H_*(C_{B/A}, Tor₁^𝒪(𝒥, B̲))` with its `B`-module structure. -/
abbrev torOneMooreComplexB : ChainComplex (ModuleCat.{max u v} B) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj (torOneSimplicialB.{u, v} A B)

/-! ### The two short exact sequences over `P₀` -/

/-- The term `P₀` of the standard resolution. -/
abbrev resolutionZero : Type (max u v) := (standardResolution A B).left.obj (op ⦋0⦌)

/-- The augmentation `P₀ → B`; it is surjective. -/
abbrev augmentationZero : resolutionZero.{u, v} A B →+* (B : Type (max u v)) :=
  standardResolutionAugmentationHom.{u, v} A B (op ⦋0⦌)

/-- `B`-modules read as `P₀`-modules. -/
abbrev restrictZero : ModuleCat.{max u v} B ⥤ ModuleCat.{max u v} (resolutionZero.{u, v} A B) :=
  ModuleCat.restrictScalars (augmentationZero.{u, v} A B)

/-- `Tor₁^𝒪(𝒥, B̲)`, read as a simplicial `P₀`-module. -/
abbrev torOneZero : SimplicialObject (ModuleCat.{max u v} (resolutionZero.{u, v} A B)) :=
  torOneSimplicialB.{u, v} A B ⋙ restrictZero.{u, v} A B

/-- `Tor₁^{Pₙ}(Jₙ, B)` as a `P₀`-module, through `P₀ → B`. -/
instance (n : SimplexCategoryᵒᵖ) : Module (resolutionZero.{u, v} A B) (TorOneTerm.{u, v} A B n) :=
  Module.compHom (TorOneTerm.{u, v} A B n) (augmentationZero.{u, v} A B)

/-- The inclusion `Tor₁^{Pₙ}(Jₙ, B) ⊂ Jₙ ⊗_{Pₙ} Jₙ`, `P₀`-linearly. -/
def torOneZeroInclusionApp (n : SimplexCategoryᵒᵖ) :
    TorOneTerm.{u, v} A B n →ₗ[resolutionZero.{u, v} A B]
      (idealTensorIdeal.{u, v} A B).ObjZero n where
  toFun t := (torOneTermEquiv.{u, v} A B n t).1
  map_add' _ _ := rfl
  map_smul' r t := by
    exact congrArg Subtype.val (torOneTermEquiv_smul.{u, v} A B n (augmentationZero.{u, v} A B r)
      (degenerateMap _ n r) (standardResolutionAugmentationHom_degenerateMap.{u, v} A B n r) t)

/-- The inclusion `Tor₁^𝒪(𝒥, B̲) ⊂ 𝒥 ⊗_𝒪 𝒥` of simplicial `P₀`-modules. -/
def torOneZeroInclusion :
    torOneZero.{u, v} A B ⟶ (idealTensorIdeal.{u, v} A B).toSimplicialZero where
  app n := ModuleCat.ofHom (X := TorOneTerm.{u, v} A B n)
    (Y := (idealTensorIdeal.{u, v} A B).ObjZero n) (torOneZeroInclusionApp.{u, v} A B n)
  naturality _ _ _ := rfl

/-- The short complex `Tor₁^𝒪(𝒥, B̲) → 𝒥 ⊗_𝒪 𝒥 → 𝒥²` of simplicial `P₀`-modules. -/
abbrev torOneShortComplexZero :
    ShortComplex (SimplicialObject (ModuleCat.{max u v} (resolutionZero.{u, v} A B))) where
  X₁ := torOneZero.{u, v} A B
  X₂ := (idealTensorIdeal.{u, v} A B).toSimplicialZero
  X₃ := (augmentationIdealSqModule.{u, v} A B).toSimplicialZero
  f := torOneZeroInclusion.{u, v} A B
  g := (idealMulHom.{u, v} A B).toSimplicialZero
  zero := by
    refine NatTrans.ext (funext fun n => ?_)
    ext t
    exact LinearMap.mem_ker.1 (torOneTermEquiv.{u, v} A B n t).2

/-- `0 → Tor₁ → Jₙ ⊗ Jₙ → Jₙ² → 0` is exact in every degree. -/
theorem torOneShortComplexZero_shortExact_app (n : SimplexCategoryᵒᵖ) :
    ((torOneShortComplexZero.{u, v} A B).map
      ((evaluation SimplexCategoryᵒᵖ _).obj n)).ShortExact where
  exact := by
    exact (ShortComplex.moduleCat_exact_iff _).2 fun x hx =>
      ⟨(torOneTermEquiv.{u, v} A B n).symm ⟨x, hx⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).2 fun t t' h =>
    (torOneTermEquiv.{u, v} A B n).injective (Subtype.ext h)
  epi_g := (ModuleCat.epi_iff_surjective _).2 (Submodule.mulMap'_surjective _ _)

/-- The Moore complexes of `0 → Tor₁^𝒪(𝒥, B̲) → 𝒥 ⊗_𝒪 𝒥 → 𝒥² → 0` are short exact. -/
theorem torOneShortComplexZero_moore_shortExact :
    ((torOneShortComplexZero.{u, v} A B).map
      (alternatingFaceMapComplex
        (ModuleCat.{max u v} (resolutionZero.{u, v} A B)))).ShortExact := by
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i =>
    torOneShortComplexZero_shortExact_app.{u, v} A B (op ⦋i⦌)

/-- `𝒥/𝒥²`, read as a simplicial `P₀`-module. -/
abbrev conormalZero : SimplicialObject (ModuleCat.{max u v} (resolutionZero.{u, v} A B)) :=
  conormalSimplicialModule.{u, v} A B ⋙ restrictZero.{u, v} A B

/-- The class map `Jₙ → Jₙ/Jₙ²`, `P₀`-linearly. -/
def idealToConormalZeroApp (n : SimplexCategoryᵒᵖ) :
    (augmentationIdealModule.{u, v} A B).ObjZero n →ₗ[resolutionZero.{u, v} A B]
      ↑((restrictZero.{u, v} A B).obj ((conormalSimplicialModule.{u, v} A B).obj n)) where
  toFun x := Algebra.Extension.Cotangent.mk (P := conormalExtension.{u, v} A B n)
    ((augmentationIdealModule.{u, v} A B).objZeroEquiv n x)
  map_add' x y := map_add _ _ _
  map_smul' r x := by
    have h1 := (Algebra.Extension.Cotangent.mk (P := conormalExtension.{u, v} A B n)).map_smul
      (degenerateMap _ n r)
      ((augmentationIdealModule.{u, v} A B).objZeroEquiv n x : (conormalExtension.{u, v} A B n).ker)
    refine h1.trans ?_
    change (standardResolutionAugmentationHom.{u, v} A B n (degenerateMap _ n r) •
        Algebra.Extension.Cotangent.mk (P := conormalExtension.{u, v} A B n)
          ((augmentationIdealModule.{u, v} A B).objZeroEquiv n x) :
          (conormalExtension.{u, v} A B n).Cotangent) =
      (augmentationZero.{u, v} A B r • Algebra.Extension.Cotangent.mk
          (P := conormalExtension.{u, v} A B n)
          ((augmentationIdealModule.{u, v} A B).objZeroEquiv n x) :
          (conormalExtension.{u, v} A B n).Cotangent)
    rw [standardResolutionAugmentationHom_degenerateMap]

/-- The class map `𝒥 → 𝒥/𝒥²` of simplicial `P₀`-modules. -/
def idealToConormalZero :
    (augmentationIdealModule.{u, v} A B).toSimplicialZero ⟶ conormalZero.{u, v} A B where
  app n := ModuleCat.ofHom (X := (augmentationIdealModule.{u, v} A B).ObjZero n)
    (Y := ↑((restrictZero.{u, v} A B).obj ((conormalSimplicialModule.{u, v} A B).obj n)))
    (idealToConormalZeroApp.{u, v} A B n)
  naturality n m f := by
    ext x
    exact (conormalSimplicialModule_map_mk.{u, v} A B f x
      ((augmentationIdealModule.{u, v} A B).map f x) rfl).symm

/-- The short complex `𝒥² → 𝒥 → 𝒥/𝒥²` of simplicial `P₀`-modules. -/
abbrev conormalShortComplexZero :
    ShortComplex (SimplicialObject (ModuleCat.{max u v} (resolutionZero.{u, v} A B))) where
  X₁ := (augmentationIdealSqModule.{u, v} A B).toSimplicialZero
  X₂ := (augmentationIdealModule.{u, v} A B).toSimplicialZero
  X₃ := conormalZero.{u, v} A B
  f := (idealSqInclusion.{u, v} A B).toSimplicialZero
  g := idealToConormalZero.{u, v} A B
  zero := by
    refine NatTrans.ext (funext fun n => ?_)
    ext x
    exact (Algebra.Extension.Cotangent.mk_eq_zero_iff (P := conormalExtension.{u, v} A B n)
      ⟨x.1, Ideal.mul_le_left x.2⟩).2 (by rw [sq]; exact x.2)

/-- `0 → Jₙ² → Jₙ → Jₙ/Jₙ² → 0` is exact in every degree. -/
theorem conormalShortComplexZero_shortExact_app (n : SimplexCategoryᵒᵖ) :
    ((conormalShortComplexZero.{u, v} A B).map
      ((evaluation SimplexCategoryᵒᵖ _).obj n)).ShortExact where
  exact := by
    refine (ShortComplex.moduleCat_exact_iff _).2 fun x hx => ?_
    let y : (conormalExtension.{u, v} A B n).ker := x
    have hy : Algebra.Extension.Cotangent.mk y = 0 := hx
    have hx' := (Algebra.Extension.Cotangent.mk_eq_zero_iff y).1 hy
    rw [sq] at hx'
    exact ⟨(⟨y.1, hx'⟩ : ↥(augmentationIdeal A B n * augmentationIdeal A B n)), rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).2 fun x y h =>
    Subtype.ext (congrArg Subtype.val h :)
  epi_g := (ModuleCat.epi_iff_surjective _).2 Algebra.Extension.Cotangent.mk_surjective

/-- The Moore complexes of `0 → 𝒥² → 𝒥 → 𝒥/𝒥² → 0` are short exact. -/
theorem conormalShortComplexZero_moore_shortExact :
    ((conormalShortComplexZero.{u, v} A B).map
      (alternatingFaceMapComplex
        (ModuleCat.{max u v} (resolutionZero.{u, v} A B)))).ShortExact := by
  exact HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i =>
    conormalShortComplexZero_shortExact_app.{u, v} A B (op ⦋i⦌)

/-! ### The differential over `P₀`, and the `B`-linear formula -/

/-- The connecting map `H₂(C_{B/A}, 𝒥/𝒥²) → H₁(C_{B/A}, 𝒥²)`, over `P₀`. -/
abbrev conormalToSqδZero :
    ((alternatingFaceMapComplex (ModuleCat.{max u v} (resolutionZero.{u, v} A B))).obj
        (conormalZero.{u, v} A B)).homology 2 ⟶
      ((alternatingFaceMapComplex (ModuleCat.{max u v} (resolutionZero.{u, v} A B))).obj
        (augmentationIdealSqModule.{u, v} A B).toSimplicialZero).homology 1 :=
  (conormalShortComplexZero_moore_shortExact.{u, v} A B).δ 2 1 rfl

/-- The connecting map `H₁(C_{B/A}, 𝒥²) → H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))`, over `P₀`. -/
abbrev sqToTorOneδZero :
    ((alternatingFaceMapComplex (ModuleCat.{max u v} (resolutionZero.{u, v} A B))).obj
        (augmentationIdealSqModule.{u, v} A B).toSimplicialZero).homology 1 ⟶
      ((alternatingFaceMapComplex (ModuleCat.{max u v} (resolutionZero.{u, v} A B))).obj
        (torOneZero.{u, v} A B)).homology 0 :=
  (torOneShortComplexZero_moore_shortExact.{u, v} A B).δ 1 0 rfl

/-- `H₂(𝒥) = H₁(𝒥) = 0` makes the first connecting map invertible. -/
instance isIso_conormalToSqδZero : IsIso (conormalToSqδZero.{u, v} A B) :=
  (conormalShortComplexZero_moore_shortExact.{u, v} A B).isIso_δ 2 1 rfl
    ((SimplicialModuleOver.isZero_homology_toSimplicialZero_iff _ 2).2
      (isZero_homology_augmentationIdeal.{u, v} A B 2))
    ((SimplicialModuleOver.isZero_homology_toSimplicialZero_iff _ 1).2
      (isZero_homology_augmentationIdeal.{u, v} A B 1))

/-- `H₁(𝒥 ⊗_𝒪 𝒥) = H₀(𝒥 ⊗_𝒪 𝒥) = 0` makes the second connecting map invertible. -/
instance isIso_sqToTorOneδZero : IsIso (sqToTorOneδZero.{u, v} A B) :=
  (torOneShortComplexZero_moore_shortExact.{u, v} A B).isIso_δ 1 0 rfl
    ((SimplicialModuleOver.isZero_homology_toSimplicialZero_iff _ 1).2
      (isZero_homology_one_idealTensorIdeal.{u, v} A B))
    ((SimplicialModuleOver.isZero_homology_toSimplicialZero_iff _ 0).2
      (isZero_homology_zero_idealTensorIdeal.{u, v} A B))

attribute [local instance] Functor.preservesHomologyOfExact

/-- Restriction of scalars commutes with the homology of Moore complexes. -/
def restrictScalarsMooreHomologyIso {R S : Type (max u v)} [CommRing R] [CommRing S] (f : R →+* S)
    (X : SimplicialObject (ModuleCat.{max u v} S)) (n : ℕ) :
    (ModuleCat.restrictScalars f).obj
        (((alternatingFaceMapComplex (ModuleCat.{max u v} S)).obj X).homology n) ≅
      ((alternatingFaceMapComplex (ModuleCat.{max u v} R)).obj
        (X ⋙ ModuleCat.restrictScalars f)).homology n :=
  ((((alternatingFaceMapComplex (ModuleCat.{max u v} S)).obj X).sc n).mapHomologyIso
      (ModuleCat.restrictScalars f)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso
        (ModuleCat.restrictScalars.{max u v} f)).app X)

/-- An isomorphism of modules after restriction of scalars along a surjective ring map is an
isomorphism of modules. -/
def isoOfRestrictScalarsIso {R S : Type (max u v)} [Ring R] [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) {M N : ModuleCat.{max u v} S}
    (e : (ModuleCat.restrictScalars f).obj M ≅ (ModuleCat.restrictScalars f).obj N) : M ≅ N :=
  LinearEquiv.toModuleIso
    { toFun := e.hom.hom
      invFun := e.inv.hom
      map_add' := map_add e.hom.hom
      map_smul' := fun s x => by
        obtain ⟨r, rfl⟩ := hf s
        exact e.hom.hom.map_smul r x
      left_inv := fun x => ConcreteCategory.congr_hom e.hom_inv_id x
      right_inv := fun x => ConcreteCategory.congr_hom e.inv_hom_id x }

/-- **The differential `H₂(C_{B/A}, 𝒥/𝒥²) → H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))`, read over `P₀`**: the
composite of the two connecting maps, between the two `B`-modules with scalars restricted along
`P₀ → B`. -/
def conormalTorOneDifferentialZero :
    (restrictZero.{u, v} A B).obj ((conormalMooreComplex.{u, v} A B).homology 2) ⟶
      (restrictZero.{u, v} A B).obj ((torOneMooreComplexB.{u, v} A B).homology 0) :=
  (restrictScalarsMooreHomologyIso.{u, v} (augmentationZero.{u, v} A B)
      (conormalSimplicialModule.{u, v} A B) 2).hom ≫ conormalToSqδZero.{u, v} A B ≫
    sqToTorOneδZero.{u, v} A B ≫
      (restrictScalarsMooreHomologyIso.{u, v} (augmentationZero.{u, v} A B)
        (torOneSimplicialB.{u, v} A B) 0).inv

/-- The differential over `P₀` is an isomorphism. -/
instance isIso_conormalTorOneDifferentialZero :
    IsIso (conormalTorOneDifferentialZero.{u, v} A B) := by
  unfold conormalTorOneDifferentialZero
  infer_instance

/-- **Stacks 09D5: `H₂(L_{B/A}) = H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))`, as `B`-modules.** `H₂(L_{B/A})`
is the homology in cohomological degree `-2` of the cotangent complex of Tag 08PN, and the
right-hand side is `H₀` of the Moore complex of the simplicial `B`-module
`n ↦ Tor₁^{Pₙ}(Jₙ, B)` on the standard resolution. The isomorphism is
`H₂(L_{B/A}) ≅ H₂(C_{B/A}, 𝒥/𝒥²)` followed by the differential, made `B`-linear by
`Stacks.Cotangent.isoOfRestrictScalarsIso`. -/
@[stacks 09D5 "H₂(L_{B/A}) = H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲)), an isomorphism of B-modules"]
def cotangentComplexHomologyTwoLinearIsoTorOne :
    (cotangentComplex A B).homology (-2) ≅ (torOneMooreComplexB.{u, v} A B).homology 0 :=
  isoOfRestrictScalarsIso.{u, v} (augmentationZero.{u, v} A B)
    (surjective_standardResolutionAugmentationHom.{u, v} A B (op ⦋0⦌))
    ((restrictZero.{u, v} A B).mapIso (cotangentComplexHomologyTwoIsoConormal.{u, v} A B) ≪≫
      asIso (conormalTorOneDifferentialZero.{u, v} A B))

end Stacks.Cotangent
