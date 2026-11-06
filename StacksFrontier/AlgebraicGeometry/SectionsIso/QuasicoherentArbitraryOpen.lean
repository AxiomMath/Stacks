module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.CechDegreewise
public import StacksFrontier.AlgebraicGeometry.SectionsIso.Descent
public import StacksFrontier.RingTheory.TensorProduct.TensorPi

/-!
# Degree-zero base change for every quasi-coherent module, over an arbitrary scheme

Let

```
Y --p--> X
|        |
k        iX
v        v
T --q--> S
```

be a cartesian square of schemes with `S` and `T` affine, and let `F` be a quasi-coherent
`𝒪_X`-module. For every open `U` of `X` the canonical comparison

  `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ(p^* F, p⁻¹U)`

is `Stacks.AlgebraicGeometry.SectionsBaseChange.sectionsBaseChangeMap`, and
`bijective_sectionsBaseChangeMap_of_isAffineOpen` inverts it when `U` is affine. This file
removes the affineness of `U`: when `Γ(T, ⊤)` is a flat, finitely presented `Γ(S, ⊤)`-module the
comparison is bijective over **every** open of **every** scheme `X`, with no quasi-compactness,
quasi-separatedness or separatedness hypothesis anywhere.

Specialised to `U = ⊤` and to a finite locally free `q`, this is the degree-zero assertion of
[Stacks, Tag 0CKW] for an arbitrary quasi-coherent module.
`Stacks.Tag0CKW.isIso_globalSectionsBaseChange_of_finiteLocallyFree` is the same assertion for
`F = 𝒪_X`, stated through Mathlib's `AlgebraicGeometry.pushoutSection`; what is added here is
the passage from the structure sheaf to an arbitrary quasi-coherent module.

## The argument

Cover `U` by **all** of the affine opens it contains — an index type with no finiteness and no
smallness condition. Writing `A = Γ(S, ⊤)`, `B = Γ(T, ⊤)` and `M(W) = Γ(F, W)`, the sheaf
condition for `F` on that cover is an exact sequence of `A`-modules

  `0 ⟶ M(U) ⟶ ∏ₐ M(Vₐ) ⟶ ∏ₐ,ᵦ M(Vₐ ⊓ Vᵦ)`.

Two properties of `B` carry it through `B ⊗_A -`: flatness makes the functor exact, and finite
presentation makes it commute with the two products — that is [Stacks, Tag 059K], here as
`TensorProduct.piRightOfFinitePresentation`, and it is what lets the cover be infinite. The
comparison is already known over each `Vₐ`, which is affine; the pairwise intersections
`Vₐ ⊓ Vᵦ` need not be affine, and over them only *injectivity* is used — which is the first
theorem below, proved for an arbitrary open from the affine case alone.

This is the sentence *"as `B` is finitely presented as an `A`-module we see that tensoring with
`B` over `A` commutes with products"* in the proof of [Stacks, Tag 0CKW], carried out on
sections rather than on a Čech complex.

## Main results

* `Stacks.Tag0CKW.injective_sectionsBaseChangeMap`: the comparison is injective over every open
  of every scheme. This is the module-valued counterpart of
  `Stacks.Tag0CKW.mono_pushoutSection_of_isAffineOpen_base`.
* `Stacks.Tag0CKW.bijective_sectionsBaseChangeMap`: it is bijective over every open.
* `Stacks.Tag0CKW.bijective_sectionsBaseChangeMap_of_isFiniteLocallyFree`: the same with the
  hypotheses on `q` in their geometric form, `Stacks.Morphisms.IsFiniteLocallyFree`.
* `Stacks.Tag0CKW.bijective_globalSectionsBaseChange_of_finiteLocallyFree`: the degree-zero
  case of [Stacks, Tag 0CKW] for an arbitrary quasi-coherent module, over `⊤`; the statement in
  every degree is `Stacks.Tag0CKW.isIso_cohomologyBaseChangeMap`.

## References

* [Stacks Project, Tag 0CKW](https://stacks.math.columbia.edu/tag/0CKW)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 059K](https://stacks.math.columbia.edu/tag/059K)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

universe u

namespace Stacks.Tag0CKW

/-! ### Base change of a product of modules -/

section Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [Module.FinitePresentation A B] {ι : Type u} (M : ι → Type u)
  [∀ a, AddCommGroup (M a)] [∀ a, Module A (M a)]

/-- **Base change of a map into a product, read componentwise.** -/
theorem piRight_lTensor_pi_apply {N : Type u} [AddCommGroup N] [Module A N]
    (f : ∀ a, N →ₗ[A] M a) (a : ι) (w : B ⊗[A] N) :
    TensorProduct.piRightOfFinitePresentation A B B M
        (LinearMap.lTensor B (LinearMap.pi f) w) a =
      LinearMap.lTensor B (f a) w := by
  induction w with
  | tmul b m => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- **Base change of a map out of a product, read through the comparison.** -/
theorem lTensor_comp_proj_apply {P : Type u} [AddCommGroup P] [Module A P] (a : ι)
    (g : M a →ₗ[A] P) (z : B ⊗[A] (∀ b, M b)) :
    LinearMap.lTensor B (g ∘ₗ (LinearMap.proj a : (∀ b, M b) →ₗ[A] M a)) z =
      LinearMap.lTensor B g (TensorProduct.piRightOfFinitePresentation A B B M z a) := by
  induction z with
  | tmul b m => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Algebra

/-! ### The cover of an arbitrary open by all the affine opens inside it -/

/-- The affine opens contained in a given open. -/
abbrev affineOpensIn {X : Scheme.{u}} (U : X.Opens) : Type u :=
  { V : X.affineOpens // (V : X.Opens) ≤ U }

/-- **Every open of every scheme is covered by the affine opens it contains.** The index type
carries no finiteness condition; this is the quasi-compactness-free cover that
[Stacks, Tag 0CKW] runs on. -/
theorem le_iSup_affineOpensIn {X : Scheme.{u}} (U : X.Opens) :
    U ≤ ⨆ a : affineOpensIn U, (a.1 : X.Opens) := by
  intro x hx
  obtain ⟨V, hVmem, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (U := U) (x := x) hx
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, hVmem⟩, hVU⟩, hxV⟩

/-! ### Injectivity over an arbitrary open -/

section

variable {S T X Y : Scheme.{u}} {q : T ⟶ S} {iX : X ⟶ S} {p : Y ⟶ X} {k : Y ⟶ T}

/-- **The canonical degree-zero comparison is injective over every open.** For a cartesian
square with `S` and `T` affine and `Γ(T, ⊤)` a flat, finitely presented `Γ(S, ⊤)`-module, the
map `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ(p^* F, p⁻¹U)` is injective for *every* open `U` of `X`,
with no hypothesis on `X`.

Only the affine case `bijective_sectionsBaseChangeMap_of_isAffineOpen` is used: cover `U` by the
affine opens it contains, note that `Γ(F, U)` injects into the product of the `Γ(F, Vₐ)` because
`F` is a sheaf, and carry that injection through `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} -`, which is exact
(flatness) and commutes with the product ([Stacks, Tag 059K]).

This is the module-valued counterpart of
`Stacks.Tag0CKW.mono_pushoutSection_of_isAffineOpen_base`, which is the same statement for the
structure sheaf. -/
theorem injective_sectionsBaseChangeMap (H : IsPullback p k iX q) [IsAffine S] [IsAffine T]
    (F : X.Modules) [F.IsQuasicoherent]
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
    (hfp : letI := (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom.toAlgebra;
      Module.FinitePresentation ↑Γ(S, ⊤) ↑Γ(T, ⊤))
    (U : X.Opens) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Function.Injective (sectionsBaseChangeMap H F U) := by
  let algAB := baseAlgebra q
  let modAF : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
  let modAG : ∀ W : X.Opens,
      Module Γ(S, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let modBG : ∀ W : X.Opens,
      Module Γ(T, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let towerG : ∀ W : X.Opens,
      IsScalarTower Γ(S, ⊤) Γ(T, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  have : Module.Flat Γ(S, ⊤) Γ(T, ⊤) := hq
  have : Module.FinitePresentation Γ(S, ⊤) Γ(T, ⊤) := hfp
  -- the cover of `U` by all the affine opens inside it
  set ι := affineOpensIn U
  set V : ι → X.Opens := fun a => (a.1 : X.Opens)
  have hVle : ∀ a : ι, V a ≤ U := fun a => a.2
  have hcover : U ≤ ⨆ a : ι, V a := le_iSup_affineOpensIn U
  -- the restriction map of `F` into the product over the cover
  set r : Γ(F, U) →ₗ[Γ(S, ⊤)] (∀ a : ι, Γ(F, V a)) :=
    LinearMap.pi (fun a => baseResHom iX F (hVle a)) with hrdef
  have hrB : Function.Injective (LinearMap.lTensor Γ(T, ⊤) r) :=
    Module.Flat.lTensor_preserves_injective_linearMap r fun s t hst =>
      TopCat.Sheaf.eq_of_locally_eq' ⟨F.presheaf, Scheme.Modules.isSheaf F⟩
        V U (fun a => homOfLE (hVle a)) hcover s t fun a => congrFun hst a
  rw [injective_iff_map_eq_zero]
  intro z hz
  refine hrB ?_
  rw [map_zero]
  refine (TensorProduct.piRightOfFinitePresentation Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤)
    (fun a : ι => ↑Γ(F, V a))).injective ?_
  rw [map_zero]
  funext a
  rw [hrdef, piRight_lTensor_pi_apply (fun a : ι => ↑Γ(F, V a))
    (fun a => baseResHom iX F (hVle a)) a z]
  refine (bijective_sectionsBaseChangeMap_of_isAffineOpen H F a.1.2).1 ?_
  rw [Pi.zero_apply, map_zero, sectionsBaseChangeMap_comm_res H F (hVle a) z, hz, map_zero]

/-! ### Bijectivity over an arbitrary open -/

/-- Restriction of sections of `F` composes. -/
theorem baseResHom_trans (g : X ⟶ S) (F : X.Modules) {U V W : X.Opens}
    (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(F, U)) :
    baseResHom g F h₂ (baseResHom g F h₁ s) = baseResHom g F (h₂.trans h₁) s := by
  have e : F.presheaf.map (homOfLE h₁).op ≫ F.presheaf.map (homOfLE h₂).op =
      F.presheaf.map (homOfLE (h₂.trans h₁)).op := by
    rw [← Functor.map_comp]
    rfl
  exact congrArg (fun m : Γ(F, U) ⟶ Γ(F, W) => ConcreteCategory.hom m s) e

/-- Restriction of sections of `p^* F` along preimages composes. -/
theorem pullbackBaseResHom_trans (k : Y ⟶ T) (p : Y ⟶ X) (F : X.Modules) {U V W : X.Opens}
    (h₁ : V ≤ U) (h₂ : W ≤ V) (y : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)) :
    pullbackBaseResHom k p F h₂ (pullbackBaseResHom k p F h₁ y) =
      pullbackBaseResHom k p F (h₂.trans h₁) y := by
  have e : ((Scheme.Modules.pullback p).obj F).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono p h₁)).op ≫
        ((Scheme.Modules.pullback p).obj F).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono p h₂)).op =
      ((Scheme.Modules.pullback p).obj F).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono p (h₂.trans h₁))).op := by
    rw [← Functor.map_comp]
    rfl
  exact congrArg (fun m : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U) ⟶
    Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) => ConcreteCategory.hom m y) e

/-- **The sheaf condition on a cover, as a three-term exact sequence.** For a family of opens
`V` covering `U`, restriction `Γ(F, U) ⟶ ∏ₐ Γ(F, Vₐ)` is exact against the difference of the
two restrictions `∏ₐ Γ(F, Vₐ) ⟶ ∏ₐ,ᵦ Γ(F, Vₐ ⊓ Vᵦ)`. -/
theorem exact_pi_baseResHom (g : X ⟶ S) (F : X.Modules) {ι : Type u} {U : X.Opens}
    (V : ι → X.Opens) (hVle : ∀ a, V a ≤ U) (hcover : U ≤ ⨆ a, V a) :
    letI : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule g F W
    Function.Exact (LinearMap.pi fun a => baseResHom g F (hVle a))
      (LinearMap.pi fun ab : ι × ι =>
        baseResHom g F (inf_le_left : V ab.1 ⊓ V ab.2 ≤ V ab.1) ∘ₗ LinearMap.proj ab.1 -
          baseResHom g F (inf_le_right : V ab.1 ⊓ V ab.2 ≤ V ab.2) ∘ₗ LinearMap.proj ab.2) := by
  intro y
  refine ⟨fun hy => ?_, ?_⟩
  · have hcompat : TopCat.Presheaf.IsCompatible F.presheaf V y := fun i j => by
      have hc := congrFun hy (i, j)
      simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.proj_apply, Pi.zero_apply, sub_eq_zero] at hc
      exact hc
    obtain ⟨s, hs, -⟩ :=
      TopCat.Sheaf.existsUnique_gluing' ⟨F.presheaf, Scheme.Modules.isSheaf F⟩
        V U (fun a => homOfLE (hVle a)) hcover y hcompat
    exact ⟨s, funext hs⟩
  · rintro ⟨s, rfl⟩
    funext ab
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.proj_apply, Pi.zero_apply, sub_eq_zero]
    rw [baseResHom_trans, baseResHom_trans]

/-- **Local preimages of a section form a cocycle.** If `zₐ` is a preimage of `t|_{p⁻¹Vₐ}` under
the comparison over each `Vₐ`, then the base change of the difference of the two restrictions to
the `Vₐ ⊓ Vᵦ` kills the family `(zₐ)`, because the comparison is injective over every open. -/
theorem lTensor_pi_baseResHom_sub_symm_eq_zero (H : IsPullback p k iX q) [IsAffine S]
    [IsAffine T] (F : X.Modules) [F.IsQuasicoherent]
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
    (hfp : letI := (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom.toAlgebra;
      Module.FinitePresentation ↑Γ(S, ⊤) ↑Γ(T, ⊤))
    {ι : Type u} {U : X.Opens} (V : ι → X.Opens) (hVle : ∀ a, V a ≤ U)
    (t : Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ U)) :
    letI := baseAlgebra q
    letI : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
    letI : Module.FinitePresentation Γ(S, ⊤) Γ(T, ⊤) := hfp
    ∀ z : ∀ a, Γ(T, ⊤) ⊗[Γ(S, ⊤)] ↑Γ(F, V a),
      (∀ a, sectionsBaseChangeMap H F (V a) (z a) = pullbackBaseResHom k p F (hVle a) t) →
      LinearMap.lTensor Γ(T, ⊤) (LinearMap.pi fun ab : ι × ι =>
          baseResHom iX F (inf_le_left : V ab.1 ⊓ V ab.2 ≤ V ab.1) ∘ₗ LinearMap.proj ab.1 -
            baseResHom iX F (inf_le_right : V ab.1 ⊓ V ab.2 ≤ V ab.2) ∘ₗ LinearMap.proj ab.2)
        ((TensorProduct.piRightOfFinitePresentation Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤)
          (fun a : ι => ↑Γ(F, V a))).symm z) = 0 := by
  let := baseAlgebra q
  let : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
  have : Module.FinitePresentation Γ(S, ⊤) Γ(T, ⊤) := hfp
  intro z hz
  refine (TensorProduct.piRightOfFinitePresentation Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤)
    (fun ab : ι × ι => ↑Γ(F, V ab.1 ⊓ V ab.2))).injective ?_
  rw [map_zero]
  funext ab
  rw [piRight_lTensor_pi_apply (fun ab : ι × ι => ↑Γ(F, V ab.1 ⊓ V ab.2)) _ ab,
    Pi.zero_apply, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero,
    lTensor_comp_proj_apply (fun a : ι => (Γ(F, V a) : Type u)) ab.1,
    lTensor_comp_proj_apply (fun a : ι => (Γ(F, V a) : Type u)) ab.2,
    LinearEquiv.apply_symm_apply]
  refine injective_sectionsBaseChangeMap H F hq hfp (V ab.1 ⊓ V ab.2) ?_
  rw [sectionsBaseChangeMap_comm_res H F (inf_le_left : V ab.1 ⊓ V ab.2 ≤ V ab.1) (z ab.1),
    sectionsBaseChangeMap_comm_res H F (inf_le_right : V ab.1 ⊓ V ab.2 ≤ V ab.2) (z ab.2),
    hz ab.1, hz ab.2, pullbackBaseResHom_trans, pullbackBaseResHom_trans]

/-- **The canonical degree-zero comparison is bijective over every open.** For a cartesian
square with `S` and `T` affine and `Γ(T, ⊤)` a flat, finitely presented `Γ(S, ⊤)`-module, the
canonical map

  `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ(p^* F, p⁻¹U)`,  `b ⊗ a ↦ b • p^* a`,

is bijective for every quasi-coherent `F` and *every* open `U` of `X`. **No quasi-compactness,
quasi-separatedness or separatedness hypothesis is imposed on `X`** — that is the content of
[Stacks, Tag 0CKW] in degree zero, and finite presentation of `Γ(T, ⊤)` is what pays for it.

`Stacks.AlgebraicGeometry.SectionsBaseChange.bijective_sectionsBaseChangeMap_of_isAffineOpen` is
the affine case, and is the only input about the geometry: the cover of `U` by all the affine
opens inside it has affine members, while its pairwise intersections need not be affine and are
handled by `injective_sectionsBaseChangeMap` alone. -/
theorem bijective_sectionsBaseChangeMap (H : IsPullback p k iX q) [IsAffine S] [IsAffine T]
    (F : X.Modules) [F.IsQuasicoherent]
    (hq : RingHom.Flat (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom)
    (hfp : letI := (q.appLE ⊤ ⊤ (le_preimage_top q ⊤)).hom.toAlgebra;
      Module.FinitePresentation ↑Γ(S, ⊤) ↑Γ(T, ⊤))
    (U : X.Opens) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Function.Bijective (sectionsBaseChangeMap H F U) := by
  classical
  let algAB := baseAlgebra q
  let modAF : ∀ W : X.Opens, Module Γ(S, ⊤) ↑Γ(F, W) := fun W => baseModule iX F W
  let modAG : ∀ W : X.Opens,
      Module Γ(S, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let modBG : ∀ W : X.Opens,
      Module Γ(T, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  let towerG : ∀ W : X.Opens,
      IsScalarTower Γ(S, ⊤) Γ(T, ⊤) ↑Γ((Scheme.Modules.pullback p).obj F, p ⁻¹ᵁ W) :=
    fun W => baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ W)
  have : Module.Flat Γ(S, ⊤) Γ(T, ⊤) := hq
  have : Module.FinitePresentation Γ(S, ⊤) Γ(T, ⊤) := hfp
  refine ⟨injective_sectionsBaseChangeMap H F hq hfp U, fun t => ?_⟩
  set ι := affineOpensIn U
  set V : ι → X.Opens := fun a => (a.1 : X.Opens)
  have hVle : ∀ a : ι, V a ≤ U := fun a => a.2
  have hcover : U ≤ ⨆ a : ι, V a := le_iSup_affineOpensIn U
  have hcover' : p ⁻¹ᵁ U ≤ ⨆ a : ι, p ⁻¹ᵁ V a := by
    rw [← Scheme.Hom.preimage_iSup]
    exact Scheme.Hom.preimage_mono p hcover
  set r : Γ(F, U) →ₗ[Γ(S, ⊤)] (∀ a : ι, ↑Γ(F, V a)) :=
    LinearMap.pi (fun a => baseResHom iX F (hVle a)) with hrdef
  -- the unique preimage over each affine member of the cover
  choose z hz using fun a : ι =>
    (bijective_sectionsBaseChangeMap_of_isAffineOpen H F a.1.2).2
      (pullbackBaseResHom k p F (hVle a) t)
  set e := TensorProduct.piRightOfFinitePresentation Γ(S, ⊤) Γ(T, ⊤) Γ(T, ⊤)
    (fun a : ι => ↑Γ(F, V a)) with hedef
  -- the family is a cocycle, so it descends, and the descended element is the preimage of `t`
  obtain ⟨w, hw⟩ := (Module.Flat.lTensor_exact Γ(T, ⊤)
    (exact_pi_baseResHom iX F V hVle hcover) (e.symm z)).mp
    (lTensor_pi_baseResHom_sub_symm_eq_zero H F hq hfp V hVle t z hz)
  have hwa : ∀ a : ι, LinearMap.lTensor Γ(T, ⊤) (baseResHom iX F (hVle a)) w = z a := by
    intro a
    rw [← piRight_lTensor_pi_apply (fun a : ι => ↑Γ(F, V a))
      (fun a => baseResHom iX F (hVle a)) a w, ← hrdef, ← hedef, hw,
      LinearEquiv.apply_symm_apply]
  refine ⟨w, TopCat.Sheaf.eq_of_locally_eq'
    ⟨((Scheme.Modules.pullback p).obj F).presheaf,
      Scheme.Modules.isSheaf ((Scheme.Modules.pullback p).obj F)⟩
    (fun a : ι => p ⁻¹ᵁ V a) (p ⁻¹ᵁ U)
    (fun a => homOfLE (Scheme.Hom.preimage_mono p (hVle a))) hcover'
    (sectionsBaseChangeMap H F U w) t fun a => ?_⟩
  show pullbackBaseResHom k p F (hVle a) (sectionsBaseChangeMap H F U w) = _
  rw [← sectionsBaseChangeMap_comm_res H F (hVle a) w, hwa a, hz a]
  rfl

/-- **Finite locally free base change on sections, over an arbitrary open of an arbitrary
scheme.** The two module-theoretic consequences of finite local freeness of `q` — flatness of
`Γ(S, ⊤) ⟶ Γ(T, ⊤)` and finite presentation of `Γ(T, ⊤)` over `Γ(S, ⊤)` — are read off by
`Stacks.Tag0CKW.flat_and_finitePresentation_of_isFiniteLocallyFree`, which is
[Stacks, Tag 02KB]. -/
theorem bijective_sectionsBaseChangeMap_of_isFiniteLocallyFree (H : IsPullback p k iX q)
    [IsAffine S] [IsAffine T] [Stacks.Morphisms.IsFiniteLocallyFree q]
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) :
    letI := baseAlgebra q
    letI := baseModule iX F U
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ U)
    Function.Bijective (sectionsBaseChangeMap H F U) := by
  obtain ⟨hflat, hfp⟩ := flat_and_finitePresentation_of_isFiniteLocallyFree q
    (appLE_top_eq_appTop q (le_preimage_top q ⊤))
  exact bijective_sectionsBaseChangeMap H F hflat hfp U

/-- **[Stacks, Tag 0CKW] in degree zero, for an arbitrary quasi-coherent module.** For a
cartesian square

```
Y --p--> X
|        |
k        iX
v        v
T --q--> S
```

with `S` and `T` affine and `q` finite locally free, and any quasi-coherent `𝒪_X`-module `F`,
the canonical map

  `Γ(T, ⊤) ⊗_{Γ(S, ⊤)} Γ(X, F) ⟶ Γ(Y, p^* F)`,  `b ⊗ a ↦ b • p^* a`,

is bijective. **`X` is an arbitrary scheme, not required to be quasi-compact, quasi-separated
or separated**, which is what distinguishes Tag 0CKW from [Stacks, Tag 02KH]: finite local
freeness of `q` makes `Γ(T, ⊤)` a finitely presented `Γ(S, ⊤)`-module, so tensoring with it
commutes with products over an arbitrary index ([Stacks, Tag 059K]) and the cover of `X` by
*all* of its affine opens may be used.

The map is `Stacks.AlgebraicGeometry.SectionsBaseChange.sectionsBaseChangeMap`, pinned on pure
tensors by `sectionsBaseChangeMap_tmul`, so this is the canonical base-change map and not an
unconstrained isomorphism.

`Stacks.Tag0CKW.isIso_globalSectionsBaseChange_of_finiteLocallyFree` is the case `F = 𝒪_X` of
this, stated through Mathlib's `AlgebraicGeometry.pushoutSection` as a map of *rings*.

The same statement in every degree, for the canonical map on cohomology, is
`Stacks.Tag0CKW.isIso_cohomologyBaseChangeMap`; this is its degree-zero case read on sections. -/
theorem bijective_globalSectionsBaseChange_of_finiteLocallyFree (H : IsPullback p k iX q)
    [IsAffine S] [IsAffine T] [Stacks.Morphisms.IsFiniteLocallyFree q]
    (F : X.Modules) [F.IsQuasicoherent] :
    letI := baseAlgebra q
    letI := baseModule iX F ⊤
    letI := baseModule (p ≫ iX) ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ ⊤)
    letI := baseModule k ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ ⊤)
    letI := baseTower H ((Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ ⊤)
    Function.Bijective (sectionsBaseChangeMap H F ⊤) :=
  bijective_sectionsBaseChangeMap_of_isFiniteLocallyFree H F ⊤

end

end Stacks.Tag0CKW

end
