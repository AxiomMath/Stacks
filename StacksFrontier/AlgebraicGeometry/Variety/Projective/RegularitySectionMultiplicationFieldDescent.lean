module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistActionLinear
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.GradedAlgebraTwist.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.CechCharts
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.FieldExtension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Twist
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Composite
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Sections
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularityGlobalGeneration
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRegularity
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RegularitySectionMultiplication
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# The reduction of Tag 08A7 to an infinite base field

[Stacks, Tag 08A7] says that for a coherent `m`-regular sheaf `ℱ` on `ℙⁿ_k` over a field `k` the
multiplication map `H⁰(ℙⁿ_k, ℱ(m)) ⊗_k H⁰(ℙⁿ_k, 𝒪(1)) ⟶ H⁰(ℙⁿ_k, ℱ(m+1))` is surjective. Its
proof begins "we may assume `k` is infinite", by faithfully flat base change along `k ⟶ k(t)`.
This file supplies exactly that step:
`AlgebraicGeometry.span_mulSections_eq_top_of_isMRegular_of_infinite` is the statement that the
tag over every **infinite** field implies the tag over every field.

## Main results

* `AlgebraicGeometry.span_mulSections_eq_top_of_isMRegular_of_infinite`: **the reduction.**
* `AlgebraicGeometry.mulSectionsSpan_eq_top_iff_gammaProductSpan`: the tag's conclusion, read on
  global sections, is that the products of a global section of `ℱ(d)` with a global section of
  `𝒪(1)` span `Γ(ℱ(d) ⊗ 𝒪(1), ⊤)`.
* `AlgebraicGeometry.gammaProductSpan_eq_top_of_fieldExtension`: **that span descends along a
  field extension.**
* `AlgebraicGeometry.mulSectionOne_val_app_top`: multiplication by a global section of `𝒪(1)`,
  read on global sections, is the product of sections of [Stacks, Tag 01CD].
* `Submodule.span_range_eq_top_of_baseChange`, `Submodule.eq_top_of_span_eq_top_of_map_mem` and
  `Submodule.mem_of_bilinear_of_span_eq_top`: the three pieces of span bookkeeping the descent
  needs, at abstract types.

## Main definitions

* `AlgebraicGeometry.projectiveGamma`: `Γ(ℱ, ⊤)` as a `k`-vector space, for a module on `ℙⁿ_k` —
  the same `k`-structure `AlgebraicGeometry.projectiveH` carries.
* `AlgebraicGeometry.gammaProductSpan`: the `k`-span of those products.
* `AlgebraicGeometry.sectionsEquivTop`: a compatible family of sections of a module on a scheme
  is its value over `⊤`, the top open being terminal.

## How the regrouping of the twists is avoided

`Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication.twistSectionMul`, the arrow
`ℱ(d) ⟶ ℱ(d+1)` the tag is about, is multiplication by the section followed by the regrouping
isomorphism `(ℱ(d)) ⊗ 𝒪(1) ≅ ℱ(d+1)` of `AlgebraicGeometry.twistAssocIso`
(`AlgebraicGeometry.twistSectionMul_eq_mulSectionOne_comp`). A base-change argument stated for
`twistSectionMul` would have to compare the regrouping over `k` with the one over `K`, a
coherence for the isomorphisms `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a+b)` that this development does not have.

`mulSectionsSpan_eq_top_iff_gammaProductSpan` peels the regrouping off instead: it is an
isomorphism, so the span of the products is everything exactly when the span of the
*unregrouped* products in `Γ(ℱ(d) ⊗ 𝒪(1), ⊤)` is. The regrouping is then applied separately over
each field and the two are never compared. What crosses the extension is only the product of
sections of [Stacks, Tag 01CD], whose base change is
`Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt`.

## Implementation notes

The `k`-vector space structure on `H⁰` is a restriction of scalars along the structure morphism,
and the base-change theorem
`Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange` is stated
over `Γ(Spec k, ⊤)` rather than over `k`. The two scalar structures differ by the ring
isomorphism `Γ(Spec k, ⊤) ≅ k`, which acts on a span only through
`Submodule.span_subset_span_of_surjective` and `Submodule.span_subset_span_of_smul_eq`; both are
applied with the comparison of scalars discharged by `rfl`.

`AlgebraicGeometry.mem_span_pullback_tensorSections` and
`AlgebraicGeometry.span_pullback_tensorSections_eq_top` are the two halves of the descent, split
off from `gammaProductSpan_eq_top_of_fieldExtension` because the single declaration exceeded the
kernel's heartbeat budget; they are stated for arbitrary modules and an arbitrary comparison
isomorphism, which is all their proofs use.

## References

* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 08A4](https://stacks.math.columbia.edu/tag/08A4)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication

open scoped TensorProduct

universe u v w

/-! ### Spans and bijective linear maps -/

/-- A span is everything exactly when the span of its image under a bijective linear map is. -/
public theorem Submodule.span_image_eq_top_iff_of_bijective {R M N : Type*} [CommRing R]
    [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Bijective f)
    (T : Set M) : Submodule.span R (f '' T) = ⊤ ↔ Submodule.span R T = ⊤ := by
  refine ⟨fun h => eq_top_iff.2 fun x _ => ?_, fun h => ?_⟩
  · have hx : f x ∈ Submodule.span R (f '' T) := h ▸ Submodule.mem_top
    rw [Submodule.span_image] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    exact hf.1 hyx ▸ hy
  · rw [Submodule.span_image, h, Submodule.map_top, LinearMap.range_eq_top]
    exact hf.2

/-- Restricting the scalars of a span along a surjective ring map does not shrink it. -/
public theorem Submodule.span_subset_span_of_surjective {R S W : Type*} [CommRing R] [CommRing S]
    [AddCommGroup W] [Module R W] [Module S W] (φ : S →+* R) (hφ : Function.Surjective φ)
    (hsmul : ∀ (c : S) (w : W), c • w = φ c • w) (T : Set W) :
    (Submodule.span R T : Set W) ⊆ (Submodule.span S T : Set W) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
      obtain ⟨c, rfl⟩ := hφ a
      exact (hsmul c x).symm ▸ Submodule.smul_mem _ c hx

/-- **A base change pinned on pure tensors is spanned by the image of the canonical map.** If
`B ⊗_A W ≃ W'` carries `1 ⊗ x` to `ρ x`, then `W'` is spanned over `B` by the range of `ρ`. -/
public theorem Submodule.span_range_eq_top_of_baseChange {A B W W' : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup W] [Module A W] [AddCommGroup W'] [Module B W']
    (e : B ⊗[A] W ≃ₗ[B] W') (ρ : W → W') (hρ : ∀ x, ρ x = e (1 ⊗ₜ[A] x)) :
    Submodule.span B {y | ∃ x, y = ρ x} = ⊤ := by
  have key : ∀ z : B ⊗[A] W, e z ∈ Submodule.span B {y | ∃ x, y = ρ x} := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => exact (map_add e z₁ z₂) ▸ add_mem h₁ h₂
    | tmul b x =>
        have hb : b ⊗ₜ[A] x = b • (1 : B) ⊗ₜ[A] x := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hb, map_smul, ← hρ]
        exact Submodule.smul_mem _ b (Submodule.subset_span ⟨x, rfl⟩)
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨z, hz⟩ := e.surjective y
  exact hz ▸ key z

/-- An additive and homogeneous map sends a spanning set's span into a submodule containing the
images of the set. -/
private theorem map_mem_of_mem_span {B W W' : Type*} [CommRing B]
    [AddCommGroup W] [Module B W] [AddCommGroup W'] [Module B W'] (f : W → W')
    (hadd : ∀ a b, f (a + b) = f a + f b) (hsmul : ∀ (b : B) a, f (b • a) = b • f a)
    (T : Set W) (P : Submodule B W') (h : ∀ t ∈ T, f t ∈ P) : ∀ x ∈ Submodule.span B T, f x ∈ P :=
  fun _ hx => (Submodule.span_le (p := P.comap (⟨⟨f, hadd⟩, hsmul⟩ : W →ₗ[B] W'))).2 h hx

/-- **A submodule containing the image of a spanning set under a surjective additive and
`B`-homogeneous map is everything.** -/
public theorem Submodule.eq_top_of_span_eq_top_of_map_mem {B W W' : Type*} [CommRing B]
    [AddCommGroup W] [Module B W] [AddCommGroup W'] [Module B W'] (f : W → W')
    (hadd : ∀ a b, f (a + b) = f a + f b) (hsmul : ∀ (b : B) a, f (b • a) = b • f a)
    (hsurj : Function.Surjective f) (T : Set W) (hT : Submodule.span B T = ⊤)
    (P : Submodule B W') (h : ∀ t ∈ T, f t ∈ P) : P = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨x, hx⟩ := hsurj y
  exact hx ▸ map_mem_of_mem_span f hadd hsmul T P h x (hT.ge Submodule.mem_top)

/-- **Every value of a bilinear map lies in a submodule containing the values on two spanning
sets.** -/
public theorem Submodule.mem_of_bilinear_of_span_eq_top {B W₁ W₂ W₃ : Type*} [CommRing B]
    [AddCommGroup W₁] [Module B W₁] [AddCommGroup W₂] [Module B W₂] [AddCommGroup W₃]
    [Module B W₃] (μ : W₁ → W₂ → W₃)
    (hadd₁ : ∀ z z' w, μ (z + z') w = μ z w + μ z' w)
    (hsmul₁ : ∀ (b : B) z w, μ (b • z) w = b • μ z w)
    (hadd₂ : ∀ z w w', μ z (w + w') = μ z w + μ z w')
    (hsmul₂ : ∀ (b : B) z w, μ z (b • w) = b • μ z w)
    (P : Submodule B W₃) (T₁ : Set W₁) (T₂ : Set W₂)
    (hT₁ : Submodule.span B T₁ = ⊤) (hT₂ : Submodule.span B T₂ = ⊤)
    (h : ∀ z ∈ T₁, ∀ w ∈ T₂, μ z w ∈ P) : ∀ z w, μ z w ∈ P := fun z w =>
  map_mem_of_mem_span (fun z => μ z w) (fun a b => hadd₁ a b w) (fun b a => hsmul₁ b a w) T₁ P
    (fun z hz => map_mem_of_mem_span (μ z) (hadd₂ z) (hsmul₂ · z) T₂ P (h z hz) w
      (hT₂.ge Submodule.mem_top)) z (hT₁.ge Submodule.mem_top)

/-! ### Spans, scalar restriction along the structure morphism -/

/-- Enlarging the scalars of a span along a ring map does not shrink it. -/
public theorem Submodule.span_subset_span_of_smul_eq {R S W : Type*} [CommRing R] [CommRing S]
    [AddCommGroup W] [Module R W] [Module S W] (φ : S →+* R)
    (hsmul : ∀ (c : S) (w : W), c • w = φ c • w) (T : Set W) :
    (Submodule.span S T : Set W) ⊆ (Submodule.span R T : Set W) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact (hsmul c x) ▸ Submodule.smul_mem _ (φ c) hx

namespace AlgebraicGeometry

/-! ### Global sections of a module on a scheme -/

/-- The top open of a scheme is a terminal object of its category of opens. -/
public def isTerminalTopOpens (X : Scheme.{u}) : Limits.IsTerminal (⊤ : X.Opens) :=
  Limits.IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) fun _ _ => Subsingleton.elim _ _

/-- **A compatible family of sections of a module on a scheme is its value over `⊤`.** -/
public def sectionsEquivTop {X : Scheme.{u}} (M : X.Modules) : M.sections ≃ Γ(M, ⊤) :=
  Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M (isTerminalTopOpens X)

/-- `sectionsEquivTop` sends a compatible family of sections to its value over `⊤`. -/
public theorem sectionsEquivTop_apply {X : Scheme.{u}} (M : X.Modules) (s : M.sections) :
    sectionsEquivTop M s = s.val (op ⊤) := rfl

/-- Every global section over `⊤` extends to a compatible family. -/
public theorem exists_sections_val_top {X : Scheme.{u}} (M : X.Modules) (y : Γ(M, ⊤)) :
    ∃ s : M.sections, s.val (op ⊤) = y :=
  ⟨(sectionsEquivTop M).symm y, (sectionsEquivTop M).apply_symm_apply y⟩

/-- A composite of morphisms of modules, read on global sections. -/
public theorem comp_val_app_top {X : Scheme.{u}} {A B C : X.Modules} (f : A ⟶ B) (g : B ⟶ C)
    (a : Γ(A, ⊤)) :
    PresheafOfModules.Hom.app (f ≫ g).val (op ⊤) a =
      PresheafOfModules.Hom.app g.val (op ⊤) (PresheafOfModules.Hom.app f.val (op ⊤) a) := rfl

/-- The two spellings of a morphism of modules read on global sections. -/
public theorem app_top_eq_val_app {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B) (a : Γ(A, ⊤)) :
    f.app ⊤ a = PresheafOfModules.Hom.app f.val (op ⊤) a := rfl

/-- A global section of a module, read as a morphism out of the structure sheaf, sends the unit
section to that global section. -/
public theorem sectionHom_val_app_one {X : Scheme.{u}} (A : X.Modules) (s : A.sections)
    (U : X.Opensᵒᵖ) :
    PresheafOfModules.Hom.app (sectionHom A s).val U (1 : X.ringCatSheaf.obj.obj U) = s.val U :=
  (SheafOfModules.unitHomEquiv_apply_coe A ((A.unitHomEquiv).symm s) U).symm.trans
    (congrArg (fun t : A.sections => t.val U) (A.unitHomEquiv.apply_symm_apply s))

/-! ### Reading morphisms of modules on global sections -/

/-- A morphism of modules, read on global sections, is additive. -/
public theorem app_top_add {X : Scheme.{u}} {A B : X.Modules} (φ : A ⟶ B) (x y : Γ(A, ⊤)) :
    φ.app ⊤ (x + y) = φ.app ⊤ x + φ.app ⊤ y :=
  map_add (ConcreteCategory.hom (φ.app ⊤)) x y

/-- A morphism of modules, read on global sections, is linear over the sections of a base
scheme. -/
public theorem app_top_smul_base {X T : Scheme.{u}} (h : X ⟶ T) {A B : X.Modules} (φ : A ⟶ B)
    (r : Γ(T, ⊤)) (x : Γ(A, ⊤)) :
    letI := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule h A ⊤
    letI := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule h B ⊤
    φ.app ⊤ (r • x) = r • φ.app ⊤ x :=
  Scheme.Modules.Hom.app_smul φ
    ((h.appLE ⊤ ⊤ (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top h ⊤)).hom r) x

/-- The pullback of a global section, in the two spellings the library uses. -/
public theorem pullbackSectionsHom_top_eq_pullbackGlobalSections {X Y : Scheme.{u}} (p : Y ⟶ X)
    (F : X.Modules) (x : Γ(F, ⊤)) :
    Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom p F ⊤ ⊤
        (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top p ⊤) x =
      pullbackGlobalSections p F x :=
  (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom_top p F x).trans
    (congrArg (fun φ : Γ(F, ⊤) ⟶ Γ((Scheme.Modules.pullback p).obj F, ⊤) =>
      ConcreteCategory.hom φ x) (pullbackGlobalSections_eq_unit p F)).symm

/-! ### The comparison of Tag 01CD on products of global sections -/

/-- The tensor product of two isomorphisms of modules, read on a product of global sections. -/
public theorem tensorModulesMapIso_hom_val_app_top {W : Scheme.{u}} {A A' B B' : W.Modules}
    (e : A ≅ A') (f : B ≅ B') (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    PresheafOfModules.Hom.app (tensorModulesMapIso W e f).hom.val (op ⊤)
        (Stacks.SheafOfModules.tensorSectionsAt W.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf W) (op ⊤)
          A B a b) =
      Stacks.SheafOfModules.tensorSectionsAt W.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf W) (op ⊤) A' B'
        (PresheafOfModules.Hom.app e.hom.val (op ⊤) a)
        (PresheafOfModules.Hom.app f.hom.val (op ⊤) b) :=
  Stacks.PullbackTensorIso.tensorSheafMap_tensorSectionsAt e.hom f.hom a b

/-- **The comparison of [Stacks, Tag 01CD] on products of global sections, read backwards**: the
product of the pullbacks of two global sections is the pullback of their product. -/
public theorem pullbackTensorIso_inv_val_app_top_tensorSectionsAt {X Y : Scheme.{u}} (p : Y ⟶ X)
    (A B : X.Modules) (a : Γ(A, ⊤)) (b : Γ(B, ⊤)) :
    PresheafOfModules.Hom.app
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A B).inv.val (op ⊤)
        (Stacks.SheafOfModules.tensorSectionsAt Y.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y) (op ⊤)
          ((Scheme.Modules.pullback p).obj A) ((Scheme.Modules.pullback p).obj B)
          (pullbackGlobalSections p A a) (pullbackGlobalSections p B b)) =
      pullbackGlobalSections p
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
                (forget₂ CommRingCat RingCat)
                ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj
            (A)).obj (B)))
        (Stacks.SheafOfModules.tensorSectionsAt X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (op ⊤)
          A B a b) := by
  refine Eq.trans (congrArg (PresheafOfModules.Hom.app
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A B).inv.val (op ⊤))
      (Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt p A B a b).symm) ?_
  refine Eq.trans (comp_val_app_top
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A B).hom
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A B).inv _).symm ?_
  exact congrArg (fun φ : (Scheme.Modules.pullback p).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
                (forget₂ CommRingCat RingCat)
                ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj
            (A)).obj (B))) ⟶
      (Scheme.Modules.pullback p).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
                (forget₂ CommRingCat RingCat)
                ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj
            (A)).obj (B))) =>
      PresheafOfModules.Hom.app φ.val (op ⊤)
        (pullbackGlobalSections p
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf)
                  (forget₂ CommRingCat RingCat)
                  ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj
              (A)).obj (B)))
          (Stacks.SheafOfModules.tensorSectionsAt X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (op ⊤)
            A B a b)))
    (Iso.hom_inv_id (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p A B))

/-! ### Multiplication by a global section of `𝒪(1)`, on global sections -/

/-- **Multiplication by a global section `s` of `𝒪(1)`, read on global sections, is the product
of sections of [Stacks, Tag 01CD].** -/
public theorem mulSectionOne_val_app_top (n : ℕ) (S : Scheme.{u})
    (M : (projectiveSpaceOver n S).Modules) (s : (twistOver n S 1).sections) (x : Γ(M, ⊤)) :
    PresheafOfModules.Hom.app (mulSectionOne n S M s).val (op ⊤) x =
      Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOver n S).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver n S)) (op ⊤) M
            (twistOver n S 1) x
        (s.val (op ⊤)) := by
  refine (comp_val_app_top _ _ x).trans ?_
  refine (congrArg (PresheafOfModules.Hom.app
      (tensorRightOfUnitHom n S M (sectionHom (twistOver n S 1) s)).val (op ⊤))
      (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSections_rightUnitorInvAt
        (projectiveSpaceOver n S).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver n S))
        (op ⊤) M x)).trans ?_
  refine (Stacks.PullbackTensorIso.tensorSheafMap_tensorSectionsAt (𝟙 M)
      (sectionHom (twistOver n S 1) s) x _).trans ?_
  exact congrArg (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOver n S).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOver n S)) (op ⊤) M
            (twistOver n S 1) x)
    (sectionHom_val_app_one (twistOver n S 1) s (op ⊤))

/-! ### `Γ(ℱ, ⊤)` as a `k`-vector space -/

variable (k : Type u) [Field k] (n : ℕ)

/-- `Γ(ℱ, ⊤)` as a `k`-vector space, for a module `ℱ` on `ℙⁿ_k`: the `k`-structure is the one
restriction of scalars along the structure morphism puts on it, the same one
`AlgebraicGeometry.projectiveH` carries. -/
public abbrev projectiveGamma (M : (projectiveSpaceOverRing n (.of k)).Modules) :
    ModuleCat.{u} k :=
  (restrictScalarsOverBase k (projectiveSpaceToBase k n)).obj
    ((SheafOfModules.evaluation (projectiveSpaceOverRing n (.of k)).ringCatSheaf (op ⊤)).obj M)

/-- A morphism of modules on `ℙⁿ_k`, read on global sections as a `k`-linear map. -/
public abbrev projectiveGammaMap {M M' : (projectiveSpaceOverRing n (.of k)).Modules}
    (φ : M ⟶ M') : projectiveGamma k n M ⟶ projectiveGamma k n M' :=
  (restrictScalarsOverBase k (projectiveSpaceToBase k n)).map
    ((SheafOfModules.evaluation (projectiveSpaceOverRing n (.of k)).ringCatSheaf (op ⊤)).map φ)

/-- On a global section, `projectiveGammaMap φ` is the component of `φ` over `⊤`. -/
public theorem projectiveGammaMap_apply {M M' : (projectiveSpaceOverRing n (.of k)).Modules}
    (φ : M ⟶ M') (x : projectiveGamma k n M) :
    projectiveGammaMap k n φ x = PresheafOfModules.Hom.app φ.val (op ⊤) x := rfl

/-- The `k`-span of the products of a global section of `ℱ(d)` with a global section of `𝒪(1)`,
inside `Γ(ℱ(d) ⊗ 𝒪(1), ⊤)`. -/
public def gammaProductSpan (F : (projectiveSpaceOverRing n (.of k)).Modules) (d : ℤ) :
    Submodule k ↑(projectiveGamma k n
      (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k))
        (projectiveTwist n F d)
        (twistOver n (Spec (.of k)) 1))) :=
  Submodule.span k {t | ∃ (x : ↑(projectiveGamma k n (projectiveTwist n F d)))
      (y : ↑(projectiveGamma k n (twistOver n (Spec (.of k)) 1))),
    t = Stacks.SheafOfModules.tensorSectionsAt
      (projectiveSpaceOverRing n (.of k)).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing n (.of k)))
            (op ⊤)
      (projectiveTwist n F d) (twistOver n (Spec (.of k)) 1) x y}

/-- **Multiplication by a global section of `𝒪(1)` on `H⁰`, read on global sections.** Through
`AlgebraicGeometry.cohomologyOverFieldZeroLinearIso` the multiplication map of [Stacks, Tag 08A7]
is the product of sections of [Stacks, Tag 01CD] followed by the regrouping of the twists. -/
public theorem cohomologyOverFieldZeroLinearIso_mulSection
    (F : (projectiveSpaceOverRing n (.of k)).Modules) (d : ℤ)
    (s : (twistOver n (Spec (.of k)) 1).sections)
    (a : ↑(projectiveH k n (projectiveTwist n F d) 0)) :
    (cohomologyOverFieldZeroLinearIso k (projectiveSpaceToBase k n)
          (projectiveTwist n F (d + 1))).hom
        (ConcreteCategory.hom (mulSection k n F s d) a) =
      projectiveGammaMap k n (twistAssocIso n (Spec (.of k)) F d).hom
        (Stacks.SheafOfModules.tensorSectionsAt
          (projectiveSpaceOverRing n (.of k)).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing n (.of k)))
            (op ⊤)
          (projectiveTwist n F d) (twistOver n (Spec (.of k)) 1)
          ((cohomologyOverFieldZeroLinearIso k (projectiveSpaceToBase k n)
            (projectiveTwist n F d)).hom a) (s.val (op ⊤))) := by
  refine (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k (projectiveSpaceToBase k n)
      (twistSectionMul n (Spec (.of k)) F s d) a).trans ?_
  refine (app_top_eq_val_app (twistSectionMul n (Spec (.of k)) F s d) _).trans ?_
  refine (congrArg (fun φ : projectiveTwist n F d ⟶ projectiveTwist n F (d + 1) =>
      PresheafOfModules.Hom.app φ.val (op ⊤)
        ((cohomologyOverFieldZeroLinearIso k (projectiveSpaceToBase k n)
          (projectiveTwist n F d)).hom a))
    (twistSectionMul_eq_mulSectionOne_comp n (Spec (.of k)) F s d)).trans ?_
  refine (comp_val_app_top _ _ _).trans ?_
  exact congrArg (PresheafOfModules.Hom.app (twistAssocIso n (Spec (.of k)) F d).hom.val (op ⊤))
    (mulSectionOne_val_app_top n (Spec (.of k)) (projectiveTwist n F d) s _)

/-- **[Stacks, Tag 08A7] in the form the base change argument needs.** The multiplication map on
`H⁰` is surjective exactly when the products of global sections span `Γ(ℱ(d) ⊗ 𝒪(1), ⊤)`.

Both identifications used are bijections of `k`-vector spaces:
`AlgebraicGeometry.cohomologyOverFieldZeroLinearIso` in the two degrees, and the regrouping
isomorphism `(ℱ(d)) ⊗ 𝒪(1) ≅ ℱ(d + 1)` of `AlgebraicGeometry.twistAssocIso`. Peeling the
regrouping off is what keeps the statement free of any comparison between the isomorphisms
`𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` over two different base fields. -/
public theorem mulSectionsSpan_eq_top_iff_gammaProductSpan
    (F : (projectiveSpaceOverRing n (.of k)).Modules) (d : ℤ) :
    mulSectionsSpan k n F d = ⊤ ↔ gammaProductSpan k n F d = ⊤ := by
  have hiso : IsIso (projectiveGammaMap k n (twistAssocIso n (Spec (.of k)) F d).hom) :=
    ((restrictScalarsOverBase k (projectiveSpaceToBase k n)).mapIso
      ((SheafOfModules.evaluation (projectiveSpaceOverRing n (.of k)).ringCatSheaf
        (op ⊤)).mapIso (twistAssocIso n (Spec (.of k)) F d))).isIso_hom
  have hΦ := ConcreteCategory.bijective_of_isIso
    (projectiveGammaMap k n (twistAssocIso n (Spec (.of k)) F d).hom)
  have h₁ := ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k (projectiveSpaceToBase k n) (projectiveTwist n F d)).hom
  have h₂ := ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k (projectiveSpaceToBase k n)
      (projectiveTwist n F (d + 1))).hom
  have himg : ConcreteCategory.hom (cohomologyOverFieldZeroLinearIso k
        (projectiveSpaceToBase k n) (projectiveTwist n F (d + 1))).hom ''
      {t | ∃ (s : (twistOver n (Spec (.of k)) 1).sections)
          (a : ↑(projectiveH k n (projectiveTwist n F d) 0)),
        t = ConcreteCategory.hom (mulSection k n F s d) a} =
      ConcreteCategory.hom (projectiveGammaMap k n
        (twistAssocIso n (Spec (.of k)) F d).hom) ''
      {t | ∃ (x : ↑(projectiveGamma k n (projectiveTwist n F d)))
          (y : ↑(projectiveGamma k n (twistOver n (Spec (.of k)) 1))),
        t = Stacks.SheafOfModules.tensorSectionsAt
          (projectiveSpaceOverRing n (.of k)).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing n (.of k)))
            (op ⊤)
          (projectiveTwist n F d) (twistOver n (Spec (.of k)) 1) x y} := by
    apply Set.eq_of_subset_of_subset
    · rintro t ⟨w, ⟨s, a, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, s.val (op ⊤), rfl⟩, (cohomologyOverFieldZeroLinearIso_mulSection
        k n F d s a).symm⟩
    · rintro t ⟨w, ⟨x, y, rfl⟩, rfl⟩
      obtain ⟨s, hs⟩ := exists_sections_val_top (twistOver n (Spec (.of k)) 1) y
      obtain ⟨a, ha⟩ := h₁.2 x
      refine ⟨_, ⟨s, a, rfl⟩, ?_⟩
      rw [cohomologyOverFieldZeroLinearIso_mulSection k n F d s a, ha, hs]
  rw [mulSectionsSpan, gammaProductSpan,
    ← Submodule.span_image_eq_top_iff_of_bijective _ h₂, himg,
    Submodule.span_image_eq_top_iff_of_bijective _ hΦ]

/-! ### Descent of the span along a field extension -/

open Stacks.SheafOfModules in
/-- **The pairing of sections over an object is linear in its left argument.** The mirror of
`Stacks.TwistActionLinear.tensorSectionsAt_smul_right`, deduced from it by exchanging the two
arguments with the braiding of the tensor product, which is linear over the sections of the ring
sheaf of the tensor product. Each of the two sheaves of rings the scalar acts through is written
out in the statement: on the left the structure sheaf, whose sections `F` is a module over, and on
the right the ring sheaf of the tensor product, as in the right-hand version. -/
private theorem tensorSectionsAt_smul_left {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    (U : Cᵒᵖ) (F G : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (r : O.obj U) (s : F.val.obj U) (t : G.val.obj U) :
    tensorSectionsAt O hO U F G
        ((show (TensorSheafification.structureSheaf O hO).obj.obj U from r) • s) t =
      (show (Tensor.ringSheaf ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
        (forget₂ CommRingCat RingCat) (hO)⟩).obj.obj U from r) •
        tensorSectionsAt O hO U F G s t := by
  refine (tensorSections_braidingAt O hO U G F t _).symm.trans ?_
  refine (congrArg (fun y => ((Invertible.tensorProductBraiding O hO G F).hom.val.app U) y)
    (Stacks.TwistActionLinear.tensorSectionsAt_smul_right O hO U G F r t s)).trans ?_
  refine (LinearMap.map_smul
    ((Invertible.tensorProductBraiding O hO G F).hom.val.app U).hom _ _).trans ?_
  exact congrArg (fun y => (show (Tensor.ringSheaf ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O)
    (forget₂ CommRingCat RingCat) (hO)⟩).obj.obj U from r) • y)
    (tensorSections_braidingAt O hO U G F t s)

open Stacks.AlgebraicGeometry.SectionsBaseChange in
/-- **Every product of two global sections upstairs lies in the span of the pullbacks of the
products downstairs.** The products of sections are bilinear and the comparison of
[Stacks, Tag 01CD] is linear, so this follows from the two base-change spanning statements by a
double induction on the span, `Submodule.mem_of_bilinear_of_span_eq_top`. -/
private theorem mem_span_pullback_tensorSections (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : ℕ) (M L : (projectiveSpaceOverRing n (.of k)).Modules)
    (c : ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) M L)) ≅
        Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of K))
        ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj M)
        ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj L))
    (hprod : ∀ (x : ↑Γ(M, ⊤)) (y : ↑Γ(L, ⊤)),
      c.inv.app ⊤ (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOverRing n (.of
          K)).presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf
          (projectiveSpaceOverRing n (.of K))) (op ⊤)
        ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj M)
            ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj L)
            (pullbackGlobalSections (projectiveSpaceFieldExtensionMap k K n) M x)
            (pullbackGlobalSections (projectiveSpaceFieldExtensionMap k K n) L y)) =
        (pullbackGlobalSections (projectiveSpaceFieldExtensionMap k K n)
            (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) M L)
            (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOverRing n (.of k)).presheaf
            (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing n (.of
            k))) (op ⊤)
        M L x y))) :
    letI := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
        (projectiveSpaceFieldExtensionMap k K n)).obj M) ⊤
    letI := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
        (projectiveSpaceFieldExtensionMap k K n)).obj L) ⊤
    letI := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
        (projectiveSpaceFieldExtensionMap k K n)).obj (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (.of k)) M L)) ⊤
    ∀ (_ : Submodule.span ↑Γ(Spec (CommRingCat.of K), ⊤)
        {z : ↑Γ(((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj M), ⊤) | ∃ x
            : ↑Γ(M, ⊤), z = (pullbackGlobalSections (projectiveSpaceFieldExtensionMap k K n) M x)} =
            ⊤)
      (_ : Submodule.span ↑Γ(Spec (CommRingCat.of K), ⊤)
        {z : ↑Γ(((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj L), ⊤) | ∃ x
            : ↑Γ(L, ⊤), z = (pullbackGlobalSections (projectiveSpaceFieldExtensionMap k K n) L x)} =
            ⊤)
      (z : ↑Γ(((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj M), ⊤)) (w :
          ↑Γ(((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj L), ⊤)),
      c.inv.app ⊤ (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOverRing n (.of
          K)).presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf
          (projectiveSpaceOverRing n (.of K))) (op ⊤)
        ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj M)
            ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj L) z w) ∈
        Submodule.span ↑Γ(Spec (CommRingCat.of K), ⊤) {t : ↑Γ(((Scheme.Modules.pullback
            (projectiveSpaceFieldExtensionMap k K n)).obj (Stacks.RelativeVeryAmple.tensorModules
            (projectiveSpaceOverRing n (.of k)) M L)), ⊤) |
      ∃ (x : ↑Γ(M, ⊤)) (y : ↑Γ(L, ⊤)),
      t = (pullbackGlobalSections (projectiveSpaceFieldExtensionMap k K n)
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) M L)
          (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOverRing n (.of k)).presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing n (.of
          k))) (op ⊤)
        M L x y))} := by
  let := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k K n)).obj M) ⊤
  let := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k K n)).obj L) ⊤
  let := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k K n)).obj (Stacks.RelativeVeryAmple.tensorModules
      (projectiveSpaceOverRing n (.of k)) M L)) ⊤
  intro hspanM hspanL
  refine Submodule.mem_of_bilinear_of_span_eq_top _ ?_ ?_ ?_ ?_ _ _ _ hspanM hspanL ?_
  · exact fun z z' w => (congrArg (fun v => c.inv.app ⊤ v)
      (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_add_left _ _ (op ⊤) _ _ z z'
          w)).trans
        (app_top_add c.inv _ _)
  · exact fun b z w => (congrArg (fun v => c.inv.app ⊤ v)
      (tensorSectionsAt_smul_left _ _ (op ⊤) _ _ _ z w)).trans
        (app_top_smul_base (projectiveSpaceToBase K n) c.inv b _)
  · exact fun z w w' => (congrArg (fun v => c.inv.app ⊤ v)
      (Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_add_right _ _ (op ⊤) _ _ z w
          w')).trans
        (app_top_add c.inv _ _)
  · exact fun b z w => (congrArg (fun v => c.inv.app ⊤ v)
      (Stacks.TwistActionLinear.tensorSectionsAt_smul_right _ _ (op ⊤) _ _ _ z w)).trans
        (app_top_smul_base (projectiveSpaceToBase K n) c.inv b _)
  · rintro z ⟨x, rfl⟩ w ⟨y, rfl⟩
    exact (hprod x y) ▸ Submodule.subset_span ⟨x, y, rfl⟩

open Stacks.AlgebraicGeometry.SectionsBaseChange in
/-- **The pullbacks of the products of global sections span, upstairs.** The products of sections
upstairs span by hypothesis; each of them is, through the comparisons of the three modules, a
product of sections of the pullbacks, hence lies in the span of the pullbacks of the products. -/
private theorem span_pullback_tensorSections_eq_top (k K : Type u) [Field k] [Field K]
    [Algebra k K] (n : ℕ) (M L : (projectiveSpaceOverRing n (.of k)).Modules) (M' L' :
        (projectiveSpaceOverRing n (.of K)).Modules)
    (Ξ : M' ≅ ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj M)) (u : L' ≅
        ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj L))
    (c : ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) M L)) ≅
        Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of K))
        ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj M)
        ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj L))
    (hmem : letI := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
        (projectiveSpaceFieldExtensionMap k K n)).obj M) ⊤
      letI := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
          (projectiveSpaceFieldExtensionMap k K n)).obj L) ⊤
      letI := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
          (projectiveSpaceFieldExtensionMap k K n)).obj (Stacks.RelativeVeryAmple.tensorModules
          (projectiveSpaceOverRing n (.of k)) M L)) ⊤
      ∀ (z : ↑Γ(((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj M), ⊤)) (w :
          ↑Γ(((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj L), ⊤)),
        c.inv.app ⊤ (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOverRing n (.of
            K)).presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf
            (projectiveSpaceOverRing n (.of K))) (op ⊤)
        ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj M)
            ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj L) z w) ∈
          Submodule.span ↑Γ(Spec (CommRingCat.of K), ⊤) {t : ↑Γ(((Scheme.Modules.pullback
              (projectiveSpaceFieldExtensionMap k K n)).obj (Stacks.RelativeVeryAmple.tensorModules
              (projectiveSpaceOverRing n (.of k)) M L)), ⊤) |
      ∃ (x : ↑Γ(M, ⊤)) (y : ↑Γ(L, ⊤)),
      t = (pullbackGlobalSections (projectiveSpaceFieldExtensionMap k K n)
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) M L)
          (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOverRing n (.of k)).presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing n (.of
          k))) (op ⊤)
        M L x y))})
    (hKspan : Submodule.span K {t : ↑(projectiveGamma K n (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (.of K)) M' L')) |
      ∃ (x : ↑(projectiveGamma K n M')) (y : ↑(projectiveGamma K n L')),
      t = (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOverRing n (.of K)).presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing n (.of
          K))) (op ⊤)
        M' L' x y)} = ⊤) :
    letI := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
        (projectiveSpaceFieldExtensionMap k K n)).obj (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (.of k)) M L)) ⊤
    Submodule.span ↑Γ(Spec (CommRingCat.of K), ⊤) {t : ↑Γ(((Scheme.Modules.pullback
        (projectiveSpaceFieldExtensionMap k K n)).obj (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (.of k)) M L)), ⊤) |
      ∃ (x : ↑Γ(M, ⊤)) (y : ↑Γ(L, ⊤)),
      t = (pullbackGlobalSections (projectiveSpaceFieldExtensionMap k K n)
          (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) M L)
          (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOverRing n (.of k)).presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing n (.of
          k))) (op ⊤)
        M L x y))} = ⊤ := by
  let := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k K n)).obj M) ⊤
  let := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k K n)).obj L) ⊤
  let := baseModule (projectiveSpaceToBase K n) ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k K n)).obj (Stacks.RelativeVeryAmple.tensorModules
      (projectiveSpaceOverRing n (.of k)) M L)) ⊤
  let := baseModule (projectiveSpaceToBase K n) (Stacks.RelativeVeryAmple.tensorModules
      (projectiveSpaceOverRing n (.of K)) M' L') ⊤
  let : Module ↑Γ(Spec (CommRingCat.of K), ⊤) ↑(projectiveGamma K n
      (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of K)) M' L')) :=
    baseModule (projectiveSpaceToBase K n) (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (.of K)) M' L') ⊤
  let Φ : (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of K)) M' L') ≅
      Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of K))
      ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj M)
      ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj L) :=
      tensorModulesMapIso (projectiveSpaceOverRing n (.of K)) Ξ u
  refine Submodule.eq_top_of_span_eq_top_of_map_mem
    (fun v => c.inv.app ⊤ (Φ.hom.app ⊤ v)) ?_ ?_ ?_ {t : ↑(projectiveGamma K n
        (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of K)) M' L')) |
      ∃ (x : ↑(projectiveGamma K n M')) (y : ↑(projectiveGamma K n L')),
      t = (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOverRing n (.of K)).presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing n (.of
          K))) (op ⊤)
        M' L' x y)} ?_ _ ?_
  · exact fun a b => (congrArg (fun v => c.inv.app ⊤ v) (app_top_add Φ.hom a b)).trans
      (app_top_add c.inv _ _)
  · exact fun b a => (congrArg (fun v => c.inv.app ⊤ v)
      (app_top_smul_base (projectiveSpaceToBase K n) Φ.hom b a)).trans
        (app_top_smul_base (projectiveSpaceToBase K n) c.inv b _)
  · intro t
    have hev : IsIso ((SheafOfModules.evaluation (projectiveSpaceOverRing n (.of K)).ringCatSheaf
        (op ⊤)).map (Φ ≪≫ c.symm).hom) := ((SheafOfModules.evaluation (projectiveSpaceOverRing n
        (.of K)).ringCatSheaf (op ⊤)).mapIso (Φ ≪≫ c.symm)).isIso_hom
    obtain ⟨v, hv⟩ := (ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.evaluation (projectiveSpaceOverRing n (.of K)).ringCatSheaf (op ⊤)).map (Φ ≪≫
          c.symm).hom)).2 t
    exact ⟨v, hv⟩
  · refine eq_top_iff.2 fun t _ => ?_
    refine Submodule.span_subset_span_of_smul_eq (R := ↑Γ(Spec (CommRingCat.of K), ⊤)) (S := K)
      (W := ↑(projectiveGamma K n (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n
          (.of K)) M' L')))
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (fun _ _ => rfl) _ ?_
    exact hKspan.ge Submodule.mem_top
  · rintro t ⟨x', y', rfl⟩
    have e₂ : Φ.hom.app ⊤ (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOverRing n (.of
        K)).presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing
        n (.of K))) (op ⊤)
        M' L' x' y') =
        (Stacks.SheafOfModules.tensorSectionsAt (projectiveSpaceOverRing n (.of K)).presheaf
            (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing n (.of
            K))) (op ⊤)
        ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj M)
            ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj L) (Ξ.hom.app ⊤
            x') (u.hom.app ⊤ y')) :=
      tensorModulesMapIso_hom_val_app_top Ξ u x' y'
    have hz := hmem (Ξ.hom.app ⊤ x') (u.hom.app ⊤ y')
    rwa [← e₂] at hz

open Stacks.AlgebraicGeometry.SectionsBaseChange in
/-- **The reduction of [Stacks, Tag 08A7] to a field extension.** If the products of a global
section of `ℱ(m)` with a global section of `𝒪(1)` span after base change to an extension field
`K`, then they span over `k`.

This is faithfully flat descent for the span. `Γ(𝒢, ⊤) ⊗_k K = Γ(g^*𝒢, ⊤)` for every
quasi-coherent `𝒢`, by `Stacks.AlgebraicGeometry.SectionsBaseChange`‑
`.exists_linearEquiv_sections_baseChange`; the comparison of [Stacks, Tag 01CD] identifies the
product of two pulled-back sections with the pullback of their product, so the products upstairs
are `K`-combinations of pullbacks of products downstairs; and
`Submodule.eq_top_of_span_image_baseChange` descends the conclusion. Nothing here compares the
isomorphisms `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` over `k` and over `K`. -/
public theorem gammaProductSpan_eq_top_of_fieldExtension (k K : Type u) [Field k] [Field K]
    [Algebra k K] (n : ℕ) (F : (projectiveSpaceOverRing n (.of k)).Modules) [F.IsCoherent]
    (m : ℤ)
    (hKspan : gammaProductSpan K n
      ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj F) m = ⊤) :
    gammaProductSpan k n F m = ⊤ := by
  have H : IsPullback (projectiveSpaceFieldExtensionMap k K n) (projectiveSpaceToBase K n)
      (projectiveSpaceToBase k n) (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    isPullback_projectiveSpaceFieldExtensionMap k K n
  let : CompactSpace (projectiveSpaceOverRing n (.of k)) :=
    Stacks.ProjectiveCohomology.compactSpace_projectiveSpaceOverRing n (.of k)
  let : QuasiSeparatedSpace (projectiveSpaceOverRing n (.of k)) :=
    Stacks.ProjectiveCohomology.quasiSeparatedSpace_projectiveSpaceOverRing n (.of k)
  let hMqc : (projectiveTwist n F m).IsQuasicoherent :=
    isQuasicoherent_projectiveTwist_of_isCoherent n F m
  let hNqc : (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k))
      (projectiveTwist n F m)
      (twistOver n (Spec (CommRingCat.of k)) 1)).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent
      (projectiveSpaceOverRing n (.of k)).toRingedSpace _ _ hMqc
      (Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.isQuasicoherent_twistOver n
        (Spec (CommRingCat.of k)) 1)
  let := baseAlgebra (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let : Module.FaithfullyFlat ↑Γ(Spec (CommRingCat.of k), ⊤)
      ↑Γ(Spec (CommRingCat.of K), ⊤) := by
    have hk : IsField ↑Γ(Spec (CommRingCat.of k), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
        (Field.toIsField k)
    have hK : IsField ↑Γ(Spec (CommRingCat.of K), ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
        (Field.toIsField K)
    let := hk.toField
    let := hK.toField
    infer_instance
  let := baseModule (projectiveSpaceToBase k n) (projectiveTwist n F m) ⊤
  let := baseModule (projectiveSpaceToBase k n) (twistOver n (Spec (CommRingCat.of k)) 1) ⊤
  let := baseModule (projectiveSpaceToBase k n)
    (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) (projectiveTwist n F
        m)
      (twistOver n (Spec (CommRingCat.of k)) 1)) ⊤
  let := baseModule (projectiveSpaceFieldExtensionMap k K n ≫ projectiveSpaceToBase k n)
    ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
      (projectiveTwist n F m)) ⊤
  let := baseModule (projectiveSpaceFieldExtensionMap k K n ≫ projectiveSpaceToBase k n)
    ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
      (twistOver n (Spec (CommRingCat.of k)) 1)) ⊤
  let := baseModule (projectiveSpaceFieldExtensionMap k K n ≫ projectiveSpaceToBase k n)
    ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
      (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) (projectiveTwist n
          F m)
        (twistOver n (Spec (CommRingCat.of k)) 1))) ⊤
  let := baseModule (projectiveSpaceToBase K n)
    ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
      (projectiveTwist n F m)) ⊤
  let := baseModule (projectiveSpaceToBase K n)
    ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
      (twistOver n (Spec (CommRingCat.of k)) 1)) ⊤
  let := baseModule (projectiveSpaceToBase K n)
    ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
      (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) (projectiveTwist n
          F m)
        (twistOver n (Spec (CommRingCat.of k)) 1))) ⊤
  let := baseModule (projectiveSpaceToBase K n)
    (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of K))
      (projectiveTwist n ((Scheme.Modules.pullback
        (projectiveSpaceFieldExtensionMap k K n)).obj F) m)
      (twistOver n (Spec (CommRingCat.of K)) 1)) ⊤
  let := baseTower H ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
    (projectiveTwist n F m)) ⊤
  let := baseTower H ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
    (twistOver n (Spec (CommRingCat.of k)) 1)) ⊤
  let := baseTower H ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
    (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) (projectiveTwist n F
        m)
      (twistOver n (Spec (CommRingCat.of k)) 1))) ⊤
  obtain ⟨eM, heM⟩ := exists_linearEquiv_sections_baseChange H (projectiveTwist n F m)
  obtain ⟨eL, heL⟩ := exists_linearEquiv_sections_baseChange H
    (twistOver n (Spec (CommRingCat.of k)) 1)
  obtain ⟨eN, heN⟩ := exists_linearEquiv_sections_baseChange H
    (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) (projectiveTwist n F
        m)
      (twistOver n (Spec (CommRingCat.of k)) 1))
  -- the comparison isomorphisms
  let : Module ↑Γ(Spec (CommRingCat.of K), ⊤) ↑(projectiveGamma K n
      (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of K)) (projectiveTwist n
      ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj F) m) (twistOver n
      (Spec (CommRingCat.of K)) 1))) :=
    baseModule (projectiveSpaceToBase K n) (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (.of K)) (projectiveTwist n ((Scheme.Modules.pullback
        (projectiveSpaceFieldExtensionMap k K n)).obj F) m) (twistOver n (Spec (CommRingCat.of K))
        1)) ⊤
  let : Module ↑Γ(Spec (CommRingCat.of k), ⊤) ↑(projectiveGamma k n
      (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) (projectiveTwist n
      F m) (twistOver n (Spec (CommRingCat.of k)) 1))) :=
    baseModule (projectiveSpaceToBase k n) (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing n (.of k)) (projectiveTwist n F m) (twistOver n (Spec
        (CommRingCat.of k)) 1)) ⊤
  have Ξ : (projectiveTwist n ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K
      n)).obj F) m) ≅ ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
      (projectiveTwist n F m)) :=
    projectiveTwistPullbackIso (CommRingCat.ofHom (algebraMap k K)) n m F
  have u : (twistOver n (Spec (CommRingCat.of K)) 1) ≅ ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k K n)).obj (twistOver n (Spec (CommRingCat.of k)) 1)) :=
    (twistingSheafPullbackIso (CommRingCat.ofHom (algebraMap k K)) n 1).symm
  let c : ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj
      (Stacks.RelativeVeryAmple.tensorModules (projectiveSpaceOverRing n (.of k)) (projectiveTwist n
      F m) (twistOver n (Spec (CommRingCat.of k)) 1))) ≅ Stacks.RelativeVeryAmple.tensorModules
      (projectiveSpaceOverRing n (.of K)) ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k K n)).obj (projectiveTwist n F m))
      ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k K n)).obj (twistOver n (Spec
      (CommRingCat.of k)) 1)) :=
    Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (projectiveSpaceFieldExtensionMap k K n)
        (projectiveTwist n F m) (twistOver n (Spec (CommRingCat.of k)) 1)
  -- `Γ(g^*𝒢, ⊤)` is spanned over `Γ(Spec K, ⊤)` by the pullbacks of global sections of `𝒢`
  have hspanM := Submodule.span_range_eq_top_of_baseChange eM
    (pullbackGlobalSections (projectiveSpaceFieldExtensionMap k K n) (projectiveTwist n F m))
    fun x => ((heM 1 x).trans ((one_smul _ _).trans
      (pullbackSectionsHom_top_eq_pullbackGlobalSections _ _ x))).symm
  have hspanL := Submodule.span_range_eq_top_of_baseChange eL
    (pullbackGlobalSections (projectiveSpaceFieldExtensionMap k K n)
      (twistOver n (Spec (CommRingCat.of k)) 1))
    fun x => ((heL 1 x).trans ((one_smul _ _).trans
      (pullbackSectionsHom_top_eq_pullbackGlobalSections _ _ x))).symm
  -- every product of sections upstairs lies in the span of the pullbacks of products
  have hmem := mem_span_pullback_tensorSections k K n (projectiveTwist n F m)
    (twistOver n (Spec (CommRingCat.of k)) 1) c
    (fun x y => pullbackTensorIso_inv_val_app_top_tensorSectionsAt
      (projectiveSpaceFieldExtensionMap k K n) (projectiveTwist n F m)
      (twistOver n (Spec (CommRingCat.of k)) 1) x y) hspanM hspanL
  -- the pullbacks of the products span upstairs
  have hPtop := span_pullback_tensorSections_eq_top k K n (projectiveTwist n F m)
    (twistOver n (Spec (CommRingCat.of k)) 1)
    (projectiveTwist n ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k K n)).obj F) m)
    (twistOver n (Spec (CommRingCat.of K)) 1) Ξ u c hmem hKspan
  -- descend the span along the faithfully flat extension
  refine eq_top_iff.2 fun t _ => ?_
  refine Submodule.span_subset_span_of_surjective (R := ↑Γ(Spec (CommRingCat.of k), ⊤)) (S := k)
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
    (fun _ _ => rfl) _ ?_
  refine (Submodule.eq_top_of_span_image_baseChange _ eN _ hPtop ?_).ge Submodule.mem_top
  rintro t ⟨x, y, rfl⟩
  have h₁ := (heN 1 (Stacks.SheafOfModules.tensorSectionsAt
    (projectiveSpaceOverRing n (.of k)).presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (projectiveSpaceOverRing n (.of k)))
    (op ⊤) (projectiveTwist n F m) (twistOver n (Spec (CommRingCat.of k)) 1) x y)).trans
    ((one_smul _ _).trans (pullbackSectionsHom_top_eq_pullbackGlobalSections _ _ _))
  have h₂ := (congrArg eN.symm h₁).symm.trans (eN.symm_apply_apply _)
  exact Eq.mpr (congrArg (fun z => z ∈ Submodule.baseChange ↑Γ(Spec (CommRingCat.of K), ⊤)
      (Submodule.span ↑Γ(Spec (CommRingCat.of k), ⊤) _)) h₂)
    (Submodule.tmul_mem_baseChange_of_mem 1 (Submodule.subset_span ⟨x, y, rfl⟩))

/-! ### The reduction -/

/-- **The reduction of [Stacks, Tag 08A7] to an infinite base field.** Granted the conclusion of
[Stacks, Tag 08A7] over every *infinite* field, it holds over every field.

This is the source's "we may assume `k` is infinite". Pass to `k(t)`, which is infinite:
`m`-regularity is insensitive to the extension by [Stacks, Tag 08A4], and the span of the
products of global sections descends along the faithfully flat extension `k ⟶ k(t)` by
`AlgebraicGeometry.gammaProductSpan_eq_top_of_fieldExtension`. The statement is an implication
and not a conditional registration on purpose: as soon as the infinite-field case is available
the hypothesis is discharged and [Stacks, Tag 08A7] closes over an arbitrary field. -/
public theorem span_mulSections_eq_top_of_isMRegular_of_infinite
    (H : ∀ (K : Type u) [Field K] [Infinite K] (N : ℕ)
      (G : (projectiveSpaceOverRing N (.of K)).Modules) (hGc : G.IsCoherent) (d : ℤ),
      @IsMRegular K _ N G hGc d → mulSectionsSpan K N G d = ⊤)
    (k : Type u) [Field k] (n : ℕ) (F : (projectiveSpaceOverRing n (.of k)).Modules)
    [F.IsCoherent] (m : ℤ) (hF : IsMRegular k n F m) :
    mulSectionsSpan k n F m = ⊤ := by
  have : Infinite (RatFunc k) := infinite_ratFunc k
  have : IsLocallyNoetherian (projectiveSpaceOverRing n (.of (RatFunc k))) :=
    projectiveSpaceOver_isLocallyNoetherian n (Spec (.of (RatFunc k)))
  have hFK : ((Scheme.Modules.pullback
      (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj F).IsCoherent :=
    isCoherent_pullback (projectiveSpaceFieldExtensionMap k (RatFunc k) n) F
  have h₁ : IsMRegular (RatFunc k) n
      ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj F) m :=
    (isMRegular_iff_fieldExtension k (RatFunc k) n F m).mp hF
  have h₂ := H (RatFunc k) n
    ((Scheme.Modules.pullback (projectiveSpaceFieldExtensionMap k (RatFunc k) n)).obj F) hFK m h₁
  exact (mulSectionsSpan_eq_top_iff_gammaProductSpan k n F m).2
    (gammaProductSpan_eq_top_of_fieldExtension k (RatFunc k) n F m
      ((mulSectionsSpan_eq_top_iff_gammaProductSpan (RatFunc k) n _ m).1 h₂))

end AlgebraicGeometry

end
