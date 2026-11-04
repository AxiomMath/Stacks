module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleColimitClauseTransfer

/-!
# Quotients along a pullback system

Let `A` be a pullback system (`Stacks.ModuleColimit.PullbackSystem`) of abelian categories over a
cofiltered index category, whose inverse images are right exact, and which satisfies the three
clauses of Stacks 07V7 (faithfulness, fullness and essential surjectivity) for a property `P` of
objects stable under inverse images and under cokernels.  This file derives the two halves of the
colimit assertion for *quotients* used in the proof of Stacks 082Q:

* **descent of quotients**: given a family of objects `M j` at the stages, identified with each
  other along the inverse images and with an object `M_L` over the limit, every epimorphism
  `M_L ⟶ Q` onto an object of `PL` is, up to isomorphism, the inverse image of an epimorphism
  `M j ⟶ N` onto an object of `P` at some stage;
* **eventual equality of quotients**: two epimorphisms out of one object at a stage whose inverse
  images to the limit differ by a morphism in each direction have the same kernel after inverse
  image to a later stage.

The surjectivity at a stage is Stacks 05LI read through the faithfulness clause: the cokernel of
the descended morphism is in `P`, it vanishes over the limit, hence at a later stage.

## Main results

* `Stacks.ModuleColimit.PullbackSystem.exists_epi_pb_of_epi_pbL`
* `Stacks.ModuleColimit.PullbackSystem.exists_quotient_of_quotient_pbL`
* `Stacks.ModuleColimit.PullbackSystem.exists_kernelSubobject_eq_of_pbL`

## References

* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
* [Stacks Project, Tag 07V7](https://stacks.math.columbia.edu/tag/07V7)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' v₁ u₁

namespace Stacks.ModuleColimit.PullbackSystem

variable {J : Type w} [Category.{w'} J] (A : PullbackSystem.{w, w', v₁, u₁} J)

/-- A relation between two morphisms over the limit, read one stage further along the system
through the comparison isomorphisms. -/
theorem pbL_map_pb_map_comp_conj {j k : J} (e : j ⟶ k) {M N N' : A.C k} (ψ : M ⟶ N)
    (ψ' : M ⟶ N') (χ : (A.pbL k).obj N ⟶ (A.pbL k).obj N')
    (h : (A.pbL k).map ψ ≫ χ = (A.pbL k).map ψ') :
    (A.pbL j).map ((A.pb e).map ψ) ≫
        ((A.comp e).inv.app N ≫ χ ≫ (A.comp e).hom.app N') =
      (A.pbL j).map ((A.pb e).map ψ') := by
  have n₁ := (A.comp e).inv.naturality ψ
  have n₂ := (A.comp e).hom.naturality ψ'
  simp only [Functor.comp_map] at n₁ n₂
  rw [reassoc_of% n₁, reassoc_of% h, n₂, Iso.inv_hom_id_app_assoc]

section Abelian

variable [∀ j, Abelian (A.C j)] [Abelian A.L]
  [∀ {j k : J} (e : j ⟶ k), (A.pb e).PreservesZeroMorphisms]
  [∀ {j k : J} (e : j ⟶ k), PreservesColimitsOfShape WalkingParallelPair (A.pb e)]
  [∀ j, (A.pbL j).PreservesZeroMorphisms]

/-- **Surjectivity at a stage** (Stacks 05LI through Stacks 07V7, faithfulness): a morphism
between objects of `P` whose inverse image to the limit is an epimorphism is an epimorphism after
inverse image to a later stage, provided `P` is stable under cokernels. -/
theorem exists_epi_pb_of_epi_pbL (hA : A.Faithfulness)
    (hcoker : ∀ j {M N : A.C j} (f : M ⟶ N), A.P j M → A.P j N → A.P j (cokernel f))
    {k : J} {M N : A.C k} (hM : A.P k M) (hN : A.P k N) (ψ : M ⟶ N)
    (hψ : Epi ((A.pbL k).map ψ)) :
    ∃ (j : J) (e : j ⟶ k), Epi ((A.pb e).map ψ) := by
  have h0 : (A.pbL k).map (cokernel.π ψ) = (A.pbL k).map 0 := by
    rw [Functor.map_zero]
    refine (cancel_epi ((A.pbL k).map ψ)).1 ?_
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero]
  obtain ⟨j, e, he⟩ := hA k N (cokernel ψ) hN (hcoker k ψ hM hN) _ _ h0
  refine ⟨j, e, Abelian.epi_of_cokernel_π_eq_zero _ ?_⟩
  rw [Functor.map_zero] at he
  have hc := π_comp_cokernelComparison ψ (A.pb e)
  rw [he] at hc
  exact (cancel_mono (cokernelComparison ψ (A.pb e))).1 (by rw [hc, zero_comp])

omit [∀ j, Abelian (A.C j)] [Abelian A.L]
  [∀ {j k : J} (e : j ⟶ k), (A.pb e).PreservesZeroMorphisms]
  [∀ {j k : J} (e : j ⟶ k), PreservesColimitsOfShape WalkingParallelPair (A.pb e)]
  [∀ j, (A.pbL j).PreservesZeroMorphisms] in
/-- The image along `pbL` of the inverse of an identification `σ e`, written through the
identifications `τ` with the object over the limit. -/
theorem pbL_map_inv_eq {Mj : ∀ j, A.C j} {ML : A.L} (τ : ∀ j, (A.pbL j).obj (Mj j) ≅ ML)
    (σ : ∀ {j k : J} (e : j ⟶ k), (A.pb e).obj (Mj k) ≅ Mj j)
    (hστ : ∀ {j k : J} (e : j ⟶ k),
      (A.comp e).hom.app (Mj k) ≫ (A.pbL j).map (σ e).hom ≫ (τ j).hom = (τ k).hom)
    {j k : J} (e : j ⟶ k) :
    (A.pbL j).map (σ e).inv = (τ j).hom ≫ (τ k).inv ≫ (A.comp e).hom.app (Mj k) := by
  refine (cancel_epi ((A.pbL j).map (σ e).hom)).1 ?_
  rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  have h' : (A.pbL j).map (σ e).hom ≫ (τ j).hom = (A.comp e).inv.app (Mj k) ≫ (τ k).hom := by
    rw [← hστ e]; simp
  rw [← Category.assoc, h']
  simp

variable [IsCofiltered J]

omit [IsCofiltered J] in
/-- **Descent of quotients along the system.**  Let `M j` be objects of `P` at the stages,
identified along the inverse images by `σ` and with an object `M_L` over the limit by `τ`,
compatibly.  An epimorphism `p : M_L ⟶ Q` onto an object of `PL` is, up to an isomorphism
`α`, the inverse image of an epimorphism `M j ⟶ N` onto an object of `P` at some stage. -/
theorem exists_quotient_of_quotient_pbL (hF : A.Faithfulness) (hFu : A.Fullness)
    (hE : A.EssSurj)
    (hpb : ∀ {j k : J} (e : j ⟶ k) (N : A.C k), A.P k N → A.P j ((A.pb e).obj N))
    (hcoker : ∀ j {M N : A.C j} (f : M ⟶ N), A.P j M → A.P j N → A.P j (cokernel f))
    {Mj : ∀ j, A.C j} (hMj : ∀ j, A.P j (Mj j)) {ML : A.L}
    (τ : ∀ j, (A.pbL j).obj (Mj j) ≅ ML)
    (σ : ∀ {j k : J} (e : j ⟶ k), (A.pb e).obj (Mj k) ≅ Mj j)
    (hστ : ∀ {j k : J} (e : j ⟶ k),
      (A.comp e).hom.app (Mj k) ≫ (A.pbL j).map (σ e).hom ≫ (τ j).hom = (τ k).hom)
    {Q : A.L} (hQ : A.PL Q) (p : ML ⟶ Q) [Epi p] :
    ∃ (j : J) (N : A.C j) (ψ : Mj j ⟶ N), A.P j N ∧ Epi ψ ∧
      ∃ α : (A.pbL j).obj N ≅ Q, (τ j).inv ≫ (A.pbL j).map ψ ≫ α.hom = p := by
  obtain ⟨k₀, N₀, hN₀, ⟨β⟩⟩ := hE Q hQ
  obtain ⟨j₁, e₁, φ₁, hφ₁⟩ := hFu k₀ (Mj k₀) N₀ (hMj k₀) hN₀ ((τ k₀).hom ≫ p ≫ β.inv)
  let ψ₁ : Mj j₁ ⟶ (A.pb e₁).obj N₀ := (σ e₁).inv ≫ φ₁
  let α₁ : (A.pbL j₁).obj ((A.pb e₁).obj N₀) ≅ Q := ((A.comp e₁).app N₀).symm ≪≫ β
  have key₁ : (τ j₁).inv ≫ (A.pbL j₁).map ψ₁ ≫ α₁.hom = p := by
    simp only [ψ₁, α₁, Functor.map_comp, A.pbL_map_inv_eq τ σ hστ e₁, hφ₁, Iso.trans_hom,
      Iso.symm_hom, Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hepi₁ : Epi ((A.pbL j₁).map ψ₁) := by
    have : (A.pbL j₁).map ψ₁ = (τ j₁).hom ≫ p ≫ α₁.inv := by
      rw [← key₁]; simp
    rw [this]; infer_instance
  obtain ⟨j₂, e₂, hepi₂⟩ := A.exists_epi_pb_of_epi_pbL hF hcoker (hMj j₁) (hpb e₁ N₀ hN₀) ψ₁
    hepi₁
  refine ⟨j₂, (A.pb e₂).obj ((A.pb e₁).obj N₀), (σ e₂).inv ≫ (A.pb e₂).map ψ₁,
    hpb e₂ _ (hpb e₁ N₀ hN₀), epi_comp _ _, ((A.comp e₂).app _).symm ≪≫ α₁, ?_⟩
  rw [← key₁]
  have n := (A.comp e₂).hom.naturality ψ₁
  simp only [Functor.comp_map] at n
  simp only [Functor.map_comp, A.pbL_map_inv_eq τ σ hστ e₂, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← reassoc_of% n, Iso.hom_inv_id_app_assoc]

omit [∀ j, Abelian (A.C j)] [Abelian A.L]
  [∀ {j k : J} (e : j ⟶ k), (A.pb e).PreservesZeroMorphisms]
  [∀ {j k : J} (e : j ⟶ k), PreservesColimitsOfShape WalkingParallelPair (A.pb e)]
  [∀ j, (A.pbL j).PreservesZeroMorphisms]
  [IsCofiltered J] in
/-- **One half of the eventual equality of quotients**: if the inverse images to the limit of
`ψ : M ⟶ N` and `ψ' : M ⟶ N'` at a stage are related by `χ`, the inverse images of `ψ` and `ψ'`
along two further transition morphisms are related by a morphism at that stage. -/
theorem exists_comp_eq_of_pbL (hF : A.Faithfulness) (hFu : A.Fullness)
    {k : J} {M N N' : A.C k} (hM : A.P k M) (hN : A.P k N) (hN' : A.P k N')
    (hpb : ∀ {j k : J} (e : j ⟶ k) (N : A.C k), A.P k N → A.P j ((A.pb e).obj N))
    (ψ : M ⟶ N) (ψ' : M ⟶ N') (χ : (A.pbL k).obj N ⟶ (A.pbL k).obj N')
    (h : (A.pbL k).map ψ ≫ χ = (A.pbL k).map ψ') :
    ∃ (j : J) (e : j ⟶ k) (j' : J) (e' : j' ⟶ j)
      (a : (A.pb e').obj ((A.pb e).obj N) ⟶ (A.pb e').obj ((A.pb e).obj N')),
      (A.pb e').map ((A.pb e).map ψ) ≫ a = (A.pb e').map ((A.pb e).map ψ') := by
  obtain ⟨j, e, φ, hφ⟩ := hFu k N N' hN hN' χ
  have h' := A.pbL_map_pb_map_comp_conj e ψ ψ' χ h
  rw [← hφ, ← Functor.map_comp] at h'
  obtain ⟨j', e', he'⟩ := hF j _ _ (hpb e M hM) (hpb e N' hN') _ _ h'
  exact ⟨j, e, j', e', (A.pb e').map φ, by rw [← Functor.map_comp, he']⟩

omit [Abelian A.L] [∀ {j k : J} (e : j ⟶ k), (A.pb e).PreservesZeroMorphisms]
  [∀ {j k : J} (e : j ⟶ k), PreservesColimitsOfShape WalkingParallelPair (A.pb e)]
  [∀ j, (A.pbL j).PreservesZeroMorphisms]
  [IsCofiltered J] in
/-- **Eventual equality of quotients**: two morphisms `ψ : M ⟶ N` and `ψ' : M ⟶ N'` between
objects of `P` at a stage whose inverse images to the limit differ by an isomorphism have the same
kernel after inverse image along a chain of transition morphisms. -/
theorem exists_kernelSubobject_eq_of_pbL (hF : A.Faithfulness) (hFu : A.Fullness)
    (hpb : ∀ {j k : J} (e : j ⟶ k) (N : A.C k), A.P k N → A.P j ((A.pb e).obj N))
    {k : J} {M N N' : A.C k} (hM : A.P k M) (hN : A.P k N) (hN' : A.P k N')
    (ψ : M ⟶ N) (ψ' : M ⟶ N') (ι : (A.pbL k).obj N ≅ (A.pbL k).obj N')
    (h : (A.pbL k).map ψ ≫ ι.hom = (A.pbL k).map ψ') :
    ∃ (j₁ : J) (e₁ : j₁ ⟶ k) (j₂ : J) (e₂ : j₂ ⟶ j₁) (j₃ : J) (e₃ : j₃ ⟶ j₂) (j₄ : J)
      (e₄ : j₄ ⟶ j₃),
      kernelSubobject ((A.pb e₁ ⋙ A.pb e₂ ⋙ A.pb e₃ ⋙ A.pb e₄).map ψ) =
        kernelSubobject ((A.pb e₁ ⋙ A.pb e₂ ⋙ A.pb e₃ ⋙ A.pb e₄).map ψ') := by
  obtain ⟨j₁, e₁, j₂, e₂, a, ha⟩ := A.exists_comp_eq_of_pbL hF hFu hM hN hN' hpb ψ ψ' ι.hom h
  -- The inverse relation, transported to the stage `j₂`.
  have hinv : (A.pbL k).map ψ' ≫ ι.inv = (A.pbL k).map ψ := by rw [← h]; simp
  have h₁ := A.pbL_map_pb_map_comp_conj e₁ ψ' ψ ι.inv hinv
  have h₂ := A.pbL_map_pb_map_comp_conj e₂ ((A.pb e₁).map ψ') ((A.pb e₁).map ψ) _ h₁
  obtain ⟨j₃, e₃, j₄, e₄, b, hb⟩ := A.exists_comp_eq_of_pbL hF hFu
    (hpb e₂ _ (hpb e₁ M hM)) (hpb e₂ _ (hpb e₁ N' hN')) (hpb e₂ _ (hpb e₁ N hN)) hpb
    ((A.pb e₂).map ((A.pb e₁).map ψ')) ((A.pb e₂).map ((A.pb e₁).map ψ)) _ h₂
  have key : ∀ {X Y Y' : A.C j₄} (f : X ⟶ Y) (f' : X ⟶ Y') (a : Y ⟶ Y'), f ≫ a = f' →
      kernelSubobject f ≤ kernelSubobject f' := by
    rintro _ _ _ f _ a rfl
    exact kernelSubobject_comp_le f a
  exact ⟨j₁, e₁, j₂, e₂, j₃, e₃, j₄, e₄,
    le_antisymm (key _ _ ((A.pb e₄).map ((A.pb e₃).map a))
      (by simp only [Functor.comp_map, ← Functor.map_comp, ha]))
      (key _ _ b (by simp only [Functor.comp_map, hb]))⟩

end Abelian

end Stacks.ModuleColimit.PullbackSystem

end
