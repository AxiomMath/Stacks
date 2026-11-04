module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Stalk
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.GradedSections.Braided
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.Basic

/-!
# Multiplication by a regular section of an invertible module, and its cokernels

Let `ℒ` be an invertible module on a scheme `X` and `σ` a section of `ℒ`. Multiplication by `σ`
gives maps `ℒ^{⊗ n} ⟶ ℒ^{⊗ 1 + n}`, which are monomorphisms when `σ` is one. The supports of
their cokernels decrease with `n` and lie in the zero locus of `σ`. A section `t` of `ℒ^{⊗ e}`
induces maps between these cokernels, which are epimorphisms as soon as every point of the
support of the target lies in the nonvanishing locus of `t`.

## Main definitions

* `Stacks.RegularSectionGeneration.quot`: the cokernel of multiplication by `σ` from `ℒ^{⊗ n}` to
  `ℒ^{⊗ 1 + n}`.
* `Stacks.RegularSectionGeneration.quotMap`: the map of cokernels `quot σ a ⟶ quot σ (e + a)`
  induced by multiplication by `t`.

## Main results

* `Stacks.RegularSectionGeneration.mono_mulMap`: multiplication by a regular section is a
  monomorphism in every degree.
* `Stacks.RegularSectionGeneration.supp_quot_succ_subset`: the supports of the cokernels decrease
  with the degree.
* `Stacks.RegularSectionGeneration.notMem_supp_quot_of_mem_nvLocus`: off the zero locus of `σ`
  every cokernel vanishes.
* `Stacks.RegularSectionGeneration.epi_quotMap`: multiplication by `t` is an epimorphism of
  cokernels when every point lies in the nonvanishing locus of `t` or misses the support of the
  target.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Ample
open Stacks.GradedSections (powSections mulMap mul)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.RegularSectionGeneration

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- **Tensoring on the right with an invertible module preserves monomorphisms.** -/
theorem mono_whiskerRight {M N : X.Modules} (f : M ⟶ N) [Mono f] : Mono (f ▷ L) := by
  have : (tensorLeft L).IsEquivalence :=
    (AlgebraicGeometry.SheafOfModules.isInvertible_iff_isEquivalence_tensorLeft X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L).mp inferInstance
  have hl : Mono (L ◁ f) := (tensorLeft L).map_mono f
  have hb : f ▷ L = (β_ M L).hom ≫ (L ◁ f) ≫ (β_ N L).inv := by
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left f L, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [hb]
  infer_instance

/-! ### Multiplication by a section of degree one, and its cokernels -/

variable {L} (σ : powSections L 1)

/-- **The cokernel of multiplication by `σ` from `ℒ^{⊗ n}` to `ℒ^{⊗ 1 + n}`.** For `σ` the regular
section of [Stacks, Tag 0E8V] this is `i_*(ℒ^{⊗ n+1}|_Z)`, `Z` the zero scheme of `σ`. -/
abbrev quot (n : ℕ) : X.Modules := cokernel (mulMap σ n)

/-- **Multiplication by a regular section is a monomorphism in every degree.** -/
theorem mono_mulMap [hσ : Mono σ] : ∀ n : ℕ, Mono (mulMap σ n)
  | 0 => hσ
  | n + 1 => by
    rw [Stacks.GradedSections.mulMap_succ]
    have := mono_mulMap n
    exact mono_whiskerRight L _

omit [IsInvertibleModule X L] in
/-- **A point misses the support of `quot σ n` exactly when multiplication by `σ` is surjective on
the stalk there.** -/
theorem notMem_supp_quot_iff (n : ℕ) (x : X) :
    x ∉ SheafOfModules.supp (quot σ n) ↔ Stacks.SectionProduct.SurjStalk (mulMap σ n) x :=
  (AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel _ x).symm

omit [IsInvertibleModule X L] in
/-- **The supports of the cokernels shrink with the degree.** -/
theorem supp_quot_succ_subset (n : ℕ) :
    SheafOfModules.supp (quot σ (n + 1)) ⊆ SheafOfModules.supp (quot σ n) := by
  intro x hx
  by_contra hn
  rw [notMem_supp_quot_iff] at hn
  exact (notMem_supp_quot_iff σ (n + 1) x).mpr
    (Stacks.SectionProduct.SurjStalk.whiskerRight _ L hn) hx

omit [IsInvertibleModule X L] in
/-- The supports of the cokernels in positive degree all lie in that of degree one. -/
theorem supp_quot_subset_one : ∀ {n : ℕ}, 1 ≤ n →
    SheafOfModules.supp (quot σ n) ⊆ SheafOfModules.supp (quot σ 1)
  | 0, h => absurd h (by omega)
  | 1, _ => subset_rfl
  | n + 2, _ => (supp_quot_succ_subset σ (n + 1)).trans (supp_quot_subset_one (by omega))

/-- **Off the zero locus of `σ` every cokernel vanishes.** -/
theorem notMem_supp_quot_of_mem_nvLocus {x : X}
    (hx : x ∈ Stacks.AmpleFiniteAvoidance.nvLocus L σ) (n : ℕ) :
    x ∉ SheafOfModules.supp (quot σ n) :=
  (notMem_supp_quot_iff σ n x).mpr
    (Stacks.SectionProduct.surjStalk_mulMap L 1 σ x
      (Stacks.SectionProduct.surjStalk_of_mem_nonvanishingLocus _ σ x hx) n)

/-! ### Multiplication by a second section commutes with multiplication by `σ` -/

omit [IsInvertibleModule X L] in
/-- Multiplication by a transported section is multiplication by the section, transported. -/
theorem mulMap_comp_powCongr {n m : ℕ} (h : n = m) (s : powSections L n) (k : ℕ) :
    mulMap (s ≫ Stacks.GradedSections.powCongr L h) k =
      mulMap s k ≫ Stacks.GradedSections.powCongr L (congrArg (· + k) h) := by
  subst h
  simp

/-- **Multiplication by `σ` and by `t` commute**, up to the transport of degrees that the two
orders of multiplication produce. -/
theorem mulMap_comm {e : ℕ} (t : powSections L e) (a : ℕ) :
    mulMap σ a ≫ mulMap t (1 + a) =
      mulMap t a ≫ mulMap σ (e + a) ≫
        Stacks.GradedSections.powCongr L (by omega : 1 + (e + a) = e + (1 + a)) := by
  have h1 := Stacks.GradedSections.mulMap_mul t σ a
  have h2 := Stacks.GradedSections.mulMap_mul σ t a
  have h3 := Stacks.GradedSections.mul_comm' σ t
  rw [← h3, mulMap_comp_powCongr, h2] at h1
  rw [← cancel_mono (Stacks.GradedSections.powCongr L (Nat.add_assoc e 1 a).symm)]
  simp only [Category.assoc] at h1 ⊢
  rw [← h1]
  simp

/-! ### The map of cokernels induced by multiplication by a second section -/

variable {e : ℕ} (t : powSections L e)

/-- The degree transport of `mulMap_comm`, cancelled against its inverse. -/
theorem mulMap_comm' (a : ℕ) :
    mulMap σ a ≫ mulMap t (1 + a) ≫
        Stacks.GradedSections.powCongr L (by omega : e + (1 + a) = 1 + (e + a)) =
      mulMap t a ≫ mulMap σ (e + a) := by
  rw [← Category.assoc, mulMap_comm σ t a]
  simp

/-- **Multiplication by `t`, on the cokernels of multiplication by `σ`**: the map
`quot σ a ⟶ quot σ (e + a)` induced by multiplication by `t` on `ℒ^{⊗ a}` and `ℒ^{⊗ 1 + a}`. -/
def quotMap (a : ℕ) : quot σ a ⟶ quot σ (e + a) :=
  cokernel.map (mulMap σ a) (mulMap σ (e + a)) (mulMap t a)
    (mulMap t (1 + a) ≫
      Stacks.GradedSections.powCongr L (by omega : e + (1 + a) = 1 + (e + a)))
    (mulMap_comm' σ t a)

/-- `quotMap` on the image of a section of `ℒ^{⊗ 1 + a}`. -/
theorem π_quotMap (a : ℕ) :
    cokernel.π (mulMap σ a) ≫ quotMap σ t a =
      (mulMap t (1 + a) ≫
        Stacks.GradedSections.powCongr L (by omega : e + (1 + a) = 1 + (e + a))) ≫
        cokernel.π (mulMap σ (e + a)) := by
  simp [quotMap]

/-! ### Epimorphisms from stalks -/

omit [IsInvertibleModule X L] in
/-- **A morphism surjective on every stalk is an epimorphism.** -/
theorem epi_of_forall_surjStalk {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x, Stacks.SectionProduct.SurjStalk f x) : Epi f := by
  have hf : Epi (C := SheafOfModules.{u} X.ringCatSheaf) f :=
    (AlgebraicGeometry.epi_iff_stalk_surjective X.ringCatSheaf f).mpr h
  exact ⟨fun g k hc => hf.left_cancellation g k hc⟩

omit [IsInvertibleModule X L] in
/-- **An epimorphism is surjective on every stalk.** -/
theorem surjStalk_of_epi {M N : X.Modules} (f : M ⟶ N) [hf : Epi f] (x : X) :
    Stacks.SectionProduct.SurjStalk f x := by
  have hf' : Epi (C := SheafOfModules.{u} X.ringCatSheaf) f := hf
  exact (AlgebraicGeometry.epi_iff_stalk_surjective X.ringCatSheaf f).mp hf' x

omit [IsInvertibleModule X L] in
/-- **Every morphism is surjective on the stalk at a point outside the support of its
target.** -/
theorem surjStalk_of_notMem_supp {M N : X.Modules} (f : M ⟶ N) {x : X}
    (hx : x ∉ SheafOfModules.supp N) : Stacks.SectionProduct.SurjStalk f x := by
  have h := ModuleCat.subsingleton_of_isZero
    ((AlgebraicGeometry.Scheme.Modules.notMem_supp_iff_isZero_stalk N x).mp hx)
  exact fun z => ⟨0, @Subsingleton.elim _ h _ _⟩

/-- **Multiplication by `t` is an epimorphism of cokernels** as soon as every point either lies in
the nonvanishing locus of `t` or misses the support of the target. -/
theorem epi_quotMap (a : ℕ)
    (h : ∀ x, x ∈ Stacks.AmpleFiniteAvoidance.nvLocus L t ∨
      x ∉ SheafOfModules.supp (quot σ (e + a))) :
    Epi (quotMap σ t a) := by
  refine epi_of_forall_surjStalk _ fun x => ?_
  rcases h x with hx | hx
  · have h1 : Stacks.SectionProduct.SurjStalk (mulMap t (1 + a)) x :=
      Stacks.SectionProduct.surjStalk_mulMap L e t x
        (Stacks.SectionProduct.surjStalk_of_mem_nonvanishingLocus _ t x hx) (1 + a)
    have h2 : Stacks.SectionProduct.SurjStalk
        (Stacks.GradedSections.powCongr L (by omega : e + (1 + a) = 1 + (e + a))) x :=
      Stacks.SectionProduct.surjStalk_of_inv
        (e' := Stacks.GradedSections.powCongr L (by omega : 1 + (e + a) = e + (1 + a)))
        (by simp) x
    have h3 : Stacks.SectionProduct.SurjStalk (cokernel.π (mulMap σ (e + a))) x :=
      surjStalk_of_epi _ x
    have h4 := (h1.comp h2).comp h3
    rw [← π_quotMap] at h4
    exact Stacks.SectionProduct.SurjStalk.of_comp_left _ h4
  · exact surjStalk_of_notMem_supp _ hx

end Stacks.RegularSectionGeneration

end
