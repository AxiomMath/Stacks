module

public import StacksFrontier.Algebra.Category.Ring.IndPushoutEqualization
public import StacksFrontier.Algebra.Category.Ring.UnderPushoutTensor
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.AtPrime

/-!
# Descending a construction over an ind-étale base change to an étale stage

Let `C → A` be a ring map and let `Λ` be an **ind-étale** `C`-algebra, a filtered colimit of étale
`C`-algebras — the case of interest being `Λ` a strict henselization
`StacksDraft.strictHenselizationAtPrime`, by
`StacksDraft.indEtale_strictHenselizationAtPrime`. Then `A ⊗[C] Λ` is the filtered colimit of the
`A ⊗[C] D` over the étale stages `D` of `Λ`, and this file is the two consequences of that which
a descent argument needs:

* an `A`-algebra map of **finite presentation** into `A ⊗[C] Λ` already lands in `A ⊗[C] D` for a
  single étale stage `D`, compatibly with that stage's own structure map `D → Λ`;
* an **equation** between two elements of a base change `M ⊗[C] D` of a finitely presented stage
  which holds in `M ⊗[C] Λ` already holds in `M ⊗[C] D'` for a (possibly later) étale stage
  `D → D' → Λ`.

Both are the `Algebra`-language form of the categorical statements in
`StacksFrontier.Algebra.Category.Ring.IndPushoutFactorization` and
`StacksFrontier.Algebra.Category.Ring.IndPushoutEqualization`, transported along
`CommRingCat.underTensorIso`.

The first is how a **retraction** descends. By the base-change adjunction an `A ⊗[C] Λ`-algebra
retraction of `A ⊗[C] Λ → A' ⊗[A] (A ⊗[C] Λ)` is the same thing as an `A`-algebra map
`A' → A ⊗[C] Λ`, which is the form taken here; `A'` is finitely presented over `A` whenever
`A → A'` is étale, so the hypothesis is met in the application. The second is how the equation
expressing that something constructed at a stage is *invariant* descends: the two elements are
the two pullbacks of an idempotent along the source and target maps of a groupoid.

## Main results

* `StacksDraft.exists_etale_stage_of_indEtale`: **the factorization through a single étale
  stage**, with that stage's structure map to `Λ`.
* `StacksDraft.exists_etale_stage_eq_of_indEtale`: **the equation at a single étale stage**, with
  the map from the given stage into it over `Λ`.

## Implementation notes

The stage `D` is returned together with its `CommRing` and `Algebra C D` structures, so the
mismatch between an algebra structure a caller already has and the one `CategoryTheory.Under`
manufactures from a structure map does not arise on that side. On the side of `Λ`, which the
caller supplies, it is avoided by `CommRingCat.underTensorIso`, whose tensor product is formed
with the given `Algebra C Λ`; see the implementation notes there.

In `StacksDraft.exists_etale_stage_eq_of_indEtale` the given stage `D` is assumed only *finitely
presented* over `C`, not étale, which is what the proof uses; it is étale in the application,
being the stage the first statement returns.

## References

* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
* [Stacks Project, Tag 0BSH](https://stacks.math.columbia.edu/tag/0BSH)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)

## Tags

ind-étale, filtered colimit, descent, étale stage, base change
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace StacksDraft

variable {C Λ : Type u} [CommRing C] [CommRing Λ] [Algebra C Λ]

/-- A morphism in `Under` commutes with the structure maps of source and target. -/
private theorem under_hom_right_apply {R : CommRingCat.{u}} {X Y : Under R} (f : X ⟶ Y)
    (r : R) : f.right (X.hom r) = Y.hom r := by
  rw [← CommRingCat.comp_apply, Under.w f]

/-- The structure map of `Under.mk (ofHom (algebraMap R S))` is finitely presented. -/
private theorem finitePresentation_under_mk_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (h : Algebra.FinitePresentation R S) :
    (Under.mk (CommRingCat.ofHom (algebraMap R S))).hom.hom.FinitePresentation :=
  show (algebraMap R S).FinitePresentation from RingHom.finitePresentation_algebraMap.mpr h

/-- **An `A`-algebra map of finite presentation into `A ⊗[C] Λ`, for `Λ` ind-étale over `C`,
factors through `A ⊗[C] D` for a single étale stage `D`**, the second map being the base change of
the structure map `D → Λ` of that stage.

This is how the strictly-henselian-stage retraction of [Stacks Project, Tag 0DT9] descends: the
retraction is, by the base-change adjunction, an `A`-algebra map `A' → A ⊗[C] Λ`, and `A'` is
finitely presented over `A` because `U' → U` is étale. -/
theorem exists_etale_stage_of_indEtale {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra C A] [Algebra A A'] (hΛ : IndEtale C Λ) (hA' : Algebra.FinitePresentation A A')
    (f : A' →ₐ[A] A ⊗[C] Λ) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra C D), Algebra.Etale C D ∧
      ∃ (h : D →ₐ[C] Λ) (g : A' →ₐ[A] A ⊗[C] D),
        (Algebra.TensorProduct.map (AlgHom.id A A) h).comp g = f := by
  have hX := finitePresentation_under_mk_algebraMap hA'
  have hfu : CommRingCat.ofHom (algebraMap A A') ≫
      CommRingCat.ofHom (f : A' →+* A ⊗[C] Λ) =
      (CommRingCat.underTensor C A Λ).hom := by
    ext a; simp
  obtain ⟨Du, hDu, hu, gu, hgu⟩ :=
    CommRingCat.exists_factorization_of_ind_pushout (CommRingCat.ofHom (algebraMap C A))
      (indEtale_iff_ind_underMk.mp hΛ) hX
      (Under.homMk (CommRingCat.ofHom (f : A' →+* A ⊗[C] Λ)) hfu ≫
        (CommRingCat.underTensorIso C A Λ).hom)
  let : Algebra C (Du : Type u) := (Du.hom.hom).toAlgebra
  have : Algebra.Etale C (Du : Type u) := RingHom.etale_algebraMap.mp hDu
  have hcm : ∀ r : C, hu.right (Du.hom r) = algebraMap C Λ r := under_hom_right_apply hu
  set gu' := gu ≫ (CommRingCat.underTensorIso C A (Du : Type u)).inv with hgu'
  have hcg : ∀ a : A, gu'.right (algebraMap A A' a) =
      algebraMap A (A ⊗[C] (Du : Type u)) a := fun a => by
    have h : ((Under.mk (CommRingCat.ofHom (algebraMap A A'))).hom ≫ gu'.right) a =
        (CommRingCat.underTensor C A (Du : Type u)).hom a := by rw [Under.w gu']
    simpa using h
  let hA : (Du : Type u) →ₐ[C] Λ := { __ := hu.right.hom, commutes' := hcm }
  let gA : A' →ₐ[A] A ⊗[C] (Du : Type u) := { __ := gu'.right.hom, commutes' := hcg }
  refine ⟨(Du : Type u), inferInstance, inferInstance, inferInstance, hA, gA, ?_⟩
  have hid : CommRingCat.underAlgHom C hA = hu := Under.UnderMorphism.ext rfl
  have key : gu' ≫ CommRingCat.underTensorMap C A hA =
      Under.homMk (CommRingCat.ofHom (f : A' →+* A ⊗[C] Λ)) hfu := by
    rw [← cancel_mono (CommRingCat.underTensorIso C A Λ).hom, Category.assoc,
      CommRingCat.underTensorMap_comp_underTensorIso, hid, hgu', Category.assoc,
      Iso.inv_hom_id_assoc]
    exact hgu
  exact AlgHom.ext fun x => congr($(key).right x)

/-- **Two elements of a base change `M ⊗[C] D` of a finitely presented stage which agree in
`M ⊗[C] Λ`, for `Λ` ind-étale over `C`, already agree in `M ⊗[C] D'` for a single étale stage
`D'`** with a map `D → D'` over `Λ`.

This is how the invariance equation of [Stacks Project, Tag 0DT9] descends: invariance of the
sheet cut out by an idempotent `e` of the stage is the single equation `s'^♯ e = t'^♯ e`, which
holds over the strict henselization and therefore over some étale stage. -/
theorem exists_etale_stage_eq_of_indEtale {M D : Type u} [CommRing M] [CommRing D]
    [Algebra C M] [Algebra C D] (hΛ : IndEtale C Λ) (hD : Algebra.FinitePresentation C D)
    (h : D →ₐ[C] Λ) (x y : M ⊗[C] D)
    (hxy : Algebra.TensorProduct.map (AlgHom.id M M) h x =
      Algebra.TensorProduct.map (AlgHom.id M M) h y) :
    ∃ (D' : Type u) (_ : CommRing D') (_ : Algebra C D'), Algebra.Etale C D' ∧
      ∃ (h' : D' →ₐ[C] Λ) (φ : D →ₐ[C] D'), h'.comp φ = h ∧
        Algebra.TensorProduct.map (AlgHom.id M M) φ x =
          Algebra.TensorProduct.map (AlgHom.id M M) φ y := by
  have hDfp := finitePresentation_under_mk_algebraMap hD
  have hn : ∀ z : M ⊗[C] D,
      (CommRingCat.underTensorMap C M h ≫ (CommRingCat.underTensorIso C M Λ).hom).right z =
      ((CommRingCat.underTensorIso C M D).hom ≫
        (Under.pushout (CommRingCat.ofHom (algebraMap C M))).map
          (CommRingCat.underAlgHom C h)).right z :=
    fun z => congr($(CommRingCat.underTensorMap_comp_underTensorIso C M h).right z)
  have hxy' : ((Under.pushout (CommRingCat.ofHom (algebraMap C M))).map
        (CommRingCat.underAlgHom C h)).right
          ((CommRingCat.underTensorIso C M D).hom.right x) =
      ((Under.pushout (CommRingCat.ofHom (algebraMap C M))).map
        (CommRingCat.underAlgHom C h)).right
          ((CommRingCat.underTensorIso C M D).hom.right y) :=
    (hn x).symm.trans ((congrArg (CommRingCat.underTensorIso C M Λ).hom.right hxy).trans (hn y))
  obtain ⟨D'u, hP, h'u, φu, hφ, heq⟩ :=
    CommRingCat.exists_stage_eq_of_ind_pushout (CommRingCat.ofHom (algebraMap C M))
      (indEtale_iff_ind_underMk.mp hΛ) hDfp (CommRingCat.underAlgHom C h)
      ((CommRingCat.underTensorIso C M D).hom.right x)
      ((CommRingCat.underTensorIso C M D).hom.right y) hxy'
  let : Algebra C (D'u : Type u) := (D'u.hom.hom).toAlgebra
  have : Algebra.Etale C (D'u : Type u) := RingHom.etale_algebraMap.mp hP
  have hcm' : ∀ r : C, h'u.right (D'u.hom r) = algebraMap C Λ r := under_hom_right_apply h'u
  have hcmφ : ∀ r : C, φu.right (algebraMap C D r) = algebraMap C (D'u : Type u) r :=
    under_hom_right_apply φu
  let h' : (D'u : Type u) →ₐ[C] Λ := { __ := h'u.right.hom, commutes' := hcm' }
  let φ : D →ₐ[C] (D'u : Type u) := { __ := φu.right.hom, commutes' := hcmφ }
  refine ⟨(D'u : Type u), inferInstance, inferInstance, inferInstance, h', φ, ?_, ?_⟩
  · exact AlgHom.ext fun d => congr($(hφ).right d)
  · have hidφ : CommRingCat.underAlgHom C φ = φu := Under.UnderMorphism.ext rfl
    have hnφ : ∀ z : M ⊗[C] D,
        (CommRingCat.underTensorIso C M (D'u : Type u)).hom.right
            (Algebra.TensorProduct.map (AlgHom.id M M) φ z) =
          ((Under.pushout (CommRingCat.ofHom (algebraMap C M))).map φu).right
            ((CommRingCat.underTensorIso C M D).hom.right z) := fun z => by
      rw [← hidφ]
      exact congr($(CommRingCat.underTensorMap_comp_underTensorIso C M φ).right z)
    have hback : ∀ z : M ⊗[C] (D'u : Type u),
        (CommRingCat.underTensorIso C M (D'u : Type u)).inv.right
          ((CommRingCat.underTensorIso C M (D'u : Type u)).hom.right z) = z := fun z => by
      rw [← CommRingCat.comp_apply, Under.hom_right_inv_right]
      simp
    refine (hback _).symm.trans ?_
    rw [hnφ x, heq, ← hnφ y, hback]

end StacksDraft

end
